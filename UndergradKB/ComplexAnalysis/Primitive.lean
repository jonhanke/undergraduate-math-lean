import Mathlib.Analysis.Convex.Segment
import UndergradKB.ComplexAnalysis.PathIntegralMore
import UndergradKB.ComplexAnalysis.SmallFacts
import UndergradKB.Common.Attr

/-!
# Antiderivatives from vanishing closed integrals (row CX-065)

On an open connected set `G`, a continuous `f` whose integral over every closed polygonal path
made of horizontal and vertical segments in `G` vanishes has an antiderivative on `G`; conversely a
function with an antiderivative has this property. Such polygonal paths are weaker test paths than
arbitrary closed piecewise smooth paths, so the result is at least as strong as the general one.

`HVPathIntegral G f a b I` says that `I` is the integral of `f` along some such polygonal path in
`G` from `a` to `b`.
-/

open Set Metric Complex

namespace UndergradKB.ComplexAnalysis

/-! ### Segments -/

/-- Parametrisation `t ↦ b + t (c - b)` of the segment from `b` to `c`. -/
def segPath (b c : ℂ) (t : ℝ) : ℂ := b + (t : ℂ) * (c - b)

/-- The integral of `f` along the segment from `b` to `c`. -/
noncomputable def segInt (f : ℂ → ℂ) (b c : ℂ) : ℂ := pathIntegral f (segPath b c) 0 1

lemma hasDerivAt_segPath (b c : ℂ) (t : ℝ) : HasDerivAt (segPath b c) (c - b) t := by
  have h : HasDerivAt (fun t : ℝ => b + (t : ℂ) * (c - b)) (c - b) t := by
    simpa using ((hasDerivAt_id t).ofReal_comp.mul_const (c - b)).const_add b
  exact h

lemma deriv_segPath (b c : ℂ) (t : ℝ) : deriv (segPath b c) t = c - b :=
  (hasDerivAt_segPath b c t).deriv

lemma isC1On_segPath (b c : ℂ) (x y : ℝ) : IsC1On (segPath b c) x y := by
  refine ⟨fun t _ => (hasDerivAt_segPath b c t).differentiableAt, ?_⟩
  rw [show deriv (segPath b c) = fun _ => c - b from funext (deriv_segPath b c)]
  exact continuousOn_const

lemma segPath_zero (b c : ℂ) : segPath b c 0 = b := by simp [segPath]

lemma segPath_one (b c : ℂ) : segPath b c 1 = c := by simp [segPath]

lemma segPath_mem {b c : ℂ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : segPath b c t ∈ segment ℝ b c :=
  ⟨1 - t, t, sub_nonneg.2 ht.2, ht.1, by ring, by
    simp only [segPath, Complex.real_smul]; push_cast; ring⟩

lemma pathIntegral_const_segPath (k b c : ℂ) :
    pathIntegral (fun _ => k) (segPath b c) 0 1 = k * (c - b) := by
  simp [pathIntegral, deriv_segPath]

lemma segInt_symm (f : ℂ → ℂ) (b c : ℂ) : segInt f c b = -segInt f b c := by
  unfold segInt
  have h : segPath c b = fun t => segPath b c (0 + 1 - t) := by
    funext t
    simp only [segPath]
    push_cast
    ring
  rw [h]
  exact pathIntegral_reverse

/-- A segment integral differs from `k (c - b)` by at most `M |c - b|` if `|f - k| ≤ M` on it. -/
lemma norm_segInt_sub_le {f : ℂ → ℂ} {b c k : ℂ} {M : ℝ} (hf : ContinuousOn f (segment ℝ b c))
    (hM : ∀ y ∈ segment ℝ b c, ‖f y - k‖ ≤ M) :
    ‖segInt f b c - k * (c - b)‖ ≤ M * ‖c - b‖ := by
  have hγ := isC1On_segPath b c 0 1
  have himg : segPath b c '' uIcc 0 1 ⊆ segment ℝ b c := by
    rintro _ ⟨t, ht, rfl⟩
    rw [uIcc_of_le zero_le_one] at ht
    exact segPath_mem ht
  have hfc : ContinuousOn f (segPath b c '' uIcc 0 1) := hf.mono himg
  have hconst : ContinuousOn (fun _ : ℂ => k) (segPath b c '' uIcc 0 1) := continuousOn_const
  have h1 : segInt f b c - k * (c - b)
      = pathIntegral (fun y => f y - k) (segPath b c) 0 1 := by
    have h := pathIntegral_sub (f := f) (g := fun _ => k)
      (intervalIntegrable_integrand hγ hfc) (intervalIntegrable_integrand hγ hconst)
    rw [pathIntegral_const_segPath] at h
    exact h.symm
  rw [h1]
  have h2 := norm_pathIntegral_le (f := fun y => f y - k) (M := M) hγ (hfc.sub hconst)
    zero_le_one (fun t ht => hM _ (segPath_mem ht))
  have hl : pathLength (segPath b c) 0 1 = ‖c - b‖ := pathLength_segment b c
  rw [hl] at h2
  exact h2

/-! ### The analytic step -/

private lemma norm_re_part_le (z w : ℂ) : ‖(⟨w.re, z.im⟩ : ℂ) - z‖ ≤ ‖w - z‖ := by
  have : (⟨w.re, z.im⟩ : ℂ) - z = (((w - z).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp)
  rw [this, Complex.norm_real, Real.norm_eq_abs]
  exact Complex.abs_re_le_norm _

private lemma norm_im_part_le (z w : ℂ) : ‖w - (⟨w.re, z.im⟩ : ℂ)‖ ≤ ‖w - z‖ := by
  have : w - (⟨w.re, z.im⟩ : ℂ) = (((w - z).im : ℝ) : ℂ) * I := Complex.ext (by simp) (by simp)
  rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  exact Complex.abs_im_le_norm _

/-- If `F` increases along every horizontal or vertical segment of `G` by the integral of the
continuous function `f`, then `F' = f` on the open set `G`. -/
theorem hasDerivAt_of_stepwise {f F : ℂ → ℂ} {G : Set ℂ} (hG : IsOpen G) (hf : ContinuousOn f G)
    (hF : ∀ b c, segment ℝ b c ⊆ G → (b.re = c.re ∨ b.im = c.im) →
      F c - F b = segInt f b c) {z : ℂ} (hz : z ∈ G) : HasDerivAt F (f z) z := by
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨ε, hε, hB⟩ := Metric.isOpen_iff.1 hG z hz
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.1 (hf.continuousAt (hG.mem_nhds hz))
    (c / 2) (half_pos hc)
  set R : ℝ := min ε δ with hR
  have hRpos : 0 < R := lt_min hε hδ
  have hRG : ball z R ⊆ G := (ball_subset_ball (min_le_left _ _)).trans hB
  have hRf : ∀ y ∈ ball z R, ‖f y - f z‖ ≤ c / 2 := by
    intro y hy
    have : dist y z < δ := lt_of_lt_of_le (mem_ball.1 hy) (min_le_right _ _)
    rw [← dist_eq_norm]
    exact (hδf this).le
  filter_upwards [ball_mem_nhds z hRpos] with w hw
  set m : ℂ := ⟨w.re, z.im⟩ with hm
  have hmz : ‖m - z‖ ≤ ‖w - z‖ := norm_re_part_le z w
  have hwm : ‖w - m‖ ≤ ‖w - z‖ := norm_im_part_le z w
  have hwz : ‖w - z‖ < R := by rwa [mem_ball, dist_eq_norm] at hw
  have hmb : m ∈ ball z R := by
    rw [mem_ball, dist_eq_norm]
    exact lt_of_le_of_lt hmz hwz
  have seg1 : segment ℝ z m ⊆ ball z R := (convex_ball z R).segment_subset (mem_ball_self hRpos) hmb
  have seg2 : segment ℝ m w ⊆ ball z R := (convex_ball z R).segment_subset hmb hw
  have e1 : F m - F z = segInt f z m := hF z m (seg1.trans hRG) (Or.inr rfl)
  have e2 : F w - F m = segInt f m w := hF m w (seg2.trans hRG) (Or.inl rfl)
  have est1 := norm_segInt_sub_le (f := f) (b := z) (c := m) (k := f z) (M := c / 2)
    (hf.mono (seg1.trans hRG)) (fun y hy => hRf y (seg1 hy))
  have est2 := norm_segInt_sub_le (f := f) (b := m) (c := w) (k := f z) (M := c / 2)
    (hf.mono (seg2.trans hRG)) (fun y hy => hRf y (seg2 hy))
  have key : F w - F z - (w - z) • f z
      = (segInt f z m - f z * (m - z)) + (segInt f m w - f z * (w - m)) := by
    rw [smul_eq_mul]
    linear_combination e1 + e2
  rw [key]
  refine (norm_add_le _ _).trans ?_
  nlinarith [mul_le_mul_of_nonneg_left hmz (half_pos hc).le,
    mul_le_mul_of_nonneg_left hwm (half_pos hc).le]

/-! ### Polygonal paths and path independence -/

/-- `HVPathIntegral G f a b I`: `I` is the integral of `f` along a polygonal path in `G` from `a`
to `b` consisting of horizontal and vertical segments. -/
inductive HVPathIntegral (G : Set ℂ) (f : ℂ → ℂ) (a : ℂ) : ℂ → ℂ → Prop
  | refl (h : a ∈ G) : HVPathIntegral G f a a 0
  | step {b c I : ℂ} : HVPathIntegral G f a b I → (b.re = c.re ∨ b.im = c.im) →
      segment ℝ b c ⊆ G → HVPathIntegral G f a c (I + segInt f b c)

namespace HVPathIntegral

variable {G : Set ℂ} {f : ℂ → ℂ}

theorem concat {a b c I J : ℂ} (h1 : HVPathIntegral G f a b I) (h2 : HVPathIntegral G f b c J) :
    HVPathIntegral G f a c (I + J) := by
  induction h2 with
  | refl _ => simpa using h1
  | step _ hbc hseg ih =>
    have := ih.step hbc hseg
    rwa [add_assoc] at this

theorem reverse {a b I : ℂ} (h : HVPathIntegral G f a b I) : HVPathIntegral G f b a (-I) := by
  induction h with
  | refl ha => simpa using HVPathIntegral.refl ha
  | @step d e I' _ hde hseg ih =>
    have he : e ∈ G := hseg (right_mem_segment ℝ d e)
    have hed : HVPathIntegral G f e d (0 + segInt f e d) :=
      (HVPathIntegral.refl he).step (hde.imp Eq.symm Eq.symm) (by rw [segment_symm]; exact hseg)
    have := hed.concat ih
    convert this using 1
    rw [segInt_symm]
    ring

theorem exists_of_hvJoined {a b : ℂ} (h : HVJoined G a b) : ∃ I, HVPathIntegral G f a b I := by
  induction h with
  | refl ha => exact ⟨0, HVPathIntegral.refl ha⟩
  | step _ hbc hseg ih =>
    obtain ⟨I, hI⟩ := ih
    exact ⟨_, hI.step hbc hseg⟩

/-- Path independence: if all closed polygonal integrals vanish, the integral along a polygonal
path depends only on its endpoints. -/
theorem unique {a b I J : ℂ}
    (hcl : ∀ a I, HVPathIntegral G f a a I → I = 0)
    (h1 : HVPathIntegral G f a b I) (h2 : HVPathIntegral G f a b J) : I = J := by
  have := hcl a _ (h1.concat h2.reverse)
  linear_combination this

end HVPathIntegral

/-- Closed polygonal integrals vanish implies a potential exists with the stepwise property. -/
theorem exists_stepwise_potential {f : ℂ → ℂ} {G : Set ℂ} (hG : IsOpen G) (hconn : IsPreconnected G)
    {z₀ : ℂ} (hz₀ : z₀ ∈ G) (hcl : ∀ a I, HVPathIntegral G f a a I → I = 0) :
    ∃ F : ℂ → ℂ, ∀ b c, segment ℝ b c ⊆ G → (b.re = c.re ∨ b.im = c.im) →
      F c - F b = segInt f b c := by
  classical
  let F : ℂ → ℂ := fun w => if h : ∃ I, HVPathIntegral G f z₀ w I then h.choose else 0
  have hFspec : ∀ w I, HVPathIntegral G f z₀ w I → F w = I := by
    intro w I hI
    have h : ∃ I, HVPathIntegral G f z₀ w I := ⟨I, hI⟩
    simp only [F, h, ↓reduceDIte]
    exact HVPathIntegral.unique hcl h.choose_spec hI
  refine ⟨F, fun b c hseg hbc => ?_⟩
  have hb : b ∈ G := hseg (left_mem_segment ℝ b c)
  obtain ⟨I, hI⟩ := HVPathIntegral.exists_of_hvJoined (f := f)
    (hvJoined_of_isPreconnected hG hconn hz₀ hb)
  have hc := hI.step hbc hseg
  rw [hFspec b I hI, hFspec c _ hc]
  ring

/-- Beck Theorem 4.2.9 (CX-065). Let `G` be open and connected and `f` continuous on `G`. If the
integral of `f` along every closed polygonal path in `G` (horizontal and vertical segments) is
`0`, then `f` has an antiderivative on `G`. -/
@[kb "beck2025" "Theorem 4.2.9, p. 76"]
theorem exists_antiderivative_of_closed_integrals {f : ℂ → ℂ} {G : Set ℂ} (hG : IsOpen G)
    (hconn : IsPreconnected G) (hf : ContinuousOn f G)
    (hcl : ∀ a I, HVPathIntegral G f a a I → I = 0) :
    ∃ F : ℂ → ℂ, ∀ z ∈ G, HasDerivAt F (f z) z := by
  rcases G.eq_empty_or_nonempty with rfl | ⟨z₀, hz₀⟩
  · exact ⟨0, fun z hz => absurd hz (notMem_empty z)⟩
  obtain ⟨F, hF⟩ := exists_stepwise_potential hG hconn hz₀ hcl
  exact ⟨F, fun z hz => hasDerivAt_of_stepwise hG hf hF hz⟩

/-- Along a polygonal path the integral of a function with an antiderivative is the difference of
the values at the endpoints. -/
theorem HVPathIntegral.eq_sub {f F : ℂ → ℂ} {G : Set ℂ} (hf : ContinuousOn f G)
    (hF : ∀ z ∈ G, HasDerivAt F (f z) z) {a b I : ℂ} (h : HVPathIntegral G f a b I) :
    I = F b - F a := by
  induction h with
  | refl _ => simp
  | @step d e I' _ _ hseg ih =>
    have hs : segInt f d e = F e - F d := by
      have := pathIntegral_eq_sub (f := f) (F := F) (U := G) (γ := segPath d e) (a := 0) (b := 1)
        (isC1On_segPath d e 0 1)
        (fun t ht => by
          rw [uIcc_of_le zero_le_one] at ht
          exact hseg (segPath_mem ht)) hF hf
      rwa [segPath_zero, segPath_one] at this
    rw [ih, hs]
    ring

/-- Beck Corollary 4.2.10 (CX-065). For a continuous `f` on an open connected `G`: `f` has an
antiderivative on `G` if and only if its integral over every closed polygonal path in `G` is `0`. -/
@[kb "beck2025" "Corollary 4.2.10, p. 77"]
theorem hasAntiderivative_iff_closed_integrals_zero {f : ℂ → ℂ} {G : Set ℂ} (hG : IsOpen G)
    (hconn : IsPreconnected G) (hf : ContinuousOn f G) :
    (∃ F : ℂ → ℂ, ∀ z ∈ G, HasDerivAt F (f z) z) ↔
      ∀ a I, HVPathIntegral G f a a I → I = 0 := by
  refine ⟨fun ⟨F, hF⟩ a I h => ?_, exists_antiderivative_of_closed_integrals hG hconn hf⟩
  simpa using h.eq_sub hf hF

/-- Beck Corollary 4.2.10 (CX-065). If `f` has an antiderivative, the integral along a polygonal
path depends only on the endpoints. -/
@[kb "beck2025" "Corollary 4.2.10, p. 77"]
theorem HVPathIntegral.path_independent {f F : ℂ → ℂ} {G : Set ℂ} (hf : ContinuousOn f G)
    (hF : ∀ z ∈ G, HasDerivAt F (f z) z) {a b I J : ℂ} (h1 : HVPathIntegral G f a b I)
    (h2 : HVPathIntegral G f a b J) : I = J := by
  rw [h1.eq_sub hf hF, h2.eq_sub hf hF]

end UndergradKB.ComplexAnalysis
