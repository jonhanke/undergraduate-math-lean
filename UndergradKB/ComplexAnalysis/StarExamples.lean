import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import UndergradKB.ComplexAnalysis.StarPath
import UndergradKB.ComplexAnalysis.ResidueGeneral
import UndergradKB.ComplexAnalysis.HomotopyGeneral

/-!
# Polar paths, ellipses and the residue theorem for convex star-shaped paths

* `polarPath c ρ`: the closed path `t ↦ c + ρ(t) e^{2π i t}` for a positive continuous radius
  function with `ρ 0 = ρ 1` is star-shaped about `c` (`isStarPath_polarPath`).
* `IsStarPath.contractible`: a path on the boundary of a convex set `K ⊆ G` is `G`-contractible.
* `IsStarPath.residue_theorem`, `IsStarPath.cauchy_integral_formula`: the residue theorem 9.2.2 and
  Cauchy's integral formula 4.4.5 for convex star-shaped paths, with no topological assumption.
* `ellipsePath c a b`: the ellipse `((x - x₀)/a)² + ((y - y₀)/b)² = 1` traversed once
  counterclockwise (in polar form about its centre); it is a positively oriented simple closed path
  whose inside is the open elliptical disc (`isPositivelyOrientedSimpleClosed_ellipsePath`,
  `insideOf_ellipsePath`), and Example 4.3.9 (`∫ Log = 0` over an ellipse in `ℂ \ ℝ≤0`).
-/

open Set Metric Complex Filter Topology
open scoped Real

namespace UndergradKB.ComplexAnalysis

/-! ### Polar paths -/

/-- The closed path `t ↦ c + ρ(t) e^{2π i t}` on `[0, 1]`. -/
noncomputable def polarPath (c : ℂ) (ρ : ℝ → ℝ) (t : ℝ) : ℂ := c + ρ t * exp ((2 * π * t : ℝ) * I)

lemma norm_polarPath_sub {c : ℂ} {ρ : ℝ → ℝ} {t : ℝ} (ht : 0 < ρ t) :
    ‖polarPath c ρ t - c‖ = ρ t := by
  rw [polarPath, add_sub_cancel_left, norm_mul, norm_exp_ofReal_mul_I, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos ht, mul_one]

/-- A polar path with a positive continuous radius taking the same value at `0` and `1` is
star-shaped about its centre, with angle `2π t`. -/
theorem isStarPath_polarPath {c : ℂ} {ρ : ℝ → ℝ} (hρ : ContinuousOn ρ (Icc 0 1))
    (hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < ρ t) (h01 : ρ 0 = ρ 1) :
    IsStarPath (polarPath c ρ) c (fun t => 2 * π * t) where
  cont := continuousOn_const.add (ContinuousOn.mul (continuous_ofReal.comp_continuousOn hρ)
    (by fun_prop : Continuous fun t : ℝ => exp ((2 * π * t : ℝ) * I)).continuousOn)
  closed := by
    simp only [polarPath, mul_zero, ofReal_zero, zero_mul, exp_zero, mul_one, h01]
    push_cast
    rw [exp_two_pi_mul_I, mul_one]
  ne := fun t ht e => by
    have := norm_polarPath_sub (c := c) (hpos t ht)
    rw [e, sub_self, norm_zero] at this
    exact (hpos t ht).ne this
  angle_cont := (continuous_const.mul continuous_id).continuousOn
  angle_mono := fun _ _ _ _ hst => by
    simp only
    nlinarith [Real.pi_pos]
  eq_angle := fun t ht => by rw [norm_polarPath_sub (hpos t ht), polarPath]
  angle_one := by ring

/-! ### Contractibility, the residue theorem and Cauchy's formula -/

namespace IsStarPath

variable {γ : ℝ → ℂ} {c : ℂ} {φ : ℝ → ℝ} {K : Set ℂ}

/-- A path in a convex set `K ⊆ G` is `G`-contractible (straight-line homotopy to a point of
`K`). -/
theorem contractible (h : IsStarPath γ c φ) (hK : Convex ℝ K) (hcK : c ∈ K)
    (himK : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ K) {G : Set ℂ} (hKG : K ⊆ G) :
    IsGHomotopic G γ (fun _ => c) := by
  refine ⟨fun t s => (1 - s : ℝ) • γ t + (s : ℝ) • c, ?_, fun t ht s hs => hKG
    (hK (himK t ht) hcK (sub_nonneg.2 hs.2) hs.1 (by ring)), ?_, ?_, ?_⟩
  · refine ContinuousOn.add (ContinuousOn.smul (continuousOn_const.sub continuousOn_snd)
      (h.cont.comp continuousOn_fst (fun q (hq : q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) => hq.1)))
      (continuousOn_snd.smul continuousOn_const)
  · intro t _; simp
  · intro t _; simp
  · intro s _; simp only [h.closed]

open Classical in
/-- **The residue theorem for convex star-shaped paths** (Beck Theorem 9.2.2, with no topological
assumption): if `f` is holomorphic on the open set `G` except at the finitely many points of `S`,
the path `γ` is piecewise smooth, star-shaped about `c`, on the boundary of a convex set
`K ⊆ G` containing `c`, and avoids `S`, then `∫_γ f = 2π i ∑_{s ∈ S, s ∈ interior K} Res_s f`. -/
@[kb "beck2025" "Theorem 9.2.2, p. 154"]
theorem residue_theorem (h : IsStarPath γ c φ) (hs : IsPiecewiseSmooth γ 0 1)
    (hK : Convex ℝ K) (hcK : c ∈ K) (himK : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ K)
    (hint : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∉ interior K) {f : ℂ → ℂ} {G : Set ℂ} (hG : IsOpen G)
    (hKG : K ⊆ G) {S : Finset ℂ} (hf : DifferentiableOn ℂ f (G \ S))
    (hγS : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∉ S) :
    pathIntegral f γ 0 1 = 2 * π * I * ∑ s ∈ S.filter (· ∈ interior K), residue f s := by
  rw [UndergradKB.ComplexAnalysis.residue_theorem hG hf
    (h.isPositivelyOrientedSimpleClosed hs hK hcK himK hint) hγS
    (h.contractible hK hcK himK hKG)]
  congr 2
  ext s
  simp [Finset.mem_filter, h.insideOf_eq_interior hK hcK himK hint]

end IsStarPath

/-! ### Ellipses -/

/-- The radius of the ellipse `(x/a)² + (y/b)² = 1` in the direction `2π t`. -/
noncomputable def ellipseRadius (a b : ℝ) (t : ℝ) : ℝ :=
  a * b / √(b ^ 2 * Real.cos (2 * π * t) ^ 2 + a ^ 2 * Real.sin (2 * π * t) ^ 2)

/-- The ellipse with centre `c` and semi-axes `a` (horizontal) and `b` (vertical), traversed once
counterclockwise from `c + a`, in polar form about the centre. -/
noncomputable def ellipsePath (c : ℂ) (a b : ℝ) : ℝ → ℂ := polarPath c (ellipseRadius a b)

/-- The closed elliptical disc `((x - x₀)/a)² + ((y - y₀)/b)² ≤ 1`. -/
def ellipseDisc (c : ℂ) (a b : ℝ) : Set ℂ := {z | ((z - c).re / a) ^ 2 + ((z - c).im / b) ^ 2 ≤ 1}

/-- The open elliptical disc `((x - x₀)/a)² + ((y - y₀)/b)² < 1`. -/
def ellipseOpenDisc (c : ℂ) (a b : ℝ) : Set ℂ :=
  {z | ((z - c).re / a) ^ 2 + ((z - c).im / b) ^ 2 < 1}

section Ellipse

variable {c : ℂ} {a b : ℝ}

lemma ellipse_denom_pos (ha : 0 < a) (hb : 0 < b) (θ : ℝ) :
    0 < b ^ 2 * Real.cos θ ^ 2 + a ^ 2 * Real.sin θ ^ 2 := by
  rcases eq_or_ne (Real.cos θ) 0 with h | h
  · have : Real.sin θ ^ 2 = 1 := by nlinarith [Real.sin_sq_add_cos_sq θ]
    rw [h, this]; positivity
  · have : 0 < Real.cos θ ^ 2 := by positivity
    positivity

lemma ellipseRadius_pos (ha : 0 < a) (hb : 0 < b) (t : ℝ) : 0 < ellipseRadius a b t := by
  unfold ellipseRadius
  have := ellipse_denom_pos ha hb (2 * π * t)
  positivity

lemma contDiff_ellipseRadius (ha : 0 < a) (hb : 0 < b) :
    ContDiff ℝ 1 (ellipseRadius a b) := by
  unfold ellipseRadius
  refine contDiff_const.div ?_ (fun t => (Real.sqrt_pos.2 (ellipse_denom_pos ha hb _)).ne')
  exact ContDiff.sqrt (by fun_prop) (fun t => (ellipse_denom_pos ha hb _).ne')

lemma ellipseRadius_periodic (t : ℝ) : ellipseRadius a b (t + 1) = ellipseRadius a b t := by
  unfold ellipseRadius
  rw [show 2 * π * (t + 1) = 2 * π * t + 2 * π by ring, Real.cos_add_two_pi, Real.sin_add_two_pi]

lemma ellipsePath_sub (t : ℝ) :
    ellipsePath c a b t - c =
      ⟨ellipseRadius a b t * Real.cos (2 * π * t), ellipseRadius a b t * Real.sin (2 * π * t)⟩ := by
  rw [ellipsePath, polarPath, add_sub_cancel_left]
  apply Complex.ext <;>
    simp only [mul_re, mul_im, ofReal_re, ofReal_im, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im] <;>
    ring

/-- The ellipse path lies on the ellipse. -/
lemma ellipsePath_on_ellipse (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    ((ellipsePath c a b t - c).re / a) ^ 2 + ((ellipsePath c a b t - c).im / b) ^ 2 = 1 := by
  rw [ellipsePath_sub]
  simp only
  have hD := ellipse_denom_pos ha hb (2 * π * t)
  unfold ellipseRadius
  rw [div_pow, div_pow, mul_pow, mul_pow, div_pow, Real.sq_sqrt hD.le]
  field_simp

lemma convex_ellipseDisc : Convex ℝ (ellipseDisc c a b) := by
  intro x hx y hy s t hs ht hst
  simp only [ellipseDisc, Set.mem_ofPred_eq] at hx hy ⊢
  obtain rfl : t = 1 - s := by linarith
  have hre : (s • x + (1 - s) • y - c).re / a =
      s * ((x - c).re / a) + (1 - s) * ((y - c).re / a) := by
    simp only [sub_re, add_re, Complex.real_smul, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    ring
  have him : (s • x + (1 - s) • y - c).im / b =
      s * ((x - c).im / b) + (1 - s) * ((y - c).im / b) := by
    simp only [sub_im, add_im, Complex.real_smul, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
    ring
  rw [hre, him]
  set p := (x - c).re / a
  set q := (y - c).re / a
  set p' := (x - c).im / b
  set q' := (y - c).im / b
  have h1 : (s * p + (1 - s) * q) ^ 2 ≤ s * p ^ 2 + (1 - s) * q ^ 2 := by
    nlinarith [sq_nonneg (p - q), mul_nonneg hs ht]
  have h2 : (s * p' + (1 - s) * q') ^ 2 ≤ s * p' ^ 2 + (1 - s) * q' ^ 2 := by
    nlinarith [sq_nonneg (p' - q'), mul_nonneg hs ht]
  nlinarith

lemma ellipse_scale (k : ℝ) (z : ℂ) :
    ((c + k * (z - c) - c).re / a) ^ 2 + ((c + k * (z - c) - c).im / b) ^ 2 =
      k ^ 2 * (((z - c).re / a) ^ 2 + ((z - c).im / b) ^ 2) := by
  rw [add_sub_cancel_left]
  simp only [mul_re, mul_im, ofReal_re, ofReal_im, zero_mul, sub_zero, add_zero]
  ring

lemma ellipsePath_not_mem_interior (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    ellipsePath c a b t ∉ interior (ellipseDisc c a b) := by
  intro hmem
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hmem)
  set z := ellipsePath c a b t
  have hr := ellipseRadius_pos ha hb t
  have hzc : ‖z - c‖ = ellipseRadius a b t := norm_polarPath_sub hr
  set δ := ε / (2 * ellipseRadius a b t) with hδ
  have hδ0 : 0 < δ := by positivity
  have hmem2 : c + ((1 + δ : ℝ) : ℂ) * (z - c) ∈ ellipseDisc c a b := by
    refine hball (mem_ball.2 ?_)
    rw [dist_eq_norm, show c + ((1 + δ : ℝ) : ℂ) * (z - c) - z = (δ : ℂ) * (z - c) by
      push_cast; ring, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ0, hzc, hδ]
    field_simp
    linarith
  simp only [ellipseDisc, Set.mem_ofPred_eq] at hmem2
  rw [ellipse_scale, ellipsePath_on_ellipse ha hb] at hmem2
  nlinarith

lemma center_mem_ellipseDisc : c ∈ ellipseDisc c a b := by
  simp [ellipseDisc]

lemma isStarPath_ellipsePath (ha : 0 < a) (hb : 0 < b) :
    IsStarPath (ellipsePath c a b) c (fun t => 2 * π * t) :=
  isStarPath_polarPath (contDiff_ellipseRadius ha hb).continuous.continuousOn
    (fun t _ => ellipseRadius_pos ha hb t) (by simpa using (ellipseRadius_periodic (a := a) (b := b) 0).symm)

lemma isPiecewiseSmooth_ellipsePath (ha : 0 < a) (hb : 0 < b) :
    IsPiecewiseSmooth (ellipsePath c a b) 0 1 := by
  have hc : ContDiff ℝ 1 (ellipsePath c a b) := by
    unfold ellipsePath polarPath
    have h1 : ContDiff ℝ 1 (fun t => ((ellipseRadius a b t : ℝ) : ℂ)) :=
      ofRealCLM.contDiff.comp (contDiff_ellipseRadius ha hb)
    have h2 : ContDiff ℝ 1 (fun t : ℝ => exp (((2 * π * t : ℝ) : ℂ) * I)) :=
      Complex.contDiff_exp.comp ((ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).mul
        contDiff_const)
    exact contDiff_const.add (h1.mul h2)
  refine IsC1On.isPiecewiseSmooth ⟨fun t _ => (hc.differentiable (by norm_num)).differentiableAt,
    (hc.continuous_deriv le_rfl).continuousOn⟩ zero_le_one

/-- The interior of the closed elliptical disc is the open elliptical disc. -/
lemma interior_ellipseDisc :
    interior (ellipseDisc c a b) = ellipseOpenDisc c a b := by
  have hcont : Continuous fun z : ℂ => ((z - c).re / a) ^ 2 + ((z - c).im / b) ^ 2 := by
    fun_prop
  refine Subset.antisymm (fun z hz => ?_) (interior_maximal
    (fun z (hz : z ∈ ellipseOpenDisc c a b) => by
      simp only [ellipseOpenDisc, ellipseDisc, Set.mem_ofPred_eq] at hz ⊢; exact hz.le)
    (isOpen_lt hcont continuous_const))
  simp only [ellipseOpenDisc, Set.mem_ofPred_eq]
  refine lt_of_le_of_ne (interior_subset hz) (fun he => ?_)
  -- a point of the ellipse is not interior: push it outward
  have hzc : z ≠ c := by
    rintro rfl
    simp at he
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hz)
  have hn : 0 < ‖z - c‖ := norm_pos_iff.2 (sub_ne_zero.2 hzc)
  set δ := ε / (2 * ‖z - c‖) with hδ
  have hδ0 : 0 < δ := by positivity
  have hmem2 : c + ((1 + δ : ℝ) : ℂ) * (z - c) ∈ ellipseDisc c a b := by
    refine hball (mem_ball.2 ?_)
    rw [dist_eq_norm, show c + ((1 + δ : ℝ) : ℂ) * (z - c) - z = (δ : ℂ) * (z - c) by
      push_cast; ring, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ0, hδ]
    field_simp
    linarith
  simp only [ellipseDisc, Set.mem_ofPred_eq] at hmem2
  rw [ellipse_scale, he] at hmem2
  nlinarith

/-- **Ellipses are positively oriented simple closed paths**, with both fields of
Definition 4.4.4 proved. -/
@[kb "beck2025" "Definition 4.4.4, p. 83"]
theorem isPositivelyOrientedSimpleClosed_ellipsePath (ha : 0 < a) (hb : 0 < b) :
    IsPositivelyOrientedSimpleClosed (ellipsePath c a b) :=
  (isStarPath_ellipsePath ha hb).isPositivelyOrientedSimpleClosed
    (isPiecewiseSmooth_ellipsePath ha hb) (convex_ellipseDisc) center_mem_ellipseDisc
    (fun t _ => le_of_eq (ellipsePath_on_ellipse ha hb t))
    (fun t _ => ellipsePath_not_mem_interior ha hb t)

/-- The inside of the ellipse is the open elliptical disc. -/
@[kb "beck2025" "Jordan curve theorem, §4.4, p. 82"]
theorem insideOf_ellipsePath (ha : 0 < a) (hb : 0 < b) :
    insideOf (ellipsePath c a b) = ellipseOpenDisc c a b := by
  rw [(isStarPath_ellipsePath ha hb).insideOf_eq_interior (convex_ellipseDisc)
    center_mem_ellipseDisc (fun t _ => le_of_eq (ellipsePath_on_ellipse ha hb t))
    (fun t _ => ellipsePath_not_mem_interior ha hb t), interior_ellipseDisc]

/-- An ellipse with `a < Re c` lies in the open right half-plane, hence in `ℂ \ ℝ≤0`. -/
lemma ellipseDisc_subset_slitPlane (ha : 0 < a) (hc : a < c.re) :
    ellipseDisc c a b ⊆ slitPlane := by
  intro z hz
  simp only [ellipseDisc, Set.mem_ofPred_eq] at hz
  rw [mem_slitPlane_iff]
  left
  have h1 : ((z - c).re / a) ^ 2 ≤ 1 := by nlinarith [sq_nonneg ((z - c).im / b)]
  have h2 : |(z - c).re / a| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]; exact h1
  rw [abs_le, le_div_iff₀ ha] at h2
  simp only [sub_re] at h2
  nlinarith [h2.1]

/-- **Example 4.3.9**: `Log` is holomorphic on `ℂ \ ℝ≤0` and an ellipse in the right half-plane is
contractible there, so `∫_γ Log z dz = 0`. -/
@[kb "beck2025" "Example 4.3.9, p. 80"]
theorem example_4_3_9 (ha : 0 < a) (hb : 0 < b) (hc : a < c.re) :
    pathIntegral log (ellipsePath c a b) 0 1 = 0 :=
  pathIntegral_eq_zero_of_contractible isOpen_slitPlane
    (fun _ hz => (differentiableAt_log hz).differentiableWithinAt)
    (isPiecewiseSmooth_ellipsePath ha hb)
    ((isStarPath_ellipsePath ha hb).contractible (convex_ellipseDisc) center_mem_ellipseDisc
      (fun t _ => le_of_eq (ellipsePath_on_ellipse ha hb t))
      (ellipseDisc_subset_slitPlane ha hc))

end Ellipse

end UndergradKB.ComplexAnalysis
