import Mathlib.Analysis.Complex.ReImTopology
import UndergradKB.ComplexAnalysis.CauchyFormula
import UndergradKB.ComplexAnalysis.Primitive

/-!
# Rectangles are positively oriented simple closed paths

Beck et al. integrate over rectangles throughout (Section 10.1 uses the rectangles `γ_N`). The
residue theorem 9.2.2 and Cauchy's integral formula 4.4.5 (`ResidueGeneral.lean`,
`CauchyFormula.lean`) are stated for paths satisfying `IsPositivelyOrientedSimpleClosed`, whose
fields `inside_nonempty` and `annulus` record the topology the book assumes in Section 4.4 (the
Jordan curve and annulus theorems). Here these fields are *proved* for the boundary of every
rectangle `[x₀, x₁] × [y₀, y₁]`, traversed counterclockwise:

* `insideOf_rectPath`: the inside of the rectangular path is the open rectangle;
* `isGHomotopic_circlePath_of_angle`: a closed path in a convex set `K` with a continuous angle
  function about `w` that increases by `2π` is homotopic to the circle `C[w, R]` inside `K` minus
  the open disc (radial projection to the circle, then a homotopy on the circle);
* `isPositivelyOrientedSimpleClosed_rectPath`: the rectangle satisfies the structure, so the
  residue theorem holds for rectangles unconditionally.
-/

open Set Metric Complex Filter Topology
open scoped Real

namespace UndergradKB.ComplexAnalysis

/-! ### The annulus homotopy from an angle function -/

/-- If the closed path `γ` lies in the convex set `K`, keeps distance at least `R > 0` from `w`, the
closed disc `D[w, R]` lies in `K`, and `γ t = w + |γ t - w| e^{i θ(t)}` with a continuous angle `θ`
that increases by `2π` from `t = 0` to `t = 1`, then `γ` is homotopic to the counterclockwise
circle `C[w, R]` within `K` minus the open disc `D(w, R)`. -/
theorem isGHomotopic_circlePath_of_angle {K : Set ℂ} (hK : Convex ℝ K) {γ : ℝ → ℂ}
    (hγ : ContinuousOn γ (Icc 0 1)) (hcl : γ 0 = γ 1) {w : ℂ} {R : ℝ} (hR : 0 < R)
    (hball : closedBall w R ⊆ K) (hγK : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ K)
    (hγR : ∀ t ∈ Icc (0 : ℝ) 1, R ≤ ‖γ t - w‖) {θ : ℝ → ℝ} (hθ : ContinuousOn θ (Icc 0 1))
    (hθγ : ∀ t ∈ Icc (0 : ℝ) 1, γ t = w + ‖γ t - w‖ * exp (θ t * I))
    (hθ1 : θ 1 = θ 0 + 2 * π) :
    IsGHomotopic (K \ ball w R) γ (circlePath w R) := by
  have hθc : ContinuousOn (fun q : ℝ × ℝ => θ q.1) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    hθ.comp continuousOn_fst (fun q hq => hq.1)
  have hnorm : ∀ x : ℝ, ‖exp (x * I)‖ = 1 := fun x => norm_exp_ofReal_mul_I x
  have hsph : ∀ x : ℝ, w + (R : ℂ) * exp (x * I) ∈ K \ ball w R := by
    intro x
    have hd : dist (w + (R : ℂ) * exp (x * I)) w = R := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_mul, hnorm, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hR, mul_one]
    refine ⟨hball (mem_closedBall.2 hd.le), fun h => ?_⟩
    have := mem_ball.1 h
    linarith
  -- first stage: radial projection of `γ` to the circle
  have h1 : IsGHomotopic (K \ ball w R) γ (fun t => w + (R : ℂ) * exp (θ t * I)) := by
    refine ⟨fun t s => w + (((1 - s) * ‖γ t - w‖ + s * R : ℝ) : ℂ) * exp (θ t * I), ?_, ?_, ?_,
      ?_, ?_⟩
    · have hn : ContinuousOn (fun q : ℝ × ℝ => ‖γ q.1 - w‖) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
        ((hγ.comp continuousOn_fst (fun q (hq : q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) => hq.1)).sub
          continuousOn_const).norm
      have he : ContinuousOn (fun q : ℝ × ℝ => exp (θ q.1 * I)) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
        Complex.continuous_exp.comp_continuousOn
          ((continuous_ofReal.comp_continuousOn hθc).mul continuousOn_const)
      refine continuousOn_const.add (ContinuousOn.mul ?_ he)
      exact continuous_ofReal.comp_continuousOn
        (((continuousOn_const.sub continuousOn_snd).mul hn).add
          (continuousOn_snd.mul continuousOn_const))
    · intro t ht s hs
      have hγt := hθγ t ht
      refine ⟨?_, ?_⟩
      · have hp := (hsph (θ t)).1
        have := hK (hγK t ht) hp (sub_nonneg.2 hs.2) hs.1 (by ring)
        convert this using 1
        rw [Complex.real_smul, Complex.real_smul]
        conv_rhs => rw [hγt]
        push_cast; ring
      · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, hnorm, mul_one,
          Complex.norm_real, Real.norm_eq_abs, not_lt]
        have := hγR t ht
        rw [abs_of_nonneg (by nlinarith [hs.1, hs.2])]
        nlinarith [hs.1, hs.2]
    · intro t ht
      simp only [sub_zero, one_mul, zero_mul, add_zero]
      exact (hθγ t ht).symm
    · intro t _
      simp
    · intro s _
      simp only
      rw [hθ1, ← hcl]
      congr 2
      push_cast
      rw [add_mul, exp_add, show (2 * (π : ℂ)) * I = 2 * π * I by ring, exp_two_pi_mul_I, mul_one]
  -- second stage: on the circle, from the angle `θ` to the angle `2πt`
  have h2 : IsGHomotopic (K \ ball w R) (fun t => w + (R : ℂ) * exp (θ t * I))
      (circlePath w R) := by
    refine ⟨fun t s => w + (R : ℂ) * exp ((((1 - s) * θ t + s * (2 * π * t)) : ℝ) * I), ?_,
      fun t _ s _ => hsph _, ?_, ?_, ?_⟩
    · refine continuousOn_const.add (continuousOn_const.mul ?_)
      refine Complex.continuous_exp.comp_continuousOn
        ((continuous_ofReal.comp_continuousOn ?_).mul continuousOn_const)
      exact ((continuousOn_const.sub continuousOn_snd).mul hθc).add
        (continuousOn_snd.mul (continuous_const.mul continuous_fst).continuousOn)
    · intro t _; simp
    · intro t _; simp [circlePath_eq]
    · intro s _
      simp only [mul_zero, add_zero, mul_one]
      rw [hθ1]
      congr 2
      push_cast
      rw [show ((1 - (s : ℂ)) * (θ 0 + 2 * π) + s * (2 * π)) * I
          = (1 - s) * θ 0 * I + 2 * π * I by ring, exp_add, exp_two_pi_mul_I, mul_one]
  exact h1.trans h2

/-! ### Unbounded components -/

/-- If the whole ray `z + u d` (`u ≥ 0`, `d ≠ 0`) avoids `S`, the component of `z` in the
complement of `S` is unbounded. -/
lemma not_isBounded_connectedComponentIn_of_ray {S : Set ℂ} {z d : ℂ} (hd : d ≠ 0)
    (h : ∀ u : ℝ, 0 ≤ u → z + u * d ∉ S) :
    ¬ Bornology.IsBounded (connectedComponentIn Sᶜ z) := by
  intro hb
  have hsub : (fun u : ℝ => z + u * d) '' Ici 0 ⊆ connectedComponentIn Sᶜ z :=
    (isPreconnected_Ici.image _ (by fun_prop : Continuous fun u : ℝ => z + u * d).continuousOn
      ).subset_connectedComponentIn ⟨0, self_mem_Ici, by simp⟩
      (by rintro _ ⟨u, hu, rfl⟩; exact h u hu)
  obtain ⟨M, hM⟩ := hb.subset_closedBall 0
  have hdn : 0 < ‖d‖ := norm_pos_iff.2 hd
  set u : ℝ := (|M| + ‖z‖ + 1) / ‖d‖ with hu
  have hu0 : 0 ≤ u := by positivity
  have hmem := hM (hsub ⟨u, hu0, rfl⟩)
  rw [mem_closedBall, dist_zero_right] at hmem
  have h2 : ‖(u : ℂ) * d‖ = |M| + ‖z‖ + 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0, hu]
    field_simp
  have h3 : ‖(u : ℂ) * d‖ ≤ ‖z + u * d‖ + ‖z‖ := by
    have := norm_sub_le (z + u * d) z
    rwa [add_sub_cancel_left] at this
  linarith [le_abs_self M]

/-! ### The rectangular path -/

/-- The boundary of the rectangle `[x₀, x₁] × [y₀, y₁]`, counterclockwise from the corner
`x₁ + i y₀`: up the right side, left along the top, down the left side and right along the bottom
(each side on a quarter of `[0, 1]`). For `x₀ = -(N + 1/2)`, `x₁ = N + 1/2`, `y₀ = -N`, `y₁ = N`
this is Beck's path `γ_N` of Section 10.1. -/
noncomputable def rectPath (x₀ x₁ y₀ y₁ : ℝ) : ℝ → ℂ :=
  pathConcat (pathConcat (segPath ⟨x₁, y₀⟩ ⟨x₁, y₁⟩) (segPath ⟨x₁, y₁⟩ ⟨x₀, y₁⟩))
    (pathConcat (segPath ⟨x₀, y₁⟩ ⟨x₀, y₀⟩) (segPath ⟨x₀, y₀⟩ ⟨x₁, y₀⟩))

variable {x₀ x₁ y₀ y₁ : ℝ}

lemma rectPath_q1 {t : ℝ} (h : t ≤ 1 / 4) :
    rectPath x₀ x₁ y₀ y₁ t = ⟨x₁, y₀ + 4 * t * (y₁ - y₀)⟩ := by
  unfold rectPath
  rw [pathConcat_of_le (by linarith), pathConcat_of_le (by linarith)]
  apply Complex.ext <;> simp [segPath] <;> ring_nf <;> simp

lemma rectPath_q2 {t : ℝ} (h1 : 1 / 4 < t) (h2 : t ≤ 1 / 2) :
    rectPath x₀ x₁ y₀ y₁ t = ⟨x₁ - (4 * t - 1) * (x₁ - x₀), y₁⟩ := by
  unfold rectPath
  rw [pathConcat_of_le h2, pathConcat_of_lt (by linarith)]
  apply Complex.ext <;> simp [segPath] <;> ring_nf <;> simp

lemma rectPath_q3 {t : ℝ} (h1 : 1 / 2 < t) (h2 : t ≤ 3 / 4) :
    rectPath x₀ x₁ y₀ y₁ t = ⟨x₀, y₁ - (4 * t - 2) * (y₁ - y₀)⟩ := by
  unfold rectPath
  rw [pathConcat_of_lt h1, pathConcat_of_le (by linarith)]
  apply Complex.ext <;> simp [segPath] <;> ring_nf <;> simp

lemma rectPath_q4 {t : ℝ} (h1 : 3 / 4 < t) :
    rectPath x₀ x₁ y₀ y₁ t = ⟨x₀ + (4 * t - 3) * (x₁ - x₀), y₀⟩ := by
  unfold rectPath
  rw [pathConcat_of_lt (by linarith), pathConcat_of_lt (by linarith)]
  apply Complex.ext <;> simp [segPath] <;> ring_nf <;> simp

lemma rectPath_zero : rectPath x₀ x₁ y₀ y₁ 0 = ⟨x₁, y₀⟩ := by
  rw [rectPath_q1 (by norm_num)]; simp

lemma rectPath_one : rectPath x₀ x₁ y₀ y₁ 1 = ⟨x₁, y₀⟩ := by
  rw [rectPath_q4 (by norm_num)]; apply Complex.ext <;> simp; ring

lemma rectPath_half : rectPath x₀ x₁ y₀ y₁ (1 / 2) = ⟨x₀, y₁⟩ := by
  rw [rectPath_q2 (by norm_num) le_rfl]; apply Complex.ext <;> simp; ring

/-- The four sides, by the quarter of `[0, 1]` the parameter lies in. -/
lemma rectPath_cases {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (0 ≤ t ∧ t ≤ 1 / 4 ∧ rectPath x₀ x₁ y₀ y₁ t = ⟨x₁, y₀ + 4 * t * (y₁ - y₀)⟩) ∨
    (1 / 4 < t ∧ t ≤ 1 / 2 ∧ rectPath x₀ x₁ y₀ y₁ t = ⟨x₁ - (4 * t - 1) * (x₁ - x₀), y₁⟩) ∨
    (1 / 2 < t ∧ t ≤ 3 / 4 ∧ rectPath x₀ x₁ y₀ y₁ t = ⟨x₀, y₁ - (4 * t - 2) * (y₁ - y₀)⟩) ∨
    (3 / 4 < t ∧ t ≤ 1 ∧ rectPath x₀ x₁ y₀ y₁ t = ⟨x₀ + (4 * t - 3) * (x₁ - x₀), y₀⟩) := by
  rcases le_or_gt t (1 / 4) with h1 | h1
  · exact Or.inl ⟨ht.1, h1, rectPath_q1 h1⟩
  rcases le_or_gt t (1 / 2) with h2 | h2
  · exact Or.inr (Or.inl ⟨h1, h2, rectPath_q2 h1 h2⟩)
  rcases le_or_gt t (3 / 4) with h3 | h3
  · exact Or.inr (Or.inr (Or.inl ⟨h2, h3, rectPath_q3 h2 h3⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h3, ht.2, rectPath_q4 h3⟩))

lemma isPiecewiseSmooth_rectPath : IsPiecewiseSmooth (rectPath x₀ x₁ y₀ y₁) 0 1 := by
  have hs : ∀ b c : ℂ, IsPiecewiseSmooth (segPath b c) 0 1 := fun b c =>
    (isC1On_segPath b c 0 1).isPiecewiseSmooth zero_le_one
  refine ((hs _ _).pathConcat (hs _ _) ?_).pathConcat ((hs _ _).pathConcat (hs _ _) ?_) ?_
  · rw [segPath_one, segPath_zero]
  · rw [segPath_one, segPath_zero]
  · rw [pathConcat_one, pathConcat_zero, segPath_one, segPath_zero]

/-- The closed rectangle `[x₀, x₁] × [y₀, y₁]`. -/
abbrev closedRect (x₀ x₁ y₀ y₁ : ℝ) : Set ℂ := Icc x₀ x₁ ×ℂ Icc y₀ y₁

/-- The open rectangle `(x₀, x₁) × (y₀, y₁)`. -/
abbrev openRect (x₀ x₁ y₀ y₁ : ℝ) : Set ℂ := Ioo x₀ x₁ ×ℂ Ioo y₀ y₁

/-- The rectangular path runs along the boundary of the rectangle. -/
lemma rectPath_mem_boundary (hx : x₀ < x₁) (hy : y₀ < y₁) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    rectPath x₀ x₁ y₀ y₁ t ∈ closedRect x₀ x₁ y₀ y₁ ∧
      rectPath x₀ x₁ y₀ y₁ t ∉ openRect x₀ x₁ y₀ y₁ := by
  simp only [mem_reProdIm, mem_Icc, mem_Ioo]
  rcases rectPath_cases (x₀ := x₀) (x₁ := x₁) (y₀ := y₀) (y₁ := y₁) ht with
    ⟨a, b, e⟩ | ⟨a, b, e⟩ | ⟨a, b, e⟩ | ⟨a, b, e⟩ <;> rw [e] <;>
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩ <;> simp <;> nlinarith

/-- Every boundary point of the rectangle is on the path. -/
lemma mem_pathImage_rectPath (hx : x₀ < x₁) (hy : y₀ < y₁) {z : ℂ}
    (hz : z ∈ closedRect x₀ x₁ y₀ y₁) (hz' : z ∉ openRect x₀ x₁ y₀ y₁) :
    z ∈ pathImage (rectPath x₀ x₁ y₀ y₁) := by
  simp only [mem_reProdIm, mem_Icc, mem_Ioo, not_and_or, not_lt] at hz hz'
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
  have hdx : 0 < x₁ - x₀ := sub_pos.2 hx
  have hdy : 0 < y₁ - y₀ := sub_pos.2 hy
  by_cases e1 : z.re = x₁
  · refine ⟨(z.im - y₀) / (4 * (y₁ - y₀)), ⟨div_nonneg (by linarith) (by positivity), ?_⟩, ?_⟩
    · rw [div_le_one (by positivity)]; linarith
    · rw [rectPath_q1 (by rw [div_le_iff₀ (by positivity)]; linarith)]
      apply Complex.ext <;> simp [e1]; field_simp; ring
  by_cases e2 : z.im = y₁
  · have hr : z.re < x₁ := lt_of_le_of_ne h2 e1
    have hp : 0 < (x₁ - z.re) / (4 * (x₁ - x₀)) := div_pos (by linarith) (by positivity)
    have hq : (x₁ - z.re) / (4 * (x₁ - x₀)) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    refine ⟨1 / 4 + (x₁ - z.re) / (4 * (x₁ - x₀)), ⟨by linarith, by linarith⟩, ?_⟩
    rw [rectPath_q2 (by linarith) (by linarith)]
    apply Complex.ext <;> simp [e2]; field_simp; ring
  by_cases e3 : z.re = x₀
  · have hi : z.im < y₁ := lt_of_le_of_ne h4 e2
    have hp : 0 < (y₁ - z.im) / (4 * (y₁ - y₀)) := div_pos (by linarith) (by positivity)
    have hq : (y₁ - z.im) / (4 * (y₁ - y₀)) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    refine ⟨1 / 2 + (y₁ - z.im) / (4 * (y₁ - y₀)), ⟨by linarith, by linarith⟩, ?_⟩
    rw [rectPath_q3 (by linarith) (by linarith)]
    apply Complex.ext <;> simp [e3]; field_simp; ring
  · have e4 : z.im = y₀ := by
      rcases hz' with (h | h) | (h | h)
      · exact absurd (le_antisymm h h1) e3
      · exact absurd (le_antisymm h2 h) e1
      · exact le_antisymm h h3
      · exact absurd (le_antisymm h4 h) e2
    have hr : x₀ < z.re := lt_of_le_of_ne h1 (Ne.symm e3)
    have hr' : z.re < x₁ := lt_of_le_of_ne h2 e1
    have hp : 0 < (z.re - x₀) / (4 * (x₁ - x₀)) := div_pos (by linarith) (by positivity)
    have hq : (z.re - x₀) / (4 * (x₁ - x₀)) < 1 / 4 := by
      rw [div_lt_iff₀ (by positivity)]; linarith
    refine ⟨3 / 4 + (z.re - x₀) / (4 * (x₁ - x₀)), ⟨by linarith, by linarith⟩, ?_⟩
    rw [rectPath_q4 (by linarith)]
    apply Complex.ext <;> simp [e4]; field_simp; ring

/-- The rectangular path is simple: injective on `[0, 1)`. -/
lemma rectPath_injOn (hx : x₀ < x₁) (hy : y₀ < y₁) :
    InjOn (rectPath x₀ x₁ y₀ y₁) (Ico 0 1) := by
  intro s hs t ht hst
  have hdx : 0 < x₁ - x₀ := sub_pos.2 hx
  have hdy : 0 < y₁ - y₀ := sub_pos.2 hy
  have hs1 := hs.2
  have ht1 := ht.2
  rcases rectPath_cases (x₀ := x₀) (x₁ := x₁) (y₀ := y₀) (y₁ := y₁) (Ico_subset_Icc_self hs) with
    ⟨a, b, e⟩ | ⟨a, b, e⟩ | ⟨a, b, e⟩ | ⟨a, b, e⟩ <;>
  rcases rectPath_cases (x₀ := x₀) (x₁ := x₁) (y₀ := y₀) (y₁ := y₁) (Ico_subset_Icc_self ht) with
    ⟨c, d, f⟩ | ⟨c, d, f⟩ | ⟨c, d, f⟩ | ⟨c, d, f⟩ <;>
  rw [e, f, Complex.mk.injEq] at hst <;> obtain ⟨h1, h2⟩ := hst <;> nlinarith

/-- The inside of the rectangular path is the open rectangle. -/
theorem insideOf_rectPath (hx : x₀ < x₁) (hy : y₀ < y₁) :
    insideOf (rectPath x₀ x₁ y₀ y₁) = openRect x₀ x₁ y₀ y₁ := by
  have himg : pathImage (rectPath x₀ x₁ y₀ y₁) ⊆
      closedRect x₀ x₁ y₀ y₁ \ openRect x₀ x₁ y₀ y₁ := by
    rintro _ ⟨t, ht, rfl⟩
    exact rectPath_mem_boundary hx hy ht
  have hsub : openRect x₀ x₁ y₀ y₁ ⊆ closedRect x₀ x₁ y₀ y₁ := by
    intro z hz
    simp only [mem_reProdIm, mem_Icc, mem_Ioo] at hz ⊢
    exact ⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2.1.le, hz.2.2.le⟩
  ext z
  constructor
  · rintro ⟨hz, hb⟩
    by_contra hzo
    refine hz (mem_pathImage_rectPath hx hy ?_ hzo)
    by_contra hzc
    simp only [mem_reProdIm, mem_Icc, not_and_or, not_le] at hzc
    have hray : ∀ d : ℂ, d ≠ 0 → (∀ u : ℝ, 0 ≤ u → z + u * d ∉ closedRect x₀ x₁ y₀ y₁) →
        False := fun d hd h => not_isBounded_connectedComponentIn_of_ray hd
          (fun u hu hmem => h u hu ((himg hmem).1)) hb
    rcases hzc with (h | h) | (h | h)
    · refine hray (-1) (by norm_num) fun u hu hm => ?_
      simp only [mem_reProdIm, mem_Icc] at hm
      have := hm.1.1; simp at this; linarith
    · refine hray 1 one_ne_zero fun u hu hm => ?_
      simp only [mem_reProdIm, mem_Icc] at hm
      have := hm.1.2; simp at this; linarith
    · refine hray (-I) (by simp) fun u hu hm => ?_
      simp only [mem_reProdIm, mem_Icc] at hm
      have := hm.2.1; simp at this; linarith
    · refine hray I I_ne_zero fun u hu hm => ?_
      simp only [mem_reProdIm, mem_Icc] at hm
      have := hm.2.2; simp at this; linarith
  · intro hz
    have hz' : z ∉ pathImage (rectPath x₀ x₁ y₀ y₁) := fun h => (himg h).2 hz
    refine ⟨hz', ?_⟩
    have hcomp : connectedComponentIn (pathImage (rectPath x₀ x₁ y₀ y₁))ᶜ z ⊆
        openRect x₀ x₁ y₀ y₁ := by
      refine (isPreconnected_connectedComponentIn).subset_of_closure_inter_subset
        (isOpen_Ioo.reProdIm isOpen_Ioo) ⟨z, mem_connectedComponentIn hz', hz⟩ ?_
      rintro y ⟨hy1, hy2⟩
      have hyc : y ∈ closedRect x₀ x₁ y₀ y₁ :=
        closure_minimal hsub (isClosed_Icc.reProdIm isClosed_Icc) hy1
      by_contra hyo
      exact connectedComponentIn_subset _ _ hy2 (mem_pathImage_rectPath hx hy hyc hyo)
    exact ((isCompact_Icc.reProdIm isCompact_Icc).isBounded.subset hsub).subset hcomp

/-! ### The angle function about a point inside -/

/-- An angle of `rectPath t - w` (for `w` inside): the principal argument on the right side and
the top, and `arg (-(rectPath t - w)) + π` on the left side and the bottom. -/
noncomputable def rectAngle (x₀ x₁ y₀ y₁ : ℝ) (w : ℂ) (t : ℝ) : ℝ :=
  if t ≤ 1 / 2 then arg (rectPath x₀ x₁ y₀ y₁ t - w)
  else arg (-(rectPath x₀ x₁ y₀ y₁ t - w)) + π

lemma rectPath_sub_mem_slitPlane {w : ℂ} (hw : w ∈ openRect x₀ x₁ y₀ y₁) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (1 / 2)) : rectPath x₀ x₁ y₀ y₁ t - w ∈ slitPlane := by
  simp only [mem_reProdIm, mem_Ioo] at hw
  rw [mem_slitPlane_iff]
  rcases le_or_gt t (1 / 4) with h | h
  · left; rw [rectPath_q1 h]; simp; linarith [hw.1.2]
  · right; rw [rectPath_q2 h ht.2]; simp; linarith [hw.2.2]

lemma neg_rectPath_sub_mem_slitPlane {w : ℂ} (hw : w ∈ openRect x₀ x₁ y₀ y₁) {t : ℝ}
    (ht : t ∈ Icc (1 / 2 : ℝ) 1) : -(rectPath x₀ x₁ y₀ y₁ t - w) ∈ slitPlane := by
  simp only [mem_reProdIm, mem_Ioo] at hw
  rw [mem_slitPlane_iff]
  rcases eq_or_lt_of_le ht.1 with h | h
  · left; rw [← h, rectPath_half]; simp; linarith [hw.1.1]
  rcases le_or_gt t (3 / 4) with h' | h'
  · left; rw [rectPath_q3 h h']; simp; linarith [hw.1.1]
  · right; rw [rectPath_q4 h']; simp; linarith [hw.2.1]

lemma continuousOn_rectAngle {w : ℂ} (hw : w ∈ openRect x₀ x₁ y₀ y₁) :
    ContinuousOn (rectAngle x₀ x₁ y₀ y₁ w) (Icc 0 1) := by
  have hc : ContinuousOn (fun t => rectPath x₀ x₁ y₀ y₁ t - w) (Icc 0 1) :=
    isPiecewiseSmooth_rectPath.continuousOn.sub continuousOn_const
  have hL : ContinuousOn (rectAngle x₀ x₁ y₀ y₁ w) (Icc 0 (1 / 2)) := by
    have : ContinuousOn (fun t => arg (rectPath x₀ x₁ y₀ y₁ t - w)) (Icc 0 (1 / 2)) := by
      intro t ht
      exact ContinuousAt.comp_continuousWithinAt (f := fun t => rectPath x₀ x₁ y₀ y₁ t - w)
        (continuousAt_arg (rectPath_sub_mem_slitPlane hw ht))
        ((hc t ⟨ht.1, by linarith [ht.2]⟩).mono (Icc_subset_Icc le_rfl (by norm_num)))
    exact this.congr fun t ht => if_pos ht.2
  have hR : ContinuousOn (rectAngle x₀ x₁ y₀ y₁ w) (Icc (1 / 2) 1) := by
    have : ContinuousOn (fun t => arg (-(rectPath x₀ x₁ y₀ y₁ t - w)) + π) (Icc (1 / 2) 1) := by
      refine ContinuousOn.add (fun t ht => ?_) continuousOn_const
      exact ContinuousAt.comp_continuousWithinAt (f := fun t => -(rectPath x₀ x₁ y₀ y₁ t - w))
        (continuousAt_arg (neg_rectPath_sub_mem_slitPlane hw ht))
        ((hc t ⟨by linarith [ht.1], ht.2⟩).neg.mono (Icc_subset_Icc (by norm_num) le_rfl))
    refine this.congr fun t ht => ?_
    rcases eq_or_lt_of_le ht.1 with h | h
    · subst h
      simp only [rectAngle, le_refl, if_true]
      have him : 0 < (rectPath x₀ x₁ y₀ y₁ (1 / 2) - w).im := by
        simp only [mem_reProdIm, mem_Ioo] at hw
        rw [rectPath_half]; simp; linarith [hw.2.2]
      rw [arg_neg_eq_arg_sub_pi_of_im_pos him]; ring
    · simp only [rectAngle, if_neg (not_le.2 h)]
  have hU : Icc (0 : ℝ) 1 = Icc 0 (1 / 2) ∪ Icc (1 / 2) 1 :=
    (Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)).symm
  rw [hU]
  exact hL.union_of_isClosed hR isClosed_Icc isClosed_Icc

lemma rectPath_eq_angle (w : ℂ) (t : ℝ) :
    rectPath x₀ x₁ y₀ y₁ t =
      w + ‖rectPath x₀ x₁ y₀ y₁ t - w‖ * exp (rectAngle x₀ x₁ y₀ y₁ w t * I) := by
  set z := rectPath x₀ x₁ y₀ y₁ t - w with hz
  have key : (‖z‖ : ℂ) * exp (rectAngle x₀ x₁ y₀ y₁ w t * I) = z := by
    unfold rectAngle
    split_ifs
    · exact norm_mul_exp_arg_mul_I z
    · have h := norm_mul_exp_arg_mul_I (-z)
      rw [norm_neg] at h
      push_cast
      rw [add_mul, exp_add, exp_pi_mul_I, ← mul_assoc, h]
      ring
  rw [key, hz]; ring

lemma rectAngle_one {w : ℂ} (hw : w ∈ openRect x₀ x₁ y₀ y₁) :
    rectAngle x₀ x₁ y₀ y₁ w 1 = rectAngle x₀ x₁ y₀ y₁ w 0 + 2 * π := by
  have him : (rectPath x₀ x₁ y₀ y₁ 0 - w).im < 0 := by
    simp only [mem_reProdIm, mem_Ioo] at hw
    rw [rectPath_zero]; simp; linarith [hw.2.1]
  simp only [rectAngle, show ¬ (1 : ℝ) ≤ 1 / 2 by norm_num, if_false,
    show (0 : ℝ) ≤ 1 / 2 by norm_num, if_true]
  rw [rectPath_one, ← rectPath_zero (x₀ := x₀) (y₁ := y₁), arg_neg_eq_arg_add_pi_of_im_neg him]
  ring

/-- The closed rectangle is convex. -/
lemma convex_closedRect : Convex ℝ (closedRect x₀ x₁ y₀ y₁) := by
  intro a ha b hb s t hs ht hst
  simp only [mem_reProdIm, mem_Icc] at ha hb ⊢
  simp only [add_re, add_im, Complex.real_smul, mul_re, mul_im, ofReal_re, ofReal_im, zero_mul,
    sub_zero, add_zero]
  have e1 := mul_le_mul_of_nonneg_left ha.1.1 hs
  have e2 := mul_le_mul_of_nonneg_left ha.1.2 hs
  have e3 := mul_le_mul_of_nonneg_left ha.2.1 hs
  have e4 := mul_le_mul_of_nonneg_left ha.2.2 hs
  have f1 := mul_le_mul_of_nonneg_left hb.1.1 ht
  have f2 := mul_le_mul_of_nonneg_left hb.1.2 ht
  have f3 := mul_le_mul_of_nonneg_left hb.2.1 ht
  have f4 := mul_le_mul_of_nonneg_left hb.2.2 ht
  have g : t = 1 - s := by linarith
  subst g
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith

/-- **Rectangles are positively oriented simple closed paths.** The boundary of the rectangle
`[x₀, x₁] × [y₀, y₁]` traversed counterclockwise satisfies `IsPositivelyOrientedSimpleClosed`
(Definition 4.4.4): its inside is the open rectangle (`insideOf_rectPath`), and the annulus
homotopy to a circle about any closed disc inside is built from the angle `rectAngle`. So the
topology the book assumes in Section 4.4 is proved for rectangles. -/
@[kb "beck2025" "Definition 4.4.4, p. 83"]
theorem isPositivelyOrientedSimpleClosed_rectPath (hx : x₀ < x₁) (hy : y₀ < y₁) :
    IsPositivelyOrientedSimpleClosed (rectPath x₀ x₁ y₀ y₁) where
  smooth := isPiecewiseSmooth_rectPath
  closed := by rw [rectPath_zero, rectPath_one]
  simple := rectPath_injOn hx hy
  inside_nonempty := by
    refine ⟨⟨(x₀ + x₁) / 2, (y₀ + y₁) / 2⟩, ?_⟩
    rw [insideOf_rectPath hx hy]
    simp only [mem_reProdIm, mem_Ioo]
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  annulus := by
    intro w R hR hsub
    rw [insideOf_rectPath hx hy] at hsub
    have hw : w ∈ openRect x₀ x₁ y₀ y₁ := hsub (mem_closedBall_self hR.le)
    have hsub' : openRect x₀ x₁ y₀ y₁ ⊆ closedRect x₀ x₁ y₀ y₁ := by
      intro z hz
      simp only [mem_reProdIm, mem_Icc, mem_Ioo] at hz ⊢
      exact ⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2.1.le, hz.2.2.le⟩
    have H := isGHomotopic_circlePath_of_angle (K := closedRect x₀ x₁ y₀ y₁) convex_closedRect
      isPiecewiseSmooth_rectPath.continuousOn (by rw [rectPath_zero, rectPath_one]) hR
      (hsub.trans hsub') (fun t ht => (rectPath_mem_boundary hx hy ht).1)
      (fun t ht => by
        by_contra h
        refine (rectPath_mem_boundary hx hy ht).2 (hsub ?_)
        rw [mem_closedBall, dist_eq_norm]
        exact (lt_of_not_ge h).le)
      (continuousOn_rectAngle hw) (fun t _ => rectPath_eq_angle w t) (rectAngle_one hw)
    refine H.mono ?_
    rintro z ⟨hz, hzb⟩
    refine ⟨?_, hzb⟩
    rw [insideOf_rectPath hx hy]
    by_cases ho : z ∈ openRect x₀ x₁ y₀ y₁
    · exact Or.inl ho
    · exact Or.inr (mem_pathImage_rectPath hx hy hz ho)

/-! ### Integrals along the rectangle -/

lemma image_subset_pathConcat_left {γ₁ γ₂ : ℝ → ℂ} :
    γ₁ '' Icc 0 1 ⊆ pathConcat γ₁ γ₂ '' Icc 0 1 := by
  rintro _ ⟨t, ht, rfl⟩
  refine ⟨t / 2, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
  rw [pathConcat_of_le (by linarith [ht.2])]
  congr 1; ring

lemma image_subset_pathConcat_right {γ₁ γ₂ : ℝ → ℂ} (h : γ₁ 1 = γ₂ 0) :
    γ₂ '' Icc 0 1 ⊆ pathConcat γ₁ γ₂ '' Icc 0 1 := by
  rintro _ ⟨t, ht, rfl⟩
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
    rw [pathConcat_of_le le_rfl, ← h0, ← h]; norm_num
  · refine ⟨(t + 1) / 2, ⟨by linarith, by linarith [ht.2]⟩, ?_⟩
    rw [pathConcat_of_lt (by linarith)]
    congr 1; ring

/-- The integral along the rectangle is the sum of the integrals along its four sides. -/
lemma pathIntegral_rectPath {f : ℂ → ℂ}
    (hf : ContinuousOn f (pathImage (rectPath x₀ x₁ y₀ y₁))) :
    pathIntegral f (rectPath x₀ x₁ y₀ y₁) 0 1 =
      segInt f ⟨x₁, y₀⟩ ⟨x₁, y₁⟩ + segInt f ⟨x₁, y₁⟩ ⟨x₀, y₁⟩ +
        (segInt f ⟨x₀, y₁⟩ ⟨x₀, y₀⟩ + segInt f ⟨x₀, y₀⟩ ⟨x₁, y₀⟩) := by
  have hs : ∀ b c : ℂ, IsPiecewiseSmooth (segPath b c) 0 1 := fun b c =>
    (isC1On_segPath b c 0 1).isPiecewiseSmooth zero_le_one
  have e1 : segPath (⟨x₁, y₀⟩ : ℂ) ⟨x₁, y₁⟩ 1 = segPath ⟨x₁, y₁⟩ ⟨x₀, y₁⟩ 0 := by
    rw [segPath_one, segPath_zero]
  have e2 : segPath (⟨x₀, y₁⟩ : ℂ) ⟨x₀, y₀⟩ 1 = segPath ⟨x₀, y₀⟩ ⟨x₁, y₀⟩ 0 := by
    rw [segPath_one, segPath_zero]
  have e3 : pathConcat (segPath (⟨x₁, y₀⟩ : ℂ) ⟨x₁, y₁⟩) (segPath ⟨x₁, y₁⟩ ⟨x₀, y₁⟩) 1 =
      pathConcat (segPath (⟨x₀, y₁⟩ : ℂ) ⟨x₀, y₀⟩) (segPath ⟨x₀, y₀⟩ ⟨x₁, y₀⟩) 0 := by
    rw [pathConcat_one, pathConcat_zero, segPath_one, segPath_zero]
  have hL := image_subset_pathConcat_left (γ₁ := pathConcat (segPath (⟨x₁, y₀⟩ : ℂ) ⟨x₁, y₁⟩)
    (segPath ⟨x₁, y₁⟩ ⟨x₀, y₁⟩)) (γ₂ := pathConcat (segPath (⟨x₀, y₁⟩ : ℂ) ⟨x₀, y₀⟩)
    (segPath ⟨x₀, y₀⟩ ⟨x₁, y₀⟩))
  have hR := image_subset_pathConcat_right e3
  have hfL := hf.mono hL
  have hfR := hf.mono hR
  unfold rectPath
  rw [pathIntegral_pathConcat ((hs _ _).pathConcat (hs _ _) e1)
    ((hs _ _).pathConcat (hs _ _) e2) e3 hfL hfR,
    pathIntegral_pathConcat (hs _ _) (hs _ _) e1 (hfL.mono image_subset_pathConcat_left)
      (hfL.mono (image_subset_pathConcat_right e1)),
    pathIntegral_pathConcat (hs _ _) (hs _ _) e2 (hfR.mono image_subset_pathConcat_left)
      (hfR.mono (image_subset_pathConcat_right e2))]
  rfl

lemma norm_segInt_le {f : ℂ → ℂ} {b c : ℂ} {M : ℝ}
    (hf : ContinuousOn f (segPath b c '' Icc 0 1))
    (hM : ∀ z ∈ segPath b c '' Icc 0 1, ‖f z‖ ≤ M) : ‖segInt f b c‖ ≤ M * ‖c - b‖ := by
  have h := norm_pathIntegral_le (isC1On_segPath b c 0 1) (by rwa [uIcc_of_le zero_le_one])
    zero_le_one (M := M) (fun t ht => hM _ ⟨t, ht, rfl⟩)
  rwa [show pathLength (segPath b c) 0 1 = ‖c - b‖ from pathLength_segment b c] at h

/-- Beck Proposition 4.1.8 for the rectangle: `|∫ f| ≤ M · (perimeter)` when `|f| ≤ M` on it. -/
lemma norm_pathIntegral_rectPath_le {f : ℂ → ℂ} {M : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    (hf : ContinuousOn f (pathImage (rectPath x₀ x₁ y₀ y₁)))
    (hM : ∀ z ∈ pathImage (rectPath x₀ x₁ y₀ y₁), ‖f z‖ ≤ M) :
    ‖pathIntegral f (rectPath x₀ x₁ y₀ y₁) 0 1‖ ≤ M * (2 * (x₁ - x₀) + 2 * (y₁ - y₀)) := by
  have e1 : segPath (⟨x₁, y₀⟩ : ℂ) ⟨x₁, y₁⟩ 1 = segPath ⟨x₁, y₁⟩ ⟨x₀, y₁⟩ 0 := by
    rw [segPath_one, segPath_zero]
  have e2 : segPath (⟨x₀, y₁⟩ : ℂ) ⟨x₀, y₀⟩ 1 = segPath ⟨x₀, y₀⟩ ⟨x₁, y₀⟩ 0 := by
    rw [segPath_one, segPath_zero]
  have e3 : pathConcat (segPath (⟨x₁, y₀⟩ : ℂ) ⟨x₁, y₁⟩) (segPath ⟨x₁, y₁⟩ ⟨x₀, y₁⟩) 1 =
      pathConcat (segPath (⟨x₀, y₁⟩ : ℂ) ⟨x₀, y₀⟩) (segPath ⟨x₀, y₀⟩ ⟨x₁, y₀⟩) 0 := by
    rw [pathConcat_one, pathConcat_zero, segPath_one, segPath_zero]
  have hL : pathImage (pathConcat (segPath (⟨x₁, y₀⟩ : ℂ) ⟨x₁, y₁⟩)
      (segPath ⟨x₁, y₁⟩ ⟨x₀, y₁⟩)) ⊆ pathImage (rectPath x₀ x₁ y₀ y₁) :=
    image_subset_pathConcat_left
  have hR : pathImage (pathConcat (segPath (⟨x₀, y₁⟩ : ℂ) ⟨x₀, y₀⟩)
      (segPath ⟨x₀, y₀⟩ ⟨x₁, y₀⟩)) ⊆ pathImage (rectPath x₀ x₁ y₀ y₁) :=
    image_subset_pathConcat_right e3
  have h1 : segPath (⟨x₁, y₀⟩ : ℂ) ⟨x₁, y₁⟩ '' Icc 0 1 ⊆ pathImage (rectPath x₀ x₁ y₀ y₁) :=
    image_subset_pathConcat_left.trans hL
  have h2 : segPath (⟨x₁, y₁⟩ : ℂ) ⟨x₀, y₁⟩ '' Icc 0 1 ⊆ pathImage (rectPath x₀ x₁ y₀ y₁) :=
    (image_subset_pathConcat_right e1).trans hL
  have h3 : segPath (⟨x₀, y₁⟩ : ℂ) ⟨x₀, y₀⟩ '' Icc 0 1 ⊆ pathImage (rectPath x₀ x₁ y₀ y₁) :=
    image_subset_pathConcat_left.trans hR
  have h4 : segPath (⟨x₀, y₀⟩ : ℂ) ⟨x₁, y₀⟩ '' Icc 0 1 ⊆ pathImage (rectPath x₀ x₁ y₀ y₁) :=
    (image_subset_pathConcat_right e2).trans hR
  have n1 : ‖(⟨x₁, y₁⟩ : ℂ) - ⟨x₁, y₀⟩‖ = y₁ - y₀ := by
    rw [show (⟨x₁, y₁⟩ : ℂ) - ⟨x₁, y₀⟩ = ((y₁ - y₀ : ℝ) : ℂ) * I by
      apply Complex.ext <;> simp, norm_mul, norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have n2 : ‖(⟨x₀, y₁⟩ : ℂ) - ⟨x₁, y₁⟩‖ = x₁ - x₀ := by
    rw [show (⟨x₀, y₁⟩ : ℂ) - ⟨x₁, y₁⟩ = ((x₀ - x₁ : ℝ) : ℂ) by
      apply Complex.ext <;> simp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    ring
  have n3 : ‖(⟨x₀, y₀⟩ : ℂ) - ⟨x₀, y₁⟩‖ = y₁ - y₀ := by
    rw [show (⟨x₀, y₀⟩ : ℂ) - ⟨x₀, y₁⟩ = ((y₀ - y₁ : ℝ) : ℂ) * I by
      apply Complex.ext <;> simp, norm_mul, norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  have n4 : ‖(⟨x₁, y₀⟩ : ℂ) - ⟨x₀, y₀⟩‖ = x₁ - x₀ := by
    rw [show (⟨x₁, y₀⟩ : ℂ) - ⟨x₀, y₀⟩ = ((x₁ - x₀ : ℝ) : ℂ) by
      apply Complex.ext <;> simp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
  have b1 := norm_segInt_le (hf.mono h1) (fun z hz => hM z (h1 hz))
  have b2 := norm_segInt_le (hf.mono h2) (fun z hz => hM z (h2 hz))
  have b3 := norm_segInt_le (hf.mono h3) (fun z hz => hM z (h3 hz))
  have b4 := norm_segInt_le (hf.mono h4) (fun z hz => hM z (h4 hz))
  rw [n1] at b1; rw [n2] at b2; rw [n3] at b3; rw [n4] at b4
  rw [pathIntegral_rectPath hf]
  calc _ ≤ ‖segInt f ⟨x₁, y₀⟩ ⟨x₁, y₁⟩‖ + ‖segInt f ⟨x₁, y₁⟩ ⟨x₀, y₁⟩‖ +
        (‖segInt f ⟨x₀, y₁⟩ ⟨x₀, y₀⟩‖ + ‖segInt f ⟨x₀, y₀⟩ ⟨x₁, y₀⟩‖) :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
    _ ≤ _ := by linarith

end UndergradKB.ComplexAnalysis
