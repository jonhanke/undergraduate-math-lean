import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import UndergradKB.ComplexAnalysis.Rectangle
import UndergradKB.Common.Attr

/-! # Worked examples on contour integrals (Beck et al., Sections 4.3, 4.4, 5.1)

Examples 4.3.2, 4.3.11, 4.4.8, 5.1.2, 5.1.3 and 5.1.5, stated in the book's terms and proved from
Mathlib's circle-integral form of Cauchy's formulas (for the circle integrals) and from the
annulus homotopy for rectangles (`isPositivelyOrientedSimpleClosed_rectPath`). -/

open Set Metric Complex Filter Topology MeasureTheory
open scoped Real

namespace UndergradKB.ComplexAnalysis

/-! ### Symmetry of homotopy -/

/-- `G`-homotopy of closed paths is symmetric (reverse the homotopy parameter). -/
lemma IsGHomotopic.symm {G : Set ℂ} {γ₀ γ₁ : ℝ → ℂ} (h : IsGHomotopic G γ₀ γ₁) :
    IsGHomotopic G γ₁ γ₀ := by
  obtain ⟨h, hc, hm, h0, h1, hcl⟩ := h
  refine ⟨fun t s => h t (1 - s), ?_, ?_, ?_, ?_, ?_⟩
  · exact hc.comp (f := fun p : ℝ × ℝ => (p.1, 1 - p.2)) (by fun_prop)
      (fun p hp => ⟨hp.1, ⟨by linarith [hp.2.2], by linarith [hp.2.1]⟩⟩)
  · intro t ht s hs
    exact hm t ht _ ⟨by linarith [hs.2], by linarith [hs.1]⟩
  · intro t ht
    simpa using h1 t ht
  · intro t ht
    simpa using h0 t ht
  · intro s hs
    exact hcl _ ⟨by linarith [hs.2], by linarith [hs.1]⟩

/-! ### Circle integrals of `f z / (z - w)` for entire `f` -/

section Circle

variable {f : ℂ → ℂ} {R : ℝ} {w : ℂ}

lemma circleIntegrable_div_sub (hf : Differentiable ℂ f) (hR : 0 ≤ R) (hw : w ∉ sphere (0 : ℂ) R) :
    CircleIntegrable (fun z => f z / (z - w)) 0 R :=
  ContinuousOn.circleIntegrable hR fun z hz =>
    (hf z).continuousAt.continuousWithinAt.div
      (continuousWithinAt_id.sub continuousWithinAt_const) (sub_ne_zero.2 fun h => hw (h ▸ hz))

lemma circleIntegrable_div_pow (hf : Differentiable ℂ f) (hR : 0 < R) (n : ℕ) :
    CircleIntegrable (fun z => f z / z ^ (n + 1)) 0 R :=
  ContinuousOn.circleIntegrable hR.le fun z hz =>
    (hf z).continuousAt.continuousWithinAt.div (by fun_prop) (by
      have : z ≠ 0 := by
        rintro rfl
        rw [mem_sphere, dist_self] at hz
        linarith
      exact pow_ne_zero _ this)

/-- Cauchy's formula for an entire function and a point inside the circle. -/
lemma circleIntegral_div_sub_of_mem (hf : Differentiable ℂ f) (hw : w ∈ ball (0 : ℂ) R) :
    (∮ z in C(0, R), f z / (z - w)) = 2 * π * I * f w := by
  have := Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    (c := 0) (R := R) (w := w) (f := f) countable_empty hw hf.continuous.continuousOn
    (fun x _ => hf x)
  simp only [smul_eq_mul] at this
  rw [← this]
  congr 1
  ext z
  rw [div_eq_inv_mul]

/-- Cauchy's theorem for `f z / (z - w)` with `f` entire and `w` outside the circle. -/
lemma circleIntegral_div_sub_of_not_mem (hf : Differentiable ℂ f) (hR : 0 ≤ R)
    (hw : w ∉ closedBall (0 : ℂ) R) : (∮ z in C(0, R), f z / (z - w)) = 0 := by
  have hd : DifferentiableOn ℂ (fun z => f z / (z - w)) (closedBall 0 R) := fun z hz =>
    (hf z).differentiableWithinAt.div (differentiableWithinAt_id.sub_const w)
      (sub_ne_zero.2 fun h => hw (h ▸ hz))
  exact (hd.diffContOnCl_ball le_rfl).circleIntegral_eq_zero hR

/-- Cauchy's formula for derivatives for an entire function, centred at the origin. -/
lemma circleIntegral_div_pow (hf : Differentiable ℂ f) (hR : 0 < R) (n : ℕ) :
    (∮ z in C(0, R), f z / z ^ (n + 1)) = 2 * π * I / n.factorial * iteratedDeriv n f 0 := by
  have key := (hf.differentiableOn (s := closedBall 0 R)).circleIntegral_one_div_sub_center_pow_smul
    hR n
  simp only [smul_eq_mul, sub_zero] at key
  rw [← key]
  congr 1
  ext z
  rw [one_div, div_eq_inv_mul]

end Circle

/-! ### The examples -/

/-- Example 4.3.2: the unit circle is homotopic to the square with corners `±3 ± 3i` in the
plane punctured at the origin. -/
@[kb "beck2025" "Example 4.3.2, p. 77"]
theorem example_4_3_2 :
    IsGHomotopic {0}ᶜ (circlePath 0 1) (rectPath (-3) 3 (-3) 3) := by
  have hrect := isPositivelyOrientedSimpleClosed_rectPath (x₀ := -3) (x₁ := 3) (y₀ := -3)
    (y₁ := 3) (by norm_num) (by norm_num)
  have hsub : closedBall (0 : ℂ) 1 ⊆ insideOf (rectPath (-3) 3 (-3) 3) := by
    rw [insideOf_rectPath (by norm_num) (by norm_num)]
    intro z hz
    rw [mem_closedBall, dist_zero_right] at hz
    have h1 : |z.re| ≤ 1 := (abs_re_le_norm z).trans hz
    have h2 : |z.im| ≤ 1 := (abs_im_le_norm z).trans hz
    rw [abs_le] at h1 h2
    simp only [mem_reProdIm, mem_Ioo]
    exact ⟨⟨by linarith [h1.1], by linarith [h1.2]⟩, by linarith [h2.1], by linarith [h2.2]⟩
  have h := hrect.annulus 0 1 one_pos hsub
  refine IsGHomotopic.symm (h.mono ?_)
  intro z hz h0
  exact hz.2 (by rw [mem_singleton_iff.1 h0]; exact mem_ball_self one_pos)

/-- Example 4.3.11: the integral of `1/(z² - 2z)` around the unit circle is `-πi`. -/
@[kb "beck2025" "Example 4.3.11, p. 80"]
theorem example_4_3_11 : (∮ z in C(0, 1), 1 / (z ^ 2 - 2 * z)) = -π * I := by
  have h1 : (∮ z in C(0, 1), 1 / (z ^ 2 - 2 * z)) =
      ∮ z in C(0, 1), (1 / 2 : ℂ) * ((fun _ : ℂ => (1 : ℂ)) z / (z - 2) -
        (fun _ : ℂ => (1 : ℂ)) z / (z - 0)) := by
    refine circleIntegral.integral_congr zero_le_one fun z hz => ?_
    have hz1 : ‖z‖ = 1 := by simpa using hz
    have hz0 : z ≠ 0 := by rintro rfl; simp at hz1
    have hz2 : z - 2 ≠ 0 := by
      intro h
      have : z = 2 := by linear_combination h
      rw [this] at hz1; norm_num at hz1
    have hz3 : z ^ 2 - 2 * z ≠ 0 := by
      have : z ^ 2 - 2 * z = z * (z - 2) := by ring
      rw [this]; exact mul_ne_zero hz0 hz2
    simp only [sub_zero]
    field_simp
    ring
  have hc : Differentiable ℂ (fun _ : ℂ => (1 : ℂ)) := differentiable_const _
  have hn2 : (2 : ℂ) ∉ closedBall (0 : ℂ) 1 := by simp [mem_closedBall]
  have hs2 : (2 : ℂ) ∉ sphere (0 : ℂ) 1 := fun h => hn2 (sphere_subset_closedBall h)
  have hs0 : (0 : ℂ) ∉ sphere (0 : ℂ) 1 := by simp
  rw [h1, circleIntegral.integral_const_mul,
    circleIntegral.integral_sub (circleIntegrable_div_sub hc zero_le_one hs2)
      (circleIntegrable_div_sub hc zero_le_one hs0),
    circleIntegral_div_sub_of_not_mem hc zero_le_one hn2,
    circleIntegral_div_sub_of_mem hc (mem_ball_self one_pos)]
  ring

/-- Example 4.4.8: the integral of `e^z/(z² - 2z)` around the circle of radius 3 is
`πi (e² - 1)`. -/
@[kb "beck2025" "Example 4.4.8, p. 84"]
theorem example_4_4_8 :
    (∮ z in C(0, 3), Complex.exp z / (z ^ 2 - 2 * z)) = π * I * (Complex.exp 2 - 1) := by
  have h1 : (∮ z in C(0, 3), Complex.exp z / (z ^ 2 - 2 * z)) =
      ∮ z in C(0, 3), (1 / 2 : ℂ) * (Complex.exp z / (z - 2) - Complex.exp z / (z - 0)) := by
    refine circleIntegral.integral_congr (by norm_num) fun z hz => ?_
    have hz1 : ‖z‖ = 3 := by simpa using hz
    have hz0 : z ≠ 0 := by rintro rfl; simp at hz1
    have hz2 : z - 2 ≠ 0 := by
      intro h
      have : z = 2 := by linear_combination h
      rw [this] at hz1; norm_num at hz1
    have hz3 : z ^ 2 - 2 * z ≠ 0 := by
      have : z ^ 2 - 2 * z = z * (z - 2) := by ring
      rw [this]; exact mul_ne_zero hz0 hz2
    simp only [sub_zero]
    field_simp
    ring
  have hc : Differentiable ℂ Complex.exp := Complex.differentiable_exp
  have hm2 : (2 : ℂ) ∈ ball (0 : ℂ) 3 := by simp [mem_ball]; norm_num
  have hm0 : (0 : ℂ) ∈ ball (0 : ℂ) 3 := mem_ball_self (by norm_num)
  have hs2 : (2 : ℂ) ∉ sphere (0 : ℂ) 3 := fun h => by
    simp at h
  have hs0 : (0 : ℂ) ∉ sphere (0 : ℂ) 3 := by simp
  rw [h1, circleIntegral.integral_const_mul,
    circleIntegral.integral_sub (circleIntegrable_div_sub hc (by norm_num) hs2)
      (circleIntegrable_div_sub hc (by norm_num) hs0),
    circleIntegral_div_sub_of_mem hc hm2, circleIntegral_div_sub_of_mem hc hm0]
  simp only [Complex.exp_zero]
  ring

/-- Example 5.1.2: the integral of `sin z / z²` around the unit circle is `2πi`. -/
@[kb "beck2025" "Example 5.1.2, p. 92"]
theorem example_5_1_2 : (∮ z in C(0, 1), Complex.sin z / z ^ 2) = 2 * π * I := by
  have := circleIntegral_div_pow Complex.differentiable_sin one_pos 1
  simp only [Nat.factorial_one, Nat.cast_one, div_one, iteratedDeriv_one,
    Complex.deriv_sin, Complex.cos_zero, mul_one] at this
  simpa using this

/-- Example 5.1.3: the integral of `1/(z²(z - 1))` around the circle of radius 2 is `0`. -/
@[kb "beck2025" "Example 5.1.3, p. 92"]
theorem example_5_1_3 : (∮ z in C(0, 2), 1 / (z ^ 2 * (z - 1))) = 0 := by
  have hc : Differentiable ℂ (fun _ : ℂ => (1 : ℂ)) := differentiable_const _
  have h1 : (∮ z in C(0, 2), 1 / (z ^ 2 * (z - 1))) =
      ∮ z in C(0, 2), (1 / (z - 1) - 1 / (z - 0) - 1 / z ^ (1 + 1)) := by
    refine circleIntegral.integral_congr (by norm_num) fun z hz => ?_
    have hz1 : ‖z‖ = 2 := by simpa using hz
    have hz0 : z ≠ 0 := by rintro rfl; simp at hz1
    have hz2 : z - 1 ≠ 0 := by
      intro h
      have : z = 1 := by linear_combination h
      rw [this] at hz1; norm_num at hz1
    simp only [sub_zero]
    field_simp
    ring
  have hm1 : (1 : ℂ) ∈ ball (0 : ℂ) 2 := by simp [mem_ball]
  have hm0 : (0 : ℂ) ∈ ball (0 : ℂ) 2 := mem_ball_self (by norm_num)
  have hs1 : (1 : ℂ) ∉ sphere (0 : ℂ) 2 := fun h => by
    simp at h
  have hs0 : (0 : ℂ) ∉ sphere (0 : ℂ) 2 := by simp
  have hI1 : CircleIntegrable (fun z : ℂ => 1 / (z - 1)) 0 2 :=
    circleIntegrable_div_sub hc (by norm_num) hs1
  have hI0 : CircleIntegrable (fun z : ℂ => 1 / (z - 0)) 0 2 :=
    circleIntegrable_div_sub hc (by norm_num) hs0
  have hI2 : CircleIntegrable (fun z : ℂ => 1 / z ^ (1 + 1)) 0 2 :=
    circleIntegrable_div_pow hc (by norm_num) 1
  have A : (∮ z in C(0, 2), 1 / (z - 1)) = 2 * π * I * 1 := circleIntegral_div_sub_of_mem hc hm1
  have B : (∮ z in C(0, 2), 1 / (z - 0)) = 2 * π * I * 1 := circleIntegral_div_sub_of_mem hc hm0
  have C : (∮ z in C(0, 2), 1 / z ^ (1 + 1)) = 2 * π * I / (Nat.factorial 1 : ℕ) *
      iteratedDeriv 1 (fun _ : ℂ => (1 : ℂ)) 0 := circleIntegral_div_pow hc (by norm_num) 1
  have e1 := circleIntegral.integral_sub (f := fun z : ℂ => 1 / (z - 1) - 1 / (z - 0))
    (g := fun z : ℂ => 1 / z ^ (1 + 1)) (c := 0) (R := 2) (hI1.sub hI0) hI2
  have e2 := circleIntegral.integral_sub (f := fun z : ℂ => 1 / (z - 1))
    (g := fun z : ℂ => 1 / (z - 0)) (c := 0) (R := 2) hI1 hI0
  rw [h1, e1, e2, A, B, C]
  simp [iteratedDeriv_one]

/-- Example 5.1.5: the integral of `cos z / z³` around the unit circle is `-πi`. -/
@[kb "beck2025" "Example 5.1.5, p. 93"]
theorem example_5_1_5 : (∮ z in C(0, 1), Complex.cos z / z ^ 3) = -π * I := by
  have := circleIntegral_div_pow Complex.differentiable_cos one_pos 2
  have h2 : iteratedDeriv 2 Complex.cos 0 = -1 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    have : deriv Complex.cos = fun z => -Complex.sin z := funext fun z => Complex.deriv_cos
    rw [this]
    simp
  rw [h2] at this
  have e : (∮ z in C(0, 1), Complex.cos z / z ^ 3) = ∮ z in C(0, 1), Complex.cos z / z ^ (2 + 1) :=
    rfl
  rw [e, this]
  simp [Nat.factorial]
  ring
end UndergradKB.ComplexAnalysis
