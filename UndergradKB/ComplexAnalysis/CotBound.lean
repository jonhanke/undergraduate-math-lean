import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Real.Pi.Bounds
import UndergradKB.Common

/-!
# Bounds for the complex cotangent

Beck et al., Exercise 3.6.35 and Section 10.1: closed forms for `|sin z|²`, `|cos z|²`, and bounds
on `cot` (and `1/sin`) away from the real zeros, used for the contour estimates on large rectangles.
-/

open Complex
open scoped Real

namespace UndergradKB.ComplexAnalysis

theorem sin_re_eq (z : ℂ) : (Complex.sin z).re = Real.sin z.re * Real.cosh z.im := by
  conv_lhs => rw [← Complex.re_add_im z, Complex.sin_add_mul_I]
  simp [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sinh, ← Complex.ofReal_cosh]

theorem sin_im_eq (z : ℂ) : (Complex.sin z).im = Real.cos z.re * Real.sinh z.im := by
  conv_lhs => rw [← Complex.re_add_im z, Complex.sin_add_mul_I]
  simp [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sinh, ← Complex.ofReal_cosh]

theorem cos_re_eq (z : ℂ) : (Complex.cos z).re = Real.cos z.re * Real.cosh z.im := by
  conv_lhs => rw [← Complex.re_add_im z, Complex.cos_add_mul_I]
  simp [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sinh, ← Complex.ofReal_cosh]

theorem cos_im_eq (z : ℂ) : (Complex.cos z).im = -(Real.sin z.re * Real.sinh z.im) := by
  conv_lhs => rw [← Complex.re_add_im z, Complex.cos_add_mul_I]
  simp [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sinh, ← Complex.ofReal_cosh]

/-- `|sin z|² = sin² x + sinh² y`. -/
@[kb "beck2025" "Exercise 3.6.35, p. 66"]
theorem norm_sin_sq (z : ℂ) : ‖Complex.sin z‖ ^ 2 = Real.sin z.re ^ 2 + Real.sinh z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, sin_re_eq, sin_im_eq]
  have := Real.cosh_sq z.im
  nlinarith [Real.sin_sq_add_cos_sq z.re]

/-- `|cos z|² = cos² x + sinh² y`. -/
@[kb "beck2025" "Exercise 3.6.35, p. 66"]
theorem norm_cos_sq (z : ℂ) : ‖Complex.cos z‖ ^ 2 = Real.cos z.re ^ 2 + Real.sinh z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, cos_re_eq, cos_im_eq]
  have := Real.cosh_sq z.im
  nlinarith [Real.sin_sq_add_cos_sq z.re]

theorem sinh_one_gt : 1 < Real.sinh 1 := by
  rw [Real.sinh_eq]
  have h := Real.exp_one_gt_d9
  have h2 : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
  rw [h2]
  have hp : 0 < Real.exp 1 := Real.exp_pos 1
  have : (Real.exp 1)⁻¹ < 1 / 2 := by
    rw [inv_lt_comm₀ hp (by norm_num)]; linarith
  linarith

theorem one_lt_sinh_sq {y : ℝ} (h : 1 ≤ |y|) : 1 < Real.sinh y ^ 2 := by
  have h1 : Real.sinh 1 ≤ Real.sinh |y| := Real.sinh_le_sinh.mpr h
  have h2 : Real.sinh |y| = |Real.sinh y| := (Real.abs_sinh y).symm
  have := sinh_one_gt
  rw [← sq_abs, ← h2]
  nlinarith

theorem norm_cot_eq (z : ℂ) : ‖Complex.cot z‖ = ‖Complex.cos z‖ / ‖Complex.sin z‖ := by
  rw [Complex.cot_eq_cos_div_sin, norm_div]

/-- part (c): if cos x = 0 then |cot z| ≤ 1 -/
@[kb "beck2025" "Exercise 3.6.35, p. 66"]
theorem norm_cot_le_one_of_cos_re_eq_zero {z : ℂ} (h : Real.cos z.re = 0) :
    ‖Complex.cot z‖ ≤ 1 := by
  have hs := norm_sin_sq z
  have hc := norm_cos_sq z
  have h1 : Real.sin z.re ^ 2 = 1 := by
    have := Real.sin_sq_add_cos_sq z.re
    rw [h] at this; linarith
  rw [h1] at hs
  rw [h] at hc
  have hpos : 0 < ‖Complex.sin z‖ := by
    apply norm_pos_iff.mpr
    intro h0
    rw [h0, norm_zero] at hs
    nlinarith [sq_nonneg (Real.sinh z.im)]
  rw [norm_cot_eq, div_le_one hpos]
  nlinarith [norm_nonneg (Complex.cos z), norm_nonneg (Complex.sin z)]

/-- part (d): if |y| ≥ 1 then |cot z| < 2. -/
@[kb "beck2025" "Exercise 3.6.35, p. 66"]
theorem norm_cot_lt_two_of_one_le_abs_im {z : ℂ} (h : 1 ≤ |z.im|) : ‖Complex.cot z‖ < 2 := by
  have hs := norm_sin_sq z
  have hc := norm_cos_sq z
  have h1 := one_lt_sinh_sq h
  have hpos : 0 < ‖Complex.sin z‖ := by
    apply norm_pos_iff.mpr
    intro h0
    rw [h0, norm_zero] at hs
    nlinarith [sq_nonneg (Real.sin z.re)]
  rw [norm_cot_eq, div_lt_iff₀ hpos]
  by_contra hcon
  push Not at hcon
  have := Real.cos_sq_le_one z.re
  have := Real.sin_sq_add_cos_sq z.re
  nlinarith [norm_nonneg (Complex.cos z), norm_nonneg (Complex.sin z), sq_nonneg (Real.sin z.re)]

theorem cos_pi_mul_re_eq_zero {N : ℕ} {x : ℝ} (h : |x| = N + 1 / 2) : Real.cos (π * x) = 0 := by
  rw [Real.cos_eq_zero_iff]
  rcases abs_cases x with ⟨h1, _⟩ | ⟨h1, _⟩
  · rw [h1] at h
    refine ⟨N, ?_⟩
    rw [h]; push_cast; ring
  · rw [h1] at h
    refine ⟨-(N : ℤ) - 1, ?_⟩
    have : x = -(N + 1 / 2) := by linarith
    rw [this]; push_cast; ring

/-- Section 10.1 (2a): on the vertical sides of the book's rectangle γ_N. -/
@[kb "beck2025" "Section 10.1, p. 163"]
theorem norm_cot_pi_mul_lt_two_of_re {N : ℕ} {z : ℂ} (h : |z.re| = N + 1 / 2) :
    ‖Complex.cot (π * z)‖ < 2 := by
  have h0 : Real.cos (π * z.re) = 0 := cos_pi_mul_re_eq_zero h
  have : Real.cos ((π * z : ℂ)).re = 0 := by simpa using h0
  exact lt_of_le_of_lt (norm_cot_le_one_of_cos_re_eq_zero this) (by norm_num)

theorem one_le_abs_im_pi_mul {N : ℕ} (hN : 1 ≤ N) {z : ℂ} (h : |z.im| = N) :
    1 ≤ |(π * z : ℂ).im| := by
  have : (π * z : ℂ).im = π * z.im := by simp
  rw [this, abs_mul, abs_of_pos Real.pi_pos, h]
  have : (1 : ℝ) ≤ N := by exact_mod_cast hN
  nlinarith [Real.pi_gt_three]

/-- Section 10.1 (2a): on the horizontal sides. -/
@[kb "beck2025" "Section 10.1, p. 163"]
theorem norm_cot_pi_mul_lt_two_of_im {N : ℕ} (hN : 1 ≤ N) {z : ℂ} (h : |z.im| = N) :
    ‖Complex.cot (π * z)‖ < 2 :=
  norm_cot_lt_two_of_one_le_abs_im (one_le_abs_im_pi_mul hN h)

theorem norm_inv_lt_three {w : ℂ} (h : 1 ≤ ‖w‖ ^ 2) : ‖w⁻¹‖ < 3 := by
  have h1 : 1 ≤ ‖w‖ := by
    by_contra hc
    push Not at hc
    nlinarith [norm_nonneg w]
  rw [norm_inv]
  calc ‖w‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    _ < 3 := by norm_num

/-- Section 10.1 (5) hint: so `|1/sin(πz)| < 3` on the vertical sides. -/
@[kb "beck2025" "Section 10.1, p. 163"]
theorem norm_inv_sin_pi_mul_lt_three_of_re {N : ℕ} {z : ℂ} (h : |z.re| = N + 1 / 2) :
    ‖(Complex.sin (π * z))⁻¹‖ < 3 := by
  apply norm_inv_lt_three
  have h0 : Real.cos (π * z.re) = 0 := cos_pi_mul_re_eq_zero h
  rw [norm_sin_sq]
  have h1 : Real.sin (π * z : ℂ).re ^ 2 = 1 := by
    have := Real.sin_sq_add_cos_sq (π * z : ℂ).re
    have h2 : Real.cos (π * z : ℂ).re = 0 := by simpa using h0
    rw [h2] at this; linarith
  nlinarith [sq_nonneg (Real.sinh (π * z : ℂ).im)]

@[kb "beck2025" "Section 10.1, p. 163"]
theorem norm_inv_sin_pi_mul_lt_three_of_im {N : ℕ} (hN : 1 ≤ N) {z : ℂ} (h : |z.im| = N) :
    ‖(Complex.sin (π * z))⁻¹‖ < 3 := by
  apply norm_inv_lt_three
  rw [norm_sin_sq]
  have := one_lt_sinh_sq (one_le_abs_im_pi_mul hN h)
  nlinarith [sq_nonneg (Real.sin (π * z : ℂ).re)]

end UndergradKB.ComplexAnalysis
