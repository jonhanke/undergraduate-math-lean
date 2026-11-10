import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import UndergradKB.Common.Attr

/-! # Course layer: Corral, *Trigonometry*, Chapter 3

Thin theorems in the book's terms (fundamental identities, sum, difference, double, half-angle and
product formulas) whose proofs are Mathlib declarations.  All angles are in radians.
-/

namespace UndergradKB.Trigonometry.Course.Corral

/-- Tangent is sine over cosine (TR-048). -/
@[kb "corraltrig" "Eq 3.1, p. 73"]
theorem eq_3_1_tan_eq_sin_div_cos (θ : ℝ) : Real.tan θ = Real.sin θ / Real.cos θ :=
  Real.tan_eq_sin_div_cos θ

/-- Cotangent is cosine over sine (TR-049). -/
@[kb "corraltrig" "Eq 3.2, p. 74"]
theorem eq_3_2_cot_eq_cos_div_sin (θ : ℝ) : Real.cot θ = Real.cos θ / Real.sin θ :=
  Real.cot_eq_cos_div_sin θ

/-- The Pythagorean identity `cos² θ + sin² θ = 1` (TR-050). -/
@[kb "corraltrig" "Eq 3.3, p. 74"]
theorem eq_3_3_cos_sq_add_sin_sq (θ : ℝ) : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 :=
  Real.cos_sq_add_sin_sq θ

/-- Solving the Pythagorean identity for either square, and the root forms (TR-051). -/
@[kb "corraltrig" "Eq 3.4-3.7, p. 74"]
theorem eq_3_4_solved_forms (θ : ℝ) :
    Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 ∧ Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 ∧
      |Real.sin θ| = √(1 - Real.cos θ ^ 2) ∧ |Real.cos θ| = √(1 - Real.sin θ ^ 2) :=
  ⟨Real.sin_sq θ, Real.cos_sq' θ, Real.abs_sin_eq_sqrt_one_sub_cos_sq θ,
    Real.abs_cos_eq_sqrt_one_sub_sin_sq θ⟩

/-- Sine and cosine are bounded between `-1` and `1` (TR-052). -/
@[kb "corraltrig" "Eq 3.8-3.9, p. 75"]
theorem eq_3_8_bounds (θ : ℝ) :
    -1 ≤ Real.sin θ ∧ Real.sin θ ≤ 1 ∧ -1 ≤ Real.cos θ ∧ Real.cos θ ≤ 1 :=
  ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ, Real.neg_one_le_cos θ, Real.cos_le_one θ⟩

/-- Sum formulas for sine and cosine (TR-058). -/
@[kb "corraltrig" "Eq 3.12-3.13, p. 79"]
theorem eq_3_12_sum_formulas (A B : ℝ) :
    Real.sin (A + B) = Real.sin A * Real.cos B + Real.cos A * Real.sin B ∧
      Real.cos (A + B) = Real.cos A * Real.cos B - Real.sin A * Real.sin B :=
  ⟨Real.sin_add A B, Real.cos_add A B⟩

/-- Difference formulas for sine and cosine (TR-059). -/
@[kb "corraltrig" "Eq 3.16-3.17, p. 80"]
theorem eq_3_16_difference_formulas (A B : ℝ) :
    Real.sin (A - B) = Real.sin A * Real.cos B - Real.cos A * Real.sin B ∧
      Real.cos (A - B) = Real.cos A * Real.cos B + Real.sin A * Real.sin B :=
  ⟨Real.sin_sub A B, Real.cos_sub A B⟩

/-- Tangent of a sum and of a difference, when neither angle is an odd multiple of `π/2`
(TR-060). -/
@[kb "corraltrig" "Eq 3.18-3.19, p. 81"]
theorem eq_3_18_tan_sum_difference {A B : ℝ}
    (h : (∀ k : ℤ, A ≠ (2 * k + 1) * Real.pi / 2) ∧ ∀ l : ℤ, B ≠ (2 * l + 1) * Real.pi / 2) :
    Real.tan (A + B) = (Real.tan A + Real.tan B) / (1 - Real.tan A * Real.tan B) ∧
      Real.tan (A - B) = (Real.tan A - Real.tan B) / (1 + Real.tan A * Real.tan B) :=
  ⟨Real.tan_add' h, Real.tan_sub' h⟩

/-- Double-angle formulas for sine and the three forms of cosine (TR-065). -/
@[kb "corraltrig" "Eq 3.23-3.24, p. 86"]
theorem eq_3_23_double_angle (θ : ℝ) :
    Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ ∧
      Real.cos (2 * θ) = Real.cos θ ^ 2 - Real.sin θ ^ 2 ∧
      Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 ∧ Real.cos (2 * θ) = 1 - 2 * Real.sin θ ^ 2 :=
  ⟨Real.sin_two_mul θ, Real.cos_two_mul' θ, Real.cos_two_mul θ, Real.cos_two_mul_eq_one_sub θ⟩

/-- Double-angle formula for tangent (TR-066). -/
@[kb "corraltrig" "Eq 3.25, p. 86"]
theorem eq_3_25_tan_double_angle (θ : ℝ) :
    Real.tan (2 * θ) = 2 * Real.tan θ / (1 - Real.tan θ ^ 2) :=
  Real.tan_two_mul

/-- Triple-angle formulas for sine and cosine (TR-067). -/
@[kb "corraltrig" "Ex 3.13, p. 86"]
theorem ex_3_13_triple_angle (θ : ℝ) :
    Real.sin (3 * θ) = 3 * Real.sin θ - 4 * Real.sin θ ^ 3 ∧
      Real.cos (3 * θ) = 4 * Real.cos θ ^ 3 - 3 * Real.cos θ :=
  ⟨Real.sin_three_mul θ, Real.cos_three_mul θ⟩

/-- Power-reducing identities for sine and cosine squared, in the variable `x = θ` (TR-068). -/
@[kb "corraltrig" "Eq 3.28-3.29, p. 87"]
theorem eq_3_28_power_reduction (θ : ℝ) :
    Real.sin θ ^ 2 = 1 / 2 - Real.cos (2 * θ) / 2 ∧
      Real.cos θ ^ 2 = 1 / 2 + Real.cos (2 * θ) / 2 :=
  ⟨Real.sin_sq_eq_half_sub θ, Real.cos_sq θ⟩

/-- Half-angle formulas: absolute value of the sine, and the cosine on `[-π, π]`, as square roots
(TR-070). -/
@[kb "corraltrig" "Eq 3.31-3.32, p. 88"]
theorem eq_3_31_half_angle (θ : ℝ) :
    |Real.sin (θ / 2)| = √((1 - Real.cos θ) / 2) ∧
      (-Real.pi ≤ θ → θ ≤ Real.pi → Real.cos (θ / 2) = √((1 + Real.cos θ) / 2)) :=
  ⟨Real.abs_sin_half θ, fun hl hr => Real.cos_half hl hr⟩

/-- Half-angle sine with its sign fixed by the range of the angle (TR-070). -/
theorem eq_3_31_half_angle_sine_sign (θ : ℝ) :
    (0 ≤ θ → θ ≤ 2 * Real.pi → Real.sin (θ / 2) = √((1 - Real.cos θ) / 2)) ∧
      (-(2 * Real.pi) ≤ θ → θ ≤ 0 → Real.sin (θ / 2) = -√((1 - Real.cos θ) / 2)) :=
  ⟨fun hl hr => Real.sin_half_eq_sqrt hl hr, fun hl hr => Real.sin_half_eq_neg_sqrt hl hr⟩

/-- Product-to-sum formulas (each with factor 2 on the product) (TR-072). -/
@[kb "corraltrig" "Eq 3.37-3.40, p. 90"]
theorem eq_3_37_product_to_sum (A B : ℝ) :
    2 * Real.sin A * Real.cos B = Real.sin (A - B) + Real.sin (A + B) ∧
      2 * Real.cos A * Real.cos B = Real.cos (A - B) + Real.cos (A + B) ∧
      2 * Real.sin A * Real.sin B = Real.cos (A - B) - Real.cos (A + B) :=
  ⟨Real.two_mul_sin_mul_cos A B, Real.two_mul_cos_mul_cos A B, Real.two_mul_sin_mul_sin A B⟩

/-- Sum-to-product formulas for sums and differences of sines and cosines (TR-073). -/
@[kb "corraltrig" "Eq 3.41-3.44, p. 90"]
theorem eq_3_41_sum_to_product (A B : ℝ) :
    Real.sin A + Real.sin B = 2 * Real.sin ((A + B) / 2) * Real.cos ((A - B) / 2) ∧
      Real.sin A - Real.sin B = 2 * Real.sin ((A - B) / 2) * Real.cos ((A + B) / 2) ∧
      Real.cos A + Real.cos B = 2 * Real.cos ((A + B) / 2) * Real.cos ((A - B) / 2) ∧
      Real.cos A - Real.cos B = -2 * Real.sin ((A + B) / 2) * Real.sin ((A - B) / 2) :=
  ⟨Real.sin_add_sin A B, Real.sin_sub_sin A B, Real.cos_add_cos A B, Real.cos_sub_cos A B⟩

end UndergradKB.Trigonometry.Course.Corral
