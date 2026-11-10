import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle
import UndergradKB.Common.Attr

/-! # Course layer: OpenStax *Algebra and Trigonometry* 2e, Chapter 9

Thin theorems in the book's terms (sum, difference, double-angle, half-angle, product and
sum-to-product formulas) whose proofs are Mathlib declarations.  All angles are in radians.
-/

namespace UndergradKB.Trigonometry.Course.OpenStax

open EuclideanGeometry

/-- Sum formulas for sine and cosine (TR-058). -/
@[kb "openstaxalgtrig2e" "§9.2, p. 822"]
theorem s9_2_sum_formulas (a b : ℝ) :
    Real.sin (a + b) = Real.sin a * Real.cos b + Real.cos a * Real.sin b ∧
      Real.cos (a + b) = Real.cos a * Real.cos b - Real.sin a * Real.sin b :=
  ⟨Real.sin_add a b, Real.cos_add a b⟩

/-- Difference formulas for sine and cosine (TR-059). -/
@[kb "openstaxalgtrig2e" "§9.2, p. 822"]
theorem s9_2_difference_formulas (a b : ℝ) :
    Real.sin (a - b) = Real.sin a * Real.cos b - Real.cos a * Real.sin b ∧
      Real.cos (a - b) = Real.cos a * Real.cos b + Real.sin a * Real.sin b :=
  ⟨Real.sin_sub a b, Real.cos_sub a b⟩

/-- Tangent of a sum and of a difference, when neither angle is an odd multiple of `π/2`
(TR-060). -/
@[kb "openstaxalgtrig2e" "§9.2, p. 827"]
theorem s9_2_tan_sum_difference {a b : ℝ}
    (h : (∀ k : ℤ, a ≠ (2 * k + 1) * Real.pi / 2) ∧ ∀ l : ℤ, b ≠ (2 * l + 1) * Real.pi / 2) :
    Real.tan (a + b) = (Real.tan a + Real.tan b) / (1 - Real.tan a * Real.tan b) ∧
      Real.tan (a - b) = (Real.tan a - Real.tan b) / (1 + Real.tan a * Real.tan b) :=
  ⟨Real.tan_add' h, Real.tan_sub' h⟩

/-- Double-angle formulas for sine and the three forms of cosine (TR-065). -/
@[kb "openstaxalgtrig2e" "§9.3, p. 838"]
theorem s9_3_double_angle (t : ℝ) :
    Real.sin (2 * t) = 2 * Real.sin t * Real.cos t ∧
      Real.cos (2 * t) = Real.cos t ^ 2 - Real.sin t ^ 2 ∧
      Real.cos (2 * t) = 2 * Real.cos t ^ 2 - 1 ∧ Real.cos (2 * t) = 1 - 2 * Real.sin t ^ 2 :=
  ⟨Real.sin_two_mul t, Real.cos_two_mul' t, Real.cos_two_mul t, Real.cos_two_mul_eq_one_sub t⟩

/-- Double-angle formula for tangent (TR-066). -/
@[kb "openstaxalgtrig2e" "§9.3, p. 838"]
theorem s9_3_tan_double_angle (t : ℝ) :
    Real.tan (2 * t) = 2 * Real.tan t / (1 - Real.tan t ^ 2) :=
  Real.tan_two_mul

/-- Power-reducing identities for sine and cosine squared (TR-068). -/
@[kb "openstaxalgtrig2e" "§9.3, p. 842"]
theorem s9_3_power_reduction (t : ℝ) :
    Real.sin t ^ 2 = 1 / 2 - Real.cos (2 * t) / 2 ∧
      Real.cos t ^ 2 = 1 / 2 + Real.cos (2 * t) / 2 :=
  ⟨Real.sin_sq_eq_half_sub t, Real.cos_sq t⟩

/-- Half-angle formulas as square roots, the sign being fixed by the range of the angle
(TR-070). -/
@[kb "openstaxalgtrig2e" "§9.3, p. 844"]
theorem s9_3_half_angle (t : ℝ) :
    |Real.sin (t / 2)| = √((1 - Real.cos t) / 2) ∧
      (-Real.pi ≤ t → t ≤ Real.pi → Real.cos (t / 2) = √((1 + Real.cos t) / 2)) ∧
      (0 ≤ t → t ≤ 2 * Real.pi → Real.sin (t / 2) = √((1 - Real.cos t) / 2)) ∧
      (-(2 * Real.pi) ≤ t → t ≤ 0 → Real.sin (t / 2) = -√((1 - Real.cos t) / 2)) :=
  ⟨Real.abs_sin_half t, fun hl hr => Real.cos_half hl hr,
    fun hl hr => Real.sin_half_eq_sqrt hl hr, fun hl hr => Real.sin_half_eq_neg_sqrt hl hr⟩

/-- Product-to-sum formulas (each with factor 2 on the product) (TR-072). -/
@[kb "openstaxalgtrig2e" "§9.4, p. 852"]
theorem s9_4_product_to_sum (a b : ℝ) :
    2 * Real.sin a * Real.cos b = Real.sin (a - b) + Real.sin (a + b) ∧
      2 * Real.cos a * Real.cos b = Real.cos (a - b) + Real.cos (a + b) ∧
      2 * Real.sin a * Real.sin b = Real.cos (a - b) - Real.cos (a + b) :=
  ⟨Real.two_mul_sin_mul_cos a b, Real.two_mul_cos_mul_cos a b, Real.two_mul_sin_mul_sin a b⟩

/-- Sum-to-product formulas (TR-073). -/
@[kb "openstaxalgtrig2e" "§9.4, p. 853"]
theorem s9_4_sum_to_product (a b : ℝ) :
    Real.sin a + Real.sin b = 2 * Real.sin ((a + b) / 2) * Real.cos ((a - b) / 2) ∧
      Real.sin a - Real.sin b = 2 * Real.sin ((a - b) / 2) * Real.cos ((a + b) / 2) ∧
      Real.cos a + Real.cos b = 2 * Real.cos ((a + b) / 2) * Real.cos ((a - b) / 2) ∧
      Real.cos a - Real.cos b = -2 * Real.sin ((a + b) / 2) * Real.sin ((a - b) / 2) :=
  ⟨Real.sin_add_sin a b, Real.sin_sub_sin a b, Real.cos_add_cos a b, Real.cos_sub_cos a b⟩

/-- Sine and cosine stay between `-1` and `1`, which rules out spurious solutions (TR-052). -/
@[kb "openstaxalgtrig2e" "§9.5, p. 862"]
theorem s9_5_bounds (t : ℝ) :
    -1 ≤ Real.sin t ∧ Real.sin t ≤ 1 ∧ -1 ≤ Real.cos t ∧ Real.cos t ≤ 1 :=
  ⟨Real.neg_one_le_sin t, Real.sin_le_one t, Real.neg_one_le_cos t, Real.cos_le_one t⟩

section Geometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- Pythagoras: the square on the side opposite the vertex is the sum of the other two squares
exactly when the angle at the vertex is right (TR-013). -/
@[kb "openstaxalgtrig2e" "§9.5, p. 867"]
theorem s9_5_pythagoras (p₁ p₂ p₃ : P) :
    dist p₁ p₃ * dist p₁ p₃ = dist p₁ p₂ * dist p₁ p₂ + dist p₃ p₂ * dist p₃ p₂ ↔
      ∠ p₁ p₂ p₃ = Real.pi / 2 :=
  dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two p₁ p₂ p₃

end Geometry

end UndergradKB.Trigonometry.Course.OpenStax
