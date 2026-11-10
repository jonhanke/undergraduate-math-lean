import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle
import UndergradKB.Common.Attr

/-! # Course layer: OpenStax *Algebra and Trigonometry* 2e, Chapter 7

Thin theorems in the book's terms (right-triangle trigonometry, the unit circle, the basic
identities) whose proofs are Mathlib declarations.  All angles are in radians.
-/

namespace UndergradKB.Trigonometry.Course.OpenStax

open EuclideanGeometry Set

section Geometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- In a right triangle the leg adjacent to an acute angle is the hypotenuse times its cosine
(TR-021). -/
@[kb "openstaxalgtrig2e" "§7.2, p. 704"]
theorem s7_2_adjacent_leg {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = Real.pi / 2) :
    Real.cos (∠ p₂ p₃ p₁) * dist p₁ p₃ = dist p₃ p₂ :=
  cos_angle_mul_dist_of_angle_eq_pi_div_two h

/-- In a right triangle the leg opposite an acute angle is the hypotenuse times its sine
(TR-021). -/
theorem s7_2_opposite_leg {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = Real.pi / 2) :
    Real.sin (∠ p₂ p₃ p₁) * dist p₁ p₃ = dist p₁ p₂ :=
  sin_angle_mul_dist_of_angle_eq_pi_div_two h

/-- In a right triangle the opposite leg is the adjacent leg times the tangent (TR-021). -/
theorem s7_2_tangent_leg {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = Real.pi / 2)
    (h0 : p₁ = p₂ ∨ p₃ ≠ p₂) :
    Real.tan (∠ p₂ p₃ p₁) * dist p₃ p₂ = dist p₁ p₂ :=
  tan_angle_mul_dist_of_angle_eq_pi_div_two h h0

end Geometry

/-- Cofunction identities: sine and cosine of the complementary angle swap, and tangent becomes the
reciprocal of tangent (TR-046). -/
@[kb "openstaxalgtrig2e" "§7.2, p. 704"]
theorem s7_2_cofunction (t : ℝ) :
    Real.sin (Real.pi / 2 - t) = Real.cos t ∧ Real.cos (Real.pi / 2 - t) = Real.sin t ∧
      Real.tan (Real.pi / 2 - t) = (Real.tan t)⁻¹ :=
  ⟨Real.sin_pi_div_two_sub t, Real.cos_pi_div_two_sub t, Real.tan_pi_div_two_sub t⟩

/-- A point `(x, y)` lies on the unit circle exactly when `x² + y² = 1` (TR-038). -/
@[kb "openstaxalgtrig2e" "§7.3, p. 711"]
theorem s7_3_unit_circle (x y : ℝ) :
    (⟨x, y⟩ : ℂ) ∈ Metric.sphere (0 : ℂ) 1 ↔ x ^ 2 + y ^ 2 = 1 := by
  rw [mem_sphere_zero_iff_norm, Complex.norm_def, Real.sqrt_eq_one, Complex.normSq_apply]
  constructor <;> intro h <;> simp only [sq] at * <;> linarith

/-- The Pythagorean identity from the unit circle (TR-050). -/
@[kb "openstaxalgtrig2e" "§7.3, p. 714"]
theorem s7_3_cos_sq_add_sin_sq (t : ℝ) : Real.cos t ^ 2 + Real.sin t ^ 2 = 1 :=
  Real.cos_sq_add_sin_sq t

/-- Solving the Pythagorean identity for one function in terms of the other (TR-051). -/
@[kb "openstaxalgtrig2e" "§7.3, p. 715"]
theorem s7_3_solved_forms (t : ℝ) :
    Real.sin t ^ 2 = 1 - Real.cos t ^ 2 ∧ Real.cos t ^ 2 = 1 - Real.sin t ^ 2 ∧
      |Real.sin t| = √(1 - Real.cos t ^ 2) ∧ |Real.cos t| = √(1 - Real.sin t ^ 2) :=
  ⟨Real.sin_sq t, Real.cos_sq' t, Real.abs_sin_eq_sqrt_one_sub_cos_sq t,
    Real.abs_cos_eq_sqrt_one_sub_sin_sq t⟩

/-- Sine and cosine of any angle lie in `[-1, 1]` (TR-024). -/
@[kb "openstaxalgtrig2e" "§7.3, p. 720"]
theorem s7_3_sin_cos_range (t : ℝ) : |Real.sin t| ≤ 1 ∧ |Real.cos t| ≤ 1 :=
  ⟨Real.abs_sin_le_one t, Real.abs_cos_le_one t⟩

/-- Sine and cosine have range `[-1, 1]` and tangent takes every real value (TR-120). -/
@[kb "openstaxalgtrig2e" "§7.3, p. 720"]
theorem s7_3_ranges :
    Set.range Real.sin = Icc (-1) 1 ∧ Set.range Real.cos = Icc (-1) 1 ∧
      Function.Surjective Real.tan :=
  ⟨Real.range_sin, Real.range_cos, Real.tan_surjective⟩

/-- Parity: cosine is even, sine and tangent are odd (TR-033). -/
@[kb "openstaxalgtrig2e" "§7.3, p. 721"]
theorem s7_3_even_odd (t : ℝ) :
    Real.sin (-t) = -Real.sin t ∧ Real.cos (-t) = Real.cos t ∧ Real.tan (-t) = -Real.tan t :=
  ⟨Real.sin_neg t, Real.cos_neg t, Real.tan_neg t⟩

/-- The mate of an angle in the second quadrant keeps sine and negates cosine and tangent
(TR-035). -/
@[kb "openstaxalgtrig2e" "§7.3, p. 721"]
theorem s7_3_pi_sub (t : ℝ) :
    Real.sin (Real.pi - t) = Real.sin t ∧ Real.cos (Real.pi - t) = -Real.cos t ∧
      Real.tan (Real.pi - t) = -Real.tan t :=
  ⟨Real.sin_pi_sub t, Real.cos_pi_sub t, Real.tan_pi_sub t⟩

/-- A point at distance `r` and polar angle `t` has coordinates `(r cos t, r sin t)` (TR-196). -/
@[kb "openstaxalgtrig2e" "§7.3, p. 724"]
theorem s7_3_polar_coordinates (r t : ℝ) :
    polarCoord.symm (r, t) = (r * Real.cos t, r * Real.sin t) :=
  polarCoord_symm_apply (r, t)

/-- For a complex number, the real and imaginary parts are `r cos t` and `r sin t` (TR-196). -/
theorem s7_3_complex_polar (z : ℂ) :
    ‖z‖ * Real.cos (Complex.arg z) = z.re ∧ ‖z‖ * Real.sin (Complex.arg z) = z.im :=
  ⟨Complex.norm_mul_cos_arg z, Complex.norm_mul_sin_arg z⟩

/-- Tangent is sine over cosine (TR-048). -/
@[kb "openstaxalgtrig2e" "§7.4, p. 729"]
theorem s7_4_tan_eq_sin_div_cos (t : ℝ) : Real.tan t = Real.sin t / Real.cos t :=
  Real.tan_eq_sin_div_cos t

/-- A function is even if `f (-x) = f x` and odd if `f (-x) = -f x` (TR-034). -/
@[kb "openstaxalgtrig2e" "§7.4, p. 733"]
theorem s7_4_even_odd_def (f : ℝ → ℝ) :
    (Function.Even f ↔ ∀ x, f (-x) = f x) ∧ (Function.Odd f ↔ ∀ x, f (-x) = -f x) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- Cotangent is cosine over sine (TR-049). -/
@[kb "openstaxalgtrig2e" "§7.4, p. 734"]
theorem s7_4_cot_eq_cos_div_sin (t : ℝ) : Real.cot t = Real.cos t / Real.sin t :=
  Real.cot_eq_cos_div_sin t

end UndergradKB.Trigonometry.Course.OpenStax
