import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Geometry.Euclidean.Angle.Sphere
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Geometry.Euclidean.Sphere.Tangent
import Mathlib.NumberTheory.PythagoreanTriples
import UndergradKB.Common.Attr

/-! # Course layer: Corral, *Trigonometry*, Chapter 1

Thin theorems in the book's terms whose proofs are the Mathlib declarations listed in the coverage
checklist.  All angles are in radians.
-/

namespace UndergradKB.Trigonometry.Course.Corral

open EuclideanGeometry

section Geometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- The three angles of a triangle add up to a straight angle (TR-003). -/
@[kb "corraltrig" "Box §1.1, p. 10"]
theorem box_1_1_angle_sum (p₁ p₂ p₃ : P) (h : p₂ ≠ p₁) :
    ∠ p₁ p₂ p₃ + ∠ p₂ p₃ p₁ + ∠ p₃ p₁ p₂ = Real.pi :=
  angle_add_angle_add_angle_eq_pi p₃ h

/-- Pythagoras: the square on the side opposite the vertex is the sum of the other two squares
exactly when the angle at the vertex is right (TR-013). -/
@[kb "corraltrig" "Thm 1.1, p. 12"]
theorem thm_1_1_pythagoras (p₁ p₂ p₃ : P) :
    dist p₁ p₃ * dist p₁ p₃ = dist p₁ p₂ * dist p₁ p₂ + dist p₃ p₂ * dist p₃ p₂ ↔
      ∠ p₁ p₂ p₃ = Real.pi / 2 :=
  dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two p₁ p₂ p₃

/-- In a right triangle the leg adjacent to an acute angle is the hypotenuse times its cosine
(TR-021). -/
@[kb "corraltrig" "Box §1.3, p. 27"]
theorem box_1_3_adjacent_leg {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = Real.pi / 2) :
    Real.cos (∠ p₂ p₃ p₁) * dist p₁ p₃ = dist p₃ p₂ :=
  cos_angle_mul_dist_of_angle_eq_pi_div_two h

/-- In a right triangle the leg opposite an acute angle is the hypotenuse times its sine
(TR-021). -/
theorem box_1_3_opposite_leg {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = Real.pi / 2) :
    Real.sin (∠ p₂ p₃ p₁) * dist p₁ p₃ = dist p₁ p₂ :=
  sin_angle_mul_dist_of_angle_eq_pi_div_two h

/-- In a right triangle the opposite leg is the adjacent leg times the tangent (TR-021). -/
theorem box_1_3_tangent_leg {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = Real.pi / 2)
    (h0 : p₁ = p₂ ∨ p₃ ≠ p₂) :
    Real.tan (∠ p₂ p₃ p₁) * dist p₃ p₂ = dist p₁ p₂ :=
  tan_angle_mul_dist_of_angle_eq_pi_div_two h h0

/-- An angle inscribed in a semicircle on a diameter is a right angle, and conversely (TR-087). -/
@[kb "corraltrig" "Ex 1.2, p. 11"]
theorem ex_1_2_thales {p₁ p₂ p₃ : P} {s : Sphere P} (hd : s.IsDiameter p₁ p₃) :
    ∠ p₁ p₂ p₃ = Real.pi / 2 ↔ p₂ ∈ s :=
  Sphere.thales_theorem hd

/-- A tangent line meets the circle only at its point of tangency (TR-088). -/
@[kb "corraltrig" "Def §1.1, p. 14"]
theorem def_1_1_tangent_meets_once {s : Sphere P} {p q : P} {as : AffineSubspace ℝ P}
    (h : s.IsTangentAt p as) (hs : q ∈ s) (has : q ∈ as) : q = p :=
  h.eq_of_mem_of_mem hs has

/-- A tangent line is perpendicular to the radius drawn to the point of tangency (TR-089). -/
@[kb "corraltrig" "Box §1.1, p. 14"]
theorem box_1_1_tangent_perp_radius {s : Sphere P} {p q : P} {as : AffineSubspace ℝ P}
    (h : s.IsTangentAt p as) (hq : q ∈ as) : ∠ q p s.center = Real.pi / 2 :=
  h.angle_eq_pi_div_two hq

end Geometry

/-- Three integers form a Pythagorean triple when the squares of two add to the square of the
third (TR-015). -/
@[kb "corraltrig" "Def §1.1, p. 14"]
theorem def_1_1_pythagorean_triple (x y z : ℤ) :
    PythagoreanTriple x y z ↔ x * x + y * y = z * z :=
  Iff.rfl

/-- Sine and cosine of any angle lie in `[-1, 1]` (TR-024). -/
@[kb "corraltrig" "Box §1.4, p. 33"]
theorem box_1_4_abs_sin_cos_le_one (x : ℝ) : |Real.sin x| ≤ 1 ∧ |Real.cos x| ≤ 1 :=
  ⟨Real.abs_sin_le_one x, Real.abs_cos_le_one x⟩

/-- Coterminal angles (differing by a full turn) have the same sine and cosine, and tangent has
period `π` (TR-028). -/
@[kb "corraltrig" "Box §1.4, p. 37"]
theorem box_1_4_coterminal (x : ℝ) :
    Real.sin (x + 2 * Real.pi) = Real.sin x ∧ Real.cos (x + 2 * Real.pi) = Real.cos x ∧
      Real.tan (x + Real.pi) = Real.tan x :=
  ⟨Real.sin_add_two_pi x, Real.cos_add_two_pi x, Real.tan_add_pi x⟩

/-- Adding or subtracting a half turn negates sine and cosine and preserves tangent (TR-032). -/
@[kb "corraltrig" "Box §1.5, p. 42"]
theorem box_1_5_half_turn (t : ℝ) :
    Real.sin (t + Real.pi) = -Real.sin t ∧ Real.cos (t + Real.pi) = -Real.cos t ∧
      Real.tan (t + Real.pi) = Real.tan t ∧ Real.sin (t - Real.pi) = -Real.sin t ∧
      Real.cos (t - Real.pi) = -Real.cos t :=
  ⟨Real.sin_add_pi t, Real.cos_add_pi t, Real.tan_add_pi t, Real.sin_sub_pi t,
    Real.cos_sub_pi t⟩

/-- Parity: sine and tangent are odd, cosine is even (TR-033). -/
@[kb "corraltrig" "Box §1.5, p. 43"]
theorem box_1_5_even_odd (t : ℝ) :
    Real.sin (-t) = -Real.sin t ∧ Real.cos (-t) = Real.cos t ∧ Real.tan (-t) = -Real.tan t :=
  ⟨Real.sin_neg t, Real.cos_neg t, Real.tan_neg t⟩

/-- A function is even if `f (-x) = f x` and odd if `f (-x) = -f x` (TR-034). -/
@[kb "corraltrig" "Def §1.5, p. 43"]
theorem def_1_5_even_odd (f : ℝ → ℝ) :
    (Function.Even f ↔ ∀ x, f (-x) = f x) ∧ (Function.Odd f ↔ ∀ x, f (-x) = -f x) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- Reflecting about the vertical axis (`π - t`) keeps sine and flips cosine and tangent
(TR-035). -/
@[kb "corraltrig" "Box §1.5, p. 43"]
theorem box_1_5_pi_sub (t : ℝ) :
    Real.sin (Real.pi - t) = Real.sin t ∧ Real.cos (Real.pi - t) = -Real.cos t ∧
      Real.tan (Real.pi - t) = -Real.tan t :=
  ⟨Real.sin_pi_sub t, Real.cos_pi_sub t, Real.tan_pi_sub t⟩

/-- Cofunction identities: sine and cosine of the complement swap (TR-046). -/
@[kb "corraltrig" "Box §1.5, p. 43"]
theorem box_1_5_cofunction (t : ℝ) :
    Real.sin (Real.pi / 2 - t) = Real.cos t ∧ Real.cos (Real.pi / 2 - t) = Real.sin t ∧
      Real.tan (Real.pi / 2 - t) = (Real.tan t)⁻¹ :=
  ⟨Real.sin_pi_div_two_sub t, Real.cos_pi_div_two_sub t, Real.tan_pi_div_two_sub t⟩

end UndergradKB.Trigonometry.Course.Corral
