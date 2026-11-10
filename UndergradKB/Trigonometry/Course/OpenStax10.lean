import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Geometry.Euclidean.Triangle
import UndergradKB.Common.Attr

/-! # Course layer: OpenStax *Algebra and Trigonometry* 2e, Chapter 10

Thin theorems in the book's terms (laws of sines and cosines, complex numbers in the plane and in
polar form) whose proofs are Mathlib declarations.  All angles are in radians.
-/

namespace UndergradKB.Trigonometry.Course.OpenStax

open EuclideanGeometry

section Geometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- Law of sines, cross-multiplied: sides are proportional to the sines of the opposite angles
(TR-074). -/
@[kb "openstaxalgtrig2e" "§10.1, p. 881"]
theorem s10_1_law_of_sines (p₁ p₂ p₃ : P) :
    Real.sin (∠ p₁ p₂ p₃) * dist p₂ p₃ = Real.sin (∠ p₃ p₁ p₂) * dist p₃ p₁ :=
  law_sin p₁ p₂ p₃

/-- Law of cosines: the square of a side is the sum of the other squares minus twice their product
times the cosine of the included angle (TR-079). -/
@[kb "openstaxalgtrig2e" "§10.2, p. 898"]
theorem s10_2_law_of_cosines (p₁ p₂ p₃ : P) :
    dist p₁ p₃ * dist p₁ p₃ = dist p₁ p₂ * dist p₁ p₂ + dist p₃ p₂ * dist p₃ p₂ -
      2 * dist p₁ p₂ * dist p₃ p₂ * Real.cos (∠ p₁ p₂ p₃) :=
  law_cos p₁ p₂ p₃

end Geometry

/-- A complex number `a + bi` is plotted at the point `(a, b)` of the plane (TR-200). -/
@[kb "openstaxalgtrig2e" "§10.5, p. 943"]
theorem s10_5_complex_plane :
    (∀ z : ℂ, Complex.equivRealProd z = (z.re, z.im)) ∧
      ∀ p : ℝ × ℝ, Complex.equivRealProd.symm p = p.1 + p.2 * Complex.I :=
  ⟨fun _ => rfl, Complex.equivRealProd_symm_apply⟩

/-- The absolute value of `z = a + bi` is `√(a² + b²)`, its distance from the origin (TR-185). -/
@[kb "openstaxalgtrig2e" "§10.5, p. 945"]
theorem s10_5_modulus (z : ℂ) :
    ‖z‖ = √(z.re * z.re + z.im * z.im) ∧ ‖z‖ ^ 2 = z.re * z.re + z.im * z.im :=
  ⟨by rw [Complex.norm_def, Complex.normSq_apply], by rw [Complex.sq_norm, Complex.normSq_apply]⟩

/-- Polar form: every complex number is its modulus times `cos θ + i sin θ`, with `θ` the
principal argument; and the rectangular coordinates are `r cos θ` and `r sin θ` (TR-186). -/
@[kb "openstaxalgtrig2e" "§10.5, p. 947"]
theorem s10_5_polar_form (z : ℂ) :
    (‖z‖ : ℂ) * (Complex.cos (Complex.arg z) + Complex.sin (Complex.arg z) * Complex.I) = z ∧
      ‖z‖ * Real.cos (Complex.arg z) = z.re ∧ ‖z‖ * Real.sin (Complex.arg z) = z.im :=
  ⟨Complex.norm_mul_cos_add_sin_mul_I z, Complex.norm_mul_cos_arg z, Complex.norm_mul_sin_arg z⟩

end UndergradKB.Trigonometry.Course.OpenStax
