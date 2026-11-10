import Mathlib.Geometry.Euclidean.Angle.Sphere
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Geometry.Euclidean.Circumcenter
import UndergradKB.Common.Attr

/-! # Course layer: Corral, *Trigonometry*, Chapter 2

Thin theorems in the book's terms (laws of sines and cosines, inscribed angles, circumradius)
whose proofs are Mathlib declarations.  All angles are in radians.
-/

namespace UndergradKB.Trigonometry.Course.Corral

open EuclideanGeometry Module

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- Law of sines, cross-multiplied: sides are proportional to the sines of the opposite angles
(TR-074). -/
@[kb "corraltrig" "Thm 2.1, p. 46"]
theorem thm_2_1_law_of_sines (p₁ p₂ p₃ : P) :
    Real.sin (∠ p₁ p₂ p₃) * dist p₂ p₃ = Real.sin (∠ p₃ p₁ p₂) * dist p₃ p₁ :=
  law_sin p₁ p₂ p₃

/-- In a non-degenerate triangle, the larger angle faces the larger side (TR-076). -/
@[kb "corraltrig" "Box §2.1, p. 50"]
theorem box_2_1_larger_angle_larger_side {a b c : P}
    (h : ¬Collinear ℝ ({a, b, c} : Set P)) :
    ∠ a c b < ∠ a b c ↔ dist a b < dist a c :=
  angle_lt_iff_dist_lt h

/-- Law of cosines: the square of a side is the sum of the other squares minus twice their product
times the cosine of the included angle (TR-079). -/
@[kb "corraltrig" "Thm 2.2, p. 52"]
theorem thm_2_2_law_of_cosines (p₁ p₂ p₃ : P) :
    dist p₁ p₃ * dist p₁ p₃ = dist p₁ p₂ * dist p₁ p₂ + dist p₃ p₂ * dist p₃ p₂ -
      2 * dist p₁ p₂ * dist p₃ p₂ * Real.cos (∠ p₁ p₂ p₃) :=
  law_cos p₁ p₂ p₃

section Plane

variable [Fact (finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

/-- Inscribed angle theorem (oriented form): the central angle is twice the inscribed angle
(TR-090). -/
@[kb "corraltrig" "Thm 2.4, p. 67"]
theorem thm_2_4_inscribed_angle {s : Sphere P} {p₁ p₂ p₃ : P} (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s)
    (hp₃ : p₃ ∈ s) (hp₂p₁ : p₂ ≠ p₁) (hp₂p₃ : p₂ ≠ p₃) :
    ∡ p₁ s.center p₃ = (2 : ℤ) • ∡ p₁ p₂ p₃ :=
  Sphere.oangle_center_eq_two_zsmul_oangle hp₁ hp₂ hp₃ hp₂p₁ hp₂p₃

omit [Module.Oriented ℝ V (Fin 2)] in
/-- Inscribed angle theorem (unoriented form, acute inscribed angle) (TR-090). -/
theorem thm_2_4_inscribed_angle_unoriented {s : Sphere P} {p₁ p₂ p₃ : P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s) (hp₂p₁ : p₂ ≠ p₁) (hp₂p₃ : p₂ ≠ p₃)
    (h : 2 * ∠ p₁ p₂ p₃ ≤ Real.pi) : ∠ p₁ s.center p₃ = 2 * ∠ p₁ p₂ p₃ :=
  Sphere.angle_center_eq_two_mul_angle_of_two_mul_angle_le_pi hp₁ hp₂ hp₃ hp₂p₁ hp₂p₃ h

omit [Module.Oriented ℝ V (Fin 2)] in
/-- Inscribed angle theorem (unoriented form, obtuse inscribed angle) (TR-090). -/
theorem thm_2_4_inscribed_angle_obtuse {s : Sphere P} {p₁ p₂ p₃ : P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s) (hp₂p₁ : p₂ ≠ p₁) (hp₂p₃ : p₂ ≠ p₃)
    (h : Real.pi ≤ 2 * ∠ p₁ p₂ p₃) : ∠ p₁ s.center p₃ = 2 * Real.pi - 2 * ∠ p₁ p₂ p₃ :=
  Sphere.angle_center_eq_two_pi_sub_two_mul_angle_of_pi_le_two_mul_angle hp₁ hp₂ hp₃ hp₂p₁
    hp₂p₃ h

/-- Inscribed angles on the same arc are equal modulo a half turn (TR-090). -/
theorem thm_2_4_same_arc {s : Sphere P} {p₁ p₂ p₃ p₄ : P} (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s)
    (hp₃ : p₃ ∈ s) (hp₄ : p₄ ∈ s) (hp₂p₁ : p₂ ≠ p₁) (hp₂p₄ : p₂ ≠ p₄) (hp₃p₁ : p₃ ≠ p₁)
    (hp₃p₄ : p₃ ≠ p₄) : (2 : ℤ) • ∡ p₁ p₂ p₄ = (2 : ℤ) • ∡ p₁ p₃ p₄ :=
  Sphere.two_zsmul_oangle_eq hp₁ hp₂ hp₃ hp₄ hp₂p₁ hp₂p₄ hp₃p₁ hp₃p₄

/-- Extended law of sines: a side over the sine of the opposite angle is the circumdiameter
(TR-091). -/
@[kb "corraltrig" "Thm 2.5, p. 67"]
theorem thm_2_5_circumdiameter (t : Affine.Triangle ℝ P) {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂)
    (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    dist (t.points i₁) (t.points i₃) /
      |Real.Angle.sin (∡ (t.points i₁) (t.points i₂) (t.points i₃))| = 2 * t.circumradius :=
  Affine.Triangle.dist_div_sin_oangle_eq_two_mul_circumradius t h₁₂ h₁₃ h₂₃

/-- The same statement for three points on a circle of radius `s.radius` (TR-091). -/
theorem thm_2_5_circle_diameter {s : Sphere P} {p₁ p₂ p₃ : P} (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s)
    (hp₃ : p₃ ∈ s) (hp₁p₂ : p₁ ≠ p₂) (hp₁p₃ : p₁ ≠ p₃) (hp₂p₃ : p₂ ≠ p₃) :
    dist p₁ p₃ / |Real.Angle.sin (∡ p₁ p₂ p₃)| = 2 * s.radius :=
  Sphere.dist_div_sin_oangle_eq_two_mul_radius hp₁ hp₂ hp₃ hp₁p₂ hp₁p₃ hp₂p₃

omit [Module.Oriented ℝ V (Fin 2)] in
/-- Converse of Thales in the plane: a right angle at a point of a circle means the opposite side
is a diameter (TR-092). -/
@[kb "corraltrig" "Cor 2.6, p. 68"]
theorem cor_2_6_hypotenuse_diameter {p₁ p₂ p₃ : P} {s : Sphere P} (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s)
    (hp₃ : p₃ ∈ s) (hne₁₂ : p₁ ≠ p₂) (hne₂₃ : p₂ ≠ p₃) (hangle : ∠ p₁ p₂ p₃ = Real.pi / 2) :
    s.IsDiameter p₁ p₃ :=
  Sphere.isDiameter_of_angle_eq_pi_div_two hp₁ hp₂ hp₃ hne₁₂ hne₂₃ hangle

end Plane

/-- Thales: for a diameter `p₁p₃`, the angle at `p₂` is right exactly when `p₂` is on the circle
(TR-092). -/
theorem cor_2_6_thales {p₁ p₂ p₃ : P} {s : Sphere P} (hd : s.IsDiameter p₁ p₃) :
    ∠ p₁ p₂ p₃ = Real.pi / 2 ↔ p₂ ∈ s :=
  Sphere.thales_theorem hd

end UndergradKB.Trigonometry.Course.Corral
