import Mathlib.Geometry.Euclidean.Angle.Sphere
import Mathlib.Geometry.Euclidean.Incenter.Basic
import Mathlib.Geometry.Euclidean.Triangle
import UndergradKB.Common.Attr

/-! # Area of a triangle (Corral §2.4, §2.5; OpenStax §10.1, §10.2)

A triangle is Mathlib's `Affine.Triangle ℝ P` (three affinely independent points of a real inner product
space; any dimension). Following Corral §2.4, the area is half a base times the corresponding height,
`area t = dist (t.points 1) (t.points 2) * t.height 0 / 2`, with Mathlib's `Affine.Simplex.height`
(distance from a vertex to the foot of its altitude). `area_eq_dist_mul_height_div_two` shows that every
side may serve as the base.

Results (books' notation: `a, b, c` the sides opposite the vertices with angles `A, B, C`; `s` the
semiperimeter; `R`, `r` the circumradius and inradius):
* `area_eq_mul_mul_sin_div_two`: `K = ½ bc sin A` (Corral §2.4, OpenStax §10.1);
* `area_eq_sq_mul_sin_mul_sin_div_sin`: `K = a² sin B sin C / (2 sin A)` (Corral §2.4);
* `heron`: `K = √(s(s-a)(s-b)(s-c))` (Corral §2.4, OpenStax §10.2), and the stable forms
  `heron_kahan`, `area_eq_qin_jiushao` (Corral §2.4);
* `area_eq_mul_mul_mul_div_four_mul_circumradius`, `circumradius_eq_heron` (Corral Theorem 2.8, Corollary 2.9);
* `inradius_eq_area_div_semiperimeter`, `inradius_eq_sqrt`, `inradius_eq_mul_tan_half`
  (Corral Theorems 2.10, 2.11).
-/

namespace UndergradKB.Trigonometry

open EuclideanGeometry Real
open scoped EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- The area of a triangle: half the side opposite vertex `0` (the base) times the height of vertex `0`
(Corral §2.4: area is one half base times height). Any side gives the same value
(`area_eq_dist_mul_height_div_two`). -/
noncomputable def area (t : Affine.Triangle ℝ P) : ℝ :=
  dist (t.points 1) (t.points 2) * t.height 0 / 2

section basic

variable (t : Affine.Triangle ℝ P)

lemma not_collinear_of_ne {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    ¬Collinear ℝ ({t.points i₁, t.points i₂, t.points i₃} : Set P) :=
  (affineIndependent_iff_not_collinear_of_ne h₁₂ h₁₃ h₂₃).1 t.independent

lemma dist_points_pos {i j : Fin 3} (h : i ≠ j) : 0 < dist (t.points i) (t.points j) :=
  dist_pos.2 (t.independent.injective.ne h)

lemma sin_angle_points_pos {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    0 < Real.sin (∠ (t.points i₁) (t.points i₂) (t.points i₃)) :=
  sin_pos_of_not_collinear (not_collinear_of_ne t h₁₂ h₁₃ h₂₃)

/-- Area as half the product of the two sides at the vertex `1` times the sine of the angle there. -/
private lemma area_eq_at_one :
    area t = dist (t.points 0) (t.points 1) * dist (t.points 1) (t.points 2) *
      Real.sin (∠ (t.points 0) (t.points 1) (t.points 2)) / 2 := by
  rw [area, t.height_eq_sin_mul_dist (i₁ := 0) (i₂ := 1) (i₃ := 2) (by decide) (by decide)
    (by decide)]
  ring

private lemma area_eq_at_two :
    area t = dist (t.points 0) (t.points 2) * dist (t.points 2) (t.points 1) *
      Real.sin (∠ (t.points 0) (t.points 2) (t.points 1)) / 2 := by
  rw [area, t.height_eq_sin_mul_dist (i₂ := 2) (i₃ := 1) (by decide) (by decide) (by decide),
    dist_comm (t.points 2) (t.points 1)]
  ring

private lemma area_eq_at_zero :
    area t = dist (t.points 1) (t.points 0) * dist (t.points 0) (t.points 2) *
      Real.sin (∠ (t.points 1) (t.points 0) (t.points 2)) / 2 := by
  have h := law_sin (t.points 0) (t.points 1) (t.points 2)
  rw [area_eq_at_one, angle_comm (t.points 1) (t.points 0) (t.points 2),
    dist_comm (t.points 1) (t.points 0)]
  rw [dist_comm (t.points 2) (t.points 0)] at h
  linear_combination dist (t.points 0) (t.points 1) / 2 * h

/-- **Area from two sides and the included angle**: the area of a triangle is half the product of two
sides times the sine of the angle between them, `K = ½ bc sin A` (and its cyclic versions). -/
@[kb "corraltrig" "Box §2.4 (area = ½ bc sin A), p. 62"]
theorem area_eq_mul_mul_sin_div_two {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃)
    (h₂₃ : i₂ ≠ i₃) :
    area t = dist (t.points i₁) (t.points i₂) * dist (t.points i₁) (t.points i₃) *
      Real.sin (∠ (t.points i₂) (t.points i₁) (t.points i₃)) / 2 := by
  have e0 := area_eq_at_zero t
  have e1 := area_eq_at_one t
  have e2 := area_eq_at_two t
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases i₃ <;> simp at h₁₂ h₁₃ h₂₃ ⊢
  · rw [e0, dist_comm (t.points 1) (t.points 0)]
  · rw [e0, angle_comm, dist_comm (t.points 1) (t.points 0)]; ring
  · rw [e1, dist_comm (t.points 0) (t.points 1)]
  · rw [e1, angle_comm, dist_comm (t.points 0) (t.points 1)]; ring
  · rw [e2, dist_comm (t.points 0) (t.points 2), dist_comm (t.points 2) (t.points 1)]
  · rw [e2, angle_comm, dist_comm (t.points 0) (t.points 2)]; ring

/-- The OpenStax form of the same result (§10.1): area is half the product of two sides and the sine of
the included angle. -/
@[kb "openstaxalgtrig2e" "§10.1 Area of an oblique triangle, p. 887"]
theorem area_eq_half_mul_sin_included {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃)
    (h₂₃ : i₂ ≠ i₃) :
    area t = 1 / 2 * dist (t.points i₁) (t.points i₂) * dist (t.points i₁) (t.points i₃) *
      Real.sin (∠ (t.points i₂) (t.points i₁) (t.points i₃)) := by
  rw [area_eq_mul_mul_sin_div_two t h₁₂ h₁₃ h₂₃]; ring

/-- Any side can serve as the base: the area is half of any side times the height of the opposite
vertex. -/
@[kb "corraltrig" "Box §2.4 (area = ½ base × height), p. 62"]
theorem area_eq_dist_mul_height_div_two {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃)
    (h₂₃ : i₂ ≠ i₃) :
    area t = dist (t.points i₂) (t.points i₃) * t.height i₁ / 2 := by
  rw [t.height_eq_sin_mul_dist h₁₂ h₁₃ h₂₃,
    area_eq_mul_mul_sin_div_two t (Ne.symm h₁₂) h₂₃ h₁₃]
  rw [dist_comm (t.points i₁) (t.points i₂)]
  ring

lemma area_pos : 0 < area t := by
  rw [area]
  have := dist_points_pos t (i := 1) (j := 2) (by decide)
  have := t.height_pos 0
  positivity

end basic

end UndergradKB.Trigonometry
