import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle
import Mathlib.Geometry.Euclidean.Circumcenter
import Mathlib.Geometry.Euclidean.PerpBisector
import UndergradKB.Common.Attr

/-! # Right triangles and the circumcenter (Corral §1.1-1.2, §2; OpenStax §7.2)

Complementary acute angles, the hypotenuse being longest, independence of the trigonometric ratios from the
chosen right triangle, the 45-45-90 and 30-60-90 triangles, and the circumcenter lying on each perpendicular
bisector of a side.
-/

namespace UndergradKB.Trigonometry

open EuclideanGeometry Real

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- In a triangle with a right angle at `p₂`, the other two angles add up to `π/2`. (TR-011) -/
@[kb "corraltrig" "Box §1.1, p. 10"]
theorem angle_add_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (h12 : p₂ ≠ p₁) : ∠ p₂ p₃ p₁ + ∠ p₃ p₁ p₂ = π / 2 := by
  have := angle_add_angle_add_angle_eq_pi p₃ h12
  rw [h] at this
  linarith

/-- In a triangle with a right angle at `p₂`, the hypotenuse is strictly longer than each leg. (TR-014) -/
@[kb "corraltrig" "Box §1.1, p. 12"]
theorem legs_lt_hypotenuse {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) (h12 : p₁ ≠ p₂)
    (h32 : p₃ ≠ p₂) : dist p₁ p₂ < dist p₁ p₃ ∧ dist p₃ p₂ < dist p₁ p₃ := by
  have hp := (dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two p₁ p₂ p₃).2 h
  have a := dist_pos.2 h12
  have b := dist_pos.2 h32
  have c : 0 ≤ dist p₁ p₃ := dist_nonneg
  constructor <;> nlinarith

/-- The sine, cosine and tangent of an acute angle of a right triangle depend only on that angle, not on
the size of the triangle: two right triangles with equal acute angles have equal side ratios. (TR-017) -/
@[kb "corraltrig" "Box §1.2, p. 17"]
theorem side_ratios_eq_of_angle_eq {p₁ p₂ p₃ q₁ q₂ q₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (h' : ∠ q₁ q₂ q₃ = π / 2) (h0 : p₁ ≠ p₂ ∨ p₃ ≠ p₂) (h0' : q₁ ≠ q₂ ∨ q₃ ≠ q₂)
    (hang : ∠ p₂ p₃ p₁ = ∠ q₂ q₃ q₁) :
    dist p₁ p₂ / dist p₁ p₃ = dist q₁ q₂ / dist q₁ q₃ ∧
    dist p₃ p₂ / dist p₁ p₃ = dist q₃ q₂ / dist q₁ q₃ ∧
    dist p₁ p₂ / dist p₃ p₂ = dist q₁ q₂ / dist q₃ q₂ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← sin_angle_of_angle_eq_pi_div_two h h0, ← sin_angle_of_angle_eq_pi_div_two h' h0', hang]
  · rw [← cos_angle_of_angle_eq_pi_div_two h, ← cos_angle_of_angle_eq_pi_div_two h', hang]
  · rw [← tan_angle_of_angle_eq_pi_div_two h, ← tan_angle_of_angle_eq_pi_div_two h', hang]

/-- **45-45-90 triangle**: a right triangle with an acute angle `π/4` is isosceles and its hypotenuse is
`√2` times a leg (sides in ratio `1 : 1 : √2`). (TR-019) -/
@[kb "corraltrig" "Box §1.2, p. 19"]
theorem right_triangle_pi_div_four {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (hang : ∠ p₂ p₃ p₁ = π / 4) :
    dist p₁ p₂ = dist p₂ p₃ ∧ dist p₁ p₃ = √2 * dist p₂ p₃ := by
  have hs := sin_angle_mul_dist_of_angle_eq_pi_div_two h
  have hc := cos_angle_mul_dist_of_angle_eq_pi_div_two h
  rw [hang, Real.sin_pi_div_four] at hs
  rw [hang, Real.cos_pi_div_four, dist_comm p₃ p₂] at hc
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  constructor
  · linarith
  · rw [← hc]
    linear_combination (-(1 / 2) * dist p₁ p₃) * h2

/-- **30-60-90 triangle**: a right triangle with an acute angle `π/6` has hypotenuse twice the short leg
and long leg `√3` times the short leg (sides in ratio `1 : √3 : 2`). (TR-019) -/
@[kb "corraltrig" "Box §1.2, p. 19"]
theorem right_triangle_pi_div_six {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (hang : ∠ p₂ p₃ p₁ = π / 6) :
    dist p₁ p₃ = 2 * dist p₁ p₂ ∧ dist p₂ p₃ = √3 * dist p₁ p₂ := by
  have hs := sin_angle_mul_dist_of_angle_eq_pi_div_two h
  have hc := cos_angle_mul_dist_of_angle_eq_pi_div_two h
  rw [hang, Real.sin_pi_div_six] at hs
  rw [hang, Real.cos_pi_div_six, dist_comm p₃ p₂] at hc
  constructor
  · linarith
  · have hd : dist p₁ p₃ = 2 * dist p₁ p₂ := by linarith
    rw [← hc, hd]
    ring

/-- The circumcenter of a triangle lies on the perpendicular bisector of each side. (TR-093) -/
@[kb "corraltrig" "Cor 2.7, p. 69"]
theorem circumcenter_mem_perpBisector (t : Affine.Triangle ℝ P) {i j : Fin 3} (_hij : i ≠ j) :
    t.circumcenter ∈ AffineSubspace.perpBisector (t.points i) (t.points j) := by
  rw [AffineSubspace.mem_perpBisector_iff_dist_eq, t.dist_circumcenter_eq_circumradius',
    t.dist_circumcenter_eq_circumradius']

end UndergradKB.Trigonometry
