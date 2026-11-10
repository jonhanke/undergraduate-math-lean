import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Geometry.Euclidean.Inversion.Basic
import UndergradKB.Common.Attr

/-! # Spherical geometry (Petrunin, chapter 16)

The unit sphere `Σ` of a real inner product space `V` (the book uses `ℝ³`; nothing here needs the dimension),
centred at the origin. The spherical distance `ABₛ` is the angle `∠AOB` between the position vectors
(`InnerProductGeometry.angle A B`, Definition p. 132). The angle of a spherical triangle at `C` is the angle
between the tangent half-lines at `C` of the arcs `[CA]ₛ` and `[CB]ₛ`, i.e. between the tangent vectors
`A - ⟪A, C⟫ C` and `B - ⟪B, C⟫ C` (the components of `A`, `B` orthogonal to `C`).

* `spherical_pythagorean` (Theorem 16.12): in a spherical triangle with a right angle at `C`,
  `cos c = cos a · cos b`.
* `stereographic_eq_inversion` (Exercise 16.6): the stereographic projection from the pole `S` to the plane
  through `O` perpendicular to `OS` is the restriction of the inversion across the sphere with centre `S` and
  radius `√2`, and the inverse projection is its restriction to the plane. -/

namespace UndergradKB.Geometry

open InnerProductGeometry RealInnerProductSpace Real

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The tangent vector at the point `C` of the unit sphere of the great-circle arc from `C` towards `A`:
the component of `A` orthogonal to `C`. -/
noncomputable def sphTangent (C A : V) : V := A - ⟪A, C⟫ • C

/-- The (absolute) angle `|∡ₛ ACB|` of a spherical triangle at the vertex `C` (Petrunin, p. 132): the angle
between the tangent half-lines at `C` of the arcs `[CA]ₛ` and `[CB]ₛ`. -/
noncomputable def sphAngle (A C B : V) : ℝ := angle (sphTangent C A) (sphTangent C B)

theorem inner_sphTangent_self {C A : V} (hC : ‖C‖ = 1) : ⟪sphTangent C A, C⟫ = 0 := by
  simp [sphTangent, inner_sub_left, inner_smul_left, hC]

/-- **Spherical Pythagorean theorem** (Petrunin, Theorem 16.12): for points `A`, `B`, `C` of the unit sphere
with a right angle at `C`, and `a = BCₛ`, `b = CAₛ`, `c = ABₛ`, we have `cos c = cos a · cos b`. -/
@[kb "petrunin2025" "Theorem 16.12, p. 137"]
theorem spherical_pythagorean {A B C : V} (hA : ‖A‖ = 1) (hB : ‖B‖ = 1) (hC : ‖C‖ = 1)
    (hright : sphAngle A C B = π / 2) :
    Real.cos (angle A B) = Real.cos (angle B C) * Real.cos (angle C A) := by
  have h0 : ⟪sphTangent C A, sphTangent C B⟫ = 0 :=
    (inner_eq_zero_iff_angle_eq_pi_div_two _ _).mpr hright
  simp only [cos_angle, hA, hB, hC, mul_one, div_one]
  have hCC : ⟪C, C⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hC, one_pow]
  have expand : ⟪A, B⟫ = ⟪sphTangent C A, sphTangent C B⟫ + ⟪A, C⟫ * ⟪B, C⟫ := by
    simp only [sphTangent, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      real_inner_comm B C, hCC, RCLike.conj_to_real]
    ring
  rw [expand, h0, zero_add, real_inner_comm C A, mul_comm]

/-- **Stereographic projection is an inversion** (Petrunin, Exercise 16.6). Let `N` be a unit vector, `S = -N`
the south pole of the unit sphere `Σ` and `Π` the plane through `O` orthogonal to `N`. For `P ∈ Σ`,
`P ≠ S`, the inversion of `P` across the sphere with centre `S` and radius `√2` is the point where the line
`(SP)` meets `Π` (the stereographic projection of `P`); conversely the inversion maps every point of `Π` to
`Σ`. -/
@[kb "petrunin2025" "Exercise 16.6, p. 136"]
theorem stereographic_eq_inversion {N : V} (hN : ‖N‖ = 1) :
    (∀ P : V, ‖P‖ = 1 → P ≠ -N →
      ⟪EuclideanGeometry.inversion (-N) (Real.sqrt 2) P, N⟫ = 0 ∧
      ∃ t : ℝ, EuclideanGeometry.inversion (-N) (Real.sqrt 2) P = -N + t • (P - -N)) ∧
    (∀ X : V, ⟪X, N⟫ = 0 → ‖EuclideanGeometry.inversion (-N) (Real.sqrt 2) X‖ = 1) := by
  have hNN : ⟪N, N⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hN, one_pow]
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  constructor
  · intro P hP hPS
    have hPP : ⟪P, P⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hP, one_pow]
    have hd : dist P (-N) ^ 2 = 2 + 2 * ⟪P, N⟫ := by
      rw [dist_eq_norm, ← real_inner_self_eq_norm_sq, sub_neg_eq_add, inner_add_left,
        inner_add_right, inner_add_right, hPP, hNN, real_inner_comm N P]
      ring
    have hd0 : dist P (-N) ≠ 0 := dist_ne_zero.mpr hPS
    have hd2 : (0 : ℝ) < dist P (-N) ^ 2 := by positivity
    refine ⟨?_, ⟨(Real.sqrt 2 / dist P (-N)) ^ 2, ?_⟩⟩
    · rw [EuclideanGeometry.inversion, vsub_eq_sub, vadd_eq_add, inner_add_left, inner_smul_left,
        inner_neg_left, hNN, RCLike.conj_to_real, div_pow, hs, sub_neg_eq_add, inner_add_left, hNN, hd]
      have h1 : 2 + 2 * ⟪P, N⟫ ≠ 0 := by rw [← hd]; exact hd2.ne'
      have h1' : 1 + ⟪P, N⟫ ≠ 0 := fun h => h1 (by linarith)
      field_simp
      ring
    · rw [EuclideanGeometry.inversion, vsub_eq_sub, vadd_eq_add, add_comm]
  · intro X hX
    by_cases hXS : X = -N
    · subst hXS
      simp [EuclideanGeometry.inversion_self, hN]
    have hNX : ⟪N, X⟫ = 0 := by rw [real_inner_comm]; exact hX
    have hd : dist X (-N) ^ 2 = ⟪X, X⟫ + 1 := by
      rw [dist_eq_norm, ← real_inner_self_eq_norm_sq, sub_neg_eq_add, inner_add_left,
        inner_add_right, inner_add_right, hNN, hNX, hX]
      ring
    have hd0 : dist X (-N) ≠ 0 := dist_ne_zero.mpr hXS
    have hd2 : (0 : ℝ) < dist X (-N) ^ 2 := by positivity
    rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, one_pow, ← real_inner_self_eq_norm_sq]
    rw [EuclideanGeometry.inversion, vsub_eq_sub, vadd_eq_add, div_pow, hs, sub_neg_eq_add]
    set k := 2 / dist X (-N) ^ 2 with hk
    have hk' : k * (⟪X, X⟫ + 1) = 2 := by rw [hk, ← hd]; field_simp
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, inner_neg_left,
      inner_neg_right, RCLike.conj_to_real, hNN, hX, hNX]
    linear_combination k * hk'

/-- **Every circle in space is an intersection of two spheres** (Petrunin, Observation 16.10): the circle with
centre `c` and radius `r` in the plane through `c` orthogonal to the unit vector `n` is the intersection of the
sphere about `c` of radius `r` and the sphere about `c + n` of radius `√(r² + 1)`. -/
@[kb "petrunin2025" "Observation 16.10, p. 136"]
theorem circle_eq_inter_spheres {c n : V} (hn : ‖n‖ = 1) {r : ℝ} (_hr : 0 ≤ r) :
    {x : V | ⟪x - c, n⟫ = 0 ∧ ‖x - c‖ = r} =
      Metric.sphere c r ∩ Metric.sphere (c + n) (Real.sqrt (r ^ 2 + 1)) := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Metric.mem_sphere, dist_eq_norm]
  have hnn : ⟪n, n⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hn, one_pow]
  have key : ‖x - (c + n)‖ ^ 2 = ‖x - c‖ ^ 2 - 2 * ⟪x - c, n⟫ + 1 := by
    rw [show x - (c + n) = (x - c) - n by abel, norm_sub_sq_real, hn]; ring
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨h1, ?_⟩
    rw [← Real.sqrt_sq (norm_nonneg _), key, h0, h1]; ring_nf
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1⟩
    have h2' : ‖x - (c + n)‖ ^ 2 = r ^ 2 + 1 := by
      rw [h2, Real.sq_sqrt (by positivity)]
    rw [key, h1] at h2'
    linarith

end UndergradKB.Geometry
