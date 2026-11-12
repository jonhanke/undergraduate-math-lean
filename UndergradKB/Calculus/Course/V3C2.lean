import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Convex.Segment
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Geometry.Euclidean.Angle.Unoriented.CrossProduct
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import UndergradKB.Calculus.LinesPlanes
import UndergradKB.Calculus.QuadricsCoordinates
import UndergradKB.Calculus.Vectors
import UndergradKB.Common.Attr

/-!
# OpenStax Calculus Volume 3, Chapter 2 (vectors in space): course layer

Thin wrappers around Mathlib. Vectors for algebraic statements (components, dot and cross product)
are `Fin n → ℝ`; vectors for metric statements (magnitude, distance, angle, projection) are
`EuclideanSpace ℝ (Fin n)`, written `!₂[x, y, z]`.
-/

namespace UndergradKB.Calculus.Course.V3C2

open Matrix
open scoped InnerProductSpace

/-- OpenStax Calculus 3:§2.1 Definition (operations in component form) (CA-424).
Sum, difference and scalar multiple of vectors are computed componentwise. -/
@[kb "openstaxcalculus2016" "3:§2.1 Definition (operations in component form), p. 106"]
theorem vector_operations_componentwise {n : ℕ} (u v : Fin n → ℝ) (c : ℝ) (i : Fin n) :
    (u + v) i = u i + v i ∧ (u - v) i = u i - v i ∧ (c • u) i = c * u i :=
  ⟨rfl, rfl, rfl⟩

/-- OpenStax Calculus 3:§2.1 Definition (component form) (CA-425).
The vector from initial point `P` to terminal point `Q` has components `Q i - P i`. -/
@[kb "openstaxcalculus2016" "3:§2.1 Definition (component form), p. 104"]
theorem vector_from_points_components {n : ℕ} (P Q : Fin n → ℝ) (i : Fin n) :
    (Q -ᵥ P) i = Q i - P i :=
  rfl

/-- OpenStax Calculus 3:§2.1 text (magnitude formula) (CA-426).
The magnitude of a vector in the plane is the square root of the sum of the squares of its
components. -/
@[kb "openstaxcalculus2016" "3:§2.1 text (magnitude formula), p. 105"]
theorem magnitude_plane (x y : ℝ) : ‖!₂[x, y]‖ = √(x ^ 2 + y ^ 2) := by
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]

/-- OpenStax Calculus 3:§2.2 Rule: Properties of Vectors in Space (vector magnitude) (CA-426).
The magnitude of a vector in space is the square root of the sum of the squares of its components. -/
@[kb "openstaxcalculus2016" "3:§2.2 Rule: Properties of Vectors in Space (vector magnitude), p. 131"]
theorem magnitude_space (x y z : ℝ) : ‖!₂[x, y, z]‖ = √(x ^ 2 + y ^ 2 + z ^ 2) := by
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_three]

/-- OpenStax Calculus 3:§2.1 text (magnitude formula) (CA-426).
The magnitude is zero only for the zero vector. -/
@[kb "openstaxcalculus2016" "3:§2.1 text (magnitude formula), p. 105"]
theorem magnitude_eq_zero_iff {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) : ‖v‖ = 0 ↔ v = 0 :=
  norm_eq_zero

/-- OpenStax Calculus 3:§2.1 text (triangle inequality) (CA-427).
The magnitude of a sum is at most the sum of the magnitudes. -/
@[kb "openstaxcalculus2016" "3:§2.1 text (triangle inequality), p. 101"]
theorem triangle_inequality {n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) : ‖u + v‖ ≤ ‖u‖ + ‖v‖ :=
  norm_add_le u v

/-- OpenStax Calculus 3:Theorem 2.1 (CA-428), algebraic properties of vectors.
Addition is commutative and associative with identity `0` and inverses; scalar multiplication
distributes over vector and scalar sums, is associative, `1` acts trivially, and `0 • u = 0`. -/
@[kb "openstaxcalculus2016" "3:Theorem 2.1, p. 107"]
theorem vector_algebra_properties {n : ℕ} (u v w : Fin n → ℝ) (α β : ℝ) :
    u + v = v + u ∧ (u + v) + w = u + (v + w) ∧ u + 0 = u ∧ u + -u = 0 ∧
      α • (u + v) = α • u + α • v ∧ (α + β) • u = α • u + β • u ∧
      (α * β) • u = α • (β • u) ∧ (1 : ℝ) • u = u ∧ (0 : ℝ) • u = 0 :=
  ⟨add_comm u v, add_assoc u v w, add_zero u, add_neg_cancel u, smul_add α u v, add_smul α β u,
    mul_smul α β u, one_smul ℝ u, zero_smul ℝ u⟩

/-- OpenStax Calculus 3:§2.1 text (unit vector, normalization) (CA-430).
Dividing a nonzero vector by its magnitude gives a vector of magnitude `1`. -/
@[kb "openstaxcalculus2016" "3:§2.1 text (unit vector, normalization), p. 108"]
theorem normalization_is_unit {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) :
    ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 :=
  norm_smul_inv_norm hv

/-- OpenStax Calculus 3:§2.1 text (standard unit vectors) (CA-431).
Every plane vector is `x i + y j`. -/
@[kb "openstaxcalculus2016" "3:§2.1 text (standard unit vectors, linear combination), p. 109"]
theorem plane_vector_standard_basis (x y : ℝ) :
    (![x, y] : Fin 2 → ℝ) = x • ![1, 0] + y • ![0, 1] := by
  ext i
  fin_cases i <;> simp

/-- OpenStax Calculus 3:§2.2 text (standard unit vectors in R^3) (CA-431).
Every space vector is `x i + y j + z k`. -/
@[kb "openstaxcalculus2016" "3:§2.2 text (standard unit vectors in R^3), p. 129"]
theorem space_vector_standard_basis (x y z : ℝ) :
    (![x, y, z] : Fin 3 → ℝ) = x • ![1, 0, 0] + y • ![0, 1, 0] + z • ![0, 0, 1] := by
  ext i
  fin_cases i <;> simp

/-- OpenStax Calculus 3:Theorem 2.2 (CA-433).
The distance between `(x₁, y₁, z₁)` and `(x₂, y₂, z₂)` is the square root of the sum of the squared
coordinate differences. -/
@[kb "openstaxcalculus2016" "3:Theorem 2.2, p. 120"]
theorem distance_formula_space (x₁ y₁ z₁ x₂ y₂ z₂ : ℝ) :
    dist !₂[x₁, y₁, z₁] !₂[x₂, y₂, z₂] =
      √((x₂ - x₁) ^ 2 + (y₂ - y₁) ^ 2 + (z₂ - z₁) ^ 2) := by
  rw [EuclideanSpace.dist_eq]
  simp only [Fin.sum_univ_three]
  simp only [Real.dist_eq, sq_abs]
  simp
  congr 1
  ring

/-- OpenStax Calculus 3:§2.2 Rule: Equation of a Sphere (Eq 2.2) (CA-435).
A point lies on the sphere of radius `r ≥ 0` centered at `(a, b, c)` iff
`(x-a)² + (y-b)² + (z-c)² = r²`. -/
@[kb "openstaxcalculus2016" "3:§2.2 Rule: Equation of a Sphere (Eq 2.2), p. 124"]
theorem sphere_equation (x y z a b c r : ℝ) (hr : 0 ≤ r) :
    !₂[x, y, z] ∈ Metric.sphere !₂[a, b, c] r ↔ (x - a) ^ 2 + (y - b) ^ 2 + (z - c) ^ 2 = r ^ 2 := by
  rw [Metric.mem_sphere, distance_formula_space]
  have e : (a - x) ^ 2 + (b - y) ^ 2 + (c - z) ^ 2 = (x - a) ^ 2 + (y - b) ^ 2 + (z - c) ^ 2 := by
    ring
  rw [e]
  constructor
  · intro h
    rw [← h, Real.sq_sqrt (by positivity)]
  · intro h
    rw [h, Real.sqrt_sq hr]

/-- OpenStax Calculus 3:Example 2.15 (CA-436).
The sphere with a given segment as diameter is centered at the midpoint with radius half the
length of the segment. -/
@[kb "openstaxcalculus2016" "3:Example 2.15, p. 125"]
theorem sphere_with_diameter (p q : EuclideanSpace ℝ (Fin 3)) :
    (EuclideanGeometry.Sphere.ofDiameter p q).center = midpoint ℝ p q ∧
      (EuclideanGeometry.Sphere.ofDiameter p q).radius = dist p q / 2 :=
  ⟨rfl, rfl⟩

/-- OpenStax Calculus 3:§2.3 Definition (dot product, Eq 2.3) (CA-437).
In the plane, `a ⬝ b = a₁ b₁ + a₂ b₂`. -/
@[kb "openstaxcalculus2016" "3:§2.3 Definition (dot product, Eq 2.3), p. 140"]
theorem dot_product_plane (a b : Fin 2 → ℝ) : a ⬝ᵥ b = a 0 * b 0 + a 1 * b 1 :=
  vec2_dotProduct a b

/-- OpenStax Calculus 3:§2.3 Definition (dot product, Eq 2.3) (CA-437).
In space, `a ⬝ b = a₁ b₁ + a₂ b₂ + a₃ b₃`. -/
@[kb "openstaxcalculus2016" "3:§2.3 Definition (dot product, Eq 2.3), p. 140"]
theorem dot_product_space (a b : Fin 3 → ℝ) : a ⬝ᵥ b = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 :=
  vec3_dotProduct a b

/-- OpenStax Calculus 3:§2.3 Definition (dot product, Eq 2.3) (CA-437).
The inner product of `EuclideanSpace ℝ (Fin n)` is the sum of products of components. -/
@[kb "openstaxcalculus2016" "3:§2.3 Definition (dot product, Eq 2.3), p. 140"]
theorem inner_eq_sum_mul {n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) :
    ⟪u, v⟫_ℝ = ∑ i, u i * v i := by
  simp [PiLp.inner_apply, mul_comm]

/-- OpenStax Calculus 3:Theorem 2.3 (CA-438), properties of the dot product.
Commutative, distributive over addition, compatible with scalars, `0 ⬝ a = 0`, and `a ⬝ a = ‖a‖²`. -/
@[kb "openstaxcalculus2016" "3:Theorem 2.3, p. 140"]
theorem dot_product_properties {n : ℕ} (u v w : EuclideanSpace ℝ (Fin n)) (c : ℝ) :
    ⟪u, v⟫_ℝ = ⟪v, u⟫_ℝ ∧ ⟪u, v + w⟫_ℝ = ⟪u, v⟫_ℝ + ⟪u, w⟫_ℝ ∧
      ⟪c • u, v⟫_ℝ = c * ⟪u, v⟫_ℝ ∧ ⟪(0 : EuclideanSpace ℝ (Fin n)), u⟫_ℝ = 0 ∧
      ⟪u, u⟫_ℝ = ‖u‖ ^ 2 :=
  ⟨real_inner_comm v u, inner_add_right u v w, real_inner_smul_left u v c, inner_zero_left u,
    real_inner_self_eq_norm_sq u⟩

/-- OpenStax Calculus 3:Theorem 2.4 (CA-439), `u ⬝ v = ‖u‖ ‖v‖ cos θ`. -/
@[kb "openstaxcalculus2016" "3:Theorem 2.4, p. 142"]
theorem dot_product_eq_norm_mul_norm_mul_cos {n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) :
    ⟪u, v⟫_ℝ = ‖u‖ * ‖v‖ * Real.cos (InnerProductGeometry.angle u v) := by
  rw [mul_comm, InnerProductGeometry.cos_angle_mul_norm_mul_norm]

/-- OpenStax Calculus 3:§2.3 Equation 2.5 (CA-439).
For nonzero vectors, `cos θ = (u ⬝ v) / (‖u‖ ‖v‖)`. -/
@[kb "openstaxcalculus2016" "3:§2.3 Equation 2.5 (cosine of the angle), p. 143"]
theorem cos_angle_eq_dot_div {n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) :
    Real.cos (InnerProductGeometry.angle u v) = ⟪u, v⟫_ℝ / (‖u‖ * ‖v‖) :=
  InnerProductGeometry.cos_angle u v

/-- OpenStax Calculus 3:Theorem 2.5 (CA-440).
Two vectors are orthogonal (angle `π/2`) iff their dot product is zero. -/
@[kb "openstaxcalculus2016" "3:Theorem 2.5, p. 144"]
theorem orthogonal_iff_dot_product_zero {n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) :
    ⟪u, v⟫_ℝ = 0 ↔ InnerProductGeometry.angle u v = Real.pi / 2 :=
  InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two u v

/-- OpenStax Calculus 3:§2.3 Definition (vector projection, Eq 2.6) (CA-442).
The projection of `v` onto `u` is `((u ⬝ v) / ‖u‖²) u`. -/
@[kb "openstaxcalculus2016" "3:§2.3 Definition (vector projection, Eq 2.6), p. 148"]
theorem vector_projection_formula {n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) :
    (Submodule.span ℝ {u}).starProjection v = (⟪u, v⟫_ℝ / ‖u‖ ^ 2) • u :=
  Submodule.starProjection_singleton ℝ v

/-- OpenStax Calculus 3:§2.3 text (resolution of a vector into components) (CA-444).
For `u ≠ 0`, `v` is the sum of its projection onto `u` and a part orthogonal to `u`. -/
@[kb "openstaxcalculus2016" "3:§2.3 text (resolution of a vector into components), p. 149"]
theorem resolution_into_components {n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) (hu : u ≠ 0) :
    v = (⟪u, v⟫_ℝ / ‖u‖ ^ 2) • u + (v - (⟪u, v⟫_ℝ / ‖u‖ ^ 2) • u) ∧
      ⟪u, v - (⟪u, v⟫_ℝ / ‖u‖ ^ 2) • u⟫_ℝ = 0 := by
  refine ⟨by abel, ?_⟩
  have h : ‖u‖ ^ 2 ≠ 0 := by positivity
  rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  field_simp
  ring

/-- OpenStax Calculus 3:§2.4 Definition (cross product, Eq 2.9) (CA-446).
`u × v = (u₂ v₃ - u₃ v₂, u₃ v₁ - u₁ v₃, u₁ v₂ - u₂ v₁)` (components indexed from `0`). -/
@[kb "openstaxcalculus2016" "3:§2.4 Definition (cross product, Eq 2.9), p. 157"]
theorem cross_product_components (u v : Fin 3 → ℝ) :
    u ⨯₃ v = ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0] :=
  cross_apply u v

/-- OpenStax Calculus 3:§2.4 text (cross product orthogonal to both factors) (CA-447).
`u ⬝ (u × v) = 0` and `v ⬝ (u × v) = 0`. -/
@[kb "openstaxcalculus2016" "3:§2.4 text (cross product orthogonal to both factors), p. 157"]
theorem cross_product_orthogonal (u v : Fin 3 → ℝ) :
    u ⬝ᵥ (u ⨯₃ v) = 0 ∧ v ⬝ᵥ (u ⨯₃ v) = 0 :=
  ⟨dot_self_cross u v, dot_cross_self u v⟩

/-- OpenStax Calculus 3:Theorem 2.6 (CA-450), properties of the cross product.
Anticommutative, distributive over sums, scalars factor out, `u × 0 = 0`, `v × v = 0`, and
`u ⬝ (v × w) = (u × v) ⬝ w`. -/
@[kb "openstaxcalculus2016" "3:Theorem 2.6, p. 161"]
theorem cross_product_properties (u v w : Fin 3 → ℝ) (c : ℝ) :
    u ⨯₃ v = -(v ⨯₃ u) ∧ u ⨯₃ (v + w) = u ⨯₃ v + u ⨯₃ w ∧ (c • u) ⨯₃ v = c • (u ⨯₃ v) ∧
      u ⨯₃ 0 = 0 ∧ v ⨯₃ v = 0 ∧ u ⬝ᵥ (v ⨯₃ w) = (u ⨯₃ v) ⬝ᵥ w := by
  refine ⟨(cross_anticomm v u).symm, by simp, by simp, by simp, cross_self v, ?_⟩
  rw [dotProduct_comm (u ⨯₃ v) w]
  exact (triple_product_permutation w u v).symm

/-- OpenStax Calculus 3:Theorem 2.7 (CA-451).
`‖u × v‖ = ‖u‖ ‖v‖ sin θ` where `θ` is the angle between `u` and `v`. -/
@[kb "openstaxcalculus2016" "3:Theorem 2.7, p. 162"]
theorem cross_product_norm (u v : Fin 3 → ℝ) :
    ‖WithLp.toLp 2 (u ⨯₃ v)‖ = ‖WithLp.toLp 2 u‖ * ‖WithLp.toLp 2 v‖ *
      Real.sin (InnerProductGeometry.angle (WithLp.toLp 2 u) (WithLp.toLp 2 v)) :=
  InnerProductGeometry.norm_toLp_symm_crossProduct u v

/-- OpenStax Calculus 3:§2.4 text (determinants, Eq 2.10) (CA-452).
A `2 × 2` determinant is `a d - b c`. -/
@[kb "openstaxcalculus2016" "3:§2.4 text (determinants, Eq 2.10), p. 163"]
theorem det_two_by_two (a b c d : ℝ) : Matrix.det !![a, b; c, d] = a * d - b * c :=
  Matrix.det_fin_two_of a b c d

/-- OpenStax Calculus 3:§2.4 text (determinants, Eq 2.10) (CA-452).
A `3 × 3` determinant expands along its first row as a signed sum of `2 × 2` minors. -/
@[kb "openstaxcalculus2016" "3:§2.4 text (determinants, Eq 2.10), p. 163"]
theorem det_three_by_three (a b c d e f g h i : ℝ) :
    Matrix.det !![a, b, c; d, e, f; g, h, i] =
      a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g) := by
  rw [Matrix.det_fin_three]
  simp
  ring

/-- OpenStax Calculus 3:Theorem 2.9 (CA-455), triple scalar product.
`u ⬝ (v × w)` is the determinant of the matrix with rows `u`, `v`, `w`. -/
@[kb "openstaxcalculus2016" "3:Theorem 2.9, p. 166"]
theorem triple_scalar_product_eq_det (u v w : Fin 3 → ℝ) :
    u ⬝ᵥ (v ⨯₃ w) = Matrix.det ![u, v, w] :=
  triple_product_eq_det u v w

/-- OpenStax Calculus 3:§2.5 text (line segment vector equation, Eq 2.15) (CA-461).
The segment from `P` to `Q` is `{(1 - t) P + t Q : t ∈ [0, 1]}`. -/
@[kb "openstaxcalculus2016" "3:§2.5 text (line segment vector equation, Eq 2.15), p. 180"]
theorem segment_vector_equation {n : ℕ} (P Q : Fin n → ℝ) :
    segment ℝ P Q = (fun t : ℝ => (1 - t) • P + t • Q) '' Set.Icc 0 1 :=
  segment_eq_image ℝ P Q

/-! ## Results proved in this library -/

section ProvedInKB

open UndergradKB.Calculus (len ei ej ek plane planeGen line vangle cylToCart sphToCart)
open MeasureTheory

/-- OpenStax Calculus 3:§2.2 Rule: Equations of Planes Parallel to Coordinate Planes (CA-434).
The planes through `(a, b, c)` parallel to the `xy`-, `xz`-, `yz`-planes are `z = c`, `y = b`, `x = a`;
the coordinate planes themselves are `z = 0`, `y = 0`, `x = 0`. -/
@[kb "openstaxcalculus2016" "3:§2.2 Rule: Equations of Planes Parallel to Coordinate Planes, p. 124"]
theorem plane_parallel_to_coordinate_planes (P₀ : Fin 3 → ℝ) :
    plane ek P₀ = {x | x 2 = P₀ 2} ∧ plane ej P₀ = {x | x 1 = P₀ 1} ∧
      plane ei P₀ = {x | x 0 = P₀ 0} ∧
      plane ek 0 = {x | x 2 = 0} ∧ plane ej 0 = {x | x 1 = 0} ∧ plane ei 0 = {x | x 0 = 0} :=
  UndergradKB.Calculus.plane_parallel_coordinate P₀

/-- OpenStax Calculus 3:§2.4 text (right-hand rule) (CA-448).
`(u, v, u × v)` is positively oriented: the determinant of these rows is `‖u × v‖²`, so it is
positive whenever `u × v ≠ 0`. -/
@[kb "openstaxcalculus2016" "3:§2.4 text (right-hand rule), p. 158"]
theorem right_hand_rule (u v : Fin 3 → ℝ) :
    Matrix.det ![u, v, u ⨯₃ v] = len (u ⨯₃ v) ^ 2 ∧ 0 ≤ Matrix.det ![u, v, u ⨯₃ v] ∧
      (u ⨯₃ v ≠ 0 → 0 < Matrix.det ![u, v, u ⨯₃ v]) :=
  UndergradKB.Calculus.det_self_cross u v

/-- OpenStax Calculus 3:§2.4 Rule: Cross Product Calculated by a Determinant (CA-453).
Each component of `u × v` is the determinant with the unit vector in the first row and `u`, `v`
below; equivalently the cofactor expansion along `i, j, k`. -/
@[kb "openstaxcalculus2016" "3:§2.4 Rule: Cross Product Calculated by a Determinant, p. 164"]
theorem cross_product_by_determinant (u v : Fin 3 → ℝ) :
    u ⨯₃ v = Matrix.det !![u 1, u 2; v 1, v 2] • ei - Matrix.det !![u 0, u 2; v 0, v 2] • ej
      + Matrix.det !![u 0, u 1; v 0, v 1] • ek :=
  UndergradKB.Calculus.cross_eq_cofactor u v

/-- OpenStax Calculus 3:Theorem 2.8 (CA-454).
The parallelogram spanned by `u` and `v` has area `‖u‖ ‖v‖ sin θ = ‖u × v‖`. -/
@[kb "openstaxcalculus2016" "3:Theorem 2.8, p. 165"]
theorem area_of_parallelogram (u v : Fin 3 → ℝ) :
    len (u ⨯₃ v) = len u * (len v * Real.sin (vangle u v)) ∧
    len (u ⨯₃ v) ^ 2 = len u ^ 2 * len v ^ 2 - (u ⬝ᵥ v) ^ 2 :=
  UndergradKB.Calculus.parallelogram_area u v

/-- OpenStax Calculus 3:Theorem 2.10 (CA-457).
The parallelepiped with edges `u, v, w` has volume `|u ⬝ (v × w)|`. -/
@[kb "openstaxcalculus2016" "3:Theorem 2.10, p. 168"]
theorem volume_of_parallelepiped (u v w : Fin 3 → ℝ) :
    volume (parallelepiped ![u, v, w]) = ENNReal.ofReal |u ⬝ᵥ v ⨯₃ w| :=
  UndergradKB.Calculus.volume_parallelepiped_triple u v w

/-- OpenStax Calculus 3:§2.5 text (vector equation of a line, Eq 2.12) (CA-460).
A point lies on the line through `P` with direction `v` iff it has parametric coordinates
`P + t v`; when all direction components are nonzero, iff the symmetric equations hold. -/
@[kb "openstaxcalculus2016" "3:§2.5 text (vector equation of a line, Eq 2.12), p. 178"]
theorem line_parametric_and_symmetric (P v x : Fin 3 → ℝ) :
    (x ∈ line P v ↔ ∃ t : ℝ, x 0 = P 0 + t * v 0 ∧ x 1 = P 1 + t * v 1 ∧ x 2 = P 2 + t * v 2) ∧
    (v 0 ≠ 0 → v 1 ≠ 0 → v 2 ≠ 0 →
      (x ∈ line P v ↔ (x 0 - P 0) / v 0 = (x 1 - P 1) / v 1 ∧ (x 1 - P 1) / v 1 = (x 2 - P 2) / v 2)) :=
  UndergradKB.Calculus.line_forms P v x

/-- OpenStax Calculus 3:§2.5 text (distance from a point to a line, definition) (CA-462).
The least distance from `Q` to the line through `P` with direction `v ≠ 0` is `‖PQ × v‖ / ‖v‖`. -/
@[kb "openstaxcalculus2016" "3:§2.5 text (distance from a point to a line, definition), p. 180"]
theorem distance_from_point_to_line (P Q v : Fin 3 → ℝ) (hv : v ≠ 0) :
    IsLeast {r | ∃ t : ℝ, r = len (Q - (P + t • v))} (len ((Q - P) ⨯₃ v) / len v) :=
  UndergradKB.Calculus.distance_point_line P Q v hv

/-- OpenStax Calculus 3:Theorem 2.13 (CA-465).
The distance from `Q` to the plane `n ⬝ x + d = 0` is `|n ⬝ Q + d| / ‖n‖`. -/
@[kb "openstaxcalculus2016" "3:Theorem 2.13, p. 188"]
theorem distance_from_point_to_plane (n : Fin 3 → ℝ) (d : ℝ) (Q : Fin 3 → ℝ) (hn : n ≠ 0) :
    IsLeast {r | ∃ x ∈ planeGen n d, r = len (Q - x)} (|n ⬝ᵥ Q + d| / len n) :=
  UndergradKB.Calculus.distance_point_plane n d Q hn

/-- OpenStax Calculus 3:Theorem 2.15 (CA-476).
Cylindrical coordinates give `x = r cos θ`, `y = r sin θ`, `z = z`; conversely `r² = x² + y²` and
`tan θ = y / x`. -/
@[kb "openstaxcalculus2016" "3:Theorem 2.15, p. 218"]
theorem cylindrical_cartesian_conversion :
    (∀ r θ z : ℝ, (cylToCart r θ z) 0 = r * Real.cos θ ∧ (cylToCart r θ z) 1 = r * Real.sin θ ∧
      (cylToCart r θ z) 2 = z ∧ (cylToCart r θ z) 0 ^ 2 + (cylToCart r θ z) 1 ^ 2 = r ^ 2) ∧
    (∀ p : Fin 3 → ℝ,
      p = cylToCart (Real.sqrt (p 0 ^ 2 + p 1 ^ 2)) (Complex.arg ⟨p 0, p 1⟩) (p 2) ∧
      Real.sqrt (p 0 ^ 2 + p 1 ^ 2) ^ 2 = p 0 ^ 2 + p 1 ^ 2 ∧
      (p 0 ≠ 0 → Real.tan (Complex.arg ⟨p 0, p 1⟩) = p 1 / p 0)) :=
  ⟨UndergradKB.Calculus.cylToCart_spec, UndergradKB.Calculus.cartesian_to_cylindrical⟩

/-- OpenStax Calculus 3:Theorem 2.16 (CA-478).
Spherical coordinates give `x = ρ sin φ cos θ`, `y = ρ sin φ sin θ`, `z = ρ cos φ`; conversely
`ρ² = x² + y² + z²`. -/
@[kb "openstaxcalculus2016" "3:Theorem 2.16, p. 223"]
theorem spherical_cartesian_conversion :
    (∀ {ρ φ : ℝ}, 0 ≤ ρ → 0 ≤ φ → φ ≤ Real.pi → ∀ θ : ℝ,
      (sphToCart ρ θ φ) 0 = ρ * Real.sin φ * Real.cos θ ∧
      (sphToCart ρ θ φ) 1 = ρ * Real.sin φ * Real.sin θ ∧
      (sphToCart ρ θ φ) 2 = ρ * Real.cos φ ∧
      ρ ^ 2 = (sphToCart ρ θ φ) 0 ^ 2 + (sphToCart ρ θ φ) 1 ^ 2 + (sphToCart ρ θ φ) 2 ^ 2 ∧
      len (sphToCart ρ θ φ) = ρ ∧
      Real.sqrt ((sphToCart ρ θ φ) 0 ^ 2 + (sphToCart ρ θ φ) 1 ^ 2) = ρ * Real.sin φ ∧
      (sphToCart ρ θ φ) 2 = ρ * Real.cos φ) ∧
    (∀ p : Fin 3 → ℝ, ∃ ρ θ φ : ℝ, 0 ≤ ρ ∧ 0 ≤ φ ∧ φ ≤ Real.pi ∧ p = sphToCart ρ θ φ ∧
      ρ ^ 2 = p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2) :=
  ⟨fun hρ hφ0 hφπ θ => UndergradKB.Calculus.sphToCart_spec hρ hφ0 hφπ θ,
    UndergradKB.Calculus.cartesian_to_spherical⟩

end ProvedInKB

end UndergradKB.Calculus.Course.V3C2
