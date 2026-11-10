import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.InnerProductSpace.PiL2
import UndergradKB.Common.Attr
import UndergradKB.AbstractAlgebra.MatrixGroups
import UndergradKB.AbstractAlgebra.MatrixGroups2
import UndergradKB.AbstractAlgebra.FiniteSymmetry

/-! # Judson–Beezer, chapter 12: matrix groups and symmetry (course layer)

Thin wrappers in the book's terms around Mathlib for the linear algebra background and the matrix
groups `O(n)` and `SO(n)`. -/

namespace UndergradKB.AbstractAlgebra.Course

open scoped Matrix

/-- AA-168. A square real matrix is invertible iff its determinant is nonzero. -/
@[kb "judson2026" "Definition 12.1.1 (invertibility), p. 161"]
theorem judson_12_1_1_invertible_iff_det_ne_zero {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) : IsUnit A ↔ A.det ≠ 0 := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

/-- AA-169. The determinant is multiplicative, `det A⁻¹ = 1 / det A`, and `det Aᵀ = det A`. -/
@[kb "judson2026" "Definition 12.1.1 (determinant), p. 161"]
theorem judson_12_1_1_det_properties {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) :
    (A * B).det = A.det * B.det ∧ A⁻¹.det = (A.det)⁻¹ ∧ Aᵀ.det = A.det := by
  refine ⟨Matrix.det_mul A B, ?_, Matrix.det_transpose A⟩
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']

/-- AA-170. A linear map of `ℝⁿ` multiplies (Lebesgue) volume by `|det|`. -/
@[kb "judson2026" "Definition 12.1.1 (volume), p. 161"]
theorem judson_12_1_1_volume_scaling (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (s : Set (Fin n → ℝ)) :
    MeasureTheory.volume (Matrix.toLin' A '' s) =
      ENNReal.ofReal |A.det| * MeasureTheory.volume s := by
  rw [MeasureTheory.Measure.addHaar_image_linearMap, LinearMap.det_toLin']

/-- AA-173. A real matrix lies in the orthogonal group `O(n)` iff it is invertible with
`A⁻¹ = Aᵀ`. -/
@[kb "judson2026" "Definition 12.1.3 (orthogonal group), p. 162"]
theorem judson_12_1_3_orthogonal_group {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) :
    A ∈ Matrix.orthogonalGroup n ℝ ↔ IsUnit A.det ∧ A⁻¹ = Aᵀ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  constructor
  · intro h
    have hd := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hd
    exact ⟨isUnit_iff_ne_zero.mpr (by intro h0; simp [h0] at hd),Matrix.inv_eq_right_inv h⟩
  · rintro ⟨h, h'⟩
    rw [← h']
    exact Matrix.mul_nonsing_inv A h

/-- AA-174. Properties of the Euclidean inner product on `ℝⁿ`: symmetry, bilinearity (additivity
and homogeneity in the second argument), positivity and nondegeneracy. -/
@[kb "judson2026" "Proposition 12.1.6, p. 163"]
theorem judson_12_1_6 (n : ℕ) (x y z : EuclideanSpace ℝ (Fin n)) (α : ℝ) :
    inner ℝ x y = inner ℝ y x ∧
    inner ℝ x (y + z) = inner ℝ x y + inner ℝ x z ∧
    inner ℝ x (α • y) = α * inner ℝ x y ∧
    0 ≤ inner ℝ x x ∧ (inner ℝ x x = 0 ↔ x = 0) :=
  ⟨real_inner_comm y x, inner_add_right x y z, real_inner_smul_right x y α,
    real_inner_self_nonneg, inner_self_eq_zero⟩

/-- AA-179. The special orthogonal group `SO(n)` consists of the matrices of `O(n)` of
determinant `1`. -/
@[kb "judson2026" "Definition 12.1.4 (special orthogonal group), p. 165"]
theorem judson_12_1_4_special_orthogonal_group {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) :
    A ∈ Matrix.specialOrthogonalGroup n ℝ ↔ A ∈ Matrix.orthogonalGroup n ℝ ∧ A.det = 1 :=
  Matrix.mem_specialOrthogonalGroup_iff

/-- AA-177. For a real square matrix `A`, the following are equivalent: the columns are
orthonormal; `A⁻¹ = Aᵀ`; `A` preserves inner products; `A` preserves distances; `A` preserves
lengths. -/
@[kb "judson2026" "Theorem 12.1.8, p. 163"]
theorem judson_12_1_8 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    List.TFAE
      [ ∀ i j, Aᵀ i ⬝ᵥ Aᵀ j = if i = j then 1 else 0,
        IsUnit A.det ∧ A⁻¹ = Aᵀ,
        ∀ x y : Fin n → ℝ, (A *ᵥ x) ⬝ᵥ (A *ᵥ y) = x ⬝ᵥ y,
        ∀ x y : EuclideanSpace ℝ (Fin n),
          dist (Matrix.toEuclideanLin A x) (Matrix.toEuclideanLin A y) = dist x y,
        ∀ x : EuclideanSpace ℝ (Fin n), ‖Matrix.toEuclideanLin A x‖ = ‖x‖ ] :=
  orthogonal_tfae A

/-- AA-182. An isometry of the plane `ℝ²` fixing the origin is linear, given by an element of
`O(2)`. -/
@[kb "judson2026" "Lemma 12.2.2, p. 166"]
theorem judson_12_2_2 (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hf : Isometry f) (h0 : f 0 = 0) :
    ∃ A ∈ Matrix.orthogonalGroup (Fin 2) ℝ, ∀ x, f x = Matrix.toEuclideanLin A x :=
  isometry_fixing_zero_orthogonal_two f hf h0

/-- AA-183. The isometries of the plane `ℝ²` are exactly the maps `x ↦ A x + b` with
`A ∈ O(2)`. -/
@[kb "judson2026" "Theorem 12.2.3, p. 167"]
theorem judson_12_2_3 (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) :
    Isometry f ↔ ∃ A ∈ Matrix.orthogonalGroup (Fin 2) ℝ, ∃ b : EuclideanSpace ℝ (Fin 2),
      ∀ x, f x = Matrix.toEuclideanLin A x + b :=
  isometry_two_iff f

/-- AA-183. The Euclidean group `E(2)` (pairs `(A, x)` with `A ∈ O(2)`) is isomorphic to the
group of isometries of the plane. -/
@[kb "judson2026" "Theorem 12.2.3 (E(2) is the isometry group), p. 167"]
theorem judson_12_2_3_euclidean_group :
    Nonempty (EuclideanGroup 2 ≃*
      (EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2))) :=
  ⟨EuclideanGroup.mulEquivIsometry 2⟩

/-- AA-185. A finite subgroup `G` of `O(2)` is cyclic `ℤ_n` or dihedral `D_n`, where `n` is the
order of its rotation part. -/
@[kb "judson2026" "Theorem 12.2.4, p. 167"]
theorem judson_12_2_4 (G : Subgroup (Matrix.orthogonalGroup (Fin 2) ℝ)) [Finite G] :
    ∃ n : ℕ, n = Nat.card (rotationPart G) ∧ 0 < n ∧
      (Nonempty (G ≃* Multiplicative (ZMod n)) ∨ Nonempty (G ≃* DihedralGroup n)) :=
  finite_subgroup_orthogonal_two G

/-- AA-189. The lattice (translation group) generated by two linearly independent vectors of
the plane is isomorphic to `ℤ × ℤ`. -/
@[kb "judson2026" "Theorem 12.2.8, p. 170"]
theorem judson_12_2_8 {V : Type*} [AddCommGroup V] [Module ℝ V] {x y : V}
    (hxy : LinearIndependent ℝ ![x, y]) : Nonempty ((ℤ × ℤ) ≃+ lattice2 x y) :=
  lattice2_addEquiv hxy

/-- AA-190. Crystallographic restriction: a finite-order linear map of a real plane preserving
the lattice generated by two independent vectors has order 1, 2, 3, 4 or 6. -/
@[kb "judson2026" "Theorem 12.2.9, p. 170"]
theorem judson_12_2_9 {V : Type*} [AddCommGroup V] [Module ℝ V] (hV : Module.finrank ℝ V = 2)
    {x y : V} (hxy : LinearIndependent ℝ ![x, y]) (T : V →ₗ[ℝ] V)
    (hT : ∀ v ∈ lattice2 x y, T v ∈ lattice2 x y) (m : ℕ) (hm : m ≠ 0) (hTm : T ^ m = 1) :
    orderOf T = 1 ∨ orderOf T = 2 ∨ orderOf T = 3 ∨ orderOf T = 4 ∨ orderOf T = 6 :=
  crystallographic_restriction hV hxy T hT m hm hTm

/-- AA-190. Algebraic core: an integer `2 × 2` matrix of finite order has order 1, 2, 3, 4 or 6. -/
@[kb "judson2026" "Theorem 12.2.9 (integer matrices), p. 170"]
theorem judson_12_2_9_int_matrix (A : Matrix (Fin 2) (Fin 2) ℤ) (m : ℕ) (hm : m ≠ 0)
    (hA : A ^ m = 1) : orderOf A = 1 ∨ orderOf A = 2 ∨ orderOf A = 3 ∨ orderOf A = 4 ∨
      orderOf A = 6 :=
  orderOf_int_matrix_two A m hm hA

end UndergradKB.AbstractAlgebra.Course
