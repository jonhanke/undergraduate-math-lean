import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Pi
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2
import UndergradKB.Common.Attr

/-!
# Lebl, Notes on Diffy Qs, Appendix A (linear algebra): course layer

Thin wrappers around Mathlib stating the linear algebra facts of the appendix in the book's terms.
-/

namespace UndergradKB.DifferentialEquations.Course.AppendixA

open Matrix Module

/-- Lebl §A.1 Vectors (DE-241). Operations on `ℝⁿ` are componentwise. -/
@[kb "lebldiffyqs2026" "§A.1 Vectors, p. 386"]
theorem lebl_vector_componentwise {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (i : Fin n) : (x + y) i = x i + y i ∧ (c • x) i = c * x i :=
  ⟨rfl, rfl⟩

/-- Lebl §A.1 Linear mappings (DE-242). A map is linear iff it respects addition and scalar
multiplication. -/
@[kb "lebldiffyqs2026" "§A.1 Linear mappings, p. 390"]
theorem lebl_linear_map_iff {n m : ℕ} (F : (Fin n → ℝ) → (Fin m → ℝ)) :
    IsLinearMap ℝ F ↔ (∀ x y, F (x + y) = F x + F y) ∧ ∀ (c : ℝ) x, F (c • x) = c • F x :=
  ⟨fun h => ⟨h.map_add, h.map_smul⟩, fun h => ⟨h.1, h.2⟩⟩

/-- Lebl §A.1 Standard basis, §A.4 Basis (DE-244). Every vector of `ℝⁿ` is a unique linear
combination of the standard basis vectors. -/
@[kb "lebldiffyqs2026" "§A.1 Standard basis, p. 391"]
theorem lebl_standard_basis_unique {n : ℕ} (v : Fin n → ℝ) :
    ∃! c : Fin n → ℝ, ∑ i, c i • (Pi.single i (1 : ℝ) : Fin n → ℝ) = v := by
  refine ⟨v, ?_, fun c hc => ?_⟩
  · ext j
    simp [Finset.sum_apply, Pi.single_apply]
  · ext j
    have := congrFun hc j
    simpa [Finset.sum_apply, Pi.single_apply] using this

/-- Lebl §A.1 Matrices (DE-243). An `m × n` matrix is a rectangular array of entries: it is determined by its
entries, and any array of entries is a matrix (`Matrix.of`). -/
@[kb "lebldiffyqs2026" "§A.1 Matrices, p. 390"]
theorem lebl_matrix_entries {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) :
    (A = B ↔ ∀ i j, A i j = B i j) ∧ ∀ e : Fin m → Fin n → ℝ, ∀ i j, Matrix.of e i j = e i j :=
  ⟨⟨fun h _ _ => h ▸ rfl, fun h => Matrix.ext h⟩, fun _ _ _ => rfl⟩

/-- Lebl §A.2 Matrix product (DE-245). The `(i,j)` entry of `AB` is the dot product of row `i` of
`A` with column `j` of `B`. -/
@[kb "lebldiffyqs2026" "§A.2 Matrix product, p. 399"]
theorem lebl_matrix_product_entry {l m n : ℕ} (A : Matrix (Fin l) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin n) ℝ) (i : Fin l) (j : Fin n) :
    (A * B) i j = (fun k => A i k) ⬝ᵥ (fun k => B k j) :=
  Matrix.mul_apply'

/-- Lebl §A.2 Inverse, Determinant of 2x2 (DE-246). The inverse `B` of `A` satisfies
`AB = BA = I`, and a `2×2` matrix is invertible iff `ad - bc ≠ 0`. -/
@[kb "lebldiffyqs2026" "§A.2 Inverse, p. 401"]
theorem lebl_inverse_and_det_two (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (A.det ≠ 0 → A * A⁻¹ = 1 ∧ A⁻¹ * A = 1) ∧
      (IsUnit A ↔ A 0 0 * A 1 1 - A 0 1 * A 1 0 ≠ 0) := by
  refine ⟨fun h => ?_, ?_⟩
  · have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr h
    exact ⟨Matrix.mul_nonsing_inv A hu, Matrix.nonsing_inv_mul A hu⟩
  · rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, Matrix.det_fin_two]

/-- Lebl §A.3 Nullspace (DE-248). The nullspace of `A` is the set of solutions of `Ax = 0`. -/
@[kb "lebldiffyqs2026" "§A.3 Nullspace, p. 413"]
theorem lebl_nullspace_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) :
    x ∈ LinearMap.ker (Matrix.toLin' A) ↔ A *ᵥ x = 0 := by
  simp [LinearMap.mem_ker]

/-- Lebl §A.3 Span, row space, column space (DE-249). The rank of `A` is the dimension of the span
of its rows, and of the span of its columns. -/
@[kb "lebldiffyqs2026" "§A.3 Span, row space, column space, p. 415"]
theorem lebl_row_col_space {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    A.rank = finrank ℝ (Submodule.span ℝ (Set.range A.row)) ∧
      A.rank = finrank ℝ (Submodule.span ℝ (Set.range A.col)) :=
  ⟨Matrix.rank_eq_finrank_span_row A, Matrix.rank_eq_finrank_span_cols A⟩

/-- Lebl §A.3 Rank, §A.4 Dimension (DE-250). The rank of `A` is the dimension of its column
space (the range of `x ↦ Ax`), and the dimension of a space is the size of any basis. -/
@[kb "lebldiffyqs2026" "§A.3 Rank, p. 415"]
theorem lebl_rank_and_dimension {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    {ι : Type} [Fintype ι] (V : Type) [AddCommGroup V] [Module ℝ V] (b : Basis ι ℝ V) :
    A.rank = finrank ℝ (LinearMap.range (Matrix.mulVecLin A)) ∧
      finrank ℝ V = Fintype.card ι :=
  ⟨rfl, Module.finrank_eq_card_basis b⟩

/-- Lebl §A.5 Orthogonal projection (DE-252). The orthogonal projection of `w` onto the line
spanned by a vector `v` is `(⟨v,w⟩ / ⟨v,v⟩) v`. -/
@[kb "lebldiffyqs2026" "§A.5 Orthogonal projection, p. 430"]
theorem lebl_orthogonal_projection {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (v w : E) :
    (ℝ ∙ v).starProjection w = (inner ℝ v w / inner ℝ v v) • v := by
  rw [Submodule.starProjection_singleton ℝ w, real_inner_self_eq_norm_sq]
  simp

/-- Lebl §A.5 Gram-Schmidt (DE-253). Gram-Schmidt turns a linearly independent list into a list
of nonzero, pairwise orthogonal vectors with the same span. -/
@[kb "lebldiffyqs2026" "§A.5 Gram-Schmidt, p. 433"]
theorem lebl_gram_schmidt {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
    (f : Fin n → E) (hf : LinearIndependent ℝ f) :
    (∀ i, InnerProductSpace.gramSchmidt ℝ f i ≠ 0) ∧
      (∀ i j, i ≠ j → inner ℝ (InnerProductSpace.gramSchmidt ℝ f i)
        (InnerProductSpace.gramSchmidt ℝ f j) = 0) ∧
      Submodule.span ℝ (Set.range (InnerProductSpace.gramSchmidt ℝ f)) =
        Submodule.span ℝ (Set.range f) :=
  ⟨fun i => InnerProductSpace.gramSchmidt_ne_zero i hf,
    fun _ _ h => InnerProductSpace.gramSchmidt_orthogonal ℝ f h,
    InnerProductSpace.span_gramSchmidt ℝ f⟩

/-- Lebl §A.6 Determinant and cofactors (DE-254). The determinant expands along any row by
cofactors, and the adjugate entries are the cofactors `(-1)^{i+j} det A_{ij}`. -/
@[kb "lebldiffyqs2026" "§A.6 Determinant and cofactors, p. 436"]
theorem lebl_cofactor_expansion {n : ℕ} (A : Matrix (Fin n.succ) (Fin n.succ) ℝ)
    (i : Fin n.succ) :
    A.det = ∑ j : Fin n.succ,
      (-1) ^ (i + j : ℕ) * A i j * (A.submatrix i.succAbove j.succAbove).det ∧
    ∀ j, A.adjugate j i = (-1) ^ (i + j : ℕ) * (A.submatrix i.succAbove j.succAbove).det := by
  refine ⟨Matrix.det_succ_row A i, fun j => ?_⟩
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, add_comm]

/-- Lebl Theorem A.3.1 (DE-255). Row rank equals column rank: `rank A = rank Aᵀ`. -/
@[kb "lebldiffyqs2026" "Theorem A.3.1, p. 416"]
theorem lebl_rank_transpose {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Aᵀ.rank = A.rank :=
  Matrix.rank_transpose A

/-- Lebl Theorem A.4.1 (DE-256). A subspace of `ℝⁿ` has a basis, every vector is uniquely a
combination of it, and any two bases have the same number of vectors. -/
@[kb "lebldiffyqs2026" "Theorem A.4.1, p. 422"]
theorem lebl_basis_exists_unique {n : ℕ} (S : Submodule ℝ (Fin n → ℝ)) :
    Nonempty (Basis (Basis.ofVectorSpaceIndex ℝ S) ℝ S) ∧
      (∀ {ι : Type} (b : Basis ι ℝ S) (x : S), ∃! c : ι →₀ ℝ,
        Finsupp.linearCombination ℝ b c = x) ∧
      (∀ {ι ι' : Type} [Fintype ι] [Fintype ι'], Basis ι ℝ S → Basis ι' ℝ S →
        Fintype.card ι = Fintype.card ι') :=
  ⟨⟨Basis.ofVectorSpace ℝ S⟩,
    fun b x => ⟨b.repr x, b.linearCombination_repr x, fun c hc => by
      rw [← hc, ← Basis.repr_symm_apply]; simp⟩,
    fun b b' => by rw [← Module.finrank_eq_card_basis b, ← Module.finrank_eq_card_basis b']⟩

/-- Lebl Theorem A.4.2 (DE-257). The dimensions of the column space and the row space both equal
the rank. -/
@[kb "lebldiffyqs2026" "Theorem A.4.2, p. 423"]
theorem lebl_col_row_dim_eq_rank {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    finrank ℝ (Submodule.span ℝ (Set.range A.col)) = A.rank ∧
      finrank ℝ (Submodule.span ℝ (Set.range A.row)) = A.rank :=
  ⟨(Matrix.rank_eq_finrank_span_cols A).symm, (Matrix.rank_eq_finrank_span_row A).symm⟩

/-- Lebl Theorem A.4.3 (DE-258). Rank-nullity: for a matrix with `n` columns,
`rank + nullity = n`. -/
@[kb "lebldiffyqs2026" "Theorem A.4.3, p. 425"]
theorem lebl_rank_nullity {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    A.rank + finrank ℝ (LinearMap.ker (Matrix.mulVecLin A)) = n := by
  have := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin A)
  simpa [Matrix.rank] using this

/-- Lebl Theorem A.6.1 (DE-259). `det (AB) = det A * det B`. -/
@[kb "lebldiffyqs2026" "Theorem A.6.1, p. 439"]
theorem lebl_det_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    (A * B).det = A.det * B.det :=
  Matrix.det_mul A B

/-- Lebl Theorem A.6.2 (DE-260). A square matrix is invertible iff `det A ≠ 0`. -/
@[kb "lebldiffyqs2026" "Theorem A.6.2, p. 439"]
theorem lebl_invertible_iff_det {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    IsUnit A ↔ A.det ≠ 0 := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

end UndergradKB.DifferentialEquations.Course.AppendixA
