import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Echelon.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Pi
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Complex.Basic
import UndergradKB.Common.Attr

/-!
# Lebl, Notes on Diffy Qs, Chapter 3 (systems of ODEs): course layer

Thin wrappers around Mathlib stating the linear algebra and matrix exponential facts of the
chapter in the book's terms.
-/

namespace UndergradKB.DifferentialEquations.Course.Ch3

open Matrix

/-- Lebl Definition candidate D039 (DE-078). Matrices are added and scaled entrywise. -/
@[kb "lebldiffyqs2026" "Definition candidate D039, p. 127"]
theorem lebl_matrix_add_smul {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (c : ℝ)
    (i : Fin m) (j : Fin n) :
    (A + B) i j = A i j + B i j ∧ (c • A) i j = c * A i j :=
  ⟨rfl, rfl⟩

/-- Lebl Definition candidates D040, D041 (DE-079). The `(i,j)` entry of a matrix product is the
dot product of row `i` of `A` with column `j` of `B`, and `A v` has `i`-th entry the dot product
of row `i` with `v`. -/
@[kb "lebldiffyqs2026" "Definition candidates D040, D041, p. 128"]
theorem lebl_matrix_product_dot {l m n : ℕ} (A : Matrix (Fin l) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin n) ℝ) (v : Fin m → ℝ) (i : Fin l) (j : Fin n) :
    (A * B) i j = (fun k => A i k) ⬝ᵥ (fun k => B k j) ∧ (A *ᵥ v) i = (fun k => A i k) ⬝ᵥ v :=
  ⟨Matrix.mul_apply', rfl⟩

/-- Lebl Definition candidates D042, D043 (DE-080). A square matrix with unit determinant has the
inverse `A⁻¹` satisfying `A A⁻¹ = A⁻¹ A = I`. -/
@[kb "lebldiffyqs2026" "Definition candidates D042, D043, p. 129"]
theorem lebl_inverse_mul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (h : IsUnit A.det) :
    A * A⁻¹ = 1 ∧ A⁻¹ * A = 1 :=
  ⟨Matrix.mul_nonsing_inv A h, Matrix.nonsing_inv_mul A h⟩

/-- Lebl Definition candidates D044, D045, D046 (DE-081). The determinant of a `2×2` matrix is
`ad - bc`, and a determinant expands along any row by cofactors. -/
@[kb "lebldiffyqs2026" "Definition candidates D044, D045, D046, p. 129"]
theorem lebl_det_fin_two_and_cofactor (A : Matrix (Fin 2) (Fin 2) ℝ) {n : ℕ}
    (B : Matrix (Fin n.succ) (Fin n.succ) ℝ) (i : Fin n.succ) :
    A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0 ∧
      B.det = ∑ j : Fin n.succ, (-1) ^ (i + j : ℕ) * B i j * (B.submatrix i.succAbove j.succAbove).det :=
  ⟨Matrix.det_fin_two A, Matrix.det_succ_row B i⟩

/-- Lebl Theorem 3.2.1 (DE-082). A square matrix is invertible iff its determinant is nonzero,
and then `det (A⁻¹) = 1 / det A`. -/
@[kb "lebldiffyqs2026" "Theorem 3.2.1, p. 131"]
theorem lebl_invertible_iff_det_ne_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (IsUnit A ↔ A.det ≠ 0) ∧ (A.det ≠ 0 → A⁻¹.det = (A.det)⁻¹) := by
  refine ⟨?_, fun h => ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  · rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']

/-- Lebl Definition candidates D047-D049 (DE-083). A matrix in reduced row echelon form is in row
echelon form, with leading entries equal to `1` and zeros above each leading entry. -/
@[kb "lebldiffyqs2026" "Definition candidates D047, D048, D049, p. 133"]
theorem lebl_reduced_row_echelon {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : A.IsReducedRowEchelon) :
    (∀ ⦃i : Fin m⦄ ⦃c : Fin n⦄, A.IsLeadingEntry i c → A i c = 1) ∧
      (∀ ⦃i₁ i₂ : Fin m⦄ ⦃c : Fin n⦄, i₁ < i₂ → A.IsLeadingEntry i₂ c → A i₁ c = 0) :=
  ⟨fun _ _ h => hA.eq_one h, fun _ _ _ hlt h => hA.eq_zero hlt h⟩

/-- Lebl Example 3.3.1 (DE-086). Vector functions `v₀, …, v_{k-1}` are linearly independent iff
no nontrivial constant combination vanishes for all `t`. -/
@[kb "lebldiffyqs2026" "Example 3.3.1, p. 137"]
theorem lebl_vector_functions_independent_iff {k n : ℕ} (v : Fin k → ℝ → Fin n → ℝ) :
    LinearIndependent ℝ v ↔ ∀ c : Fin k → ℝ, ∑ i, c i • v i = 0 → ∀ i, c i = 0 :=
  Fintype.linearIndependent_iff

/-- Lebl Definition candidates D053, D054 (DE-089). `v` is an eigenvector of `A` for the
eigenvalue `μ` iff `v ≠ 0` and `A v = μ v`. -/
@[kb "lebldiffyqs2026" "Definition candidates D053, D054, p. 140"]
theorem lebl_eigenvector_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ) (v : Fin n → ℝ) :
    Module.End.HasEigenvector (Matrix.toLin' A) μ v ↔ v ≠ 0 ∧ A *ᵥ v = μ • v := by
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
  simp [and_comm]

/-- Lebl Definition candidate D055 (DE-090). The eigenvalues of `A` are the roots of
`det (A - λ I)`, i.e. of the characteristic polynomial. -/
@[kb "lebldiffyqs2026" "Definition candidate D055, p. 143"]
theorem lebl_eigenvalue_iff_charpoly_root {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ) :
    Module.End.HasEigenvalue (Matrix.toLin' A) μ ↔ (Matrix.scalar (Fin n) μ - A).det = 0 := by
  rw [← Matrix.eval_charpoly]
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']
  rfl

/-- Lebl Definition candidate D056 (DE-092). The complex conjugate of `a + ib` is `a - ib`. -/
@[kb "lebldiffyqs2026" "Definition candidate D056, p. 143"]
theorem lebl_complex_conj (a b : ℝ) :
    starRingEnd ℂ ((a : ℂ) + b * Complex.I) = (a : ℂ) - b * Complex.I := by
  simp [sub_eq_add_neg]

/-- Lebl Definition candidates D064-D066 (DE-100). The matrix exponential is the sum of the
series `∑ Aᵏ / k!`, and on diagonal matrices it is computed entrywise. -/
@[kb "lebldiffyqs2026" "Definition candidates D064, D065, D066, p. 169"]
theorem lebl_matrix_exp_series {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    NormedSpace.exp A = ∑' k : ℕ, ((k.factorial : ℚ)⁻¹) • A ^ k ∧
      NormedSpace.exp (Matrix.diagonal v) = Matrix.diagonal (NormedSpace.exp v) :=
  ⟨by rw [NormedSpace.exp_eq_tsum_rat], Matrix.exp_diagonal v⟩

/-- Lebl Theorem 3.8.2 (DE-102). If `AB = BA` then `e^{A+B} = e^A e^B`. -/
@[kb "lebldiffyqs2026" "Theorem 3.8.2, p. 170"]
theorem lebl_matrix_exp_add {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (h : Commute A B) :
    NormedSpace.exp (A + B) = NormedSpace.exp A * NormedSpace.exp B :=
  Matrix.exp_add_of_commute A B h

/-- Lebl §3.8.3 conjugation of the exponential (DE-103). For invertible `B`,
`e^{B A B⁻¹} = B e^A B⁻¹`. -/
@[kb "lebldiffyqs2026" "§3.8.3 conjugation of the exponential, p. 171"]
theorem lebl_matrix_exp_conj {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (hB : IsUnit B) :
    NormedSpace.exp (B * A * B⁻¹) = B * NormedSpace.exp A * B⁻¹ :=
  Matrix.exp_conj B A hB

end UndergradKB.DifferentialEquations.Course.Ch3
