import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Basic.Real.Basic
import UndergradKB.Common.Attr

/-!
# Course layer, Chapter 8 (systems of equations, matrices, determinants)

Thin theorems in the book's terms (real matrices, real polynomials), each proved from the Mathlib
declarations named in the corresponding checklist row.
-/

namespace UndergradKB.Precalculus.Course

open Matrix Polynomial

/-- Matrices as rectangular arrays: the entry in row `i`, column `j` of the matrix built from an
array `f` is `f i j` (PC-138). -/
@[kb "stitzzeager2013" "§8.2, p. 579"]
theorem box_8_2_matrix_entries {m n : ℕ} (f : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) :
    (Matrix.of f) i j = f i j :=
  Matrix.of_apply f i j

/-- Matrix equality: two matrices are equal iff all corresponding entries agree; the size is part of
the type (PC-139). -/
@[kb "stitzzeager2013" "Definition 8.6, p. 590"]
theorem def_8_6_matrix_equality {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) :
    A = B ↔ ∀ i j, A i j = B i j :=
  Matrix.ext_iff.symm

/-- Matrix sum is entrywise (PC-140). -/
@[kb "stitzzeager2013" "Definition 8.7, p. 590"]
theorem def_8_7_matrix_sum {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (j : Fin n) :
    (A + B) i j = A i j + B i j :=
  Matrix.add_apply A B i j

/-- Matrix addition is commutative (PC-141). -/
@[kb "stitzzeager2013" "Theorem 8.3, p. 591"]
theorem thm_8_3_add_comm {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) : A + B = B + A :=
  add_comm A B

/-- Matrix addition is associative (PC-141). -/
@[kb "stitzzeager2013" "Theorem 8.3, p. 591"]
theorem thm_8_3_add_assoc {m n : ℕ} (A B C : Matrix (Fin m) (Fin n) ℝ) :
    (A + B) + C = A + (B + C) :=
  add_assoc A B C

/-- The zero matrix is an additive identity (PC-141). -/
@[kb "stitzzeager2013" "Theorem 8.3, p. 591"]
theorem thm_8_3_zero_add {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : 0 + A = A ∧ A + 0 = A :=
  ⟨zero_add A, add_zero A⟩

/-- Each matrix has a unique additive inverse, the entrywise negative `-A` (PC-141). -/
@[kb "stitzzeager2013" "Theorem 8.3, p. 591"]
theorem thm_8_3_additive_inverse {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    A + -A = 0 ∧ (∀ B, A + B = 0 → B = -A) ∧ (∀ i j, (-A) i j = -A i j) :=
  ⟨add_neg_cancel A, fun _ h => eq_neg_of_add_eq_zero_right h, fun i j => Matrix.neg_apply A i j⟩

/-- Scalar multiplication `kA` is entrywise, and so is subtraction (PC-142). -/
@[kb "stitzzeager2013" "Definition 8.8, p. 592"]
theorem def_8_8_scalar_mul_sub {m n : ℕ} (k : ℝ) (A B : Matrix (Fin m) (Fin n) ℝ)
    (i : Fin m) (j : Fin n) :
    (k • A) i j = k * A i j ∧ (A - B) i j = A i j - B i j ∧ A - B = A + -B :=
  ⟨Matrix.smul_apply k A i j, Matrix.sub_apply A B i j, sub_eq_add_neg A B⟩

/-- The `(i, j)` entry of a product is the row-by-column sum `∑ k, a_{ik} b_{kj}`
(PC-144). -/
@[kb "stitzzeager2013" "Definition 8.10, p. 596"]
theorem def_8_10_matrix_product {m n r : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin r) ℝ) (i : Fin m) (j : Fin r) :
    (A * B) i j = ∑ k, A i k * B k j :=
  Matrix.mul_apply

/-- Matrix multiplication is associative (PC-145). -/
@[kb "stitzzeager2013" "Theorem 8.5, p. 597"]
theorem thm_8_5_mul_assoc {m n r s : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin r) ℝ) (C : Matrix (Fin r) (Fin s) ℝ) :
    (A * B) * C = A * (B * C) :=
  Matrix.mul_assoc A B C

/-- Scalars pass through a matrix product: `k(AB) = (kA)B = A(kB)` (PC-145). -/
@[kb "stitzzeager2013" "Theorem 8.5, p. 597"]
theorem thm_8_5_smul_mul {m n r : ℕ} (k : ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin r) ℝ) : k • (A * B) = (k • A) * B ∧ k • (A * B) = A * (k • B) :=
  ⟨(Matrix.smul_mul k A B).symm, (Matrix.mul_smul A k B).symm⟩

/-- The identity matrix is a two-sided multiplicative identity: `I_m A = A I_n = A`
(PC-145). -/
@[kb "stitzzeager2013" "Theorem 8.5, p. 597"]
theorem thm_8_5_identity {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    (1 : Matrix (Fin m) (Fin m) ℝ) * A = A ∧ A * (1 : Matrix (Fin n) (Fin n) ℝ) = A :=
  ⟨Matrix.one_mul A, Matrix.mul_one A⟩

/-- Matrix multiplication distributes over addition on both sides (PC-145). -/
@[kb "stitzzeager2013" "Theorem 8.5, p. 597"]
theorem thm_8_5_distributive {m n r : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (B C : Matrix (Fin n) (Fin r) ℝ) (D : Matrix (Fin r) (Fin m) ℝ) :
    A * (B + C) = A * B + A * C ∧ (B + C) * D = B * D + C * D :=
  ⟨Matrix.mul_add A B C, Matrix.add_mul B C D⟩

/-- A square matrix is upper triangular exactly when every entry below the diagonal is zero
(PC-146). -/
@[kb "stitzzeager2013" "§8.3, p. 605"]
theorem box_8_3_upper_triangular {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    A.IsUpperTriangular ↔ ∀ i j, j < i → A i j = 0 :=
  Iff.rfl

/-- A square matrix is lower triangular exactly when every entry above the diagonal is zero
(PC-146). -/
@[kb "stitzzeager2013" "§8.3, p. 605"]
theorem box_8_3_lower_triangular {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    A.IsLowerTriangular ↔ ∀ i j, i < j → A i j = 0 :=
  Iff.rfl

/-- The inverse of an invertible matrix is unique: any left or right inverse `B` of `A` is
`A⁻¹` (PC-148). -/
@[kb "stitzzeager2013" "Theorem 8.6, p. 614"]
theorem thm_8_6_inverse_unique {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    (A * B = 1 → A⁻¹ = B) ∧ (B * A = 1 → A⁻¹ = B) :=
  ⟨Matrix.inv_eq_right_inv, Matrix.inv_eq_left_inv⟩

/-- The determinant expands along the first row, and a `1 × 1` determinant is its entry
(PC-151). -/
@[kb "stitzzeager2013" "Definition 8.13, p. 626"]
theorem def_8_13_det_first_row {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    A.det = ∑ j : Fin (n + 1), (-1) ^ (j : ℕ) * A 0 j * (A.submatrix Fin.succ j.succAbove).det :=
  Matrix.det_succ_row_zero A

/-- The determinant of a `1 × 1` matrix is its entry (PC-151). -/
@[kb "stitzzeager2013" "Definition 8.13, p. 626"]
theorem def_8_13_det_one_by_one (A : Matrix (Fin 1) (Fin 1) ℝ) : A.det = A 0 0 :=
  Matrix.det_unique A

/-- The `2 × 2` determinant: `ad - bc` (PC-152). -/
@[kb "stitzzeager2013" "Equation 8.1, p. 627"]
theorem eq_8_1_det_two_by_two (a b c d : ℝ) : !![a, b; c, d].det = a * d - b * c :=
  Matrix.det_fin_two_of a b c d

/-- The determinant can be expanded along any row (PC-154). -/
@[kb "stitzzeager2013" "Theorem 8.7, p. 628"]
theorem thm_8_7_expand_along_row {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (i : Fin (n + 1)) :
    A.det = ∑ j : Fin (n + 1), (-1) ^ ((i : ℕ) + j) * A i j *
      (A.submatrix i.succAbove j.succAbove).det :=
  Matrix.det_succ_row A i

/-- Swapping two distinct rows negates the determinant (PC-155). -/
@[kb "stitzzeager2013" "Theorem 8.7, p. 628"]
theorem thm_8_7_swap_rows {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {i j : Fin n} (h : i ≠ j) :
    (A.submatrix (Equiv.swap i j) id).det = -A.det := by
  rw [Matrix.det_permute, Equiv.Perm.sign_swap h]
  simp

/-- Scaling one row by `c` scales the determinant by `c` (PC-155). -/
@[kb "stitzzeager2013" "Theorem 8.7, p. 628"]
theorem thm_8_7_scale_row {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (c : ℝ) :
    (A.updateRow i (c • A i)).det = c * A.det := by
  rw [Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]

/-- Adding a multiple of another row to a row leaves the determinant unchanged (PC-155). -/
@[kb "stitzzeager2013" "Theorem 8.7, p. 628"]
theorem thm_8_7_add_multiple_of_row {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {i j : Fin n}
    (h : i ≠ j) (c : ℝ) : (A.updateRow i (A i + c • A j)).det = A.det :=
  Matrix.det_updateRow_add_smul_self A h c

/-- A matrix with two identical rows has determinant zero (PC-156). -/
@[kb "stitzzeager2013" "Theorem 8.7, p. 628"]
theorem thm_8_7_equal_rows {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {i j : Fin n} (h : i ≠ j)
    (hA : A i = A j) : A.det = 0 :=
  Matrix.det_zero_of_row_eq h hA

/-- A matrix with a zero row has determinant zero (PC-156). -/
@[kb "stitzzeager2013" "Theorem 8.7, p. 628"]
theorem thm_8_7_zero_row {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n)
    (h : ∀ j, A i j = 0) : A.det = 0 :=
  Matrix.det_eq_zero_of_row_eq_zero i h

/-- The determinant of an upper triangular matrix is the product of its diagonal entries
(PC-157). -/
@[kb "stitzzeager2013" "Theorem 8.7, p. 628"]
theorem thm_8_7_det_upper_triangular {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h : A.IsUpperTriangular) : A.det = ∏ i, A i i :=
  Matrix.det_of_isUpperTriangular h

/-- The determinant of a lower triangular matrix is the product of its diagonal entries
(PC-157). -/
@[kb "stitzzeager2013" "Theorem 8.7, p. 628"]
theorem thm_8_7_det_lower_triangular {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h : A.IsLowerTriangular) : A.det = ∏ i, A i i :=
  Matrix.det_of_isLowerTriangular A h

/-- The determinant is multiplicative: `det (AB) = det A * det B` (PC-158). -/
@[kb "stitzzeager2013" "Theorem 8.7, p. 628"]
theorem thm_8_7_det_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    (A * B).det = A.det * B.det :=
  Matrix.det_mul A B

/-- `det (A ^ k) = (det A) ^ k` (PC-158). -/
@[kb "stitzzeager2013" "Theorem 8.7, p. 628"]
theorem thm_8_7_det_pow {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    (A ^ k).det = A.det ^ k :=
  Matrix.det_pow A k

/-- A real square matrix is invertible exactly when its determinant is nonzero (PC-159). -/
@[kb "stitzzeager2013" "Theorem 8.7, p. 628"]
theorem thm_8_7_invertible_iff_det_ne_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    IsUnit A ↔ A.det ≠ 0 := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

/-- For an invertible matrix, `det A⁻¹ = 1 / det A` (PC-159). -/
@[kb "stitzzeager2013" "Theorem 8.7, p. 628"]
theorem thm_8_7_det_inverse {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    A⁻¹.det = 1 / A.det := by
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', one_div]

/-- The adjoint (adjugate) is the transpose of the cofactor matrix: its `(i, j)` entry is the
cofactor `(-1)^(i+j)` times the minor obtained by deleting row `j` and column `i` (PC-161). -/
@[kb "stitzzeager2013" "Definition 8.15, p. 634"]
theorem def_8_15_adjoint_entries {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (i j : Fin (n + 1)) :
    A.adjugate i j = (-1) ^ ((i : ℕ) + j) * (A.submatrix j.succAbove i.succAbove).det :=
  by rw [Matrix.adjugate_fin_succ_eq_det_submatrix A i j, add_comm]

/-- Inverse by the adjoint: `A⁻¹ = (1 / det A) adj A` (PC-162). -/
@[kb "stitzzeager2013" "Theorem 8.9, p. 634"]
theorem thm_8_9_inverse_via_adjoint {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    A⁻¹ = (1 / A.det) • A.adjugate := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', one_div]

/-- The inverse of a `2 × 2` matrix with `ad - bc ≠ 0` (PC-163). -/
@[kb "stitzzeager2013" "Equation 8.2, p. 634"]
theorem eq_8_2_inverse_two_by_two (a b c d : ℝ) :
    (!![a, b; c, d])⁻¹ = (1 / (a * d - b * c)) • !![d, -b; -c, a] := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two_of, Matrix.det_fin_two_of,
    one_div]

/-- Two real polynomials that agree on a nondegenerate open interval are equal, so they have the
same coefficients (PC-165). -/
@[kb "stitzzeager2013" "Theorem 8.11, p. 643"]
theorem thm_8_11_polynomial_identity (p q : ℝ[X]) {a b : ℝ} (hab : a < b)
    (h : ∀ x ∈ Set.Ioo a b, p.eval x = q.eval x) : p = q :=
  Polynomial.eq_of_infinite_eval_eq p q ((Set.Ioo_infinite hab).mono h)

end UndergradKB.Precalculus.Course
