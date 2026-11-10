import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import UndergradKB.Common.Attr

/-! # Chio's condensation (Hefferon, Topic: Chio's Method) -/

namespace UndergradKB.LinearAlgebra

open Matrix

variable {K : Type*} [Field K]

/-- The Chio condensation `C` of a square matrix `A` of size `m + 2` (Hefferon's Topic: Chio's
method): its `(i, j)` entry is the `2 × 2` determinant of rows `0, i+1` and columns `0, j+1`
of `A`. -/
def chioMatrix {m : ℕ} (A : Matrix (Fin (m + 2)) (Fin (m + 2)) K) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
  Matrix.of fun i j => A 0 0 * A i.succ j.succ - A 0 j.succ * A i.succ 0

/-- Chio's method: for an `n × n` matrix with `n = m + 2` and nonzero corner entry `a₁₁`,
`det A = det C / a₁₁ ^ (n - 2)`, written without division as `a₁₁ ^ (n-2) * det A = det C`. -/
@[kb "hefferon2020" "Topic-Chio.1, p. 387"]
theorem hefferon_Topic_Chio_1 {m : ℕ} (A : Matrix (Fin (m + 2)) (Fin (m + 2)) K)
    (h : A 0 0 ≠ 0) :
    A 0 0 ^ m * A.det = (chioMatrix A).det := by
  classical
  set a := A 0 0 with ha
  let L : Matrix (Fin (m + 2)) (Fin (m + 2)) K :=
    Matrix.of fun i j => if i = 0 then (if j = 0 then 1 else 0)
      else (if j = i then a else 0) + (if j = 0 then -A i 0 else 0)
  let B : Matrix (Fin (m + 2)) (Fin (m + 2)) K :=
    Matrix.of fun i j => if i = 0 then A 0 j else a * A i j - A i 0 * A 0 j
  have hB : B = L * A := by
    ext i j
    by_cases hi : i = 0
    · subst hi; simp [B, L, Matrix.mul_apply]
    · simp [B, L, Matrix.mul_apply, hi, add_mul, Finset.sum_add_distrib, sub_eq_add_neg]
  have hL : L.det = a ^ (m + 1) := by
    rw [det_of_isLowerTriangular L ?_]
    · rw [Fin.prod_univ_succ]
      simp [L]
    · intro i j hij
      have hij' : i < j := hij
      have hj : j ≠ 0 := by
        intro hj; subst hj; exact absurd hij' (by simp)
      have hji : j ≠ i := hij'.ne'
      by_cases hi : i = 0
      · simp [L, hi, hj]
      · simp [L, hi, hj, hji]
  have hsub : B.submatrix Fin.succ Fin.succ = chioMatrix A := by
    ext i j; simp [B, chioMatrix, ← ha, mul_comm]
  have hBdet : B.det = a * (chioMatrix A).det := by
    rw [det_succ_column_zero, Finset.sum_eq_single 0]
    · rw [Fin.succAbove_zero, hsub]
      simp [B, ← ha]
    · intro i _ hi
      have : B i 0 = 0 := by simp [B, hi, ← ha, mul_comm]
      rw [this]; simp
    · simp
  have h1 : a ^ (m + 1) * A.det = a * (chioMatrix A).det := by
    rw [← hL, ← det_mul, ← hB, hBdet]
  have h2 : a * (a ^ m * A.det) = a * (chioMatrix A).det := by rw [← h1]; ring
  exact mul_left_cancel₀ h h2

end UndergradKB.LinearAlgebra
