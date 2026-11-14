import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 8 (Stitz-Zeager): exercises with the book's answers, Sections 8.3, 8.4 and 8.5 -/

namespace UndergradKB.Precalculus.Course

open Matrix

/-- Entrywise proof of a matrix identity with explicit small matrices. -/
local macro "mt" : tactic =>
  `(tactic| (ext i j; fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.smul_apply] <;> (try norm_num) <;> (try ring)))

/-! ## 8.3 Matrix Arithmetic -/

/-- Stitz-Zeager Exercise 8.3.1: for `A = [[2,-3],[1,4]]`, `B = [[5,-2],[4,8]]`: `3A`, `-B`, `A²`, `A-2B`,
`AB` and `BA`. -/
@[kb "stitzzeager2013" "Exercise 8.3.1, p. 603"]
theorem exer_8_3_1 :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![2, -3; 1, 4]
    let B : Matrix (Fin 2) (Fin 2) ℝ := !![5, -2; 4, 8]
    (3 : ℝ) • A = !![6, -9; 3, 12] ∧ -B = !![-5, 2; -4, -8] ∧ A ^ 2 = !![1, -18; 6, 13] ∧
    A - (2 : ℝ) • B = !![-8, 1; -7, -12] ∧ A * B = !![-2, -28; 21, 30] ∧ B * A = !![8, -23; 16, 20] := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> mt

/-- Stitz-Zeager Exercise 8.3.2: for `A = [[-1,5],[-3,6]]`, `B = [[2,10],[-7,1]]`: `3A`, `-B`, `A²`, `A-2B`, `AB`
and `BA`. -/
@[kb "stitzzeager2013" "Exercise 8.3.2, p. 603"]
theorem exer_8_3_2 :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 5; -3, 6]
    let B : Matrix (Fin 2) (Fin 2) ℝ := !![2, 10; -7, 1]
    (3 : ℝ) • A = !![-3, 15; -9, 18] ∧ -B = !![-2, -10; 7, -1] ∧ A ^ 2 = !![-14, 25; -15, 21] ∧
    A - (2 : ℝ) • B = !![-5, -15; 11, 4] ∧ A * B = !![-37, -5; -48, -24] ∧ B * A = !![-32, 70; 4, -29] := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> mt

/-- Stitz-Zeager Exercise 8.3.3: for `A = [[-1,3],[5,2]]` (`2×2`) and `B = [[7,0,8],[-3,1,4]]` (`2×3`): `3A`, `-B`,
`A²` and `AB` (while `A - 2B` and `BA` are undefined). -/
@[kb "stitzzeager2013" "Exercise 8.3.3, p. 603"]
theorem exer_8_3_3 :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 3; 5, 2]
    let B : Matrix (Fin 2) (Fin 3) ℝ := !![7, 0, 8; -3, 1, 4]
    (3 : ℝ) • A = !![-3, 9; 15, 6] ∧ -B = !![-7, 0, -8; 3, -1, -4] ∧ A ^ 2 = !![16, 3; 5, 19] ∧
    A * B = !![-16, 3, 4; 29, 2, 48] := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩ <;> mt

/-- Stitz-Zeager Exercise 8.3.4: for `A = [[2,4],[6,8]]` and `B = [[-1,3,-5],[7,-9,11]]`: `3A`, `-B`, `A²` and
`AB`. -/
@[kb "stitzzeager2013" "Exercise 8.3.4, p. 603"]
theorem exer_8_3_4 :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![2, 4; 6, 8]
    let B : Matrix (Fin 2) (Fin 3) ℝ := !![-1, 3, -5; 7, -9, 11]
    (3 : ℝ) • A = !![6, 12; 18, 24] ∧ -B = !![1, -3, 5; -7, 9, -11] ∧ A ^ 2 = !![28, 40; 60, 88] ∧
    A * B = !![26, -30, 34; 50, -54, 58] := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩ <;> mt

/-- Stitz-Zeager Exercise 8.3.5: for the column `A = (7,8,9)` and the row `B = (1,2,3)`: `3A`, `-B`, `AB` is the
`3×3` matrix `[[7,14,21],[8,16,24],[9,18,27]]` and `BA = [50]`. -/
@[kb "stitzzeager2013" "Exercise 8.3.5, p. 603"]
theorem exer_8_3_5 :
    let A : Matrix (Fin 3) (Fin 1) ℝ := !![7; 8; 9]
    let B : Matrix (Fin 1) (Fin 3) ℝ := !![1, 2, 3]
    (3 : ℝ) • A = !![21; 24; 27] ∧ -B = !![-1, -2, -3] ∧ A * B = !![7, 14, 21; 8, 16, 24; 9, 18, 27] ∧
    B * A = !![50] := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩ <;> mt

/-- Stitz-Zeager Exercise 8.3.6: for `A = [[1,-2],[-3,4],[5,-6]]` (`3×2`) and `B = [-5, 1, 8]` (`1×3`): `3A`, `-B`
and `BA = [32, -34]`. -/
@[kb "stitzzeager2013" "Exercise 8.3.6, p. 603"]
theorem exer_8_3_6 :
    let A : Matrix (Fin 3) (Fin 2) ℝ := !![1, -2; -3, 4; 5, -6]
    let B : Matrix (Fin 1) (Fin 3) ℝ := !![-5, 1, 8]
    (3 : ℝ) • A = !![3, -6; -9, 12; 15, -18] ∧ -B = !![5, -1, -8] ∧ B * A = !![32, -34] := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩ <;> mt

/-- Stitz-Zeager Exercise 8.3.7: for `A = [[2,-3,5],[3,1,-2],[-7,1,-1]]` and `B = [[1,2,1],[17,33,19],[10,19,11]]`:
`A² = [[-40,-4,11],[23,-10,15],[-4,21,-36]]`, `A - 2B`, and `AB = BA = I₃`. -/
@[kb "stitzzeager2013" "Exercise 8.3.7, p. 603"]
theorem exer_8_3_7 :
    let A : Matrix (Fin 3) (Fin 3) ℝ := !![2, -3, 5; 3, 1, -2; -7, 1, -1]
    let B : Matrix (Fin 3) (Fin 3) ℝ := !![1, 2, 1; 17, 33, 19; 10, 19, 11]
    A ^ 2 = !![-40, -4, 11; 23, -10, 15; -4, 21, -36] ∧
    A - (2 : ℝ) • B = !![0, -7, 3; -31, -65, -40; -27, -37, -23] ∧ A * B = 1 ∧ B * A = 1 := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩ <;> mt

/-- Stitz-Zeager Exercise 8.3.8: with `A = [[1,2],[3,4]]`, `B = [[0,-3],[-5,2]]`: `7B - 4A = [[-4,-29],[-47,-2]]`. -/
@[kb "stitzzeager2013" "Exercise 8.3.8, p. 603"]
theorem exer_8_3_8 :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![1, 2; 3, 4]
    let B : Matrix (Fin 2) (Fin 2) ℝ := !![0, -3; -5, 2]
    (7 : ℝ) • B - (4 : ℝ) • A = !![-4, -29; -47, -2] := by
  dsimp only
  mt

/-- Stitz-Zeager Exercise 8.3.9: with `A = [[1,2],[3,4]]`, `B = [[0,-3],[-5,2]]`: `AB = [[-10,1],[-20,-1]]`. -/
@[kb "stitzzeager2013" "Exercise 8.3.9, p. 603"]
theorem exer_8_3_9 :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![1, 2; 3, 4]
    let B : Matrix (Fin 2) (Fin 2) ℝ := !![0, -3; -5, 2]
    A * B = !![-10, 1; -20, -1] := by
  dsimp only
  mt

/-- Stitz-Zeager Exercise 8.3.10: with `A = [[1,2],[3,4]]`, `B = [[0,-3],[-5,2]]`: `BA = [[-9,-12],[1,-2]]`. -/
@[kb "stitzzeager2013" "Exercise 8.3.10, p. 603"]
theorem exer_8_3_10 :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![1, 2; 3, 4]
    let B : Matrix (Fin 2) (Fin 2) ℝ := !![0, -3; -5, 2]
    B * A = !![-9, -12; 1, -2] := by
  dsimp only
  mt

/-- Stitz-Zeager Exercise 8.3.14: `A - 4 I₂ = [[-3,2],[3,0]]` for `A = [[1,2],[3,4]]`. -/
@[kb "stitzzeager2013" "Exercise 8.3.14, p. 603"]
theorem exer_8_3_14 :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![1, 2; 3, 4]
    A - (4 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) = !![-3, 2; 3, 0] := by
  dsimp only
  mt

/-- Stitz-Zeager Exercise 8.3.15: `A² - B² = [[-8,16],[25,3]]` for `A = [[1,2],[3,4]]`, `B = [[0,-3],[-5,2]]`. -/
@[kb "stitzzeager2013" "Exercise 8.3.15, p. 603"]
theorem exer_8_3_15 :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![1, 2; 3, 4]
    let B : Matrix (Fin 2) (Fin 2) ℝ := !![0, -3; -5, 2]
    A ^ 2 - B ^ 2 = !![-8, 16; 25, 3] := by
  dsimp only
  mt

/-- Stitz-Zeager Exercise 8.3.16: `(A+B)(A-B) = [[-7,3],[46,2]]` for `A = [[1,2],[3,4]]`, `B = [[0,-3],[-5,2]]`. -/
@[kb "stitzzeager2013" "Exercise 8.3.16, p. 603"]
theorem exer_8_3_16 :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![1, 2; 3, 4]
    let B : Matrix (Fin 2) (Fin 2) ℝ := !![0, -3; -5, 2]
    (A + B) * (A - B) = !![-7, 3; 46, 2] := by
  dsimp only
  mt

/-- Stitz-Zeager Exercise 8.3.17: `A² - 5A - 2 I₂ = 0` for `A = [[1,2],[3,4]]`. -/
@[kb "stitzzeager2013" "Exercise 8.3.17, p. 603"]
theorem exer_8_3_17 :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![1, 2; 3, 4]
    A ^ 2 - (5 : ℝ) • A - (2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by
  dsimp only
  mt

/-- Stitz-Zeager Exercise 8.3.18: `E² + 5E - 36 I₃ = [[-30,20,-15],[0,0,-36],[0,0,-36]]` for the upper
triangular `E = [[1,2,3],[0,4,-9],[0,0,-5]]`. -/
@[kb "stitzzeager2013" "Exercise 8.3.18, p. 603"]
theorem exer_8_3_18 :
    let E : Matrix (Fin 3) (Fin 3) ℝ := !![1, 2, 3; 0, 4, -9; 0, 0, -5]
    E ^ 2 + (5 : ℝ) • E - (36 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) = !![-30, 20, -15; 0, 0, -36; 0, 0, -36] := by
  dsimp only
  mt

/-- Stitz-Zeager Exercise 8.3.22: for `A = [[a,b,c],[d,e,f]]`: `E₁A` swaps the rows, `E₂A` multiplies row 1 by
`5`, `E₃A` replaces `R₁` by `R₁ - 2R₂`, and `E₄ = diag(1,-6)` multiplies the bottom row by `-6`. -/
@[kb "stitzzeager2013" "Exercise 8.3.22, p. 603"]
theorem exer_8_3_22 : ∀ a b c d e f : ℝ,
    !![(0 : ℝ), 1; 1, 0] * !![a, b, c; d, e, f] = !![d, e, f; a, b, c] ∧
    !![(5 : ℝ), 0; 0, 1] * !![a, b, c; d, e, f] = !![5 * a, 5 * b, 5 * c; d, e, f] ∧
    !![(1 : ℝ), -2; 0, 1] * !![a, b, c; d, e, f] = !![a - 2 * d, b - 2 * e, c - 2 * f; d, e, f] ∧
    !![(1 : ℝ), 0; 0, -6] * !![a, b, c; d, e, f] = !![a, b, c; -6 * d, -6 * e, -6 * f] := by
  intro a b c d e f
  refine ⟨?_, ?_, ?_, ?_⟩ <;> mt

/-- Stitz-Zeager Exercise 8.3.23: with transition matrix `Q = [[0.9,0.2],[0.1,0.8]]` and `X = (150, 0)`,
`QX = (135, 15)`. -/
@[kb "stitzzeager2013" "Exercise 8.3.23, p. 604"]
theorem exer_8_3_23 :
    !![(9 : ℝ) / 10, 1 / 5; 1 / 10, 4 / 5] *ᵥ ![150, 0] = ![135, 15] := by
  ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> norm_num

/-- Stitz-Zeager Exercise 8.3.27 (first part): `Xs = (100, 50)` is a steady state of `Q = [[0.9,0.2],[0.1,0.8]]`,
i.e. `Q Xs = Xs`. -/
@[kb "stitzzeager2013" "Exercise 8.3.27, p. 604"]
theorem exer_8_3_27 :
    !![(9 : ℝ) / 10, 1 / 5; 1 / 10, 4 / 5] *ᵥ ![100, 50] = ![100, 50] := by
  ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> norm_num

/-- Stitz-Zeager Exercise 8.3.29: with `S = [[2/3,2/3],[1/3,1/3]]` and `Y = (y, 150 - y)`, `S Y = (100, 50)`. -/
@[kb "stitzzeager2013" "Exercise 8.3.29, p. 605"]
theorem exer_8_3_29 : ∀ y : ℝ,
    !![(2 : ℝ) / 3, 2 / 3; 1 / 3, 1 / 3] *ᵥ ![y, 150 - y] = ![100, 50] := by
  intro y
  ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

/-- Stitz-Zeager Exercise 8.3.30: complex numbers `a + bi` correspond to matrices `[[a,b],[-b,a]]`; sums,
differences and products of matrices correspond to those of the complex numbers (`(a+bi)(c+di) =
(ac-bd) + (ad+bc)i`). -/
@[kb "stitzzeager2013" "Exercise 8.3.30, p. 605"]
theorem exer_8_3_30 : ∀ a b c d : ℝ,
    !![a, b; -b, a] + !![c, d; -d, c] = !![a + c, b + d; -(b + d), a + c] ∧
    !![a, b; -b, a] - !![c, d; -d, c] = !![a - c, b - d; -(b - d), a - c] ∧
    !![a, b; -b, a] * !![c, d; -d, c] = !![a * c - b * d, a * d + b * c; -(a * d + b * c), a * c - b * d] := by
  intro a b c d
  refine ⟨?_, ?_, ?_⟩ <;> mt

/-- Stitz-Zeager Exercise 8.3.31: `(A+B)² ≠ A² + 2AB + B²` for `A = [[1,2],[3,4]]`, `B = [[0,-3],[-5,2]]`
(`(A+B)² = [[3,-7],[-14,38]]` while `A² + 2AB + B² = [[2,6],[-35,39]]`); the correct general formula is
`(A+B)² = A² + AB + BA + B²`. -/
@[kb "stitzzeager2013" "Exercise 8.3.31, p. 605"]
theorem exer_8_3_31 :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![1, 2; 3, 4]
    let B : Matrix (Fin 2) (Fin 2) ℝ := !![0, -3; -5, 2]
    (A + B) ^ 2 = !![3, -7; -14, 38] ∧ A ^ 2 + (2 : ℝ) • (A * B) + B ^ 2 = !![2, 6; -35, 39] ∧
    (A + B) ^ 2 ≠ A ^ 2 + (2 : ℝ) • (A * B) + B ^ 2 ∧
    ∀ M N : Matrix (Fin 2) (Fin 2) ℝ, (M + N) ^ 2 = M ^ 2 + M * N + N * M + N ^ 2 := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · mt
  · mt
  · intro h
    have := congrFun (congrFun h 0) 0
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_succ] at this
    norm_num at this
  · intro M N
    noncomm_ring

/-! ## 8.4 Systems of Linear Equations: Matrix Inverses -/

/-- Stitz-Zeager Exercise 8.4.1: `[[1,2],[3,4]]⁻¹ = [[-2,1],[3/2,-1/2]]`. -/
@[kb "stitzzeager2013" "Exercise 8.4.1, p. 621"]
theorem exer_8_4_1 :
    (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ = !![-2, 1; 3 / 2, -1 / 2] := by
  refine Matrix.inv_eq_right_inv ?_
  mt

/-- Stitz-Zeager Exercise 8.4.2: `[[12,-7],[-5,3]]⁻¹ = [[3,7],[5,12]]`. -/
@[kb "stitzzeager2013" "Exercise 8.4.2, p. 621"]
theorem exer_8_4_2 :
    (!![12, -7; -5, 3] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ = !![3, 7; 5, 12] := by
  refine Matrix.inv_eq_right_inv ?_
  mt

/-- Stitz-Zeager Exercise 8.4.3: `[[6,15],[14,35]]` is not invertible (its determinant is `0`). -/
@[kb "stitzzeager2013" "Exercise 8.4.3, p. 621"]
theorem exer_8_4_3 : ¬ IsUnit (!![6, 15; 14, 35] : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two_of]
  norm_num

/-- Stitz-Zeager Exercise 8.4.4: `[[2,-1],[16,-9]]⁻¹ = [[9/2,-1/2],[8,-1]]`. -/
@[kb "stitzzeager2013" "Exercise 8.4.4, p. 621"]
theorem exer_8_4_4 :
    (!![2, -1; 16, -9] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ = !![9 / 2, -1 / 2; 8, -1] := by
  refine Matrix.inv_eq_right_inv ?_
  mt

/-- Stitz-Zeager Exercise 8.4.5: `[[3,0,4],[2,-1,3],[-3,2,-5]]⁻¹ = [[-1,8,4],[1,-3,-1],[1,-6,-3]]`. -/
@[kb "stitzzeager2013" "Exercise 8.4.5, p. 621"]
theorem exer_8_4_5 :
    (!![3, 0, 4; 2, -1, 3; -3, 2, -5] : Matrix (Fin 3) (Fin 3) ℝ)⁻¹ = !![-1, 8, 4; 1, -3, -1; 1, -6, -3] := by
  refine Matrix.inv_eq_right_inv ?_
  mt

/-- Stitz-Zeager Exercise 8.4.6: `[[4,6,-3],[3,4,-3],[1,2,6]]⁻¹ = [[-5/2,7/2,1/2],[7/4,-9/4,-1/4],[-1/6,1/6,1/6]]`. -/
@[kb "stitzzeager2013" "Exercise 8.4.6, p. 621"]
theorem exer_8_4_6 :
    (!![4, 6, -3; 3, 4, -3; 1, 2, 6] : Matrix (Fin 3) (Fin 3) ℝ)⁻¹ =
      !![-5 / 2, 7 / 2, 1 / 2; 7 / 4, -9 / 4, -1 / 4; -1 / 6, 1 / 6, 1 / 6] := by
  refine Matrix.inv_eq_right_inv ?_
  mt

/-- Stitz-Zeager Exercise 8.4.7: `[[1,2,3],[2,3,11],[3,4,19]]` is not invertible (its determinant is `0`). -/
@[kb "stitzzeager2013" "Exercise 8.4.7, p. 621"]
theorem exer_8_4_7 : ¬ IsUnit (!![1, 2, 3; 2, 3, 11; 3, 4, 19] : Matrix (Fin 3) (Fin 3) ℝ) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_three]
  norm_num

/-- Stitz-Zeager Exercise 8.4.9: `3x + 7y = 26`, `5x + 12y = 39` has the unique solution `(39, -13)`
(the inverse of the coefficient matrix is `[[12,-7],[-5,3]]`). -/
@[kb "stitzzeager2013" "Exercise 8.4.9, p. 621"]
theorem exer_8_4_9 : ∀ x y : ℝ, !![(3 : ℝ), 7; 5, 12] *ᵥ ![x, y] = ![26, 39] ↔ (x = 39 ∧ y = -13) := by
  intro x y
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> norm_num

/-- Stitz-Zeager Exercise 8.4.10: `3x + 7y = 0`, `5x + 12y = -1` has the unique solution `(7, -3)`. -/
@[kb "stitzzeager2013" "Exercise 8.4.10, p. 621"]
theorem exer_8_4_10 : ∀ x y : ℝ, !![(3 : ℝ), 7; 5, 12] *ᵥ ![x, y] = ![0, -1] ↔ (x = 7 ∧ y = -3) := by
  intro x y
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> norm_num

/-- Stitz-Zeager Exercise 8.4.11: `3x + 7y = -7`, `5x + 12y = 5` has the unique solution `(-119, 50)`. -/
@[kb "stitzzeager2013" "Exercise 8.4.11, p. 621"]
theorem exer_8_4_11 : ∀ x y : ℝ, !![(3 : ℝ), 7; 5, 12] *ᵥ ![x, y] = ![-7, 5] ↔ (x = -119 ∧ y = 50) := by
  intro x y
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> norm_num

/-- Stitz-Zeager Exercise 8.4.12: `3x + 4z = 1`, `2x - y + 3z = 0`, `-3x + 2y - 5z = 0` has the unique solution
`(-1, 1, 1)`. -/
@[kb "stitzzeager2013" "Exercise 8.4.12, p. 621"]
theorem exer_8_4_12 : ∀ x y z : ℝ,
    !![(3 : ℝ), 0, 4; 2, -1, 3; -3, 2, -5] *ᵥ ![x, y, z] = ![1, 0, 0] ↔ (x = -1 ∧ y = 1 ∧ z = 1) := by
  intro x y z
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1 h2
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨rfl, rfl, rfl⟩
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> norm_num

/-- Stitz-Zeager Exercise 8.4.13: `3x + 4z = 0`, `2x - y + 3z = 1`, `-3x + 2y - 5z = 0` has the unique solution
`(8, -3, -6)`. -/
@[kb "stitzzeager2013" "Exercise 8.4.13, p. 621"]
theorem exer_8_4_13 : ∀ x y z : ℝ,
    !![(3 : ℝ), 0, 4; 2, -1, 3; -3, 2, -5] *ᵥ ![x, y, z] = ![0, 1, 0] ↔ (x = 8 ∧ y = -3 ∧ z = -6) := by
  intro x y z
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1 h2
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨rfl, rfl, rfl⟩
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> norm_num

/-- Stitz-Zeager Exercise 8.4.14: `3x + 4z = 0`, `2x - y + 3z = 0`, `-3x + 2y - 5z = 1` has the unique solution
`(4, -1, -3)`. -/
@[kb "stitzzeager2013" "Exercise 8.4.14, p. 621"]
theorem exer_8_4_14 : ∀ x y z : ℝ,
    !![(3 : ℝ), 0, 4; 2, -1, 3; -3, 2, -5] *ᵥ ![x, y, z] = ![0, 0, 1] ↔ (x = 4 ∧ y = -1 ∧ z = -3) := by
  intro x y z
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1 h2
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨rfl, rfl, rfl⟩
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> norm_num

/-- Stitz-Zeager Exercise 8.4.16(a): the adult male Sasquatch diet (`500f + 50m + 80s = 3200` calories,
`40f + m = 130` grams of protein, `5m + 15s = 275` mg of Vitamin X) is `3` Ippizuti Fish, `10` Misty Mushrooms
and `15` Sun Berries. -/
@[kb "stitzzeager2013" "Exercise 8.4.16(a), p. 622"]
theorem exer_8_4_16_a : ∀ f m s : ℝ,
    !![(500 : ℝ), 50, 80; 40, 1, 0; 0, 5, 15] *ᵥ ![f, m, s] = ![3200, 130, 275] ↔
      (f = 3 ∧ m = 10 ∧ s = 15) := by
  intro f m s
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1 h2
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨rfl, rfl, rfl⟩
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> norm_num

/-- Stitz-Zeager Exercise 8.4.16(b): the adult female diet (`3100` calories, `120` g protein, `300` mg Vitamin X)
is `3` Ippizuti Fish, no Misty Mushrooms and `20` Sun Berries. -/
@[kb "stitzzeager2013" "Exercise 8.4.16(b), p. 622"]
theorem exer_8_4_16_b : ∀ f m s : ℝ,
    !![(500 : ℝ), 50, 80; 40, 1, 0; 0, 5, 15] *ᵥ ![f, m, s] = ![3100, 120, 300] ↔
      (f = 3 ∧ m = 0 ∧ s = 20) := by
  intro f m s
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1 h2
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨rfl, rfl, rfl⟩
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> norm_num

/-- Stitz-Zeager Exercise 8.4.16(c): the adolescent diet (`5000` calories, `400` g protein, no Vitamin X) is
`10` Ippizuti Fish and nothing else. -/
@[kb "stitzzeager2013" "Exercise 8.4.16(c), p. 622"]
theorem exer_8_4_16_c : ∀ f m s : ℝ,
    !![(500 : ℝ), 50, 80; 40, 1, 0; 0, 5, 15] *ᵥ ![f, m, s] = ![5000, 400, 0] ↔
      (f = 10 ∧ m = 0 ∧ s = 0) := by
  intro f m s
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1 h2
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨rfl, rfl, rfl⟩
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> norm_num

/-- Stitz-Zeager Exercise 8.4.17(a): the encoding matrix `[[2,-3,5],[3,1,-2],[-7,1,-1]]` has inverse
`[[1,2,1],[17,33,19],[10,19,11]]`. -/
@[kb "stitzzeager2013" "Exercise 8.4.17(a), p. 623"]
theorem exer_8_4_17_a :
    (!![2, -3, 5; 3, 1, -2; -7, 1, -1] : Matrix (Fin 3) (Fin 3) ℝ)⁻¹ = !![1, 2, 1; 17, 33, 19; 10, 19, 11] := by
  refine Matrix.inv_eq_right_inv ?_
  mt

/-- Stitz-Zeager Exercise 8.4.17(c): decoding the coded message with `A⁻¹` gives the matrix
`[[12,19,21],[15,0,12],[7,18,5]]` (the letters `LOGS RULE`). -/
@[kb "stitzzeager2013" "Exercise 8.4.17(c), p. 623"]
theorem exer_8_4_17_c :
    (!![1, 2, 1; 17, 33, 19; 10, 19, 11] : Matrix (Fin 3) (Fin 3) ℝ) * !![14, 128, 31; 37, 21, 65; -76, -151, -140] =
      !![12, 19, 21; 15, 0, 12; 7, 18, 5] := by
  mt

/-- Stitz-Zeager Exercise 8.4.18: with `A = [[1,2],[3,4]]`, `B = [[12,-7],[-5,3]]`, `D = [[2,-1],[16,-9]]`:
`AB = D` and `D⁻¹ = B⁻¹ A⁻¹`. -/
@[kb "stitzzeager2013" "Exercise 8.4.18, p. 623"]
theorem exer_8_4_18 :
    (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ) * !![12, -7; -5, 3] = !![2, -1; 16, -9] ∧
    (!![2, -1; 16, -9] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ =
      (!![12, -7; -5, 3] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ * (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ := by
  have hAB : (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ) * !![12, -7; -5, 3] = !![2, -1; 16, -9] := by mt
  refine ⟨hAB, ?_⟩
  rw [← hAB, Matrix.mul_inv_rev]

/-- Stitz-Zeager Exercise 8.4.19: for invertible `n × n` matrices `M`, `N`: `(MN)⁻¹ = N⁻¹ M⁻¹`. -/
@[kb "stitzzeager2013" "Exercise 8.4.19, p. 623"]
theorem exer_8_4_19 : ∀ (n : ℕ) (M N : Matrix (Fin n) (Fin n) ℝ), IsUnit M → IsUnit N →
    (M * N)⁻¹ = N⁻¹ * M⁻¹ := by
  intro n M N _ _
  exact Matrix.mul_inv_rev M N

/-! ## 8.5 Determinants and Cramer's Rule -/

/-- Stitz-Zeager Exercise 8.5.1: `det [[12,-7],[-5,3]] = 1`. -/
@[kb "stitzzeager2013" "Exercise 8.5.1, p. 635"]
theorem exer_8_5_1 : (!![12, -7; -5, 3] : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
  rw [Matrix.det_fin_two_of]; norm_num

/-- Stitz-Zeager Exercise 8.5.2: `det [[6,15],[14,35]] = 0`. -/
@[kb "stitzzeager2013" "Exercise 8.5.2, p. 635"]
theorem exer_8_5_2 : (!![6, 15; 14, 35] : Matrix (Fin 2) (Fin 2) ℝ).det = 0 := by
  rw [Matrix.det_fin_two_of]; norm_num

/-- Stitz-Zeager Exercise 8.5.3: `det [[x, x²],[1, 2x]] = x²`. -/
@[kb "stitzzeager2013" "Exercise 8.5.3, p. 635"]
theorem exer_8_5_3 : ∀ x : ℝ, (!![x, x ^ 2; 1, 2 * x] : Matrix (Fin 2) (Fin 2) ℝ).det = x ^ 2 := by
  intro x
  rw [Matrix.det_fin_two_of]; ring

/-- Stitz-Zeager Exercise 8.5.4: for `x > 0`, `det [[1/x³, ln(x)/x³],[-3/x⁴, (1 - 3 ln x)/x⁴]] = 1/x⁷`. -/
@[kb "stitzzeager2013" "Exercise 8.5.4, p. 635"]
theorem exer_8_5_4 : ∀ x : ℝ, 0 < x →
    (!![1 / x ^ 3, Real.log x / x ^ 3; -3 / x ^ 4, (1 - 3 * Real.log x) / x ^ 4] : Matrix (Fin 2) (Fin 2) ℝ).det =
      1 / x ^ 7 := by
  intro x hx
  rw [Matrix.det_fin_two_of]
  field_simp
  ring

/-- Stitz-Zeager Exercise 8.5.5: `det [[4,6,-3],[3,4,-3],[1,2,6]] = -12`. -/
@[kb "stitzzeager2013" "Exercise 8.5.5, p. 635"]
theorem exer_8_5_5 : (!![4, 6, -3; 3, 4, -3; 1, 2, 6] : Matrix (Fin 3) (Fin 3) ℝ).det = -12 := by
  rw [Matrix.det_fin_three]; norm_num

/-- Stitz-Zeager Exercise 8.5.6: `det [[1,2,3],[2,3,11],[3,4,19]] = 0`. -/
@[kb "stitzzeager2013" "Exercise 8.5.6, p. 635"]
theorem exer_8_5_6 : (!![1, 2, 3; 2, 3, 11; 3, 4, 19] : Matrix (Fin 3) (Fin 3) ℝ).det = 0 := by
  rw [Matrix.det_fin_three]; norm_num

/-- Stitz-Zeager Exercise 8.5.8: `det [[1,0,-3,0],[2,-2,8,7],[-5,0,16,0],[1,0,4,1]] = -2`. -/
@[kb "stitzzeager2013" "Exercise 8.5.8, p. 635"]
theorem exer_8_5_8 :
    (!![1, 0, -3, 0; 2, -2, 8, 7; -5, 0, 16, 0; 1, 0, 4, 1] : Matrix (Fin 4) (Fin 4) ℝ).det = -2 := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  norm_num

/-- Stitz-Zeager Exercise 8.5.9: Cramer's Rule example: `3x + 7y = 26`, `5x + 12y = 39` has `x = 39`, `y = -13`,
with `det A = 1`, `det A_x = 39`, `det A_y = -13`. -/
@[kb "stitzzeager2013" "Exercise 8.5.9, p. 635"]
theorem exer_8_5_9 :
    (!![3, 7; 5, 12] : Matrix (Fin 2) (Fin 2) ℝ).det = 1 ∧ (!![26, 7; 39, 12] : Matrix (Fin 2) (Fin 2) ℝ).det = 39 ∧
    (!![3, 26; 5, 39] : Matrix (Fin 2) (Fin 2) ℝ).det = -13 := by
  refine ⟨?_, ?_, ?_⟩ <;> (rw [Matrix.det_fin_two_of]; norm_num)

/-- Stitz-Zeager Exercise 8.5.10: `2x - 4y = 5`, `10x + 13y = -6` has the unique solution `(41/66, -31/33)`. -/
@[kb "stitzzeager2013" "Exercise 8.5.10, p. 635"]
theorem exer_8_5_10 : ∀ x y : ℝ, (2 * x - 4 * y = 5 ∧ 10 * x + 13 * y = -6) ↔ (x = 41 / 66 ∧ y = -31 / 33) := by
  intro x y
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 8.5.11: `x + y = 8000`, `0.03x + 0.05y = 250` has the unique solution `(7500, 500)`. -/
@[kb "stitzzeager2013" "Exercise 8.5.11, p. 635"]
theorem exer_8_5_11 : ∀ x y : ℝ, (x + y = 8000 ∧ 3 / 100 * x + 5 / 100 * y = 250) ↔ (x = 7500 ∧ y = 500) := by
  intro x y
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 8.5.12: `x/2 - y/5 = 1`, `6x + 7y = 3` has the unique solution `(76/47, -45/47)`. -/
@[kb "stitzzeager2013" "Exercise 8.5.12, p. 635"]
theorem exer_8_5_12 : ∀ x y : ℝ, (1 / 2 * x - 1 / 5 * y = 1 ∧ 6 * x + 7 * y = 3) ↔ (x = 76 / 47 ∧ y = -45 / 47) := by
  intro x y
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 8.5.13: `x+y+z = 3`, `2x-y+z = 0`, `-3x+5y+7z = 7` has the unique solution `(1,2,0)`. -/
@[kb "stitzzeager2013" "Exercise 8.5.13, p. 635"]
theorem exer_8_5_13 : ∀ x y z : ℝ,
    (x + y + z = 3 ∧ 2 * x - y + z = 0 ∧ -3 * x + 5 * y + 7 * z = 7) ↔ (x = 1 ∧ y = 2 ∧ z = 0) := by
  intro x y z
  constructor
  · rintro ⟨h1, h2, h3⟩; refine ⟨?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨rfl, rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 8.5.14: `3x+y-2z = 10`, `4x-y+z = 5`, `x-3y-4z = -1` has the unique solution
`(121/60, 131/60, -53/60)`. -/
@[kb "stitzzeager2013" "Exercise 8.5.14, p. 635"]
theorem exer_8_5_14 : ∀ x y z : ℝ,
    (3 * x + y - 2 * z = 10 ∧ 4 * x - y + z = 5 ∧ x - 3 * y - 4 * z = -1) ↔
      (x = 121 / 60 ∧ y = 131 / 60 ∧ z = -53 / 60) := by
  intro x y z
  constructor
  · rintro ⟨h1, h2, h3⟩; refine ⟨?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨rfl, rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 8.5.15: in the system `x₁-x₃ = -2`, `2x₂-x₄ = 0`, `x₁-2x₂+x₃ = 0`, `-x₃+x₄ = 1`,
`x₄ = 4`. -/
@[kb "stitzzeager2013" "Exercise 8.5.15, p. 635"]
theorem exer_8_5_15 : ∀ x₁ x₂ x₃ x₄ : ℝ,
    (x₁ - x₃ = -2 ∧ 2 * x₂ - x₄ = 0 ∧ x₁ - 2 * x₂ + x₃ = 0 ∧ -x₃ + x₄ = 1) → x₄ = 4 := by
  intro x₁ x₂ x₃ x₄ ⟨h1, h2, h3, h4⟩
  linarith

/-- Stitz-Zeager Exercise 8.5.16: in the system `4x₁+x₂ = 4`, `x₂-3x₃ = 1`, `10x₁+x₃+x₄ = 0`, `-x₂+x₃ = -3`,
`x₄ = -1`. -/
@[kb "stitzzeager2013" "Exercise 8.5.16, p. 635"]
theorem exer_8_5_16 : ∀ x₁ x₂ x₃ x₄ : ℝ,
    (4 * x₁ + x₂ = 4 ∧ x₂ - 3 * x₃ = 1 ∧ 10 * x₁ + x₃ + x₄ = 0 ∧ -x₂ + x₃ = -3) → x₄ = -1 := by
  intro x₁ x₂ x₃ x₄ ⟨h1, h2, h3, h4⟩
  linarith

/-- Stitz-Zeager Exercise 8.5.17: the inverse of `B = [[12,-7],[-5,3]]` from its determinant and adjugate:
`det B = 1` and `(det B)⁻¹ · adj B = [[3,7],[5,12]]`. -/
@[kb "stitzzeager2013" "Exercise 8.5.17, p. 636"]
theorem exer_8_5_17 : ∀ B : Matrix (Fin 2) (Fin 2) ℝ, B = !![12, -7; -5, 3] →
    B.det = 1 ∧ B.det⁻¹ • B.adjugate = !![3, 7; 5, 12] := by
  intro B hB
  subst hB
  have hd : (!![12, -7; -5, 3] : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by rw [Matrix.det_fin_two_of]; norm_num
  refine ⟨hd, ?_⟩
  rw [hd, Matrix.adjugate_fin_two_of]
  mt

/-- Stitz-Zeager Exercise 8.5.18: for `F = [[4,6,-3],[3,4,-3],[1,2,6]]`, `det F = -12` and
`(det F)⁻¹ · adj F = [[-5/2,7/2,1/2],[7/4,-9/4,-1/4],[-1/6,1/6,1/6]]`. -/
@[kb "stitzzeager2013" "Exercise 8.5.18, p. 636"]
theorem exer_8_5_18 : ∀ F : Matrix (Fin 3) (Fin 3) ℝ, F = !![4, 6, -3; 3, 4, -3; 1, 2, 6] →
    F.det = -12 ∧ F.det⁻¹ • F.adjugate = !![-5 / 2, 7 / 2, 1 / 2; 7 / 4, -9 / 4, -1 / 4; -1 / 6, 1 / 6, 1 / 6] := by
  intro F hF
  subst hF
  have hd : (!![4, 6, -3; 3, 4, -3; 1, 2, 6] : Matrix (Fin 3) (Fin 3) ℝ).det = -12 := by
    rw [Matrix.det_fin_three]; norm_num
  refine ⟨hd, ?_⟩
  rw [hd, Matrix.adjugate_fin_three_of]
  mt

/-- Stitz-Zeager Exercise 8.5.19: `c + r = 117` cards with `0.25c + 0.75r = 48.75` dollars means `78` common
and `39` rare cards. -/
@[kb "stitzzeager2013" "Exercise 8.5.19, p. 636"]
theorem exer_8_5_19 : ∀ c r : ℝ, (c + r = 117 ∧ 1 / 4 * c + 3 / 4 * r = 195 / 4) ↔ (c = 78 ∧ r = 39) := by
  intro c r
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 8.5.20: replacing `x` gallons of a `5` gallon `40%` salt solution by pure water to get
`15%`: `0.4 (5 - x) = 0.15 · 5` holds exactly for `x = 3.125`. -/
@[kb "stitzzeager2013" "Exercise 8.5.20, p. 636"]
theorem exer_8_5_20 : ∀ x : ℝ, 2 / 5 * (5 - x) = 3 / 20 * 5 ↔ x = 25 / 8 := by
  intro x
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 8.5.21: replacing `x` liters of a `10` liter `30%` acid solution by pure acid to get
`50%`: `0.3 (10 - x) + x = 0.5 · 10` holds exactly for `x = 20/7`. -/
@[kb "stitzzeager2013" "Exercise 8.5.21, p. 636"]
theorem exer_8_5_21 : ∀ x : ℝ, 3 / 10 * (10 - x) + x = 1 / 2 * 10 ↔ x = 20 / 7 := by
  intro x
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 8.5.22: snakes `s`, tarantulas `t`, scorpions `c` with `s + t + c = 49`,
`8t + 8c = 272` legs and `s + c = 28` tails: `15` snakes, `21` tarantulas, `13` scorpions. -/
@[kb "stitzzeager2013" "Exercise 8.5.22, p. 636"]
theorem exer_8_5_22 : ∀ s t c : ℝ,
    (s + t + c = 49 ∧ 8 * t + 8 * c = 272 ∧ s + c = 28) ↔ (s = 15 ∧ t = 21 ∧ c = 13) := by
  intro s t c
  constructor
  · rintro ⟨h1, h2, h3⟩; refine ⟨?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨rfl, rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 8.5.23: the diet `500f + 50m + 80s = 2500`, `40f + m = 1000`, `5m + 15s = 400` has the
mathematical solution `f = 53`, `m = -1120`, `s = 400`; the negative number of servings of Misty Mushrooms means
there is no solution that makes sense for the applied problem. -/
@[kb "stitzzeager2013" "Exercise 8.5.23, p. 636"]
theorem exer_8_5_23 : ∀ f m s : ℝ,
    (500 * f + 50 * m + 80 * s = 2500 ∧ 40 * f + m = 1000 ∧ 5 * m + 15 * s = 400) ↔
      (f = 53 ∧ m = -1120 ∧ s = 400) := by
  intro f m s
  constructor
  · rintro ⟨h1, h2, h3⟩; refine ⟨?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨rfl, rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 8.5.24: for `R = [[-7,3],[11,2]]`, `S = [[1,-5],[6,9]]`, `T = [[11,2],[-7,3]]`,
`U = [[-3,15],[6,9]]`: `det (RS) = det R · det S`, `det T = - det R`, `det U = -3 det S`. -/
@[kb "stitzzeager2013" "Exercise 8.5.24, p. 636"]
theorem exer_8_5_24 : ∀ R S T U : Matrix (Fin 2) (Fin 2) ℝ,
    R = !![-7, 3; 11, 2] → S = !![1, -5; 6, 9] → T = !![11, 2; -7, 3] → U = !![-3, 15; 6, 9] →
    (R * S).det = R.det * S.det ∧ T.det = - R.det ∧ U.det = -3 * S.det := by
  intro R S T U hR hS hT hU
  subst hR hS hT hU
  have hRS : (!![-7, 3; 11, 2] : Matrix (Fin 2) (Fin 2) ℝ) * !![1, -5; 6, 9] = !![11, 62; 23, -37] := by mt
  refine ⟨?_, ?_, ?_⟩
  · rw [hRS]; simp only [Matrix.det_fin_two_of]; norm_num
  · simp only [Matrix.det_fin_two_of]; norm_num
  · simp only [Matrix.det_fin_two_of]; norm_num

/-- Stitz-Zeager Exercise 8.5.25: the matrices `[[1,2,3],[0,0,0],[7,8,9]]`, `[[1,2,3],[1,2,3],[4,5,6]]` and
`[[1,2,3],[-2,-4,-6],[7,8,9]]` all have determinant `0`. -/
@[kb "stitzzeager2013" "Exercise 8.5.25, p. 636"]
theorem exer_8_5_25 :
    (!![1, 2, 3; 0, 0, 0; 7, 8, 9] : Matrix (Fin 3) (Fin 3) ℝ).det = 0 ∧
    (!![1, 2, 3; 1, 2, 3; 4, 5, 6] : Matrix (Fin 3) (Fin 3) ℝ).det = 0 ∧
    (!![1, 2, 3; -2, -4, -6; 7, 8, 9] : Matrix (Fin 3) (Fin 3) ℝ).det = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> (rw [Matrix.det_fin_three]; norm_num)

/-- Stitz-Zeager Exercise 8.5.26: `det I₃ = 1`, and for an invertible `3 × 3` matrix `A`,
`det (A⁻¹) = 1 / det A`. -/
@[kb "stitzzeager2013" "Exercise 8.5.26, p. 637"]
theorem exer_8_5_26 : (1 : Matrix (Fin 3) (Fin 3) ℝ).det = 1 ∧
    ∀ A : Matrix (Fin 3) (Fin 3) ℝ, IsUnit A.det → A⁻¹.det = 1 / A.det := by
  refine ⟨Matrix.det_one, fun A hA => ?_⟩
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', one_div]

/-- Stitz-Zeager Exercise 8.5.27: the characteristic polynomial of `G = [[1,2,3],[2,3,11],[3,4,19]]` is
`det (G - λ I₃) = -λ(λ-1)(λ-22)`. -/
@[kb "stitzzeager2013" "Exercise 8.5.27, p. 637"]
theorem exer_8_5_27 : ∀ l : ℝ,
    (!![1 - l, 2, 3; 2, 3 - l, 11; 3, 4, 19 - l] : Matrix (Fin 3) (Fin 3) ℝ).det = -l * (l - 1) * (l - 22) := by
  intro l
  rw [Matrix.det_fin_three]
  simp
  ring

end UndergradKB.Precalculus.Course
