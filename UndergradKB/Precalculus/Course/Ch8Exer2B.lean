import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 8 (Stitz-Zeager): exercises with the book's answers (wave 7), Sections 8.3, 8.5, 8.6, 8.7 -/

namespace UndergradKB.Precalculus.Course

open Matrix Filter Topology

/-- Entrywise proof of a matrix identity with explicit small matrices. -/
local macro "mt" : tactic =>
  `(tactic| (ext i j; fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.smul_apply] <;> (try norm_num) <;> (try ring)))

/-! ## 8.3 Matrix Arithmetic -/

/-- Stitz-Zeager Exercise 8.3.12: with `E = [[1,2,3],[0,4,-9],[0,0,-5]]` and `D = [[7,-13],[-4/3,0],[6,8]]`:
`ED = [[67/3,11],[-178/3,-72],[-30,-40]]`. -/
@[kb "stitzzeager2013" "Exercise 8.3.12, p. 603"]
theorem exer_8_3_12 :
    let E : Matrix (Fin 3) (Fin 3) ℝ := !![1, 2, 3; 0, 4, -9; 0, 0, -5]
    let D : Matrix (Fin 3) (Fin 2) ℝ := !![7, -13; -4 / 3, 0; 6, 8]
    E * D = !![67 / 3, 11; -178 / 3, -72; -30, -40] := by
  dsimp only
  mt

/-- Stitz-Zeager Exercise 8.3.13: with `C = [[10,-11/2,0],[3/5,5,9]]`, `D = [[7,-13],[-4/3,0],[6,8]]` and
`A = [[1,2],[3,4]]`: `CD + 2 I₂ A = [[238/3,-126],[863/15,361/5]]`. -/
@[kb "stitzzeager2013" "Exercise 8.3.13, p. 603"]
theorem exer_8_3_13 :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![1, 2; 3, 4]
    let C : Matrix (Fin 2) (Fin 3) ℝ := !![10, -11 / 2, 0; 3 / 5, 5, 9]
    let D : Matrix (Fin 3) (Fin 2) ℝ := !![7, -13; -4 / 3, 0; 6, 8]
    C * D + ((2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) * A = !![238 / 3, -126; 863 / 15, 361 / 5] := by
  dsimp only
  mt

/-- Stitz-Zeager Exercise 8.3.19: `EDC = [[3449/15,-407/6,99],[-9548/15,-101/3,-648],[-324,-35,-360]]` for the
matrices `E`, `D`, `C` above. -/
@[kb "stitzzeager2013" "Exercise 8.3.19, p. 603"]
theorem exer_8_3_19 :
    let C : Matrix (Fin 2) (Fin 3) ℝ := !![10, -11 / 2, 0; 3 / 5, 5, 9]
    let D : Matrix (Fin 3) (Fin 2) ℝ := !![7, -13; -4 / 3, 0; 6, 8]
    let E : Matrix (Fin 3) (Fin 3) ℝ := !![1, 2, 3; 0, 4, -9; 0, 0, -5]
    E * D * C = !![3449 / 15, -407 / 6, 99; -9548 / 15, -101 / 3, -648; -324, -35, -360] := by
  dsimp only
  mt

/-- Stitz-Zeager Exercise 8.3.21: `ABCEDI₂ = [[-90749/15,-28867/5],[-156601/15,-47033/5]]`. -/
@[kb "stitzzeager2013" "Exercise 8.3.21, p. 603"]
theorem exer_8_3_21 :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![1, 2; 3, 4]
    let B : Matrix (Fin 2) (Fin 2) ℝ := !![0, -3; -5, 2]
    let C : Matrix (Fin 2) (Fin 3) ℝ := !![10, -11 / 2, 0; 3 / 5, 5, 9]
    let D : Matrix (Fin 3) (Fin 2) ℝ := !![7, -13; -4 / 3, 0; 6, 8]
    let E : Matrix (Fin 3) (Fin 3) ℝ := !![1, 2, 3; 0, 4, -9; 0, 0, -5]
    A * B * C * E * D * (1 : Matrix (Fin 2) (Fin 2) ℝ) =
      !![-90749 / 15, -28867 / 5; -156601 / 15, -47033 / 5] := by
  dsimp only
  rw [Matrix.mul_one]
  mt

/-- Stitz-Zeager Exercise 8.3.24: with `Q = [[0.9,0.2],[0.1,0.8]]` and `X = (150, 0)`, the Week 2 numbers
`Q² X` are `(249/2, 51/2)`, i.e. `124.5` and `25.5` subscribers. -/
@[kb "stitzzeager2013" "Exercise 8.3.24, p. 604"]
theorem exer_8_3_24 :
    (!![(9 : ℝ) / 10, 1 / 5; 1 / 10, 4 / 5] ^ 2) *ᵥ ![150, 0] = ![249 / 2, 51 / 2] := by
  have hQ : (!![(9 : ℝ) / 10, 1 / 5; 1 / 10, 4 / 5] ^ 2) = !![83 / 100, 17 / 50; 17 / 100, 33 / 50] := by mt
  rw [hQ]
  ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> norm_num

/-- Stitz-Zeager Exercise 8.3.28: `Qⁿ = S + (7/10)ⁿ T` with `S = [[2/3,2/3],[1/3,1/3]]` and
`T = [[1/3,-2/3],[-1/3,2/3]]`, hence `Qⁿ → S` as `n → ∞`. -/
@[kb "stitzzeager2013" "Exercise 8.3.28, p. 605"]
theorem exer_8_3_28 :
    (∀ n : ℕ, !![(9 : ℝ) / 10, 1 / 5; 1 / 10, 4 / 5] ^ n =
      !![(2 : ℝ) / 3, 2 / 3; 1 / 3, 1 / 3] + ((7 : ℝ) / 10) ^ n • !![(1 : ℝ) / 3, -2 / 3; -1 / 3, 2 / 3]) ∧
    Tendsto (fun n : ℕ => !![(9 : ℝ) / 10, 1 / 5; 1 / 10, 4 / 5] ^ n) atTop
      (𝓝 !![(2 : ℝ) / 3, 2 / 3; 1 / 3, 1 / 3]) := by
  have hf : ∀ n : ℕ, !![(9 : ℝ) / 10, 1 / 5; 1 / 10, 4 / 5] ^ n =
      !![(2 : ℝ) / 3, 2 / 3; 1 / 3, 1 / 3] + ((7 : ℝ) / 10) ^ n • !![(1 : ℝ) / 3, -2 / 3; -1 / 3, 2 / 3] := by
    intro n
    induction n with
    | zero =>
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply] <;> norm_num
    | succ n ih =>
      rw [pow_succ, ih]
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.smul_apply, pow_succ] <;> ring
  refine ⟨hf, ?_⟩
  have h0 : Tendsto (fun n : ℕ => ((7 : ℝ) / 10) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h1 := (tendsto_const_nhds (x := !![(2 : ℝ) / 3, 2 / 3; 1 / 3, 1 / 3])).add
    (h0.smul_const !![(1 : ℝ) / 3, -2 / 3; -1 / 3, 2 / 3])
  simp only [zero_smul, add_zero] at h1
  exact h1.congr (fun n => (hf n).symm)

/-- Stitz-Zeager Exercise 8.3.32: `[[1,2],[3,4]]` is neither upper triangular nor lower triangular. -/
@[kb "stitzzeager2013" "Exercise 8.3.32, p. 606"]
theorem exer_8_3_32 :
    ¬ (∀ i j : Fin 2, j < i → (!![(1 : ℝ), 2; 3, 4]) i j = 0) ∧
    ¬ (∀ i j : Fin 2, i < j → (!![(1 : ℝ), 2; 3, 4]) i j = 0) := by
  constructor
  · intro h; have := h 1 0 (by decide); simp at this
  · intro h; have := h 0 1 (by decide); simp at this

/-- Stitz-Zeager Exercise 8.3.33: the product of two upper triangular `n × n` matrices is upper triangular. -/
@[kb "stitzzeager2013" "Exercise 8.3.33, p. 606"]
theorem exer_8_3_33 : ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ),
    (∀ i j, j < i → A i j = 0) → (∀ i j, j < i → B i j = 0) → ∀ i j, j < i → (A * B) i j = 0 := by
  intro n A B hA hB i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k < i
  · rw [hA i k hk, zero_mul]
  · rw [hB k j (lt_of_lt_of_le hij (not_lt.mp hk)), mul_zero]

/-- Stitz-Zeager Exercise 8.3.34: the product of two lower triangular `n × n` matrices is lower triangular. -/
@[kb "stitzzeager2013" "Exercise 8.3.34, p. 606"]
theorem exer_8_3_34 : ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ),
    (∀ i j, i < j → A i j = 0) → (∀ i j, i < j → B i j = 0) → ∀ i j, i < j → (A * B) i j = 0 := by
  intro n A B hA hB i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : i < k
  · rw [hA i k hk, zero_mul]
  · rw [hB k j (lt_of_le_of_lt (not_lt.mp hk) hij), mul_zero]

/-- Stitz-Zeager Exercise 8.3.35: `[[1,2],[3,4]] = L U` with the lower triangular `L = [[1,0],[3,1]]` and the
upper triangular `U = [[1,2],[0,-2]]`. -/
@[kb "stitzzeager2013" "Exercise 8.3.35, p. 606"]
theorem exer_8_3_35 :
    (!![(1 : ℝ), 2; 3, 4] = !![1, 0; 3, 1] * !![1, 2; 0, -2]) ∧ (!![(1 : ℝ), 0; 3, 1]) 0 1 = 0 ∧
      (!![(1 : ℝ), 2; 0, -2]) 1 0 = 0 := by
  refine ⟨?_, by simp, by simp⟩
  mt

/-- Stitz-Zeager Exercise 8.3.36: a square matrix is both upper and lower triangular exactly when it is
diagonal (all off-diagonal entries vanish). -/
@[kb "stitzzeager2013" "Exercise 8.3.36, p. 606"]
theorem exer_8_3_36 : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
    ((∀ i j, j < i → A i j = 0) ∧ (∀ i j, i < j → A i j = 0)) ↔ ∀ i j, i ≠ j → A i j = 0 := by
  intro n A
  constructor
  · rintro ⟨hu, hl⟩ i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hl i j h
    · exact hu i j h
  · intro h
    exact ⟨fun i j hji => h i j (ne_of_gt hji), fun i j hij => h i j (ne_of_lt hij)⟩

/-! ## 8.5 Determinants and Cramer's Rule -/

/-- Stitz-Zeager Exercise 8.5.7: `det [[i,j,k],[-1,0,5],[9,-4,-2]] = 20 i + 43 j + 4 k`. -/
@[kb "stitzzeager2013" "Exercise 8.5.7, p. 635"]
theorem exer_8_5_7 : ∀ i j k : ℝ,
    (!![i, j, k; -1, 0, 5; 9, -4, -2] : Matrix (Fin 3) (Fin 3) ℝ).det = 20 * i + 43 * j + 4 * k := by
  intro i j k
  rw [Matrix.det_fin_three]
  simp
  ring

/-! ## 8.6 Partial Fraction Decomposition -/

/-- Stitz-Zeager Exercise 8.6.1: `7/((x-3)(x+5))` has a decomposition of the form `A/(x-3) + B/(x+5)`. -/
@[kb "stitzzeager2013" "Exercise 8.6.1, p. 647"]
theorem exer_8_6_1 : ∃ A B : ℝ, ∀ x : ℝ, x ≠ 3 → x ≠ -5 →
    7 / ((x - 3) * (x + 5)) = A / (x - 3) + B / (x + 5) := by
  refine ⟨7 / 8, -7 / 8, fun x h1 h2 => ?_⟩
  have h1' : x - 3 ≠ 0 := sub_ne_zero.mpr h1
  have h2' : x + 5 ≠ 0 := by intro h; apply h2; linarith
  field_simp
  ring

/-- Stitz-Zeager Exercise 8.6.2: `(5x+4)/(x(x-2)(2-x))` has a decomposition of the form
`A/x + B/(x-2) + C/(x-2)²`. -/
@[kb "stitzzeager2013" "Exercise 8.6.2, p. 647"]
theorem exer_8_6_2 : ∃ A B C : ℝ, ∀ x : ℝ, x ≠ 0 → x ≠ 2 →
    (5 * x + 4) / (x * (x - 2) * (2 - x)) = A / x + B / (x - 2) + C / (x - 2) ^ 2 := by
  refine ⟨-1, 1, -7, fun x h1 h2 => ?_⟩
  have h2' : x - 2 ≠ 0 := sub_ne_zero.mpr h2
  have h3 : 2 - x ≠ 0 := by intro h; apply h2'; linarith
  field_simp
  ring

/-- Stitz-Zeager Exercise 8.6.3: `m/((7x-6)(x²+9))` has a decomposition of the form
`A/(7x-6) + (Bx+C)/(x²+9)`, for every constant `m`. -/
@[kb "stitzzeager2013" "Exercise 8.6.3, p. 647"]
theorem exer_8_6_3 : ∀ m : ℝ, ∃ A B C : ℝ, ∀ x : ℝ, 7 * x - 6 ≠ 0 →
    m / ((7 * x - 6) * (x ^ 2 + 9)) = A / (7 * x - 6) + (B * x + C) / (x ^ 2 + 9) := by
  intro m
  refine ⟨49 * m / 477, -7 * m / 477, -2 * m / 159, fun x h1 => ?_⟩
  have h2 : x ^ 2 + 9 ≠ 0 := by positivity
  field_simp
  ring

/-! ## 8.7 Systems of Non-Linear Equations and Inequalities -/

/-- Stitz-Zeager Exercise 8.7.15: the system `x² + y² = 25`, `4x² - 9y = 0`, `3y² - 16x = 0` has the single
solution `(3, 4)`. -/
@[kb "stitzzeager2013" "Exercise 8.7.15, p. 658"]
theorem exer_8_7_15 : ∀ x y : ℝ,
    (x ^ 2 + y ^ 2 = 25 ∧ 4 * x ^ 2 - 9 * y = 0 ∧ 3 * y ^ 2 - 16 * x = 0) ↔ (x = 3 ∧ y = 4) := by
  intro x y
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hy : y = 4 * x ^ 2 / 9 := by linarith
    have h4 : x * (x ^ 3 - 27) = 0 := by rw [hy] at h3; nlinarith [h3]
    rcases mul_eq_zero.mp h4 with h | h
    · exfalso
      rw [h] at hy h1
      nlinarith
    · have h5 : (x - 3) * (x ^ 2 + 3 * x + 9) = 0 := by nlinarith [h]
      rcases mul_eq_zero.mp h5 with h6 | h6
      · have hx : x = 3 := by linarith
        refine ⟨hx, ?_⟩
        rw [hy, hx]; norm_num
      · exfalso; nlinarith [sq_nonneg (x + 3 / 2)]
  · rintro ⟨rfl, rfl⟩; norm_num

end UndergradKB.Precalculus.Course
