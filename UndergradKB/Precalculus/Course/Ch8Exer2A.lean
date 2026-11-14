import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Echelon.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import UndergradKB.Precalculus.Systems
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 8 (Stitz-Zeager): exercises with the book's answers (wave 7), Sections 8.1, 8.2 and 8.4 -/

namespace UndergradKB.Precalculus.Course

open Matrix UndergradKB.Precalculus

/-! ## Helpers -/

private theorem mv2 (a b c d x y p q : ℝ) :
    !![a, b; c, d] *ᵥ ![x, y] = ![p, q] ↔ a * x + b * y = p ∧ c * x + d * y = q := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h0, h1⟩
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> linarith

private theorem mv3 (a b c d e f g h i x y z p q r : ℝ) :
    !![a, b, c; d, e, f; g, h, i] *ᵥ ![x, y, z] = ![p, q, r] ↔
      a * x + b * y + c * z = p ∧ d * x + e * y + f * z = q ∧ g * x + h * y + i * z = r := by
  constructor
  · intro hh
    have h0 := congrFun hh 0
    have h1 := congrFun hh 1
    have h2 := congrFun hh 2
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1 h2
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h0, h1, h2⟩
    ext j; fin_cases j <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> linarith

private theorem mv4 (a b c d e f g h i j k l m n o p x y z w q r s t : ℝ) :
    !![a, b, c, d; e, f, g, h; i, j, k, l; m, n, o, p] *ᵥ ![x, y, z, w] = ![q, r, s, t] ↔
      a * x + b * y + c * z + d * w = q ∧ e * x + f * y + g * z + h * w = r ∧
      i * x + j * y + k * z + l * w = s ∧ m * x + n * y + o * z + p * w = t := by
  constructor
  · intro hh
    have h0 := congrFun hh 0
    have h1 := congrFun hh 1
    have h2 := congrFun hh 2
    have h3 := congrFun hh 3
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1 h2 h3
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨h0, h1, h2, h3⟩
    ext u; fin_cases u <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> linarith

/-- Entrywise proof of a matrix identity with explicit small matrices. -/
local macro "mt" : tactic =>
  `(tactic| (ext i j; fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.smul_apply] <;> (try norm_num) <;> (try ring)))

/-- Closes the impossible branches of an echelon-form check by finding a nonzero entry among the leading
zeros. -/
local macro "clo " h:ident : tactic =>
  `(tactic| first
    | (have := $h 0 (by decide); simp at this; done)
    | (have := $h 1 (by decide); simp at this; done)
    | (have := $h 2 (by decide); simp at this; done)
    | (have := $h 3 (by decide); simp at this; done))

/-- The row-echelon condition of a concrete matrix, checked case by case. -/
local macro "ref1" : tactic =>
  `(tactic| (intro i₁ i₂ h j₂ hj
             fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₂ <;> simp at h hj ⊢ <;> clo hj))

/-- Every leading entry of a concrete matrix is `1`. -/
local macro "one1" : tactic =>
  `(tactic| (intro i c h
             fin_cases i <;> fin_cases c <;> simp [Matrix.IsLeadingEntry] at h ⊢ <;> clo h))

/-- Entries above a leading entry of a concrete matrix vanish. -/
local macro "zero1" : tactic =>
  `(tactic| (intro i₁ i₂ c h hc
             fin_cases i₁ <;> fin_cases i₂ <;> fin_cases c <;> simp [Matrix.IsLeadingEntry] at h hc ⊢ <;>
               clo hc))

/-! ## 8.1 Systems of Linear Equations: Gaussian Elimination -/

/-- Stitz-Zeager Exercise 8.1.4: `2x/3 - y/5 = 3`, `x/2 + 3y/4 = 1` is consistent independent with solution
`(49/12, -25/18)`. -/
@[kb "stitzzeager2013" "Exercise 8.1.4, p. 574"]
theorem exer_8_1_4 : ∀ x y : ℝ, (2 / 3 * x - 1 / 5 * y = 3 ∧ 1 / 2 * x + 3 / 4 * y = 1) ↔
    (x = 49 / 12 ∧ y = -25 / 18) := by
  intro x y
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 8.1.6: `x + 4y = 6`, `x/12 + y/3 = 1/2` is consistent dependent with solutions
`(6 - 4t, t)`. -/
@[kb "stitzzeager2013" "Exercise 8.1.6, p. 574"]
theorem exer_8_1_6 : ∀ x y : ℝ, (x + 4 * y = 6 ∧ 1 / 12 * x + 1 / 3 * y = 1 / 2) ↔
    ∃ t : ℝ, x = 6 - 4 * t ∧ y = t := by
  intro x y
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨y, by linarith, rfl⟩
  · rintro ⟨t, rfl, rfl⟩; constructor <;> ring

/-- Stitz-Zeager Exercise 8.1.7: `3y - 3x/2 = -15/2`, `x/2 - y = 3/2` is inconsistent. -/
@[kb "stitzzeager2013" "Exercise 8.1.7, p. 574"]
theorem exer_8_1_7 : ¬ ∃ x y : ℝ, 3 * y - 3 / 2 * x = -15 / 2 ∧ 1 / 2 * x - y = 3 / 2 := by
  rintro ⟨x, y, h1, h2⟩
  linarith

/-- Stitz-Zeager Exercise 8.1.8: `5x/6 + 5y/3 = -7/3`, `-10x/3 - 20y/3 = 10` is inconsistent. -/
@[kb "stitzzeager2013" "Exercise 8.1.8, p. 574"]
theorem exer_8_1_8 : ¬ ∃ x y : ℝ, 5 / 6 * x + 5 / 3 * y = -7 / 3 ∧ -10 / 3 * x - 20 / 3 * y = 10 := by
  rintro ⟨x, y, h1, h2⟩
  linarith

/-- Stitz-Zeager Exercise 8.1.15: `3x - 2y + z = -5`, `x + 3y - z = 12`, `x + y + 2z = 0` has the unique
solution `(1, 3, -2)`. -/
@[kb "stitzzeager2013" "Exercise 8.1.15, p. 574"]
theorem exer_8_1_15 : ∀ x y z : ℝ,
    (3 * x - 2 * y + z = -5 ∧ x + 3 * y - z = 12 ∧ x + y + 2 * z = 0) ↔ (x = 1 ∧ y = 3 ∧ z = -2) := by
  intro x y z
  constructor
  · rintro ⟨h1, h2, h3⟩; refine ⟨?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨rfl, rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 8.1.26: the system `x₁-x₂-5x₃+3x₄ = -1`, `x₁+x₂+5x₃-3x₄ = 0`,
`x₂+5x₃-3x₄ = 1`, `x₁-2x₂-10x₃+6x₄ = -1` is inconsistent. -/
@[kb "stitzzeager2013" "Exercise 8.1.26, p. 575"]
theorem exer_8_1_26 : ¬ ∃ x₁ x₂ x₃ x₄ : ℝ, x₁ - x₂ - 5 * x₃ + 3 * x₄ = -1 ∧ x₁ + x₂ + 5 * x₃ - 3 * x₄ = 0 ∧
    x₂ + 5 * x₃ - 3 * x₄ = 1 ∧ x₁ - 2 * x₂ - 10 * x₃ + 6 * x₄ = -1 := by
  rintro ⟨x₁, x₂, x₃, x₄, h1, h2, h3, h4⟩
  linarith

/-! ## 8.2 Systems of Linear Equations: Augmented Matrices -/

/-- Stitz-Zeager Exercise 8.2.1: `[[1,0,3],[0,1,3]]` is in reduced row echelon form (conditions of
Definitions 8.4 and 8.5 checked entrywise). -/
@[kb "stitzzeager2013" "Exercise 8.2.1, p. 586"]
theorem exer_8_2_1 : (!![(1 : ℝ), 0, 3; 0, 1, 3]).IsReducedRowEchelon ∧
    IsRowEchelonForm (!![(1 : ℝ), 0, 3; 0, 1, 3]) := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩
  · ref1
  · one1
  · zero1
  · ref1
  · one1

/-- Stitz-Zeager Exercise 8.2.2: `[[3,-1,1,3],[2,-4,3,16],[1,-1,1,5]]` is in neither row echelon form nor
reduced row echelon form (its first leading entry is `3`, not `1`). -/
@[kb "stitzzeager2013" "Exercise 8.2.2, p. 586"]
theorem exer_8_2_2 : ¬ IsRowEchelonForm (!![(3 : ℝ), -1, 1, 3; 2, -4, 3, 16; 1, -1, 1, 5]) ∧
    ¬ (!![(3 : ℝ), -1, 1, 3; 2, -4, 3, 16; 1, -1, 1, 5]).IsReducedRowEchelon := by
  have h3 : (!![(3 : ℝ), -1, 1, 3; 2, -4, 3, 16; 1, -1, 1, 5]).IsLeadingEntry 0 0 := by
    simp [Matrix.IsLeadingEntry]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h.2 0 0 h3; simp at this
  · have := h.eq_one h3; simp at this

/-- Stitz-Zeager Exercise 8.2.3: `[[1,1,4,3],[0,1,3,6],[0,0,0,1]]` is in row echelon form but not in reduced
row echelon form (the leading `1` of row 2 has a `1` above it). -/
@[kb "stitzzeager2013" "Exercise 8.2.3, p. 586"]
theorem exer_8_2_3 : IsRowEchelonForm (!![(1 : ℝ), 1, 4, 3; 0, 1, 3, 6; 0, 0, 0, 1]) ∧
    ¬ (!![(1 : ℝ), 1, 4, 3; 0, 1, 3, 6; 0, 0, 0, 1]).IsReducedRowEchelon := by
  refine ⟨⟨?_, ?_⟩, fun h => ?_⟩
  · ref1
  · one1
  · have := h.eq_zero (i₁ := 0) (i₂ := 1) (c := 1) (by decide) (by simp [Matrix.IsLeadingEntry])
    simp at this

/-- Stitz-Zeager Exercise 8.2.4: `[[1,0,0,0],[0,1,0,0],[0,0,0,1]]` is in reduced row echelon form. -/
@[kb "stitzzeager2013" "Exercise 8.2.4, p. 586"]
theorem exer_8_2_4 : (!![(1 : ℝ), 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1]).IsReducedRowEchelon ∧
    IsRowEchelonForm (!![(1 : ℝ), 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1]) := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩
  · ref1
  · one1
  · zero1
  · ref1
  · one1

/-- Stitz-Zeager Exercise 8.2.5: `[[1,0,4,3,0],[0,1,3,6,0],[0,0,0,0,0]]` is in reduced row echelon form. -/
@[kb "stitzzeager2013" "Exercise 8.2.5, p. 586"]
theorem exer_8_2_5 : (!![(1 : ℝ), 0, 4, 3, 0; 0, 1, 3, 6, 0; 0, 0, 0, 0, 0]).IsReducedRowEchelon ∧
    IsRowEchelonForm (!![(1 : ℝ), 0, 4, 3, 0; 0, 1, 3, 6, 0; 0, 0, 0, 0, 0]) := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩
  · ref1
  · one1
  · zero1
  · ref1
  · one1

/-- Stitz-Zeager Exercise 8.2.6: `[[1,1,4,3],[0,1,3,6]]` is in row echelon form but not in reduced row echelon
form. -/
@[kb "stitzzeager2013" "Exercise 8.2.6, p. 586"]
theorem exer_8_2_6 : IsRowEchelonForm (!![(1 : ℝ), 1, 4, 3; 0, 1, 3, 6]) ∧
    ¬ (!![(1 : ℝ), 1, 4, 3; 0, 1, 3, 6]).IsReducedRowEchelon := by
  refine ⟨⟨?_, ?_⟩, fun h => ?_⟩
  · ref1
  · one1
  · have := h.eq_zero (i₁ := 0) (i₂ := 1) (c := 1) (by decide) (by simp [Matrix.IsLeadingEntry])
    simp at this

/-- Stitz-Zeager Exercise 8.2.13: `-5x + y = 17`, `x + y = 5` has the solution `(-2, 7)`, as `A v = b`. -/
@[kb "stitzzeager2013" "Exercise 8.2.13, p. 586"]
theorem exer_8_2_13 : ∀ x y : ℝ, !![(-5 : ℝ), 1; 1, 1] *ᵥ ![x, y] = ![17, 5] ↔ (x = -2 ∧ y = 7) := by
  intro x y
  rw [mv2]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 8.2.15: `4x - y + z = 5`, `2y + 6z = 30`, `x + z = 5` has the solutions
`(-t+5, -3t+15, t)`. -/
@[kb "stitzzeager2013" "Exercise 8.2.15, p. 586"]
theorem exer_8_2_15 : ∀ x y z : ℝ,
    !![(4 : ℝ), -1, 1; 0, 2, 6; 1, 0, 1] *ᵥ ![x, y, z] = ![5, 30, 5] ↔
      ∃ t : ℝ, x = -t + 5 ∧ y = -3 * t + 15 ∧ z = t := by
  intro x y z
  rw [mv3]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨z, by linarith, by linarith, rfl⟩
  · rintro ⟨t, rfl, rfl, rfl⟩; refine ⟨?_, ?_, ?_⟩ <;> ring

/-- Stitz-Zeager Exercise 8.2.16: `x-2y+3z = 7`, `-3x+y+2z = -5`, `2x+2y+z = 3` has the unique solution
`(2, -1, 1)`. -/
@[kb "stitzzeager2013" "Exercise 8.2.16, p. 586"]
theorem exer_8_2_16 : ∀ x y z : ℝ,
    !![(1 : ℝ), -2, 3; -3, 1, 2; 2, 2, 1] *ᵥ ![x, y, z] = ![7, -5, 3] ↔ (x = 2 ∧ y = -1 ∧ z = 1) := by
  intro x y z
  rw [mv3]
  constructor
  · rintro ⟨h1, h2, h3⟩; refine ⟨?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨rfl, rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 8.2.17: `3x-2y+z = -5`, `x+3y-z = 12`, `x+y+2z = 0` has the unique solution
`(1, 3, -2)`. -/
@[kb "stitzzeager2013" "Exercise 8.2.17, p. 586"]
theorem exer_8_2_17 : ∀ x y z : ℝ,
    !![(3 : ℝ), -2, 1; 1, 3, -1; 1, 1, 2] *ᵥ ![x, y, z] = ![-5, 12, 0] ↔ (x = 1 ∧ y = 3 ∧ z = -2) := by
  intro x y z
  rw [mv3]
  constructor
  · rintro ⟨h1, h2, h3⟩; refine ⟨?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨rfl, rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 8.2.18: `2x-y+z = -1`, `4x+3y+5z = 1`, `5y+3z = 4` is inconsistent. -/
@[kb "stitzzeager2013" "Exercise 8.2.18, p. 586"]
theorem exer_8_2_18 : ¬ ∃ x y z : ℝ,
    !![(2 : ℝ), -1, 1; 4, 3, 5; 0, 5, 3] *ᵥ ![x, y, z] = ![-1, 1, 4] := by
  rintro ⟨x, y, z, h⟩
  rw [mv3] at h
  obtain ⟨h1, h2, h3⟩ := h
  linarith

/-- Stitz-Zeager Exercise 8.2.19: `x-y+z = -4`, `-3x+2y+4z = -5`, `x-5y+2z = -18` has the unique solution
`(1, 3, -2)`. -/
@[kb "stitzzeager2013" "Exercise 8.2.19, p. 586"]
theorem exer_8_2_19 : ∀ x y z : ℝ,
    !![(1 : ℝ), -1, 1; -3, 2, 4; 1, -5, 2] *ᵥ ![x, y, z] = ![-4, -5, -18] ↔ (x = 1 ∧ y = 3 ∧ z = -2) := by
  intro x y z
  rw [mv3]
  constructor
  · rintro ⟨h1, h2, h3⟩; refine ⟨?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨rfl, rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 8.2.20: `2x-4y+z = -7`, `x-2y+2z = -2`, `-x+4y-2z = 3` has the unique solution
`(-3, 1/2, 1)`. -/
@[kb "stitzzeager2013" "Exercise 8.2.20, p. 586"]
theorem exer_8_2_20 : ∀ x y z : ℝ,
    !![(2 : ℝ), -4, 1; 1, -2, 2; -1, 4, -2] *ᵥ ![x, y, z] = ![-7, -2, 3] ↔
      (x = -3 ∧ y = 1 / 2 ∧ z = 1) := by
  intro x y z
  rw [mv3]
  constructor
  · rintro ⟨h1, h2, h3⟩; refine ⟨?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨rfl, rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 8.2.21: `2x-y+z = 1`, `2x+2y-z = 1`, `3x+6y+4z = 9` has the unique solution
`(1/3, 2/3, 1)`. -/
@[kb "stitzzeager2013" "Exercise 8.2.21, p. 587"]
theorem exer_8_2_21 : ∀ x y z : ℝ,
    !![(2 : ℝ), -1, 1; 2, 2, -1; 3, 6, 4] *ᵥ ![x, y, z] = ![1, 1, 9] ↔
      (x = 1 / 3 ∧ y = 2 / 3 ∧ z = 1) := by
  intro x y z
  rw [mv3]
  constructor
  · rintro ⟨h1, h2, h3⟩; refine ⟨?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨rfl, rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 8.2.24: `x-y+z = 8`, `3x+3y-9z = -6`, `7x-2y+5z = 39` has the unique solution
`(4, -3, 1)`. -/
@[kb "stitzzeager2013" "Exercise 8.2.24, p. 587"]
theorem exer_8_2_24 : ∀ x y z : ℝ,
    !![(1 : ℝ), -1, 1; 3, 3, -9; 7, -2, 5] *ᵥ ![x, y, z] = ![8, -6, 39] ↔ (x = 4 ∧ y = -3 ∧ z = 1) := by
  intro x y z
  rw [mv3]
  constructor
  · rintro ⟨h1, h2, h3⟩; refine ⟨?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨rfl, rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 8.2.25: `2x-3y+z = -1`, `4x-4y+4z = -13`, `6x-5y+7z = -25` has the solutions
`(-2t - 35/4, -t - 11/2, t)`. -/
@[kb "stitzzeager2013" "Exercise 8.2.25, p. 587"]
theorem exer_8_2_25 : ∀ x y z : ℝ,
    !![(2 : ℝ), -3, 1; 4, -4, 4; 6, -5, 7] *ᵥ ![x, y, z] = ![-1, -13, -25] ↔
      ∃ t : ℝ, x = -2 * t - 35 / 4 ∧ y = -t - 11 / 2 ∧ z = t := by
  intro x y z
  rw [mv3]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨z, by linarith, by linarith, rfl⟩
  · rintro ⟨t, rfl, rfl, rfl⟩; refine ⟨?_, ?_, ?_⟩ <;> ring

/-- Stitz-Zeager Exercise 8.2.26: `x₁-x₃ = -2`, `2x₂-x₄ = 0`, `x₁-2x₂+x₃ = 0`, `-x₃+x₄ = 1` has the unique
solution `(1, 2, 3, 4)`. -/
@[kb "stitzzeager2013" "Exercise 8.2.26, p. 587"]
theorem exer_8_2_26 : ∀ a b c d : ℝ,
    !![(1 : ℝ), 0, -1, 0; 0, 2, 0, -1; 1, -2, 1, 0; 0, 0, -1, 1] *ᵥ ![a, b, c, d] = ![-2, 0, 0, 1] ↔
      (a = 1 ∧ b = 2 ∧ c = 3 ∧ d = 4) := by
  intro a b c d
  rw [mv4]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨rfl, rfl, rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 8.2.32: the line `y = m x + b` through `(-3, 4)` and `(6, 1)` has `m = -1/3`, `b = 3`. -/
@[kb "stitzzeager2013" "Exercise 8.2.32, p. 587"]
theorem exer_8_2_32 : ∀ m b : ℝ, (-3 * m + b = 4 ∧ 6 * m + b = 1) ↔ (m = -1 / 3 ∧ b = 3) := by
  intro m b
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; norm_num

/-! ## 8.4 Systems of Linear Equations: Matrix Inverses -/

/-- Stitz-Zeager Exercise 8.4.8: the inverse of `H = [[1,0,-3,0],[2,-2,8,7],[-5,0,16,0],[1,0,4,1]]` is
`[[16,0,3,0],[-90,-1/2,-35/2,7/2],[5,0,1,0],[-36,0,-7,1]]`. -/
@[kb "stitzzeager2013" "Exercise 8.4.8, p. 621"]
theorem exer_8_4_8 :
    (!![1, 0, -3, 0; 2, -2, 8, 7; -5, 0, 16, 0; 1, 0, 4, 1] : Matrix (Fin 4) (Fin 4) ℝ)⁻¹ =
      !![16, 0, 3, 0; -90, -1 / 2, -35 / 2, 7 / 2; 5, 0, 1, 0; -36, 0, -7, 1] := by
  refine Matrix.inv_eq_right_inv ?_
  mt

end UndergradKB.Precalculus.Course
