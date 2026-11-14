import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 8 (Stitz-Zeager): exercises with the book's answers, Sections 8.1 and 8.2 -/

namespace UndergradKB.Precalculus.Course

open Matrix

/-! ## 8.1 Systems of Linear Equations: Gaussian Elimination -/

/-- Stitz-Zeager Exercise 8.1.1: the system `x + 2y = 5`, `x = 6` is consistent independent with solution
`(6, -1/2)`. -/
@[kb "stitzzeager2013" "Exercise 8.1.1, p. 574"]
theorem exer_8_1_1 : ∀ x y : ℝ, (x + 2 * y = 5 ∧ x = 6) ↔ (x = 6 ∧ y = -1 / 2) := by
  intro x y
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 8.1.2: the system `2y - 3x = 1`, `y = -3` has the unique solution `(-7/3, -3)`. -/
@[kb "stitzzeager2013" "Exercise 8.1.2, p. 574"]
theorem exer_8_1_2 : ∀ x y : ℝ, (2 * y - 3 * x = 1 ∧ y = -3) ↔ (x = -7 / 3 ∧ y = -3) := by
  intro x y
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 8.1.3: `(x+2y)/4 = -5`, `(3x-y)/2 = 1` has the unique solution `(-16/7, -62/7)`. -/
@[kb "stitzzeager2013" "Exercise 8.1.3, p. 574"]
theorem exer_8_1_3 : ∀ x y : ℝ,
    ((x + 2 * y) / 4 = -5 ∧ (3 * x - y) / 2 = 1) ↔ (x = -16 / 7 ∧ y = -62 / 7) := by
  intro x y
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 8.1.5: `x/2 - y/3 = -1`, `2y - 3x = 6` is consistent dependent: its solutions are
exactly the points `(t, 3t/2 + 3)`. -/
@[kb "stitzzeager2013" "Exercise 8.1.5, p. 574"]
theorem exer_8_1_5 : ∀ x y : ℝ,
    (x / 2 - y / 3 = -1 ∧ 2 * y - 3 * x = 6) ↔ ∃ t : ℝ, x = t ∧ y = 3 / 2 * t + 3 := by
  intro x y
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨x, rfl, by linarith⟩
  · rintro ⟨t, rfl, rfl⟩; constructor <;> ring

/-- Stitz-Zeager Exercise 8.1.9: `-5x + y = 17`, `x + y = 5` has the unique solution `(-2, 7)`. -/
@[kb "stitzzeager2013" "Exercise 8.1.9, p. 574"]
theorem exer_8_1_9 : ∀ x y : ℝ, (-5 * x + y = 17 ∧ x + y = 5) ↔ (x = -2 ∧ y = 7) := by
  intro x y
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 8.1.10: `x+y+z = 3`, `2x-y+z = 0`, `-3x+5y+7z = 7` has the unique solution `(1,2,0)`. -/
@[kb "stitzzeager2013" "Exercise 8.1.10, p. 574"]
theorem exer_8_1_10 : ∀ x y z : ℝ,
    (x + y + z = 3 ∧ 2 * x - y + z = 0 ∧ -3 * x + 5 * y + 7 * z = 7) ↔ (x = 1 ∧ y = 2 ∧ z = 0) := by
  intro x y z
  constructor
  · rintro ⟨h1, h2, h3⟩; refine ⟨?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨rfl, rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 8.1.11: `4x-y+z = 5`, `2y+6z = 30`, `x+z = 5` is consistent dependent with solutions
`(-t+5, -3t+15, t)`. -/
@[kb "stitzzeager2013" "Exercise 8.1.11, p. 574"]
theorem exer_8_1_11 : ∀ x y z : ℝ,
    (4 * x - y + z = 5 ∧ 2 * y + 6 * z = 30 ∧ x + z = 5) ↔
      ∃ t : ℝ, x = -t + 5 ∧ y = -3 * t + 15 ∧ z = t := by
  intro x y z
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨z, by linarith, by linarith, rfl⟩
  · rintro ⟨t, rfl, rfl, rfl⟩; refine ⟨?_, ?_, ?_⟩ <;> ring

/-- Stitz-Zeager Exercise 8.1.12: `4x-y+z = 5`, `2y+6z = 30`, `x+z = 6` is inconsistent. -/
@[kb "stitzzeager2013" "Exercise 8.1.12, p. 574"]
theorem exer_8_1_12 : ¬ ∃ x y z : ℝ, 4 * x - y + z = 5 ∧ 2 * y + 6 * z = 30 ∧ x + z = 6 := by
  rintro ⟨x, y, z, h1, h2, h3⟩
  linarith

/-- Stitz-Zeager Exercise 8.1.13: `x+y+z = -17`, `y-3z = 0` has the solutions `(-4t-17, 3t, t)`. -/
@[kb "stitzzeager2013" "Exercise 8.1.13, p. 574"]
theorem exer_8_1_13 : ∀ x y z : ℝ,
    (x + y + z = -17 ∧ y - 3 * z = 0) ↔ ∃ t : ℝ, x = -4 * t - 17 ∧ y = 3 * t ∧ z = t := by
  intro x y z
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨z, by linarith, by linarith, rfl⟩
  · rintro ⟨t, rfl, rfl, rfl⟩; constructor <;> ring

/-- Stitz-Zeager Exercise 8.1.14: `x-2y+3z = 7`, `-3x+y+2z = -5`, `2x+2y+z = 3` has the unique solution
`(2,-1,1)`. -/
@[kb "stitzzeager2013" "Exercise 8.1.14, p. 574"]
theorem exer_8_1_14 : ∀ x y z : ℝ,
    (x - 2 * y + 3 * z = 7 ∧ -3 * x + y + 2 * z = -5 ∧ 2 * x + 2 * y + z = 3) ↔
      (x = 2 ∧ y = -1 ∧ z = 1) := by
  intro x y z
  constructor
  · rintro ⟨h1, h2, h3⟩; refine ⟨?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨rfl, rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 8.1.16: `2x-y+z = -1`, `4x+3y+5z = 1`, `5y+3z = 4` is inconsistent. -/
@[kb "stitzzeager2013" "Exercise 8.1.16, p. 574"]
theorem exer_8_1_16 : ¬ ∃ x y z : ℝ, 2 * x - y + z = -1 ∧ 4 * x + 3 * y + 5 * z = 1 ∧ 5 * y + 3 * z = 4 := by
  rintro ⟨x, y, z, h1, h2, h3⟩
  linarith

/-- Stitz-Zeager Exercise 8.1.17: `3x-2y+z = -5`, `x+3y-z = 12`, `x+y+2z = 0` has the unique solution
`(1,3,-2)`. -/
@[kb "stitzzeager2013" "Exercise 8.1.17, p. 574"]
theorem exer_8_1_17 : ∀ x y z : ℝ,
    (3 * x - 2 * y + z = -5 ∧ x + 3 * y - z = 12 ∧ x + y + 2 * z = 0) ↔ (x = 1 ∧ y = 3 ∧ z = -2) := by
  intro x y z
  constructor
  · rintro ⟨h1, h2, h3⟩; refine ⟨?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨rfl, rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 8.1.18: `2x-4y+z = -7`, `x-2y+2z = -2`, `-x+4y-2z = 3` has the unique solution
`(-3, 1/2, 1)`. -/
@[kb "stitzzeager2013" "Exercise 8.1.18, p. 574"]
theorem exer_8_1_18 : ∀ x y z : ℝ,
    (2 * x - 4 * y + z = -7 ∧ x - 2 * y + 2 * z = -2 ∧ -x + 4 * y - 2 * z = 3) ↔
      (x = -3 ∧ y = 1 / 2 ∧ z = 1) := by
  intro x y z
  constructor
  · rintro ⟨h1, h2, h3⟩; refine ⟨?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨rfl, rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 8.1.19: `2x-y+z = 1`, `2x+2y-z = 1`, `3x+6y+4z = 9` has the unique solution
`(1/3, 2/3, 1)`. -/
@[kb "stitzzeager2013" "Exercise 8.1.19, p. 574"]
theorem exer_8_1_19 : ∀ x y z : ℝ,
    (2 * x - y + z = 1 ∧ 2 * x + 2 * y - z = 1 ∧ 3 * x + 6 * y + 4 * z = 9) ↔
      (x = 1 / 3 ∧ y = 2 / 3 ∧ z = 1) := by
  intro x y z
  constructor
  · rintro ⟨h1, h2, h3⟩; refine ⟨?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨rfl, rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 8.1.20: `x-3y-4z = 3`, `3x+4y-z = 13`, `2x-19y-19z = 2` is consistent dependent with
solutions `(19t/13 + 51/13, -11t/13 + 4/13, t)`. -/
@[kb "stitzzeager2013" "Exercise 8.1.20, p. 574"]
theorem exer_8_1_20 : ∀ x y z : ℝ,
    (x - 3 * y - 4 * z = 3 ∧ 3 * x + 4 * y - z = 13 ∧ 2 * x - 19 * y - 19 * z = 2) ↔
      ∃ t : ℝ, x = 19 / 13 * t + 51 / 13 ∧ y = -11 / 13 * t + 4 / 13 ∧ z = t := by
  intro x y z
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨z, by linarith, by linarith, rfl⟩
  · rintro ⟨t, rfl, rfl, rfl⟩; refine ⟨?_, ?_, ?_⟩ <;> ring

/-- Stitz-Zeager Exercise 8.1.21: `x+y+z = 4`, `2x-4y-z = -1`, `x-y = 2` is inconsistent. -/
@[kb "stitzzeager2013" "Exercise 8.1.21, p. 575"]
theorem exer_8_1_21 : ¬ ∃ x y z : ℝ, x + y + z = 4 ∧ 2 * x - 4 * y - z = -1 ∧ x - y = 2 := by
  rintro ⟨x, y, z, h1, h2, h3⟩
  linarith

/-- Stitz-Zeager Exercise 8.1.22: `x-y+z = 8`, `3x+3y-9z = -6`, `7x-2y+5z = 39` has the unique solution
`(4,-3,1)`. -/
@[kb "stitzzeager2013" "Exercise 8.1.22, p. 575"]
theorem exer_8_1_22 : ∀ x y z : ℝ,
    (x - y + z = 8 ∧ 3 * x + 3 * y - 9 * z = -6 ∧ 7 * x - 2 * y + 5 * z = 39) ↔
      (x = 4 ∧ y = -3 ∧ z = 1) := by
  intro x y z
  constructor
  · rintro ⟨h1, h2, h3⟩; refine ⟨?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨rfl, rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 8.1.23: `2x-3y+z = -1`, `4x-4y+4z = -13`, `6x-5y+7z = -25` is consistent dependent
with solutions `(-2t - 35/4, -t - 11/2, t)`. -/
@[kb "stitzzeager2013" "Exercise 8.1.23, p. 575"]
theorem exer_8_1_23 : ∀ x y z : ℝ,
    (2 * x - 3 * y + z = -1 ∧ 4 * x - 4 * y + 4 * z = -13 ∧ 6 * x - 5 * y + 7 * z = -25) ↔
      ∃ t : ℝ, x = -2 * t - 35 / 4 ∧ y = -t - 11 / 2 ∧ z = t := by
  intro x y z
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨z, by linarith, by linarith, rfl⟩
  · rintro ⟨t, rfl, rfl, rfl⟩; refine ⟨?_, ?_, ?_⟩ <;> ring

/-- Stitz-Zeager Exercise 8.1.24: the four-variable system `2x₁+x₂-12x₃-x₄ = 16`, `-x₁+x₂+12x₃-4x₄ = -5`,
`3x₁+2x₂-16x₃-3x₄ = 25` has the two-parameter solutions `(8s-t+7, -4s+3t+2, s, t)`. -/
@[kb "stitzzeager2013" "Exercise 8.1.24, p. 575"]
theorem exer_8_1_24 : ∀ x₁ x₂ x₃ x₄ : ℝ,
    (2 * x₁ + x₂ - 12 * x₃ - x₄ = 16 ∧ -x₁ + x₂ + 12 * x₃ - 4 * x₄ = -5 ∧
      3 * x₁ + 2 * x₂ - 16 * x₃ - 3 * x₄ = 25) ↔
      ∃ s t : ℝ, x₁ = 8 * s - t + 7 ∧ x₂ = -4 * s + 3 * t + 2 ∧ x₃ = s ∧ x₄ = t := by
  intro x₁ x₂ x₃ x₄
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨x₃, x₄, by linarith, by linarith, rfl, rfl⟩
  · rintro ⟨s, t, rfl, rfl, rfl, rfl⟩; refine ⟨?_, ?_, ?_⟩ <;> ring

/-- Stitz-Zeager Exercise 8.1.25: `x₁-x₃ = -2`, `2x₂-x₄ = 0`, `x₁-2x₂+x₃ = 0`, `-x₃+x₄ = 1` has the unique
solution `(1,2,3,4)`. -/
@[kb "stitzzeager2013" "Exercise 8.1.25, p. 575"]
theorem exer_8_1_25 : ∀ x₁ x₂ x₃ x₄ : ℝ,
    (x₁ - x₃ = -2 ∧ 2 * x₂ - x₄ = 0 ∧ x₁ - 2 * x₂ + x₃ = 0 ∧ -x₃ + x₄ = 1) ↔
      (x₁ = 1 ∧ x₂ = 2 ∧ x₃ = 3 ∧ x₄ = 4) := by
  intro x₁ x₂ x₃ x₄
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨rfl, rfl, rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 8.1.27: the solutions of Exercise 8.1.11 with `x` as the free variable are
`(t, 3t, -t+5)`, and with `y` as the free variable `(t/3, t, -t/3+5)`. -/
@[kb "stitzzeager2013" "Exercise 8.1.27, p. 575"]
theorem exer_8_1_27 : ∀ x y z : ℝ, (4 * x - y + z = 5 ∧ 2 * y + 6 * z = 30 ∧ x + z = 5) →
    (∃ t : ℝ, x = t ∧ y = 3 * t ∧ z = -t + 5) ∧ (∃ t : ℝ, x = 1 / 3 * t ∧ y = t ∧ z = -1 / 3 * t + 5) := by
  intro x y z ⟨h1, h2, h3⟩
  exact ⟨⟨x, rfl, by linarith, by linarith⟩, ⟨y, by linarith, rfl, by linarith⟩⟩

/-- Stitz-Zeager Exercise 8.1.28: with `b` basic and `d` deluxe diners, `b + d = 27` and
`7.50 b + 9.25 d = 227` hold exactly for `b = 13`, `d = 14`. -/
@[kb "stitzzeager2013" "Exercise 8.1.28, p. 575"]
theorem exer_8_1_28 : ∀ b d : ℝ, (b + d = 27 ∧ 15 / 2 * b + 37 / 4 * d = 227) ↔ (b = 13 ∧ d = 14) := by
  intro b d
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 8.1.29: `a + b = 50` pounds of beans with `3a + 8b = 6 * 50` dollars hold exactly for
`20` pounds of the `$3` coffee and `30` pounds of the `$8` coffee. -/
@[kb "stitzzeager2013" "Exercise 8.1.29, p. 575"]
theorem exer_8_1_29 : ∀ a b : ℝ, (a + b = 50 ∧ 3 * a + 8 * b = 6 * 50) ↔ (a = 20 ∧ b = 30) := by
  intro a b
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 8.1.30: investing `x` at `3%` and `y` at `8%` with `x + y = 10000` and `0.03x + 0.08y = 500`
forces `x = 6000`, `y = 4000`. -/
@[kb "stitzzeager2013" "Exercise 8.1.30, p. 575"]
theorem exer_8_1_30 : ∀ x y : ℝ, (x + y = 10000 ∧ 3 / 100 * x + 8 / 100 * y = 500) ↔ (x = 6000 ∧ y = 4000) := by
  intro x y
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 8.1.31: `s` gallons of `10%` salt solution and `w` gallons of water with `s + w = 75`
and `0.10 s = 0.03 * 75` hold exactly for `s = 22.5`, `w = 52.5`. -/
@[kb "stitzzeager2013" "Exercise 8.1.31, p. 575"]
theorem exer_8_1_31 : ∀ s w : ℝ, (s + w = 75 ∧ 1 / 10 * s = 3 / 100 * 75) ↔ (s = 45 / 2 ∧ w = 105 / 2) := by
  intro s w
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 8.1.32: pounds `x, y, z` of the three teas making `2` pounds with equal parts
peppermint, rose hips and chamomile are `(4/3 - t/2, 2/3 - t/2, t)`; all amounts are nonnegative exactly for
`0 ≤ t ≤ 4/3`. -/
@[kb "stitzzeager2013" "Exercise 8.1.32, p. 575"]
theorem exer_8_1_32 : ∀ x y z : ℝ,
    (x + y + z = 2 ∧ 3 / 10 * x + 2 / 5 * y + 7 / 20 * z = 2 / 3 ∧ 2 / 5 * x + 1 / 5 * y + 3 / 10 * z = 2 / 3
      ∧ 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z) ↔
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ 4 / 3 ∧ x = 4 / 3 - t / 2 ∧ y = 2 / 3 - t / 2 ∧ z = t := by
  intro x y z
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨z, h6, by linarith, by linarith, by linarith, rfl⟩
  · rintro ⟨t, h0, h1, rfl, rfl, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-! ## 8.2 Systems of Linear Equations: Augmented Matrices -/

/-- Stitz-Zeager Exercise 8.2.7: the reduced matrix `[[1,0,-2],[0,1,7]]` gives the solution `(-2, 7)`. -/
@[kb "stitzzeager2013" "Exercise 8.2.7, p. 586"]
theorem exer_8_2_7 : ∀ x y : ℝ, !![(1 : ℝ), 0; 0, 1] *ᵥ ![x, y] = ![-2, 7] ↔ (x = -2 ∧ y = 7) := by
  intro x y
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨rfl, rfl⟩
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Stitz-Zeager Exercise 8.2.8: the reduced matrix `[[1,0,0,-3],[0,1,0,20],[0,0,1,19]]` gives the solution
`(-3, 20, 19)`. -/
@[kb "stitzzeager2013" "Exercise 8.2.8, p. 586"]
theorem exer_8_2_8 : ∀ x y z : ℝ, !![(1 : ℝ), 0, 0; 0, 1, 0; 0, 0, 1] *ᵥ ![x, y, z] = ![-3, 20, 19] ↔
    (x = -3 ∧ y = 20 ∧ z = 19) := by
  intro x y z
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1 h2
    exact ⟨h0, h1, h2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Stitz-Zeager Exercise 8.2.9: the reduced matrix `[[1,0,0,3 | 4],[0,1,0,6 | -6],[0,0,1,0 | 2]]` gives the
solutions `(-3t+4, -6t-6, 2, t)`. -/
@[kb "stitzzeager2013" "Exercise 8.2.9, p. 586"]
theorem exer_8_2_9 : ∀ x y z w : ℝ,
    !![(1 : ℝ), 0, 0, 3; 0, 1, 0, 6; 0, 0, 1, 0] *ᵥ ![x, y, z, w] = ![4, -6, 2] ↔
      ∃ t : ℝ, x = -3 * t + 4 ∧ y = -6 * t - 6 ∧ z = 2 ∧ w = t := by
  intro x y z w
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1 h2
    exact ⟨w, by linarith, by linarith, by linarith, rfl⟩
  · rintro ⟨t, rfl, rfl, rfl, rfl⟩
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

/-- Stitz-Zeager Exercise 8.2.10: the reduced matrix `[[1,0,0,3 | 0],[0,1,2,6 | 0],[0,0,0,0 | 1]]` is
inconsistent. -/
@[kb "stitzzeager2013" "Exercise 8.2.10, p. 586"]
theorem exer_8_2_10 : ∀ x y z w : ℝ,
    !![(1 : ℝ), 0, 0, 3; 0, 1, 2, 6; 0, 0, 0, 0] *ᵥ ![x, y, z, w] ≠ ![0, 0, 1] := by
  intro x y z w h
  have h2 := congrFun h 2
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h2

/-- Stitz-Zeager Exercise 8.2.11: the reduced matrix `[[1,0,-8,1 | 7],[0,1,4,-3 | 2],[0,0,0,0 | 0]]` gives the
solutions `(8s - t + 7, -4s + 3t + 2, s, t)`. -/
@[kb "stitzzeager2013" "Exercise 8.2.11, p. 586"]
theorem exer_8_2_11 : ∀ x y z w : ℝ,
    !![(1 : ℝ), 0, -8, 1; 0, 1, 4, -3; 0, 0, 0, 0] *ᵥ ![x, y, z, w] = ![7, 2, 0] ↔
      ∃ s t : ℝ, x = 8 * s - t + 7 ∧ y = -4 * s + 3 * t + 2 ∧ z = s ∧ w = t := by
  intro x y z w
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1
    exact ⟨z, w, by linarith, by linarith, rfl, rfl⟩
  · rintro ⟨s, t, rfl, rfl, rfl, rfl⟩
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

/-- Stitz-Zeager Exercise 8.2.12: the reduced matrix `[[1,0,9 | -3],[0,1,-4 | 20],[0,0,0 | 0]]` gives the
solutions `(-9t-3, 4t+20, t)`. -/
@[kb "stitzzeager2013" "Exercise 8.2.12, p. 586"]
theorem exer_8_2_12 : ∀ x y z : ℝ,
    !![(1 : ℝ), 0, 9; 0, 1, -4; 0, 0, 0] *ᵥ ![x, y, z] = ![-3, 20, 0] ↔
      ∃ t : ℝ, x = -9 * t - 3 ∧ y = 4 * t + 20 ∧ z = t := by
  intro x y z
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1
    exact ⟨z, by linarith, by linarith, rfl⟩
  · rintro ⟨t, rfl, rfl, rfl⟩
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

/-- Stitz-Zeager Exercise 8.2.14: the coefficient matrix `[[1,1,1],[2,-1,1],[-3,5,7]]` sends `(x,y,z)` to
`(3,0,7)` exactly for `(1,2,0)`. -/
@[kb "stitzzeager2013" "Exercise 8.2.14, p. 586"]
theorem exer_8_2_14 : ∀ x y z : ℝ,
    !![(1 : ℝ), 1, 1; 2, -1, 1; -3, 5, 7] *ᵥ ![x, y, z] = ![3, 0, 7] ↔ (x = 1 ∧ y = 2 ∧ z = 0) := by
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

/-- Stitz-Zeager Exercise 8.2.22: `x-3y-4z = 3`, `3x+4y-z = 13`, `2x-19y-19z = 2` has the solutions
`(19t/13 + 51/13, -11t/13 + 4/13, t)`, given as a matrix equation `A v = b`. -/
@[kb "stitzzeager2013" "Exercise 8.2.22, p. 587"]
theorem exer_8_2_22 : ∀ x y z : ℝ,
    !![(1 : ℝ), -3, -4; 3, 4, -1; 2, -19, -19] *ᵥ ![x, y, z] = ![3, 13, 2] ↔
      ∃ t : ℝ, x = 19 / 13 * t + 51 / 13 ∧ y = -11 / 13 * t + 4 / 13 ∧ z = t := by
  intro x y z
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1
    exact ⟨z, by linarith, by linarith, rfl⟩
  · rintro ⟨t, rfl, rfl, rfl⟩
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

/-- Stitz-Zeager Exercise 8.2.23: `x+y+z = 4`, `2x-4y-z = -1`, `x-y = 2` is inconsistent (as a matrix equation). -/
@[kb "stitzzeager2013" "Exercise 8.2.23, p. 587"]
theorem exer_8_2_23 : ∀ x y z : ℝ,
    !![(1 : ℝ), 1, 1; 2, -4, -1; 1, -1, 0] *ᵥ ![x, y, z] ≠ ![4, -1, 2] := by
  intro x y z h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1 h2
  linarith

/-- Stitz-Zeager Exercise 8.2.27: with `c` kids, `b` basic and `d` deluxe diners, `c + b + d = 22`, `c = 5` and
`4.50 c + 7.50 b + 9.25 d = 162.25` give `b = 10` and `d = 7`. -/
@[kb "stitzzeager2013" "Exercise 8.2.27, p. 587"]
theorem exer_8_2_27 : ∀ c b d : ℝ,
    (c + b + d = 22 ∧ c = 5 ∧ 9 / 2 * c + 15 / 2 * b + 37 / 4 * d = 649 / 4) ↔ (c = 5 ∧ b = 10 ∧ d = 7) := by
  intro c b d
  constructor
  · rintro ⟨h1, h2, h3⟩; refine ⟨h2, ?_, ?_⟩ <;> linarith
  · rintro ⟨rfl, rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 8.2.28: for a `10`-pound mix of almonds `a` (`$7`), cashews `c` (`$5`) and peanuts `p`
(`$2`) costing `$35`, the nonnegative solutions are `a = 1.5t - 7.5`, `c = 17.5 - 2.5t`, `p = t` with
`5 ≤ t ≤ 7`. -/
@[kb "stitzzeager2013" "Exercise 8.2.28, p. 587"]
theorem exer_8_2_28 : ∀ a c p : ℝ,
    (a + c + p = 10 ∧ 7 * a + 5 * c + 2 * p = 35 ∧ 0 ≤ a ∧ 0 ≤ c ∧ 0 ≤ p) ↔
      ∃ t : ℝ, 5 ≤ t ∧ t ≤ 7 ∧ a = 3 / 2 * t - 15 / 2 ∧ c = 35 / 2 - 5 / 2 * t ∧ p = t := by
  intro a c p
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨p, by linarith, by linarith, by linarith, by linarith, rfl⟩
  · rintro ⟨t, h0, h1, rfl, rfl, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- Stitz-Zeager Exercise 8.2.29: the quadratic `a x² + b x + c` through `(-2,1)`, `(1,4)`, `(3,-2)` is
`-4/5 x² + 1/5 x + 23/5`. -/
@[kb "stitzzeager2013" "Exercise 8.2.29, p. 587"]
theorem exer_8_2_29 : ∀ a b c : ℝ,
    (a * (-2) ^ 2 + b * (-2) + c = 1 ∧ a * 1 ^ 2 + b * 1 + c = 4 ∧ a * 3 ^ 2 + b * 3 + c = -2) ↔
      (a = -4 / 5 ∧ b = 1 / 5 ∧ c = 23 / 5) := by
  intro a b c
  constructor
  · rintro ⟨h1, h2, h3⟩; refine ⟨?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨rfl, rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 8.2.30: the quadratic `T(t) = a t² + b t + c` through `(0,60)`, `(3,50)`, `(9,70)` is
`20/27 t² - 50/9 t + 60`; its least value is `595/12 ≈ 49.58` degrees, attained at `t = 15/4` hours after 9 PM
(12:45 AM). -/
@[kb "stitzzeager2013" "Exercise 8.2.30, p. 587"]
theorem exer_8_2_30 : ∀ a b c : ℝ,
    (c = 60 ∧ a * 3 ^ 2 + b * 3 + c = 50 ∧ a * 9 ^ 2 + b * 9 + c = 70) ↔
      (a = 20 / 27 ∧ b = -50 / 9 ∧ c = 60) := by
  intro a b c
  constructor
  · rintro ⟨h1, h2, h3⟩; refine ⟨?_, ?_, h1⟩ <;> linarith
  · rintro ⟨rfl, rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 8.2.30 (minimum): `T(t) = 20/27 t² - 50/9 t + 60` is at least `595/12` for all `t`, with
equality at `t = 15/4`. -/
@[kb "stitzzeager2013" "Exercise 8.2.30 (minimum), p. 587"]
theorem exer_8_2_30_min : (∀ t : ℝ, 595 / 12 ≤ 20 / 27 * t ^ 2 - 50 / 9 * t + 60) ∧
    20 / 27 * (15 / 4 : ℝ) ^ 2 - 50 / 9 * (15 / 4) + 60 = 595 / 12 := by
  refine ⟨fun t => ?_, by norm_num⟩
  nlinarith [sq_nonneg (t - 15 / 4)]

/-- Stitz-Zeager Exercise 8.2.31: for whole numbers, the museum system `15x₁+8x₂ = 38`, `15x₃+8x₄ = 39`,
`15x₁+8x₂+15x₃+8x₄ = 77`, `15x₁+15x₃ = 45` has exactly one solution, `(2,1,1,3)`. -/
@[kb "stitzzeager2013" "Exercise 8.2.31, p. 587"]
theorem exer_8_2_31 : ∀ x₁ x₂ x₃ x₄ : ℕ,
    (15 * x₁ + 8 * x₂ = 38 ∧ 15 * x₃ + 8 * x₄ = 39 ∧ 15 * x₁ + 8 * x₂ + 15 * x₃ + 8 * x₄ = 77 ∧
      15 * x₁ + 15 * x₃ = 45) ↔ (x₁ = 2 ∧ x₂ = 1 ∧ x₃ = 1 ∧ x₄ = 3) := by
  intro x₁ x₂ x₃ x₄
  omega

end UndergradKB.Precalculus.Course
