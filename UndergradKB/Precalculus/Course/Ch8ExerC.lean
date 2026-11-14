import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 8 (Stitz-Zeager): exercises with the book's answers, Sections 8.6 and 8.7 -/

namespace UndergradKB.Precalculus.Course

/-! ## 8.6 Partial Fraction Decomposition -/

/-- Stitz-Zeager Exercise 8.6.7: `2x / (x² - 1) = 1/(x+1) + 1/(x-1)`. -/
@[kb "stitzzeager2013" "Exercise 8.6.7, p. 647"]
theorem exer_8_6_7 : ∀ x : ℝ, x + 1 ≠ 0 → x - 1 ≠ 0 →
    2 * x / (x ^ 2 - 1) = 1 / (x + 1) + 1 / (x - 1) := by
  intro x h1 h2
  have e : x ^ 2 - 1 = (x + 1) * (x - 1) := by ring
  have h3 : x ^ 2 - 1 ≠ 0 := by
    rw [e]; exact mul_ne_zero h1 h2
  rw [e]
  field_simp
  ring

/-- Stitz-Zeager Exercise 8.6.8: `(-7x+43)/(3x²+19x-14) = 5/(3x-2) - 4/(x+7)`. -/
@[kb "stitzzeager2013" "Exercise 8.6.8, p. 647"]
theorem exer_8_6_8 : ∀ x : ℝ, 3 * x - 2 ≠ 0 → x + 7 ≠ 0 →
    (-7 * x + 43) / (3 * x ^ 2 + 19 * x - 14) = 5 / (3 * x - 2) - 4 / (x + 7) := by
  intro x h1 h2
  have e : 3 * x ^ 2 + 19 * x - 14 = (3 * x - 2) * (x + 7) := by ring
  rw [e, div_sub_div _ _ h1 h2, div_eq_div_iff (mul_ne_zero h1 h2) (mul_ne_zero h1 h2)]
  ring

/-- Stitz-Zeager Exercise 8.6.9: `(11x²-5x-10)/(5x³-5x²) = 3/x + 2/x² - 4/(5(x-1))`. -/
@[kb "stitzzeager2013" "Exercise 8.6.9, p. 647"]
theorem exer_8_6_9 : ∀ x : ℝ, x ≠ 0 → x - 1 ≠ 0 →
    (11 * x ^ 2 - 5 * x - 10) / (5 * x ^ 3 - 5 * x ^ 2) = 3 / x + 2 / x ^ 2 - 4 / (5 * (x - 1)) := by
  intro x h1 h2
  have e : 5 * x ^ 3 - 5 * x ^ 2 = 5 * x ^ 2 * (x - 1) := by ring
  have h3 : 5 * x ^ 3 - 5 * x ^ 2 ≠ 0 := by
    rw [e]; exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 h1)) h2
  rw [e]
  field_simp
  ring

/-- Stitz-Zeager Exercise 8.6.10: `(-2x²+20x-68)/(x³+4x²+4x+16) = -9/(x+4) + (7x-8)/(x²+4)`. -/
@[kb "stitzzeager2013" "Exercise 8.6.10, p. 647"]
theorem exer_8_6_10 : ∀ x : ℝ, x + 4 ≠ 0 →
    (-2 * x ^ 2 + 20 * x - 68) / (x ^ 3 + 4 * x ^ 2 + 4 * x + 16) = -9 / (x + 4) + (7 * x - 8) / (x ^ 2 + 4) := by
  intro x h1
  have h2 : x ^ 2 + 4 ≠ 0 := by positivity
  have e : x ^ 3 + 4 * x ^ 2 + 4 * x + 16 = (x + 4) * (x ^ 2 + 4) := by ring
  have h3 : x ^ 3 + 4 * x ^ 2 + 4 * x + 16 ≠ 0 := by
    rw [e]; exact mul_ne_zero h1 h2
  rw [e]
  field_simp
  ring

/-- Stitz-Zeager Exercise 8.6.11: `(-x²+15)/(4x⁴+40x²+36) = 1/(2(x²+1)) - 3/(4(x²+9))`. -/
@[kb "stitzzeager2013" "Exercise 8.6.11, p. 647"]
theorem exer_8_6_11 : ∀ x : ℝ,
    (-x ^ 2 + 15) / (4 * x ^ 4 + 40 * x ^ 2 + 36) = 1 / (2 * (x ^ 2 + 1)) - 3 / (4 * (x ^ 2 + 9)) := by
  intro x
  have h1 : x ^ 2 + 1 ≠ 0 := by positivity
  have h2 : x ^ 2 + 9 ≠ 0 := by positivity
  have h3 : 4 * x ^ 4 + 40 * x ^ 2 + 36 ≠ 0 := by positivity
  field_simp
  ring

/-- Stitz-Zeager Exercise 8.6.12: `(-21x²+x-16)/(3x³+4x²-3x+2) = -6/(x+2) - (3x+5)/(3x²-2x+1)`. -/
@[kb "stitzzeager2013" "Exercise 8.6.12, p. 647"]
theorem exer_8_6_12 : ∀ x : ℝ, x + 2 ≠ 0 →
    (-21 * x ^ 2 + x - 16) / (3 * x ^ 3 + 4 * x ^ 2 - 3 * x + 2) =
      -6 / (x + 2) - (3 * x + 5) / (3 * x ^ 2 - 2 * x + 1) := by
  intro x h1
  have h2 : 3 * x ^ 2 - 2 * x + 1 ≠ 0 := by nlinarith [sq_nonneg (3 * x - 1)]
  have e : 3 * x ^ 3 + 4 * x ^ 2 - 3 * x + 2 = (x + 2) * (3 * x ^ 2 - 2 * x + 1) := by ring
  rw [e, div_sub_div _ _ h1 h2, div_eq_div_iff (mul_ne_zero h1 h2) (mul_ne_zero h1 h2)]
  ring

/-- Stitz-Zeager Exercise 8.6.13: `(5x⁴-34x³+70x²-33x-19)/(x-3)² = 5x² - 4x + 1 + 9/(x-3) - 1/(x-3)²`. -/
@[kb "stitzzeager2013" "Exercise 8.6.13, p. 647"]
theorem exer_8_6_13 : ∀ x : ℝ, x - 3 ≠ 0 →
    (5 * x ^ 4 - 34 * x ^ 3 + 70 * x ^ 2 - 33 * x - 19) / (x - 3) ^ 2 =
      5 * x ^ 2 - 4 * x + 1 + 9 / (x - 3) - 1 / (x - 3) ^ 2 := by
  intro x h1
  field_simp
  ring

/-- Stitz-Zeager Exercise 8.6.14: `(x⁶+5x⁵+16x⁴+80x³-2x²+6x-43)/(x³+5x²+16x+80) = x³ + (x+1)/(x²+16) - 3/(x+5)`. -/
@[kb "stitzzeager2013" "Exercise 8.6.14, p. 647"]
theorem exer_8_6_14 : ∀ x : ℝ, x + 5 ≠ 0 →
    (x ^ 6 + 5 * x ^ 5 + 16 * x ^ 4 + 80 * x ^ 3 - 2 * x ^ 2 + 6 * x - 43) / (x ^ 3 + 5 * x ^ 2 + 16 * x + 80) =
      x ^ 3 + (x + 1) / (x ^ 2 + 16) - 3 / (x + 5) := by
  intro x h1
  have h2 : x ^ 2 + 16 ≠ 0 := by positivity
  have e : x ^ 3 + 5 * x ^ 2 + 16 * x + 80 = (x + 5) * (x ^ 2 + 16) := by ring
  have h3 : x ^ 3 + 5 * x ^ 2 + 16 * x + 80 ≠ 0 := by
    rw [e]; exact mul_ne_zero h1 h2
  rw [e]
  field_simp
  ring

/-- Stitz-Zeager Exercise 8.6.15: `(-7x²-76x-208)/(x³+18x²+108x+216) = -7/(x+6) + 8/(x+6)² - 4/(x+6)³`. -/
@[kb "stitzzeager2013" "Exercise 8.6.15, p. 647"]
theorem exer_8_6_15 : ∀ x : ℝ, x + 6 ≠ 0 →
    (-7 * x ^ 2 - 76 * x - 208) / (x ^ 3 + 18 * x ^ 2 + 108 * x + 216) =
      -7 / (x + 6) + 8 / (x + 6) ^ 2 - 4 / (x + 6) ^ 3 := by
  intro x h1
  have e : x ^ 3 + 18 * x ^ 2 + 108 * x + 216 = (x + 6) ^ 3 := by ring
  have h3 : x ^ 3 + 18 * x ^ 2 + 108 * x + 216 ≠ 0 := by
    rw [e]; exact pow_ne_zero 3 h1
  rw [e]
  field_simp
  ring

/-- Stitz-Zeager Exercise 8.6.16: `(-10x⁴+x³-19x²+x-10)/(x⁵+2x³+x) = -10/x + 1/(x²+1) + x/(x²+1)²`. -/
@[kb "stitzzeager2013" "Exercise 8.6.16, p. 647"]
theorem exer_8_6_16 : ∀ x : ℝ, x ≠ 0 →
    (-10 * x ^ 4 + x ^ 3 - 19 * x ^ 2 + x - 10) / (x ^ 5 + 2 * x ^ 3 + x) =
      -10 / x + 1 / (x ^ 2 + 1) + x / (x ^ 2 + 1) ^ 2 := by
  intro x h1
  have h2 : x ^ 2 + 1 ≠ 0 := by positivity
  have e : x ^ 5 + 2 * x ^ 3 + x = x * (x ^ 2 + 1) ^ 2 := by ring
  have h3 : x ^ 5 + 2 * x ^ 3 + x ≠ 0 := by
    rw [e]; exact mul_ne_zero h1 (pow_ne_zero 2 h2)
  rw [e]
  field_simp
  ring

/-- Stitz-Zeager Exercise 8.6.17: `(4x³-9x²+12x+12)/(x⁴-4x³+8x²-16x+16) = 1/(x-2) + 4/(x-2)² + (3x+1)/(x²+4)`. -/
@[kb "stitzzeager2013" "Exercise 8.6.17, p. 647"]
theorem exer_8_6_17 : ∀ x : ℝ, x - 2 ≠ 0 →
    (4 * x ^ 3 - 9 * x ^ 2 + 12 * x + 12) / (x ^ 4 - 4 * x ^ 3 + 8 * x ^ 2 - 16 * x + 16) =
      1 / (x - 2) + 4 / (x - 2) ^ 2 + (3 * x + 1) / (x ^ 2 + 4) := by
  intro x h1
  have h2 : x ^ 2 + 4 ≠ 0 := by positivity
  have e : x ^ 4 - 4 * x ^ 3 + 8 * x ^ 2 - 16 * x + 16 = (x - 2) ^ 2 * (x ^ 2 + 4) := by ring
  have h3 : x ^ 4 - 4 * x ^ 3 + 8 * x ^ 2 - 16 * x + 16 ≠ 0 := by
    rw [e]; exact mul_ne_zero (pow_ne_zero 2 h1) h2
  rw [e]
  field_simp
  ring

/-- Stitz-Zeager Exercise 8.6.18: `(2x²+3x+14)/((x²+2x+9)(x²+x+5)) = 1/(x²+2x+9) + 1/(x²+x+5)`. -/
@[kb "stitzzeager2013" "Exercise 8.6.18, p. 647"]
theorem exer_8_6_18 : ∀ x : ℝ,
    (2 * x ^ 2 + 3 * x + 14) / ((x ^ 2 + 2 * x + 9) * (x ^ 2 + x + 5)) =
      1 / (x ^ 2 + 2 * x + 9) + 1 / (x ^ 2 + x + 5) := by
  intro x
  have h1 : x ^ 2 + 2 * x + 9 ≠ 0 := by nlinarith [sq_nonneg (x + 1)]
  have h2 : x ^ 2 + x + 5 ≠ 0 := by nlinarith [sq_nonneg (x + 1 / 2)]
  rw [div_add_div _ _ h1 h2, div_eq_div_iff (mul_ne_zero h1 h2) (mul_ne_zero h1 h2)]
  ring

/-! ## 8.7 Systems of Non-Linear Equations and Inequalities -/

/-- Stitz-Zeager Exercise 8.7.1: `x² - y = 4`, `x² + y² = 4` has exactly the solutions `(±2, 0)` and `(±√3, -1)`. -/
@[kb "stitzzeager2013" "Exercise 8.7.1, p. 658"]
theorem exer_8_7_1 : ∀ x y : ℝ, (x ^ 2 - y = 4 ∧ x ^ 2 + y ^ 2 = 4) ↔
    (x = 2 ∧ y = 0) ∨ (x = -2 ∧ y = 0) ∨ (x = √3 ∧ y = -1) ∨ (x = -√3 ∧ y = -1) := by
  intro x y
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  constructor
  · rintro ⟨h1, h2⟩
    have hy : y * (y + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hy with hy | hy
    · have hx : x ^ 2 = 2 ^ 2 := by nlinarith
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hx with hx | hx
      · exact Or.inl ⟨hx, hy⟩
      · exact Or.inr (Or.inl ⟨hx, hy⟩)
    · have hy' : y = -1 := by linarith
      have hx : x ^ 2 = √3 ^ 2 := by nlinarith
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hx with hx | hx
      · exact Or.inr (Or.inr (Or.inl ⟨hx, hy'⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hx, hy'⟩))
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> constructor <;> nlinarith

/-- Stitz-Zeager Exercise 8.7.2: `x² + y² = 4`, `x² - y = 5` has no real solution. -/
@[kb "stitzzeager2013" "Exercise 8.7.2, p. 658"]
theorem exer_8_7_2 : ¬ ∃ x y : ℝ, x ^ 2 + y ^ 2 = 4 ∧ x ^ 2 - y = 5 := by
  rintro ⟨x, y, h1, h2⟩
  nlinarith [sq_nonneg (y + 1 / 2)]

/-- Stitz-Zeager Exercise 8.7.3: `x² + y² = 16`, `16x² + 4y² = 64` has exactly the solutions `(0, ±4)`. -/
@[kb "stitzzeager2013" "Exercise 8.7.3, p. 658"]
theorem exer_8_7_3 : ∀ x y : ℝ, (x ^ 2 + y ^ 2 = 16 ∧ 16 * x ^ 2 + 4 * y ^ 2 = 64) ↔
    x = 0 ∧ (y = 4 ∨ y = -4) := by
  intro x y
  constructor
  · rintro ⟨h1, h2⟩
    have hx : x = 0 := by nlinarith [sq_nonneg x]
    subst hx
    refine ⟨rfl, ?_⟩
    have : y ^ 2 = 4 ^ 2 := by nlinarith
    exact sq_eq_sq_iff_eq_or_eq_neg.mp this
  · rintro ⟨rfl, rfl | rfl⟩ <;> constructor <;> norm_num

/-- Stitz-Zeager Exercise 8.7.4: `x² + y² = 16`, `9x² - 16y² = 144` has exactly the solutions `(±4, 0)`. -/
@[kb "stitzzeager2013" "Exercise 8.7.4, p. 658"]
theorem exer_8_7_4 : ∀ x y : ℝ, (x ^ 2 + y ^ 2 = 16 ∧ 9 * x ^ 2 - 16 * y ^ 2 = 144) ↔
    (x = 4 ∨ x = -4) ∧ y = 0 := by
  intro x y
  constructor
  · rintro ⟨h1, h2⟩
    have hy : y = 0 := by nlinarith [sq_nonneg y]
    subst hy
    refine ⟨?_, rfl⟩
    have : x ^ 2 = 4 ^ 2 := by nlinarith
    exact sq_eq_sq_iff_eq_or_eq_neg.mp this
  · rintro ⟨rfl | rfl, rfl⟩ <;> constructor <;> norm_num

/-- Stitz-Zeager Exercise 8.7.5: `x² + y² = 16`, `y²/9 - x²/16 = 1` has exactly the four solutions
`(±4√7/5, ±12√2/5)`. -/
@[kb "stitzzeager2013" "Exercise 8.7.5, p. 658"]
theorem exer_8_7_5 : ∀ x y : ℝ, (x ^ 2 + y ^ 2 = 16 ∧ y ^ 2 / 9 - x ^ 2 / 16 = 1) ↔
    (x = 4 * √7 / 5 ∨ x = -(4 * √7 / 5)) ∧ (y = 12 * √2 / 5 ∨ y = -(12 * √2 / 5)) := by
  intro x y
  have h7 : √7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  constructor
  · rintro ⟨e1, e2⟩
    have hx : x ^ 2 = (4 * √7 / 5) ^ 2 := by nlinarith
    have hy : y ^ 2 = (12 * √2 / 5) ^ 2 := by nlinarith
    exact ⟨sq_eq_sq_iff_eq_or_eq_neg.mp hx, sq_eq_sq_iff_eq_or_eq_neg.mp hy⟩
  · rintro ⟨hx | hx, hy | hy⟩ <;> subst hx <;> subst hy <;> constructor <;> nlinarith

/-- Stitz-Zeager Exercise 8.7.6: `x² + y² = 16`, `x - y = 2` has exactly the solutions `(1+√7, -1+√7)` and
`(1-√7, -1-√7)`. -/
@[kb "stitzzeager2013" "Exercise 8.7.6, p. 658"]
theorem exer_8_7_6 : ∀ x y : ℝ, (x ^ 2 + y ^ 2 = 16 ∧ x - y = 2) ↔
    (x = 1 + √7 ∧ y = -1 + √7) ∨ (x = 1 - √7 ∧ y = -1 - √7) := by
  intro x y
  have h7 : √7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  constructor
  · rintro ⟨e1, e2⟩
    have hx : x = y + 2 := by linarith
    subst hx
    have hy : (y + 1) ^ 2 = √7 ^ 2 := by nlinarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hy with hy | hy
    · exact Or.inl ⟨by linarith, by linarith⟩
    · exact Or.inr ⟨by linarith, by linarith⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> constructor <;> nlinarith

/-- Stitz-Zeager Exercise 8.7.7: `x² - y² = 1`, `x² + 4y² = 4` has exactly the four solutions
`(±2√10/5, ±√15/5)`. -/
@[kb "stitzzeager2013" "Exercise 8.7.7, p. 658"]
theorem exer_8_7_7 : ∀ x y : ℝ, (x ^ 2 - y ^ 2 = 1 ∧ x ^ 2 + 4 * y ^ 2 = 4) ↔
    (x = 2 * √10 / 5 ∨ x = -(2 * √10 / 5)) ∧ (y = √15 / 5 ∨ y = -(√15 / 5)) := by
  intro x y
  have h10 : √10 ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  have h15 : √15 ^ 2 = 15 := Real.sq_sqrt (by norm_num)
  constructor
  · rintro ⟨e1, e2⟩
    have hx : x ^ 2 = (2 * √10 / 5) ^ 2 := by nlinarith
    have hy : y ^ 2 = (√15 / 5) ^ 2 := by nlinarith
    exact ⟨sq_eq_sq_iff_eq_or_eq_neg.mp hx, sq_eq_sq_iff_eq_or_eq_neg.mp hy⟩
  · rintro ⟨hx | hx, hy | hy⟩ <;> subst hx <;> subst hy <;> constructor <;> nlinarith

/-- Stitz-Zeager Exercise 8.7.8: for `x ≥ -1`, `√(x+1) - y = 0`, `x² + 4y² = 4` has the single solution `(0, 1)`. -/
@[kb "stitzzeager2013" "Exercise 8.7.8, p. 658"]
theorem exer_8_7_8 : ∀ x y : ℝ, -1 ≤ x → ((√(x + 1) - y = 0 ∧ x ^ 2 + 4 * y ^ 2 = 4) ↔ (x = 0 ∧ y = 1)) := by
  intro x y hx
  constructor
  · rintro ⟨h1, h2⟩
    have hy : y = √(x + 1) := by linarith
    have hs : √(x + 1) ^ 2 = x + 1 := Real.sq_sqrt (by linarith)
    have hy2 : y ^ 2 = x + 1 := by rw [hy]; exact hs
    have hy0 : 0 ≤ y := by rw [hy]; exact Real.sqrt_nonneg _
    have hx0 : x * (x + 4) = 0 := by nlinarith
    rcases mul_eq_zero.mp hx0 with h | h
    · subst h
      refine ⟨rfl, ?_⟩
      nlinarith
    · exfalso; linarith
  · rintro ⟨rfl, rfl⟩
    constructor <;> norm_num

/-- Stitz-Zeager Exercise 8.7.9: `x + 2y² = 2`, `x² + 4y² = 4` has exactly the solutions `(0, ±1)` and `(2, 0)`. -/
@[kb "stitzzeager2013" "Exercise 8.7.9, p. 658"]
theorem exer_8_7_9 : ∀ x y : ℝ, (x + 2 * y ^ 2 = 2 ∧ x ^ 2 + 4 * y ^ 2 = 4) ↔
    (x = 0 ∧ (y = 1 ∨ y = -1)) ∨ (x = 2 ∧ y = 0) := by
  intro x y
  constructor
  · rintro ⟨h1, h2⟩
    have hx : x = 2 - 2 * y ^ 2 := by linarith
    subst hx
    have : y ^ 2 * (y ^ 2 - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · have : y = 0 := by simpa using h
      subst this
      right; norm_num
    · left
      have : y ^ 2 = 1 ^ 2 := by linarith
      refine ⟨by nlinarith, ?_⟩
      exact sq_eq_sq_iff_eq_or_eq_neg.mp this
  · rintro (⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩) <;> constructor <;> norm_num

/-- Stitz-Zeager Exercise 8.7.10: `(x-2)² + y² = 1`, `x² + 4y² = 4` has exactly the solutions `(4/3, ±√5/3)`. -/
@[kb "stitzzeager2013" "Exercise 8.7.10, p. 658"]
theorem exer_8_7_10 : ∀ x y : ℝ, ((x - 2) ^ 2 + y ^ 2 = 1 ∧ x ^ 2 + 4 * y ^ 2 = 4) ↔
    x = 4 / 3 ∧ (y = √5 / 3 ∨ y = -(√5 / 3)) := by
  intro x y
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : (3 * x - 4) * (x - 4) = 0 := by nlinarith
    rcases mul_eq_zero.mp h3 with h | h
    · have hx : x = 4 / 3 := by linarith
      subst hx
      refine ⟨rfl, ?_⟩
      have : y ^ 2 = (√5 / 3) ^ 2 := by nlinarith
      exact sq_eq_sq_iff_eq_or_eq_neg.mp this
    · exfalso
      have hx : x = 4 := by linarith
      subst hx
      nlinarith [sq_nonneg y]
  · rintro ⟨rfl, hy | hy⟩ <;> subst hy <;> constructor <;> nlinarith

/-- Stitz-Zeager Exercise 8.7.11: `x² + y² = 25`, `y - x = 1` has exactly the solutions `(3,4)` and `(-4,-3)`. -/
@[kb "stitzzeager2013" "Exercise 8.7.11, p. 658"]
theorem exer_8_7_11 : ∀ x y : ℝ, (x ^ 2 + y ^ 2 = 25 ∧ y - x = 1) ↔
    (x = 3 ∧ y = 4) ∨ (x = -4 ∧ y = -3) := by
  intro x y
  constructor
  · rintro ⟨h1, h2⟩
    have hy : y = x + 1 := by linarith
    subst hy
    have : (x - 3) * (x + 4) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · left; constructor <;> linarith
    · right; constructor <;> linarith
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> constructor <;> norm_num

/-- Stitz-Zeager Exercise 8.7.12: `x² + y² = 25`, `x² + (y-3)² = 10` has exactly the solutions `(±3, 4)`. -/
@[kb "stitzzeager2013" "Exercise 8.7.12, p. 658"]
theorem exer_8_7_12 : ∀ x y : ℝ, (x ^ 2 + y ^ 2 = 25 ∧ x ^ 2 + (y - 3) ^ 2 = 10) ↔
    (x = 3 ∨ x = -3) ∧ y = 4 := by
  intro x y
  constructor
  · rintro ⟨h1, h2⟩
    have hy : y = 4 := by nlinarith
    subst hy
    refine ⟨?_, rfl⟩
    have : x ^ 2 = 3 ^ 2 := by nlinarith
    exact sq_eq_sq_iff_eq_or_eq_neg.mp this
  · rintro ⟨rfl | rfl, rfl⟩ <;> constructor <;> norm_num

/-- Stitz-Zeager Exercise 8.7.13: `y = x³ + 8`, `y = 10x - x²` has exactly the solutions `(-4,-56)`, `(1,9)`,
`(2,16)`. -/
@[kb "stitzzeager2013" "Exercise 8.7.13, p. 658"]
theorem exer_8_7_13 : ∀ x y : ℝ, (y = x ^ 3 + 8 ∧ y = 10 * x - x ^ 2) ↔
    (x = -4 ∧ y = -56) ∨ (x = 1 ∧ y = 9) ∨ (x = 2 ∧ y = 16) := by
  intro x y
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : (x + 4) * ((x - 1) * (x - 2)) = 0 := by nlinarith
    rcases mul_eq_zero.mp h3 with h | h
    · left; constructor <;> nlinarith
    · rcases mul_eq_zero.mp h with h | h
      · right; left; constructor <;> nlinarith
      · right; right; constructor <;> nlinarith
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> constructor <;> norm_num

/-- Stitz-Zeager Exercise 8.7.14: `x² - xy = 8`, `y² - xy = 8` has exactly the solutions `(-2, 2)` and `(2, -2)`. -/
@[kb "stitzzeager2013" "Exercise 8.7.14, p. 658"]
theorem exer_8_7_14 : ∀ x y : ℝ, (x ^ 2 - x * y = 8 ∧ y ^ 2 - x * y = 8) ↔
    (x = -2 ∧ y = 2) ∨ (x = 2 ∧ y = -2) := by
  intro x y
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : (x - y) * (x + y) = 0 := by nlinarith
    rcases mul_eq_zero.mp h3 with h | h
    · exfalso
      have : x = y := by linarith
      subst this
      nlinarith
    · have hy : y = -x := by linarith
      subst hy
      have : x ^ 2 = 2 ^ 2 := by nlinarith
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp this with h | h
      · right; constructor <;> linarith
      · left; constructor <;> linarith
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> constructor <;> norm_num

/-- Stitz-Zeager Exercise 8.7.16: a culture `P e^{kt}` with `10000` bacteria at `t = 10` and `14000` at `t = 15`
has `P = 250000/49` initially and `e^{5k} = 7/5`. -/
@[kb "stitzzeager2013" "Exercise 8.7.16, p. 658"]
theorem exer_8_7_16 : ∀ P k : ℝ, P * Real.exp (10 * k) = 10000 → P * Real.exp (15 * k) = 14000 →
    P = 250000 / 49 ∧ Real.exp (5 * k) = 7 / 5 := by
  intro P k h1 h2
  have e15 : Real.exp (15 * k) = Real.exp (5 * k) * Real.exp (10 * k) := by
    rw [← Real.exp_add]; ring_nf
  have hpos : 0 < P * Real.exp (10 * k) := by rw [h1]; norm_num
  have hE : 0 < Real.exp (10 * k) := Real.exp_pos _
  have hq : Real.exp (5 * k) = 7 / 5 := by
    have : (Real.exp (5 * k) - 7 / 5) * (P * Real.exp (10 * k)) = 0 := by
      rw [h1]; rw [e15] at h2; nlinarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · rw [h1] at h; norm_num at h
  refine ⟨?_, hq⟩
  have e10 : Real.exp (10 * k) = Real.exp (5 * k) * Real.exp (5 * k) := by
    rw [← Real.exp_add]; ring_nf
  rw [e10, hq] at h1
  linarith

/-- Stitz-Zeager Exercise 8.7.16 (time): with `P = 250000/49` and `k = ln(7/5)/5`, the culture reaches `50000`
bacteria exactly at `t = 5 ln(49/5) / ln(7/5)` minutes. -/
@[kb "stitzzeager2013" "Exercise 8.7.16 (time), p. 658"]
theorem exer_8_7_16_time : ∀ t : ℝ,
    250000 / 49 * Real.exp (Real.log (7 / 5) / 5 * t) = 50000 ↔ t = 5 * Real.log (49 / 5) / Real.log (7 / 5) := by
  intro t
  have hk : 0 < Real.log (7 / 5) := Real.log_pos (by norm_num)
  have key : 250000 / 49 * Real.exp (Real.log (7 / 5) / 5 * t) = 50000 ↔
      Real.log (7 / 5) / 5 * t = Real.log (49 / 5) := by
    constructor
    · intro h
      have : Real.exp (Real.log (7 / 5) / 5 * t) = 49 / 5 := by linarith
      rw [← this, Real.log_exp]
    · intro h
      rw [h, Real.exp_log (by norm_num)]; norm_num
  rw [key]
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    rw [h]; field_simp

/-- Stitz-Zeager Exercise 8.7.17: for `y ≥ 0`, `4x³ + 3√y = 1`, `3x³ + 2√y = -1` holds exactly when `x³ = -5`
(`x = -∛5`) and `y = 49`. -/
@[kb "stitzzeager2013" "Exercise 8.7.17, p. 659"]
theorem exer_8_7_17 : ∀ x y : ℝ, 0 ≤ y →
    ((4 * x ^ 3 + 3 * √y = 1 ∧ 3 * x ^ 3 + 2 * √y = -1) ↔ (x ^ 3 = -5 ∧ y = 49)) := by
  intro x y hy
  have h49 : √(49 : ℝ) = 7 := by
    rw [show (49 : ℝ) = 7 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  constructor
  · rintro ⟨h1, h2⟩
    have hs : √y = 7 := by linarith
    refine ⟨by linarith, ?_⟩
    have := Real.sq_sqrt hy
    rw [hs] at this; linarith
  · rintro ⟨h1, rfl⟩
    rw [h49]; constructor <;> linarith

/-- Stitz-Zeager Exercise 8.7.18: `4eˣ + 3e⁻ʸ = 1`, `3eˣ + 2e⁻ʸ = -1` has no real solution. -/
@[kb "stitzzeager2013" "Exercise 8.7.18, p. 659"]
theorem exer_8_7_18 : ¬ ∃ x y : ℝ, 4 * Real.exp x + 3 * Real.exp (-y) = 1 ∧ 3 * Real.exp x + 2 * Real.exp (-y) = -1 := by
  rintro ⟨x, y, h1, h2⟩
  linarith [Real.exp_pos x, Real.exp_pos (-y)]

/-- Stitz-Zeager Exercise 8.7.19: for `x > 0`, `4 ln x + 3y² = 1`, `3 ln x + 2y² = -1` holds exactly for
`x = e⁻⁵` and `y = ±√7`. -/
@[kb "stitzzeager2013" "Exercise 8.7.19, p. 659"]
theorem exer_8_7_19 : ∀ x y : ℝ, 0 < x →
    ((4 * Real.log x + 3 * y ^ 2 = 1 ∧ 3 * Real.log x + 2 * y ^ 2 = -1) ↔
      (x = Real.exp (-5) ∧ (y = √7 ∨ y = -√7))) := by
  intro x y hx
  have h7 : √7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  constructor
  · rintro ⟨h1, h2⟩
    have hl : Real.log x = -5 := by linarith
    refine ⟨?_, ?_⟩
    · rw [← hl, Real.exp_log hx]
    · have : y ^ 2 = √7 ^ 2 := by linarith
      exact sq_eq_sq_iff_eq_or_eq_neg.mp this
  · rintro ⟨rfl, hy | hy⟩ <;> rw [Real.log_exp] <;> subst hy <;> constructor <;> nlinarith

/-- Stitz-Zeager Exercise 8.7.20: for `y ≥ 0`, `z > 0`: `x² + √y + log₂ z = 6`, `3x² - 2√y + 2 log₂ z = 5`,
`-5x² + 3√y + 4 log₂ z = 13` holds exactly for `x = ±1`, `y = 4`, `z = 8`. -/
@[kb "stitzzeager2013" "Exercise 8.7.20, p. 659"]
theorem exer_8_7_20 : ∀ x y z : ℝ, 0 ≤ y → 0 < z →
    ((x ^ 2 + √y + Real.logb 2 z = 6 ∧ 3 * x ^ 2 - 2 * √y + 2 * Real.logb 2 z = 5 ∧
        -5 * x ^ 2 + 3 * √y + 4 * Real.logb 2 z = 13) ↔
      ((x = 1 ∨ x = -1) ∧ y = 4 ∧ z = 8)) := by
  intro x y z hy hz
  have h4 : √(4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  have h8 : Real.logb 2 (8 : ℝ) = 3 := by
    have : (8 : ℝ) = 2 ^ (3 : ℝ) := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    rw [this]; exact Real.logb_rpow (by norm_num) (by norm_num)
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hx : x ^ 2 = 1 := by linarith
    have hs : √y = 2 := by linarith
    have hl : Real.logb 2 z = 3 := by linarith
    refine ⟨?_, ?_, ?_⟩
    · have : x ^ 2 = 1 ^ 2 := by linarith
      exact sq_eq_sq_iff_eq_or_eq_neg.mp this
    · have := Real.sq_sqrt hy
      rw [hs] at this; linarith
    · have := Real.rpow_logb (b := 2) (x := z) (by norm_num) (by norm_num) hz
      rw [hl] at this
      rw [← this]; norm_num
  · rintro ⟨hx | hx, rfl, rfl⟩ <;> subst hx <;> rw [h4, h8] <;> refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- Stitz-Zeager Exercise 8.7.27: for positive `x, y, z` and `λ`, the box system `2y + 2z = λyz`, `2x + 2z = λxz`,
`2y + 2x = λxy`, `xyz = 1000` forces `x = y = z = 10` and `λ = 2/5`. -/
@[kb "stitzzeager2013" "Exercise 8.7.27, p. 659"]
theorem exer_8_7_27 : ∀ x y z l : ℝ, 0 < x → 0 < y → 0 < z →
    (2 * y + 2 * z = l * y * z ∧ 2 * x + 2 * z = l * x * z ∧ 2 * y + 2 * x = l * x * y ∧ x * y * z = 1000) →
    x = 10 ∧ y = 10 ∧ z = 10 ∧ l = 2 / 5 := by
  intro x y z l hx hy hz ⟨h1, h2, h3, h4⟩
  have hxy : x = y := by
    by_contra hne
    have h5 : (y - x) * (2 - l * z) = 0 := by linarith
    rcases mul_eq_zero.mp h5 with h | h
    · exact hne (by linarith)
    · have : l * z = 2 := by linarith
      nlinarith
  subst hxy
  have hxz : x = z := by
    have h5 : l * x = 4 := by
      have : x * (l * x - 4) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hx.ne'
      · linarith
    nlinarith
  subst hxz
  have h5 : x ^ 3 = 10 ^ 3 := by nlinarith
  have hx10 : x = 10 := by
    exact (pow_left_inj₀ hx.le (by norm_num) (by norm_num)).mp h5
  subst hx10
  refine ⟨rfl, rfl, rfl, ?_⟩
  linarith

/-- Stitz-Zeager Exercise 8.7.28: `x⁴ + 4` has no real zeros and factors as `(x² - 2x + 2)(x² + 2x + 2)`. -/
@[kb "stitzzeager2013" "Exercise 8.7.28, p. 659"]
theorem exer_8_7_28 : (∀ x : ℝ, x ^ 4 + 4 ≠ 0) ∧
    ∀ x : ℝ, x ^ 4 + 4 = (x ^ 2 - 2 * x + 2) * (x ^ 2 + 2 * x + 2) := by
  refine ⟨fun x => by positivity, fun x => by ring⟩

/-- Stitz-Zeager Exercise 8.7.29: `x⁴ + 6x² - 5x + 6 = (x² - x + 1)(x² + x + 6)`. -/
@[kb "stitzzeager2013" "Exercise 8.7.29, p. 659"]
theorem exer_8_7_29 : ∀ x : ℝ, x ^ 4 + 6 * x ^ 2 - 5 * x + 6 = (x ^ 2 - x + 1) * (x ^ 2 + x + 6) := by
  intro x; ring

end UndergradKB.Precalculus.Course
