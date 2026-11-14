import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 8 (Stitz-Zeager): exercises with the book's answers (wave 8), Sections 8.6, 8.7 -/

namespace UndergradKB.Precalculus.Course

open Set

/-- Stitz-Zeager Exercise 8.6.19: `8/(x²-9)` is not `8/x² - 8/9` in general (for example at `x = 1` the left side is
`-1` and the right side is `64/9`). -/
@[kb "stitzzeager2013" "Exercise 8.6.19, p. 647"]
theorem exer_8_6_19 : ¬ ∀ x : ℝ, x ^ 2 ≠ 0 → x ^ 2 - 9 ≠ 0 → 8 / (x ^ 2 - 9) = 8 / x ^ 2 - 8 / 9 := by
  intro h
  have := h 1 (by norm_num) (by norm_num)
  norm_num at this

/-- Stitz-Zeager Exercise 8.7.21: the boundary curves `x² - y² = 1` and `x² + 4y² = 4` meet exactly where
`x² = 8/5` and `y² = 3/5`, i.e. at the four points `(±2√10/5, ±√15/5)`. -/
@[kb "stitzzeager2013" "Exercise 8.7.21, p. 659"]
theorem exer_8_7_21 (x y : ℝ) :
    (x ^ 2 - y ^ 2 = 1 ∧ x ^ 2 + 4 * y ^ 2 = 4) ↔ (x ^ 2 = 8 / 5 ∧ y ^ 2 = 3 / 5) := by
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

/-- Stitz-Zeager Exercise 8.7.22: the boundary circles `x² + y² = 25` and `x² + (y-3)² = 10` meet exactly at
`(3, 4)` and `(-3, 4)`. -/
@[kb "stitzzeager2013" "Exercise 8.7.22, p. 659"]
theorem exer_8_7_22 (x y : ℝ) :
    (x ^ 2 + y ^ 2 = 25 ∧ x ^ 2 + (y - 3) ^ 2 = 10) ↔ ((x = 3 ∨ x = -3) ∧ y = 4) := by
  constructor
  · rintro ⟨h1, h2⟩
    have hy : y = 4 := by nlinarith
    subst hy
    have : (x - 3) * (x + 3) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · exact ⟨Or.inl (by linarith), rfl⟩
    · exact ⟨Or.inr (by linarith), rfl⟩
  · rintro ⟨h | h, rfl⟩ <;> subst h <;> norm_num

/-- Stitz-Zeager Exercise 8.7.23: the boundary curves `(x-2)² + y² = 1` and `x² + 4y² = 4` meet exactly where
`x = 4/3` and `y² = 5/9`, i.e. at `(4/3, ±√5/3)`. -/
@[kb "stitzzeager2013" "Exercise 8.7.23, p. 659"]
theorem exer_8_7_23 (x y : ℝ) :
    ((x - 2) ^ 2 + y ^ 2 = 1 ∧ x ^ 2 + 4 * y ^ 2 = 4) ↔ (x = 4 / 3 ∧ y ^ 2 = 5 / 9) := by
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : (3 * x - 4) * (x - 4) = 0 := by nlinarith
    rcases mul_eq_zero.1 h3 with h | h
    · have hx : x = 4 / 3 := by linarith
      subst hx
      exact ⟨rfl, by nlinarith⟩
    · have hx : x = 4 := by linarith
      subst hx
      nlinarith [sq_nonneg y]
  · rintro ⟨rfl, h⟩
    constructor <;> nlinarith

private theorem x8w8b_pB (r1 r2 r3 x : ℝ) (h12 : r1 < r2) (h23 : r2 < r3) :
    0 < (x - r1) * (x - r2) * (x - r3) ↔ (r1 < x ∧ x < r2) ∨ r3 < x := by
  constructor
  · intro h
    rcases le_or_gt x r1 with h1 | h1
    · have := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ r1 - x) (by linarith : (0 : ℝ) ≤ r2 - x))
        (by linarith : (0 : ℝ) ≤ r3 - x)
      nlinarith [this]
    · rcases lt_or_ge x r2 with h2 | h2
      · exact Or.inl ⟨h1, h2⟩
      · rcases lt_or_ge r3 x with h3 | h3
        · exact Or.inr h3
        · have := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ x - r1) (by linarith : (0 : ℝ) ≤ x - r2))
            (by linarith : (0 : ℝ) ≤ r3 - x)
          nlinarith [this]
  · rintro (⟨h1, h2⟩ | h)
    · have := mul_pos (mul_pos (by linarith : (0 : ℝ) < x - r1) (by linarith : (0 : ℝ) < r2 - x))
        (by linarith : (0 : ℝ) < r3 - x)
      nlinarith [this]
    · exact mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)

/-- Stitz-Zeager Exercise 8.7.24: the boundary curves `y = 10x - x²` and `y = x³ + 8` meet exactly at
`(-4, -56)`, `(1, 9)` and `(2, 16)`; and the strip `10x - x² < y < x³ + 8` lies over exactly the `x` in
`(-4, 1) ∪ (2, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 8.7.24, p. 659"]
theorem exer_8_7_24 :
    (∀ x y : ℝ, (y = 10 * x - x ^ 2 ∧ y = x ^ 3 + 8) ↔
      ((x = -4 ∧ y = -56) ∨ (x = 1 ∧ y = 9) ∨ (x = 2 ∧ y = 16))) ∧
    {x : ℝ | ∃ y : ℝ, 10 * x - x ^ 2 < y ∧ y < x ^ 3 + 8} = Ioo (-4) 1 ∪ Ioi 2 := by
  constructor
  · intro x y
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : (x + 4) * (x - 1) * (x - 2) = 0 := by linear_combination h1 - h2
      rcases mul_eq_zero.1 h3 with h | h
      · rcases mul_eq_zero.1 h with h | h
        · have hx : x = -4 := by linarith
          subst hx
          exact Or.inl ⟨rfl, by rw [h1]; norm_num⟩
        · have hx : x = 1 := by linarith
          subst hx
          exact Or.inr (Or.inl ⟨rfl, by rw [h1]; norm_num⟩)
      · have hx : x = 2 := by linarith
        subst hx
        exact Or.inr (Or.inr ⟨rfl, by rw [h1]; norm_num⟩)
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num
  · ext x
    simp only [mem_setOf_eq, mem_union, mem_Ioo, mem_Ioi]
    have hB := x8w8b_pB (-4) 1 2 x (by norm_num) (by norm_num)
    have hx : (x - -4) * (x - 1) * (x - 2) = x ^ 3 + 8 - (10 * x - x ^ 2) := by ring
    rw [hx] at hB
    constructor
    · rintro ⟨y, h1, h2⟩
      exact hB.1 (by linarith)
    · intro h
      have h' := hB.2 h
      refine ⟨(10 * x - x ^ 2 + (x ^ 3 + 8)) / 2, by linarith, by linarith⟩

/-- Stitz-Zeager Exercise 8.7.25: the boundary curves `x + 2y² = 2` and `x² + 4y² = 4` meet exactly at `(0, 1)`,
`(0, -1)` and `(2, 0)`. -/
@[kb "stitzzeager2013" "Exercise 8.7.25, p. 659"]
theorem exer_8_7_25 (x y : ℝ) :
    (x + 2 * y ^ 2 = 2 ∧ x ^ 2 + 4 * y ^ 2 = 4) ↔
      ((x = 0 ∧ (y = 1 ∨ y = -1)) ∨ (x = 2 ∧ y = 0)) := by
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : x * (x - 2) = 0 := by nlinarith
    rcases mul_eq_zero.1 h3 with h | h
    · subst h
      have : (y - 1) * (y + 1) = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h' | h'
      · exact Or.inl ⟨rfl, Or.inl (by linarith)⟩
      · exact Or.inl ⟨rfl, Or.inr (by linarith)⟩
    · have hx : x = 2 := by linarith
      subst hx
      have : y ^ 2 = 0 := by nlinarith
      exact Or.inr ⟨rfl, by simpa using this⟩
  · rintro ((⟨rfl, rfl | rfl⟩) | ⟨rfl, rfl⟩) <;> norm_num

/-- Stitz-Zeager Exercise 8.7.26: the boundary circle `x² + y² = 25` and line `y - x = 1` meet exactly at
`(3, 4)` and `(-4, -3)`. -/
@[kb "stitzzeager2013" "Exercise 8.7.26, p. 659"]
theorem exer_8_7_26 (x y : ℝ) :
    (x ^ 2 + y ^ 2 = 25 ∧ y - x = 1) ↔ ((x = 3 ∧ y = 4) ∨ (x = -4 ∧ y = -3)) := by
  constructor
  · rintro ⟨h1, h2⟩
    have hy : y = x + 1 := by linarith
    subst hy
    have h3 : (x - 3) * (x + 4) = 0 := by nlinarith
    rcases mul_eq_zero.1 h3 with h | h
    · exact Or.inl ⟨by linarith, by linarith⟩
    · exact Or.inr ⟨by linarith, by linarith⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

end UndergradKB.Precalculus.Course
