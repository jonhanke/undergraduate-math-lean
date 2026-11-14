import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum.Basic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 2 (Stitz-Zeager): exercises with the book's answers -/

namespace UndergradKB.Precalculus.Course

/-! ## Section 2.1 -/

/-- Stitz-Zeager Exercise 2.1.1: the line of slope `3` through `(3,-1)` has point-slope form
`y + 1 = 3(x - 3)` and slope-intercept form `y = 3x - 10`. -/
@[kb "stitzzeager2013" "Exercise 2.1.1, p. 175"]
theorem exer_2_1_1 (x y : ℝ) : (y + 1 = 3 * (x - 3) ↔ y = 3 * x - 10) := by
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 2.1.5: the line of slope `-1/5` through `(10,4)` is `y = -x/5 + 6`. -/
@[kb "stitzzeager2013" "Exercise 2.1.5, p. 175"]
theorem exer_2_1_5 (x y : ℝ) : (y - 4 = -(1 / 5) * (x - 10) ↔ y = -(1 / 5) * x + 6) := by
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 2.1.9: the line of slope `-5` through `(√3, 2√3)` is `y = -5x + 7√3`. -/
@[kb "stitzzeager2013" "Exercise 2.1.9, p. 175"]
theorem exer_2_1_9 (x y : ℝ) :
    (y - 2 * Real.sqrt 3 = -5 * (x - Real.sqrt 3) ↔ y = -5 * x + 7 * Real.sqrt 3) := by
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 2.1.13: the line through `(5,0)` and `(0,-8)` is `y = (8/5)x - 8`. -/
@[kb "stitzzeager2013" "Exercise 2.1.13, p. 175"]
theorem exer_2_1_13 (m b : ℝ) :
    (m * 5 + b = 0 ∧ m * 0 + b = -8) ↔ (m = 8 / 5 ∧ b = -8) := by
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 2.1.14: the line through `(3,-5)` and `(7,4)` is `y = (9/4)x - 47/4`. -/
@[kb "stitzzeager2013" "Exercise 2.1.14, p. 175"]
theorem exer_2_1_14 (m b : ℝ) :
    (m * 3 + b = -5 ∧ m * 7 + b = 4) ↔ (m = 9 / 4 ∧ b = -47 / 4) := by
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 2.1.17: the line through `(1/2,3/4)` and `(5/2,-7/4)` is
`y = -(5/4)x + 11/8`. -/
@[kb "stitzzeager2013" "Exercise 2.1.17, p. 175"]
theorem exer_2_1_17 (m b : ℝ) :
    (m * (1 / 2) + b = 3 / 4 ∧ m * (5 / 2) + b = -7 / 4) ↔ (m = -5 / 4 ∧ b = 11 / 8) := by
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 2.1.18: the line through `(2/3,7/2)` and `(-1/3,3/2)` is
`y = 2x + 13/6`. -/
@[kb "stitzzeager2013" "Exercise 2.1.18, p. 175"]
theorem exer_2_1_18 (m b : ℝ) :
    (m * (2 / 3) + b = 7 / 2 ∧ m * (-1 / 3) + b = 3 / 2) ↔ (m = 2 ∧ b = 13 / 6) := by
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 2.1.20: the line through `(-√3,-1)` and `(√3,1)` is `y = (√3/3)x`. -/
@[kb "stitzzeager2013" "Exercise 2.1.20, p. 175"]
theorem exer_2_1_20 (m b : ℝ) :
    (m * (-Real.sqrt 3) + b = -1 ∧ m * Real.sqrt 3 + b = 1) ↔ (m = Real.sqrt 3 / 3 ∧ b = 0) := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hp : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  constructor
  · rintro ⟨h1, h2⟩
    have hb : b = 0 := by linarith
    subst hb
    refine ⟨?_, rfl⟩
    field_simp
    nlinarith
  · rintro ⟨rfl, rfl⟩
    constructor <;> nlinarith

/-- Stitz-Zeager Exercise 2.1.27: the points of `y = 2x + 1` at distance `4` from `(-1,3)` are
`(-1,-1)` and `(11/5,27/5)`. -/
@[kb "stitzzeager2013" "Exercise 2.1.27, p. 175"]
theorem exer_2_1_27 (x y : ℝ) :
    (y = 2 * x + 1 ∧ (x + 1) ^ 2 + (y - 3) ^ 2 = 4 ^ 2) ↔
      ((x = -1 ∧ y = -1) ∨ (x = 11 / 5 ∧ y = 27 / 5)) := by
  constructor
  · rintro ⟨rfl, h⟩
    have : (x + 1) * (5 * x - 11) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · left; constructor <;> linarith
    · right; constructor <;> linarith
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

/-- Stitz-Zeager Exercise 2.1.32: weekly pay `W(x) = 200 + 0.05x` equals `475` exactly when sales
are `5500`. -/
@[kb "stitzzeager2013" "Exercise 2.1.32, p. 176"]
theorem exer_2_1_32 (x : ℝ) : 200 + (5 / 100) * x = 475 ↔ x = 5500 := by
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 2.1.33: the cost line through `(600, 22.50)` and `(400, 15.50)` has
slope `0.035` and intercept `C(0) = 1.50`. -/
@[kb "stitzzeager2013" "Exercise 2.1.33, p. 176"]
theorem exer_2_1_33 (m b : ℝ) :
    (m * 600 + b = 45 / 2 ∧ m * 400 + b = 31 / 2) ↔ (m = 35 / 1000 ∧ b = 3 / 2) := by
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 2.1.35: `F(C) = (9/5)C + 32` is the unique line sending `0 ↦ 32`,
`100 ↦ 212`; `F(20) = 68`; the inverse conversion gives `C(110) = 130/3`; and `F(n) = C(n)` only
at `n = -40`. -/
@[kb "stitzzeager2013" "Exercise 2.1.35, p. 176"]
theorem exer_2_1_35 :
    (∀ a b : ℝ, (a * 0 + b = 32 ∧ a * 100 + b = 212) ↔ (a = 9 / 5 ∧ b = 32)) ∧
    (9 / 5 : ℝ) * 20 + 32 = 68 ∧ (5 / 9 : ℝ) * (110 - 32) = 130 / 3 ∧
    (∀ n : ℝ, (9 / 5) * n + 32 = (5 / 9) * (n - 32) ↔ n = -40) := by
  refine ⟨?_, by norm_num, by norm_num, ?_⟩
  · intro a b
    constructor
    · rintro ⟨h1, h2⟩; constructor <;> linarith
    · rintro ⟨rfl, rfl⟩; norm_num
  · intro n
    constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 2.1.36: the line with `N(40) = 9`, `N(70) = 5` is
`N(T) = -(2/15)T + 43/3`, with `N(20) = 35/3` and `N(107.5) = 0`. -/
@[kb "stitzzeager2013" "Exercise 2.1.36, p. 176"]
theorem exer_2_1_36 :
    (∀ a b : ℝ, (a * 40 + b = 9 ∧ a * 70 + b = 5) ↔ (a = -2 / 15 ∧ b = 43 / 3)) ∧
    (-2 / 15 : ℝ) * 20 + 43 / 3 = 35 / 3 ∧ (-2 / 15 : ℝ) * (215 / 2) + 43 / 3 = 0 := by
  refine ⟨?_, by norm_num, by norm_num⟩
  intro a b
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 2.1.44-49: average rates of change of `x³` on `[-1,2]` (`3`), `1/x` on
`[1,5]` (`-1/5`), `√x` on `[0,16]` (`1/4`), `x²` on `[-3,3]` (`0`), `(x+4)/(x-3)` on `[5,7]`
(`-7/8`), `3x²+2x-7` on `[-4,2]` (`-4`). -/
@[kb "stitzzeager2013" "Exercise 2.1.44, p. 177"]
theorem exer_2_1_44 :
    ((2 : ℝ) ^ 3 - (-1) ^ 3) / (2 - (-1)) = 3 ∧
    ((1 : ℝ) / 5 - 1 / 1) / (5 - 1) = -1 / 5 ∧
    (Real.sqrt 16 - Real.sqrt 0) / (16 - 0) = 1 / 4 ∧
    ((3 : ℝ) ^ 2 - (-3) ^ 2) / (3 - (-3)) = 0 ∧
    ((7 + 4) / (7 - 3) - (5 + 4) / (5 - 3) : ℝ) / (7 - 5) = -7 / 8 ∧
    ((3 * 2 ^ 2 + 2 * 2 - 7) - (3 * (-4) ^ 2 + 2 * (-4) - 7) : ℝ) / (2 - (-4)) = -4 := by
  have h16 : Real.sqrt 16 = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  rw [h16, Real.sqrt_zero]
  norm_num

/-- Stitz-Zeager Exercise 2.1.50-53: difference quotients of `x³` (`3x²+3xh+h²`), `1/x`
(`-1/(x(x+h))`), `(x+4)/(x-3)` (`-7/((x-3)(x+h-3))`) and `3x²+2x-7` (`6x+3h+2`), for `h ≠ 0`
and arguments in the domain. -/
@[kb "stitzzeager2013" "Exercise 2.1.50, p. 178"]
theorem exer_2_1_50 (x h : ℝ) (hh : h ≠ 0) (hx : x ≠ 0) (hxh : x + h ≠ 0) (h3 : x - 3 ≠ 0)
    (h3' : x + h - 3 ≠ 0) :
    (((x + h) ^ 3 - x ^ 3) / h = 3 * x ^ 2 + 3 * x * h + h ^ 2) ∧
    ((1 / (x + h) - 1 / x) / h = -1 / (x * (x + h))) ∧
    (((x + h + 4) / (x + h - 3) - (x + 4) / (x - 3)) / h = -7 / ((x - 3) * (x + h - 3))) ∧
    (((3 * (x + h) ^ 2 + 2 * (x + h) - 7) - (3 * x ^ 2 + 2 * x - 7)) / h = 6 * x + 3 * h + 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring

/-- Stitz-Zeager Exercise 2.1.54: for `h(t) = -16t² + 64`, the average rate of change over
`[0,2]` is `-32`. -/
@[kb "stitzzeager2013" "Exercise 2.1.54, p. 178"]
theorem exer_2_1_54 :
    ((-16 * 2 ^ 2 + 64 : ℝ) - (-16 * 0 ^ 2 + 64)) / (2 - 0) = -32 := by norm_num

/-- Stitz-Zeager Exercise 2.1.55: for `F(t) = -0.0076t² + 0.45t + 16`, the average rate of change
over `[0,28]` is `0.2372`. -/
@[kb "stitzzeager2013" "Exercise 2.1.55, p. 178"]
theorem exer_2_1_55 :
    ((-76 / 10000 * 28 ^ 2 + 45 / 100 * 28 + 16 : ℝ) - (-76 / 10000 * 0 ^ 2 + 45 / 100 * 0 + 16)) /
      (28 - 0) = 2372 / 10000 := by norm_num

/-- Stitz-Zeager Exercise 2.1.56: for `T(t) = -t²/2 + 8t + 32`: `T(4) = 56`, `T(8) = 64`,
`T(12) = 56`, and the average rates of change over `[4,8]`, `[8,12]`, `[4,12]` are `2`, `-2`, `0`. -/
@[kb "stitzzeager2013" "Exercise 2.1.56, p. 178"]
theorem exer_2_1_56 :
    let T : ℝ → ℝ := fun t => -(1 / 2) * t ^ 2 + 8 * t + 32
    T 4 = 56 ∧ T 8 = 64 ∧ T 12 = 56 ∧ (T 8 - T 4) / (8 - 4) = 2 ∧
      (T 12 - T 8) / (12 - 8) = -2 ∧ (T 12 - T 4) / (12 - 4) = 0 := by
  intro T
  simp only [T]
  norm_num

/-- Stitz-Zeager Exercise 2.1.57: for `C(x) = x² - 10x + 27`, the average rate of change from
`3` to `5` is `-2`. -/
@[kb "stitzzeager2013" "Exercise 2.1.57, p. 178"]
theorem exer_2_1_57 :
    (((5 : ℝ) ^ 2 - 10 * 5 + 27) - (3 ^ 2 - 10 * 3 + 27)) / (5 - 3) = -2 := by norm_num

/-- Stitz-Zeager Exercise 2.1.59-60: lines parallel to `y = 3x + 2` through the origin and to
`y = -6x + 5` through `(3,2)`: `y = 3x` and `y = -6x + 20`. -/
@[kb "stitzzeager2013" "Exercise 2.1.59, p. 178"]
theorem exer_2_1_59 :
    (∀ b : ℝ, 3 * 0 + b = 0 ↔ b = 0) ∧ (∀ b : ℝ, -6 * 3 + b = 2 ↔ b = 20) := by
  constructor <;> intro b <;> constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 2.1.62: the line parallel to `y = (4-x)/3` through `(1,-1)` is
`y = -x/3 - 2/3`. -/
@[kb "stitzzeager2013" "Exercise 2.1.62, p. 179"]
theorem exer_2_1_62 (b : ℝ) : (-(1 / 3) * 1 + b = -1 ↔ b = -2 / 3) := by
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 2.1.66-68: lines perpendicular to `y = -6x + 5` through `(3,2)`
(`y = x/6 + 3/2`), to `y = (2/3)x - 7` through `(6,0)` (`y = -(3/2)x + 9`), and to `y = (4-x)/3`
through `(1,-1)` (`y = 3x - 4`). -/
@[kb "stitzzeager2013" "Exercise 2.1.66, p. 179"]
theorem exer_2_1_66 :
    (-6 : ℝ) * (1 / 6) = -1 ∧ (∀ b : ℝ, 1 / 6 * 3 + b = 2 ↔ b = 3 / 2) ∧
    (2 / 3 : ℝ) * (-3 / 2) = -1 ∧ (∀ b : ℝ, -3 / 2 * 6 + b = 0 ↔ b = 9) ∧
    (-1 / 3 : ℝ) * 3 = -1 ∧ (∀ b : ℝ, 3 * 1 + b = -1 ↔ b = -4) := by
  refine ⟨by norm_num, ?_, by norm_num, ?_, by norm_num, ?_⟩ <;> intro b <;> constructor <;>
    intro h <;> linarith

/-- Stitz-Zeager Exercise 2.1.72: for `a ≠ b`, the line through `(a,b)` and `(b,a)` has slope `-1`,
the negative reciprocal of the slope of `y = x`. -/
@[kb "stitzzeager2013" "Exercise 2.1.72, p. 180"]
theorem exer_2_1_72 (a b : ℝ) (h : a ≠ b) : (a - b) / (b - a) * 1 = -1 := by
  have : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  field_simp
  ring

/-! ## Section 2.2 -/

/-- Stitz-Zeager Exercise 2.2.2: `|3x - 1| = 10` iff `x = -3` or `x = 11/3`. -/
@[kb "stitzzeager2013" "Exercise 2.2.2, p. 195"]
theorem exer_2_2_2 (x : ℝ) : |3 * x - 1| = 10 ↔ x = -3 ∨ x = 11 / 3 := by
  constructor
  · intro h
    rcases abs_cases (3 * x - 1) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] at h <;>
      first | (left; linarith) | (right; linarith)
  · rintro (rfl | rfl) <;> norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Stitz-Zeager Exercise 2.2.5: `2|5x + 1| - 3 = 0` iff `x = -1/2` or `x = 1/10`. -/
@[kb "stitzzeager2013" "Exercise 2.2.5, p. 195"]
theorem exer_2_2_5 (x : ℝ) : 2 * |5 * x + 1| - 3 = 0 ↔ x = -1 / 2 ∨ x = 1 / 10 := by
  constructor
  · intro h
    rcases abs_cases (5 * x + 1) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] at h <;>
      first | (left; linarith) | (right; linarith)
  · rintro (rfl | rfl) <;> norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Stitz-Zeager Exercise 2.2.6: `|7x - 1| + 2 = 0` has no real solution. -/
@[kb "stitzzeager2013" "Exercise 2.2.6, p. 195"]
theorem exer_2_2_6 : ¬ ∃ x : ℝ, |7 * x - 1| + 2 = 0 := by
  rintro ⟨x, h⟩
  have := abs_nonneg (7 * x - 1)
  linarith

/-- Stitz-Zeager Exercise 2.2.7: `(5 - |x|)/2 = 1` iff `x = -3` or `x = 3`. -/
@[kb "stitzzeager2013" "Exercise 2.2.7, p. 195"]
theorem exer_2_2_7 (x : ℝ) : (5 - |x|) / 2 = 1 ↔ x = -3 ∨ x = 3 := by
  constructor
  · intro h
    rcases abs_cases x with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] at h <;>
      first | (left; linarith) | (right; linarith)
  · rintro (rfl | rfl) <;> norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Stitz-Zeager Exercise 2.2.9: `|x| = x + 3` iff `x = -3/2`. -/
@[kb "stitzzeager2013" "Exercise 2.2.9, p. 195"]
theorem exer_2_2_9 (x : ℝ) : |x| = x + 3 ↔ x = -3 / 2 := by
  constructor
  · intro h
    rcases abs_cases x with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] at h <;> linarith
  · rintro rfl; norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Stitz-Zeager Exercise 2.2.10: `|2x - 1| = x + 1` iff `x = 0` or `x = 2`. -/
@[kb "stitzzeager2013" "Exercise 2.2.10, p. 195"]
theorem exer_2_2_10 (x : ℝ) : |2 * x - 1| = x + 1 ↔ x = 0 ∨ x = 2 := by
  constructor
  · intro h
    rcases abs_cases (2 * x - 1) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] at h <;>
      first | (left; linarith) | (right; linarith)
  · rintro (rfl | rfl) <;> norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Stitz-Zeager Exercise 2.2.11: `4 - |x| = 2x + 1` iff `x = 1`. -/
@[kb "stitzzeager2013" "Exercise 2.2.11, p. 195"]
theorem exer_2_2_11 (x : ℝ) : 4 - |x| = 2 * x + 1 ↔ x = 1 := by
  constructor
  · intro h
    rcases abs_cases x with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] at h <;> linarith
  · rintro rfl; norm_num

/-- Stitz-Zeager Exercise 2.2.12: `|x - 4| = x - 5` has no real solution. -/
@[kb "stitzzeager2013" "Exercise 2.2.12, p. 195"]
theorem exer_2_2_12 : ¬ ∃ x : ℝ, |x - 4| = x - 5 := by
  rintro ⟨x, h⟩
  rcases abs_cases (x - 4) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] at h <;> linarith

/-- Stitz-Zeager Exercise 2.2.13: `|x| = x²` iff `x ∈ {-1, 0, 1}`. -/
@[kb "stitzzeager2013" "Exercise 2.2.13, p. 195"]
theorem exer_2_2_13 (x : ℝ) : |x| = x ^ 2 ↔ x = -1 ∨ x = 0 ∨ x = 1 := by
  constructor
  · intro h
    rcases abs_cases x with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] at h
    · have : x * (x - 1) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · right; left; exact h
      · right; right; linarith
    · have : x * (x + 1) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · right; left; exact h
      · left; linarith
  · rintro (rfl | rfl | rfl) <;> norm_num

/-- Stitz-Zeager Exercise 2.2.14: `|x| = 12 - x²` iff `x = -3` or `x = 3`. -/
@[kb "stitzzeager2013" "Exercise 2.2.14, p. 195"]
theorem exer_2_2_14 (x : ℝ) : |x| = 12 - x ^ 2 ↔ x = -3 ∨ x = 3 := by
  constructor
  · intro h
    rcases abs_cases x with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] at h
    · have : (x - 3) * (x + 4) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · right; linarith
      · exfalso; linarith
    · have : (x + 3) * (x - 4) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · left; linarith
      · exfalso; linarith
  · rintro (rfl | rfl) <;> norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Stitz-Zeager Exercise 2.2.15: `|x² - 1| = 3` iff `x = -2` or `x = 2`. -/
@[kb "stitzzeager2013" "Exercise 2.2.15, p. 195"]
theorem exer_2_2_15 (x : ℝ) : |x ^ 2 - 1| = 3 ↔ x = -2 ∨ x = 2 := by
  constructor
  · intro h
    rcases abs_cases (x ^ 2 - 1) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] at h
    · have : (x - 2) * (x + 2) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · right; linarith
      · left; linarith
    · nlinarith [sq_nonneg x]
  · rintro (rfl | rfl) <;> norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Stitz-Zeager Exercise 2.2.16 (preliminary claim): if `|f| = |g|` then `f = g` or `f = -g`. -/
@[kb "stitzzeager2013" "Exercise 2.2.16, p. 195"]
theorem exer_2_2_16_lemma (a b : ℝ) (h : |a| = |b|) : a = b ∨ a = -b := abs_eq_abs.1 h

/-- Stitz-Zeager Exercise 2.2.16-18: `|3x - 2| = |2x + 7|` iff `x ∈ {-1, 9}`;
`|3x + 1| = |4x|` iff `x ∈ {-1/7, 1}`; `|1 - 2x| = |x + 1|` iff `x ∈ {0, 2}`. -/
@[kb "stitzzeager2013" "Exercise 2.2.16, p. 195"]
theorem exer_2_2_16 (x : ℝ) :
    (|3 * x - 2| = |2 * x + 7| ↔ x = -1 ∨ x = 9) ∧
    (|3 * x + 1| = |4 * x| ↔ x = -1 / 7 ∨ x = 1) ∧
    (|1 - 2 * x| = |x + 1| ↔ x = 0 ∨ x = 2) := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [abs_eq_abs] <;> constructor <;> rintro (h | h) <;>
    first | (left; linarith) | (right; linarith)

/-- Stitz-Zeager Exercise 2.2.19-21: `|4 - x| - |x + 2| = 0` iff `x = 1`; `|2 - 5x| = 5|x + 1|`
iff `x = -3/10`; `3|x - 1| = 2|x + 1|` iff `x ∈ {1/5, 5}`. -/
@[kb "stitzzeager2013" "Exercise 2.2.19, p. 195"]
theorem exer_2_2_19 (x : ℝ) :
    (|4 - x| - |x + 2| = 0 ↔ x = 1) ∧ (|2 - 5 * x| = 5 * |x + 1| ↔ x = -3 / 10) ∧
    (3 * |x - 1| = 2 * |x + 1| ↔ x = 1 / 5 ∨ x = 5) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [sub_eq_zero, abs_eq_abs]
    constructor
    · rintro (h | h) <;> linarith
    · rintro rfl; left; norm_num
  · have : 5 * |x + 1| = |5 * x + 5| := by
      rw [show 5 * x + 5 = 5 * (x + 1) by ring, abs_mul]; norm_num
    rw [this, abs_eq_abs]
    constructor
    · rintro (h | h)
      · linarith
      · exfalso; linarith
    · rintro rfl; left; norm_num
  · have h3 : 3 * |x - 1| = |3 * x - 3| := by
      rw [show 3 * x - 3 = 3 * (x - 1) by ring, abs_mul]; norm_num
    have h2 : 2 * |x + 1| = |2 * x + 2| := by
      rw [show 2 * x + 2 = 2 * (x + 1) by ring, abs_mul]; norm_num
    rw [h3, h2, abs_eq_abs]
    constructor
    · rintro (h | h)
      · right; linarith
      · left; linarith
    · rintro (rfl | rfl)
      · right; norm_num
      · left; norm_num

/-- Stitz-Zeager Exercise 2.2.30: `x + |x| - 3` is `-3` for `x < 0` and `2x - 3` for `x ≥ 0`, with
its only zero at `x = 3/2` and range `[-3, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 2.2.30, p. 195"]
theorem exer_2_2_30 :
    (∀ x : ℝ, x < 0 → x + |x| - 3 = -3) ∧ (∀ x : ℝ, 0 ≤ x → x + |x| - 3 = 2 * x - 3) ∧
    (∀ x : ℝ, x + |x| - 3 = 0 ↔ x = 3 / 2) ∧
    (∀ x : ℝ, -3 ≤ x + |x| - 3) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx; rw [abs_of_neg hx]; ring
  · intro x hx; rw [abs_of_nonneg hx]; ring
  · intro x
    constructor
    · intro h
      rcases abs_cases x with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] at h <;> linarith
    · rintro rfl; norm_num [abs_of_nonneg]
  · intro x
    rcases abs_cases x with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;> linarith

/-- Stitz-Zeager Exercise 2.2.32: `|x + 2| - |x|` is `-2` for `x < -2`, `2x + 2` on `[-2, 0)`,
`2` for `x ≥ 0`. -/
@[kb "stitzzeager2013" "Exercise 2.2.32, p. 195"]
theorem exer_2_2_32 :
    (∀ x : ℝ, x < -2 → |x + 2| - |x| = -2) ∧
    (∀ x : ℝ, -2 ≤ x → x < 0 → |x + 2| - |x| = 2 * x + 2) ∧
    (∀ x : ℝ, 0 ≤ x → |x + 2| - |x| = 2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx; rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]; ring
  · intro x h1 h2; rw [abs_of_nonneg (by linarith), abs_of_neg h2]; ring
  · intro x hx; rw [abs_of_nonneg (by linarith), abs_of_nonneg hx]; ring

/-- Stitz-Zeager Exercise 2.2.36: the triangle inequality `|a + b| ≤ |a| + |b|`. -/
@[kb "stitzzeager2013" "Exercise 2.2.36, p. 195"]
theorem exer_2_2_36 (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  rcases abs_cases (a + b) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;>
    nlinarith [le_abs_self a, le_abs_self b, neg_abs_le a, neg_abs_le b]

end UndergradKB.Precalculus.Course
