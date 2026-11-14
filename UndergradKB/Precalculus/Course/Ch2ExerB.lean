import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Data.Int.Cast.Lemmas
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 2 (Stitz-Zeager): exercises with the book's answers, Sections 2.3 on -/

namespace UndergradKB.Precalculus.Course

private lemma aux_sq_eq_sqrt (y c : ℝ) (hc : 0 ≤ c) : y ^ 2 = c ↔ y = √c ∨ y = -√c := by
  have h := Real.sq_sqrt hc
  constructor
  · intro hy
    have : (y - √c) * (y + √c) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · left; linarith
    · right; linarith
  · rintro (h1 | h1) <;> rw [h1] <;> nlinarith

/-! ## Section 2.3 -/

/-- Stitz-Zeager Exercise 2.3.3: `f(x) = x² - 2x - 8` has vertex form `(x - 1)² - 9`, zeros `-2` and
`4`, and its minimum value `-9` at `x = 1`. -/
@[kb "stitzzeager2013" "Exercise 2.3.3, p. 212"]
theorem exer_2_3_3 : (∀ x : ℝ, x ^ 2 - 2 * x - 8 = (x - 1) ^ 2 - 9) ∧
    (∀ x : ℝ, x ^ 2 - 2 * x - 8 = 0 ↔ x = -2 ∨ x = 4) ∧ (∀ x : ℝ, -9 ≤ x ^ 2 - 2 * x - 8) := by
  refine ⟨fun x => by ring, fun x => ?_, fun x => by nlinarith [sq_nonneg (x - 1)]⟩
  constructor
  · intro h
    have : (x + 2) * (x - 4) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num

/-- Stitz-Zeager Exercise 2.3.4: `-2(x+1)² + 4 = -2x² - 4x + 2`, with zeros `-1 ± √2` and maximum
value `4`. -/
@[kb "stitzzeager2013" "Exercise 2.3.4, p. 212"]
theorem exer_2_3_4 : (∀ x : ℝ, -2 * (x + 1) ^ 2 + 4 = -2 * x ^ 2 - 4 * x + 2) ∧
    (∀ x : ℝ, -2 * x ^ 2 - 4 * x + 2 = 0 ↔ x = -1 - √2 ∨ x = -1 + √2) ∧
    (∀ x : ℝ, -2 * x ^ 2 - 4 * x + 2 ≤ 4) := by
  refine ⟨fun x => by ring, fun x => ?_, fun x => by nlinarith [sq_nonneg (x + 1)]⟩
  have key : -2 * x ^ 2 - 4 * x + 2 = 0 ↔ (x + 1) ^ 2 = 2 := by
    constructor <;> intro h <;> nlinarith
  rw [key, aux_sq_eq_sqrt (x + 1) 2 (by norm_num)]
  constructor <;> rintro (h | h) <;> first | (left; linarith) | (right; linarith)

/-- Stitz-Zeager Exercise 2.3.5: `2x² - 4x - 1 = 2(x-1)² - 3`, with zeros `(2 ± √6)/2` and minimum
value `-3`. -/
@[kb "stitzzeager2013" "Exercise 2.3.5, p. 212"]
theorem exer_2_3_5 : (∀ x : ℝ, 2 * x ^ 2 - 4 * x - 1 = 2 * (x - 1) ^ 2 - 3) ∧
    (∀ x : ℝ, 2 * x ^ 2 - 4 * x - 1 = 0 ↔ x = (2 - √6) / 2 ∨ x = (2 + √6) / 2) ∧
    (∀ x : ℝ, -3 ≤ 2 * x ^ 2 - 4 * x - 1) := by
  refine ⟨fun x => by ring, fun x => ?_, fun x => by nlinarith [sq_nonneg (x - 1)]⟩
  have key : 2 * x ^ 2 - 4 * x - 1 = 0 ↔ (2 * x - 2) ^ 2 = 6 := by
    constructor <;> intro h <;> nlinarith
  rw [key, aux_sq_eq_sqrt (2 * x - 2) 6 (by norm_num)]
  constructor <;> rintro (h | h) <;> first | (left; linarith) | (right; linarith)

/-- Stitz-Zeager Exercise 2.3.6: `-3x² + 4x - 7 = -3(x - 2/3)² - 17/3` has no zeros, and its maximum
value is `-17/3` at `x = 2/3`. -/
@[kb "stitzzeager2013" "Exercise 2.3.6, p. 212"]
theorem exer_2_3_6 : (∀ x : ℝ, -3 * x ^ 2 + 4 * x - 7 = -3 * (x - 2 / 3) ^ 2 - 17 / 3) ∧
    (∀ x : ℝ, -3 * x ^ 2 + 4 * x - 7 ≠ 0) ∧ (∀ x : ℝ, -3 * x ^ 2 + 4 * x - 7 ≤ -17 / 3) ∧
    -3 * (2 / 3 : ℝ) ^ 2 + 4 * (2 / 3) - 7 = -17 / 3 := by
  refine ⟨fun x => by ring, fun x h => ?_, fun x => by nlinarith [sq_nonneg (x - 2 / 3)], by norm_num⟩
  nlinarith [sq_nonneg (x - 2 / 3)]

/-- Stitz-Zeager Exercise 2.3.7: `x² + x + 1 = (x + 1/2)² + 3/4` has no zeros and minimum value
`3/4` at `x = -1/2`. -/
@[kb "stitzzeager2013" "Exercise 2.3.7, p. 212"]
theorem exer_2_3_7 : (∀ x : ℝ, x ^ 2 + x + 1 = (x + 1 / 2) ^ 2 + 3 / 4) ∧
    (∀ x : ℝ, x ^ 2 + x + 1 ≠ 0) ∧ (∀ x : ℝ, 3 / 4 ≤ x ^ 2 + x + 1) ∧
    (-1 / 2 : ℝ) ^ 2 + (-1 / 2) + 1 = 3 / 4 := by
  refine ⟨fun x => by ring, fun x h => ?_, fun x => by nlinarith [sq_nonneg (x + 1 / 2)], by norm_num⟩
  nlinarith [sq_nonneg (x + 1 / 2)]

/-- Stitz-Zeager Exercise 2.3.8: `-3x² + 5x + 4 = -3(x - 5/6)² + 73/12`, with zeros `(5 ± √73)/6`
and maximum value `73/12` at `x = 5/6`. -/
@[kb "stitzzeager2013" "Exercise 2.3.8, p. 212"]
theorem exer_2_3_8 : (∀ x : ℝ, -3 * x ^ 2 + 5 * x + 4 = -3 * (x - 5 / 6) ^ 2 + 73 / 12) ∧
    (∀ x : ℝ, -3 * x ^ 2 + 5 * x + 4 = 0 ↔ x = (5 - √73) / 6 ∨ x = (5 + √73) / 6) ∧
    (∀ x : ℝ, -3 * x ^ 2 + 5 * x + 4 ≤ 73 / 12) := by
  refine ⟨fun x => by ring, fun x => ?_, fun x => by nlinarith [sq_nonneg (x - 5 / 6)]⟩
  have key : -3 * x ^ 2 + 5 * x + 4 = 0 ↔ (6 * x - 5) ^ 2 = 73 := by
    constructor <;> intro h <;> nlinarith
  rw [key, aux_sq_eq_sqrt (6 * x - 5) 73 (by norm_num)]
  constructor <;> rintro (h | h) <;> first | (left; linarith) | (right; linarith)

/-- Stitz-Zeager Exercise 2.3.10: with `C(x) = 2x + 26` and `p(x) = 30 - 2x`, the profit is
`-2x² + 28x - 26`, at most `72`, attained at `x = 7` (price `16`), with break-even points `1`, `13`. -/
@[kb "stitzzeager2013" "Exercise 2.3.10, p. 212"]
theorem exer_2_3_10 (P : ℝ → ℝ) (hP : ∀ x, P x = x * (30 - 2 * x) - (2 * x + 26)) :
    (∀ x, P x = -2 * x ^ 2 + 28 * x - 26) ∧ (∀ x, P x ≤ 72) ∧ P 7 = 72 ∧ (30 - 2 * 7 : ℝ) = 16 ∧
    (∀ x, P x = 0 ↔ x = 1 ∨ x = 13) := by
  refine ⟨fun x => by rw [hP]; ring, fun x => by rw [hP]; nlinarith [sq_nonneg (x - 7)],
    by rw [hP]; norm_num, by norm_num, fun x => ?_⟩
  rw [hP]
  constructor
  · intro h
    have : (x - 1) * (x - 13) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num

/-- Stitz-Zeager Exercise 2.3.11: with `C(x) = 10x + 100` and `p(x) = 35 - x`, the profit is
`-x² + 25x - 100`; among whole numbers of bottles the maximum profit is `56`, reached at `12` (price
`23`) and `13` (price `22`); break-even points are `5` and `20`. -/
@[kb "stitzzeager2013" "Exercise 2.3.11, p. 212"]
theorem exer_2_3_11 (P : ℝ → ℝ) (hP : ∀ x, P x = x * (35 - x) - (10 * x + 100)) :
    (∀ x, P x = -x ^ 2 + 25 * x - 100) ∧ (∀ n : ℤ, P n ≤ 56) ∧ P 12 = 56 ∧ P 13 = 56 ∧
    (35 - 12 : ℝ) = 23 ∧ (35 - 13 : ℝ) = 22 ∧ (∀ x, P x = 0 ↔ x = 5 ∨ x = 20) := by
  refine ⟨fun x => by rw [hP]; ring, fun n => ?_, by rw [hP]; norm_num, by rw [hP]; norm_num,
    by norm_num, by norm_num, fun x => ?_⟩
  · have h : (0 : ℤ) ≤ (n - 12) * (n - 13) := by
      rcases le_or_gt n 12 with h | h <;> nlinarith
    have h' : (0 : ℝ) ≤ ((n : ℝ) - 12) * ((n : ℝ) - 13) := by exact_mod_cast h
    rw [hP]; nlinarith
  · rw [hP]
    constructor
    · intro h
      have : (x - 5) * (x - 20) = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h | h
      · left; linarith
      · right; linarith
    · rintro (rfl | rfl) <;> norm_num

/-- Stitz-Zeager Exercise 2.3.12: with `C(x) = 18x + 240` and `p(x) = 90 - 3x`, the profit is
`-3x² + 72x - 240`, at most `192` at `x = 12` (price `54`), with break-even points `4` and `20`. -/
@[kb "stitzzeager2013" "Exercise 2.3.12, p. 212"]
theorem exer_2_3_12 (P : ℝ → ℝ) (hP : ∀ x, P x = x * (90 - 3 * x) - (18 * x + 240)) :
    (∀ x, P x = -3 * x ^ 2 + 72 * x - 240) ∧ (∀ x, P x ≤ 192) ∧ P 12 = 192 ∧ (90 - 3 * 12 : ℝ) = 54 ∧
    (∀ x, P x = 0 ↔ x = 4 ∨ x = 20) := by
  refine ⟨fun x => by rw [hP]; ring, fun x => by rw [hP]; nlinarith [sq_nonneg (x - 12)],
    by rw [hP]; norm_num, by norm_num, fun x => ?_⟩
  rw [hP]
  constructor
  · intro h
    have : (x - 4) * (x - 20) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num

/-- Stitz-Zeager Exercise 2.3.13: with `C(x) = 3x + 36` and `p(x) = 12 - x/2`, the profit is
`-x²/2 + 9x - 36`, at most `9/2` at `x = 9` (price `15/2`), with break-even points `6` and `12`. -/
@[kb "stitzzeager2013" "Exercise 2.3.13, p. 212"]
theorem exer_2_3_13 (P : ℝ → ℝ) (hP : ∀ x, P x = x * (12 - x / 2) - (3 * x + 36)) :
    (∀ x, P x = -(1 / 2) * x ^ 2 + 9 * x - 36) ∧ (∀ x, P x ≤ 9 / 2) ∧ P 9 = 9 / 2 ∧
    (12 - 9 / 2 : ℝ) = 15 / 2 ∧ (∀ x, P x = 0 ↔ x = 6 ∨ x = 12) := by
  refine ⟨fun x => by rw [hP]; ring, fun x => by rw [hP]; nlinarith [sq_nonneg (x - 9)],
    by rw [hP]; norm_num, by norm_num, fun x => ?_⟩
  rw [hP]
  constructor
  · intro h
    have : (x - 6) * (x - 12) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num

/-- Stitz-Zeager Exercise 2.3.14: with `C(x) = 20x + 1000` and `p(x) = 140 - 2x`, the profit is
`-2x² + 120x - 1000`, at most `800` at `x = 30` (price `80`), with break-even points `10`, `50`. -/
@[kb "stitzzeager2013" "Exercise 2.3.14, p. 212"]
theorem exer_2_3_14 (P : ℝ → ℝ) (hP : ∀ x, P x = x * (140 - 2 * x) - (20 * x + 1000)) :
    (∀ x, P x = -2 * x ^ 2 + 120 * x - 1000) ∧ (∀ x, P x ≤ 800) ∧ P 30 = 800 ∧
    (140 - 2 * 30 : ℝ) = 80 ∧ (∀ x, P x = 0 ↔ x = 10 ∨ x = 50) := by
  refine ⟨fun x => by rw [hP]; ring, fun x => by rw [hP]; nlinarith [sq_nonneg (x - 30)],
    by rw [hP]; norm_num, by norm_num, fun x => ?_⟩
  rw [hP]
  constructor
  · intro h
    have : (x - 10) * (x - 50) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num

/-- Stitz-Zeager Exercise 2.3.15: the profit `x(10 - 0.01x) - (0.1x + 25)` is maximized exactly at
`x = 495` cookies. -/
@[kb "stitzzeager2013" "Exercise 2.3.15, p. 213"]
theorem exer_2_3_15 (P : ℝ → ℝ) (hP : ∀ x, P x = x * (10 - x / 100) - (x / 10 + 25)) :
    ∀ x, P x ≤ P 495 ∧ (P x = P 495 ↔ x = 495) := by
  intro x
  rw [hP, hP]
  refine ⟨by nlinarith [sq_nonneg (x - 495)], ⟨fun h => ?_, fun h => by rw [h]⟩⟩
  have : (x - 495) ^ 2 = 0 := by nlinarith
  have := pow_eq_zero_iff (two_ne_zero) |>.1 this
  linarith

/-- Stitz-Zeager Exercise 2.3.17: `T(t) = -t²/2 + 8t + 32` is at most `64`, attained only at `t = 8`. -/
@[kb "stitzzeager2013" "Exercise 2.3.17, p. 213"]
theorem exer_2_3_17 (t : ℝ) :
    -(1 / 2) * t ^ 2 + 8 * t + 32 ≤ 64 ∧ (-(1 / 2) * t ^ 2 + 8 * t + 32 = 64 ↔ t = 8) := by
  refine ⟨by nlinarith [sq_nonneg (t - 8)], ⟨fun h => ?_, fun h => by rw [h]; norm_num⟩⟩
  have : (t - 8) ^ 2 = 0 := by nlinarith
  have := pow_eq_zero_iff (two_ne_zero) |>.1 this
  linarith

/-- Stitz-Zeager Exercise 2.3.18: `C(x) = x² - 10x + 27` is at least `2` (hundred dollars), attained
only at `x = 5` (thousand pens). -/
@[kb "stitzzeager2013" "Exercise 2.3.18, p. 213"]
theorem exer_2_3_18 (x : ℝ) :
    2 ≤ x ^ 2 - 10 * x + 27 ∧ (x ^ 2 - 10 * x + 27 = 2 ↔ x = 5) := by
  refine ⟨by nlinarith [sq_nonneg (x - 5)], ⟨fun h => ?_, fun h => by rw [h]; norm_num⟩⟩
  have : (x - 5) ^ 2 = 0 := by nlinarith
  have := pow_eq_zero_iff (two_ne_zero) |>.1 this
  linarith

/-- Stitz-Zeager Exercise 2.3.19: with `32` feet of fence and one side along the house, the area
`x(32 - 2x)` is at most `128`, attained only at `x = 8` (a `8` by `16` garden). -/
@[kb "stitzzeager2013" "Exercise 2.3.19, p. 213"]
theorem exer_2_3_19 (x : ℝ) :
    x * (32 - 2 * x) ≤ 128 ∧ (x * (32 - 2 * x) = 128 ↔ x = 8) ∧ (32 - 2 * 8 : ℝ) = 16 := by
  refine ⟨by nlinarith [sq_nonneg (x - 8)], ⟨fun h => ?_, fun h => by rw [h]; norm_num⟩, by norm_num⟩
  have : (x - 8) ^ 2 = 0 := by nlinarith
  have := pow_eq_zero_iff (two_ne_zero) |>.1 this
  linarith

/-- Stitz-Zeager Exercise 2.3.20: with `200` feet of fence on all four sides, the area `x(100 - x)`
is at most `2500`, attained only for the square `x = 50`; this gives `100` alpacas at `25` square
feet each. -/
@[kb "stitzzeager2013" "Exercise 2.3.20, p. 213"]
theorem exer_2_3_20 (x : ℝ) :
    x * (100 - x) ≤ 2500 ∧ (x * (100 - x) = 2500 ↔ x = 50) ∧ (2500 / 25 : ℝ) = 100 := by
  refine ⟨by nlinarith [sq_nonneg (x - 50)], ⟨fun h => ?_, fun h => by rw [h]; norm_num⟩, by norm_num⟩
  have : (x - 50) ^ 2 = 0 := by nlinarith
  have := pow_eq_zero_iff (two_ne_zero) |>.1 this
  linarith

/-- Stitz-Zeager Exercise 2.3.21: a rectangle with perimeter `14` has sides `x` and `7 - x` and area
at most `49/4 = 12.25`, attained at the square. -/
@[kb "stitzzeager2013" "Exercise 2.3.21, p. 213"]
theorem exer_2_3_21 (x : ℝ) : x * (7 - x) ≤ 49 / 4 ∧ (x * (7 - x) = 49 / 4 ↔ x = 7 / 2) := by
  refine ⟨by nlinarith [sq_nonneg (x - 7 / 2)], ⟨fun h => ?_, fun h => by rw [h]; norm_num⟩⟩
  have : (x - 7 / 2) ^ 2 = 0 := by nlinarith
  have := pow_eq_zero_iff (two_ne_zero) |>.1 this
  linarith

/-- Stitz-Zeager Exercise 2.3.22: for `t ≥ 0`, `h(t) = -16t² + 64` vanishes exactly at `t = 2`. -/
@[kb "stitzzeager2013" "Exercise 2.3.22, p. 213"]
theorem exer_2_3_22 (t : ℝ) (ht : 0 ≤ t) : -16 * t ^ 2 + 64 = 0 ↔ t = 2 := by
  constructor
  · intro h
    have : (t - 2) * (t + 2) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h <;> linarith
  · rintro rfl; norm_num

/-- Stitz-Zeager Exercise 2.3.23: the rocket height `-5t² + 100t` is at most `500`, attained only at
`t = 10`. -/
@[kb "stitzzeager2013" "Exercise 2.3.23, p. 213"]
theorem exer_2_3_23 (t : ℝ) :
    -5 * t ^ 2 + 100 * t ≤ 500 ∧ (-5 * t ^ 2 + 100 * t = 500 ↔ t = 10) := by
  refine ⟨by nlinarith [sq_nonneg (t - 10)], ⟨fun h => ?_, fun h => by rw [h]; norm_num⟩⟩
  have : (t - 10) ^ 2 = 0 := by nlinarith
  have := pow_eq_zero_iff (two_ne_zero) |>.1 this
  linarith

/-- Stitz-Zeager Exercise 2.3.24: the hammer height `-16t² + 22.08t + 6` is at most `13.6176`
(about `13.62`), attained at `t = 0.69`. -/
@[kb "stitzzeager2013" "Exercise 2.3.24, p. 213"]
theorem exer_2_3_24 (t : ℝ) :
    -16 * t ^ 2 + 2208 / 100 * t + 6 ≤ 136176 / 10000 ∧
      -16 * (69 / 100 : ℝ) ^ 2 + 2208 / 100 * (69 / 100) + 6 = 136176 / 10000 := by
  refine ⟨by nlinarith [sq_nonneg (t - 69 / 100)], by norm_num⟩

/-- Stitz-Zeager Exercise 2.3.26: the bridge cable `p(x) = a x² + 10` through `(200, 100)` has
`a = 9/4000`, and then `p(-150) = 485/8 = 60.625`. -/
@[kb "stitzzeager2013" "Exercise 2.3.26, p. 214"]
theorem exer_2_3_26 :
    (∀ a : ℝ, a * 200 ^ 2 + 10 = 100 ↔ a = 9 / 4000) ∧ (9 / 4000 : ℝ) * (-150) ^ 2 + 10 = 485 / 8 := by
  refine ⟨fun a => ⟨fun h => by linarith, fun h => by rw [h]; norm_num⟩, by norm_num⟩

/-- Stitz-Zeager Exercise 2.3.28: the points of `y = 1 - x` at distance `2` from `(1,-1)` are
`((3 - √7)/2, (-1 + √7)/2)` and `((3 + √7)/2, (-1 - √7)/2)`. -/
@[kb "stitzzeager2013" "Exercise 2.3.28, p. 214"]
theorem exer_2_3_28 (x y : ℝ) :
    (y = 1 - x ∧ (x - 1) ^ 2 + (y + 1) ^ 2 = 2 ^ 2) ↔
      ((x = (3 - √7) / 2 ∧ y = (-1 + √7) / 2) ∨ (x = (3 + √7) / 2 ∧ y = (-1 - √7) / 2)) := by
  have h7 := Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)
  constructor
  · rintro ⟨rfl, h⟩
    have key : (2 * x - 3) ^ 2 = 7 := by nlinarith
    rcases (aux_sq_eq_sqrt (2 * x - 3) 7 (by norm_num)).1 key with h | h
    · right; constructor <;> linarith
    · left; constructor <;> linarith
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> constructor <;> nlinarith

/-- Stitz-Zeager Exercise 2.3.29: the squared distance from `(x, 2x+1)` to the origin is
`5x² + 4x + 1`, minimized exactly at `x = -2/5`, giving the point `(-2/5, 1/5)`. -/
@[kb "stitzzeager2013" "Exercise 2.3.29, p. 214"]
theorem exer_2_3_29 (x : ℝ) :
    x ^ 2 + (2 * x + 1) ^ 2 = 5 * x ^ 2 + 4 * x + 1 ∧
      (5 * (-2 / 5 : ℝ) ^ 2 + 4 * (-2 / 5) + 1 ≤ 5 * x ^ 2 + 4 * x + 1) ∧
      (5 * x ^ 2 + 4 * x + 1 = 5 * (-2 / 5 : ℝ) ^ 2 + 4 * (-2 / 5) + 1 ↔ x = -2 / 5) ∧
      2 * (-2 / 5 : ℝ) + 1 = 1 / 5 := by
  refine ⟨by ring, by nlinarith [sq_nonneg (x + 2 / 5)], ⟨fun h => ?_, fun h => by rw [h]⟩,
    by norm_num⟩
  have : (x + 2 / 5) ^ 2 = 0 := by nlinarith
  have := pow_eq_zero_iff (two_ne_zero) |>.1 this
  linarith

/-- Stitz-Zeager Exercise 2.3.30: if `ax² + bx + c` has distinct zeros `r` and `s` (`a ≠ 0`), the
vertex abscissa `-b/(2a)` is their midpoint. -/
@[kb "stitzzeager2013" "Exercise 2.3.30, p. 214"]
theorem exer_2_3_30 (a b c r s : ℝ) (ha : a ≠ 0) (hrs : r ≠ s)
    (hr : a * r ^ 2 + b * r + c = 0) (hs : a * s ^ 2 + b * s + c = 0) :
    -b / (2 * a) = (r + s) / 2 := by
  have h1 : (r - s) * (a * (r + s) + b) = 0 := by linear_combination hr - hs
  have h2 : a * (r + s) + b = 0 := by
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (sub_eq_zero.1 h) hrs
    · exact h
  field_simp
  linarith

/-- Stitz-Zeager Exercise 2.3.31-32, 35: `x² - 10y² = 0` iff `x = ±y√10`; and
`y² - 4y = x² - 4` iff `x = ±(y - 2)`, iff `y = 2 ± x`. -/
@[kb "stitzzeager2013" "Exercise 2.3.31, p. 214"]
theorem exer_2_3_31 (x y : ℝ) :
    (x ^ 2 - 10 * y ^ 2 = 0 ↔ x = y * √10 ∨ x = -(y * √10)) ∧
    (y ^ 2 - 4 * y = x ^ 2 - 4 ↔ x = y - 2 ∨ x = -(y - 2)) ∧
    (y ^ 2 - 4 * y = x ^ 2 - 4 ↔ y = 2 + x ∨ y = 2 - x) := by
  have h10 := Real.sq_sqrt (show (0 : ℝ) ≤ 10 by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro h
      have : (x - y * √10) * (x + y * √10) = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h | h
      · left; linarith
      · right; linarith
    · rintro (h | h) <;> rw [h] <;> nlinarith
  · constructor
    · intro h
      have : (x - (y - 2)) * (x + (y - 2)) = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h | h
      · left; linarith
      · right; linarith
    · rintro (h | h) <;> rw [h] <;> ring
  · constructor
    · intro h
      have : (y - 2 - x) * (y - 2 + x) = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h | h
      · left; linarith
      · right; linarith
    · rintro (h | h) <;> rw [h] <;> ring

/-- Stitz-Zeager Exercise 2.3.33: `x² - mx = 1` iff `x = (m ± √(m² + 4))/2`. -/
@[kb "stitzzeager2013" "Exercise 2.3.33, p. 214"]
theorem exer_2_3_33 (m x : ℝ) :
    x ^ 2 - m * x = 1 ↔ x = (m + √(m ^ 2 + 4)) / 2 ∨ x = (m - √(m ^ 2 + 4)) / 2 := by
  have hc : 0 ≤ m ^ 2 + 4 := by positivity
  have key : x ^ 2 - m * x = 1 ↔ (2 * x - m) ^ 2 = m ^ 2 + 4 := by
    constructor <;> intro h <;> nlinarith
  rw [key, aux_sq_eq_sqrt _ _ hc]
  constructor <;> rintro (h | h) <;> first | (left; linarith) | (right; linarith)

/-- Stitz-Zeager Exercise 2.3.34: for `16x + 9 ≥ 0`, `y² - 3y = 4x` iff `y = (3 ± √(16x + 9))/2`. -/
@[kb "stitzzeager2013" "Exercise 2.3.34, p. 214"]
theorem exer_2_3_34 (x y : ℝ) (hx : 0 ≤ 16 * x + 9) :
    y ^ 2 - 3 * y = 4 * x ↔ y = (3 + √(16 * x + 9)) / 2 ∨ y = (3 - √(16 * x + 9)) / 2 := by
  have key : y ^ 2 - 3 * y = 4 * x ↔ (2 * y - 3) ^ 2 = 16 * x + 9 := by
    constructor <;> intro h <;> nlinarith
  rw [key, aux_sq_eq_sqrt _ _ hx]
  constructor <;> rintro (h | h) <;> first | (left; linarith) | (right; linarith)

/-- Stitz-Zeager Exercise 2.3.36: for `g ≠ 0` and `v₀² + 4 g s₀ ≥ 0`, `-gt² + v₀t + s₀ = 0` iff
`t = (v₀ ± √(v₀² + 4 g s₀))/(2g)`. -/
@[kb "stitzzeager2013" "Exercise 2.3.36, p. 214"]
theorem exer_2_3_36 (g v₀ s₀ t : ℝ) (hg : g ≠ 0) (hd : 0 ≤ v₀ ^ 2 + 4 * g * s₀) :
    -g * t ^ 2 + v₀ * t + s₀ = 0 ↔
      t = (v₀ + √(v₀ ^ 2 + 4 * g * s₀)) / (2 * g) ∨ t = (v₀ - √(v₀ ^ 2 + 4 * g * s₀)) / (2 * g) := by
  have h2 : (2 * g) ≠ 0 := mul_ne_zero two_ne_zero hg
  have key : -g * t ^ 2 + v₀ * t + s₀ = 0 ↔ (2 * g * t - v₀) ^ 2 = v₀ ^ 2 + 4 * g * s₀ := by
    constructor
    · intro h; linear_combination (-4 * g) * h
    · intro h
      have : 4 * g * (-g * t ^ 2 + v₀ * t + s₀) = 0 := by linear_combination (-1) * h
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (mul_ne_zero four_ne_zero hg)
      · exact h
  rw [key, aux_sq_eq_sqrt _ _ hd, eq_div_iff h2, eq_div_iff h2]
  constructor <;> rintro (h | h) <;> first | (left; linarith) | (right; linarith)

end UndergradKB.Precalculus.Course
