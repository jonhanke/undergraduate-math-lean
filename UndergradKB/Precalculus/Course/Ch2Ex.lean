import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Interval.Set.Basic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 2 (Stitz-Zeager): worked examples -/

namespace UndergradKB.Precalculus.Course

open Set

/-! ## Section 2.1 -/

/-- Stitz-Zeager Example 2.1.1: slopes of the lines through four of the listed pairs of points
(`(0,0),(2,4)`; `(-1,2),(3,4)`; `(-2,3),(2,-3)`; `(-3,2),(4,2)`) are `2`, `1/2`, `-3/2`, `0`. -/
@[kb "stitzzeager2013" "Example 2.1.1, p. 163"]
theorem ex_2_1_1_slopes :
    ((4 : ℝ) - 0) / (2 - 0) = 2 ∧ ((4 : ℝ) - 2) / (3 - (-1)) = 1 / 2 ∧
      ((-3 : ℝ) - 3) / (2 - (-2)) = -3 / 2 ∧ ((2 : ℝ) - 2) / (4 - (-3)) = 0 := by
  norm_num

/-- Stitz-Zeager Example 2.1.1(6): the slope through `(2,3)` and `(2.1,-1)` is `-40`. -/
@[kb "stitzzeager2013" "Example 2.1.1, p. 163"]
theorem ex_2_1_1_f_steep_slope : ((-1 : ℝ) - 3) / (21 / 10 - 2) = -40 := by norm_num

/-- Stitz-Zeager Example 2.1.2: the temperature readings `(6,24)`, `(10,32)` give slope `2`, and the
line predicts `36` at noon. -/
@[kb "stitzzeager2013" "Example 2.1.2, p. 166"]
theorem ex_2_1_2_temperature :
    ((32 : ℝ) - 24) / (10 - 6) = 2 ∧ (32 : ℝ) + 2 * (12 - 10) = 36 := by
  norm_num

/-- Stitz-Zeager Example 2.1.4(3): `(3 - 2x)/4` is the linear function with slope `-1/2` and
`y`-intercept `3/4`. -/
@[kb "stitzzeager2013" "Example 2.1.4, p. 168"]
theorem ex_2_1_4_c_linear_form (x : ℝ) : (3 - 2 * x) / 4 = (-1 / 2) * x + 3 / 4 := by ring

/-- Stitz-Zeager Example 2.1.4(4): away from `x = 2`, `(x²-4)/(x-2)` equals `x + 2`. -/
@[kb "stitzzeager2013" "Example 2.1.4, p. 168"]
theorem ex_2_1_4_d_cancel (x : ℝ) (hx : x ≠ 2) : (x ^ 2 - 4) / (x - 2) = x + 2 := by
  have : x - 2 ≠ 0 := sub_ne_zero.mpr hx
  field_simp; ring

/-- Stitz-Zeager Example 2.1.4: `(2x²+2)/(x²+1)` is the constant function `2` on all of `ℝ`. -/
@[kb "stitzzeager2013" "Example 2.1.4, p. 168"]
theorem ex_2_1_4_constant_function (x : ℝ) : (2 * x ^ 2 + 2) / (x ^ 2 + 1) = 2 := by
  have : x ^ 2 + 1 ≠ 0 := by positivity
  rw [div_eq_iff this]; ring

/-- Stitz-Zeager Example 2.1.5(1,4): for the cost `C x = 80x + 150`, `C 10 = 950` and `C 0 = 150`. -/
@[kb "stitzzeager2013" "Example 2.1.5, p. 170"]
theorem ex_2_1_5_cost_values : (80 * (10 : ℝ) + 150 = 950) ∧ (80 * (0 : ℝ) + 150 = 150) := by
  norm_num

/-- Stitz-Zeager Example 2.1.5(2): with `$15000`, the cost `80x + 150` is affordable exactly when
`x = 1485/8 = 185.625` is not exceeded, so at most `185` whole systems can be made. -/
@[kb "stitzzeager2013" "Example 2.1.5, p. 170"]
theorem ex_2_1_5_b_how_many :
    (80 * (1485 / 8 : ℝ) + 150 = 15000) ∧ ∀ n : ℕ, 80 * (n : ℝ) + 150 ≤ 15000 ↔ n ≤ 185 := by
  refine ⟨by norm_num, fun n => ?_⟩
  constructor
  · intro h
    have : (n : ℝ) < 186 := by linarith
    exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
  · intro h
    have : (n : ℝ) ≤ 185 := by exact_mod_cast h
    linarith

/-- Stitz-Zeager Example 2.1.5(5): the cost line `80x + 150` has slope `80` (the variable cost per item). -/
@[kb "stitzzeager2013" "Example 2.1.5, p. 170"]
theorem ex_2_1_5_e_slope (a b : ℝ) (hab : a ≠ b) :
    ((80 * b + 150) - (80 * a + 150)) / (b - a) = 80 := by
  have : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  field_simp; ring

/-- Stitz-Zeager Example 2.1.6(1): the only line `p = m x + b` with `p 20 = 220` and `p 40 = 190`
is `p = -1.5 x + 250`. -/
@[kb "stitzzeager2013" "Example 2.1.6, p. 171"]
theorem ex_2_1_6_a_demand_line (m b : ℝ) :
    (m * 20 + b = 220 ∧ m * 40 + b = 190) ↔ (m = -3 / 2 ∧ b = 250) := by
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; norm_num

/-- Stitz-Zeager Example 2.1.6(4,5): `p 150 = 25`, and the price `150` is reached exactly at `x = 200/3`
(about `66.7`, so `66` whole systems). -/
@[kb "stitzzeager2013" "Example 2.1.6, p. 171"]
theorem ex_2_1_6_d_price_and_sales (x : ℝ) :
    (-3 / 2 * (150 : ℝ) + 250 = 25) ∧ (-3 / 2 * x + 250 = 150 ↔ x = 200 / 3) := by
  refine ⟨by norm_num, ?_⟩
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Example 2.1.6(2): the price `-1.5x + 250` is nonnegative exactly for `x ≤ 500/3`. -/
@[kb "stitzzeager2013" "Example 2.1.6, p. 171"]
theorem ex_2_1_6_b_applied_domain (x : ℝ) : 0 ≤ -3 / 2 * x + 250 ↔ x ≤ 500 / 3 := by
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Example 2.1.7(1): revenue is `x * (-1.5x + 250) = -1.5x² + 250x`. -/
@[kb "stitzzeager2013" "Example 2.1.7, p. 173"]
theorem ex_2_1_7_a_revenue (x : ℝ) : x * (-3 / 2 * x + 250) = -3 / 2 * x ^ 2 + 250 * x := by ring

/-- Stitz-Zeager Example 2.1.7(2-4): average rates of change of `R x = -1.5x² + 250x` are
`175` on `[0,50]`, `25` on `[50,100]` and `-125` on `[100,150]`. -/
@[kb "stitzzeager2013" "Example 2.1.7, p. 173"]
theorem ex_2_1_7_b_average_rates :
    let R : ℝ → ℝ := fun x => -3 / 2 * x ^ 2 + 250 * x
    (R 50 - R 0) / (50 - 0) = 175 ∧ (R 100 - R 50) / (100 - 50) = 25 ∧
      (R 150 - R 100) / (150 - 100) = -125 := by
  intro R
  simp only [R]; norm_num

/-! ## Section 2.2 -/

/-- Stitz-Zeager Example 2.2.1(1): `|3x - 1| = 6` iff `x = 7/3` or `x = -5/3`. -/
@[kb "stitzzeager2013" "Example 2.2.1, p. 186"]
theorem ex_2_2_1_a (x : ℝ) : |3 * x - 1| = 6 ↔ x = 7 / 3 ∨ x = -5 / 3 := by
  rw [abs_eq (by norm_num)]
  constructor <;> rintro (h | h) <;> [left; right; left; right] <;> linarith

/-- Stitz-Zeager Example 2.2.1(2): `3 - |x + 5| = 1` iff `x = -3` or `x = -7`. -/
@[kb "stitzzeager2013" "Example 2.2.1, p. 186"]
theorem ex_2_2_1_b (x : ℝ) : 3 - |x + 5| = 1 ↔ x = -3 ∨ x = -7 := by
  have : 3 - |x + 5| = 1 ↔ |x + 5| = 2 := by constructor <;> intro h <;> linarith
  rw [this, abs_eq (by norm_num)]
  constructor <;> rintro (h | h) <;> [left; right; left; right] <;> linarith

/-- Stitz-Zeager Example 2.2.1(3): `3|2x + 1| - 5 = 0` iff `x = 1/3` or `x = -4/3`. -/
@[kb "stitzzeager2013" "Example 2.2.1, p. 186"]
theorem ex_2_2_1_c (x : ℝ) : 3 * |2 * x + 1| - 5 = 0 ↔ x = 1 / 3 ∨ x = -4 / 3 := by
  have : 3 * |2 * x + 1| - 5 = 0 ↔ |2 * x + 1| = 5 / 3 := by
    constructor <;> intro h <;> linarith
  rw [this, abs_eq (by norm_num)]
  constructor <;> rintro (h | h) <;> [left; right; left; right] <;> linarith

/-- Stitz-Zeager Example 2.2.1(4): `4 - |5x + 3| = 5` has no real solution. -/
@[kb "stitzzeager2013" "Example 2.2.1, p. 186"]
theorem ex_2_2_1_d (x : ℝ) : 4 - |5 * x + 3| ≠ 5 := by
  have := abs_nonneg (5 * x + 3)
  intro h; linarith

/-- Stitz-Zeager Example 2.2.1(5): `|x| = x² - 6` iff `x = 3` or `x = -3`. -/
@[kb "stitzzeager2013" "Example 2.2.1, p. 186"]
theorem ex_2_2_1_e (x : ℝ) : |x| = x ^ 2 - 6 ↔ x = 3 ∨ x = -3 := by
  constructor
  · intro h
    rcases le_or_gt 0 x with hx | hx
    · rw [abs_of_nonneg hx] at h
      have : (x - 3) * (x + 2) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h' | h'
      · left; linarith
      · exfalso; linarith
    · rw [abs_of_neg hx] at h
      have : (x + 3) * (x - 2) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h' | h'
      · right; linarith
      · exfalso; linarith
  · rintro (h | h) <;> subst h <;> norm_num

/-- Stitz-Zeager Example 2.2.1(6): `|x - 2| + 1 = x` iff `x = 3/2`. -/
@[kb "stitzzeager2013" "Example 2.2.1, p. 186"]
theorem ex_2_2_1_f (x : ℝ) : |x - 2| + 1 = x ↔ x = 3 / 2 := by
  constructor
  · intro h
    rcases le_or_gt 0 (x - 2) with hx | hx
    · rw [abs_of_nonneg hx] at h; linarith
    · rw [abs_of_neg hx] at h; linarith
  · rintro rfl
    rw [abs_of_neg (by norm_num)]; norm_num

/-- Stitz-Zeager Example 2.2.4(1): `|x|/x` has no zero, equals `-1` for `x < 0` and `1` for `x > 0`,
and takes exactly the values `-1` and `1`. -/
@[kb "stitzzeager2013" "Example 2.2.4, p. 192"]
theorem ex_2_2_4_a_sign_function :
    (∀ x : ℝ, x ≠ 0 → |x| / x ≠ 0) ∧ (∀ x : ℝ, x < 0 → |x| / x = -1) ∧
      (∀ x : ℝ, 0 < x → |x| / x = 1) ∧ {y : ℝ | ∃ x : ℝ, x ≠ 0 ∧ |x| / x = y} = {-1, 1} := by
  refine ⟨fun x hx => by simp [hx], fun x hx => ?_, fun x hx => ?_, ?_⟩
  · rw [abs_of_neg hx, neg_div, div_self hx.ne]
  · rw [abs_of_pos hx, div_self hx.ne']
  · ext y
    simp only [mem_setOf_eq, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases lt_or_gt_of_ne hx with h | h
      · left; rw [abs_of_neg h, neg_div, div_self h.ne]
      · right; rw [abs_of_pos h, div_self h.ne']
    · rintro (rfl | rfl)
      · exact ⟨-1, by norm_num, by norm_num⟩
      · exact ⟨1, by norm_num, by norm_num⟩

/-- Stitz-Zeager Example 2.2.4(2): `|x+2| - |x-3| + 1` equals `-4` for `x < -2`, `2x` for `-2 ≤ x < 3`
and `6` for `x ≥ 3`. -/
@[kb "stitzzeager2013" "Example 2.2.4, p. 192"]
theorem ex_2_2_4_b_pieces (x : ℝ) :
    |x + 2| - |x - 3| + 1 = if x < -2 then -4 else if x < 3 then 2 * x else 6 := by
  by_cases h1 : x < -2
  · rw [if_pos h1, abs_of_neg (by linarith), abs_of_neg (by linarith)]; ring
  · by_cases h2 : x < 3
    · rw [if_neg h1, if_pos h2, abs_of_nonneg (by linarith), abs_of_neg (by linarith)]; ring
    · rw [if_neg h1, if_neg h2, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; ring

/-- Stitz-Zeager Example 2.2.4(2): the only zero of `|x+2| - |x-3| + 1` is `0`, and its range is `[-4,6]`. -/
@[kb "stitzzeager2013" "Example 2.2.4, p. 192"]
theorem ex_2_2_4_b_zero_and_range :
    (∀ x : ℝ, |x + 2| - |x - 3| + 1 = 0 ↔ x = 0) ∧
      range (fun x : ℝ => |x + 2| - |x - 3| + 1) = Icc (-4) 6 := by
  constructor
  · intro x
    rw [ex_2_2_4_b_pieces]
    by_cases h1 : x < -2
    · rw [if_pos h1]; constructor <;> intro h <;> [norm_num at h; (exfalso; linarith)]
    · by_cases h2 : x < 3
      · rw [if_neg h1, if_pos h2]; constructor <;> intro h <;> linarith
      · rw [if_neg h1, if_neg h2]; constructor <;> intro h <;> [norm_num at h; (exfalso; linarith)]
  · ext y
    simp only [mem_range, mem_Icc]
    constructor
    · rintro ⟨x, rfl⟩
      rw [ex_2_2_4_b_pieces]
      by_cases h1 : x < -2
      · rw [if_pos h1]; norm_num
      · by_cases h2 : x < 3
        · rw [if_neg h1, if_pos h2]; constructor <;> linarith [not_lt.mp h1]
        · rw [if_neg h1, if_neg h2]; norm_num
    · rintro ⟨h1, h2⟩
      refine ⟨if y < 6 then y / 2 else 3, ?_⟩
      rw [ex_2_2_4_b_pieces]
      by_cases h : y < 6
      · rw [if_pos h, if_neg (by linarith), if_pos (by linarith)]; ring
      · rw [if_neg h, if_neg (by norm_num), if_neg (by norm_num)]; linarith [not_lt.mp h]

/-! ## Section 2.3 -/

/-- Stitz-Zeager Example 2.3.1(1): `(x+2)² - 3` has zeros `-2 ± √3`, value `1` at `0`, and range `[-3,∞)`. -/
@[kb "stitzzeager2013" "Example 2.3.1, p. 200"]
theorem ex_2_3_1_a_shifted_parabola :
    (∀ x : ℝ, (x + 2) ^ 2 - 3 = 0 ↔ x = -2 + Real.sqrt 3 ∨ x = -2 - Real.sqrt 3) ∧
      ((0 : ℝ) + 2) ^ 2 - 3 = 1 ∧ range (fun x : ℝ => (x + 2) ^ 2 - 3) = Ici (-3) := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine ⟨fun x => ?_, by norm_num, ?_⟩
  · constructor
    · intro h
      have : (x + 2 - Real.sqrt 3) * (x + 2 + Real.sqrt 3) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h' | h'
      · left; linarith
      · right; linarith
    · rintro (h | h) <;> subst h <;> nlinarith
  · ext y
    simp only [mem_range, mem_Ici]
    constructor
    · rintro ⟨x, rfl⟩; nlinarith [sq_nonneg (x + 2)]
    · intro hy
      refine ⟨Real.sqrt (y + 3) - 2, ?_⟩
      have := Real.sq_sqrt (show 0 ≤ y + 3 by linarith)
      nlinarith

/-- Stitz-Zeager Example 2.3.1(2): `-2(x-3)² + 1` has zeros `3 ± √2/2`, value `-17` at `0`, and range `(-∞,1]`. -/
@[kb "stitzzeager2013" "Example 2.3.1, p. 200"]
theorem ex_2_3_1_b_reflected_parabola :
    (∀ x : ℝ, -2 * (x - 3) ^ 2 + 1 = 0 ↔ x = 3 + Real.sqrt 2 / 2 ∨ x = 3 - Real.sqrt 2 / 2) ∧
      -2 * ((0 : ℝ) - 3) ^ 2 + 1 = -17 ∧ range (fun x : ℝ => -2 * (x - 3) ^ 2 + 1) = Iic 1 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  refine ⟨fun x => ?_, by norm_num, ?_⟩
  · constructor
    · intro h
      have : (x - 3 - Real.sqrt 2 / 2) * (x - 3 + Real.sqrt 2 / 2) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h' | h'
      · left; linarith
      · right; linarith
    · rintro (h | h) <;> subst h <;> nlinarith
  · ext y
    simp only [mem_range, mem_Iic]
    constructor
    · rintro ⟨x, rfl⟩; nlinarith [sq_nonneg (x - 3)]
    · intro hy
      refine ⟨3 + Real.sqrt ((1 - y) / 2), ?_⟩
      have := Real.sq_sqrt (show 0 ≤ (1 - y) / 2 by linarith)
      nlinarith

/-- Stitz-Zeager Example 2.3.2(1): `x² - 4x + 3 = (x-2)² - 1`, zeros `1` and `3`, value `3` at `0`,
range `[-1,∞)`. -/
@[kb "stitzzeager2013" "Example 2.3.2, p. 203"]
theorem ex_2_3_2_a_complete_square :
    (∀ x : ℝ, x ^ 2 - 4 * x + 3 = (x - 2) ^ 2 - 1) ∧
      (∀ x : ℝ, x ^ 2 - 4 * x + 3 = 0 ↔ x = 1 ∨ x = 3) ∧
      ((0 : ℝ) ^ 2 - 4 * 0 + 3 = 3) ∧ range (fun x : ℝ => x ^ 2 - 4 * x + 3) = Ici (-1) := by
  refine ⟨fun x => by ring, fun x => ?_, by norm_num, ?_⟩
  · constructor
    · intro h
      have : (x - 1) * (x - 3) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h' | h'
      · left; linarith
      · right; linarith
    · rintro (h | h) <;> subst h <;> norm_num
  · ext y
    simp only [mem_range, mem_Ici]
    constructor
    · rintro ⟨x, rfl⟩; nlinarith [sq_nonneg (x - 2)]
    · intro hy
      refine ⟨2 + Real.sqrt (y + 1), ?_⟩
      have := Real.sq_sqrt (show 0 ≤ y + 1 by linarith)
      nlinarith

/-- Stitz-Zeager Example 2.3.2(2): `6 - x - x² = -(x + 1/2)² + 25/4`, zeros `-3` and `2`, value `6` at `0`,
range `(-∞, 25/4]`. -/
@[kb "stitzzeager2013" "Example 2.3.2, p. 203"]
theorem ex_2_3_2_b_complete_square :
    (∀ x : ℝ, 6 - x - x ^ 2 = -(x + 1 / 2) ^ 2 + 25 / 4) ∧
      (∀ x : ℝ, 6 - x - x ^ 2 = 0 ↔ x = -3 ∨ x = 2) ∧
      ((6 : ℝ) - 0 - 0 ^ 2 = 6) ∧ range (fun x : ℝ => 6 - x - x ^ 2) = Iic (25 / 4) := by
  refine ⟨fun x => by ring, fun x => ?_, by norm_num, ?_⟩
  · constructor
    · intro h
      have : (x + 3) * (x - 2) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h' | h'
      · left; linarith
      · right; linarith
    · rintro (h | h) <;> subst h <;> norm_num
  · ext y
    simp only [mem_range, mem_Iic]
    constructor
    · rintro ⟨x, rfl⟩; nlinarith [sq_nonneg (x + 1 / 2)]
    · intro hy
      refine ⟨-1 / 2 + Real.sqrt (25 / 4 - y), ?_⟩
      have := Real.sq_sqrt (show 0 ≤ 25 / 4 - y by linarith)
      nlinarith

/-- Stitz-Zeager Example 2.3.3(1): profit `R - C` for `R x = -1.5x² + 250x`, `C x = 80x + 150` is
`-1.5x² + 170x - 150`. -/
@[kb "stitzzeager2013" "Example 2.3.3, p. 208"]
theorem ex_2_3_3_a_profit (x : ℝ) :
    (-3 / 2 * x ^ 2 + 250 * x) - (80 * x + 150) = -3 / 2 * x ^ 2 + 170 * x - 150 := by ring

/-- Stitz-Zeager Example 2.3.3(2): the profit `-1.5x² + 170x - 150` vanishes exactly at
`x = (170 ± 20√70)/3`, and equals `-150` at `0`. -/
@[kb "stitzzeager2013" "Example 2.3.3, p. 208"]
theorem ex_2_3_3_b_zeros (x : ℝ) :
    -3 / 2 * x ^ 2 + 170 * x - 150 = 0 ↔
      x = (170 + 20 * Real.sqrt 70) / 3 ∨ x = (170 - 20 * Real.sqrt 70) / 3 := by
  have h : Real.sqrt 70 ^ 2 = 70 := Real.sq_sqrt (by norm_num)
  constructor
  · intro h0
    have : (x - (170 + 20 * Real.sqrt 70) / 3) * (x - (170 - 20 * Real.sqrt 70) / 3) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp this with h' | h'
    · left; linarith
    · right; linarith
  · rintro (h' | h') <;> subst h' <;> nlinarith

/-- Stitz-Zeager Example 2.3.3(2): the profit parabola has vertex `(170/3, 14000/3)`, so `P x ≤ 14000/3`
with equality at `x = 170/3`. -/
@[kb "stitzzeager2013" "Example 2.3.3, p. 208"]
theorem ex_2_3_3_c_vertex :
    (-3 / 2 * (170 / 3 : ℝ) ^ 2 + 170 * (170 / 3) - 150 = 14000 / 3) ∧
      ∀ x : ℝ, -3 / 2 * x ^ 2 + 170 * x - 150 ≤ 14000 / 3 := by
  refine ⟨by norm_num, fun x => ?_⟩
  nlinarith [sq_nonneg (x - 170 / 3)]

/-- Stitz-Zeager Example 2.3.3(4,5): among whole numbers of systems, the profit is greatest at `57`
(`P 56 = 4666`, `P 57 = 4666.5`), and the matching price is `p 57 = 164.5`. -/
@[kb "stitzzeager2013" "Example 2.3.3, p. 208"]
theorem ex_2_3_3_d_best_integer :
    (-3 / 2 * (56 : ℝ) ^ 2 + 170 * 56 - 150 = 4666) ∧
      (-3 / 2 * (57 : ℝ) ^ 2 + 170 * 57 - 150 = 4666.5) ∧
      (∀ n : ℤ, -3 / 2 * (n : ℝ) ^ 2 + 170 * n - 150 ≤ 4666.5) ∧
      (-3 / 2 * (57 : ℝ) + 250 = 164.5) := by
  refine ⟨by norm_num, by norm_num, fun n => ?_, by norm_num⟩
  rcases le_or_gt n 56 with h | h
  · have : (n : ℝ) ≤ 56 := by exact_mod_cast h
    nlinarith
  · have : (n : ℝ) ≥ 57 := by exact_mod_cast h
    nlinarith

/-- Stitz-Zeager Example 2.3.4: the pasture area `w (200 - 2w) = 200w - 2w²` is at most `5000`,
with equality at `w = 50` (length `100`), and `5000/25 = 200` alpaca fit. -/
@[kb "stitzzeager2013" "Example 2.3.4, p. 209"]
theorem ex_2_3_4_pasture :
    (∀ w : ℝ, w * (200 - 2 * w) = 200 * w - 2 * w ^ 2) ∧
      (∀ w : ℝ, 200 * w - 2 * w ^ 2 ≤ 5000) ∧ (200 * (50 : ℝ) - 2 * 50 ^ 2 = 5000) ∧
      ((200 : ℝ) - 2 * 50 = 100) ∧ ((5000 : ℝ) / 25 = 200) := by
  refine ⟨fun w => by ring, fun w => ?_, by norm_num, by norm_num, by norm_num⟩
  nlinarith [sq_nonneg (w - 50)]

/-- Stitz-Zeager Example 2.3.5: `|x² - x - 6|` equals `-(x²-x-6)` for `-2 < x < 3` and `x²-x-6`
otherwise; its inner parabola has zeros `-2, 3`, value `-6` at `0` and minimum `-25/4` at `1/2`. -/
@[kb "stitzzeager2013" "Example 2.3.5, p. 210"]
theorem ex_2_3_5_abs_of_quadratic :
    (∀ x : ℝ, |x ^ 2 - x - 6| = if -2 < x ∧ x < 3 then -(x ^ 2 - x - 6) else x ^ 2 - x - 6) ∧
      (∀ x : ℝ, x ^ 2 - x - 6 = 0 ↔ x = -2 ∨ x = 3) ∧
      ((1 / 2 : ℝ) ^ 2 - 1 / 2 - 6 = -25 / 4) ∧ (∀ x : ℝ, -25 / 4 ≤ x ^ 2 - x - 6) := by
  refine ⟨fun x => ?_, fun x => ?_, by norm_num, fun x => by nlinarith [sq_nonneg (x - 1 / 2)]⟩
  · by_cases h : -2 < x ∧ x < 3
    · rw [if_pos h, abs_of_neg (by nlinarith [h.1, h.2])]
    · rw [if_neg h, abs_of_nonneg]
      by_contra hneg
      apply h
      push_neg at hneg
      constructor <;> nlinarith
  · constructor
    · intro h
      have : (x + 2) * (x - 3) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h' | h'
      · left; linarith
      · right; linarith
    · rintro (h | h) <;> subst h <;> norm_num

/-! ## Section 2.4 -/

/-- Stitz-Zeager Example 2.4.1: for `f x = 2x - 1` and `g x = 5`, `f = g` at `x = 3`, `f < g` for `x < 3`,
`f > g` for `x > 3`. -/
@[kb "stitzzeager2013" "Example 2.4.1, p. 220"]
theorem ex_2_4_1_linear_vs_constant :
    {x : ℝ | 2 * x - 1 = 5} = {3} ∧ {x : ℝ | 2 * x - 1 < 5} = Iio 3 ∧
      {x : ℝ | 2 * x - 1 > 5} = Ioi 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> ext x <;> simp <;> constructor <;> intro h <;> linarith

/-- Stitz-Zeager Example 2.4.3(1): `|x - 1| ≥ 3` is `(-∞,-2] ∪ [4,∞)`. -/
@[kb "stitzzeager2013" "Example 2.4.3, p. 223"]
theorem ex_2_4_3_a : {x : ℝ | |x - 1| ≥ 3} = Iic (-2) ∪ Ici 4 := by
  ext x
  simp only [mem_setOf_eq, mem_union, mem_Iic, mem_Ici, ge_iff_le]
  rw [le_abs']
  constructor <;> rintro (h | h) <;> [left; right; left; right] <;> linarith

/-- Stitz-Zeager Example 2.4.3(2): `4 - 3|2x + 1| > -2` is `(-3/2, 1/2)`. -/
@[kb "stitzzeager2013" "Example 2.4.3, p. 223"]
theorem ex_2_4_3_b : {x : ℝ | 4 - 3 * |2 * x + 1| > -2} = Ioo (-3 / 2) (1 / 2) := by
  ext x
  simp only [mem_setOf_eq, mem_Ioo, gt_iff_lt]
  have : -2 < 4 - 3 * |2 * x + 1| ↔ |2 * x + 1| < 2 := by constructor <;> intro h <;> linarith
  rw [this, abs_lt]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- Stitz-Zeager Example 2.4.3(3): `2 < |x - 1| ≤ 5` is `[-4,-1) ∪ (3,6]`. -/
@[kb "stitzzeager2013" "Example 2.4.3, p. 223"]
theorem ex_2_4_3_c : {x : ℝ | 2 < |x - 1| ∧ |x - 1| ≤ 5} = Ico (-4) (-1) ∪ Ioc 3 6 := by
  ext x
  simp only [mem_setOf_eq, mem_union, mem_Ico, mem_Ioc, abs_le, lt_abs]
  constructor
  · rintro ⟨h | h, h1, h2⟩
    · right; constructor <;> linarith
    · left; constructor <;> linarith
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨Or.inr (by linarith), by constructor <;> linarith⟩
    · exact ⟨Or.inl (by linarith), by constructor <;> linarith⟩

/-- Stitz-Zeager Example 2.4.3(4): `|x + 1| ≥ (x + 4)/2` is `(-∞,-2] ∪ [2,∞)`. -/
@[kb "stitzzeager2013" "Example 2.4.3, p. 223"]
theorem ex_2_4_3_d : {x : ℝ | |x + 1| ≥ (x + 4) / 2} = Iic (-2) ∪ Ici 2 := by
  ext x
  simp only [mem_setOf_eq, mem_union, mem_Iic, mem_Ici, ge_iff_le]
  rw [le_abs']
  constructor
  · rintro (h | h)
    · left; linarith
    · right; linarith
  · rintro (h | h)
    · left; linarith
    · right; linarith

/-- Stitz-Zeager Example 2.4.4(1): `2x² ≤ 3 - x` is `[-3/2, 1]`. -/
@[kb "stitzzeager2013" "Example 2.4.4, p. 227"]
theorem ex_2_4_4_a : {x : ℝ | 2 * x ^ 2 ≤ 3 - x} = Icc (-3 / 2) 1 := by
  ext x
  simp only [mem_setOf_eq, mem_Icc]
  constructor
  · intro h
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    nlinarith

/-- Stitz-Zeager Example 2.4.4(2): `x² - 2x > 1` is `(-∞, 1-√2) ∪ (1+√2, ∞)`. -/
@[kb "stitzzeager2013" "Example 2.4.4, p. 227"]
theorem ex_2_4_4_b :
    {x : ℝ | x ^ 2 - 2 * x > 1} = Iio (1 - Real.sqrt 2) ∪ Ioi (1 + Real.sqrt 2) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  ext x
  simp only [mem_setOf_eq, mem_union, mem_Iio, mem_Ioi, gt_iff_lt]
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    nlinarith [hc.1, hc.2]
  · rintro (h | h) <;> nlinarith

/-- Stitz-Zeager Example 2.4.4(3): `x² + 1 ≤ 2x` holds only at `x = 1`. -/
@[kb "stitzzeager2013" "Example 2.4.4, p. 227"]
theorem ex_2_4_4_c : {x : ℝ | x ^ 2 + 1 ≤ 2 * x} = {1} := by
  ext x
  simp only [mem_setOf_eq, mem_singleton_iff]
  constructor
  · intro h
    have : (x - 1) ^ 2 = 0 := by nlinarith [sq_nonneg (x - 1)]
    have := pow_eq_zero_iff (two_ne_zero) |>.mp this
    linarith
  · rintro rfl; norm_num

/-- Stitz-Zeager Example 2.4.4(4): `2x - x² ≥ |x - 1| - 1` is `[0,2]`. -/
@[kb "stitzzeager2013" "Example 2.4.4, p. 227"]
theorem ex_2_4_4_d : {x : ℝ | 2 * x - x ^ 2 ≥ |x - 1| - 1} = Icc 0 2 := by
  ext x
  simp only [mem_setOf_eq, mem_Icc, ge_iff_le]
  rcases le_or_gt 0 (x - 1) with h | h
  · rw [abs_of_nonneg h]
    constructor
    · intro h'; constructor <;> nlinarith
    · rintro ⟨h1, h2⟩; nlinarith
  · rw [abs_of_neg h]
    constructor
    · intro h'; constructor <;> nlinarith
    · rintro ⟨h1, h2⟩; nlinarith

/-- Stitz-Zeager Example 2.4.5: a side `x ≥ 0` keeps the area within `1/4` of `576` exactly when
`√575.75 ≤ x ≤ √576.25`. -/
@[kb "stitzzeager2013" "Example 2.4.5, p. 230"]
theorem ex_2_4_5_tolerance (x : ℝ) (hx : 0 ≤ x) :
    |x ^ 2 - 576| ≤ 1 / 4 ↔ Real.sqrt (2303 / 4) ≤ x ∧ x ≤ Real.sqrt (2305 / 4) := by
  rw [abs_le, Real.sqrt_le_left hx, Real.le_sqrt hx (by norm_num)]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- Stitz-Zeager Example 2.4.6(3): the curves `y = |x|` and `y = 2 - x²` meet exactly at `x = ±1`. -/
@[kb "stitzzeager2013" "Example 2.4.6, p. 230"]
theorem ex_2_4_6_c_intersection (x : ℝ) : |x| = 2 - x ^ 2 ↔ x = 1 ∨ x = -1 := by
  constructor
  · intro h
    rcases le_or_gt 0 x with hx | hx
    · rw [abs_of_nonneg hx] at h
      have : (x - 1) * (x + 2) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h' | h'
      · left; linarith
      · exfalso; linarith
    · rw [abs_of_neg hx] at h
      have : (x + 1) * (x - 2) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h' | h'
      · right; linarith
      · exfalso; linarith
  · rintro (h | h) <;> subst h <;> norm_num

end UndergradKB.Precalculus.Course
