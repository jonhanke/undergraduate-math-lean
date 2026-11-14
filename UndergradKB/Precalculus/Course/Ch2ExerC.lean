import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Order.Interval.Set.Basic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 2 (Stitz-Zeager): exercises with the book's answers, Sections 2.4-2.5 -/

namespace UndergradKB.Precalculus.Course

private lemma aux_pos (r s x : ℝ) (h : r ≤ s) : 0 < (x - r) * (x - s) ↔ x < r ∨ s < x := by
  constructor
  · intro h1
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg (sub_nonneg.2 hc.1) (sub_nonneg.2 hc.2)]
  · rintro (a | a)
    · nlinarith [mul_pos (sub_pos.2 a) (sub_pos.2 (lt_of_lt_of_le a h))]
    · nlinarith [mul_pos (sub_pos.2 (lt_of_le_of_lt h a)) (sub_pos.2 a)]

private lemma aux_nonneg (r s x : ℝ) (h : r ≤ s) : 0 ≤ (x - r) * (x - s) ↔ x ≤ r ∨ s ≤ x := by
  constructor
  · intro h1
    by_contra hc
    push Not at hc
    nlinarith [mul_pos (sub_pos.2 hc.1) (sub_pos.2 hc.2)]
  · rintro (a | a)
    · nlinarith [mul_nonneg (sub_nonneg.2 a) (sub_nonneg.2 (le_trans a h))]
    · nlinarith [mul_nonneg (sub_nonneg.2 (le_trans h a)) (sub_nonneg.2 a)]

private lemma aux_neg (r s x : ℝ) (h : r ≤ s) : (x - r) * (x - s) < 0 ↔ r < x ∧ x < s := by
  rw [← not_le, aux_nonneg r s x h]; push Not; exact Iff.rfl

private lemma aux_nonpos (r s x : ℝ) (h : r ≤ s) : (x - r) * (x - s) ≤ 0 ↔ r ≤ x ∧ x ≤ s := by
  rw [← not_lt, aux_pos r s x h]; push Not; exact Iff.rfl

/-- Closing tactic for the forward direction of interval membership goals. -/
local macro "fwd" : tactic =>
  `(tactic| first | (exfalso; linarith) | (left; refine ⟨?_, ?_⟩ <;> linarith) |
    (right; refine ⟨?_, ?_⟩ <;> linarith) | (refine ⟨?_, ?_⟩ <;> linarith) | (left; linarith) |
    (right; linarith))

/-! ## Section 2.4 -/

/-- Stitz-Zeager Exercise 2.4.1: `|3x - 5| ≤ 4` has solution set `[1/3, 3]`. -/
@[kb "stitzzeager2013" "Exercise 2.4.1, p. 232"]
theorem exer_2_4_1 : {x : ℝ | |3 * x - 5| ≤ 4} = Set.Icc (1 / 3) 3 := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_Icc, abs_le]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- Stitz-Zeager Exercise 2.4.2: `|7x + 2| > 10` has solution set `(-∞, -12/7) ∪ (8/7, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 2.4.2, p. 232"]
theorem exer_2_4_2 : {x : ℝ | 10 < |7 * x + 2|} = Set.Iio (-12 / 7) ∪ Set.Ioi (8 / 7) := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
  constructor
  · intro h
    rcases abs_cases (7 * x + 2) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> fwd
  · rintro (h | h) <;> rcases abs_cases (7 * x + 2) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> linarith

/-- Stitz-Zeager Exercise 2.4.3: `|2x + 1| - 5 < 0` has solution set `(-3, 2)`. -/
@[kb "stitzzeager2013" "Exercise 2.4.3, p. 232"]
theorem exer_2_4_3 : {x : ℝ | |2 * x + 1| - 5 < 0} = Set.Ioo (-3) 2 := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_Ioo]
  constructor
  · intro h
    rcases abs_cases (2 * x + 1) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> fwd
  · rintro ⟨h1, h2⟩
    rcases abs_cases (2 * x + 1) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> linarith

/-- Stitz-Zeager Exercise 2.4.4: `|2 - x| - 4 ≥ -3` has solution set `(-∞, 1] ∪ [3, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 2.4.4, p. 232"]
theorem exer_2_4_4 : {x : ℝ | -3 ≤ |2 - x| - 4} = Set.Iic 1 ∪ Set.Ici 3 := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iic, Set.mem_Ici]
  constructor
  · intro h
    rcases abs_cases (2 - x) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> fwd
  · rintro (h | h) <;> rcases abs_cases (2 - x) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> linarith

/-- Stitz-Zeager Exercise 2.4.5: `|3x + 5| + 2 < 1` has no solution. -/
@[kb "stitzzeager2013" "Exercise 2.4.5, p. 232"]
theorem exer_2_4_5 : {x : ℝ | |3 * x + 5| + 2 < 1} = ∅ := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
  linarith [abs_nonneg (3 * x + 5)]

/-- Stitz-Zeager Exercise 2.4.6: `2|7 - x| + 4 > 1` holds for every real `x`. -/
@[kb "stitzzeager2013" "Exercise 2.4.6, p. 232"]
theorem exer_2_4_6 : {x : ℝ | 1 < 2 * |7 - x| + 4} = Set.univ := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  linarith [abs_nonneg (7 - x)]

/-- Stitz-Zeager Exercise 2.4.7: `2 ≤ |4 - x| < 7` has solution set `(-3, 2] ∪ [6, 11)`. -/
@[kb "stitzzeager2013" "Exercise 2.4.7, p. 232"]
theorem exer_2_4_7 : {x : ℝ | 2 ≤ |4 - x| ∧ |4 - x| < 7} = Set.Ioc (-3) 2 ∪ Set.Ico 6 11 := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Ioc, Set.mem_Ico]
  constructor
  · rintro ⟨h1, h2⟩
    rcases abs_cases (4 - x) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> fwd
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> rcases abs_cases (4 - x) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
      constructor <;> linarith

/-- Stitz-Zeager Exercise 2.4.8: `1 < |2x - 9| ≤ 3` has solution set `[3, 4) ∪ (5, 6]`. -/
@[kb "stitzzeager2013" "Exercise 2.4.8, p. 232"]
theorem exer_2_4_8 : {x : ℝ | 1 < |2 * x - 9| ∧ |2 * x - 9| ≤ 3} = Set.Ico 3 4 ∪ Set.Ioc 5 6 := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Ioc, Set.mem_Ico]
  constructor
  · rintro ⟨h1, h2⟩
    rcases abs_cases (2 * x - 9) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> fwd
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> rcases abs_cases (2 * x - 9) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
      constructor <;> linarith

/-- Stitz-Zeager Exercise 2.4.9: `|x + 3| ≥ |6x + 9|` has solution set `[-12/7, -6/5]`. -/
@[kb "stitzzeager2013" "Exercise 2.4.9, p. 232"]
theorem exer_2_4_9 : {x : ℝ | |6 * x + 9| ≤ |x + 3|} = Set.Icc (-12 / 7) (-6 / 5) := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_Icc]
  constructor
  · intro h
    rcases abs_cases (6 * x + 9) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
      rcases abs_cases (x + 3) with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> fwd
  · rintro ⟨h1, h2⟩
    rcases abs_cases (6 * x + 9) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
      rcases abs_cases (x + 3) with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> linarith

/-- Stitz-Zeager Exercise 2.4.10: `|x - 3| - |2x + 1| < 0` has solution set `(-∞, -4) ∪ (2/3, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 2.4.10, p. 232"]
theorem exer_2_4_10 :
    {x : ℝ | |x - 3| - |2 * x + 1| < 0} = Set.Iio (-4) ∪ Set.Ioi (2 / 3) := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
  constructor
  · intro h
    rcases abs_cases (x - 3) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
      rcases abs_cases (2 * x + 1) with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> fwd
  · rintro (h | h) <;> rcases abs_cases (x - 3) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
      rcases abs_cases (2 * x + 1) with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> linarith

/-- Stitz-Zeager Exercise 2.4.11: `|1 - 2x| ≥ x + 5` has solution set `(-∞, -4/3] ∪ [6, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 2.4.11, p. 232"]
theorem exer_2_4_11 : {x : ℝ | x + 5 ≤ |1 - 2 * x|} = Set.Iic (-4 / 3) ∪ Set.Ici 6 := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iic, Set.mem_Ici]
  constructor
  · intro h
    rcases abs_cases (1 - 2 * x) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> fwd
  · rintro (h | h) <;> rcases abs_cases (1 - 2 * x) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> linarith

/-- Stitz-Zeager Exercise 2.4.12: `x + 5 < |x + 5|` has solution set `(-∞, -5)`. -/
@[kb "stitzzeager2013" "Exercise 2.4.12, p. 232"]
theorem exer_2_4_12 : {x : ℝ | x + 5 < |x + 5|} = Set.Iio (-5) := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_Iio]
  constructor
  · intro h
    rcases abs_cases (x + 5) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> linarith
  · intro h
    rcases abs_cases (x + 5) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> linarith

/-- Stitz-Zeager Exercise 2.4.13: `x ≥ |x + 1|` has no solution. -/
@[kb "stitzzeager2013" "Exercise 2.4.13, p. 232"]
theorem exer_2_4_13 : {x : ℝ | |x + 1| ≤ x} = ∅ := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
  rcases abs_cases (x + 1) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> linarith

/-- Stitz-Zeager Exercise 2.4.14: `|2x + 1| ≤ 6 - x` has solution set `[-7, 5/3]`. -/
@[kb "stitzzeager2013" "Exercise 2.4.14, p. 232"]
theorem exer_2_4_14 : {x : ℝ | |2 * x + 1| ≤ 6 - x} = Set.Icc (-7) (5 / 3) := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_Icc]
  constructor
  · intro h
    rcases abs_cases (2 * x + 1) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> fwd
  · rintro ⟨h1, h2⟩
    rcases abs_cases (2 * x + 1) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> linarith

/-- Stitz-Zeager Exercise 2.4.15: `x + |2x - 3| < 2` has solution set `(1, 5/3)`. -/
@[kb "stitzzeager2013" "Exercise 2.4.15, p. 232"]
theorem exer_2_4_15 : {x : ℝ | x + |2 * x - 3| < 2} = Set.Ioo 1 (5 / 3) := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_Ioo]
  constructor
  · intro h
    rcases abs_cases (2 * x - 3) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> fwd
  · rintro ⟨h1, h2⟩
    rcases abs_cases (2 * x - 3) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> linarith

/-- Stitz-Zeager Exercise 2.4.17: `x² + 2x - 3 ≥ 0` has solution set `(-∞, -3] ∪ [1, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 2.4.17, p. 232"]
theorem exer_2_4_17 : {x : ℝ | 0 ≤ x ^ 2 + 2 * x - 3} = Set.Iic (-3) ∪ Set.Ici 1 := by
  ext x
  have e : x ^ 2 + 2 * x - 3 = (x - (-3)) * (x - 1) := by ring
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iic, Set.mem_Ici, e]
  exact aux_nonneg _ _ _ (by norm_num)

/-- Stitz-Zeager Exercise 2.4.18: `16x² + 8x + 1 > 0` holds exactly for `x ≠ -1/4`. -/
@[kb "stitzzeager2013" "Exercise 2.4.18, p. 232"]
theorem exer_2_4_18 : {x : ℝ | 0 < 16 * x ^ 2 + 8 * x + 1} = Set.Iio (-1 / 4) ∪ Set.Ioi (-1 / 4) := by
  ext x
  have e : 16 * x ^ 2 + 8 * x + 1 = 16 * ((x - (-1 / 4)) * (x - (-1 / 4))) := by ring
  have : 0 < 16 * x ^ 2 + 8 * x + 1 ↔ 0 < (x - (-1 / 4)) * (x - (-1 / 4)) := by
    rw [e]; constructor <;> intro h <;> linarith
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi, this]
  rw [aux_pos _ _ _ le_rfl]

/-- Stitz-Zeager Exercise 2.4.19: `x² + 9 < 6x` has no solution. -/
@[kb "stitzzeager2013" "Exercise 2.4.19, p. 232"]
theorem exer_2_4_19 : {x : ℝ | x ^ 2 + 9 < 6 * x} = ∅ := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
  nlinarith [sq_nonneg (x - 3)]

/-- Stitz-Zeager Exercise 2.4.21: `x² + 4 ≤ 4x` has the single solution `x = 2`. -/
@[kb "stitzzeager2013" "Exercise 2.4.21, p. 232"]
theorem exer_2_4_21 : {x : ℝ | x ^ 2 + 4 ≤ 4 * x} = {2} := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    have : (x - 2) ^ 2 = 0 := by nlinarith [sq_nonneg (x - 2)]
    have := pow_eq_zero_iff (two_ne_zero) |>.1 this
    linarith
  · rintro rfl; norm_num

/-- Stitz-Zeager Exercise 2.4.23: `3x² ≤ 11x + 4` has solution set `[-1/3, 4]`. -/
@[kb "stitzzeager2013" "Exercise 2.4.23, p. 232"]
theorem exer_2_4_23 : {x : ℝ | 3 * x ^ 2 ≤ 11 * x + 4} = Set.Icc (-1 / 3) 4 := by
  ext x
  have e : 3 * x ^ 2 ≤ 11 * x + 4 ↔ (x - (-1 / 3)) * (x - 4) ≤ 0 := by
    constructor <;> intro h <;> nlinarith
  simp only [Set.mem_ofPred_eq, Set.mem_Icc, e]
  exact aux_nonpos _ _ _ (by norm_num)

/-- Stitz-Zeager Exercise 2.4.24: `x > x²` has solution set `(0, 1)`. -/
@[kb "stitzzeager2013" "Exercise 2.4.24, p. 232"]
theorem exer_2_4_24 : {x : ℝ | x ^ 2 < x} = Set.Ioo 0 1 := by
  ext x
  have e : x ^ 2 < x ↔ (x - 0) * (x - 1) < 0 := by
    constructor <;> intro h <;> nlinarith
  simp only [Set.mem_ofPred_eq, Set.mem_Ioo, e]
  exact aux_neg _ _ _ (by norm_num)

/-- Stitz-Zeager Exercise 2.4.25: `2x² - 4x - 1 > 0` has solution set
`(-∞, (2 - √6)/2) ∪ ((2 + √6)/2, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 2.4.25, p. 232"]
theorem exer_2_4_25 :
    {x : ℝ | 0 < 2 * x ^ 2 - 4 * x - 1} = Set.Iio ((2 - √6) / 2) ∪ Set.Ioi ((2 + √6) / 2) := by
  ext x
  have h6 : √6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have h0 := Real.sqrt_nonneg 6
  have e : 0 < 2 * x ^ 2 - 4 * x - 1 ↔ 0 < (x - (2 - √6) / 2) * (x - (2 + √6) / 2) := by
    constructor <;> intro h <;> nlinarith
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi, e]
  exact aux_pos _ _ _ (by linarith)

/-- Stitz-Zeager Exercise 2.4.26: `5x + 4 ≤ 3x²` has solution set
`(-∞, (5 - √73)/6] ∪ [(5 + √73)/6, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 2.4.26, p. 232"]
theorem exer_2_4_26 :
    {x : ℝ | 5 * x + 4 ≤ 3 * x ^ 2} = Set.Iic ((5 - √73) / 6) ∪ Set.Ici ((5 + √73) / 6) := by
  ext x
  have h6 : √73 ^ 2 = 73 := Real.sq_sqrt (by norm_num)
  have h0 := Real.sqrt_nonneg 73
  have e : 5 * x + 4 ≤ 3 * x ^ 2 ↔ 0 ≤ (x - (5 - √73) / 6) * (x - (5 + √73) / 6) := by
    constructor <;> intro h <;> nlinarith
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iic, Set.mem_Ici, e]
  exact aux_nonneg _ _ _ (by linarith)

/-- Stitz-Zeager Exercise 2.4.28: `x² ≤ |4x - 3|` has solution set
`[-2 - √7, -2 + √7] ∪ [1, 3]`. -/
@[kb "stitzzeager2013" "Exercise 2.4.28, p. 232"]
theorem exer_2_4_28 :
    {x : ℝ | x ^ 2 ≤ |4 * x - 3|} = Set.Icc (-2 - √7) (-2 + √7) ∪ Set.Icc 1 3 := by
  ext x
  have h7 : √7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have h0 := Real.sqrt_nonneg 7
  have q1 := aux_nonpos 1 3 x (by norm_num)
  have q2 := aux_nonpos (-2 - √7) (-2 + √7) x (by linarith)
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Icc]
  constructor
  · intro h
    rcases abs_cases (4 * x - 3) with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · right; exact q1.1 (by nlinarith)
    · left; exact q2.1 (by nlinarith)
  · rintro (h | h)
    · have := q2.2 h
      nlinarith [neg_le_abs (4 * x - 3)]
    · have := q1.2 h
      nlinarith [le_abs_self (4 * x - 3)]

/-- Stitz-Zeager Exercise 2.4.30: `x² ≥ |x|` has solution set `(-∞, -1] ∪ {0} ∪ [1, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 2.4.30, p. 232"]
theorem exer_2_4_30 : {x : ℝ | |x| ≤ x ^ 2} = Set.Iic (-1) ∪ {0} ∪ Set.Ici 1 := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_singleton_iff]
  constructor
  · intro h
    by_cases h0 : x = 0
    · left; right; exact h0
    · rcases lt_or_gt_of_ne h0 with hn | hp
      · rw [abs_of_neg hn] at h
        left; left
        by_contra hc
        push Not at hc
        nlinarith [mul_pos (neg_pos.2 hn) (show 0 < x + 1 by linarith)]
      · rw [abs_of_pos hp] at h
        right
        by_contra hc
        push Not at hc
        nlinarith [mul_pos hp (show 0 < 1 - x by linarith)]
  · rintro ((h | h) | h)
    · rw [abs_of_neg (by linarith)]; nlinarith
    · rw [h]; norm_num
    · rw [abs_of_pos (by linarith)]; nlinarith

/-- Stitz-Zeager Exercise 2.4.33: with `P(x) = -x² + 25x - 100` on `[0,35]`, `P(x) ≥ 50` iff
`10 ≤ x ≤ 15`. -/
@[kb "stitzzeager2013" "Exercise 2.4.33, p. 232"]
theorem exer_2_4_33 (x : ℝ) (_ : 0 ≤ x) (_ : x ≤ 35) :
    50 ≤ -x ^ 2 + 25 * x - 100 ↔ 10 ≤ x ∧ x ≤ 15 := by
  have e : 50 ≤ -x ^ 2 + 25 * x - 100 ↔ (x - 10) * (x - 15) ≤ 0 := by
    constructor <;> intro h <;> nlinarith
  rw [e, aux_nonpos _ _ _ (by norm_num)]

/-- Stitz-Zeager Exercise 2.4.34: `x² - 10x + 27 ≤ 11` (costs in hundreds, `x` in thousands of
pens) iff `2 ≤ x ≤ 8`. -/
@[kb "stitzzeager2013" "Exercise 2.4.34, p. 232"]
theorem exer_2_4_34 (x : ℝ) (_ : 0 ≤ x) : x ^ 2 - 10 * x + 27 ≤ 11 ↔ 2 ≤ x ∧ x ≤ 8 := by
  have e : x ^ 2 - 10 * x + 27 ≤ 11 ↔ (x - 2) * (x - 8) ≤ 0 := by
    constructor <;> intro h <;> nlinarith
  rw [e, aux_nonpos _ _ _ (by norm_num)]

/-- Stitz-Zeager Exercise 2.4.35: for `0 ≤ t ≤ 12`, `T(t) = -t²/2 + 8t + 32` exceeds `42` iff
`t > 8 - 2√11` (about `1.37`); the upper endpoint `8 + 2√11` lies beyond the domain. -/
@[kb "stitzzeager2013" "Exercise 2.4.35, p. 232"]
theorem exer_2_4_35 (t : ℝ) (_ : 0 ≤ t) (ht : t ≤ 12) :
    42 < -(1 / 2) * t ^ 2 + 8 * t + 32 ↔ 8 - 2 * √11 < t := by
  have h11 : √11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  have h0 := Real.sqrt_nonneg 11
  have h2 : 2 < √11 := by nlinarith
  have e : 42 < -(1 / 2) * t ^ 2 + 8 * t + 32 ↔
      (t - (8 - 2 * √11)) * (t - (8 + 2 * √11)) < 0 := by
    constructor <;> intro h <;> nlinarith
  rw [e, aux_neg _ _ _ (by linarith)]
  constructor
  · exact fun h => h.1
  · intro h; exact ⟨h, by linarith⟩

/-- Stitz-Zeager Exercise 2.4.36: the rocket height `-5t² + 100t` is at least `250` iff
`10 - 5√2 ≤ t ≤ 10 + 5√2` (about `2.93` to `17.07`). -/
@[kb "stitzzeager2013" "Exercise 2.4.36, p. 233"]
theorem exer_2_4_36 (t : ℝ) :
    250 ≤ -5 * t ^ 2 + 100 * t ↔ 10 - 5 * √2 ≤ t ∧ t ≤ 10 + 5 * √2 := by
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h0 := Real.sqrt_nonneg 2
  have e : 250 ≤ -5 * t ^ 2 + 100 * t ↔ (t - (10 - 5 * √2)) * (t - (10 + 5 * √2)) ≤ 0 := by
    constructor <;> intro h <;> nlinarith
  rw [e, aux_nonpos _ _ _ (by linarith)]

/-- Stitz-Zeager Exercise 2.4.38: the Fahrenheit range `50 ≤ F ≤ 95` corresponds to
`10 ≤ C ≤ 35` under `C = (5/9)(F - 32)`. -/
@[kb "stitzzeager2013" "Exercise 2.4.38, p. 233"]
theorem exer_2_4_38 (F : ℝ) :
    (50 ≤ F ∧ F ≤ 95) ↔ (10 ≤ 5 / 9 * (F - 32) ∧ 5 / 9 * (F - 32) ≤ 35) := by
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- Stitz-Zeager Exercise 2.4.39-40: `|x - 2| ≤ 4` iff `x ∈ [-2, 6]`; `|3x + 1| ≤ 2` iff
`x ∈ [-1, 1/3]`. -/
@[kb "stitzzeager2013" "Exercise 2.4.39, p. 233"]
theorem exer_2_4_39 :
    {x : ℝ | |x - 2| ≤ 4} = Set.Icc (-2) 6 ∧ {x : ℝ | |3 * x + 1| ≤ 2} = Set.Icc (-1) (1 / 3) := by
  constructor <;> ext x <;> simp only [Set.mem_ofPred_eq, Set.mem_Icc, abs_le] <;>
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- Stitz-Zeager Exercise 2.4.41: `|x² - 3| ≤ 1` has solution set `[-2, -√2] ∪ [√2, 2]`. -/
@[kb "stitzzeager2013" "Exercise 2.4.41, p. 233"]
theorem exer_2_4_41 :
    {x : ℝ | |x ^ 2 - 3| ≤ 1} = Set.Icc (-2) (-√2) ∪ Set.Icc (√2) 2 := by
  ext x
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h0 := Real.sqrt_nonneg 2
  have q1 := aux_nonneg (-√2) (√2) x (by linarith)
  have q2 := aux_nonpos (-2) 2 x (by norm_num)
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Icc, abs_le]
  constructor
  · rintro ⟨h1, h3⟩
    have a := q1.1 (by nlinarith)
    have b := q2.1 (by nlinarith)
    rcases a with a | a
    · left; constructor <;> linarith [b.1, b.2]
    · right; constructor <;> linarith [b.1, b.2]
  · rintro (⟨h1, h3⟩ | ⟨h1, h3⟩)
    · have a := q2.2 ⟨h1, by linarith⟩
      have b := q1.2 (Or.inl h3)
      constructor <;> nlinarith
    · have a := q2.2 ⟨by linarith, h3⟩
      have b := q1.2 (Or.inr h1)
      constructor <;> nlinarith

/-- Stitz-Zeager Exercise 2.4.42: `|x² - 4| ≥ 7` has solution set `(-∞, -√11] ∪ [√11, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 2.4.42, p. 233"]
theorem exer_2_4_42 :
    {x : ℝ | 7 ≤ |x ^ 2 - 4|} = Set.Iic (-√11) ∪ Set.Ici (√11) := by
  ext x
  have h11 : √11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  have h0 := Real.sqrt_nonneg 11
  have q1 := aux_nonneg (-√11) (√11) x (by linarith)
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iic, Set.mem_Ici]
  constructor
  · intro h
    rcases abs_cases (x ^ 2 - 4) with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · exact q1.1 (by nlinarith)
    · nlinarith [sq_nonneg x]
  · intro h
    have := q1.2 h
    rcases abs_cases (x ^ 2 - 4) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> nlinarith

/-- Stitz-Zeager Exercise 2.4.43: for `x > 0`, `|6x² - 42| ≤ 3` iff `√(13/2) ≤ x ≤ √(15/2)`
(about `2.550` to `2.739`). -/
@[kb "stitzzeager2013" "Exercise 2.4.43, p. 233"]
theorem exer_2_4_43 (x : ℝ) (hx : 0 < x) :
    |6 * x ^ 2 - 42| ≤ 3 ↔ √(13 / 2) ≤ x ∧ x ≤ √(15 / 2) := by
  rw [abs_le, Real.sqrt_le_left hx.le, Real.le_sqrt hx.le]
  · constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  · norm_num

/-! ## Section 2.5 -/

/-- Stitz-Zeager Exercise 2.5.1(a): for the Lake County census data, the normal equations of least
squares have the unique solution slope `936.31`, intercept `-1645322.6`. -/
@[kb "stitzzeager2013" "Exercise 2.5.1, p. 242"]
theorem exer_2_5_1 (m b : ℝ) :
    ((197200 - (m * 1970 + b)) + (212801 - (m * 1980 + b)) + (215499 - (m * 1990 + b)) +
        (227511 - (m * 2000 + b)) = 0 ∧
      1970 * (197200 - (m * 1970 + b)) + 1980 * (212801 - (m * 1980 + b)) +
        1990 * (215499 - (m * 1990 + b)) + 2000 * (227511 - (m * 2000 + b)) = 0) ↔
      (m = 93631 / 100 ∧ b = -16453226 / 10) := by
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; constructor <;> norm_num

/-- Stitz-Zeager Exercise 2.5.2(a): for the Lorain County census data, the least-squares normal
equations have the unique solution slope `796.8`, intercept `-1309762.5`. -/
@[kb "stitzzeager2013" "Exercise 2.5.2, p. 242"]
theorem exer_2_5_2 (m b : ℝ) :
    ((256843 - (m * 1970 + b)) + (274909 - (m * 1980 + b)) + (271126 - (m * 1990 + b)) +
        (284664 - (m * 2000 + b)) = 0 ∧
      1970 * (256843 - (m * 1970 + b)) + 1980 * (274909 - (m * 1980 + b)) +
        1990 * (271126 - (m * 1990 + b)) + 2000 * (284664 - (m * 2000 + b)) = 0) ↔
      (m = 3984 / 5 ∧ b = -2619525 / 2) := by
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; constructor <;> norm_num

/-- Stitz-Zeager Exercise 2.5.3(c): for the energy data of 1970-2000, the least-squares normal
equations have the unique solution slope `0.266`, intercept `-459.86`. -/
@[kb "stitzzeager2013" "Exercise 2.5.3, p. 242"]
theorem exer_2_5_3 (m b : ℝ) :
    ((635 / 10 - (m * 1970 + b)) + (672 / 10 - (m * 1980 + b)) + (707 / 10 - (m * 1990 + b)) +
        (712 / 10 - (m * 2000 + b)) = 0 ∧
      1970 * (635 / 10 - (m * 1970 + b)) + 1980 * (672 / 10 - (m * 1980 + b)) +
        1990 * (707 / 10 - (m * 1990 + b)) + 2000 * (712 / 10 - (m * 2000 + b)) = 0) ↔
      (m = 266 / 1000 ∧ b = -45986 / 100) := by
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; constructor <;> norm_num

end UndergradKB.Precalculus.Course
