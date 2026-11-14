import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Basic
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.Radicals

/-! # Course layer, Chapter 3 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 3.3 -/

namespace UndergradKB.Precalculus.Course

private lemma w7c_sq (y c : ℝ) (hc : 0 ≤ c) : y ^ 2 = c ↔ y = -√c ∨ y = √c := by
  have h := Real.sq_sqrt hc
  constructor
  · intro hy
    have : (y - √c) * (y + √c) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · right; linarith
    · left; linarith
  · rintro (h1 | h1) <;> rw [h1] <;> nlinarith

/-! ## Section 3.3 -/

/-- Stitz-Zeager Exercise 3.3.1 (Cauchy's bound): every real zero of `x³ - 2x² - 5x + 6` lies in `[-7, 7]`. -/
@[kb "stitzzeager2013" "Exercise 3.3.1, p. 292"]
theorem exer_3_3_1 (x : ℝ) (h : x ^ 3 - 2 * x ^ 2 - 5 * x + 6 = 0) : x ∈ Set.Icc (-7 : ℝ) 7 := by
  constructor
  · refine le_of_not_gt fun hc => ?_
    nlinarith [mul_nonneg (by linarith : 0 ≤ -7 - x) (sq_nonneg x), sq_nonneg x]
  · refine le_of_not_gt fun hc => ?_
    nlinarith [mul_nonneg (by linarith : 0 ≤ x - 7) (sq_nonneg x), sq_nonneg x]

/-- Stitz-Zeager Exercise 3.3.2 (Cauchy's bound): every real zero of `x⁴ + 2x³ - 12x² - 40x - 32`
lies in `[-41, 41]`. -/
@[kb "stitzzeager2013" "Exercise 3.3.2, p. 292"]
theorem exer_3_3_2 (x : ℝ) (h : x ^ 4 + 2 * x ^ 3 - 12 * x ^ 2 - 40 * x - 32 = 0) :
    x ∈ Set.Icc (-41 : ℝ) 41 := by
  constructor
  · refine le_of_not_gt fun hc => ?_
    nlinarith [mul_nonneg (by linarith : 0 ≤ -41 - x) (sq_nonneg x), sq_nonneg x,
      mul_nonneg (sq_nonneg x) (sq_nonneg x), mul_nonneg (by linarith : 0 ≤ -41 - x) (sq_nonneg (x ^ 2))]
  · refine le_of_not_gt fun hc => ?_
    nlinarith [mul_nonneg (by linarith : 0 ≤ x - 41) (sq_nonneg x), sq_nonneg x,
      mul_nonneg (by linarith : 0 ≤ x - 41) (pow_nonneg (by linarith : (0 : ℝ) ≤ x) 3)]

/-- Stitz-Zeager Exercise 3.3.3 (Cauchy's bound): every real zero of `x⁴ - 9x² - 4x + 12` lies in
`[-13, 13]`. -/
@[kb "stitzzeager2013" "Exercise 3.3.3, p. 292"]
theorem exer_3_3_3 (x : ℝ) (h : x ^ 4 - 9 * x ^ 2 - 4 * x + 12 = 0) : x ∈ Set.Icc (-13 : ℝ) 13 := by
  constructor
  · refine le_of_not_gt fun hc => ?_
    nlinarith [sq_nonneg x, mul_nonneg (sq_nonneg x) (sq_nonneg x),
      mul_nonneg (by linarith : 0 ≤ -13 - x) (sq_nonneg x)]
  · refine le_of_not_gt fun hc => ?_
    nlinarith [mul_nonneg (by linarith : 0 ≤ x - 13) (pow_nonneg (by linarith : (0 : ℝ) ≤ x) 3),
      sq_nonneg x]

/-- Stitz-Zeager Exercise 3.3.4 (Cauchy's bound): every real zero of `x³ + 4x² - 11x + 6` lies in
`[-12, 12]`. -/
@[kb "stitzzeager2013" "Exercise 3.3.4, p. 292"]
theorem exer_3_3_4 (x : ℝ) (h : x ^ 3 + 4 * x ^ 2 - 11 * x + 6 = 0) : x ∈ Set.Icc (-12 : ℝ) 12 := by
  constructor
  · refine le_of_not_gt fun hc => ?_
    nlinarith [mul_nonneg (by linarith : 0 ≤ -12 - x) (sq_nonneg x), sq_nonneg x]
  · refine le_of_not_gt fun hc => ?_
    nlinarith [mul_nonneg (by linarith : 0 ≤ x - 12) (sq_nonneg x), sq_nonneg x]

/-- Stitz-Zeager Exercise 3.3.5 (Cauchy's bound): every real zero of `x³ - 7x² + x - 7` lies in `[-8, 8]`. -/
@[kb "stitzzeager2013" "Exercise 3.3.5, p. 292"]
theorem exer_3_3_5 (x : ℝ) (h : x ^ 3 - 7 * x ^ 2 + x - 7 = 0) : x ∈ Set.Icc (-8 : ℝ) 8 := by
  constructor
  · refine le_of_not_gt fun hc => ?_
    nlinarith [mul_nonneg (by linarith : 0 ≤ -8 - x) (sq_nonneg x), sq_nonneg x]
  · refine le_of_not_gt fun hc => ?_
    nlinarith [mul_nonneg (by linarith : 0 ≤ x - 8) (sq_nonneg x), sq_nonneg x]

/-- Stitz-Zeager Exercise 3.3.6 (Cauchy's bound): every real zero of `-2x³ + 19x² - 49x + 20` lies in
`[-51/2, 51/2]`. -/
@[kb "stitzzeager2013" "Exercise 3.3.6, p. 292"]
theorem exer_3_3_6 (x : ℝ) (h : -2 * x ^ 3 + 19 * x ^ 2 - 49 * x + 20 = 0) :
    x ∈ Set.Icc (-(51 / 2) : ℝ) (51 / 2) := by
  constructor
  · refine le_of_not_gt fun hc => ?_
    nlinarith [mul_nonneg (by linarith : 0 ≤ -(51 / 2) - x) (sq_nonneg x), sq_nonneg x]
  · refine le_of_not_gt fun hc => ?_
    nlinarith [mul_nonneg (by linarith : 0 ≤ x - 51 / 2) (sq_nonneg x), sq_nonneg x]

/-- Stitz-Zeager Exercise 3.3.7 (Cauchy's bound): every real zero of `-17x³ + 5x² + 34x - 10` lies in
`[-3, 3]`. -/
@[kb "stitzzeager2013" "Exercise 3.3.7, p. 292"]
theorem exer_3_3_7 (x : ℝ) (h : -17 * x ^ 3 + 5 * x ^ 2 + 34 * x - 10 = 0) :
    x ∈ Set.Icc (-3 : ℝ) 3 := by
  constructor
  · refine le_of_not_gt fun hc => ?_
    nlinarith [mul_nonneg (by linarith : 0 ≤ -3 - x) (sq_nonneg x), sq_nonneg x]
  · refine le_of_not_gt fun hc => ?_
    nlinarith [mul_nonneg (by linarith : 0 ≤ x - 3) (sq_nonneg x), sq_nonneg x]

/-- Stitz-Zeager Exercise 3.3.8 (Cauchy's bound): every real zero of `36x⁴ - 12x³ - 11x² + 2x + 1` lies
in `[-4/3, 4/3]`. -/
@[kb "stitzzeager2013" "Exercise 3.3.8, p. 292"]
theorem exer_3_3_8 (x : ℝ) (h : 36 * x ^ 4 - 12 * x ^ 3 - 11 * x ^ 2 + 2 * x + 1 = 0) :
    x ∈ Set.Icc (-(4 / 3) : ℝ) (4 / 3) := by
  constructor
  · refine le_of_not_gt fun hc => ?_
    nlinarith [sq_nonneg x, mul_nonneg (sq_nonneg x) (sq_nonneg x),
      mul_nonneg (by linarith : 0 ≤ -(4 / 3) - x) (sq_nonneg x)]
  · refine le_of_not_gt fun hc => ?_
    nlinarith [mul_nonneg (by linarith : 0 ≤ x - 4 / 3) (pow_nonneg (by linarith : (0 : ℝ) ≤ x) 3),
      sq_nonneg x]

/-- Stitz-Zeager Exercise 3.3.9 (Cauchy's bound): every real zero of `3x³ + 3x² - 11x - 10` lies in
`[-14/3, 14/3]`. -/
@[kb "stitzzeager2013" "Exercise 3.3.9, p. 292"]
theorem exer_3_3_9 (x : ℝ) (h : 3 * x ^ 3 + 3 * x ^ 2 - 11 * x - 10 = 0) :
    x ∈ Set.Icc (-(14 / 3) : ℝ) (14 / 3) := by
  constructor
  · refine le_of_not_gt fun hc => ?_
    nlinarith [mul_nonneg (by linarith : 0 ≤ -(14 / 3) - x) (sq_nonneg x), sq_nonneg x]
  · refine le_of_not_gt fun hc => ?_
    nlinarith [mul_nonneg (by linarith : 0 ≤ x - 14 / 3) (sq_nonneg x), sq_nonneg x]

/-- Stitz-Zeager Exercise 3.3.10 (Cauchy's bound): every real zero of `2x⁴ + x³ - 7x² - 3x + 3` lies in
`[-9/2, 9/2]`. -/
@[kb "stitzzeager2013" "Exercise 3.3.10, p. 292"]
theorem exer_3_3_10 (x : ℝ) (h : 2 * x ^ 4 + x ^ 3 - 7 * x ^ 2 - 3 * x + 3 = 0) :
    x ∈ Set.Icc (-(9 / 2) : ℝ) (9 / 2) := by
  constructor
  · refine le_of_not_gt fun hc => ?_
    nlinarith [sq_nonneg x, mul_nonneg (sq_nonneg x) (sq_nonneg x),
      mul_nonneg (by linarith : 0 ≤ -(9 / 2) - x) (sq_nonneg x)]
  · refine le_of_not_gt fun hc => ?_
    nlinarith [mul_nonneg (by linarith : 0 ≤ x - 9 / 2) (pow_nonneg (by linarith : (0 : ℝ) ≤ x) 3),
      sq_nonneg x]

/-- Stitz-Zeager Exercise 3.3.24: the real zeros of `x⁴ - 9x² + 14` are `±√2` and `±√7`. -/
@[kb "stitzzeager2013" "Exercise 3.3.24, p. 292"]
theorem exer_3_3_24 (x : ℝ) :
    x ^ 4 - 9 * x ^ 2 + 14 = 0 ↔ x = -√2 ∨ x = √2 ∨ x = -√7 ∨ x = √7 := by
  have e : x ^ 4 - 9 * x ^ 2 + 14 = (x ^ 2 - 2) * (x ^ 2 - 7) := by ring
  rw [e, mul_eq_zero, sub_eq_zero, sub_eq_zero, w7c_sq x 2 (by norm_num), w7c_sq x 7 (by norm_num)]
  simp only [or_assoc]

/-- Stitz-Zeager Exercise 3.3.25: the real zeros of `3x⁴ - 14x² - 5` are `±√5`. -/
@[kb "stitzzeager2013" "Exercise 3.3.25, p. 292"]
theorem exer_3_3_25 (x : ℝ) : 3 * x ^ 4 - 14 * x ^ 2 - 5 = 0 ↔ x = -√5 ∨ x = √5 := by
  have e : 3 * x ^ 4 - 14 * x ^ 2 - 5 = (3 * x ^ 2 + 1) * (x ^ 2 - 5) := by ring
  rw [e, mul_eq_zero, sub_eq_zero, w7c_sq x 5 (by norm_num)]
  constructor
  · rintro (h | h)
    · exfalso; nlinarith [sq_nonneg x]
    · exact h
  · intro h; right; exact h

/-- Stitz-Zeager Exercise 3.3.26: the real zeros of `2x⁴ - 7x² + 6` are `±√2` and `±√6/2`. -/
@[kb "stitzzeager2013" "Exercise 3.3.26, p. 292"]
theorem exer_3_3_26 (x : ℝ) :
    2 * x ^ 4 - 7 * x ^ 2 + 6 = 0 ↔ x = -√2 ∨ x = √2 ∨ x = -(√6 / 2) ∨ x = √6 / 2 := by
  have e : 2 * x ^ 4 - 7 * x ^ 2 + 6 = (2 * x ^ 2 - 3) * (x ^ 2 - 2) := by ring
  have a1 : 2 * x ^ 2 - 3 = 0 ↔ x = -(√6 / 2) ∨ x = √6 / 2 := by
    have key : 2 * x ^ 2 - 3 = 0 ↔ (2 * x) ^ 2 = 6 := by
      constructor <;> intro h <;> nlinarith
    rw [key, w7c_sq _ _ (by norm_num)]
    constructor
    · rintro (h | h)
      · left; linarith
      · right; linarith
    · rintro (h | h)
      · left; linarith
      · right; linarith
  rw [e, mul_eq_zero, a1, sub_eq_zero, w7c_sq x 2 (by norm_num)]
  tauto

/-- Stitz-Zeager Exercise 3.3.27: `x⁶ - 3x³ - 10 = (x³ - 5)(x³ + 2)` has the real zeros `∛5` and
`∛(-2)` (the real cube roots). -/
@[kb "stitzzeager2013" "Exercise 3.3.27, p. 292"]
theorem exer_3_3_27 (x : ℝ) :
    x ^ 6 - 3 * x ^ 3 - 10 = 0 ↔ x = principalRoot 3 (-2) ∨ x = principalRoot 3 5 := by
  have e : x ^ 6 - 3 * x ^ 3 - 10 = (x ^ 3 + 2) * (x ^ 3 - 5) := by ring
  have h3 : Odd 3 := by decide
  rw [e, mul_eq_zero, principalRoot_eq_iff_odd h3, principalRoot_eq_iff_odd h3]
  constructor <;> rintro (h | h) <;> first | (left; linarith) | (right; linarith)

/-- Stitz-Zeager Exercise 3.3.28: `2x⁶ - 9x³ + 10 = (2x³ - 5)(x³ - 2)` has the real zeros `∛20 / 2`
(that is `∛(5/2)`) and `∛2`. -/
@[kb "stitzzeager2013" "Exercise 3.3.28, p. 292"]
theorem exer_3_3_28 (x : ℝ) :
    2 * x ^ 6 - 9 * x ^ 3 + 10 = 0 ↔ x = principalRoot 3 20 / 2 ∨ x = principalRoot 3 2 := by
  have e : 2 * x ^ 6 - 9 * x ^ 3 + 10 = (2 * x ^ 3 - 5) * (x ^ 3 - 2) := by ring
  have h3 : Odd 3 := by decide
  have h20 : principalRoot 3 20 ^ 3 = 20 := principalRoot_pow (by norm_num) (Or.inl h3)
  rw [e, mul_eq_zero]
  constructor
  · rintro (h | h)
    · left
      have : (2 * x) ^ 3 = 20 := by nlinarith
      have h2 := (principalRoot_eq_iff_odd h3 20 (2 * x)).mpr this
      linarith
    · right
      exact (principalRoot_eq_iff_odd h3 2 x).mpr (by linarith)
  · rintro (h | h)
    · left
      rw [h]
      have : (principalRoot 3 20 / 2) ^ 3 = principalRoot 3 20 ^ 3 / 8 := by ring
      rw [this, h20]; norm_num
    · right
      have := (principalRoot_eq_iff_odd h3 2 x).mp h
      linarith

/-- Stitz-Zeager Exercise 3.3.30: `2x⁵ + 3x⁴ - 18x - 27 = (2x + 3)(x² - 3)(x² + 3)` has the real zeros
`-3/2` and `±√3`. -/
@[kb "stitzzeager2013" "Exercise 3.3.30, p. 292"]
theorem exer_3_3_30 (x : ℝ) :
    2 * x ^ 5 + 3 * x ^ 4 - 18 * x - 27 = 0 ↔ x = -(3 / 2) ∨ x = -√3 ∨ x = √3 := by
  have e : 2 * x ^ 5 + 3 * x ^ 4 - 18 * x - 27 = (2 * x + 3) * ((x ^ 2 - 3) * (x ^ 2 + 3)) := by
    ring
  have hp : x ^ 2 + 3 ≠ 0 := by nlinarith [sq_nonneg x]
  rw [e, mul_eq_zero, mul_eq_zero, sub_eq_zero, w7c_sq x 3 (by norm_num)]
  constructor
  · rintro (h | h | h)
    · left; linarith
    · right; exact h
    · exact absurd h hp
  · rintro (h | h)
    · left; linarith
    · right; left; exact h

/-- Stitz-Zeager Exercise 3.3.35: `9x³ = 5x² + x` iff `x ∈ {0, (5 ± √61)/18}`. -/
@[kb "stitzzeager2013" "Exercise 3.3.35, p. 293"]
theorem exer_3_3_35 (x : ℝ) :
    9 * x ^ 3 = 5 * x ^ 2 + x ↔ x = 0 ∨ x = (5 - √61) / 18 ∨ x = (5 + √61) / 18 := by
  have e : 9 * x ^ 3 - (5 * x ^ 2 + x) = x * (9 * x ^ 2 - 5 * x - 1) := by ring
  have a2 : 9 * x ^ 2 - 5 * x - 1 = 0 ↔ x = (5 - √61) / 18 ∨ x = (5 + √61) / 18 := by
    have key : 9 * x ^ 2 - 5 * x - 1 = 0 ↔ (18 * x - 5) ^ 2 = 61 := by
      constructor <;> intro h <;> nlinarith
    rw [key, w7c_sq _ _ (by norm_num)]
    constructor <;> rintro (h | h) <;> first | (left; linarith) | (right; linarith)
  rw [← sub_eq_zero, e, mul_eq_zero, a2]

/-- Stitz-Zeager Exercise 3.3.36: `9x² + 5x³ = 6x⁴` iff `x ∈ {0, (5 ± √241)/12}`. -/
@[kb "stitzzeager2013" "Exercise 3.3.36, p. 293"]
theorem exer_3_3_36 (x : ℝ) :
    9 * x ^ 2 + 5 * x ^ 3 = 6 * x ^ 4 ↔ x = 0 ∨ x = (5 - √241) / 12 ∨ x = (5 + √241) / 12 := by
  have e : 6 * x ^ 4 - (9 * x ^ 2 + 5 * x ^ 3) = x ^ 2 * (6 * x ^ 2 - 5 * x - 9) := by ring
  have a2 : 6 * x ^ 2 - 5 * x - 9 = 0 ↔ x = (5 - √241) / 12 ∨ x = (5 + √241) / 12 := by
    have key : 6 * x ^ 2 - 5 * x - 9 = 0 ↔ (12 * x - 5) ^ 2 = 241 := by
      constructor <;> intro h <;> nlinarith
    rw [key, w7c_sq _ _ (by norm_num)]
    constructor <;> rintro (h | h) <;> first | (left; linarith) | (right; linarith)
  rw [eq_comm, ← sub_eq_zero, e, mul_eq_zero, pow_eq_zero_iff two_ne_zero, a2]

/-- Stitz-Zeager Exercise 3.3.37: `x³ + 6 = 2x² + 5x` iff `x ∈ {-2, 1, 3}`. -/
@[kb "stitzzeager2013" "Exercise 3.3.37, p. 293"]
theorem exer_3_3_37 (x : ℝ) : x ^ 3 + 6 = 2 * x ^ 2 + 5 * x ↔ x = -2 ∨ x = 1 ∨ x = 3 := by
  have e : x ^ 3 + 6 - (2 * x ^ 2 + 5 * x) = (x + 2) * (x - 1) * (x - 3) := by ring
  rw [← sub_eq_zero, e, mul_eq_zero, mul_eq_zero, sub_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg]
  tauto

/-- Stitz-Zeager Exercise 3.3.38: `x⁴ + 2x³ = 12x² + 40x + 32` iff `x ∈ {-2, 4}`. -/
@[kb "stitzzeager2013" "Exercise 3.3.38, p. 293"]
theorem exer_3_3_38 (x : ℝ) : x ^ 4 + 2 * x ^ 3 = 12 * x ^ 2 + 40 * x + 32 ↔ x = -2 ∨ x = 4 := by
  have e : x ^ 4 + 2 * x ^ 3 - (12 * x ^ 2 + 40 * x + 32) = (x + 2) ^ 3 * (x - 4) := by ring
  rw [← sub_eq_zero, e, mul_eq_zero, pow_eq_zero_iff (by norm_num), sub_eq_zero,
    add_eq_zero_iff_eq_neg]

/-- Stitz-Zeager Exercise 3.3.39: `x³ - 7x² = 7 - x` iff `x = 7`. -/
@[kb "stitzzeager2013" "Exercise 3.3.39, p. 293"]
theorem exer_3_3_39 (x : ℝ) : x ^ 3 - 7 * x ^ 2 = 7 - x ↔ x = 7 := by
  have e : x ^ 3 - 7 * x ^ 2 - (7 - x) = (x - 7) * (x ^ 2 + 1) := by ring
  have hp : x ^ 2 + 1 ≠ 0 := by nlinarith [sq_nonneg x]
  rw [← sub_eq_zero, e, mul_eq_zero, sub_eq_zero]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h hp
  · intro h; left; exact h

/-- Stitz-Zeager Exercise 3.3.40: `2x³ = 19x² - 49x + 20` iff `x ∈ {1/2, 4, 5}`. -/
@[kb "stitzzeager2013" "Exercise 3.3.40, p. 293"]
theorem exer_3_3_40 (x : ℝ) : 2 * x ^ 3 = 19 * x ^ 2 - 49 * x + 20 ↔ x = 1 / 2 ∨ x = 4 ∨ x = 5 := by
  have e : 2 * x ^ 3 - (19 * x ^ 2 - 49 * x + 20) = (2 * x - 1) * (x - 4) * (x - 5) := by ring
  rw [← sub_eq_zero, e, mul_eq_zero, mul_eq_zero]
  constructor
  · rintro ((h | h) | h)
    · left; linarith
    · right; left; linarith
    · right; right; linarith
  · rintro (h | h | h)
    · left; left; linarith
    · left; right; linarith
    · right; linarith

/-- Stitz-Zeager Exercise 3.3.41: `x³ + x² = (11x + 10)/3` iff `x ∈ {-2, (3 ± √69)/6}`. -/
@[kb "stitzzeager2013" "Exercise 3.3.41, p. 293"]
theorem exer_3_3_41 (x : ℝ) :
    x ^ 3 + x ^ 2 = (11 * x + 10) / 3 ↔ x = -2 ∨ x = (3 - √69) / 6 ∨ x = (3 + √69) / 6 := by
  have e : x ^ 3 + x ^ 2 - (11 * x + 10) / 3 = (1 / 3) * ((x + 2) * (3 * x ^ 2 - 3 * x - 5)) := by
    ring
  have a2 : 3 * x ^ 2 - 3 * x - 5 = 0 ↔ x = (3 - √69) / 6 ∨ x = (3 + √69) / 6 := by
    have key : 3 * x ^ 2 - 3 * x - 5 = 0 ↔ (6 * x - 3) ^ 2 = 69 := by
      constructor <;> intro h <;> nlinarith
    rw [key, w7c_sq _ _ (by norm_num)]
    constructor <;> rintro (h | h) <;> first | (left; linarith) | (right; linarith)
  have a1 : x + 2 = 0 ↔ x = -2 := by constructor <;> intro h <;> linarith
  rw [← sub_eq_zero, e, mul_eq_zero, mul_eq_zero, a1, a2]
  constructor
  · rintro (h | h | h)
    · norm_num at h
    · left; exact h
    · right; exact h
  · rintro (h | h)
    · right; left; exact h
    · right; right; exact h

/-- Stitz-Zeager Exercise 3.3.42: `x⁴ + 2x² = 15` iff `x = ±√3`. -/
@[kb "stitzzeager2013" "Exercise 3.3.42, p. 293"]
theorem exer_3_3_42 (x : ℝ) : x ^ 4 + 2 * x ^ 2 = 15 ↔ x = -√3 ∨ x = √3 := by
  have e : x ^ 4 + 2 * x ^ 2 - 15 = (x ^ 2 + 5) * (x ^ 2 - 3) := by ring
  rw [← sub_eq_zero, e, mul_eq_zero, sub_eq_zero, w7c_sq x 3 (by norm_num)]
  constructor
  · rintro (h | h)
    · exfalso; nlinarith [sq_nonneg x]
    · exact h
  · intro h; right; exact h

/-- Stitz-Zeager Exercise 3.3.43: `14x² + 5 = 3x⁴` iff `x = ±√5`. -/
@[kb "stitzzeager2013" "Exercise 3.3.43, p. 293"]
theorem exer_3_3_43 (x : ℝ) : 14 * x ^ 2 + 5 = 3 * x ^ 4 ↔ x = -√5 ∨ x = √5 := by
  have e : 3 * x ^ 4 - (14 * x ^ 2 + 5) = (3 * x ^ 2 + 1) * (x ^ 2 - 5) := by ring
  rw [eq_comm, ← sub_eq_zero, e, mul_eq_zero, sub_eq_zero, w7c_sq x 5 (by norm_num)]
  constructor
  · rintro (h | h)
    · exfalso; nlinarith [sq_nonneg x]
    · exact h
  · intro h; right; exact h

/-- Stitz-Zeager Exercise 3.3.44: `2x⁵ + 3x⁴ = 18x + 27` iff `x ∈ {-3/2, ±√3}`. -/
@[kb "stitzzeager2013" "Exercise 3.3.44, p. 293"]
theorem exer_3_3_44 (x : ℝ) :
    2 * x ^ 5 + 3 * x ^ 4 = 18 * x + 27 ↔ x = -(3 / 2) ∨ x = -√3 ∨ x = √3 := by
  rw [← sub_eq_zero]
  have := exer_3_3_30 x
  rw [← this]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 3.3.48: `4x³ ≥ 3x + 1` iff `x ∈ {-1/2} ∪ [1, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 3.3.48, p. 293"]
theorem exer_3_3_48 : {x : ℝ | 3 * x + 1 ≤ 4 * x ^ 3} = {-(1 / 2)} ∪ Set.Ici 1 := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff, Set.mem_Ici]
  have e : 4 * x ^ 3 - (3 * x + 1) = (x - 1) * (2 * x + 1) ^ 2 := by ring
  constructor
  · intro h
    have h' : 0 ≤ (x - 1) * (2 * x + 1) ^ 2 := by rw [← e]; linarith
    by_cases hx : 2 * x + 1 = 0
    · left; linarith
    · right
      have hp : 0 < (2 * x + 1) ^ 2 := by positivity
      by_contra hc
      push Not at hc
      nlinarith
  · rintro (h | h)
    · rw [h]; norm_num
    · have : 0 ≤ (x - 1) * (2 * x + 1) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
      linarith

/-- Stitz-Zeager Exercise 3.3.50: `3x² + 2x < x⁴` iff `x ∈ (-∞, -1) ∪ (-1, 0) ∪ (2, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 3.3.50, p. 293"]
theorem exer_3_3_50 :
    {x : ℝ | 3 * x ^ 2 + 2 * x < x ^ 4} = Set.Iio (-1) ∪ Set.Ioo (-1) 0 ∪ Set.Ioi 2 := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioo, Set.mem_Ioi]
  have e : x ^ 4 - (3 * x ^ 2 + 2 * x) = x * (x - 2) * (x + 1) ^ 2 := by ring
  constructor
  · intro h
    have h' : 0 < x * (x - 2) * (x + 1) ^ 2 := by rw [← e]; linarith
    have hne : x + 1 ≠ 0 := by
      intro h0; rw [h0] at h'; norm_num at h'
    have hp : 0 < (x + 1) ^ 2 := by positivity
    have h2 : 0 < x * (x - 2) := by
      by_contra hc
      push Not at hc
      nlinarith
    by_cases hx : x < 0
    · rcases lt_or_gt_of_ne hne with h3 | h3
      · left; left; linarith
      · left; right; exact ⟨by linarith, hx⟩
    · right
      push Not at hx
      by_contra hc
      push Not at hc
      nlinarith
  · rintro ((h | ⟨h1, h2⟩) | h)
    · have : 0 < x * (x - 2) := mul_pos_of_neg_of_neg (by linarith) (by linarith)
      have hp : 0 < (x + 1) ^ 2 := by nlinarith
      nlinarith [mul_pos this hp]
    · have : 0 < x * (x - 2) := mul_pos_of_neg_of_neg (by linarith) (by linarith)
      have hp : 0 < (x + 1) ^ 2 := by nlinarith
      nlinarith [mul_pos this hp]
    · have : 0 < x * (x - 2) := mul_pos (by linarith) (by linarith)
      have hp : 0 < (x + 1) ^ 2 := by nlinarith
      nlinarith [mul_pos this hp]

/-- Stitz-Zeager Exercise 3.3.56: with `C(x) = .03x³ - 4.5x² + 225x + 250`, `C(82) = 4983.04`,
`C(83) = 5078.11`, and for a whole number `n` of systems `C(n) ≤ 5000` iff `n ≤ 82`. -/
@[kb "stitzzeager2013" "Exercise 3.3.56, p. 294"]
theorem exer_3_3_56 (C : ℝ → ℝ) (hC : ∀ x, C x = 3 / 100 * x ^ 3 - 9 / 2 * x ^ 2 + 225 * x + 250) :
    C 82 = 498304 / 100 ∧ C 83 = 507811 / 100 ∧ ∀ n : ℕ, C n ≤ 5000 ↔ n ≤ 82 := by
  refine ⟨by rw [hC]; norm_num, by rw [hC]; norm_num, fun n => ?_⟩
  have key : C n = 3 / 100 * ((n : ℝ) - 50) ^ 3 + 4000 := by rw [hC]; ring
  rw [key]
  constructor
  · intro h
    by_contra hc
    have h83 : (83 : ℝ) ≤ n := by
      have : 83 ≤ n := by omega
      exact_mod_cast this
    have h33 : (33 : ℝ) ≤ (n : ℝ) - 50 := by linarith
    have := pow_le_pow_left₀ (by norm_num) h33 3
    norm_num at this
    linarith
  · intro h
    have h82 : (n : ℝ) ≤ 82 := by exact_mod_cast h
    have h32 : (n : ℝ) - 50 ≤ 32 := by linarith
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hp : (-50 : ℝ) ≤ (n : ℝ) - 50 := by linarith
    have : ((n : ℝ) - 50) ^ 3 ≤ 32 ^ 3 := by
      rcases le_or_gt 0 ((n : ℝ) - 50) with h0 | h0
      · exact pow_le_pow_left₀ h0 h32 3
      · nlinarith [sq_nonneg ((n : ℝ) - 50), pow_pos (by norm_num : (0 : ℝ) < 32) 3]
    norm_num at this
    linarith

end UndergradKB.Precalculus.Course
