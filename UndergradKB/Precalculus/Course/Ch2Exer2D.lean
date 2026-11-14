import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.NatSqrt
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 2 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 2.4 -/

namespace UndergradKB.Precalculus.Course

/-! ## Section 2.4 -/

/-- Stitz-Zeager Exercise 2.4.16: `|3 - x| ≥ x - 5` holds for every real `x`. -/
@[kb "stitzzeager2013" "Exercise 2.4.16, p. 232"]
theorem exer_2_4_16 : {x : ℝ | |3 - x| ≥ x - 5} = Set.univ := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
  rcases abs_cases (3 - x) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith

/-- Stitz-Zeager Exercise 2.4.20: `9x² + 16 ≥ 24x` holds for every real `x`. -/
@[kb "stitzzeager2013" "Exercise 2.4.20, p. 232"]
theorem exer_2_4_20 : {x : ℝ | 9 * x ^ 2 + 16 ≥ 24 * x} = Set.univ := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
  nlinarith [sq_nonneg (3 * x - 4)]

/-- Stitz-Zeager Exercise 2.4.22: `x² + 1 < 0` has no real solution. -/
@[kb "stitzzeager2013" "Exercise 2.4.22, p. 232"]
theorem exer_2_4_22 : {x : ℝ | x ^ 2 + 1 < 0} = ∅ := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
  nlinarith [sq_nonneg x]

/-- Stitz-Zeager Exercise 2.4.27: `2 ≤ |x² - 9| < 9` iff `x` lies in
`(-3√2, -√11] ∪ [-√7, 0) ∪ (0, √7] ∪ [√11, 3√2)` (the endpoints `±3√2` give `|x² - 9| = 9`). -/
@[kb "stitzzeager2013" "Exercise 2.4.27, p. 232"]
theorem exer_2_4_27 (x : ℝ) :
    (2 ≤ |x ^ 2 - 9| ∧ |x ^ 2 - 9| < 9) ↔
      ((-(3 * Real.sqrt 2) < x ∧ x ≤ -Real.sqrt 11) ∨ (-Real.sqrt 7 ≤ x ∧ x < 0) ∨
        (0 < x ∧ x ≤ Real.sqrt 7) ∨ (Real.sqrt 11 ≤ x ∧ x < 3 * Real.sqrt 2)) := by
  have s2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have s7 : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have s11 : Real.sqrt 11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  have p2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have p7 : 0 < Real.sqrt 7 := Real.sqrt_pos.mpr (by norm_num)
  have p11 : 0 < Real.sqrt 11 := Real.sqrt_pos.mpr (by norm_num)
  constructor
  · rintro ⟨h1, h2⟩
    rcases abs_cases (x ^ 2 - 9) with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · -- x² ≥ 11 and x² < 18
      rcases le_or_gt 0 x with hx | hx
      · right; right; right
        constructor
        · by_contra hc; push_neg at hc; nlinarith
        · by_contra hc; push_neg at hc; nlinarith
      · left
        constructor
        · by_contra hc; push_neg at hc; nlinarith
        · by_contra hc; push_neg at hc; nlinarith
    · -- 0 < x² ≤ 7
      rcases lt_trichotomy x 0 with hx | hx | hx
      · right; left
        constructor
        · by_contra hc; push_neg at hc; nlinarith
        · exact hx
      · exfalso; subst hx; norm_num at h2
      · right; right; left
        constructor
        · exact hx
        · by_contra hc; push_neg at hc; nlinarith
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · rw [abs_of_nonneg (by nlinarith)]; constructor <;> nlinarith
    · rw [abs_of_nonpos (by nlinarith)]; constructor <;> nlinarith
    · rw [abs_of_nonpos (by nlinarith)]; constructor <;> nlinarith
    · rw [abs_of_nonneg (by nlinarith)]; constructor <;> nlinarith

/-- Stitz-Zeager Exercise 2.4.29: `x² + x + 1 ≥ 0` holds for every real `x`. -/
@[kb "stitzzeager2013" "Exercise 2.4.29, p. 232"]
theorem exer_2_4_29 : {x : ℝ | x ^ 2 + x + 1 ≥ 0} = Set.univ := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
  nlinarith [sq_nonneg (2 * x + 1)]

/-- Stitz-Zeager Exercise 2.4.31: `x|x + 5| ≥ -6` iff `x ∈ [-6, -3] ∪ [-2, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 2.4.31, p. 232"]
theorem exer_2_4_31 (x : ℝ) :
    x * |x + 5| ≥ -6 ↔ x ∈ Set.Icc (-6 : ℝ) (-3) ∪ Set.Ici (-2) := by
  simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ici]
  constructor
  · intro h
    rcases abs_cases (x + 5) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1] at h
      rcases le_or_gt (-2) x with h3 | h3
      · right; exact h3
      · left
        constructor
        · linarith
        · refine le_of_not_gt fun hc => ?_
          nlinarith
    · rw [h1] at h
      left
      constructor
      · refine le_of_not_gt fun hc => ?_
        nlinarith
      · linarith
  · intro h
    rcases abs_cases (x + 5) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1]
      rcases h with ⟨h3, h4⟩ | h3 <;> nlinarith
    · rw [h1]
      rcases h with ⟨h3, h4⟩ | h3
      · nlinarith
      · linarith

/-- Stitz-Zeager Exercise 2.4.32: `x|x - 3| < 2` iff `x < 1` or `2 < x < (3 + √17)/2`. -/
@[kb "stitzzeager2013" "Exercise 2.4.32, p. 232"]
theorem exer_2_4_32 (x : ℝ) :
    x * |x - 3| < 2 ↔ x < 1 ∨ (2 < x ∧ x < (3 + Real.sqrt 17) / 2) := by
  have s : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have p : 0 < Real.sqrt 17 := Real.sqrt_pos.mpr (by norm_num)
  have lo : 4 < Real.sqrt 17 := by nlinarith
  have hi : Real.sqrt 17 < 5 := by nlinarith
  constructor
  · intro h
    rcases abs_cases (x - 3) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1] at h
      right; constructor
      · nlinarith
      · by_contra hc; push_neg at hc; nlinarith
    · rw [h1] at h
      by_contra hc; push_neg at hc
      nlinarith [hc.1, hc.2 (by nlinarith)]
  · intro h
    rcases abs_cases (x - 3) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1]
      rcases h with h | ⟨h3, h4⟩
      · linarith
      · nlinarith
    · rw [h1]
      rcases h with h | ⟨h3, h4⟩
      · nlinarith
      · nlinarith

/-- Stitz-Zeager Exercise 2.4.37: for `s(t) = -4.9t² + 30t + 2`, `s(t) > 35` iff `t` lies between the
roots `5(30 ∓ √253.2)/49`, about `1.44` and `4.68`. -/
@[kb "stitzzeager2013" "Exercise 2.4.37, p. 233"]
theorem exer_2_4_37 (s : ℝ → ℝ) (hs : ∀ t, s t = -(49 / 10) * t ^ 2 + 30 * t + 2) (t : ℝ) :
    s t > 35 ↔ 5 * (30 - Real.sqrt (1266 / 5)) / 49 < t ∧ t < 5 * (30 + Real.sqrt (1266 / 5)) / 49 := by
  have hr : Real.sqrt (1266 / 5) ^ 2 = 1266 / 5 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt (1266 / 5) := Real.sqrt_pos.mpr (by norm_num)
  have key : (t - 5 * (30 - Real.sqrt (1266 / 5)) / 49) * (t - 5 * (30 + Real.sqrt (1266 / 5)) / 49) =
      (10 / 49) * (35 - s t) := by
    rw [hs]; linear_combination (-25 / 2401) * hr
  have hlt : 5 * (30 - Real.sqrt (1266 / 5)) / 49 < 5 * (30 + Real.sqrt (1266 / 5)) / 49 := by
    linarith
  constructor
  · intro h
    have hneg : (t - 5 * (30 - Real.sqrt (1266 / 5)) / 49) *
        (t - 5 * (30 + Real.sqrt (1266 / 5)) / 49) < 0 := by rw [key]; linarith
    rcases mul_neg_iff.mp hneg with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by linarith, by linarith⟩
    · exfalso; linarith
  · rintro ⟨h1, h2⟩
    have : (t - 5 * (30 - Real.sqrt (1266 / 5)) / 49) *
        (t - 5 * (30 + Real.sqrt (1266 / 5)) / 49) < 0 :=
      mul_neg_of_pos_of_neg (by linarith) (by linarith)
    rw [key] at this; linarith

/-- Stitz-Zeager Exercise 2.4.37 (numerical form): the endpoints `5(30 ∓ √253.2)/49` round to
`1.44` and `4.68`. -/
@[kb "stitzzeager2013" "Exercise 2.4.37, p. 233"]
theorem exer_2_4_37_bounds :
    (1.435 : ℝ) < 5 * (30 - Real.sqrt (1266 / 5)) / 49 ∧
      5 * (30 - Real.sqrt (1266 / 5)) / 49 < 1.44 ∧
      (4.68 : ℝ) < 5 * (30 + Real.sqrt (1266 / 5)) / 49 ∧
      5 * (30 + Real.sqrt (1266 / 5)) / 49 < 4.685 := by
  have hlo : (15.912 : ℝ) < Real.sqrt (1266 / 5) := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hhi : Real.sqrt (1266 / 5) < 15.913 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Stitz-Zeager Exercise 2.4.40: `3x` is within `2` units of `-1` iff `-1 ≤ x ≤ 1/3`. -/
@[kb "stitzzeager2013" "Exercise 2.4.40, p. 233"]
theorem exer_2_4_40 (x : ℝ) : |3 * x - (-1)| ≤ 2 ↔ x ∈ Set.Icc (-1 : ℝ) (1 / 3) := by
  rw [Set.mem_Icc, abs_le]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

end UndergradKB.Precalculus.Course
