import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 3 (Stitz-Zeager): exercises with the book's answers (wave 8), Sections 3.1 and 3.3,
definite facts of exercises that print no answer -/

namespace UndergradKB.Precalculus.Course

open Set

/-- Stitz-Zeager Exercise 3.1.37: for `f(x) = (x-1)(x-2)²(x-3)³(x-4)⁴(x-5)⁵` the zeros are `1,...,5`; the sign of
`f` away from `2,3,4,5` is the sign of `(x-1)(x-3)(x-5)`, so the graph crosses the axis at `1, 3, 5` (odd
multiplicity) and touches it at `2, 4` (even multiplicity). -/
@[kb "stitzzeager2013" "Exercise 3.1.37, p. 261"]
theorem exer_3_1_37 (f : ℝ → ℝ)
    (hf : ∀ x, f x = (x - 1) * (x - 2) ^ 2 * (x - 3) ^ 3 * (x - 4) ^ 4 * (x - 5) ^ 5) :
    (f 1 = 0 ∧ f 2 = 0 ∧ f 3 = 0 ∧ f 4 = 0 ∧ f 5 = 0) ∧
      ∀ x : ℝ, x ≠ 2 → x ≠ 3 → x ≠ 4 → x ≠ 5 →
        (0 < f x ↔ 0 < (x - 1) * (x - 3) * (x - 5)) ∧ (f x < 0 ↔ (x - 1) * (x - 3) * (x - 5) < 0) := by
  refine ⟨?_, fun x h2 h3 h4 h5 => ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [hf] <;> norm_num
  · have a2 : x - 2 ≠ 0 := sub_ne_zero.mpr h2
    have a3 : x - 3 ≠ 0 := sub_ne_zero.mpr h3
    have a4 : x - 4 ≠ 0 := sub_ne_zero.mpr h4
    have a5 : x - 5 ≠ 0 := sub_ne_zero.mpr h5
    have hQ : 0 < (x - 2) ^ 2 * (x - 3) ^ 2 * (x - 4) ^ 4 * (x - 5) ^ 4 := by positivity
    have key : f x = ((x - 1) * (x - 3) * (x - 5)) * ((x - 2) ^ 2 * (x - 3) ^ 2 * (x - 4) ^ 4 * (x - 5) ^ 4) := by
      rw [hf]; ring
    rw [key]
    constructor
    · constructor
      · intro h
        by_contra hP
        push_neg at hP
        nlinarith [mul_nonneg (neg_nonneg.mpr hP) hQ.le]
      · intro h; exact mul_pos h hQ
    · constructor
      · intro h
        by_contra hP
        push_neg at hP
        nlinarith [mul_nonneg hP hQ.le]
      · intro h; exact mul_neg_of_neg_of_pos h hQ

/-- Stitz-Zeager Exercise 3.3.57: `f(x) = 5x⁷ - 33x⁶ + 3x⁵ - 71x⁴ - 597x³ + 2097x² - 1971x + 567` factors as
`(x-1)²(x+3)(5x-3)(x-7)(x²+9)`, so its real zeros are `1` (multiplicity 2), `-3`, `3/5`, `7`, and the
`y`-intercept is `567`. -/
@[kb "stitzzeager2013" "Exercise 3.3.57, p. 294"]
theorem exer_3_3_57 (f : ℝ → ℝ)
    (hf : ∀ x, f x = 5 * x ^ 7 - 33 * x ^ 6 + 3 * x ^ 5 - 71 * x ^ 4 - 597 * x ^ 3 + 2097 * x ^ 2 - 1971 * x + 567) :
    (∀ x, f x = (x - 1) ^ 2 * (x + 3) * (5 * x - 3) * (x - 7) * (x ^ 2 + 9)) ∧
      {x : ℝ | f x = 0} = {1, -3, 3 / 5, 7} ∧ f 0 = 567 := by
  have key : ∀ x, f x = (x - 1) ^ 2 * (x + 3) * (5 * x - 3) * (x - 7) * (x ^ 2 + 9) := by
    intro x; rw [hf]; ring
  refine ⟨key, ?_, by rw [hf]; norm_num⟩
  ext x
  simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff, key]
  constructor
  · intro h
    have h9 : x ^ 2 + 9 ≠ 0 := by positivity
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · rcases mul_eq_zero.mp h with h | h
          · left
            have h' : x - 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h
            linarith
          · right; left; linarith
        · right; right; left; linarith
      · right; right; right; linarith
    · exact absurd h h9
  · rintro (rfl | rfl | rfl | rfl) <;> norm_num

end UndergradKB.Precalculus.Course
