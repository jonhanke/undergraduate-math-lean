import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Interval.Set.Basic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 7 (Stitz-Zeager): exercises with the book's answers (wave 8), Section 7.2 -/

namespace UndergradKB.Precalculus.Course

open Set

/-- Stitz-Zeager Exercise 7.2.19: a circle with centre `(h, k)` and radius `r > 0` is obtained from the unit
circle by the transformation `x ↦ (x - h)/r`, `y ↦ (y - k)/r`: `(x-h)² + (y-k)² = r²` holds exactly when
`((x-h)/r)² + ((y-k)/r)² = 1`. -/
@[kb "stitzzeager2013" "Exercise 7.2.19, p. 514"]
theorem exer_7_2_19 (h k r x y : ℝ) (hr : 0 < r) :
    (x - h) ^ 2 + (y - k) ^ 2 = r ^ 2 ↔ ((x - h) / r) ^ 2 + ((y - k) / r) ^ 2 = 1 := by
  have hr2 : r ^ 2 ≠ 0 := by positivity
  rw [div_pow, div_pow, ← add_div, div_eq_one_iff_eq hr2]

/-- Stitz-Zeager Exercise 7.2.20: the top half of the unit circle is the graph of `y = √(1 - x²)` on `[-1, 1]`. -/
@[kb "stitzzeager2013" "Exercise 7.2.20, p. 514"]
theorem exer_7_2_20 (x y : ℝ) :
    (x ^ 2 + y ^ 2 = 1 ∧ 0 ≤ y) ↔ (-1 ≤ x ∧ x ≤ 1 ∧ y = Real.sqrt (1 - x ^ 2)) := by
  constructor
  · rintro ⟨h, hy⟩
    refine ⟨by nlinarith [sq_nonneg y], by nlinarith [sq_nonneg y], ?_⟩
    rw [show 1 - x ^ 2 = y ^ 2 by linarith, Real.sqrt_sq hy]
  · rintro ⟨h1, h2, h3⟩
    have h0 : 0 ≤ 1 - x ^ 2 := by nlinarith
    refine ⟨?_, by rw [h3]; exact Real.sqrt_nonneg _⟩
    rw [h3, Real.sq_sqrt h0]; ring

/-- Stitz-Zeager Exercise 7.2.21: a one-to-one function whose graph is half of the unit circle:
`f(x) = √(1 - x²)` for `-1 ≤ x < 0` and `f(x) = -√(1 - x²)` for `0 ≤ x < 1`. -/
@[kb "stitzzeager2013" "Exercise 7.2.21, p. 514"]
theorem exer_7_2_21 (f : ℝ → ℝ) (hf : f = fun x => if x < 0 then Real.sqrt (1 - x ^ 2) else -Real.sqrt (1 - x ^ 2)) :
    InjOn f (Ico (-1 : ℝ) 1) ∧ ∀ x ∈ Ico (-1 : ℝ) 1, x ^ 2 + (f x) ^ 2 = 1 := by
  subst hf
  constructor
  · intro x hx y hy h
    have hx0 : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    have hy0 : 0 ≤ 1 - y ^ 2 := by nlinarith [hy.1, hy.2]
    by_cases hxn : x < 0 <;> by_cases hyn : y < 0 <;> simp only [hxn, hyn, if_true, if_false] at h
    · have := (Real.sqrt_inj hx0 hy0).1 h
      have h2 : (x - y) * (x + y) = 0 := by linarith
      rcases mul_eq_zero.1 h2 with h3 | h3
      · linarith
      · linarith
    · have hpos : 0 < Real.sqrt (1 - y ^ 2) := Real.sqrt_pos.2 (by nlinarith [hy.2, not_lt.1 hyn])
      linarith [Real.sqrt_nonneg (1 - x ^ 2)]
    · have hpos : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.2 (by nlinarith [hx.2, not_lt.1 hxn])
      linarith [Real.sqrt_nonneg (1 - y ^ 2)]
    · have h' := neg_inj.1 h
      have := (Real.sqrt_inj hx0 hy0).1 h'
      have h2 : (x - y) * (x + y) = 0 := by linarith
      rcases mul_eq_zero.1 h2 with h3 | h3
      · linarith
      · linarith [not_lt.1 hxn, not_lt.1 hyn]
  · intro x hx
    have hx0 : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    by_cases hxn : x < 0
    · simp only [hxn, if_true]
      rw [Real.sq_sqrt hx0]; ring
    · simp only [hxn, if_false]
      rw [neg_sq, Real.sq_sqrt hx0]; ring

end UndergradKB.Precalculus.Course
