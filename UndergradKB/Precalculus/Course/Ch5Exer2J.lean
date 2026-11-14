import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Interval.Set.Basic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 5 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 5.3 (one more graph) -/

namespace UndergradKB.Precalculus.Course

open Set

/-- Stitz-Zeager Exercise 5.3.5: `f(x) = ⁴√(16x/(x²-9))` (written as an iterated square root) has domain
`(-3, 0] ∪ (3, ∞)`, its only zero is `0`, and it is positive elsewhere on the domain. -/
@[kb "stitzzeager2013" "Exercise 5.3.5, p. 419"]
theorem exer_5_3_5 (f : ℝ → ℝ) (hf : f = fun x => Real.sqrt (Real.sqrt (16 * x / (x ^ 2 - 9)))) :
    {x : ℝ | x ^ 2 - 9 ≠ 0 ∧ 0 ≤ 16 * x / (x ^ 2 - 9)} = Ioc (-3) 0 ∪ Ioi 3 ∧
    (∀ x ∈ Ioc (-3 : ℝ) 0 ∪ Ioi 3, f x = 0 ↔ x = 0) ∧
    (∀ x ∈ Ioc (-3 : ℝ) 0 ∪ Ioi 3, x ≠ 0 → 0 < f x) := by
  subst hf
  have dom : {x : ℝ | x ^ 2 - 9 ≠ 0 ∧ 0 ≤ 16 * x / (x ^ 2 - 9)} = Ioc (-3) 0 ∪ Ioi 3 := by
    ext x
    simp only [mem_ofPred_eq, mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro ⟨h1, h2⟩
      rcases (div_nonneg_iff).1 h2 with ⟨a, b⟩ | ⟨a, b⟩
      · right
        have : x ^ 2 - 9 > 0 := lt_of_le_of_ne b (Ne.symm h1)
        by_contra hc; push Not at hc; nlinarith
      · left
        have : x ^ 2 - 9 < 0 := lt_of_le_of_ne b h1
        refine ⟨?_, by linarith⟩
        by_contra hc; push Not at hc; nlinarith
    · rintro (⟨h1, h2⟩ | h)
      · refine ⟨by nlinarith, div_nonneg_of_nonpos (by linarith) (by nlinarith)⟩
      · refine ⟨by nlinarith, div_nonneg (by linarith) (by nlinarith)⟩
  have inner : ∀ x ∈ Ioc (-3 : ℝ) 0 ∪ Ioi 3, 0 ≤ 16 * x / (x ^ 2 - 9) := by
    intro x hx
    rw [← dom] at hx
    exact hx.2
  refine ⟨dom, fun x hx => ?_, fun x hx hx0 => ?_⟩
  · show Real.sqrt (Real.sqrt (16 * x / (x ^ 2 - 9))) = 0 ↔ x = 0
    rw [Real.sqrt_eq_zero (Real.sqrt_nonneg _), Real.sqrt_eq_zero (inner x hx), div_eq_zero_iff]
    have hne : x ^ 2 - 9 ≠ 0 := by rw [← dom] at hx; exact hx.1
    simp [hne]
  · show 0 < Real.sqrt (Real.sqrt (16 * x / (x ^ 2 - 9)))
    have hne : x ^ 2 - 9 ≠ 0 := by rw [← dom] at hx; exact hx.1
    have hp : 0 < 16 * x / (x ^ 2 - 9) := by
      refine lt_of_le_of_ne (inner x hx) (fun h => ?_)
      rcases div_eq_zero_iff.1 h.symm with h | h
      · exact hx0 (by linarith)
      · exact hne h
    exact Real.sqrt_pos.2 (Real.sqrt_pos.2 hp)

end UndergradKB.Precalculus.Course
