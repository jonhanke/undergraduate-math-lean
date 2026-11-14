import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Sqrt
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 9 (Stitz-Zeager): exercises with the book's answers (wave 8), Section 9.2 -/

namespace UndergradKB.Precalculus.Course

/-- Stitz-Zeager Exercise 9.2.42: what goes wrong with the infinite sums `∑ 2^(k-1)`, `∑ 1.0001^(k-1)` and
`∑ (-1)^(k-1)` (indices `k ≥ 1`, written here with the index shifted to start at `0`): each is a geometric series
with ratio of absolute value at least `1`, so none of them is summable and the finite geometric-sum formula gives no
value for them. -/
@[kb "stitzzeager2013" "Exercise 9.2.42, p. 683"]
theorem exer_9_2_42 :
    ¬ Summable (fun k : ℕ => (2 : ℝ) ^ k) ∧ ¬ Summable (fun k : ℕ => (1.0001 : ℝ) ^ k) ∧
      ¬ Summable (fun k : ℕ => (-1 : ℝ) ^ k) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := summable_geometric_iff_norm_lt_one.1 h
    norm_num at this
  · have := summable_geometric_iff_norm_lt_one.1 h
    norm_num at this
  · have := summable_geometric_iff_norm_lt_one.1 h
    norm_num at this

end UndergradKB.Precalculus.Course
