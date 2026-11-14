import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Real.Pi.Bounds
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 10 (Stitz-Zeager): worked examples, wave 6

The decimal answer of Example 10.6.6, which wave 5 stated only as `π/8 < θ < π/6`: the pitch angle `arctan (1/2)` is
`26.56°` to two decimals. The bounds come from the Maclaurin series of `arctan` (`Real.hasSum_arctan`) and the
alternating-series bounds of Mathlib. -/

namespace UndergradKB.Precalculus.Course

open Real Finset Filter

/-- Partial sums of the arctangent series at `1/2` bracket `arctan (1/2)`. -/
private theorem arctan_half_bracket (k : ℕ) :
    ∑ i ∈ range (2 * k), (-1) ^ i * ((1 / 2 : ℝ) ^ (2 * i + 1) / (2 * i + 1)) ≤ arctan (1 / 2) ∧
      arctan (1 / 2) ≤ ∑ i ∈ range (2 * k + 1), (-1) ^ i * ((1 / 2 : ℝ) ^ (2 * i + 1) / (2 * i + 1)) := by
  set f : ℕ → ℝ := fun i => (1 / 2 : ℝ) ^ (2 * i + 1) / (2 * i + 1)
  have hs := Real.hasSum_arctan (x := 1 / 2) (by norm_num [abs_of_pos])
  have hs' : HasSum (fun i => (-1) ^ i * f i) (arctan (1 / 2)) := by
    convert hs using 2 with i
    simp only [f]; push_cast; ring
  have ht := hs'.tendsto_sum_nat
  have hf : Antitone f := by
    refine antitone_nat_of_succ_le fun n => ?_
    simp only [f]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (1 / 2 : ℝ) ^ (2 * (n + 1) + 1) = (1 / 2) ^ (2 * n + 1) * (1 / 4) := by
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, pow_add]; norm_num
    rw [h1]
    have h2 : (0 : ℝ) < (1 / 2) ^ (2 * n + 1) := by positivity
    push_cast
    nlinarith
  exact ⟨hf.alternating_series_le_tendsto ht k, hf.tendsto_le_alternating_series ht k⟩

/-- Stitz-Zeager Example 10.6.6, the decimal answer: the pitch angle `θ = arctan (6/12)` of a roof with rise `6`
over run `12` is `26.56°` to two decimal places, i.e. `26.56 < θ · 180/π < 26.57`. -/
@[kb "stitzzeager2013" "Example 10.6.6, p. 849"]
theorem ex_10_6_6_degrees :
    (26.56 : ℝ) < arctan (6 / 12) * 180 / π ∧ arctan (6 / 12) * 180 / π < 26.57 := by
  have h : (6 : ℝ) / 12 = 1 / 2 := by norm_num
  rw [h]
  obtain ⟨lo, -⟩ := arctan_half_bracket 3
  obtain ⟨-, hi⟩ := arctan_half_bracket 2
  simp only [sum_range_succ, sum_range_zero] at lo hi
  norm_num at lo hi
  have p1 := pi_gt_d6
  have p2 := pi_lt_d6
  have hp : 0 < π := pi_pos
  constructor
  · rw [lt_div_iff₀ hp]; nlinarith
  · rw [div_lt_iff₀ hp]; nlinarith

end UndergradKB.Precalculus.Course
