import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 9 (Stitz-Zeager): worked examples, wave 5 -/

namespace UndergradKB.Precalculus.Course

open Finset

/-- Stitz-Zeager Example 9.2.1(2b): the alternating sum `1 - 1/2 + 1/3 - ... + 1/117` is
`∑_{n=1}^{117} (-1)^(n-1) / n`: the first terms are `1, -1/2, 1/3, -1/4`, the last term
(`n = 117`) is `+1/117`, and the sum is the odd reciprocals minus the even ones. -/
@[kb "stitzzeager2013" "Example 9.2.1, p. 674"]
theorem ex_9_2_1_2_b :
    ((-1 : ℚ) ^ (1 - 1) / 1 = 1 ∧ (-1 : ℚ) ^ (2 - 1) / 2 = -1 / 2 ∧ (-1 : ℚ) ^ (3 - 1) / 3 = 1 / 3 ∧
      (-1 : ℚ) ^ (4 - 1) / 4 = -1 / 4 ∧ (-1 : ℚ) ^ (117 - 1) / 117 = 1 / 117) ∧
    ∑ n ∈ Icc (1 : ℕ) 117, (-1 : ℚ) ^ (n - 1) / (n : ℚ) =
      ∑ n ∈ (Icc (1 : ℕ) 117).filter (fun n => n % 2 = 1), (1 : ℚ) / (n : ℚ) -
        ∑ n ∈ (Icc (1 : ℕ) 117).filter (fun n => n % 2 = 0), (1 : ℚ) / (n : ℚ) := by
  refine ⟨by norm_num, ?_⟩
  rw [← Finset.sum_filter_add_sum_filter_not (Icc (1 : ℕ) 117) (fun n => n % 2 = 1)]
  have h1 : ∑ n ∈ (Icc (1 : ℕ) 117).filter (fun n => n % 2 = 1), (-1 : ℚ) ^ (n - 1) / (n : ℚ) =
      ∑ n ∈ (Icc (1 : ℕ) 117).filter (fun n => n % 2 = 1), (1 : ℚ) / (n : ℚ) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_filter] at hn
    obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    subst hk
    simp
  have h2 : ∑ n ∈ (Icc (1 : ℕ) 117).filter (fun n => ¬ n % 2 = 1), (-1 : ℚ) ^ (n - 1) / (n : ℚ) =
      -∑ n ∈ (Icc (1 : ℕ) 117).filter (fun n => n % 2 = 0), (1 : ℚ) / (n : ℚ) := by
    rw [← Finset.sum_neg_distrib]
    have hs : (Icc (1 : ℕ) 117).filter (fun n => ¬ n % 2 = 1) =
        (Icc (1 : ℕ) 117).filter (fun n => n % 2 = 0) := by
      ext n; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    rw [hs]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hn2⟩, hn3⟩ := hn
    obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 2 * k + 2 := ⟨n / 2 - 1, by omega⟩
    subst hk
    have : 2 * k + 2 - 1 = 2 * k + 1 := by omega
    rw [this, pow_succ, pow_mul]
    simp
    ring
  rw [h1, h2]; ring

end UndergradKB.Precalculus.Course
