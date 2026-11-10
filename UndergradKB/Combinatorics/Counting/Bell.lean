import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Fin
import UndergradKB.Common.Attr

/-!
# Bell numbers

Source: Keller--Trotter, *Applied Combinatorics* (2017), p. 195.

The Bell number `B_n` is the number of partitions of an `n`-set.  Since a partition of an `n`-set
into `k` blocks is counted by Mathlib's Stirling number of the second kind, we define
`B_n = sum_{k <= n} S(n,k)`.  (The exponential generating function `exp(e^x - 1)` and the
non-P-recursiveness are not formalized; neither is the identification with `Finpartition` of
`Fin n`.)
-/

namespace UndergradKB.Combinatorics

open Finset Nat

/-- CO-213. The Bell number `B_n = sum_{k=0}^{n} S(n,k)`, the number of partitions of an `n`-set
(counted by number of blocks via Stirling numbers of the second kind). -/
@[kb "kellertrotter2017" "text, p. 195"]
def bellNumber (n : ℕ) : ℕ := ∑ k ∈ range (n + 1), Nat.stirlingSecond n k

/-- Auxiliary identity `S(n+1, k+1) = sum_j C(n,j) S(j,k)`: choose the elements sharing a block
with the new element. -/
lemma stirlingSecond_succ_succ_eq_sum (n : ℕ) :
    ∀ k, Nat.stirlingSecond (n + 1) (k + 1) =
      ∑ j ∈ range (n + 1), n.choose j * Nat.stirlingSecond j k := by
  induction n with
  | zero =>
    intro k
    simp [Nat.stirlingSecond_succ_succ]
  | succ n ih =>
    intro k
    rcases k with _ | m
    · rw [Nat.stirlingSecond_one_right, Finset.sum_range_succ']
      simp
    · have hz : Nat.stirlingSecond 0 (m + 1) = 0 := Nat.stirlingSecond_zero_succ m
      have hshift : ∑ j ∈ range (n + 1), n.choose (j + 1) * Nat.stirlingSecond (j + 1) (m + 1) =
          ∑ j ∈ range (n + 1), n.choose j * Nat.stirlingSecond j (m + 1) := by
        have h := Finset.sum_range_succ' (fun j => n.choose j * Nat.stirlingSecond j (m + 1)) (n + 1)
        rw [Finset.sum_range_succ] at h
        simp [hz] at h
        exact h.symm
      have e1 : ∑ j ∈ range (n + 1 + 1), (n + 1).choose j * Nat.stirlingSecond j (m + 1) =
          ∑ j ∈ range (n + 1), (n.choose j * ((m + 1) * Nat.stirlingSecond j (m + 1) +
            Nat.stirlingSecond j m) + n.choose (j + 1) * Nat.stirlingSecond (j + 1) (m + 1)) := by
        rw [Finset.sum_range_succ']
        simp only [hz, mul_zero, add_zero]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Nat.choose_succ_succ, Nat.stirlingSecond_succ_succ]
        ring
      rw [Nat.stirlingSecond_succ_succ, ih (m + 1), ih m, e1, Finset.sum_add_distrib, hshift,
        Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring

/-- CO-213. The recurrence of the Bell numbers: `B_{n+1} = sum_{k=0}^{n} C(n,k) B_k`. -/
@[kb "kellertrotter2017" "text, p. 195"]
theorem bellNumber_succ (n : ℕ) :
    bellNumber (n + 1) = ∑ k ∈ range (n + 1), n.choose k * bellNumber k := by
  unfold bellNumber
  rw [Finset.sum_range_succ', Nat.stirlingSecond_succ_zero, add_zero]
  simp only [stirlingSecond_succ_succ_eq_sum n, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  congr 1
  have hjn : j + 1 ≤ n + 1 := by have := Finset.mem_range.1 hj; omega
  symm
  refine Finset.sum_subset (Finset.range_subset_range.2 hjn) ?_
  intro k _ hk
  exact Nat.stirlingSecond_eq_zero_of_lt (by simpa using hk)

end UndergradKB.Combinatorics
