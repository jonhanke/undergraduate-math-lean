import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Factorial.Basic
import UndergradKB.Common.Attr

/-!
# Keller–Trotter, Chapter 3 and Appendix B: thin course wrappers (wave 2)

Each theorem restates a book item in the book's terms and is proved by a Mathlib declaration.
-/

namespace UndergradKB.Combinatorics.Course.KellerTrotter

open Finset

/-- CO-058. Recursive definition of a finite sum: `∑_{i=1}^1 f(i) = f(1)` and
`∑_{i=1}^{n+1} f(i) = f(n+1) + ∑_{i=1}^{n} f(i)`. -/
@[kb "kellertrotter2017" "text (recursive sum), p. 65"]
theorem recursive_sum (f : ℕ → ℤ) :
    (∑ i ∈ Icc 1 1, f i = f 1) ∧
      ∀ n : ℕ, 1 ≤ n → ∑ i ∈ Icc 1 (n + 1), f i = f (n + 1) + ∑ i ∈ Icc 1 n, f i := by
  refine ⟨by simp, fun n hn => ?_⟩
  rw [Finset.sum_Icc_succ_top (by omega), add_comm]

/-- CO-058. Recursive definition of the factorial: `0! = 1` and `(n+1)! = (n+1) · n!`. -/
@[kb "kellertrotter2017" "text (recursive factorial), p. 66"]
theorem recursive_factorial :
    Nat.factorial 0 = 1 ∧ ∀ n : ℕ, Nat.factorial (n + 1) = (n + 1) * Nat.factorial n :=
  ⟨Nat.factorial_zero, fun n => Nat.factorial_succ n⟩

/-- CO-058. Inductive definition of the factorial and of finite sums (`1! = 1`,
`(k+1)! = (k+1) k!`; `∑_{i=1}^{k+1} f(i) = ∑_{i=1}^{k} f(i) + f(k+1)`). -/
@[kb "kellertrotter2017" "text (inductive definitions), p. 73"]
theorem inductive_definitions (f : ℕ → ℤ) :
    Nat.factorial 1 = 1 ∧ (∀ k : ℕ, Nat.factorial (k + 1) = (k + 1) * Nat.factorial k) ∧
      ∀ k : ℕ, 1 ≤ k → ∑ i ∈ Icc 1 (k + 1), f i = ∑ i ∈ Icc 1 k, f i + f (k + 1) := by
  refine ⟨rfl, fun k => Nat.factorial_succ k, fun k hk => ?_⟩
  rw [Finset.sum_Icc_succ_top (by omega)]

/-- CO-065. Merge sort: sorting a list of integers by splitting, sorting recursively and merging
returns a list that is in increasing order and is a rearrangement of the input. -/
@[kb "kellertrotter2017" "text (merge and merge sort), p. 71"]
theorem merge_sort_correct (l : List ℤ) :
    (List.mergeSort l (fun a b => decide (a ≤ b))).Pairwise (· ≤ ·) ∧
      (List.mergeSort l (fun a b => decide (a ≤ b))).Perm l :=
  ⟨List.pairwise_mergeSort' (· ≤ ·) l, List.mergeSort_perm l _⟩

/-- CO-338. The Peano postulates for the natural numbers `ℕ` with the successor function:
the successor is one-to-one, `0` is not a successor, and induction: a set containing `0` and
closed under the successor is all of `ℕ`. -/
@[kb "kellertrotter2017" "Peano Postulates, p. 365"]
theorem peano_postulates :
    Function.Injective Nat.succ ∧ (∀ n : ℕ, 0 ≠ Nat.succ n) ∧
      ∀ S : Set ℕ, 0 ∈ S → (∀ k, k ∈ S → Nat.succ k ∈ S) → S = Set.univ := by
  refine ⟨Nat.succ_injective, fun n => (Nat.succ_ne_zero n).symm, fun S h0 hs => ?_⟩
  refine Set.eq_univ_of_forall fun n => ?_
  induction n with
  | zero => exact h0
  | succ k ih => exact hs k ih

end UndergradKB.Combinatorics.Course.KellerTrotter
