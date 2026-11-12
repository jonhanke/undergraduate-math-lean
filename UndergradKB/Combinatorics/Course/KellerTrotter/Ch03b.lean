import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Algebra.BigOperators.Intervals
import UndergradKB.Combinatorics.Counting.Basic
import UndergradKB.Combinatorics.Counting.Misc
import UndergradKB.Combinatorics.Recurrence.Examples
import UndergradKB.Combinatorics.Recurrence.Domino
import UndergradKB.Common.Attr

/-!
# Keller–Trotter, Chapter 3: course wrappers of results proved in this library (wave 3)
-/

namespace UndergradKB.Combinatorics.Course.KellerTrotter.Ch03b

open Finset

/-- CO-215. The number `t n` of domino tilings of a `2 × n` board satisfies
`t (n+2) = t (n+1) + t n`, with `t 1 = 1`, `t 2 = 2`; so `t n` is a Fibonacci number. -/
@[kb "kellertrotter2017" "Example 3.5, p. 68"]
theorem ex_3_5_domino_tilings :
    (∀ n : ℕ, Recurrence.Domino.boardTilingCount (n + 2) =
      Recurrence.Domino.boardTilingCount (n + 1) + Recurrence.Domino.boardTilingCount n) ∧
    (∀ n : ℕ, Recurrence.Domino.boardTilingCount n = Nat.fib (n + 1)) ∧
    Recurrence.tilingCount 1 = 1 ∧ Recurrence.tilingCount 2 = 2 ∧
    (∀ n : ℕ, Recurrence.tilingCount (n + 2) =
      Recurrence.tilingCount (n + 1) + Recurrence.tilingCount n) ∧
    (∀ n : ℕ, Recurrence.tilingCount n = Nat.fib (n + 1)) :=
  ⟨Recurrence.Domino.boardTilingCount_add_two, Recurrence.Domino.boardTilingCount_eq_fib,
   Recurrence.tilingCount_one, Recurrence.tilingCount_two, Recurrence.tilingCount_succ_succ,
   Recurrence.tilingCount_eq_fib⟩

/-- CO-216. Ternary strings of length `n` with no `2` immediately followed by `0` number `g n`,
with `g 1 = 3`, `g 2 = 8` and `g (n+2) = 3 g (n+1) - g n`. -/
@[kb "kellertrotter2017" "Example 3.6, p. 68"]
theorem ex_3_6_ternary_strings :
    (Recurrence.ternGood 1).card = 3 ∧ (Recurrence.ternGood 2).card = 8 ∧
    (∀ n : ℕ, (Recurrence.ternGood (n + 2)).card + (Recurrence.ternGood n).card =
      3 * (Recurrence.ternGood (n + 1)).card) ∧
    (∀ n : ℕ, ((Recurrence.ternGood (n + 2)).card : ℤ) =
      3 * (Recurrence.ternGood (n + 1)).card - (Recurrence.ternGood n).card) :=
  ⟨Recurrence.ternGood_card_one, Recurrence.ternGood_card_two,
   Recurrence.ternGood_card_succ_succ, Recurrence.ternGood_card_recurrence⟩

/-- CO-059. Division algorithm: for positive `m`, `n` there are unique `q`, `r` with
`m = q n + r` and `0 ≤ r < n`. -/
@[kb "kellertrotter2017" "Theorem 3.7, p. 69"]
theorem thm_3_7_division_algorithm {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    ∃! p : ℕ × ℕ, m = p.1 * n + p.2 ∧ p.2 < n :=
  division_algorithm hm hn

/-- CO-061. If `m = q n + r` with `0 < r < n` then `gcd(m,n) = gcd(n,r)`; if `r = 0` then
`gcd(m,n) = n`. -/
@[kb "kellertrotter2017" "Theorem 3.8, p. 69"]
theorem thm_3_8_gcd_step :
    (∀ {m n q r : ℕ}, m = q * n + r → 0 < r → r < n → Nat.gcd m n = Nat.gcd n r) ∧
    (∀ {m n q : ℕ}, m = q * n + 0 → Nat.gcd m n = n) :=
  ⟨fun h hr hrn => gcd_eq_gcd_of_div h hr hrn, fun h => gcd_eq_of_remainder_zero h⟩

/-- CO-062. Euclid's algorithm (recursively replace `(m,n)` by `(n, m mod n)`) computes the
greatest common divisor. -/
@[kb "kellertrotter2017" "text, p. 70"]
theorem text_3_euclid_algorithm (m n : ℕ) : euclidGcd m n = Nat.gcd m n :=
  euclidGcd_eq_gcd m n

/-- CO-070. Merge sort: from `S(2n) ≤ 2 S(n) + 2n` the running time satisfies
`S(2^k) ≤ 2^k (S(1) + k)`, hence is `O(n log n)`. -/
@[kb "kellertrotter2017" "text, p. 72"]
theorem text_3_merge_sort_bound (S : ℕ → ℕ) (h : ∀ n, 1 ≤ n → S (2 * n) ≤ 2 * S n + 2 * n)
    (k : ℕ) :
    S (2 ^ k) ≤ 2 ^ k * (S 1 + k) ∧ (1 ≤ k → S (2 ^ k) ≤ (S 1 + 1) * (2 ^ k * k)) :=
  ⟨mergeSort_bound S h k, fun hk => mergeSort_bound_nlogn S h k hk⟩

/-- CO-056. The sum of the first `n` odd positive integers is `n^2`. -/
@[kb "kellertrotter2017" "Proposition 3.13, p. 76"]
theorem prop_3_13_sum_first_odd (n : ℕ) : ∑ i ∈ range n, (2 * i + 1) = n ^ 2 :=
  sum_first_odd n

end UndergradKB.Combinatorics.Course.KellerTrotter.Ch03b
