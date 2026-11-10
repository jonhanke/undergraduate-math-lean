import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Ring
import UndergradKB.Common.Attr

/-!
# Keller–Trotter, Chapter 3 (Induction and Recursion): thin course wrappers
-/

namespace UndergradKB.Combinatorics.Course.KellerTrotter

open Finset

/-- CO-057. Well-ordering: every nonempty set of positive integers has a least element. -/
@[kb "kellertrotter2017" "Principle 3.1, p. 64"]
theorem principle_3_1 (S : Set ℕ) (hne : S.Nonempty) (_hpos : ∀ n ∈ S, 0 < n) :
    ∃ m ∈ S, ∀ n ∈ S, m ≤ n := by
  classical
  exact ⟨Nat.find hne, Nat.find_spec hne, fun n hn => Nat.find_min' hne hn⟩

/-- CO-036. Pascal's recursion `C(n,k) = C(n-1,k-1) + C(n-1,k)` for `0 < k < n`. -/
@[kb "kellertrotter2017" "text (Pascal recursion), p. 66"]
theorem text_p66_pascal {n k : ℕ} (hk : 0 < k) (_hkn : k < n) :
    n.choose k = (n - 1).choose (k - 1) + (n - 1).choose k := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simpa using Nat.choose_succ_succ' n' k'

/-- CO-064. The equation `a m + b n = c` has an integer solution `(a,b)` iff `gcd(m,n)` divides
`c`. -/
@[kb "kellertrotter2017" "Theorem 3.9, p. 70"]
theorem thm_3_9 (m n : ℤ) (c : ℕ) :
    (Int.gcd m n : ℤ) ∣ c ↔ ∃ a b : ℤ, (c : ℤ) = m * a + n * b := by
  rw [Int.natCast_dvd_natCast]
  exact Int.gcd_dvd_iff

/-- CO-063. Extended Euclid: `gcd(m,n) = a m + b n` for suitable integers. -/
@[kb "kellertrotter2017" "Example 3.10, p. 70"]
theorem ex_3_10 (m n : ℤ) :
    (Int.gcd m n : ℤ) = m * Int.gcdA m n + n * Int.gcdB m n :=
  Int.gcd_eq_gcd_ab m n

/-- CO-066. Principle of mathematical induction. -/
@[kb "kellertrotter2017" "Principle 3.11, p. 73"]
theorem principle_3_11 (S : ℕ → Prop) (h1 : S 1) (hstep : ∀ k, 1 ≤ k → S k → S (k + 1)) :
    ∀ n, 1 ≤ n → S n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact h1
  | succ k hk ih => exact hstep k hk ih

/-- CO-055. The sum of the first `n` positive integers is `n(n+1)/2`, in multiplied-out form. -/
@[kb "kellertrotter2017" "Proposition 3.12, p. 74"]
theorem prop_3_12 (n : ℕ) : (∑ i ∈ Icc 1 n, i) * 2 = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), add_mul, ih]
    ring

/-- CO-067. Strong induction: if `S 1` holds and `S (k+1)` follows from `S m` for all
`1 ≤ m ≤ k`, then `S n` for all `n ≥ 1`. -/
@[kb "kellertrotter2017" "text (strong induction), p. 78"]
theorem text_p78_strong_induction (S : ℕ → Prop) (h1 : S 1)
    (hstep : ∀ k, 1 ≤ k → (∀ m, 1 ≤ m → m ≤ k → S m) → S (k + 1)) :
    ∀ n, 1 ≤ n → S n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 2 with h | h
    · obtain rfl : n = 1 := by omega
      exact h1
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      exact hstep k (by omega) fun m hm hmk => ih m (by omega) hm


/-- CO-060. The greatest common divisor `gcd(m,n)` is a common divisor, and every common divisor
divides it. -/
@[kb "kellertrotter2017" "Definition (unnumbered) divides/gcd, p. 69"]
theorem def_p69_gcd (m n : ℕ) :
    Nat.gcd m n ∣ m ∧ Nat.gcd m n ∣ n ∧ ∀ d, d ∣ m → d ∣ n → d ∣ Nat.gcd m n :=
  ⟨Nat.gcd_dvd_left m n, Nat.gcd_dvd_right m n, fun _ => Nat.dvd_gcd⟩

end UndergradKB.Combinatorics.Course.KellerTrotter
