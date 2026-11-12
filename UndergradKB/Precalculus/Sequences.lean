import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-!
# Sequences (Stitz-Zeager Precalculus, Chapter 9)

Sequences are `ℕ → ℝ` indexed from `1` as in the book: the value at index `0` is never constrained.
-/

namespace UndergradKB.Precalculus

/-- A sequence (indexed from 1) is arithmetic with common difference `d` when each term after the
first is the previous term plus `d` (PC-167). -/
def IsArithmeticSeq (a : ℕ → ℝ) (d : ℝ) : Prop := ∀ n : ℕ, 1 ≤ n → a (n + 1) = a n + d

/-- A sequence (indexed from 1) is geometric with common ratio `r` when each term after the
first is `r` times the previous term (PC-167). -/
def IsGeometricSeq (a : ℕ → ℝ) (r : ℝ) : Prop := ∀ n : ℕ, 1 ≤ n → a (n + 1) = r * a n

/-- The arithmetic and geometric predicates unfold to the stated recurrences (PC-167). -/
@[kb "stitzzeager2013" "Definition 9.2, p. 666"]
theorem seq_arith_geom_recurrence (a : ℕ → ℝ) (c : ℝ) :
    (IsArithmeticSeq a c ↔ ∀ n : ℕ, 1 ≤ n → a (n + 1) - a n = c) ∧
    (IsGeometricSeq a c ↔ ∀ n : ℕ, 1 ≤ n → a (n + 1) = c * a n) := by
  refine ⟨?_, Iff.rfl⟩
  unfold IsArithmeticSeq
  constructor
  · intro h n hn; rw [h n hn]; ring
  · intro h n hn; rw [← h n hn]; ring

/-- Closed form of an arithmetic sequence: `a n = a 1 + (n-1) d` (PC-168). -/
@[kb "stitzzeager2013" "Equation 9.1, p. 668"]
theorem seq_arith_nth_term {a : ℕ → ℝ} {d : ℝ} (h : IsArithmeticSeq a d) (n : ℕ) (hn : 1 ≤ n) :
    a n = a 1 + ((n : ℝ) - 1) * d := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih => rw [h n hn, ih]; push_cast; ring

/-- Closed form of a geometric sequence: `a n = a 1 * r^(n-1)` (PC-168). -/
@[kb "stitzzeager2013" "Equation 9.1, p. 668"]
theorem seq_geom_nth_term {a : ℕ → ℝ} {r : ℝ} (h : IsGeometricSeq a r) (n : ℕ) (hn : 1 ≤ n) :
    a n = a 1 * r ^ (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [h n hn, ih]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp [pow_succ]; ring

/-- Sum of the first `n` terms of an arithmetic sequence, second form:
`n/2 * (2 a₁ + (n-1) d)` (PC-171). -/
@[kb "stitzzeager2013" "Equation 9.2, p. 678"]
theorem seq_arith_sum_formula {a : ℕ → ℝ} {d : ℝ} (h : IsArithmeticSeq a d) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, a k = (n : ℝ) / 2 * (2 * a 1 + ((n : ℝ) - 1) * d) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, seq_arith_nth_term h (n + 1) (by omega)]
    push_cast; ring

/-- Sum of the first `n` terms of an arithmetic sequence, first form:
`n (a₁ + aₙ) / 2` (PC-171). -/
@[kb "stitzzeager2013" "Equation 9.2, p. 678"]
theorem seq_arith_sum_first_last {a : ℕ → ℝ} {d : ℝ} (h : IsArithmeticSeq a d) (n : ℕ)
    (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 1 n, a k = (n : ℝ) * (a 1 + a n) / 2 := by
  rw [seq_arith_sum_formula h, seq_arith_nth_term h n hn]; ring

/-- Annuity: with balance recursion `B (k+1) = B k * (1 + i) + P` and `B 0 = 0`, the balance after
`k` payments is `P ((1+i)^k - 1) / i` for `i ≠ 0` (PC-174). -/
@[kb "stitzzeager2013" "Equation 9.3, p. 679"]
theorem seq_annuity_balance (B : ℕ → ℝ) (P i : ℝ) (hi : i ≠ 0) (h0 : B 0 = 0)
    (hB : ∀ k, B (k + 1) = B k * (1 + i) + P) (k : ℕ) :
    B k = P * ((1 + i) ^ k - 1) / i := by
  induction k with
  | zero => simp [h0]
  | succ k ih => rw [hB, ih, pow_succ]; field_simp; ring

/-- For every `n ≥ 7`, `3^n < n!` (PC-180). -/
@[kb "stitzzeager2013" "Example 9.4.1, p. 693"]
theorem seq_three_pow_lt_factorial (n : ℕ) (hn : 7 ≤ n) : 3 ^ n < n.factorial := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    rw [Nat.factorial_succ, pow_succ]
    nlinarith

end UndergradKB.Precalculus
