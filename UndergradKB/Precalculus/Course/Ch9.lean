import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Powerset
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Real.Basic
import UndergradKB.Common.Attr

/-!
# Course layer, Chapter 9 (sequences, summation, induction, the binomial theorem)

Thin theorems in the book's terms, each proved from the Mathlib declarations named in the
corresponding checklist row.
-/

namespace UndergradKB.Precalculus.Course

open Finset

/-- Summation notation over a closed index range: the sum from `m` to `p` is the sum of the
terms `a m, ..., a p`; peeling off the last term and the one-term sum (PC-169). -/
@[kb "stitzzeager2013" "Definition 9.3, p. 673"]
theorem def_9_3_summation (a : ℕ → ℝ) (m p : ℕ) (h : m ≤ p) :
    (∑ k ∈ Icc m (p + 1), a k = ∑ k ∈ Icc m p, a k + a (p + 1)) ∧ (∑ k ∈ Icc m m, a k = a m) :=
  ⟨Finset.sum_Icc_succ_top (Nat.le_succ_of_le h) a, by simp⟩

/-- Summation is additive: the sum of sums is the sum of the termwise sums (PC-170). -/
@[kb "stitzzeager2013" "Theorem 9.1, p. 676"]
theorem thm_9_1_sum_add (a b : ℕ → ℝ) (m p : ℕ) :
    ∑ k ∈ Icc m p, (a k + b k) = ∑ k ∈ Icc m p, a k + ∑ k ∈ Icc m p, b k :=
  Finset.sum_add_distrib

/-- Summation respects differences (PC-170). -/
@[kb "stitzzeager2013" "Theorem 9.1, p. 676"]
theorem thm_9_1_sum_sub (a b : ℕ → ℝ) (m p : ℕ) :
    ∑ k ∈ Icc m p, (a k - b k) = ∑ k ∈ Icc m p, a k - ∑ k ∈ Icc m p, b k :=
  Finset.sum_sub_distrib a b

/-- A constant factor comes out of a sum (PC-170). -/
@[kb "stitzzeager2013" "Theorem 9.1, p. 676"]
theorem thm_9_1_sum_const_mul (c : ℝ) (a : ℕ → ℝ) (m p : ℕ) :
    ∑ k ∈ Icc m p, c * a k = c * ∑ k ∈ Icc m p, a k :=
  (Finset.mul_sum _ _ _).symm

/-- A sum splits at an interior index: `∑_{k=m}^{p} = ∑_{k=m}^{q} + ∑_{k=q+1}^{p}` (PC-170). -/
@[kb "stitzzeager2013" "Theorem 9.1, p. 676"]
theorem thm_9_1_sum_split (a : ℕ → ℝ) {m q p : ℕ} (hmq : m ≤ q + 1) (hqp : q ≤ p) :
    ∑ k ∈ Icc m p, a k = ∑ k ∈ Icc m q, a k + ∑ k ∈ Icc (q + 1) p, a k := by
  rw [← Finset.Ico_add_one_right_eq_Icc, ← Finset.Ico_add_one_right_eq_Icc,
    ← Finset.Ico_add_one_right_eq_Icc]
  exact (Finset.sum_Ico_consecutive a hmq (Nat.succ_le_succ hqp)).symm

/-- The index of summation can be shifted: `∑_{k=m}^{p} a(k+c) = ∑_{k=m+c}^{p+c} a(k)`
(PC-170). -/
@[kb "stitzzeager2013" "Theorem 9.1, p. 676"]
theorem thm_9_1_sum_shift (a : ℕ → ℝ) (m p c : ℕ) :
    ∑ k ∈ Icc m p, a (k + c) = ∑ k ∈ Icc (m + c) (p + c), a k := by
  rw [← Finset.Ico_add_one_right_eq_Icc, ← Finset.Ico_add_one_right_eq_Icc]
  have := Finset.sum_Ico_add' a m (p + 1) c
  rw [show p + c + 1 = p + 1 + c by omega]
  exact this

/-- `1 + 2 + ... + n = n(n+1)/2` (PC-172). -/
@[kb "stitzzeager2013" "Equation 9.2, p. 678"]
theorem eq_9_2_sum_first_n (n : ℕ) : ∑ k ∈ Icc 1 n, (k : ℝ) = n * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

/-- Sum of the first `n` terms of a geometric sequence `a, ar, ar², ...` with `r ≠ 1`
(PC-173). -/
@[kb "stitzzeager2013" "Equation 9.2, p. 678"]
theorem eq_9_2_geometric_sum (a r : ℝ) (hr : r ≠ 1) (n : ℕ) :
    ∑ k ∈ Icc 1 n, a * r ^ (k - 1) = a * ((1 - r ^ n) / (1 - r)) := by
  have h1 : (1 - r) ≠ 0 := sub_ne_zero.mpr (Ne.symm hr)
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    simp only [Nat.add_sub_cancel]
    field_simp
    ring

/-- For ratio `r = 1` the geometric sum of `n` terms is `n a` (PC-173). -/
@[kb "stitzzeager2013" "Equation 9.2, p. 678"]
theorem eq_9_2_geometric_sum_ratio_one (a : ℝ) (n : ℕ) :
    ∑ k ∈ Icc 1 n, a * (1 : ℝ) ^ (k - 1) = n * a := by
  simp [mul_comm]

/-- An infinite geometric series with `|r| < 1` sums to `a / (1 - r)` (PC-175). -/
@[kb "stitzzeager2013" "Theorem 9.2, p. 681"]
theorem thm_9_2_geometric_series_converges (a r : ℝ) (hr : |r| < 1) :
    HasSum (fun k : ℕ => a * r ^ k) (a / (1 - r)) := by
  have := (hasSum_geometric_of_abs_lt_one hr).mul_left a
  simpa [div_eq_mul_inv] using this

/-- An infinite geometric series with first term `a ≠ 0` and `|r| ≥ 1` does not converge
(PC-175). -/
@[kb "stitzzeager2013" "Theorem 9.2, p. 681"]
theorem thm_9_2_geometric_series_diverges (a r : ℝ) (ha : a ≠ 0) (hr : 1 ≤ |r|) :
    ¬ Summable (fun k : ℕ => a * r ^ k) := by
  intro h
  have h2 : Summable (fun k : ℕ => r ^ k) := (summable_mul_left_iff ha).mp h
  have := summable_geometric_iff_norm_lt_one.mp h2
  rw [Real.norm_eq_abs] at this
  linarith

/-- Principle of mathematical induction: if `P 1` holds and `P k` implies `P (k+1)` for each
`k ≥ 1`, then `P n` holds for every `n ≥ 1` (PC-176). -/
@[kb "stitzzeager2013" "§9.3, p. 685"]
theorem box_9_3_induction (P : ℕ → Prop) (h1 : P 1) (hstep : ∀ k, 1 ≤ k → P k → P (k + 1)) :
    ∀ n, 1 ≤ n → P n := fun _ hn =>
  Nat.le_induction h1 hstep _ hn

/-- The conjugate of `z ^ n` is `(conj z) ^ n` (PC-177). -/
@[kb "stitzzeager2013" "Example 9.3.1, p. 686"]
theorem ex_9_3_1_conj_pow (z : ℂ) (n : ℕ) :
    (starRingEnd ℂ) (z ^ n) = ((starRingEnd ℂ) z) ^ n :=
  map_pow _ z n

/-- Replacing a row of a square matrix by `c` times that row multiplies the determinant by `c`
(PC-178). -/
@[kb "stitzzeager2013" "Example 9.3.1, p. 686"]
theorem ex_9_3_1_det_scaled_row {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (c : ℝ) :
    (A.updateRow i (c • A i)).det = c * A.det := by
  rw [Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]

/-- Factorial: `0! = 1` and `(n+1)! = (n+1) * n!` (PC-179). -/
@[kb "stitzzeager2013" "Definition 9.4, p. 693"]
theorem def_9_4_factorial (n : ℕ) :
    Nat.factorial 0 = 1 ∧ Nat.factorial (n + 1) = (n + 1) * Nat.factorial n :=
  ⟨Nat.factorial_zero, Nat.factorial_succ n⟩

/-- For each real `x`, `xⁿ / n!` tends to `0` as `n` grows (PC-181). -/
@[kb "stitzzeager2013" "§9.4, p. 694"]
theorem box_9_4_pow_div_factorial_tendsto (x : ℝ) :
    Filter.Tendsto (fun n : ℕ => x ^ n / (n.factorial : ℝ)) Filter.atTop (nhds 0) :=
  FloorSemiring.tendsto_pow_div_factorial_atTop x

/-- Binomial coefficient: `C(n, j) = n! / (j! (n-j)!)` for `j ≤ n` (PC-182). -/
@[kb "stitzzeager2013" "Definition 9.5, p. 695"]
theorem def_9_5_choose_factorial (n j : ℕ) (h : j ≤ n) :
    (n.choose j : ℝ) = n.factorial / (j.factorial * (n - j).factorial) :=
  Nat.cast_choose ℝ h

/-- `C(n, j)` is the number of `j`-element subsets of an `n`-element set (PC-183). -/
@[kb "stitzzeager2013" "§9.4, p. 695"]
theorem box_9_4_choose_counts_subsets {α : Type*} (s : Finset α) (j : ℕ) :
    (s.powersetCard j).card = s.card.choose j :=
  Finset.card_powersetCard j s

/-- Pascal's rule: `C(n, j-1) + C(n, j) = C(n+1, j)` for `j ≥ 1` (PC-184). -/
@[kb "stitzzeager2013" "Theorem 9.3, p. 695"]
theorem thm_9_3_pascal (n j : ℕ) (hj : 1 ≤ j) :
    n.choose (j - 1) + n.choose j = (n + 1).choose j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  simpa using (Nat.choose_succ_succ n k).symm

/-- The Binomial Theorem: `(a + b)ⁿ = ∑ C(n, j) aⁿ⁻ʲ bʲ` (PC-185). -/
@[kb "stitzzeager2013" "Theorem 9.4, p. 696"]
theorem thm_9_4_binomial (a b : ℝ) (n : ℕ) :
    (a + b) ^ n = ∑ j ∈ range (n + 1), (n.choose j : ℝ) * a ^ (n - j) * b ^ j := by
  rw [add_comm, add_pow]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end UndergradKB.Precalculus.Course
