import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import UndergradKB.Common

/-!
# Course layer: Levin, Discrete Mathematics, Chapter 4, worked examples (second batch)
-/

namespace UndergradKB.Foundations.Course

open scoped fwdDiff

/-- Levin Example 4.1.12: the recurrence `a n = 3 a (n-1) + 2` with `a 0 = 1` produces the terms
`1, 5, 17, 53, 161, 485`. -/
@[kb "levin2025" "Example 4.1.12, p. 342"]
theorem levin_ex_4_1_12_recurrence_terms (a : ℕ → ℕ) (h0 : a 0 = 1)
    (h : ∀ n, a (n + 1) = 3 * a n + 2) :
    a 0 = 1 ∧ a 1 = 5 ∧ a 2 = 17 ∧ a 3 = 53 ∧ a 4 = 161 ∧ a 5 = 485 := by
  have h1 : a 1 = 5 := by rw [h 0, h0]
  have h2 : a 2 = 17 := by rw [h 1, h1]
  have h3 : a 3 = 53 := by rw [h 2, h2]
  have h4 : a 4 = 161 := by rw [h 3, h3]
  have h5 : a 5 = 485 := by rw [h 4, h4]
  exact ⟨h0, h1, h2, h3, h4, h5⟩

/-- Levin Example 4.3.3: `6 + 10 + ... + (4n - 2) = (n - 1)(4n + 4) / 2` for `n ≥ 1`
(stated as twice the sum). -/
@[kb "levin2025" "Example 4.3.3, p. 361"]
theorem levin_ex_4_3_3_arithmetic_sum (n : ℕ) (hn : 1 ≤ n) :
    2 * ∑ k ∈ Finset.Icc 2 n, ((4 : ℤ) * k - 2) = ((n : ℤ) - 1) * (4 * n + 4) := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    push_cast
    linear_combination ih

/-- Levin Example 4.3.9: the formula `a n = (3/2) n^2 - (1/2) n + 2` starts `2, 3, 7, 14, 24, 37`
and satisfies `a n = a (n-1) + 3 n - 2`. -/
@[kb "levin2025" "Example 4.3.9, p. 365"]
theorem levin_ex_4_3_9_fitted_formula :
    let a : ℕ → ℚ := fun n => 3 / 2 * (n : ℚ) ^ 2 - 1 / 2 * n + 2
    a 0 = 2 ∧ a 1 = 3 ∧ a 2 = 7 ∧ a 3 = 14 ∧ a 4 = 24 ∧ a 5 = 37 ∧
      ∀ n : ℕ, a (n + 1) = a n + 3 * (n + 1) - 2 := by
  intro a
  refine ⟨by norm_num [a], by norm_num [a], by norm_num [a], by norm_num [a], by norm_num [a],
    by norm_num [a], fun n => ?_⟩
  simp only [a]
  push_cast
  ring

/-- Levin Example 4.3.10 (second sequence): `0, 7, 50, 183, 484, 1055` is given by the degree 4
polynomial `n^4 + 3 n^3 + 2 n^2 + n`, whose fourth differences are constantly 24. -/
@[kb "levin2025" "Example 4.3.10, p. 366"]
theorem levin_ex_4_3_10_degree_four :
    let p : ℤ → ℤ := fun n => n ^ 4 + 3 * n ^ 3 + 2 * n ^ 2 + n
    p 0 = 0 ∧ p 1 = 7 ∧ p 2 = 50 ∧ p 3 = 183 ∧ p 4 = 484 ∧ p 5 = 1055 ∧
      ∀ y : ℤ, (Δ_[(1 : ℤ)])^[4] p y = 24 := by
  intro p
  refine ⟨by norm_num [p], by norm_num [p], by norm_num [p], by norm_num [p], by norm_num [p],
    by norm_num [p], fun y => ?_⟩
  rw [fwdDiff_iter_eq_sum_shift]
  simp [Finset.sum_range_succ, p, Nat.choose]
  ring

end UndergradKB.Foundations.Course
