import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import UndergradKB.Common.Attr

/-!
# Course layer, Chapter 9 (Stitz-Zeager): worked examples

Terms of sequences, arithmetic and geometric classification, finite sums and binomial
expansions: the facts established by the worked examples of Chapter 9.
-/

namespace UndergradKB.Precalculus.Course

open Finset

/-- Stitz-Zeager Example 9.1.1(1): the first four terms of `a n = 5^(n-1)/3^n` are
`1/3, 5/9, 25/27, 125/81`. -/
@[kb "stitzzeager2013" "Example 9.1.1, p. 664"]
theorem ex_9_1_1_1 :
    (fun n : ℕ => (5 : ℝ) ^ (n - 1) / 3 ^ n) 1 = 1 / 3 ∧
    (fun n : ℕ => (5 : ℝ) ^ (n - 1) / 3 ^ n) 2 = 5 / 9 ∧
    (fun n : ℕ => (5 : ℝ) ^ (n - 1) / 3 ^ n) 3 = 25 / 27 ∧
    (fun n : ℕ => (5 : ℝ) ^ (n - 1) / 3 ^ n) 4 = 125 / 81 := by
  norm_num

/-- Stitz-Zeager Example 9.1.1(2): the first four terms of `b k = (-1)^k/(2k+1)`, `k ≥ 0`, are
`1, -1/3, 1/5, -1/7`. -/
@[kb "stitzzeager2013" "Example 9.1.1, p. 664"]
theorem ex_9_1_1_2 :
    (fun k : ℕ => (-1 : ℝ) ^ k / (2 * k + 1)) 0 = 1 ∧
    (fun k : ℕ => (-1 : ℝ) ^ k / (2 * k + 1)) 1 = -1 / 3 ∧
    (fun k : ℕ => (-1 : ℝ) ^ k / (2 * k + 1)) 2 = 1 / 5 ∧
    (fun k : ℕ => (-1 : ℝ) ^ k / (2 * k + 1)) 3 = -1 / 7 := by
  norm_num

/-- Stitz-Zeager Example 9.1.1(3): the first four terms of `2n - 1`, `n ≥ 1`, are `1, 3, 5, 7`. -/
@[kb "stitzzeager2013" "Example 9.1.1, p. 664"]
theorem ex_9_1_1_3 :
    (fun n : ℕ => (2 * n - 1 : ℤ)) 1 = 1 ∧ (fun n : ℕ => (2 * n - 1 : ℤ)) 2 = 3 ∧
    (fun n : ℕ => (2 * n - 1 : ℤ)) 3 = 5 ∧ (fun n : ℕ => (2 * n - 1 : ℤ)) 4 = 7 := by
  norm_num

/-- Stitz-Zeager Example 9.1.1(4): the first four terms of `(1 + (-1)^i)/i`, `i ≥ 2`, are
`1, 0, 1/2, 0`. -/
@[kb "stitzzeager2013" "Example 9.1.1, p. 664"]
theorem ex_9_1_1_4 :
    (fun i : ℕ => (1 + (-1 : ℝ) ^ i) / i) 2 = 1 ∧ (fun i : ℕ => (1 + (-1 : ℝ) ^ i) / i) 3 = 0 ∧
    (fun i : ℕ => (1 + (-1 : ℝ) ^ i) / i) 4 = 1 / 2 ∧
    (fun i : ℕ => (1 + (-1 : ℝ) ^ i) / i) 5 = 0 := by
  norm_num

/-- Stitz-Zeager Example 9.1.1(5): the recursion `a 1 = 7`, `a (n+1) = 2 - a n` gives
`7, -5, 7, -5`. -/
@[kb "stitzzeager2013" "Example 9.1.1, p. 664"]
theorem ex_9_1_1_5 (a : ℕ → ℝ) (h1 : a 1 = 7) (h : ∀ n ≥ 1, a (n + 1) = 2 - a n) :
    a 1 = 7 ∧ a 2 = -5 ∧ a 3 = 7 ∧ a 4 = -5 := by
  have h2 : a 2 = -5 := by rw [h 1 le_rfl, h1]; norm_num
  have h3 : a 3 = 7 := by rw [h 2 (by norm_num), h2]; norm_num
  have h4 : a 4 = -5 := by rw [h 3 (by norm_num), h3]; norm_num
  exact ⟨h1, h2, h3, h4⟩

/-- Stitz-Zeager Example 9.1.1(6): the recursion `f 0 = 1`, `f n = n * f (n-1)` gives
`1, 1, 2, 6` for the first four terms. -/
@[kb "stitzzeager2013" "Example 9.1.1, p. 664"]
theorem ex_9_1_1_6 (f : ℕ → ℕ) (h0 : f 0 = 1) (h : ∀ n ≥ 1, f n = n * f (n - 1)) :
    f 0 = 1 ∧ f 1 = 1 ∧ f 2 = 2 ∧ f 3 = 6 := by
  have h1 : f 1 = 1 := by rw [h 1 le_rfl]; simp [h0]
  have h2 : f 2 = 2 := by rw [h 2 (by norm_num)]; simp [h1]
  have h3 : f 3 = 6 := by rw [h 3 (by norm_num)]; simp [h2]
  exact ⟨h0, h1, h2, h3⟩

/-- Stitz-Zeager Example 9.1.2(1): `a n = 5^(n-1)/3^n` (`n ≥ 1`) is geometric with ratio `5/3`
and is not arithmetic. -/
@[kb "stitzzeager2013" "Example 9.1.2, p. 666"]
theorem ex_9_1_2_1 :
    (∀ n : ℕ, 1 ≤ n →
      (5 : ℝ) ^ (n + 1 - 1) / 3 ^ (n + 1) = 5 / 3 * ((5 : ℝ) ^ (n - 1) / 3 ^ n)) ∧
    ¬ ∃ d : ℝ, ∀ n : ℕ, 1 ≤ n →
      (5 : ℝ) ^ (n + 1 - 1) / 3 ^ (n + 1) = (5 : ℝ) ^ (n - 1) / 3 ^ n + d := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [pow_succ, pow_succ]
    field_simp
  · rintro ⟨d, hd⟩
    have h1 := hd 1 le_rfl
    have h2 := hd 2 (by norm_num)
    norm_num at h1 h2
    linarith

/-- Stitz-Zeager Example 9.1.2(2): `b k = (-1)^k/(2k+1)`, `k ≥ 0`, is neither arithmetic nor
geometric. -/
@[kb "stitzzeager2013" "Example 9.1.2, p. 666"]
theorem ex_9_1_2_2 :
    (¬ ∃ d : ℝ, ∀ k : ℕ, (-1 : ℝ) ^ (k + 1) / (2 * (k + 1 : ℕ) + 1) = (-1 : ℝ) ^ k / (2 * k + 1) + d) ∧
    ¬ ∃ r : ℝ, ∀ k : ℕ, (-1 : ℝ) ^ (k + 1) / (2 * (k + 1 : ℕ) + 1) = r * ((-1 : ℝ) ^ k / (2 * k + 1)) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨d, hd⟩
    have h0 := hd 0
    have h1 := hd 1
    norm_num at h0 h1
    linarith
  · rintro ⟨r, hr⟩
    have h0 := hr 0
    have h1 := hr 1
    norm_num at h0 h1
    linarith

/-- Stitz-Zeager Example 9.1.2(3): `2n - 1` is arithmetic with common difference `2`, and not
geometric. -/
@[kb "stitzzeager2013" "Example 9.1.2, p. 666"]
theorem ex_9_1_2_3 :
    (∀ n : ℕ, (2 * ((n : ℝ) + 1) - 1) - (2 * (n : ℝ) - 1) = 2) ∧
    ¬ ∃ r : ℝ, ∀ n : ℕ, 1 ≤ n → (2 * ((n : ℝ) + 1) - 1) = r * (2 * (n : ℝ) - 1) := by
  refine ⟨fun n => by ring, ?_⟩
  rintro ⟨r, hr⟩
  have h1 := hr 1 le_rfl
  have h2 := hr 2 (by norm_num)
  norm_num at h1 h2
  nlinarith

/-- Stitz-Zeager Example 9.1.2(4): the sequence `1/2, -3/4, 9/8, -27/16, ...`, with general term
`(1/2) (-3/2)^(n-1)`, is geometric with ratio `-3/2`. -/
@[kb "stitzzeager2013" "Example 9.1.2, p. 666"]
theorem ex_9_1_2_4 :
    ((1 / 2 : ℝ) * (-3 / 2) ^ 0 = 1 / 2 ∧ (1 / 2 : ℝ) * (-3 / 2) ^ 1 = -3 / 4 ∧
      (1 / 2 : ℝ) * (-3 / 2) ^ 2 = 9 / 8 ∧ (1 / 2 : ℝ) * (-3 / 2) ^ 3 = -27 / 16) ∧
    ∀ n : ℕ, (1 / 2 : ℝ) * (-3 / 2) ^ (n + 1) = (-3 / 2) * ((1 / 2 : ℝ) * (-3 / 2) ^ n) := by
  refine ⟨by norm_num, fun n => by ring⟩

/-- Stitz-Zeager Example 9.2.1(1a): `∑_{k=1}^{4} 13/100^k = 0.13131313`. -/
@[kb "stitzzeager2013" "Example 9.2.1, p. 674"]
theorem ex_9_2_1_1_a : ∑ k ∈ Icc 1 4, (13 : ℚ) / 100 ^ k = 13131313 / 100000000 := by
  decide +kernel

/-- Stitz-Zeager Example 9.2.1(1b): `∑_{n=0}^{4} n!/2 = 17`. -/
@[kb "stitzzeager2013" "Example 9.2.1, p. 674"]
theorem ex_9_2_1_1_b : ∑ n ∈ range 5, (n.factorial : ℚ) / 2 = 17 := by
  simp [Finset.sum_range_succ, Nat.factorial]
  norm_num

/-- Stitz-Zeager Example 9.2.1(1c): `∑_{n=1}^{5} (-1)^(n+1) (x-1)^n / n` expands to
`(x-1) - (x-1)^2/2 + (x-1)^3/3 - (x-1)^4/4 + (x-1)^5/5`. -/
@[kb "stitzzeager2013" "Example 9.2.1, p. 674"]
theorem ex_9_2_1_1_c (x : ℝ) :
    ∑ n ∈ Icc (1 : ℕ) 5, (-1 : ℝ) ^ (n + 1) / (n : ℝ) * (x - 1) ^ n =
      (x - 1) - (x - 1) ^ 2 / 2 + (x - 1) ^ 3 / 3 - (x - 1) ^ 4 / 4 + (x - 1) ^ 5 / 5 := by
  simp [Finset.sum_Icc_succ_top]
  norm_num
  ring

/-- Stitz-Zeager Example 9.2.1(2a): the sum `1 + 3 + ... + 117` is `∑_{n=1}^{59} (2n-1)`: its
last term is `117`, and it equals the sum of the odd numbers below `118`. -/
@[kb "stitzzeager2013" "Example 9.2.1, p. 674"]
theorem ex_9_2_1_2_a :
    2 * 59 - 1 = 117 ∧
      ∑ n ∈ Icc 1 59, (2 * n - 1) = ∑ m ∈ (range 118).filter (fun m => m % 2 = 1), m := by
  refine ⟨by norm_num, ?_⟩
  decide +kernel

/-- Stitz-Zeager Example 9.2.1(2c): the sum `0.9 + 0.09 + ...` with `n` terms is
`∑_{k=1}^{n} 9/10^k = 1 - 1/10^n`. -/
@[kb "stitzzeager2013" "Example 9.2.1, p. 674"]
theorem ex_9_2_1_2_c (n : ℕ) : ∑ k ∈ Icc 1 n, (9 : ℚ) / 10 ^ k = 1 - 1 / 10 ^ n := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    field_simp
    ring

/-- Stitz-Zeager Example 9.4.2(1): `(x-2)^4 = x^4 - 8x^3 + 24x^2 - 32x + 16`, as the binomial
sum. -/
@[kb "stitzzeager2013" "Example 9.4.2, p. 699"]
theorem ex_9_4_2_1 (x : ℝ) :
    (x - 2) ^ 4 = ∑ j ∈ range 5, (Nat.choose 4 j : ℝ) * x ^ (4 - j) * (-2) ^ j ∧
    (x - 2) ^ 4 = x ^ 4 - 8 * x ^ 3 + 24 * x ^ 2 - 32 * x + 16 := by
  refine ⟨?_, by ring⟩
  rw [sub_eq_add_neg, add_comm, add_pow]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Stitz-Zeager Example 9.4.2(2): `2.1^3 = (2 + 1/10)^3 = 9.261`, i.e. `9261/1000`. -/
@[kb "stitzzeager2013" "Example 9.4.2, p. 699"]
theorem ex_9_4_2_2 : (2 + 1 / 10 : ℚ) ^ 3 = 9261 / 1000 := by
  norm_num

/-- Stitz-Zeager Example 9.4.2(3): in `(2x + y)^5` the term with `x^3` (index `j = 2`) is
`C(5,2) (2x)^3 y^2 = 80 x^3 y^2`. -/
@[kb "stitzzeager2013" "Example 9.4.2, p. 699"]
theorem ex_9_4_2_3 (x y : ℝ) :
    (Nat.choose 5 2 : ℝ) * (2 * x) ^ (5 - 2) * y ^ 2 = 80 * x ^ 3 * y ^ 2 := by
  rw [show Nat.choose 5 2 = 10 by decide, show 5 - 2 = 3 by rfl]
  push_cast
  ring

end UndergradKB.Precalculus.Course
