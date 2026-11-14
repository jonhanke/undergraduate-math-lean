import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 9 (Stitz-Zeager): exercises with the book's answers (wave 7), Sections 9.1 and 9.2 -/

namespace UndergradKB.Precalculus.Course

open Finset

/-! ## Section 9.1 -/

/-- Stitz-Zeager Exercise 9.1.6: for `aₙ = ln(n)/n`, `n ≥ 1`, the first four terms are `0, ln(2)/2, ln(3)/3,
ln(4)/4`, and `ln(4)/4 = ln(2)/2`. -/
@[kb "stitzzeager2013" "Exercise 9.1.6, p. 670"]
theorem exer_9_1_6 (a : ℕ → ℝ) (h : ∀ n, a n = Real.log n / n) :
    a 1 = 0 ∧ a 2 = Real.log 2 / 2 ∧ a 3 = Real.log 3 / 3 ∧ a 4 = Real.log 4 / 4 ∧
      Real.log 4 / 4 = Real.log 2 / 2 := by
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [h]
  · simp [h]
  · simp [h]
  · simp [h]
  · rw [h4]; ring

/-- Stitz-Zeager Exercise 9.1.8: `d₀ = 12`, `dₘ = dₘ₋₁/100` gives `12, 0.12, 0.0012, 0.000012`. -/
@[kb "stitzzeager2013" "Exercise 9.1.8, p. 670"]
theorem exer_9_1_8 (d : ℕ → ℝ) (h0 : d 0 = 12) (h : ∀ m, d (m + 1) = d m / 100) :
    d 0 = 12 ∧ d 1 = 0.12 ∧ d 2 = 0.0012 ∧ d 3 = 0.000012 := by
  have h1 := h 0
  have h2 := h 1
  have h3 := h 2
  refine ⟨h0, ?_, ?_, ?_⟩
  · rw [h1, h0]; norm_num
  · rw [h2, h1, h0]; norm_num
  · rw [h3, h2, h1, h0]; norm_num

/-- Stitz-Zeager Exercise 9.1.11: `a₁ = 117`, `aₙ₊₁ = 1/aₙ` gives `117, 1/117, 117, 1/117`. -/
@[kb "stitzzeager2013" "Exercise 9.1.11, p. 670"]
theorem exer_9_1_11 (a : ℕ → ℝ) (h1 : a 1 = 117) (h : ∀ n, 1 ≤ n → a (n + 1) = 1 / a n) :
    a 1 = 117 ∧ a 2 = 1 / 117 ∧ a 3 = 117 ∧ a 4 = 1 / 117 := by
  have h2 := h 1 le_rfl
  have h3 := h 2 (by norm_num)
  have h4 := h 3 (by norm_num)
  have e2 : a 2 = 1 / 117 := by rw [h2, h1]
  have e3 : a 3 = 117 := by rw [h3, e2]; norm_num
  refine ⟨h1, e2, e3, ?_⟩
  rw [h4, e3]

/-- Stitz-Zeager Exercise 9.1.25: the sequence `1, 2/3, 1/3, 4/27, ...` has the explicit formula
`aₙ = n / 3^(n-1)`, `n ≥ 1`. -/
@[kb "stitzzeager2013" "Exercise 9.1.25, p. 670"]
theorem exer_9_1_25 (a : ℕ → ℝ) (h : ∀ n, a n = (n : ℝ) / 3 ^ (n - 1)) :
    a 1 = 1 ∧ a 2 = 2 / 3 ∧ a 3 = 1 / 3 ∧ a 4 = 4 / 27 := by
  simp only [h]; norm_num

/-- Stitz-Zeager Exercise 9.1.27: the sequence `x, -x³/3, x⁵/5, -x⁷/7, ...` has the explicit formula
`aₙ = (-1)^(n-1) x^(2n-1)/(2n-1)`, `n ≥ 1`. -/
@[kb "stitzzeager2013" "Exercise 9.1.27, p. 670"]
theorem exer_9_1_27 (x : ℝ) (a : ℕ → ℝ) (h : ∀ n, a n = (-1) ^ (n - 1) * x ^ (2 * n - 1) / (2 * (n : ℝ) - 1)) :
    a 1 = x ∧ a 2 = -x ^ 3 / 3 ∧ a 3 = x ^ 5 / 5 ∧ a 4 = -x ^ 7 / 7 := by
  simp only [h]; norm_num

/-- Stitz-Zeager Exercise 9.1.31: a constant sequence is both arithmetic (common difference `0`) and geometric
(common ratio `1`). -/
@[kb "stitzzeager2013" "Exercise 9.1.31, p. 671"]
theorem exer_9_1_31 : ∃ a : ℕ → ℝ, (∃ d : ℝ, ∀ n, a (n + 1) = a n + d) ∧
    (∃ r : ℝ, ∀ n, a (n + 1) = a n * r) ∧ ∀ n, a n ≠ 0 :=
  ⟨fun _ => 5, ⟨0, fun _ => by norm_num⟩, ⟨1, fun _ => by norm_num⟩, fun _ => by norm_num⟩

/-- Stitz-Zeager Exercise 9.1.32: taking `ln` of the terms of a (positive) geometric sequence gives an
arithmetic sequence with common difference `ln r`. -/
@[kb "stitzzeager2013" "Exercise 9.1.32, p. 671"]
theorem exer_9_1_32 (a : ℕ → ℝ) (r : ℝ) (hpos : ∀ n, 0 < a n) (h : ∀ n, a (n + 1) = a n * r) :
    ∀ n, Real.log (a (n + 1)) = Real.log (a n) + Real.log r := by
  have hr : r ≠ 0 := by
    intro h0
    have := h 0
    rw [h0, mul_zero] at this
    exact (hpos 1).ne' this
  intro n
  rw [h n, Real.log_mul (hpos n).ne' hr]

/-- Stitz-Zeager Exercise 9.1.34: doubling a penny each day for 30 days gives `2²⁹ = 536870912` pennies on the
30th day and `2³⁰ - 1 = 1073741823` pennies, i.e. `$10,737,418.23`, in total. -/
@[kb "stitzzeager2013" "Exercise 9.1.34, p. 671"]
theorem exer_9_1_34 : (2 : ℕ) ^ 29 = 536870912 ∧ ∑ k ∈ range 30, (2 : ℕ) ^ k = 1073741823 ∧
    ((1073741823 : ℚ) / 100 = 10737418.23) := by
  refine ⟨by norm_num, ?_, by norm_num⟩
  rw [Nat.geomSum_eq (le_refl 2)]
  norm_num

/-- Stitz-Zeager Exercise 9.1.35: in an arithmetic sequence each term is the arithmetic mean of its two
neighbors; in a geometric sequence the square of each term is the product of its two neighbors. -/
@[kb "stitzzeager2013" "Exercise 9.1.35, p. 671"]
theorem exer_9_1_35 (a : ℕ → ℝ) :
    ((∃ d : ℝ, ∀ n, a (n + 1) = a n + d) → ∀ k, a (k + 1) = (a k + a (k + 2)) / 2) ∧
    ((∃ r : ℝ, ∀ n, a (n + 1) = a n * r) → ∀ k, a (k + 1) ^ 2 = a k * a (k + 2)) := by
  constructor
  · rintro ⟨d, hd⟩ k
    rw [hd (k + 1), hd k]; ring
  · rintro ⟨r, hr⟩ k
    rw [hr (k + 1), hr k]; ring

/-- Stitz-Zeager Exercise 9.1.36: the sequence `i, -1, -i, 1, i, ...` has the explicit formula `aₙ = iⁿ`,
`n ≥ 1` (period `4`). -/
@[kb "stitzzeager2013" "Exercise 9.1.36, p. 671"]
theorem exer_9_1_36 : Complex.I ^ 1 = Complex.I ∧ Complex.I ^ 2 = -1 ∧ Complex.I ^ 3 = -Complex.I ∧
    Complex.I ^ 4 = 1 ∧ ∀ n : ℕ, Complex.I ^ (n + 4) = Complex.I ^ n := by
  refine ⟨by simp, by simp, by simp [pow_succ], by simp [pow_succ], fun n => ?_⟩
  rw [pow_add]; simp [pow_succ]

/-! ## Section 9.2 -/

/-- Stitz-Zeager Exercise 9.2.12: `1 + 2 + 4 + ... + 2²⁹ = ∑_{k=1}^{30} 2^(k-1)` (its value is `2³⁰ - 1`). -/
@[kb "stitzzeager2013" "Exercise 9.2.12, p. 682"]
theorem exer_9_2_12 : (2 : ℕ) ^ (1 - 1) = 1 ∧ (2 : ℕ) ^ (2 - 1) = 2 ∧ (2 : ℕ) ^ (3 - 1) = 4 ∧
    (2 : ℕ) ^ (30 - 1) = 2 ^ 29 ∧ ∑ k ∈ Icc (1 : ℕ) 30, (2 : ℕ) ^ (k - 1) = 2 ^ 30 - 1 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num [sum_Icc_succ_top]

/-- Stitz-Zeager Exercise 9.2.13: `2 + 3/2 + 4/3 + 5/4 + 6/5 = ∑_{k=1}^{5} (k+1)/k`. -/
@[kb "stitzzeager2013" "Exercise 9.2.13, p. 682"]
theorem exer_9_2_13 :
    (2 + 3 / 2 + 4 / 3 + 5 / 4 + 6 / 5 : ℚ) = ∑ k ∈ Icc (1 : ℕ) 5, ((k : ℚ) + 1) / k := by
  norm_num [sum_Icc_succ_top]

/-- Stitz-Zeager Exercise 9.2.14: `-ln 3 + ln 4 - ln 5 + ... + ln 20 = ∑_{k=3}^{20} (-1)^k ln k`. -/
@[kb "stitzzeager2013" "Exercise 9.2.14, p. 682"]
theorem exer_9_2_14 :
    (-Real.log 3 + Real.log 4 - Real.log 5 + Real.log 6 - Real.log 7 + Real.log 8 - Real.log 9 +
      Real.log 10 - Real.log 11 + Real.log 12 - Real.log 13 + Real.log 14 - Real.log 15 + Real.log 16 -
      Real.log 17 + Real.log 18 - Real.log 19 + Real.log 20 : ℝ) =
      ∑ k ∈ Icc (3 : ℕ) 20, (-1 : ℝ) ^ k * Real.log k := by
  norm_num [sum_Icc_succ_top]
  ring

/-- Stitz-Zeager Exercise 9.2.28: `∑_{n=1}^{10} (-2n + (5/3)ⁿ) = 17771050/59049`. -/
@[kb "stitzzeager2013" "Exercise 9.2.28, p. 682"]
theorem exer_9_2_28 : ∑ n ∈ Icc (1 : ℕ) 10, (-2 * (n : ℚ) + (5 / 3) ^ n) = 17771050 / 59049 := by
  norm_num [sum_Icc_succ_top]

/-- Stitz-Zeager Exercise 9.2.40: the basic properties of summation (sum and difference of sequences, constant
multiples, sum of a constant). -/
@[kb "stitzzeager2013" "Exercise 9.2.40, p. 683"]
theorem exer_9_2_40 (a b : ℕ → ℝ) (c : ℝ) (m p : ℕ) :
    ∑ n ∈ Icc m p, (a n + b n) = ∑ n ∈ Icc m p, a n + ∑ n ∈ Icc m p, b n ∧
    ∑ n ∈ Icc m p, (a n - b n) = ∑ n ∈ Icc m p, a n - ∑ n ∈ Icc m p, b n ∧
    ∑ n ∈ Icc m p, c * a n = c * ∑ n ∈ Icc m p, a n ∧
    ∑ _n ∈ Icc m p, c = ((p + 1 - m : ℕ) : ℝ) * c := by
  refine ⟨sum_add_distrib, sum_sub_distrib _ _, (mul_sum _ _ _).symm, ?_⟩
  rw [sum_const, Nat.card_Icc, nsmul_eq_mul]

/-- Stitz-Zeager Exercise 9.2.41: the future value of an annuity due, `∑_{k=1}^{N} P (1+i)^k`, equals
`P (1+i) ((1+i)^N - 1)/i` for `i ≠ 0`. -/
@[kb "stitzzeager2013" "Exercise 9.2.41, p. 683"]
theorem exer_9_2_41 (P i : ℝ) (hi : i ≠ 0) (N : ℕ) :
    ∑ k ∈ range N, P * (1 + i) ^ (k + 1) = P * (1 + i) * ((1 + i) ^ N - 1) / i := by
  have h := geom_sum_eq (x := 1 + i) (by intro h; apply hi; linarith) N
  have h1 : (1 + i - 1) = i := by ring
  rw [h1] at h
  calc ∑ k ∈ range N, P * (1 + i) ^ (k + 1)
      = P * (1 + i) * ∑ k ∈ range N, (1 + i) ^ k := by
        rw [mul_sum]; refine sum_congr rfl fun k _ => ?_; ring
    _ = P * (1 + i) * ((1 + i) ^ N - 1) / i := by rw [h]; ring

end UndergradKB.Precalculus.Course
