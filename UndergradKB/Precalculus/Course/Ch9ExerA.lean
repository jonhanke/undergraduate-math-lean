import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import UndergradKB.Precalculus.Sequences
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 9 (Stitz-Zeager): exercises with the book's answers -/

namespace UndergradKB.Precalculus.Course

open Finset UndergradKB.Precalculus

/-! ## Section 9.1 -/

/-- Stitz-Zeager Exercise 9.1.1: for `aₙ = 2ⁿ - 1`, `n ≥ 0`, the first four terms are `0, 1, 3, 7`. -/
@[kb "stitzzeager2013" "Exercise 9.1.1, p. 670"]
theorem exer_9_1_1 (a : ℕ → ℝ) (h : ∀ n, a n = 2 ^ n - 1) :
    a 0 = 0 ∧ a 1 = 1 ∧ a 2 = 3 ∧ a 3 = 7 := by
  simp only [h]; norm_num

/-- Stitz-Zeager Exercise 9.1.2: for `dⱼ = (-1)^(j(j+1)/2)`, `j ≥ 1`, the first four terms are
`-1, -1, 1, 1`. -/
@[kb "stitzzeager2013" "Exercise 9.1.2, p. 670"]
theorem exer_9_1_2 (d : ℕ → ℤ) (h : ∀ j, d j = (-1) ^ (j * (j + 1) / 2)) :
    d 1 = -1 ∧ d 2 = -1 ∧ d 3 = 1 ∧ d 4 = 1 := by
  simp only [h]; norm_num

/-- Stitz-Zeager Exercise 9.1.3: the sequence `5k - 2`, `k ≥ 1`, starts `3, 8, 13, 18`. -/
@[kb "stitzzeager2013" "Exercise 9.1.3, p. 670"]
theorem exer_9_1_3 (a : ℕ → ℝ) (h : ∀ k, a k = 5 * k - 2) :
    a 1 = 3 ∧ a 2 = 8 ∧ a 3 = 13 ∧ a 4 = 18 := by
  simp only [h]; norm_num

/-- Stitz-Zeager Exercise 9.1.4: the sequence `(n²+1)/(n+1)`, `n ≥ 0`, starts `1, 1, 5/3, 5/2`. -/
@[kb "stitzzeager2013" "Exercise 9.1.4, p. 670"]
theorem exer_9_1_4 (a : ℕ → ℝ) (h : ∀ n, a n = ((n : ℝ) ^ 2 + 1) / (n + 1)) :
    a 0 = 1 ∧ a 1 = 1 ∧ a 2 = 5 / 3 ∧ a 3 = 5 / 2 := by
  simp only [h]; norm_num

/-- Stitz-Zeager Exercise 9.1.5: the sequence `xⁿ/n²`, `n ≥ 1`, starts `x, x²/4, x³/9, x⁴/16`. -/
@[kb "stitzzeager2013" "Exercise 9.1.5, p. 670"]
theorem exer_9_1_5 (x : ℝ) (a : ℕ → ℝ) (h : ∀ n, a n = x ^ n / (n : ℝ) ^ 2) :
    a 1 = x ∧ a 2 = x ^ 2 / 4 ∧ a 3 = x ^ 3 / 9 ∧ a 4 = x ^ 4 / 16 := by
  simp only [h]; norm_num

/-- Stitz-Zeager Exercise 9.1.7: `a₁ = 3`, `aₙ₊₁ = aₙ - 1` gives `3, 2, 1, 0`. -/
@[kb "stitzzeager2013" "Exercise 9.1.7, p. 670"]
theorem exer_9_1_7 (a : ℕ → ℝ) (h1 : a 1 = 3) (h : ∀ n, 1 ≤ n → a (n + 1) = a n - 1) :
    a 1 = 3 ∧ a 2 = 2 ∧ a 3 = 1 ∧ a 4 = 0 := by
  have h2 := h 1 le_rfl
  have h3 := h 2 (by norm_num)
  have h4 := h 3 (by norm_num)
  refine ⟨h1, ?_, ?_, ?_⟩ <;> norm_num at h2 h3 h4 <;> linarith

/-- Stitz-Zeager Exercise 9.1.9: `b₁ = 2`, `bₖ₊₁ = 3bₖ + 1` gives `2, 7, 22, 67`. -/
@[kb "stitzzeager2013" "Exercise 9.1.9, p. 670"]
theorem exer_9_1_9 (b : ℕ → ℝ) (h1 : b 1 = 2) (h : ∀ k, 1 ≤ k → b (k + 1) = 3 * b k + 1) :
    b 1 = 2 ∧ b 2 = 7 ∧ b 3 = 22 ∧ b 4 = 67 := by
  have h2 := h 1 le_rfl
  have h3 := h 2 (by norm_num)
  have h4 := h 3 (by norm_num)
  refine ⟨h1, ?_, ?_, ?_⟩ <;> norm_num at h2 h3 h4 <;> linarith

/-- Stitz-Zeager Exercise 9.1.10: `c₀ = -2`, `cⱼ = cⱼ₋₁/((j+1)(j+2))` gives
`-2, -1/3, -1/36, -1/720`. -/
@[kb "stitzzeager2013" "Exercise 9.1.10, p. 670"]
theorem exer_9_1_10 (c : ℕ → ℝ) (h0 : c 0 = -2)
    (h : ∀ j, c (j + 1) = c j / (((j : ℝ) + 2) * ((j : ℝ) + 3))) :
    c 0 = -2 ∧ c 1 = -1 / 3 ∧ c 2 = -1 / 36 ∧ c 3 = -1 / 720 := by
  have h1 := h 0
  have h2 := h 1
  have h3 := h 2
  refine ⟨h0, ?_, ?_, ?_⟩
  · rw [h1, h0]; norm_num
  · rw [h2, h1, h0]; norm_num
  · rw [h3, h2, h1, h0]; norm_num

/-- Stitz-Zeager Exercise 9.1.12: `s₀ = 1`, `sₙ₊₁ = xⁿ⁺¹ + sₙ` gives `1, x+1, x²+x+1, x³+x²+x+1`. -/
@[kb "stitzzeager2013" "Exercise 9.1.12, p. 670"]
theorem exer_9_1_12 (x : ℝ) (s : ℕ → ℝ) (h0 : s 0 = 1) (h : ∀ n, s (n + 1) = x ^ (n + 1) + s n) :
    s 0 = 1 ∧ s 1 = x + 1 ∧ s 2 = x ^ 2 + x + 1 ∧ s 3 = x ^ 3 + x ^ 2 + x + 1 := by
  have h1 := h 0
  have h2 := h 1
  have h3 := h 2
  refine ⟨h0, ?_, ?_, ?_⟩
  · rw [h1, h0]; ring
  · rw [h2, h1, h0]; ring
  · rw [h3, h2, h1, h0]; ring

/-- Stitz-Zeager Exercise 9.1.13: the Fibonacci sequence `F₀ = F₁ = 1`, `Fₙ = Fₙ₋₁ + Fₙ₋₂` starts
`1, 1, 2, 3`. -/
@[kb "stitzzeager2013" "Exercise 9.1.13, p. 670"]
theorem exer_9_1_13 (F : ℕ → ℕ) (h0 : F 0 = 1) (h1 : F 1 = 1)
    (h : ∀ n, F (n + 2) = F (n + 1) + F n) :
    F 0 = 1 ∧ F 1 = 1 ∧ F 2 = 2 ∧ F 3 = 3 := by
  have h2 := h 0
  have h3 := h 1
  refine ⟨h0, h1, ?_, ?_⟩
  · rw [h2, h1, h0]
  · rw [h3, h2, h1, h0]

/-- Stitz-Zeager Exercise 9.1.14: `3n - 5` is arithmetic with common difference `3`. -/
@[kb "stitzzeager2013" "Exercise 9.1.14, p. 670"]
theorem exer_9_1_14 : IsArithmeticSeq (fun n : ℕ => 3 * (n : ℝ) - 5) 3 := by
  intro n _; push_cast; ring

/-- Stitz-Zeager Exercise 9.1.15: `n² + 3n + 2` is neither arithmetic nor geometric. -/
@[kb "stitzzeager2013" "Exercise 9.1.15, p. 670"]
theorem exer_9_1_15 : (¬ ∃ d, IsArithmeticSeq (fun n : ℕ => (n : ℝ) ^ 2 + 3 * n + 2) d) ∧
    ¬ ∃ r, IsGeometricSeq (fun n : ℕ => (n : ℝ) ^ 2 + 3 * n + 2) r := by
  constructor
  · rintro ⟨d, h⟩
    have h1 := h 1 le_rfl
    have h2 := h 2 (by norm_num)
    norm_num at h1 h2
    linarith
  · rintro ⟨r, h⟩
    have h1 := h 1 le_rfl
    have h2 := h 2 (by norm_num)
    norm_num at h1 h2
    linarith

/-- Stitz-Zeager Exercise 9.1.16: `1/3, 1/6, 1/12, ...` is geometric with ratio `1/2`. -/
@[kb "stitzzeager2013" "Exercise 9.1.16, p. 670"]
theorem exer_9_1_16 : IsGeometricSeq (fun n : ℕ => (1 / 3 : ℝ) * (1 / 2) ^ (n - 1)) (1 / 2) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp [pow_succ]; ring

/-- Stitz-Zeager Exercise 9.1.17: `3 (1/5)^(n-1)` is geometric with ratio `1/5`. -/
@[kb "stitzzeager2013" "Exercise 9.1.17, p. 670"]
theorem exer_9_1_17 : IsGeometricSeq (fun n : ℕ => (3 : ℝ) * (1 / 5) ^ (n - 1)) (1 / 5) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp [pow_succ]; ring

/-- Stitz-Zeager Exercise 9.1.18: `17, 5, -7, -19, ...` is arithmetic with difference `-12`. -/
@[kb "stitzzeager2013" "Exercise 9.1.18, p. 670"]
theorem exer_9_1_18 : IsArithmeticSeq (fun n : ℕ => (17 : ℝ) - 12 * ((n : ℝ) - 1)) (-12) := by
  intro n _; push_cast; ring

/-- Stitz-Zeager Exercise 9.1.19: `2, 22, 222, 2222, ...` (that is `2(10ⁿ - 1)/9`) is neither
arithmetic nor geometric. -/
@[kb "stitzzeager2013" "Exercise 9.1.19, p. 670"]
theorem exer_9_1_19 : (¬ ∃ d, IsArithmeticSeq (fun n : ℕ => 2 * ((10 : ℝ) ^ n - 1) / 9) d) ∧
    ¬ ∃ r, IsGeometricSeq (fun n : ℕ => 2 * ((10 : ℝ) ^ n - 1) / 9) r := by
  constructor
  · rintro ⟨d, h⟩
    have h1 := h 1 le_rfl
    have h2 := h 2 (by norm_num)
    norm_num at h1 h2
    linarith
  · rintro ⟨r, h⟩
    have h1 := h 1 le_rfl
    have h2 := h 2 (by norm_num)
    norm_num at h1 h2
    linarith

/-- Stitz-Zeager Exercise 9.1.20: `0.9, 9, 90, 900, ...` is geometric with ratio `10`. -/
@[kb "stitzzeager2013" "Exercise 9.1.20, p. 670"]
theorem exer_9_1_20 : IsGeometricSeq (fun n : ℕ => (9 / 10 : ℝ) * 10 ^ (n - 1)) 10 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp [pow_succ]; ring

/-- Stitz-Zeager Exercise 9.1.21: `n!/2`, `n ≥ 0`, is neither arithmetic nor geometric. -/
@[kb "stitzzeager2013" "Exercise 9.1.21, p. 670"]
theorem exer_9_1_21 : (¬ ∃ d, IsArithmeticSeq (fun n : ℕ => (n.factorial : ℝ) / 2) d) ∧
    ¬ ∃ r, IsGeometricSeq (fun n : ℕ => (n.factorial : ℝ) / 2) r := by
  constructor
  · rintro ⟨d, h⟩
    have h1 := h 1 le_rfl
    have h2 := h 2 (by norm_num)
    norm_num [Nat.factorial] at h1 h2
    linarith
  · rintro ⟨r, h⟩
    have h1 := h 1 le_rfl
    have h2 := h 2 (by norm_num)
    norm_num [Nat.factorial] at h1 h2
    linarith

/-- Stitz-Zeager Exercise 9.1.22: the sequence `3, 5, 7, 9, ...` (arithmetic from `3` with step `2`)
has `aₙ = 1 + 2n`. -/
@[kb "stitzzeager2013" "Exercise 9.1.22, p. 670"]
theorem exer_9_1_22 (a : ℕ → ℝ) (h1 : a 1 = 3) (h : IsArithmeticSeq a 2) :
    ∀ n : ℕ, 1 ≤ n → a n = 1 + 2 * n := by
  intro n hn
  rw [seq_arith_nth_term h n hn, h1]; ring

/-- Stitz-Zeager Exercise 9.1.23: `1, -1/2, 1/4, -1/8, ...` (geometric with ratio `-1/2`) has
`aₙ = (-1/2)^(n-1)`. -/
@[kb "stitzzeager2013" "Exercise 9.1.23, p. 670"]
theorem exer_9_1_23 (a : ℕ → ℝ) (h1 : a 1 = 1) (h : IsGeometricSeq a (-1 / 2)) :
    ∀ n : ℕ, 1 ≤ n → a n = (-1 / 2) ^ (n - 1) := by
  intro n hn
  rw [seq_geom_nth_term h n hn, h1]; ring

/-- Stitz-Zeager Exercise 9.1.24: the formula `2^(n-1)/(2n-1)` produces `1, 2/3, 4/5, 8/7`. -/
@[kb "stitzzeager2013" "Exercise 9.1.24, p. 670"]
theorem exer_9_1_24 (a : ℕ → ℝ) (h : ∀ n, a n = 2 ^ (n - 1) / (2 * n - 1)) :
    a 1 = 1 ∧ a 2 = 2 / 3 ∧ a 3 = 4 / 5 ∧ a 4 = 8 / 7 := by
  simp only [h]; norm_num

/-- Stitz-Zeager Exercise 9.1.26: the formula `1/n²` produces `1, 1/4, 1/9, 1/16`. -/
@[kb "stitzzeager2013" "Exercise 9.1.26, p. 670"]
theorem exer_9_1_26 (a : ℕ → ℝ) (h : ∀ n, a n = 1 / (n : ℝ) ^ 2) :
    a 1 = 1 ∧ a 2 = 1 / 4 ∧ a 3 = 1 / 9 ∧ a 4 = 1 / 16 := by
  simp only [h]; norm_num

/-- Stitz-Zeager Exercise 9.1.28: the formula `(10ⁿ - 1)/10ⁿ` produces `0.9, 0.99, 0.999, 0.9999`. -/
@[kb "stitzzeager2013" "Exercise 9.1.28, p. 671"]
theorem exer_9_1_28 (a : ℕ → ℝ) (h : ∀ n, a n = (10 ^ n - 1) / 10 ^ n) :
    a 1 = 0.9 ∧ a 2 = 0.99 ∧ a 3 = 0.999 ∧ a 4 = 0.9999 := by
  simp only [h]; norm_num

/-- Stitz-Zeager Exercise 9.1.29: the formula `(n+2)³` produces `27, 64, 125, 216`. -/
@[kb "stitzzeager2013" "Exercise 9.1.29, p. 671"]
theorem exer_9_1_29 (a : ℕ → ℝ) (h : ∀ n, a n = ((n : ℝ) + 2) ^ 3) :
    a 1 = 27 ∧ a 2 = 64 ∧ a 3 = 125 ∧ a 4 = 216 := by
  simp only [h]; norm_num

/-- Stitz-Zeager Exercise 9.1.30: the formula `(1 + (-1)^(n-1))/2` produces `1, 0, 1, 0`. -/
@[kb "stitzzeager2013" "Exercise 9.1.30, p. 671"]
theorem exer_9_1_30 (a : ℕ → ℝ) (h : ∀ n, a n = (1 + (-1) ^ (n - 1)) / 2) :
    a 1 = 1 ∧ a 2 = 0 ∧ a 3 = 1 ∧ a 4 = 0 := by
  simp only [h]; norm_num

/-! ## Section 9.2 -/

/-- Stitz-Zeager Exercise 9.2.1: `∑_{g=4}^{9} (5g + 3) = 213`. -/
@[kb "stitzzeager2013" "Exercise 9.2.1, p. 682"]
theorem exer_9_2_1 : ∑ g ∈ Icc (4 : ℕ) 9, (5 * (g : ℝ) + 3) = 213 := by
  norm_num [sum_Icc_succ_top]

/-- Stitz-Zeager Exercise 9.2.2: `∑_{k=3}^{8} 1/k = 341/280`. -/
@[kb "stitzzeager2013" "Exercise 9.2.2, p. 682"]
theorem exer_9_2_2 : ∑ k ∈ Icc (3 : ℕ) 8, (1 / (k : ℝ)) = 341 / 280 := by
  norm_num [sum_Icc_succ_top]

/-- Stitz-Zeager Exercise 9.2.3: `∑_{j=0}^{5} 2ʲ = 63`. -/
@[kb "stitzzeager2013" "Exercise 9.2.3, p. 682"]
theorem exer_9_2_3 : ∑ j ∈ range 6, (2 : ℝ) ^ j = 63 := by
  norm_num [sum_range_succ]

/-- Stitz-Zeager Exercise 9.2.4: `∑_{k=0}^{2} (3k - 5) xᵏ = -5 - 2x + x²`. -/
@[kb "stitzzeager2013" "Exercise 9.2.4, p. 682"]
theorem exer_9_2_4 (x : ℝ) :
    ∑ k ∈ range 3, (3 * (k : ℝ) - 5) * x ^ k = -5 - 2 * x + x ^ 2 := by
  norm_num [sum_range_succ]; ring

/-- Stitz-Zeager Exercise 9.2.5: `∑_{i=1}^{4} (i² + 1)/4 = 17/2`. -/
@[kb "stitzzeager2013" "Exercise 9.2.5, p. 682"]
theorem exer_9_2_5 : ∑ i ∈ Icc (1 : ℕ) 4, (1 / 4 : ℝ) * ((i : ℝ) ^ 2 + 1) = 17 / 2 := by
  norm_num [sum_Icc_succ_top]

/-- Stitz-Zeager Exercise 9.2.6: `∑_{n=1}^{100} (-1)ⁿ = 0`. -/
@[kb "stitzzeager2013" "Exercise 9.2.6, p. 682"]
theorem exer_9_2_6 : ∑ n ∈ Icc 1 100, ((-1 : ℤ)) ^ n = 0 := by
  decide +kernel

/-- Stitz-Zeager Exercise 9.2.7: `∑_{n=1}^{5} (n+1)!/n! = 20`. -/
@[kb "stitzzeager2013" "Exercise 9.2.7, p. 682"]
theorem exer_9_2_7 : ∑ n ∈ Icc 1 5, ((n + 1).factorial : ℚ) / n.factorial = 20 := by
  norm_num [sum_Icc_succ_top, Nat.factorial]

/-- Stitz-Zeager Exercise 9.2.8: `∑_{j=1}^{3} 5!/(j!(5-j)!) = 25`. -/
@[kb "stitzzeager2013" "Exercise 9.2.8, p. 682"]
theorem exer_9_2_8 :
    ∑ j ∈ Icc 1 3, ((Nat.factorial 5 : ℚ) / (j.factorial * (5 - j).factorial)) = 25 := by
  norm_num [sum_Icc_succ_top, Nat.factorial]

/-- Stitz-Zeager Exercise 9.2.9: `8 + 11 + 14 + 17 + 20 = ∑_{k=1}^{5} (3k + 5)`. -/
@[kb "stitzzeager2013" "Exercise 9.2.9, p. 682"]
theorem exer_9_2_9 : (8 + 11 + 14 + 17 + 20 : ℕ) = ∑ k ∈ Icc 1 5, (3 * k + 5) := by
  decide

/-- Stitz-Zeager Exercise 9.2.10: `1 - 2 + 3 - ... - 8 = ∑_{k=1}^{8} (-1)^(k-1) k`. -/
@[kb "stitzzeager2013" "Exercise 9.2.10, p. 682"]
theorem exer_9_2_10 :
    (1 - 2 + 3 - 4 + 5 - 6 + 7 - 8 : ℤ) = ∑ k ∈ Icc (1 : ℕ) 8, (-1 : ℤ) ^ (k - 1) * (k : ℤ) := by
  decide

/-- Stitz-Zeager Exercise 9.2.11: `x - x³/3 + x⁵/5 - x⁷/7 = ∑_{k=1}^{4} (-1)^(k-1) x^(2k-1)/(2k-1)`. -/
@[kb "stitzzeager2013" "Exercise 9.2.11, p. 682"]
theorem exer_9_2_11 (x : ℝ) :
    x - x ^ 3 / 3 + x ^ 5 / 5 - x ^ 7 / 7 =
      ∑ k ∈ Icc (1 : ℕ) 4, (-1 : ℝ) ^ (k - 1) * x ^ (2 * k - 1) / (2 * (k : ℝ) - 1) := by
  norm_num [sum_Icc_succ_top]; ring

/-- Stitz-Zeager Exercise 9.2.15: `1 - 1/4 + 1/9 - 1/16 + 1/25 - 1/36 = ∑_{k=1}^{6} (-1)^(k-1)/k²`. -/
@[kb "stitzzeager2013" "Exercise 9.2.15, p. 682"]
theorem exer_9_2_15 :
    (1 - 1 / 4 + 1 / 9 - 1 / 16 + 1 / 25 - 1 / 36 : ℝ) =
      ∑ k ∈ Icc (1 : ℕ) 6, (-1 : ℝ) ^ (k - 1) / (k : ℝ) ^ 2 := by
  norm_num [sum_Icc_succ_top]

/-- Stitz-Zeager Exercise 9.2.16: `∑_{k=1}^{4} (1/2k)(x-5)ᵏ` is the displayed four-term sum. -/
@[kb "stitzzeager2013" "Exercise 9.2.16, p. 682"]
theorem exer_9_2_16 (x : ℝ) :
    (1 / 2) * (x - 5) + (1 / 4) * (x - 5) ^ 2 + (1 / 6) * (x - 5) ^ 3 + (1 / 8) * (x - 5) ^ 4 =
      ∑ k ∈ Icc (1 : ℕ) 4, (1 / (2 * (k : ℝ))) * (x - 5) ^ k := by
  norm_num [sum_Icc_succ_top]

/-- Stitz-Zeager Exercise 9.2.17: `∑_{n=1}^{10} (5n + 3) = 305`. -/
@[kb "stitzzeager2013" "Exercise 9.2.17, p. 682"]
theorem exer_9_2_17 : ∑ n ∈ Icc (1 : ℕ) 10, (5 * (n : ℝ) + 3) = 305 := by
  norm_num [sum_Icc_succ_top]

/-- Stitz-Zeager Exercise 9.2.18: `∑_{n=1}^{20} (2n - 1) = 400`. -/
@[kb "stitzzeager2013" "Exercise 9.2.18, p. 682"]
theorem exer_9_2_18 : ∑ n ∈ Icc (1 : ℕ) 20, (2 * (n : ℝ) - 1) = 400 := by
  norm_num [sum_Icc_succ_top]

/-- Stitz-Zeager Exercise 9.2.19: `∑_{k=0}^{15} (3 - k) = -72`. -/
@[kb "stitzzeager2013" "Exercise 9.2.19, p. 682"]
theorem exer_9_2_19 : ∑ k ∈ range 16, (3 - (k : ℝ)) = -72 := by
  norm_num [sum_range_succ]

/-- Stitz-Zeager Exercise 9.2.20: `∑_{n=1}^{10} (1/2)ⁿ = 1023/1024`. -/
@[kb "stitzzeager2013" "Exercise 9.2.20, p. 682"]
theorem exer_9_2_20 : ∑ n ∈ Icc (1 : ℕ) 10, (1 / 2 : ℝ) ^ n = 1023 / 1024 := by
  norm_num [sum_Icc_succ_top]

/-- Stitz-Zeager Exercise 9.2.21: `∑_{n=1}^{5} (3/2)ⁿ = 633/32`. -/
@[kb "stitzzeager2013" "Exercise 9.2.21, p. 682"]
theorem exer_9_2_21 : ∑ n ∈ Icc (1 : ℕ) 5, (3 / 2 : ℝ) ^ n = 633 / 32 := by
  norm_num [sum_Icc_succ_top]

/-- Stitz-Zeager Exercise 9.2.22: `∑_{k=0}^{5} 2 (1/4)ᵏ = 1365/512`. -/
@[kb "stitzzeager2013" "Exercise 9.2.22, p. 682"]
theorem exer_9_2_22 : ∑ k ∈ range 6, 2 * (1 / 4 : ℝ) ^ k = 1365 / 512 := by
  norm_num [sum_range_succ]

/-- Stitz-Zeager Exercise 9.2.23: `1 + 4 + 7 + ... + 295 = 14652` (99 terms `1 + 3k`). -/
@[kb "stitzzeager2013" "Exercise 9.2.23, p. 682"]
theorem exer_9_2_23 : ∑ k ∈ range 99, (1 + 3 * (k : ℝ)) = 14652 ∧ 1 + 3 * (98 : ℝ) = 295 := by
  constructor
  · norm_num [sum_range_succ]
  · norm_num

/-- Stitz-Zeager Exercise 9.2.24: `4 + 2 + 0 - 2 - ... - 146 = -5396` (76 terms `4 - 2k`). -/
@[kb "stitzzeager2013" "Exercise 9.2.24, p. 682"]
theorem exer_9_2_24 : ∑ k ∈ range 76, (4 - 2 * (k : ℝ)) = -5396 ∧ 4 - 2 * (75 : ℝ) = -146 := by
  constructor
  · norm_num [sum_range_succ]
  · norm_num

/-- Stitz-Zeager Exercise 9.2.25: `1 + 3 + 9 + ... + 2187 = 3280`. -/
@[kb "stitzzeager2013" "Exercise 9.2.25, p. 682"]
theorem exer_9_2_25 : ∑ k ∈ range 8, (3 : ℝ) ^ k = 3280 ∧ (3 : ℝ) ^ 7 = 2187 := by
  constructor
  · norm_num [sum_range_succ]
  · norm_num

/-- Stitz-Zeager Exercise 9.2.26: `1/2 + 1/4 + ... + 1/256 = 255/256`. -/
@[kb "stitzzeager2013" "Exercise 9.2.26, p. 682"]
theorem exer_9_2_26 : ∑ k ∈ Icc (1 : ℕ) 8, (1 / 2 : ℝ) ^ k = 255 / 256 := by
  norm_num [sum_Icc_succ_top]

/-- Stitz-Zeager Exercise 9.2.27: `3 - 3/2 + 3/4 - ... + 3/256 = 513/256`. -/
@[kb "stitzzeager2013" "Exercise 9.2.27, p. 682"]
theorem exer_9_2_27 : ∑ k ∈ range 9, 3 * (-1 / 2 : ℝ) ^ k = 513 / 256 := by
  norm_num [sum_range_succ]

/-- Stitz-Zeager Exercise 9.2.29: `0.777... = 7/9` as a geometric series. -/
@[kb "stitzzeager2013" "Exercise 9.2.29, p. 682"]
theorem exer_9_2_29 : HasSum (fun n : ℕ => (7 / 10 : ℝ) * (1 / 10) ^ n) (7 / 9) := by
  have := (hasSum_geometric_of_lt_one (r := (1 / 10 : ℝ)) (by norm_num) (by norm_num)).mul_left
    (7 / 10)
  convert this using 1; norm_num

/-- Stitz-Zeager Exercise 9.2.30: `0.131313... = 13/99` as a geometric series. -/
@[kb "stitzzeager2013" "Exercise 9.2.30, p. 682"]
theorem exer_9_2_30 : HasSum (fun n : ℕ => (13 / 100 : ℝ) * (1 / 100) ^ n) (13 / 99) := by
  have := (hasSum_geometric_of_lt_one (r := (1 / 100 : ℝ)) (by norm_num) (by norm_num)).mul_left
    (13 / 100)
  convert this using 1; norm_num

/-- Stitz-Zeager Exercise 9.2.31: `10.159159... = 10 + 53/333 = 3383/333`. -/
@[kb "stitzzeager2013" "Exercise 9.2.31, p. 682"]
theorem exer_9_2_31 :
    HasSum (fun n : ℕ => (159 / 1000 : ℝ) * (1 / 1000) ^ n) (53 / 333) ∧
      (10 : ℝ) + 53 / 333 = 3383 / 333 := by
  refine ⟨?_, by norm_num⟩
  have := (hasSum_geometric_of_lt_one (r := (1 / 1000 : ℝ)) (by norm_num) (by norm_num)).mul_left
    (159 / 1000)
  convert this using 1; norm_num

/-- Stitz-Zeager Exercise 9.2.32: `-5.867676... = -(29/5) - 67/990 = -5809/990`. -/
@[kb "stitzzeager2013" "Exercise 9.2.32, p. 682"]
theorem exer_9_2_32 :
    HasSum (fun n : ℕ => (67 / 1000 : ℝ) * (1 / 100) ^ n) (67 / 990) ∧
      -(29 / 5 : ℝ) - 67 / 990 = -(5809 / 990) := by
  refine ⟨?_, by norm_num⟩
  have := (hasSum_geometric_of_lt_one (r := (1 / 100 : ℝ)) (by norm_num) (by norm_num)).mul_left
    (67 / 1000)
  convert this using 1; norm_num

/-- Stitz-Zeager Exercise 9.2.33: the future value of an ordinary annuity with payments `300` monthly
at annual rate `2.5%` for 17 years is `$76,163.67` to the cent. -/
@[kb "stitzzeager2013" "Exercise 9.2.33, p. 683"]
theorem exer_9_2_33 :
    |300 * ((1 + (0.025 : ℝ) / 12) ^ (12 * 17) - 1) / (0.025 / 12) - 76163.67| ≤ 0.005 := by
  rw [abs_le]; constructor <;> norm_num

/-- Stitz-Zeager Exercise 9.2.34: payments `50`, rate `1%`, 30 years: `$20,981.41` to the cent
(the book prints `20,981.40`). -/
@[kb "stitzzeager2013" "Exercise 9.2.34, p. 683"]
theorem exer_9_2_34 :
    |50 * ((1 + (0.01 : ℝ) / 12) ^ (12 * 30) - 1) / (0.01 / 12) - 20981.41| ≤ 0.005 := by
  have h : (1 + (0.01 : ℝ) / 12) ^ (12 * 30) = ((1 + (0.01 : ℝ) / 12) ^ 180) ^ 2 := by
    rw [← pow_mul]
  rw [h, abs_le]; constructor <;> norm_num

/-- Stitz-Zeager Exercise 9.2.35: payments `100`, rate `2%`, 20 years: `$29,479.68` to the cent
(the book prints `29,479.69`). -/
@[kb "stitzzeager2013" "Exercise 9.2.35, p. 683"]
theorem exer_9_2_35 :
    |100 * ((1 + (0.02 : ℝ) / 12) ^ (12 * 20) - 1) / (0.02 / 12) - 29479.68| ≤ 0.005 := by
  rw [abs_le]; constructor <;> norm_num

/-- Stitz-Zeager Exercise 9.2.36: payments `100`, rate `2%`, 25 years: `$38,882.11` to the cent
(the book prints `38,882.12`). -/
@[kb "stitzzeager2013" "Exercise 9.2.36, p. 683"]
theorem exer_9_2_36 :
    |100 * ((1 + (0.02 : ℝ) / 12) ^ (12 * 25) - 1) / (0.02 / 12) - 38882.11| ≤ 0.005 := by
  have h : (1 + (0.02 : ℝ) / 12) ^ (12 * 25) = ((1 + (0.02 : ℝ) / 12) ^ 150) ^ 2 := by
    rw [← pow_mul]
  rw [h, abs_le]; constructor <;> norm_num

/-- Stitz-Zeager Exercise 9.2.37: payments `100`, rate `2%`, 30 years: `$49,272.54` to the cent
(the book prints `49,272.55`). -/
@[kb "stitzzeager2013" "Exercise 9.2.37, p. 683"]
theorem exer_9_2_37 :
    |100 * ((1 + (0.02 : ℝ) / 12) ^ (12 * 30) - 1) / (0.02 / 12) - 49272.54| ≤ 0.005 := by
  have h : (1 + (0.02 : ℝ) / 12) ^ (12 * 30) = ((1 + (0.02 : ℝ) / 12) ^ 180) ^ 2 := by
    rw [← pow_mul]
  rw [h, abs_le]; constructor <;> norm_num

/-- Stitz-Zeager Exercise 9.2.38: payments `100`, rate `2%`, 35 years: `$60,754.78` to the cent
(the book prints `60,754.80`). -/
@[kb "stitzzeager2013" "Exercise 9.2.38, p. 683"]
theorem exer_9_2_38 :
    |100 * ((1 + (0.02 : ℝ) / 12) ^ (12 * 35) - 1) / (0.02 / 12) - 60754.78| ≤ 0.005 := by
  have h : (1 + (0.02 : ℝ) / 12) ^ (12 * 35) = ((1 + (0.02 : ℝ) / 12) ^ 210) ^ 2 := by
    rw [← pow_mul]
  rw [h, abs_le]; constructor <;> norm_num

/-- Stitz-Zeager Exercise 9.2.39: the monthly payment giving `$100,000` after 30 years at `2%`
is about `$202.95`. -/
@[kb "stitzzeager2013" "Exercise 9.2.39, p. 683"]
theorem exer_9_2_39 :
    |100000 * ((0.02 : ℝ) / 12) / ((1 + (0.02 : ℝ) / 12) ^ (12 * 30) - 1) - 202.95| ≤ 0.005 := by
  have h : (1 + (0.02 : ℝ) / 12) ^ (12 * 30) = ((1 + (0.02 : ℝ) / 12) ^ 180) ^ 2 := by
    rw [← pow_mul]
  rw [h, abs_le]; constructor <;> norm_num

end UndergradKB.Precalculus.Course
