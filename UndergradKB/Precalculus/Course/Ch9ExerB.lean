import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 9 (Stitz-Zeager): exercises with the book's answers, Sections 9.3-9.4 -/

namespace UndergradKB.Precalculus.Course

open Finset

/-! ## Section 9.3 (the exercises state the assertions to prove; the book prints some proofs) -/

/-- Stitz-Zeager Exercise 9.3.1: `∑_{j=1}^{n} j² = n(n+1)(2n+1)/6`. -/
@[kb "stitzzeager2013" "Exercise 9.3.1, p. 690"]
theorem exer_9_3_1 (n : ℕ) :
    ∑ j ∈ Icc 1 n, (j : ℝ) ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
  induction n with
  | zero => simp
  | succ k ih => rw [sum_Icc_succ_top (by omega), ih]; push_cast; ring

/-- Stitz-Zeager Exercise 9.3.2: `∑_{j=1}^{n} j³ = n²(n+1)²/4`. -/
@[kb "stitzzeager2013" "Exercise 9.3.2, p. 690"]
theorem exer_9_3_2 (n : ℕ) :
    ∑ j ∈ Icc 1 n, (j : ℝ) ^ 3 = (n : ℝ) ^ 2 * (n + 1) ^ 2 / 4 := by
  induction n with
  | zero => simp
  | succ k ih => rw [sum_Icc_succ_top (by omega), ih]; push_cast; ring

/-- Stitz-Zeager Exercise 9.3.3: `2ⁿ > 500 n` for `n > 12`. -/
@[kb "stitzzeager2013" "Exercise 9.3.3, p. 690"]
theorem exer_9_3_3 (n : ℕ) (hn : 12 < n) : 500 * n < 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ]; omega

/-- Stitz-Zeager Exercise 9.3.4: `3ⁿ > n³` for `n ≥ 4`. -/
@[kb "stitzzeager2013" "Exercise 9.3.4, p. 690"]
theorem exer_9_3_4 (n : ℕ) (hn : 4 ≤ n) : n ^ 3 < 3 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have h : (k + 1) ^ 3 ≤ 3 * k ^ 3 := by nlinarith [Nat.mul_le_mul hk hk, Nat.mul_le_mul (Nat.mul_le_mul hk hk) hk]
    rw [pow_succ 3 k]; omega

/-- Stitz-Zeager Exercise 9.3.5: `|xⁿ| = |x|ⁿ` for every real `x` and `n ≥ 1`. -/
@[kb "stitzzeager2013" "Exercise 9.3.5, p. 690"]
theorem exer_9_3_5 (x : ℝ) (n : ℕ) (hn : 1 ≤ n) : |x ^ n| = |x| ^ n := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ k hk ih => rw [pow_succ, abs_mul, ih, pow_succ]

/-- Stitz-Zeager Exercise 9.3.6: `log (xⁿ) = n log x` for `x > 0` and `n ≥ 1`. -/
@[kb "stitzzeager2013" "Exercise 9.3.6, p. 690"]
theorem exer_9_3_6 (x : ℝ) (hx : 0 < x) (n : ℕ) (hn : 1 ≤ n) :
    Real.log (x ^ n) = n * Real.log x := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [pow_succ, Real.log_mul (pow_pos hx k).ne' hx.ne', ih]; push_cast; ring

/-- Stitz-Zeager Exercise 9.3.7: `[[a,0],[0,b]]ⁿ = [[aⁿ,0],[0,bⁿ]]` for `n ≥ 1`. -/
@[kb "stitzzeager2013" "Exercise 9.3.7, p. 690"]
theorem exer_9_3_7 (a b : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (!![a, 0; 0, b] : Matrix (Fin 2) (Fin 2) ℝ) ^ n = !![a ^ n, 0; 0, b ^ n] := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ]

/-- Stitz-Zeager Exercise 9.3.8a: if `a₁ = a` and `aₙ₊₁ = r aₙ` then `aₙ = a rⁿ⁻¹`. -/
@[kb "stitzzeager2013" "Exercise 9.3.8a, p. 690"]
theorem exer_9_3_8a (a r : ℝ) (s : ℕ → ℝ) (h1 : s 1 = a) (h : ∀ n, 1 ≤ n → s (n + 1) = r * s n)
    (n : ℕ) (hn : 1 ≤ n) : s n = a * r ^ (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => simp [h1]
  | succ k hk ih => rw [h k hk, ih, Nat.add_sub_cancel]; obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩; simp [pow_succ]; ring

/-- Stitz-Zeager Exercise 9.3.8b: `∑_{j=1}^{n} a r^(j-1) = a (1 - rⁿ)/(1 - r)` for `r ≠ 1`, and
`= n a` for `r = 1`. -/
@[kb "stitzzeager2013" "Exercise 9.3.8b, p. 690"]
theorem exer_9_3_8b (a r : ℝ) (n : ℕ) :
    (r ≠ 1 → ∑ j ∈ Icc 1 n, a * r ^ (j - 1) = a * ((1 - r ^ n) / (1 - r))) ∧
      (r = 1 → ∑ j ∈ Icc 1 n, a * r ^ (j - 1) = n * a) := by
  constructor
  · intro hr
    have h1 : 1 - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hr)
    induction n with
    | zero => simp
    | succ k ih =>
      rw [sum_Icc_succ_top (by omega), ih, Nat.add_sub_cancel]
      field_simp
      ring
  · rintro rfl
    induction n with
    | zero => simp
    | succ k ih => rw [sum_Icc_succ_top (by omega), ih]; push_cast; ring

/-- Stitz-Zeager Exercise 9.3.9: the determinant of a lower triangular matrix is the product of its
diagonal entries; in particular `det Iₙ = 1`. -/
@[kb "stitzzeager2013" "Exercise 9.3.9, p. 690"]
theorem exer_9_3_9 (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsLowerTriangular) :
    A.det = ∏ i, A i i ∧ (1 : Matrix (Fin n) (Fin n) ℝ).det = 1 := by
  exact ⟨Matrix.det_of_isLowerTriangular A hA, Matrix.det_one⟩

/-! ## Section 9.4 -/

/-- Stitz-Zeager Exercise 9.4.1: `(3!)² = 36`. -/
@[kb "stitzzeager2013" "Exercise 9.4.1, p. 703"]
theorem exer_9_4_1 : (Nat.factorial 3) ^ 2 = 36 := by decide

/-- Stitz-Zeager Exercise 9.4.2: `10!/7! = 720`. -/
@[kb "stitzzeager2013" "Exercise 9.4.2, p. 703"]
theorem exer_9_4_2 : (Nat.factorial 10 : ℚ) / Nat.factorial 7 = 720 := by
  norm_num [Nat.factorial]

/-- Stitz-Zeager Exercise 9.4.3: `7!/(2³ 3!) = 105`. -/
@[kb "stitzzeager2013" "Exercise 9.4.3, p. 703"]
theorem exer_9_4_3 : (Nat.factorial 7 : ℚ) / (2 ^ 3 * Nat.factorial 3) = 105 := by
  norm_num [Nat.factorial]

/-- Stitz-Zeager Exercise 9.4.4: `9!/(4! 3! 2!) = 1260`. -/
@[kb "stitzzeager2013" "Exercise 9.4.4, p. 703"]
theorem exer_9_4_4 :
    (Nat.factorial 9 : ℚ) / (Nat.factorial 4 * Nat.factorial 3 * Nat.factorial 2) = 1260 := by
  norm_num [Nat.factorial]

/-- Stitz-Zeager Exercise 9.4.5: `(n+1)!/n! = n + 1`. -/
@[kb "stitzzeager2013" "Exercise 9.4.5, p. 703"]
theorem exer_9_4_5 (n : ℕ) : (Nat.factorial (n + 1) : ℚ) / Nat.factorial n = n + 1 := by
  rw [Nat.factorial_succ]; push_cast
  field_simp [Nat.factorial_ne_zero]

/-- Stitz-Zeager Exercise 9.4.6: `(k-1)!/(k+2)! = 1/(k(k+1)(k+2))` for `k ≥ 1`. -/
@[kb "stitzzeager2013" "Exercise 9.4.6, p. 703"]
theorem exer_9_4_6 (k : ℕ) (hk : 1 ≤ k) :
    (Nat.factorial (k - 1) : ℚ) / Nat.factorial (k + 2) = 1 / (k * (k + 1) * (k + 2)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [show m + 1 + 2 = (m + 1 + 1) + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ,
    Nat.factorial_succ]
  push_cast
  have := (Nat.factorial_pos m).ne'
  field_simp
  ring

/-- Stitz-Zeager Exercise 9.4.7: `C(8,3) = 56`. -/
@[kb "stitzzeager2013" "Exercise 9.4.7, p. 703"]
theorem exer_9_4_7 : Nat.choose 8 3 = 56 := by decide

/-- Stitz-Zeager Exercise 9.4.8: `C(117,0) = 1`. -/
@[kb "stitzzeager2013" "Exercise 9.4.8, p. 703"]
theorem exer_9_4_8 : Nat.choose 117 0 = 1 := Nat.choose_zero_right 117

/-- Stitz-Zeager Exercise 9.4.9: `C(n, n-2) = n(n-1)/2` for `n ≥ 2`. -/
@[kb "stitzzeager2013" "Exercise 9.4.9, p. 703"]
theorem exer_9_4_9 (n : ℕ) (hn : 2 ≤ n) : (Nat.choose n (n - 2) : ℚ) = n * (n - 1) / 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [Nat.add_sub_cancel, Nat.choose_symm_add]
  have hd : 2 ∣ (m + 2) * (m + 1) := by
    simpa [mul_comm] using (Nat.even_mul_succ_self (m + 1)).two_dvd
  have h : (m + 2).choose 2 * 2 = (m + 2) * (m + 1) := by
    rw [Nat.choose_two_right]; exact Nat.div_mul_cancel hd
  have h' := congrArg (Nat.cast : ℕ → ℚ) h
  push_cast at h' ⊢
  linarith

/-- Stitz-Zeager Exercise 9.4.10: `(x+2)⁵ = x⁵ + 10x⁴ + 40x³ + 80x² + 80x + 32`. -/
@[kb "stitzzeager2013" "Exercise 9.4.10, p. 703"]
theorem exer_9_4_10 (x : ℝ) :
    (x + 2) ^ 5 = x ^ 5 + 10 * x ^ 4 + 40 * x ^ 3 + 80 * x ^ 2 + 80 * x + 32 := by ring

/-- Stitz-Zeager Exercise 9.4.11: `(2x-1)⁴ = 16x⁴ - 32x³ + 24x² - 8x + 1`. -/
@[kb "stitzzeager2013" "Exercise 9.4.11, p. 703"]
theorem exer_9_4_11 (x : ℝ) :
    (2 * x - 1) ^ 4 = 16 * x ^ 4 - 32 * x ^ 3 + 24 * x ^ 2 - 8 * x + 1 := by ring

/-- Stitz-Zeager Exercise 9.4.12: `(x/3 + y²)³ = x³/27 + x²y²/3 + x y⁴ + y⁶`. -/
@[kb "stitzzeager2013" "Exercise 9.4.12, p. 703"]
theorem exer_9_4_12 (x y : ℝ) :
    (1 / 3 * x + y ^ 2) ^ 3 = 1 / 27 * x ^ 3 + 1 / 3 * x ^ 2 * y ^ 2 + x * y ^ 4 + y ^ 6 := by
  ring

/-- Stitz-Zeager Exercise 9.4.13: `(x - 1/x)⁴ = x⁴ - 4x² + 6 - 4x⁻² + x⁻⁴` for `x ≠ 0`. -/
@[kb "stitzzeager2013" "Exercise 9.4.13, p. 703"]
theorem exer_9_4_13 (x : ℝ) (hx : x ≠ 0) :
    (x - x⁻¹) ^ 4 = x ^ 4 - 4 * x ^ 2 + 6 - 4 * x⁻¹ ^ 2 + x⁻¹ ^ 4 := by
  field_simp
  ring

/-- Stitz-Zeager Exercise 9.4.14: `(1 + 2i)⁴ = -7 - 24i`. -/
@[kb "stitzzeager2013" "Exercise 9.4.14, p. 703"]
theorem exer_9_4_14 : (1 + 2 * Complex.I) ^ 4 = -7 - 24 * Complex.I := by
  ring_nf
  simp [Complex.I_sq]
  ring

/-- Stitz-Zeager Exercise 9.4.15: `(-1 + i√3)³ = 8`. -/
@[kb "stitzzeager2013" "Exercise 9.4.15, p. 703"]
theorem exer_9_4_15 : (-1 + (Real.sqrt 3 : ℂ) * Complex.I) ^ 3 = 8 := by
  have hs : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination (-3 * (Complex.I ^ 2 + 1) + 3 - (Real.sqrt 3 : ℂ) * Complex.I
    + (Real.sqrt 3 : ℂ) * Complex.I * (Complex.I ^ 2 + 1)) * hs
    + (-9 + 3 * (Real.sqrt 3 : ℂ) * Complex.I) * hI

/-- Stitz-Zeager Exercise 9.4.16: `(√3/2 + i/2)³ = i`. -/
@[kb "stitzzeager2013" "Exercise 9.4.16, p. 703"]
theorem exer_9_4_16 :
    ((Real.sqrt 3 : ℂ) / 2 + Complex.I / 2) ^ 3 = Complex.I := by
  have hs : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have h3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 3 = 3 * (Real.sqrt 3 : ℂ) := by
    rw [pow_succ, hs]
  have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, hI]; ring
  have : ((Real.sqrt 3 : ℂ) / 2 + Complex.I / 2) ^ 3 =
      ((Real.sqrt 3 : ℂ) ^ 3 + 3 * (Real.sqrt 3 : ℂ) ^ 2 * Complex.I
        + 3 * (Real.sqrt 3 : ℂ) * Complex.I ^ 2 + Complex.I ^ 3) / 8 := by ring
  rw [this, h3, hs, hI, hI3]
  ring

/-- Stitz-Zeager Exercise 9.4.17: `(√2/2 - (√2/2) i)⁴ = -1`. -/
@[kb "stitzzeager2013" "Exercise 9.4.17, p. 703"]
theorem exer_9_4_17 :
    ((Real.sqrt 2 : ℂ) / 2 - (Real.sqrt 2 : ℂ) / 2 * Complex.I) ^ 4 = -1 := by
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have : ((Real.sqrt 2 : ℂ) / 2 - (Real.sqrt 2 : ℂ) / 2 * Complex.I) ^ 4 =
      ((Real.sqrt 2 : ℂ) ^ 2) ^ 2 * (1 - Complex.I) ^ 4 / 16 := by ring
  have h1 : (1 - Complex.I) ^ 4 = -4 := by
    have : (1 - Complex.I) ^ 2 = -2 * Complex.I := by
      linear_combination hI
    calc (1 - Complex.I) ^ 4 = ((1 - Complex.I) ^ 2) ^ 2 := by ring
      _ = -4 := by rw [this]; linear_combination 4 * hI
  rw [this, hs, h1]; norm_num

/-- Stitz-Zeager Exercise 9.4.18: the `x³` term of `(2x - y)⁵` is `80 x³ y²`. -/
@[kb "stitzzeager2013" "Exercise 9.4.18, p. 703"]
theorem exer_9_4_18 (x y : ℝ) :
    (2 * x) ^ 3 * (-y) ^ (5 - 3) * (Nat.choose 5 3 : ℝ) = 80 * x ^ 3 * y ^ 2 := by
  norm_num [Nat.choose]; ring

/-- Stitz-Zeager Exercise 9.4.19: the `x¹¹⁷` term of `(x + 2)¹¹⁸` is `236 x¹¹⁷`. -/
@[kb "stitzzeager2013" "Exercise 9.4.19, p. 703"]
theorem exer_9_4_19 (x : ℝ) :
    x ^ 117 * 2 ^ (118 - 117) * (Nat.choose 118 117 : ℝ) = 236 * x ^ 117 := by
  rw [show Nat.choose 118 117 = 118 by decide]; norm_num; ring

/-- Stitz-Zeager Exercise 9.4.20: the `x^(7/2)` term of `(√x - 3)⁸` is `-24 x^(7/2)`. -/
@[kb "stitzzeager2013" "Exercise 9.4.20, p. 703"]
theorem exer_9_4_20 (x : ℝ) (hx : 0 < x) :
    Real.sqrt x ^ 7 * (-3) ^ (8 - 7) * (Nat.choose 8 7 : ℝ) = -24 * x ^ (7 / 2 : ℝ) := by
  have : Real.sqrt x ^ 7 = x ^ (7 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
  rw [this, show Nat.choose 8 7 = 8 by decide]; norm_num; ring

/-- Stitz-Zeager Exercise 9.4.21: the `x⁻⁷` term of `(2x - x⁻³)⁵` is `-40 x⁻⁷`. -/
@[kb "stitzzeager2013" "Exercise 9.4.21, p. 703"]
theorem exer_9_4_21 (x : ℝ) (hx : x ≠ 0) :
    (2 * x) ^ 2 * (-(x ^ (-3 : ℤ))) ^ (5 - 2) * (Nat.choose 5 2 : ℝ) = -40 * x ^ (-7 : ℤ) := by
  rw [show Nat.choose 5 2 = 10 by decide]
  have e1 : x ^ (-3 : ℤ) = (x ^ 3)⁻¹ := by rw [zpow_neg]; norm_cast
  have e2 : x ^ (-7 : ℤ) = (x ^ 7)⁻¹ := by rw [zpow_neg]; norm_cast
  rw [e1, e2, show 5 - 2 = 3 from rfl, Odd.neg_pow (by decide), inv_pow, ← pow_mul]
  field_simp
  push_cast
  ring

/-- Stitz-Zeager Exercise 9.4.22: the constant term of `(x + x⁻¹)⁸` is `70`. -/
@[kb "stitzzeager2013" "Exercise 9.4.22, p. 703"]
theorem exer_9_4_22 (x : ℝ) (hx : x ≠ 0) :
    x ^ 4 * x⁻¹ ^ (8 - 4) * (Nat.choose 8 4 : ℝ) = 70 := by
  rw [show Nat.choose 8 4 = 70 by decide, show 8 - 4 = 4 from rfl, inv_pow,
    mul_inv_cancel₀ (pow_ne_zero 4 hx)]
  norm_num

/-- Stitz-Zeager Exercise 9.4.23: `n! > 2ⁿ` for `n ≥ 4`. -/
@[kb "stitzzeager2013" "Exercise 9.4.23, p. 703"]
theorem exer_9_4_23 (n : ℕ) (hn : 4 ≤ n) : 2 ^ n < Nat.factorial n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [pow_succ, Nat.factorial_succ]
    nlinarith

/-- Stitz-Zeager Exercise 9.4.24: `∑_{j=0}^{n} C(n,j) = 2ⁿ`. -/
@[kb "stitzzeager2013" "Exercise 9.4.24, p. 703"]
theorem exer_9_4_24 (n : ℕ) : ∑ j ∈ range (n + 1), Nat.choose n j = 2 ^ n :=
  Nat.sum_range_choose n

/-- Stitz-Zeager Exercise 9.4.26: `C(5,2) = C(5,3) = 10`. -/
@[kb "stitzzeager2013" "Exercise 9.4.26, p. 703"]
theorem exer_9_4_26 : Nat.choose 5 2 = Nat.choose 5 3 ∧ Nat.choose 5 2 = 10 :=
  ⟨Nat.choose_symm_of_eq_add rfl, by decide⟩

end UndergradKB.Precalculus.Course
