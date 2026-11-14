import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.IntervalCases
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.DescartesParity

/-! # Course layer, Chapter 3 (Stitz-Zeager): exercises with the book's answers (wave 8), Section 3.3 -/

namespace UndergradKB.Precalculus.Course

open Set Polynomial

/-- Stitz-Zeager Exercise 3.3.1 (Rational Zeros Theorem): every rational zero of `x ^ 3 - 2 * x ^ 2 - 5 * x + 6` lies in the
book's list of candidates (numerators dividing `6`, denominators dividing `1`). -/
@[kb "stitzzeager2013" "Exercise 3.3.1, p. 292"]
theorem exer_3_3_1_rational (q : ℚ)
    (hq : q ^ 3 - 2 * q ^ 2 - 5 * q + 6 = 0) :
    q ∈ ({1, -1, 2, -2, 3, -3, 6, -6} : Finset ℚ) := by
  obtain ⟨n, d, hd, hcop, rfl⟩ : ∃ n d : ℤ, 0 < d ∧ IsCoprime n d ∧ q = n / d :=
    ⟨q.num, q.den, by exact_mod_cast q.den_pos, Rat.isCoprime_num_den q, by simp [Rat.num_div_den]⟩
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have e : n ^ 3 - 2 * n ^ 2 * d - 5 * n * d ^ 2 + 6 * d ^ 3 = 0 := by
    have : ((n ^ 3 - 2 * n ^ 2 * d - 5 * n * d ^ 2 + 6 * d ^ 3 : ℤ) : ℚ) = 0 := by
      push_cast
      field_simp at hq
      linarith
    exact_mod_cast this
  have h1 : d ∣ 1 * n ^ 3 :=
    ⟨-(6 * d ^ 2 - 5 * n * d - 2 * n ^ 2), by linear_combination e⟩
  have h2 : n ∣ 6 * d ^ 3 :=
    ⟨-(-5 * d ^ 2 - 2 * n * d + n ^ 2), by linear_combination e⟩
  have h1' : d ∣ 1 := (hcop.symm.pow_right (n := 3)).dvd_of_dvd_mul_right h1
  have h2' : n ∣ 6 := (hcop.pow_right (n := 3)).dvd_of_dvd_mul_right h2
  have hd2 : d ≤ 1 := Int.le_of_dvd (by norm_num) h1'
  have hn3 : n ≤ 6 := Int.le_of_dvd (by norm_num) (by simpa using h2')
  have hn3' : -n ≤ 6 := Int.le_of_dvd (by norm_num) (by simpa using (neg_dvd).2 h2')
  have hd1 : 1 ≤ d := hd
  have hn : -6 ≤ n := by omega
  have hmem : ∀ x : ℚ, x ∈ ({1, -1, 2, -2, 3, -3, 6, -6} : Finset ℚ) ↔
      x = 1 ∨ x = -1 ∨ x = 2 ∨ x = -2 ∨ x = 3 ∨ x = -3 ∨ x = 6 ∨ x = -6 := by
    intro x; simp
  rw [hmem]
  interval_cases n <;> interval_cases d <;> first | (norm_num at e; done) | norm_num

/-- Stitz-Zeager Exercise 3.3.2 (Rational Zeros Theorem): every rational zero of `x ^ 4 + 2 * x ^ 3 - 12 * x ^ 2 - 40 * x - 32` lies in the
book's list of candidates (numerators dividing `32`, denominators dividing `1`). -/
@[kb "stitzzeager2013" "Exercise 3.3.2, p. 292"]
theorem exer_3_3_2_rational (q : ℚ)
    (hq : q ^ 4 + 2 * q ^ 3 - 12 * q ^ 2 - 40 * q - 32 = 0) :
    q ∈ ({1, -1, 2, -2, 4, -4, 8, -8, 16, -16, 32, -32} : Finset ℚ) := by
  obtain ⟨n, d, hd, hcop, rfl⟩ : ∃ n d : ℤ, 0 < d ∧ IsCoprime n d ∧ q = n / d :=
    ⟨q.num, q.den, by exact_mod_cast q.den_pos, Rat.isCoprime_num_den q, by simp [Rat.num_div_den]⟩
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have e : n ^ 4 + 2 * n ^ 3 * d - 12 * n ^ 2 * d ^ 2 - 40 * n * d ^ 3 - 32 * d ^ 4 = 0 := by
    have : ((n ^ 4 + 2 * n ^ 3 * d - 12 * n ^ 2 * d ^ 2 - 40 * n * d ^ 3 - 32 * d ^ 4 : ℤ) : ℚ) = 0 := by
      push_cast
      field_simp at hq
      linarith
    exact_mod_cast this
  have h1 : d ∣ 1 * n ^ 4 :=
    ⟨-(-32 * d ^ 3 - 40 * n * d ^ 2 - 12 * n ^ 2 * d + 2 * n ^ 3), by linear_combination e⟩
  have h2 : n ∣ 32 * d ^ 4 :=
    ⟨-40 * d ^ 3 - 12 * n * d ^ 2 + 2 * n ^ 2 * d + n ^ 3, by linear_combination -e⟩
  have h1' : d ∣ 1 := (hcop.symm.pow_right (n := 4)).dvd_of_dvd_mul_right h1
  have h2' : n ∣ 32 := (hcop.pow_right (n := 4)).dvd_of_dvd_mul_right h2
  have hd2 : d ≤ 1 := Int.le_of_dvd (by norm_num) h1'
  have hn3 : n ≤ 32 := Int.le_of_dvd (by norm_num) (by simpa using h2')
  have hn3' : -n ≤ 32 := Int.le_of_dvd (by norm_num) (by simpa using (neg_dvd).2 h2')
  have hd1 : 1 ≤ d := hd
  have hn : -32 ≤ n := by omega
  have hmem : ∀ x : ℚ, x ∈ ({1, -1, 2, -2, 4, -4, 8, -8, 16, -16, 32, -32} : Finset ℚ) ↔
      x = 1 ∨ x = -1 ∨ x = 2 ∨ x = -2 ∨ x = 4 ∨ x = -4 ∨ x = 8 ∨ x = -8 ∨ x = 16 ∨ x = -16 ∨ x = 32 ∨ x = -32 := by
    intro x; simp
  rw [hmem]
  interval_cases n <;> interval_cases d <;> first | (norm_num at e; done) | norm_num

/-- Stitz-Zeager Exercise 3.3.3 (Rational Zeros Theorem): every rational zero of `x ^ 4 - 9 * x ^ 2 - 4 * x + 12` lies in the
book's list of candidates (numerators dividing `12`, denominators dividing `1`). -/
@[kb "stitzzeager2013" "Exercise 3.3.3, p. 292"]
theorem exer_3_3_3_rational (q : ℚ)
    (hq : q ^ 4 - 9 * q ^ 2 - 4 * q + 12 = 0) :
    q ∈ ({1, -1, 2, -2, 3, -3, 4, -4, 6, -6, 12, -12} : Finset ℚ) := by
  obtain ⟨n, d, hd, hcop, rfl⟩ : ∃ n d : ℤ, 0 < d ∧ IsCoprime n d ∧ q = n / d :=
    ⟨q.num, q.den, by exact_mod_cast q.den_pos, Rat.isCoprime_num_den q, by simp [Rat.num_div_den]⟩
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have e : n ^ 4 - 9 * n ^ 2 * d ^ 2 - 4 * n * d ^ 3 + 12 * d ^ 4 = 0 := by
    have : ((n ^ 4 - 9 * n ^ 2 * d ^ 2 - 4 * n * d ^ 3 + 12 * d ^ 4 : ℤ) : ℚ) = 0 := by
      push_cast
      field_simp at hq
      linarith
    exact_mod_cast this
  have h1 : d ∣ 1 * n ^ 4 :=
    ⟨-(12 * d ^ 3 - 4 * n * d ^ 2 - 9 * n ^ 2 * d), by linear_combination e⟩
  have h2 : n ∣ 12 * d ^ 4 :=
    ⟨-(-4 * d ^ 3 - 9 * n * d ^ 2 + n ^ 3), by linear_combination e⟩
  have h1' : d ∣ 1 := (hcop.symm.pow_right (n := 4)).dvd_of_dvd_mul_right h1
  have h2' : n ∣ 12 := (hcop.pow_right (n := 4)).dvd_of_dvd_mul_right h2
  have hd2 : d ≤ 1 := Int.le_of_dvd (by norm_num) h1'
  have hn3 : n ≤ 12 := Int.le_of_dvd (by norm_num) (by simpa using h2')
  have hn3' : -n ≤ 12 := Int.le_of_dvd (by norm_num) (by simpa using (neg_dvd).2 h2')
  have hd1 : 1 ≤ d := hd
  have hn : -12 ≤ n := by omega
  have hmem : ∀ x : ℚ, x ∈ ({1, -1, 2, -2, 3, -3, 4, -4, 6, -6, 12, -12} : Finset ℚ) ↔
      x = 1 ∨ x = -1 ∨ x = 2 ∨ x = -2 ∨ x = 3 ∨ x = -3 ∨ x = 4 ∨ x = -4 ∨ x = 6 ∨ x = -6 ∨ x = 12 ∨ x = -12 := by
    intro x; simp
  rw [hmem]
  interval_cases n <;> interval_cases d <;> first | (norm_num at e; done) | norm_num

/-- Stitz-Zeager Exercise 3.3.4 (Rational Zeros Theorem): every rational zero of `x ^ 3 + 4 * x ^ 2 - 11 * x + 6` lies in the
book's list of candidates (numerators dividing `6`, denominators dividing `1`). -/
@[kb "stitzzeager2013" "Exercise 3.3.4, p. 292"]
theorem exer_3_3_4_rational (q : ℚ)
    (hq : q ^ 3 + 4 * q ^ 2 - 11 * q + 6 = 0) :
    q ∈ ({1, -1, 2, -2, 3, -3, 6, -6} : Finset ℚ) := by
  obtain ⟨n, d, hd, hcop, rfl⟩ : ∃ n d : ℤ, 0 < d ∧ IsCoprime n d ∧ q = n / d :=
    ⟨q.num, q.den, by exact_mod_cast q.den_pos, Rat.isCoprime_num_den q, by simp [Rat.num_div_den]⟩
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have e : n ^ 3 + 4 * n ^ 2 * d - 11 * n * d ^ 2 + 6 * d ^ 3 = 0 := by
    have : ((n ^ 3 + 4 * n ^ 2 * d - 11 * n * d ^ 2 + 6 * d ^ 3 : ℤ) : ℚ) = 0 := by
      push_cast
      field_simp at hq
      linarith
    exact_mod_cast this
  have h1 : d ∣ 1 * n ^ 3 :=
    ⟨-(6 * d ^ 2 - 11 * n * d + 4 * n ^ 2), by linear_combination e⟩
  have h2 : n ∣ 6 * d ^ 3 :=
    ⟨-(-11 * d ^ 2 + 4 * n * d + n ^ 2), by linear_combination e⟩
  have h1' : d ∣ 1 := (hcop.symm.pow_right (n := 3)).dvd_of_dvd_mul_right h1
  have h2' : n ∣ 6 := (hcop.pow_right (n := 3)).dvd_of_dvd_mul_right h2
  have hd2 : d ≤ 1 := Int.le_of_dvd (by norm_num) h1'
  have hn3 : n ≤ 6 := Int.le_of_dvd (by norm_num) (by simpa using h2')
  have hn3' : -n ≤ 6 := Int.le_of_dvd (by norm_num) (by simpa using (neg_dvd).2 h2')
  have hd1 : 1 ≤ d := hd
  have hn : -6 ≤ n := by omega
  have hmem : ∀ x : ℚ, x ∈ ({1, -1, 2, -2, 3, -3, 6, -6} : Finset ℚ) ↔
      x = 1 ∨ x = -1 ∨ x = 2 ∨ x = -2 ∨ x = 3 ∨ x = -3 ∨ x = 6 ∨ x = -6 := by
    intro x; simp
  rw [hmem]
  interval_cases n <;> interval_cases d <;> first | (norm_num at e; done) | norm_num

/-- Stitz-Zeager Exercise 3.3.5 (Rational Zeros Theorem): every rational zero of `x ^ 3 - 7 * x ^ 2 + x - 7` lies in the
book's list of candidates (numerators dividing `7`, denominators dividing `1`). -/
@[kb "stitzzeager2013" "Exercise 3.3.5, p. 292"]
theorem exer_3_3_5_rational (q : ℚ)
    (hq : q ^ 3 - 7 * q ^ 2 + q - 7 = 0) :
    q ∈ ({1, -1, 7, -7} : Finset ℚ) := by
  obtain ⟨n, d, hd, hcop, rfl⟩ : ∃ n d : ℤ, 0 < d ∧ IsCoprime n d ∧ q = n / d :=
    ⟨q.num, q.den, by exact_mod_cast q.den_pos, Rat.isCoprime_num_den q, by simp [Rat.num_div_den]⟩
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have e : n ^ 3 - 7 * n ^ 2 * d + n * d ^ 2 - 7 * d ^ 3 = 0 := by
    have : ((n ^ 3 - 7 * n ^ 2 * d + n * d ^ 2 - 7 * d ^ 3 : ℤ) : ℚ) = 0 := by
      push_cast
      field_simp at hq
      linarith
    exact_mod_cast this
  have h1 : d ∣ 1 * n ^ 3 :=
    ⟨-(-7 * d ^ 2 + n * d - 7 * n ^ 2), by linear_combination e⟩
  have h2 : n ∣ 7 * d ^ 3 :=
    ⟨d ^ 2 - 7 * n * d + n ^ 2, by linear_combination -e⟩
  have h1' : d ∣ 1 := (hcop.symm.pow_right (n := 3)).dvd_of_dvd_mul_right h1
  have h2' : n ∣ 7 := (hcop.pow_right (n := 3)).dvd_of_dvd_mul_right h2
  have hd2 : d ≤ 1 := Int.le_of_dvd (by norm_num) h1'
  have hn3 : n ≤ 7 := Int.le_of_dvd (by norm_num) (by simpa using h2')
  have hn3' : -n ≤ 7 := Int.le_of_dvd (by norm_num) (by simpa using (neg_dvd).2 h2')
  have hd1 : 1 ≤ d := hd
  have hn : -7 ≤ n := by omega
  have hmem : ∀ x : ℚ, x ∈ ({1, -1, 7, -7} : Finset ℚ) ↔
      x = 1 ∨ x = -1 ∨ x = 7 ∨ x = -7 := by
    intro x; simp
  rw [hmem]
  interval_cases n <;> interval_cases d <;> first | (norm_num at e; done) | norm_num

/-- Stitz-Zeager Exercise 3.3.6 (Rational Zeros Theorem): every rational zero of `-2 * x ^ 3 + 19 * x ^ 2 - 49 * x + 20` lies in the
book's list of candidates (numerators dividing `20`, denominators dividing `2`). -/
@[kb "stitzzeager2013" "Exercise 3.3.6, p. 292"]
theorem exer_3_3_6_rational (q : ℚ)
    (hq : -2 * q ^ 3 + 19 * q ^ 2 - 49 * q + 20 = 0) :
    q ∈ ({1 / 2, -1 / 2, 1, -1, 2, -2, 5 / 2, -5 / 2, 4, -4, 5, -5, 10, -10, 20, -20} : Finset ℚ) := by
  obtain ⟨n, d, hd, hcop, rfl⟩ : ∃ n d : ℤ, 0 < d ∧ IsCoprime n d ∧ q = n / d :=
    ⟨q.num, q.den, by exact_mod_cast q.den_pos, Rat.isCoprime_num_den q, by simp [Rat.num_div_den]⟩
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have e : 2 * n ^ 3 - 19 * n ^ 2 * d + 49 * n * d ^ 2 - 20 * d ^ 3 = 0 := by
    have : ((2 * n ^ 3 - 19 * n ^ 2 * d + 49 * n * d ^ 2 - 20 * d ^ 3 : ℤ) : ℚ) = 0 := by
      push_cast
      field_simp at hq
      linarith
    exact_mod_cast this
  have h1 : d ∣ 2 * n ^ 3 :=
    ⟨-(-20 * d ^ 2 + 49 * n * d - 19 * n ^ 2), by linear_combination e⟩
  have h2 : n ∣ 20 * d ^ 3 :=
    ⟨49 * d ^ 2 - 19 * n * d + 2 * n ^ 2, by linear_combination -e⟩
  have h1' : d ∣ 2 := (hcop.symm.pow_right (n := 3)).dvd_of_dvd_mul_right h1
  have h2' : n ∣ 20 := (hcop.pow_right (n := 3)).dvd_of_dvd_mul_right h2
  have hd2 : d ≤ 2 := Int.le_of_dvd (by norm_num) h1'
  have hn3 : n ≤ 20 := Int.le_of_dvd (by norm_num) (by simpa using h2')
  have hn3' : -n ≤ 20 := Int.le_of_dvd (by norm_num) (by simpa using (neg_dvd).2 h2')
  have hd1 : 1 ≤ d := hd
  have hn : -20 ≤ n := by omega
  have hmem : ∀ x : ℚ, x ∈ ({1 / 2, -1 / 2, 1, -1, 2, -2, 5 / 2, -5 / 2, 4, -4, 5, -5, 10, -10, 20, -20} : Finset ℚ) ↔
      x = 1 / 2 ∨ x = -1 / 2 ∨ x = 1 ∨ x = -1 ∨ x = 2 ∨ x = -2 ∨ x = 5 / 2 ∨ x = -5 / 2 ∨ x = 4 ∨ x = -4 ∨ x = 5 ∨ x = -5 ∨ x = 10 ∨ x = -10 ∨ x = 20 ∨ x = -20 := by
    intro x; simp
  rw [hmem]
  interval_cases n <;> interval_cases d <;> first | (norm_num at e; done) | norm_num

/-- Stitz-Zeager Exercise 3.3.7 (Rational Zeros Theorem): every rational zero of `-17 * x ^ 3 + 5 * x ^ 2 + 34 * x - 10` lies in the
book's list of candidates (numerators dividing `10`, denominators dividing `17`). -/
@[kb "stitzzeager2013" "Exercise 3.3.7, p. 292"]
theorem exer_3_3_7_rational (q : ℚ)
    (hq : -17 * q ^ 3 + 5 * q ^ 2 + 34 * q - 10 = 0) :
    q ∈ ({1 / 17, -1 / 17, 2 / 17, -2 / 17, 5 / 17, -5 / 17, 10 / 17, -10 / 17, 1, -1, 2, -2, 5, -5, 10, -10} : Finset ℚ) := by
  obtain ⟨n, d, hd, hcop, rfl⟩ : ∃ n d : ℤ, 0 < d ∧ IsCoprime n d ∧ q = n / d :=
    ⟨q.num, q.den, by exact_mod_cast q.den_pos, Rat.isCoprime_num_den q, by simp [Rat.num_div_den]⟩
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have e : 17 * n ^ 3 - 5 * n ^ 2 * d - 34 * n * d ^ 2 + 10 * d ^ 3 = 0 := by
    have : ((17 * n ^ 3 - 5 * n ^ 2 * d - 34 * n * d ^ 2 + 10 * d ^ 3 : ℤ) : ℚ) = 0 := by
      push_cast
      field_simp at hq
      linarith
    exact_mod_cast this
  have h1 : d ∣ 17 * n ^ 3 :=
    ⟨-(10 * d ^ 2 - 34 * n * d - 5 * n ^ 2), by linear_combination e⟩
  have h2 : n ∣ 10 * d ^ 3 :=
    ⟨-(-34 * d ^ 2 - 5 * n * d + 17 * n ^ 2), by linear_combination e⟩
  have h1' : d ∣ 17 := (hcop.symm.pow_right (n := 3)).dvd_of_dvd_mul_right h1
  have h2' : n ∣ 10 := (hcop.pow_right (n := 3)).dvd_of_dvd_mul_right h2
  have hd2 : d ≤ 17 := Int.le_of_dvd (by norm_num) h1'
  have hn3 : n ≤ 10 := Int.le_of_dvd (by norm_num) (by simpa using h2')
  have hn3' : -n ≤ 10 := Int.le_of_dvd (by norm_num) (by simpa using (neg_dvd).2 h2')
  have hd1 : 1 ≤ d := hd
  have hn : -10 ≤ n := by omega
  have hmem : ∀ x : ℚ, x ∈ ({1 / 17, -1 / 17, 2 / 17, -2 / 17, 5 / 17, -5 / 17, 10 / 17, -10 / 17, 1, -1, 2, -2, 5, -5, 10, -10} : Finset ℚ) ↔
      x = 1 / 17 ∨ x = -1 / 17 ∨ x = 2 / 17 ∨ x = -2 / 17 ∨ x = 5 / 17 ∨ x = -5 / 17 ∨ x = 10 / 17 ∨ x = -10 / 17 ∨ x = 1 ∨ x = -1 ∨ x = 2 ∨ x = -2 ∨ x = 5 ∨ x = -5 ∨ x = 10 ∨ x = -10 := by
    intro x; simp
  rw [hmem]
  interval_cases n <;> interval_cases d <;> first | (norm_num at e; done) | norm_num

/-- Stitz-Zeager Exercise 3.3.8 (Rational Zeros Theorem): every rational zero of `36 * x ^ 4 - 12 * x ^ 3 - 11 * x ^ 2 + 2 * x + 1` lies in the
book's list of candidates (numerators dividing `1`, denominators dividing `36`). -/
@[kb "stitzzeager2013" "Exercise 3.3.8, p. 292"]
theorem exer_3_3_8_rational (q : ℚ)
    (hq : 36 * q ^ 4 - 12 * q ^ 3 - 11 * q ^ 2 + 2 * q + 1 = 0) :
    q ∈ ({1 / 36, -1 / 36, 1 / 18, -1 / 18, 1 / 12, -1 / 12, 1 / 9, -1 / 9, 1 / 6, -1 / 6, 1 / 4, -1 / 4, 1 / 3, -1 / 3, 1 / 2, -1 / 2, 1, -1} : Finset ℚ) := by
  obtain ⟨n, d, hd, hcop, rfl⟩ : ∃ n d : ℤ, 0 < d ∧ IsCoprime n d ∧ q = n / d :=
    ⟨q.num, q.den, by exact_mod_cast q.den_pos, Rat.isCoprime_num_den q, by simp [Rat.num_div_den]⟩
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have e : 36 * n ^ 4 - 12 * n ^ 3 * d - 11 * n ^ 2 * d ^ 2 + 2 * n * d ^ 3 + d ^ 4 = 0 := by
    have : ((36 * n ^ 4 - 12 * n ^ 3 * d - 11 * n ^ 2 * d ^ 2 + 2 * n * d ^ 3 + d ^ 4 : ℤ) : ℚ) = 0 := by
      push_cast
      field_simp at hq
      linarith
    exact_mod_cast this
  have h1 : d ∣ 36 * n ^ 4 :=
    ⟨-(d ^ 3 + 2 * n * d ^ 2 - 11 * n ^ 2 * d - 12 * n ^ 3), by linear_combination e⟩
  have h2 : n ∣ 1 * d ^ 4 :=
    ⟨-(2 * d ^ 3 - 11 * n * d ^ 2 - 12 * n ^ 2 * d + 36 * n ^ 3), by linear_combination e⟩
  have h1' : d ∣ 36 := (hcop.symm.pow_right (n := 4)).dvd_of_dvd_mul_right h1
  have h2' : n ∣ 1 := (hcop.pow_right (n := 4)).dvd_of_dvd_mul_right h2
  have hd2 : d ≤ 36 := Int.le_of_dvd (by norm_num) h1'
  have hn3 : n ≤ 1 := Int.le_of_dvd (by norm_num) (by simpa using h2')
  have hn3' : -n ≤ 1 := Int.le_of_dvd (by norm_num) (by simpa using (neg_dvd).2 h2')
  have hd1 : 1 ≤ d := hd
  have hn : -1 ≤ n := by omega
  have hmem : ∀ x : ℚ, x ∈ ({1 / 36, -1 / 36, 1 / 18, -1 / 18, 1 / 12, -1 / 12, 1 / 9, -1 / 9, 1 / 6, -1 / 6, 1 / 4, -1 / 4, 1 / 3, -1 / 3, 1 / 2, -1 / 2, 1, -1} : Finset ℚ) ↔
      x = 1 / 36 ∨ x = -1 / 36 ∨ x = 1 / 18 ∨ x = -1 / 18 ∨ x = 1 / 12 ∨ x = -1 / 12 ∨ x = 1 / 9 ∨ x = -1 / 9 ∨ x = 1 / 6 ∨ x = -1 / 6 ∨ x = 1 / 4 ∨ x = -1 / 4 ∨ x = 1 / 3 ∨ x = -1 / 3 ∨ x = 1 / 2 ∨ x = -1 / 2 ∨ x = 1 ∨ x = -1 := by
    intro x; simp
  rw [hmem]
  interval_cases n <;> interval_cases d <;> first | (norm_num at e; done) | norm_num

/-- Stitz-Zeager Exercise 3.3.9 (Rational Zeros Theorem): every rational zero of `3 * x ^ 3 + 3 * x ^ 2 - 11 * x - 10` lies in the
book's list of candidates (numerators dividing `10`, denominators dividing `3`). -/
@[kb "stitzzeager2013" "Exercise 3.3.9, p. 292"]
theorem exer_3_3_9_rational (q : ℚ)
    (hq : 3 * q ^ 3 + 3 * q ^ 2 - 11 * q - 10 = 0) :
    q ∈ ({1 / 3, -1 / 3, 2 / 3, -2 / 3, 5 / 3, -5 / 3, 10 / 3, -10 / 3, 1, -1, 2, -2, 5, -5, 10, -10} : Finset ℚ) := by
  obtain ⟨n, d, hd, hcop, rfl⟩ : ∃ n d : ℤ, 0 < d ∧ IsCoprime n d ∧ q = n / d :=
    ⟨q.num, q.den, by exact_mod_cast q.den_pos, Rat.isCoprime_num_den q, by simp [Rat.num_div_den]⟩
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have e : 3 * n ^ 3 + 3 * n ^ 2 * d - 11 * n * d ^ 2 - 10 * d ^ 3 = 0 := by
    have : ((3 * n ^ 3 + 3 * n ^ 2 * d - 11 * n * d ^ 2 - 10 * d ^ 3 : ℤ) : ℚ) = 0 := by
      push_cast
      field_simp at hq
      linarith
    exact_mod_cast this
  have h1 : d ∣ 3 * n ^ 3 :=
    ⟨-(-10 * d ^ 2 - 11 * n * d + 3 * n ^ 2), by linear_combination e⟩
  have h2 : n ∣ 10 * d ^ 3 :=
    ⟨-11 * d ^ 2 + 3 * n * d + 3 * n ^ 2, by linear_combination -e⟩
  have h1' : d ∣ 3 := (hcop.symm.pow_right (n := 3)).dvd_of_dvd_mul_right h1
  have h2' : n ∣ 10 := (hcop.pow_right (n := 3)).dvd_of_dvd_mul_right h2
  have hd2 : d ≤ 3 := Int.le_of_dvd (by norm_num) h1'
  have hn3 : n ≤ 10 := Int.le_of_dvd (by norm_num) (by simpa using h2')
  have hn3' : -n ≤ 10 := Int.le_of_dvd (by norm_num) (by simpa using (neg_dvd).2 h2')
  have hd1 : 1 ≤ d := hd
  have hn : -10 ≤ n := by omega
  have hmem : ∀ x : ℚ, x ∈ ({1 / 3, -1 / 3, 2 / 3, -2 / 3, 5 / 3, -5 / 3, 10 / 3, -10 / 3, 1, -1, 2, -2, 5, -5, 10, -10} : Finset ℚ) ↔
      x = 1 / 3 ∨ x = -1 / 3 ∨ x = 2 / 3 ∨ x = -2 / 3 ∨ x = 5 / 3 ∨ x = -5 / 3 ∨ x = 10 / 3 ∨ x = -10 / 3 ∨ x = 1 ∨ x = -1 ∨ x = 2 ∨ x = -2 ∨ x = 5 ∨ x = -5 ∨ x = 10 ∨ x = -10 := by
    intro x; simp
  rw [hmem]
  interval_cases n <;> interval_cases d <;> first | (norm_num at e; done) | norm_num

/-- Stitz-Zeager Exercise 3.3.10 (Rational Zeros Theorem): every rational zero of `2 * x ^ 4 + x ^ 3 - 7 * x ^ 2 - 3 * x + 3` lies in the
book's list of candidates (numerators dividing `3`, denominators dividing `2`). -/
@[kb "stitzzeager2013" "Exercise 3.3.10, p. 292"]
theorem exer_3_3_10_rational (q : ℚ)
    (hq : 2 * q ^ 4 + q ^ 3 - 7 * q ^ 2 - 3 * q + 3 = 0) :
    q ∈ ({1 / 2, -1 / 2, 1, -1, 3 / 2, -3 / 2, 3, -3} : Finset ℚ) := by
  obtain ⟨n, d, hd, hcop, rfl⟩ : ∃ n d : ℤ, 0 < d ∧ IsCoprime n d ∧ q = n / d :=
    ⟨q.num, q.den, by exact_mod_cast q.den_pos, Rat.isCoprime_num_den q, by simp [Rat.num_div_den]⟩
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have e : 2 * n ^ 4 + n ^ 3 * d - 7 * n ^ 2 * d ^ 2 - 3 * n * d ^ 3 + 3 * d ^ 4 = 0 := by
    have : ((2 * n ^ 4 + n ^ 3 * d - 7 * n ^ 2 * d ^ 2 - 3 * n * d ^ 3 + 3 * d ^ 4 : ℤ) : ℚ) = 0 := by
      push_cast
      field_simp at hq
      linarith
    exact_mod_cast this
  have h1 : d ∣ 2 * n ^ 4 :=
    ⟨-(3 * d ^ 3 - 3 * n * d ^ 2 - 7 * n ^ 2 * d + n ^ 3), by linear_combination e⟩
  have h2 : n ∣ 3 * d ^ 4 :=
    ⟨-(-3 * d ^ 3 - 7 * n * d ^ 2 + n ^ 2 * d + 2 * n ^ 3), by linear_combination e⟩
  have h1' : d ∣ 2 := (hcop.symm.pow_right (n := 4)).dvd_of_dvd_mul_right h1
  have h2' : n ∣ 3 := (hcop.pow_right (n := 4)).dvd_of_dvd_mul_right h2
  have hd2 : d ≤ 2 := Int.le_of_dvd (by norm_num) h1'
  have hn3 : n ≤ 3 := Int.le_of_dvd (by norm_num) (by simpa using h2')
  have hn3' : -n ≤ 3 := Int.le_of_dvd (by norm_num) (by simpa using (neg_dvd).2 h2')
  have hd1 : 1 ≤ d := hd
  have hn : -3 ≤ n := by omega
  have hmem : ∀ x : ℚ, x ∈ ({1 / 2, -1 / 2, 1, -1, 3 / 2, -3 / 2, 3, -3} : Finset ℚ) ↔
      x = 1 / 2 ∨ x = -1 / 2 ∨ x = 1 ∨ x = -1 ∨ x = 3 / 2 ∨ x = -3 / 2 ∨ x = 3 ∨ x = -3 := by
    intro x; simp
  rw [hmem]
  interval_cases n <;> interval_cases d <;> first | (norm_num at e; done) | norm_num
