import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic
import UndergradKB.Common.Attr
import UndergradKB.Probability.DiscreteDistributions

/-! # Probability: worked examples on statistical tests and normal approximations (wave 5)

Fisher's exact test (Example 5.6), the chi-squared statistic of a contingency table (Example 5.10),
the chi-squared test of a die (Example 7.8) and the exact binomial values behind the local and
global central limit approximations (Examples 9.1, 9.2). Binomial arithmetic is done exactly in
the kernel on natural-number numerators. -/

open Finset

namespace UndergradKB.Probability

/-- Kernel-cheap binomial coefficient `n.descFactorial k / k!`. -/
def testsCh (n k : ℕ) : ℕ := n.descFactorial k / k.factorial

lemma testsCh_eq (n k : ℕ) : (n.choose k : ℝ) = (testsCh n k : ℝ) := by
  rw [testsCh, Nat.choose_eq_descFactorial_div_factorial]

attribute [irreducible] testsCh

/-! ### Example 5.6: Fisher's exact test -/

/-- Numerator of the tail `P(s₁₁ ≥ 24)` of Example 5.6 (over the common denominator `C(50,28)`). -/
def fisherNum : ℕ := ∑ a ∈ Icc 24 28, testsCh 32 a * testsCh 18 (28 - a)

lemma fisherNum_lo : 3945 * testsCh 50 28 < 10 ^ 7 * fisherNum := by
  unfold fisherNum testsCh; decide +kernel

lemma fisherNum_hi : 10 ^ 7 * fisherNum < 3955 * testsCh 50 28 := by
  unfold fisherNum testsCh; decide +kernel

lemma testsCh_50_28_pos : 0 < testsCh 50 28 := by unfold testsCh; decide +kernel

lemma fisher_tail_eq : ∑ a ∈ Icc 24 28, hyperMass 32 18 28 a = (fisherNum : ℝ) / (testsCh 50 28 : ℝ) := by
  unfold hyperMass fisherNum
  rw [Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp only [Nat.cast_mul, testsCh_eq]

/-- Grinstead–Snell Example 5.6 (PR-199). Table 5.2 has marginals 28 women, 22 men, 32 Democrats,
18 Republicans (n = 50). Given the marginals, the number `a` of female Democrats has the hypergeometric
law `C(32,a) C(18,28-a) / C(50,28)` (`a = 0..28`, zero for `a < 10`), whose masses sum to 1; its mean is
`28 · 32/50 = 17.92`; and the tail probability of `a ≥ 24` (observed value 24, as extreme data 24..28)
lies in `(.0003945, .0003955)`, i.e. is `.000395` to six places. -/
@[kb "grinsteadsnell2006" "Example 5.6, p. 201"]
theorem fisher_exact_test_table_5_2 :
    (∀ a, hyperMass 32 18 28 a = (Nat.choose 32 a : ℝ) * Nat.choose 18 (28 - a) / Nat.choose 50 28) ∧
    (∀ a, 0 ≤ hyperMass 32 18 28 a) ∧
    (∀ a, a < 10 → hyperMass 32 18 28 a = 0) ∧
    ∑ a ∈ range 29, hyperMass 32 18 28 a = 1 ∧
    ∑ a ∈ range 29, (a : ℝ) * hyperMass 32 18 28 a = 17.92 ∧
    (0.0003945 : ℝ) < ∑ a ∈ Icc 24 28, hyperMass 32 18 28 a ∧
    ∑ a ∈ Icc 24 28, hyperMass 32 18 28 a < 0.0003955 := by
  have hD : (0 : ℝ) < testsCh 50 28 := by exact_mod_cast testsCh_50_28_pos
  refine ⟨fun a => by simp [hyperMass], fun a => by unfold hyperMass; positivity, ?_,
    sum_hyperMass 32 18 28 (by norm_num), ?_, ?_, ?_⟩
  · intro a ha
    unfold hyperMass
    have : Nat.choose 18 (28 - a) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [this]
  · have := hyperMass_mean 32 18 28 (by norm_num)
    rw [this]; norm_num
  · rw [fisher_tail_eq, lt_div_iff₀ hD]
    have : (3945 : ℝ) * testsCh 50 28 < 10 ^ 7 * fisherNum := by exact_mod_cast fisherNum_lo
    norm_num; linarith
  · rw [fisher_tail_eq, div_lt_iff₀ hD]
    have : (10 : ℝ) ^ 7 * fisherNum < 3955 * testsCh 50 28 := by exact_mod_cast fisherNum_hi
    norm_num; linarith

/-! ### Example 5.10: chi-squared statistic of Table 5.8 -/

/-- Table 5.8: rows A, B, C, below C; columns female, male. -/
def gradesObs : Fin 4 → Fin 2 → ℝ := ![![37, 56], ![63, 60], ![47, 43], ![5, 8]]

/-- Row totals of an observed table. -/
def tabRow (O : Fin 4 → Fin 2 → ℝ) (i : Fin 4) : ℝ := ∑ j, O i j

/-- Column totals of an observed table. -/
def tabCol (O : Fin 4 → Fin 2 → ℝ) (j : Fin 2) : ℝ := ∑ i, O i j

/-- Expected entries `(row total)(column total)/n`. -/
noncomputable def tabExp (O : Fin 4 → Fin 2 → ℝ) (i : Fin 4) (j : Fin 2) : ℝ :=
  tabRow O i * tabCol O j / ∑ i, tabRow O i

/-- The statistic `∑ (O - E)²/E`. -/
noncomputable def tabChiSq (O : Fin 4 → Fin 2 → ℝ) : ℝ :=
  ∑ i, ∑ j, (O i j - tabExp O i j) ^ 2 / tabExp O i j

/-- Grinstead–Snell Example 5.10 (PR-201). For Table 5.8 (319 students) the row totals are
93, 123, 90, 13, the column totals 152, 167, the grand total 319; the expected entries are
(row total)(column total)/319 (for instance 44.3 for female A, to one place); the chi-squared statistic
`∑ (O-E)²/E` lies in `[4.125, 4.135)`, i.e. is `4.13` as printed, and is below the 5 percent critical value
`7.815` (for `(4-1)(2-1) = 3` degrees of freedom, which is a remark only). -/
@[kb "grinsteadsnell2006" "Example 5.10, p. 224"]
theorem chi_squared_grades_gender :
    (∀ i, tabRow gradesObs i = ![93, 123, 90, 13] i) ∧
    (∀ j, tabCol gradesObs j = ![152, 167] j) ∧
    ∑ i, tabRow gradesObs i = 319 ∧
    (44.25 : ℝ) ≤ tabExp gradesObs 0 0 ∧ tabExp gradesObs 0 0 < 44.35 ∧
    (4.125 : ℝ) ≤ tabChiSq gradesObs ∧ tabChiSq gradesObs < 4.135 ∧
    tabChiSq gradesObs < 7.815 := by
  have hr : ∀ i, tabRow gradesObs i = ![93, 123, 90, 13] i := by
    intro i; fin_cases i <;> simp [tabRow, gradesObs, Fin.sum_univ_succ] <;> norm_num
  have hc : ∀ j, tabCol gradesObs j = ![152, 167] j := by
    intro j; fin_cases j <;> simp [tabCol, gradesObs, Fin.sum_univ_succ] <;> norm_num
  have ht : ∑ i, tabRow gradesObs i = 319 := by
    simp [hr, Fin.sum_univ_succ]; norm_num
  have hE : ∀ i j, tabExp gradesObs i j = ![93, 123, 90, 13] i * ![152, 167] j / 319 := by
    intro i j; rw [tabExp, ht, hr, hc]
  have h4 : (4.125 : ℝ) ≤ tabChiSq gradesObs ∧ tabChiSq gradesObs < 4.135 := by
    simp only [tabChiSq, hE, Fin.sum_univ_succ]
    simp [gradesObs]
    norm_num
  refine ⟨hr, hc, ht, ?_, ?_, h4.1, h4.2, by linarith [h4.2]⟩ <;>
    simp only [hE] <;> simp <;> norm_num

/-! ### Example 7.8: chi-squared test of a die -/

/-- Table 7.1: observed frequencies of the faces 1..6 in 60 rolls. -/
def dieObs : Fin 6 → ℝ := ![15, 8, 7, 5, 7, 18]

/-- Number of rolls showing face `i`. -/
def dieCount {n : ℕ} (ω : Fin n → Fin 6) (i : Fin 6) : ℝ := ∑ k, if ω k = i then 1 else 0

/-- The statistic `V = ∑ (o_i - n/6)²/(n/6)`. -/
noncomputable def dieV {n : ℕ} (ω : Fin n → Fin 6) : ℝ :=
  ∑ i, (dieCount ω i - (n : ℝ) / 6) ^ 2 / ((n : ℝ) / 6)

private lemma die_sum_sq (i : Fin 6) (n : ℕ) :
    ∑ ω : Fin n → Fin 6, (dieCount ω i - (n : ℝ) / 6) ^ 2 = 6 ^ n * ((n : ℝ) * 5 / 36) := by
  induction n with
  | zero => simp [dieCount]
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 6)).sum_comp, Fintype.sum_prod_type]
    have key : ∀ (a : Fin 6) (ω : Fin n → Fin 6),
        (dieCount ((Fin.consEquiv (fun _ : Fin (n + 1) => Fin 6)) (a, ω)) i - ((n + 1 : ℕ) : ℝ) / 6) ^ 2
        = (dieCount ω i - (n : ℝ) / 6) ^ 2 + 2 * (dieCount ω i - (n : ℝ) / 6) * ((if a = i then 1 else 0) - 1 / 6)
          + ((if a = i then 1 else 0) - 1 / 6) ^ 2 := by
      intro a ω
      have : (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 6)) (a, ω) = Fin.cons a ω := rfl
      rw [this, dieCount, Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, dieCount]
      push_cast; ring
    simp only [key]
    have s1 : ∑ a : Fin 6, ((if a = i then (1:ℝ) else 0) - 1 / 6) = 0 := by
      rw [Finset.sum_sub_distrib]; simp
    have s2 : ∑ a : Fin 6, ((if a = i then (1:ℝ) else 0) - 1 / 6) ^ 2 = 5 / 6 := by
      fin_cases i <;> simp [Fin.sum_univ_succ] <;> norm_num
    have hc : ∀ c : ℝ, ∑ ω : Fin n → Fin 6, ((dieCount ω i - (n : ℝ) / 6) ^ 2
        + 2 * (dieCount ω i - (n : ℝ) / 6) * c + c ^ 2)
        = 6 ^ n * ((n : ℝ) * 5 / 36) + 2 * (∑ ω : Fin n → Fin 6, (dieCount ω i - (n : ℝ) / 6)) * c
          + 6 ^ n * c ^ 2 := by
      intro c
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ih, ← Finset.sum_mul, ← Finset.mul_sum]
      simp [Fintype.card_pi]
    simp only [hc, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, s1, s2, mul_zero,
      zero_mul, add_zero]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring

/-- Grinstead–Snell Example 7.8 (PR-203). (a) For the 60 rolls of Table 7.1 (frequencies 15, 8, 7, 5, 7, 18)
the statistic `V = ∑ (o_i - 10)²/10` equals `136/10 = 13.6`. (b) For a fair die rolled `n ≥ 1` times (uniform
measure on `Fin n → Fin 6`, expectation as the average over the `6^n` equally likely outcomes), the expected
value of `V = ∑ (o_i - n/6)²/(n/6)` is exactly `5`. -/
@[kb "grinsteadsnell2006" "Example 7.8, p. 305"]
theorem chi_squared_die_test :
    ∑ i, (dieObs i - 10) ^ 2 / 10 = 136 / 10 ∧
    ∀ n : ℕ, 1 ≤ n →
      (∑ ω : Fin n → Fin 6, dieV ω) / (Fintype.card (Fin n → Fin 6) : ℝ) = 5 := by
  refine ⟨by simp [dieObs, Fin.sum_univ_succ]; norm_num, fun n hn => ?_⟩
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have : ∑ ω : Fin n → Fin 6, dieV ω = 6 * (6 ^ n * ((n : ℝ) * 5 / 36)) / ((n : ℝ) / 6) := by
    unfold dieV
    rw [Finset.sum_comm]
    simp only [← Finset.sum_div, die_sum_sq]
    simp
  rw [this]
  simp only [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  field_simp
  ring

/-! ### Examples 9.1 and 9.2: exact binomial values -/

lemma rlt {a b : ℕ} (h : a < b) : (a : ℝ) < b := Nat.cast_lt.2 h
lemma rle {a b : ℕ} (h : a ≤ b) : (a : ℝ) ≤ b := Nat.cast_le.2 h

/-- Fair-coin numerator `∑ C(100,k)`. -/
def fairNum (lo hi : ℕ) : ℕ := ∑ k ∈ Icc lo hi, testsCh 100 k

/-- Binomial mass `b(n, p, k)`. -/
noncomputable def clt_b (n : ℕ) (p : ℝ) (k : ℕ) : ℝ := (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)

lemma clt_b_half (k : ℕ) : clt_b 100 (1 / 2) k = (testsCh 100 k : ℝ) / 2 ^ 100 := by
  rw [clt_b, ← testsCh_eq]
  rcases le_or_gt k 100 with h | h
  · have e : (2 : ℝ) ^ 100 = 2 ^ k * 2 ^ (100 - k) := by rw [← pow_add]; congr 1; omega
    have h1 : (1 / 2 : ℝ) ^ k * 2 ^ k = 1 := by rw [← mul_pow]; norm_num
    have h2 : (1 / 2 : ℝ) ^ (100 - k) * 2 ^ (100 - k) = 1 := by rw [← mul_pow]; norm_num
    have e3 : (1 - 1 / 2 : ℝ) = 1 / 2 := by norm_num
    rw [e, e3, eq_div_iff (by positivity)]
    linear_combination ((Nat.choose 100 k : ℝ) * (1 / 2) ^ (100 - k) * 2 ^ (100 - k)) * h1
      + (Nat.choose 100 k : ℝ) * h2
  · simp [Nat.choose_eq_zero_of_lt h]

lemma fair_sum (lo hi : ℕ) :
    ∑ k ∈ Icc lo hi, clt_b 100 (1 / 2) k = (fairNum lo hi : ℝ) / 2 ^ 100 := by
  simp only [clt_b_half, fairNum, Nat.cast_sum, Finset.sum_div]

lemma fair_55a : 4845 * 2 ^ 100 < 10 ^ 5 * testsCh 100 55 := by unfold testsCh; decide +kernel
lemma fair_55b : 10 ^ 5 * testsCh 100 55 < 4855 * 2 ^ 100 := by unfold testsCh; decide +kernel
lemma fair_50a : 7955 * 2 ^ 100 < 10 ^ 5 * testsCh 100 50 := by unfold testsCh; decide +kernel
lemma fair_50b : 10 ^ 5 * testsCh 100 50 < 7965 * 2 ^ 100 := by unfold testsCh; decide +kernel
lemma six_a : 10925 * 6 ^ 36 < 10 ^ 5 * (testsCh 36 8 * 5 ^ 28) := by unfold testsCh; decide +kernel
lemma six_b : 10 ^ 5 * (testsCh 36 8 * 5 ^ 28) < 10935 * 6 ^ 36 := by unfold testsCh; decide +kernel
lemma six_c : 10 ^ 5 * (testsCh 36 8 * 5 ^ 28) < 11955 * 6 ^ 36 := by unfold testsCh; decide +kernel
lemma mid60_a : 964795 * 2 ^ 100 ≤ 10 ^ 6 * fairNum 40 60 := by unfold fairNum testsCh; decide +kernel
lemma mid60_b : 10 ^ 6 * fairNum 40 60 < 964805 * 2 ^ 100 := by unfold fairNum testsCh; decide +kernel
lemma mid65_a : 998205 * 2 ^ 100 ≤ 10 ^ 6 * fairNum 35 65 := by unfold fairNum testsCh; decide +kernel
lemma mid65_b : 10 ^ 6 * fairNum 35 65 < 998215 * 2 ^ 100 := by unfold fairNum testsCh; decide +kernel

set_option linter.constructorNameAsVariable false in
/-- Grinstead–Snell Example 9.1 (PR-204). Exact binomial values, to the printed precision: for a fair coin
`b(100,1/2,55)` rounds to `.0485` (lies in `(.04845, .04855)`) and `b(100,1/2,50)` to `.0796`
(`(.07955, .07965)`). The book's `b(36,1/6,8) = .1196` is a misprint: the true value rounds to `.1093`
(lies in `(.10925, .10935)`), and the book's `.1196` is false (the value is below `.11955`). -/
@[kb "grinsteadsnell2006" "Example 9.1, p. 337"]
theorem clt_local_exact_values :
    (0.04845 : ℝ) < clt_b 100 (1 / 2) 55 ∧ clt_b 100 (1 / 2) 55 < 0.04855 ∧
    (0.07955 : ℝ) < clt_b 100 (1 / 2) 50 ∧ clt_b 100 (1 / 2) 50 < 0.07965 ∧
    (0.10925 : ℝ) < clt_b 36 (1 / 6) 8 ∧ clt_b 36 (1 / 6) 8 < 0.10935 ∧
    clt_b 36 (1 / 6) 8 < 0.11955 := by
  have h2 : (0 : ℝ) < 2 ^ 100 := by positivity
  have h6 : (0 : ℝ) < 6 ^ 36 := by positivity
  have e2 : clt_b 36 (1 / 6) 8 = ((testsCh 36 8 : ℝ) * 5 ^ 28) / (6 ^ 36 : ℝ) := by
    rw [clt_b, testsCh_eq]
    have e3 : (1 - 1 / 6 : ℝ) = 5 / 6 := by norm_num
    rw [e3, div_pow, div_pow, one_pow]
    field_simp
  have a1 := rlt fair_55a
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at a1
  have a2 := rlt fair_55b
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at a2
  have a3 := rlt fair_50a
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at a3
  have a4 := rlt fair_50b
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at a4
  have s1 := rlt six_a
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at s1
  have s2 := rlt six_b
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at s2
  have s3 := rlt six_c
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at s3
  rw [clt_b_half, clt_b_half, e2]
  generalize (2 : ℝ) ^ 100 = X at *
  generalize (6 : ℝ) ^ 36 = Y at *
  generalize (5 : ℝ) ^ 28 = Z at *
  simp only [lt_div_iff₀ h2, div_lt_iff₀ h2, lt_div_iff₀ h6, div_lt_iff₀ h6]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

set_option linter.constructorNameAsVariable false in
/-- Grinstead–Snell Example 9.2 (PR-204). For a fair coin tossed 100 times, `P(40 ≤ S₁₀₀ ≤ 60)` lies in
`[.964795, .964805)` (`.96480` to five places) and `P(35 ≤ S₁₀₀ ≤ 65)` in `[.998205, .998215)`
(`.99821`). -/
@[kb "grinsteadsnell2006" "Example 9.2, p. 340"]
theorem clt_global_exact_values :
    (0.964795 : ℝ) ≤ ∑ k ∈ Icc 40 60, clt_b 100 (1 / 2) k ∧
    ∑ k ∈ Icc 40 60, clt_b 100 (1 / 2) k < 0.964805 ∧
    (0.998205 : ℝ) ≤ ∑ k ∈ Icc 35 65, clt_b 100 (1 / 2) k ∧
    ∑ k ∈ Icc 35 65, clt_b 100 (1 / 2) k < 0.998215 := by
  have h2 : (0 : ℝ) < 2 ^ 100 := by positivity
  rw [fair_sum, fair_sum]
  have a1 := rle mid60_a
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at a1
  have a2 := rlt mid60_b
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at a2
  have a3 := rle mid65_a
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at a3
  have a4 := rlt mid65_b
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at a4
  generalize (2 : ℝ) ^ 100 = X at *
  simp only [le_div_iff₀ h2, div_lt_iff₀ h2]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- Grinstead–Snell Example 9.1 (PR-204), local approximation. For `n = 100`, `p = 1/2`, `j = 55` we have
`x₅₅ = 1`, and the approximation `φ(1)/5 = e^{-1/2}/(5 √(2π))` lies in `(.04835, .04845)`, i.e. is `.0484`
to four places. -/
@[kb "grinsteadsnell2006" "Example 9.1, p. 337"]
theorem clt_local_approximation_value :
    (0.04835 : ℝ) < Real.exp (-(1 / 2)) / (5 * Real.sqrt (2 * Real.pi)) ∧
    Real.exp (-(1 / 2)) / (5 * Real.sqrt (2 * Real.pi)) < 0.04845 := by
  have he : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have e1 := Real.exp_one_gt_d9
  have e2 := Real.exp_one_lt_d9
  have h0 : 0 < Real.exp (1 / 2) := Real.exp_pos _
  have x1 : (1.6487 : ℝ) < Real.exp (1 / 2) := by nlinarith
  have x2 : Real.exp (1 / 2) < 1.6488 := by nlinarith
  have p1 := Real.pi_gt_d6
  have p2 := Real.pi_lt_d6
  have s1 : (2.5066 : ℝ) < Real.sqrt (2 * Real.pi) := by
    apply Real.lt_sqrt_of_sq_lt; nlinarith
  have s2 : Real.sqrt (2 * Real.pi) < 2.5067 := by
    rw [Real.sqrt_lt' (by norm_num)]; nlinarith
  have hs : 0 < Real.sqrt (2 * Real.pi) := by linarith
  have hq : Real.exp (-(1 / 2)) / (5 * Real.sqrt (2 * Real.pi))
      = 1 / (Real.exp (1 / 2) * (5 * Real.sqrt (2 * Real.pi))) := by
    rw [Real.exp_neg]; field_simp
  have hp1 : Real.exp (1 / 2) * Real.sqrt (2 * Real.pi) < 1.6488 * 2.5067 :=
    mul_lt_mul'' x2 s2 h0.le hs.le
  have hp2 : 1.6487 * 2.5066 < Real.exp (1 / 2) * Real.sqrt (2 * Real.pi) :=
    mul_lt_mul'' x1 s1 (by norm_num) (by norm_num)
  have hpos : 0 < Real.exp (1 / 2) * (5 * Real.sqrt (2 * Real.pi)) := by positivity
  rw [hq]
  constructor
  · rw [lt_div_iff₀ hpos]; nlinarith
  · rw [div_lt_iff₀ hpos]; nlinarith

end UndergradKB.Probability
