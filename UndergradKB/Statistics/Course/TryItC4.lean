import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Fin.VecNotation
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Discrete

/-!
# Try It exercises, chapter 4 (OpenStax *Introductory Statistics 2e*): discrete random variables

Probability tables, expected values and standard deviations, and the binomial, geometric,
hypergeometric and Poisson laws.  Exact rational answers where possible; two-sided bounds where the
book rounds or where `e^(-λ)` enters.  Exercises that only ask for a verbal identification (what is
`X`, what is a success, why is it binomial, ...) are not formalized.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal unitInterval

set_option maxRecDepth 100000

namespace UndergradKB.Statistics.Course.TryItC4

private lemma real_Iic (μ : Measure ℕ) [IsFiniteMeasure μ] (k : ℕ) :
    μ.real (Set.Iic k) = ∑ j ∈ range (k + 1), μ.real {j} := by
  have : (Set.Iic k : Set ℕ) = ↑(Finset.range (k + 1)) := by
    ext; simp
  rw [this, sum_measureReal_singleton]

private lemma real_Ioi (μ : Measure ℕ) [IsProbabilityMeasure μ] (k : ℕ) :
    μ.real (Set.Ioi k) = 1 - ∑ j ∈ range (k + 1), μ.real {j} := by
  rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, real_Iic]

private lemma hp0 {c : ℝ} (h0 : 0 < c) (h1 : c ≤ 1) :
    (⟨c, h0.le, h1⟩ : unitInterval) ≠ 0 := by
  intro h
  have := congrArg Subtype.val h
  simp at this
  linarith

/-- Bounds for `e^(-n)` from bounds for `e`. -/
private lemma exp_neg_nat_bounds (n : ℕ) (hn : n ≠ 0) :
    (1 / 2.7182818286 : ℝ) ^ n < Real.exp (-(n : ℝ)) ∧
      Real.exp (-(n : ℝ)) < (1 / 2.7182818283 : ℝ) ^ n := by
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.exp_one_lt_d9
  have e : Real.exp (-(n : ℝ)) = (1 / Real.exp 1) ^ n := by
    rw [Real.exp_neg, one_div, inv_pow, ← Real.exp_nat_mul, mul_one]
  rw [e]
  constructor
  · apply pow_lt_pow_left₀ _ (by positivity) hn
    exact one_div_lt_one_div_of_lt (by positivity) h2
  · apply pow_lt_pow_left₀ _ (by positivity) hn
    exact one_div_lt_one_div_of_lt (by norm_num) h1

/-! ### Sections 4.1 and 4.2: tables, expected value, standard deviation -/

/-- OpenStax Introductory Statistics 2e Try It 4.1. A sample of 50 patients rings the nurse 0 to 5
times in a shift, with relative frequencies 4, 8, 16, 14, 6, 2 out of 50: every `P(x)` lies in
`[0, 1]` and the column sums to 1 (the two reasons it is a probability distribution). -/
@[kb "openstaxintrostats2e" "Try It 4.1, p. 241"]
theorem tryit_4_1_nurse_calls_distribution :
    let p : Fin 6 → ℝ := ![4 / 50, 8 / 50, 16 / 50, 14 / 50, 6 / 50, 2 / 50]
    (∀ i, 0 ≤ p i ∧ p i ≤ 1) ∧ ∑ i, p i = 1 := by
  intro p
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> simp [p] <;> norm_num
  · simp [p, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Try It 4.2. Jeremiah attends 0, 1 or 2 practices a week with
probabilities 0.02, 0.08, 0.90: the table is a probability distribution (entries in `[0, 1]`, total 1). -/
@[kb "openstaxintrostats2e" "Try It 4.2, p. 242"]
theorem tryit_4_2_practices_attended_table :
    let p : Fin 3 → ℝ := ![0.02, 0.08, 0.90]
    (∀ i, 0 ≤ p i ∧ p i ≤ 1) ∧ ∑ i, p i = 1 := by
  intro p
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> simp [p] <;> norm_num
  · simp [p, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Try It 4.3. A customer orders 1, 2 or 3 bottles with
probabilities 0.6, 0.3, 0.1: the expected number of bottles is 1.5. -/
@[kb "openstaxintrostats2e" "Try It 4.3, p. 243"]
theorem tryit_4_3_bottles_expected_value :
    let x : Fin 3 → ℝ := ![1, 2, 3]
    let p : Fin 3 → ℝ := ![0.6, 0.3, 0.1]
    ∑ i, x i * p i = 1.5 := by
  intro x p
  simp [x, p, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Try It 4.4. For the nurse-call table of Try It 4.1 (values
0 to 5 with relative frequencies 4, 8, 16, 14, 6, 2 out of 50) the expected value is `2.32`. -/
@[kb "openstaxintrostats2e" "Try It 4.4, p. 244"]
theorem tryit_4_4_nurse_calls_expected_value :
    let x : Fin 6 → ℝ := ![0, 1, 2, 3, 4, 5]
    let p : Fin 6 → ℝ := ![4 / 50, 8 / 50, 16 / 50, 14 / 50, 6 / 50, 2 / 50]
    ∑ i, x i * p i = 2.32 := by
  intro x p
  simp [x, p, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Try It 4.5. Guess the suit of four cards drawn with
replacement (probability `(1/4)^4 = 1/256` of being right four times); a win pays $256 profit and a
loss costs the $1 stake: the expected profit is `1/256` dollars per play (a small positive gain). -/
@[kb "openstaxintrostats2e" "Try It 4.5, p. 245"]
theorem tryit_4_5_suit_guessing_expected_profit :
    256 * ((1 : ℝ) / 4) ^ 4 + (-1) * (1 - ((1 : ℝ) / 4) ^ 4) = 1 / 256 := by
  norm_num

/-- OpenStax Introductory Statistics 2e Try It 4.6. A spinner with probabilities 2/5 (red, pay $10),
2/5 (blue, nothing) and 1/5 (green, win $10): the probabilities sum to 1, the red entry of the
`x P(x)` column is `-20/5`, and the expected profit is `-2` dollars per game. -/
@[kb "openstaxintrostats2e" "Try It 4.6, p. 246"]
theorem tryit_4_6_spinner_expected_value :
    let x : Fin 3 → ℝ := ![-10, 0, 10]
    let p : Fin 3 → ℝ := ![2 / 5, 2 / 5, 1 / 5]
    ∑ i, p i = 1 ∧ x 0 * p 0 = -20 / 5 ∧ ∑ i, x i * p i = -2 := by
  intro x p
  refine ⟨?_, ?_⟩ <;> simp [x, p, Fin.sum_univ_succ] <;> norm_num

/-- OpenStax Introductory Statistics 2e Try It 4.7. One card from each of two stacks numbered 1 to 8;
`X` is the number of odd cards, so `P(0), P(1), P(2) = 1/4, 1/2, 1/4`. The mean is 1, the variance
`1/2` and the standard deviation lies in `(0.7071, 0.7072)`. -/
@[kb "openstaxintrostats2e" "Try It 4.7, p. 248"]
theorem tryit_4_7_two_stacks_odd_cards :
    let x : Fin 3 → ℝ := ![0, 1, 2]
    let p : Fin 3 → ℝ := ![1 / 4, 1 / 2, 1 / 4]
    ∑ i, p i = 1 ∧ ∑ i, x i * p i = 1 ∧ ∑ i, (x i - 1) ^ 2 * p i = 1 / 2 ∧
      (0.7071 < Real.sqrt (∑ i, (x i - 1) ^ 2 * p i) ∧
        Real.sqrt (∑ i, (x i - 1) ^ 2 * p i) < 0.7072) := by
  intro x p
  have h : ∑ i, (x i - 1) ^ 2 * p i = 1 / 2 := by
    simp [x, p, Fin.sum_univ_succ]; norm_num
  refine ⟨by simp [p, Fin.sum_univ_succ]; norm_num, by simp [x, p, Fin.sum_univ_succ]; norm_num,
    h, ?_, ?_⟩
  · rw [h, Real.lt_sqrt (by norm_num)]; norm_num
  · rw [h, Real.sqrt_lt' (by norm_num)]; norm_num

/-- OpenStax Introductory Statistics 2e Try It 4.8. A bet on a moderate earthquake in Japan wins $100
with probability 0.0108 and loses $10 otherwise: the mean profit is `-8.812` dollars, the variance
lies in `(129.268, 129.269)` and the standard deviation in `(11.3696, 11.3697)`. -/
@[kb "openstaxintrostats2e" "Try It 4.8, p. 248"]
theorem tryit_4_8_japan_earthquake_bet :
    let x : Fin 2 → ℝ := ![100, -10]
    let p : Fin 2 → ℝ := ![0.0108, 1 - 0.0108]
    ∑ i, x i * p i = -8.812 ∧
      (129.268 < ∑ i, (x i - (-8.812)) ^ 2 * p i ∧ ∑ i, (x i - (-8.812)) ^ 2 * p i < 129.269) ∧
      (11.3696 < Real.sqrt (∑ i, (x i - (-8.812)) ^ 2 * p i) ∧
        Real.sqrt (∑ i, (x i - (-8.812)) ^ 2 * p i) < 11.3697) := by
  intro x p
  have hv : ∑ i, (x i - (-8.812)) ^ 2 * p i = (100 + 8.812) ^ 2 * 0.0108 +
      (-10 + 8.812) ^ 2 * (1 - 0.0108) := by
    simp [x, p, Fin.sum_univ_succ]
  refine ⟨by simp [x, p, Fin.sum_univ_succ]; norm_num, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hv]; norm_num
  · rw [hv]; norm_num
  · rw [hv, Real.lt_sqrt (by norm_num)]; norm_num
  · rw [hv, Real.sqrt_lt' (by norm_num)]; norm_num

/-! ### Section 4.3: binomial -/

/-- OpenStax Introductory Statistics 2e Try It 4.10. A dolphin catches a fish with probability 0.35
per attempt; in 20 attempts `X ~ B(20, 0.35)` and `P(X = 12)` lies in `(0.01356, 0.01357)`. -/
@[kb "openstaxintrostats2e" "Try It 4.10, p. 249"]
theorem tryit_4_10_dolphin_twelve_catches :
    let p : unitInterval := ⟨0.35, by norm_num⟩
    0.01356 < Bin(20, p).real {12} ∧ Bin(20, p).real {12} < 0.01357 := by
  intro p
  rw [binomial_real_singleton]
  simp [p, Nat.choose]
  constructor <;> norm_num

/-- OpenStax Introductory Statistics 2e Try It 4.11. A fair die is rolled ten times and `X` counts
the ones, `X ~ B(10, 1/6)`: `P(X > 3)` lies in `(0.0697, 0.0698)`. -/
@[kb "openstaxintrostats2e" "Try It 4.11, p. 250"]
theorem tryit_4_11_more_than_three_ones :
    let p : unitInterval := ⟨1 / 6, by norm_num⟩
    0.0697 < Bin(10, p).real (Set.Ioi 3) ∧ Bin(10, p).real (Set.Ioi 3) < 0.0698 := by
  intro p
  rw [real_Ioi]
  simp [Finset.sum_range_succ, binomial_real_singleton, p, Nat.choose]
  constructor <;> norm_num

/-- OpenStax Introductory Statistics 2e Try It 4.13. About 32% of students volunteer; among 30
random students `X ~ B(30, 0.32)` and `P(X ≤ 14)` lies in `(0.9695, 0.9696)`. -/
@[kb "openstaxintrostats2e" "Try It 4.13, p. 252"]
theorem tryit_4_13_volunteers_at_most_fourteen :
    let p : unitInterval := ⟨0.32, by norm_num⟩
    0.9695 < Bin(30, p).real (Set.Iic 14) ∧ Bin(30, p).real (Set.Iic 14) < 0.9696 := by
  intro p
  rw [real_Iic]
  simp only [binomial_real_singleton, Finset.sum_range_succ, Finset.sum_range_zero, p]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

private lemma choose_real (n k : ℕ) :
    (Nat.choose n k : ℝ) = (n.descFactorial k : ℝ) / (k.factorial : ℝ) := by
  rw [Nat.choose_eq_descFactorial_div_factorial, Nat.cast_div (Nat.factorial_dvd_descFactorial n k)
    (by positivity)]

/-- OpenStax Introductory Statistics 2e Try It 4.14. 60% of adults prefer saving; among 50 sampled
adults `X ~ B(50, 0.6)`. `P(X = 25)` lies in `(0.04046, 0.04047)`, `P(X ≤ 20)` in
`(0.00336, 0.003361)`, `P(X > 30)` in `(0.4464, 0.4465)`; the mean is `np = 30`, the variance
`npq = 12` and the standard deviation lies in `(3.464, 3.465)`. -/
@[kb "openstaxintrostats2e" "Try It 4.14, p. 253"]
theorem tryit_4_14_saving_over_spending :
    let p : unitInterval := ⟨0.6, by norm_num⟩
    (0.04046 < Bin(50, p).real {25} ∧ Bin(50, p).real {25} < 0.04047) ∧
      (0.00336 < Bin(50, p).real (Set.Iic 20) ∧ Bin(50, p).real (Set.Iic 20) < 0.003361) ∧
      (0.4464 < Bin(50, p).real (Set.Ioi 30) ∧ Bin(50, p).real (Set.Ioi 30) < 0.4465) ∧
      ∫ x, x ∂Bin(ℝ, 50, p) = 30 ∧ variance (id : ℝ → ℝ) Bin(ℝ, 50, p) = 12 ∧
      (3.464 < Real.sqrt (variance (id : ℝ → ℝ) Bin(ℝ, 50, p)) ∧
        Real.sqrt (variance (id : ℝ → ℝ) Bin(ℝ, 50, p)) < 3.465) := by
  intro p
  have hv : variance (id : ℝ → ℝ) Bin(ℝ, 50, p) = 12 := by
    rw [UndergradKB.Statistics.variance_binomial]; simp [p] <;> norm_num
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, hv, ?_, ?_⟩
  · rw [binomial_real_singleton]
    simp only [p, choose_real]
    norm_num [Nat.descFactorial, Nat.factorial]
  · rw [binomial_real_singleton]
    simp only [p, choose_real]
    norm_num [Nat.descFactorial, Nat.factorial]
  · rw [real_Iic]
    simp only [binomial_real_singleton, Finset.sum_range_succ, Finset.sum_range_zero, p, choose_real]
    norm_num [Nat.descFactorial, Nat.factorial]
  · rw [real_Iic]
    simp only [binomial_real_singleton, Finset.sum_range_succ, Finset.sum_range_zero, p, choose_real]
    norm_num [Nat.descFactorial, Nat.factorial]
  · rw [real_Ioi]
    simp only [binomial_real_singleton, Finset.sum_range_succ, Finset.sum_range_zero, p, choose_real]
    norm_num [Nat.descFactorial, Nat.factorial]
  · rw [real_Ioi]
    simp only [binomial_real_singleton, Finset.sum_range_succ, Finset.sum_range_zero, p, choose_real]
    norm_num [Nat.descFactorial, Nat.factorial]
  · have : ∫ x, x ∂Bin(ℝ, 50, p) = p * 50 :=
      integral_of_hasLaw_binomial (X := id) (P := Bin(ℝ, 50, p)) HasLaw.id
    rw [this]; simp [p]; norm_num
  · rw [hv, Real.lt_sqrt (by norm_num)]; norm_num
  · rw [hv, Real.sqrt_lt' (by norm_num)]; norm_num

/-- OpenStax Introductory Statistics 2e Try It 4.15. A player scores on 61.3% of shots; among 80
shots `X ~ B(80, 0.613)`. The mean is `49.04`, the variance `18.97848`, the standard deviation lies in
`(4.356, 4.357)`; `P(X = 60)` lies in `(0.00355, 0.003551)` and `P(X > 50)` in `(0.3718, 0.3719)`. -/
@[kb "openstaxintrostats2e" "Try It 4.15, p. 253"]
theorem tryit_4_15_field_goal_shots :
    let p : unitInterval := ⟨0.613, by norm_num⟩
    ∫ x, x ∂Bin(ℝ, 80, p) = 49.04 ∧ variance (id : ℝ → ℝ) Bin(ℝ, 80, p) = 18.97848 ∧
      (4.356 < Real.sqrt (variance (id : ℝ → ℝ) Bin(ℝ, 80, p)) ∧
        Real.sqrt (variance (id : ℝ → ℝ) Bin(ℝ, 80, p)) < 4.357) ∧
      (0.00355 < Bin(80, p).real {60} ∧ Bin(80, p).real {60} < 0.003551) ∧
      (0.3718 < Bin(80, p).real (Set.Ioi 50) ∧ Bin(80, p).real (Set.Ioi 50) < 0.3719) := by
  intro p
  have hv : variance (id : ℝ → ℝ) Bin(ℝ, 80, p) = 18.97848 := by
    rw [UndergradKB.Statistics.variance_binomial]; simp [p] <;> norm_num
  refine ⟨?_, hv, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have : ∫ x, x ∂Bin(ℝ, 80, p) = p * 80 :=
      integral_of_hasLaw_binomial (X := id) (P := Bin(ℝ, 80, p)) HasLaw.id
    rw [this]; simp [p]; norm_num
  · rw [hv, Real.lt_sqrt (by norm_num)]; norm_num
  · rw [hv, Real.sqrt_lt' (by norm_num)]; norm_num
  · rw [binomial_real_singleton]
    simp only [p, choose_real]
    norm_num [Nat.descFactorial, Nat.factorial]
  · rw [binomial_real_singleton]
    simp only [p, choose_real]
    norm_num [Nat.descFactorial, Nat.factorial]
  · rw [real_Ioi]
    simp only [binomial_real_singleton, Finset.sum_range_succ, Finset.sum_range_zero, p, choose_real]
    norm_num [Nat.descFactorial, Nat.factorial]
  · rw [real_Ioi]
    simp only [binomial_real_singleton, Finset.sum_range_succ, Finset.sum_range_zero, p, choose_real]
    norm_num [Nat.descFactorial, Nat.factorial]

/-! ### Section 4.4: geometric (Mathlib counts the failures before the first success) -/

/-- OpenStax Introductory Statistics 2e Try It 4.17. A dart hits the center with probability 0.17;
needing eight throws means seven misses first, with probability `(0.83)^7 (0.17)`, which lies in
`(0.0461, 0.0462)`. -/
@[kb "openstaxintrostats2e" "Try It 4.17, p. 255"]
theorem tryit_4_17_darts_eight_throws :
    let p : unitInterval := ⟨0.17, by norm_num⟩
    (geometricMeasure p).real {7} = 0.83 ^ 7 * 0.17 ∧
      (0.0461 < (geometricMeasure p).real {7} ∧ (geometricMeasure p).real {7} < 0.0462) := by
  intro p
  have h : (geometricMeasure p).real {7} = 0.83 ^ 7 * 0.17 := by
    rw [geometricMeasure_real_singleton (hp0 (by norm_num) (by norm_num))]
    simp only [p]; norm_num
  exact ⟨h, by rw [h]; constructor <;> norm_num⟩

/-- OpenStax Introductory Statistics 2e Try It 4.18. 15% of exams score below a C and exams are
examined until one does; needing at least ten exams means at least nine failures first, with
probability `(0.85)^9`, which lies in `(0.2316, 0.2317)`. -/
@[kb "openstaxintrostats2e" "Try It 4.18, p. 256"]
theorem tryit_4_18_at_least_ten_exams :
    let p : unitInterval := ⟨0.15, by norm_num⟩
    (geometricMeasure p).real (Set.Ici 9) = 0.85 ^ 9 ∧
      (0.2316 < (geometricMeasure p).real (Set.Ici 9) ∧
        (geometricMeasure p).real (Set.Ici 9) < 0.2317) := by
  intro p
  have hp := hp0 (c := 0.15) (by norm_num) (by norm_num)
  have h : (geometricMeasure p).real (Set.Ici 9) = 0.85 ^ 9 := by
    have e : (Set.Ici 9 : Set ℕ) = (Set.Iic 8)ᶜ := by
      ext n; simp only [Set.mem_Ici, Set.mem_compl_iff, Set.mem_Iic, not_le]; omega
    rw [e, probReal_compl_eq_one_sub measurableSet_Iic, real_Iic]
    simp [Finset.sum_range_succ, geometricMeasure_real_singleton hp, p]
    norm_num
  exact ⟨h, by rw [h]; constructor <;> norm_num⟩

/-- OpenStax Introductory Statistics 2e Try It 4.20. Each steel rod is defective with probability
0.01; the first defect on the ninth rod (eight good rods first) has probability `(0.99)^8 (0.01)`,
which lies in `(0.00922, 0.00923)`. -/
@[kb "openstaxintrostats2e" "Try It 4.20, p. 259"]
theorem tryit_4_20_first_defective_rod :
    let p : unitInterval := ⟨0.01, by norm_num⟩
    (geometricMeasure p).real {8} = 0.99 ^ 8 * 0.01 ∧
      (0.00922 < (geometricMeasure p).real {8} ∧ (geometricMeasure p).real {8} < 0.00923) := by
  intro p
  have h : (geometricMeasure p).real {8} = 0.99 ^ 8 * 0.01 := by
    rw [geometricMeasure_real_singleton (hp0 (by norm_num) (by norm_num))]
    simp only [p]; norm_num
  exact ⟨h, by rw [h]; constructor <;> norm_num⟩

/-- OpenStax Introductory Statistics 2e Try It 4.21. Literacy rate of Afghan women 12%; `X` is the
number of women asked until the first literate one. Asking five women (four illiterate first) has
probability `(0.88)^4 (0.12) = 0.0719634432`; asking ten has probability `(0.88)^9 (0.12)` in
`(0.0379, 0.038)`; the mean is `1/p = 25/3`, the variance `(1 - p)/p²` and the standard deviation
lies in `(7.817, 7.818)`. -/
@[kb "openstaxintrostats2e" "Try It 4.21, p. 259"]
theorem tryit_4_21_afghan_literacy :
    let p : unitInterval := ⟨0.12, by norm_num⟩
    (geometricMeasure p).real {4} = 0.0719634432 ∧
      (geometricMeasure p).real {9} = 0.88 ^ 9 * 0.12 ∧
      (0.0379 < (geometricMeasure p).real {9} ∧ (geometricMeasure p).real {9} < 0.038) ∧
      ∫ n, ((n : ℝ) + 1) ∂geometricMeasure p = 25 / 3 ∧
      (7.817 < Real.sqrt (variance (fun n : ℕ => (n : ℝ) + 1) (geometricMeasure p)) ∧
        Real.sqrt (variance (fun n : ℕ => (n : ℝ) + 1) (geometricMeasure p)) < 7.818) := by
  intro p
  have hp := hp0 (c := 0.12) (by norm_num) (by norm_num)
  have h9 : (geometricMeasure p).real {9} = 0.88 ^ 9 * 0.12 := by
    rw [geometricMeasure_real_singleton hp]
    simp only [p]; norm_num
  have hv : variance (fun n : ℕ => (n : ℝ) + 1) (geometricMeasure p) = 0.88 / 0.12 ^ 2 := by
    rw [UndergradKB.Statistics.variance_geometricMeasure_trials hp]
    simp only [p]; norm_num
  refine ⟨?_, h9, ⟨by rw [h9]; norm_num, by rw [h9]; norm_num⟩, ?_, ?_, ?_⟩
  · rw [geometricMeasure_real_singleton hp]
    simp only [p]; norm_num
  · rw [UndergradKB.Statistics.integral_geometricMeasure_trials hp]
    simp only [p]; norm_num
  · rw [hv, Real.lt_sqrt (by norm_num)]; norm_num
  · rw [hv, Real.sqrt_lt' (by norm_num)]; norm_num

/-! ### Section 4.5: hypergeometric -/

/-- OpenStax Introductory Statistics 2e Try It 4.22. A bag has 44 vowel tiles and 56 consonant
tiles and seven are drawn: `P(X = 4)` for the number of vowels is `H(44, 56, 7)` at 4, which lies in
`(0.2350, 0.2351)`. -/
@[kb "openstaxintrostats2e" "Try It 4.22, p. 260"]
theorem tryit_4_22_four_vowels_of_seven :
    0.2350 < UndergradKB.Statistics.hypergeometricPMF 44 56 7 4 ∧
      UndergradKB.Statistics.hypergeometricPMF 44 56 7 4 < 0.2351 := by
  simp only [UndergradKB.Statistics.hypergeometricPMF, choose_real]
  norm_num [Nat.descFactorial, Nat.factorial]

/-- OpenStax Introductory Statistics 2e Try It 4.23. A gross of 144 eggs contains 12 cracked ones and
15 are inspected: the probability of at most three cracked eggs
`∑_{x = 0}^{3} H(12, 132, 15)(x)` lies in `(0.9767, 0.9768)`. -/
@[kb "openstaxintrostats2e" "Try It 4.23, p. 260"]
theorem tryit_4_23_cracked_eggs_at_most_three :
    0.9767 < ∑ x ∈ range 4, UndergradKB.Statistics.hypergeometricPMF 12 132 15 x ∧
      ∑ x ∈ range 4, UndergradKB.Statistics.hypergeometricPMF 12 132 15 x < 0.9768 := by
  simp only [UndergradKB.Statistics.hypergeometricPMF, choose_real, Finset.sum_range_succ,
    Finset.sum_range_zero]
  norm_num [Nat.descFactorial, Nat.factorial]

/-- OpenStax Introductory Statistics 2e Try It 4.24. Of 200 milk cartons 10 have leaked and 18 are
inspected: the probability that at most two leak, `∑_{x = 0}^{2} H(10, 190, 18)(x)`, lies in
`(0.9505, 0.9506)`. -/
@[kb "openstaxintrostats2e" "Try It 4.24, p. 261"]
theorem tryit_4_24_leaking_cartons_at_most_two :
    0.9505 < ∑ x ∈ range 3, UndergradKB.Statistics.hypergeometricPMF 10 190 18 x ∧
      ∑ x ∈ range 3, UndergradKB.Statistics.hypergeometricPMF 10 190 18 x < 0.9506 := by
  simp only [UndergradKB.Statistics.hypergeometricPMF, choose_real, Finset.sum_range_succ,
    Finset.sum_range_zero]
  norm_num [Nat.descFactorial, Nat.factorial]

/-- OpenStax Introductory Statistics 2e Try It 4.25. A ten-player team is drawn from 15 boys and
12 girls: the probability that exactly eight players are boys is `H(15, 12, 10)(8) = 22/437`
(about 0.0503). -/
@[kb "openstaxintrostats2e" "Try It 4.25, p. 262"]
theorem tryit_4_25_basketball_team_eight_boys :
    UndergradKB.Statistics.hypergeometricPMF 15 12 10 8 = 22 / 437 := by
  simp only [UndergradKB.Statistics.hypergeometricPMF, choose_real]
  norm_num [Nat.descFactorial, Nat.factorial]

/-! ### Section 4.6: Poisson -/

/-- Pure arithmetic: if `E` lies between two bounds and `S > 0`, the product `E * S` is bracketed. -/
private lemma bound_mul {E a b S lo hi : ℝ} (hS : 0 < S) (ha : a < E) (hb : E < b)
    (h1 : lo ≤ a * S) (h2 : b * S ≤ hi) : lo < E * S ∧ E * S < hi :=
  ⟨lt_of_le_of_lt h1 (mul_lt_mul_of_pos_right ha hS),
    lt_of_lt_of_le (mul_lt_mul_of_pos_right hb hS) h2⟩

private lemma poisson_Iic (r : ℝ≥0) (k : ℕ) :
    (poissonMeasure r).real (Set.Iic k) =
      Real.exp (-(r : ℝ)) * ∑ j ∈ range (k + 1), (r : ℝ) ^ j / (j.factorial : ℝ) := by
  rw [real_Iic, Finset.mul_sum]
  exact sum_congr rfl fun j _ => by rw [poissonMeasure_real_singleton]; ring

/-- Bounds for `e^(-1/2)` (Taylor polynomial of degree 7 with the remainder estimate). -/
private lemma exp_neg_half_bounds :
    (0.6065306 : ℝ) < Real.exp (-(1 / 2)) ∧ Real.exp (-(1 / 2)) < 0.6065307 := by
  have hb := Real.exp_bound (x := -(1 / 2)) (by norm_num [abs_of_neg]) (n := 12) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb
  norm_num [abs_le] at hb
  constructor <;> linarith [hb.1, hb.2]

/-- Bounds for `e^(-225/2)`. -/
private lemma exp_neg_112_5_bounds :
    (1 / 2.7182818286 : ℝ) ^ 112 * 0.6065306 < Real.exp (-(225 / 2)) ∧
      Real.exp (-(225 / 2)) < (1 / 2.7182818283 : ℝ) ^ 112 * 0.6065307 := by
  obtain ⟨h1, h2⟩ := exp_neg_nat_bounds 112 (by norm_num)
  obtain ⟨h3, h4⟩ := exp_neg_half_bounds
  have e : Real.exp (-(225 / 2)) = Real.exp (-((112 : ℕ) : ℝ)) * Real.exp (-(1 / 2)) := by
    rw [← Real.exp_add]; norm_num
  rw [e]
  exact ⟨mul_lt_mul'' h1 h3 (by positivity) (by positivity),
    mul_lt_mul'' h2 h4 (by positivity) (by positivity)⟩

/-- Bounds for `e^(-1.43)`, from the Taylor polynomial of `e^(-0.715)` and squaring. -/
private lemma exp_neg_1_43_bounds :
    (0.239308 : ℝ) < Real.exp (-(143 / 100)) ∧ Real.exp (-(143 / 100)) < 0.23931 := by
  have hb := Real.exp_bound (x := -(143 / 200)) (by norm_num [abs_of_neg]) (n := 12) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb
  norm_num [abs_le] at hb
  have e : Real.exp (-(143 / 100)) = Real.exp (-(143 / 200)) * Real.exp (-(143 / 200)) := by
    rw [← Real.exp_add]; norm_num
  have h1 : (0.4891921 : ℝ) < Real.exp (-(143 / 200)) := by linarith [hb.1]
  have h2 : Real.exp (-(143 / 200)) < 0.4891922 := by linarith [hb.2]
  rw [e]
  constructor <;> nlinarith

/-- OpenStax Introductory Statistics 2e Try It 4.26. Eight fish an hour on average gives
`8 · (15/60) = 2` fish per fifteen minutes. -/
@[kb "openstaxintrostats2e" "Try It 4.26, p. 263"]
theorem tryit_4_26_fish_in_fifteen_minutes :
    (8 : ℝ) * (15 / 60) = 2 := by norm_num

/-- OpenStax Introductory Statistics 2e Try It 4.27. Ten returns a day on average, `X ~ P(10)`:
`P(X < 8) = P(X ≤ 7)` lies in `(0.2202, 0.2203)`. -/
@[kb "openstaxintrostats2e" "Try It 4.27, p. 263"]
theorem tryit_4_27_returns_fewer_than_eight :
    0.2202 < (poissonMeasure 10).real (Set.Iic 7) ∧ (poissonMeasure 10).real (Set.Iic 7) < 0.2203 := by
  rw [poisson_Iic]
  obtain ⟨h1, h2⟩ := exp_neg_nat_bounds 10 (by norm_num)
  simp only [NNReal.coe_ofNat, Nat.cast_ofNat] at h1 h2 ⊢
  exact bound_mul (by positivity) h1 h2
    (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

/-- OpenStax Introductory Statistics 2e Try It 4.29. Ten emails per half hour is 2 per six minutes:
`P(X > 4) = 1 - 7 e⁻²` lies in `(0.05265, 0.05266)`. -/
@[kb "openstaxintrostats2e" "Try It 4.29, p. 265"]
theorem tryit_4_29_emails_in_six_minutes :
    (poissonMeasure 2).real (Set.Ioi 4) = 1 - 7 * Real.exp (-2) ∧
      (0.05265 < (poissonMeasure 2).real (Set.Ioi 4) ∧
        (poissonMeasure 2).real (Set.Ioi 4) < 0.05266) := by
  have h : (poissonMeasure 2).real (Set.Ioi 4) = 1 - 7 * Real.exp (-2) := by
    rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, poisson_Iic]
    simp [Finset.sum_range_succ, Nat.factorial]
    ring
  obtain ⟨h1, h2⟩ := exp_neg_nat_bounds 2 (by norm_num)
  simp only [Nat.cast_ofNat] at h1 h2
  have hb : (0.94734 : ℝ) ≤ (1 / 2.7182818286) ^ 2 * 7 ∧ (1 / 2.7182818283 : ℝ) ^ 2 * 7 ≤ 0.94735 := by
    constructor <;> norm_num
  refine ⟨h, ?_, ?_⟩ <;> rw [h] <;> nlinarith [hb.1, hb.2]

/-- OpenStax Introductory Statistics 2e Try It 4.30. Texts per day `X ~ P(187)`: `P(X = 175)` lies in
`(0.02033, 0.02034)` and `P(X ≤ 150)` in `(0.002968, 0.002969)`. -/
@[kb "openstaxintrostats2e" "Try It 4.30, p. 265"]
theorem tryit_4_30_text_messages :
    (0.02033 < (poissonMeasure 187).real {175} ∧ (poissonMeasure 187).real {175} < 0.02034) ∧
      (0.002968 < (poissonMeasure 187).real (Set.Iic 150) ∧
        (poissonMeasure 187).real (Set.Iic 150) < 0.002969) := by
  obtain ⟨h1, h2⟩ := exp_neg_nat_bounds 187 (by norm_num)
  simp only [Nat.cast_ofNat] at h1 h2
  refine ⟨?_, ?_⟩
  · rw [poissonMeasure_real_singleton]
    simp only [NNReal.coe_ofNat]
    rw [mul_div_assoc]
    exact bound_mul (by positivity) h1 h2 (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
  · rw [poisson_Iic]
    simp only [NNReal.coe_ofNat]
    exact bound_mul (by positivity) h1 h2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

/-- OpenStax Introductory Statistics 2e Try It 4.31. Atlanta airport: 2700 movements a day is
`2700/24 = 112.5` per hour, and `X ~ P(112.5)`: `P(X = 100)` lies in `(0.019369, 0.01937)` and
`P(X ≤ 100)` in `(0.12789, 0.1279)`. -/
@[kb "openstaxintrostats2e" "Try It 4.31, p. 266"]
theorem tryit_4_31_airport_arrivals_per_hour :
    (2700 : ℝ) / 24 = 112.5 ∧
      (0.019369 < (poissonMeasure (225 / 2)).real {100} ∧
        (poissonMeasure (225 / 2)).real {100} < 0.01937) ∧
      (0.12789 < (poissonMeasure (225 / 2)).real (Set.Iic 100) ∧
        (poissonMeasure (225 / 2)).real (Set.Iic 100) < 0.1279) := by
  obtain ⟨h1, h2⟩ := exp_neg_112_5_bounds
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [poissonMeasure_real_singleton]
    push_cast
    rw [mul_div_assoc]
    exact bound_mul (by positivity) h1 h2 (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
  · rw [poisson_Iic]
    push_cast
    exact bound_mul (by positivity) h1 h2
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

/-- OpenStax Introductory Statistics 2e Try It 4.32. An event with probability 0.0143 per day over
100 days: the binomial `B(100, 0.0143)` gives `P(X = 5)` in `(0.011459, 0.01146)`, the Poisson
approximation `P(1.43)` gives a value in `(0.01192, 0.01193)`, and the two differ by less than
0.001 (they are close). -/
@[kb "openstaxintrostats2e" "Try It 4.32, p. 266"]
theorem tryit_4_32_seismic_binomial_vs_poisson :
    let p : unitInterval := ⟨0.0143, by norm_num⟩
    (0.011459 < Bin(100, p).real {5} ∧ Bin(100, p).real {5} < 0.01146) ∧
      (0.01192 < (poissonMeasure (143 / 100)).real {5} ∧
        (poissonMeasure (143 / 100)).real {5} < 0.01193) ∧
      |Bin(100, p).real {5} - (poissonMeasure (143 / 100)).real {5}| < 0.001 := by
  intro p
  obtain ⟨h1, h2⟩ := exp_neg_1_43_bounds
  have hB : 0.011459 < Bin(100, p).real {5} ∧ Bin(100, p).real {5} < 0.01146 := by
    rw [binomial_real_singleton]
    simp only [p, choose_real]
    norm_num [Nat.descFactorial, Nat.factorial]
  have hP : 0.01192 < (poissonMeasure (143 / 100)).real {5} ∧
      (poissonMeasure (143 / 100)).real {5} < 0.01193 := by
    rw [poissonMeasure_real_singleton]
    push_cast
    rw [mul_div_assoc]
    exact bound_mul (by positivity) h1 h2 (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
  refine ⟨hB, hP, ?_⟩
  rw [abs_lt]
  constructor <;> linarith [hB.1, hB.2, hP.1, hP.2]

end UndergradKB.Statistics.Course.TryItC4
