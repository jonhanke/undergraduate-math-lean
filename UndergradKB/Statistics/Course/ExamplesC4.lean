import Mathlib.Probability.UniformOn
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Prod
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Discrete

/-!
# Worked examples, chapter 4 (OpenStax *Introductory Statistics 2e*): discrete random variables

Probability tables, expected values and standard deviations, and the binomial, geometric,
hypergeometric and Poisson laws, with exact answers (or two-sided bounds where the book rounds).
Mathlib's `binomial`, `geometricMeasure` (counting failures before the first success) and
`poissonMeasure` are used for the named laws, and `hypergeometricPMF` from the repository.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal unitInterval

namespace UndergradKB.Statistics.Course.ExamplesC4

section Helpers

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype Ω]

private lemma coe_filter_univ (p : Ω → Prop) [DecidablePred p] :
    ((Finset.univ.filter p : Finset Ω) : Set Ω) = {ω | p ω} := by
  ext; simp

private lemma uniform_real (s : Finset Ω) :
    (uniformOn (Set.univ : Set Ω) (s : Set Ω)).toReal = (#s : ℝ) / Fintype.card Ω := by
  classical
  have h := uniformOn_apply_finset (Ω := Ω) (s := Finset.univ) (t := s)
  rw [Finset.coe_univ] at h
  rw [h, Finset.univ_inter, Finset.card_univ, ENNReal.toReal_div]
  simp

omit [MeasurableSingletonClass Ω] [Fintype Ω] in
private lemma cond_real (μ : Measure Ω) {s t : Set Ω} (hs : MeasurableSet s) :
    (μ[t | s]).toReal = (μ (s ∩ t)).toReal / (μ s).toReal := by
  rw [cond_apply hs, ENNReal.toReal_mul, ENNReal.toReal_inv]
  ring

private lemma prob_card (p : Ω → Prop) [DecidablePred p] (k N : ℕ) (hN : Fintype.card Ω = N)
    (hk : #(Finset.univ.filter p) = k) :
    (uniformOn (Set.univ : Set Ω) {ω | p ω}).toReal = (k : ℝ) / N := by
  have := uniform_real (Finset.univ.filter p)
  rw [coe_filter_univ] at this
  rw [this, hk, hN]

private lemma cprob_card (p q : Ω → Prop) [DecidablePred p] [DecidablePred q] (a b : ℕ)
    (ha : #(Finset.univ.filter (fun ω => p ω ∧ q ω)) = a) (hb : #(Finset.univ.filter p) = b) :
    ((uniformOn (Set.univ : Set Ω))[{ω | q ω} | {ω | p ω}]).toReal = (a : ℝ) / b := by
  have hs : MeasurableSet {ω | p ω} := (Set.toFinite _).measurableSet
  rw [cond_real _ hs]
  have h1 := uniform_real (Finset.univ.filter (fun ω => p ω ∧ q ω))
  have h2 := uniform_real (Finset.univ.filter p)
  rw [coe_filter_univ] at h1 h2
  have : {ω | p ω} ∩ {ω | q ω} = {ω | p ω ∧ q ω} := rfl
  rw [this, h1, h2, ha, hb]
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · rw [← ha, ← hb]; simp
  · have : (Fintype.card Ω : ℝ) ≠ 0 := by positivity
    rw [div_div_div_cancel_right₀ this]

/-- Expectation under the uniform measure is the average. -/
private lemma uniform_integral (f : Ω → ℝ) :
    ∫ ω, f ω ∂(uniformOn (Set.univ : Set Ω)) = (∑ ω, f ω) / Fintype.card Ω := by
  classical
  rw [integral_fintype _]
  simp only [measureReal_def]
  have : ∀ ω : Ω, (uniformOn (Set.univ : Set Ω) {ω}).toReal = 1 / Fintype.card Ω := by
    intro ω
    have := uniform_real ({ω} : Finset Ω)
    simpa using this
  simp only [this, smul_eq_mul]
  rw [← Finset.mul_sum]
  · ring
  · exact Integrable.of_finite

end Helpers

private lemma real_Iic (μ : Measure ℕ) [IsFiniteMeasure μ] (k : ℕ) :
    μ.real (Set.Iic k) = ∑ j ∈ range (k + 1), μ.real {j} := by
  have : (Set.Iic k : Set ℕ) = ↑(Finset.range (k + 1)) := by
    ext; simp [Nat.lt_succ_iff]
  rw [this, sum_measureReal_singleton]

private lemma exp_neg_two_bounds : (0.13533 : ℝ) < Real.exp (-2) ∧ Real.exp (-2) < 0.13534 := by
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.exp_one_lt_d9
  have e : Real.exp (-2) = 1 / (Real.exp 1 * Real.exp 1) := by
    rw [show (-2 : ℝ) = -(1 + 1) by norm_num, Real.exp_neg, Real.exp_add, one_div, mul_inv]
  rw [e]
  have hp : 0 < Real.exp 1 * Real.exp 1 := by positivity
  constructor
  · rw [lt_div_iff₀ hp]; nlinarith
  · rw [div_lt_iff₀ hp]; nlinarith

private lemma exp_neg_six_bounds : (0.002478 : ℝ) < Real.exp (-6) ∧ Real.exp (-6) < 0.00248 := by
  obtain ⟨h1, h2⟩ := exp_neg_two_bounds
  have e : Real.exp (-6) = Real.exp (-2) ^ 3 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  exact ⟨lt_of_lt_of_le (by norm_num) (pow_le_pow_left₀ (by norm_num) h1.le 3),
    lt_of_le_of_lt (pow_le_pow_left₀ (by positivity) h2.le 3) (by norm_num)⟩

/-- OpenStax Introductory Statistics 2e Example 4.2. Nancy attends class 0, 1, 2 or 3 days a week
with probabilities 0.01, 0.04, 0.15, 0.80: every `P(x)` lies in `[0, 1]` and the column sums to 1. -/
@[kb "openstaxintrostats2e" "Example 4.2, p. 241"]
theorem example_4_2_probability_table_sums_to_one :
    let p : Fin 4 → ℝ := ![0.01, 0.04, 0.15, 0.80]
    (∀ i, 0 ≤ p i ∧ p i ≤ 1) ∧ ∑ i, p i = 1 := by
  intro p
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> simp [p] <;> norm_num
  · simp [p, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Example 4.3. A soccer team plays 0, 1 or 2 days a week with
probabilities 0.2, 0.5, 0.3: the expected value is `μ = 1.1`, the variance `0.49` and the standard
deviation `σ = 0.7`. -/
@[kb "openstaxintrostats2e" "Example 4.3, p. 243"]
theorem example_4_3_soccer_expected_value :
    let x : Fin 3 → ℝ := ![0, 1, 2]
    let p : Fin 3 → ℝ := ![0.2, 0.5, 0.3]
    ∑ i, x i * p i = 1.1 ∧ ∑ i, (x i - 1.1) ^ 2 * p i = 0.49 ∧
      Real.sqrt (∑ i, (x i - 1.1) ^ 2 * p i) = 0.7 := by
  intro x p
  have h : ∑ i, (x i - 1.1) ^ 2 * p i = 0.49 := by
    simp [x, p, Fin.sum_univ_succ]; norm_num
  refine ⟨by simp [x, p, Fin.sum_univ_succ]; norm_num, h, ?_⟩
  rw [h, show (0.49 : ℝ) = 0.7 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- OpenStax Introductory Statistics 2e Example 4.4 (with the table of Example 4.1). The number of
times per week a newborn wakes its mother has probabilities 0.04, 0.22, 0.46, 0.18, 0.08, 0.02 for
0 to 5: they sum to 1, the mean is 2.1, the variance `∑ (x - μ)² P(x)` is 1.05 and the standard
deviation lies between 1.0246 and 1.0247 (the book's 1.0247). -/
@[kb "openstaxintrostats2e" "Example 4.4, p. 243"]
theorem example_4_4_newborn_waking_mean_and_sd :
    let x : Fin 6 → ℝ := ![0, 1, 2, 3, 4, 5]
    let p : Fin 6 → ℝ := ![0.04, 0.22, 0.46, 0.18, 0.08, 0.02]
    ∑ i, p i = 1 ∧ ∑ i, x i * p i = 2.1 ∧ ∑ i, (x i - 2.1) ^ 2 * p i = 1.05 ∧
      (1.0246 < Real.sqrt (∑ i, (x i - 2.1) ^ 2 * p i) ∧
        Real.sqrt (∑ i, (x i - 2.1) ^ 2 * p i) < 1.0247) := by
  intro x p
  have h : ∑ i, (x i - 2.1) ^ 2 * p i = 1.05 := by
    simp [x, p, Fin.sum_univ_succ]; norm_num
  refine ⟨by simp [p, Fin.sum_univ_succ]; norm_num, by simp [x, p, Fin.sum_univ_succ]; norm_num,
    h, ?_, ?_⟩
  · rw [h, Real.lt_sqrt (by norm_num)]; norm_num
  · rw [h, Real.sqrt_lt' (by norm_num)]; norm_num

/-- OpenStax Introductory Statistics 2e Example 4.5. A $2 game pays $100 000 profit for matching five
random digits in order (probability `(1/10)^5 = 0.00001`): the expected profit is `-0.99998`
dollars, about a $1 loss per play. -/
@[kb "openstaxintrostats2e" "Example 4.5, p. 245"]
theorem example_4_5_lottery_expected_profit :
    ((1 : ℝ) / 10) ^ 5 = 0.00001 ∧
      100000 * ((1 : ℝ) / 10) ^ 5 + (-2) * (1 - ((1 : ℝ) / 10) ^ 5) = -0.99998 := by
  constructor <;> norm_num

/-- OpenStax Introductory Statistics 2e Example 4.6. A biased coin: a tail (probability 1/3) wins
$10 and a head (probability 2/3) loses $6, so the expected profit per play is `-2/3` dollars (a
loss of about 67 cents). -/
@[kb "openstaxintrostats2e" "Example 4.6, p. 245"]
theorem example_4_6_biased_coin_game :
    (10 : ℝ) * (1 / 3) + (-6) * (2 / 3) = -2 / 3 := by norm_num

/-- OpenStax Introductory Statistics 2e Example 4.7. Toss a fair die twice and let `X` be the number
of even faces (face `i + 1` is even exactly when `i` is odd): `P(X = 0) = 1/4`, `P(X = 1) = 1/2`,
`P(X = 2) = 1/4`, the mean is 1, the variance `1/2` and the standard deviation lies in
`(0.7071, 0.7072)` (it is `√2 / 2 ≈ 0.7071`). -/
@[kb "openstaxintrostats2e" "Example 4.7, p. 247"]
theorem example_4_7_two_dice_even_faces :
    let P : Measure (Fin 6 × Fin 6) := uniformOn Set.univ
    let X : Fin 6 × Fin 6 → ℕ := fun ω => (ω.1 : ℕ) % 2 + (ω.2 : ℕ) % 2
    (P {ω | X ω = 0}).toReal = 1 / 4 ∧ (P {ω | X ω = 1}).toReal = 1 / 2 ∧
      (P {ω | X ω = 2}).toReal = 1 / 4 ∧ ∫ ω, (X ω : ℝ) ∂P = 1 ∧
      ∫ ω, ((X ω : ℝ) - 1) ^ 2 ∂P = 1 / 2 ∧
      (0.7071 < Real.sqrt (∫ ω, ((X ω : ℝ) - 1) ^ 2 ∂P) ∧
        Real.sqrt (∫ ω, ((X ω : ℝ) - 1) ^ 2 ∂P) < 0.7072) := by
  intro P X
  have hc : Fintype.card (Fin 6 × Fin 6) = 36 := by simp
  have hm : ∫ ω, (X ω : ℝ) ∂P = 1 := by
    rw [uniform_integral, hc]
    have h : ∑ ω, X ω = 36 := by decide
    have := congrArg (Nat.cast : ℕ → ℝ) h
    push_cast at this
    rw [this]; norm_num
  have hv : ∫ ω, ((X ω : ℝ) - 1) ^ 2 ∂P = 1 / 2 := by
    rw [uniform_integral, hc]
    have h : ∑ ω, ((X ω : ℤ) - 1) ^ 2 = 18 := by decide
    have := congrArg (Int.cast : ℤ → ℝ) h
    push_cast at this
    rw [this]; norm_num
  refine ⟨?_, ?_, ?_, hm, hv, ?_, ?_⟩
  · exact (prob_card (fun ω : Fin 6 × Fin 6 => X ω = 0) 9 36 hc (by decide)).trans (by norm_num)
  · exact (prob_card (fun ω : Fin 6 × Fin 6 => X ω = 1) 18 36 hc (by decide)).trans (by norm_num)
  · exact (prob_card (fun ω : Fin 6 × Fin 6 => X ω = 2) 9 36 hc (by decide)).trans (by norm_num)
  · rw [hv, Real.lt_sqrt (by norm_num)]; norm_num
  · rw [hv, Real.sqrt_lt' (by norm_num)]; norm_num

/-- OpenStax Introductory Statistics 2e Example 4.8. A bet wins $50 with probability 0.2142 and loses
$20 otherwise: the mean profit is `-5.006` dollars, the variance lies in `(824.7, 824.8)` and the
standard deviation in `(28.7, 28.72)`. -/
@[kb "openstaxintrostats2e" "Example 4.8, p. 248"]
theorem example_4_8_earthquake_bet :
    let x : Fin 2 → ℝ := ![50, -20]
    let p : Fin 2 → ℝ := ![0.2142, 1 - 0.2142]
    ∑ i, x i * p i = -5.006 ∧
      (824.7 < ∑ i, (x i - (-5.006)) ^ 2 * p i ∧ ∑ i, (x i - (-5.006)) ^ 2 * p i < 824.8) ∧
      (28.7 < Real.sqrt (∑ i, (x i - (-5.006)) ^ 2 * p i) ∧
        Real.sqrt (∑ i, (x i - (-5.006)) ^ 2 * p i) < 28.72) := by
  intro x p
  have hv : ∑ i, (x i - (-5.006)) ^ 2 * p i = (50 + 5.006) ^ 2 * 0.2142 +
      (-20 + 5.006) ^ 2 * (1 - 0.2142) := by
    simp [x, p, Fin.sum_univ_succ]
  refine ⟨by simp [x, p, Fin.sum_univ_succ]; norm_num, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hv]; norm_num
  · rw [hv]; norm_num
  · rw [hv, Real.lt_sqrt (by norm_num)]; norm_num
  · rw [hv, Real.sqrt_lt' (by norm_num)]; norm_num

/-- OpenStax Introductory Statistics 2e Example 4.10. Winning 15 of 20 independent games, each won
with probability 0.55: `P(X = 15) = C(20, 15) (0.55)^15 (0.45)^5`, which lies in `(0.0364, 0.0365)`
(`X ~ B(20, 0.55)`). -/
@[kb "openstaxintrostats2e" "Example 4.10, p. 249"]
theorem example_4_10_fifteen_wins_in_twenty :
    let p : unitInterval := ⟨0.55, by norm_num⟩
    Bin(20, p).real {15} = 15504 * (11 / 20) ^ 15 * (9 / 20) ^ 5 ∧
      (0.0364 < Bin(20, p).real {15} ∧ Bin(20, p).real {15} < 0.0365) := by
  intro p
  have h : Bin(20, p).real {15} = 15504 * (11 / 20) ^ 15 * (9 / 20) ^ 5 := by
    rw [binomial_real_singleton]
    simp [p, Nat.choose]
    norm_num
  exact ⟨h, by rw [h]; constructor <;> norm_num⟩

/-- OpenStax Introductory Statistics 2e Example 4.11. A coin weighted to land heads with probability
0.25 is flipped five times: `P(X > 3) = P(X = 4) + P(X = 5) = 1/64` (`X ~ B(5, 0.25)`). -/
@[kb "openstaxintrostats2e" "Example 4.11, p. 250"]
theorem example_4_11_weighted_coin_more_than_three_heads :
    let p : unitInterval := ⟨1 / 4, by norm_num⟩
    Bin(5, p).real {4} + Bin(5, p).real {5} = 1 / 64 := by
  intro p
  rw [binomial_real_singleton, binomial_real_singleton]
  simp [p, Nat.choose]
  norm_num

/-- OpenStax Introductory Statistics 2e Example 4.13. For `X ~ B(20, 0.41)`: `P(X ≤ 12)` lies in
`(0.97375, 0.97385)` (the book's 0.9738), the mean is `np = 8.2`, the variance is `npq = 4.838` and
the standard deviation lies in `(2.19, 2.21)` (the book's 2.20). -/
@[kb "openstaxintrostats2e" "Example 4.13, p. 251"]
theorem example_4_13_high_school_diploma_workers :
    let p : unitInterval := ⟨0.41, by norm_num⟩
    (0.97375 < Bin(20, p).real (Set.Iic 12) ∧ Bin(20, p).real (Set.Iic 12) < 0.97385) ∧
      ∫ x, x ∂Bin(ℝ, 20, p) = 8.2 ∧ variance (id : ℝ → ℝ) Bin(ℝ, 20, p) = 4.838 ∧
      (2.19 < Real.sqrt (variance (id : ℝ → ℝ) Bin(ℝ, 20, p)) ∧
        Real.sqrt (variance (id : ℝ → ℝ) Bin(ℝ, 20, p)) < 2.21) := by
  intro p
  have hv : variance (id : ℝ → ℝ) Bin(ℝ, 20, p) = 4.838 := by
    rw [UndergradKB.Statistics.variance_binomial]; simp [p] <;> norm_num
  have hs : Bin(20, p).real (Set.Iic 12) = ∑ j ∈ range 13, (Nat.choose 20 j : ℝ) * (0.41 : ℝ) ^ j *
      (1 - 0.41) ^ (20 - j) := by
    rw [real_Iic]
    exact sum_congr rfl fun j _ => by rw [binomial_real_singleton]
  refine ⟨?_, ?_, hv, ?_, ?_⟩
  · rw [hs]
    simp [Finset.sum_range_succ, Nat.choose]
    constructor <;> norm_num
  · have : ∫ x, x ∂Bin(ℝ, 20, p) = p * 20 :=
      integral_of_hasLaw_binomial (X := id) (P := Bin(ℝ, 20, p)) HasLaw.id
    rw [this]; simp [p]; norm_num
  · rw [hv, Real.lt_sqrt (by norm_num)]; norm_num
  · rw [hv, Real.sqrt_lt' (by norm_num)]; norm_num

/-- OpenStax Introductory Statistics 2e Example 4.14. Of 560 catalog pages 8 feature signature
artists and 100 pages are sampled, so `X ~ B(100, 1/70)`: `P(X = 2)` lies in `(0.2465, 0.2467)`
(the book's 0.2466), the mean is `100/70 = 10/7` and the standard deviation lies in
`(1.186, 1.188)` (the book's 1.1867). -/
@[kb "openstaxintrostats2e" "Example 4.14, p. 252"]
theorem example_4_14_signature_artist_pages :
    let p : unitInterval := ⟨1 / 70, by norm_num⟩
    (0.2465 < Bin(100, p).real {2} ∧ Bin(100, p).real {2} < 0.2467) ∧
      ∫ x, x ∂Bin(ℝ, 100, p) = 10 / 7 ∧
      (1.186 < Real.sqrt (variance (id : ℝ → ℝ) Bin(ℝ, 100, p)) ∧
        Real.sqrt (variance (id : ℝ → ℝ) Bin(ℝ, 100, p)) < 1.188) := by
  intro p
  have hv : variance (id : ℝ → ℝ) Bin(ℝ, 100, p) = 100 * (1 / 70) * (69 / 70) := by
    rw [UndergradKB.Statistics.variance_binomial]; simp [p] <;> norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [binomial_real_singleton]
    simp [p, Nat.choose]
    constructor <;> norm_num
  · have : ∫ x, x ∂Bin(ℝ, 100, p) = p * 100 :=
      integral_of_hasLaw_binomial (X := id) (P := Bin(ℝ, 100, p)) HasLaw.id
    rw [this]; simp [p]; norm_num
  · rw [hv, Real.lt_sqrt (by norm_num)]; norm_num
  · rw [hv, Real.sqrt_lt' (by norm_num)]; norm_num

/-- OpenStax Introductory Statistics 2e Example 4.15. Lifetime cancer risk 1.5%, 200 people sampled,
`X ~ B(200, 0.015)`: the mean is 3, the standard deviation lies in `(1.71, 1.73)`, and five cases
(probability in `(0.10105, 0.10115)`) are more likely than six (probability in `(0.04995, 0.05005)`). -/
@[kb "openstaxintrostats2e" "Example 4.15, p. 253"]
theorem example_4_15_lifetime_cancer_risk :
    let p : unitInterval := ⟨0.015, by norm_num⟩
    ∫ x, x ∂Bin(ℝ, 200, p) = 3 ∧
      (1.71 < Real.sqrt (variance (id : ℝ → ℝ) Bin(ℝ, 200, p)) ∧
        Real.sqrt (variance (id : ℝ → ℝ) Bin(ℝ, 200, p)) < 1.73) ∧
      (0.10105 < Bin(200, p).real {5} ∧ Bin(200, p).real {5} < 0.10115) ∧
      (0.04995 < Bin(200, p).real {6} ∧ Bin(200, p).real {6} < 0.05005) ∧
      Bin(200, p).real {6} < Bin(200, p).real {5} := by
  intro p
  have hv : variance (id : ℝ → ℝ) Bin(ℝ, 200, p) = 200 * 0.015 * (1 - 0.015) := by
    rw [UndergradKB.Statistics.variance_binomial]; simp [p]
  have c5 : Nat.choose 200 5 = 2535650040 := by
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  have c6 : Nat.choose 200 6 = 82408626300 := by
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  have h5 : (0.10105 < Bin(200, p).real {5} ∧ Bin(200, p).real {5} < 0.10115) := by
    rw [binomial_real_singleton, c5]
    simp only [p]
    constructor <;> norm_num
  have h6 : (0.04995 < Bin(200, p).real {6} ∧ Bin(200, p).real {6} < 0.05005) := by
    rw [binomial_real_singleton, c6]
    simp only [p]
    constructor <;> norm_num
  refine ⟨?_, ⟨?_, ?_⟩, h5, h6, by linarith [h5.1, h5.2, h6.1, h6.2]⟩
  · have : ∫ x, x ∂Bin(ℝ, 200, p) = p * 200 :=
      integral_of_hasLaw_binomial (X := id) (P := Bin(ℝ, 200, p)) HasLaw.id
    rw [this]; simp [p]; norm_num
  · rw [hv, Real.lt_sqrt (by norm_num)]; norm_num
  · rw [hv, Real.sqrt_lt' (by norm_num)]; norm_num

/-- Ordered draws of two distinct items from `n` without replacement. -/
abbrev TwoWithoutReplacement (n : ℕ) := {p : Fin n × Fin n // p.1 ≠ p.2}

/-- OpenStax Introductory Statistics 2e Example 4.16. A committee of 10 staff and 6 students picks a
chairperson and then a recorder without replacement (240 equally likely ordered pairs, members
`i < 6` are students): both are students with probability `(6/16)(5/15) = 1/8`, but the chance that
the recorder is a student is `1/3` after a student chair and `2/5` after a staff chair, so the draws
are not independent and the count of students is not binomial. -/
@[kb "openstaxintrostats2e" "Example 4.16, p. 254"]
theorem example_4_16_committee_not_binomial :
    let P : Measure (TwoWithoutReplacement 16) := uniformOn Set.univ
    (P {ω | (ω.1.1 : ℕ) < 6 ∧ (ω.1.2 : ℕ) < 6}).toReal = 1 / 8 ∧
      (P[{ω | (ω.1.2 : ℕ) < 6} | {ω | (ω.1.1 : ℕ) < 6}]).toReal = 1 / 3 ∧
      (P[{ω | (ω.1.2 : ℕ) < 6} | {ω | 6 ≤ (ω.1.1 : ℕ)}]).toReal = 2 / 5 := by
  intro P
  have hc : Fintype.card (TwoWithoutReplacement 16) = 240 := by decide +kernel
  refine ⟨?_, ?_, ?_⟩
  · exact (prob_card (fun ω : TwoWithoutReplacement 16 => (ω.1.1 : ℕ) < 6 ∧ (ω.1.2 : ℕ) < 6) 30 240
      hc (by decide +kernel)).trans (by norm_num)
  · exact (cprob_card (fun ω : TwoWithoutReplacement 16 => (ω.1.1 : ℕ) < 6)
      (fun ω => (ω.1.2 : ℕ) < 6) 30 90 (by decide +kernel) (by decide +kernel)).trans
      (by norm_num)
  · exact (cprob_card (fun ω : TwoWithoutReplacement 16 => 6 ≤ (ω.1.1 : ℕ))
      (fun ω => (ω.1.2 : ℕ) < 6) 60 150 (by decide +kernel) (by decide +kernel)).trans
      (by norm_num)

/-- OpenStax Introductory Statistics 2e Example 4.17. A game is played until the first loss, each
game being lost with probability 0.57. Mathlib's `geometricMeasure` counts the failures (wins)
before the first success (loss); needing five games means four wins first, with probability
`(0.43)^4 (0.57)`, which lies in `(0.0194, 0.0196)`. -/
@[kb "openstaxintrostats2e" "Example 4.17, p. 255"]
theorem example_4_17_games_until_first_loss :
    let p : unitInterval := ⟨0.57, by norm_num⟩
    (geometricMeasure p).real {4} = 0.43 ^ 4 * 0.57 ∧
      (0.0194 < (geometricMeasure p).real {4} ∧ (geometricMeasure p).real {4} < 0.0196) := by
  intro p
  have hp : p ≠ 0 := by
    intro h
    have := congrArg Subtype.val h
    norm_num [p] at this
  have h : (geometricMeasure p).real {4} = 0.43 ^ 4 * 0.57 := by
    rw [geometricMeasure_real_singleton hp]
    simp only [p]; norm_num
  exact ⟨h, by rw [h]; constructor <;> norm_num⟩

/-- OpenStax Introductory Statistics 2e Example 4.18. Reports are examined until one shows an
accident caused by failure to follow instructions (probability 0.35 per report). The expected
number of reports examined is `1/p = 20/7`, and the probability that at least three are needed
(at least two failures first) is `0.65² = 0.4225`. -/
@[kb "openstaxintrostats2e" "Example 4.18, p. 255"]
theorem example_4_18_reports_until_first_hit :
    let p : unitInterval := ⟨0.35, by norm_num⟩
    ∫ n, ((n : ℝ) + 1) ∂geometricMeasure p = 20 / 7 ∧
      (geometricMeasure p).real (Set.Ici 2) = 0.4225 := by
  intro p
  have hp : p ≠ 0 := by
    intro h
    have := congrArg Subtype.val h
    norm_num [p] at this
  refine ⟨?_, ?_⟩
  · rw [UndergradKB.Statistics.integral_geometricMeasure_trials hp]
    simp only [p]; norm_num
  · have e : (Set.Ici 2 : Set ℕ) = (Set.Iic 1)ᶜ := by
      ext n; simp only [Set.mem_Ici, Set.mem_compl_iff, Set.mem_Iic, not_le]; omega
    rw [e, probReal_compl_eq_one_sub measurableSet_Iic, real_Iic]
    simp [Finset.sum_range_succ, geometricMeasure_real_singleton hp, p]
    norm_num

/-- OpenStax Introductory Statistics 2e Example 4.19. Contacting students until one lives within
five miles (probability 0.55 each): the first success on the fourth contact (three failures first)
has probability `(0.45)^3 (0.55) = 0.05011875`. -/
@[kb "openstaxintrostats2e" "Example 4.19, p. 256"]
theorem example_4_19_fourth_student_is_first :
    let p : unitInterval := ⟨0.55, by norm_num⟩
    (geometricMeasure p).real {3} = 0.05011875 := by
  intro p
  have hp : p ≠ 0 := by
    intro h
    have := congrArg Subtype.val h
    norm_num [p] at this
  rw [geometricMeasure_real_singleton hp]
  simp only [p]; norm_num

/-- OpenStax Introductory Statistics 2e Example 4.20. Each component is defective with probability
0.02. The first defect is the seventh component tested with probability `(0.98)^6 (0.02)` (in
`(0.0177, 0.0178)`, the book's 0.0177); the expected number tested is `1/p = 50`, the variance is
`(1 - p)/p² = 2450` and the standard deviation lies in `(49.49, 49.5)` (the book's 49.5). -/
@[kb "openstaxintrostats2e" "Example 4.20, p. 258"]
theorem example_4_20_first_defective_component :
    let p : unitInterval := ⟨0.02, by norm_num⟩
    (geometricMeasure p).real {6} = 0.98 ^ 6 * 0.02 ∧
      (0.0177 < (geometricMeasure p).real {6} ∧ (geometricMeasure p).real {6} < 0.0178) ∧
      ∫ n, ((n : ℝ) + 1) ∂geometricMeasure p = 50 ∧
      variance (fun n : ℕ => (n : ℝ) + 1) (geometricMeasure p) = 2450 ∧
      (49.49 < Real.sqrt (variance (fun n : ℕ => (n : ℝ) + 1) (geometricMeasure p)) ∧
        Real.sqrt (variance (fun n : ℕ => (n : ℝ) + 1) (geometricMeasure p)) < 49.5) := by
  intro p
  have hp : p ≠ 0 := by
    intro h
    have := congrArg Subtype.val h
    norm_num [p] at this
  have h1 : (geometricMeasure p).real {6} = 0.98 ^ 6 * 0.02 := by
    rw [geometricMeasure_real_singleton hp]
    simp only [p]; norm_num
  have hv : variance (fun n : ℕ => (n : ℝ) + 1) (geometricMeasure p) = 2450 := by
    rw [UndergradKB.Statistics.variance_geometricMeasure_trials hp]
    simp only [p]; norm_num
  refine ⟨h1, ⟨by rw [h1]; norm_num, by rw [h1]; norm_num⟩, ?_, hv, ?_, ?_⟩
  · rw [UndergradKB.Statistics.integral_geometricMeasure_trials hp]
    simp only [p]; norm_num
  · rw [hv, Real.lt_sqrt (by norm_num)]; norm_num
  · rw [hv, Real.sqrt_lt' (by norm_num)]; norm_num

/-- OpenStax Introductory Statistics 2e Example 4.24. A committee of seven is drawn from 15 men and
18 women: the probability of more than four men is `h(5) + h(6) + h(7) = 117/899`, which is about
0.13 (hypergeometric law with `A = 15`, `B = 18`, `n = 7`). -/
@[kb "openstaxintrostats2e" "Example 4.24, p. 260"]
theorem example_4_24_committee_with_more_than_four_men :
    UndergradKB.Statistics.hypergeometricPMF 15 18 7 5 +
      UndergradKB.Statistics.hypergeometricPMF 15 18 7 6 +
      UndergradKB.Statistics.hypergeometricPMF 15 18 7 7 = 117 / 899 := by
  have c : ∀ n k : ℕ, (Nat.choose n k : ℝ) = (n.descFactorial k : ℝ) / (k.factorial : ℝ) := by
    intro n k
    rw [Nat.choose_eq_descFactorial_div_factorial, Nat.cast_div (Nat.factorial_dvd_descFactorial n k)
      (by positivity)]
  simp only [UndergradKB.Statistics.hypergeometricPMF, c]
  norm_num [Nat.descFactorial, Nat.factorial]

/-- OpenStax Introductory Statistics 2e Example 4.25. A committee of four is drawn from six men and
five women, `X ~ H(6, 5, 4)` counting the men: `P(X = 2) = 5/11 ≈ 0.4545` and the expected number of
men is `n A/(A + B) = 24/11 ≈ 2.18`. -/
@[kb "openstaxintrostats2e" "Example 4.25, p. 261"]
theorem example_4_25_school_site_committee :
    UndergradKB.Statistics.hypergeometricPMF 6 5 4 2 = 5 / 11 ∧
      ∑ x ∈ range (4 + 1), (x : ℝ) * UndergradKB.Statistics.hypergeometricPMF 6 5 4 x = 24 / 11 := by
  refine ⟨?_, ?_⟩
  · simp [UndergradKB.Statistics.hypergeometricPMF, Nat.choose]; norm_num
  · rw [UndergradKB.Statistics.sum_mul_hypergeometricPMF 6 5 4 (by norm_num)]; norm_num

/-- OpenStax Introductory Statistics 2e Example 4.26. A bakery shelves 12 loaves per half hour on
average, i.e. 2 per five minutes: the probability of exactly three loaves in five minutes is
`2³ e⁻² / 3! = (4/3) e⁻²`, which lies in `(0.1804, 0.1805)`. -/
@[kb "openstaxintrostats2e" "Example 4.26, p. 262"]
theorem example_4_26_loaves_in_five_minutes :
    (poissonMeasure 2).real {3} = 4 / 3 * Real.exp (-2) ∧
      (0.1804 < (poissonMeasure 2).real {3} ∧ (poissonMeasure 2).real {3} < 0.1805) := by
  have h : (poissonMeasure 2).real {3} = 4 / 3 * Real.exp (-2) := by
    rw [poissonMeasure_real_singleton]
    simp [Nat.factorial]
    ring
  obtain ⟨h1, h2⟩ := exp_neg_two_bounds
  refine ⟨h, ?_, ?_⟩ <;> rw [h] <;> linarith

/-- OpenStax Introductory Statistics 2e Example 4.27. A bank gets six bad checks a day on average:
the probability of fewer than five is `P(X ≤ 4) = e⁻⁶ (1 + 6 + 18 + 36 + 54) = 115 e⁻⁶`, which lies
in `(0.2849, 0.2852)`. -/
@[kb "openstaxintrostats2e" "Example 4.27, p. 263"]
theorem example_4_27_bad_checks_fewer_than_five :
    (poissonMeasure 6).real (Set.Iic 4) = 115 * Real.exp (-6) ∧
      (0.2849 < (poissonMeasure 6).real (Set.Iic 4) ∧
        (poissonMeasure 6).real (Set.Iic 4) < 0.2852) := by
  have h : (poissonMeasure 6).real (Set.Iic 4) = 115 * Real.exp (-6) := by
    rw [real_Iic]
    simp [Finset.sum_range_succ, poissonMeasure_real_singleton, Nat.factorial]
    ring
  obtain ⟨h1, h2⟩ := exp_neg_six_bounds
  refine ⟨h, ?_, ?_⟩ <;> rw [h] <;> linarith

/-- OpenStax Introductory Statistics 2e Example 4.28. A reporter says "uh" twice per broadcast on
average: the probability of more than two is `1 - e⁻² (1 + 2 + 2) = 1 - 5 e⁻²`, which lies in
`(0.3233, 0.3234)`. -/
@[kb "openstaxintrostats2e" "Example 4.28, p. 263"]
theorem example_4_28_reporter_says_uh :
    (poissonMeasure 2).real (Set.Ioi 2) = 1 - 5 * Real.exp (-2) ∧
      (0.3233 < (poissonMeasure 2).real (Set.Ioi 2) ∧
        (poissonMeasure 2).real (Set.Ioi 2) < 0.3234) := by
  have h : (poissonMeasure 2).real (Set.Ioi 2) = 1 - 5 * Real.exp (-2) := by
    rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, real_Iic]
    simp [Finset.sum_range_succ, poissonMeasure_real_singleton, Nat.factorial]
    ring
  obtain ⟨h1, h2⟩ := exp_neg_two_bounds
  refine ⟨h, ?_, ?_⟩ <;> rw [h] <;> linarith

/-- OpenStax Introductory Statistics 2e Example 4.29. Leah gets 6 calls in two hours, i.e. 0.75 per
quarter hour: the probability of more than one call is `1 - e^(-3/4) (1 + 3/4)`, which lies in
`(0.1733, 0.1735)` (the book's 0.1734). -/
@[kb "openstaxintrostats2e" "Example 4.29, p. 264"]
theorem example_4_29_calls_in_a_quarter_hour :
    (poissonMeasure (3 / 4)).real (Set.Ioi 1) = 1 - Real.exp (-(3 / 4)) * (7 / 4) ∧
      (0.1733 < (poissonMeasure (3 / 4)).real (Set.Ioi 1) ∧
        (poissonMeasure (3 / 4)).real (Set.Ioi 1) < 0.1735) := by
  have h : (poissonMeasure (3 / 4)).real (Set.Ioi 1) = 1 - Real.exp (-(3 / 4)) * (7 / 4) := by
    rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, real_Iic]
    simp [Finset.sum_range_succ, poissonMeasure_real_singleton, Nat.factorial]
    ring_nf
  have hb := Real.exp_bound (x := -(3 / 4)) (by norm_num [abs_of_neg]) (n := 8) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb
  norm_num [abs_le] at hb
  refine ⟨h, ?_, ?_⟩ <;> rw [h] <;> nlinarith [hb.1, hb.2]

/-- OpenStax Introductory Statistics 2e Example 4.30 (standard deviation). An email user gets 147
emails a day on average, `X ~ P(147)`: the variance is 147 and the standard deviation `√147` lies in
`(12.12, 12.13)`. -/
@[kb "openstaxintrostats2e" "Example 4.30, p. 265"]
theorem example_4_30_email_standard_deviation :
    variance (fun n : ℕ => (n : ℝ)) (poissonMeasure 147) = 147 ∧
      (12.12 < Real.sqrt (variance (fun n : ℕ => (n : ℝ)) (poissonMeasure 147)) ∧
        Real.sqrt (variance (fun n : ℕ => (n : ℝ)) (poissonMeasure 147)) < 12.13) := by
  have h : variance (fun n : ℕ => (n : ℝ)) (poissonMeasure 147) = 147 := by
    rw [UndergradKB.Statistics.variance_poissonMeasure]; simp
  refine ⟨h, ?_, ?_⟩
  · rw [h, Real.lt_sqrt (by norm_num)]; norm_num
  · rw [h, Real.sqrt_lt' (by norm_num)]; norm_num

end UndergradKB.Statistics.Course.ExamplesC4
