import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF
import Mathlib.Data.Fin.VecNotation
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Data
import UndergradKB.Statistics.Inference
import UndergradKB.Statistics.PValue
import UndergradKB.Statistics.NormalCdf
import UndergradKB.Statistics.CriticalValues

/-!
# Course layer, chapter 9 (OpenStax *Introductory Statistics 2e*): Try It exercises

One-sample hypothesis tests. As in the worked examples, a `z` test models the sample statistic as a
normal variable under the null hypothesis; we prove two-sided bounds on the test statistic and on the
p-value (through enclosures of the standard normal distribution function `Φ`) and the decision. For
the `t` tests only the statistic is proved and compared with the book's table value (not proved).

Skipped, being purely verbal (hypotheses or errors in words, or a drawing of a p-value): Try It 9.1,
9.3, 9.4, 9.5, 9.6, 9.7, 9.8. Try It 9.2 and 9.9 to 9.13 get the honest mathematical content that
the repository has (Type I error of a two-sided z test, p-value as a tail probability, decision rule).
-/

namespace UndergradKB.Statistics.Course.TryItC9

open MeasureTheory ProbabilityTheory Real Set UndergradKB.Statistics

local notation "Φ" => cdf (gaussianReal 0 1)

/-- Rational Taylor sums used in the `Φ` enclosures. -/
macro "tryit_emp_tac" : tactic =>
  `(tactic| (simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial]))

private lemma Phi_gt {k z a : ℝ} (hk : 0 ≤ k) (m : ℕ) (ha : 0 < a) (hz : k ≤ z)
    (hl : a * 2.5067 < 2 * empR (2 * m) k) : 1 / 2 + a / 2 < Φ z := by
  have h : a < (gaussianReal 0 1).real (Ioo (-k) k) := by
    rw [gaussianReal_real_Ioo_eq hk]
    have hl' := le_integral_gauss m hk
    have s1 := sqrt_two_pi_gt
    have s2 := sqrt_two_pi_lt
    have hp : 0 < √(2 * π) := by linarith
    rw [lt_div_iff₀ hp]; nlinarith
  have h1 := stdNormalCdf_eq_Ioo hk
  have h2 : Φ k ≤ Φ z := (cdf (gaussianReal 0 1)).mono hz
  linarith

private lemma Phi_lt {k z b : ℝ} (hk : 0 ≤ k) (m : ℕ) (hb : 0 < b) (hz : z ≤ k)
    (hu : 2 * empR (2 * m + 1) k < b * 2.5066) : Φ z < 1 / 2 + b / 2 := by
  have h : (gaussianReal 0 1).real (Ioo (-k) k) < b := by
    rw [gaussianReal_real_Ioo_eq hk]
    have hu' := integral_gauss_le m hk
    have s1 := sqrt_two_pi_gt
    have s2 := sqrt_two_pi_lt
    have hp : 0 < √(2 * π) := by linarith
    rw [div_lt_iff₀ hp]; nlinarith
  have h1 := stdNormalCdf_eq_Ioo hk
  have h2 : Φ z ≤ Φ k := (cdf (gaussianReal 0 1)).mono hz
  linarith

private lemma Phi_neg_lt {k z a : ℝ} (hk : 0 ≤ k) (m : ℕ) (ha : 0 < a) (hz : z ≤ -k)
    (hl : a * 2.5067 < 2 * empR (2 * m) k) : Φ z < 1 / 2 - a / 2 := by
  have h := Phi_gt hk m ha (le_refl k) hl
  have h2 : Φ z ≤ Φ (-k) := (cdf (gaussianReal 0 1)).mono hz
  have h3 := stdNormalCdf_neg k
  linarith

private lemma Phi_neg_gt {k z b : ℝ} (hk : 0 ≤ k) (m : ℕ) (hb : 0 < b) (hz : -k ≤ z)
    (hu : 2 * empR (2 * m + 1) k < b * 2.5066) : 1 / 2 - b / 2 < Φ z := by
  have h := Phi_lt hk m hb (le_refl k) hu
  have h2 : Φ (-k) ≤ Φ z := (cdf (gaussianReal 0 1)).mono hz
  have h3 := stdNormalCdf_neg k
  linarith

/-- Right-tail probability of a normal variable: `P(X > x) = 1 - Φ((x - μ)/σ)`. -/
private lemma real_gt_normal {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}
    {μ σ : ℝ} (hσ : 0 < σ) (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) (x : ℝ) :
    P.real {ω | x < X ω} = 1 - Φ ((x - μ) / σ) := by
  have e : {ω | x < X ω} = {ω | X ω ≤ x}ᶜ := by
    ext ω; simp
  have hm : NullMeasurableSet {ω | X ω ≤ x} P :=
    hX.aemeasurable.nullMeasurable measurableSet_Iic
  have : IsProbabilityMeasure P := hX.isProbabilityMeasure_iff.2 inferInstance
  rw [e, probReal_compl_eq_one_sub₀ hm, prob_le_normal hσ hX]

/-- The probability of an event described through a variable with law `ν` is `ν.real` of the set. -/
private lemma real_mem_of_hasLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → ℝ}
    {ν : Measure ℝ} (h : HasLaw Z ν P) {S : Set ℝ} (hS : MeasurableSet S) :
    P.real {ω | Z ω ∈ S} = ν.real S := by
  unfold Measure.real
  rw [prob_mem_of_hasLaw h hS]

/-! ### Hypotheses, errors and tails -/

/-- OpenStax Introductory Statistics 2e Try It 9.2. The exercise asks for the hypotheses
`H0 : μ = 66` against `Ha : μ ≠ 66` in words and symbols; here they are tested by the two-sided z test
(normal sample of size `n`, known `σ`) at the book's default level `α = 0.05`: rejecting when the z
statistic exceeds 1.96 in absolute value has, when the true mean is 66, Type I error probability between
0.0499 and 0.0501. -/
@[kb "openstaxintrostats2e" "Try It 9.2, p. 475"]
theorem tryit_9_2_typeI_error {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} {X : Fin n → Ω → ℝ} {σ : ℝ} (hn : 1 ≤ n) (hσ : 0 < σ)
    (hX : IsNormalSample X 66 σ P) :
    0.0499 < P.real {ω | 1.96 < |(mean (fun i ↦ X i ω) - 66) / (σ / √(n : ℝ))|} ∧
      P.real {ω | 1.96 < |(mean (fun i ↦ X i ω) - 66) / (σ / √(n : ℝ))|} < 0.0501 := by
  have h := prob_abs_gt (hasLaw_zStatistic hn hσ hX) 1.96
  have h1 : gaussianReal 0 1 (Icc (-1.96) 1.96) ≤ 1 := prob_le_one
  have e : P.real {ω | 1.96 < |(mean (fun i ↦ X i ω) - 66) / (σ / √(n : ℝ))|} =
      1 - (gaussianReal 0 1).real (Ioo (-1.96) 1.96) := by
    rw [Measure.real, h, ENNReal.toReal_sub_of_le h1 ENNReal.one_ne_top,
      measureReal_congr Ioo_ae_eq_Icc]
    simp [Measure.real]
  rw [e]
  obtain ⟨a, b⟩ := critical_values_standard_normal.2.1
  constructor <;> linarith

/-- OpenStax Introductory Statistics 2e Try It 9.9. Standard deviation `1`, `n = 36`, null mean `12`
against `μ > 12`, observed sample mean `12.5`. If the sample mean `X` is normal with mean `12` and
standard deviation `1/√36`, the `z` statistic is exactly `3` and the right-tail p-value `P(X > 12.5)`
lies in `(0.0013, 0.0014)` (the book quotes `0.0013`; the exact value is about `0.00135`). The
drawing the exercise asks for is not formalized. -/
@[kb "openstaxintrostats2e" "Try It 9.9, p. 480"]
theorem tryit_9_9_right_tail_p_value {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : Ω → ℝ} (hX : HasLaw X (gaussianReal 12 (((1 : ℝ) / √36) ^ 2).toNNReal) P) :
    (12.5 - 12) / (1 / √(36 : ℝ)) = 3 ∧
      (0.0013 < P.real {ω | 12.5 < X ω} ∧ P.real {ω | 12.5 < X ω} < 0.0014) := by
  have h6 : √(36 : ℝ) = 6 := by
    rw [show (36 : ℝ) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hσ : 0 < (1 : ℝ) / √36 := by positivity
  have hz : (12.5 - 12) / (1 / √(36 : ℝ)) = 3 := by rw [h6]; norm_num
  have hp := real_gt_normal hσ hX 12.5
  rw [hz] at hp
  have u := Phi_gt (k := 3) (z := 3) (a := 0.9972) (by norm_num) 14 (by norm_num) le_rfl
    (by tryit_emp_tac)
  have l := Phi_lt (k := 3) (z := 3) (b := 0.9974) (by norm_num) 14 (by norm_num) le_rfl
    (by tryit_emp_tac)
  refine ⟨hz, ?_, ?_⟩ <;> rw [hp] <;> linarith

/-- OpenStax Introductory Statistics 2e Try It 9.10. With `α = 0.01` and p-value `0.025` the decision
rule "reject when the p-value is below `α`" does not reject: `α ≤ p-value`. (The plain-language
conclusion the exercise asks for is not formalized.) -/
@[kb "openstaxintrostats2e" "Try It 9.10, p. 481"]
theorem tryit_9_10_do_not_reject :
    (0.01 : ℝ) ≤ 0.025 ∧ ¬ ((0.025 : ℝ) < 0.01) := by
  constructor <;> norm_num

/-- OpenStax Introductory Statistics 2e Try It 9.11. For `H0 : μ = 10` against `Ha : μ < 10`
(left-tailed), with a normal sample of known `σ`: the p-value of an observed z statistic `z₀` is the
left tail `P(z-statistic ≤ z₀) = Φ(z₀)` computed under `H0`. -/
@[kb "openstaxintrostats2e" "Try It 9.11, p. 482"]
theorem tryit_9_11_left_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} {X : Fin n → Ω → ℝ} {σ : ℝ} (hn : 1 ≤ n) (hσ : 0 < σ)
    (hX : IsNormalSample X 10 σ P) (z₀ : ℝ) :
    P.real {ω | (mean (fun i ↦ X i ω) - 10) / (σ / √(n : ℝ)) ≤ z₀} = Φ z₀ := by
  have h := real_mem_of_hasLaw (hasLaw_zStatistic hn hσ hX) (measurableSet_Iic (a := z₀))
  simp only [mem_Iic] at h
  rw [h, cdf_eq_real]

/-- OpenStax Introductory Statistics 2e Try It 9.12. For `H0 : μ ≤ 1` against `Ha : μ > 1`
(right-tailed), with a normal sample of known `σ`: the p-value of an observed z statistic `z₀` is the
right tail `P(z-statistic > z₀) = 1 - Φ(z₀)` computed under the boundary value `μ = 1`. -/
@[kb "openstaxintrostats2e" "Try It 9.12, p. 482"]
theorem tryit_9_12_right_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} {X : Fin n → Ω → ℝ} {σ : ℝ} (hn : 1 ≤ n) (hσ : 0 < σ)
    (hX : IsNormalSample X 1 σ P) (z₀ : ℝ) :
    P.real {ω | z₀ < (mean (fun i ↦ X i ω) - 1) / (σ / √(n : ℝ))} = 1 - Φ z₀ := by
  have h := real_mem_of_hasLaw (hasLaw_zStatistic hn hσ hX) (measurableSet_Ioi (a := z₀))
  simp only [mem_Ioi] at h
  rw [h, gaussianReal_real_Ioi]

/-- OpenStax Introductory Statistics 2e Try It 9.13. For a two-tailed test (`H0 : p = 0.5`,
`Ha : p ≠ 0.5`) with the standardised statistic `Z` standard normal under `H0`: the p-value of an
observed value `z₀` is the probability of a statistic at least as far from zero as `z₀`; it is the sum of
the left tail below `-|z₀|` and the right tail above `|z₀|`, and these two tails are equal. -/
@[kb "openstaxintrostats2e" "Try It 9.13, p. 483"]
theorem tryit_9_13_two_tails {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P) (z₀ : ℝ) :
    P.real {ω | |z₀| < |Z ω|} = zPValue z₀ ∧
    zPValue z₀ = (gaussianReal 0 1).real (Iio (-|z₀|)) + (gaussianReal 0 1).real (Ioi |z₀|) ∧
    (gaussianReal 0 1).real (Iio (-|z₀|)) = (gaussianReal 0 1).real (Ioi |z₀|) := by
  have h := prob_abs_gt hZ |z₀|
  have h1 : gaussianReal 0 1 (Icc (-|z₀|) |z₀|) ≤ 1 := prob_le_one
  have hc := gaussianReal_real_Icc |z₀| (abs_nonneg _)
  have e : P.real {ω | |z₀| < |Z ω|} = zPValue z₀ := by
    rw [Measure.real, h, ENNReal.toReal_sub_of_le h1 ENNReal.one_ne_top]
    have : (gaussianReal 0 1 (Icc (-|z₀|) |z₀|)).toReal = 1 - 2 * (1 - Φ |z₀|) := hc
    rw [this, zPValue]
    simp
  have hs := gaussianReal_real_Iio_neg |z₀|
  refine ⟨e, ?_, hs⟩
  rw [zPValue_eq_two_mul_tail, hs]
  ring

/-! ### Tests of a mean -/

/-- OpenStax Introductory Statistics 2e Try It 9.14. Throwing distances with known `σ = 2`, `n = 20`,
null mean `40`, observed sample mean `45`. If the sample mean `X` is normal with mean `40` and standard
deviation `2/√20`, the `z` statistic lies in `(11.18, 11.19)`, the right-tail p-value `P(X > 45)` is
below `0.0014`, hence below `α = 0.05`, so `H0` is rejected. -/
@[kb "openstaxintrostats2e" "Try It 9.14, p. 484"]
theorem tryit_9_14_football_z_test {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : Ω → ℝ} (hX : HasLaw X (gaussianReal 40 (((2 : ℝ) / √20) ^ 2).toNNReal) P) :
    (11.18 < (45 - 40) / (2 / √(20 : ℝ)) ∧ (45 - 40) / (2 / √(20 : ℝ)) < 11.19) ∧
    P.real {ω | 45 < X ω} < 0.0014 ∧ P.real {ω | 45 < X ω} < 0.05 := by
  have hs1 : 4.4721 < √(20 : ℝ) := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hs2 : √(20 : ℝ) < 4.4722 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hσ : 0 < (2 : ℝ) / √20 := by positivity
  have hz : (45 - 40) / (2 / √(20 : ℝ)) = 5 / 2 * √20 := by
    rw [div_div_eq_mul_div]; ring
  have hp := real_gt_normal hσ hX 45
  have u := Phi_gt (k := 3) (z := (45 - 40) / (2 / √(20 : ℝ))) (a := 0.9972) (by norm_num) 14
    (by norm_num) (by rw [hz]; linarith) (by tryit_emp_tac)
  refine ⟨⟨by rw [hz]; linarith, by rw [hz]; linarith⟩, ?_, ?_⟩ <;> rw [hp] <;> linarith

/-- OpenStax Introductory Statistics 2e Try It 9.15. Twenty working times (frequencies expanded) have
mean exactly `951/2 = 475.5`. With known `σ = 45` and null mean `475`, the `z` statistic lies in
`(0.0496, 0.0498)`; if the sample mean is normal with mean `475` and standard deviation `45/√20`, the
right-tail p-value `P(X > x̄)` lies in `(0.480, 0.481)`, which exceeds `α = 0.025`, so `H0` is not
rejected. -/
@[kb "openstaxintrostats2e" "Try It 9.15, p. 487"]
theorem tryit_9_15_working_time_z_test {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : Ω → ℝ} (hX : HasLaw X (gaussianReal 475 (((45 : ℝ) / √20) ^ 2).toNNReal) P) :
    let x : Fin 20 → ℝ := ![460, 460, 460, 465, 465, 470, 470, 470, 475, 480, 480, 480, 480, 480,
      480, 485, 485, 485, 490, 490]
    mean x = 951 / 2 ∧
    (0.0496 < (mean x - 475) / (45 / √(20 : ℝ)) ∧ (mean x - 475) / (45 / √(20 : ℝ)) < 0.0498) ∧
    (0.480 < P.real {ω | mean x < X ω} ∧ P.real {ω | mean x < X ω} < 0.481) ∧
    0.025 < P.real {ω | mean x < X ω} := by
  intro x
  have hm : mean x = 951 / 2 := by simp [mean, x, Fin.sum_univ_succ]; norm_num
  have hs1 : 4.4721 < √(20 : ℝ) := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hs2 : √(20 : ℝ) < 4.4722 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hσ : 0 < (45 : ℝ) / √20 := by positivity
  have hz : ((951 / 2 : ℝ) - 475) / (45 / √(20 : ℝ)) = √20 / 90 := by
    rw [div_div_eq_mul_div]; ring
  have hz1 : 0.0496 ≤ ((951 / 2 : ℝ) - 475) / (45 / √(20 : ℝ)) := by rw [hz]; linarith
  have hz2 : ((951 / 2 : ℝ) - 475) / (45 / √(20 : ℝ)) ≤ 0.0498 := by rw [hz]; linarith
  have hp := real_gt_normal hσ hX (mean x)
  rw [hm] at hp ⊢
  have u := Phi_gt (k := 0.0496) (z := ((951 / 2 : ℝ) - 475) / (45 / √(20 : ℝ))) (a := 0.0395)
    (by norm_num) 6 (by norm_num) hz1 (by tryit_emp_tac)
  have l := Phi_lt (k := 0.0498) (z := ((951 / 2 : ℝ) - 475) / (45 / √(20 : ℝ))) (b := 0.04)
    (by norm_num) 6 (by norm_num) hz2 (by tryit_emp_tac)
  refine ⟨rfl, ⟨by linarith, by linarith⟩, ⟨?_, ?_⟩, ?_⟩ <;> rw [hp] <;> linarith

/-- OpenStax Introductory Statistics 2e Try It 9.16 (with the stated standard deviation `1` taken as
known). Ten weekly stock-price changes have mean exactly `2.6`; the null growth is `5` and the
alternative is a smaller rate. If the sample mean `X` is normal with mean `5` and standard deviation
`1/√10`, the `z` statistic lies in `(-7.6, -7.58)`, the left-tail p-value `P(X ≤ x̄)` is below `0.0014`,
hence below `α = 0.05`, and `H0` is rejected. -/
@[kb "openstaxintrostats2e" "Try It 9.16, p. 488"]
theorem tryit_9_16_stock_z_test {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : Ω → ℝ} (hX : HasLaw X (gaussianReal 5 (((1 : ℝ) / √10) ^ 2).toNNReal) P) :
    let x : Fin 10 → ℝ := ![4, 3, 2, 3, 1, 7, 2, 1, 1, 2]
    mean x = 13 / 5 ∧
    (-7.6 < (mean x - 5) / (1 / √(10 : ℝ)) ∧ (mean x - 5) / (1 / √(10 : ℝ)) < -7.58) ∧
    P.real {ω | X ω ≤ mean x} < 0.0014 ∧ P.real {ω | X ω ≤ mean x} < 0.05 := by
  intro x
  have hm : mean x = 13 / 5 := by simp [mean, x, Fin.sum_univ_succ]; norm_num
  have hs1 : 3.1622 < √(10 : ℝ) := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hs2 : √(10 : ℝ) < 3.1623 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hσ : 0 < (1 : ℝ) / √10 := by positivity
  have hz : ((13 / 5 : ℝ) - 5) / (1 / √(10 : ℝ)) = -(12 / 5 * √10) := by
    rw [div_div_eq_mul_div]; ring
  have hp := prob_le_normal hσ hX (mean x)
  rw [hm] at hp ⊢
  have u := Phi_neg_lt (k := 3) (z := ((13 / 5 : ℝ) - 5) / (1 / √(10 : ℝ))) (a := 0.9972)
    (by norm_num) 14 (by norm_num) (by rw [hz]; linarith) (by tryit_emp_tac)
  refine ⟨rfl, ⟨by rw [hz]; linarith, by rw [hz]; linarith⟩, ?_, ?_⟩ <;> rw [hp] <;> linarith

/-- OpenStax Introductory Statistics 2e Try It 9.16 (the `t` version, standard deviation estimated
from the data). Ten weekly stock-price changes have mean exactly `13/5`, sample variance exactly
`152/45`, standard deviation in `(1.8378, 1.8379)`, and the `t` statistic against `μ₀ = 5` lies in
`(-4.13, -4.12)`. It is below `-1.833`, the book's table value for a left-tailed test at `5%` with `9`
degrees of freedom (a table constant, not proved), so `H0` is rejected. -/
@[kb "openstaxintrostats2e" "Try It 9.16, p. 488"]
theorem tryit_9_16_stock_t_test :
    let x : Fin 10 → ℝ := ![4, 3, 2, 3, 1, 7, 2, 1, 1, 2]
    mean x = 13 / 5 ∧ sampleVariance x = 152 / 45 ∧
      (1.8378 < sampleStdDev x ∧ sampleStdDev x < 1.8379) ∧
      (-4.13 < (mean x - 5) / (sampleStdDev x / √(10 : ℝ)) ∧
        (mean x - 5) / (sampleStdDev x / √(10 : ℝ)) < -4.12) ∧
      (mean x - 5) / (sampleStdDev x / √(10 : ℝ)) < -1.833 := by
  intro x
  have hm : mean x = 13 / 5 := by simp [mean, x, Fin.sum_univ_succ]; norm_num
  have hv : sampleVariance x = 152 / 45 := by
    simp only [sampleVariance, sumSqDev, hm]
    simp [x, Fin.sum_univ_succ]
    norm_num
  have hs1 : 1.8378 < sampleStdDev x := by
    rw [sampleStdDev, hv]; exact (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hs2 : sampleStdDev x < 1.8379 := by
    rw [sampleStdDev, hv]; exact (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have h1 : 3.1622 < √(10 : ℝ) := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have h2 : √(10 : ℝ) < 3.1623 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hq : 0 < sampleStdDev x / √(10 : ℝ) := by
    have : 0 < √(10 : ℝ) := by linarith
    have : 0 < sampleStdDev x := by linarith
    positivity
  have d1 : 1.8378 / 3.1623 < sampleStdDev x / √(10 : ℝ) := by
    rw [div_lt_div_iff₀ (by norm_num) (by linarith)]; nlinarith
  have d2 : sampleStdDev x / √(10 : ℝ) < 1.8379 / 3.1622 := by
    rw [div_lt_div_iff₀ (by linarith) (by norm_num)]; nlinarith
  have t1 : -4.13 < (mean x - 5) / (sampleStdDev x / √(10 : ℝ)) := by
    rw [hm, lt_div_iff₀ hq]; norm_num at d1 d2 ⊢; linarith
  have t2 : (mean x - 5) / (sampleStdDev x / √(10 : ℝ)) < -4.12 := by
    rw [hm, div_lt_iff₀ hq]; norm_num at d1 d2 ⊢; linarith
  exact ⟨hm, hv, ⟨hs1, hs2⟩, ⟨t1, t2⟩, by linarith⟩

/-- OpenStax Introductory Statistics 2e Try It 9.20. Fifteen boiling points have mean exactly `3032/15`
(about `202.13`), sample variance exactly `2158/105`, standard deviation in `(4.5334, 4.5335)`, and the
`t` statistic against `μ₀ = 200` lies in `(1.822, 1.823)`. It exceeds `1.345`, the book's table value
for a right-tailed test at `α = 0.1` with `14` degrees of freedom (a table constant, not proved), so
`H0` is rejected: there is evidence that the mean boiling point exceeds `200`. -/
@[kb "openstaxintrostats2e" "Try It 9.20, p. 493"]
theorem tryit_9_20_boiling_point_t_test :
    let x : Fin 15 → ℝ := ![205, 206, 206, 202, 199, 194, 197, 198, 198, 201, 201, 202, 207, 211, 205]
    mean x = 3032 / 15 ∧ sampleVariance x = 2158 / 105 ∧
      (4.5334 < sampleStdDev x ∧ sampleStdDev x < 4.5335) ∧
      (1.822 < (mean x - 200) / (sampleStdDev x / √(15 : ℝ)) ∧
        (mean x - 200) / (sampleStdDev x / √(15 : ℝ)) < 1.823) ∧
      1.345 < (mean x - 200) / (sampleStdDev x / √(15 : ℝ)) := by
  intro x
  have hm : mean x = 3032 / 15 := by simp [mean, x, Fin.sum_univ_succ]; norm_num
  have hv : sampleVariance x = 2158 / 105 := by
    simp only [sampleVariance, sumSqDev, hm]
    simp [x, Fin.sum_univ_succ]
    norm_num
  have hs1 : 4.5334 < sampleStdDev x := by
    rw [sampleStdDev, hv]; exact (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hs2 : sampleStdDev x < 4.5335 := by
    rw [sampleStdDev, hv]; exact (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have h1 : 3.8729 < √(15 : ℝ) := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have h2 : √(15 : ℝ) < 3.873 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hq : 0 < sampleStdDev x / √(15 : ℝ) := by
    have : 0 < √(15 : ℝ) := by linarith
    have : 0 < sampleStdDev x := by linarith
    positivity
  have d1 : 4.5334 / 3.873 < sampleStdDev x / √(15 : ℝ) := by
    rw [div_lt_div_iff₀ (by norm_num) (by linarith)]; nlinarith
  have d2 : sampleStdDev x / √(15 : ℝ) < 4.5335 / 3.8729 := by
    rw [div_lt_div_iff₀ (by linarith) (by norm_num)]; nlinarith
  have t1 : 1.822 < (mean x - 200) / (sampleStdDev x / √(15 : ℝ)) := by
    rw [hm, lt_div_iff₀ hq]; norm_num at d1 d2 ⊢; linarith
  have t2 : (mean x - 200) / (sampleStdDev x / √(15 : ℝ)) < 1.823 := by
    rw [hm, div_lt_iff₀ hq]; norm_num at d1 d2 ⊢; linarith
  exact ⟨hm, hv, ⟨hs1, hs2⟩, ⟨t1, t2⟩, by linarith⟩

/-! ### Tests of a proportion -/

/-- OpenStax Introductory Statistics 2e Try It 9.17. `39` of `50` students want the trip, null
`p = 0.85`, two-sided. If the sample proportion `X` is normal with mean `0.85` and standard deviation
`√(0.85 · 0.15 / 50)`, the `z` statistic lies in `(-1.3865, -1.386)`, the two-sided p-value
`P(X ≤ 39/50) + P(X > 2 · 0.85 - 39/50)` lies in `(0.165, 0.167)`, which exceeds `α = 0.01`, so `H0` is
not rejected. -/
@[kb "openstaxintrostats2e" "Try It 9.17, p. 489"]
theorem tryit_9_17_field_trip_proportion_test {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {X : Ω → ℝ}
    (hX : HasLaw X (gaussianReal 0.85 ((Real.sqrt (0.85 * (1 - 0.85) / 50)) ^ 2).toNNReal) P) :
    (-1.3865 < (39 / 50 - 0.85) / Real.sqrt (0.85 * (1 - 0.85) / 50) ∧
      (39 / 50 - 0.85) / Real.sqrt (0.85 * (1 - 0.85) / 50) < -1.386) ∧
    (0.165 < P.real {ω | X ω ≤ 39 / 50} + P.real {ω | 2 * 0.85 - 39 / 50 < X ω} ∧
      P.real {ω | X ω ≤ 39 / 50} + P.real {ω | 2 * 0.85 - 39 / 50 < X ω} < 0.167) ∧
    0.01 < P.real {ω | X ω ≤ 39 / 50} + P.real {ω | 2 * 0.85 - 39 / 50 < X ω} := by
  have hs1 : 0.05049 < Real.sqrt (0.85 * (1 - 0.85) / 50) :=
    (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hs2 : Real.sqrt (0.85 * (1 - 0.85) / 50) < 0.0505 :=
    (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hσ : 0 < Real.sqrt (0.85 * (1 - 0.85) / 50) := by linarith
  have hz1 : -1.3865 < (39 / 50 - 0.85) / Real.sqrt (0.85 * (1 - 0.85) / 50) := by
    rw [lt_div_iff₀ hσ]; linarith
  have hz2 : (39 / 50 - 0.85) / Real.sqrt (0.85 * (1 - 0.85) / 50) < -1.386 := by
    rw [div_lt_iff₀ hσ]; linarith
  have h1 := prob_le_normal hσ hX (39 / 50)
  have h2 := real_gt_normal hσ hX (2 * 0.85 - 39 / 50)
  have e2 : (2 * (0.85 : ℝ) - 39 / 50 - 0.85) / Real.sqrt (0.85 * (1 - 0.85) / 50) =
      -((39 / 50 - 0.85) / Real.sqrt (0.85 * (1 - 0.85) / 50)) := by
    rw [← neg_div]; congr 1; ring
  rw [e2] at h2
  have h3 := stdNormalCdf_neg ((39 / 50 - 0.85) / Real.sqrt (0.85 * (1 - 0.85) / 50))
  have u := Phi_neg_lt (k := 1.386) (z := (39 / 50 - 0.85) / Real.sqrt (0.85 * (1 - 0.85) / 50))
    (a := 0.833) (by norm_num) 10 (by norm_num) hz2.le (by tryit_emp_tac)
  have l := Phi_neg_gt (k := 1.3865) (z := (39 / 50 - 0.85) / Real.sqrt (0.85 * (1 - 0.85) / 50))
    (b := 0.835) (by norm_num) 10 (by norm_num) hz1.le (by tryit_emp_tac)
  refine ⟨⟨hz1, hz2⟩, ⟨?_, ?_⟩, ?_⟩ <;> rw [h1, h2] <;> linarith

/-- OpenStax Introductory Statistics 2e Try It 9.18. `174` of `200` adults own a cell phone, null
`p = 0.92`, alternative `p < 0.92`. If the sample proportion `X` is normal with mean `0.92` and standard
deviation `√(0.92 · 0.08 / 200)`, the `z` statistic lies in `(-2.607, -2.606)`, the left-tail p-value
`P(X ≤ 174/200)` lies in `(0.0045, 0.0047)`, and it is below `α = 0.05`, so `H0` is rejected. -/
@[kb "openstaxintrostats2e" "Try It 9.18, p. 490"]
theorem tryit_9_18_cell_phone_ownership_test {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {X : Ω → ℝ}
    (hX : HasLaw X (gaussianReal 0.92 ((Real.sqrt (0.92 * (1 - 0.92) / 200)) ^ 2).toNNReal) P) :
    (-2.607 < (174 / 200 - 0.92) / Real.sqrt (0.92 * (1 - 0.92) / 200) ∧
      (174 / 200 - 0.92) / Real.sqrt (0.92 * (1 - 0.92) / 200) < -2.606) ∧
    (0.0045 < P.real {ω | X ω ≤ 174 / 200} ∧ P.real {ω | X ω ≤ 174 / 200} < 0.0047) ∧
    P.real {ω | X ω ≤ 174 / 200} < 0.05 := by
  have hs1 : 0.019183 < Real.sqrt (0.92 * (1 - 0.92) / 200) :=
    (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hs2 : Real.sqrt (0.92 * (1 - 0.92) / 200) < 0.019184 :=
    (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hσ : 0 < Real.sqrt (0.92 * (1 - 0.92) / 200) := by linarith
  have hz1 : -2.607 < (174 / 200 - 0.92) / Real.sqrt (0.92 * (1 - 0.92) / 200) := by
    rw [lt_div_iff₀ hσ]; linarith
  have hz2 : (174 / 200 - 0.92) / Real.sqrt (0.92 * (1 - 0.92) / 200) < -2.606 := by
    rw [div_lt_iff₀ hσ]; linarith
  have h1 := prob_le_normal hσ hX (174 / 200)
  have u := Phi_neg_lt (k := 2.606) (z := (174 / 200 - 0.92) / Real.sqrt (0.92 * (1 - 0.92) / 200))
    (a := 0.9906) (by norm_num) 14 (by norm_num) hz2.le (by tryit_emp_tac)
  have l := Phi_neg_gt (k := 2.607) (z := (174 / 200 - 0.92) / Real.sqrt (0.92 * (1 - 0.92) / 200))
    (b := 0.991) (by norm_num) 14 (by norm_num) hz1.le (by tryit_emp_tac)
  refine ⟨⟨hz1, hz2⟩, ⟨?_, ?_⟩, ?_⟩ <;> rw [h1] <;> linarith

/-- OpenStax Introductory Statistics 2e Try It 9.19. `20` of `50` stains washed out, null `p = 0.30`,
alternative `p > 0.30` (the new compound is beneficial). If the sample proportion `X` is normal with
mean `0.3` and standard deviation `√(0.3 · 0.7 / 50)`, the `z` statistic lies in `(1.542, 1.544)`, the
right-tail p-value `P(X > 20/50)` lies in `(0.061, 0.062)`, and it exceeds `α = 0.01`, so `H0` is not
rejected. -/
@[kb "openstaxintrostats2e" "Try It 9.19, p. 492"]
theorem tryit_9_19_car_soap_test {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {X : Ω → ℝ}
    (hX : HasLaw X (gaussianReal 0.3 ((Real.sqrt (0.3 * (1 - 0.3) / 50)) ^ 2).toNNReal) P) :
    (1.542 < (20 / 50 - 0.3) / Real.sqrt (0.3 * (1 - 0.3) / 50) ∧
      (20 / 50 - 0.3) / Real.sqrt (0.3 * (1 - 0.3) / 50) < 1.544) ∧
    (0.061 < P.real {ω | 20 / 50 < X ω} ∧ P.real {ω | 20 / 50 < X ω} < 0.062) ∧
    0.01 < P.real {ω | 20 / 50 < X ω} := by
  have hs1 : 0.0648 < Real.sqrt (0.3 * (1 - 0.3) / 50) :=
    (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hs2 : Real.sqrt (0.3 * (1 - 0.3) / 50) < 0.06481 :=
    (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hσ : 0 < Real.sqrt (0.3 * (1 - 0.3) / 50) := by linarith
  have hz1 : 1.542 < (20 / 50 - 0.3) / Real.sqrt (0.3 * (1 - 0.3) / 50) := by
    rw [lt_div_iff₀ hσ]; linarith
  have hz2 : (20 / 50 - 0.3) / Real.sqrt (0.3 * (1 - 0.3) / 50) < 1.544 := by
    rw [div_lt_iff₀ hσ]; linarith
  have h2 := real_gt_normal hσ hX (20 / 50)
  have u := Phi_gt (k := 1.542) (z := (20 / 50 - 0.3) / Real.sqrt (0.3 * (1 - 0.3) / 50))
    (a := 0.876) (by norm_num) 12 (by norm_num) hz1.le (by tryit_emp_tac)
  have l := Phi_lt (k := 1.544) (z := (20 / 50 - 0.3) / Real.sqrt (0.3 * (1 - 0.3) / 50))
    (b := 0.878) (by norm_num) 12 (by norm_num) hz2.le (by tryit_emp_tac)
  refine ⟨⟨hz1, hz2⟩, ⟨?_, ?_⟩, ?_⟩ <;> rw [h2] <;> linarith

/-- OpenStax Introductory Statistics 2e Try It 9.21. `138` skin diseases among `390000` moisturizer
users, null rate `0.00041`, alternative a greater rate. If the sample proportion `X` is normal with mean
`0.00041` and standard deviation `√(0.00041 · 0.99959 / 390000)`, the `z` statistic lies in
`(-1.733, -1.731)` (the observed rate is below the null rate), the right-tail p-value `P(X > 138/390000)`
lies in `(0.958, 0.959)`, and it exceeds `α = 0.005`, so `H0` is not rejected. The explanation of the
low significance level asked for is not formalized. -/
@[kb "openstaxintrostats2e" "Try It 9.21, p. 494"]
theorem tryit_9_21_moisturizer_test {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {X : Ω → ℝ}
    (hX : HasLaw X (gaussianReal 0.00041
      ((Real.sqrt (0.00041 * (1 - 0.00041) / 390000)) ^ 2).toNNReal) P) :
    (-1.733 < (138 / 390000 - 0.00041) / Real.sqrt (0.00041 * (1 - 0.00041) / 390000) ∧
      (138 / 390000 - 0.00041) / Real.sqrt (0.00041 * (1 - 0.00041) / 390000) < -1.731) ∧
    (0.958 < P.real {ω | 138 / 390000 < X ω} ∧ P.real {ω | 138 / 390000 < X ω} < 0.959) ∧
    0.005 < P.real {ω | 138 / 390000 < X ω} := by
  have hs1 : 0.00003241 < Real.sqrt (0.00041 * (1 - 0.00041) / 390000) :=
    (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hs2 : Real.sqrt (0.00041 * (1 - 0.00041) / 390000) < 0.00003242 :=
    (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hσ : 0 < Real.sqrt (0.00041 * (1 - 0.00041) / 390000) := by linarith
  have hz1 : -1.733 < (138 / 390000 - 0.00041) / Real.sqrt (0.00041 * (1 - 0.00041) / 390000) := by
    rw [lt_div_iff₀ hσ]; linarith
  have hz2 : (138 / 390000 - 0.00041) / Real.sqrt (0.00041 * (1 - 0.00041) / 390000) < -1.731 := by
    rw [div_lt_iff₀ hσ]; linarith
  have h2 := real_gt_normal hσ hX (138 / 390000)
  have u := Phi_neg_lt (k := 1.731)
    (z := (138 / 390000 - 0.00041) / Real.sqrt (0.00041 * (1 - 0.00041) / 390000))
    (a := 0.916) (by norm_num) 12 (by norm_num) hz2.le (by tryit_emp_tac)
  have l := Phi_neg_gt (k := 1.733)
    (z := (138 / 390000 - 0.00041) / Real.sqrt (0.00041 * (1 - 0.00041) / 390000))
    (b := 0.918) (by norm_num) 12 (by norm_num) hz1.le (by tryit_emp_tac)
  refine ⟨⟨hz1, hz2⟩, ⟨?_, ?_⟩, ?_⟩ <;> rw [h2] <;> linarith

/-- OpenStax Introductory Statistics 2e Try It 9.22. `127` murders among `427648` Ohio residents,
national rate `0.00052`, two-sided. If the sample proportion `X` is normal with mean `0.00052` and
standard deviation `√(0.00052 · 0.99948 / 427648)`, the `z` statistic lies in `(-6.4, -6.39)`, the
two-sided p-value `P(X ≤ 127/427648) + P(X > 2 · 0.00052 - 127/427648)` is below `0.0028` (the exact
value is about `1.6e-10`), hence below `α = 0.01`, so `H0` is rejected. -/
@[kb "openstaxintrostats2e" "Try It 9.22, p. 495"]
theorem tryit_9_22_ohio_murder_rate_test {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {X : Ω → ℝ}
    (hX : HasLaw X (gaussianReal 0.00052
      ((Real.sqrt (0.00052 * (1 - 0.00052) / 427648)) ^ 2).toNNReal) P) :
    (-6.4 < (127 / 427648 - 0.00052) / Real.sqrt (0.00052 * (1 - 0.00052) / 427648) ∧
      (127 / 427648 - 0.00052) / Real.sqrt (0.00052 * (1 - 0.00052) / 427648) < -6.39) ∧
    P.real {ω | X ω ≤ 127 / 427648} + P.real {ω | 2 * 0.00052 - 127 / 427648 < X ω} < 0.0028 ∧
    P.real {ω | X ω ≤ 127 / 427648} + P.real {ω | 2 * 0.00052 - 127 / 427648 < X ω} < 0.01 := by
  have hs1 : 0.00003486 < Real.sqrt (0.00052 * (1 - 0.00052) / 427648) :=
    (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hs2 : Real.sqrt (0.00052 * (1 - 0.00052) / 427648) < 0.00003487 :=
    (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hσ : 0 < Real.sqrt (0.00052 * (1 - 0.00052) / 427648) := by linarith
  have hz1 : -6.4 < (127 / 427648 - 0.00052) / Real.sqrt (0.00052 * (1 - 0.00052) / 427648) := by
    rw [lt_div_iff₀ hσ]; linarith
  have hz2 : (127 / 427648 - 0.00052) / Real.sqrt (0.00052 * (1 - 0.00052) / 427648) < -6.39 := by
    rw [div_lt_iff₀ hσ]; linarith
  have h1 := prob_le_normal hσ hX (127 / 427648)
  have h2 := real_gt_normal hσ hX (2 * 0.00052 - 127 / 427648)
  have e2 : (2 * (0.00052 : ℝ) - 127 / 427648 - 0.00052) /
      Real.sqrt (0.00052 * (1 - 0.00052) / 427648) =
      -((127 / 427648 - 0.00052) / Real.sqrt (0.00052 * (1 - 0.00052) / 427648)) := by
    rw [← neg_div]; congr 1; ring
  rw [e2] at h2
  have h3 := stdNormalCdf_neg ((127 / 427648 - 0.00052) / Real.sqrt (0.00052 * (1 - 0.00052) / 427648))
  have u := Phi_neg_lt (k := 3)
    (z := (127 / 427648 - 0.00052) / Real.sqrt (0.00052 * (1 - 0.00052) / 427648))
    (a := 0.9972) (by norm_num) 14 (by norm_num) (by linarith) (by tryit_emp_tac)
  refine ⟨⟨hz1, hz2⟩, ?_, ?_⟩ <;> rw [h1, h2] <;> linarith

end UndergradKB.Statistics.Course.TryItC9
