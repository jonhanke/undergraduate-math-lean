import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Inference
import UndergradKB.Statistics.PValue
import UndergradKB.Statistics.CriticalValues
import UndergradKB.Statistics.NormalCdf

/-!
# Worked examples, chapter 9 and Example 11.10 (OpenStax *Introductory Statistics 2e*): hypotheses and tails

The examples of the hypothesis-testing chapter that only set up hypotheses, errors and tails. Where a
repository definition gives them an honest mathematical statement (the Type I error probability of a
two-sided z test, the p-value as a tail probability, the decision rule "reject when the p-value is below
alpha", a hypothesis about a variance versus the standard deviation) it is stated here.
-/

namespace UndergradKB.Statistics.Course.ExamplesC9b

open MeasureTheory ProbabilityTheory Real Set UndergradKB.Statistics

local notation "Φ" => cdf (gaussianReal 0 1)

/-- The probability of an event described through a variable with law `ν` is `ν.real` of the set. -/
private lemma real_mem_of_hasLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → ℝ}
    {ν : Measure ℝ} (h : HasLaw Z ν P) {S : Set ℝ} (hS : MeasurableSet S) :
    P.real {ω | Z ω ∈ S} = ν.real S := by
  unfold Measure.real
  rw [prob_mem_of_hasLaw h hS]

/-- OpenStax Introductory Statistics 2e Example 9.2. The example only states the hypotheses
`H0 : μ = 2.0` and `Ha : μ ≠ 2.0`; here they are tested by the two-sided z test (normal sample of size `n`,
known `σ`) at the book's default level `α = 0.05`: rejecting when the z statistic exceeds 1.96 in absolute
value has, when the true mean is 2.0, Type I error probability between 0.0499 and 0.0501. -/
@[kb "openstaxintrostats2e" "Example 9.2, p. 475"]
theorem example_9_2_typeI_error {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} {X : Fin n → Ω → ℝ} {σ : ℝ} (hn : 1 ≤ n) (hσ : 0 < σ)
    (hX : IsNormalSample X 2.0 σ P) :
    0.0499 < P.real {ω | 1.96 < |(mean (fun i ↦ X i ω) - 2.0) / (σ / √(n : ℝ))|} ∧
      P.real {ω | 1.96 < |(mean (fun i ↦ X i ω) - 2.0) / (σ / √(n : ℝ))|} < 0.0501 := by
  have h := prob_abs_gt (hasLaw_zStatistic hn hσ hX) 1.96
  have h1 : gaussianReal 0 1 (Icc (-1.96) 1.96) ≤ 1 := prob_le_one
  have e : P.real {ω | 1.96 < |(mean (fun i ↦ X i ω) - 2.0) / (σ / √(n : ℝ))|} =
      1 - (gaussianReal 0 1).real (Ioo (-1.96) 1.96) := by
    rw [Measure.real, h, ENNReal.toReal_sub_of_le h1 ENNReal.one_ne_top,
      measureReal_congr Ioo_ae_eq_Icc]
    simp [Measure.real]
  rw [e]
  obtain ⟨a, b⟩ := critical_values_standard_normal.2.1
  constructor <;> linarith

/-- OpenStax Introductory Statistics 2e Example 9.10. The decision rule "reject when the p-value is below
alpha": for a level `α` whose critical value is `c` (the standard normal mass of `[-c, c]` is `1 - α`), the
two-sided p-value of a statistic `z` is below `α` exactly when `|z| > c` (reject), and is at least `α`
exactly when `|z| ≤ c` (do not reject). -/
@[kb "openstaxintrostats2e" "Example 9.10, p. 481"]
theorem example_9_10_reject_iff_p_small {c α : ℝ} (h0 : 0 < α) (h1 : α < 1)
    (hz : gaussianReal 0 1 (Icc (-c) c) = ENNReal.ofReal (1 - α)) (z : ℝ) :
    (zPValue z < α ↔ c < |z|) ∧ (α ≤ zPValue z ↔ |z| ≤ c) := by
  have h := zPValue_lt_iff h0 h1 hz z
  exact ⟨h, by rw [← not_lt, h, not_lt]⟩

/-- OpenStax Introductory Statistics 2e Example 9.11. For `H0 : μ = 5` against `Ha : μ < 5` (left-tailed),
with a normal sample of known `σ`: the p-value of an observed z statistic `z₀` is the left tail
`P(z-statistic ≤ z₀) = Φ(z₀)` computed under `H0`. -/
@[kb "openstaxintrostats2e" "Example 9.11, p. 482"]
theorem example_9_11_left_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} {X : Fin n → Ω → ℝ} {σ : ℝ} (hn : 1 ≤ n) (hσ : 0 < σ)
    (hX : IsNormalSample X 5 σ P) (z₀ : ℝ) :
    P.real {ω | (mean (fun i ↦ X i ω) - 5) / (σ / √(n : ℝ)) ≤ z₀} = Φ z₀ := by
  have h := real_mem_of_hasLaw (hasLaw_zStatistic hn hσ hX) (measurableSet_Iic (a := z₀))
  simp only [mem_Iic] at h
  rw [h, cdf_eq_real]

/-- OpenStax Introductory Statistics 2e Example 9.12. For a right-tailed test (`H0 : p ≤ 0.2` against
`Ha : p > 0.2`), with the standardised statistic `Z` standard normal under the boundary value `p = 0.2`: the
p-value of an observed value `z₀` is the right tail `P(Z > z₀) = 1 - Φ(z₀)`. -/
@[kb "openstaxintrostats2e" "Example 9.12, p. 482"]
theorem example_9_12_right_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) P) (z₀ : ℝ) :
    P.real {ω | z₀ < Z ω} = 1 - Φ z₀ := by
  have h := real_mem_of_hasLaw hZ (measurableSet_Ioi (a := z₀))
  simp only [mem_Ioi] at h
  rw [h, gaussianReal_real_Ioi]

/-- OpenStax Introductory Statistics 2e Example 9.13. For a two-tailed test (`H0 : μ = 50`,
`Ha : μ ≠ 50`) with a normal sample of known `σ`: the p-value of an observed z statistic `z₀` is the
probability, under `H0`, of a statistic at least as far from zero as `z₀`; it is the sum of the left tail
below `-|z₀|` and the right tail above `|z₀|`, and these two tails are equal. -/
@[kb "openstaxintrostats2e" "Example 9.13, p. 482"]
theorem example_9_13_two_tails {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} {X : Fin n → Ω → ℝ} {σ : ℝ} (hn : 1 ≤ n) (hσ : 0 < σ)
    (hX : IsNormalSample X 50 σ P) (z₀ : ℝ) :
    P.real {ω | |z₀| < |(mean (fun i ↦ X i ω) - 50) / (σ / √(n : ℝ))|} = zPValue z₀ ∧
    zPValue z₀ = (gaussianReal 0 1).real (Iio (-|z₀|)) + (gaussianReal 0 1).real (Ioi |z₀|) ∧
    (gaussianReal 0 1).real (Iio (-|z₀|)) = (gaussianReal 0 1).real (Ioi |z₀|) := by
  have h := prob_abs_gt (hasLaw_zStatistic hn hσ hX) |z₀|
  have h1 : gaussianReal 0 1 (Icc (-|z₀|) |z₀|) ≤ 1 := prob_le_one
  have hc := gaussianReal_real_Icc |z₀| (abs_nonneg _)
  have e : P.real {ω | |z₀| < |(mean (fun i ↦ X i ω) - 50) / (σ / √(n : ℝ))|} = zPValue z₀ := by
    rw [Measure.real, h, ENNReal.toReal_sub_of_le h1 ENNReal.one_ne_top]
    have : (gaussianReal 0 1 (Icc (-|z₀|) |z₀|)).toReal = 1 - 2 * (1 - Φ |z₀|) := hc
    rw [this, zPValue]
    simp
  have hs := gaussianReal_real_Iio_neg |z₀|
  refine ⟨e, ?_, hs⟩
  rw [zPValue_eq_two_mul_tail, hs]
  ring

/-- OpenStax Introductory Statistics 2e Example 11.10. For a standard deviation `σ ≥ 0`, the null
hypothesis `σ² = 5²` is the claim `σ = 5`, and the alternative `σ² > 5²` is the claim `σ > 5`: working with
the variance loses nothing. -/
@[kb "openstaxintrostats2e" "Example 11.10, p. 594"]
theorem example_11_10_variance_hypotheses {σ : ℝ} (hσ : 0 ≤ σ) :
    (σ ^ 2 = 5 ^ 2 ↔ σ = 5) ∧ (5 ^ 2 < σ ^ 2 ↔ 5 < σ) := by
  constructor
  · constructor <;> intro h <;> nlinarith
  · constructor <;> intro h <;> nlinarith

end UndergradKB.Statistics.Course.ExamplesC9b
