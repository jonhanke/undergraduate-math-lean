import Mathlib.Probability.CDF
import Mathlib.Probability.Density
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Distributions.Exponential
import UndergradKB.Common.Attr

/-!
# Course layer, chapter 5 (OpenStax *Introductory Statistics 2e*): continuous distributions
-/

namespace UndergradKB.Statistics.Course.C5

open MeasureTheory ProbabilityTheory

/-- OpenStax Introductory Statistics 2e §5.1 (ST-048). A continuous random variable (a law
without atoms) gives probability zero to each single value. -/
@[kb "openstaxintrostats2e" "§5.1, p. 303"]
theorem prob_single_value_eq_zero {μ : Measure ℝ} [NullSingletonClass μ] (x : ℝ) :
    μ {x} = 0 :=
  measure_singleton x

/-- OpenStax Introductory Statistics 2e §5.1 (ST-048). The density of a random variable with a
density has total area equal to the total probability, `1` for a probability law. -/
@[kb "openstaxintrostats2e" "§5.1, p. 303"]
theorem density_total_area {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}
    [HasPDF X P volume] :
    ∫⁻ x, pdf X P volume x = P Set.univ :=
  pdf.lintegral_eq_measure_univ

/-- OpenStax Introductory Statistics 2e §5.1 (ST-049). The cumulative distribution function
`F(x) = P(X ≤ x)` is nondecreasing with limits 0 at `-∞` and 1 at `+∞`. -/
@[kb "openstaxintrostats2e" "§5.1, p. 303"]
theorem cdf_monotone_with_limits (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Monotone (cdf μ) ∧ Filter.Tendsto (cdf μ) Filter.atBot (nhds 0) ∧
      Filter.Tendsto (cdf μ) Filter.atTop (nhds 1) :=
  ⟨monotone_cdf μ, tendsto_cdf_atBot μ, tendsto_cdf_atTop μ⟩

/-- OpenStax Introductory Statistics 2e §5.2 (ST-050). Uniform distribution on `[a, b]`:
for `a ≤ c ≤ d ≤ b`, `P(c < X < d) = (d - c) / (b - a)`. -/
@[kb "openstaxintrostats2e" "§5.2, p. 306"]
theorem uniform_interval_probability {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : Ω → ℝ} {a b c d : ℝ} (hX : pdf.IsUniform X (Set.Icc a b) P volume)
    (hac : a ≤ c) (hdb : d ≤ b) :
    P (X ⁻¹' Set.Ioo c d) = ENNReal.ofReal (d - c) / ENNReal.ofReal (b - a) := by
  rw [hX.measure_preimage measurableSet_Ioo]
  have : Set.Icc a b ∩ Set.Ioo c d = Set.Ioo c d :=
    Set.inter_eq_right.2 (Set.Ioo_subset_Icc_self.trans (Set.Icc_subset_Icc hac hdb))
  rw [this, Real.volume_Ioo, Real.volume_Icc]

/-- OpenStax Introductory Statistics 2e §5.3 (ST-053). The exponential density `m e^(-m x)` on
`x ≥ 0` has total area 1. -/
@[kb "openstaxintrostats2e" "§5.3, p. 313"]
theorem exponential_density_total_area {m : ℝ} (hm : 0 < m) :
    ∫⁻ x, exponentialPDF m x = 1 :=
  lintegral_exponentialPDF_eq_one hm

/-- OpenStax Introductory Statistics 2e §5.3 (ST-054). Exponential distribution function:
`P(X ≤ x) = 1 - e^(-m x)` for `x ≥ 0` (and 0 below). -/
@[kb "openstaxintrostats2e" "§5.3, p. 313"]
theorem exponential_cdf {m : ℝ} (hm : 0 < m) (x : ℝ) :
    cdf (expMeasure m) x = if 0 ≤ x then 1 - Real.exp (-(m * x)) else 0 :=
  cdf_expMeasure_eq hm x

end UndergradKB.Statistics.Course.C5
