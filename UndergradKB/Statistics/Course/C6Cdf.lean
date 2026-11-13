import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF
import UndergradKB.Common.Attr
import UndergradKB.Statistics.NormalCdf

/-!
# Course layer, chapter 6 (continued): the standard normal distribution function
-/

namespace UndergradKB.Statistics.Course.C6Cdf

open MeasureTheory ProbabilityTheory UndergradKB.Statistics

/-- OpenStax Introductory Statistics 2e §6.2 (ST-061). The standard normal distribution function
`Φ` (the z-table) is continuous, strictly increasing, tends to `0` at `-∞` and to `1` at `+∞`, and
takes only values strictly between `0` and `1`. -/
@[kb "openstaxintrostats2e" "§6.2, p. 351"]
theorem z_table_properties :
    Continuous (cdf (gaussianReal 0 1)) ∧ StrictMono (cdf (gaussianReal 0 1)) ∧
      Filter.Tendsto (cdf (gaussianReal 0 1)) Filter.atBot (nhds 0) ∧
      Filter.Tendsto (cdf (gaussianReal 0 1)) Filter.atTop (nhds 1) ∧
      ∀ z, 0 < cdf (gaussianReal 0 1) z ∧ cdf (gaussianReal 0 1) z < 1 :=
  stdNormalCdf_properties

/-- OpenStax Introductory Statistics 2e §6.2 (ST-061). Symmetry of the z-table:
`Φ(-z) = 1 - Φ(z)`. -/
@[kb "openstaxintrostats2e" "§6.2, p. 351"]
theorem z_table_symmetry (z : ℝ) :
    cdf (gaussianReal 0 1) (-z) = 1 - cdf (gaussianReal 0 1) z :=
  stdNormalCdf_neg z

/-- OpenStax Introductory Statistics 2e §6.2 (ST-061). The z-score `z_p` of the `p`-th percentile
satisfies `Φ(z_p) = p` for `0 < p < 1`, and it is the only number with this property. -/
@[kb "openstaxintrostats2e" "§6.2, p. 351"]
theorem inverse_z_table_right_inverse {p : ℝ} (h0 : 0 < p) (h1 : p < 1) :
    cdf (gaussianReal 0 1) (normalQuantile p) = p ∧
      ∀ z, cdf (gaussianReal 0 1) z = p → z = normalQuantile p :=
  stdNormalCdf_normalQuantile h0 h1

/-- OpenStax Introductory Statistics 2e §6.2 (ST-061). Looking up `Φ(z)` in the z-table and then
inverting returns the starting z-score. -/
@[kb "openstaxintrostats2e" "§6.2, p. 351"]
theorem inverse_z_table_left_inverse (z : ℝ) :
    normalQuantile (cdf (gaussianReal 0 1) z) = z :=
  normalQuantile_stdNormalCdf z

/-- OpenStax Introductory Statistics 2e §6.2 (ST-061). Normal probabilities from the z-table: if
`X ~ N(μ, σ²)` with `σ > 0`, then `P(X ≤ x) = Φ((x - μ)/σ)`. -/
@[kb "openstaxintrostats2e" "§6.2, p. 351"]
theorem normal_probability_at_most {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : Ω → ℝ} {μ σ : ℝ} (hσ : 0 < σ) (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P)
    (x : ℝ) :
    P.real {ω | X ω ≤ x} = cdf (gaussianReal 0 1) ((x - μ) / σ) :=
  prob_le_normal hσ hX x

/-- OpenStax Introductory Statistics 2e §6.2 (ST-061). Normal probability of an interval:
`P(a < X ≤ b) = Φ((b - μ)/σ) - Φ((a - μ)/σ)` for `X ~ N(μ, σ²)`, `σ > 0`. -/
@[kb "openstaxintrostats2e" "§6.2, p. 351"]
theorem normal_probability_between {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : Ω → ℝ} {μ σ : ℝ} (hσ : 0 < σ) (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P)
    (a b : ℝ) (hab : a ≤ b) :
    P.real {ω | a < X ω ∧ X ω ≤ b} =
      cdf (gaussianReal 0 1) ((b - μ) / σ) - cdf (gaussianReal 0 1) ((a - μ) / σ) :=
  prob_Ioc_normal hσ hX a b hab

/-- OpenStax Introductory Statistics 2e §6.2 (ST-061). Percentiles of a normal variable from the
inverse z-table: for `X ~ N(μ, σ²)`, `σ > 0` and `0 < p < 1`, the number `x` with `P(X ≤ x) = p`
exists, is unique, and equals `μ + σ z_p`, where `z_p` is the z-score of the `p`-th percentile. -/
@[kb "openstaxintrostats2e" "§6.2, p. 351"]
theorem normal_percentile_formula {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : Ω → ℝ} {μ σ : ℝ} (hσ : 0 < σ) (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P)
    {p : ℝ} (h0 : 0 < p) (h1 : p < 1) :
    (P.real {ω | X ω ≤ μ + σ * normalQuantile p} = p) ∧
      ∀ x, P.real {ω | X ω ≤ x} = p → x = μ + σ * normalQuantile p :=
  normal_percentile hσ hX h0 h1

end UndergradKB.Statistics.Course.C6Cdf
