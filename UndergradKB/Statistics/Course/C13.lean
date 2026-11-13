import UndergradKB.Statistics.Anova
import UndergradKB.Statistics.AnovaTest
import UndergradKB.Statistics.FDistribution
import UndergradKB.Statistics.Inference
import UndergradKB.Common.Attr

/-!
# Course layer, chapter 13 (OpenStax *Introductory Statistics 2e*): the F distribution and
one-way ANOVA
-/

namespace UndergradKB.Statistics.Course.C13

open MeasureTheory ProbabilityTheory Set UndergradKB.Statistics

/-- OpenStax Introductory Statistics 2e §13.2 (ST-114). One-way decomposition of variation:
`SS_total = SS_between + SS_within`, with `SS_between = ∑ nⱼ (x̄ⱼ - x̄)²`. -/
@[kb "openstaxintrostats2e" "§13.2, p. 691"]
theorem sum_of_squares_total_eq_between_plus_within {n k : ℕ} (x : Fin n → ℝ) (g : Fin n → Fin k) :
    sumSqDev x = ssBetween x g + ssWithin x g :=
  sumSqDev_eq_ssBetween_add_ssWithin x g

/-- OpenStax Introductory Statistics 2e §13.2 (ST-115). Under `H₀` (equal means; independent normal
observations with a common `σ`, every group nonempty, `2 ≤ k < n`), the statistic
`F = MS_between / MS_within` has the F distribution with `k - 1` and `n - k` degrees of freedom. -/
@[kb "openstaxintrostats2e" "§13.2, p. 691"]
theorem anova_f_statistic_law {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n k : ℕ} (g : Fin n → Fin k) (hg : ∀ j, 0 < groupSize g j)
    (hk : 2 ≤ k) (hkn : k < n) {Y : Fin n → Ω → ℝ} {μ σ : ℝ} (hσ : 0 < σ)
    (hY : IsNormalSample Y μ σ P) :
    HasLaw (fun ω ↦ fStatistic (fun i ↦ Y i ω) g) (fDistribution ((k : ℝ) - 1) ((n : ℝ) - k)) P :=
  hasLaw_fStatistic g hg hk hkn hσ hY

/-- OpenStax Introductory Statistics 2e §13.3 (ST-116). The F distribution is the law of a ratio
of two independent chi-square variables, each divided by its degrees of freedom:
`(U/d₁) / (V/d₂)` has the F distribution with `d₁` and `d₂` degrees of freedom. -/
@[kb "openstaxintrostats2e" "§13.3, p. 695"]
theorem f_distribution_is_ratio_of_chi_squares {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {U V : Ω → ℝ} {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hU : HasLaw U (chiSquared d₁) P) (hV : HasLaw V (chiSquared d₂) P)
    (hind : IndepFun U V P) :
    HasLaw (fun ω ↦ (U ω / d₁) / (V ω / d₂)) (fDistribution d₁ d₂) P :=
  hasLaw_fDistribution hd₁ hd₂ hU hV hind

/-- OpenStax Introductory Statistics 2e §13.3 (ST-116). The F distribution is nonnegative: it puts
no mass on `(-∞, 0]`. -/
@[kb "openstaxintrostats2e" "§13.3, p. 695"]
theorem f_distribution_nonnegative (d₁ d₂ : ℝ) : fDistribution d₁ d₂ (Iic 0) = 0 :=
  fDistribution_Iic_zero d₁ d₂

/-- OpenStax Introductory Statistics 2e §13.4 (ST-117). Test of two variances: for independent
normal samples of sizes `n₁, n₂ ≥ 2`, `(s₁²/σ₁²) / (s₂²/σ₂²)` has the F distribution with `n₁ - 1`
and `n₂ - 1` degrees of freedom (under `H₀`, `σ₁ = σ₂`, this is `s₁²/s₂²`). -/
@[kb "openstaxintrostats2e" "§13.4, p. 701"]
theorem two_variances_f_statistic_law {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n₁ n₂ : ℕ} {X : Fin n₁ → Ω → ℝ} {Y : Fin n₂ → Ω → ℝ}
    {μ₁ μ₂ σ₁ σ₂ : ℝ} (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂) (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂)
    (hX : IsNormalSample X μ₁ σ₁ P) (hY : IsNormalSample Y μ₂ σ₂ P)
    (hind : IndepFun (fun ω i ↦ X i ω) (fun ω j ↦ Y j ω) P) :
    HasLaw (fun ω ↦ (sampleVariance (fun i ↦ X i ω) / σ₁ ^ 2) /
        (sampleVariance (fun j ↦ Y j ω) / σ₂ ^ 2))
      (fDistribution ((n₁ : ℝ) - 1) ((n₂ : ℝ) - 1)) P :=
  hasLaw_varianceRatio hn₁ hn₂ hσ₁ hσ₂ hX hY hind

/-- OpenStax Introductory Statistics 2e §13.4 (ST-117). The reciprocal of an F variable is F with
the degrees of freedom swapped, so the ratio of variances may be taken either way round. -/
@[kb "openstaxintrostats2e" "§13.4, p. 701"]
theorem reciprocal_of_f_statistic_law {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {U V : Ω → ℝ} {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hU : HasLaw U (chiSquared d₁) P) (hV : HasLaw V (chiSquared d₂) P)
    (hind : IndepFun U V P) :
    HasLaw (fun ω ↦ ((U ω / d₁) / (V ω / d₂))⁻¹) (fDistribution d₂ d₁) P :=
  hasLaw_inv_fDistribution hd₁ hd₂ hU hV hind

end UndergradKB.Statistics.Course.C13
