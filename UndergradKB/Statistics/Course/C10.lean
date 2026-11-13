import UndergradKB.Statistics.Inference
import UndergradKB.Statistics.TwoProportions
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Welch
import UndergradKB.Statistics.TwoSample
import UndergradKB.Statistics.SampleMoments

/-!
# Course layer, chapter 10 (OpenStax *Introductory Statistics 2e*): two samples and paired data
-/

namespace UndergradKB.Statistics.Course.C10

open MeasureTheory ProbabilityTheory UndergradKB.Statistics

section TwoIndependent

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n₁ n₂ : ℕ} {X : Fin n₁ → Ω → ℝ} {Y : Fin n₂ → Ω → ℝ} {μ₁ μ₂ σ₁ σ₂ : ℝ}

/-- OpenStax Introductory Statistics 2e §10.1 (ST-091). For independent normal samples, the
difference of the sample means `x̄₁ - x̄₂` is normal with mean `μ₁ - μ₂` and variance
`σ₁²/n₁ + σ₂²/n₂`. -/
@[kb "openstaxintrostats2e" "§10.1, p. 523"]
theorem difference_of_sample_means_law (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂) (hσ₁ : 0 < σ₁)
    (hσ₂ : 0 < σ₂) (hX : IsNormalSample X μ₁ σ₁ P) (hY : IsNormalSample Y μ₂ σ₂ P)
    (hind : IndepFun (fun ω i ↦ X i ω) (fun ω j ↦ Y j ω) P) :
    HasLaw (fun ω ↦ mean (fun i ↦ X i ω) - mean (fun j ↦ Y j ω))
      (gaussianReal (μ₁ - μ₂) (σ₁ ^ 2 / n₁ + σ₂ ^ 2 / n₂).toNNReal) P :=
  hasLaw_diffMeans hn₁ hn₂ hσ₁ hσ₂ hX hY hind

/-- OpenStax Introductory Statistics 2e §10.2 (ST-092). Two independent means with known standard
deviations: `z = ((x̄₁ - x̄₂) - (μ₁ - μ₂)) / √(σ₁²/n₁ + σ₂²/n₂)` is standard normal. -/
@[kb "openstaxintrostats2e" "§10.2, p. 531"]
theorem two_sample_z_statistic_law (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂) (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂)
    (hX : IsNormalSample X μ₁ σ₁ P) (hY : IsNormalSample Y μ₂ σ₂ P)
    (hind : IndepFun (fun ω i ↦ X i ω) (fun ω j ↦ Y j ω) P) :
    HasLaw (fun ω ↦ ((mean (fun i ↦ X i ω) - mean (fun j ↦ Y j ω)) - (μ₁ - μ₂)) /
      √(σ₁ ^ 2 / n₁ + σ₂ ^ 2 / n₂)) (gaussianReal 0 1) P :=
  hasLaw_twoSampleZ hn₁ hn₂ hσ₁ hσ₂ hX hY hind

/-- OpenStax Introductory Statistics 2e §10.1 (ST-090). Welch degrees of freedom: for independent
normal samples of sizes `n₁, n₂ ≥ 2`, the estimate `V = s₁²/n₁ + s₂²/n₂` of the variance of
`x̄₁ - x̄₂` is matched in mean and variance by a scaled chi-square variable with `ν > 0` degrees of
freedom exactly when `ν` is the Welch degrees of freedom. -/
@[kb "openstaxintrostats2e" "§10.1, p. 523"]
theorem welch_degrees_of_freedom_match_moments (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂) (hσ₁ : 0 < σ₁)
    (hσ₂ : 0 < σ₂) (hX : IsNormalSample X μ₁ σ₁ P) (hY : IsNormalSample Y μ₂ σ₂ P)
    (hind : IndepFun (fun ω i ↦ X i ω) (fun ω j ↦ Y j ω) P) {ν : ℝ} (hν : 0 < ν) :
    2 * (∫ ω, (sampleVariance (fun i ↦ X i ω) / n₁ + sampleVariance (fun j ↦ Y j ω) / n₂) ∂P) ^ 2 / ν =
        variance (fun ω ↦ sampleVariance (fun i ↦ X i ω) / n₁ + sampleVariance (fun j ↦ Y j ω) / n₂) P ↔
      ν = welchDF (σ₁ ^ 2) (σ₂ ^ 2) n₁ n₂ :=
  welch_moment_matching hn₁ hn₂ hσ₁ hσ₂ hX hY hind hν

end TwoIndependent

/-- OpenStax Introductory Statistics 2e §10.1 (ST-090). The Welch degrees of freedom lie between
`min(n₁, n₂) - 1` and `n₁ + n₂ - 2`. -/
@[kb "openstaxintrostats2e" "§10.1, p. 523"]
theorem welch_degrees_of_freedom_bounds {v₁ v₂ : ℝ} {n₁ n₂ : ℕ} (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂)
    (h₁ : 0 < v₁) (h₂ : 0 < v₂) :
    ((min n₁ n₂ : ℕ) : ℝ) - 1 ≤ welchDF v₁ v₂ n₁ n₂ ∧
      welchDF v₁ v₂ n₁ n₂ ≤ (n₁ : ℝ) + n₂ - 2 :=
  welchDF_bounds hn₁ hn₂ h₁ h₂

/-- OpenStax Introductory Statistics 2e §10.4 (ST-094). Matched pairs: if the differences
`dᵢ = xᵢ - yᵢ` form a normal sample with mean `μ_d`, then `t = (d̄ - μ_d) / (s_d / √n)` has the
Student t distribution with `n - 1` degrees of freedom. -/
@[kb "openstaxintrostats2e" "§10.4, p. 538"]
theorem matched_pairs_t_statistic_law {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} {X Y : Fin n → Ω → ℝ} {μd σd : ℝ} (hn : 2 ≤ n)
    (hσ : 0 < σd) (hD : IsNormalSample (fun i ω ↦ X i ω - Y i ω) μd σd P) :
    HasLaw (fun ω ↦ (mean (fun i ↦ X i ω - Y i ω) - μd) /
      (sampleStdDev (fun i ↦ X i ω - Y i ω) / √(n : ℝ))) (studentT ((n : ℝ) - 1)) P :=
  hasLaw_pairedTStatistic hn hσ hD

/-- OpenStax Introductory Statistics 2e §10.3 (ST-093). Two independent population proportions:
with Bernoulli trials `X` (success probability `p_A`) and `Y` (success probability `p_B`), all
independent, and sample sizes `n_A = a n`, `n_B = b n` in a fixed ratio, the standardized difference
`((p'_A - p'_B) - (p_A - p_B)) / √(p_A q_A / n_A + p_B q_B / n_B)` is approximately standard normal:
it converges in distribution to `N(0, 1)` as `n → ∞`. -/
@[kb "openstaxintrostats2e" "§10.3, p. 534"]
theorem difference_of_proportions_approx_normal {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] {X Y : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) {pA pB : ℝ} (hA0 : 0 < pA) (hA1 : pA < 1)
    (hB0 : 0 < pB) (hB1 : pB < 1) (hZ : HasLaw Z (gaussianReal 0 1) P')
    (hmX : ∀ i, Measurable (X i)) (hmY : ∀ i, Measurable (Y i))
    (h01X : ∀ i ω, X i ω = 0 ∨ X i ω = 1) (h01Y : ∀ i ω, Y i ω = 0 ∨ Y i ω = 1)
    (hprobA : P.real {ω | X 0 ω = 1} = pA) (hprobB : P.real {ω | Y 0 ω = 1} = pB)
    (hindep : iIndepFun (Sum.elim X Y) P)
    (hidentX : ∀ i, IdentDistrib (X i) (X 0) P P) (hidentY : ∀ i, IdentDistrib (Y i) (Y 0) P P) :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦
        ((∑ i ∈ Finset.range (a * n), X i ω) / ((a * n : ℕ) : ℝ) -
            (∑ j ∈ Finset.range (b * n), Y j ω) / ((b * n : ℕ) : ℝ) - (pA - pB)) /
          √(pA * (1 - pA) / ((a * n : ℕ) : ℝ) + pB * (1 - pB) / ((b * n : ℕ) : ℝ)))
      Filter.atTop Z (fun _ ↦ P) P' :=
  tendstoInDistribution_two_proportions ha hb hA0 hA1 hB0 hB1 hZ hmX hmY h01X h01Y hprobA hprobB
    hindep hidentX hidentY

/-- OpenStax Introductory Statistics 2e §10.2 (ST-092). Two independent samples of arbitrary sizes:
for independent populations A and B with means `μ_A, μ_B`, positive standard deviations `σ_A, σ_B`
and finite variances, if both sample sizes tend to infinity in any manner, the standardized
difference `((x̄_A - x̄_B) - (μ_A - μ_B)) / √(σ_A²/n_A + σ_B²/n_B)` converges in distribution to
`N(0, 1)`. -/
@[kb "openstaxintrostats2e" "§10.2, p. 531"]
theorem two_sample_means_approx_normal {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {X Y : ℕ → Ω → ℝ} {Z : Ω' → ℝ} {μA μB σA σB : ℝ} (hσA : 0 < σA) (hσB : 0 < σB)
    (hZ : HasLaw Z (gaussianReal 0 1) P')
    (hLX : MemLp (X 0) 2 P) (hLY : MemLp (Y 0) 2 P)
    (hμA : P[X 0] = μA) (hμB : P[Y 0] = μB) (hvA : Var[X 0; P] = σA ^ 2)
    (hvB : Var[Y 0; P] = σB ^ 2) (hindep : iIndepFun (Sum.elim X Y) P)
    (hidentX : ∀ i, IdentDistrib (X i) (X 0) P P) (hidentY : ∀ i, IdentDistrib (Y i) (Y 0) P P)
    {nA nB : ℕ → ℕ} (hnA : Filter.Tendsto nA Filter.atTop Filter.atTop)
    (hnB : Filter.Tendsto nB Filter.atTop Filter.atTop) :
    TendstoInDistribution
      (fun k ω ↦ ((∑ i ∈ Finset.range (nA k), X i ω) / nA k -
          (∑ j ∈ Finset.range (nB k), Y j ω) / nB k - (μA - μB)) /
          √(σA ^ 2 / nA k + σB ^ 2 / nB k))
      Filter.atTop Z (fun _ ↦ P) P' :=
  tendstoInDistribution_two_sample_means hσA hσB hZ hLX hLY hμA hμB hvA hvB hindep hidentX
    hidentY hnA hnB

/-- OpenStax Introductory Statistics 2e §10.3 (ST-093). Two proportions with arbitrary sample sizes:
for independent 0/1 samples with success probabilities `p_A, p_B` strictly between 0 and 1, if both
sample sizes tend to infinity in any manner, `((p'_A - p'_B) - (p_A - p_B)) / √(p_A q_A/n_A +
p_B q_B/n_B)` converges in distribution to `N(0, 1)`. -/
@[kb "openstaxintrostats2e" "§10.3, p. 534"]
theorem difference_of_proportions_approx_normal_sizes {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] {X Y : ℕ → Ω → ℝ} {Z : Ω' → ℝ} {pA pB : ℝ} (hA0 : 0 < pA)
    (hA1 : pA < 1) (hB0 : 0 < pB) (hB1 : pB < 1) (hZ : HasLaw Z (gaussianReal 0 1) P')
    (hmX : ∀ i, Measurable (X i)) (hmY : ∀ i, Measurable (Y i))
    (h01X : ∀ i ω, X i ω = 0 ∨ X i ω = 1) (h01Y : ∀ i ω, Y i ω = 0 ∨ Y i ω = 1)
    (hprobA : P.real {ω | X 0 ω = 1} = pA) (hprobB : P.real {ω | Y 0 ω = 1} = pB)
    (hindep : iIndepFun (Sum.elim X Y) P)
    (hidentX : ∀ i, IdentDistrib (X i) (X 0) P P) (hidentY : ∀ i, IdentDistrib (Y i) (Y 0) P P)
    {nA nB : ℕ → ℕ} (hnA : Filter.Tendsto nA Filter.atTop Filter.atTop)
    (hnB : Filter.Tendsto nB Filter.atTop Filter.atTop) :
    TendstoInDistribution
      (fun k ω ↦ ((∑ i ∈ Finset.range (nA k), X i ω) / nA k -
          (∑ j ∈ Finset.range (nB k), Y j ω) / nB k - (pA - pB)) /
          √(pA * (1 - pA) / nA k + pB * (1 - pB) / nB k))
      Filter.atTop Z (fun _ ↦ P) P' :=
  tendstoInDistribution_two_proportions_sizes hA0 hA1 hB0 hB1 hZ hmX hmY h01X h01Y hprobA hprobB
    hindep hidentX hidentY hnA hnB

/-- OpenStax Introductory Statistics 2e §10.3 (ST-093). Pooled two-proportion test: under the null
hypothesis `p_A = p_B = p` with `0 < p < 1`, the test statistic
`z = (p'_A - p'_B) / √(p_c (1 - p_c) (1/n_A + 1/n_B))`, where `p_c = (x_A + x_B)/(n_A + n_B)` is the
pooled proportion, converges in distribution to `N(0, 1)` as both sample sizes tend to infinity. -/
@[kb "openstaxintrostats2e" "§10.3, p. 534"]
theorem pooled_two_proportion_z_approx_normal {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] {X Y : ℕ → Ω → ℝ} {Z : Ω' → ℝ} {p : ℝ} (h0 : 0 < p) (h1 : p < 1)
    (hZ : HasLaw Z (gaussianReal 0 1) P')
    (hmX : ∀ i, Measurable (X i)) (hmY : ∀ i, Measurable (Y i))
    (h01X : ∀ i ω, X i ω = 0 ∨ X i ω = 1) (h01Y : ∀ i ω, Y i ω = 0 ∨ Y i ω = 1)
    (hprobA : P.real {ω | X 0 ω = 1} = p) (hprobB : P.real {ω | Y 0 ω = 1} = p)
    (hindep : iIndepFun (Sum.elim X Y) P)
    (hidentX : ∀ i, IdentDistrib (X i) (X 0) P P) (hidentY : ∀ i, IdentDistrib (Y i) (Y 0) P P)
    {nA nB : ℕ → ℕ} (hnA : Filter.Tendsto nA Filter.atTop Filter.atTop)
    (hnB : Filter.Tendsto nB Filter.atTop Filter.atTop) :
    TendstoInDistribution
      (fun k ω ↦ ((∑ i ∈ Finset.range (nA k), X i ω) / nA k -
          (∑ j ∈ Finset.range (nB k), Y j ω) / nB k) /
          √(pooledProportion X Y (nA k) (nB k) ω * (1 - pooledProportion X Y (nA k) (nB k) ω) *
            (1 / nA k + 1 / nB k)))
      Filter.atTop Z (fun _ ↦ P) P' :=
  tendstoInDistribution_pooled_two_proportions h0 h1 hZ hmX hmY h01X h01Y hprobA hprobB hindep
    hidentX hidentY hnA hnB

/-- OpenStax Introductory Statistics 2e §10.2 (ST-091). Mean and variance of the difference of two
sample means: if all `n₁ + n₂` observations are pairwise independent and square integrable, the `X`
sample having mean `μ₁` and variance `σ₁²` and the `Y` sample mean `μ₂` and variance `σ₂²`, then
`x̄₁ - x̄₂` has mean `μ₁ - μ₂` and variance `σ₁²/n₁ + σ₂²/n₂`. -/
@[kb "openstaxintrostats2e" "§10.2, p. 531"]
theorem difference_of_sample_means_mean_and_variance {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n₁ n₂ : ℕ} (h₁ : 1 ≤ n₁) (h₂ : 1 ≤ n₂)
    {X : Fin n₁ → Ω → ℝ} {Y : Fin n₂ → Ω → ℝ} {μ₁ μ₂ σ₁ σ₂ : ℝ}
    (hX : ∀ i, MemLp (X i) 2 P) (hY : ∀ j, MemLp (Y j) 2 P)
    (hμX : ∀ i, P[X i] = μ₁) (hμY : ∀ j, P[Y j] = μ₂)
    (hσX : ∀ i, Var[X i; P] = σ₁ ^ 2) (hσY : ∀ j, Var[Y j; P] = σ₂ ^ 2)
    (hind : Pairwise fun a b : Fin n₁ ⊕ Fin n₂ ↦ IndepFun (Sum.elim X Y a) (Sum.elim X Y b) P) :
    (∫ ω, (mean (fun i ↦ X i ω) - mean (fun j ↦ Y j ω)) ∂P = μ₁ - μ₂) ∧
      Var[fun ω ↦ mean (fun i ↦ X i ω) - mean (fun j ↦ Y j ω); P] =
        σ₁ ^ 2 / n₁ + σ₂ ^ 2 / n₂ :=
  sampleMean_diff_moments h₁ h₂ hX hY hμX hμY hσX hσY hind

/-- OpenStax Introductory Statistics 2e §10.2 (ST-091). Under the hypotheses of
`difference_of_sample_means_mean_and_variance`, the standard deviation of `x̄₁ - x̄₂` is
`√(σ₁²/n₁ + σ₂²/n₂)`. -/
@[kb "openstaxintrostats2e" "§10.2, p. 531"]
theorem difference_of_sample_means_standard_deviation {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n₁ n₂ : ℕ} (h₁ : 1 ≤ n₁) (h₂ : 1 ≤ n₂)
    {X : Fin n₁ → Ω → ℝ} {Y : Fin n₂ → Ω → ℝ} {μ₁ μ₂ σ₁ σ₂ : ℝ}
    (hX : ∀ i, MemLp (X i) 2 P) (hY : ∀ j, MemLp (Y j) 2 P)
    (hμX : ∀ i, P[X i] = μ₁) (hμY : ∀ j, P[Y j] = μ₂)
    (hσX : ∀ i, Var[X i; P] = σ₁ ^ 2) (hσY : ∀ j, Var[Y j; P] = σ₂ ^ 2)
    (hind : Pairwise fun a b : Fin n₁ ⊕ Fin n₂ ↦ IndepFun (Sum.elim X Y a) (Sum.elim X Y b) P) :
    Real.sqrt Var[fun ω ↦ mean (fun i ↦ X i ω) - mean (fun j ↦ Y j ω); P] =
      Real.sqrt (σ₁ ^ 2 / n₁ + σ₂ ^ 2 / n₂) :=
  sampleMean_diff_stdDev h₁ h₂ hX hY hμX hμY hσX hσY hind

end UndergradKB.Statistics.Course.C10
