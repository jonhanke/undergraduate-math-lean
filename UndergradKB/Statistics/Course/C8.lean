import UndergradKB.Statistics.Inference
import UndergradKB.Statistics.Limits
import UndergradKB.Statistics.Descriptive
import UndergradKB.Common.Attr
import UndergradKB.Statistics.CriticalValues
import UndergradKB.Statistics.Remarks
import UndergradKB.Statistics.DistributionLimits

/-!
# Course layer, chapter 8 (OpenStax *Introductory Statistics 2e*): confidence intervals
-/

namespace UndergradKB.Statistics.Course.C8

open MeasureTheory ProbabilityTheory Set UndergradKB.Statistics

section Normal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n : ℕ} {X : Fin n → Ω → ℝ} {μ σ : ℝ}

/-- OpenStax Introductory Statistics 2e §8.1 (ST-071). With `σ` known and a normal population, the
interval `x̄ ± z σ/√n` covers `μ` with probability `P(-z ≤ Z ≤ z)` for a standard normal `Z`. -/
@[kb "openstaxintrostats2e" "§8.1, p. 418"]
theorem z_interval_coverage (hn : 1 ≤ n) (hσ : 0 < σ) (hX : IsNormalSample X μ σ P) (z : ℝ) :
    P {ω | mean (fun i ↦ X i ω) - z * (σ / √(n : ℝ)) ≤ μ ∧
        μ ≤ mean (fun i ↦ X i ω) + z * (σ / √(n : ℝ))} = gaussianReal 0 1 (Icc (-z) z) :=
  zInterval_coverage hn hσ hX z

/-- OpenStax Introductory Statistics 2e §8.1 (ST-071). When `z = z_{α/2}` satisfies
`P(-z ≤ Z ≤ z) = 1 - α`, the interval `x̄ ± z σ/√n` is a `1 - α` confidence interval for `μ`. -/
@[kb "openstaxintrostats2e" "§8.1, p. 418"]
theorem z_interval_confidence_level (hn : 1 ≤ n) (hσ : 0 < σ) (hX : IsNormalSample X μ σ P)
    {z α : ℝ} (hz : gaussianReal 0 1 (Icc (-z) z) = ENNReal.ofReal (1 - α)) :
    P {ω | mean (fun i ↦ X i ω) - z * (σ / √(n : ℝ)) ≤ μ ∧
        μ ≤ mean (fun i ↦ X i ω) + z * (σ / √(n : ℝ))} = ENNReal.ofReal (1 - α) :=
  zInterval_confidence_level hn hσ hX hz

/-- OpenStax Introductory Statistics 2e §8.2 (ST-075). For a normal population, the statistic
`(x̄ - μ) / (s/√n)` has the Student t distribution with `n - 1` degrees of freedom. -/
@[kb "openstaxintrostats2e" "§8.2, p. 427"]
theorem t_statistic_law (hn : 2 ≤ n) (hσ : 0 < σ) (hX : IsNormalSample X μ σ P) :
    HasLaw (fun ω ↦ (mean (fun i ↦ X i ω) - μ) / (sampleStdDev (fun i ↦ X i ω) / √(n : ℝ)))
      (studentT ((n : ℝ) - 1)) P :=
  hasLaw_tStatistic hn hσ hX

/-- OpenStax Introductory Statistics 2e §8.2 (ST-075). For a normal population the sample mean and
the sample variance are independent. -/
@[kb "openstaxintrostats2e" "§8.2, p. 427"]
theorem sample_mean_independent_of_sample_variance (hn : 2 ≤ n) (hσ : 0 < σ)
    (hX : IsNormalSample X μ σ P) :
    IndepFun (fun ω ↦ mean fun i ↦ X i ω) (fun ω ↦ sampleVariance fun i ↦ X i ω) P :=
  indepFun_sampleMean_sampleVariance hn hσ hX

/-- OpenStax Introductory Statistics 2e §8.2 (ST-077). The interval `x̄ ± t s/√n` covers `μ` with
the Student t probability of `[-t, t]` with `n - 1` degrees of freedom. -/
@[kb "openstaxintrostats2e" "§8.2, p. 427"]
theorem t_interval_coverage (hn : 2 ≤ n) (hσ : 0 < σ) (hX : IsNormalSample X μ σ P) (t : ℝ) :
    P {ω | mean (fun i ↦ X i ω) - t * (sampleStdDev (fun i ↦ X i ω) / √(n : ℝ)) ≤ μ ∧
        μ ≤ mean (fun i ↦ X i ω) + t * (sampleStdDev (fun i ↦ X i ω) / √(n : ℝ))} =
      studentT ((n : ℝ) - 1) (Icc (-t) t) :=
  tInterval_coverage hn hσ hX t

end Normal

/-- OpenStax Introductory Statistics 2e §8.2 (ST-075). If `Z` is standard normal and `V` is
chi-square with `ν` degrees of freedom, independent, then `Z / √(V/ν)` has the Student t
distribution with `ν` degrees of freedom. -/
@[kb "openstaxintrostats2e" "§8.2, p. 427"]
theorem t_distribution_of_normal_over_chi_square {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z V : Ω → ℝ} {ν : ℝ} (hν : 0 < ν)
    (hZ : HasLaw Z (gaussianReal 0 1) P) (hV : HasLaw V (chiSquared ν) P)
    (hind : IndepFun Z V P) :
    HasLaw (fun ω ↦ Z ω / √(V ω / ν)) (studentT ν) P :=
  hasLaw_studentT hν hZ hV hind

/-- OpenStax Introductory Statistics 2e §8.2 (ST-076). The Student t density is symmetric about 0. -/
@[kb "openstaxintrostats2e" "§8.2, p. 427"]
theorem t_density_symmetric (ν x : ℝ) : studentTPDFReal ν (-x) = studentTPDFReal ν x :=
  studentTPDFReal_neg ν x

/-- OpenStax Introductory Statistics 2e §8.2 (ST-076). The Student t density is bell shaped: it
decreases as `|t|` grows. -/
@[kb "openstaxintrostats2e" "§8.2, p. 427"]
theorem t_density_bell_shaped {ν : ℝ} (hν : 0 < ν) {s t : ℝ} (h : |s| ≤ |t|) :
    studentTPDFReal ν t ≤ studentTPDFReal ν s :=
  studentTPDFReal_le_of_abs_le hν h

/-- OpenStax Introductory Statistics 2e §8.2 (ST-076). As the degrees of freedom grow, the Student
t density tends to the standard normal density. -/
@[kb "openstaxintrostats2e" "§8.2, p. 427"]
theorem t_density_tends_to_normal_density (t : ℝ) :
    Filter.Tendsto (fun ν : ℝ ↦ studentTPDFReal ν t) Filter.atTop
      (nhds (gaussianPDFReal 0 1 t)) :=
  tendsto_studentTPDFReal_gaussianPDFReal t

/-- OpenStax Introductory Statistics 2e §8.3 (ST-078). For Bernoulli trials with success
probability `p`, the sample proportion `p'` satisfies: `√n (p' - p) / √(p q)` converges in
distribution to the standard normal, i.e. `p'` is approximately `N(p, √(pq/n))`. -/
@[kb "openstaxintrostats2e" "§8.3, p. 431"]
theorem sample_proportion_normal_approximation {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω}
    {mΩ' : MeasurableSpace Ω'} {P : Measure Ω} {P' : Measure Ω'} {X : ℕ → Ω → ℝ} {Y : Ω' → ℝ}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hY : HasLaw Y (gaussianReal 0 1) P')
    (hmeas : ∀ i, Measurable (X i)) (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hprob : P.real {ω | X 0 ω = 1} = p) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ √n * ((∑ k ∈ Finset.range n, X k ω) / n - p) / √(p * (1 - p)))
      Filter.atTop Y (fun _ ↦ P) P' :=
  tendstoInDistribution_sampleProportion hp0 hp1 hY hmeas h01 hprob hindep hident

/-- OpenStax Introductory Statistics 2e §8.1 (ST-073). Sample size for a given error bound: if
`n ≥ z² σ² / EBM²` then the margin of error `z σ/√n` is at most `EBM`. -/
@[kb "openstaxintrostats2e" "§8.1, p. 418"]
theorem sample_size_for_error_bound_mean (z σ EBM : ℝ) (n : ℕ) (hz : 0 < z) (hσ : 0 < σ)
    (hEBM : 0 < EBM) (hn : z ^ 2 * σ ^ 2 / EBM ^ 2 ≤ n) : z * σ / Real.sqrt n ≤ EBM :=
  margin_le_of_sampleSize z σ EBM n hz hσ hEBM hn

/-- OpenStax Introductory Statistics 2e §8.3 (ST-079). Sample size for a proportion: if
`n ≥ z² p' q' / EBP²` then the margin of error `z √(p'q'/n)` is at most `EBP`. -/
@[kb "openstaxintrostats2e" "§8.3, p. 431"]
theorem sample_size_for_error_bound_proportion (z p' q' EBP : ℝ) (n : ℕ) (hz : 0 < z)
    (hpq : 0 ≤ p' * q') (hEBP : 0 < EBP) (hn : z ^ 2 * (p' * q') / EBP ^ 2 ≤ n) :
    z * Real.sqrt (p' * q' / n) ≤ EBP :=
  proportion_margin_le_of_sampleSize z p' q' EBP n hz hpq hEBP hn

/-- OpenStax Introductory Statistics 2e §8.3 (ST-079). When `p'` is unknown, using `p' = 0.5`
gives the conservative bound: `n ≥ z² / (4 EBP²)` makes the margin at most `EBP` for every `p'`. -/
@[kb "openstaxintrostats2e" "§8.3, p. 431"]
theorem sample_size_for_proportion_unknown (z p' EBP : ℝ) (n : ℕ) (hz : 0 < z) (hp0 : 0 ≤ p')
    (hp1 : p' ≤ 1) (hEBP : 0 < EBP) (hn : z ^ 2 / (4 * EBP ^ 2) ≤ n) :
    z * Real.sqrt (p' * (1 - p') / n) ≤ EBP :=
  proportion_margin_le_of_conservative z p' EBP n hz hp0 hp1 hEBP hn

/-- OpenStax Introductory Statistics 2e §8.1 (ST-071). The critical values for 90%, 95% and 99%
confidence: the standard normal mass within `1.645`, `1.96`, `2.576` of zero lies in
`(0.8999, 0.9001)`, `(0.9499, 0.9501)`, `(0.9899, 0.9901)` respectively. -/
@[kb "openstaxintrostats2e" "§8.1, p. 418"]
theorem critical_values_standard_normal_mass :
    ((0.8999 : ℝ) < (gaussianReal 0 1).real (Ioo (-1.645) 1.645) ∧
      (gaussianReal 0 1).real (Ioo (-1.645) 1.645) < 0.9001) ∧
    ((0.9499 : ℝ) < (gaussianReal 0 1).real (Ioo (-1.96) 1.96) ∧
      (gaussianReal 0 1).real (Ioo (-1.96) 1.96) < 0.9501) ∧
    ((0.9899 : ℝ) < (gaussianReal 0 1).real (Ioo (-2.576) 2.576) ∧
      (gaussianReal 0 1).real (Ioo (-2.576) 2.576) < 0.9901) :=
  critical_values_standard_normal

/-- OpenStax Introductory Statistics 2e §8.1 (ST-071). One-sided form of the critical values: the
standard normal distribution function satisfies `Φ(1.645) ∈ (0.9499, 0.9501)`,
`Φ(1.96) ∈ (0.9749, 0.9751)`, `Φ(2.576) ∈ (0.9949, 0.9951)`. -/
@[kb "openstaxintrostats2e" "§8.1, p. 418"]
theorem critical_values_standard_normal_cdf :
    ((0.9499 : ℝ) < cdf (gaussianReal 0 1) 1.645 ∧ cdf (gaussianReal 0 1) 1.645 < 0.9501) ∧
    ((0.9749 : ℝ) < cdf (gaussianReal 0 1) 1.96 ∧ cdf (gaussianReal 0 1) 1.96 < 0.9751) ∧
    ((0.9949 : ℝ) < cdf (gaussianReal 0 1) 2.576 ∧ cdf (gaussianReal 0 1) 2.576 < 0.9951) :=
  critical_values_stdNormalCdf

/-- OpenStax Introductory Statistics 2e §8.1 (ST-071). Critical values for a general normal variable
`X ~ N(μ, σ²)` with `σ > 0`: the probability that `X` is within `1.645σ`, `1.96σ`, `2.576σ` of the
mean lies in `(0.8999, 0.9001)`, `(0.9499, 0.9501)`, `(0.9899, 0.9901)`. -/
@[kb "openstaxintrostats2e" "§8.1, p. 418"]
theorem critical_values_general_normal {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {μ σ : ℝ} (hσ : 0 < σ) (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) :
    ((0.8999 : ℝ) < P.real {ω | |X ω - μ| < 1.645 * σ} ∧
      P.real {ω | |X ω - μ| < 1.645 * σ} < 0.9001) ∧
    ((0.9499 : ℝ) < P.real {ω | |X ω - μ| < 1.96 * σ} ∧
      P.real {ω | |X ω - μ| < 1.96 * σ} < 0.9501) ∧
    ((0.9899 : ℝ) < P.real {ω | |X ω - μ| < 2.576 * σ} ∧
      P.real {ω | |X ω - μ| < 2.576 * σ} < 0.9901) :=
  critical_values_normal hσ hX

section LongRun

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

open scoped Classical in
/-- OpenStax Introductory Statistics 2e §8.1 (ST-074). Long-run reading of a confidence level: if
experiments are repeated independently and the `k`-th produces an event `E k` ("the interval covers
the parameter") with probability `1 - α`, then almost surely the fraction of the first `n`
experiments in which the event occurs tends to `1 - α`. -/
@[kb "openstaxintrostats2e" "§8.1, p. 418"]
theorem confidence_level_long_run_fraction (E : ℕ → Set Ω) (hmeas : ∀ k, MeasurableSet (E k))
    (hindep : iIndepSet E P) (α : ℝ) (hprob : ∀ k, P.real (E k) = 1 - α) :
    ∀ᵐ ω ∂P, Filter.Tendsto
      (fun n : ℕ => (((Finset.range n).filter (fun k => ω ∈ E k)).card : ℝ) / n) Filter.atTop
      (nhds (1 - α)) :=
  coverage_fraction_tendsto E hmeas hindep α hprob

variable {n : ℕ} {μ σ : ℝ}

open scoped Classical in
/-- OpenStax Introductory Statistics 2e §8.1 (ST-074). For repeated z intervals from normal samples
`S k` with mean `μ` and standard deviation `σ`, with independent measurable coverage events and `z`
giving confidence level `1 - α`, almost surely the fraction of the first `m` intervals covering `μ`
tends to `1 - α`. -/
@[kb "openstaxintrostats2e" "§8.1, p. 418"]
theorem z_interval_long_run_fraction (hn : 1 ≤ n) (hσ : 0 < σ) (S : ℕ → Fin n → Ω → ℝ)
    (hS : ∀ k, IsNormalSample (S k) μ σ P) {z α : ℝ} (hα : α ≤ 1)
    (hz : gaussianReal 0 1 (Set.Icc (-z) z) = ENNReal.ofReal (1 - α))
    (hmeas : ∀ k, MeasurableSet {ω | mean (fun i ↦ S k i ω) - z * (σ / √(n : ℝ)) ≤ μ ∧
        μ ≤ mean (fun i ↦ S k i ω) + z * (σ / √(n : ℝ))})
    (hindep : iIndepSet (fun k => {ω | mean (fun i ↦ S k i ω) - z * (σ / √(n : ℝ)) ≤ μ ∧
        μ ≤ mean (fun i ↦ S k i ω) + z * (σ / √(n : ℝ))}) P) :
    ∀ᵐ ω ∂P, Filter.Tendsto
      (fun m : ℕ => (((Finset.range m).filter (fun k =>
        mean (fun i ↦ S k i ω) - z * (σ / √(n : ℝ)) ≤ μ ∧
        μ ≤ mean (fun i ↦ S k i ω) + z * (σ / √(n : ℝ)))).card : ℝ) / m) Filter.atTop
      (nhds (1 - α)) :=
  zInterval_coverage_fraction_tendsto hn hσ S hS hα hz hmeas hindep

end LongRun

/-- OpenStax Introductory Statistics 2e §8.2 (ST-076). The Student t distribution has heavier tails
than the standard normal: for every `ν > 0`, the ratio of the t density with `ν` degrees of freedom
to the standard normal density tends to infinity as `t → ∞`. -/
@[kb "openstaxintrostats2e" "§8.2, p. 427"]
theorem student_t_density_has_heavier_tails_than_normal {ν : ℝ} (hν : 0 < ν) :
    Filter.Tendsto (fun t : ℝ ↦ studentTPDFReal ν t / gaussianPDFReal 0 1 t) Filter.atTop
      Filter.atTop :=
  tendsto_studentTPDFReal_div_gaussianPDFReal hν

end UndergradKB.Statistics.Course.C8
