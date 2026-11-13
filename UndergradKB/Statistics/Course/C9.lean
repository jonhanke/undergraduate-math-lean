import UndergradKB.Statistics.Inference
import UndergradKB.Statistics.PValue
import UndergradKB.Statistics.Limits
import UndergradKB.Common.Attr

/-!
# Course layer, chapter 9 (OpenStax *Introductory Statistics 2e*): hypothesis testing
-/

namespace UndergradKB.Statistics.Course.C9

open MeasureTheory ProbabilityTheory Set UndergradKB.Statistics

section Normal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n : ℕ} {X : Fin n → Ω → ℝ} {μ σ : ℝ}

/-- OpenStax Introductory Statistics 2e §9.2 (ST-082). Type I error of the two-sided z test: the
probability of rejecting a true `H₀` equals the level of significance `α`. -/
@[kb "openstaxintrostats2e" "§9.2, p. 475"]
theorem type_I_error_z_test (hn : 1 ≤ n) (hσ : 0 < σ) (hX : IsNormalSample X μ σ P)
    {z α : ℝ} (hα : α ≤ 1) (hz : gaussianReal 0 1 (Icc (-z) z) = ENNReal.ofReal (1 - α)) :
    P {ω | z < |(mean (fun i ↦ X i ω) - μ) / (σ / √(n : ℝ))|} = ENNReal.ofReal α :=
  zTest_typeI_error hn hσ hX hα hz

/-- OpenStax Introductory Statistics 2e §9.2 (ST-082). Type I error of the two-sided t test: the
probability of rejecting a true `H₀` equals the level of significance `α`. -/
@[kb "openstaxintrostats2e" "§9.2, p. 475"]
theorem type_I_error_t_test (hn : 2 ≤ n) (hσ : 0 < σ) (hX : IsNormalSample X μ σ P)
    {t α : ℝ} (hα : α ≤ 1)
    (ht : studentT ((n : ℝ) - 1) (Icc (-t) t) = ENNReal.ofReal (1 - α)) :
    P {ω | t < |(mean (fun i ↦ X i ω) - μ) / (sampleStdDev (fun i ↦ X i ω) / √(n : ℝ))|} =
      ENNReal.ofReal α :=
  tTest_typeI_error hn hσ hX hα ht

/-- OpenStax Introductory Statistics 2e §9.2 (ST-083). If the true mean is `μ₁`, the right-tailed
z test (reject when `z > c`) rejects with probability equal to the power
`1 - Φ(c - (μ₁ - μ₀) √n / σ)`, so the Type II error is `β = 1 - power`. -/
@[kb "openstaxintrostats2e" "§9.2, p. 475"]
theorem power_of_z_test (hn : 1 ≤ n) (hσ : 0 < σ) (hX : IsNormalSample X μ σ P) (μ₀ c : ℝ) :
    P {ω | c < (mean (fun i ↦ X i ω) - μ₀) / (σ / √(n : ℝ))} =
      ENNReal.ofReal (zTestPower μ₀ μ σ n c) :=
  zTest_power_eq hn hσ hX μ₀ c

/-- OpenStax Introductory Statistics 2e §9.3 (ST-084). Under `H₀`, the test statistic
`z = (x̄ - μ₀) / (σ / √n)` is standard normal (known `σ`, normal population). -/
@[kb "openstaxintrostats2e" "§9.3, p. 477"]
theorem z_test_statistic_law (hn : 1 ≤ n) (hσ : 0 < σ) (hX : IsNormalSample X μ σ P) :
    HasLaw (fun ω ↦ (mean (fun i ↦ X i ω) - μ) / (σ / √(n : ℝ))) (gaussianReal 0 1) P :=
  hasLaw_zStatistic hn hσ hX

/-- OpenStax Introductory Statistics 2e §9.3 (ST-085). Under `H₀`, with `σ` unknown and a normal
population, `t = (x̄ - μ₀) / (s/√n)` has the Student t distribution with `n - 1` degrees of
freedom. -/
@[kb "openstaxintrostats2e" "§9.3, p. 477"]
theorem t_test_statistic_law (hn : 2 ≤ n) (hσ : 0 < σ) (hX : IsNormalSample X μ σ P) :
    HasLaw (fun ω ↦ (mean (fun i ↦ X i ω) - μ) / (sampleStdDev (fun i ↦ X i ω) / √(n : ℝ)))
      (studentT ((n : ℝ) - 1)) P :=
  hasLaw_tStatistic hn hσ hX

/-- OpenStax Introductory Statistics 2e §9.4 (ST-087). Under `H₀`, the probability that the
two-sided p-value falls below `α` is `α`: rejecting when the p-value is less than `α` is a test of
level `α`. -/
@[kb "openstaxintrostats2e" "§9.4, p. 478"]
theorem p_value_below_alpha_probability (hn : 1 ≤ n) (hσ : 0 < σ)
    (hX : IsNormalSample X μ σ P) {c α : ℝ} (h0 : 0 < α) (h1 : α < 1)
    (hz : gaussianReal 0 1 (Icc (-c) c) = ENNReal.ofReal (1 - α)) :
    P {ω | zPValue ((mean (fun i ↦ X i ω) - μ) / (σ / √(n : ℝ))) < α} = ENNReal.ofReal α :=
  zPValue_prob_lt hn hσ hX h0 h1 hz

end Normal

/-- OpenStax Introductory Statistics 2e §9.2 (ST-083). For a fixed sample size, decreasing the
level of significance `α` (raising the critical value) strictly decreases the power, that is,
increases `β`. -/
@[kb "openstaxintrostats2e" "§9.2, p. 475"]
theorem smaller_alpha_gives_smaller_power (μ₀ μ₁ σ : ℝ) (n : ℕ) {c c' α α' : ℝ}
    (hc : 1 - cdf (gaussianReal 0 1) c = α) (hc' : 1 - cdf (gaussianReal 0 1) c' = α')
    (h : α' < α) :
    zTestPower μ₀ μ₁ σ n c' < zTestPower μ₀ μ₁ σ n c :=
  zTestPower_lt_of_smaller_level μ₀ μ₁ σ n hc hc' h

/-- OpenStax Introductory Statistics 2e §9.2 (ST-083). For a fixed critical value, increasing the
sample size strictly increases the power and strictly decreases `β` (when `μ₁ > μ₀`). -/
@[kb "openstaxintrostats2e" "§9.2, p. 475"]
theorem larger_sample_size_reduces_type_II_error {μ₀ μ₁ σ : ℝ} (hμ : μ₀ < μ₁) (hσ : 0 < σ)
    (c : ℝ) {n n' : ℕ} (h : n < n') :
    zTestPower μ₀ μ₁ σ n c < zTestPower μ₀ μ₁ σ n' c ∧
      zTestTypeII μ₀ μ₁ σ n' c < zTestTypeII μ₀ μ₁ σ n c :=
  zTestPower_strictMono_sampleSize hμ hσ c h

/-- OpenStax Introductory Statistics 2e §9.3 (ST-086). Test of a proportion: under `H₀` (success
probability `p₀`), the statistic `z = (p' - p₀) / √(p₀ q₀ / n)` converges in distribution to the
standard normal. -/
@[kb "openstaxintrostats2e" "§9.3, p. 477"]
theorem proportion_test_statistic_normal_approximation {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω}
    {mΩ' : MeasurableSpace Ω'} {P : Measure Ω} {P' : Measure Ω'} {X : ℕ → Ω → ℝ} {Y : Ω' → ℝ}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {p₀ : ℝ} (hp0 : 0 < p₀) (hp1 : p₀ < 1)
    (hY : HasLaw Y (gaussianReal 0 1) P')
    (hmeas : ∀ i, Measurable (X i)) (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hprob : P.real {ω | X 0 ω = 1} = p₀) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ √n * ((∑ k ∈ Finset.range n, X k ω) / n - p₀) / √(p₀ * (1 - p₀)))
      Filter.atTop Y (fun _ ↦ P) P' :=
  tendstoInDistribution_sampleProportion hp0 hp1 hY hmeas h01 hprob hindep hident

/-- OpenStax Introductory Statistics 2e §9.4 (ST-087). The two-sided p-value of an observed
statistic `z` is below `α` exactly when `|z|` exceeds the critical value `z_{α/2}`, so reject `H₀`
when the p-value is less than `α`. -/
@[kb "openstaxintrostats2e" "§9.4, p. 478"]
theorem reject_iff_p_value_less_than_alpha {c α : ℝ} (h0 : 0 < α) (h1 : α < 1)
    (hz : gaussianReal 0 1 (Icc (-c) c) = ENNReal.ofReal (1 - α)) (z : ℝ) :
    zPValue z < α ↔ c < |z| :=
  zPValue_lt_iff h0 h1 hz z

/-- OpenStax Introductory Statistics 2e §9.5 (ST-089). A two-sided z test at critical value `z`
accepts `μ₀` exactly when `μ₀` lies in the confidence interval `x̄ ± z σ/√n`. -/
@[kb "openstaxintrostats2e" "§9.5, p. 480"]
theorem z_test_matches_confidence_interval {xbar μ₀ σ z : ℝ} {n : ℕ} (hσ : 0 < σ) (hn : 0 < n) :
    |xbar - μ₀| / (σ / √(n : ℝ)) ≤ z ↔
      μ₀ ∈ Icc (xbar - z * (σ / √(n : ℝ))) (xbar + z * (σ / √(n : ℝ))) :=
  zTest_accepts_iff_mem_interval hσ hn

/-- OpenStax Introductory Statistics 2e §9.5 (ST-089). The t version of the duality between a
two-sided test and the confidence interval `x̄ ± t s/√n` (for `s > 0`). -/
@[kb "openstaxintrostats2e" "§9.5, p. 480"]
theorem t_test_matches_confidence_interval {xbar μ₀ s t : ℝ} {n : ℕ} (hs : 0 < s) (hn : 0 < n) :
    |xbar - μ₀| / (s / √(n : ℝ)) ≤ t ↔
      μ₀ ∈ Icc (xbar - t * (s / √(n : ℝ))) (xbar + t * (s / √(n : ℝ))) :=
  tTest_accepts_iff_mem_interval hs hn

end UndergradKB.Statistics.Course.C9
