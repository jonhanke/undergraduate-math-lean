import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import UndergradKB.Common.Attr
import UndergradKB.Statistics.NormalSample
import UndergradKB.Statistics.FDistribution

/-!
# Inference for normal samples (OpenStax *Introductory Statistics 2e*, chapters 8-10 and 13)

Consequences of the laws of the sample mean and sample variance of a normal sample
(`UndergradKB.Statistics.NormalSample`): the z statistic, coverage of the z and t confidence
intervals, the type I error of the two-sided tests, the duality between tests and intervals, paired
samples, the difference of two independent sample means, and the ratio of two sample variances.
-/

namespace UndergradKB.Statistics

open MeasureTheory ProbabilityTheory Real Set

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-! ### Small lemmas -/

lemma prob_mem_of_hasLaw {Z : Ω → ℝ} {ν : Measure ℝ} (h : HasLaw Z ν P) {S : Set ℝ}
    (hS : MeasurableSet S) : P {ω | Z ω ∈ S} = ν S :=
  h.measure_eq (p := (· ∈ S)) hS

/-- The chi-square law has no atoms (it has a density). -/
lemma chiSquared_singleton (k x : ℝ) : chiSquared k {x} = 0 := by
  unfold chiSquared gammaMeasure
  exact withDensity_absolutelyContinuous volume _ Real.volume_singleton

/-- `P(|Z| > c) = 1 - ν[-c, c]` when `Z` has the (probability) law `ν`. -/
lemma prob_abs_gt {Z : Ω → ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν] (h : HasLaw Z ν P)
    (c : ℝ) : P {ω | c < |Z ω|} = 1 - ν (Icc (-c) c) := by
  have h1 := prob_mem_of_hasLaw h (measurableSet_Icc (a := -c) (b := c)).compl
  rw [prob_compl_eq_one_sub measurableSet_Icc] at h1
  rw [← h1]
  congr 1
  ext ω
  simp only [mem_setOf_eq, mem_compl_iff, mem_Icc]
  rw [← abs_le, not_le]

lemma ofReal_one_sub_ofReal {α : ℝ} (h : α ≤ 1) :
    1 - ENNReal.ofReal (1 - α) = ENNReal.ofReal α := by
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith)]
  congr 1
  ring

lemma measurable_mean' {n : ℕ} : Measurable (fun v : Fin n → ℝ ↦ mean v) := by
  unfold mean; fun_prop

lemma measurable_sampleVariance' {n : ℕ} : Measurable (fun v : Fin n → ℝ ↦ sampleVariance v) := by
  unfold sampleVariance sumSqDev mean; fun_prop

lemma sampleVariance_nonneg' {n : ℕ} (hn : 1 ≤ n) (v : Fin n → ℝ) : 0 ≤ sampleVariance v := by
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact div_nonneg (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (by linarith)

/-! ### The z statistic and the z interval -/

section OneSample

variable {n : ℕ} [IsProbabilityMeasure P] {X : Fin n → Ω → ℝ} {μ σ : ℝ}

/-- OpenStax Introductory Statistics 2e §9.3 (ST-084). Under `H₀` (a sample from `N(μ₀, σ)`), the
test statistic `z = (xbar - μ₀) / (σ / √n)` has the standard normal law. -/
@[kb "openstaxintrostats2e" "§9.3, p. 477"]
theorem hasLaw_zStatistic (hn : 1 ≤ n) (hσ : 0 < σ) (hX : IsNormalSample X μ σ P) :
    HasLaw (fun ω ↦ (mean (fun i ↦ X i ω) - μ) / (σ / √(n : ℝ))) (gaussianReal 0 1) P := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := hasLaw_sampleMean_normal hn hσ hX
  have e : (σ / √(n : ℝ)) ^ 2 = σ ^ 2 / n := by rw [div_pow, sq_sqrt hn'.le]
  rw [← e] at h
  exact hasLaw_standardize (div_pos hσ (sqrt_pos.2 hn')) h

/-- OpenStax Introductory Statistics 2e §8.1 (ST-071). Coverage of the z interval
`xbar ± z σ/√n` for a normal sample: the probability that it covers `μ` is the standard normal
probability of `[-z, z]`. -/
@[kb "openstaxintrostats2e" "§8.1, p. 418"]
theorem zInterval_coverage (hn : 1 ≤ n) (hσ : 0 < σ) (hX : IsNormalSample X μ σ P) (z : ℝ) :
    P {ω | mean (fun i ↦ X i ω) - z * (σ / √(n : ℝ)) ≤ μ ∧
        μ ≤ mean (fun i ↦ X i ω) + z * (σ / √(n : ℝ))} = gaussianReal 0 1 (Icc (-z) z) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : 0 < σ / √(n : ℝ) := div_pos hσ (sqrt_pos.2 hn')
  rw [← prob_mem_of_hasLaw (hasLaw_zStatistic hn hσ hX) (measurableSet_Icc (a := -z) (b := z))]
  congr 1
  ext ω
  simp only [mem_setOf_eq, mem_Icc]
  rw [le_div_iff₀ hc, div_le_iff₀ hc]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- OpenStax Introductory Statistics 2e §8.1 (ST-071). If `z` is chosen with
`P(-z ≤ Z ≤ z) = 1 - α` for a standard normal `Z`, the z interval has confidence level `1 - α`. -/
@[kb "openstaxintrostats2e" "§8.1, p. 418"]
theorem zInterval_confidence_level (hn : 1 ≤ n) (hσ : 0 < σ) (hX : IsNormalSample X μ σ P)
    {z α : ℝ} (hz : gaussianReal 0 1 (Icc (-z) z) = ENNReal.ofReal (1 - α)) :
    P {ω | mean (fun i ↦ X i ω) - z * (σ / √(n : ℝ)) ≤ μ ∧
        μ ≤ mean (fun i ↦ X i ω) + z * (σ / √(n : ℝ))} = ENNReal.ofReal (1 - α) := by
  rw [zInterval_coverage hn hσ hX z, hz]

/-- OpenStax Introductory Statistics 2e §8.2 (ST-077). Coverage of the t interval
`xbar ± t s/√n` for a normal sample (`n ≥ 2`): the probability that it covers `μ` is the Student
`t` probability of `[-t, t]` with `n - 1` degrees of freedom. -/
@[kb "openstaxintrostats2e" "§8.2, p. 427"]
theorem tInterval_coverage (hn : 2 ≤ n) (hσ : 0 < σ) (hX : IsNormalSample X μ σ P) (t : ℝ) :
    P {ω | mean (fun i ↦ X i ω) - t * (sampleStdDev (fun i ↦ X i ω) / √(n : ℝ)) ≤ μ ∧
        μ ≤ mean (fun i ↦ X i ω) + t * (sampleStdDev (fun i ↦ X i ω) / √(n : ℝ))} =
      studentT ((n : ℝ) - 1) (Icc (-t) t) := by
  have hn1 : 1 ≤ n := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hT := hasLaw_tStatistic hn hσ hX
  have hV := hasLaw_sampleVariance_chiSquared hn hσ hX
  have hs0 : ∀ᵐ ω ∂P, sampleStdDev (fun i ↦ X i ω) ≠ 0 := by
    have hnull := prob_mem_of_hasLaw hV (measurableSet_singleton (0 : ℝ))
    rw [chiSquared_singleton] at hnull
    have hae : ∀ᵐ ω ∂P, ¬ (((n : ℝ) - 1) * sampleVariance (fun i ↦ X i ω) / σ ^ 2 ∈
        ({0} : Set ℝ)) := ae_iff.2 (by simpa only [not_not] using hnull)
    filter_upwards [hae] with ω hω hs
    apply hω
    have h1 : sampleVariance (fun i ↦ X i ω) ≤ 0 := by
      unfold sampleStdDev at hs
      exact (Real.sqrt_eq_zero'.1 hs)
    have h2 := sampleVariance_nonneg' hn1 (fun i ↦ X i ω)
    have : sampleVariance (fun i ↦ X i ω) = 0 := le_antisymm h1 h2
    simp [this]
  rw [← prob_mem_of_hasLaw hT (measurableSet_Icc (a := -t) (b := t))]
  refine measure_congr ?_
  refine Filter.eventuallyEq_set.2 ?_
  filter_upwards [hs0] with ω hω
  have hpos : 0 < sampleStdDev (fun i ↦ X i ω) :=
    lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hω)
  have hc : 0 < sampleStdDev (fun i ↦ X i ω) / √(n : ℝ) := div_pos hpos (sqrt_pos.2 hn')
  simp only [mem_setOf_eq, mem_Icc]
  rw [le_div_iff₀ hc, div_le_iff₀ hc]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- OpenStax Introductory Statistics 2e §9.2 (ST-082). Type I error of the two-sided z test:
if `P(|Z| ≤ z) = 1 - α` for a standard normal `Z`, rejecting when `|z-statistic| > z` has
probability `α` under `H₀`. -/
@[kb "openstaxintrostats2e" "§9.2, p. 475"]
theorem zTest_typeI_error (hn : 1 ≤ n) (hσ : 0 < σ) (hX : IsNormalSample X μ σ P)
    {z α : ℝ} (hα : α ≤ 1) (hz : gaussianReal 0 1 (Icc (-z) z) = ENNReal.ofReal (1 - α)) :
    P {ω | z < |(mean (fun i ↦ X i ω) - μ) / (σ / √(n : ℝ))|} = ENNReal.ofReal α := by
  rw [prob_abs_gt (hasLaw_zStatistic hn hσ hX), hz, ofReal_one_sub_ofReal hα]

/-- OpenStax Introductory Statistics 2e §9.2 (ST-082). Type I error of the two-sided t test: if the
Student `t` law with `n - 1` degrees of freedom gives `[-t, t]` probability `1 - α`, rejecting
when `|t-statistic| > t` has probability `α` under `H₀`. -/
@[kb "openstaxintrostats2e" "§9.2, p. 475"]
theorem tTest_typeI_error (hn : 2 ≤ n) (hσ : 0 < σ) (hX : IsNormalSample X μ σ P)
    {t α : ℝ} (hα : α ≤ 1)
    (ht : studentT ((n : ℝ) - 1) (Icc (-t) t) = ENNReal.ofReal (1 - α)) :
    P {ω | t < |(mean (fun i ↦ X i ω) - μ) / (sampleStdDev (fun i ↦ X i ω) / √(n : ℝ))|} =
      ENNReal.ofReal α := by
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  haveI := isProbabilityMeasure_studentT' hn1
  rw [prob_abs_gt (hasLaw_tStatistic hn hσ hX), ht, ofReal_one_sub_ofReal hα]

end OneSample

/-! ### Duality between tests and intervals -/

/-- OpenStax Introductory Statistics 2e §9.5 (ST-089). A two-sided z test of `μ₀` at critical
value `z` accepts exactly when `μ₀` lies in the z confidence interval `xbar ± z σ/√n`. -/
@[kb "openstaxintrostats2e" "§9.5, p. 480"]
theorem zTest_accepts_iff_mem_interval {xbar μ₀ σ z : ℝ} {n : ℕ} (hσ : 0 < σ) (hn : 0 < n) :
    |xbar - μ₀| / (σ / √(n : ℝ)) ≤ z ↔
      μ₀ ∈ Icc (xbar - z * (σ / √(n : ℝ))) (xbar + z * (σ / √(n : ℝ))) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : 0 < σ / √(n : ℝ) := div_pos hσ (sqrt_pos.2 hn')
  rw [div_le_iff₀ hc, abs_le, mem_Icc]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- OpenStax Introductory Statistics 2e §9.5 (ST-089). The t version of the duality, for a sample
standard deviation `s > 0`. -/
@[kb "openstaxintrostats2e" "§9.5, p. 480"]
theorem tTest_accepts_iff_mem_interval {xbar μ₀ s t : ℝ} {n : ℕ} (hs : 0 < s) (hn : 0 < n) :
    |xbar - μ₀| / (s / √(n : ℝ)) ≤ t ↔
      μ₀ ∈ Icc (xbar - t * (s / √(n : ℝ))) (xbar + t * (s / √(n : ℝ))) :=
  zTest_accepts_iff_mem_interval hs hn

/-! ### Paired samples -/

section Paired

variable {n : ℕ} [IsProbabilityMeasure P]

/-- OpenStax Introductory Statistics 2e §10.4 (ST-094). Matched pairs: if the differences
`Dᵢ = Xᵢ - Yᵢ` form a normal sample with mean `μ_d`, then `(d̄ - μ_d) / (s_d / √n)` has the Student
`t` law with `n - 1` degrees of freedom. -/
@[kb "openstaxintrostats2e" "§10.4, p. 538"]
theorem hasLaw_pairedTStatistic {X Y : Fin n → Ω → ℝ} {μd σd : ℝ} (hn : 2 ≤ n) (hσ : 0 < σd)
    (hD : IsNormalSample (fun i ω ↦ X i ω - Y i ω) μd σd P) :
    HasLaw (fun ω ↦ (mean (fun i ↦ X i ω - Y i ω) - μd) /
      (sampleStdDev (fun i ↦ X i ω - Y i ω) / √(n : ℝ))) (studentT ((n : ℝ) - 1)) P :=
  hasLaw_tStatistic hn hσ hD

end Paired

/-! ### Two independent normal samples -/

section TwoSamples

variable [IsProbabilityMeasure P] {n₁ n₂ : ℕ} {X : Fin n₁ → Ω → ℝ} {Y : Fin n₂ → Ω → ℝ}
  {μ₁ μ₂ σ₁ σ₂ : ℝ}

/-- OpenStax Introductory Statistics 2e §10.1 (ST-091). For independent normal samples
`N(μ₁, σ₁)` of size `n₁` and `N(μ₂, σ₂)` of size `n₂`, the difference of sample means is
`N(μ₁ - μ₂, σ₁²/n₁ + σ₂²/n₂)`. -/
@[kb "openstaxintrostats2e" "§10.1, p. 523"]
theorem hasLaw_diffMeans (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂) (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂)
    (hX : IsNormalSample X μ₁ σ₁ P) (hY : IsNormalSample Y μ₂ σ₂ P)
    (hind : IndepFun (fun ω i ↦ X i ω) (fun ω j ↦ Y j ω) P) :
    HasLaw (fun ω ↦ mean (fun i ↦ X i ω) - mean (fun j ↦ Y j ω))
      (gaussianReal (μ₁ - μ₂) (σ₁ ^ 2 / n₁ + σ₂ ^ 2 / n₂).toNNReal) P := by
  have hn₁' : (0 : ℝ) < n₁ := by exact_mod_cast hn₁
  have hn₂' : (0 : ℝ) < n₂ := by exact_mod_cast hn₂
  have hx := hasLaw_sampleMean_normal hn₁ hσ₁ hX
  have hy := gaussianReal_const_mul (hasLaw_sampleMean_normal hn₂ hσ₂ hY) (-1)
  have hind' : IndepFun (fun ω ↦ mean (fun i ↦ X i ω)) (fun ω ↦ -1 * mean (fun j ↦ Y j ω)) P :=
    hind.comp (measurable_mean') (measurable_mean'.const_mul (-1))
  have h := hind'.hasLaw_add hx hy
  rw [gaussianReal_conv_gaussianReal] at h
  have e : (fun ω ↦ mean (fun i ↦ X i ω) - mean (fun j ↦ Y j ω)) =
      (fun ω ↦ mean (fun i ↦ X i ω)) + fun ω ↦ -1 * mean (fun j ↦ Y j ω) := by
    funext ω; simp; ring
  rw [e]
  convert h using 2
  · ring
  · have p1 : 0 ≤ σ₁ ^ 2 / n₁ := by positivity
    have p2 : 0 ≤ σ₂ ^ 2 / n₂ := by positivity
    apply NNReal.eq
    rw [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ p1,
      Real.coe_toNNReal _ p2, Real.coe_toNNReal _ (add_nonneg p1 p2)]
    ring

/-- OpenStax Introductory Statistics 2e §10.2 (ST-092). With the standard deviations known, the
standardized difference of two independent sample means
`((xbar - ȳ) - (μ₁ - μ₂)) / √(σ₁²/n₁ + σ₂²/n₂)` is standard normal. -/
@[kb "openstaxintrostats2e" "§10.2, p. 531"]
theorem hasLaw_twoSampleZ (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂) (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂)
    (hX : IsNormalSample X μ₁ σ₁ P) (hY : IsNormalSample Y μ₂ σ₂ P)
    (hind : IndepFun (fun ω i ↦ X i ω) (fun ω j ↦ Y j ω) P) :
    HasLaw (fun ω ↦ ((mean (fun i ↦ X i ω) - mean (fun j ↦ Y j ω)) - (μ₁ - μ₂)) /
      √(σ₁ ^ 2 / n₁ + σ₂ ^ 2 / n₂)) (gaussianReal 0 1) P := by
  have hn₁' : (0 : ℝ) < n₁ := by exact_mod_cast hn₁
  have hn₂' : (0 : ℝ) < n₂ := by exact_mod_cast hn₂
  have h := hasLaw_diffMeans hn₁ hn₂ hσ₁ hσ₂ hX hY hind
  have hV : 0 < σ₁ ^ 2 / n₁ + σ₂ ^ 2 / n₂ := by positivity
  have e : √(σ₁ ^ 2 / n₁ + σ₂ ^ 2 / n₂) ^ 2 = σ₁ ^ 2 / n₁ + σ₂ ^ 2 / n₂ := sq_sqrt hV.le
  rw [← e] at h
  exact hasLaw_standardize (sqrt_pos.2 hV) h

/-- OpenStax Introductory Statistics 2e §13.4 (ST-117). For independent normal samples of sizes
`n₁, n₂ ≥ 2`, the ratio `(s₁²/σ₁²) / (s₂²/σ₂²)` has the F distribution with `n₁ - 1` numerator and
`n₂ - 1` denominator degrees of freedom. -/
@[kb "openstaxintrostats2e" "§13.4, p. 701"]
theorem hasLaw_varianceRatio (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂) (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂)
    (hX : IsNormalSample X μ₁ σ₁ P) (hY : IsNormalSample Y μ₂ σ₂ P)
    (hind : IndepFun (fun ω i ↦ X i ω) (fun ω j ↦ Y j ω) P) :
    HasLaw (fun ω ↦ (sampleVariance (fun i ↦ X i ω) / σ₁ ^ 2) /
        (sampleVariance (fun j ↦ Y j ω) / σ₂ ^ 2))
      (fDistribution ((n₁ : ℝ) - 1) ((n₂ : ℝ) - 1)) P := by
  have h1 : (0 : ℝ) < (n₁ : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n₁ := by exact_mod_cast hn₁
    linarith
  have h2 : (0 : ℝ) < (n₂ : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n₂ := by exact_mod_cast hn₂
    linarith
  have hU := hasLaw_sampleVariance_chiSquared hn₁ hσ₁ hX
  have hV := hasLaw_sampleVariance_chiSquared hn₂ hσ₂ hY
  have hind' : IndepFun
      (fun ω ↦ ((n₁ : ℝ) - 1) * sampleVariance (fun i ↦ X i ω) / σ₁ ^ 2)
      (fun ω ↦ ((n₂ : ℝ) - 1) * sampleVariance (fun j ↦ Y j ω) / σ₂ ^ 2) P :=
    hind.comp
      (show Measurable (fun v : Fin n₁ → ℝ ↦ ((n₁ : ℝ) - 1) * sampleVariance v / σ₁ ^ 2) by
        have := measurable_sampleVariance' (n := n₁); fun_prop)
      (show Measurable (fun v : Fin n₂ → ℝ ↦ ((n₂ : ℝ) - 1) * sampleVariance v / σ₂ ^ 2) by
        have := measurable_sampleVariance' (n := n₂); fun_prop)
  have h := hasLaw_fDistribution h1 h2 hU hV hind'
  have frac : ∀ d s σ2 : ℝ, d ≠ 0 → d * s / σ2 / d = s / σ2 := by
    intro d s σ2 hd; field_simp
  convert h using 1
  funext ω
  rw [frac _ _ _ h1.ne', frac _ _ _ h2.ne']

end TwoSamples

end UndergradKB.Statistics
