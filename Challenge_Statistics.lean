/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import UndergradKB.Statistics.NormalSample
import UndergradKB.Statistics.AnovaTest
import UndergradKB.Statistics.CorrelationTest

/-!
# Headline statements of undergraduate-math-lean 0.2.0: statistics (OpenStax *Introductory Statistics*)

The main results of this topic that Mathlib and Tau Ceti lack, one theorem each, with every proof a deliberate
`sorry`: the exact sampling distributions behind the textbook tests for normal samples. For a sample of independent
normal observations, the sample mean and the sample variance are independent and the scaled sample variance is
chi-square (Student's theorem); the t statistic has the Student t law; the F statistic of one-way analysis of
variance has the F law; and the t statistic of the sample correlation coefficient has the Student t law. To check
what is claimed, read this file. `Solution_Statistics.lean` proves the same statements from the library, and
`lake comparator` (configured by `comparator/Statistics.json`) checks that each proved statement is exactly the one
here and uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Each statement is the library's statement, copied. The statements were not yet reviewed by a human (see the README).

## Definitions used

Besides Mathlib (`HasLaw`, `IndepFun`, `iIndepFun`, `gaussianReal`, `gammaMeasure`), the statements use these
definitions of the library (namespace `UndergradKB.Statistics`); a reader checking a statement should check these
too:

* `IsNormalSample X μ σ P`: the `n` random variables `X i` are measurable, mutually independent, and each has the
  normal law with mean `μ` and variance `σ ^ 2`.
* `mean x = (∑ i, x i) / n`; `sumSqDev x = ∑ i, (x i - mean x) ^ 2`; `sampleVariance x = sumSqDev x / (n - 1)`;
  `sampleStdDev x = √(sampleVariance x)`; `sumProdDev x y = ∑ i, (x i - mean x) * (y i - mean y)`;
  `correlation x y = sumProdDev x y / √(sumSqDev x * sumSqDev y)` (data lists `x y : Fin n → ℝ`).
* `chiSquared k = gammaMeasure (k / 2) (1 / 2)`, the chi-square law with `k` degrees of freedom.
* `studentT ν`: Lebesgue measure with the Student t density
  `Γ((ν+1)/2) / (√(νπ) Γ(ν/2)) · (1 + x²/ν)^(-(ν+1)/2)`.
* `fDistribution d₁ d₂`: Lebesgue measure with the F density
  `Γ((d₁+d₂)/2) / (Γ(d₁/2) Γ(d₂/2)) · (d₁/d₂)^(d₁/2) · x^(d₁/2-1) · (1 + d₁x/d₂)^(-(d₁+d₂)/2)` for `x > 0`, and 0
  otherwise.
* For analysis of variance, `g : Fin n → Fin k` assigns each observation to one of `k` groups; `groupSize g j` is
  the size of group `j`, `groupMean x g j` its mean; `ssBetween x g = ∑ j, groupSize g j * (groupMean x g j -
  mean x) ^ 2`, `ssWithin x g = ∑ i, (x i - groupMean x g (g i)) ^ 2`; `msBetween = ssBetween / (k - 1)`,
  `msWithin = ssWithin / (n - k)`, and `fStatistic x g = msBetween x g / msWithin x g`.
-/

namespace UndergradKB.Headlines.Statistics

open MeasureTheory ProbabilityTheory Real Set Finset UndergradKB.Statistics

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n k : ℕ}

/-- **The sample mean and the sample variance of a normal sample are independent** (OpenStax *Introductory
Statistics* §§ 8.2, 11.6; Student's theorem). Related: Mathlib has no chi-square, Student t or F law; Tau
Ceti has these laws and the splitting of a standard Gaussian vector over orthogonal subspaces, but no statement about
the sample mean and sample variance. -/
theorem indepFun_sampleMean_sampleVariance [IsProbabilityMeasure P] {X : Fin n → Ω → ℝ} {μ σ : ℝ}
    (hn : 2 ≤ n) (hσ : 0 < σ) (hX : IsNormalSample X μ σ P) :
    IndepFun (fun ω ↦ mean fun i ↦ X i ω) (fun ω ↦ sampleVariance fun i ↦ X i ω) P := by
  sorry

/-- **The scaled sample variance of a normal sample is chi-square** (OpenStax *Introductory Statistics* § 11.6, the
test of a single variance): `(n - 1) s² / σ²` has the chi-square law with `n - 1` degrees of freedom. Related: as
above. -/
theorem hasLaw_sampleVariance_chiSquared [IsProbabilityMeasure P] {X : Fin n → Ω → ℝ} {μ σ : ℝ}
    (hn : 2 ≤ n) (hσ : 0 < σ) (hX : IsNormalSample X μ σ P) :
    HasLaw (fun ω ↦ ((n : ℝ) - 1) * (sampleVariance fun i ↦ X i ω) / σ ^ 2) (chiSquared ((n : ℝ) - 1)) P := by
  sorry

/-- **The t statistic of a normal sample has the Student t law** (OpenStax *Introductory Statistics* §§ 8.2, 9.3),
with `n - 1` degrees of freedom.
Related: Tau Ceti proves that a Gaussian over the square root of an independent chi-square variable is Student t,
but states nothing about a sample. -/
theorem hasLaw_tStatistic [IsProbabilityMeasure P] {X : Fin n → Ω → ℝ} {μ σ : ℝ} (hn : 2 ≤ n) (hσ : 0 < σ)
    (hX : IsNormalSample X μ σ P) :
    HasLaw (fun ω ↦ (mean (fun i ↦ X i ω) - μ) / (sampleStdDev (fun i ↦ X i ω) / √n))
      (studentT ((n : ℝ) - 1)) P := by
  sorry

/-- **The F test of one-way analysis of variance** (OpenStax *Introductory Statistics* § 13.2): when all `n` observations are independent and normal
with the same mean and variance (the null hypothesis), split into `k ≥ 2` nonempty groups, the F statistic has the F
law with `k - 1` and `n - k` degrees of freedom. Related: neither Mathlib nor Tau Ceti has analysis of variance. -/
theorem hasLaw_fStatistic [IsProbabilityMeasure P] (g : Fin n → Fin k) (hg : ∀ j, 0 < groupSize g j)
    (hk : 2 ≤ k) (hkn : k < n) {Y : Fin n → Ω → ℝ} {μ σ : ℝ} (hσ : 0 < σ)
    (hY : IsNormalSample Y μ σ P) :
    HasLaw (fun ω ↦ fStatistic (fun i ↦ Y i ω) g) (fDistribution ((k : ℝ) - 1) ((n : ℝ) - k)) P := by
  sorry

/-- **The t test of the correlation coefficient** (OpenStax *Introductory Statistics* § 12.4): for fixed, not all equal, predictor values `x` and
independent normal responses with a common mean (no linear relation: the null hypothesis, stated conditionally on
the predictors), `r √(n-2) / √(1-r²)` has the Student t law with `n - 2` degrees of freedom, where `r` is the sample
correlation coefficient. Related: neither Mathlib nor Tau Ceti has the sample correlation coefficient. -/
theorem hasLaw_correlation_tStatistic [IsProbabilityMeasure P] (x : Fin n → ℝ) (hx : 0 < sumSqDev x)
    (hn : 3 ≤ n) {Y : Fin n → Ω → ℝ} {μ σ : ℝ} (hσ : 0 < σ) (hY : IsNormalSample Y μ σ P) :
    HasLaw (fun ω ↦ correlation x (fun i ↦ Y i ω) * √((n : ℝ) - 2) /
      √(1 - correlation x (fun i ↦ Y i ω) ^ 2)) (studentT ((n : ℝ) - 2)) P := by
  sorry

end UndergradKB.Headlines.Statistics
