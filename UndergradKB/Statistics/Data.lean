import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Fin
import UndergradKB.Common.Attr

/-!
# Statistics of a finite data list

Bridging definitions for the descriptive statistics of OpenStax *Introductory Statistics 2e* (chapters 2 and 12):
a data list is `x : Fin n → ℝ`. Mathlib has the population notions for a probability law
(`ProbabilityTheory.variance`, `ProbabilityTheory.covariance`) but no sample mean, sample variance (divisor
`n - 1`) or sample correlation of a data list; these are defined here and used throughout the topic.
-/

namespace UndergradKB.Statistics

open Finset

variable {n : ℕ}

/-- The mean `x̄ = (x₁ + ⋯ + xₙ) / n` of a data list. -/
noncomputable def mean (x : Fin n → ℝ) : ℝ := (∑ i, x i) / n

/-- The sum of squared deviations from the mean, `∑ (xᵢ - x̄)²` (written `SS` or `Sxx`). -/
noncomputable def sumSqDev (x : Fin n → ℝ) : ℝ := ∑ i, (x i - mean x) ^ 2

/-- The sum of products of deviations, `∑ (xᵢ - x̄)(yᵢ - ȳ)` (written `Sxy`). -/
noncomputable def sumProdDev (x y : Fin n → ℝ) : ℝ := ∑ i, (x i - mean x) * (y i - mean y)

/-- The sample variance `s² = ∑ (xᵢ - x̄)² / (n - 1)`. -/
noncomputable def sampleVariance (x : Fin n → ℝ) : ℝ := sumSqDev x / ((n : ℝ) - 1)

/-- The sample standard deviation `s = √s²`. -/
noncomputable def sampleStdDev (x : Fin n → ℝ) : ℝ := Real.sqrt (sampleVariance x)

/-- The population variance `σ² = ∑ (xᵢ - μ)² / N` of a finite population listed as `x`. -/
noncomputable def populationVariance (x : Fin n → ℝ) : ℝ := sumSqDev x / n

/-- The population standard deviation `σ = √σ²`. -/
noncomputable def populationStdDev (x : Fin n → ℝ) : ℝ := Real.sqrt (populationVariance x)

/-- The sample correlation coefficient `r = Sxy / √(Sxx Syy)`. -/
noncomputable def correlation (x y : Fin n → ℝ) : ℝ :=
  sumProdDev x y / Real.sqrt (sumSqDev x * sumSqDev y)

/-- The z-score `(v - x̄) / s` of a value `v` relative to a data list (sample standard deviation). -/
noncomputable def zScore (x : Fin n → ℝ) (v : ℝ) : ℝ := (v - mean x) / sampleStdDev x

lemma sum_sub_mean (x : Fin n → ℝ) : ∑ i, (x i - mean x) = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have : (n : ℝ) ≠ 0 := by positivity
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mean]
  field_simp
  ring

end UndergradKB.Statistics
