import UndergradKB.Statistics.Regression
import UndergradKB.Statistics.CorrelationTest
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Remarks

/-!
# Course layer, chapter 12 (OpenStax *Introductory Statistics 2e*): linear regression and
correlation
-/

namespace UndergradKB.Statistics.Course.C12

open MeasureTheory ProbabilityTheory UndergradKB.Statistics

variable {n : ℕ}

/-- OpenStax Introductory Statistics 2e §12.1 (ST-102). Along the line `y = a + b x`, moving from
`x₁` to `x₂` changes `y` by `b (x₂ - x₁)`. -/
@[kb "openstaxintrostats2e" "§12.1, p. 628"]
theorem line_change_along_x (a b x₁ x₂ : ℝ) : (a + b * x₂) - (a + b * x₁) = b * (x₂ - x₁) :=
  line_change a b x₁ x₂

/-- OpenStax Introductory Statistics 2e §12.1 (ST-102). A one-unit increase in `x` changes the value
of the line `y = a + b x` by exactly the slope `b`. -/
@[kb "openstaxintrostats2e" "§12.1, p. 628"]
theorem slope_is_change_per_unit_x (a b x : ℝ) : (a + b * (x + 1)) - (a + b * x) = b :=
  line_unit_change a b x

/-- OpenStax Introductory Statistics 2e §12.3 (ST-103). The least-squares line
`ŷ = a + b x` with `b = Sxy / Sxx` and `a = ȳ - b x̄` has the smallest sum of squared errors (SSE)
among all lines. -/
@[kb "openstaxintrostats2e" "§12.3, p. 634"]
theorem least_squares_line_minimizes_sse (x y : Fin n → ℝ) (hx : sumSqDev x ≠ 0) (a b : ℝ) :
    sse x y (intercept x y) (slope x y) ≤ sse x y a b :=
  sse_intercept_slope_le x y hx a b

/-- OpenStax Introductory Statistics 2e §12.3 (ST-103). The least-squares line is the only line
attaining the minimal sum of squared errors. -/
@[kb "openstaxintrostats2e" "§12.3, p. 634"]
theorem least_squares_line_unique (x y : Fin n → ℝ) (hx : sumSqDev x ≠ 0) (a b : ℝ)
    (h : sse x y a b = sse x y (intercept x y) (slope x y)) :
    a = intercept x y ∧ b = slope x y :=
  eq_intercept_slope_of_sse_eq x y hx a b h

/-- OpenStax Introductory Statistics 2e §12.3 (ST-104). The least-squares line passes through the
point of means `(x̄, ȳ)`. -/
@[kb "openstaxintrostats2e" "§12.3, p. 634"]
theorem least_squares_line_through_means (x y : Fin n → ℝ) :
    intercept x y + slope x y * mean x = mean y :=
  intercept_add_slope_mul_mean x y

/-- OpenStax Introductory Statistics 2e §12.3 (ST-104). The residuals of the least-squares line
sum to zero. -/
@[kb "openstaxintrostats2e" "§12.3, p. 634"]
theorem residuals_sum_to_zero (x y : Fin n → ℝ) :
    ∑ i, (y i - (intercept x y + slope x y * x i)) = 0 :=
  sum_residual_eq_zero x y

/-- OpenStax Introductory Statistics 2e §12.3 (ST-105). The slope equals `r s_y / s_x`, where `r`
is the sample correlation coefficient and `s_x`, `s_y` are the sample standard deviations. -/
@[kb "openstaxintrostats2e" "§12.3, p. 634"]
theorem slope_equals_r_times_sy_over_sx (x y : Fin n → ℝ) (hn : 2 ≤ n) (hx : 0 < sumSqDev x)
    (hy : 0 < sumSqDev y) :
    slope x y = correlation x y * sampleStdDev y / sampleStdDev x :=
  slope_eq_correlation_mul x y hn hx hy

/-- OpenStax Introductory Statistics 2e §12.3 (ST-106). The correlation coefficient satisfies
`-1 ≤ r ≤ 1`. -/
@[kb "openstaxintrostats2e" "§12.3, p. 634"]
theorem correlation_between_neg_one_and_one (x y : Fin n → ℝ) :
    -1 ≤ correlation x y ∧ correlation x y ≤ 1 :=
  correlation_mem_Icc x y

/-- OpenStax Introductory Statistics 2e §12.3 (ST-107). `r = 1` exactly when all the points lie on
a line with positive slope. -/
@[kb "openstaxintrostats2e" "§12.3, p. 634"]
theorem correlation_one_iff_points_on_line_positive_slope (x y : Fin n → ℝ) (hx : 0 < sumSqDev x)
    (hy : 0 < sumSqDev y) :
    correlation x y = 1 ↔ ∃ a b : ℝ, 0 < b ∧ ∀ i, y i = a + b * x i :=
  correlation_eq_one_iff x y hx hy

/-- OpenStax Introductory Statistics 2e §12.3 (ST-107). `r = -1` exactly when all the points lie on
a line with negative slope. -/
@[kb "openstaxintrostats2e" "§12.3, p. 634"]
theorem correlation_neg_one_iff_points_on_line_negative_slope (x y : Fin n → ℝ)
    (hx : 0 < sumSqDev x) (hy : 0 < sumSqDev y) :
    correlation x y = -1 ↔ ∃ a b : ℝ, b < 0 ∧ ∀ i, y i = a + b * x i :=
  correlation_eq_neg_one_iff x y hx hy

/-- OpenStax Introductory Statistics 2e §12.3 (ST-108). The total variation of `y` splits into the
variation explained by the regression line and the unexplained variation: `SST = SSR + SSE`. -/
@[kb "openstaxintrostats2e" "§12.3, p. 634"]
theorem total_variation_explained_plus_unexplained (x y : Fin n → ℝ) (hx : sumSqDev x ≠ 0) :
    sumSqDev y = ∑ i, (intercept x y + slope x y * x i - mean y) ^ 2
      + sse x y (intercept x y) (slope x y) :=
  sumSqDev_eq_ssr_add_sse x y hx

/-- OpenStax Introductory Statistics 2e §12.3 (ST-108). The coefficient of determination `r²` is
the fraction `SSR / SST` of the variation of `y` explained by the regression line. -/
@[kb "openstaxintrostats2e" "§12.3, p. 634"]
theorem coefficient_of_determination_is_explained_fraction (x y : Fin n → ℝ) (hx : 0 < sumSqDev x)
    (hy : 0 < sumSqDev y) :
    correlation x y ^ 2
      = (∑ i, (intercept x y + slope x y * x i - mean y) ^ 2) / sumSqDev y :=
  correlation_sq_eq_ssr_div x y hx hy

/-- OpenStax Introductory Statistics 2e §12.4 (ST-109). Test for the significance of `r`: under
`H₀` (`ρ = 0`, normal `y` values), `t = r √(n - 2) / √(1 - r²)` has the Student t distribution with
`n - 2` degrees of freedom. -/
@[kb "openstaxintrostats2e" "§12.4, p. 642"]
theorem correlation_t_statistic_law {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (x : Fin n → ℝ) (hx : 0 < sumSqDev x) (hn : 3 ≤ n)
    {Y : Fin n → Ω → ℝ} {μ σ : ℝ} (hσ : 0 < σ) (hY : IsNormalSample Y μ σ P) :
    HasLaw (fun ω ↦ correlation x (fun i ↦ Y i ω) * √((n : ℝ) - 2) /
      √(1 - correlation x (fun i ↦ Y i ω) ^ 2)) (studentT ((n : ℝ) - 2)) P :=
  hasLaw_correlation_tStatistic x hx hn hσ hY

/-- OpenStax Introductory Statistics 2e §12.5 (ST-110). The standard error of the estimate
`s = √(SSE / (n - 2))` equals `√((1 - r²) Syy / (n - 2))`. -/
@[kb "openstaxintrostats2e" "§12.5, p. 646"]
theorem standard_error_of_estimate_formula (x y : Fin n → ℝ) (hx : 0 < sumSqDev x)
    (hy : 0 < sumSqDev y) :
    stdErrorEstimate x y
      = Real.sqrt ((1 - correlation x y ^ 2) * sumSqDev y / ((n : ℝ) - 2)) :=
  stdErrorEstimate_eq x y hx hy

end UndergradKB.Statistics.Course.C12
