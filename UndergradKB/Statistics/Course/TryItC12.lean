import Mathlib.Data.Fin.VecNotation
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Data
import UndergradKB.Statistics.Regression

/-!
# "Try It" exercises, chapter 12 (OpenStax *Introductory Statistics 2e*): linear regression and correlation

Least-squares lines, correlation coefficients, coefficients of determination, predictions and the
outlier rule for the data of the Try It exercises of chapter 12, computed from the repository
definitions `mean`, `sumSqDev`, `sumProdDev`, `slope`, `intercept`, `correlation`, `sse` and
`stdErrorEstimate`. The critical values of the correlation coefficient are the book's table values.
-/

namespace UndergradKB.Statistics.Course.TryItC12

open UndergradKB.Statistics

private lemma corr_bounds {A B lo hi : ℝ} (hA : 0 < A) (hB : 0 < B) (_hlo : 0 < lo) (hhi : 0 < hi)
    (h1 : lo ^ 2 * B < A ^ 2) (h2 : A ^ 2 < hi ^ 2 * B) : lo < A / Real.sqrt B ∧ A / Real.sqrt B < hi := by
  have hs : 0 < Real.sqrt B := Real.sqrt_pos.2 hB
  have hsq : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB.le
  constructor
  · rw [lt_div_iff₀ hs]
    by_contra h
    rw [not_lt] at h
    nlinarith [mul_nonneg hs.le _hlo.le, mul_self_nonneg (lo * Real.sqrt B - A)]
  · rw [div_lt_iff₀ hs]
    by_contra h
    rw [not_lt] at h
    nlinarith [mul_nonneg hs.le hhi.le, mul_self_nonneg (hi * Real.sqrt B - A)]

/-! ### Section 12.1: linear equations -/

/-- OpenStax Introductory Statistics 2e Try It 12.1. The function `x ↦ -0.125 - 3.5 x` has the form
`a + b x` with `a = -0.125` and `b = -3.5`, so it is a linear equation; its graph has slope `-3.5`
(each unit step in `x` lowers `y` by `3.5`) and meets the `y`-axis at `-0.125`. -/
@[kb "openstaxintrostats2e" "Try It 12.1, p. 630"]
theorem tryit_12_1_linear_equation :
    ∃ a b : ℝ, (∀ x : ℝ, -0.125 - 3.5 * x = a + b * x) ∧ a = -0.125 ∧ b = -3.5 ∧
      ∀ x : ℝ, (-0.125 - 3.5 * (x + 1)) - (-0.125 - 3.5 * x) = b := by
  refine ⟨-0.125, -3.5, fun x => by ring, rfl, rfl, fun x => by ring⟩

/-- The total cost (dollars) of a hang-gliding class with `n` students: a fee of `50` plus `20` per
student (Try It 12.3). -/
def gliderCost (n : ℝ) : ℝ := 50 + 20 * n

/-- OpenStax Introductory Statistics 2e Try It 12.3. The cost of a class with `n` students is
`y = 50 + 20 n`: the cost with no students is the fee `50`, and every added student adds exactly
`20`. -/
@[kb "openstaxintrostats2e" "Try It 12.3, p. 631"]
theorem tryit_12_3_hang_gliding_cost :
    (∀ n : ℝ, gliderCost n = 50 + 20 * n) ∧ gliderCost 0 = 50 ∧
      ∀ n : ℝ, gliderCost (n + 1) - gliderCost n = 20 := by
  refine ⟨fun n => rfl, by simp [gliderCost], fun n => by simp only [gliderCost]; ring⟩

/-- The amount (dollars) Ethan earns for a visit of `x` hours: `25 + 20 x` (Try It 12.4). -/
def repairEarnings (x : ℝ) : ℝ := 25 + 20 * x

/-- OpenStax Introductory Statistics 2e Try It 12.4. For the equation `y = 25 + 20 x` (hours `x`
independent, earnings `y` dependent) the `y`-intercept is `25` (the earnings of a visit of length
zero, the fixed charge) and the slope is `20` (the extra earnings per hour of work). -/
@[kb "openstaxintrostats2e" "Try It 12.4, p. 632"]
theorem tryit_12_4_repair_visit :
    repairEarnings 0 = 25 ∧ ∀ x : ℝ, repairEarnings (x + 1) - repairEarnings x = 20 := by
  refine ⟨by simp [repairEarnings], fun x => by simp only [repairEarnings]; ring⟩

/-! ### Section 12.2: Amelia's jump shot -/

/-- Hours of jump-shot practice per week (Try It 12.5). -/
noncomputable def practiceHours : Fin 6 → ℝ := ![5, 7, 9, 10, 11, 12]

/-- Points scored in a game (Try It 12.5). -/
noncomputable def pointsScored : Fin 6 → ℝ := ![15, 22, 28, 31, 33, 36]

private lemma ph_mean : mean practiceHours = 9 := by
  simp [mean, practiceHours, Fin.sum_univ_succ]; norm_num

private lemma ps_mean : mean pointsScored = 55 / 2 := by
  simp [mean, pointsScored, Fin.sum_univ_succ]; norm_num

private lemma ph_sxx : sumSqDev practiceHours = 34 := by
  simp only [sumSqDev, ph_mean]; simp [practiceHours, Fin.sum_univ_succ]; norm_num

private lemma ps_syy : sumSqDev pointsScored = 603 / 2 := by
  simp only [sumSqDev, ps_mean]; simp [pointsScored, Fin.sum_univ_succ]; norm_num

private lemma phs_sxy : sumProdDev practiceHours pointsScored = 101 := by
  simp only [sumProdDev, ph_mean, ps_mean]; simp [practiceHours, pointsScored, Fin.sum_univ_succ]
  norm_num

/-- OpenStax Introductory Statistics 2e Try It 12.5. For the six pairs (hours, points) =
(5, 15), (7, 22), (9, 28), (10, 31), (11, 33), (12, 36) the least-squares slope is exactly
`101/34` (about `2.97` points per extra hour) and the intercept exactly `13/17`; the correlation lies
strictly between `0.9975` and `0.9976`, a strong positive linear relation, which supports Amelia's
belief that more practice goes with more points. -/
@[kb "openstaxintrostats2e" "Try It 12.5, p. 633"]
theorem tryit_12_5_jump_shot :
    slope practiceHours pointsScored = 101 / 34 ∧ intercept practiceHours pointsScored = 13 / 17 ∧
      0 < slope practiceHours pointsScored ∧
      0.9975 < correlation practiceHours pointsScored ∧
      correlation practiceHours pointsScored < 0.9976 := by
  have hs : slope practiceHours pointsScored = 101 / 34 := by rw [slope, phs_sxy, ph_sxx]
  refine ⟨hs, ?_, by rw [hs]; norm_num, ?_⟩
  · rw [intercept, hs, ph_mean, ps_mean]; norm_num
  · unfold correlation
    rw [phs_sxy, ph_sxx, ps_syy]
    exact corr_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)

/-! ### Section 12.3: the regression equation -/

/-- Depths in feet (Try It 12.6). -/
noncomputable def diveDepth : Fin 6 → ℝ := ![50, 60, 70, 80, 90, 100]

/-- Maximum dive times in minutes (Try It 12.6). -/
noncomputable def diveTime : Fin 6 → ℝ := ![80, 55, 45, 35, 25, 22]

private lemma dd_mean : mean diveDepth = 75 := by
  simp [mean, diveDepth, Fin.sum_univ_succ]; norm_num

private lemma dt_mean : mean diveTime = 131 / 3 := by
  simp [mean, diveTime, Fin.sum_univ_succ]; norm_num

private lemma dd_sxx : sumSqDev diveDepth = 1750 := by
  simp only [sumSqDev, dd_mean]; simp [diveDepth, Fin.sum_univ_succ]; norm_num

private lemma dt_syy : sumSqDev diveTime = 7030 / 3 := by
  simp only [sumSqDev, dt_mean]; simp [diveTime, Fin.sum_univ_succ]; norm_num

private lemma dive_sxy : sumProdDev diveDepth diveTime = -1950 := by
  simp only [sumProdDev, dd_mean, dt_mean]; simp [diveDepth, diveTime, Fin.sum_univ_succ]; norm_num

private lemma dive_slope : slope diveDepth diveTime = -39 / 35 := by
  rw [slope, dive_sxy, dd_sxx]; norm_num

private lemma dive_intercept : intercept diveDepth diveTime = 2672 / 21 := by
  rw [intercept, dive_slope, dd_mean, dt_mean]; norm_num

/-- OpenStax Introductory Statistics 2e Try It 12.6. The least-squares line of maximum dive time on
depth has slope exactly `-39/35` (about `-1.114` minutes per foot) and intercept exactly `2672/21`
(about `127.24`); the correlation is negative and lies strictly between `-0.9630` and `-0.9629`. -/
@[kb "openstaxintrostats2e" "Try It 12.6, p. 636"]
theorem tryit_12_6_dive_line :
    slope diveDepth diveTime = -39 / 35 ∧ intercept diveDepth diveTime = 2672 / 21 ∧
      -0.9630 < correlation diveDepth diveTime ∧ correlation diveDepth diveTime < -0.9629 := by
  refine ⟨dive_slope, dive_intercept, ?_⟩
  have hsq := correlation_sq (x := diveDepth) (y := diveTime) (by rw [dd_sxx]; norm_num)
    (by rw [dt_syy]; norm_num)
  rw [dive_sxy, dd_sxx, dt_syy] at hsq
  have hneg : correlation diveDepth diveTime < 0 := by
    unfold correlation
    rw [dive_sxy]
    exact div_neg_of_neg_of_pos (by norm_num) (Real.sqrt_pos.2 (by rw [dd_sxx, dt_syy]; norm_num))
  generalize correlation diveDepth diveTime = r at hsq hneg ⊢
  norm_num at hsq
  constructor <;> nlinarith

/-- OpenStax Introductory Statistics 2e Try It 12.6 (prediction). The least-squares line predicts a
maximum dive time of exactly `14/3` minutes (about `4.67`) at a depth of `110` feet. -/
@[kb "openstaxintrostats2e" "Try It 12.6, p. 636"]
theorem tryit_12_6_dive_prediction :
    intercept diveDepth diveTime + slope diveDepth diveTime * 110 = 14 / 3 := by
  rw [dive_intercept, dive_slope]; norm_num

/-! ### Section 12.5: testing the correlation coefficient (critical values of the book's table) -/

/-- OpenStax Introductory Statistics 2e Try It 12.7. With `r = 0.6501` from `n = 12` points the
degrees of freedom are `10`; the book's table critical value `0.576` is exceeded by `|r|`, so `r` is
significant and the line may be used for prediction. -/
@[kb "openstaxintrostats2e" "Try It 12.7, p. 645"]
theorem tryit_12_7_significant_r :
    (12 : ℕ) - 2 = 10 ∧ (0.576 : ℝ) < |(0.6501 : ℝ)| := by
  refine ⟨by norm_num, ?_⟩
  rw [abs_of_pos (by norm_num)]; norm_num

/-- OpenStax Introductory Statistics 2e Try It 12.8. With `r = 0.5204` from `n = 9` points the
degrees of freedom are `7`; `|r|` does not exceed the book's critical value `0.666`, so `r` is not
significant and the line should not be used for prediction. -/
@[kb "openstaxintrostats2e" "Try It 12.8, p. 645"]
theorem tryit_12_8_r_not_significant :
    (9 : ℕ) - 2 = 7 ∧ |(0.5204 : ℝ)| < 0.666 := by
  refine ⟨by norm_num, ?_⟩
  rw [abs_of_pos (by norm_num)]; norm_num

/-- OpenStax Introductory Statistics 2e Try It 12.9. With `r = -0.7204` from `n = 8` points the
degrees of freedom are `6`; `|r| = 0.7204` exceeds the critical value `0.707`, so `r` is significant
and the line may be used for prediction. -/
@[kb "openstaxintrostats2e" "Try It 12.9, p. 646"]
theorem tryit_12_9_negative_r_significant :
    (8 : ℕ) - 2 = 6 ∧ (0.707 : ℝ) < |(-0.7204 : ℝ)| := by
  refine ⟨by norm_num, ?_⟩
  rw [abs_of_neg (by norm_num)]; norm_num

/-- OpenStax Introductory Statistics 2e Try It 12.10. With `r = 0` from `n = 100` points the degrees
of freedom are `98`; `|r| = 0` lies below the book's table value (`0.195` for `100` degrees of
freedom, and in any case any positive critical value), so `r` is not significant and the line should
not be used for prediction. -/
@[kb "openstaxintrostats2e" "Try It 12.10, p. 646"]
theorem tryit_12_10_zero_r :
    (100 : ℕ) - 2 = 98 ∧ |(0 : ℝ)| < 0.195 := by
  refine ⟨by norm_num, by norm_num⟩

/-! ### Section 12.5: prediction -/

/-- OpenStax Introductory Statistics 2e Try It 12.11. The line `ŷ = 72.5 + 2.8 x` predicts a math-test
score of exactly `86.5` for `x = 5` hours of practice per week. -/
@[kb "openstaxintrostats2e" "Try It 12.11, p. 648"]
theorem tryit_12_11_math_score_prediction : (72.5 + 2.8 * 5 : ℝ) = 86.5 := by norm_num

/-! ### Section 12.6: outliers -/

/-- The `x` values of the ten points of Try It 12.13. -/
noncomputable def outX : Fin 10 → ℝ := ![1, 2, 2, 3, 4, 4, 5, 6, 7, 7]

/-- The `y` values of the ten points of Try It 12.13. -/
noncomputable def outY : Fin 10 → ℝ := ![5, 7, 6, 9, 12, 13, 18, 19, 12, 21]

private lemma ox_mean : mean outX = 41 / 10 := by
  simp [mean, outX, Fin.sum_univ_succ]; norm_num

private lemma oy_mean : mean outY = 61 / 5 := by
  simp [mean, outY, Fin.sum_univ_succ]; norm_num

private lemma o_sxx : sumSqDev outX = 409 / 10 := by
  simp only [sumSqDev, ox_mean]; simp [outX, Fin.sum_univ_succ]; norm_num

private lemma o_sxy : sumProdDev outX outY = 464 / 5 := by
  simp only [sumProdDev, ox_mean, oy_mean]; simp [outX, outY, Fin.sum_univ_succ]; norm_num

private lemma o_slope : slope outX outY = 928 / 409 := by
  rw [slope, o_sxy, o_sxx]; norm_num

private lemma o_intercept : intercept outX outY = 1185 / 409 := by
  rw [intercept, o_slope, ox_mean, oy_mean]; norm_num

private lemma o_sse : sse outX outY (intercept outX outY) (slope outX outY) = 30692 / 409 := by
  rw [o_intercept, o_slope]
  simp [sse, outX, outY, Fin.sum_univ_succ]
  norm_num

private lemma o_se_bounds : 3.062 < stdErrorEstimate outX outY ∧ stdErrorEstimate outX outY < 3.063 := by
  unfold stdErrorEstimate
  rw [o_sse]
  have h : ((10 : ℕ) : ℝ) - 2 = 8 := by norm_num
  rw [h]
  exact ⟨(Real.lt_sqrt (by norm_num)).2 (by norm_num), (Real.sqrt_lt' (by norm_num)).2 (by norm_num)⟩

/-- OpenStax Introductory Statistics 2e Try It 12.13 (finding the outlier). For the ten points the
least-squares line is `ŷ = 1185/409 + (928/409) x`, with sum of squared errors `30692/409` and
standard error of the estimate between `3.062` and `3.063`. The point `(7, 12)` (index `8`) has a
residual of absolute value above twice that standard error, while all the other nine points have
residuals below it: it is the outlier. -/
@[kb "openstaxintrostats2e" "Try It 12.13, p. 652"]
theorem tryit_12_13_outlier :
    slope outX outY = 928 / 409 ∧ intercept outX outY = 1185 / 409 ∧
      sse outX outY (intercept outX outY) (slope outX outY) = 30692 / 409 ∧
      2 * stdErrorEstimate outX outY <
        |outY 8 - (intercept outX outY + slope outX outY * outX 8)| ∧
      ∀ i : Fin 10, i ≠ 8 →
        |outY i - (intercept outX outY + slope outX outY * outX i)| <
          2 * stdErrorEstimate outX outY := by
  obtain ⟨h1, h2⟩ := o_se_bounds
  refine ⟨o_slope, o_intercept, o_sse, ?_, ?_⟩
  · rw [o_intercept, o_slope]
    generalize stdErrorEstimate outX outY = s at h1 h2 ⊢
    simp [outX, outY]
    rw [abs_of_neg (by norm_num)]
    linarith
  · intro i hi
    rw [o_intercept, o_slope]
    generalize stdErrorEstimate outX outY = s at h1 h2 ⊢
    fin_cases i
    all_goals first
      | exact absurd rfl hi
      | (simp [outX, outY, abs_lt]; constructor <;> linarith)

/-- The `x` values of Try It 12.13 with the outlier `(7, 12)` removed. -/
noncomputable def cleanX : Fin 9 → ℝ := ![1, 2, 2, 3, 4, 4, 5, 6, 7]

/-- The `y` values of Try It 12.13 with the outlier `(7, 12)` removed. -/
noncomputable def cleanY : Fin 9 → ℝ := ![5, 7, 6, 9, 12, 13, 18, 19, 21]

private lemma cx_mean : mean cleanX = 34 / 9 := by
  simp [mean, cleanX, Fin.sum_univ_succ]; norm_num

private lemma cy_mean : mean cleanY = 110 / 9 := by
  simp [mean, cleanY, Fin.sum_univ_succ]; norm_num

private lemma c_sxx : sumSqDev cleanX = 284 / 9 := by
  simp only [sumSqDev, cx_mean]; simp [cleanX, Fin.sum_univ_succ]; norm_num

private lemma c_syy : sumSqDev cleanY = 2570 / 9 := by
  simp only [sumSqDev, cy_mean]; simp [cleanY, Fin.sum_univ_succ]; norm_num

private lemma c_sxy : sumProdDev cleanX cleanY = 841 / 9 := by
  simp only [sumProdDev, cx_mean, cy_mean]; simp [cleanX, cleanY, Fin.sum_univ_succ]; norm_num

private lemma c_slope : slope cleanX cleanY = 841 / 284 := by
  rw [slope, c_sxy, c_sxx]; norm_num

private lemma c_intercept : intercept cleanX cleanY = 147 / 142 := by
  rw [intercept, c_slope, cx_mean, cy_mean]; norm_num

/-- OpenStax Introductory Statistics 2e Try It 12.13. Without the outlier `(7, 12)` the nine
remaining points have least-squares line `ŷ = 147/142 + (841/284) x` (slope about `2.96`, intercept
about `1.04`) and correlation strictly between `0.9843` and `0.9844`; the line predicts exactly
`2176/71` (about `30.65`) at `x = 10`. -/
@[kb "openstaxintrostats2e" "Try It 12.13, p. 652"]
theorem tryit_12_13_line_without_outlier :
    slope cleanX cleanY = 841 / 284 ∧ intercept cleanX cleanY = 147 / 142 ∧
      0.9843 < correlation cleanX cleanY ∧ correlation cleanX cleanY < 0.9844 ∧
      intercept cleanX cleanY + slope cleanX cleanY * 10 = 2176 / 71 := by
  refine ⟨c_slope, c_intercept, ?_, ?_, ?_⟩
  · unfold correlation
    rw [c_sxy, c_sxx, c_syy]
    exact (corr_bounds (lo := 0.9843) (hi := 0.9844) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)).1
  · unfold correlation
    rw [c_sxy, c_sxx, c_syy]
    exact (corr_bounds (lo := 0.9843) (hi := 0.9844) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)).2
  · rw [c_intercept, c_slope]; norm_num

/-! ### Try It 12.14: per capita income -/

/-- Years of Try It 12.14. -/
noncomputable def incYear : Fin 10 → ℝ := ![1870, 1880, 1890, 1900, 1910, 1920, 1930, 1940, 1950, 1960]

/-- Per capita income of Try It 12.14. -/
noncomputable def incPcinc : Fin 10 → ℝ := ![340, 499, 592, 757, 927, 1050, 1170, 1364, 1836, 2132]

private lemma iy_mean : mean incYear = 1915 := by
  simp [mean, incYear, Fin.sum_univ_succ]; norm_num

private lemma ip_mean : mean incPcinc = 10667 / 10 := by
  simp [mean, incPcinc, Fin.sum_univ_succ]; norm_num

private lemma i_sxx : sumSqDev incYear = 8250 := by
  simp only [sumSqDev, iy_mean]; simp [incYear, Fin.sum_univ_succ]; norm_num

private lemma i_syy : sumSqDev incPcinc = 30171701 / 10 := by
  simp only [sumSqDev, ip_mean]; simp [incPcinc, Fin.sum_univ_succ]; norm_num

private lemma i_sxy : sumProdDev incYear incPcinc = 153545 := by
  simp only [sumProdDev, iy_mean, ip_mean]; simp [incYear, incPcinc, Fin.sum_univ_succ]; norm_num

private lemma i_slope : slope incYear incPcinc = 30709 / 1650 := by
  rw [slope, i_sxy, i_sxx]; norm_num

private lemma i_intercept : intercept incYear incPcinc = -5704768 / 165 := by
  rw [intercept, i_slope, iy_mean, ip_mean]; norm_num

private lemma i_sse : sse incYear incPcinc (intercept incYear incPcinc) (slope incYear incPcinc) =
    26311726 / 165 := by
  rw [i_intercept, i_slope]
  simp [sse, incYear, incPcinc, Fin.sum_univ_succ]
  norm_num

private lemma i_se_bounds :
    141.18 < stdErrorEstimate incYear incPcinc ∧ stdErrorEstimate incYear incPcinc < 141.19 := by
  unfold stdErrorEstimate
  rw [i_sse]
  have h : ((10 : ℕ) : ℝ) - 2 = 8 := by norm_num
  rw [h]
  exact ⟨(Real.lt_sqrt (by norm_num)).2 (by norm_num), (Real.sqrt_lt' (by norm_num)).2 (by norm_num)⟩

/-- OpenStax Introductory Statistics 2e Try It 12.14 (independent and dependent variables, line,
correlation). With the year as independent variable and the per capita income as dependent variable,
the least-squares line has slope exactly `30709/1650` (about `18.61` per year) and intercept
`-5704768/165`; the correlation lies strictly between `0.9732` and `0.9733`. -/
@[kb "openstaxintrostats2e" "Try It 12.14, p. 654"]
theorem tryit_12_14_income_line :
    slope incYear incPcinc = 30709 / 1650 ∧ intercept incYear incPcinc = -5704768 / 165 ∧
      0.9732 < correlation incYear incPcinc ∧ correlation incYear incPcinc < 0.9733 := by
  refine ⟨i_slope, i_intercept, ?_⟩
  unfold correlation
  rw [i_sxy, i_sxx, i_syy]
  exact corr_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- OpenStax Introductory Statistics 2e Try It 12.14 (significance, determination). The correlation
`r` of the income data exceeds the book's table critical value `0.632` for `8` degrees of freedom
(`10` points), and the coefficient of determination is `r² = 153545² / (8250 · 30171701/10)`,
strictly between `0.9471` and `0.9472`: about `94.7%` of the variation in income is explained by the
line. -/
@[kb "openstaxintrostats2e" "Try It 12.14, p. 654"]
theorem tryit_12_14_income_correlation_significant :
    0.632 < correlation incYear incPcinc ∧
      correlation incYear incPcinc ^ 2 = 153545 ^ 2 / (8250 * (30171701 / 10)) ∧
      0.9471 < correlation incYear incPcinc ^ 2 ∧ correlation incYear incPcinc ^ 2 < 0.9472 := by
  have hsq := correlation_sq (x := incYear) (y := incPcinc) (by rw [i_sxx]; norm_num)
    (by rw [i_syy]; norm_num)
  rw [i_sxy, i_sxx, i_syy] at hsq
  have hr : 0.9732 < correlation incYear incPcinc := by
    unfold correlation
    rw [i_sxy, i_sxx, i_syy]
    exact (corr_bounds (lo := 0.9732) (hi := 0.9733) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)).1
  refine ⟨by linarith, hsq, ?_, ?_⟩ <;> rw [hsq] <;> norm_num

/-- OpenStax Introductory Statistics 2e Try It 12.14 (estimates). The least-squares line estimates a
per capita income strictly between `787.52` and `787.53` for 1900 (an observed year, actual value
`757`) and strictly between `2648.67` and `2648.68` for 2000 (an extrapolation beyond the data, which
end in 1960). -/
@[kb "openstaxintrostats2e" "Try It 12.14, p. 654"]
theorem tryit_12_14_income_estimates :
    (787.52 < intercept incYear incPcinc + slope incYear incPcinc * 1900 ∧
      intercept incYear incPcinc + slope incYear incPcinc * 1900 < 787.53) ∧
    (2648.67 < intercept incYear incPcinc + slope incYear incPcinc * 2000 ∧
      intercept incYear incPcinc + slope incYear incPcinc * 2000 < 2648.68) := by
  rw [i_intercept, i_slope]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> norm_num

/-- OpenStax Introductory Statistics 2e Try It 12.14 (slope). The slope of the line is `30709/1650`,
strictly between `18.61` and `18.62`: per capita income rises by about `18.6` per year on average. -/
@[kb "openstaxintrostats2e" "Try It 12.14, p. 654"]
theorem tryit_12_14_income_slope_meaning :
    18.61 < slope incYear incPcinc ∧ slope incYear incPcinc < 18.62 := by
  rw [i_slope]; constructor <;> norm_num

/-- OpenStax Introductory Statistics 2e Try It 12.14 (outliers). The standard error of the estimate
lies strictly between `141.18` and `141.19`, and every residual of the line has absolute value below
twice that value (about `282.4`), so by the book's rule no point is an outlier. -/
@[kb "openstaxintrostats2e" "Try It 12.14, p. 654"]
theorem tryit_12_14_income_no_outliers :
    141.18 < stdErrorEstimate incYear incPcinc ∧ stdErrorEstimate incYear incPcinc < 141.19 ∧
      ∀ i : Fin 10,
        |incPcinc i - (intercept incYear incPcinc + slope incYear incPcinc * incYear i)| <
          2 * stdErrorEstimate incYear incPcinc := by
  obtain ⟨h1, h2⟩ := i_se_bounds
  refine ⟨h1, h2, ?_⟩
  intro i
  rw [i_intercept, i_slope]
  generalize stdErrorEstimate incYear incPcinc = s at h1 h2 ⊢
  fin_cases i
  all_goals (simp [incYear, incPcinc, abs_lt]; constructor <;> linarith)

end UndergradKB.Statistics.Course.TryItC12
