import Mathlib.Data.Fin.VecNotation
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Data
import UndergradKB.Statistics.Regression

/-!
# Course layer, chapters 11 to 13 (OpenStax *Introductory Statistics 2e*): remaining worked examples

Linear equations read off exact data with the repository's `slope` and `intercept` (Examples
12.1 to 12.4), the critical-value method for the significance of a correlation coefficient
(Examples 12.7 to 12.10), the consumer-price-index regression (Example 12.14), a chi-square
statistic with merged categories (Example 11.1) and an `F` ratio (Example 13.5). Table values
(`t`, `F`, chi-square probabilities) are taken from the book and named as such.
-/

namespace UndergradKB.Statistics.Course.ExamplesC11C13b

open UndergradKB.Statistics

/-! ### Example 11.1 -/

/-- OpenStax Introductory Statistics 2e Example 11.1. After merging the last two classes (so every
expected count is at least five) the faculty expected `50, 30, 12, 8` of 100 students in the four
absence classes and the survey observed `35, 40, 20, 5`. The expected counts add up to 100, each is
at least 5, and the chi-square statistic is exactly `343/24`, strictly between `14.29` and `14.30`,
with `4 - 1 = 3` degrees of freedom. -/
@[kb "openstaxintrostats2e" "Example 11.1, p. 577"]
theorem example_11_1_absences_merged :
    (∑ i, (![50, 30, 12, 8] : Fin 4 → ℝ) i) = 100 ∧ (∀ i, 5 ≤ (![50, 30, 12, 8] : Fin 4 → ℝ) i) ∧
      (∑ i, ((![35, 40, 20, 5] : Fin 4 → ℝ) i - (![50, 30, 12, 8] : Fin 4 → ℝ) i) ^ 2 /
        (![50, 30, 12, 8] : Fin 4 → ℝ) i) = 343 / 24 ∧ 14.29 < (343 / 24 : ℝ) ∧ (343 / 24 : ℝ) < 14.30 ∧
      Fintype.card (Fin 4) - 1 = 3 := by
  refine ⟨?_, ?_, ?_, by norm_num, by norm_num, rfl⟩
  · simp [Fin.sum_univ_succ]; norm_num
  · intro i; fin_cases i <;> simp <;> norm_num
  · simp [Fin.sum_univ_succ]; norm_num

/-! ### Examples 12.1 to 12.4: linear equations -/

/-- OpenStax Introductory Statistics 2e Example 12.1. A line `y = a + b x` has intercept `a` (its value
at `x = 0`) and slope `b` (the change in `y` when `x` grows by one), for every `a` and `b`. -/
@[kb "openstaxintrostats2e" "Example 12.1, p. 630"]
theorem example_12_1_linear_equation (a b : ℝ) :
    (fun x : ℝ => a + b * x) 0 = a ∧ ∀ x : ℝ, (fun x : ℝ => a + b * x) (x + 1) -
      (fun x : ℝ => a + b * x) x = b := by
  refine ⟨by simp, fun x => by ring⟩

/-- OpenStax Introductory Statistics 2e Example 12.2. Four points of the line `y = -1 + 2x`, namely
`(0,-1), (1,1), (2,3), (3,5)`, have least-squares line with intercept `-1` and slope `2`, and
the line fits them with zero sum of squared errors. -/
@[kb "openstaxintrostats2e" "Example 12.2, p. 630"]
theorem example_12_2_line_through_points :
    intercept (![0, 1, 2, 3] : Fin 4 → ℝ) ![-1, 1, 3, 5] = -1 ∧
      slope (![0, 1, 2, 3] : Fin 4 → ℝ) ![-1, 1, 3, 5] = 2 ∧
      sse (![0, 1, 2, 3] : Fin 4 → ℝ) ![-1, 1, 3, 5] (-1) 2 = 0 := by
  have hs : slope (![0, 1, 2, 3] : Fin 4 → ℝ) ![-1, 1, 3, 5] = 2 := by
    simp [slope, sumProdDev, sumSqDev, mean, Fin.sum_univ_succ]; norm_num
  refine ⟨?_, hs, ?_⟩
  · simp only [intercept, hs]
    simp [mean, Fin.sum_univ_succ]; norm_num
  · simp [sse, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Example 12.3. The tax-preparation cost is `y = 31.50 + 32 x`
dollars for `x` hours. Billing for `1, 2, 3, 4` hours gives `63.5, 95.5, 127.5, 159.5`, and the
least-squares line through these four points has intercept `31.5` and slope `32`. -/
@[kb "openstaxintrostats2e" "Example 12.3, p. 631"]
theorem example_12_3_tax_cost_line :
    (∀ x : ℝ, (31.50 + 32 * x : ℝ) = 31.5 + 32 * x) ∧
      intercept (![1, 2, 3, 4] : Fin 4 → ℝ) ![63.5, 95.5, 127.5, 159.5] = 31.5 ∧
      slope (![1, 2, 3, 4] : Fin 4 → ℝ) ![63.5, 95.5, 127.5, 159.5] = 32 := by
  have hs : slope (![1, 2, 3, 4] : Fin 4 → ℝ) ![63.5, 95.5, 127.5, 159.5] = 32 := by
    simp [slope, sumProdDev, sumSqDev, mean, Fin.sum_univ_succ]; norm_num
  refine ⟨fun x => by norm_num, ?_, hs⟩
  simp only [intercept, hs]
  simp [mean, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Example 12.4. Svetlana earns `y = 25 + 15 x` dollars for
`x` hours. Sessions of `1, 2, 3, 4` hours pay `40, 55, 70, 85`; the least-squares line through them has
intercept `25` (the fixed fee) and slope `15` (the hourly rate). -/
@[kb "openstaxintrostats2e" "Example 12.4, p. 632"]
theorem example_12_4_tutoring_line :
    intercept (![1, 2, 3, 4] : Fin 4 → ℝ) ![40, 55, 70, 85] = 25 ∧
      slope (![1, 2, 3, 4] : Fin 4 → ℝ) ![40, 55, 70, 85] = 15 := by
  have hs : slope (![1, 2, 3, 4] : Fin 4 → ℝ) ![40, 55, 70, 85] = 15 := by
    simp [slope, sumProdDev, sumSqDev, mean, Fin.sum_univ_succ]; norm_num
  refine ⟨?_, hs⟩
  simp only [intercept, hs]
  simp [mean, Fin.sum_univ_succ]; norm_num

/-! ### Examples 12.7 to 12.10: critical values of the correlation coefficient -/

/-- The critical value of the sample correlation coefficient with `d` degrees of freedom, obtained
from the two-sided critical value `t` of the Student `t` distribution as `t / √(t² + d)`. -/
noncomputable def critR (t d : ℝ) : ℝ := t / Real.sqrt (t ^ 2 + d)

private lemma critR_bounds {t d lo hi : ℝ} (ht : 0 < t) (hd : 0 < d) (_hlo : 0 < lo) (hhi : 0 < hi)
    (h1 : lo ^ 2 * (t ^ 2 + d) < t ^ 2) (h2 : t ^ 2 < hi ^ 2 * (t ^ 2 + d)) :
    lo < critR t d ∧ critR t d < hi := by
  have hB : 0 < t ^ 2 + d := by positivity
  have hs : 0 < Real.sqrt (t ^ 2 + d) := Real.sqrt_pos.2 hB
  have hsq : Real.sqrt (t ^ 2 + d) ^ 2 = t ^ 2 + d := Real.sq_sqrt hB.le
  unfold critR
  constructor
  · rw [lt_div_iff₀ hs]
    by_contra h
    rw [not_lt] at h
    nlinarith [mul_nonneg hs.le _hlo.le, mul_self_nonneg (lo * Real.sqrt (t ^ 2 + d) - t)]
  · rw [div_lt_iff₀ hs]
    by_contra h
    rw [not_lt] at h
    nlinarith [mul_nonneg hs.le hhi.le, mul_self_nonneg (hi * Real.sqrt (t ^ 2 + d) - t)]

private lemma critR_lt_abs_iff {t d r : ℝ} (ht : 0 < t) (hd : 0 < d) (hr : r ^ 2 < 1) :
    critR t d < |r| ↔ t ^ 2 < r ^ 2 * d / (1 - r ^ 2) := by
  have hB : 0 < t ^ 2 + d := by positivity
  have hs : 0 < Real.sqrt (t ^ 2 + d) := Real.sqrt_pos.2 hB
  have hsq : Real.sqrt (t ^ 2 + d) ^ 2 = t ^ 2 + d := Real.sq_sqrt hB.le
  have h1 : (0 : ℝ) < 1 - r ^ 2 := by linarith
  unfold critR
  rw [div_lt_iff₀ hs, lt_div_iff₀ h1,
    ← pow_lt_pow_iff_left₀ ht.le (mul_nonneg (abs_nonneg r) hs.le) (two_ne_zero)]
  rw [mul_pow, sq_abs, hsq]
  constructor <;> intro h <;> nlinarith

private lemma abs_lt_critR_iff {t d r : ℝ} (ht : 0 < t) (hd : 0 < d) (hr : r ^ 2 < 1) :
    |r| < critR t d ↔ r ^ 2 * d / (1 - r ^ 2) < t ^ 2 := by
  have hB : 0 < t ^ 2 + d := by positivity
  have hs : 0 < Real.sqrt (t ^ 2 + d) := Real.sqrt_pos.2 hB
  have hsq : Real.sqrt (t ^ 2 + d) ^ 2 = t ^ 2 + d := Real.sq_sqrt hB.le
  have h1 : (0 : ℝ) < 1 - r ^ 2 := by linarith
  unfold critR
  rw [lt_div_iff₀ hs, div_lt_iff₀ h1,
    ← pow_lt_pow_iff_left₀ (mul_nonneg (abs_nonneg r) hs.le) ht.le (two_ne_zero)]
  rw [mul_pow, sq_abs, hsq]
  constructor <;> intro h <;> nlinarith

/-- OpenStax Introductory Statistics 2e Example 12.7. With `n = 10` points there are `8` degrees of
freedom. From the book's two-sided `t` table value `2.306`, the critical correlation `t/√(t²+8)`
lies strictly between `0.631` and `0.633` (the book's `0.632`). The observed `r = 0.801` exceeds it,
and equivalently its squared `t` statistic `r² · 8 / (1 - r²)` exceeds `2.306²`. -/
@[kb "openstaxintrostats2e" "Example 12.7, p. 645"]
theorem example_12_7_significant_positive :
    0.631 < critR 2.306 8 ∧ critR 2.306 8 < 0.633 ∧ critR 2.306 8 < |(0.801 : ℝ)| ∧
      (2.306 : ℝ) ^ 2 < 0.801 ^ 2 * 8 / (1 - 0.801 ^ 2) := by
  have h := critR_bounds (t := 2.306) (d := 8) (lo := 0.631) (hi := 0.633) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hlt : critR 2.306 8 < |(0.801 : ℝ)| := by
    rw [abs_of_pos (by norm_num)]; linarith [h.2]
  exact ⟨h.1, h.2, hlt,
    (critR_lt_abs_iff (t := 2.306) (d := 8) (r := 0.801) (by norm_num) (by norm_num)
      (by norm_num)).1 hlt⟩

/-- OpenStax Introductory Statistics 2e Example 12.8. With `n = 14` points (12 degrees of freedom) and
the book's `t` table value `2.179`, the critical correlation lies strictly between `0.531` and `0.533`
(the book's `0.532`). The observed `r = -0.624` has `|r|` above it, so `r` is significant;
equivalently `2.179² < r² · 12 / (1 - r²)`. -/
@[kb "openstaxintrostats2e" "Example 12.8, p. 645"]
theorem example_12_8_significant_negative :
    0.531 < critR 2.179 12 ∧ critR 2.179 12 < 0.533 ∧ critR 2.179 12 < |(-0.624 : ℝ)| ∧
      (2.179 : ℝ) ^ 2 < (-0.624) ^ 2 * 12 / (1 - (-0.624) ^ 2) := by
  have h := critR_bounds (t := 2.179) (d := 12) (lo := 0.531) (hi := 0.533) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hlt : critR 2.179 12 < |(-0.624 : ℝ)| := by
    rw [abs_of_neg (by norm_num)]; linarith [h.2]
  exact ⟨h.1, h.2, hlt,
    (critR_lt_abs_iff (t := 2.179) (d := 12) (r := -0.624) (by norm_num) (by norm_num)
      (by norm_num)).1 hlt⟩

/-- OpenStax Introductory Statistics 2e Example 12.9. With `n = 6` points (4 degrees of freedom) and
the book's `t` table value `2.776`, the critical correlation lies strictly between `0.810` and `0.812`
(the book's `0.811`). The observed `r = 0.776` is smaller, so `r` is not significant;
equivalently `r² · 4 / (1 - r²) < 2.776²`. -/
@[kb "openstaxintrostats2e" "Example 12.9, p. 645"]
theorem example_12_9_not_significant :
    0.810 < critR 2.776 4 ∧ critR 2.776 4 < 0.812 ∧ |(0.776 : ℝ)| < critR 2.776 4 ∧
      (0.776 : ℝ) ^ 2 * 4 / (1 - 0.776 ^ 2) < 2.776 ^ 2 := by
  have h := critR_bounds (t := 2.776) (d := 4) (lo := 0.810) (hi := 0.812) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hlt : |(0.776 : ℝ)| < critR 2.776 4 := by
    rw [abs_of_pos (by norm_num)]; linarith [h.1]
  exact ⟨h.1, h.2, hlt,
    (abs_lt_critR_iff (t := 2.776) (d := 4) (r := 0.776) (by norm_num) (by norm_num)
      (by norm_num)).1 hlt⟩

/-- OpenStax Introductory Statistics 2e Example 12.10(a). With `n = 19` points (17 degrees of freedom)
and the book's `t` table value `2.110`, the critical correlation lies strictly between `0.455` and
`0.457` (the book's `0.456`). The observed `r = -0.567` has larger absolute value: significant. -/
@[kb "openstaxintrostats2e" "Example 12.10, p. 646"]
theorem example_12_10a_significant :
    0.455 < critR 2.110 17 ∧ critR 2.110 17 < 0.457 ∧ critR 2.110 17 < |(-0.567 : ℝ)| ∧
      (2.110 : ℝ) ^ 2 < (-0.567) ^ 2 * 17 / (1 - (-0.567) ^ 2) := by
  have h := critR_bounds (t := 2.110) (d := 17) (lo := 0.455) (hi := 0.457) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hlt : critR 2.110 17 < |(-0.567 : ℝ)| := by
    rw [abs_of_neg (by norm_num)]; linarith [h.2]
  exact ⟨h.1, h.2, hlt,
    (critR_lt_abs_iff (t := 2.110) (d := 17) (r := -0.567) (by norm_num) (by norm_num)
      (by norm_num)).1 hlt⟩

/-- OpenStax Introductory Statistics 2e Example 12.10(b). With `n = 9` points (7 degrees of freedom)
and the book's `t` table value `2.365`, the critical correlation lies strictly between `0.665` and
`0.667` (the book's `0.666`). The observed `r = 0.708` is larger: significant. -/
@[kb "openstaxintrostats2e" "Example 12.10, p. 646"]
theorem example_12_10b_significant :
    0.665 < critR 2.365 7 ∧ critR 2.365 7 < 0.667 ∧ critR 2.365 7 < |(0.708 : ℝ)| ∧
      (2.365 : ℝ) ^ 2 < 0.708 ^ 2 * 7 / (1 - 0.708 ^ 2) := by
  have h := critR_bounds (t := 2.365) (d := 7) (lo := 0.665) (hi := 0.667) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hlt : critR 2.365 7 < |(0.708 : ℝ)| := by
    rw [abs_of_pos (by norm_num)]; linarith [h.2]
  exact ⟨h.1, h.2, hlt,
    (critR_lt_abs_iff (t := 2.365) (d := 7) (r := 0.708) (by norm_num) (by norm_num)
      (by norm_num)).1 hlt⟩

/-- OpenStax Introductory Statistics 2e Example 12.10(c). With `n = 14` points (12 degrees of freedom)
and the book's `t` table value `2.179`, the critical correlation lies strictly between `0.531` and
`0.533`. The observed `r = 0.134` is smaller: not significant. -/
@[kb "openstaxintrostats2e" "Example 12.10, p. 646"]
theorem example_12_10c_not_significant :
    0.531 < critR 2.179 12 ∧ critR 2.179 12 < 0.533 ∧ |(0.134 : ℝ)| < critR 2.179 12 ∧
      (0.134 : ℝ) ^ 2 * 12 / (1 - 0.134 ^ 2) < 2.179 ^ 2 := by
  have h := critR_bounds (t := 2.179) (d := 12) (lo := 0.531) (hi := 0.533) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hlt : |(0.134 : ℝ)| < critR 2.179 12 := by
    rw [abs_of_pos (by norm_num)]; linarith [h.1]
  exact ⟨h.1, h.2, hlt,
    (abs_lt_critR_iff (t := 2.179) (d := 12) (r := 0.134) (by norm_num) (by norm_num)
      (by norm_num)).1 hlt⟩

/-- OpenStax Introductory Statistics 2e Example 12.10(d). With `n = 5` points (3 degrees of freedom)
and the book's `t` table value `3.182`, the critical correlation lies strictly between `0.877` and
`0.879`. The observed `r = 0` is below it: not significant. -/
@[kb "openstaxintrostats2e" "Example 12.10, p. 646"]
theorem example_12_10d_zero_not_significant :
    0.877 < critR 3.182 3 ∧ critR 3.182 3 < 0.879 ∧ |(0 : ℝ)| < critR 3.182 3 := by
  have h := critR_bounds (t := 3.182) (d := 3) (lo := 0.877) (hi := 0.879) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1, h.2, by rw [abs_zero]; linarith [h.1]⟩

/-! ### Example 12.14: consumer price index -/

/-- Years of the first fourteen observations of the consumer-price-index table of Example 12.14
(the book's computations use `n = 14` points). -/
noncomputable def cpiX : Fin 14 → ℝ :=
  ![1915, 1926, 1935, 1940, 1947, 1952, 1964, 1969, 1975, 1979, 1980, 1986, 1991, 1999]

/-- Price index values paired with `cpiX`. -/
noncomputable def cpiY : Fin 14 → ℝ :=
  ![10.1, 17.7, 13.7, 14.7, 24.1, 26.5, 31.0, 36.7, 49.3, 72.6, 82.4, 109.6, 130.7, 166.6]

private lemma mean_cpiX : mean cpiX = 13729 / 7 := by
  simp [mean, cpiX, Fin.sum_univ_succ]; norm_num

private lemma mean_cpiY : mean cpiY = 7857 / 140 := by
  simp [mean, cpiY, Fin.sum_univ_succ]; norm_num

private lemma sxx_cpi : sumSqDev cpiX = 60598 / 7 := by
  simp only [sumSqDev, mean_cpiX]; simp [cpiX, Fin.sum_univ_succ]; norm_num

private lemma syy_cpi : sumSqDev cpiY = 44319301 / 1400 := by
  simp only [sumSqDev, mean_cpiY]; simp [cpiY, Fin.sum_univ_succ]; norm_num

private lemma sxy_cpi : sumProdDev cpiX cpiY = 1007413 / 70 := by
  simp only [sumProdDev, mean_cpiX, mean_cpiY]; simp [cpiX, cpiY, Fin.sum_univ_succ]; norm_num

private lemma slope_cpi : slope cpiX cpiY = 1007413 / 605980 := by
  rw [slope, sxy_cpi, sxx_cpi]; norm_num

private lemma intercept_cpi : intercept cpiX cpiY = -970908131 / 302990 := by
  rw [intercept, slope_cpi, mean_cpiX, mean_cpiY]; norm_num

private lemma sse_cpi : sse cpiX cpiY (intercept cpiX cpiY) (slope cpiX cpiY) =
    4684993549 / 605980 := by
  rw [intercept_cpi, slope_cpi]
  simp [sse, cpiX, cpiY, Fin.sum_univ_succ]; norm_num

private lemma stdErr_cpi : 25.38 < stdErrorEstimate cpiX cpiY ∧ stdErrorEstimate cpiX cpiY < 25.39 := by
  unfold stdErrorEstimate
  rw [sse_cpi]
  have h : ((14 : ℕ) : ℝ) - 2 = 12 := by norm_num
  rw [h]
  constructor
  · exact (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  · exact (Real.sqrt_lt' (by norm_num)).2 (by norm_num)

/-- OpenStax Introductory Statistics 2e Example 12.14 (line). For the fourteen index values, the
least-squares slope is exactly `1007413/605980`, strictly between `1.6624` and `1.6625` (the book's
`1.662`), and the intercept is exactly `-970908131/302990`, strictly between `-3204.43` and
`-3204.42` (the book's `-3204`). -/
@[kb "openstaxintrostats2e" "Example 12.14, p. 652"]
theorem example_12_14_regression_line :
    slope cpiX cpiY = 1007413 / 605980 ∧ intercept cpiX cpiY = -970908131 / 302990 ∧
      1.6624 < slope cpiX cpiY ∧ slope cpiX cpiY < 1.6625 ∧
      -3204.43 < intercept cpiX cpiY ∧ intercept cpiX cpiY < -3204.42 := by
  rw [slope_cpi, intercept_cpi]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩ <;> norm_num

/-- OpenStax Introductory Statistics 2e Example 12.14 (correlation). The correlation coefficient of
the fourteen points satisfies `0.869 < r < 0.870` (the book's `0.8694`), which exceeds the book's
critical value `0.532` for 12 degrees of freedom. -/
@[kb "openstaxintrostats2e" "Example 12.14, p. 652"]
theorem example_12_14_correlation :
    0.869 < correlation cpiX cpiY ∧ correlation cpiX cpiY < 0.870 ∧ 0.532 < correlation cpiX cpiY := by
  have h : 0.869 < correlation cpiX cpiY ∧ correlation cpiX cpiY < 0.870 := by
    unfold correlation
    rw [sxy_cpi, sxx_cpi, syy_cpi]
    have hB : (0 : ℝ) < 60598 / 7 * (44319301 / 1400) := by norm_num
    have hs : 0 < Real.sqrt (60598 / 7 * (44319301 / 1400)) := Real.sqrt_pos.2 hB
    have hsq := Real.sq_sqrt hB.le
    constructor
    · rw [lt_div_iff₀ hs]
      by_contra h
      rw [not_lt] at h
      nlinarith [mul_self_nonneg (0.869 * Real.sqrt (60598 / 7 * (44319301 / 1400)) - 1007413 / 70)]
    · rw [div_lt_iff₀ hs]
      by_contra h
      rw [not_lt] at h
      nlinarith [mul_self_nonneg (0.870 * Real.sqrt (60598 / 7 * (44319301 / 1400)) - 1007413 / 70)]
  exact ⟨h.1, h.2, by linarith [h.1]⟩

/-- OpenStax Introductory Statistics 2e Example 12.14 (prediction). The least-squares line predicts a
price index strictly between `103.85` and `103.86` for 1990; the book's `103.4` is the value of the
rounded line `-3204 + 1.662 x`. -/
@[kb "openstaxintrostats2e" "Example 12.14, p. 652"]
theorem example_12_14_prediction_1990 :
    103.85 < intercept cpiX cpiY + slope cpiX cpiY * 1990 ∧
      intercept cpiX cpiY + slope cpiX cpiY * 1990 < 103.86 ∧
      (-3204 + 1.662 * 1990 : ℝ) = 103.38 := by
  rw [intercept_cpi, slope_cpi]
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- OpenStax Introductory Statistics 2e Example 12.14 (outliers). The standard error of the estimate
lies strictly between `25.38` and `25.39` (the book's `25.4`), and every residual of the fourteen
points has absolute value below `2s`, so no point is a potential outlier. -/
@[kb "openstaxintrostats2e" "Example 12.14, p. 652"]
theorem example_12_14_no_outliers :
    25.38 < stdErrorEstimate cpiX cpiY ∧ stdErrorEstimate cpiX cpiY < 25.39 ∧
      ∀ i, |cpiY i - (intercept cpiX cpiY + slope cpiX cpiY * cpiX i)| <
        2 * stdErrorEstimate cpiX cpiY := by
  have key : ∀ i : Fin 14,
      |cpiY i - (intercept cpiX cpiY + slope cpiX cpiY * cpiX i)| < 50.76 := by
    rw [intercept_cpi, slope_cpi]
    intro i
    fin_cases i <;> simp [cpiX, cpiY] <;> rw [abs_lt] <;> constructor <;> norm_num
  refine ⟨stdErr_cpi.1, stdErr_cpi.2, fun i => ?_⟩
  linarith [key i, stdErr_cpi.1]

/-! ### Example 13.5 -/

/-- OpenStax Introductory Statistics 2e Example 13.5. Two instructors grade the same 30 exams with
sample variances `52.3` and `89.9`. The `F` ratio `52.3/89.9` (with `29` and `29` degrees of freedom)
is strictly between `0.5817` and `0.5818` (the book's `0.5818`). The left-tail probability `0.0753`
is the book's computed value (not proved here); it is below `α = 0.10`, so the claim that the first
variance is smaller is accepted. -/
@[kb "openstaxintrostats2e" "Example 13.5, p. 703"]
theorem example_13_5_f_ratio :
    0.5817 < (52.3 : ℝ) / 89.9 ∧ (52.3 : ℝ) / 89.9 < 0.5818 ∧ (30 : ℕ) - 1 = 29 ∧
      (let pBook : ℝ := 0.0753; pBook < 0.10) := by
  refine ⟨by norm_num, by norm_num, rfl, by norm_num⟩

end UndergradKB.Statistics.Course.ExamplesC11C13b
