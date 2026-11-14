import Mathlib.Data.Fin.VecNotation
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Data
import UndergradKB.Statistics.Regression

/-!
# Practice exercises, chapter 12 (OpenStax *Introductory Statistics 2e*): linear regression and correlation

Linear equations, the least-squares line of the athlete-endorsement data and of the flu-case data,
correlations, predictions and the outlier cutoff. Critical values of the correlation coefficient are the
book's table values (named in the statements, not proved).
-/

namespace UndergradKB.Statistics.Course.PracticeC12

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

/-- OpenStax Introductory Statistics 2e Practice exercise 12.2. Renting diving equipment costs an
up-front `25` plus `12.5` per hour, so the total fee for `x` hours is `25 + 12.5 x`: the fee for no
hours is `25` and each extra hour adds exactly `12.5`. -/
@[kb "openstaxintrostats2e" "Exercise 12.2, p. 663"]
theorem ex_12_2_scuba_fee :
    let fee : ℝ → ℝ := fun x => 25 + 12.5 * x
    fee 0 = 25 ∧ (∀ x, fee (x + 1) - fee x = 12.5) ∧ fee 4 = 75 := by
  intro fee
  refine ⟨by simp [fee], fun x => by simp only [fee]; ring, by simp only [fee]; norm_num⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 12.4. A late credit card payment costs `10`
plus `5` for each day late, so the total fee after `x` days is `10 + 5 x`: the fee on day zero is
`10` and each extra day adds exactly `5`; after `7` days it is `45`. -/
@[kb "openstaxintrostats2e" "Exercise 12.4, p. 663"]
theorem ex_12_4_late_fee :
    let fee : ℝ → ℝ := fun x => 10 + 5 * x
    fee 0 = 10 ∧ (∀ x, fee (x + 1) - fee x = 5) ∧ fee 7 = 45 := by
  intro fee
  refine ⟨by simp [fee], fun x => by simp only [fee]; ring, by simp only [fee]; norm_num⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 12.6. The equation `y = 10 + 5x - 3x²` is not
linear: no constants `a`, `b` give `10 + 5x - 3x² = a + b x` for every `x`. -/
@[kb "openstaxintrostats2e" "Exercise 12.6, p. 663"]
theorem ex_12_6_quadratic_not_linear :
    ¬ ∃ a b : ℝ, ∀ x : ℝ, 10 + 5 * x - 3 * x ^ 2 = a + b * x := by
  rintro ⟨a, b, h⟩
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 12.7. Of the four equations, `y = 6x + 8`,
`y + 7 = 3x` (that is `y = -7 + 3x`) and `4y = 8` (that is `y = 2`, slope zero) are linear, while
`y - x = 8x²` is not (it is not of the form `a + b x` for all `x`). -/
@[kb "openstaxintrostats2e" "Exercise 12.7, p. 663"]
theorem ex_12_7_which_linear :
    (∃ a b : ℝ, ∀ x y : ℝ, y = 6 * x + 8 ↔ y = a + b * x) ∧
    (∃ a b : ℝ, ∀ x y : ℝ, y + 7 = 3 * x ↔ y = a + b * x) ∧
    (¬ ∃ a b : ℝ, ∀ x y : ℝ, y - x = 8 * x ^ 2 ↔ y = a + b * x) ∧
    (∃ a b : ℝ, ∀ x y : ℝ, 4 * y = 8 ↔ y = a + b * x) := by
  refine ⟨⟨8, 6, fun x y => by constructor <;> intro h <;> linarith⟩,
    ⟨-7, 3, fun x y => by constructor <;> intro h <;> linarith⟩, ?_,
    ⟨2, 0, fun x y => by constructor <;> intro h <;> linarith⟩⟩
  rintro ⟨a, b, h⟩
  have e : ∀ x : ℝ, (x + 8 * x ^ 2) = a + b * x := fun x => (h x (x + 8 * x ^ 2)).1 (by ring)
  have h0 := e 0
  have h1 := e 1
  have h2 := e 2
  linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 12.11. For the cleaning fee `y = 50 + 100 x`
the intercept is `50` (the fee for zero hours) and the slope is `100` (the extra charge per hour). -/
@[kb "openstaxintrostats2e" "Exercise 12.11, p. 665"]
theorem ex_12_11_cleaning_fee :
    let fee : ℝ → ℝ := fun x => 50 + 100 * x
    fee 0 = 50 ∧ ∀ x, fee (x + 1) - fee x = 100 := by
  intro fee
  exact ⟨by simp [fee], fun x => by simp only [fee]; ring⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 12.13. With the soil-loss equation
`y = 12000 x`, one year (`x = 1`) loses exactly `12000` pounds. -/
@[kb "openstaxintrostats2e" "Exercise 12.13, p. 665"]
theorem ex_12_13_soil_loss_one_year : (12000 : ℝ) * 1 = 12000 := by norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 12.14. The soil-loss equation `y = 12000 x`
has `y`-intercept `0`: no time has passed, no soil has been lost. Every extra year adds `12000`. -/
@[kb "openstaxintrostats2e" "Exercise 12.14, p. 665"]
theorem ex_12_14_soil_loss_intercept :
    let loss : ℝ → ℝ := fun x => 12000 * x
    loss 0 = 0 ∧ ∀ x, loss (x + 1) - loss x = 12000 := by
  intro loss
  exact ⟨by simp [loss], fun x => by simp only [loss]; ring⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 12.15. The stock price `y = 15 - 1.5 x`
has `y`-intercept `15` (the opening price) and slope `-1.5` (the price drops by exactly `1.5` each
hour). -/
@[kb "openstaxintrostats2e" "Exercise 12.15, p. 665"]
theorem ex_12_15_stock_price :
    let price : ℝ → ℝ := fun x => 15 - 1.5 * x
    price 0 = 15 ∧ ∀ x, price (x + 1) - price x = -1.5 := by
  intro price
  exact ⟨by norm_num [price], fun x => by simp only [price]; ring⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 12.16. With the negative slope `-1.5` the
stock price strictly decreases over the trading day: it is `15` at the start and `3` after the eight
hours, and later times always give lower prices; a holder would prefer a positive slope. -/
@[kb "openstaxintrostats2e" "Exercise 12.16, p. 665"]
theorem ex_12_16_stock_slope_sign :
    let price : ℝ → ℝ := fun x => 15 - 1.5 * x
    price 8 = 3 ∧ price 8 < price 0 ∧ ∀ s t : ℝ, s < t → price t < price s := by
  intro price
  refine ⟨by simp only [price]; norm_num, by simp only [price]; norm_num, fun s t h => ?_⟩
  simp only [price]; linarith

/-! ### Section 12.3: athletes and endorsements (Table 12.14) -/

/-- Number of endorsements of the ten athletes of Table 12.14. -/
noncomputable def endorse : Fin 10 → ℝ := ![0, 3, 2, 1, 5, 5, 4, 3, 0, 4]

/-- Money made (millions of dollars) by the ten athletes of Table 12.14. -/
noncomputable def money : Fin 10 → ℝ := ![2, 8, 7, 3, 13, 12, 9, 9, 3, 10]

private lemma en_mean : mean endorse = 27 / 10 := by
  simp [mean, endorse, Fin.sum_univ_succ]; norm_num

private lemma mo_mean : mean money = 38 / 5 := by
  simp [mean, money, Fin.sum_univ_succ]; norm_num

private lemma en_sxx : sumSqDev endorse = 321 / 10 := by
  simp only [sumSqDev, en_mean]; simp [endorse, Fin.sum_univ_succ]; norm_num

private lemma mo_syy : sumSqDev money = 662 / 5 := by
  simp only [sumSqDev, mo_mean]; simp [money, Fin.sum_univ_succ]; norm_num

private lemma em_sxy : sumProdDev endorse money = 319 / 5 := by
  simp only [sumProdDev, en_mean, mo_mean]; simp [endorse, money, Fin.sum_univ_succ]; norm_num

private lemma em_slope : slope endorse money = 638 / 321 := by
  rw [slope, em_sxy, en_sxx]; norm_num

private lemma em_intercept : intercept endorse money = 239 / 107 := by
  rw [intercept, em_slope, en_mean, mo_mean]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 12.21. For the ten athletes the least-squares
line of money on endorsements is exactly `ŷ = 239/107 + (638/321) x`, which is `2.23 + 1.99 x` to two
decimals (both coefficients are within `0.005` of those values). -/
@[kb "openstaxintrostats2e" "Exercise 12.21, p. 667"]
theorem ex_12_21_athlete_line :
    intercept endorse money = 239 / 107 ∧ slope endorse money = 638 / 321 ∧
      |intercept endorse money - 2.23| < 0.005 ∧ |slope endorse money - 1.99| < 0.005 := by
  rw [em_intercept, em_slope]
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> rw [abs_lt] <;> constructor <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 12.23. The slope of the line of best fit is
`638/321`, strictly between `1.98` and `1.99`: each further endorsement goes with about `1.99` more
million dollars earned. -/
@[kb "openstaxintrostats2e" "Exercise 12.23, p. 667"]
theorem ex_12_23_athlete_slope : 1.98 < slope endorse money ∧ slope endorse money < 1.99 := by
  rw [em_slope]; constructor <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 12.24. The `y`-intercept of the line of best
fit is `239/107`, strictly between `2.23` and `2.24`: the predicted earnings with no endorsement, about
`2.23` million dollars. -/
@[kb "openstaxintrostats2e" "Exercise 12.24, p. 667"]
theorem ex_12_24_athlete_intercept : 2.23 < intercept endorse money ∧ intercept endorse money < 2.24 := by
  rw [em_intercept]; constructor <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 12.21 (correlation, supplementary). The
correlation of the athlete data lies strictly between `0.9786` and `0.9787` and its square strictly
between `0.9577` and `0.9578`: the line explains about `95.8%` of the variation in earnings. -/
@[kb "openstaxintrostats2e" "Exercise 12.21, p. 667"]
theorem ex_12_21_athlete_correlation :
    0.9786 < correlation endorse money ∧ correlation endorse money < 0.9787 ∧
      0.9577 < correlation endorse money ^ 2 ∧ correlation endorse money ^ 2 < 0.9578 := by
  have hsq := correlation_sq (x := endorse) (y := money) (by rw [en_sxx]; norm_num)
    (by rw [mo_syy]; norm_num)
  rw [em_sxy, en_sxx, mo_syy] at hsq
  have h := corr_bounds (A := 319 / 5) (B := 321 / 10 * (662 / 5)) (lo := 0.9786) (hi := 0.9787)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold correlation; rw [em_sxy, en_sxx, mo_syy]; exact h.1
  · unfold correlation; rw [em_sxy, en_sxx, mo_syy]; exact h.2
  · rw [hsq]; norm_num
  · rw [hsq]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 12.25. If the correlation coefficient of a
data set (with non-constant `x` and `y`) is zero, the sample covariance sum vanishes, so the
least-squares line is flat: its slope is `0` and its intercept is the mean of `y`. There is no linear
relationship. -/
@[kb "openstaxintrostats2e" "Exercise 12.25, p. 667"]
theorem ex_12_25_zero_correlation {n : ℕ} (x y : Fin n → ℝ) (hx : 0 < sumSqDev x)
    (hy : 0 < sumSqDev y) (hr : correlation x y = 0) :
    slope x y = 0 ∧ intercept x y = mean y := by
  have hs := Real.sqrt_pos.2 (mul_pos hx hy)
  have hxy : sumProdDev x y = 0 := by
    unfold correlation at hr
    rcases div_eq_zero_iff.1 hr with h | h
    · exact h
    · exact absurd h hs.ne'
  have hsl : slope x y = 0 := by rw [slope, hxy]; simp
  exact ⟨hsl, by rw [intercept, hsl]; ring⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 12.26. With `n = 2` points there are
`n - 2 = 0` degrees of freedom, and any two points with increasing `x` and increasing `y` give a
correlation of exactly `1`: two points always lie on a line, so `r = 1` carries no evidence about a
linear relationship (the correlation test cannot be applied). -/
@[kb "openstaxintrostats2e" "Exercise 12.26, p. 667"]
theorem ex_12_26_two_points_perfect :
    (2 : ℕ) - 2 = 0 ∧ ∀ x₁ x₂ y₁ y₂ : ℝ, x₁ < x₂ → y₁ < y₂ →
      correlation (![x₁, x₂] : Fin 2 → ℝ) ![y₁, y₂] = 1 := by
  refine ⟨rfl, fun x₁ x₂ y₁ y₂ hx hy => ?_⟩
  have sx : 0 < sumSqDev (![x₁, x₂] : Fin 2 → ℝ) := by
    simp [sumSqDev, mean, Fin.sum_univ_succ]
    nlinarith [sq_pos_of_pos (sub_pos.2 hx)]
  have sy : 0 < sumSqDev (![y₁, y₂] : Fin 2 → ℝ) := by
    simp [sumSqDev, mean, Fin.sum_univ_succ]
    nlinarith [sq_pos_of_pos (sub_pos.2 hy)]
  rw [correlation_eq_one_iff _ _ sx sy]
  have hne : x₂ - x₁ ≠ 0 := (sub_pos.2 hx).ne'
  refine ⟨y₁ - (y₂ - y₁) / (x₂ - x₁) * x₁, (y₂ - y₁) / (x₂ - x₁), div_pos (sub_pos.2 hy) (sub_pos.2 hx), ?_⟩
  intro i
  fin_cases i
  · simp
  · simp
    field_simp
    ring

/-- OpenStax Introductory Statistics 2e Practice exercise 12.27. With `n = 100` points there are `98`
degrees of freedom; the correlation `r = -0.89` has absolute value above the book's table critical value
`0.195` (a table value, not proved), so it is significant: a strong negative correlation. -/
@[kb "openstaxintrostats2e" "Exercise 12.27, p. 667"]
theorem ex_12_27_significant_negative :
    (100 : ℕ) - 2 = 98 ∧ (0.195 : ℝ) < |(-0.89 : ℝ)| := by
  refine ⟨rfl, ?_⟩
  rw [abs_of_neg (by norm_num)]; norm_num

/-! ### Section 12.4: significance of the correlation -/

/-- OpenStax Introductory Statistics 2e Practice exercise 12.30. With significance level `0.05` and
p-value `0.04` the p-value is below the level, so the null hypothesis `ρ = 0` is rejected: the
correlation is significant. -/
@[kb "openstaxintrostats2e" "Exercise 12.30, p. 667"]
theorem ex_12_30_reject_at_p_below_alpha : (0.04 : ℝ) < 0.05 := by norm_num

/-! ### Section 12.5: prediction -/

/-- OpenStax Introductory Statistics 2e Practice exercise 12.31. The sales model `ŷ = 101.32 + 2.48 x`
(thousands of dollars) predicts exactly `250.12` thousand dollars (that is `$250,120`) on day `60`. -/
@[kb "openstaxintrostats2e" "Exercise 12.31, p. 667"]
theorem ex_12_31_sales_day_60 : (101.32 + 2.48 * 60 : ℝ) = 250.12 := by norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 12.32. The sales model `ŷ = 101.32 + 2.48 x`
predicts exactly `324.52` thousand dollars on day `90`. -/
@[kb "openstaxintrostats2e" "Exercise 12.32, p. 667"]
theorem ex_12_32_sales_day_90 : (101.32 + 2.48 * 90 : ℝ) = 324.52 := by norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 12.33. By the mowing model
`ŷ = 1350 - 1.2 x`, exactly `1326` acres are left after `20` hours. -/
@[kb "openstaxintrostats2e" "Exercise 12.33, p. 667"]
theorem ex_12_33_mowing_20_hours : (1350 - 1.2 * 20 : ℝ) = 1326 := by norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 12.34. By the mowing model
`ŷ = 1350 - 1.2 x`, exactly `1230` acres are left after `100` hours. -/
@[kb "openstaxintrostats2e" "Exercise 12.34, p. 667"]
theorem ex_12_34_mowing_100_hours : (1350 - 1.2 * 100 : ℝ) = 1230 := by norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 12.35. The mowing model `ŷ = 1350 - 1.2 x`
reaches `ŷ = 0` exactly at `x = 1125` hours, and that is the only such `x`. -/
@[kb "openstaxintrostats2e" "Exercise 12.35, p. 667"]
theorem ex_12_35_mowing_all_done : ∀ x : ℝ, 1350 - 1.2 * x = 0 ↔ x = 1125 := by
  intro x
  constructor <;> intro h <;> linarith

/-! ### Section 12.5: flu cases (Table 12.15, years 1981 to 2002) -/

/-- The years `1981, ..., 2002` of Table 12.15 (the pre-1981 row is left out). -/
noncomputable def fluYear : Fin 22 → ℝ :=
  ![1981, 1982, 1983, 1984, 1985, 1986, 1987, 1988, 1989, 1990, 1991, 1992, 1993, 1994, 1995, 1996,
    1997, 1998, 1999, 2000, 2001, 2002]

/-- Diagnosed flu cases in the years `1981, ..., 2002` of Table 12.15. -/
noncomputable def fluCases : Fin 22 → ℝ :=
  ![319, 1170, 3076, 6240, 11776, 19032, 28564, 35447, 42674, 48634, 59660, 78530, 78834, 71874,
    68505, 59347, 47149, 38393, 25174, 25522, 25643, 26464]

private lemma fy_mean : mean fluYear = 3983 / 2 := by
  simp [mean, fluYear, Fin.sum_univ_succ]; norm_num

private lemma fc_mean : mean fluCases = 802027 / 22 := by
  simp [mean, fluCases, Fin.sum_univ_succ]; norm_num

private lemma fy_sxx : sumSqDev fluYear = 1771 / 2 := by
  simp only [sumSqDev, fy_mean]; simp [fluYear, Fin.sum_univ_succ]; norm_num

private lemma fc_syy : sumSqDev fluCases = 291125666961 / 22 := by
  simp only [sumSqDev, fc_mean]; simp [fluCases, Fin.sum_univ_succ]; norm_num

private lemma flu_sxy : sumProdDev fluYear fluCases = 3098855 / 2 := by
  simp only [sumProdDev, fy_mean, fc_mean]; simp [fluYear, fluCases, Fin.sum_univ_succ]; norm_num

private lemma flu_slope : slope fluYear fluCases = 3098855 / 1771 := by
  rw [slope, flu_sxy, fy_sxx]; norm_num

private lemma flu_intercept : intercept fluYear fluCases = -872400937 / 253 := by
  rw [intercept, flu_slope, fy_mean, fc_mean]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 12.37. The least-squares line of diagnosed
flu cases on the year (1981 to 2002) has slope exactly `3098855/1771` and intercept `-872400937/253`,
that is `ŷ ≈ -3 448 225 + 1750 x` to the nearest whole number (both coefficients are within `1/2` of
those integers). -/
@[kb "openstaxintrostats2e" "Exercise 12.37, p. 669"]
theorem ex_12_37_flu_line :
    slope fluYear fluCases = 3098855 / 1771 ∧ intercept fluYear fluCases = -872400937 / 253 ∧
      |slope fluYear fluCases - 1750| < 1 / 2 ∧ |intercept fluYear fluCases + 3448225| < 1 / 2 := by
  rw [flu_slope, flu_intercept]
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> rw [abs_lt] <;> constructor <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 12.38. The correlation coefficient of year
and diagnosed flu cases lies strictly between `0.4526` and `0.4527`. -/
@[kb "openstaxintrostats2e" "Exercise 12.38, p. 669"]
theorem ex_12_38_flu_correlation :
    0.4526 < correlation fluYear fluCases ∧ correlation fluYear fluCases < 0.4527 := by
  have h := corr_bounds (A := 3098855 / 2) (B := 1771 / 2 * (291125666961 / 22)) (lo := 0.4526)
    (hi := 0.4527) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold correlation
  rw [flu_sxy, fy_sxx, fc_syy]
  exact h

/-- OpenStax Introductory Statistics 2e Practice exercise 12.39 (as the book computes it, with the
rounded line `ŷ = -3 448 225 + 1750 x`). The predictions are exactly `25525` cases for 1985, `34275`
for 1990, and `-725` for 1970; the last is negative, so it cannot be a number of cases (1970 is far
outside the data range, an extrapolation). -/
@[kb "openstaxintrostats2e" "Exercise 12.39, p. 669"]
theorem ex_12_39_flu_predictions_rounded_line :
    (-3448225 + 1750 * 1985 : ℝ) = 25525 ∧ (-3448225 + 1750 * 1990 : ℝ) = 34275 ∧
      (-3448225 + 1750 * 1970 : ℝ) = -725 ∧ (-3448225 + 1750 * 1970 : ℝ) < 0 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 12.39 (with the exact least-squares line).
The line predicts strictly between `25082.22` and `25082.23` cases for 1985, strictly between `33831.10`
and `33831.11` for 1990, and strictly between `-1164.44` and `-1164.43` for 1970 (a negative number of
cases, nonsense, since 1970 lies outside the data range 1981 to 2002). -/
@[kb "openstaxintrostats2e" "Exercise 12.39, p. 669"]
theorem ex_12_39_flu_predictions_exact_line :
    (25082.22 < intercept fluYear fluCases + slope fluYear fluCases * 1985 ∧
      intercept fluYear fluCases + slope fluYear fluCases * 1985 < 25082.23) ∧
    (33831.10 < intercept fluYear fluCases + slope fluYear fluCases * 1990 ∧
      intercept fluYear fluCases + slope fluYear fluCases * 1990 < 33831.11) ∧
    (-1164.44 < intercept fluYear fluCases + slope fluYear fluCases * 1970 ∧
      intercept fluYear fluCases + slope fluYear fluCases * 1970 < -1164.43) := by
  rw [flu_intercept, flu_slope]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 12.40. The line fits the flu data poorly: the
coefficient of determination `r²` lies strictly between `0.2048` and `0.2049`, so the line accounts for
only about a fifth of the variation in the number of cases. -/
@[kb "openstaxintrostats2e" "Exercise 12.40, p. 669"]
theorem ex_12_40_flu_poor_fit :
    0.2048 < correlation fluYear fluCases ^ 2 ∧ correlation fluYear fluCases ^ 2 < 0.2049 := by
  have hsq := correlation_sq (x := fluYear) (y := fluCases) (by rw [fy_sxx]; norm_num)
    (by rw [fc_syy]; norm_num)
  rw [flu_sxy, fy_sxx, fc_syy] at hsq
  rw [hsq]; constructor <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 12.41. The correlation of the flu data
(`r > 0.4526`) exceeds the book's table critical value `0.423` for `20` degrees of freedom (22 points,
a table value, not proved), so the correlation is formally significant even though the scatter is not
linear. -/
@[kb "openstaxintrostats2e" "Exercise 12.41, p. 669"]
theorem ex_12_41_flu_r_exceeds_critical :
    (22 : ℕ) - 2 = 20 ∧ (let rCrit : ℝ := 0.423; rCrit < correlation fluYear fluCases) := by
  refine ⟨rfl, ?_⟩
  have := ex_12_38_flu_correlation
  show (0.423 : ℝ) < _
  linarith [this.1]

/-- OpenStax Introductory Statistics 2e Practice exercise 12.43. The equation of the line in the
book's rounding is `ŷ = -3 448 225 + 1750 x`: the intercept of the least-squares line is within `1/2` of
`-3448225` and the slope within `1/2` of `1750`. -/
@[kb "openstaxintrostats2e" "Exercise 12.43, p. 669"]
theorem ex_12_43_flu_equation_rounded :
    |intercept fluYear fluCases - (-3448225)| < 1 / 2 ∧ |slope fluYear fluCases - 1750| < 1 / 2 := by
  rw [flu_slope, flu_intercept]
  refine ⟨?_, ?_⟩ <;> rw [abs_lt] <;> constructor <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 12.45. The flu data rise until 1993 and then
decline: the year 1993 (index `12`) has the largest number of cases, and every later year has strictly
fewer; a straight line cannot follow such a shape. -/
@[kb "openstaxintrostats2e" "Exercise 12.45, p. 669"]
theorem ex_12_45_flu_peak_in_1993 :
    fluYear 12 = 1993 ∧ (∀ i : Fin 22, fluCases i ≤ fluCases 12) ∧
      ∀ i : Fin 22, 12 < i → fluCases i < fluCases 12 := by
  refine ⟨by simp [fluYear], fun i => ?_, fun i hi => ?_⟩
  · fin_cases i <;> simp [fluCases] <;> norm_num
  · fin_cases i <;> simp [fluCases] at hi ⊢ <;> norm_num at hi ⊢

/-- OpenStax Introductory Statistics 2e Practice exercise 12.49. To four decimals the regression line
of the flu data (1981 to 2002; the pre-1981 row is excluded because its year is unknown) has slope
strictly between `1749.7769` and `1749.7770` and intercept strictly between `-3448225.0475` and
`-3448225.0474`. -/
@[kb "openstaxintrostats2e" "Exercise 12.49, p. 669"]
theorem ex_12_49_flu_line_four_decimals :
    (1749.7769 < slope fluYear fluCases ∧ slope fluYear fluCases < 1749.7770) ∧
      (-3448225.0475 < intercept fluYear fluCases ∧ intercept fluYear fluCases < -3448225.0474) := by
  rw [flu_slope, flu_intercept]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 12.50. The correlation of year and flu cases
is strictly between `0.4526` and `0.4527` (about `0.4526`). -/
@[kb "openstaxintrostats2e" "Exercise 12.50, p. 669"]
theorem ex_12_50_flu_correlation_four_decimals :
    0.4526 < correlation fluYear fluCases ∧ correlation fluYear fluCases < 0.4527 :=
  ex_12_38_flu_correlation

/-! ### Section 12.6: outliers -/

/-- OpenStax Introductory Statistics 2e Practice exercise 12.55. A data set of `18` points whose sum of
squared errors is `49` has standard error of the estimate `√(49/(18 - 2)) = 7/4 = 1.75`. -/
@[kb "openstaxintrostats2e" "Exercise 12.55, p. 670"]
theorem ex_12_55_standard_error_from_sse :
    Real.sqrt (49 / (((18 : ℕ) : ℝ) - 2)) = 7 / 4 := by
  rw [show (49 : ℝ) / (((18 : ℕ) : ℝ) - 2) = (7 / 4) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-- OpenStax Introductory Statistics 2e Practice exercise 12.56. By the book's rule a point is an outlier
when its vertical distance from the line exceeds twice the standard error: for standard error `9.8` the
cutoff is exactly `19.6`. -/
@[kb "openstaxintrostats2e" "Exercise 12.56, p. 670"]
theorem ex_12_56_outlier_cutoff : (2 * 9.8 : ℝ) = 19.6 := by norm_num

end UndergradKB.Statistics.Course.PracticeC12
