import Mathlib.Data.Fin.VecNotation
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Data
import UndergradKB.Statistics.Regression

/-!
# Course layer, chapter 12 (OpenStax *Introductory Statistics 2e*): worked examples

Least-squares lines, correlation coefficients, predictions and residuals for the small data sets of
chapter 12, computed from the repository definitions `mean`, `sumSqDev`, `sumProdDev`, `slope`,
`intercept`, `correlation`, `sse` and `stdErrorEstimate`. Exact rational values are proved where the
book's output is exact arithmetic; where the book rounds, a two-sided bound is proved.
-/

namespace UndergradKB.Statistics.Course.ExamplesC12

open UndergradKB.Statistics

/-- Third-exam scores `x` of the eleven students of Example 12.6. -/
noncomputable def thirdExam : Fin 11 → ℝ := ![65, 67, 71, 71, 66, 75, 67, 70, 71, 69, 69]

/-- Final-exam scores `y` of the eleven students of Example 12.6. -/
noncomputable def finalExam : Fin 11 → ℝ := ![175, 133, 185, 163, 126, 198, 153, 163, 159, 151, 159]

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

private lemma mean_thirdExam : mean thirdExam = 761 / 11 := by
  simp [mean, thirdExam, Fin.sum_univ_succ]; norm_num

private lemma mean_finalExam : mean finalExam = 1765 / 11 := by
  simp [mean, finalExam, Fin.sum_univ_succ]; norm_num

private lemma sxx_thirdExam : sumSqDev thirdExam = 898 / 11 := by
  simp only [sumSqDev, mean_thirdExam]; simp [thirdExam, Fin.sum_univ_succ]; norm_num

private lemma syy_finalExam : sumSqDev finalExam = 47594 / 11 := by
  simp only [sumSqDev, mean_finalExam]; simp [finalExam, Fin.sum_univ_succ]; norm_num

private lemma sxy_exam : sumProdDev thirdExam finalExam = 4335 / 11 := by
  simp only [sumProdDev, mean_thirdExam, mean_finalExam]
  simp [thirdExam, finalExam, Fin.sum_univ_succ]
  norm_num

private lemma slope_exam : slope thirdExam finalExam = 4335 / 898 := by
  rw [slope, sxy_exam, sxx_thirdExam]; norm_num

private lemma intercept_exam : intercept thirdExam finalExam = -155815 / 898 := by
  rw [intercept, slope_exam, mean_thirdExam, mean_finalExam]; norm_num

/-- OpenStax Introductory Statistics 2e Example 12.6. For the eleven third-exam/final-exam pairs the
sample means are `x̄ = 761/11` and `ȳ = 1765/11`, and the sums of squares and products are
`Sxx = 898/11`, `Syy = 47594/11`, `Sxy = 4335/11`. -/
@[kb "openstaxintrostats2e" "Example 12.6, p. 635"]
theorem example_12_6_sums_of_squares :
    mean thirdExam = 761 / 11 ∧ mean finalExam = 1765 / 11 ∧ sumSqDev thirdExam = 898 / 11 ∧
      sumSqDev finalExam = 47594 / 11 ∧ sumProdDev thirdExam finalExam = 4335 / 11 :=
  ⟨mean_thirdExam, mean_finalExam, sxx_thirdExam, syy_finalExam, sxy_exam⟩

/-- OpenStax Introductory Statistics 2e Example 12.6. The least-squares slope for the third-exam
data is exactly `b = Sxy / Sxx = 4335/898`, which lies strictly between `4.82` and `4.83` (the book's
`4.83`), and the intercept is exactly `-155815/898`, strictly between `-173.52` and `-173.51`. -/
@[kb "openstaxintrostats2e" "Example 12.6, p. 635"]
theorem example_12_6_regression_line :
    slope thirdExam finalExam = 4335 / 898 ∧ intercept thirdExam finalExam = -155815 / 898 ∧
      4.82 < slope thirdExam finalExam ∧ slope thirdExam finalExam < 4.83 ∧
      -173.52 < intercept thirdExam finalExam ∧ intercept thirdExam finalExam < -173.51 := by
  rw [slope_exam, intercept_exam]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩ <;> norm_num

/-- OpenStax Introductory Statistics 2e Example 12.6. The correlation coefficient of the third-exam
and final-exam scores satisfies `0.663 < r < 0.664` (the book's `r = 0.6631`). -/
@[kb "openstaxintrostats2e" "Example 12.6, p. 635"]
theorem example_12_6_correlation :
    0.663 < correlation thirdExam finalExam ∧ correlation thirdExam finalExam < 0.664 := by
  unfold correlation
  rw [sxy_exam, sxx_thirdExam, syy_finalExam]
  exact corr_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

private lemma sse_exam :
    sse thirdExam finalExam (intercept thirdExam finalExam) (slope thirdExam finalExam) =
      2177017 / 898 := by
  rw [intercept_exam, slope_exam]
  simp [sse, thirdExam, finalExam, Fin.sum_univ_succ]
  norm_num

private lemma stdErr_exam_bounds :
    16.41 < stdErrorEstimate thirdExam finalExam ∧ stdErrorEstimate thirdExam finalExam < 16.42 := by
  unfold stdErrorEstimate
  rw [sse_exam]
  have h : ((11 : ℕ) : ℝ) - 2 = 9 := by norm_num
  rw [h]
  constructor
  · exact (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  · exact (Real.sqrt_lt' (by norm_num)).2 (by norm_num)

/-- OpenStax Introductory Statistics 2e Example 12.6 (sum of squared errors). The least-squares
line of the third-exam data has sum of squared errors exactly `2177017/898`, strictly between
`2424.29` and `2424.30`, and its standard error of the estimate `√(SSE/(n - 2))` lies strictly
between `16.41` and `16.42` (the book's `s = 16.412`). -/
@[kb "openstaxintrostats2e" "Example 12.6, p. 635"]
theorem example_12_6_sum_of_squared_errors :
    sse thirdExam finalExam (intercept thirdExam finalExam) (slope thirdExam finalExam) =
        2177017 / 898 ∧
      2424.29 < sse thirdExam finalExam (intercept thirdExam finalExam)
        (slope thirdExam finalExam) ∧
      sse thirdExam finalExam (intercept thirdExam finalExam) (slope thirdExam finalExam) < 2424.30 ∧
      16.41 < stdErrorEstimate thirdExam finalExam ∧ stdErrorEstimate thirdExam finalExam < 16.42 := by
  rw [sse_exam]
  exact ⟨rfl, by norm_num, by norm_num, stdErr_exam_bounds⟩

/-- OpenStax Introductory Statistics 2e Example 12.6 (least squares). Any other line, here the
rounded line `ŷ = -173.51 + 4.83 x` quoted in the book, has a larger sum of squared errors than the
least-squares line. -/
@[kb "openstaxintrostats2e" "Example 12.6, p. 635"]
theorem example_12_6_rounded_line_has_larger_sse :
    sse thirdExam finalExam (intercept thirdExam finalExam) (slope thirdExam finalExam) <
      sse thirdExam finalExam (-173.51) 4.83 := by
  rw [sse_exam]
  simp [sse, thirdExam, finalExam, Fin.sum_univ_succ]
  norm_num

/-- OpenStax Introductory Statistics 2e Example 12.6. The least-squares line passes through the
point of means: `a + b x̄ = ȳ`. -/
@[kb "openstaxintrostats2e" "Example 12.6, p. 635"]
theorem example_12_6_line_through_means :
    intercept thirdExam finalExam + slope thirdExam finalExam * mean thirdExam =
      mean finalExam :=
  intercept_add_slope_mul_mean thirdExam finalExam

/-- OpenStax Introductory Statistics 2e Section 12.5 (third-exam example). The least-squares line
predicts a final-exam score strictly between `178.88` and `178.89` for a third-exam score of 73;
the book's `179.08` is the value of the rounded line `-173.51 + 4.83 x`. -/
@[kb "openstaxintrostats2e" "§12.5, p. 646"]
theorem example_12_5_prediction_at_73 :
    178.88 < intercept thirdExam finalExam + slope thirdExam finalExam * 73 ∧
      intercept thirdExam finalExam + slope thirdExam finalExam * 73 < 178.89 ∧
      (-173.51 + 4.83 * 73 : ℝ) = 179.08 := by
  rw [intercept_exam, slope_exam]
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- OpenStax Introductory Statistics 2e Example 12.11(a). For a third-exam score of 66 the
least-squares line predicts a final-exam score strictly between `145.09` and `145.10`; the book's
`145.27` is the value of the rounded line `-173.51 + 4.83 x`. -/
@[kb "openstaxintrostats2e" "Example 12.11, p. 647"]
theorem example_12_11_prediction_at_66 :
    145.09 < intercept thirdExam finalExam + slope thirdExam finalExam * 66 ∧
      intercept thirdExam finalExam + slope thirdExam finalExam * 66 < 145.10 ∧
      (-173.51 + 4.83 * 66 : ℝ) = 145.27 := by
  rw [intercept_exam, slope_exam]
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- OpenStax Introductory Statistics 2e Example 12.11(b). Extrapolating to a third-exam score of 90
(outside the observed range 65 to 75) the line gives a value strictly between `260.95` and `260.96`,
above the maximum possible final score 200; the book's `261.19` is the rounded line's value. -/
@[kb "openstaxintrostats2e" "Example 12.11, p. 647"]
theorem example_12_11_extrapolation_at_90 :
    260.95 < intercept thirdExam finalExam + slope thirdExam finalExam * 90 ∧
      intercept thirdExam finalExam + slope thirdExam finalExam * 90 < 260.96 ∧
      (200 : ℝ) < intercept thirdExam finalExam + slope thirdExam finalExam * 90 ∧
      (-173.51 + 4.83 * 90 : ℝ) = 261.19 := by
  rw [intercept_exam, slope_exam]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num

/-- OpenStax Introductory Statistics 2e Example 12.12. Outlier rule: the student with third-exam
score 65 and final score 175 has residual exactly `31190/898 ≈ 34.73`, which exceeds twice the
standard error of the estimate (about `2 · 16.41`), while every other residual is smaller than
twice the standard error in absolute value. -/
@[kb "openstaxintrostats2e" "Example 12.12, p. 649"]
theorem example_12_12_outlier :
    finalExam 0 - (intercept thirdExam finalExam + slope thirdExam finalExam * thirdExam 0) =
        31190 / 898 ∧
      2 * stdErrorEstimate thirdExam finalExam <
        finalExam 0 - (intercept thirdExam finalExam + slope thirdExam finalExam * thirdExam 0) ∧
      ∀ i : Fin 11, i ≠ 0 →
        |finalExam i - (intercept thirdExam finalExam + slope thirdExam finalExam * thirdExam i)| <
          2 * stdErrorEstimate thirdExam finalExam := by
  obtain ⟨h1, h2⟩ := stdErr_exam_bounds
  have hr : finalExam 0 - (intercept thirdExam finalExam + slope thirdExam finalExam *
      thirdExam 0) = 31190 / 898 := by
    rw [intercept_exam, slope_exam]; simp [finalExam, thirdExam]; norm_num
  refine ⟨hr, ?_, ?_⟩
  · rw [hr]; linarith
  · intro i hi
    rw [intercept_exam, slope_exam]
    generalize stdErrorEstimate thirdExam finalExam = s at h1 h2 ⊢
    fin_cases i
    · exact absurd rfl hi
    all_goals
      simp [finalExam, thirdExam, abs_lt]
      constructor <;> linarith

/-- Third-exam scores of Example 12.6 after deleting the outlier `(65, 175)` (Example 12.12). -/
noncomputable def thirdExam' : Fin 10 → ℝ := ![67, 71, 71, 66, 75, 67, 70, 71, 69, 69]

/-- Final-exam scores of Example 12.6 after deleting the outlier `(65, 175)` (Example 12.12). -/
noncomputable def finalExam' : Fin 10 → ℝ := ![133, 185, 163, 126, 198, 153, 163, 159, 151, 159]

private lemma mean_x2 : mean thirdExam' = 348 / 5 := by
  simp [mean, thirdExam', Fin.sum_univ_succ]; norm_num

private lemma mean_y2 : mean finalExam' = 159 := by
  simp [mean, finalExam', Fin.sum_univ_succ]; norm_num

private lemma sxx2 : sumSqDev thirdExam' = 312 / 5 := by
  simp only [sumSqDev, mean_x2]; simp [thirdExam', Fin.sum_univ_succ]; norm_num

private lemma syy2 : sumSqDev finalExam' = 4094 := by
  simp only [sumSqDev, mean_y2]; simp [finalExam', Fin.sum_univ_succ]; norm_num

private lemma sxy2 : sumProdDev thirdExam' finalExam' = 461 := by
  simp only [sumProdDev, mean_x2, mean_y2]; simp [thirdExam', finalExam', Fin.sum_univ_succ]
  norm_num

private lemma slope2 : slope thirdExam' finalExam' = 2305 / 312 := by
  rw [slope, sxy2, sxx2]; norm_num

private lemma intercept2 : intercept thirdExam' finalExam' = -9235 / 26 := by
  rw [intercept, slope2, mean_x2, mean_y2]; norm_num

/-- OpenStax Introductory Statistics 2e Example 12.12 (outlier removed). Deleting the outlier
`(65, 175)` leaves ten points whose least-squares line has slope exactly `2305/312` (about `7.39`)
and intercept exactly `-9235/26` (about `-355.19`); the correlation lies strictly between `0.912`
and `0.913` (the book's `0.9121`). -/
@[kb "openstaxintrostats2e" "Example 12.12, p. 649"]
theorem example_12_12_line_without_outlier :
    slope thirdExam' finalExam' = 2305 / 312 ∧ intercept thirdExam' finalExam' = -9235 / 26 ∧
      0.912 < correlation thirdExam' finalExam' ∧ correlation thirdExam' finalExam' < 0.913 := by
  refine ⟨slope2, intercept2, ?_⟩
  unfold correlation
  rw [sxy2, sxx2, syy2]
  exact corr_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- OpenStax Introductory Statistics 2e Example 12.12 (outlier removed, sum of squares). The line
fitted without the outlier has sum of squared errors exactly `214723/312 ≈ 688.2` on the ten
remaining points, far smaller than the `2177017/898 ≈ 2424.3` of the full eleven-point line. -/
@[kb "openstaxintrostats2e" "Example 12.12, p. 649"]
theorem example_12_12_sse_without_outlier :
    sse thirdExam' finalExam' (intercept thirdExam' finalExam') (slope thirdExam' finalExam') =
        214723 / 312 ∧ (214723 / 312 : ℝ) < 2177017 / 898 := by
  refine ⟨?_, by norm_num⟩
  rw [intercept2, slope2]
  simp [sse, thirdExam', finalExam', Fin.sum_univ_succ]
  norm_num

/-- OpenStax Introductory Statistics 2e Example 12.13. With the outlier removed the line
`-9235/26 + (2305/312) x` predicts a final score strictly between `184.11` and `184.12` for a
third-exam score of 73 (the book's `184.28` is the value of the rounded line `-355.19 + 7.39 x`),
which differs from the original line's prediction by more than 5 points. -/
@[kb "openstaxintrostats2e" "Example 12.13, p. 652"]
theorem example_12_13_prediction_without_outlier :
    184.11 < intercept thirdExam' finalExam' + slope thirdExam' finalExam' * 73 ∧
    intercept thirdExam' finalExam' + slope thirdExam' finalExam' * 73 < 184.12 ∧
    (-355.19 + 7.39 * 73 : ℝ) = 184.28 ∧
    5 < (intercept thirdExam' finalExam' + slope thirdExam' finalExam' * 73) -
      (intercept thirdExam finalExam + slope thirdExam finalExam * 73) := by
  rw [intercept2, slope2, intercept_exam, slope_exam]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num

/-- Ages (years) of the children in Example 12.5. -/
noncomputable def childAge : Fin 4 → ℝ := ![3, 4, 6, 7]

/-- Vocabulary sizes (words) of the children in Example 12.5. -/
noncomputable def childVocab : Fin 4 → ℝ := ![655, 1098, 2463, 3195]

private lemma vocab_stats :
    mean childAge = 5 ∧ mean childVocab = 7411 / 4 ∧ sumSqDev childAge = 10 ∧
      sumSqDev childVocab = 16713171 / 4 ∧ sumProdDev childAge childVocab = 6445 := by
  have h1 : mean childAge = 5 := by simp [mean, childAge, Fin.sum_univ_succ]; norm_num
  have h2 : mean childVocab = 7411 / 4 := by simp [mean, childVocab, Fin.sum_univ_succ]; norm_num
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · simp only [sumSqDev, h1]; simp [childAge, Fin.sum_univ_succ]; norm_num
  · simp only [sumSqDev, h2]; simp [childVocab, Fin.sum_univ_succ]; norm_num
  · simp only [sumProdDev, h1, h2]; simp [childAge, childVocab, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Example 12.5. For the four children (age, vocabulary size)
= (3, 655), (4, 1098), (6, 2463), (7, 3195) the least-squares line has slope exactly `644.5` words
per year and intercept exactly `-5479/4`, and the correlation lies strictly between `0.997` and
`0.998`, confirming the strong positive linear relationship seen in the scatter plot. -/
@[kb "openstaxintrostats2e" "Example 12.5, p. 632"]
theorem example_12_5_vocabulary_regression :
    slope childAge childVocab = 1289 / 2 ∧ intercept childAge childVocab = -5479 / 4 ∧
      0.997 < correlation childAge childVocab ∧ correlation childAge childVocab < 0.998 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := vocab_stats
  have hs : slope childAge childVocab = 1289 / 2 := by rw [slope, h5, h3]; norm_num
  refine ⟨hs, ?_, ?_⟩
  · rw [intercept, hs, h1, h2]; norm_num
  · unfold correlation
    rw [h3, h4, h5]
    exact corr_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)

/-- Noon temperatures (degrees F) of the nine days of the ice-cream residuals example. -/
noncomputable def temperature : Fin 9 → ℝ := ![70, 85, 65, 72, 80, 61, 75, 78, 68]

/-- Ice-cream cones sold on the nine days of the residuals example. -/
noncomputable def conesSold : Fin 9 → ℝ := ![105, 240, 49, 147, 231, 38, 193, 196, 89]

private lemma cone_stats :
    mean temperature = 218 / 3 ∧ mean conesSold = 1288 / 9 ∧ sumSqDev temperature = 464 ∧
      sumSqDev conesSold = 420290 / 9 ∧ sumProdDev temperature conesSold = 13612 / 3 := by
  have h1 : mean temperature = 218 / 3 := by simp [mean, temperature, Fin.sum_univ_succ]; norm_num
  have h2 : mean conesSold = 1288 / 9 := by simp [mean, conesSold, Fin.sum_univ_succ]; norm_num
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · simp only [sumSqDev, h1]; simp [temperature, Fin.sum_univ_succ]; norm_num
  · simp only [sumSqDev, h2]; simp [conesSold, Fin.sum_univ_succ]; norm_num
  · simp only [sumProdDev, h1, h2]; simp [temperature, conesSold, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e, residuals-plot example of Section 12.3 (nine days of ice
cream sales against temperature). The least-squares slope is exactly `3403/348`, strictly between
`9.77` and `9.78` cones per degree; the correlation lies strictly between `0.974` and `0.975`;
and the nine residuals of the line sum to exactly zero. -/
@[kb "openstaxintrostats2e" "§12.3, p. 634"]
theorem example_12_3_ice_cream_regression :
    slope temperature conesSold = 3403 / 348 ∧ 9.77 < slope temperature conesSold ∧
      slope temperature conesSold < 9.78 ∧
      0.974 < correlation temperature conesSold ∧ correlation temperature conesSold < 0.975 ∧
      ∑ i, (conesSold i - (intercept temperature conesSold + slope temperature conesSold *
        temperature i)) = 0 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := cone_stats
  have hs : slope temperature conesSold = 3403 / 348 := by rw [slope, h5, h3]; norm_num
  have hc : 0.974 < correlation temperature conesSold ∧ correlation temperature conesSold < 0.975 := by
    unfold correlation
    rw [h3, h4, h5]
    exact corr_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  refine ⟨hs, ?_, ?_, hc.1, hc.2, sum_residual_eq_zero temperature conesSold⟩
  · rw [hs]; norm_num
  · rw [hs]; norm_num

end UndergradKB.Statistics.Course.ExamplesC12
