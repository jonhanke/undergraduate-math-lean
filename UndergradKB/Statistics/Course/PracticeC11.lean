import Mathlib.Data.Fin.VecNotation
import UndergradKB.Common.Attr
import UndergradKB.Statistics.ChiSquared
import UndergradKB.Statistics.Course.ExamplesC11C13

/-!
# Practice exercises, chapter 11 (OpenStax *Introductory Statistics 2e*): the chi-square distribution

Mean and standard deviation of the chi-square law, and the goodness-of-fit, independence, homogeneity
and single-variance computations of the Practice exercises of chapter 11, using `chiSquareStat`,
`tableExpected` and `tableChiSquare` of `ExamplesC11C13`. Chi-square critical values used for decisions
are standard table values (quoted, not proved); p-values are not computed.
-/

namespace UndergradKB.Statistics.Course.PracticeC11

open MeasureTheory ProbabilityTheory UndergradKB.Statistics UndergradKB.Statistics.Course.ExamplesC11C13

/-! ### Section 11.1: facts about the chi-square distribution -/

/-- OpenStax Introductory Statistics 2e Practice exercise 11.1. The chi-square law with `25` degrees of
freedom has mean `25` and variance `50`, so its standard deviation `√50` lies strictly between `7.0710` and
`7.0711`. -/
@[kb "openstaxintrostats2e" "Exercise 11.1, p. 602"]
theorem ex_11_1_mean_and_sd_df25 :
    ∫ x, x ∂(chiSquared 25) = 25 ∧ variance id (chiSquared 25) = 50 ∧
      (7.0710 < Real.sqrt 50 ∧ Real.sqrt 50 < 7.0711) := by
  refine ⟨integral_id_chiSquared (by norm_num), ?_, ?_, ?_⟩
  · rw [variance_id_chiSquared (by norm_num)]; norm_num
  · apply Real.lt_sqrt_of_sq_lt; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 11.4. The mean of the chi-square curve sits at
its number of degrees of freedom: for every `k > 0`, the mean of the law with `k` degrees of freedom is
`k`. -/
@[kb "openstaxintrostats2e" "Exercise 11.4, p. 602"]
theorem ex_11_4_mean_is_df {k : ℝ} (hk : 0 < k) : ∫ x, x ∂(chiSquared k) = k :=
  integral_id_chiSquared hk

/-! ### Section 11.2: goodness of fit -/

/-- OpenStax Introductory Statistics 2e Practice exercise 11.9. The teacher's grade proportions
`0.25, 0.30, 0.35, 0.10` add up to `1`, they give expected counts `5, 6, 7, 2` for a class of `20`, and the
test has `4 - 1 = 3` degrees of freedom. -/
@[kb "openstaxintrostats2e" "Exercise 11.9, p. 603"]
theorem ex_11_9_grades_df :
    (∑ i, (![0.25, 0.30, 0.35, 0.10] : Fin 4 → ℝ) i) = 1 ∧
      (fun i : Fin 4 => 20 * (![0.25, 0.30, 0.35, 0.10] : Fin 4 → ℝ) i) = ![5, 6, 7, 2] ∧
      Fintype.card (Fin 4) - 1 = 3 := by
  refine ⟨?_, ?_, rfl⟩
  · simp [Fin.sum_univ_succ]; norm_num
  · funext i; fin_cases i <;> simp <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 11.10. The null hypothesis of the grade test
specifies the proportions `0.25, 0.30, 0.35, 0.10` for A, B, C, D, a valid distribution: the
proportions are nonnegative and add up to `1`. -/
@[kb "openstaxintrostats2e" "Exercise 11.10, p. 603"]
theorem ex_11_10_grade_null_distribution :
    (∀ i, 0 ≤ (![0.25, 0.30, 0.35, 0.10] : Fin 4 → ℝ) i) ∧
      (∑ i, (![0.25, 0.30, 0.35, 0.10] : Fin 4 → ℝ) i) = 1 := by
  refine ⟨?_, ?_⟩
  · intro i; fin_cases i <;> simp <;> norm_num
  · simp [Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 11.11. For observed grade counts `7, 7, 5, 1`
against expected `5, 6, 7, 2` the statistic is exactly `214/105`, strictly between `2.038` and
`2.039`. -/
@[kb "openstaxintrostats2e" "Exercise 11.11, p. 603"]
theorem ex_11_11_grades_statistic :
    chiSquareStat (![7, 7, 5, 1] : Fin 4 → ℝ) ![5, 6, 7, 2] = 214 / 105 ∧
      (2.038 < chiSquareStat (![7, 7, 5, 1] : Fin 4 → ℝ) ![5, 6, 7, 2] ∧
        chiSquareStat (![7, 7, 5, 1] : Fin 4 → ℝ) ![5, 6, 7, 2] < 2.039) := by
  have h : chiSquareStat (![7, 7, 5, 1] : Fin 4 → ℝ) ![5, 6, 7, 2] = 214 / 105 := by
    simp [chiSquareStat, Fin.sum_univ_succ]; norm_num
  rw [h]
  exact ⟨rfl, by norm_num, by norm_num⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 11.13. The grade statistic `214/105 (≈ 2.04)` is
below the standard table value `7.815` for `3` degrees of freedom and level `0.05` (a table value, not
proved): do not reject the teacher's distribution. -/
@[kb "openstaxintrostats2e" "Exercise 11.13, p. 603"]
theorem ex_11_13_grades_decision :
    chiSquareStat (![7, 7, 5, 1] : Fin 4 → ℝ) ![5, 6, 7, 2] < 7.815 := by
  have h : chiSquareStat (![7, 7, 5, 1] : Fin 4 → ℝ) ![5, 6, 7, 2] = 214 / 105 := by
    simp [chiSquareStat, Fin.sum_univ_succ]; norm_num
  rw [h]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 11.14. In Santa Clara County the population
percentages `42.9, 26.7, 2.6, 27.8` add up to `100`, and for `4075` COVID-19 cases the expected counts are
`1748.175, 1088.025, 105.95, 1132.85` (the first rounds to the book's `1748.18`); the case counts
`2229, 1157, 457, 232` add up to `4075`. -/
@[kb "openstaxintrostats2e" "Exercise 11.14, p. 604"]
theorem ex_11_14_covid_expected :
    (∑ i, (![0.429, 0.267, 0.026, 0.278] : Fin 4 → ℝ) i) = 1 ∧
      (fun i : Fin 4 => 4075 * (![0.429, 0.267, 0.026, 0.278] : Fin 4 → ℝ) i) =
        ![1748.175, 1088.025, 105.95, 1132.85] ∧
      (∑ i, (![2229, 1157, 457, 232] : Fin 4 → ℝ) i) = 4075 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Fin.sum_univ_succ]; norm_num
  · funext i; fin_cases i <;> simp <;> norm_num
  · simp [Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 11.18. Four ethnic groups give `4 - 1 = 3`
degrees of freedom for the COVID-19 goodness-of-fit test. -/
@[kb "openstaxintrostats2e" "Exercise 11.18, p. 604"]
theorem ex_11_18_covid_df : Fintype.card (Fin 4) - 1 = 3 := rfl

/-- OpenStax Introductory Statistics 2e Practice exercise 11.19. For observed cases `2229, 1157, 457, 232`
against expected `1748.175, 1088.025, 105.95, 1132.85` the statistic is exactly
`19596546445/9719853`, strictly between `2016.136` and `2016.137`. -/
@[kb "openstaxintrostats2e" "Exercise 11.19, p. 604"]
theorem ex_11_19_covid_statistic :
    chiSquareStat (![2229, 1157, 457, 232] : Fin 4 → ℝ) ![1748.175, 1088.025, 105.95, 1132.85] =
        19596546445 / 9719853 ∧
      (2016.136 < chiSquareStat (![2229, 1157, 457, 232] : Fin 4 → ℝ) ![1748.175, 1088.025, 105.95, 1132.85] ∧
        chiSquareStat (![2229, 1157, 457, 232] : Fin 4 → ℝ) ![1748.175, 1088.025, 105.95, 1132.85] < 2016.137) := by
  have h : chiSquareStat (![2229, 1157, 457, 232] : Fin 4 → ℝ) ![1748.175, 1088.025, 105.95, 1132.85] =
      19596546445 / 9719853 := by
    simp [chiSquareStat, Fin.sum_univ_succ]; norm_num
  rw [h]
  exact ⟨rfl, by norm_num, by norm_num⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 11.22. The COVID-19 statistic (above `2016`)
far exceeds the standard table value `7.815` for `3` degrees of freedom and level `0.05` (a table value,
not proved): reject, the cases do not follow the county's ethnic make-up. -/
@[kb "openstaxintrostats2e" "Exercise 11.22, p. 604"]
theorem ex_11_22_covid_decision :
    (7.815 : ℝ) < chiSquareStat (![2229, 1157, 457, 232] : Fin 4 → ℝ) ![1748.175, 1088.025, 105.95, 1132.85] := by
  have h : chiSquareStat (![2229, 1157, 457, 232] : Fin 4 → ℝ) ![1748.175, 1088.025, 105.95, 1132.85] =
      19596546445 / 9719853 := by
    simp [chiSquareStat, Fin.sum_univ_succ]; norm_num
  rw [h]; norm_num

/-! ### Section 11.3: test of independence -/

/-- Observed table of the railroad exercises (rows: distance classes 1-100, 101-200, 201-300, 301-400,
401-500 miles; columns: third, second, first class). -/
noncomputable def railTable : Fin 5 → Fin 3 → ℝ :=
  ![![21, 14, 6], ![18, 16, 8], ![16, 17, 15], ![12, 14, 21], ![6, 6, 10]]

/-- OpenStax Introductory Statistics 2e Practice exercise 11.27. The railroad independence test has
`(5 - 1)(3 - 1) = 8` degrees of freedom; the printed row totals `41, 42, 48, 47, 22`, column totals
`73, 67, 60` and grand total `200` check. -/
@[kb "openstaxintrostats2e" "Exercise 11.27, p. 605"]
theorem ex_11_27_rail_df :
    (Fintype.card (Fin 5) - 1) * (Fintype.card (Fin 3) - 1) = 8 ∧
      (∀ i : Fin 5, ∑ j, railTable i j = ![41, 42, 48, 47, 22] i) ∧
      (∀ j : Fin 3, ∑ i, railTable i j = ![73, 67, 60] j) ∧ (∑ i, ∑ j, railTable i j) = 200 := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [railTable, Fin.sum_univ_succ] <;> norm_num
  · intro j; fin_cases j <;> simp [railTable, Fin.sum_univ_succ] <;> norm_num
  · simp [railTable, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 11.28. Under independence the expected number
of passengers travelling `201-300` miles in second class is `48 · 67 / 200 = 16.08`. -/
@[kb "openstaxintrostats2e" "Exercise 11.28, p. 605"]
theorem ex_11_28_rail_expected_second_201_300 : tableExpected railTable 2 1 = 16.08 := by
  simp [tableExpected, railTable, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 11.29. Under independence the expected number
of passengers travelling `401-500` miles in first class is `22 · 60 / 200 = 6.6`. -/
@[kb "openstaxintrostats2e" "Exercise 11.29, p. 605"]
theorem ex_11_29_rail_expected_first_401_500 : tableExpected railTable 4 2 = 6.6 := by
  simp [tableExpected, railTable, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 11.30. The independence statistic of the
railroad table lies strictly between `15.92` and `15.93`. -/
@[kb "openstaxintrostats2e" "Exercise 11.30, p. 605"]
theorem ex_11_30_rail_statistic : 15.92 < tableChiSquare railTable ∧ tableChiSquare railTable < 15.93 := by
  constructor <;> simp [tableChiSquare, tableExpected, railTable, Fin.sum_univ_succ] <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 11.32. The railroad statistic (about `15.92`)
exceeds the standard table value `15.507` for `8` degrees of freedom and level `0.05` (a table value, not
proved): reject independence of ticket class and distance. -/
@[kb "openstaxintrostats2e" "Exercise 11.32, p. 605"]
theorem ex_11_32_rail_decision : (15.507 : ℝ) < tableChiSquare railTable := by
  simp [tableChiSquare, tableExpected, railTable, Fin.sum_univ_succ]; norm_num

/-- Observed table of the smoking exercises (rows: at most 10, 11 to 20, 21 to 30, at least 31
cigarettes per day; columns: Black, Native Hawaiian, Hispanic/Latino, Japanese American, White). -/
noncomputable def smokeTable : Fin 4 → Fin 5 → ℝ :=
  ![![9886, 2745, 12831, 8378, 7650], ![6514, 3062, 4932, 10680, 9877],
    ![1671, 1419, 1406, 4715, 6062], ![759, 788, 800, 2305, 3970]]

/-- OpenStax Introductory Statistics 2e Practice exercise 11.33. The completed smoking table has row
totals `41490, 35065, 15273, 8622`, column totals `18830, 8014, 19969, 26078, 27559` and grand total
`100450`. -/
@[kb "openstaxintrostats2e" "Exercise 11.33, p. 605"]
theorem ex_11_33_smoking_totals :
    (∀ i : Fin 4, ∑ j, smokeTable i j = ![41490, 35065, 15273, 8622] i) ∧
      (∀ j : Fin 5, ∑ i, smokeTable i j = ![18830, 8014, 19969, 26078, 27559] j) ∧
      (∑ i, ∑ j, smokeTable i j) = 100450 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [smokeTable, Fin.sum_univ_succ] <;> norm_num
  · intro j; fin_cases j <;> simp [smokeTable, Fin.sum_univ_succ] <;> norm_num
  · simp [smokeTable, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 11.35. Some expected counts of the smoking
table, each within `0.005` of the printed two-decimal value: the first row `7777.57, 3310.11` (Black,
Native Hawaiian), the last row's first entry `1616.25`, and the White column's second row `9620.27`. -/
@[kb "openstaxintrostats2e" "Exercise 11.35, p. 606"]
theorem ex_11_35_smoking_expected :
    (7777.565 < tableExpected smokeTable 0 0 ∧ tableExpected smokeTable 0 0 < 7777.575) ∧
      (3310.105 < tableExpected smokeTable 0 1 ∧ tableExpected smokeTable 0 1 < 3310.115) ∧
      (1616.245 < tableExpected smokeTable 3 0 ∧ tableExpected smokeTable 3 0 < 1616.255) ∧
      (9620.265 < tableExpected smokeTable 1 4 ∧ tableExpected smokeTable 1 4 < 9620.275) := by
  simp [tableExpected, smokeTable, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 11.36. The smoking independence test has
`(4 - 1)(5 - 1) = 12` degrees of freedom. -/
@[kb "openstaxintrostats2e" "Exercise 11.36, p. 606"]
theorem ex_11_36_smoking_df : (Fintype.card (Fin 4) - 1) * (Fintype.card (Fin 5) - 1) = 12 := rfl

/-- OpenStax Introductory Statistics 2e Practice exercise 11.37. The smoking statistic lies strictly
between `10301.84` and `10301.85` (the book prints `10,301.8`). -/
@[kb "openstaxintrostats2e" "Exercise 11.37, p. 606"]
theorem ex_11_37_smoking_statistic :
    10301.84 < tableChiSquare smokeTable ∧ tableChiSquare smokeTable < 10301.85 := by
  constructor <;> simp [tableChiSquare, tableExpected, smokeTable, Fin.sum_univ_succ] <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 11.41. At level `0.05` the smoking statistic
(above `10301`) exceeds the standard table value `21.026` for `12` degrees of freedom (a table value, not
proved): reject independence of smoking level and ethnic group. -/
@[kb "openstaxintrostats2e" "Exercise 11.41, p. 606"]
theorem ex_11_41_smoking_decision_05 : (21.026 : ℝ) < tableChiSquare smokeTable := by
  simp [tableChiSquare, tableExpected, smokeTable, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 11.42. At level `0.01` the smoking statistic
exceeds the standard table value `26.217` for `12` degrees of freedom (a table value, not proved):
reject independence. -/
@[kb "openstaxintrostats2e" "Exercise 11.42, p. 606"]
theorem ex_11_42_smoking_decision_01 : (26.217 : ℝ) < tableChiSquare smokeTable := by
  simp [tableChiSquare, tableExpected, smokeTable, Fin.sum_univ_succ]; norm_num

/-! ### Section 11.4: test for homogeneity -/

/-- Observed table of the doctors' working hours (rows: private practice, hospital; columns: 20-30,
30-40, 40-50, 50-60 hours). -/
noncomputable def doctorsTable : Fin 2 → Fin 4 → ℝ :=
  ![![16, 40, 38, 6], ![8, 44, 59, 39]]

/-- OpenStax Introductory Statistics 2e Practice exercise 11.49. The doctors' table has `100` private
practice and `150` hospital doctors, and the homogeneity test has `4 - 1 = 3` degrees of freedom. -/
@[kb "openstaxintrostats2e" "Exercise 11.49, p. 607"]
theorem ex_11_49_doctors_df :
    (∑ j, doctorsTable 0 j) = 100 ∧ (∑ j, doctorsTable 1 j) = 150 ∧ Fintype.card (Fin 4) - 1 = 3 := by
  refine ⟨?_, ?_, rfl⟩
  · simp [doctorsTable, Fin.sum_univ_succ]; norm_num
  · simp [doctorsTable, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 11.50. The homogeneity statistic of the doctors'
table lies strictly between `22.50` and `22.51`. -/
@[kb "openstaxintrostats2e" "Exercise 11.50, p. 607"]
theorem ex_11_50_doctors_statistic :
    22.50 < tableChiSquare doctorsTable ∧ tableChiSquare doctorsTable < 22.51 := by
  constructor <;> simp [tableChiSquare, tableExpected, doctorsTable, Fin.sum_univ_succ] <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 11.52. The doctors' statistic (about `22.50`)
exceeds the standard table value `7.815` for `3` degrees of freedom and level `0.05` (a table value, not
proved): reject, the distributions of working hours differ. -/
@[kb "openstaxintrostats2e" "Exercise 11.52, p. 607"]
theorem ex_11_52_doctors_decision : (7.815 : ℝ) < tableChiSquare doctorsTable := by
  simp [tableChiSquare, tableExpected, doctorsTable, Fin.sum_univ_succ]; norm_num

/-! ### Section 11.6: test of a single variance -/

/-- OpenStax Introductory Statistics 2e Practice exercise 11.63. The height exercise tests
`H₀: σ² = 0.81²` against `σ² > 0.81²`; the null value of the variance is `0.6561`. -/
@[kb "openstaxintrostats2e" "Exercise 11.63, p. 607"]
theorem ex_11_63_height_null_variance : (0.81 : ℝ) ^ 2 = 0.6561 := by norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 11.64. For `50` students the test has
`50 - 1 = 49` degrees of freedom; the statistic `49 · 0.96² / 0.81²` equals `50176/729`, strictly between
`68.82` and `68.83`. -/
@[kb "openstaxintrostats2e" "Exercise 11.64, p. 608"]
theorem ex_11_64_height_df :
    50 - 1 = 49 ∧ ((50 : ℝ) - 1) * 0.96 ^ 2 / 0.81 ^ 2 = 50176 / 729 ∧
      (68.82 < ((50 : ℝ) - 1) * 0.96 ^ 2 / 0.81 ^ 2 ∧ ((50 : ℝ) - 1) * 0.96 ^ 2 / 0.81 ^ 2 < 68.83) := by
  refine ⟨rfl, by norm_num, by norm_num, by norm_num⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 11.66. For `30` patients with sample standard
deviation `4.1` against `3.4` the statistic `29 · 4.1² / 3.4²` is exactly `48749/1156`, strictly between
`42.17` and `42.18`. -/
@[kb "openstaxintrostats2e" "Exercise 11.66, p. 608"]
theorem ex_11_66_waiting_statistic :
    ((30 : ℝ) - 1) * 4.1 ^ 2 / 3.4 ^ 2 = 48749 / 1156 ∧
      (42.17 < ((30 : ℝ) - 1) * 4.1 ^ 2 / 3.4 ^ 2 ∧ ((30 : ℝ) - 1) * 4.1 ^ 2 / 3.4 ^ 2 < 42.18) := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 11.68. The waiting-time statistic `48749/1156`
(about `42.17`) is below the standard right-tail table value `42.557` for `29` degrees of freedom and level
`0.05` (a table value, not proved): do not reject the original variance. -/
@[kb "openstaxintrostats2e" "Exercise 11.68, p. 608"]
theorem ex_11_68_waiting_decision : ((30 : ℝ) - 1) * 4.1 ^ 2 / 3.4 ^ 2 < 42.557 := by
  norm_num

end UndergradKB.Statistics.Course.PracticeC11
