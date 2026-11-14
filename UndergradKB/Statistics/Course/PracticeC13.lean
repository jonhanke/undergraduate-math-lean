import Mathlib.Data.Fin.VecNotation
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Data
import UndergradKB.Statistics.Anova

/-!
# Practice exercises, chapter 13 (OpenStax *Introductory Statistics 2e*): F distribution and ANOVA

One-way analysis of variance tables (sums of squares, mean squares, degrees of freedom, the `F` ratio)
for the data of the Practice exercises, and the `F` ratio of two sample variances. Quantiles and p-values
of the `F` distribution are not computable in this repository: where an exercise asks for a decision the
critical value is the standard table value (named in the statement, not proved) and only the comparison
is proved; exercises asking for the p-value itself are skipped.
-/

namespace UndergradKB.Statistics.Course.PracticeC13

open UndergradKB.Statistics

/-! ### Section 13.3: the `F` statistic is nonnegative -/

/-- OpenStax Introductory Statistics 2e Practice exercise 13.24. The `F` statistic of any one-way
ANOVA (with `1 ≤ k` groups and more observations than groups) is nonnegative; it can take any value from
`0` upward, since it is a ratio of two nonnegative mean squares. -/
@[kb "openstaxintrostats2e" "Exercise 13.24, p. 710"]
theorem ex_13_24_f_statistic_nonneg {n k : ℕ} (x : Fin n → ℝ) (g : Fin n → Fin k) (hk : 1 ≤ k)
    (hkn : k < n) : 0 ≤ fStatistic x g := by
  have h1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have h2 : (0 : ℝ) ≤ (n : ℝ) - k := by
    have : (k : ℝ) ≤ n := by exact_mod_cast hkn.le
    linarith
  have hb : 0 ≤ ssBetween x g :=
    Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hw : 0 ≤ ssWithin x g := Finset.sum_nonneg fun i _ => sq_nonneg _
  exact div_nonneg (div_nonneg hb h1) (div_nonneg hw h2)

/-! ### Section 13.2: weights of men in three areas (Table 13.13) -/

/-- The fifteen weights of Table 13.13 (group 1, then group 2, then group 3). -/
noncomputable def wx : Fin 15 → ℝ :=
  ![216, 198, 240, 187, 176, 202, 213, 284, 228, 210, 170, 165, 182, 197, 201]

/-- The group of each weight of Table 13.13. -/
def wg : Fin 15 → Fin 3 := ![0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2]

private lemma w_size : ∀ j, groupSize wg j = (![5, 5, 5] : Fin 3 → ℕ) j := by
  intro j; fin_cases j <;> decide

private lemma w_ssb : ssBetween wx wg = 24696 / 5 := by
  simp only [ssBetween, groupMean, w_size, Finset.sum_filter]
  simp [mean, wx, wg, Finset.sum_filter, Fin.sum_univ_succ]
  norm_num

private lemma w_ssw : ssWithin wx wg = 39602 / 5 := by
  simp only [ssWithin, groupMean, w_size, Finset.sum_filter]
  simp [wx, wg, Finset.sum_filter, Fin.sum_univ_succ]
  norm_num

private lemma w_msb : msBetween wx wg = 12348 / 5 := by rw [msBetween, w_ssb]; norm_num

private lemma w_msw : msWithin wx wg = 19801 / 30 := by rw [msWithin, w_ssw]; norm_num

private lemma w_f : fStatistic wx wg = 74088 / 19801 := by
  rw [fStatistic, w_msb, w_msw]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 13.9. The sum of squares between the three
weight groups is exactly `24696/5 = 4939.2`. -/
@[kb "openstaxintrostats2e" "Exercise 13.9, p. 709"]
theorem ex_13_9_weights_ss_between : ssBetween wx wg = 24696 / 5 := w_ssb

/-- OpenStax Introductory Statistics 2e Practice exercise 13.10. The sum of squares of error (within
the groups) of the weights is exactly `39602/5 = 7920.4`. -/
@[kb "openstaxintrostats2e" "Exercise 13.10, p. 709"]
theorem ex_13_10_weights_ss_within : ssWithin wx wg = 39602 / 5 := w_ssw

/-- OpenStax Introductory Statistics 2e Practice exercise 13.11. With `3` groups, the numerator degrees
of freedom of the weights ANOVA are `3 - 1 = 2`. -/
@[kb "openstaxintrostats2e" "Exercise 13.11, p. 709"]
theorem ex_13_11_weights_df_numerator : (3 : ℕ) - 1 = 2 := rfl

/-- OpenStax Introductory Statistics 2e Practice exercise 13.12. With `15` observations in `3` groups,
the denominator degrees of freedom of the weights ANOVA are `15 - 3 = 12`. -/
@[kb "openstaxintrostats2e" "Exercise 13.12, p. 709"]
theorem ex_13_12_weights_df_denominator : (15 : ℕ) - 3 = 12 := rfl

/-- OpenStax Introductory Statistics 2e Practice exercise 13.13. The mean square between the weight
groups is exactly `12348/5 = 2469.6`. -/
@[kb "openstaxintrostats2e" "Exercise 13.13, p. 709"]
theorem ex_13_13_weights_ms_between : msBetween wx wg = 12348 / 5 := w_msb

/-- OpenStax Introductory Statistics 2e Practice exercise 13.14. The mean square error of the weights is
exactly `19801/30`, strictly between `660.03` and `660.04`. -/
@[kb "openstaxintrostats2e" "Exercise 13.14, p. 709"]
theorem ex_13_14_weights_ms_within :
    msWithin wx wg = 19801 / 30 ∧ 660.03 < msWithin wx wg ∧ msWithin wx wg < 660.04 := by
  rw [w_msw]; refine ⟨rfl, ?_, ?_⟩ <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 13.15. The `F` statistic of the weights is
exactly `74088/19801`, strictly between `3.7416` and `3.7417`. -/
@[kb "openstaxintrostats2e" "Exercise 13.15, p. 709"]
theorem ex_13_15_weights_f_statistic :
    fStatistic wx wg = 74088 / 19801 ∧ 3.7416 < fStatistic wx wg ∧ fStatistic wx wg < 3.7417 := by
  rw [w_f]; refine ⟨rfl, ?_, ?_⟩ <;> norm_num

/-! ### Section 13.2: goals per game of four soccer teams (Table 13.14) -/

/-- The twenty goal counts of Table 13.14 (team 1, then team 2, team 3, team 4). -/
noncomputable def sx : Fin 20 → ℝ :=
  ![1, 2, 0, 3, 2, 2, 3, 2, 4, 4, 0, 1, 1, 0, 0, 3, 4, 4, 3, 2]

/-- The team of each goal count of Table 13.14. -/
def sg : Fin 20 → Fin 4 := ![0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3]

private lemma s_size : ∀ j, groupSize sg j = (![5, 5, 5, 5] : Fin 4 → ℕ) j := by
  intro j; fin_cases j <;> decide

private lemma s_ssb : ssBetween sx sg = 103 / 4 := by
  simp only [ssBetween, groupMean, s_size, Finset.sum_filter]
  simp [mean, sx, sg, Finset.sum_filter, Fin.sum_univ_succ]
  norm_num

private lemma s_ssw : ssWithin sx sg = 66 / 5 := by
  simp only [ssWithin, groupMean, s_size, Finset.sum_filter]
  simp [sx, sg, Finset.sum_filter, Fin.sum_univ_succ]
  norm_num

private lemma s_msb : msBetween sx sg = 103 / 12 := by rw [msBetween, s_ssb]; norm_num

private lemma s_msw : msWithin sx sg = 33 / 40 := by rw [msWithin, s_ssw]; norm_num

private lemma s_f : fStatistic sx sg = 1030 / 99 := by
  rw [fStatistic, s_msb, s_msw]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 13.16. The sum of squares between the four
soccer teams is exactly `103/4 = 25.75`. -/
@[kb "openstaxintrostats2e" "Exercise 13.16, p. 709"]
theorem ex_13_16_soccer_ss_between : ssBetween sx sg = 103 / 4 := s_ssb

/-- OpenStax Introductory Statistics 2e Practice exercise 13.17. With `4` teams the numerator degrees of
freedom are `4 - 1 = 3`. -/
@[kb "openstaxintrostats2e" "Exercise 13.17, p. 709"]
theorem ex_13_17_soccer_df_numerator : (4 : ℕ) - 1 = 3 := rfl

/-- OpenStax Introductory Statistics 2e Practice exercise 13.18. The mean square between the soccer
teams is exactly `103/12`, strictly between `8.58` and `8.59`. -/
@[kb "openstaxintrostats2e" "Exercise 13.18, p. 709"]
theorem ex_13_18_soccer_ms_between :
    msBetween sx sg = 103 / 12 ∧ 8.58 < msBetween sx sg ∧ msBetween sx sg < 8.59 := by
  rw [s_msb]; refine ⟨rfl, ?_, ?_⟩ <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 13.19. The sum of squares within the soccer
teams is exactly `66/5 = 13.2`. -/
@[kb "openstaxintrostats2e" "Exercise 13.19, p. 709"]
theorem ex_13_19_soccer_ss_within : ssWithin sx sg = 66 / 5 := s_ssw

/-- OpenStax Introductory Statistics 2e Practice exercise 13.20. With `20` observations in `4` teams the
denominator degrees of freedom are `20 - 4 = 16`. -/
@[kb "openstaxintrostats2e" "Exercise 13.20, p. 709"]
theorem ex_13_20_soccer_df_denominator : (20 : ℕ) - 4 = 16 := rfl

/-- OpenStax Introductory Statistics 2e Practice exercise 13.21. The mean square within the soccer teams
is exactly `33/40 = 0.825`. -/
@[kb "openstaxintrostats2e" "Exercise 13.21, p. 709"]
theorem ex_13_21_soccer_ms_within : msWithin sx sg = 33 / 40 ∧ msWithin sx sg = 0.825 := by
  rw [s_msw]; constructor <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 13.22. The `F` statistic of the soccer data is
exactly `1030/99`, strictly between `10.40` and `10.41`. -/
@[kb "openstaxintrostats2e" "Exercise 13.22, p. 710"]
theorem ex_13_22_soccer_f_statistic :
    fStatistic sx sg = 1030 / 99 ∧ 10.40 < fStatistic sx sg ∧ fStatistic sx sg < 10.41 := by
  rw [s_f]; refine ⟨rfl, ?_, ?_⟩ <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 13.23. The `F` statistic `1030/99 ≈ 10.40` of
the soccer data is far above the standard table critical value `3.24` for `3` and `16` degrees of
freedom at the 5% level (a table value, not proved), so a rejection of equal mean goals per game is
likely. -/
@[kb "openstaxintrostats2e" "Exercise 13.23, p. 710"]
theorem ex_13_23_soccer_likely_reject :
    (let fCrit : ℝ := 3.24; fCrit < fStatistic sx sg) := by
  show (3.24 : ℝ) < _
  rw [s_f]; norm_num

/-! ### Section 13.3: jump heights of five basketball teams (Table 13.15) -/

/-- The fifteen jump heights of Table 13.15 (team 1, then teams 2 to 5). -/
noncomputable def jx : Fin 15 → ℝ :=
  ![36, 42, 51, 32, 35, 38, 48, 50, 39, 38, 44, 46, 41, 39, 40]

/-- The team of each jump height of Table 13.15. -/
def jg : Fin 15 → Fin 5 := ![0, 0, 0, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4, 4]

private lemma j_size : ∀ j, groupSize jg j = (![3, 3, 3, 3, 3] : Fin 5 → ℕ) j := by
  intro j; fin_cases j <;> decide

private lemma j_ssb : ssBetween jx jg = 978 / 5 := by
  simp only [ssBetween, groupMean, j_size, Finset.sum_filter]
  simp [mean, jx, jg, Finset.sum_filter, Fin.sum_univ_succ]
  norm_num

private lemma j_ssw : ssWithin jx jg = 712 / 3 := by
  simp only [ssWithin, groupMean, j_size, Finset.sum_filter]
  simp [jx, jg, Finset.sum_filter, Fin.sum_univ_succ]
  norm_num

private lemma j_msb : msBetween jx jg = 489 / 10 := by rw [msBetween, j_ssb]; norm_num

private lemma j_msw : msWithin jx jg = 356 / 15 := by rw [msWithin, j_ssw]; norm_num

private lemma j_f : fStatistic jx jg = 1467 / 712 := by
  rw [fStatistic, j_msb, j_msw]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 13.26. With `5` teams the numerator degrees of
freedom are `5 - 1 = 4`. -/
@[kb "openstaxintrostats2e" "Exercise 13.26, p. 710"]
theorem ex_13_26_jump_df_numerator : (5 : ℕ) - 1 = 4 := rfl

/-- OpenStax Introductory Statistics 2e Practice exercise 13.27. With `15` observations in `5` teams the
denominator degrees of freedom are `15 - 5 = 10`. -/
@[kb "openstaxintrostats2e" "Exercise 13.27, p. 710"]
theorem ex_13_27_jump_df_denominator : (15 : ℕ) - 5 = 10 := rfl

/-- OpenStax Introductory Statistics 2e Practice exercise 13.28. For the jump heights the sum of squares
between the teams (factor) is exactly `978/5 = 195.6` and the mean square factor exactly `489/10 = 48.9`. -/
@[kb "openstaxintrostats2e" "Exercise 13.28, p. 710"]
theorem ex_13_28_jump_factor_squares :
    ssBetween jx jg = 978 / 5 ∧ msBetween jx jg = 489 / 10 := ⟨j_ssb, j_msb⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 13.29. For the jump heights the sum of squares
of error is exactly `712/3` (strictly between `237.33` and `237.34`) and the mean square error exactly
`356/15` (strictly between `23.73` and `23.74`). -/
@[kb "openstaxintrostats2e" "Exercise 13.29, p. 710"]
theorem ex_13_29_jump_error_squares :
    ssWithin jx jg = 712 / 3 ∧ 237.33 < ssWithin jx jg ∧ ssWithin jx jg < 237.34 ∧
      msWithin jx jg = 356 / 15 ∧ 23.73 < msWithin jx jg ∧ msWithin jx jg < 23.74 := by
  rw [j_ssw, j_msw]; refine ⟨rfl, ?_, ?_, rfl, ?_, ?_⟩ <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 13.30. The `F` statistic of the jump heights is
exactly `1467/712`, strictly between `2.0603` and `2.0604`. -/
@[kb "openstaxintrostats2e" "Exercise 13.30, p. 710"]
theorem ex_13_30_jump_f_statistic :
    fStatistic jx jg = 1467 / 712 ∧ 2.0603 < fStatistic jx jg ∧ fStatistic jx jg < 2.0604 := by
  rw [j_f]; refine ⟨rfl, ?_, ?_⟩ <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 13.32. The `F` statistic of the jump heights
(`≈ 2.06`) is below the standard table critical value `3.48` for `4` and `10` degrees of freedom at the
5% level (a table value, not proved), so no difference in mean jump heights among the teams is
established. -/
@[kb "openstaxintrostats2e" "Exercise 13.32, p. 710"]
theorem ex_13_32_jump_no_difference :
    (let fCrit : ℝ := 3.48; fStatistic jx jg < fCrit) := by
  show _ < (3.48 : ℝ)
  rw [j_f]; norm_num

/-! ### Section 13.3: scores of three groups for a video game (Table 13.16) -/

/-- The fifteen scores of Table 13.16 (group A, then groups B and C). -/
noncomputable def vx : Fin 15 → ℝ :=
  ![101, 108, 98, 107, 111, 151, 149, 160, 112, 126, 101, 109, 198, 186, 160]

/-- The group of each score of Table 13.16. -/
def vg : Fin 15 → Fin 3 := ![0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2]

private lemma v_size : ∀ j, groupSize vg j = (![5, 5, 5] : Fin 3 → ℕ) j := by
  intro j; fin_cases j <;> decide

private lemma v_ssb : ssBetween vx vg = 28502 / 5 := by
  simp only [ssBetween, groupMean, v_size, Finset.sum_filter]
  simp [mean, vx, vg, Finset.sum_filter, Fin.sum_univ_succ]
  norm_num

private lemma v_ssw : ssWithin vx vg = 9474 := by
  simp only [ssWithin, groupMean, v_size, Finset.sum_filter]
  simp [vx, vg, Finset.sum_filter, Fin.sum_univ_succ]
  norm_num

private lemma v_msb : msBetween vx vg = 14251 / 5 := by rw [msBetween, v_ssb]; norm_num

private lemma v_msw : msWithin vx vg = 1579 / 2 := by rw [msWithin, v_ssw]; norm_num

private lemma v_f : fStatistic vx vg = 28502 / 7895 := by
  rw [fStatistic, v_msb, v_msw]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 13.33. With `3` groups the numerator degrees of
freedom are `3 - 1 = 2`. -/
@[kb "openstaxintrostats2e" "Exercise 13.33, p. 710"]
theorem ex_13_33_video_df_numerator : (3 : ℕ) - 1 = 2 := rfl

/-- OpenStax Introductory Statistics 2e Practice exercise 13.34. With `15` scores in `3` groups the
denominator degrees of freedom are `15 - 3 = 12`. -/
@[kb "openstaxintrostats2e" "Exercise 13.34, p. 710"]
theorem ex_13_34_video_df_denominator : (15 : ℕ) - 3 = 12 := rfl

/-- OpenStax Introductory Statistics 2e Practice exercise 13.35. The sum of squares between the three
video-game groups is exactly `28502/5 = 5700.4` and the mean square between exactly `14251/5 = 2850.2`. -/
@[kb "openstaxintrostats2e" "Exercise 13.35, p. 710"]
theorem ex_13_35_video_between :
    ssBetween vx vg = 28502 / 5 ∧ msBetween vx vg = 14251 / 5 := ⟨v_ssb, v_msb⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 13.36. The sum of squares within the groups is
exactly `9474` and the mean square within exactly `1579/2 = 789.5`. -/
@[kb "openstaxintrostats2e" "Exercise 13.36, p. 710"]
theorem ex_13_36_video_within :
    ssWithin vx vg = 9474 ∧ msWithin vx vg = 1579 / 2 := ⟨v_ssw, v_msw⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 13.37. The `F` statistic of the video-game scores
is exactly `28502/7895`, strictly between `3.6101` and `3.6102`. -/
@[kb "openstaxintrostats2e" "Exercise 13.37, p. 710"]
theorem ex_13_37_video_f_statistic :
    fStatistic vx vg = 28502 / 7895 ∧ 3.6101 < fStatistic vx vg ∧ fStatistic vx vg < 3.6102 := by
  rw [v_f]; refine ⟨rfl, ?_, ?_⟩ <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 13.39. The `F` statistic `≈ 3.61` of the
video-game scores exceeds the standard table critical value `2.81` for `2` and `12` degrees of freedom at
the 10% level (a table value, not proved), so at the 10% level the mean scores of the groups differ. -/
@[kb "openstaxintrostats2e" "Exercise 13.39, p. 711"]
theorem ex_13_39_video_reject :
    (let fCrit : ℝ := 2.81; fCrit < fStatistic vx vg) := by
  show (2.81 : ℝ) < _
  rw [v_f]; norm_num

/-! ### Section 13.3: ages at which teenagers get a driver's licence (Table 13.17) -/

/-- The twenty ages of Table 13.17 (Northeast, South, West, Central, East). -/
noncomputable def dx : Fin 20 → ℝ :=
  ![16.3, 16.1, 16.4, 16.5, 16.9, 16.5, 16.4, 16.2, 16.4, 16.5, 16.6, 16.1, 16.2, 16.6, 16.5, 16.4,
    17.1, 17.2, 16.6, 16.8]

/-- The region of each age of Table 13.17. -/
def dg : Fin 20 → Fin 5 := ![0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4]

private lemma d_size : ∀ j, groupSize dg j = (![4, 4, 4, 4, 4] : Fin 5 → ℕ) j := by
  intro j; fin_cases j <;> decide

private lemma d_ssb : ssBetween dx dg = 903 / 1000 := by
  simp only [ssBetween, groupMean, d_size, Finset.sum_filter]
  simp [mean, dx, dg, Finset.sum_filter, Fin.sum_univ_succ]
  norm_num

private lemma d_ssw : ssWithin dx dg = 321 / 400 := by
  simp only [ssWithin, groupMean, d_size, Finset.sum_filter]
  simp [dx, dg, Finset.sum_filter, Fin.sum_univ_succ]
  norm_num

private lemma d_msb : msBetween dx dg = 903 / 4000 := by rw [msBetween, d_ssb]; norm_num

private lemma d_msw : msWithin dx dg = 107 / 2000 := by rw [msWithin, d_ssw]; norm_num

private lemma d_f : fStatistic dx dg = 903 / 214 := by
  rw [fStatistic, d_msb, d_msw]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 13.40. The ANOVA table of the driver's-licence
ages: `SS(between) = 903/1000` with `5 - 1 = 4` degrees of freedom, `SS(within) = 321/400` with
`20 - 5 = 15`, mean squares `903/4000` and `107/2000`, and `F = 903/214`, strictly between `4.2196` and
`4.2197`. The p-value itself is not computable here (it is the `F` tail beyond this value). -/
@[kb "openstaxintrostats2e" "Exercise 13.40, p. 711"]
theorem ex_13_40_licence_anova_table :
    ssBetween dx dg = 903 / 1000 ∧ ssWithin dx dg = 321 / 400 ∧ msBetween dx dg = 903 / 4000 ∧
      msWithin dx dg = 107 / 2000 ∧ fStatistic dx dg = 903 / 214 ∧
      4.2196 < fStatistic dx dg ∧ fStatistic dx dg < 4.2197 ∧ (5 : ℕ) - 1 = 4 ∧ (20 : ℕ) - 5 = 15 := by
  rw [d_f]
  exact ⟨d_ssb, d_ssw, d_msb, d_msw, rfl, by norm_num, by norm_num, rfl, rfl⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 13.41. At the 5% level the standard table
critical value for `4` and `15` degrees of freedom is `3.06` (a table value, not proved); the `F`
statistic `903/214 ≈ 4.22` of the licence ages exceeds it, so the decision is to reject the null
hypothesis of equal mean ages. -/
@[kb "openstaxintrostats2e" "Exercise 13.41, p. 711"]
theorem ex_13_41_licence_reject_at_5_percent :
    (let fCrit : ℝ := 3.06; fCrit < fStatistic dx dg) := by
  show (3.06 : ℝ) < _
  rw [d_f]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 13.42. At the 1% level the standard table
critical value for `4` and `15` degrees of freedom is `4.89` (a table value, not proved); the `F`
statistic `903/214 ≈ 4.22` of the licence ages is below it, so the decision is not to reject the null
hypothesis of equal mean ages. -/
@[kb "openstaxintrostats2e" "Exercise 13.42, p. 711"]
theorem ex_13_42_licence_no_reject_at_1_percent :
    (let fCrit : ℝ := 4.89; fStatistic dx dg < fCrit) := by
  show _ < (4.89 : ℝ)
  rw [d_f]; norm_num

/-! ### Section 13.4: tests of two variances -/

/-- OpenStax Introductory Statistics 2e Practice exercise 13.46. The first commuter's variance is
`12.1`, so the standard deviation `s₁ = √12.1` lies strictly between `3.478` and `3.479`. -/
@[kb "openstaxintrostats2e" "Exercise 13.46, p. 711"]
theorem ex_13_46_commute_s1 : 3.478 < Real.sqrt 12.1 ∧ Real.sqrt 12.1 < 3.479 :=
  ⟨(Real.lt_sqrt (by norm_num)).2 (by norm_num), (Real.sqrt_lt' (by norm_num)).2 (by norm_num)⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 13.47. The second commuter's variance is
`16.9`, so the standard deviation `s₂ = √16.9` lies strictly between `4.110` and `4.111`. -/
@[kb "openstaxintrostats2e" "Exercise 13.47, p. 711"]
theorem ex_13_47_commute_s2 : 4.110 < Real.sqrt 16.9 ∧ Real.sqrt 16.9 < 4.111 :=
  ⟨(Real.lt_sqrt (by norm_num)).2 (by norm_num), (Real.sqrt_lt' (by norm_num)).2 (by norm_num)⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 13.48. Each commuter recorded `n = 20`
trips, so each sample variance has `20 - 1 = 19` degrees of freedom. -/
@[kb "openstaxintrostats2e" "Exercise 13.48, p. 711"]
theorem ex_13_48_commute_sample_size : (20 : ℕ) - 1 = 19 := rfl

/-- OpenStax Introductory Statistics 2e Practice exercise 13.49. The `F` statistic of the commute times,
the ratio of the variances `12.1 / 16.9 = 121/169`, lies strictly between `0.7159` and `0.7160`. -/
@[kb "openstaxintrostats2e" "Exercise 13.49, p. 711"]
theorem ex_13_49_commute_f_statistic :
    (12.1 : ℝ) / 16.9 = 121 / 169 ∧ 0.7159 < (12.1 : ℝ) / 16.9 ∧ (12.1 : ℝ) / 16.9 < 0.7160 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 13.51. The claim is that the first worker's
variance is smaller, a left-tailed test at the 10% level. The left critical value is the reciprocal of
the upper 10% table value for `19` and `19` degrees of freedom; the table value `1.79` (for `20`, `20`
degrees of freedom, slightly smaller than the one needed, a table value not proved) already gives the
cutoff `1/1.79 ≈ 0.559`, below the statistic `121/169 ≈ 0.716`, so the null hypothesis is not rejected
and the claim is not supported. -/
@[kb "openstaxintrostats2e" "Exercise 13.51, p. 712"]
theorem ex_13_51_commute_claim_not_supported :
    (let fUpper : ℝ := 1.79; 1 / fUpper < (12.1 : ℝ) / 16.9) := by
  show 1 / (1.79 : ℝ) < _
  norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 13.53. The `F` statistic of the math scores
(standard deviations `38.1` and `22.5`, the larger variance on top) is `38.1² / 22.5² = 16129/5625`,
strictly between `2.8673` and `2.8674`. -/
@[kb "openstaxintrostats2e" "Exercise 13.53, p. 712"]
theorem ex_13_53_math_f_statistic :
    (38.1 : ℝ) ^ 2 / 22.5 ^ 2 = 16129 / 5625 ∧ 2.8673 < (38.1 : ℝ) ^ 2 / 22.5 ^ 2 ∧
      (38.1 : ℝ) ^ 2 / 22.5 ^ 2 < 2.8674 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 13.55. There are `15` tests per student, so
`14` and `14` degrees of freedom. The statistic `≈ 2.867` exceeds the upper 5% table value for `12` and
`12` degrees of freedom, `2.69` (a table value, not proved; the value for `14` and `14` is smaller), so
the null hypothesis of equal variances is rejected in favour of a larger variance for the first student. -/
@[kb "openstaxintrostats2e" "Exercise 13.55, p. 712"]
theorem ex_13_55_math_reject :
    (15 : ℕ) - 1 = 14 ∧ (let fCrit : ℝ := 2.69; fCrit < (38.1 : ℝ) ^ 2 / 22.5 ^ 2) := by
  refine ⟨rfl, ?_⟩
  show (2.69 : ℝ) < _
  norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 13.57. The `F` statistic of the cyclists'
pace variances `23.8` and `32.1` is `23.8 / 32.1 = 238/321`, strictly between `0.7414` and `0.7415`
(with `35 - 1 = 34` degrees of freedom each). -/
@[kb "openstaxintrostats2e" "Exercise 13.57, p. 712"]
theorem ex_13_57_cyclist_f_statistic :
    (35 : ℕ) - 1 = 34 ∧ (23.8 : ℝ) / 32.1 = 238 / 321 ∧ 0.7414 < (23.8 : ℝ) / 32.1 ∧
      (23.8 : ℝ) / 32.1 < 0.7415 := by
  refine ⟨rfl, by norm_num, by norm_num, by norm_num⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 13.58. A two-sided test at the 5% level uses
the upper `2.5%` table value for `34` and `34` degrees of freedom, which is at least the value `1.88`
for `40` and `40` degrees (a table value, not proved). The statistic `238/321 ≈ 0.741` lies between the
cutoffs `1/1.88 ≈ 0.532` and `1.88` (and the true cutoffs are even wider), so the hypothesis that the
variances are equal is not rejected. -/
@[kb "openstaxintrostats2e" "Exercise 13.58, p. 712"]
theorem ex_13_58_cyclist_variances_not_different :
    (let fUpper : ℝ := 1.88; 1 / fUpper < (23.8 : ℝ) / 32.1 ∧ (23.8 : ℝ) / 32.1 < fUpper) := by
  show 1 / (1.88 : ℝ) < _ ∧ _ < (1.88 : ℝ)
  constructor <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 13.50 (arithmetic of the commute test). The
degrees of freedom are `19` and `19`; the observed `F = 121/169` is below `1`, the left-tail side of the
distribution, where a left-tailed test looks for evidence for the first worker's smaller variance. -/
@[kb "openstaxintrostats2e" "Exercise 13.50, p. 712"]
theorem ex_13_50_commute_f_below_one : (12.1 : ℝ) / 16.9 < 1 := by norm_num

end UndergradKB.Statistics.Course.PracticeC13
