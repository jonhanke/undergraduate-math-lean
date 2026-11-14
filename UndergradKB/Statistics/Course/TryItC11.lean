import Mathlib.Data.Fin.VecNotation
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Data
import UndergradKB.Statistics.Course.ExamplesC11C13

/-!
# "Try It" exercises, chapter 11 (OpenStax *Introductory Statistics 2e*): the chi-square distribution

Chi-square statistics, degrees of freedom and expected counts for the data of the Try It exercises
of chapter 11, computed with the definitions `chiSquareStat`, `tableExpected` and `tableChiSquare` of
`ExamplesC11C13`. The chi-square critical values used for decisions are values of a standard table (the book links to external tables)
(quoted, not proved).
-/

namespace UndergradKB.Statistics.Course.TryItC11

open UndergradKB.Statistics UndergradKB.Statistics.Course.ExamplesC11C13

/-! ### Section 11.2: goodness of fit -/

/-- OpenStax Introductory Statistics 2e Try It 11.1. The expected numbers of defects are
`5, 6, 7, 8, 10` for the five production ranges and the observed ones `5, 7, 8, 9, 11`. The
goodness-of-fit statistic is exactly `449/840`, strictly between `0.5345` and `0.5346`, with
`5 - 1 = 4` degrees of freedom. -/
@[kb "openstaxintrostats2e" "Try It 11.1, p. 579"]
theorem tryit_11_1_defects :
    chiSquareStat (![5, 7, 8, 9, 11] : Fin 5 → ℝ) ![5, 6, 7, 8, 10] = 449 / 840 ∧
      0.5345 < chiSquareStat (![5, 7, 8, 9, 11] : Fin 5 → ℝ) ![5, 6, 7, 8, 10] ∧
      chiSquareStat (![5, 7, 8, 9, 11] : Fin 5 → ℝ) ![5, 6, 7, 8, 10] < 0.5346 ∧
      Fintype.card (Fin 5) - 1 = 4 := by
  have h : chiSquareStat (![5, 7, 8, 9, 11] : Fin 5 → ℝ) ![5, 6, 7, 8, 10] = 449 / 840 := by
    simp [chiSquareStat, Fin.sum_univ_succ]
    norm_num
  rw [h]
  refine ⟨rfl, by norm_num, by norm_num, rfl⟩

/-- OpenStax Introductory Statistics 2e Try It 11.2. Fifty-six students name their main homework
night (`11, 8, 10, 7, 10, 5, 5` from Sunday to Saturday); equal frequency means `56/7 = 8` expected
per night. The goodness-of-fit statistic is exactly `9/2` with `7 - 1 = 6` degrees of freedom (the
test is a goodness-of-fit test against the uniform distribution). -/
@[kb "openstaxintrostats2e" "Try It 11.2, p. 581"]
theorem tryit_11_2_homework_nights :
    (∑ i, (![11, 8, 10, 7, 10, 5, 5] : Fin 7 → ℝ) i) = 56 ∧ (56 : ℝ) / 7 = 8 ∧
      chiSquareStat (![11, 8, 10, 7, 10, 5, 5] : Fin 7 → ℝ) (fun _ => 8) = 9 / 2 ∧
      Fintype.card (Fin 7) - 1 = 6 := by
  refine ⟨?_, by norm_num, ?_, rfl⟩
  · simp [Fin.sum_univ_succ]; norm_num
  · simp [chiSquareStat, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Try It 11.3. A sample of `1000` students has pet counts
`210, 240, 320, 140, 90`; the national percentages `18, 25, 30, 18, 9` give expected counts
`180, 250, 300, 180, 90`, which add up to `1000`. The goodness-of-fit statistic is exactly `703/45`,
strictly between `15.62` and `15.63`, on `5 - 1 = 4` degrees of freedom. It exceeds the standard table
value `13.277` for level `1%` (a table value, not proved): reject. -/
@[kb "openstaxintrostats2e" "Try It 11.3, p. 584"]
theorem tryit_11_3_pets :
    (fun i : Fin 5 => 1000 * (![0.18, 0.25, 0.30, 0.18, 0.09] : Fin 5 → ℝ) i) = ![180, 250, 300, 180, 90] ∧
      (∑ i, (![210, 240, 320, 140, 90] : Fin 5 → ℝ) i) = 1000 ∧
      chiSquareStat (![210, 240, 320, 140, 90] : Fin 5 → ℝ) ![180, 250, 300, 180, 90] = 703 / 45 ∧
      (15.62 < chiSquareStat (![210, 240, 320, 140, 90] : Fin 5 → ℝ) ![180, 250, 300, 180, 90] ∧
        chiSquareStat (![210, 240, 320, 140, 90] : Fin 5 → ℝ) ![180, 250, 300, 180, 90] < 15.63) ∧
      Fintype.card (Fin 5) - 1 = 4 ∧
      (13.277 : ℝ) < chiSquareStat (![210, 240, 320, 140, 90] : Fin 5 → ℝ) ![180, 250, 300, 180, 90] := by
  have h : chiSquareStat (![210, 240, 320, 140, 90] : Fin 5 → ℝ) ![180, 250, 300, 180, 90] = 703 / 45 := by
    simp [chiSquareStat, Fin.sum_univ_succ]
    norm_num
  rw [h]
  refine ⟨?_, ?_, rfl, ⟨by norm_num, by norm_num⟩, rfl, by norm_num⟩
  · funext i
    fin_cases i <;> simp <;> norm_num
  · simp [Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Try It 11.4. For the ten regional literacy rates
`99.0, 99.5, 67.3, 62.5, 91.0, 93.8, 61.9, 91.9, 84.5, 66.4` against the hypothesised `82` everywhere,
the test statistic `∑ (O - 82)²/82` is exactly `108173/4100`, strictly between `26.38` and `26.39`, with
`10 - 1 = 9` degrees of freedom. -/
@[kb "openstaxintrostats2e" "Try It 11.4, p. 586"]
theorem tryit_11_4_literacy :
    chiSquareStat (![99.0, 99.5, 67.3, 62.5, 91.0, 93.8, 61.9, 91.9, 84.5, 66.4] : Fin 10 → ℝ)
        (fun _ => 82) = 108173 / 4100 ∧
      (26.38 < chiSquareStat (![99.0, 99.5, 67.3, 62.5, 91.0, 93.8, 61.9, 91.9, 84.5, 66.4] : Fin 10 → ℝ)
          (fun _ => 82) ∧
        chiSquareStat (![99.0, 99.5, 67.3, 62.5, 91.0, 93.8, 61.9, 91.9, 84.5, 66.4] : Fin 10 → ℝ)
          (fun _ => 82) < 26.39) ∧
      Fintype.card (Fin 10) - 1 = 9 := by
  have h : chiSquareStat (![99.0, 99.5, 67.3, 62.5, 91.0, 93.8, 61.9, 91.9, 84.5, 66.4] : Fin 10 → ℝ)
      (fun _ => 82) = 108173 / 4100 := by
    simp [chiSquareStat, Fin.sum_univ_succ]
    norm_num
  rw [h]
  refine ⟨rfl, ⟨by norm_num, by norm_num⟩, rfl⟩

/-! ### Section 11.3: test of independence -/

/-- OpenStax Introductory Statistics 2e Try It 11.5. Of `300` students, `50` are music students and
`97` are on the honor roll; under independence the expected number of music students on the honor roll
is `50 · 97 / 300 = 97/6`, strictly between `16.16` and `16.17` (about `16`). -/
@[kb "openstaxintrostats2e" "Try It 11.5, p. 587"]
theorem tryit_11_5_music_honor_roll :
    (50 : ℝ) * 97 / 300 = 97 / 6 ∧ 16.16 < (50 : ℝ) * 97 / 300 ∧ (50 : ℝ) * 97 / 300 < 16.17 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- Observed table of Try It 11.6 (rows: seven industry sectors; columns: the years 2000, 2010, 2020;
thousands of jobs). -/
noncomputable def jobsTable : Fin 7 → Fin 3 → ℝ :=
  ![![13243, 13044, 15018], ![2457, 1771, 1950], ![10786, 11273, 13068], ![240, 214, 201],
    ![931, 894, 972], ![14, 11, 11], ![196, 144, 152]]

/-- OpenStax Introductory Statistics 2e Try It 11.6. The row totals of the jobs table are
`41305, 6178, 35127, 655, 2797, 36, 492`, the column totals `27867, 27351, 31372`, and the grand total
`86590`, as printed; the independence test has `(7 - 1)(3 - 1) = 12` degrees of freedom. The
chi-square statistic of independence lies strictly between `227.72` and `227.73`. -/
@[kb "openstaxintrostats2e" "Try It 11.6, p. 589"]
theorem tryit_11_6_jobs_independence :
    (∀ i : Fin 7, ∑ j, jobsTable i j = ![41305, 6178, 35127, 655, 2797, 36, 492] i) ∧
      (∀ j : Fin 3, ∑ i, jobsTable i j = ![27867, 27351, 31372] j) ∧
      (∑ i, ∑ j, jobsTable i j) = 86590 ∧
      (Fintype.card (Fin 7) - 1) * (Fintype.card (Fin 3) - 1) = 12 ∧
      227.72 < tableChiSquare jobsTable ∧ tableChiSquare jobsTable < 227.73 := by
  refine ⟨?_, ?_, ?_, rfl, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [jobsTable, Fin.sum_univ_succ] <;> norm_num
  · intro j
    fin_cases j <;> simp [jobsTable, Fin.sum_univ_succ] <;> norm_num
  · simp [jobsTable, Fin.sum_univ_succ]; norm_num
  · simp [tableChiSquare, tableExpected, jobsTable, Fin.sum_univ_succ]; norm_num
  · simp [tableChiSquare, tableExpected, jobsTable, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Try It 11.7. For the jobs table of Try It 11.6 the expected
number of services-providing jobs in 2020 is `35127 · 31372 / 86590 = 551002122/43295`, strictly between
`12726.69` and `12726.70`, and of nonagriculture wage and salary jobs `41305 · 31372 / 86590 =
129582046/8659`, strictly between `14965.01` and `14965.02` (thousands). -/
@[kb "openstaxintrostats2e" "Try It 11.7, p. 590"]
theorem tryit_11_7_expected_jobs_2020 :
    tableExpected jobsTable 2 2 = 551002122 / 43295 ∧
      (12726.69 < tableExpected jobsTable 2 2 ∧ tableExpected jobsTable 2 2 < 12726.70) ∧
      tableExpected jobsTable 0 2 = 129582046 / 8659 ∧
      (14965.01 < tableExpected jobsTable 0 2 ∧ tableExpected jobsTable 0 2 < 14965.02) := by
  have h1 : tableExpected jobsTable 2 2 = 551002122 / 43295 := by
    simp [tableExpected, jobsTable, Fin.sum_univ_succ]; norm_num
  have h2 : tableExpected jobsTable 0 2 = 129582046 / 8659 := by
    simp [tableExpected, jobsTable, Fin.sum_univ_succ]; norm_num
  rw [h1, h2]
  refine ⟨rfl, ⟨by norm_num, by norm_num⟩, rfl, ⟨by norm_num, by norm_num⟩⟩

/-! ### Section 11.4: test for homogeneity -/

/-- Observed table of Try It 11.8 (rows: families, singles; columns: sport, sedan, hatchback, truck,
van/SUV). -/
noncomputable def carsTable : Fin 2 → Fin 5 → ℝ :=
  ![![5, 15, 35, 17, 28], ![45, 65, 37, 46, 7]]

/-- OpenStax Introductory Statistics 2e Try It 11.8. For `100` families and `200` singles the
homogeneity statistic is exactly `70461/1120`, strictly between `62.91` and `62.92`, on
`5 - 1 = 4` degrees of freedom. It exceeds the standard table value `9.488` for level `0.05` (a table
value, not proved): reject, the distributions of cars differ. -/
@[kb "openstaxintrostats2e" "Try It 11.8, p. 592"]
theorem tryit_11_8_cars :
    (∑ i, ∑ j, carsTable i j) = 300 ∧ tableChiSquare carsTable = 70461 / 1120 ∧
      (62.91 < tableChiSquare carsTable ∧ tableChiSquare carsTable < 62.92) ∧
      Fintype.card (Fin 5) - 1 = 4 ∧ (9.488 : ℝ) < tableChiSquare carsTable := by
  have h : tableChiSquare carsTable = 70461 / 1120 := by
    simp [tableChiSquare, tableExpected, carsTable, Fin.sum_univ_succ]
    norm_num
  rw [h]
  refine ⟨?_, rfl, ⟨by norm_num, by norm_num⟩, rfl, by norm_num⟩
  simp [carsTable, Fin.sum_univ_succ]; norm_num

/-- Observed table of Try It 11.9 (rows: regular, early-decision acceptances; columns: Brown,
Columbia, Cornell, Dartmouth, Penn, Yale). -/
noncomputable def ivyTable : Fin 2 → Fin 6 → ℝ :=
  ![![2115, 1792, 5306, 1734, 2685, 1245], ![577, 627, 1228, 444, 1195, 761]]

/-- OpenStax Introductory Statistics 2e Try It 11.9. The two rows of acceptances have totals `14877`
and `4832` (grand total `19709`). The homogeneity statistic lies strictly between `430.06` and
`430.07`, on `6 - 1 = 5` degrees of freedom. It exceeds the standard table value `11.070` for level
`0.05` (a table value, not proved): reject, the two distributions differ. -/
@[kb "openstaxintrostats2e" "Try It 11.9, p. 593"]
theorem tryit_11_9_ivy_league :
    (∑ j, ivyTable 0 j) = 14877 ∧ (∑ j, ivyTable 1 j) = 4832 ∧
      430.06 < tableChiSquare ivyTable ∧ tableChiSquare ivyTable < 430.07 ∧
      Fintype.card (Fin 6) - 1 = 5 ∧ (11.070 : ℝ) < tableChiSquare ivyTable := by
  have h : tableChiSquare ivyTable = 2169129355442782164839483 / 5043743569001294353152 := by
    simp [tableChiSquare, tableExpected, ivyTable, Fin.sum_univ_succ]
    norm_num
  rw [h]
  refine ⟨?_, ?_, by norm_num, by norm_num, rfl, by norm_num⟩
  · simp [ivyTable, Fin.sum_univ_succ]; norm_num
  · simp [ivyTable, Fin.sum_univ_succ]; norm_num

/-! ### Section 11.6: test of a single variance -/

/-- OpenStax Introductory Statistics 2e Try It 11.11. Fifteen providers have sample standard deviation
`13.2` against the reported `12.2`: the statistic `(n - 1) s² / σ² = 14 · 13.2² / 12.2² = 60984/3721`
lies strictly between `16.38` and `16.39`, with `15 - 1 = 14` degrees of freedom. It is below a
standard right-tail table value `29.141` for level `1%` (a table value, not proved): do not reject. -/
@[kb "openstaxintrostats2e" "Try It 11.11, p. 596"]
theorem tryit_11_11_internet_speed_variance :
    ((15 : ℝ) - 1) * 13.2 ^ 2 / 12.2 ^ 2 = 60984 / 3721 ∧ 16.38 < ((15 : ℝ) - 1) * 13.2 ^ 2 / 12.2 ^ 2 ∧
      ((15 : ℝ) - 1) * 13.2 ^ 2 / 12.2 ^ 2 < 16.39 ∧ 15 - 1 = 14 ∧
      ((15 : ℝ) - 1) * 13.2 ^ 2 / 12.2 ^ 2 < 29.141 := by
  refine ⟨by norm_num, by norm_num, by norm_num, rfl, by norm_num⟩

end UndergradKB.Statistics.Course.TryItC11
