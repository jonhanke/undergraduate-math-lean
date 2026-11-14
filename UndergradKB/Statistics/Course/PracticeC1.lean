import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.Count
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Data

/-!
# Practice exercises, chapter 1 (OpenStax *Introductory Statistics 2e*): sampling and data

The numerical content of the chapter 1 Practice exercises: the sample means of the two researchers' recovery
times, the frequency tables built from those data, the earthquake-death proportions of Table 1.27, the
relative and cumulative relative frequencies of the video-game tables, and the improvement rates of the two
software studies. The verbal exercises (key terms, kinds of data, sampling methods, reasons data differ,
experimental design, ethics, levels of measurement) have no mathematical statement and are not formalised.
-/

namespace UndergradKB.Statistics.Course.PracticeC1

open UndergradKB.Statistics Finset

/-- Researcher A's recovery times in days (40 patients). -/
private def resA : List ℕ :=
  [3, 4, 11, 15, 16, 17, 22, 44, 37, 16, 14, 24, 25, 15, 26, 27, 33, 29, 35, 44, 13, 21, 22, 10, 12, 8, 40,
    32, 26, 27, 31, 34, 29, 17, 8, 24, 18, 47, 33, 34]

/-- Researcher B's recovery times in days (40 patients). -/
private def resB : List ℕ :=
  [3, 14, 11, 5, 16, 17, 28, 41, 31, 18, 14, 14, 26, 25, 21, 22, 31, 2, 35, 44, 23, 21, 21, 16, 12, 18, 41,
    22, 16, 25, 33, 34, 29, 13, 18, 24, 23, 42, 33, 29]

/-- Number of entries of an integer list lying between `a` and `b` inclusive (the classes of the book,
with half-integer boundaries, contain exactly the integers from `a` to `b`). -/
private def classCount (l : List ℕ) (a b : ℕ) : ℕ := l.countP (fun x => decide (a ≤ x ∧ x ≤ b))

/-- OpenStax Introductory Statistics 2e Practice exercise 1.4. The statistic of the study of researcher A is
the sample mean of his 40 recovery times: the times add to 943 days, so the mean is 943/40 = 23.575 days
(the mean of researcher B's 40 times is 911/40 = 22.775 days). -/
@[kb "openstaxintrostats2e" "Exercise 1.4, p. 57"]
theorem ex_1_4_sample_means :
    (resA.length = 40 ∧ resA.sum = 943 ∧ ((resA.sum : ℚ) / resA.length = 23.575)) ∧
      (resB.length = 40 ∧ resB.sum = 911 ∧ ((resB.sum : ℚ) / resB.length = 22.775)) := by
  refine ⟨⟨by rfl, by rfl, ?_⟩, ⟨by rfl, by rfl, ?_⟩⟩
  · have h1 : resA.sum = 943 := by rfl
    have h2 : resA.length = 40 := by rfl
    rw [h1, h2]; norm_num
  · have h1 : resB.sum = 911 := by rfl
    have h2 : resB.length = 40 := by rfl
    rw [h1, h2]; norm_num

/-- Table 1.27: deaths by earthquakes in years 1 to 13. -/
private def deaths : Fin 13 → ℕ :=
  ![231, 21357, 11685, 33819, 228802, 88003, 6605, 712, 88011, 1790, 320120, 21953, 768]

/-- OpenStax Introductory Statistics 2e Practice exercise 1.11 (total and part a). The thirteen yearly death
counts of Table 1.27 add to the printed total 823,856. Reading "between year 8 and year 13" as the years
strictly between them, years 9 to 12 account for 431,874 deaths, a proportion of 431874/823856, strictly
between 0.5242 and 0.5243 (the book's 0.5242). -/
@[kb "openstaxintrostats2e" "Exercise 1.11, p. 58"]
theorem ex_1_11_a_proportion_years_8_to_13 :
    (∑ i, deaths i = 823856) ∧
      (deaths 8 + deaths 9 + deaths 10 + deaths 11 = 431874) ∧
      (0.5242 < (431874 : ℚ) / 823856 ∧ (431874 : ℚ) / 823856 < 0.5243) := by
  refine ⟨by simp [deaths, Fin.sum_univ_succ], by simp [deaths], by norm_num, by norm_num⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 1.11 (b). Only year 1 precedes year 2, with 231
deaths, which is 231/823856 of the total, between 0.028% and 0.0281% (percent value strictly between 0.028
and 0.0281). -/
@[kb "openstaxintrostats2e" "Exercise 1.11, p. 58"]
theorem ex_1_11_b_percent_before_year_2 :
    (deaths 0 = 231) ∧ (0.028 < (231 : ℚ) / 823856 * 100 ∧ (231 : ℚ) / 823856 * 100 < 0.0281) := by
  refine ⟨by simp [deaths], by norm_num, by norm_num⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 1.11 (c). Year 4 (33,819 deaths) together with the
years after year 11 (21,953 + 768 deaths) gives 56,540 deaths, i.e. 56540/823856 of the total, a percentage
strictly between 6.86 and 6.87. -/
@[kb "openstaxintrostats2e" "Exercise 1.11, p. 58"]
theorem ex_1_11_c_percent_year_4_or_after_11 :
    (deaths 3 + deaths 11 + deaths 12 = 56540) ∧
      (6.86 < (56540 : ℚ) / 823856 * 100 ∧ (56540 : ℚ) / 823856 * 100 < 6.87) := by
  refine ⟨by simp [deaths], by norm_num, by norm_num⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 1.11 (d). The deaths before year 13 number
823,856 - 768 = 823,088, so their fraction of the total is 823088/823856, strictly between 0.9990 and
0.9991. -/
@[kb "openstaxintrostats2e" "Exercise 1.11, p. 58"]
theorem ex_1_11_d_fraction_before_year_13 :
    (∑ i : Fin 13, (if i.val < 12 then deaths i else 0) = 823088) ∧
      (0.999 < (823088 : ℚ) / 823856 ∧ (823088 : ℚ) / 823856 < 0.9991) := by
  refine ⟨by simp [deaths, Fin.sum_univ_succ], by norm_num, by norm_num⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 1.16 (table for researcher A). With the classes
0.5-6.5, 6.5-12.5, ..., 42.5-48.5 (which contain the integers 1-6, 7-12, ..., 43-48) the frequencies of
researcher A's 40 times are 2, 5, 9, 5, 7, 7, 2, 3 (total 40); the relative frequencies are 0.05, 0.125,
0.225, 0.125, 0.175, 0.175, 0.05, 0.075. -/
@[kb "openstaxintrostats2e" "Exercise 1.16, p. 59"]
theorem ex_1_16_table_researcher_A :
    ([(1, 6), (7, 12), (13, 18), (19, 24), (25, 30), (31, 36), (37, 42), (43, 48)].map
        (fun p : ℕ × ℕ => classCount resA p.1 p.2) = [2, 5, 9, 5, 7, 7, 2, 3]) ∧
      ([2, 5, 9, 5, 7, 7, 2, 3].sum = 40) ∧
      ([2, 5, 9, 5, 7, 7, 2, 3].map (fun f : ℕ => (f : ℚ) / 40) =
        [0.05, 0.125, 0.225, 0.125, 0.175, 0.175, 0.05, 0.075]) := by
  refine ⟨by rfl, by rfl, ?_⟩
  simp only [List.map_cons, List.map_nil]
  norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 1.16 (cumulative relative frequencies, researcher
A). The cumulative frequencies of the table for researcher A are 2, 7, 16, 21, 28, 35, 37, 40, so the
cumulative relative frequencies are 0.05, 0.175, 0.4, 0.525, 0.7, 0.875, 0.925, 1. -/
@[kb "openstaxintrostats2e" "Exercise 1.16, p. 59"]
theorem ex_1_16_cumulative_researcher_A :
    ((List.range 8).map (fun k => ([2, 5, 9, 5, 7, 7, 2, 3].take (k + 1)).sum) = [2, 7, 16, 21, 28, 35, 37, 40]) ∧
      ([2, 7, 16, 21, 28, 35, 37, 40].map (fun f : ℕ => (f : ℚ) / 40) =
        [0.05, 0.175, 0.4, 0.525, 0.7, 0.875, 0.925, 1]) := by
  refine ⟨by rfl, ?_⟩
  simp only [List.map_cons, List.map_nil]
  norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 1.16 (table for researcher B). With the classes
0.5-6.5, ..., 30.5-36.5 and 36.5-45.5 (integers 1-6, ..., 31-36 and 37-45) the frequencies of researcher
B's 40 times are 3, 2, 11, 8, 6, 6, 4 (total 40); the relative frequencies are 0.075, 0.05, 0.275, 0.2,
0.15, 0.15, 0.1 and the cumulative relative frequencies 0.075, 0.125, 0.4, 0.6, 0.75, 0.9, 1. -/
@[kb "openstaxintrostats2e" "Exercise 1.16, p. 59"]
theorem ex_1_16_table_researcher_B :
    ([(1, 6), (7, 12), (13, 18), (19, 24), (25, 30), (31, 36), (37, 45)].map
        (fun p : ℕ × ℕ => classCount resB p.1 p.2) = [3, 2, 11, 8, 6, 6, 4]) ∧
      ([3, 2, 11, 8, 6, 6, 4].sum = 40) ∧
      ([3, 2, 11, 8, 6, 6, 4].map (fun f : ℕ => (f : ℚ) / 40) =
        [0.075, 0.05, 0.275, 0.2, 0.15, 0.15, 0.1]) ∧
      ((List.range 7).map (fun k => (([3, 2, 11, 8, 6, 6, 4].take (k + 1)).sum : ℚ) / 40) =
        [0.075, 0.125, 0.4, 0.6, 0.75, 0.9, 1]) := by
  refine ⟨by rfl, by rfl, ?_, ?_⟩
  · simp only [List.map_cons, List.map_nil]
    norm_num
  · simp [List.range_succ]
    norm_num

/-- Frequencies of the video-game hours tables (classes 0-2, 2-4, ..., 10-12), researcher A. -/
private def gamesA : Fin 6 → ℕ := ![26, 30, 49, 25, 12, 8]

/-- Frequencies of the video-game hours tables, researcher B. -/
private def gamesB : Fin 6 → ℕ := ![48, 51, 24, 12, 11, 4]

/-- OpenStax Introductory Statistics 2e Practice exercise 1.25 (sample sizes). Both video-game tables are
built from 150 students; each printed relative frequency is the frequency over 150 rounded to two decimals
(the difference is below 0.005), which is the data behind the question whether 150 students suffice. -/
@[kb "openstaxintrostats2e" "Exercise 1.25, p. 60"]
theorem ex_1_25_sample_size_150 :
    (∑ i, gamesA i = 150) ∧ (∑ i, gamesB i = 150) ∧
      (∀ k : Fin 6, |(gamesA k : ℚ) / 150 - (![0.17, 0.20, 0.33, 0.17, 0.08, 0.05] : Fin 6 → ℚ) k| < 0.005) ∧
      (∀ k : Fin 6, |(gamesB k : ℚ) / 150 - (![0.32, 0.34, 0.16, 0.08, 0.07, 0.03] : Fin 6 → ℚ) k| < 0.005) := by
  refine ⟨by simp [gamesA, Fin.sum_univ_succ], by simp [gamesB, Fin.sum_univ_succ], ?_, ?_⟩
  · intro k
    fin_cases k <;> simp [gamesA] <;> norm_num [abs_lt]
  · intro k
    fin_cases k <;> simp [gamesB] <;> norm_num [abs_lt]

/-- OpenStax Introductory Statistics 2e Practice exercise 1.27 (cumulative columns). The cumulative relative
frequencies printed in the two video-game tables are the running totals of the printed relative
frequencies: 0.17, 0.37, 0.70, 0.87, 0.95, 1 for researcher A and 0.32, 0.66, 0.82, 0.90, 0.97, 1 for
researcher B. -/
@[kb "openstaxintrostats2e" "Exercise 1.27, p. 60"]
theorem ex_1_27_cumulative_columns :
    ((List.range 6).map (fun k => (([0.17, 0.20, 0.33, 0.17, 0.08, 0.05] : List ℚ).take (k + 1)).sum) =
        [0.17, 0.37, 0.70, 0.87, 0.95, 1]) ∧
      ((List.range 6).map (fun k => (([0.32, 0.34, 0.16, 0.08, 0.07, 0.03] : List ℚ).take (k + 1)).sum) =
        [0.32, 0.66, 0.82, 0.90, 0.97, 1]) := by
  constructor <;> (simp [List.range_succ]; norm_num)

/-- OpenStax Introductory Statistics 2e Practice exercise 1.27 (most frequent class). In researcher A's
table the class 4-6 hours is the most frequent (49 of 150 students); in researcher B's table it is the class
2-4 hours (51 of 150). Both statements are true of their own samples, so the data of the two researchers
differ rather than contradict each other. -/
@[kb "openstaxintrostats2e" "Exercise 1.27, p. 60"]
theorem ex_1_27_most_frequent_classes :
    (∀ k : Fin 6, gamesA k ≤ gamesA 2) ∧ (∀ k : Fin 6, k ≠ 2 → gamesA k < gamesA 2) ∧
      (∀ k : Fin 6, gamesB k ≤ gamesB 1) ∧ (∀ k : Fin 6, k ≠ 1 → gamesB k < gamesB 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro k <;> fin_cases k <;> simp [gamesA, gamesB]

/-- OpenStax Introductory Statistics 2e Practice exercise 1.29 (row totals, first study). In Table 1.32
the program group has 142 + 43 + 15 = 200 patients and the group without the program has 72 + 110 + 18 =
200 patients. -/
@[kb "openstaxintrostats2e" "Exercise 1.29, p. 61"]
theorem ex_1_29_study1_group_sizes :
    (142 + 43 + 15 = 200) ∧ (72 + 110 + 18 = 200) := by
  decide

/-- OpenStax Introductory Statistics 2e Practice exercise 1.29 (row totals, second study). In Table 1.33
the program group has 105 + 74 + 19 = 198 patients and the group without the program has 89 + 99 + 4 = 192
patients (not 200 each, although the text speaks of 200 patients). -/
@[kb "openstaxintrostats2e" "Exercise 1.29, p. 61"]
theorem ex_1_29_study2_group_sizes :
    (105 + 74 + 19 = 198) ∧ (89 + 99 + 4 = 192) := by
  decide

/-- OpenStax Introductory Statistics 2e Practice exercise 1.31 (improvement rates). In the first study the
share showing improvement is 142/200 = 71% with the program and 72/200 = 36% without it; in the second
study it is 105/198 (between 0.530 and 0.531) with the program and 89/192 (between 0.463 and 0.464) without.
In both studies the rate is higher with the program, which alone does not show that the software causes the
improvement. -/
@[kb "openstaxintrostats2e" "Exercise 1.31, p. 61"]
theorem ex_1_31_improvement_rates :
    ((142 : ℚ) / 200 = 0.71 ∧ (72 : ℚ) / 200 = 0.36 ∧ (72 : ℚ) / 200 < 142 / 200) ∧
      (0.530 < (105 : ℚ) / 198 ∧ (105 : ℚ) / 198 < 0.531 ∧ 0.463 < (89 : ℚ) / 192 ∧
        (89 : ℚ) / 192 < 0.464 ∧ (89 : ℚ) / 192 < 105 / 198) := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num⟩, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 1.34. A sample of 1,000 from a population of
5,000 is one fifth of the population. -/
@[kb "openstaxintrostats2e" "Exercise 1.34, p. 61"]
theorem ex_1_34_sample_fraction :
    (1000 : ℚ) / 5000 = 1 / 5 := by
  norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 1.35. A sample of 500 volunteers from a
population of 2,500 is one fifth of the population (the volunteering is the issue, not the size). -/
@[kb "openstaxintrostats2e" "Exercise 1.35, p. 61"]
theorem ex_1_35_sample_fraction :
    (500 : ℚ) / 2500 = 1 / 5 := by
  norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 1.37. A sample of two from a population of five
is two fifths of the population, i.e. 40%, but only two observations. -/
@[kb "openstaxintrostats2e" "Exercise 1.37, p. 61"]
theorem ex_1_37_sample_fraction :
    (2 : ℚ) / 5 = 0.4 := by
  norm_num

end UndergradKB.Statistics.Course.PracticeC1
