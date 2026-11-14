import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.Count
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Data

/-!
# "Try It" exercises, chapter 1 (OpenStax *Introductory Statistics 2e*): sampling and data

The numerical content of the chapter 1 exercises: sample means of the listed data, counts and relative
frequencies of a list, and relative and cumulative relative frequencies of frequency tables. The verbal
exercises (key terms, kinds of data, sampling methods, experimental design, ethics) have no mathematical
statement and are not formalised.
-/

namespace UndergradKB.Statistics.Course.TryItC1

open UndergradKB.Statistics Finset

/-- OpenStax Introductory Statistics 2e Try It 1.1. The three family expenditures listed (65, 75, 95
dollars) total 235 dollars, so their mean is 235/3 dollars. (This is the arithmetic on the listed data
only; the exercise itself asks to name the population, sample and so on.) -/
@[kb "openstaxintrostats2e" "Try It 1.1, p. 20"]
theorem tryit_1_1_uniform_mean :
    (∑ i, (![65, 75, 95] : Fin 3 → ℝ) i) = 235 ∧ mean (![65, 75, 95] : Fin 3 → ℝ) = 235 / 3 := by
  simp [mean, Fin.sum_univ_succ]
  norm_num

/-- OpenStax Introductory Statistics 2e Try It 1.2. The four athlete heights 1.82, 1.76, 1.69, 1.93
meters have mean 1.8 meters (the statistic of the study; the matching of key terms is verbal). -/
@[kb "openstaxintrostats2e" "Try It 1.2, p. 20"]
theorem tryit_1_2_heights_mean :
    mean (![1.82, 1.76, 1.69, 1.93] : Fin 4 → ℝ) = 1.8 := by
  simp [mean, Fin.sum_univ_succ]
  norm_num

/-- OpenStax Introductory Statistics 2e Try It 1.5. The numbers of machines in the five gyms (12, 15, 10,
22, 20; counts, hence quantitative discrete data) total 79, with mean 79/5. -/
@[kb "openstaxintrostats2e" "Try It 1.5, p. 23"]
theorem tryit_1_5_machines_mean :
    (∑ i, (![12, 15, 10, 22, 20] : Fin 5 → ℝ) i) = 79 ∧
      mean (![12, 15, 10, 22, 20] : Fin 5 → ℝ) = 79 / 5 := by
  simp [mean, Fin.sum_univ_succ]
  norm_num

/-- OpenStax Introductory Statistics 2e Try It 1.6. The five lawn areas (144, 160, 190, 180, 210 square
feet) total 884, with mean 176.8 square feet. -/
@[kb "openstaxintrostats2e" "Try It 1.6, p. 23"]
theorem tryit_1_6_lawn_mean :
    (∑ i, (![144, 160, 190, 180, 210] : Fin 5 → ℝ) i) = 884 ∧
      mean (![144, 160, 190, 180, 210] : Fin 5 → ℝ) = 176.8 := by
  simp [mean, Fin.sum_univ_succ]
  norm_num

/-- OpenStax Introductory Statistics 2e Try It 1.8. Among the five house colours white, yellow, white,
red, white, white occurs three times, so its relative frequency is 3/5; the counts of the three colours
add to five. -/
@[kb "openstaxintrostats2e" "Try It 1.8, p. 24"]
theorem tryit_1_8_colour_counts :
    (["white", "yellow", "white", "red", "white"].count "white" = 3) ∧
    ((["white", "yellow", "white", "red", "white"].count "white" : ℚ) / 5 = 3 / 5) ∧
    (["white", "yellow", "white", "red", "white"].count "white" +
      ["white", "yellow", "white", "red", "white"].count "yellow" +
      ["white", "yellow", "white", "red", "white"].count "red" = 5) := by
  refine ⟨by decide, by norm_num [List.count_cons], by decide⟩

/-- OpenStax Introductory Statistics 2e Try It 1.13. Of the 200 people surveyed, 24 prefer more talk and
176 prefer more music: the relative frequencies are 3/25 = 0.12 and 22/25 = 0.88 and they add to one.
(Whether a convenience sample at a concert represents the 20,000 listeners is a verbal question; the
sample proportions are all the data give.) -/
@[kb "openstaxintrostats2e" "Try It 1.13, p. 36"]
theorem tryit_1_13_listener_proportions :
    (24 + 176 = 200) ∧ ((24 : ℚ) / 200 = 3 / 25 ∧ (3 : ℚ) / 25 = 0.12) ∧
      ((176 : ℚ) / 200 = 22 / 25 ∧ (22 : ℚ) / 25 = 0.88) ∧ (24 : ℚ) / 200 + 176 / 200 = 1 := by
  refine ⟨rfl, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, by norm_num⟩

/-- Frequencies of Table 1.14 (annual rainfall in 50 towns, six classes). -/
private def rainFreq : Fin 6 → ℕ := ![6, 7, 15, 8, 9, 5]

/-- OpenStax Introductory Statistics 2e Try It 1.14. The frequencies of Table 1.14 add to 50, the
relative frequencies are 0.12, 0.14, 0.30, 0.16, 0.18, 0.10 and the cumulative relative frequencies 0.12,
0.26, 0.56, 0.72, 0.90, 1.00. The first three classes (rainfall below 9.01 inches) hold 28 of the 50
towns, i.e. 56%. -/
@[kb "openstaxintrostats2e" "Try It 1.14, p. 41"]
theorem tryit_1_14_below_901 :
    (∑ i, rainFreq i = 50) ∧
    ((fun k : Fin 6 => (rainFreq k : ℚ) / 50) = ![0.12, 0.14, 0.30, 0.16, 0.18, 0.10]) ∧
    ((fun k : Fin 6 => ((∑ i : Fin 6, if i ≤ k then rainFreq i else 0 : ℕ) : ℚ) / 50) =
      ![0.12, 0.26, 0.56, 0.72, 0.90, 1.00]) ∧
    (rainFreq 0 + rainFreq 1 + rainFreq 2 = 28) ∧ ((28 : ℚ) / 50 = 0.56) := by
  refine ⟨by simp [rainFreq, Fin.sum_univ_succ], ?_, ?_, by simp [rainFreq], by norm_num⟩
  · funext k
    fin_cases k <;> simp [rainFreq] <;> norm_num
  · funext k
    fin_cases k <;> simp [rainFreq, Fin.sum_univ_succ, Fin.le_def] <;> norm_num

/-- OpenStax Introductory Statistics 2e Try It 1.15. The classes 6.99-9.01, 9.01-11.03 and 11.03-13.05
inches of Table 1.14 hold 15 + 8 + 9 = 32 of the 50 towns, so the rainfall between 6.99 and 13.05 inches
has relative frequency 32/50 = 0.64. -/
@[kb "openstaxintrostats2e" "Try It 1.15, p. 42"]
theorem tryit_1_15_between :
    ((rainFreq 2 : ℚ) + rainFreq 3 + rainFreq 4) / 50 = 0.64 := by
  simp [rainFreq]
  norm_num

/-- OpenStax Introductory Statistics 2e Try It 1.16. The number of towns with rainfall between 2.95 and
9.01 inches (the first three classes of Table 1.14) is 6 + 7 + 15 = 28. -/
@[kb "openstaxintrostats2e" "Try It 1.16, p. 43"]
theorem tryit_1_16_count :
    rainFreq 0 + rainFreq 1 + rainFreq 2 = 28 := by
  simp [rainFreq]

/-- OpenStax Introductory Statistics 2e Try It 1.17. The fraction of the towns of Table 1.14 with rainfall
between 11.03 and 13.05 inches (the fifth class, 9 towns) is 9/50 = 0.18. -/
@[kb "openstaxintrostats2e" "Try It 1.17, p. 44"]
theorem tryit_1_17_fraction :
    (rainFreq 4 : ℚ) / 50 = 9 / 50 ∧ (9 : ℚ) / 50 = 0.18 := by
  refine ⟨by simp [rainFreq], by norm_num⟩

/-- Numbers of fatal crashes in years 1 to 18 (Table 1.17). -/
private def crashes : Fin 18 → ℕ :=
  ![36254, 37241, 37494, 37324, 37107, 37140, 37526, 37862, 38491, 38477, 38444, 39252, 38648, 37435,
    34172, 30862, 30296, 29757]

/-- OpenStax Introductory Statistics 2e Try It 1.18 (total and part a). The 18 yearly counts of Table 1.17
add up to the printed total 653,782, and the frequency from year 7 through year 11 is 190,800. -/
@[kb "openstaxintrostats2e" "Try It 1.18, p. 45"]
theorem tryit_1_18_total_and_frequency :
    (∑ i, crashes i = 653782) ∧
      (crashes 6 + crashes 7 + crashes 8 + crashes 9 + crashes 10 = 190800) := by
  refine ⟨by simp [crashes, Fin.sum_univ_succ], by simp [crashes]⟩

/-- OpenStax Introductory Statistics 2e Try It 1.18 (b, c, d). The relative frequency of crashes after
year 13 (years 14 to 18, 162,522 crashes) is 81261/326891, strictly between 0.2485 and 0.2486 (about
24.9%); of year 7 or before (260,086 crashes) it is 130043/326891, between 0.3978 and 0.3979; and of year
18 it is 273/5998, between 0.0455 and 0.0456 (about 4.6%). -/
@[kb "openstaxintrostats2e" "Try It 1.18, p. 45"]
theorem tryit_1_18_relative :
    (crashes 13 + crashes 14 + crashes 15 + crashes 16 + crashes 17 = 162522 ∧
      ((162522 : ℚ) / 653782 = 81261 / 326891 ∧ 0.2485 < (81261 : ℚ) / 326891 ∧
        (81261 : ℚ) / 326891 < 0.2486)) ∧
    (crashes 0 + crashes 1 + crashes 2 + crashes 3 + crashes 4 + crashes 5 + crashes 6 = 260086 ∧
      ((260086 : ℚ) / 653782 = 130043 / 326891 ∧ 0.3978 < (130043 : ℚ) / 326891 ∧
        (130043 : ℚ) / 326891 < 0.3979)) ∧
    ((crashes 17 : ℚ) / 653782 = 273 / 5998 ∧ 0.0455 < (273 : ℚ) / 5998 ∧ (273 : ℚ) / 5998 < 0.0456) := by
  refine ⟨⟨by simp [crashes], by norm_num, by norm_num, by norm_num⟩,
    ⟨by simp [crashes], by norm_num, by norm_num, by norm_num⟩, ?_⟩
  refine ⟨by simp [crashes]; norm_num, by norm_num, by norm_num⟩

/-- OpenStax Introductory Statistics 2e Try It 1.18 (e). The cumulative frequency through year 13 is
491,260 crashes, so the cumulative relative frequency is 245630/326891, strictly between 0.7514 and 0.7515:
about 75% of all the crashes of the 18 years occurred in the first 13 years. -/
@[kb "openstaxintrostats2e" "Try It 1.18, p. 45"]
theorem tryit_1_18_cumulative_year13 :
    (∑ i : Fin 18, (if i.val ≤ 12 then crashes i else 0) = 491260) ∧
      ((491260 : ℚ) / 653782 = 245630 / 326891 ∧ 0.7514 < (245630 : ℚ) / 326891 ∧
        (245630 : ℚ) / 326891 < 0.7515) := by
  refine ⟨by simp [crashes, Fin.sum_univ_succ], by norm_num, by norm_num, by norm_num⟩

/-- OpenStax Introductory Statistics 2e Try It 1.22 (d). Of the surveyed teens, 25% prefer Brand X, 33%
prefer Brand Y and 42% have no preference. Brand X is liked "as much as or more" than Brand Y by 25 + 42 =
67%, a majority, yet Brand Y is liked as much as or more by 33 + 42 = 75%, and strictly more teens prefer
Y (33%) than X (25%): the claim is true but misleading. -/
@[kb "openstaxintrostats2e" "Try It 1.22, p. 50"]
theorem tryit_1_22_brand_claim :
    (25 + 33 + 42 = 100) ∧ (25 + 42 = 67 ∧ 50 < 25 + 42) ∧ (33 + 42 = 75 ∧ 25 + 42 < 33 + 42) ∧
      25 < 33 := by
  decide

end UndergradKB.Statistics.Course.TryItC1
