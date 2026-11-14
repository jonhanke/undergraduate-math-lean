import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.Count
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Data
import UndergradKB.Statistics.Sampling

/-!
# Worked examples, chapter 1 (OpenStax *Introductory Statistics 2e*): sampling and data

The numerical content of the chapter 1 examples: sample means of the listed data, the chance that a given
student is chosen in a simple random sample, and frequency tables (counts, relative and cumulative relative
frequencies). Purely verbal classification examples are not formalised.
-/

namespace UndergradKB.Statistics.Course.ExamplesC1

open UndergradKB.Statistics Finset

/-- OpenStax Introductory Statistics 2e Example 1.2. The four listed grade point averages 3.65, 2.80, 1.50,
3.90 have sample mean 2.9625 (the statistic of the study). -/
@[kb "openstaxintrostats2e" "Example 1.2, p. 20"]
theorem example_1_2_gpa_mean :
    mean (![3.65, 2.80, 1.50, 3.90] : Fin 4 → ℝ) = 2.9625 := by
  simp [mean, Fin.sum_univ_succ]
  norm_num

/-- OpenStax Introductory Statistics 2e Example 1.5. The numbers of books carried by the five sampled
students (3, 3, 4, 2, 1) have total 13 and mean 13/5. -/
@[kb "openstaxintrostats2e" "Example 1.5, p. 23"]
theorem example_1_5_books_mean :
    (∑ i, (![3, 3, 4, 2, 1] : Fin 5 → ℝ) i) = 13 ∧ mean (![3, 3, 4, 2, 1] : Fin 5 → ℝ) = 13 / 5 := by
  simp [mean, Fin.sum_univ_succ]
  norm_num

/-- OpenStax Introductory Statistics 2e Example 1.6. The backpack weights 6.2, 7, 6.8, 9.1, 4.3 pounds have
total 33.4 and mean 6.68 pounds. -/
@[kb "openstaxintrostats2e" "Example 1.6, p. 23"]
theorem example_1_6_weights_mean :
    (∑ i, (![6.2, 7, 6.8, 9.1, 4.3] : Fin 5 → ℝ) i) = 33.4 ∧
      mean (![6.2, 7, 6.8, 9.1, 4.3] : Fin 5 → ℝ) = 6.68 := by
  simp [mean, Fin.sum_univ_succ]
  norm_num

/-- OpenStax Introductory Statistics 2e Example 1.8. Among the five backpack colours red, black, black,
green, gray, black occurs twice, so its relative frequency is 2/5, and the counts of the four colours add to
five. -/
@[kb "openstaxintrostats2e" "Example 1.8, p. 24"]
theorem example_1_8_colour_counts :
    (["red", "black", "black", "green", "gray"].count "black" = 2) ∧
    ((["red", "black", "black", "green", "gray"].count "black" : ℚ) / 5 = 2 / 5) ∧
    (["red", "black", "black", "green", "gray"].count "red" +
      ["red", "black", "black", "green", "gray"].count "black" +
      ["red", "black", "black", "green", "gray"].count "green" +
      ["red", "black", "black", "green", "gray"].count "gray" = 5) := by
  refine ⟨by decide, by norm_num [List.count_cons], by decide⟩

/-- OpenStax Introductory Statistics 2e Example 1.13 (first sample). The ten convenience-sample book
expenditures sum to 1420 dollars, so their mean is 142 dollars. -/
@[kb "openstaxintrostats2e" "Example 1.13, p. 35"]
theorem example_1_13_sample1_mean :
    mean (![128, 87, 173, 116, 130, 204, 147, 189, 93, 153] : Fin 10 → ℝ) = 142 := by
  simp [mean, Fin.sum_univ_succ]
  norm_num

/-- OpenStax Introductory Statistics 2e Example 1.13 (second sample). The ten senior-citizen expenditures
sum to 428 dollars, so their mean is 42.8 dollars. -/
@[kb "openstaxintrostats2e" "Example 1.13, p. 35"]
theorem example_1_13_sample2_mean :
    mean (![50, 40, 36, 15, 50, 100, 40, 53, 22, 22] : Fin 10 → ℝ) = 42.8 := by
  simp [mean, Fin.sum_univ_succ]
  norm_num

/-- OpenStax Introductory Statistics 2e Example 1.13 (third sample). The ten expenditures of the
stratified sample sum to 1530 dollars, so their mean is 153 dollars. -/
@[kb "openstaxintrostats2e" "Example 1.13, p. 35"]
theorem example_1_13_sample3_mean :
    mean (![180, 50, 150, 85, 260, 75, 180, 200, 200, 150] : Fin 10 → ℝ) = 153 := by
  simp [mean, Fin.sum_univ_succ]
  norm_num

/-- OpenStax Introductory Statistics 2e Example 1.13. The means of the first two samples differ by 99.2
dollars: the first is more than three times the second. -/
@[kb "openstaxintrostats2e" "Example 1.13, p. 35"]
theorem example_1_13_means_differ :
    mean (![128, 87, 173, 116, 130, 204, 147, 189, 93, 153] : Fin 10 → ℝ) -
      mean (![50, 40, 36, 15, 50, 100, 40, 53, 22, 22] : Fin 10 → ℝ) = 99.2 ∧
    3 * mean (![50, 40, 36, 15, 50, 100, 40, 53, 22, 22] : Fin 10 → ℝ) <
      mean (![128, 87, 173, 116, 130, 204, 147, 189, 93, 153] : Fin 10 → ℝ) := by
  simp [mean, Fin.sum_univ_succ]
  norm_num

/-- OpenStax Introductory Statistics 2e Example 1.13 (the third sample). With 10 disciplines of 1000
part-time students each, a student picked by simple random sampling within his or her discipline is chosen
with probability 1/1000 = 10/10000, the same chance as in a simple random sample of ten from all 10000
part-time students. -/
@[kb "openstaxintrostats2e" "Example 1.13, p. 35"]
theorem example_1_13_equal_chance (i : Fin 1000) (j : Fin 10000) :
    (srsLaw 1000 1).real {S | i ∈ S} = 1 / 1000 ∧
    (srsLaw 10000 10).real {S | j ∈ S} = 1 / 1000 := by
  rw [srsLaw_inclusion_prob (by norm_num) (by norm_num),
    srsLaw_inclusion_prob (by norm_num) (by norm_num)]
  norm_num

/-- Frequencies of Table 1.13 (heights of 100 soccer players, eight classes). -/
private def heightFreq : Fin 8 → ℕ := ![5, 3, 15, 40, 17, 12, 7, 1]

/-- OpenStax Introductory Statistics 2e Example 1.14. In Table 1.13 the first three classes contain
5 + 3 + 15 = 23 of the 100 players, so 23% are shorter than 65.95 inches; the cumulative relative
frequencies of the whole table are 0.05, 0.08, 0.23, 0.63, 0.80, 0.92, 0.99, 1.00. -/
@[kb "openstaxintrostats2e" "Example 1.14, p. 41"]
theorem example_1_14_below_6595 :
    (∑ i, heightFreq i = 100) ∧
    (heightFreq 0 + heightFreq 1 + heightFreq 2 = 23) ∧
    ((23 : ℚ) / 100 = 0.23) ∧
    ((fun k : Fin 8 => ((∑ i : Fin 8, if i ≤ k then heightFreq i else 0 : ℕ) : ℚ) / 100) =
      ![0.05, 0.08, 0.23, 0.63, 0.80, 0.92, 0.99, 1.00]) := by
  refine ⟨by simp [heightFreq, Fin.sum_univ_succ], by simp [heightFreq], by norm_num, ?_⟩
  funext k
  fin_cases k <;> simp [heightFreq, Fin.sum_univ_succ, Fin.le_def] <;> norm_num

/-- OpenStax Introductory Statistics 2e Example 1.15. The classes 61.95-63.95 and 63.95-65.95 hold
3 + 15 = 18 of the 100 players, a relative frequency of 0.18. -/
@[kb "openstaxintrostats2e" "Example 1.15, p. 42"]
theorem example_1_15_between :
    ((heightFreq 1 : ℚ) + heightFreq 2) / 100 = 0.18 := by
  simp [heightFreq]
  norm_num

/-- OpenStax Introductory Statistics 2e Example 1.16 (a, b, c). The relative frequency of heights from
67.95 to 71.95 is 29%, from 67.95 to 73.95 is 36%, and above 65.95 is 77%. -/
@[kb "openstaxintrostats2e" "Example 1.16, p. 42"]
theorem example_1_16_percentages :
    ((heightFreq 4 : ℚ) + heightFreq 5) / 100 = 0.29 ∧
    ((heightFreq 4 : ℚ) + heightFreq 5 + heightFreq 6) / 100 = 0.36 ∧
    ((heightFreq 3 : ℚ) + heightFreq 4 + heightFreq 5 + heightFreq 6 + heightFreq 7) / 100 = 0.77 := by
  simp [heightFreq]
  norm_num

/-- OpenStax Introductory Statistics 2e Example 1.16 (d). The number of players between 61.95 and 71.95
inches tall (classes 2 to 6) is 87. -/
@[kb "openstaxintrostats2e" "Example 1.16, p. 42"]
theorem example_1_16_count :
    heightFreq 1 + heightFreq 2 + heightFreq 3 + heightFreq 4 + heightFreq 5 = 87 := by
  simp [heightFreq]

/-- The nineteen commuting distances of Example 1.17. -/
private def commute : List ℕ := [2, 5, 7, 3, 2, 10, 18, 15, 20, 7, 10, 18, 5, 12, 13, 12, 4, 5, 10]

/-- OpenStax Introductory Statistics 2e Example 1.17 (a). The frequency column of Table 1.15 (2, 1, 1, 3,
2, 3, 2, 1, 1, 1, 1) sums to 18 although 19 people were asked; the true frequency of 18 miles is 2, not 1,
and with it the counts computed from the data add up to 19. -/
@[kb "openstaxintrostats2e" "Example 1.17, p. 43"]
theorem example_1_17_table_error :
    (2 + 1 + 1 + 3 + 2 + 3 + 2 + 1 + 1 + 1 + 1 = 18) ∧ commute.length = 19 ∧
    commute.count 18 = 2 ∧
    (commute.count 2 = 2 ∧ commute.count 3 = 1 ∧ commute.count 4 = 1 ∧ commute.count 5 = 3 ∧
      commute.count 7 = 2 ∧ commute.count 10 = 3 ∧ commute.count 12 = 2 ∧ commute.count 13 = 1 ∧
      commute.count 15 = 1 ∧ commute.count 20 = 1) := by
  decide +kernel

/-- OpenStax Introductory Statistics 2e Example 1.17 (b). The fraction of the 19 people commuting at most
three miles is 3/19 (about 16%), not 3%. -/
@[kb "openstaxintrostats2e" "Example 1.17, p. 43"]
theorem example_1_17_at_most_three :
    (commute.countP (· ≤ 3) : ℚ) / commute.length = 3 / 19 ∧ (3 : ℚ) / 19 ≠ 3 / 100 := by
  have h : commute.countP (· ≤ 3) = 3 := by decide +kernel
  have h2 : commute.length = 19 := by decide +kernel
  rw [h, h2]
  norm_num

/-- OpenStax Introductory Statistics 2e Example 1.17 (c, d). Of the 19 people, 5/19 commute five or seven
miles, 7/19 commute 12 miles or more, 12/19 less than 12 miles, and 7/19 strictly between five and 13
miles. -/
@[kb "openstaxintrostats2e" "Example 1.17, p. 43"]
theorem example_1_17_fractions :
    (commute.countP (fun x => x = 5 ∨ x = 7) : ℚ) / commute.length = 5 / 19 ∧
    (commute.countP (12 ≤ ·) : ℚ) / commute.length = 7 / 19 ∧
    (commute.countP (· < 12) : ℚ) / commute.length = 12 / 19 ∧
    (commute.countP (fun x => 5 < x ∧ x < 13) : ℚ) / commute.length = 7 / 19 := by
  have h1 : commute.countP (fun x => x = 5 ∨ x = 7) = 5 := by decide +kernel
  have h2 : commute.countP (12 ≤ ·) = 7 := by decide +kernel
  have h3 : commute.countP (· < 12) = 12 := by decide +kernel
  have h4 : commute.countP (fun x => 5 < x ∧ x < 13) = 7 := by decide +kernel
  have h : commute.length = 19 := by decide +kernel
  rw [h1, h2, h3, h4, h]
  norm_num

/-- Numbers of federal employees by years of service 24, 25, ..., 35 (Table 1.16). -/
private def service : Fin 12 → ℕ := ![2, 1, 3, 0, 4, 6, 11, 12, 7, 8, 6, 10]

/-- OpenStax Introductory Statistics 2e Example 1.18. Table 1.16 covers 70 employees; 54 of them have
between 30 and 35 years of service. -/
@[kb "openstaxintrostats2e" "Example 1.18, p. 44"]
theorem example_1_18_cumulative :
    (∑ i, service i = 70) ∧
      (service 6 + service 7 + service 8 + service 9 + service 10 + service 11 = 54) := by
  simp [service, Fin.sum_univ_succ]

/-- OpenStax Introductory Statistics 2e Example 1.18 (b, c, d). The relative frequency of 30 years is
11/70 (0.157), of 30 years or less 27/70 (0.386), and of 25 years or more 68/70 (0.971); the book's
three-decimal values are within 0.0005. -/
@[kb "openstaxintrostats2e" "Example 1.18, p. 44"]
theorem example_1_18_relative :
    ((service 6 : ℚ) / 70 = 11 / 70 ∧ |(11 : ℚ) / 70 - 0.157| < 0.0005) ∧
    (((service 0 + service 1 + service 2 + service 3 + service 4 + service 5 + service 6 : ℕ) : ℚ) / 70
        = 27 / 70 ∧ |(27 : ℚ) / 70 - 0.386| < 0.0005) ∧
    (((70 - service 0 : ℕ) : ℚ) / 70 = 68 / 70 ∧ |(68 : ℚ) / 70 - 0.971| < 0.0005) := by
  refine ⟨⟨by simp [service], ?_⟩, ⟨by simp [service], ?_⟩, ⟨by simp [service], ?_⟩⟩ <;>
    (rw [abs_lt]; constructor <;> norm_num)

end UndergradKB.Statistics.Course.ExamplesC1
