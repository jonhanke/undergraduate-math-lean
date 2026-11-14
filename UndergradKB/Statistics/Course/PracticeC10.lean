import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF
import Mathlib.Data.Fin.VecNotation
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Data
import UndergradKB.Statistics.Welch
import UndergradKB.Statistics.EmpiricalRule
import UndergradKB.Statistics.CriticalValues
import UndergradKB.Statistics.Course.ExamplesC10

/-!
# "Practice" exercises, chapter 10 (OpenStax *Introductory Statistics 2e*): hypothesis tests with two samples

Test statistics, degrees of freedom and normal `p`-values for the end-of-chapter Practice exercises of
chapter 10, computed with the definitions of `ExamplesC10` (`welchT`, `pooledZ`, `pairedT`) and `welchDF`.
Normal `p`-values are proved as two-sided bounds through enclosures of the standard normal distribution
function. Student `t` critical values are standard table values (quoted, not proved) and are used only for
the reject / do-not-reject decision. The purely verbal exercises (classifying a test, naming the random
variable, hypotheses in words, sketches) are not formalised.
-/

namespace UndergradKB.Statistics.Course.PracticeC10

open UndergradKB.Statistics UndergradKB.Statistics.Course.ExamplesC10 MeasureTheory ProbabilityTheory
  Real Set

local notation "Φ" => cdf (gaussianReal 0 1)

local macro "emp" : tactic =>
  `(tactic| (simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial]))

/-! ### Helpers -/

private lemma pos_bounds {c x a b L U : ℝ} (hc : 0 ≤ c) (ha : 0 < a) (hb : 0 < b) (h1 : a ^ 2 < x)
    (h2 : x < b ^ 2) (hL : L * b < c) (hU : c < U * a) : L < c / √x ∧ c / √x < U := by
  have s1 : a < √x := (Real.lt_sqrt ha.le).2 h1
  have s2 : √x < b := (Real.sqrt_lt' hb).2 h2
  have hp : 0 < √x := by linarith
  have hU0 : 0 ≤ U := by
    by_contra h
    have h' : U < 0 := not_le.mp h
    nlinarith
  constructor
  · rw [lt_div_iff₀ hp]
    rcases le_total 0 L with h | h
    · nlinarith [mul_le_mul_of_nonneg_left s2.le h]
    · nlinarith
  · rw [div_lt_iff₀ hp]
    nlinarith [mul_le_mul_of_nonneg_left s1.le hU0]

private lemma neg_bounds {c x a b L U : ℝ} (hc : c ≤ 0) (ha : 0 < a) (hb : 0 < b) (h1 : a ^ 2 < x)
    (h2 : x < b ^ 2) (hL : L * a < c) (hU : c < U * b) : L < c / √x ∧ c / √x < U := by
  have := pos_bounds (c := -c) (x := x) (a := a) (b := b) (L := -U) (U := -L) (by linarith) ha hb h1 h2
    (by linarith) (by linarith)
  rw [neg_div] at this
  constructor <;> linarith [this.1, this.2]

private lemma sqrt_eq {x r : ℝ} (hr : 0 ≤ r) (h : x = r ^ 2) : √x = r := by
  rw [h]; exact Real.sqrt_sq hr

/-- Two-sided `p`-value of a positive statistic `z` between `L` and `U`, from enclosures of the central
mass of the standard normal law at `L` and at `U`. -/
private lemma two_sided_pos {z L U a b : ℝ} (hL0 : 0 ≤ L) (hz : L < z ∧ z < U)
    (e1 : a < (gaussianReal 0 1).real (Ioo (-L) L)) (e2 : (gaussianReal 0 1).real (Ioo (-U) U) < b) :
    1 - b < 2 * (1 - Φ z) ∧ 2 * (1 - Φ z) < 1 - a := by
  have hU0 : 0 ≤ U := by linarith [hz.1, hz.2]
  have h1 := stdNormalCdf_eq_Ioo hL0
  have h2 := stdNormalCdf_eq_Ioo hU0
  have m1 := monotone_cdf (gaussianReal 0 1) hz.1.le
  have m2 := monotone_cdf (gaussianReal 0 1) hz.2.le
  constructor <;> linarith

/-- Two-sided `p`-value `2 Φ z` of a negative statistic `z` between `-U` and `-L`. -/
private lemma two_sided_neg {z L U a b : ℝ} (hL0 : 0 ≤ L) (hz : -U < z ∧ z < -L)
    (e1 : a < (gaussianReal 0 1).real (Ioo (-L) L)) (e2 : (gaussianReal 0 1).real (Ioo (-U) U) < b) :
    1 - b < 2 * Φ z ∧ 2 * Φ z < 1 - a := by
  have := two_sided_pos (z := -z) hL0 ⟨by linarith [hz.2], by linarith [hz.1]⟩ e1 e2
  rw [stdNormalCdf_neg] at this
  constructor <;> linarith [this.1, this.2]

/-- If `z ≥ k` and the central mass at `k` exceeds `a`, the right tail is below `(1 - a)/2`. -/
private lemma tail_lt {z k a : ℝ} (hk : 0 ≤ k) (hkz : k ≤ z)
    (e : a < (gaussianReal 0 1).real (Ioo (-k) k)) : 1 - Φ z < 1 / 2 - a / 2 := by
  have h1 := stdNormalCdf_eq_Ioo hk
  have h2 := monotone_cdf (gaussianReal 0 1) hkz
  linarith

/-! ### Section 10.1: two means, unknown standard deviations -/

/-- OpenStax Introductory Statistics 2e Practice exercise 10.7. English essay grades: `31` women (mean `82`,
standard deviation `3`) against `25` men (mean `76`, standard deviation `4`), right-tailed (women higher),
unknown standard deviations. The Welch statistic lies strictly between `6.22063` and `6.22064`, the degrees of
freedom strictly between `43.54` and `43.55`; the statistic exceeds the right-tail `5%` critical value
`1.684` of a standard `t` table (`40` degrees of freedom row, a table value, not proved): reject. -/
@[kb "openstaxintrostats2e" "Exercise 10.7, p. 549"]
theorem ex_10_7_essay_grades :
    (6.22063 < welchT 82 76 (3 ^ 2) (4 ^ 2) 31 25 ∧ welchT 82 76 (3 ^ 2) (4 ^ 2) 31 25 < 6.22064) ∧
      (43.54 < welchDF (3 ^ 2) (4 ^ 2) 31 25 ∧ welchDF (3 ^ 2) (4 ^ 2) 31 25 < 43.55) ∧
      1.684 < welchT 82 76 (3 ^ 2) (4 ^ 2) 31 25 := by
  have e : welchT 82 76 (3 ^ 2) (4 ^ 2) 31 25 = 6 / √(9 / 31 + 16 / 25) := by
    unfold welchT; norm_num
  have hz := pos_bounds (c := 6) (x := 9 / 31 + 16 / 25) (a := 0.9645323) (b := 0.9645324) (L := 6.22063)
    (U := 6.22064) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  rw [e]
  refine ⟨hz, ⟨?_, ?_⟩, by linarith [hz.1]⟩
  · unfold welchDF; norm_num
  · unfold welchDF; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 10.8. Batting averages with known standard
deviation `0.06`; mean `0.21` (Rattlers) and `0.26` (Vikings) for samples of `8` each. The `z` statistic is
exactly `-5/3`, and the two-sided `p`-value `2 Φ(z)` lies strictly between `0.0955` and `0.0957`, above
`0.05`: do not reject, no statistical difference at the `5%` level. -/
@[kb "openstaxintrostats2e" "Exercise 10.8, p. 550"]
theorem ex_10_8_batting_averages :
    welchT 0.21 0.26 (0.06 ^ 2) (0.06 ^ 2) 8 8 = -5 / 3 ∧
      (0.0955 < 2 * Φ (welchT 0.21 0.26 (0.06 ^ 2) (0.06 ^ 2) 8 8) ∧
        2 * Φ (welchT 0.21 0.26 (0.06 ^ 2) (0.06 ^ 2) 8 8) < 0.0957) ∧
      0.05 < 2 * Φ (welchT 0.21 0.26 (0.06 ^ 2) (0.06 ^ 2) 8 8) := by
  have e : welchT 0.21 0.26 (0.06 ^ 2) (0.06 ^ 2) 8 8 = -5 / 3 := by
    have h : welchT 0.21 0.26 (0.06 ^ 2) (0.06 ^ 2) 8 8 = (-1 / 20) / √(9 / 10000) := by
      unfold welchT; norm_num
    rw [h, sqrt_eq (r := 3 / 100) (by norm_num) (by norm_num)]; norm_num
  refine ⟨e, ?_⟩
  rw [e]
  have e1 := Ioo_enclosure (k := 1.6666) (a := 0.9043) (b := 0.9045) (by norm_num) 10 (by norm_num)
    (by emp) (by emp)
  have e2 := Ioo_enclosure (k := 1.6667) (a := 0.9043) (b := 0.9045) (by norm_num) 10 (by norm_num)
    (by emp) (by emp)
  have := two_sided_neg (z := -5 / 3) (L := 1.6666) (U := 1.6667) (a := 0.9043) (b := 0.9045)
    (by norm_num) ⟨by norm_num, by norm_num⟩ e1.1 e2.2
  refine ⟨⟨by linarith [this.1], by linarith [this.2]⟩, by linarith [this.1]⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 10.9. Conifer forests: `56` of `100` in the United
States against `40` of `80` in Mexico, right-tailed (United States higher). The pooled `z` statistic lies
strictly between `0.80178` and `0.80179` and the right-tail `p`-value strictly between `0.211` and `0.2114`,
above `0.05`: do not reject. -/
@[kb "openstaxintrostats2e" "Exercise 10.9, p. 550"]
theorem ex_10_9_conifer_forests :
    (0.80178 < pooledZ 56 100 40 80 ∧ pooledZ 56 100 40 80 < 0.80179) ∧
      (0.211 < 1 - Φ (pooledZ 56 100 40 80) ∧ 1 - Φ (pooledZ 56 100 40 80) < 0.2114) ∧
      0.05 < 1 - Φ (pooledZ 56 100 40 80) := by
  have e : pooledZ 56 100 40 80 =
      (56 / 100 - 40 / 80) / √((96 / 180) * (1 - 96 / 180) * (1 / 100 + 1 / 80)) := by
    unfold pooledZ; norm_num
  have hz : 0.80178 < pooledZ 56 100 40 80 ∧ pooledZ 56 100 40 80 < 0.80179 := by
    rw [e]
    exact pos_bounds (c := 56 / 100 - 40 / 80) (x := (96 / 180) * (1 - 96 / 180) * (1 / 100 + 1 / 80))
      (a := 0.0748331) (b := 0.0748332) (L := 0.80178) (U := 0.80179) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e1 := Ioo_enclosure (k := 0.80178) (a := 0.5772) (b := 0.5775) (by norm_num) 10 (by norm_num)
    (by emp) (by emp)
  have e2 := Ioo_enclosure (k := 0.80179) (a := 0.5772) (b := 0.5775) (by norm_num) 10 (by norm_num)
    (by emp) (by emp)
  have := two_sided_pos (L := 0.80178) (U := 0.80179) (a := 0.5772) (b := 0.5775) (by norm_num) hz
    e1.1 e2.2
  refine ⟨hz, ⟨by linarith [this.1], by linarith [this.2]⟩, by linarith [this.1]⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 10.11. Sleep of teenagers (`16`, mean `8.9`,
standard deviation `1.2`) against adults (`12`, mean `6.9`, standard deviation `0.6`), right-tailed. The Welch
statistic lies strictly between `5.7735` and `5.77351`, the degrees of freedom strictly between `23.15` and
`23.16`; the statistic exceeds the right-tail `5%` critical value `1.714` of a standard `t` table (`23` degrees
of freedom, a table value, not proved): reject. -/
@[kb "openstaxintrostats2e" "Exercise 10.11, p. 550"]
theorem ex_10_11_teen_adult_sleep :
    (5.7735 < welchT 8.9 6.9 (1.2 ^ 2) (0.6 ^ 2) 16 12 ∧ welchT 8.9 6.9 (1.2 ^ 2) (0.6 ^ 2) 16 12 < 5.77351) ∧
      (23.15 < welchDF (1.2 ^ 2) (0.6 ^ 2) 16 12 ∧ welchDF (1.2 ^ 2) (0.6 ^ 2) 16 12 < 23.16) ∧
      1.714 < welchT 8.9 6.9 (1.2 ^ 2) (0.6 ^ 2) 16 12 := by
  have e : welchT 8.9 6.9 (1.2 ^ 2) (0.6 ^ 2) 16 12 = 2 / √(144 / 100 / 16 + 36 / 100 / 12) := by
    unfold welchT; norm_num
  have hz := pos_bounds (c := 2) (x := 144 / 100 / 16 + 36 / 100 / 12) (a := 0.3464101) (b := 0.3464102)
    (L := 5.7735) (U := 5.77351) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  rw [e]
  refine ⟨hz, ⟨?_, ?_⟩, by linarith [hz.1]⟩
  · unfold welchDF; norm_num
  · unfold welchDF; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 10.13. Graduate tuition: school A (`12` programs,
mean `64000`, standard deviation `8000`) against school B (`16`, mean `80000`, standard deviation `6000`),
two-sided. The Welch statistic lies strictly between `-5.81019` and `-5.81018`, the degrees of freedom
strictly between `19.67` and `19.68`; its absolute value exceeds the two-sided `5%` critical value `2.093`
of a standard `t` table (`19` degrees of freedom, a table value, not proved): reject, the mean tuitions
differ. -/
@[kb "openstaxintrostats2e" "Exercise 10.13, p. 550"]
theorem ex_10_13_graduate_tuition :
    (-5.81019 < welchT 64000 80000 (8000 ^ 2) (6000 ^ 2) 12 16 ∧
        welchT 64000 80000 (8000 ^ 2) (6000 ^ 2) 12 16 < -5.81018) ∧
      (19.67 < welchDF (8000 ^ 2) (6000 ^ 2) 12 16 ∧ welchDF (8000 ^ 2) (6000 ^ 2) 12 16 < 19.68) ∧
      2.093 < |welchT 64000 80000 (8000 ^ 2) (6000 ^ 2) 12 16| := by
  have e : welchT 64000 80000 (8000 ^ 2) (6000 ^ 2) 12 16 =
      (-16000) / √(8000 ^ 2 / 12 + 6000 ^ 2 / 16) := by
    unfold welchT; norm_num
  have hz := neg_bounds (c := -16000) (x := 8000 ^ 2 / 12 + 6000 ^ 2 / 16) (a := 2753.7852736)
    (b := 2753.7852737) (L := -5.81019) (U := -5.81018) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [e]
  refine ⟨hz, ⟨?_, ?_⟩, ?_⟩
  · unfold welchDF; norm_num
  · unfold welchDF; norm_num
  · rw [abs_of_neg (by linarith [hz.2])]; linarith [hz.2]

/-- OpenStax Introductory Statistics 2e Practice exercise 10.15. Driving to school: `45%` of `20` athletes
(`9` students) against `6%` of `35` non-athletes (`2.1` students, as the percentage is given), right-tailed.
The pooled `z` statistic lies strictly between `3.46657` and `3.46658`, above `3.46`, and the right-tail
`p`-value is below `0.0003`: reject. -/
@[kb "openstaxintrostats2e" "Exercise 10.15, p. 550"]
theorem ex_10_15_drive_to_school :
    (3.46657 < pooledZ 9 20 2.1 35 ∧ pooledZ 9 20 2.1 35 < 3.46658) ∧
      1 - Φ (pooledZ 9 20 2.1 35) < 0.0003 := by
  have e : pooledZ 9 20 2.1 35 =
      (9 / 20 - 21 / 10 / 35) / √((111 / 550) * (1 - 111 / 550) * (1 / 20 + 1 / 35)) := by
    unfold pooledZ; norm_num
  have hz : 3.46657 < pooledZ 9 20 2.1 35 ∧ pooledZ 9 20 2.1 35 < 3.46658 := by
    rw [e]
    exact pos_bounds (c := 9 / 20 - 21 / 10 / 35) (x := (111 / 550) * (1 - 111 / 550) * (1 / 20 + 1 / 35))
      (a := 0.112502813) (b := 0.112502814) (L := 3.46657) (U := 3.46658) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e1 := Ioo_enclosure (k := 3.46) (a := 0.9994) (b := 1.001) (by norm_num) 30 (by norm_num)
    (by emp) (by emp)
  have := tail_lt (z := pooledZ 9 20 2.1 35) (k := 3.46) (a := 0.9994) (by norm_num)
    (by linarith [hz.1]) e1.1
  exact ⟨hz, by linarith⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 10.16. Sugar in two soft drinks: beverage A
(`13` cans, mean `36`, standard deviation `0.6`) and B (`6` cans, mean `38`, standard deviation `0.8`); the
standard deviations are sample values, so the Welch `t` statistic applies. The statistic for `B - A` lies
strictly between `5.45628` and `5.45629`, and the degrees of freedom strictly between `7.71` and `7.72`. -/
@[kb "openstaxintrostats2e" "Exercise 10.16, p. 550"]
theorem ex_10_16_soft_drink_sugar :
    (5.45628 < welchT 38 36 (0.8 ^ 2) (0.6 ^ 2) 6 13 ∧ welchT 38 36 (0.8 ^ 2) (0.6 ^ 2) 6 13 < 5.45629) ∧
      (7.71 < welchDF (0.8 ^ 2) (0.6 ^ 2) 6 13 ∧ welchDF (0.8 ^ 2) (0.6 ^ 2) 6 13 < 7.72) := by
  have e : welchT 38 36 (0.8 ^ 2) (0.6 ^ 2) 6 13 = 2 / √(64 / 100 / 6 + 36 / 100 / 13) := by
    unfold welchT; norm_num
  have hz := pos_bounds (c := 2) (x := 64 / 100 / 6 + 36 / 100 / 13) (a := 0.3665500) (b := 0.3665501)
    (L := 5.45628) (U := 5.45629) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  rw [e]
  refine ⟨hz, ?_, ?_⟩
  · unfold welchDF; norm_num
  · unfold welchDF; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 10.18. The one-tailed test of exercise 10.16
(B has more sugar): the statistic for `B - A` is positive, in the direction of the alternative, and exceeds
the right-tail `5%` critical value `1.895` of a standard `t` table (`7` degrees of freedom, a table value,
not proved). -/
@[kb "openstaxintrostats2e" "Exercise 10.18, p. 550"]
theorem ex_10_18_soft_drink_one_tailed :
    0 < welchT 38 36 (0.8 ^ 2) (0.6 ^ 2) 6 13 ∧ 1.895 < welchT 38 36 (0.8 ^ 2) (0.6 ^ 2) 6 13 := by
  have e : welchT 38 36 (0.8 ^ 2) (0.6 ^ 2) 6 13 = 2 / √(64 / 100 / 6 + 36 / 100 / 13) := by
    unfold welchT; norm_num
  have hz := pos_bounds (c := 2) (x := 64 / 100 / 6 + 36 / 100 / 13) (a := 0.3665500) (b := 0.3665501)
    (L := 5.45628) (U := 5.45629) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  rw [e]
  exact ⟨by linarith [hz.1], by linarith [hz.1]⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 10.26. Life spans in a county: `124` White people
(mean `45.3`, standard deviation `12.7`) against `82` non-White people (mean `34.1`, standard deviation
`15.6`), two-sided. The Welch statistic lies strictly between `5.42099` and `5.421`, the degrees of freedom
strictly between `148.74` and `148.75`. -/
@[kb "openstaxintrostats2e" "Exercise 10.26, p. 551"]
theorem ex_10_26_life_span_statistic :
    (5.42099 < welchT 45.3 34.1 (12.7 ^ 2) (15.6 ^ 2) 124 82 ∧
        welchT 45.3 34.1 (12.7 ^ 2) (15.6 ^ 2) 124 82 < 5.421) ∧
      (148.74 < welchDF (12.7 ^ 2) (15.6 ^ 2) 124 82 ∧ welchDF (12.7 ^ 2) (15.6 ^ 2) 124 82 < 148.75) := by
  have e : welchT 45.3 34.1 (12.7 ^ 2) (15.6 ^ 2) 124 82 =
      (56 / 5) / √(12.7 ^ 2 / 124 + 15.6 ^ 2 / 82) := by
    unfold welchT; norm_num
  have hz := pos_bounds (c := 56 / 5) (x := 12.7 ^ 2 / 124 + 15.6 ^ 2 / 82) (a := 2.0660422)
    (b := 2.0660423) (L := 5.42099) (U := 5.421) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  rw [e]
  refine ⟨hz, ?_, ?_⟩
  · unfold welchDF; norm_num
  · unfold welchDF; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 10.28. The Student `t` `p`-value of the life-span
comparison (`148` degrees of freedom) is not computable here. What is proved: the statistic of exercise 10.26
exceeds `5.42` and hence the two-sided `5%` critical value `1.98` of a standard `t` table (`120` degrees of
freedom row, a table value, not proved), so the `p`-value is below `0.05`; and the statistic is far beyond the
normal `0.1%` critical value `3.29` as well (`3.29 < 5.42`). -/
@[kb "openstaxintrostats2e" "Exercise 10.28, p. 551"]
theorem ex_10_28_life_span_p_value :
    5.42 < welchT 45.3 34.1 (12.7 ^ 2) (15.6 ^ 2) 124 82 ∧
      1.98 < |welchT 45.3 34.1 (12.7 ^ 2) (15.6 ^ 2) 124 82| ∧
      (3.29 : ℝ) < 5.42 := by
  have e : welchT 45.3 34.1 (12.7 ^ 2) (15.6 ^ 2) 124 82 =
      (56 / 5) / √(12.7 ^ 2 / 124 + 15.6 ^ 2 / 82) := by
    unfold welchT; norm_num
  have hz := pos_bounds (c := 56 / 5) (x := 12.7 ^ 2 / 124 + 15.6 ^ 2 / 82) (a := 2.0660422)
    (b := 2.0660423) (L := 5.42099) (U := 5.421) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  rw [e]
  refine ⟨by linarith [hz.1], ?_, by norm_num⟩
  rw [abs_of_pos (by linarith [hz.1])]; linarith [hz.1]

/-- OpenStax Introductory Statistics 2e Practice exercise 10.29. Decision at `α = 0.05` for the life-span
comparison: the absolute value of the Welch statistic exceeds the two-sided `5%` critical value `1.98` of a
standard `t` table (a table value, not proved), so the null hypothesis of equal means is rejected. -/
@[kb "openstaxintrostats2e" "Exercise 10.29, p. 551"]
theorem ex_10_29_life_span_decision :
    1.98 < |welchT 45.3 34.1 (12.7 ^ 2) (15.6 ^ 2) 124 82| := (ex_10_28_life_span_p_value).2.1

/-- OpenStax Introductory Statistics 2e Practice exercise 10.30. Do the mean life spans look the same? The
sample difference is exactly `11.2` years, and the `95%` interval `11.2 ± 1.98 · SE` (with the table value
`1.98`, not proved) has endpoints strictly between `7.109` and `7.110` and between `15.290` and `15.292`,
so it excludes `0`: the means do not appear to be equal. -/
@[kb "openstaxintrostats2e" "Exercise 10.30, p. 551"]
theorem ex_10_30_life_span_interval :
    (45.3 : ℝ) - 34.1 = 11.2 ∧
      (7.109 < 11.2 - 1.98 * √(12.7 ^ 2 / 124 + 15.6 ^ 2 / 82) ∧
        11.2 - 1.98 * √(12.7 ^ 2 / 124 + 15.6 ^ 2 / 82) < 7.110) ∧
      (15.290 < 11.2 + 1.98 * √(12.7 ^ 2 / 124 + 15.6 ^ 2 / 82) ∧
        11.2 + 1.98 * √(12.7 ^ 2 / 124 + 15.6 ^ 2 / 82) < 15.292) := by
  have s1 : (2.0660422 : ℝ) < √(12.7 ^ 2 / 124 + 15.6 ^ 2 / 82) :=
    (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have s2 : √(12.7 ^ 2 / 124 + 15.6 ^ 2 / 82) < (2.0660423 : ℝ) :=
    (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  refine ⟨by norm_num, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-! ### Section 10.2: two means, known standard deviations -/

/-- OpenStax Introductory Statistics 2e Practice exercise 10.33. Fastball speeds, `14` pitches each: Wesley
(mean `86`, population standard deviation `3`) and Rodriguez (mean `91`, standard deviation `7`). The `z`
statistic for `Wesley - Rodriguez` lies strictly between `-2.45652` and `-2.45651` (about `-2.46`). -/
@[kb "openstaxintrostats2e" "Exercise 10.33, p. 551"]
theorem ex_10_33_fastball_statistic :
    -2.45652 < welchT 86 91 (3 ^ 2) (7 ^ 2) 14 14 ∧ welchT 86 91 (3 ^ 2) (7 ^ 2) 14 14 < -2.45651 := by
  have e : welchT 86 91 (3 ^ 2) (7 ^ 2) 14 14 = (-5) / √(9 / 14 + 49 / 14) := by
    unfold welchT; norm_num
  rw [e]
  exact neg_bounds (c := -5) (x := 9 / 14 + 49 / 14) (a := 2.0354009) (b := 2.035401) (L := -2.45652)
    (U := -2.45651) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- OpenStax Introductory Statistics 2e Practice exercise 10.34. The left-tail `p`-value `Φ(z)` of the
fastball comparison lies strictly between `0.0069` and `0.0071` (about `0.007`). -/
@[kb "openstaxintrostats2e" "Exercise 10.34, p. 551"]
theorem ex_10_34_fastball_p_value :
    0.0069 < Φ (welchT 86 91 (3 ^ 2) (7 ^ 2) 14 14) ∧ Φ (welchT 86 91 (3 ^ 2) (7 ^ 2) 14 14) < 0.0071 := by
  have hz := ex_10_33_fastball_statistic
  have e1 := Ioo_enclosure (k := 2.45651) (a := 0.9858) (b := 0.9861) (by norm_num) 14 (by norm_num)
    (by emp) (by emp)
  have e2 := Ioo_enclosure (k := 2.45652) (a := 0.9858) (b := 0.9861) (by norm_num) 14 (by norm_num)
    (by emp) (by emp)
  have := two_sided_neg (L := 2.45651) (U := 2.45652) (a := 0.9858) (b := 0.9861) (by norm_num)
    ⟨hz.1, hz.2⟩ e1.1 e2.2
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 10.35. At the `1%` level the left-tail `p`-value
`Φ(z)` of the fastball comparison is below `0.0071`, hence below `0.01`: reject, Rodriguez's mean speed is
higher. -/
@[kb "openstaxintrostats2e" "Exercise 10.35, p. 551"]
theorem ex_10_35_fastball_conclusion :
    Φ (welchT 86 91 (3 ^ 2) (7 ^ 2) 14 14) < 0.01 := by
  have := ex_10_34_fastball_p_value
  linarith [this.2]

/-- OpenStax Introductory Statistics 2e Practice exercise 10.38. Plant food, `9` plants per group: food
(mean `16`, standard deviation `2.5`) against no food (mean `14`, standard deviation `1.5`), known standard
deviations, right-tailed. The `z` statistic lies strictly between `2.05798` and `2.05799` and the right-tail
`p`-value strictly between `0.0197` and `0.0199`. -/
@[kb "openstaxintrostats2e" "Exercise 10.38, p. 551"]
theorem ex_10_38_plant_food :
    (2.05798 < welchT 16 14 (2.5 ^ 2) (1.5 ^ 2) 9 9 ∧ welchT 16 14 (2.5 ^ 2) (1.5 ^ 2) 9 9 < 2.05799) ∧
      (0.0197 < 1 - Φ (welchT 16 14 (2.5 ^ 2) (1.5 ^ 2) 9 9) ∧
        1 - Φ (welchT 16 14 (2.5 ^ 2) (1.5 ^ 2) 9 9) < 0.0199) := by
  have e : welchT 16 14 (2.5 ^ 2) (1.5 ^ 2) 9 9 = 2 / √(2.5 ^ 2 / 9 + 1.5 ^ 2 / 9) := by
    unfold welchT; norm_num
  have hz : 2.05798 < welchT 16 14 (2.5 ^ 2) (1.5 ^ 2) 9 9 ∧ welchT 16 14 (2.5 ^ 2) (1.5 ^ 2) 9 9 < 2.05799 := by
    rw [e]
    exact pos_bounds (c := 2) (x := 2.5 ^ 2 / 9 + 1.5 ^ 2 / 9) (a := 0.9718253) (b := 0.9718254)
      (L := 2.05798) (U := 2.05799) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  have e1 := Ioo_enclosure (k := 2.05798) (a := 0.9602) (b := 0.9606) (by norm_num) 14 (by norm_num)
    (by emp) (by emp)
  have e2 := Ioo_enclosure (k := 2.05799) (a := 0.9602) (b := 0.9606) (by norm_num) 14 (by norm_num)
    (by emp) (by emp)
  have := two_sided_pos (L := 2.05798) (U := 2.05799) (a := 0.9602) (b := 0.9606) (by norm_num) hz
    e1.1 e2.2
  exact ⟨hz, by linarith [this.1], by linarith [this.2]⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 10.40. At the `1%` level the right-tail `p`-value
of the plant-food comparison is above `0.0197`, hence above `0.01`: do not reject, there is not enough
evidence that the food makes the plants taller. -/
@[kb "openstaxintrostats2e" "Exercise 10.40, p. 551"]
theorem ex_10_40_plant_food_conclusion :
    0.01 < 1 - Φ (welchT 16 14 (2.5 ^ 2) (1.5 ^ 2) 9 9) := by
  have := ex_10_38_plant_food
  linarith [this.2.1]

/-- OpenStax Introductory Statistics 2e Practice exercise 10.43. Melting points, `15` pieces each: alloy
Gamma (mean `800`, standard deviation `95`) against Zeta (mean `900`, standard deviation `105`), known
standard deviations, two-sided. The `z` statistic lies strictly between `-2.7352` and `-2.73519` and the
two-sided `p`-value `2 Φ(z)` strictly between `0.0061` and `0.0064` (about `0.0062`). -/
@[kb "openstaxintrostats2e" "Exercise 10.43, p. 552"]
theorem ex_10_43_alloys :
    (-2.7352 < welchT 800 900 (95 ^ 2) (105 ^ 2) 15 15 ∧ welchT 800 900 (95 ^ 2) (105 ^ 2) 15 15 < -2.73519) ∧
      (0.0061 < 2 * Φ (welchT 800 900 (95 ^ 2) (105 ^ 2) 15 15) ∧
        2 * Φ (welchT 800 900 (95 ^ 2) (105 ^ 2) 15 15) < 0.0064) := by
  have e : welchT 800 900 (95 ^ 2) (105 ^ 2) 15 15 = (-100) / √(95 ^ 2 / 15 + 105 ^ 2 / 15) := by
    unfold welchT; norm_num
  have hz : -2.7352 < welchT 800 900 (95 ^ 2) (105 ^ 2) 15 15 ∧ welchT 800 900 (95 ^ 2) (105 ^ 2) 15 15 < -2.73519 := by
    rw [e]
    exact neg_bounds (c := -100) (x := 95 ^ 2 / 15 + 105 ^ 2 / 15) (a := 36.5604522) (b := 36.5604523)
      (L := -2.7352) (U := -2.73519) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  have e1 := Ioo_enclosure (k := 2.73519) (a := 0.9936) (b := 0.9939) (by norm_num) 14 (by norm_num)
    (by emp) (by emp)
  have e2 := Ioo_enclosure (k := 2.7352) (a := 0.9936) (b := 0.9939) (by norm_num) 14 (by norm_num)
    (by emp) (by emp)
  have := two_sided_neg (L := 2.73519) (U := 2.7352) (a := 0.9936) (b := 0.9939) (by norm_num)
    ⟨hz.1, hz.2⟩ e1.1 e2.2
  exact ⟨hz, by linarith [this.1], by linarith [this.2]⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 10.45. At the `1%` level the two-sided `p`-value of
the alloy comparison is below `0.0064`, hence below `0.01`: reject, the melting points differ. -/
@[kb "openstaxintrostats2e" "Exercise 10.45, p. 552"]
theorem ex_10_45_alloys_conclusion :
    2 * Φ (welchT 800 900 (95 ^ 2) (105 ^ 2) 15 15) < 0.01 := by
  have := ex_10_43_alloys
  linarith [this.2.2]

/-! ### Section 10.3: two proportions -/

/-- OpenStax Introductory Statistics 2e Practice exercise 10.49. Phone operating systems: `15` of `150`
crashes with OS1 against `9` of `150` with OS2, right-tailed (OS1 crashes more). The pooled `z` statistic
lies strictly between `1.27688` and `1.27689` and the right-tail `p`-value strictly between `0.1007` and
`0.1009`. (The book's printed value `0.1018` is slightly off; the value computed here is about `0.1008`.) -/
@[kb "openstaxintrostats2e" "Exercise 10.49, p. 552"]
theorem ex_10_49_operating_systems :
    (1.27688 < pooledZ 15 150 9 150 ∧ pooledZ 15 150 9 150 < 1.27689) ∧
      (0.1007 < 1 - Φ (pooledZ 15 150 9 150) ∧ 1 - Φ (pooledZ 15 150 9 150) < 0.1009) := by
  have e : pooledZ 15 150 9 150 = (15 / 150 - 9 / 150) /
      √((24 / 300) * (1 - 24 / 300) * (1 / 150 + 1 / 150)) := by
    unfold pooledZ; norm_num
  have hz : 1.27688 < pooledZ 15 150 9 150 ∧ pooledZ 15 150 9 150 < 1.27689 := by
    rw [e]
    exact pos_bounds (c := 15 / 150 - 9 / 150) (x := (24 / 300) * (1 - 24 / 300) * (1 / 150 + 1 / 150))
      (a := 0.0313262) (b := 0.0313263) (L := 1.27688) (U := 1.27689) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e1 := Ioo_enclosure (k := 1.27688) (a := 0.7982) (b := 0.7985) (by norm_num) 10 (by norm_num)
    (by emp) (by emp)
  have e2 := Ioo_enclosure (k := 1.27689) (a := 0.7982) (b := 0.7985) (by norm_num) 10 (by norm_num)
    (by emp) (by emp)
  have := two_sided_pos (L := 1.27688) (U := 1.27689) (a := 0.7982) (b := 0.7985) (by norm_num) hz
    e1.1 e2.2
  exact ⟨hz, by linarith [this.1], by linarith [this.2]⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 10.50. Conclusion about the two operating systems:
the right-tail `p`-value of exercise 10.49 is above `0.1`, so the null hypothesis of equal crash proportions
is not rejected at any of the usual levels `1%`, `5%`, `10%`: no evidence that OS2 is more stable. -/
@[kb "openstaxintrostats2e" "Exercise 10.50, p. 552"]
theorem ex_10_50_operating_systems_conclusion :
    0.1 < 1 - Φ (pooledZ 15 150 9 150) := by
  have := ex_10_49_operating_systems
  linarith [this.2.1]

/-- OpenStax Introductory Statistics 2e Practice exercise 10.57. The normal approximation for two proportions
is justified for the two-race survey: the counts of "yes" and "no" answers in both samples (`9` and `991` of
`1000` North Dakotans, `17` and `483` of `500` Nevadans) are all at least `5`. -/
@[kb "openstaxintrostats2e" "Exercise 10.57, p. 552"]
theorem ex_10_57_two_races_counts :
    (5 : ℝ) ≤ 9 ∧ (5 : ℝ) ≤ 1000 - 9 ∧ (5 : ℝ) ≤ 17 ∧ (5 : ℝ) ≤ 500 - 17 := by
  norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 10.58. Test statistic for the two-race survey:
`17` of `500` Nevadans against `9` of `1000` North Dakotans (pooled proportion `26/1500`). The pooled `z`
statistic lies strictly between `3.49731` and `3.49732`. -/
@[kb "openstaxintrostats2e" "Exercise 10.58, p. 552"]
theorem ex_10_58_two_races_statistic :
    3.49731 < pooledZ 17 500 9 1000 ∧ pooledZ 17 500 9 1000 < 3.49732 := by
  have e : pooledZ 17 500 9 1000 = (17 / 500 - 9 / 1000) /
      √((26 / 1500) * (1 - 26 / 1500) * (1 / 500 + 1 / 1000)) := by
    unfold pooledZ; norm_num
  rw [e]
  exact pos_bounds (c := 17 / 500 - 9 / 1000) (x := (26 / 1500) * (1 - 26 / 1500) * (1 / 500 + 1 / 1000))
    (a := 0.007148333) (b := 0.007148334) (L := 3.49731) (U := 3.49732) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- OpenStax Introductory Statistics 2e Practice exercise 10.60. The right-tail `p`-value of the two-race
survey (statistic above `3.49`) is below `0.0003` (the exact value is about `0.000235`). -/
@[kb "openstaxintrostats2e" "Exercise 10.60, p. 553"]
theorem ex_10_60_two_races_p_value :
    1 - Φ (pooledZ 17 500 9 1000) < 0.0003 := by
  have hz := ex_10_58_two_races_statistic
  have e1 := Ioo_enclosure (k := 3.49) (a := 0.9994) (b := 1.001) (by norm_num) 30 (by norm_num)
    (by emp) (by emp)
  have := tail_lt (z := pooledZ 17 500 9 1000) (k := 3.49) (a := 0.9994) (by norm_num)
    (by linarith [hz.1]) e1.1
  linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 10.61. Decision at `α = 0.05` for the two-race
survey: the right-tail `p`-value is below `0.0003`, hence below `0.05`: reject the null hypothesis of equal
proportions. -/
@[kb "openstaxintrostats2e" "Exercise 10.61, p. 553"]
theorem ex_10_61_two_races_decision :
    1 - Φ (pooledZ 17 500 9 1000) < 0.05 := by
  have := ex_10_60_two_races_p_value
  linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 10.62. The sample proportion of Nevadans (`17/500 =
0.034`) exceeds that of North Dakotans (`9/1000 = 0.009`), and the evidence is significant: the right-tail
`p`-value is below `0.0003`, below every usual level. -/
@[kb "openstaxintrostats2e" "Exercise 10.62, p. 553"]
theorem ex_10_62_two_races_higher :
    (17 / 500 : ℝ) = 0.034 ∧ (9 / 1000 : ℝ) = 0.009 ∧ (9 / 1000 : ℝ) < 17 / 500 ∧
      1 - Φ (pooledZ 17 500 9 1000) < 0.0003 :=
  ⟨by norm_num, by norm_num, by norm_num, ex_10_60_two_races_p_value⟩

/-! ### Section 10.4: matched pairs -/

private lemma sqrt_div_eq {x r : ℝ} (hr : 0 ≤ r) (h : x = r ^ 2) : √x = r := sqrt_eq hr h

/-- "After minus before" system failures of exercise 10.63. -/
noncomputable def patchDiff : Fin 8 → ℝ := ![1, 5, 2, 0, 1, 0, 2, 2] - ![3, 6, 4, 2, 5, 8, 2, 6]

private lemma patchDiff_mean : mean patchDiff = -23 / 8 := by
  simp [mean, patchDiff, Fin.sum_univ_succ]; norm_num

private lemma patchDiff_var : sampleVariance patchDiff = 49 / 8 := by
  rw [sampleVariance, sumSqDev, patchDiff_mean]; simp [patchDiff, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 10.65. Software patch, `8` installations. The
after-minus-before differences are `-2, -1, -2, -2, -4, -8, 0, -4`, with mean `-23/8`, sample variance
`49/8` and paired `t` statistic exactly `-23/7` (about `-3.29`) on `7` degrees of freedom. The statistic is
below the left-tail `1%` critical value `-2.998` of a standard `t` table (a table value, not proved), which
is the content of the book's `p`-value `0.0067 < 0.01`: reject. -/
@[kb "openstaxintrostats2e" "Exercise 10.65, p. 553"]
theorem ex_10_65_software_patch :
    patchDiff = ![-2, -1, -2, -2, -4, -8, 0, -4] ∧ mean patchDiff = -23 / 8 ∧
      sampleVariance patchDiff = 49 / 8 ∧ pairedT patchDiff = -23 / 7 ∧ pairedT patchDiff < -2.998 := by
  have e : pairedT patchDiff = -23 / 7 := by
    unfold pairedT; rw [patchDiff_mean, patchDiff_var]
    have h : √((49 / 8 : ℝ) / ((8 : ℕ) : ℝ)) = 7 / 8 := by
      apply sqrt_eq (by norm_num); norm_num
    rw [h]; norm_num
  refine ⟨?_, patchDiff_mean, patchDiff_var, e, by rw [e]; norm_num⟩
  funext i
  fin_cases i <;> simp [patchDiff] <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 10.67. Conclusion about the software patch: the
paired statistic `-23/7` is below the left-tail `1%` critical value `-2.998` (`7` degrees of freedom, a table
value, not proved), so the null hypothesis of no reduction is rejected: the patch reduces system failures. -/
@[kb "openstaxintrostats2e" "Exercise 10.67, p. 553"]
theorem ex_10_67_software_patch_conclusion :
    pairedT patchDiff < -2.998 := (ex_10_65_software_patch).2.2.2.2

/-- "After minus before" juggled balls of exercise 10.68. -/
noncomputable def jugDiff : Fin 6 → ℝ := ![4, 5, 6, 4, 5, 7] - ![3, 4, 3, 2, 4, 5]

private lemma jugDiff_mean : mean jugDiff = 5 / 3 := by
  simp [mean, jugDiff, Fin.sum_univ_succ]; norm_num

private lemma jugDiff_var : sampleVariance jugDiff = 2 / 3 := by
  rw [sampleVariance, sumSqDev, jugDiff_mean]; simp [jugDiff, Fin.sum_univ_succ]; norm_num

private lemma jugDiff_t : pairedT jugDiff = 5 := by
  unfold pairedT; rw [jugDiff_mean, jugDiff_var]
  have h : √((2 / 3 : ℝ) / ((6 : ℕ) : ℝ)) = 1 / 3 := by
    apply sqrt_eq (by norm_num); norm_num
  rw [h]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 10.69. Juggling class, `6` subjects. The
after-minus-before differences are `1, 1, 3, 2, 1, 2`, with sample variance `2/3`, and the paired `t`
statistic is exactly `5` on `5` degrees of freedom. It exceeds the right-tail `1%` critical value `3.365` of a
standard `t` table (a table value, not proved), which is the content of the book's `p`-value `0.0021 < 0.01`:
reject. -/
@[kb "openstaxintrostats2e" "Exercise 10.69, p. 553"]
theorem ex_10_69_juggling_class :
    jugDiff = ![1, 1, 3, 2, 1, 2] ∧ sampleVariance jugDiff = 2 / 3 ∧ pairedT jugDiff = 5 ∧
      3.365 < pairedT jugDiff := by
  refine ⟨?_, jugDiff_var, jugDiff_t, by rw [jugDiff_t]; norm_num⟩
  funext i
  fin_cases i <;> simp [jugDiff] <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 10.70. The sample mean of the after-minus-before
differences in the juggling class is exactly `5/3`. -/
@[kb "openstaxintrostats2e" "Exercise 10.70, p. 553"]
theorem ex_10_70_juggling_mean_difference :
    mean jugDiff = 5 / 3 := jugDiff_mean

/-- OpenStax Introductory Statistics 2e Practice exercise 10.72. Conclusion about the juggling class: the
paired statistic `5` exceeds the right-tail `1%` critical value `3.365` of a standard `t` table (`5` degrees
of freedom, a table value, not proved), so the null hypothesis of no improvement is rejected: the class
increases the number of balls juggled. -/
@[kb "openstaxintrostats2e" "Exercise 10.72, p. 554"]
theorem ex_10_72_juggling_conclusion :
    3.365 < pairedT jugDiff := (ex_10_69_juggling_class).2.2.2

/-- "After minus before" systolic pressures of exercise 10.73. -/
noncomputable def bpDiff : Fin 6 → ℝ := ![158, 159, 166, 160, 167, 169] - ![161, 162, 165, 162, 166, 171]

private lemma bpDiff_mean : mean bpDiff = -4 / 3 := by
  simp [mean, bpDiff, Fin.sum_univ_succ]; norm_num

private lemma bpDiff_var : sampleVariance bpDiff = 52 / 15 := by
  rw [sampleVariance, sumSqDev, bpDiff_mean]; simp [bpDiff, Fin.sum_univ_succ]; norm_num

private lemma bpDiff_t : -1.75412 < pairedT bpDiff ∧ pairedT bpDiff < -1.75411 := by
  have e : pairedT bpDiff = (-4 / 3) / √(52 / 15 / 6) := by
    unfold pairedT; rw [bpDiff_mean, bpDiff_var]; norm_num
  rw [e]
  exact neg_bounds (c := -4 / 3) (x := 52 / 15 / 6) (a := 0.7601169) (b := 0.760117) (L := -1.75412)
    (U := -1.75411) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- OpenStax Introductory Statistics 2e Practice exercise 10.74. Blood pressure medication, `6` patients.
The after-minus-before differences are `-3, -3, 1, -2, 1, -2`, with sample variance `52/15`; the paired `t`
statistic (`5` degrees of freedom) lies strictly between `-1.75412` and `-1.75411`. -/
@[kb "openstaxintrostats2e" "Exercise 10.74, p. 554"]
theorem ex_10_74_blood_pressure_statistic :
    bpDiff = ![-3, -3, 1, -2, 1, -2] ∧ sampleVariance bpDiff = 52 / 15 ∧
      (-1.75412 < pairedT bpDiff ∧ pairedT bpDiff < -1.75411) := by
  refine ⟨?_, bpDiff_var, bpDiff_t⟩
  funext i
  fin_cases i <;> simp [bpDiff] <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 10.76. The sample mean of the after-minus-before
systolic differences is exactly `-4/3`. -/
@[kb "openstaxintrostats2e" "Exercise 10.76, p. 554"]
theorem ex_10_76_blood_pressure_mean_difference :
    mean bpDiff = -4 / 3 := bpDiff_mean

/-- OpenStax Introductory Statistics 2e Practice exercise 10.77. Conclusion at the `1%` level: the paired
statistic is above the left-tail `1%` critical value `-3.365` of a standard `t` table (`5` degrees of
freedom, a table value, not proved), which is the content of the book's `p`-value `0.0699 > 0.01`: do not
reject, there is no sufficient evidence that the medication lowers blood pressure. -/
@[kb "openstaxintrostats2e" "Exercise 10.77, p. 554"]
theorem ex_10_77_blood_pressure_conclusion :
    -3.365 < pairedT bpDiff := by
  have := bpDiff_t
  linarith [this.1]

end UndergradKB.Statistics.Course.PracticeC10
