import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Data
import UndergradKB.Statistics.CriticalValues
import UndergradKB.Statistics.Course.TryItC8

/-!
# Course layer, chapter 8 (OpenStax *Introductory Statistics 2e*): Practice exercises

End-of-chapter Practice exercises 8.1 to 8.94 on confidence intervals. The critical values `1.645`,
`1.96`, `2.576` are proved to cut off the stated central mass of the standard normal law, and the other
`z` values used (`0.8225`, `1.751`, `2.326`) are enclosed in the same way. Student `t` values are the
standard table constants, named in the statements and not proved. Margins of error and interval
endpoints are two-sided bounds around the rounded values; sample sizes are exact least naturals.
-/

namespace UndergradKB.Statistics.Course.PracticeC8

open UndergradKB.Statistics MeasureTheory ProbabilityTheory Set
open UndergradKB.Statistics.Course.TryItC8 (centralMass)

private lemma sqrt_bd {n lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 < hi) (h1 : lo ^ 2 < n)
    (h2 : n < hi ^ 2) : lo < √n ∧ √n < hi :=
  ⟨(Real.lt_sqrt hlo.le).2 h1, (Real.sqrt_lt' hhi).2 h2⟩

/-- Bounds on `z * (s / √n)` from bounds on `s` and on `√n`. -/
private lemma zebm {z s sl sh n lo hi a b : ℝ} (hz : 0 < z) (hsl0 : 0 < sl) (hsl : sl ≤ s)
    (hsh : s ≤ sh) (hlo : 0 < lo) (hhi : 0 < hi) (h1 : lo ^ 2 < n) (h2 : n < hi ^ 2)
    (ha : a ≤ z * sl / hi) (hb : z * sh / lo ≤ b) : a < z * (s / √n) ∧ z * (s / √n) < b := by
  obtain ⟨l, h⟩ := sqrt_bd hlo hhi h1 h2
  have hp : 0 < √n := by linarith
  have hs : 0 < s := by linarith
  have e : z * (s / √n) = z * s / √n := by ring
  rw [e]
  have k1 : z * sl * √n ≤ z * s * √n := by gcongr
  have k2 : z * s * √n < z * s * hi := by gcongr
  have k3 : z * s * lo < z * s * √n := by gcongr
  have k4 : z * s * √n ≤ z * sh * √n := by gcongr
  constructor
  · calc a ≤ z * sl / hi := ha
      _ < z * s / √n := by rw [div_lt_div_iff₀ hhi hp]; linarith
  · calc z * s / √n < z * sh / lo := by rw [div_lt_div_iff₀ hp hlo]; linarith
      _ ≤ b := hb

/-- Bounds on `s / √n`. -/
private lemma sdiv {s sl sh n lo hi a b : ℝ} (hsl0 : 0 < sl) (hsl : sl ≤ s)
    (hsh : s ≤ sh) (hlo : 0 < lo) (hhi : 0 < hi) (h1 : lo ^ 2 < n) (h2 : n < hi ^ 2)
    (ha : a ≤ sl / hi) (hb : sh / lo ≤ b) : a < s / √n ∧ s / √n < b := by
  have := zebm (z := 1) (s := s) (sl := sl) (sh := sh) (n := n) (lo := lo) (hi := hi) (a := a)
    (b := b) one_pos hsl0 hsl hsh hlo hhi h1 h2 (by simpa using ha) (by simpa using hb)
  simpa using this

/-- Bounds on `z * √v`. -/
private lemma zsqrt {z v lo hi a b : ℝ} (hz : 0 < z) (hlo : 0 < lo) (hhi : 0 < hi)
    (h1 : lo ^ 2 < v) (h2 : v < hi ^ 2) (ha : a ≤ z * lo) (hb : z * hi ≤ b) :
    a < z * √v ∧ z * √v < b := by
  obtain ⟨l, h⟩ := sqrt_bd hlo hhi h1 h2
  constructor <;> nlinarith

private lemma centralMass_mono {z w : ℝ} (h : z ≤ w) : centralMass z ≤ centralMass w := by
  unfold centralMass
  exact measureReal_mono (Ioo_subset_Ioo (by linarith) h)

private lemma sqrt25 : √(25 : ℝ) = 5 := by
  rw [show (25 : ℝ) = 5 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)

/-- Table 8.10 of the book (colours on 39 flags) as a list of 39 values. -/
noncomputable def flagsX : Fin 39 → ℝ :=
  ![1, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4,
    5, 5, 5, 5, 5, 5]

private lemma flags_mean : mean flagsX = 127 / 39 := by
  simp [mean, flagsX, Fin.sum_univ_succ]; norm_num

private lemma flags_var : sampleVariance flagsX = 769 / 741 := by
  simp only [sampleVariance, sumSqDev, flags_mean]
  simp [flagsX, Fin.sum_univ_succ]
  norm_num

private lemma flags_sd : (1.0187 : ℝ) < sampleStdDev flagsX ∧ sampleStdDev flagsX < 1.0188 := by
  rw [sampleStdDev, flags_var]
  exact ⟨(Real.lt_sqrt (by norm_num)).2 (by norm_num), (Real.sqrt_lt' (by norm_num)).2 (by norm_num)⟩

/-! ### Section 8.1: mean, known standard deviation (elephant calves, Census short form) -/

/-- OpenStax Introductory Statistics 2e Practice exercise 8.1. Newborn elephant calves: sample mean 244 pounds, known population standard deviation 15, n = 50 (the sample standard deviation 11 plays no role). The standard error 15/sqrt 50 lies in (2.1213, 2.1214). -/
@[kb "openstaxintrostats2e" "Exercise 8.1, p. 446"]
theorem ex_8_1_elephant_parameters :
    2.1213 < (15 : ℝ) / √50 ∧ (15 : ℝ) / √50 < 2.1214 := by
  obtain ⟨h1, h2⟩ := sdiv (s := 15) (sl := 15) (sh := 15) (n := 50) (lo := 7.0710678) (hi := 7.0710680) (a := 2.1213) (b := 2.1214)
    (by norm_num) le_rfl le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h1, h2⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 8.4. Elephant calves, 95% interval for the mean weight from mean 244, sigma 15, n = 50 (critical value 1.96, central standard normal mass in (0.9499, 0.9501)). The margin of error lies in (4.1577, 4.1578), the lower endpoint in (239.8422, 239.8423) and the upper endpoint in (248.1577, 248.1578). -/
@[kb "openstaxintrostats2e" "Exercise 8.4, p. 446"]
theorem ex_8_4_elephant_ci_95 :
    (0.9499 < centralMass 1.96 ∧ centralMass 1.96 < 0.9501) ∧
    let ebm : ℝ := 1.96 * (15 / √50)
    4.1577 < ebm ∧ ebm < 4.1578 ∧ 239.8422 < 244 - ebm ∧ 244 - ebm < 239.8423 ∧
      248.1577 < 244 + ebm ∧ 244 + ebm < 248.1578 := by
  refine ⟨critical_values_standard_normal.2.1, ?_⟩
  intro ebm
  obtain ⟨h1, h2⟩ := zebm (z := 1.96) (s := 15) (sl := 15) (sh := 15) (n := 50) (lo := 7.0710678) (hi := 7.0710680) (a := 4.1577) (b := 4.1578)
    (by norm_num) (by norm_num) le_rfl le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [ebm]
  refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 8.5. Weighing 500 calves instead of 50 (same mean 244, sigma 15, 95%): the margin of error 1.96 * 15/sqrt 500 lies in (1.3148, 1.3149) and is smaller than the margin for n = 50, which lies in (4.1577, 4.1578). -/
@[kb "openstaxintrostats2e" "Exercise 8.5, p. 446"]
theorem ex_8_5_elephant_more_calves_narrower :
    let e500 : ℝ := 1.96 * (15 / √500)
    let e50 : ℝ := 1.96 * (15 / √50)
    1.3148 < e500 ∧ e500 < 1.3149 ∧ 4.1577 < e50 ∧ e50 < 4.1578 ∧ e500 < e50 := by
  intro e500 e50
  obtain ⟨h1, h2⟩ := zebm (z := 1.96) (s := 15) (sl := 15) (sh := 15) (n := 500) (lo := 22.3606797) (hi := 22.3606799) (a := 1.3148) (b := 1.3149)
    (by norm_num) (by norm_num) le_rfl le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨g1, g2⟩ := zebm (z := 1.96) (s := 15) (sl := 15) (sh := 15) (n := 50) (lo := 7.0710678) (hi := 7.0710680) (a := 4.1577) (b := 4.1578)
    (by norm_num) (by norm_num) le_rfl le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [e500, e50]
  refine ⟨h1, h2, g1, g2, ?_⟩
  linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 8.6. Census short form: sample mean 8.2 minutes, known standard deviation 2.2, n = 200. The standard error 2.2/sqrt 200 lies in (0.1555, 0.1556). -/
@[kb "openstaxintrostats2e" "Exercise 8.6, p. 447"]
theorem ex_8_6_census_parameters :
    0.1555 < (2.2 : ℝ) / √200 ∧ (2.2 : ℝ) / √200 < 0.1556 := by
  obtain ⟨h1, h2⟩ := sdiv (s := 2.2) (sl := 2.2) (sh := 2.2) (n := 200) (lo := 14.1421356) (hi := 14.1421358) (a := 0.1555) (b := 0.1556)
    (by norm_num) le_rfl le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h1, h2⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 8.9. Census short form, 90% interval from mean 8.2, sigma 2.2, n = 200 (critical value 1.645, central mass in (0.8999, 0.9001)); the interval is about (7.944, 8.456). The margin of error lies in (0.2559, 0.2560), the lower endpoint in (7.9440, 7.9441) and the upper endpoint in (8.4559, 8.4560). -/
@[kb "openstaxintrostats2e" "Exercise 8.9, p. 447"]
theorem ex_8_9_census_ci_90 :
    (0.8999 < centralMass 1.645 ∧ centralMass 1.645 < 0.9001) ∧
    let ebm : ℝ := 1.645 * (2.2 / √200)
    0.2559 < ebm ∧ ebm < 0.2560 ∧ 7.9440 < 8.2 - ebm ∧ 8.2 - ebm < 7.9441 ∧
      8.4559 < 8.2 + ebm ∧ 8.2 + ebm < 8.4560 := by
  refine ⟨critical_values_standard_normal.1, ?_⟩
  intro ebm
  obtain ⟨h1, h2⟩ := zebm (z := 1.645) (s := 2.2) (sl := 2.2) (sh := 2.2) (n := 200) (lo := 14.1421356) (hi := 14.1421358) (a := 0.2559) (b := 0.2560)
    (by norm_num) (by norm_num) le_rfl le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [ebm]
  refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 8.10. If two surveys give the same margin of error z * 2.2/sqrt n for a mean with sigma 2.2, and the second has the larger critical value (higher confidence), then the second needs the larger sample size. -/
@[kb "openstaxintrostats2e" "Exercise 8.10, p. 447"]
theorem ex_8_10_more_confidence_same_error_needs_more_people :
    ∀ z₁ z₂ n₁ n₂ : ℝ, 0 < z₁ → z₁ < z₂ → 0 < n₁ → 0 < n₂ →
      z₁ * (2.2 / √n₁) = z₂ * (2.2 / √n₂) → n₁ < n₂ := by
  intro z₁ z₂ n₁ n₂ hz hzz hn₁ hn₂ h
  have h1 : 0 < √n₁ := Real.sqrt_pos.2 hn₁
  have h2 : 0 < √n₂ := Real.sqrt_pos.2 hn₂
  have h3 : z₁ * √n₂ = z₂ * √n₁ := by
    field_simp at h; linarith
  have h4 : √n₁ < √n₂ := by
    by_contra hc
    replace hc := not_lt.mp hc
    nlinarith [mul_le_mul_of_nonneg_left hc hz.le, mul_pos (sub_pos.2 hzz) h1]
  exact (Real.sqrt_lt_sqrt_iff hn₁.le).1 h4

/-- OpenStax Introductory Statistics 2e Practice exercise 8.11. Keep the 90% margin of error 1.645 * 2.2/sqrt 200 of the 200-person survey but survey only 50 people: the critical value must then be z = 0.8225 (half of 1.645), whose central normal mass lies in (0.5891, 0.5894), well below 0.9, so the confidence level falls. -/
@[kb "openstaxintrostats2e" "Exercise 8.11, p. 447"]
theorem ex_8_11_census_fifty_people_confidence_drops :
    ∀ z : ℝ, 1.645 * (2.2 / √200) = z * (2.2 / √50) →
      z = 0.8225 ∧ (0.5891 < centralMass z ∧ centralMass z < 0.5894) ∧ centralMass z < 0.8999 := by
  intro z h
  have h200 : √(200 : ℝ) = 2 * √50 := by
    rw [show (200 : ℝ) = 2 ^ 2 * 50 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have hp : 0 < √(50 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hz : z = 0.8225 := by
    have : z * (2.2 / √50) = 0.8225 * (2.2 / √50) := by
      rw [← h, h200]; field_simp; norm_num
    exact mul_right_cancel₀ (by positivity) this
  subst hz
  have hl : (0.5891 < centralMass 0.8225 ∧ centralMass 0.8225 < 0.5894) :=
    Ioo_enclosure (k := 0.8225) (a := 0.5891) (b := 0.5894) (by norm_num) 14 (by norm_num)
      (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
      (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
  exact ⟨rfl, hl, by linarith [hl.2]⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 8.12. Census at 98% confidence (critical value 2.326, central mass in (0.9798, 0.9801)): with n = 200 the margin of error lies in (0.3618, 0.3619), above the 90% margin in (0.2559, 0.2560). Holding the error at the 90% value requires n >= 200 (2.326/1.645)^2, about 399.87, so the least sample size is 400, more than 200. -/
@[kb "openstaxintrostats2e" "Exercise 8.12, p. 447"]
theorem ex_8_12_census_98_percent_needs_more_people :
    (0.9798 < centralMass 2.326 ∧ centralMass 2.326 < 0.9801) ∧
    (let e98 : ℝ := 2.326 * (2.2 / √200)
     let e90 : ℝ := 1.645 * (2.2 / √200)
     0.3618 < e98 ∧ e98 < 0.3619 ∧ 0.2559 < e90 ∧ e90 < 0.2560 ∧ e90 < e98) ∧
    IsLeast {n : ℕ | 200 * (2.326 / 1.645 : ℝ) ^ 2 ≤ n} 400 := by
  refine ⟨Ioo_enclosure (k := 2.326) (a := 0.9798) (b := 0.9801) (by norm_num) 14 (by norm_num)
      (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
      (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial]), ?_, ?_, ?_⟩
  · intro e98 e90
    obtain ⟨h1, h2⟩ := zebm (z := 2.326) (s := 2.2) (sl := 2.2) (sh := 2.2) (n := 200) (lo := 14.1421356) (hi := 14.1421358) (a := 0.3618) (b := 0.3619)
      (by norm_num) (by norm_num) le_rfl le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨g1, g2⟩ := zebm (z := 1.645) (s := 2.2) (sl := 2.2) (sh := 2.2) (n := 200) (lo := 14.1421356) (hi := 14.1421358) (a := 0.2559) (b := 0.2560)
      (by norm_num) (by norm_num) le_rfl le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simp only [e98, e90]
    refine ⟨h1, h2, g1, g2, ?_⟩
    linarith
  · show 200 * (2.326 / 1.645 : ℝ) ^ 2 ≤ ((400 : ℕ) : ℝ)
    norm_num
  · intro n hn
    by_contra h
    have : n ≤ 399 := by omega
    have h2 : (n : ℝ) ≤ 399 := by exact_mod_cast this
    have h3 : 200 * (2.326 / 1.645 : ℝ) ^ 2 ≤ n := hn
    norm_num at h3
    linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 8.13. Heads of lettuce: sample mean 2.2 pounds, known sigma 0.2, n = 20 (the sample standard deviation 0.1 is not used). The standard error 0.2/sqrt 20 lies in (0.0447, 0.0448). -/
@[kb "openstaxintrostats2e" "Exercise 8.13, p. 447"]
theorem ex_8_13_lettuce_parameters :
    0.0447 < (0.2 : ℝ) / √20 ∧ (0.2 : ℝ) / √20 < 0.0448 := by
  obtain ⟨h1, h2⟩ := sdiv (s := 0.2) (sl := 0.2) (sh := 0.2) (n := 20) (lo := 4.4721359) (hi := 4.4721361) (a := 0.0447) (b := 0.0448)
    (by norm_num) le_rfl le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h1, h2⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 8.17. Lettuce, 90% interval from mean 2.2, sigma 0.2, n = 20 (critical value 1.645, central mass in (0.8999, 0.9001)); the interval is about (2.126, 2.274). The margin of error lies in (0.0735, 0.0736), the lower endpoint in (2.1264, 2.1265) and the upper endpoint in (2.2735, 2.2736). -/
@[kb "openstaxintrostats2e" "Exercise 8.17, p. 447"]
theorem ex_8_17_lettuce_ci_90 :
    (0.8999 < centralMass 1.645 ∧ centralMass 1.645 < 0.9001) ∧
    let ebm : ℝ := 1.645 * (0.2 / √20)
    0.0735 < ebm ∧ ebm < 0.0736 ∧ 2.1264 < 2.2 - ebm ∧ 2.2 - ebm < 2.1265 ∧
      2.2735 < 2.2 + ebm ∧ 2.2 + ebm < 2.2736 := by
  refine ⟨critical_values_standard_normal.1, ?_⟩
  intro ebm
  obtain ⟨h1, h2⟩ := zebm (z := 1.645) (s := 0.2) (sl := 0.2) (sh := 0.2) (n := 20) (lo := 4.4721359) (hi := 4.4721361) (a := 0.0735) (b := 0.0736)
    (by norm_num) (by norm_num) le_rfl le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [ebm]
  refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 8.18. Lettuce, 95% interval from mean 2.2, sigma 0.2, n = 20 (critical value 1.96, central mass in (0.9499, 0.9501)); the interval is about (2.112, 2.288). The margin of error lies in (0.0876, 0.0877), the lower endpoint in (2.1123, 2.1124) and the upper endpoint in (2.2876, 2.2877). -/
@[kb "openstaxintrostats2e" "Exercise 8.18, p. 447"]
theorem ex_8_18_lettuce_ci_95 :
    (0.9499 < centralMass 1.96 ∧ centralMass 1.96 < 0.9501) ∧
    let ebm : ℝ := 1.96 * (0.2 / √20)
    0.0876 < ebm ∧ ebm < 0.0877 ∧ 2.1123 < 2.2 - ebm ∧ 2.2 - ebm < 2.1124 ∧
      2.2876 < 2.2 + ebm ∧ 2.2 + ebm < 2.2877 := by
  refine ⟨critical_values_standard_normal.2.1, ?_⟩
  intro ebm
  obtain ⟨h1, h2⟩ := zebm (z := 1.96) (s := 0.2) (sl := 0.2) (sh := 0.2) (n := 20) (lo := 4.4721359) (hi := 4.4721361) (a := 0.0876) (b := 0.0877)
    (by norm_num) (by norm_num) le_rfl le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [ebm]
  refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 8.19. The 95% margin of error 1.96 * 0.2/sqrt 20, in (0.0876, 0.0877), exceeds the 90% margin 1.645 * 0.2/sqrt 20, in (0.0735, 0.0736), so the 95% interval around 2.2 is wider. -/
@[kb "openstaxintrostats2e" "Exercise 8.19, p. 447"]
theorem ex_8_19_lettuce_95_wider_than_90 :
    let e90 : ℝ := 1.645 * (0.2 / √20)
    let e95 : ℝ := 1.96 * (0.2 / √20)
    0.0735 < e90 ∧ e90 < 0.0736 ∧ 0.0876 < e95 ∧ e95 < 0.0877 ∧ e90 < e95 ∧
      2.2 - e95 < 2.2 - e90 ∧ 2.2 + e90 < 2.2 + e95 := by
  intro e90 e95
  obtain ⟨h1, h2⟩ := zebm (z := 1.645) (s := 0.2) (sl := 0.2) (sh := 0.2) (n := 20) (lo := 4.4721359) (hi := 4.4721361) (a := 0.0735) (b := 0.0736)
    (by norm_num) (by norm_num) le_rfl le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨g1, g2⟩ := zebm (z := 1.96) (s := 0.2) (sl := 0.2) (sh := 0.2) (n := 20) (lo := 4.4721359) (hi := 4.4721361) (a := 0.0876) (b := 0.0877)
    (by norm_num) (by norm_num) le_rfl le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [e90, e95]
  refine ⟨h1, h2, g1, g2, ?_, ?_, ?_⟩ <;> linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 8.21. Sample 40 heads instead of 20 but keep the 90% margin 1.645 * 0.2/sqrt 20: the critical value becomes 1.645 * sqrt 2, which is above 2.326, so the confidence level exceeds the central mass of 2.326: it lies above 0.9798 (that mass lies in (0.9798, 0.9801)), far above 0.9. -/
@[kb "openstaxintrostats2e" "Exercise 8.21, p. 447"]
theorem ex_8_21_lettuce_forty_heads_same_error_more_confidence :
    ∀ z : ℝ, 1.645 * (0.2 / √20) = z * (0.2 / √40) → z = 1.645 * √2 ∧ 0.9798 < centralMass z := by
  intro z h
  have h40 : √(40 : ℝ) = √2 * √20 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have h2 : 0 < √(2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have h20 : 0 < √(20 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hz : z = 1.645 * √2 := by
    have : z * (0.2 / √40) = (1.645 * √2) * (0.2 / √40) := by
      rw [← h, h40]; field_simp
    exact mul_right_cancel₀ (by positivity) this
  have hs : (1.4142 : ℝ) < √2 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hl : (0.9798 : ℝ) < centralMass 2.326 ∧ centralMass 2.326 < 0.9801 :=
    Ioo_enclosure (k := 2.326) (a := 0.9798) (b := 0.9801) (by norm_num) 14 (by norm_num)
      (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
      (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
  refine ⟨hz, ?_⟩
  have : centralMass 2.326 ≤ centralMass z := centralMass_mono (by rw [hz]; linarith)
  linarith [hl.1]

/-- OpenStax Introductory Statistics 2e Practice exercise 8.22. With 40 heads of lettuce at the same 90% level (sigma 0.2) the margin 1.645 * 0.2/sqrt 40 lies in (0.0520, 0.0521), smaller than the 20-head margin in (0.0735, 0.0736). -/
@[kb "openstaxintrostats2e" "Exercise 8.22, p. 447"]
theorem ex_8_22_lettuce_forty_heads_same_confidence :
    let e40 : ℝ := 1.645 * (0.2 / √40)
    let e20 : ℝ := 1.645 * (0.2 / √20)
    0.0520 < e40 ∧ e40 < 0.0521 ∧ 0.0735 < e20 ∧ e20 < 0.0736 ∧ e40 < e20 := by
  intro e40 e20
  obtain ⟨h1, h2⟩ := zebm (z := 1.645) (s := 0.2) (sl := 0.2) (sh := 0.2) (n := 40) (lo := 6.3245553) (hi := 6.3245555) (a := 0.0520) (b := 0.0521)
    (by norm_num) (by norm_num) le_rfl le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨g1, g2⟩ := zebm (z := 1.645) (s := 0.2) (sl := 0.2) (sh := 0.2) (n := 20) (lo := 4.4721359) (hi := 4.4721361) (a := 0.0735) (b := 0.0736)
    (by norm_num) (by norm_num) le_rfl le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [e40, e20]
  refine ⟨h1, h2, g1, g2, ?_⟩
  linarith

/-! ### Foothill College (exercises 8.23 to 8.37) -/

/-- OpenStax Introductory Statistics 2e Practice exercise 8.23. The 25 sampled Winter students have mean age 30.4, which is 2.8 years below the Fall population mean 33.2. -/
@[kb "openstaxintrostats2e" "Exercise 8.23, p. 447"]
theorem ex_8_23_foothill_sample_mean :
    (30.4 : ℝ) - 33.2 = -2.8 := by
  norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 8.24. With n = 25 the square root of the sample size is exactly 5, so the standard error 15/sqrt 25 equals 3. -/
@[kb "openstaxintrostats2e" "Exercise 8.24, p. 447"]
theorem ex_8_24_foothill_sample_size :
    √(25 : ℝ) = 5 ∧ (15 : ℝ) / √25 = 3 := by
  rw [sqrt25]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 8.25. With sigma = 15 the variance of the age is 225, and the variance of the mean of 25 ages is 225/25 = 9. -/
@[kb "openstaxintrostats2e" "Exercise 8.25, p. 448"]
theorem ex_8_25_foothill_sigma :
    (15 : ℝ) ^ 2 = 225 ∧ (15 : ℝ) ^ 2 / 25 = 9 := by
  norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 8.30. For 95% confidence the two tails together hold 1 - 0.95 = 0.05 of the standard normal mass; indeed the central mass within 1.96 lies in (0.9499, 0.9501). -/
@[kb "openstaxintrostats2e" "Exercise 8.30, p. 448"]
theorem ex_8_30_foothill_alpha_95 :
    (1 : ℝ) - 0.95 = 0.05 ∧ (0.9499 < centralMass 1.96 ∧ centralMass 1.96 < 0.9501) := by
  exact ⟨by norm_num, critical_values_standard_normal.2.1⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 8.31. Each tail has alpha/2 = 0.025 of the standard normal mass: the upper tail above 1.96 lies in (0.0249, 0.0251). -/
@[kb "openstaxintrostats2e" "Exercise 8.31, p. 448"]
theorem ex_8_31_foothill_alpha_half :
    ((1 : ℝ) - 0.95) / 2 = 0.025 ∧
      (0.0249 < 1 - cdf (gaussianReal 0 1) 1.96 ∧ 1 - cdf (gaussianReal 0 1) 1.96 < 0.0251) := by
  have h := critical_values_stdNormalCdf.2.1
  refine ⟨by norm_num, ?_, ?_⟩ <;> linarith [h.1, h.2]

/-- OpenStax Introductory Statistics 2e Practice exercise 8.32. Winter Foothill ages, mean 30.4, sigma 15, n = 25, 95%: the error bound is 1.96 * 15/5 = 5.88, the lower limit 24.52 and the upper limit 36.28. -/
@[kb "openstaxintrostats2e" "Exercise 8.32, p. 448"]
theorem ex_8_32_foothill_limits_error_bound :
    let ebm : ℝ := 1.96 * (15 / √25)
    ebm = 5.88 ∧ 30.4 - ebm = 24.52 ∧ 30.4 + ebm = 36.28 := by
  intro ebm
  simp only [ebm]
  rw [sqrt25]
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 8.33. The 95% confidence interval for the mean age of Winter Foothill students is the closed interval from 24.52 to 36.28 (critical value 1.96, central mass in (0.9499, 0.9501)). -/
@[kb "openstaxintrostats2e" "Exercise 8.33, p. 448"]
theorem ex_8_33_foothill_ci_95 :
    (0.9499 < centralMass 1.96 ∧ centralMass 1.96 < 0.9501) ∧
    Set.Icc (30.4 - 1.96 * (15 / √25) : ℝ) (30.4 + 1.96 * (15 / √25)) = Set.Icc 24.52 36.28 := by
  refine ⟨critical_values_standard_normal.2.1, ?_⟩
  rw [sqrt25]
  norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 8.36. With n = 69 instead of 25 (same mean, sigma 15, 95%) the error bound 1.96 * 15/sqrt 69 lies in (3.5393, 3.5394), smaller than the n = 25 error bound 5.88. -/
@[kb "openstaxintrostats2e" "Exercise 8.36, p. 448"]
theorem ex_8_36_foothill_n69_smaller_error :
    let e69 : ℝ := 1.96 * (15 / √69)
    3.5393 < e69 ∧ e69 < 3.5394 ∧ e69 < 5.88 := by
  intro e69
  obtain ⟨h1, h2⟩ := zebm (z := 1.96) (s := 15) (sl := 15) (sh := 15) (n := 69) (lo := 8.3066238) (hi := 8.3066240) (a := 3.5393) (b := 3.5394)
    (by norm_num) (by norm_num) le_rfl le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [e69]
  refine ⟨h1, h2, ?_⟩
  linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 8.37. At 90% confidence (critical value 1.645, central mass in (0.8999, 0.9001)) with n = 25 the error bound is 1.645 * 15/5 = 4.935, smaller than the 95% error bound 5.88. -/
@[kb "openstaxintrostats2e" "Exercise 8.37, p. 448"]
theorem ex_8_37_foothill_90_smaller_error :
    (0.8999 < centralMass 1.645 ∧ centralMass 1.645 < 0.9001) ∧
    (1.645 * (15 / √25) : ℝ) = 4.935 ∧ (1.645 * (15 / √25) : ℝ) < 5.88 := by
  refine ⟨critical_values_standard_normal.1, ?_, ?_⟩ <;> rw [sqrt25] <;> norm_num

/-! ### Section 8.2: mean, unknown standard deviation (Student t table values) -/

/-- OpenStax Introductory Statistics 2e Practice exercise 8.38. Emergency-room waits: mean 1.5 hours, sample standard deviation 0.5, n = 70, so 69 degrees of freedom; the standard error 0.5/sqrt 70 lies in (0.0597, 0.0598). -/
@[kb "openstaxintrostats2e" "Exercise 8.38, p. 448"]
theorem ex_8_38_er_wait_parameters :
    (70 : ℕ) - 1 = 69 ∧ 0.0597 < (0.5 : ℝ) / √70 ∧ (0.5 : ℝ) / √70 < 0.0598 := by
  obtain ⟨h1, h2⟩ := sdiv (s := 0.5) (sl := 0.5) (sh := 0.5) (n := 70) (lo := 8.3666002) (hi := 8.3666004) (a := 0.0597) (b := 0.0598)
    (by norm_num) le_rfl le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨by norm_num, h1, h2⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 8.41. Emergency-room waits, 95% interval from mean 1.5, s = 0.5, n = 70 using the table value t = 1.995 for 69 degrees of freedom (a standard table value, not proved here); the interval is about (1.381, 1.619). The margin of error lies in (0.1192, 0.1193), the lower endpoint in (1.3807, 1.3808) and the upper endpoint in (1.6192, 1.6193). -/
@[kb "openstaxintrostats2e" "Exercise 8.41, p. 448"]
theorem ex_8_41_er_wait_ci_95_t :
        let ebm : ℝ := 1.995 * (0.5 / √70)
    0.1192 < ebm ∧ ebm < 0.1193 ∧ 1.3807 < 1.5 - ebm ∧ 1.5 - ebm < 1.3808 ∧
      1.6192 < 1.5 + ebm ∧ 1.5 + ebm < 1.6193 := by
  intro ebm
  obtain ⟨h1, h2⟩ := zebm (z := 1.995) (s := 0.5) (sl := 0.5) (sh := 0.5) (n := 70) (lo := 8.3666002) (hi := 8.3666004) (a := 0.1192) (b := 0.1193)
    (by norm_num) (by norm_num) le_rfl le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [ebm]
  refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 8.43. Monthly television hours of 108 Americans: mean 151, sample standard deviation 32, so 107 degrees of freedom; the standard error 32/sqrt 108 lies in (3.0792, 3.0793). -/
@[kb "openstaxintrostats2e" "Exercise 8.43, p. 449"]
theorem ex_8_43_television_parameters :
    (108 : ℕ) - 1 = 107 ∧ 3.0792 < (32 : ℝ) / √108 ∧ (32 : ℝ) / √108 < 3.0793 := by
  obtain ⟨h1, h2⟩ := sdiv (s := 32) (sl := 32) (sh := 32) (n := 108) (lo := 10.3923048) (hi := 10.3923050) (a := 3.0792) (b := 3.0793)
    (by norm_num) le_rfl le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨by norm_num, h1, h2⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 8.47. Television hours, 99% interval from mean 151, s = 32, n = 108 using the table value t = 2.623 for 107 degrees of freedom (a standard table value, not proved here); the interval is about (142.92, 159.08) and the error bound about 8.08. The margin of error lies in (8.0767, 8.0768), the lower endpoint in (142.9232, 142.9233) and the upper endpoint in (159.0767, 159.0768). -/
@[kb "openstaxintrostats2e" "Exercise 8.47, p. 449"]
theorem ex_8_47_television_ci_99_t :
        let ebm : ℝ := 2.623 * (32 / √108)
    8.0767 < ebm ∧ ebm < 8.0768 ∧ 142.9232 < 151 - ebm ∧ 151 - ebm < 142.9233 ∧
      159.0767 < 151 + ebm ∧ 151 + ebm < 159.0768 := by
  intro ebm
  obtain ⟨h1, h2⟩ := zebm (z := 2.623) (s := 32) (sl := 32) (sh := 32) (n := 108) (lo := 10.3923048) (hi := 10.3923050) (a := 8.0767) (b := 8.0768)
    (by norm_num) (by norm_num) le_rfl le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [ebm]
  refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 8.48. Television hours at 95%, with the table value t = 1.982 for 107 degrees of freedom (not proved here): the error bound 1.982 * 32/sqrt 108 lies in (6.1029, 6.1030), smaller than the 99% error bound (t = 2.623) in (8.0767, 8.0768). -/
@[kb "openstaxintrostats2e" "Exercise 8.48, p. 449"]
theorem ex_8_48_television_95_smaller_error :
    let e95 : ℝ := 1.982 * (32 / √108)
    let e99 : ℝ := 2.623 * (32 / √108)
    6.1029 < e95 ∧ e95 < 6.1030 ∧ 8.0767 < e99 ∧ e99 < 8.0768 ∧ e95 < e99 := by
  intro e95 e99
  obtain ⟨h1, h2⟩ := zebm (z := 1.982) (s := 32) (sl := 32) (sh := 32) (n := 108) (lo := 10.3923048) (hi := 10.3923050) (a := 6.1029) (b := 6.1030)
    (by norm_num) (by norm_num) le_rfl le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨g1, g2⟩ := zebm (z := 2.623) (s := 32) (sl := 32) (sh := 32) (n := 108) (lo := 10.3923048) (hi := 10.3923050) (a := 8.0767) (b := 8.0768)
    (by norm_num) (by norm_num) le_rfl le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [e95, e99]
  refine ⟨h1, h2, g1, g2, ?_⟩
  linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 8.49. Colours on 39 flags (Table 8.10 expanded to 39 values, n = 39): the sample mean is exactly 127/39 (about 3.26), the sample variance exactly 769/741 and the sample standard deviation lies in (1.0187, 1.0188) (about 1.02). -/
@[kb "openstaxintrostats2e" "Exercise 8.49, p. 449"]
theorem ex_8_49_flags_mean_sd :
    mean flagsX = 127 / 39 ∧ sampleVariance flagsX = 769 / 741 ∧
      1.0187 < sampleStdDev flagsX ∧ sampleStdDev flagsX < 1.0188 := by
  exact ⟨flags_mean, flags_var, flags_sd.1, flags_sd.2⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 8.54. For 95% confidence the two tails together hold alpha = 1 - 0.95 = 0.05. -/
@[kb "openstaxintrostats2e" "Exercise 8.54, p. 449"]
theorem ex_8_54_flags_alpha :
    (1 : ℝ) - 0.95 = 0.05 := by
  norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 8.55. Each tail holds alpha/2 = 0.025. -/
@[kb "openstaxintrostats2e" "Exercise 8.55, p. 449"]
theorem ex_8_55_flags_alpha_half :
    ((1 : ℝ) - 0.95) / 2 = 0.025 := by
  norm_num

/-- Margin of error for the flag data with the table value `t = 2.024`. -/
private lemma flags_ebm_95 :
    0.3301 < 2.024 * (sampleStdDev flagsX / √39) ∧ 2.024 * (sampleStdDev flagsX / √39) < 0.3302 := by
  obtain ⟨s1, s2⟩ := flags_sd
  exact zebm (z := 2.024) (s := sampleStdDev flagsX) (sl := 1.0187) (sh := 1.0188) (n := 39)
    (lo := 6.2449979) (hi := 6.2449981) (a := 0.3301) (b := 0.3302)
    (by norm_num) (by norm_num) s1.le s2.le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)


/-- OpenStax Introductory Statistics 2e Practice exercise 8.56. Flag colours, 95% interval using the table value t = 2.024 for 38 degrees of freedom (not proved here): the error bound lies in (0.3301, 0.3302), the lower limit in (2.9262, 2.9264) and the upper limit in (3.5865, 3.5867). -/
@[kb "openstaxintrostats2e" "Exercise 8.56, p. 450"]
theorem ex_8_56_flags_limits_error_bound :
    let ebm : ℝ := 2.024 * (sampleStdDev flagsX / √39)
    0.3301 < ebm ∧ ebm < 0.3302 ∧ 2.9262 < mean flagsX - ebm ∧ mean flagsX - ebm < 2.9264 ∧
      3.5865 < mean flagsX + ebm ∧ mean flagsX + ebm < 3.5867 := by
  intro ebm
  obtain ⟨h1, h2⟩ := flags_ebm_95
  rw [flags_mean]
  simp only [ebm]
  refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩ <;> norm_num <;> linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 8.57. The same flag-colour interval (t = 2.024, not proved here) rounds to (2.93, 3.59): the lower limit lies in (2.925, 2.935) and the upper limit in (3.585, 3.595). -/
@[kb "openstaxintrostats2e" "Exercise 8.57, p. 450"]
theorem ex_8_57_flags_ci_95_rounded :
    let ebm : ℝ := 2.024 * (sampleStdDev flagsX / √39)
    2.925 < mean flagsX - ebm ∧ mean flagsX - ebm < 2.935 ∧
      3.585 < mean flagsX + ebm ∧ mean flagsX + ebm < 3.595 := by
  intro ebm
  obtain ⟨h1, h2⟩ := flags_ebm_95
  rw [flags_mean]
  simp only [ebm]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num <;> linarith

private lemma flags_ebm_69 :
    0.2446 < 1.995 * (sampleStdDev flagsX / √69) ∧ 1.995 * (sampleStdDev flagsX / √69) < 0.2447 := by
  obtain ⟨s1, s2⟩ := flags_sd
  exact zebm (z := 1.995) (s := sampleStdDev flagsX) (sl := 1.0187) (sh := 1.0188) (n := 69)
    (lo := 8.3066238) (hi := 8.3066240) (a := 0.2446) (b := 0.2447)
    (by norm_num) (by norm_num) s1.le s2.le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)


/-- OpenStax Introductory Statistics 2e Practice exercise 8.60. With n = 69 instead of 39 (same mean and standard deviation, 95%, table value t = 1.995 for 68 degrees of freedom, not proved here) the error bound lies in (0.2446, 0.2447), smaller than the n = 39 error bound (in (0.3301, 0.3302)). -/
@[kb "openstaxintrostats2e" "Exercise 8.60, p. 450"]
theorem ex_8_60_flags_n69_smaller_error :
    let e69 : ℝ := 1.995 * (sampleStdDev flagsX / √69)
    let e39 : ℝ := 2.024 * (sampleStdDev flagsX / √39)
    0.2446 < e69 ∧ e69 < 0.2447 ∧ e69 < e39 := by
  intro e69 e39
  simp only [e69, e39]
  obtain ⟨h1, h2⟩ := flags_ebm_69
  obtain ⟨g1, g2⟩ := flags_ebm_95
  refine ⟨h1, h2, ?_⟩
  linarith

private lemma flags_ebm_90 :
    0.2750 < 1.686 * (sampleStdDev flagsX / √39) ∧ 1.686 * (sampleStdDev flagsX / √39) < 0.2751 := by
  obtain ⟨s1, s2⟩ := flags_sd
  exact zebm (z := 1.686) (s := sampleStdDev flagsX) (sl := 1.0187) (sh := 1.0188) (n := 39)
    (lo := 6.2449979) (hi := 6.2449981) (a := 0.2750) (b := 0.2751)
    (by norm_num) (by norm_num) s1.le s2.le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)


/-- OpenStax Introductory Statistics 2e Practice exercise 8.61. At 90% confidence the table value for 38 degrees of freedom is t = 1.686 (not proved here); the error bound lies in (0.2750, 0.2751), smaller than the 95% error bound (in (0.3301, 0.3302)). -/
@[kb "openstaxintrostats2e" "Exercise 8.61, p. 450"]
theorem ex_8_61_flags_90_smaller_error :
    let e90 : ℝ := 1.686 * (sampleStdDev flagsX / √39)
    let e95 : ℝ := 2.024 * (sampleStdDev flagsX / √39)
    0.2750 < e90 ∧ e90 < 0.2751 ∧ e90 < e95 := by
  intro e90 e95
  simp only [e90, e95]
  obtain ⟨h1, h2⟩ := flags_ebm_90
  obtain ⟨g1, g2⟩ := flags_ebm_95
  refine ⟨h1, h2, ?_⟩
  linarith

/-! ### Section 8.3: proportions -/

/-- OpenStax Introductory Statistics 2e Practice exercise 8.62. To estimate a proportion within 0.05 with 90% confidence (critical value 1.645, central mass in (0.8999, 0.9001)) and the worst case p = 0.5, the sample size must be at least 1.645^2 * 0.25/0.05^2 = 270.6025; the least such whole number is 271. -/
@[kb "openstaxintrostats2e" "Exercise 8.62, p. 450"]
theorem ex_8_62_women_sample_size_90 :
    (0.8999 < centralMass 1.645 ∧ centralMass 1.645 < 0.9001) ∧
    (1.645 : ℝ) ^ 2 * (0.5 * 0.5) / 0.05 ^ 2 = 270.6025 ∧
      IsLeast {n : ℕ | (1.645 : ℝ) ^ 2 * (0.5 * 0.5) / 0.05 ^ 2 ≤ n} 271 := by
  refine ⟨critical_values_standard_normal.1, by norm_num, ?_, ?_⟩
  · show (1.645 : ℝ) ^ 2 * (0.5 * 0.5) / 0.05 ^ 2 ≤ ((271 : ℕ) : ℝ)
    norm_num
  · intro n hn
    by_contra h
    have : n ≤ 270 := by omega
    have h2 : (n : ℝ) ≤ 270 := by exact_mod_cast this
    have h3 : (1.645 : ℝ) ^ 2 * (0.5 * 0.5) / 0.05 ^ 2 ≤ n := hn
    norm_num at h3
    linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 8.63. Raising the confidence to 95% (critical value 1.96, central mass in (0.9499, 0.9501)) with the same error 0.05 raises the needed sample size: 1.96^2 * 0.25/0.05^2 = 384.16, so the least sample size is 385, more than 271. -/
@[kb "openstaxintrostats2e" "Exercise 8.63, p. 450"]
theorem ex_8_63_women_sample_size_95 :
    (0.9499 < centralMass 1.96 ∧ centralMass 1.96 < 0.9501) ∧
    (1.96 : ℝ) ^ 2 * (0.5 * 0.5) / 0.05 ^ 2 = 384.16 ∧ 271 < 385 ∧
      IsLeast {n : ℕ | (1.96 : ℝ) ^ 2 * (0.5 * 0.5) / 0.05 ^ 2 ≤ n} 385 := by
  refine ⟨critical_values_standard_normal.2.1, by norm_num, by norm_num, ?_, ?_⟩
  · show (1.96 : ℝ) ^ 2 * (0.5 * 0.5) / 0.05 ^ 2 ≤ ((385 : ℕ) : ℝ)
    norm_num
  · intro n hn
    by_contra h
    have : n ≤ 384 := by omega
    have h2 : (n : ℝ) ≤ 384 := by exact_mod_cast this
    have h3 : (1.96 : ℝ) ^ 2 * (0.5 * 0.5) / 0.05 ^ 2 ≤ n := hn
    norm_num at h3
    linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 8.64. In 120 of 200 surveyed households the woman made the main purchasing decisions: x = 120, n = 200, p-hat = 120/200 = 3/5. -/
@[kb "openstaxintrostats2e" "Exercise 8.64, p. 450"]
theorem ex_8_64_households_phat :
    (120 : ℝ) / 200 = 3 / 5 ∧ (120 : ℝ) / 200 = 0.6 := by
  constructor <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 8.67. Households where the woman decides: 95% interval from p-hat = 120/200, n = 200 (critical value 1.96, central mass in (0.9499, 0.9501)); the interval is about (0.5321, 0.6679). The error bound lies in (0.0678, 0.0679), the lower endpoint in (0.5321, 0.5322) and the upper endpoint in (0.6678, 0.6679). -/
@[kb "openstaxintrostats2e" "Exercise 8.67, p. 450"]
theorem ex_8_67_households_ci_95 :
    (0.9499 < centralMass 1.96 ∧ centralMass 1.96 < 0.9501) ∧
    let p : ℝ := (120 / 200)
    let ebp : ℝ := 1.96 * √(p * (1 - p) / 200)
    0.0678 < ebp ∧ ebp < 0.0679 ∧ 0.5321 < p - ebp ∧ p - ebp < 0.5322 ∧
      0.6678 < p + ebp ∧ p + ebp < 0.6679 := by
  refine ⟨critical_values_standard_normal.2.1, ?_⟩
  intro p ebp
  obtain ⟨h1, h2⟩ := zsqrt (z := 1.96) (v := (120 / 200) * (1 - (120 / 200)) / 200) (lo := 0.0346410) (hi := 0.0346412) (a := 0.0678) (b := 0.0679)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [p, ebp]
  refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 8.71. Executives preferring trucks: 95% interval from p-hat = 0.26 and n = 160 (critical value 1.96). The book prints (0.19432, 0.33068) with error bound 0.0707; its interval is centred at 0.2625 = 42/160 (26% of 160 is not a whole number) and its printed error bound is inconsistent with its own interval, whose half-width is about 0.0682. Here the exact p-hat = 0.26 is used. The error bound lies in (0.0679, 0.0680), the lower endpoint in (0.1920, 0.1921) and the upper endpoint in (0.3279, 0.3280). -/
@[kb "openstaxintrostats2e" "Exercise 8.71, p. 451"]
theorem ex_8_71_executives_ci_95_p26 :
    (0.9499 < centralMass 1.96 ∧ centralMass 1.96 < 0.9501) ∧
    let p : ℝ := 0.26
    let ebp : ℝ := 1.96 * √(p * (1 - p) / 160)
    0.0679 < ebp ∧ ebp < 0.0680 ∧ 0.1920 < p - ebp ∧ p - ebp < 0.1921 ∧
      0.3279 < p + ebp ∧ p + ebp < 0.3280 := by
  refine ⟨critical_values_standard_normal.2.1, ?_⟩
  intro p ebp
  obtain ⟨h1, h2⟩ := zsqrt (z := 1.96) (v := 0.26 * (1 - 0.26) / 160) (lo := 0.0346770) (hi := 0.0346772) (a := 0.0679) (b := 0.0680)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [p, ebp]
  refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 8.71. Executives preferring trucks: 95% interval when the 26% of 160 executives is rounded to 42 executives, p-hat = 42/160 = 0.2625 (critical value 1.96); this reproduces the book's interval (0.19432, 0.33068), with error bound about 0.0682 rather than the printed 0.0707. The error bound lies in (0.0681, 0.0682), the lower endpoint in (0.1943, 0.1944) and the upper endpoint in (0.3306, 0.3307). -/
@[kb "openstaxintrostats2e" "Exercise 8.71, p. 451"]
theorem ex_8_71_executives_ci_95_p42 :
    (0.9499 < centralMass 1.96 ∧ centralMass 1.96 < 0.9501) ∧
    let p : ℝ := (42 / 160)
    let ebp : ℝ := 1.96 * √(p * (1 - p) / 160)
    0.0681 < ebp ∧ ebp < 0.0682 ∧ 0.1943 < p - ebp ∧ p - ebp < 0.1944 ∧
      0.3306 < p + ebp ∧ p + ebp < 0.3307 := by
  refine ⟨critical_values_standard_normal.2.1, ?_⟩
  intro p ebp
  obtain ⟨h1, h2⟩ := zsqrt (z := 1.96) (v := (42 / 160) * (1 - (42 / 160)) / 160) (lo := 0.0347844) (hi := 0.0347846) (a := 0.0681) (b := 0.0682)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [p, ebp]
  refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 8.77. Voters naming the economy: 90% interval from p-hat = 0.65, n = 1200 (critical value 1.645); the interval is about (0.6273, 0.6727) with error bound about 0.0226. The error bound lies in (0.0226, 0.0227), the lower endpoint in (0.6273, 0.6274) and the upper endpoint in (0.6726, 0.6727). -/
@[kb "openstaxintrostats2e" "Exercise 8.77, p. 451"]
theorem ex_8_77_economy_ci_90 :
    (0.8999 < centralMass 1.645 ∧ centralMass 1.645 < 0.9001) ∧
    let p : ℝ := 0.65
    let ebp : ℝ := 1.645 * √(p * (1 - p) / 1200)
    0.0226 < ebp ∧ ebp < 0.0227 ∧ 0.6273 < p - ebp ∧ p - ebp < 0.6274 ∧
      0.6726 < p + ebp ∧ p + ebp < 0.6727 := by
  refine ⟨critical_values_standard_normal.1, ?_⟩
  intro p ebp
  obtain ⟨h1, h2⟩ := zsqrt (z := 1.645) (v := 0.65 * (1 - 0.65) / 1200) (lo := 0.0137689) (hi := 0.0137691) (a := 0.0226) (b := 0.0227)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [p, ebp]
  refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 8.78. Voters naming the economy: the 95% interval from p-hat = 0.65, n = 1200 (critical value 1.96), about (0.6230, 0.6770). The error bound lies in (0.0269, 0.0270), the lower endpoint in (0.6230, 0.6231) and the upper endpoint in (0.6769, 0.6770). -/
@[kb "openstaxintrostats2e" "Exercise 8.78, p. 451"]
theorem ex_8_78_economy_ci_95 :
    (0.9499 < centralMass 1.96 ∧ centralMass 1.96 < 0.9501) ∧
    let p : ℝ := 0.65
    let ebp : ℝ := 1.96 * √(p * (1 - p) / 1200)
    0.0269 < ebp ∧ ebp < 0.0270 ∧ 0.6230 < p - ebp ∧ p - ebp < 0.6231 ∧
      0.6769 < p + ebp ∧ p + ebp < 0.6770 := by
  refine ⟨critical_values_standard_normal.2.1, ?_⟩
  intro p ebp
  obtain ⟨h1, h2⟩ := zsqrt (z := 1.96) (v := 0.65 * (1 - 0.65) / 1200) (lo := 0.0137689) (hi := 0.0137691) (a := 0.0269) (b := 0.0270)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [p, ebp]
  refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 8.78. The 95% error bound (0.0269, 0.0270) exceeds the 90% error bound (0.0226, 0.0227), so the 95% interval around 0.65 contains the 90% interval and is wider. -/
@[kb "openstaxintrostats2e" "Exercise 8.78, p. 451"]
theorem ex_8_78_economy_95_wider_than_90 :
    let e90 : ℝ := 1.645 * √(0.65 * (1 - 0.65) / 1200)
    let e95 : ℝ := 1.96 * √(0.65 * (1 - 0.65) / 1200)
    0.0226 < e90 ∧ e90 < 0.0227 ∧ 0.0269 < e95 ∧ e95 < 0.0270 ∧ 0.65 - e95 < 0.65 - e90 ∧
      0.65 + e90 < 0.65 + e95 := by
  intro e90 e95
  obtain ⟨h1, h2⟩ := zsqrt (z := 1.645) (v := 0.65 * (1 - 0.65) / 1200) (lo := 0.0137689) (hi := 0.0137691) (a := 0.0226) (b := 0.0227)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨g1, g2⟩ := zsqrt (z := 1.96) (v := 0.65 * (1 - 0.65) / 1200) (lo := 0.0137689) (hi := 0.0137691) (a := 0.0269) (b := 0.0270)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [e90, e95]
  refine ⟨h1, h2, g1, g2, ?_, ?_⟩ <;> linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 8.81. Ice-skating class with 64 girls and 16 boys: x = 64 girls, n = 64 + 16 = 80, p-hat = 64/80 = 0.8. -/
@[kb "openstaxintrostats2e" "Exercise 8.81, p. 451"]
theorem ex_8_81_skating_phat :
    (64 : ℕ) + 16 = 80 ∧ (64 : ℝ) / 80 = 0.8 := by
  constructor <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 8.82. The estimated distribution of the number of girls is binomial with n = 80 and p = 0.8: its mean is 80 * 0.8 = 64 and its variance 80 * 0.8 * 0.2 = 12.8. -/
@[kb "openstaxintrostats2e" "Exercise 8.82, p. 451"]
theorem ex_8_82_skating_binomial_mean_variance :
    (80 : ℝ) * 0.8 = 64 ∧ (80 : ℝ) * 0.8 * 0.2 = 12.8 := by
  constructor <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 8.85. Girls in beginning skating classes: 92% interval from p-hat = 64/80 = 0.8, n = 80 with critical value 1.751 (about 1.7507 in the table; its central mass lies in (0.9199, 0.9202)); the book gives (0.72171, 0.87829) using 1.7507. The error bound lies in (0.0783, 0.0784), the lower endpoint in (0.7216, 0.7217) and the upper endpoint in (0.8783, 0.8784). -/
@[kb "openstaxintrostats2e" "Exercise 8.85, p. 451"]
theorem ex_8_85_skating_ci_92 :
    (0.9199 < centralMass 1.751 ∧ centralMass 1.751 < 0.9202) ∧
    let p : ℝ := (64 / 80)
    let ebp : ℝ := 1.751 * √(p * (1 - p) / 80)
    0.0783 < ebp ∧ ebp < 0.0784 ∧ 0.7216 < p - ebp ∧ p - ebp < 0.7217 ∧
      0.8783 < p + ebp ∧ p + ebp < 0.8784 := by
  refine ⟨Ioo_enclosure (k := 1.751) (a := 0.9199) (b := 0.9202) (by norm_num) 14 (by norm_num)
      (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
      (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial]), ?_⟩
  intro p ebp
  obtain ⟨h1, h2⟩ := zsqrt (z := 1.751) (v := (64 / 80) * (1 - (64 / 80)) / 80) (lo := 0.0447213) (hi := 0.0447215) (a := 0.0783) (b := 0.0784)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [p, ebp]
  refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 8.86. A 92% interval leaves alpha = 1 - 0.92 = 0.08 in the two tails together; the central normal mass within 1.751 lies in (0.9199, 0.9202). -/
@[kb "openstaxintrostats2e" "Exercise 8.86, p. 451"]
theorem ex_8_86_skating_alpha :
    (1 : ℝ) - 0.92 = 0.08 ∧ (0.9199 < centralMass 1.751 ∧ centralMass 1.751 < 0.9202) := by
  exact ⟨by norm_num, Ioo_enclosure (k := 1.751) (a := 0.9199) (b := 0.9202) (by norm_num) 14 (by norm_num)
      (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
      (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 8.87. Each tail has alpha/2 = 0.04; the upper tail above 1.751 lies in (0.0398, 0.0401). -/
@[kb "openstaxintrostats2e" "Exercise 8.87, p. 451"]
theorem ex_8_87_skating_alpha_half :
    ((1 : ℝ) - 0.92) / 2 = 0.04 ∧
      (0.0398 < 1 - cdf (gaussianReal 0 1) 1.751 ∧ 1 - cdf (gaussianReal 0 1) 1.751 < 0.0401) := by
  have hl : (0.9199 < (gaussianReal 0 1).real (Ioo (-1.751) 1.751) ∧ (gaussianReal 0 1).real (Ioo (-1.751) 1.751) < 0.9202) :=
    Ioo_enclosure (k := 1.751) (a := 0.9199) (b := 0.9202) (by norm_num) 14 (by norm_num)
      (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
      (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
  have h := stdNormalCdf_eq_Ioo (z := 1.751) (by norm_num)
  refine ⟨by norm_num, ?_, ?_⟩ <;> linarith [hl.1, hl.2]

/-- OpenStax Introductory Statistics 2e Practice exercise 8.88. Girls in beginning skating classes, 92% limits and error bound (critical value 1.751, p-hat = 0.8, n = 80). The error bound lies in (0.0783, 0.0784), the lower endpoint in (0.7216, 0.7217) and the upper endpoint in (0.8783, 0.8784). -/
@[kb "openstaxintrostats2e" "Exercise 8.88, p. 451"]
theorem ex_8_88_skating_limits_error_bound :
    (0.9199 < centralMass 1.751 ∧ centralMass 1.751 < 0.9202) ∧
    let p : ℝ := (64 / 80)
    let ebp : ℝ := 1.751 * √(p * (1 - p) / 80)
    0.0783 < ebp ∧ ebp < 0.0784 ∧ 0.7216 < p - ebp ∧ p - ebp < 0.7217 ∧
      0.8783 < p + ebp ∧ p + ebp < 0.8784 := by
  refine ⟨Ioo_enclosure (k := 1.751) (a := 0.9199) (b := 0.9202) (by norm_num) 14 (by norm_num)
      (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
      (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial]), ?_⟩
  intro p ebp
  obtain ⟨h1, h2⟩ := zsqrt (z := 1.751) (v := (64 / 80) * (1 - (64 / 80)) / 80) (lo := 0.0447213) (hi := 0.0447215) (a := 0.0783) (b := 0.0784)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [p, ebp]
  refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 8.89. The 92% interval rounds to (0.72, 0.88): the lower limit lies in (0.715, 0.725) and the upper limit in (0.875, 0.885). The error bound lies in (0.0783, 0.0784), the lower endpoint in (0.7216, 0.7217) and the upper endpoint in (0.8783, 0.8784). -/
@[kb "openstaxintrostats2e" "Exercise 8.89, p. 451"]
theorem ex_8_89_skating_ci_rounded :
    (0.9199 < centralMass 1.751 ∧ centralMass 1.751 < 0.9202) ∧
    let p : ℝ := (64 / 80)
    let ebp : ℝ := 1.751 * √(p * (1 - p) / 80)
    0.0783 < ebp ∧ ebp < 0.0784 ∧ 0.7216 < p - ebp ∧ p - ebp < 0.7217 ∧
      0.8783 < p + ebp ∧ p + ebp < 0.8784 ∧
      0.715 < p - ebp ∧ p - ebp < 0.725 ∧ 0.875 < p + ebp ∧ p + ebp < 0.885 := by
  refine ⟨Ioo_enclosure (k := 1.751) (a := 0.9199) (b := 0.9202) (by norm_num) 14 (by norm_num)
      (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
      (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial]), ?_⟩
  intro p ebp
  obtain ⟨h1, h2⟩ := zsqrt (z := 1.751) (v := (64 / 80) * (1 - (64 / 80)) / 80) (lo := 0.0447213) (hi := 0.0447215) (a := 0.0783) (b := 0.0784)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [p, ebp]
  refine ⟨h1, h2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 8.92. With n = 100 instead of 80 (same p-hat = 0.8 and 92% level) the error bound lies in (0.0700, 0.0701), smaller than the n = 80 error bound in (0.0783, 0.0784). -/
@[kb "openstaxintrostats2e" "Exercise 8.92, p. 452"]
theorem ex_8_92_skating_n100_smaller_error :
    let e80 : ℝ := 1.751 * √(64 / 80 * (1 - 64 / 80) / 80)
    let e100 : ℝ := 1.751 * √(64 / 80 * (1 - 64 / 80) / 100)
    0.0783 < e80 ∧ e80 < 0.0784 ∧ 0.0700 < e100 ∧ e100 < 0.0701 ∧ e100 < e80 := by
  intro e80 e100
  obtain ⟨h1, h2⟩ := zsqrt (z := 1.751) (v := (64 / 80) * (1 - (64 / 80)) / 80) (lo := 0.0447213) (hi := 0.0447215) (a := 0.0783) (b := 0.0784)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨g1, g2⟩ := zsqrt (z := 1.751) (v := (64 / 80) * (1 - (64 / 80)) / 100) (lo := 0.0399999) (hi := 0.0400001) (a := 0.0700) (b := 0.0701)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [e80, e100]
  refine ⟨h1, h2, g1, g2, ?_⟩
  linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 8.93. At 98% confidence (critical value 2.326, central mass in (0.9798, 0.9801)) with n = 80 and p-hat = 0.8 the error bound lies in (0.1040, 0.1041), larger than the 92% error bound in (0.0783, 0.0784). -/
@[kb "openstaxintrostats2e" "Exercise 8.93, p. 452"]
theorem ex_8_93_skating_98_larger_error :
    (0.9798 < centralMass 2.326 ∧ centralMass 2.326 < 0.9801) ∧
    let e92 : ℝ := 1.751 * √(64 / 80 * (1 - 64 / 80) / 80)
    let e98 : ℝ := 2.326 * √(64 / 80 * (1 - 64 / 80) / 80)
    0.0783 < e92 ∧ e92 < 0.0784 ∧ 0.1040 < e98 ∧ e98 < 0.1041 ∧ e92 < e98 := by
  refine ⟨Ioo_enclosure (k := 2.326) (a := 0.9798) (b := 0.9801) (by norm_num) 14 (by norm_num)
      (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
      (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial]), ?_⟩
  intro e92 e98
  obtain ⟨h1, h2⟩ := zsqrt (z := 1.751) (v := (64 / 80) * (1 - (64 / 80)) / 80) (lo := 0.0447213) (hi := 0.0447215) (a := 0.0783) (b := 0.0784)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨g1, g2⟩ := zsqrt (z := 2.326) (v := (64 / 80) * (1 - (64 / 80)) / 80) (lo := 0.0447213) (hi := 0.0447215) (a := 0.1040) (b := 0.1041)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [e92, e98]
  refine ⟨h1, h2, g1, g2, ?_⟩
  linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 8.94. For a fixed critical value z > 0 and worst-case p = 0.5, the sample size bound z^2 * 0.25/E^2 grows as the allowed error E shrinks. Concretely at 90% (z = 1.645): E = 0.03 needs 1.645^2 * 0.25/0.03^2, about 751.67, more than the 270.6025 needed for E = 0.05. -/
@[kb "openstaxintrostats2e" "Exercise 8.94, p. 452"]
theorem ex_8_94_smaller_error_larger_sample :
    (∀ z E₁ E₂ : ℝ, 0 < z → 0 < E₁ → E₁ < E₂ → z ^ 2 * 0.25 / E₂ ^ 2 < z ^ 2 * 0.25 / E₁ ^ 2) ∧
    (1.645 : ℝ) ^ 2 * 0.25 / 0.05 ^ 2 < 1.645 ^ 2 * 0.25 / 0.03 ^ 2 := by
  refine ⟨?_, by norm_num⟩
  intro z E₁ E₂ hz h1 h12
  have h2 : 0 < E₂ := by linarith
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have hz2 : 0 < z ^ 2 * 0.25 := by positivity
  have : E₁ ^ 2 < E₂ ^ 2 := by nlinarith
  nlinarith

end UndergradKB.Statistics.Course.PracticeC8
