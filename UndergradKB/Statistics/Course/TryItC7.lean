import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF
import UndergradKB.Common.Attr
import UndergradKB.Statistics.NormalCdf
import UndergradKB.Statistics.CriticalValues
import UndergradKB.Statistics.EmpiricalRule
import UndergradKB.Statistics.Continuous
import UndergradKB.Statistics.Course.ExamplesC7

/-!
# "Try It" exercises, chapter 7 (OpenStax *Introductory Statistics 2e*): the central limit theorem

As in `ExamplesC7.lean`, the normal approximation of the book is the hypothesis: the sample mean (or
sample sum, or binomial count) `X` has the normal law with the mean and variance the book computes
(`HasLaw X (gaussianReal μ v.toNNReal) P`).  Standard errors are exact; every probability and
percentile is enclosed between two bounds around the rounded value of the book (percentiles: any `k`
with `P(X ≤ k) = p`).  Values of the standard normal distribution function `Φ` come from the
alternating Taylor enclosures (`Phi_enc` of `ExamplesC7.lean`).
-/

namespace UndergradKB.Statistics.Course.TryItC7

open MeasureTheory ProbabilityTheory Set UndergradKB.Statistics
open UndergradKB.Statistics.Course.ExamplesC7

local notation "Φ" => cdf (gaussianReal 0 1)

macro "emp_num" : tactic =>
  `(tactic| (simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial]))

/-! ### Values of `Φ` -/

private lemma t_2_0539 : (0.97997 : ℝ) < Φ 2.0539 ∧ Φ 2.0539 < 0.98002 :=
  Phi_enc (by norm_num) 5 (by norm_num) (by emp_num) (by emp_num)

private lemma t_2_054 : (0.97998 : ℝ) < Φ 2.054 ∧ Φ 2.054 < 0.98003 :=
  Phi_enc (by norm_num) 5 (by norm_num) (by emp_num) (by emp_num)

private lemma t_25_12 : (0.98135 : ℝ) < Φ (25 / 12 : ℝ) ∧ Φ (25 / 12 : ℝ) < 0.9814 :=
  Phi_enc (by norm_num) 5 (by norm_num) (by emp_num) (by emp_num)

private lemma t_0_4077 : (0.65813 : ℝ) < Φ 0.4077 ∧ Φ 0.4077 < 0.65826 :=
  Phi_enc (by norm_num) 1 (by norm_num) (by emp_num) (by emp_num)

private lemma t_0_4078 : (0.65817 : ℝ) < Φ 0.4078 ∧ Φ 0.4078 < 0.6583 :=
  Phi_enc (by norm_num) 1 (by norm_num) (by emp_num) (by emp_num)

private lemma t_2_6516 : (0.99596 : ℝ) < Φ 2.6516 ∧ Φ 2.6516 < 0.99601 :=
  Phi_enc (by norm_num) 7 (by norm_num) (by emp_num) (by emp_num)

private lemma t_2_6517 : (0.99596 : ℝ) < Φ 2.6517 ∧ Φ 2.6517 < 0.99601 :=
  Phi_enc (by norm_num) 7 (by norm_num) (by emp_num) (by emp_num)

private lemma t_0_5604 : (0.71238 : ℝ) < Φ 0.5604 ∧ Φ 0.5604 < 0.7124 :=
  Phi_enc (by norm_num) 2 (by norm_num) (by emp_num) (by emp_num)

private lemma t_0_5605 : (0.71242 : ℝ) < Φ 0.5605 ∧ Φ 0.5605 < 0.71244 :=
  Phi_enc (by norm_num) 2 (by norm_num) (by emp_num) (by emp_num)

private lemma t_2_1616 : (0.98461 : ℝ) < Φ 2.1616 ∧ Φ 2.1616 < 0.98469 :=
  Phi_enc (by norm_num) 5 (by norm_num) (by emp_num) (by emp_num)

private lemma t_2_1618 : (0.98462 : ℝ) < Φ 2.1618 ∧ Φ 2.1618 < 0.9847 :=
  Phi_enc (by norm_num) 5 (by norm_num) (by emp_num) (by emp_num)

private lemma t_3_107 : (0.99903 : ℝ) < Φ 3.107 ∧ Φ 3.107 < 0.99907 :=
  Phi_enc (by norm_num) 9 (by norm_num) (by emp_num) (by emp_num)

private lemma t_3_108 : (0.99903 : ℝ) < Φ 3.108 ∧ Φ 3.108 < 0.99907 :=
  Phi_enc (by norm_num) 9 (by norm_num) (by emp_num) (by emp_num)

private lemma t_12_11 : (0.86233 : ℝ) < Φ (12 / 11 : ℝ) ∧ Φ (12 / 11 : ℝ) < 0.86235 :=
  Phi_enc (by norm_num) 3 (by norm_num) (by emp_num) (by emp_num)

private lemma t_7_11 : (0.73772 : ℝ) < Φ (7 / 11 : ℝ) ∧ Φ (7 / 11 : ℝ) < 0.73774 :=
  Phi_enc (by norm_num) 2 (by norm_num) (by emp_num) (by emp_num)

private lemma t_0_841 : (0.79979 : ℝ) < Φ 0.841 ∧ Φ 0.841 < 0.79984 :=
  Phi_enc (by norm_num) 2 (by norm_num) (by emp_num) (by emp_num)

private lemma t_0_842 : (0.80007 : ℝ) < Φ 0.842 ∧ Φ 0.842 < 0.80012 :=
  Phi_enc (by norm_num) 2 (by norm_num) (by emp_num) (by emp_num)

private lemma t_1_035 : (0.84965 : ℝ) < Φ 1.035 ∧ Φ 1.035 < 0.84967 :=
  Phi_enc (by norm_num) 3 (by norm_num) (by emp_num) (by emp_num)

private lemma t_1_037 : (0.85012 : ℝ) < Φ 1.037 ∧ Φ 1.037 < 0.85014 :=
  Phi_enc (by norm_num) 3 (by norm_num) (by emp_num) (by emp_num)

private lemma t_1_28 : (0.8997 : ℝ) < Φ 1.28 ∧ Φ 1.28 < 0.89974 :=
  Phi_enc (by norm_num) 3 (by norm_num) (by emp_num) (by emp_num)

private lemma t_1_29 : (0.90144 : ℝ) < Φ 1.29 ∧ Φ 1.29 < 0.90149 :=
  Phi_enc (by norm_num) 3 (by norm_num) (by emp_num) (by emp_num)

private lemma t_0_5838 : (0.72031 : ℝ) < Φ 0.5838 ∧ Φ 0.5838 < 0.72033 :=
  Phi_enc (by norm_num) 2 (by norm_num) (by emp_num) (by emp_num)

private lemma t_0_584 : (0.72038 : ℝ) < Φ 0.584 ∧ Φ 0.584 < 0.7204 :=
  Phi_enc (by norm_num) 2 (by norm_num) (by emp_num) (by emp_num)

private lemma t_0_3969 : (0.65417 : ℝ) < Φ 0.3969 ∧ Φ 0.3969 < 0.65429 :=
  Phi_enc (by norm_num) 1 (by norm_num) (by emp_num) (by emp_num)

private lemma t_0_397 : (0.65421 : ℝ) < Φ 0.397 ∧ Φ 0.397 < 0.65432 :=
  Phi_enc (by norm_num) 1 (by norm_num) (by emp_num) (by emp_num)

private lemma t_2_5104 : (0.99389 : ℝ) < Φ 2.5104 ∧ Φ 2.5104 < 0.994 :=
  Phi_enc (by norm_num) 6 (by norm_num) (by emp_num) (by emp_num)

private lemma t_2_5106 : (0.99389 : ℝ) < Φ 2.5106 ∧ Φ 2.5106 < 0.994 :=
  Phi_enc (by norm_num) 6 (by norm_num) (by emp_num) (by emp_num)

private lemma t_1_7497 : (0.95987 : ℝ) < Φ 1.7497 ∧ Φ 1.7497 < 0.95993 :=
  Phi_enc (by norm_num) 4 (by norm_num) (by emp_num) (by emp_num)

private lemma t_1_7498 : (0.95988 : ℝ) < Φ 1.7498 ∧ Φ 1.7498 < 0.95994 :=
  Phi_enc (by norm_num) 4 (by norm_num) (by emp_num) (by emp_num)

private lemma t_0_994 : (0.83987 : ℝ) < Φ 0.994 ∧ Φ 0.994 < 0.8399 :=
  Phi_enc (by norm_num) 3 (by norm_num) (by emp_num) (by emp_num)

private lemma t_0_995 : (0.84012 : ℝ) < Φ 0.995 ∧ Φ 0.995 < 0.84014 :=
  Phi_enc (by norm_num) 3 (by norm_num) (by emp_num) (by emp_num)

private lemma t_0_674 : (0.74983 : ℝ) < Φ 0.674 ∧ Φ 0.674 < 0.74985 :=
  Phi_enc (by norm_num) 2 (by norm_num) (by emp_num) (by emp_num)

private lemma t_0_675 : (0.75015 : ℝ) < Φ 0.675 ∧ Φ 0.675 < 0.75017 :=
  Phi_enc (by norm_num) 2 (by norm_num) (by emp_num) (by emp_num)

/-! ### Helpers -/

private lemma sqrt_144 : Real.sqrt 144 = 12 := by
  rw [show (144 : ℝ) = 12 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)

section Helpers

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}

/-- A normal law with variance `v ≥ 0` has standard deviation `√v`. -/
private lemma law_sqrt {μ v : ℝ} (hv : 0 ≤ v) (hX : HasLaw X (gaussianReal μ v.toNNReal) P) :
    HasLaw X (gaussianReal μ ((Real.sqrt v) ^ 2).toNNReal) P := by
  rwa [Real.sq_sqrt hv]

/-- A number `k` with `P(X ≤ k) = p` lies between the values given by `z`-scores `lo` and `hi`
whenever `Φ lo < p < Φ hi`. -/
private lemma pct {μ σ : ℝ} (hσ : 0 < σ) (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P)
    {p lo hi : ℝ} (h0 : 0 < p) (h1 : p < 1) (hlo : Φ lo < p) (hhi : p < Φ hi) {k : ℝ}
    (hk : P.real {ω | X ω ≤ k} = p) : μ + σ * lo < k ∧ k < μ + σ * hi := by
  obtain ⟨k', hk', h1', h2'⟩ := percentile_bd hσ hX h0 h1 hlo hhi
  have e : k = k' := ((normal_percentile hσ hX h0 h1).2 k hk).trans
    ((normal_percentile hσ hX h0 h1).2 k' hk').symm
  rw [e]
  exact ⟨h1', h2'⟩

end Helpers

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}

/-! ### Section 7.1: sample means -/

/-- OpenStax Introductory Statistics 2e Try It 7.1. A population has mean 45 and standard deviation 8;
the mean of a sample of 30 has the normal law with mean 45 and variance `8²/30`. The probability that
it lies between 42 and 50 is enclosed in `(0.9785, 0.9801)`. -/
@[kb "openstaxintrostats2e" "Try It 7.1, p. 380"]
theorem tryit_7_1_mean_between [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal 45 ((8 ^ 2 / 30 : ℝ).toNNReal)) P) :
    0.9785 < P.real {ω | 42 < X ω ∧ X ω < 50} ∧ P.real {ω | 42 < X ω ∧ X ω < 50} < 0.9801 := by
  have hs := sqrt_bd (n := (30 : ℝ)) (a := 5.4772) (b := 5.4773) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hne : Real.sqrt 30 ≠ 0 := by positivity
  have hpos : 0 < 8 / Real.sqrt 30 := by positivity
  have hX' := law_mean (s := 8) (n := 30) (by norm_num) hX
  have hP := prob_Ioo hpos hX' (a := 42) (b := 50) (by norm_num)
  have e1 : (50 - 45) / (8 / Real.sqrt 30) = 0.625 * Real.sqrt 30 := by
    field_simp; norm_num
  have e2 : (42 - 45) / (8 / Real.sqrt 30) = -(0.375 * Real.sqrt 30) := by
    field_simp; norm_num
  rw [hP, e1, e2, stdNormalCdf_neg]
  have h3 := Phi_between (z := 0.375 * Real.sqrt 30) (lo := 2.0539) (hi := 2.054)
    (by linarith [hs.1]) (by linarith [hs.2]) t_2_0539.1 t_2_054.2
  have h4 : (0.99862 : ℝ) < Φ (0.625 * Real.sqrt 30) :=
    lt_of_lt_of_le phi_3.1 (Phi_mono (by linarith [hs.1]))
  have h5 := Phi_lt_one (0.625 * Real.sqrt 30)
  constructor <;> linarith [h3.1, h3.2]

/-- OpenStax Introductory Statistics 2e Try It 7.2. SAT times are normal with mean 2.5 and standard
deviation 0.25 hours; the mean of 60 students has the normal law with mean 2.5 and variance `0.25²/60`.
The probability that it lies between 2 and 3 hours is enclosed in `(0.9994, 1)` (the book: about 1). -/
@[kb "openstaxintrostats2e" "Try It 7.2, p. 381"]
theorem tryit_7_2_sat_mean_between [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal 2.5 ((0.25 ^ 2 / 60 : ℝ).toNNReal)) P) :
    0.9994 < P.real {ω | 2 < X ω ∧ X ω < 3} ∧ P.real {ω | 2 < X ω ∧ X ω < 3} < 1 := by
  have hs := sqrt_bd (n := (60 : ℝ)) (a := 7.7459) (b := 7.7460) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hne : Real.sqrt 60 ≠ 0 := by positivity
  have hpos : 0 < 0.25 / Real.sqrt 60 := by positivity
  have hX' := law_mean (s := 0.25) (n := 60) (by norm_num) hX
  have hP := prob_Ioo hpos hX' (a := 2) (b := 3) (by norm_num)
  have e1 : (3 - 2.5) / (0.25 / Real.sqrt 60) = 2 * Real.sqrt 60 := by
    field_simp; norm_num
  have e2 : (2 - 2.5) / (0.25 / Real.sqrt 60) = -(2 * Real.sqrt 60) := by
    field_simp; norm_num
  rw [hP, e1, e2, stdNormalCdf_neg]
  have h4 : (0.99973 : ℝ) < Φ (2 * Real.sqrt 60) :=
    lt_of_lt_of_le phi_3_5.1 (Phi_mono (by linarith [hs.1]))
  have h5 := Phi_lt_one (2 * Real.sqrt 60)
  constructor <;> linarith

/-- OpenStax Introductory Statistics 2e Try It 7.3. Strategy players have mean age 28 and standard
deviation 4.8; for 100 players the standard deviation of the mean is `4.8/√100 = 0.48`, and the mean has
the normal law with mean 28. The probability that it lies in the target range 29 to 35 is enclosed in
`(0.0183, 0.0187)`, small, so the target market is unlikely to match the sample (the book's conclusion
is verbal). -/
@[kb "openstaxintrostats2e" "Try It 7.3, p. 382"]
theorem tryit_7_3_gamers_mean_between [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal 28 ((4.8 ^ 2 / 100 : ℝ).toNNReal)) P) :
    4.8 / Real.sqrt 100 = 0.48 ∧
      0.0183 < P.real {ω | 29 < X ω ∧ X ω < 35} ∧ P.real {ω | 29 < X ω ∧ X ω < 35} < 0.0187 := by
  have hX' := law_mean (s := 4.8) (n := 100) (by norm_num) hX
  rw [sqrt_100] at hX'
  have hσ : (0 : ℝ) < 4.8 / 10 := by norm_num
  have hP := prob_Ioo hσ hX' (a := 29) (b := 35) (by norm_num)
  have e1 : ((35 : ℝ) - 28) / (4.8 / 10) = 175 / 12 := by norm_num
  have e2 : ((29 : ℝ) - 28) / (4.8 / 10) = 25 / 12 := by norm_num
  have h4 : (0.99973 : ℝ) < Φ (175 / 12 : ℝ) :=
    lt_of_lt_of_le phi_3_5.1 (Phi_mono (by norm_num))
  have h5 := Phi_lt_one (175 / 12 : ℝ)
  refine ⟨by rw [sqrt_100]; norm_num, ?_⟩
  rw [hP, e1, e2]
  constructor <;> linarith [t_25_12.1, t_25_12.2]

/-- OpenStax Introductory Statistics 2e Try It 7.4. Cola cans with `μ = 16` and `σ = 0.143` ounces:
the mean of 34 cans has the normal law with mean 16 and variance `0.143²/34`. The probability that the
mean exceeds 16.01 lies in `(0.3417, 0.3419)`; such a probability is far from small, so a sample mean of
16.01 does not suggest overfilling. -/
@[kb "openstaxintrostats2e" "Try It 7.4, p. 382"]
theorem tryit_7_4_cola_mean_above [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal 16 ((0.143 ^ 2 / 34 : ℝ).toNNReal)) P) :
    0.3417 < P.real {ω | 16.01 < X ω} ∧ P.real {ω | 16.01 < X ω} < 0.3419 := by
  have hs := sqrt_bd (n := (34 : ℝ)) (a := 5.8309) (b := 5.831) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hne : Real.sqrt 34 ≠ 0 := by positivity
  have hσ : 0 < 0.143 / Real.sqrt 34 := by positivity
  have hX' := law_mean (s := 0.143) (n := 34) (by norm_num) hX
  have hP := prob_gt hσ hX' 16.01
  have e : (16.01 - 16) / (0.143 / Real.sqrt 34) = Real.sqrt 34 / 14.3 := by
    field_simp; norm_num
  rw [hP, e]
  have h := Phi_between (z := Real.sqrt 34 / 14.3) (lo := 0.4077) (hi := 0.4078)
    (by rw [le_div_iff₀ (by norm_num)]; linarith [hs.1])
    (by rw [div_le_iff₀ (by norm_num)]; linarith [hs.2]) t_0_4077.1 t_0_4078.2
  constructor <;> linarith [h.1, h.2]

/-! ### Section 7.2: sample sums -/

/-- OpenStax Introductory Statistics 2e Try It 7.5. The sum of 50 values from a population with mean 45
and standard deviation 8 has the normal law with mean `50 · 45 = 2250` and variance `50 · 8²`. The
probability that the sum exceeds 2400 lies in `(0.0039, 0.0041)`. -/
@[kb "openstaxintrostats2e" "Try It 7.5, p. 384"]
theorem tryit_7_5_sum_above [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal (50 * 45) ((50 * 8 ^ 2 : ℝ).toNNReal)) P) :
    0.0039 < P.real {ω | 2400 < X ω} ∧ P.real {ω | 2400 < X ω} < 0.0041 := by
  have hs := sqrt_bd (n := (50 : ℝ)) (a := 7.07106) (b := 7.07107) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hX' := law_sum (s := 8) (n := 50) (by norm_num) hX
  rw [show (50 * 45 : ℝ) = 2250 by norm_num] at hX'
  have hσ : 0 < Real.sqrt 50 * 8 := by have := hs.1; positivity
  have hP := prob_gt hσ hX' 2400
  have e : ((2400 : ℝ) - 2250) / (Real.sqrt 50 * 8) = 150 / (Real.sqrt 50 * 8) := by norm_num
  rw [hP, e]
  have h := Phi_div (c := 150) (s := Real.sqrt 50 * 8) (s1 := 56.56848) (s2 := 56.56856)
    (lo := 2.6516) (hi := 2.6517) (by norm_num) (by linarith [hs.1]) (by linarith [hs.2])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) t_2_6516.1 t_2_6517.2
  constructor <;> linarith [h.1, h.2]

/-- OpenStax Introductory Statistics 2e Try It 7.6(a). For 39 iPad users with mean age 35 and standard
deviation 10, the sum of the ages has mean `39 · 35 = 1365` and standard deviation `√39 · 10`, strictly
between `62.44` and `62.45`; its distribution is normal (hypothesis of the next two theorems). -/
@[kb "openstaxintrostats2e" "Try It 7.6, p. 385"]
theorem tryit_7_6a_mean_and_sd_of_sum :
    (39 : ℝ) * 35 = 1365 ∧ 62.44 < Real.sqrt 39 * 10 ∧ Real.sqrt 39 * 10 < 62.45 := by
  have hs := sqrt_bd (n := (39 : ℝ)) (a := 6.24499) (b := 6.245) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  refine ⟨by norm_num, by linarith [hs.1], by linarith [hs.2]⟩

/-- OpenStax Introductory Statistics 2e Try It 7.6(b). The sum of the 39 ages has the normal law with
mean `39 · 35` and variance `39 · 10²`. The probability that it lies between 1400 and 1500 is enclosed
in `(0.2721, 0.2724)`. -/
@[kb "openstaxintrostats2e" "Try It 7.6, p. 385"]
theorem tryit_7_6b_sum_between [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal (39 * 35) ((39 * 10 ^ 2 : ℝ).toNNReal)) P) :
    0.2721 < P.real {ω | 1400 < X ω ∧ X ω < 1500} ∧
      P.real {ω | 1400 < X ω ∧ X ω < 1500} < 0.2724 := by
  have hs := sqrt_bd (n := (39 : ℝ)) (a := 6.24499) (b := 6.245) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hX' := law_sum (s := 10) (n := 39) (by norm_num) hX
  rw [show (39 * 35 : ℝ) = 1365 by norm_num] at hX'
  have hσ : 0 < Real.sqrt 39 * 10 := by have := hs.1; positivity
  have hP := prob_Ioo hσ hX' (a := 1400) (b := 1500) (by norm_num)
  have e1 : ((1500 : ℝ) - 1365) / (Real.sqrt 39 * 10) = 135 / (Real.sqrt 39 * 10) := by norm_num
  have e2 : ((1400 : ℝ) - 1365) / (Real.sqrt 39 * 10) = 35 / (Real.sqrt 39 * 10) := by norm_num
  rw [hP, e1, e2]
  have h1 := Phi_div (c := 135) (s := Real.sqrt 39 * 10) (s1 := 62.4499) (s2 := 62.45)
    (lo := 2.1616) (hi := 2.1618) (by norm_num) (by linarith [hs.1]) (by linarith [hs.2])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) t_2_1616.1 t_2_1618.2
  have h2 := Phi_div (c := 35) (s := Real.sqrt 39 * 10) (s1 := 62.4499) (s2 := 62.45)
    (lo := 0.5604) (hi := 0.5605) (by norm_num) (by linarith [hs.1]) (by linarith [hs.2])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) t_0_5604.1 t_0_5605.2
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- OpenStax Introductory Statistics 2e Try It 7.6(c). For the same normal law of the sum of 39 ages, any
`k` with `P(S ≤ k) = 0.9` (the 90th percentile) lies in `(1444.9, 1445.6)`. -/
@[kb "openstaxintrostats2e" "Try It 7.6, p. 385"]
theorem tryit_7_6c_sum_percentile_90
    (hX : HasLaw X (gaussianReal (39 * 35) ((39 * 10 ^ 2 : ℝ).toNNReal)) P) {k : ℝ}
    (hk : P.real {ω | X ω ≤ k} = 9 / 10) : 1444.9 < k ∧ k < 1445.6 := by
  have hs := sqrt_bd (n := (39 : ℝ)) (a := 6.24499) (b := 6.245) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hX' := law_sum (s := 10) (n := 39) (by norm_num) hX
  rw [show (39 * 35 : ℝ) = 1365 by norm_num] at hX'
  have hσ : 0 < Real.sqrt 39 * 10 := by have := hs.1; positivity
  have := pct hσ hX' (by norm_num) (by norm_num) (lo := 1.28) (hi := 1.29)
    (by linarith [t_1_28.2]) (by linarith [t_1_29.1]) hk
  constructor <;> nlinarith [this.1, this.2, hs.1, hs.2]

/-- OpenStax Introductory Statistics 2e Try It 7.7(a). The sum of the app-engagement times of 70 users
(mean 8.2 minutes, standard deviation 1) has the normal law with mean `70 · 8.2 = 574` minutes and
variance `70`. The probability that the total is between 7 hours (420 minutes) and 10 hours
(600 minutes) is enclosed in `(0.9987, 0.9991)`: almost all samples of 70 users total between these. -/
@[kb "openstaxintrostats2e" "Try It 7.7, p. 385"]
theorem tryit_7_7a_sum_between [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal (70 * 8.2) ((70 * 1 ^ 2 : ℝ).toNNReal)) P) :
    0.9987 < P.real {ω | 420 < X ω ∧ X ω < 600} ∧ P.real {ω | 420 < X ω ∧ X ω < 600} < 0.9991 := by
  have hs := sqrt_bd (n := (70 : ℝ)) (a := 8.3666) (b := 8.3667) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hX' := law_sum (s := 1) (n := 70) (by norm_num) hX
  rw [show (70 * 8.2 : ℝ) = 574 by norm_num] at hX'
  have hσ : 0 < Real.sqrt 70 * 1 := by have := hs.1; positivity
  have hP := prob_Ioo hσ hX' (a := 420) (b := 600) (by norm_num)
  have e1 : ((600 : ℝ) - 574) / (Real.sqrt 70 * 1) = 26 / (Real.sqrt 70 * 1) := by norm_num
  have e2 : ((420 : ℝ) - 574) / (Real.sqrt 70 * 1) = -(154 / (Real.sqrt 70 * 1)) := by
    rw [← neg_div]; norm_num
  rw [hP, e1, e2, stdNormalCdf_neg]
  have h := Phi_div (c := 26) (s := Real.sqrt 70 * 1) (s1 := 8.3666) (s2 := 8.3667)
    (lo := 3.107) (hi := 3.108) (by norm_num) (by linarith [hs.1]) (by linarith [hs.2])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) t_3_107.1 t_3_108.2
  have h4 : (0.99973 : ℝ) < Φ (154 / (Real.sqrt 70 * 1)) :=
    lt_of_lt_of_le phi_3_5.1 (Phi_mono (by rw [le_div_iff₀ hσ]; linarith [hs.2]))
  have h5 := Phi_lt_one (154 / (Real.sqrt 70 * 1))
  constructor <;> linarith [h.1, h.2]

/-- OpenStax Introductory Statistics 2e Try It 7.7(b). For the same normal law of the total time of 70
users, any `k₈₄` with `P(S ≤ k₈₄) = 0.84` lies in `(582.31, 582.33)` and any `k₁₆` with
`P(S ≤ k₁₆) = 0.16` lies in `(565.67, 565.69)` minutes. -/
@[kb "openstaxintrostats2e" "Try It 7.7, p. 385"]
theorem tryit_7_7b_sum_percentiles
    (hX : HasLaw X (gaussianReal (70 * 8.2) ((70 * 1 ^ 2 : ℝ).toNNReal)) P) {k84 k16 : ℝ}
    (h84 : P.real {ω | X ω ≤ k84} = 21 / 25) (h16 : P.real {ω | X ω ≤ k16} = 4 / 25) :
    (582.31 < k84 ∧ k84 < 582.33) ∧ (565.67 < k16 ∧ k16 < 565.69) := by
  have hs := sqrt_bd (n := (70 : ℝ)) (a := 8.3666) (b := 8.3667) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hX' := law_sum (s := 1) (n := 70) (by norm_num) hX
  rw [show (70 * 8.2 : ℝ) = 574 by norm_num] at hX'
  have hσ : 0 < Real.sqrt 70 * 1 := by have := hs.1; positivity
  have l : Φ 0.994 < 21 / 25 := by linarith [t_0_994.2]
  have g : 21 / 25 < Φ 0.995 := by linarith [t_0_995.1]
  have l' : Φ (-0.995) < 4 / 25 := by rw [stdNormalCdf_neg]; linarith [t_0_995.1]
  have g' : 4 / 25 < Φ (-0.994) := by rw [stdNormalCdf_neg]; linarith [t_0_994.2]
  have a := pct hσ hX' (by norm_num) (by norm_num) l g h84
  have b := pct hσ hX' (by norm_num) (by norm_num) l' g' h16
  refine ⟨⟨by nlinarith [a.1, hs.1], by nlinarith [a.2, hs.2]⟩,
    ⟨by nlinarith [b.1, hs.2], by nlinarith [b.2, hs.1]⟩⟩

/-! ### Section 7.3: using the central limit theorem -/

/-- OpenStax Introductory Statistics 2e Try It 7.8(a), (c). A stress score uniform on `[1, 5]` has mean 3
and variance `4²/12`; the mean of 55 scores has the normal law with mean 3 and variance `4²/12/55`.
The probability that it is below 7 lies in `(0.9986, 1)` (the book: about 1), and any 80th percentile `k`
of the mean lies in `(3.13, 3.132)`. -/
@[kb "openstaxintrostats2e" "Try It 7.8, p. 388"]
theorem tryit_7_8ac_mean [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal 3 ((4 ^ 2 / 12 / 55 : ℝ).toNNReal)) P) {k : ℝ}
    (hk : P.real {ω | X ω ≤ k} = 4 / 5) :
    (0.9986 < P.real {ω | X ω < 7} ∧ P.real {ω | X ω < 7} < 1) ∧ 3.13 < k ∧ k < 3.132 := by
  have hs := sqrt_bd (n := (4 ^ 2 / 12 / 55 : ℝ)) (a := 0.15569) (b := 0.1557) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have hX' := law_sqrt (by norm_num) hX
  have hσ : 0 < Real.sqrt (4 ^ 2 / 12 / 55 : ℝ) := lt_trans (by norm_num) hs.1
  refine ⟨?_, ?_⟩
  · rw [prob_lt hσ hX' 7]
    have h4 : (0.99862 : ℝ) < Φ (((7 : ℝ) - 3) / Real.sqrt (4 ^ 2 / 12 / 55 : ℝ)) :=
      lt_of_lt_of_le phi_3.1
        (Phi_mono (by rw [le_div_iff₀ hσ]; linarith [hs.2]))
    exact ⟨by linarith, Phi_lt_one _⟩
  · have := pct hσ hX' (by norm_num) (by norm_num) (lo := 0.841) (hi := 0.842)
      (by linarith [t_0_841.2]) (by linarith [t_0_842.1]) hk
    constructor <;> linarith [this.1, this.2, hs.1, hs.2]

/-- OpenStax Introductory Statistics 2e Try It 7.8(b), (d). The sum of 55 stress scores has the normal
law with mean `55 · 3 = 165` and variance `55 · (4²/12)`. The probability that the sum exceeds 170 lies in
`(0.2795, 0.2797)`, and any 85th percentile `k` of the sum lies in `(173.86, 173.89)`. -/
@[kb "openstaxintrostats2e" "Try It 7.8, p. 388"]
theorem tryit_7_8bd_sum [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal (55 * 3) ((55 * (4 ^ 2 / 12) : ℝ).toNNReal)) P) {k : ℝ}
    (hk : P.real {ω | X ω ≤ k} = 17 / 20) :
    (0.2795 < P.real {ω | 170 < X ω} ∧ P.real {ω | 170 < X ω} < 0.2797) ∧
      173.86 < k ∧ k < 173.89 := by
  have hs := sqrt_bd (n := (55 * (4 ^ 2 / 12) : ℝ)) (a := 8.5634) (b := 8.5635) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  rw [show (55 * 3 : ℝ) = 165 by norm_num] at hX
  have hX' := law_sqrt (by norm_num) hX
  have hσ : 0 < Real.sqrt (55 * (4 ^ 2 / 12) : ℝ) := lt_trans (by norm_num) hs.1
  refine ⟨?_, ?_⟩
  · rw [prob_gt hσ hX' 170]
    have e : ((170 : ℝ) - 165) / Real.sqrt (55 * (4 ^ 2 / 12) : ℝ) =
        5 / Real.sqrt (55 * (4 ^ 2 / 12) : ℝ) := by norm_num
    rw [e]
    have h := Phi_div (c := 5) (s := Real.sqrt (55 * (4 ^ 2 / 12) : ℝ)) (s1 := 8.5634)
      (s2 := 8.5635) (lo := 0.5838) (hi := 0.584) (by norm_num) hs.1 hs.2 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) t_0_5838.1 t_0_584.2
    constructor <;> linarith [h.1, h.2]
  · have := pct hσ hX' (by norm_num) (by norm_num) (lo := 1.035) (hi := 1.037)
      (by linarith [t_1_035.2]) (by linarith [t_1_037.1]) hk
    constructor <;> linarith [this.1, this.2, hs.1, hs.2]

/-- OpenStax Introductory Statistics 2e Try It 7.9(a), (c). An excess time is exponential with mean 22
minutes (standard deviation 22); the mean of 144 has the normal law with mean 22 and variance `22²/144`
(standard deviation `22/12`). The probability that it lies between 20 and 30 is enclosed in
`(0.862, 0.8624)`, and any 75th percentile `k` of the mean lies in `(23.23, 23.24)`. -/
@[kb "openstaxintrostats2e" "Try It 7.9, p. 390"]
theorem tryit_7_9ac_mean [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal 22 ((22 ^ 2 / 144 : ℝ).toNNReal)) P) {k : ℝ}
    (hk : P.real {ω | X ω ≤ k} = 3 / 4) :
    (0.862 < P.real {ω | 20 < X ω ∧ X ω < 30} ∧ P.real {ω | 20 < X ω ∧ X ω < 30} < 0.8624) ∧
      23.23 < k ∧ k < 23.24 := by
  have hX' := law_mean (s := 22) (n := 144) (by norm_num) hX
  rw [sqrt_144] at hX'
  have hσ : (0 : ℝ) < 22 / 12 := by norm_num
  refine ⟨?_, ?_⟩
  · have hP := prob_Ioo hσ hX' (a := 20) (b := 30) (by norm_num)
    have e1 : ((30 : ℝ) - 22) / (22 / 12) = 48 / 11 := by norm_num
    have e2 : ((20 : ℝ) - 22) / (22 / 12) = -(12 / 11) := by norm_num
    rw [hP, e1, e2, stdNormalCdf_neg]
    have h4 : (0.99973 : ℝ) < Φ (48 / 11 : ℝ) :=
      lt_of_lt_of_le phi_3_5.1 (Phi_mono (by norm_num))
    have h5 := Phi_lt_one (48 / 11 : ℝ)
    constructor <;> linarith [t_12_11.1, t_12_11.2]
  · have l : Φ 0.674 < 3 / 4 := by linarith [t_0_674.2]
    have g : 3 / 4 < Φ 0.675 := by linarith [t_0_675.1]
    have := pct hσ hX' (by norm_num) (by norm_num) l g hk
    constructor <;> linarith [this.1, this.2]

/-- OpenStax Introductory Statistics 2e Try It 7.9(b), (d). The sum of 144 excess times has the normal
law with mean `144 · 22 = 3168` and variance `144 · 22²` (standard deviation `12 · 22 = 264`). The
probability that the sum is at least 3000 lies in `(0.7377, 0.7378)`, and any 85th percentile `k` of the
sum lies in `(3441.2, 3441.8)`. -/
@[kb "openstaxintrostats2e" "Try It 7.9, p. 390"]
theorem tryit_7_9bd_sum [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal (144 * 22) ((144 * 22 ^ 2 : ℝ).toNNReal)) P) {k : ℝ}
    (hk : P.real {ω | X ω ≤ k} = 17 / 20) :
    (0.7377 < P.real {ω | 3000 ≤ X ω} ∧ P.real {ω | 3000 ≤ X ω} < 0.7378) ∧
      3441.2 < k ∧ k < 3441.8 := by
  have hX' := law_sum (s := 22) (n := 144) (by norm_num) hX
  rw [sqrt_144, show (144 * 22 : ℝ) = 3168 by norm_num] at hX'
  have hσ : (0 : ℝ) < 12 * 22 := by norm_num
  refine ⟨?_, ?_⟩
  · rw [prob_ge hσ hX' 3000]
    have e : ((3000 : ℝ) - 3168) / (12 * 22) = -(7 / 11) := by norm_num
    rw [e, stdNormalCdf_neg]
    constructor <;> linarith [t_7_11.1, t_7_11.2]
  · have := pct hσ hX' (by norm_num) (by norm_num) (lo := 1.035) (hi := 1.037)
      (by linarith [t_1_035.2]) (by linarith [t_1_037.1]) hk
    constructor <;> linarith [this.1, this.2]

/-- OpenStax Introductory Statistics 2e Try It 7.10(a). Systolic blood pressure `X ~ N(114.8, 13.1²)`:
the probability that one woman exceeds 120 lies in `(0.3456, 0.3459)`. -/
@[kb "openstaxintrostats2e" "Try It 7.10, p. 391"]
theorem tryit_7_10a_individual_above_120 [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal 114.8 ((13.1 : ℝ) ^ 2).toNNReal) P) :
    0.3456 < P.real {ω | 120 < X ω} ∧ P.real {ω | 120 < X ω} < 0.3459 := by
  rw [prob_gt (by norm_num) hX 120]
  have e : ((120 : ℝ) - 114.8) / 13.1 = 52 / 131 := by norm_num
  rw [e]
  have h := Phi_between (z := (52 / 131 : ℝ)) (lo := 0.3969) (hi := 0.397) (by norm_num)
    (by norm_num) t_0_3969.1 t_0_397.2
  constructor <;> linarith [h.1, h.2]

/-- OpenStax Introductory Statistics 2e Try It 7.10(b). The mean pressure of 40 women has the normal law
with mean 114.8 and variance `13.1²/40`; the probability that it exceeds 120 lies in `(0.0059, 0.0062)`,
much smaller than the probability for one woman. -/
@[kb "openstaxintrostats2e" "Try It 7.10, p. 391"]
theorem tryit_7_10b_mean_above_120 [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal 114.8 ((13.1 ^ 2 / 40 : ℝ).toNNReal)) P) :
    0.0059 < P.real {ω | 120 < X ω} ∧ P.real {ω | 120 < X ω} < 0.0062 := by
  have hs := sqrt_bd (n := (40 : ℝ)) (a := 6.3245) (b := 6.3246) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hne : Real.sqrt 40 ≠ 0 := by positivity
  have hσ : 0 < 13.1 / Real.sqrt 40 := by positivity
  have hX' := law_mean (s := 13.1) (n := 40) (by norm_num) hX
  rw [prob_gt hσ hX' 120]
  have e : ((120 : ℝ) - 114.8) / (13.1 / Real.sqrt 40) = (52 / 131) * Real.sqrt 40 := by
    field_simp; norm_num
  rw [e]
  have h := Phi_between (z := (52 / 131) * Real.sqrt 40) (lo := 2.5104) (hi := 2.5106)
    (by linarith [hs.1]) (by linarith [hs.2]) t_2_5104.1 t_2_5106.2
  constructor <;> linarith [h.1, h.2]

/-- OpenStax Introductory Statistics 2e Try It 7.11(a). Men's heights `X ~ N(69, 2.8²)`: any height `k`
with `P(X ≤ k) = 0.95` lies in `(73.59, 73.62)` inches, so a 72-inch doorway is lower than it. -/
@[kb "openstaxintrostats2e" "Try It 7.11, p. 391"]
theorem tryit_7_11a_doorway_individual
    (hX : HasLaw X (gaussianReal 69 ((2.8 : ℝ) ^ 2).toNNReal) P) {k : ℝ}
    (hk : P.real {ω | X ω ≤ k} = 19 / 20) : (73.59 < k ∧ k < 73.62) ∧ 72 < k := by
  have := pct (by norm_num) hX (by norm_num) (by norm_num) (lo := 1.64) (hi := 1.65)
    (by linarith [phi_1_64.2]) (by linarith [phi_1_65.1]) hk
  refine ⟨⟨by linarith [this.1], by linarith [this.2]⟩, by linarith [this.1]⟩

/-- OpenStax Introductory Statistics 2e Try It 7.11(b). The mean height of 100 men has the normal law
with mean 69 and variance `2.8²/100` (standard deviation `0.28`); the height `h` with
`P(X̄ ≤ h) = 0.95` lies in `(69.45, 69.47)` inches. -/
@[kb "openstaxintrostats2e" "Try It 7.11, p. 391"]
theorem tryit_7_11b_doorway_mean
    (hX : HasLaw X (gaussianReal 69 ((2.8 ^ 2 / 100 : ℝ).toNNReal)) P) {h : ℝ}
    (hk : P.real {ω | X ω ≤ h} = 19 / 20) : 69.45 < h ∧ h < 69.47 := by
  have hX' := law_mean (s := 2.8) (n := 100) (by norm_num) hX
  rw [sqrt_100] at hX'
  have := pct (by norm_num : (0 : ℝ) < 2.8 / 10) hX' (by norm_num) (by norm_num) (lo := 1.64)
    (hi := 1.65) (by linarith [phi_1_64.2]) (by linarith [phi_1_65.1]) hk
  constructor <;> linarith [this.1, this.2]

/-! ### Section 7.4: normal approximation to the binomial -/

/-- OpenStax Introductory Statistics 2e Try It 7.12. With `n = 500` and `p = 0.46` the binomial count has
mean `np = 230` and variance `npq = 124.2`; for its normal approximation `Y`, the continuity-corrected
probability of at least 250 successes, `P(Y ≥ 249.5)`, lies in `(0.04, 0.0402)`. -/
@[kb "openstaxintrostats2e" "Try It 7.12, p. 393"]
theorem tryit_7_12_at_least_250 [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal (500 * 0.46) ((500 * 0.46 * 0.54 : ℝ).toNNReal)) P) :
    (500 : ℝ) * 0.46 = 230 ∧ (500 : ℝ) * 0.46 * 0.54 = 124.2 ∧
      0.04 < P.real {ω | 249.5 ≤ X ω} ∧ P.real {ω | 249.5 ≤ X ω} < 0.0402 := by
  have hs := sqrt_bd (n := (124.2 : ℝ)) (a := 11.1445) (b := 11.1446) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have e : (500 * 0.46 * 0.54 : ℝ) = (Real.sqrt 124.2) ^ 2 := by
    rw [Real.sq_sqrt (by norm_num)]; norm_num
  rw [e, show (500 * 0.46 : ℝ) = 230 by norm_num] at hX
  have hσ : 0 < Real.sqrt 124.2 := by have := hs.1; positivity
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [prob_ge hσ hX 249.5]
  have e1 : ((249.5 : ℝ) - 230) / Real.sqrt 124.2 = 19.5 / Real.sqrt 124.2 := by norm_num
  rw [e1]
  have h := Phi_div (c := 19.5) (s := Real.sqrt 124.2) (s1 := 11.1445) (s2 := 11.1446)
    (lo := 1.7497) (hi := 1.7498) (by norm_num) hs.1 hs.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) t_1_7497.1 t_1_7498.2
  constructor <;> linarith [h.1, h.2]

end UndergradKB.Statistics.Course.TryItC7
