import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Probability.Distributions.Poisson.Basic
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Continuous
import UndergradKB.Statistics.Waiting

/-!
# Course layer, chapter 5 (OpenStax *Introductory Statistics 2e*): "Try It" exercises

Uniform and exponential exercises, proved exactly or with two-sided numerical bounds.
A uniform variable on `[a, b]` is `pdf.IsUniform X (Icc a b) P`; an exponential variable with decay
rate `m` is `HasLaw X (expMeasure m) P` (mean `1/m`).
-/

namespace UndergradKB.Statistics.Course.TryItC5

open MeasureTheory ProbabilityTheory Set Real UndergradKB.Statistics

/-- Two-sided bound on `exp t` from the Taylor bound at `x = t / k` (private helper). -/
private lemma exp_in {t x lo hi : ℝ} (k : ℕ) (hx : x * k = t) (hx1 : |x| ≤ 1) (h0 : 0 ≤ lo)
    (hl : lo ≤ (∑ m ∈ Finset.range 10, x ^ m / m.factorial) - |x| ^ 10 * (11 / (10 * 3628800)))
    (hh : (∑ m ∈ Finset.range 10, x ^ m / m.factorial) + |x| ^ 10 * (11 / (10 * 3628800)) ≤ hi) :
    lo ^ k ≤ exp t ∧ exp t ≤ hi ^ k := by
  have h := Real.exp_bound hx1 (n := 10) (by norm_num)
  have h' : |x| ^ 10 * ((Nat.succ 10 : ℕ) / ((Nat.factorial 10 : ℕ) * (10 : ℕ))) =
      |x| ^ 10 * (11 / (10 * 3628800)) := by norm_num [Nat.factorial]
  rw [h', abs_le] at h
  have e : exp t = exp x ^ k := by rw [← Real.exp_nat_mul, ← hx]; ring_nf
  rw [e]
  exact ⟨pow_le_pow_left₀ h0 (by linarith [h.1]) k,
    pow_le_pow_left₀ (by linarith [h.1, Real.exp_pos x]) (by linarith [h.2]) k⟩

/-- Interval probability of the exponential law (private helper). -/
private lemma expMeasure_Ioo_real {m : ℝ} (hm : 0 < m) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (expMeasure m).real (Ioo a b) = exp (-(m * a)) - exp (-(m * b)) := by
  have := isProbabilityMeasure_expMeasure hm
  have hnoatom : NullSingletonClass (expMeasure m) := by
    refine ⟨fun x => ?_⟩
    have h : expMeasure m ≪ (volume : Measure ℝ) := withDensity_absolutelyContinuous _ _
    exact h (Real.volume_singleton)
  rw [measureReal_congr Ioo_ae_eq_Ioc, ← Ioi_sdiff_Ioi,
    measureReal_sdiff (Ioi_subset_Ioi hab) measurableSet_Ioi,
    expMeasure_Ioi_real hm ha, expMeasure_Ioi_real hm (ha.trans hab)]

private lemma real_Iic (μ : Measure ℕ) [IsFiniteMeasure μ] (k : ℕ) :
    μ.real (Set.Iic k) = ∑ j ∈ Finset.range (k + 1), μ.real {j} := by
  have : (Set.Iic k : Set ℕ) = ↑(Finset.range (k + 1)) := by
    ext; simp
  rw [this, sum_measureReal_singleton]

section Helpers

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}

private lemma exp_between_real {m : ℝ} (hX : HasLaw X (expMeasure m) P) (hm : 0 < m) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    P.real {ω | a < X ω ∧ X ω < b} = exp (-(m * a)) - exp (-(m * b)) := by
  rw [hX.measureReal_eq (p := fun y => a < y ∧ y < b) measurableSet_Ioo]
  exact expMeasure_Ioo_real hm ha hab

private lemma unif_real {a b : ℝ} (hX : pdf.IsUniform X (Icc a b) P) (hab : a < b) {c d : ℝ}
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    P.real {ω | c < X ω ∧ X ω < d} = (d - c) / (b - a) := by
  rw [measureReal_def, uniform_prob_Ioo hX hab hac hcd hdb,
    ENNReal.toReal_ofReal (div_nonneg (by linarith) (by linarith))]

private lemma unif_cond_real {a b : ℝ} (hX : pdf.IsUniform X (Icc a b) P) (hab : a < b) {c d : ℝ}
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) (hcb : c < b) :
    (P[X ⁻¹' Ioi d | X ⁻¹' Ioi c]).toReal = (b - d) / (b - c) := by
  rw [uniform_cond_Ioi hX hab hac hcd hdb hcb,
    ENNReal.toReal_ofReal (div_nonneg (by linarith) (by linarith))]

end Helpers

section Uniform

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}

/-- OpenStax Introductory Statistics 2e Try It 5.1. A variable with constant density `1/8` on
`[0, 8]` is uniform on `[0, 8]`; the probability that it lies between 2.5 and 7.5 is `5/8`. -/
@[kb "openstaxintrostats2e" "Try It 5.1, p. 307"]
theorem tryit_5_1_uniform_probability (hX : pdf.IsUniform X (Icc 0 8) P) :
    P.real {ω | 2.5 < X ω ∧ X ω < 7.5} = 5 / 8 := by
  rw [unif_real hX (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; norm_num

/-- OpenStax Introductory Statistics 2e Try It 5.2. Fish weights equally likely between 0 and 14
pounds are uniform on `[0, 14]` (so `a = 0`, `b = 14`); the theoretical mean is `7`, the variance
is `14²/12`, and the standard deviation lies strictly between `4.04` and `4.05`. -/
@[kb "openstaxintrostats2e" "Try It 5.2, p. 308"]
theorem tryit_5_2_uniform_mean_sd (hX : pdf.IsUniform X (Icc 0 14) P) :
    P[X] = 7 ∧ variance X P = 14 ^ 2 / 12 ∧ 4.04 < Real.sqrt (variance X P) ∧
      Real.sqrt (variance X P) < 4.05 := by
  have hv : variance X P = 14 ^ 2 / 12 := by
    rw [uniform_variance hX (by norm_num)]; norm_num
  refine ⟨?_, hv, ?_, ?_⟩
  · rw [uniform_mean hX (by norm_num)]; norm_num
  · rw [hv]; exact (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  · rw [hv]; exact (Real.sqrt_lt' (by norm_num)).2 (by norm_num)

/-- OpenStax Introductory Statistics 2e Try It 5.3. For `X ~ U(0, 20)`, the probability that
`2 < X < 18` is `4/5`, and the 90th percentile is `18`: `P(0 < X < 18) = 9/10`. -/
@[kb "openstaxintrostats2e" "Try It 5.3, p. 310"]
theorem tryit_5_3_uniform_probability_percentile (hX : pdf.IsUniform X (Icc 0 20) P) :
    P.real {ω | 2 < X ω ∧ X ω < 18} = 4 / 5 ∧ P.real {ω | 0 < X ω ∧ X ω < 18} = 9 / 10 := by
  constructor <;>
  · rw [unif_real hX (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; norm_num

/-- OpenStax Introductory Statistics 2e Try It 5.4(c). Season length of baseball games is uniform on
`[447, 521]` hours (so `a = 447` and `b = 521`); the mean is `484` and the standard deviation
(`74/√12`) lies strictly between `21.36` and `21.37`. -/
@[kb "openstaxintrostats2e" "Try It 5.4, p. 311"]
theorem tryit_5_4_uniform_mean_sd (hX : pdf.IsUniform X (Icc 447 521) P) :
    P[X] = 484 ∧ variance X P = 74 ^ 2 / 12 ∧ 21.36 < Real.sqrt (variance X P) ∧
      Real.sqrt (variance X P) < 21.37 := by
  have hv : variance X P = 74 ^ 2 / 12 := by
    rw [uniform_variance hX (by norm_num)]; norm_num
  refine ⟨?_, hv, ?_, ?_⟩
  · rw [uniform_mean hX (by norm_num)]; norm_num
  · rw [hv]; exact (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  · rw [hv]; exact (Real.sqrt_lt' (by norm_num)).2 (by norm_num)

/-- OpenStax Introductory Statistics 2e Try It 5.4(d, e). For a season length uniform on
`[447, 521]` hours, the probability of a value between 480 and 500 is `10/37`, and the 65th
percentile is `495.1` hours: `P(447 < X < 495.1) = 13/20`. -/
@[kb "openstaxintrostats2e" "Try It 5.4, p. 311"]
theorem tryit_5_4_uniform_probability_percentile (hX : pdf.IsUniform X (Icc 447 521) P) :
    P.real {ω | 480 < X ω ∧ X ω < 500} = 10 / 37 ∧
      P.real {ω | 447 < X ω ∧ X ω < 495.1} = 13 / 20 := by
  constructor <;>
  · rw [unif_real hX (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; norm_num

/-- OpenStax Introductory Statistics 2e Try It 5.5. A quiz time uniform on `[6, 15]` minutes is at
least 8 minutes with probability `7/9`; given that the student has already taken more than 7
minutes, the chance of taking more than 8 is `7/8`. -/
@[kb "openstaxintrostats2e" "Try It 5.5, p. 312"]
theorem tryit_5_5_uniform_probability_conditional (hX : pdf.IsUniform X (Icc 6 15) P) :
    P.real {ω | 8 < X ω ∧ X ω < 15} = 7 / 9 ∧
      (P[X ⁻¹' Ioi 8 | X ⁻¹' Ioi 7]).toReal = 7 / 8 := by
  constructor
  · rw [unif_real hX (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; norm_num
  · rw [unif_cond_real hX (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    norm_num

/-- OpenStax Introductory Statistics 2e Try It 5.6(d, e). An oil-change time uniform on `[11, 21]`
minutes exceeds 19 minutes (that is, lies between 19 and 21) with probability `1/5`, and its 50th
percentile (median) is `16`: `P(11 < X < 16) = 1/2`. -/
@[kb "openstaxintrostats2e" "Try It 5.6, p. 314"]
theorem tryit_5_6_uniform_probability_median (hX : pdf.IsUniform X (Icc 11 21) P) :
    P.real {ω | 19 < X ω ∧ X ω < 21} = 1 / 5 ∧ P.real {ω | 11 < X ω ∧ X ω < 16} = 1 / 2 := by
  constructor <;>
  · rw [unif_real hX (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; norm_num

end Uniform

section Exponential

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}

/-- OpenStax Introductory Statistics 2e Try It 5.7. Shopping time for anniversary cards has mean 8
minutes, so `X ~ Exp(1/8)`: the mean and the standard deviation are both 8, and the density is
`(1/8) e^{-x/8}` for `x ≥ 0` (as an extended-real value). -/
@[kb "openstaxintrostats2e" "Try It 5.7, p. 315"]
theorem tryit_5_7_exponential_distribution (hX : HasLaw X (expMeasure (1 / 8)) P) :
    P[X] = 8 ∧ Real.sqrt (variance X P) = 8 ∧
      ∀ x : ℝ, 0 ≤ x → exponentialPDF (1 / 8) x = ENNReal.ofReal (1 / 8 * exp (-(x / 8))) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [expectation_of_hasLaw_exp hX (by norm_num)]; norm_num
  · rw [variance_of_hasLaw_exp hX (by norm_num)]
    rw [show (1 : ℝ) / (1 / 8) ^ 2 = 8 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  · intro x hx
    rw [exponentialPDF_eq, if_pos hx]
    congr 3
    ring

/-- OpenStax Introductory Statistics 2e Try It 5.8(a). Days of advance purchase are exponential with
mean 15 (rate `1/15`); fewer than ten days has probability `1 - e^{-2/3}`, strictly between
`0.4865` and `0.4867`. -/
@[kb "openstaxintrostats2e" "Try It 5.8, p. 317"]
theorem tryit_5_8_exponential_fewer_than_ten (hX : HasLaw X (expMeasure (1 / 15)) P) :
    P.real {ω | 0 < X ω ∧ X ω < 10} = 1 - exp (-(2 / 3)) ∧
      0.4865 < P.real {ω | 0 < X ω ∧ X ω < 10} ∧ P.real {ω | 0 < X ω ∧ X ω < 10} < 0.4867 := by
  have h : P.real {ω | 0 < X ω ∧ X ω < 10} = 1 - exp (-(2 / 3)) := by
    rw [exp_between_real hX (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  obtain ⟨a1, a2⟩ := exp_in (t := -(2 / 3)) (x := -(2 / 3)) (lo := 0.5134) (hi := 0.51343) 1
    (by norm_num) (by norm_num [abs_neg]) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg])
    (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg])
  norm_num at a1 a2
  refine ⟨h, ?_, ?_⟩ <;> rw [h] <;> linarith

/-- OpenStax Introductory Statistics 2e Try It 5.8(b). Half of all travelers buy their ticket within
the median `-ln(1 - 1/2)/(1/15) = 15 ln 2` days, which lies strictly between `10.39` and `10.40`. -/
@[kb "openstaxintrostats2e" "Try It 5.8, p. 317"]
theorem tryit_5_8_exponential_median (hX : HasLaw X (expMeasure (1 / 15)) P) :
    P.real {ω | X ω ≤ 15 * Real.log 2} = 1 / 2 ∧ 10.39 < 15 * Real.log 2 ∧
      15 * Real.log 2 < 10.40 := by
  have h := expMeasure_percentile_of_hasLaw hX (m := 1 / 15) (by norm_num) (p := 1 / 2)
    (by norm_num) (by norm_num)
  have e : -Real.log (1 - 1 / 2) / (1 / 15) = 15 * Real.log 2 := by
    rw [show (1 : ℝ) - 1 / 2 = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]; ring
  rw [e] at h
  refine ⟨h, ?_, ?_⟩ <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- OpenStax Introductory Statistics 2e Try It 5.9(a). A pair of shoes lasts an exponential time with
mean 18 months (rate `1/18`); it lasts more than 15 months with probability `e^{-5/6}`, strictly
between `0.4345` and `0.4347`. -/
@[kb "openstaxintrostats2e" "Try It 5.9, p. 319"]
theorem tryit_5_9_exponential_survival (hX : HasLaw X (expMeasure (1 / 18)) P) :
    P.real {ω | 15 < X ω} = exp (-(5 / 6)) ∧ 0.4345 < P.real {ω | 15 < X ω} ∧
      P.real {ω | 15 < X ω} < 0.4347 := by
  have h : P.real {ω | 15 < X ω} = exp (-(5 / 6)) := by
    rw [expMeasure_survival_of_hasLaw hX (by norm_num) (by norm_num)]
    norm_num
  obtain ⟨a1, a2⟩ := exp_in (t := -(5 / 6)) (x := -(5 / 6)) (lo := 0.43459) (hi := 0.43461) 1
    (by norm_num) (by norm_num [abs_neg]) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg])
    (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg])
  norm_num at a1 a2
  refine ⟨h, ?_, ?_⟩ <;> rw [h] <;> linarith

/-- OpenStax Introductory Statistics 2e Try It 5.9(b). If one pair lasts 18 months on average, six
pairs used one after another last 108 months on average (linearity of the expectation for six
exponential lifetimes of rate `1/18`). -/
@[kb "openstaxintrostats2e" "Try It 5.9, p. 319"]
theorem tryit_5_9_exponential_six_pairs {Y : Fin 6 → Ω → ℝ}
    (hY : ∀ i, HasLaw (Y i) (expMeasure (1 / 18)) P) (hint : ∀ i, Integrable (Y i) P) :
    P[fun ω => ∑ i, Y i ω] = 108 := by
  rw [integral_finsetSum _ (fun i _ => hint i)]
  simp only [expectation_of_hasLaw_exp (hY _) (by norm_num : (0 : ℝ) < 1 / 18)]
  norm_num

/-- OpenStax Introductory Statistics 2e Try It 5.9(c). For a lifetime exponential with mean 18
months, 80% of lifetimes are at most the 80th percentile `-ln(0.2)/(1/18) = 18 ln 5`, which lies
strictly between `28.96` and `28.98`. -/
@[kb "openstaxintrostats2e" "Try It 5.9, p. 319"]
theorem tryit_5_9_exponential_percentile (hX : HasLaw X (expMeasure (1 / 18)) P) :
    P.real {ω | X ω ≤ 18 * Real.log 5} = 4 / 5 ∧ 28.96 < 18 * Real.log 5 ∧
      18 * Real.log 5 < 28.98 := by
  have h := expMeasure_percentile_of_hasLaw hX (m := 1 / 18) (by norm_num) (p := 4 / 5)
    (by norm_num) (by norm_num)
  have e : -Real.log (1 - 4 / 5) / (1 / 18) = 18 * Real.log 5 := by
    rw [show (1 : ℝ) - 4 / 5 = (5 : ℝ)⁻¹ by norm_num, Real.log_inv]; ring
  rw [e] at h
  have hl := Real.abs_log_sub_add_sum_range_le (x := 1 / 5) (by norm_num [abs_of_pos]) 8
  have h45 : Real.log (1 - 1 / 5) = 2 * Real.log 2 - Real.log 5 := by
    rw [show (1 : ℝ) - 1 / 5 = 2 ^ 2 / 5 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
  rw [h45] at hl
  norm_num [Finset.sum_range_succ, abs_le] at hl
  refine ⟨h, ?_, ?_⟩ <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, hl.1, hl.2]

/-- OpenStax Introductory Statistics 2e Try It 5.10. A commuting distance is exponential with decay
parameter `m = 1/20` (read from the page image), so the mean `μ` and the standard deviation `σ` are both
20 miles; the probability of more than 25 miles is `e^{-5/4}`, strictly between `0.2864` and `0.2866`. -/
@[kb "openstaxintrostats2e" "Try It 5.10, p. 319"]
theorem tryit_5_10_exponential_commute (hX : HasLaw X (expMeasure (1 / 20)) P) :
    P[X] = 20 ∧ Real.sqrt (variance X P) = 20 ∧ P.real {ω | 25 < X ω} = exp (-(5 / 4)) ∧
      0.2864 < P.real {ω | 25 < X ω} ∧ P.real {ω | 25 < X ω} < 0.2866 := by
  have h : P.real {ω | 25 < X ω} = exp (-(5 / 4)) := by
    rw [expMeasure_survival_of_hasLaw hX (by norm_num) (by norm_num)]
    norm_num
  obtain ⟨a1, a2⟩ := exp_in (t := -(5 / 4)) (x := -(5 / 8)) (lo := 0.53525) (hi := 0.53528) 2
    (by norm_num) (by norm_num [abs_neg]) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg])
    (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg])
  norm_num at a1 a2
  refine ⟨?_, ?_, h, ?_, ?_⟩
  · rw [expectation_of_hasLaw_exp hX (by norm_num)]; norm_num
  · rw [variance_of_hasLaw_exp hX (by norm_num)]
    rw [show (1 : ℝ) / (1 / 20) ^ 2 = 20 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  · rw [h]; linarith
  · rw [h]; linarith

/-- OpenStax Introductory Statistics 2e Try It 5.11(a, b). Cars pass at five per minute, so the gap
between cars is exponential with rate 5 per minute: its mean is `1/5` minute, that is `12` seconds;
seven successive gaps have total mean `7/5` minute, that is `84` seconds. -/
@[kb "openstaxintrostats2e" "Try It 5.11, p. 321"]
theorem tryit_5_11_exponential_mean_gaps {Y : Fin 7 → Ω → ℝ}
    (hY : ∀ i, HasLaw (Y i) (expMeasure 5) P) (hint : ∀ i, Integrable (Y i) P) :
    P[Y 0] * 60 = 12 ∧ P[fun ω => ∑ i, Y i ω] = 7 / 5 ∧ P[fun ω => ∑ i, Y i ω] * 60 = 84 := by
  have h1 : P[fun ω => ∑ i, Y i ω] = 7 / 5 := by
    rw [integral_finsetSum _ (fun i _ => hint i)]
    simp only [expectation_of_hasLaw_exp (hY _) (by norm_num : (0 : ℝ) < 5)]
    norm_num
  refine ⟨?_, h1, by rw [h1]; norm_num⟩
  rw [expectation_of_hasLaw_exp (hY 0) (by norm_num)]; norm_num

/-- OpenStax Introductory Statistics 2e Try It 5.11(c). With an exponential gap of rate 5 per minute,
the next car passes within 20 seconds (`1/3` minute) with probability `1 - e^{-5/3}`, strictly between
`0.8111` and `0.8112`. -/
@[kb "openstaxintrostats2e" "Try It 5.11, p. 321"]
theorem tryit_5_11_exponential_within_twenty_seconds (hX : HasLaw X (expMeasure 5) P) :
    P.real {ω | 0 < X ω ∧ X ω < 1 / 3} = 1 - exp (-(5 / 3)) ∧
      0.8111 < P.real {ω | 0 < X ω ∧ X ω < 1 / 3} ∧
      P.real {ω | 0 < X ω ∧ X ω < 1 / 3} < 0.8112 := by
  have h : P.real {ω | 0 < X ω ∧ X ω < 1 / 3} = 1 - exp (-(5 / 3)) := by
    rw [exp_between_real hX (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  obtain ⟨a1, a2⟩ := exp_in (t := -(5 / 3)) (x := -(5 / 6)) (lo := 0.43459) (hi := 0.43461) 2
    (by norm_num) (by norm_num [abs_neg]) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg])
    (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg])
  norm_num at a1 a2
  refine ⟨h, ?_, ?_⟩ <;> rw [h] <;> linarith

/-- OpenStax Introductory Statistics 2e Try It 5.11(d). With an exponential gap of rate 5 per minute,
the next car takes at least another 15 seconds (`1/4` minute) with probability `e^{-5/4}`, strictly
between `0.2864` and `0.2866`. -/
@[kb "openstaxintrostats2e" "Try It 5.11, p. 321"]
theorem tryit_5_11_exponential_at_least_fifteen_seconds (hX : HasLaw X (expMeasure 5) P) :
    P.real {ω | 1 / 4 < X ω} = exp (-(5 / 4)) ∧ 0.2864 < P.real {ω | 1 / 4 < X ω} ∧
      P.real {ω | 1 / 4 < X ω} < 0.2866 := by
  have h : P.real {ω | 1 / 4 < X ω} = exp (-(5 / 4)) := by
    rw [expMeasure_survival_of_hasLaw hX (by norm_num) (by norm_num)]
    norm_num
  obtain ⟨a1, a2⟩ := exp_in (t := -(5 / 4)) (x := -(5 / 8)) (lo := 0.53525) (hi := 0.53528) 2
    (by norm_num) (by norm_num [abs_neg]) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg])
    (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg])
  norm_num at a1 a2
  refine ⟨h, ?_, ?_⟩ <;> rw [h] <;> linarith

/-- OpenStax Introductory Statistics 2e Try It 5.12. A light bulb lifetime is exponential with mean 8
years (rate `1/8`). By memorylessness, given that the bulb has lasted 12 years, the probability that
it lasts beyond 19 years is `P(X > 7) = e^{-7/8}`, strictly between `0.4168` and `0.4170`. -/
@[kb "openstaxintrostats2e" "Try It 5.12, p. 323"]
theorem tryit_5_12_exponential_memoryless (hX : HasLaw X (expMeasure (1 / 8)) P) :
    (P[X ⁻¹' Ioi 19 | X ⁻¹' Ioi 12]).toReal = exp (-(7 / 8)) ∧
      0.4168 < (P[X ⁻¹' Ioi 19 | X ⁻¹' Ioi 12]).toReal ∧
      (P[X ⁻¹' Ioi 19 | X ⁻¹' Ioi 12]).toReal < 0.4170 := by
  have h : (P[X ⁻¹' Ioi 19 | X ⁻¹' Ioi 12]).toReal = exp (-(7 / 8)) := by
    have := expMeasure_memoryless_of_hasLaw hX (by norm_num) (x := 12) (k := 7) (by norm_num)
      (by norm_num)
    rw [show (19 : ℝ) = 12 + 7 by norm_num, this]
    have h2 : (P (X ⁻¹' Ioi 7)).toReal = exp (-(1 / 8 * 7)) :=
      expMeasure_survival_of_hasLaw hX (by norm_num) (x := 7) (by norm_num)
    rw [h2]
    norm_num
  obtain ⟨a1, a2⟩ := exp_in (t := -(7 / 8)) (x := -(7 / 8)) (lo := 0.41686) (hi := 0.41687) 1
    (by norm_num) (by norm_num [abs_neg]) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg])
    (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg])
  norm_num at a1 a2
  refine ⟨h, ?_, ?_⟩ <;> rw [h] <;> linarith

/-- OpenStax Introductory Statistics 2e Try It 5.13(a). Accidents occur as a Poisson count with mean 3
per week; the probability of at most 2 in a week is `e^{-3}(1 + 3 + 9/2) = (17/2) e^{-3}`, strictly
between `0.4231` and `0.4233`. -/
@[kb "openstaxintrostats2e" "Try It 5.13, p. 324"]
theorem tryit_5_13_poisson_at_most_two :
    (poissonMeasure 3).real (Set.Iic 2) = 17 / 2 * exp (-3) ∧
      (0.4231 < (poissonMeasure 3).real (Set.Iic 2) ∧
        (poissonMeasure 3).real (Set.Iic 2) < 0.4233) := by
  have h : (poissonMeasure 3).real (Set.Iic 2) = 17 / 2 * exp (-3) := by
    rw [real_Iic]
    simp [Finset.sum_range_succ, poissonMeasure_real_singleton, Nat.factorial]
    ring
  obtain ⟨a1, a2⟩ := exp_in (t := -3) (x := -1) (lo := 0.36787) (hi := 0.36789) 3
    (by norm_num) (by norm_num [abs_neg]) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg])
    (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg])
  norm_num at a1 a2
  refine ⟨h, ?_, ?_⟩ <;> rw [h] <;> linarith

/-- OpenStax Introductory Statistics 2e Try It 5.13(b). With three accidents per week, the gap `T`
between accidents is exponential with rate 3 per week; the probability of a gap of more than two weeks
is `e^{-6}`, strictly between `0.00247` and `0.00249`. -/
@[kb "openstaxintrostats2e" "Try It 5.13, p. 324"]
theorem tryit_5_13_exponential_two_weeks (hX : HasLaw X (expMeasure 3) P) :
    P.real {ω | 2 < X ω} = exp (-6) ∧ 0.00247 < P.real {ω | 2 < X ω} ∧
      P.real {ω | 2 < X ω} < 0.00249 := by
  have h : P.real {ω | 2 < X ω} = exp (-6) := by
    rw [expMeasure_survival_of_hasLaw hX (by norm_num) (by norm_num)]
    norm_num
  obtain ⟨a1, a2⟩ := exp_in (t := -6) (x := -1) (lo := 0.36787) (hi := 0.36789) 6
    (by norm_num) (by norm_num [abs_neg]) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg])
    (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg])
  norm_num at a1 a2
  refine ⟨h, ?_, ?_⟩ <;> rw [h] <;> linarith

end Exponential

end UndergradKB.Statistics.Course.TryItC5
