import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Continuous
import UndergradKB.Statistics.Waiting

/-!
# Course layer, chapter 5 (OpenStax *Introductory Statistics 2e*): worked examples

Uniform and exponential worked examples, proved exactly or with two-sided numerical bounds.
A uniform variable on `[a, b]` is `pdf.IsUniform X (Icc a b) P`; an exponential variable with decay
rate `m` is `HasLaw X (expMeasure m) P` (mean `1/m`).
-/

namespace UndergradKB.Statistics.Course.ExamplesC5

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

section Helpers

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}

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

private lemma exp_between_real {m : ℝ} (hX : HasLaw X (expMeasure m) P) (hm : 0 < m) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    P.real {ω | a < X ω ∧ X ω < b} = exp (-(m * a)) - exp (-(m * b)) := by
  rw [hX.measureReal_eq (p := fun y => a < y ∧ y < b) measurableSet_Ioo]
  exact expMeasure_Ioo_real hm ha hab

end Helpers

section Uniform

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}

/-- OpenStax Introductory Statistics 2e Example 5.2. A baby's smiling time is modelled as uniform
on `[0, 23]` seconds; the theoretical mean is `11.5` seconds. -/
@[kb "openstaxintrostats2e" "Example 5.2, p. 307"]
theorem example_5_2_uniform_mean (hX : pdf.IsUniform X (Icc 0 23) P) : P[X] = 11.5 := by
  rw [uniform_mean hX (by norm_num)]; norm_num

/-- OpenStax Introductory Statistics 2e Example 5.2. For the uniform smiling time on `[0, 23]` the
variance is `23²/12` and the standard deviation is about `6.64`, in fact strictly between `6.63`
and `6.65`. -/
@[kb "openstaxintrostats2e" "Example 5.2, p. 307"]
theorem example_5_2_uniform_standard_deviation (hX : pdf.IsUniform X (Icc 0 23) P) :
    variance X P = 23 ^ 2 / 12 ∧ 6.63 < Real.sqrt (variance X P) ∧
      Real.sqrt (variance X P) < 6.65 := by
  have hv : variance X P = 23 ^ 2 / 12 := by
    rw [uniform_variance hX (by norm_num)]; norm_num
  refine ⟨hv, ?_, ?_⟩ <;> rw [hv]
  · exact (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  · exact (Real.sqrt_lt' (by norm_num)).2 (by norm_num)

/-- OpenStax Introductory Statistics 2e Example 5.3(a). For a smiling time uniform on `[0, 23]`,
the probability of a smile lasting between 2 and 18 seconds is `16/23`. -/
@[kb "openstaxintrostats2e" "Example 5.3, p. 308"]
theorem example_5_3_uniform_probability (hX : pdf.IsUniform X (Icc 0 23) P) :
    P.real {ω | 2 < X ω ∧ X ω < 18} = 16 / 23 := by
  rw [unif_real hX (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; norm_num

/-- OpenStax Introductory Statistics 2e Example 5.3(b). For a smiling time uniform on `[0, 23]`,
the value `k = 20.7` seconds satisfies `P(0 < X < k) = 0.9`, so it is the 90th percentile. -/
@[kb "openstaxintrostats2e" "Example 5.3, p. 308"]
theorem example_5_3_uniform_percentile (hX : pdf.IsUniform X (Icc 0 23) P) :
    P.real {ω | 0 < X ω ∧ X ω < 20.7} = 9 / 10 := by
  rw [unif_real hX (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; norm_num

/-- OpenStax Introductory Statistics 2e Example 5.3(c). For a smiling time uniform on `[0, 23]`,
given that the smile lasts more than 8 seconds, the chance it lasts more than 12 seconds is
`11/15`. -/
@[kb "openstaxintrostats2e" "Example 5.3, p. 308"]
theorem example_5_3_uniform_conditional (hX : pdf.IsUniform X (Icc 0 23) P) :
    (P[X ⁻¹' Ioi 12 | X ⁻¹' Ioi 8]).toReal = 11 / 15 := by
  rw [unif_cond_real hX (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- OpenStax Introductory Statistics 2e Example 5.4(a). A bus waiting time is uniform on
`[0, 15]` minutes; the probability of waiting less than 12.5 minutes is `5/6 ≈ 0.8333`. -/
@[kb "openstaxintrostats2e" "Example 5.4, p. 310"]
theorem example_5_4_uniform_probability (hX : pdf.IsUniform X (Icc 0 15) P) :
    P.real {ω | 0 < X ω ∧ X ω < 12.5} = 5 / 6 := by
  rw [unif_real hX (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; norm_num

/-- OpenStax Introductory Statistics 2e Example 5.4(b). A bus waiting time is uniform on
`[0, 15]` minutes; its mean is `7.5` and its standard deviation (`√18.75`) lies strictly between
`4.33` and `4.34`. -/
@[kb "openstaxintrostats2e" "Example 5.4, p. 310"]
theorem example_5_4_uniform_mean_sd (hX : pdf.IsUniform X (Icc 0 15) P) :
    P[X] = 7.5 ∧ variance X P = 18.75 ∧ 4.33 < Real.sqrt (variance X P) ∧
      Real.sqrt (variance X P) < 4.34 := by
  have hv : variance X P = 18.75 := by
    rw [uniform_variance hX (by norm_num)]; norm_num
  refine ⟨?_, hv, ?_, ?_⟩
  · rw [uniform_mean hX (by norm_num)]; norm_num
  · rw [hv]; exact (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  · rw [hv]; exact (Real.sqrt_lt' (by norm_num)).2 (by norm_num)

/-- OpenStax Introductory Statistics 2e Example 5.4(c). For a waiting time uniform on `[0, 15]`
minutes, the 90th percentile is `13.5` minutes: `P(0 < X < 13.5) = 0.9`. -/
@[kb "openstaxintrostats2e" "Example 5.4, p. 310"]
theorem example_5_4_uniform_percentile (hX : pdf.IsUniform X (Icc 0 15) P) :
    P.real {ω | 0 < X ω ∧ X ω < 13.5} = 9 / 10 := by
  rw [unif_real hX (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; norm_num

/-- OpenStax Introductory Statistics 2e Example 5.5(a). A donut-eating time is uniform on
`[0.5, 4]` minutes; the probability of taking between 2 and 4 minutes is `4/7 ≈ 0.5714`. -/
@[kb "openstaxintrostats2e" "Example 5.5, p. 311"]
theorem example_5_5_uniform_probability (hX : pdf.IsUniform X (Icc 0.5 4) P) :
    P.real {ω | 2 < X ω ∧ X ω < 4} = 4 / 7 := by
  rw [unif_real hX (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; norm_num

/-- OpenStax Introductory Statistics 2e Example 5.5(b). A donut-eating time is uniform on
`[0.5, 4]` minutes; given that the child has already taken more than 1.5 minutes, the chance of
taking more than 2 minutes is `4/5`. -/
@[kb "openstaxintrostats2e" "Example 5.5, p. 311"]
theorem example_5_5_uniform_conditional (hX : pdf.IsUniform X (Icc 0.5 4) P) :
    (P[X ⁻¹' Ioi 2 | X ⁻¹' Ioi 1.5]).toReal = 4 / 5 := by
  rw [unif_cond_real hX (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- OpenStax Introductory Statistics 2e Example 5.6(a, b). A furnace repair time is uniform on
`[1.5, 4]` hours; the probability of more than 2 hours (that is, between 2 and 4) is `4/5`, and
that of less than 3 hours (between 1.5 and 3) is `3/5`. -/
@[kb "openstaxintrostats2e" "Example 5.6, p. 312"]
theorem example_5_6_uniform_probabilities (hX : pdf.IsUniform X (Icc 1.5 4) P) :
    P.real {ω | 2 < X ω ∧ X ω < 4} = 4 / 5 ∧ P.real {ω | 1.5 < X ω ∧ X ω < 3} = 3 / 5 := by
  constructor <;>
  · rw [unif_real hX (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; norm_num

/-- OpenStax Introductory Statistics 2e Example 5.6(c, d). For a repair time uniform on
`[1.5, 4]` hours, the 30th percentile is `2.25` (`P(1.5 < X < 2.25) = 0.3`) and the cut-off for
the longest 25% of repair times is `3.375` (`P(3.375 < X < 4) = 0.25`). -/
@[kb "openstaxintrostats2e" "Example 5.6, p. 312"]
theorem example_5_6_uniform_percentiles (hX : pdf.IsUniform X (Icc 1.5 4) P) :
    P.real {ω | 1.5 < X ω ∧ X ω < 2.25} = 3 / 10 ∧
      P.real {ω | 3.375 < X ω ∧ X ω < 4} = 1 / 4 := by
  constructor <;>
  · rw [unif_real hX (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; norm_num

/-- OpenStax Introductory Statistics 2e Example 5.6(e). A repair time uniform on `[1.5, 4]`
hours has mean `2.75` and standard deviation `2.5/√12`, which lies strictly between `0.72` and
`0.73`. -/
@[kb "openstaxintrostats2e" "Example 5.6, p. 312"]
theorem example_5_6_uniform_mean_sd (hX : pdf.IsUniform X (Icc 1.5 4) P) :
    P[X] = 2.75 ∧ variance X P = 2.5 ^ 2 / 12 ∧ 0.72 < Real.sqrt (variance X P) ∧
      Real.sqrt (variance X P) < 0.73 := by
  have hv : variance X P = 2.5 ^ 2 / 12 := by
    rw [uniform_variance hX (by norm_num)]; norm_num
  refine ⟨?_, hv, ?_, ?_⟩
  · rw [uniform_mean hX (by norm_num)]; norm_num
  · rw [hv]; exact (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  · rw [hv]; exact (Real.sqrt_lt' (by norm_num)).2 (by norm_num)

end Uniform

section Exponential

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}

/-- OpenStax Introductory Statistics 2e Example 5.7. A postal clerk's service time has mean 4
minutes and is exponential, so the decay rate is `m = 1/4`; both the mean and the standard
deviation equal 4. -/
@[kb "openstaxintrostats2e" "Example 5.7, p. 315"]
theorem example_5_7_exponential_mean_sd (hX : HasLaw X (expMeasure (1 / 4)) P) :
    P[X] = 4 ∧ Real.sqrt (variance X P) = 4 := by
  refine ⟨?_, ?_⟩
  · rw [expectation_of_hasLaw_exp hX (by norm_num)]; norm_num
  · rw [variance_of_hasLaw_exp hX (by norm_num)]
    rw [show (1 : ℝ) / (1 / 4) ^ 2 = 4 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)

/-- OpenStax Introductory Statistics 2e Example 5.8(a). A service time exponential with rate
`0.25` falls between 4 and 5 minutes with probability `e^{-1} - e^{-1.25}`, which lies strictly
between `0.0813` and `0.0815` (the book's `0.0814`). -/
@[kb "openstaxintrostats2e" "Example 5.8, p. 315"]
theorem example_5_8_exponential_between (hX : HasLaw X (expMeasure (1 / 4)) P) :
    P.real {ω | 4 < X ω ∧ X ω < 5} = exp (-1) - exp (-(5 / 4)) ∧
      0.0813 < P.real {ω | 4 < X ω ∧ X ω < 5} ∧ P.real {ω | 4 < X ω ∧ X ω < 5} < 0.0815 := by
  have h : P.real {ω | 4 < X ω ∧ X ω < 5} = exp (-1) - exp (-(5 / 4)) := by
    rw [exp_between_real hX (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  obtain ⟨a1, a2⟩ := exp_in (t := -1) (x := -1) (lo := 0.36786) (hi := 0.36789) 1 (by norm_num)
    (by norm_num [abs_neg]) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg])
    (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg])
  obtain ⟨b1, b2⟩ := exp_in (t := -(5 / 4)) (x := -0.625) (lo := 0.53525) (hi := 0.53528) 2
    (by norm_num) (by norm_num [abs_neg]) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg])
    (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg])
  norm_num at a1 a2 b1 b2
  refine ⟨h, ?_, ?_⟩ <;> rw [h] <;> linarith

/-- OpenStax Introductory Statistics 2e Example 5.8(b). For a service time exponential with rate
`0.25`, the median (50th percentile) is `-ln(1 - 0.5)/0.25 = 4 ln 2`, which lies strictly between
`2.77` and `2.78` (the book's `2.8`); half of all service times are at most this long. -/
@[kb "openstaxintrostats2e" "Example 5.8, p. 315"]
theorem example_5_8_exponential_median (hX : HasLaw X (expMeasure (1 / 4)) P) :
    P.real {ω | X ω ≤ 4 * Real.log 2} = 1 / 2 ∧ 2.77 < 4 * Real.log 2 ∧
      4 * Real.log 2 < 2.78 := by
  have h := expMeasure_percentile_of_hasLaw hX (m := 1 / 4) (by norm_num) (p := 1 / 2)
    (by norm_num) (by norm_num)
  have e : -Real.log (1 - 1 / 2) / (1 / 4) = 4 * Real.log 2 := by
    rw [show (1 : ℝ) - 1 / 2 = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]; ring
  rw [e] at h
  refine ⟨h, ?_, ?_⟩ <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- OpenStax Introductory Statistics 2e Example 5.9(a). A computer part's lifetime is exponential
with mean 10 years (rate `0.1`); it lasts more than 7 years with probability `e^{-0.7}`, strictly
between `0.4965` and `0.4967` (the book's `0.4966`). -/
@[kb "openstaxintrostats2e" "Example 5.9, p. 317"]
theorem example_5_9_exponential_survival (hX : HasLaw X (expMeasure (1 / 10)) P) :
    P.real {ω | 7 < X ω} = exp (-(7 / 10)) ∧ 0.4965 < P.real {ω | 7 < X ω} ∧
      P.real {ω | 7 < X ω} < 0.4967 := by
  have h : P.real {ω | 7 < X ω} = exp (-(7 / 10)) := by
    rw [expMeasure_survival_of_hasLaw hX (by norm_num) (by norm_num)]
    norm_num
  obtain ⟨a1, a2⟩ := exp_in (t := -(7 / 10)) (x := -0.7) (lo := 0.49657) (hi := 0.4966) 1
    (by norm_num) (by norm_num [abs_neg]) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg])
    (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg])
  norm_num at a1 a2
  refine ⟨h, ?_, ?_⟩ <;> rw [h] <;> linarith

/-- OpenStax Introductory Statistics 2e Example 5.9(b). If the lifetime of one part has mean 10
years, then five parts used one after another last 50 years on average (linearity of the
expectation for five exponential lifetimes of rate `0.1`). -/
@[kb "openstaxintrostats2e" "Example 5.9, p. 317"]
theorem example_5_9_exponential_five_parts {Y : Fin 5 → Ω → ℝ}
    (hY : ∀ i, HasLaw (Y i) (expMeasure (1 / 10)) P) (hint : ∀ i, Integrable (Y i) P) :
    P[fun ω => ∑ i, Y i ω] = 50 := by
  rw [integral_finsetSum _ (fun i _ => hint i)]
  simp only [expectation_of_hasLaw_exp (hY _) (by norm_num : (0 : ℝ) < 1 / 10)]
  norm_num

/-- OpenStax Introductory Statistics 2e Example 5.9(c). For a lifetime exponential with mean 10
years, the 80th percentile is `-ln(0.2)/0.1 = 10 ln 5`; this is strictly between `16.09` and
`16.10` (the book's `16.1`). -/
@[kb "openstaxintrostats2e" "Example 5.9, p. 317"]
theorem example_5_9_exponential_percentile (hX : HasLaw X (expMeasure (1 / 10)) P) :
    P.real {ω | X ω ≤ 10 * Real.log 5} = 4 / 5 ∧ 16.09 < 10 * Real.log 5 ∧
      10 * Real.log 5 < 16.10 := by
  have h := expMeasure_percentile_of_hasLaw hX (m := 1 / 10) (by norm_num) (p := 4 / 5)
    (by norm_num) (by norm_num)
  have e : -Real.log (1 - 4 / 5) / (1 / 10) = 10 * Real.log 5 := by
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

/-- OpenStax Introductory Statistics 2e Example 5.9(d). A lifetime exponential with rate `0.1`
lies between 9 and 11 years with probability `e^{-0.9} - e^{-1.1}`, strictly between `0.0736` and
`0.0738` (the book's `0.0737`). -/
@[kb "openstaxintrostats2e" "Example 5.9, p. 317"]
theorem example_5_9_exponential_between (hX : HasLaw X (expMeasure (1 / 10)) P) :
    P.real {ω | 9 < X ω ∧ X ω < 11} = exp (-(9 / 10)) - exp (-(11 / 10)) ∧
      0.0736 < P.real {ω | 9 < X ω ∧ X ω < 11} ∧ P.real {ω | 9 < X ω ∧ X ω < 11} < 0.0738 := by
  have h : P.real {ω | 9 < X ω ∧ X ω < 11} = exp (-(9 / 10)) - exp (-(11 / 10)) := by
    rw [exp_between_real hX (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  obtain ⟨a1, a2⟩ := exp_in (t := -(9 / 10)) (x := -0.9) (lo := 0.40655) (hi := 0.40658) 1
    (by norm_num) (by norm_num [abs_neg]) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg])
    (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg])
  obtain ⟨b1, b2⟩ := exp_in (t := -(11 / 10)) (x := -0.55) (lo := 0.57693) (hi := 0.57696) 2
    (by norm_num) (by norm_num [abs_neg]) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg])
    (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg])
  norm_num at a1 a2 b1 b2
  refine ⟨h, ?_, ?_⟩ <;> rw [h] <;> linarith

/-- OpenStax Introductory Statistics 2e Example 5.10. A phone call's length is exponential with
decay rate `m = 1/12`, so the mean and standard deviation are both 12 minutes, and the probability
of waiting more than five minutes is `e^{-5/12}`, strictly between `0.6592` and `0.6593`. -/
@[kb "openstaxintrostats2e" "Example 5.10, p. 319"]
theorem example_5_10_exponential_phone_call (hX : HasLaw X (expMeasure (1 / 12)) P) :
    P[X] = 12 ∧ Real.sqrt (variance X P) = 12 ∧ P.real {ω | 5 < X ω} = exp (-(5 / 12)) ∧
      0.6592 < P.real {ω | 5 < X ω} ∧ P.real {ω | 5 < X ω} < 0.6593 := by
  have h : P.real {ω | 5 < X ω} = exp (-(5 / 12)) := by
    rw [expMeasure_survival_of_hasLaw hX (by norm_num) (by norm_num)]
    norm_num
  obtain ⟨a1, a2⟩ := exp_in (t := -(5 / 12)) (x := -(5 / 12)) (lo := 0.65923) (hi := 0.65926) 1
    (by norm_num) (by norm_num [abs_neg]) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg])
    (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg])
  norm_num at a1 a2
  refine ⟨?_, ?_, h, ?_, ?_⟩
  · rw [expectation_of_hasLaw_exp hX (by norm_num)]; norm_num
  · rw [variance_of_hasLaw_exp hX (by norm_num)]
    rw [show (1 : ℝ) / (1 / 12) ^ 2 = 12 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  · rw [h]; linarith
  · rw [h]; linarith

/-- OpenStax Introductory Statistics 2e Example 5.11(c). Customers arrive on average every two
minutes, so the gap is exponential with rate `0.5`; the next customer arrives within one minute
with probability `1 - e^{-0.5}`, strictly between `0.3934` and `0.3936`. -/
@[kb "openstaxintrostats2e" "Example 5.11, p. 320"]
theorem example_5_11_exponential_within_one_minute (hX : HasLaw X (expMeasure (1 / 2)) P) :
    P.real {ω | 0 < X ω ∧ X ω < 1} = 1 - exp (-(1 / 2)) ∧
      0.3934 < P.real {ω | 0 < X ω ∧ X ω < 1} ∧ P.real {ω | 0 < X ω ∧ X ω < 1} < 0.3936 := by
  have h : P.real {ω | 0 < X ω ∧ X ω < 1} = 1 - exp (-(1 / 2)) := by
    rw [exp_between_real hX (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  obtain ⟨a1, a2⟩ := exp_in (t := -(1 / 2)) (x := -0.5) (lo := 0.60652) (hi := 0.60655) 1
    (by norm_num) (by norm_num [abs_neg]) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg])
    (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg])
  norm_num at a1 a2
  refine ⟨h, ?_, ?_⟩ <;> rw [h] <;> linarith

/-- OpenStax Introductory Statistics 2e Example 5.11(d). With an exponential gap of rate `0.5`
minutes, the next customer takes more than five minutes with probability `e^{-2.5}`, strictly
between `0.0820` and `0.0822` (the book's `0.0821`). -/
@[kb "openstaxintrostats2e" "Example 5.11, p. 320"]
theorem example_5_11_exponential_more_than_five (hX : HasLaw X (expMeasure (1 / 2)) P) :
    P.real {ω | 5 < X ω} = exp (-(5 / 2)) ∧ 0.0820 < P.real {ω | 5 < X ω} ∧
      P.real {ω | 5 < X ω} < 0.0822 := by
  have h : P.real {ω | 5 < X ω} = exp (-(5 / 2)) := by
    rw [expMeasure_survival_of_hasLaw hX (by norm_num) (by norm_num)]
    norm_num
  obtain ⟨a1, a2⟩ := exp_in (t := -(5 / 2)) (x := -(5 / 6)) (lo := 0.43458) (hi := 0.43461) 3
    (by norm_num) (by norm_num [abs_neg]) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg])
    (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg])
  norm_num at a1 a2
  refine ⟨h, ?_, ?_⟩ <;> rw [h] <;> linarith

/-- OpenStax Introductory Statistics 2e Example 5.12. A service time exponential with rate `0.25`
is memoryless: given that a customer has already used 4 minutes, the probability of at least 3
more minutes is `P(X > 3) = e^{-0.75}`, strictly between `0.4723` and `0.4725`. -/
@[kb "openstaxintrostats2e" "Example 5.12, p. 322"]
theorem example_5_12_exponential_memoryless (hX : HasLaw X (expMeasure (1 / 4)) P) :
    (P[X ⁻¹' Ioi 7 | X ⁻¹' Ioi 4]).toReal = exp (-(3 / 4)) ∧
      0.4723 < (P[X ⁻¹' Ioi 7 | X ⁻¹' Ioi 4]).toReal ∧
      (P[X ⁻¹' Ioi 7 | X ⁻¹' Ioi 4]).toReal < 0.4725 := by
  have h : (P[X ⁻¹' Ioi 7 | X ⁻¹' Ioi 4]).toReal = exp (-(3 / 4)) := by
    have := expMeasure_memoryless_of_hasLaw hX (by norm_num) (x := 4) (k := 3) (by norm_num)
      (by norm_num)
    rw [show (7 : ℝ) = 4 + 3 by norm_num, this]
    have h2 : (P (X ⁻¹' Ioi 3)).toReal = exp (-(1 / 4 * 3)) :=
      expMeasure_survival_of_hasLaw hX (by norm_num) (x := 3) (by norm_num)
    rw [h2]
    norm_num
  obtain ⟨a1, a2⟩ := exp_in (t := -(3 / 4)) (x := -0.75) (lo := 0.47235) (hi := 0.47238) 1
    (by norm_num) (by norm_num [abs_neg]) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg])
    (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg])
  norm_num at a1 a2
  refine ⟨h, ?_, ?_⟩ <;> rw [h] <;> linarith

/-- OpenStax Introductory Statistics 2e Example 5.11 (memoryless discussion). For a gap exponential
with rate `0.5`, after 5 minutes have elapsed the probability of waiting more than one further
minute is `P(X > 1) = e^{-0.5}`, strictly between `0.6065` and `0.6066`. -/
@[kb "openstaxintrostats2e" "Example 5.11, p. 320"]
theorem example_5_11_exponential_memoryless (hX : HasLaw X (expMeasure (1 / 2)) P) :
    (P[X ⁻¹' Ioi 6 | X ⁻¹' Ioi 5]).toReal = exp (-(1 / 2)) ∧
      0.6065 < (P[X ⁻¹' Ioi 6 | X ⁻¹' Ioi 5]).toReal ∧
      (P[X ⁻¹' Ioi 6 | X ⁻¹' Ioi 5]).toReal < 0.6066 := by
  have h : (P[X ⁻¹' Ioi 6 | X ⁻¹' Ioi 5]).toReal = exp (-(1 / 2)) := by
    have := expMeasure_memoryless_of_hasLaw hX (by norm_num) (x := 5) (k := 1) (by norm_num)
      (by norm_num)
    rw [show (6 : ℝ) = 5 + 1 by norm_num, this]
    have h2 : (P (X ⁻¹' Ioi 1)).toReal = exp (-(1 / 2 * 1)) :=
      expMeasure_survival_of_hasLaw hX (by norm_num) (x := 1) (by norm_num)
    rw [h2]
    norm_num
  obtain ⟨a1, a2⟩ := exp_in (t := -(1 / 2)) (x := -0.5) (lo := 0.60652) (hi := 0.60655) 1
    (by norm_num) (by norm_num [abs_neg]) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg])
    (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg])
  norm_num at a1 a2
  refine ⟨h, ?_, ?_⟩ <;> rw [h] <;> linarith

/-- OpenStax Introductory Statistics 2e Example 5.13(b). Calls arrive at four per minute, so the
gap `T` between calls is exponential with rate 4 and mean `1/4` minute; the next call comes within
ten seconds (`1/6` minute) with probability `1 - e^{-2/3}`, strictly between `0.4865` and
`0.4867`. -/
@[kb "openstaxintrostats2e" "Example 5.13, p. 323"]
theorem example_5_13_exponential_ten_seconds (hX : HasLaw X (expMeasure 4) P) :
    P[X] = 1 / 4 ∧ P.real {ω | 0 < X ω ∧ X ω < 1 / 6} = 1 - exp (-(2 / 3)) ∧
      0.4865 < P.real {ω | 0 < X ω ∧ X ω < 1 / 6} ∧
      P.real {ω | 0 < X ω ∧ X ω < 1 / 6} < 0.4867 := by
  have h : P.real {ω | 0 < X ω ∧ X ω < 1 / 6} = 1 - exp (-(2 / 3)) := by
    rw [exp_between_real hX (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  obtain ⟨a1, a2⟩ := exp_in (t := -(2 / 3)) (x := -(2 / 3)) (lo := 0.5134) (hi := 0.51343) 1
    (by norm_num) (by norm_num [abs_neg]) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg])
    (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg])
  norm_num at a1 a2
  refine ⟨?_, h, ?_, ?_⟩
  · rw [expectation_of_hasLaw_exp hX (by norm_num)]
  · rw [h]; linarith
  · rw [h]; linarith

end Exponential

end UndergradKB.Statistics.Course.ExamplesC5
