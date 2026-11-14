import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Continuous
import UndergradKB.Statistics.Waiting

/-!
# Course layer, chapter 5 (OpenStax *Introductory Statistics 2e*): Practice exercises

Practice exercises 5.1-5.71 on continuous, uniform and exponential distributions.  A uniform variable
on `[a, b]` is `pdf.IsUniform X (Icc a b) P`; an exponential variable with decay rate `m` is
`HasLaw X (expMeasure m) P` (mean `1/m`).  Probabilities are exact where possible, and rounded values
are given as two-sided bounds.  Exercises that only ask for a figure, a graph, or a verbal answer have
no theorem.
-/

namespace UndergradKB.Statistics.Course.PracticeC5

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

/-- `expb [t, x, lo, hi, k] as a b` gives `lo ^ k ≤ exp t` and `exp t ≤ hi ^ k` (with `x * k = t`). -/
local syntax "expb " "[" term ", " term ", " term ", " term ", " term "]" " as " ident ident : tactic

local macro_rules
  | `(tactic| expb [$t, $x, $lo, $hi, $k] as $a $b) =>
    `(tactic| obtain ⟨$a, $b⟩ := exp_in (t := $t) (x := $x) (lo := $lo) (hi := $hi) $k
      (by norm_num) (by norm_num [abs_neg]) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg])
      (by norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg]))

/-- Percentile bounds from bounds on exponentials (private helper): if
`exp (-(m lo)) > 1 - p > exp (-(m hi))` then `-ln(1-p)/m` lies in `(lo, hi)`. -/
private lemma pct_bd {m p lo hi : ℝ} (hm : 0 < m) (hp1 : p < 1)
    (hl : 1 - p < exp (-(m * lo))) (hh : exp (-(m * hi)) < 1 - p) :
    lo < -Real.log (1 - p) / m ∧ -Real.log (1 - p) / m < hi := by
  have hy : 0 < 1 - p := by linarith
  have h1 : Real.log (1 - p) < -(m * lo) := (Real.log_lt_iff_lt_exp hy).2 hl
  have h2 : -(m * hi) < Real.log (1 - p) := (Real.lt_log_iff_exp_lt hy).2 hh
  constructor
  · rw [lt_div_iff₀ hm]; linarith
  · rw [div_lt_iff₀ hm]; linarith

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

/-- The uniform law of an initial segment (private helper). -/
private lemma unif_Iio {a b c : ℝ} (hab : a < b) (hac : a ≤ c) (hcb : c ≤ b) :
    (volume : Measure ℝ)[Iio c | Icc a b] = ENNReal.ofReal ((c - a) / (b - a)) := by
  have : Icc a b ∩ Iio c = Ico a c := by
    ext y
    simp only [mem_inter_iff, mem_Icc, mem_Iio, mem_Ico]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, by linarith⟩, h2⟩
  rw [cond_apply measurableSet_Icc, this, Real.volume_Icc, Real.volume_Ico,
    ← ENNReal.ofReal_inv_of_pos (sub_pos.2 hab), ← ENNReal.ofReal_mul (by simp [hab.le])]
  congr 1
  rw [div_eq_inv_mul]

/-- The uniform law of a final segment (private helper). -/
private lemma unif_Ioi {a b c : ℝ} (hab : a < b) (hac : a ≤ c) (hcb : c ≤ b) :
    (volume : Measure ℝ)[Ioi c | Icc a b] = ENNReal.ofReal ((b - c) / (b - a)) := by
  have : Icc a b ∩ Ioi c = Ioc c b := by
    ext y
    simp only [mem_inter_iff, mem_Icc, mem_Ioi, mem_Ioc]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩
      exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨by linarith, h2⟩, h1⟩
  rw [cond_apply measurableSet_Icc, this, Real.volume_Icc, Real.volume_Ioc,
    ← ENNReal.ofReal_inv_of_pos (sub_pos.2 hab), ← ENNReal.ofReal_mul (by simp [hab.le])]
  congr 1
  rw [div_eq_inv_mul]

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

private lemma unif_lt_real {a b : ℝ} (hX : pdf.IsUniform X (Icc a b) P) (hab : a < b) {c : ℝ}
    (hac : a ≤ c) (hcb : c ≤ b) : P.real {ω | X ω < c} = (c - a) / (b - a) := by
  rw [measureReal_def, HasLaw.measure_eq hX (p := fun y => y < c) measurableSet_Iio]
  show ((volume : Measure ℝ)[Iio c | Icc a b]).toReal = _
  rw [unif_Iio hab hac hcb, ENNReal.toReal_ofReal (div_nonneg (by linarith) (by linarith))]

private lemma unif_gt_real {a b : ℝ} (hX : pdf.IsUniform X (Icc a b) P) (hab : a < b) {c : ℝ}
    (hac : a ≤ c) (hcb : c ≤ b) : P.real {ω | c < X ω} = (b - c) / (b - a) := by
  rw [measureReal_def, HasLaw.measure_eq hX (p := fun y => c < y) measurableSet_Ioi]
  show ((volume : Measure ℝ)[Ioi c | Icc a b]).toReal = _
  rw [unif_Ioi hab hac hcb, ENNReal.toReal_ofReal (div_nonneg (by linarith) (by linarith))]

private lemma unif_pt_real {a b : ℝ} (hX : pdf.IsUniform X (Icc a b) P) (c : ℝ) :
    P.real {ω | X ω = c} = 0 := by
  rw [measureReal_def, HasLaw.measure_eq hX (p := fun y => y = c) (measurableSet_singleton c)]
  have : (volume : Measure ℝ)[({c} : Set ℝ) | Icc a b] = 0 := by
    rw [cond_apply measurableSet_Icc, measure_mono_null inter_subset_right Real.volume_singleton,
      mul_zero]
  show ((volume : Measure ℝ)[({c} : Set ℝ) | Icc a b]).toReal = 0
  rw [this]; rfl

private lemma unif_cond_real {a b : ℝ} (hX : pdf.IsUniform X (Icc a b) P) (hab : a < b) {c d : ℝ}
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) (hcb : c < b) :
    (P[X ⁻¹' Ioi d | X ⁻¹' Ioi c]).toReal = (b - d) / (b - c) := by
  rw [uniform_cond_Ioi hX hab hac hcd hdb hcb,
    ENNReal.toReal_ofReal (div_nonneg (by linarith) (by linarith))]

private lemma unif_cond_lt_real {a b : ℝ} (hX : pdf.IsUniform X (Icc a b) P) (hab : a < b) {c d : ℝ}
    (hac : a < c) (hdc : d ≤ c) (hda : a ≤ d) (hcb : c ≤ b) :
    (P[X ⁻¹' Iio d | X ⁻¹' Iio c]).toReal = (d - a) / (c - a) := by
  rw [hasLaw_cond_preimage hX measurableSet_Iio measurableSet_Iio (Iio_subset_Iio hdc),
    unif_Iio hab hac.le hcb, unif_Iio hab hda (hdc.trans hcb)]
  have h1 : 0 < (c - a) / (b - a) := div_pos (by linarith) (by linarith)
  have h2 : 0 ≤ (d - a) / (b - a) := div_nonneg (by linarith) (by linarith)
  rw [← ENNReal.ofReal_inv_of_pos h1, ← ENNReal.ofReal_mul (inv_nonneg.2 h1.le),
    ENNReal.toReal_ofReal (mul_nonneg (inv_nonneg.2 h1.le) h2)]
  have : c - a ≠ 0 := by linarith
  have : b - a ≠ 0 := by linarith
  field_simp

/-- A variable that lies in `[a, b]` almost surely takes values outside it with probability 0. -/
private lemma null_of_ae {a b : ℝ} {s : Set ℝ} (h : ∀ᵐ ω ∂P, X ω ∈ Icc a b)
    (hs : ∀ y ∈ s, y ∉ Icc a b) : P.real {ω | X ω ∈ s} = 0 := by
  rw [measureReal_def, measure_mono_null (t := {ω | X ω ∉ Icc a b}) (fun ω hω => hs _ hω)
    (ae_iff.1 h)]
  simp

end Helpers

section General

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}

/-- OpenStax Introductory Statistics 2e Practice exercise 5.6. A continuous variable that takes
values in `[0, 15]` (with probability one) exceeds 15 with probability `0`. -/
@[kb "openstaxintrostats2e" "Exercise 5.6, p. 330"]
theorem ex_5_6_beyond_range_zero (h : ∀ᵐ ω ∂P, X ω ∈ Icc (0 : ℝ) 15) :
    P.real {ω | 15 < X ω} = 0 :=
  null_of_ae (s := Ioi 15) h (fun y hy hm => by
    simp only [mem_Ioi] at hy
    linarith [hm.2])

/-- OpenStax Introductory Statistics 2e Practice exercise 5.7. The total area under a probability
density is one: for the exponential density with any decay rate `m > 0` the whole line has
probability 1 (and the uniform law on `[a, b]` is a probability measure as well). -/
@[kb "openstaxintrostats2e" "Exercise 5.7, p. 330"]
theorem ex_5_7_total_area_one {m : ℝ} (hm : 0 < m) :
    expMeasure m univ = 1 := by
  have := isProbabilityMeasure_expMeasure hm
  exact measure_univ

/-- OpenStax Introductory Statistics 2e Practice exercise 5.8. A continuous variable (a law absolutely
continuous with respect to length) takes the single value 7 with probability `0`. -/
@[kb "openstaxintrostats2e" "Exercise 5.8, p. 330"]
theorem ex_5_8_point_probability_zero {μ : Measure ℝ} (hμ : μ ≪ volume) (hX : HasLaw X μ P) :
    P.real {ω | X ω = 7} = 0 := by
  rw [measureReal_def, hX.measure_eq (p := fun y => y = 7) (measurableSet_singleton 7)]
  have : μ {7} = 0 := hμ Real.volume_singleton
  show (μ {(7 : ℝ)}).toReal = 0
  rw [this]; rfl

/-- OpenStax Introductory Statistics 2e Practice exercise 5.9. A continuous variable restricted to
`[0, 7]` takes the value 10 with probability `0`. -/
@[kb "openstaxintrostats2e" "Exercise 5.9, p. 330"]
theorem ex_5_9_outside_range_zero (h : ∀ᵐ ω ∂P, X ω ∈ Icc (0 : ℝ) 7) :
    P.real {ω | X ω = 10} = 0 :=
  null_of_ae (s := {10}) h (fun y hy hm => by
    simp only [mem_singleton_iff] at hy
    linarith [hm.2])

/-- OpenStax Introductory Statistics 2e Practice exercise 5.10. A continuous variable restricted to
`[0, 5]` (density `1/5`) is below `0` with probability `0`. -/
@[kb "openstaxintrostats2e" "Exercise 5.10, p. 330"]
theorem ex_5_10_below_range_zero (h : ∀ᵐ ω ∂P, X ω ∈ Icc (0 : ℝ) 5) :
    P.real {ω | X ω < 0} = 0 :=
  null_of_ae (s := Iio 0) h (fun y hy hm => by
    simp only [mem_Iio] at hy
    linarith [hm.1])

/-- OpenStax Introductory Statistics 2e Practice exercise 5.11. With constant density `1/12` on
`[0, 12]` (the uniform law), the probability of lying between 0 and 12 is 1. -/
@[kb "openstaxintrostats2e" "Exercise 5.11, p. 330"]
theorem ex_5_11_whole_range_one (hX : pdf.IsUniform X (Icc 0 12) P) :
    P.real {ω | 0 < X ω ∧ X ω < 12} = 1 := by
  rw [unif_real hX (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; norm_num

end General

section Uniform

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}

/-! ### Square footage of homes, `X ~ U(1.5, 4.5)` (exercises 16-25) -/

/-- OpenStax Introductory Statistics 2e Practice exercise 5.18. For `X ~ U(1.5, 4.5)` the density is
constant: the probability of an interval inside `[1.5, 4.5]` is its length times the height `1/3`. -/
@[kb "openstaxintrostats2e" "Exercise 5.18, p. 331"]
theorem ex_5_18_uniform_height (hX : pdf.IsUniform X (Icc 1.5 4.5) P) :
    ∀ c d : ℝ, 1.5 ≤ c → c ≤ d → d ≤ 4.5 → P.real {ω | c < X ω ∧ X ω < d} = 1 / 3 * (d - c) := by
  intro c d h1 h2 h3
  rw [unif_real hX (by norm_num) h1 h2 h3]; ring

/-- OpenStax Introductory Statistics 2e Practice exercise 5.19. For `X ~ U(1.5, 4.5)`, the values lie
in `[1.5, 4.5]`: there is no mass below 1.5 or above 4.5 and the whole mass is between them. -/
@[kb "openstaxintrostats2e" "Exercise 5.19, p. 331"]
theorem ex_5_19_uniform_constraints (hX : pdf.IsUniform X (Icc 1.5 4.5) P) :
    P.real {ω | X ω < 1.5} = 0 ∧ P.real {ω | 4.5 < X ω} = 0 ∧
      P.real {ω | 1.5 < X ω ∧ X ω < 4.5} = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [unif_lt_real hX (by norm_num) le_rfl (by norm_num)]; norm_num
  · rw [unif_gt_real hX (by norm_num) (by norm_num) le_rfl]; norm_num
  · rw [unif_real hX (by norm_num) le_rfl (by norm_num) le_rfl]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 5.21. For `X ~ U(1.5, 4.5)`,
`P(2 < X < 3) = 1/3`. -/
@[kb "openstaxintrostats2e" "Exercise 5.21, p. 331"]
theorem ex_5_21_uniform_between (hX : pdf.IsUniform X (Icc 1.5 4.5) P) :
    P.real {ω | 2 < X ω ∧ X ω < 3} = 1 / 3 := by
  rw [unif_real hX (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 5.22. For `X ~ U(1.5, 4.5)`,
`P(X < 3.5 | X < 4) = 4/5`. -/
@[kb "openstaxintrostats2e" "Exercise 5.22, p. 331"]
theorem ex_5_22_uniform_conditional_below (hX : pdf.IsUniform X (Icc 1.5 4.5) P) :
    (P[X ⁻¹' Iio 3.5 | X ⁻¹' Iio 4]).toReal = 4 / 5 := by
  rw [unif_cond_lt_real hX (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 5.23. For `X ~ U(1.5, 4.5)`,
`P(X = 1.5) = 0`. -/
@[kb "openstaxintrostats2e" "Exercise 5.23, p. 331"]
theorem ex_5_23_uniform_point_zero (hX : pdf.IsUniform X (Icc 1.5 4.5) P) :
    P.real {ω | X ω = 1.5} = 0 :=
  unif_pt_real hX 1.5

/-- OpenStax Introductory Statistics 2e Practice exercise 5.24. For `X ~ U(1.5, 4.5)` the 90th
percentile is `k = 4.2`: `P(X < 4.2) = 9/10`. -/
@[kb "openstaxintrostats2e" "Exercise 5.24, p. 331"]
theorem ex_5_24_uniform_percentile_90 (hX : pdf.IsUniform X (Icc 1.5 4.5) P) :
    P.real {ω | X ω < 4.2} = 9 / 10 := by
  rw [unif_lt_real hX (by norm_num) (by norm_num) (by norm_num)]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 5.25. For `X ~ U(1.5, 4.5)` (square footage
in thousands), given more than 2 (2,000 sq ft), the probability of more than 3 is `3/5`. -/
@[kb "openstaxintrostats2e" "Exercise 5.25, p. 331"]
theorem ex_5_25_uniform_conditional_above (hX : pdf.IsUniform X (Icc 1.5 4.5) P) :
    (P[X ⁻¹' Ioi 3 | X ⁻¹' Ioi 2]).toReal = 3 / 5 := by
  rw [unif_cond_real hX (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-! ### `X ~ U(0, 12)` (exercises 26-33) -/

/-- OpenStax Introductory Statistics 2e Practice exercise 5.26. For `X ~ U(0, 12)`, `a = 0` is the
smallest value: there is no mass below it, and any `ε`-segment above it has positive mass `ε/12`. -/
@[kb "openstaxintrostats2e" "Exercise 5.26, p. 331"]
theorem ex_5_26_uniform_lowest_value (hX : pdf.IsUniform X (Icc 0 12) P) :
    P.real {ω | X ω < 0} = 0 ∧ P.real {ω | X ω < 1} = 1 / 12 := by
  constructor
  · rw [unif_lt_real hX (by norm_num) le_rfl (by norm_num)]; norm_num
  · rw [unif_lt_real hX (by norm_num) (by norm_num) (by norm_num)]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 5.27. For `X ~ U(0, 12)`, `b = 12` is the
largest value: there is no mass above it, while the segment `(11, 12)` has mass `1/12`. -/
@[kb "openstaxintrostats2e" "Exercise 5.27, p. 331"]
theorem ex_5_27_uniform_highest_value (hX : pdf.IsUniform X (Icc 0 12) P) :
    P.real {ω | 12 < X ω} = 0 ∧ P.real {ω | 11 < X ω} = 1 / 12 := by
  constructor
  · rw [unif_gt_real hX (by norm_num) (by norm_num) le_rfl]; norm_num
  · rw [unif_gt_real hX (by norm_num) (by norm_num) (by norm_num)]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 5.28. For `X ~ U(0, 12)` the density is the
constant `1/12` on `[0, 12]`: the probability of an interval inside it is `(d - c)/12`. -/
@[kb "openstaxintrostats2e" "Exercise 5.28, p. 331"]
theorem ex_5_28_uniform_density (hX : pdf.IsUniform X (Icc 0 12) P) :
    ∀ c d : ℝ, 0 ≤ c → c ≤ d → d ≤ 12 → P.real {ω | c < X ω ∧ X ω < d} = 1 / 12 * (d - c) := by
  intro c d h1 h2 h3
  rw [unif_real hX (by norm_num) h1 h2 h3]; ring

/-- OpenStax Introductory Statistics 2e Practice exercise 5.29. For `X ~ U(0, 12)` the theoretical
mean is `6`. -/
@[kb "openstaxintrostats2e" "Exercise 5.29, p. 331"]
theorem ex_5_29_uniform_mean (hX : pdf.IsUniform X (Icc 0 12) P) : P[X] = 6 := by
  rw [uniform_mean hX (by norm_num)]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 5.30. For `X ~ U(0, 12)` the variance is
`12²/12 = 12` and the standard deviation lies strictly between `3.464` and `3.465`. -/
@[kb "openstaxintrostats2e" "Exercise 5.30, p. 332"]
theorem ex_5_30_uniform_sd (hX : pdf.IsUniform X (Icc 0 12) P) :
    variance X P = 12 ∧ 3.464 < Real.sqrt (variance X P) ∧ Real.sqrt (variance X P) < 3.465 := by
  have hv : variance X P = 12 := by
    rw [uniform_variance hX (by norm_num)]; norm_num
  refine ⟨hv, ?_, ?_⟩
  · rw [hv]; exact (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  · rw [hv]; exact (Real.sqrt_lt' (by norm_num)).2 (by norm_num)

/-- OpenStax Introductory Statistics 2e Practice exercise 5.32. For `X ~ U(0, 12)`,
`P(X > 9) = 1/4`. -/
@[kb "openstaxintrostats2e" "Exercise 5.32, p. 332"]
theorem ex_5_32_uniform_above_nine (hX : pdf.IsUniform X (Icc 0 12) P) :
    P.real {ω | 9 < X ω} = 1 / 4 := by
  rw [unif_gt_real hX (by norm_num) (by norm_num) (by norm_num)]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 5.33. For `X ~ U(0, 12)` the 40th
percentile is `4.8`: `P(X < 4.8) = 2/5`. -/
@[kb "openstaxintrostats2e" "Exercise 5.33, p. 332"]
theorem ex_5_33_uniform_percentile_40 (hX : pdf.IsUniform X (Icc 0 12) P) :
    P.real {ω | X ω < 4.8} = 2 / 5 := by
  rw [unif_lt_real hX (by norm_num) (by norm_num) (by norm_num)]; norm_num

/-! ### Age of cars, `X ~ U(0.5, 9.5)` (exercises 34-45) -/

/-- OpenStax Introductory Statistics 2e Practice exercise 5.37. The car age `X ~ U(0.5, 9.5)` takes
values in `[0.5, 9.5]`: no mass below 0.5 or above 9.5, all of the mass in between. -/
@[kb "openstaxintrostats2e" "Exercise 5.37, p. 332"]
theorem ex_5_37_car_age_interval (hX : pdf.IsUniform X (Icc 0.5 9.5) P) :
    P.real {ω | X ω < 0.5} = 0 ∧ P.real {ω | 9.5 < X ω} = 0 ∧
      P.real {ω | 0.5 < X ω ∧ X ω < 9.5} = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [unif_lt_real hX (by norm_num) le_rfl (by norm_num)]; norm_num
  · rw [unif_gt_real hX (by norm_num) (by norm_num) le_rfl]; norm_num
  · rw [unif_real hX (by norm_num) le_rfl (by norm_num) le_rfl]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 5.39. The car age `X ~ U(0.5, 9.5)` has the
constant density `1/(9.5 - 0.5) = 1/9` on `[0.5, 9.5]`. -/
@[kb "openstaxintrostats2e" "Exercise 5.39, p. 332"]
theorem ex_5_39_car_age_density (hX : pdf.IsUniform X (Icc 0.5 9.5) P) :
    1 / (9.5 - 0.5 : ℝ) = 1 / 9 ∧
      ∀ c d : ℝ, 0.5 ≤ c → c ≤ d → d ≤ 9.5 → P.real {ω | c < X ω ∧ X ω < d} = 1 / 9 * (d - c) := by
  refine ⟨by norm_num, ?_⟩
  intro c d h1 h2 h3
  rw [unif_real hX (by norm_num) h1 h2 h3]; ring

/-- OpenStax Introductory Statistics 2e Practice exercise 5.40. The rectangle of the density of
`X ~ U(0.5, 9.5)` runs from `0.5` to `9.5` with height `1/9`; its area is `9 · (1/9) = 1`. -/
@[kb "openstaxintrostats2e" "Exercise 5.40, p. 332"]
theorem ex_5_40_car_age_rectangle :
    (9.5 - 0.5 : ℝ) * (1 / 9) = 1 ∧ (0.5 : ℝ) < 9.5 := by
  constructor <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 5.41. The average age of the cars,
`X ~ U(0.5, 9.5)`, is `5` years. -/
@[kb "openstaxintrostats2e" "Exercise 5.41, p. 332"]
theorem ex_5_41_car_age_mean (hX : pdf.IsUniform X (Icc 0.5 9.5) P) : P[X] = 5 := by
  rw [uniform_mean hX (by norm_num)]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 5.42. For `X ~ U(0.5, 9.5)` the probability
that a car is less than four years old is `P(X < 4) = 7/18`. -/
@[kb "openstaxintrostats2e" "Exercise 5.42, p. 332"]
theorem ex_5_42_car_age_below_four (hX : pdf.IsUniform X (Icc 0.5 9.5) P) :
    P.real {ω | X ω < 4} = 7 / 18 := by
  rw [unif_lt_real hX (by norm_num) (by norm_num) (by norm_num)]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 5.43. For `X ~ U(0.5, 9.5)`, among cars less
than 7.5 years old the probability of being less than four is `P(X < 4 | X < 7.5) = 1/2`. -/
@[kb "openstaxintrostats2e" "Exercise 5.43, p. 333"]
theorem ex_5_43_car_age_conditional (hX : pdf.IsUniform X (Icc 0.5 9.5) P) :
    (P[X ⁻¹' Iio 4 | X ⁻¹' Iio 7.5]).toReal = 1 / 2 := by
  rw [unif_cond_lt_real hX (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 5.45. For `X ~ U(0.5, 9.5)` the third
quartile is `k = 7.25`: `P(X < 7.25) = 3/4`. -/
@[kb "openstaxintrostats2e" "Exercise 5.45, p. 333"]
theorem ex_5_45_car_age_third_quartile (hX : pdf.IsUniform X (Icc 0.5 9.5) P) :
    P.real {ω | X ω < 7.25} = 3 / 4 := by
  rw [unif_lt_real hX (by norm_num) (by norm_num) (by norm_num)]; norm_num

end Uniform

section Exponential

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}

/-! ### Customer service time, `X ~ Exp(0.2)` (exercises 46-55) -/

/-- OpenStax Introductory Statistics 2e Practice exercise 5.48. For `X ~ Exp(0.2)` the decay rate
`m = 0.2` is the value of the density at `0` (and the reciprocal of the mean, which is `5`). -/
@[kb "openstaxintrostats2e" "Exercise 5.48, p. 334"]
theorem ex_5_48_decay_rate (hX : HasLaw X (expMeasure (1 / 5)) P) :
    exponentialPDF (1 / 5) 0 = ENNReal.ofReal (1 / 5) ∧ P[X] = 1 / (1 / 5 : ℝ) := by
  constructor
  · rw [exponentialPDF_eq, if_pos le_rfl]; simp
  · rw [expectation_of_hasLaw_exp hX (by norm_num)]

/-- OpenStax Introductory Statistics 2e Practice exercise 5.49. The mean of `X ~ Exp(0.2)` is `5`. -/
@[kb "openstaxintrostats2e" "Exercise 5.49, p. 334"]
theorem ex_5_49_exponential_mean (hX : HasLaw X (expMeasure (1 / 5)) P) : P[X] = 5 := by
  rw [expectation_of_hasLaw_exp hX (by norm_num)]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 5.50. The standard deviation of
`X ~ Exp(0.2)` is `5`. -/
@[kb "openstaxintrostats2e" "Exercise 5.50, p. 334"]
theorem ex_5_50_exponential_sd (hX : HasLaw X (expMeasure (1 / 5)) P) :
    Real.sqrt (variance X P) = 5 := by
  rw [variance_of_hasLaw_exp hX (by norm_num)]
  rw [show (1 : ℝ) / (1 / 5) ^ 2 = 5 ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-- OpenStax Introductory Statistics 2e Practice exercise 5.51. The density of `X ~ Exp(0.2)` is
`0.2 e^{-0.2 x}` for `x ≥ 0` (as an extended-real value). -/
@[kb "openstaxintrostats2e" "Exercise 5.51, p. 334"]
theorem ex_5_51_exponential_density :
    ∀ x : ℝ, 0 ≤ x → exponentialPDF (1 / 5) x = ENNReal.ofReal (1 / 5 * exp (-(x / 5))) := by
  intro x hx
  rw [exponentialPDF_eq, if_pos hx]
  congr 3
  ring

/-- OpenStax Introductory Statistics 2e Practice exercise 5.53. For `X ~ Exp(0.2)`,
`P(2 < X < 10) = e^{-0.4} - e^{-2}`, strictly between `0.5349` and `0.5351`. -/
@[kb "openstaxintrostats2e" "Exercise 5.53, p. 334"]
theorem ex_5_53_exponential_between (hX : HasLaw X (expMeasure (1 / 5)) P) :
    P.real {ω | 2 < X ω ∧ X ω < 10} = exp (-(2 / 5)) - exp (-2) ∧
      0.5349 < P.real {ω | 2 < X ω ∧ X ω < 10} ∧ P.real {ω | 2 < X ω ∧ X ω < 10} < 0.5351 := by
  have h : P.real {ω | 2 < X ω ∧ X ω < 10} = exp (-(2 / 5)) - exp (-2) := by
    rw [exp_between_real hX (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  expb [-(2 / 5), -(2 / 5), 0.67032, 0.670321, 1] as a1 a2
  expb [-2, -1, 0.367878, 0.36788, 2] as b1 b2
  norm_num at a1 a2 b1 b2
  refine ⟨h, ?_, ?_⟩ <;> rw [h] <;> linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 5.54. For `X ~ Exp(0.2)`,
`P(X > 6) = e^{-1.2}`, strictly between `0.3011` and `0.3013`. -/
@[kb "openstaxintrostats2e" "Exercise 5.54, p. 334"]
theorem ex_5_54_exponential_survival (hX : HasLaw X (expMeasure (1 / 5)) P) :
    P.real {ω | 6 < X ω} = exp (-(6 / 5)) ∧ 0.3011 < P.real {ω | 6 < X ω} ∧
      P.real {ω | 6 < X ω} < 0.3013 := by
  have h : P.real {ω | 6 < X ω} = exp (-(6 / 5)) := by
    rw [expMeasure_survival_of_hasLaw hX (by norm_num) (by norm_num)]
    norm_num
  expb [-(6 / 5), -(3 / 5), 0.548811, 0.548812, 2] as a1 a2
  norm_num at a1 a2
  refine ⟨h, ?_, ?_⟩ <;> rw [h] <;> linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 5.55. For `X ~ Exp(0.2)` the 70th
percentile is `k = -ln(0.3)/0.2`, with `P(X ≤ k) = 0.7`, strictly between `6.0195` and `6.02`
(the book's `6.02`). -/
@[kb "openstaxintrostats2e" "Exercise 5.55, p. 334"]
theorem ex_5_55_exponential_percentile_70 (hX : HasLaw X (expMeasure (1 / 5)) P) :
    P.real {ω | X ω ≤ -Real.log (1 - 7 / 10) / (1 / 5)} = 7 / 10 ∧
      6.0195 < -Real.log (1 - 7 / 10) / (1 / 5) ∧ -Real.log (1 - 7 / 10) / (1 / 5) < 6.02 := by
  refine ⟨expMeasure_percentile_of_hasLaw hX (by norm_num) (by norm_num) (by norm_num), ?_⟩
  expb [-(12039 / 10000), -(12039 / 20000), 0.547742, 0.547743, 2] as a1 a2
  expb [-(301 / 250), -(301 / 500), 0.547715, 0.547716, 2] as b1 b2
  norm_num at a1 a2 b1 b2
  exact pct_bd (m := 1 / 5) (p := 7 / 10) (lo := 6.0195) (hi := 6.02) (by norm_num) (by norm_num)
    (by norm_num; linarith) (by norm_num; linarith)

/-! ### `X ~ Exp(0.75)` (exercises 56-63) -/

/-- OpenStax Introductory Statistics 2e Practice exercise 5.56. For `X ~ Exp(0.75)` the decay rate
`m = 0.75` is the value of the density at `0`, and the mean is `1/m = 4/3`. -/
@[kb "openstaxintrostats2e" "Exercise 5.56, p. 334"]
theorem ex_5_56_decay_rate (hX : HasLaw X (expMeasure (3 / 4)) P) :
    exponentialPDF (3 / 4) 0 = ENNReal.ofReal (3 / 4) ∧ P[X] = 1 / (3 / 4 : ℝ) := by
  constructor
  · rw [exponentialPDF_eq, if_pos le_rfl]; simp
  · rw [expectation_of_hasLaw_exp hX (by norm_num)]

/-- OpenStax Introductory Statistics 2e Practice exercise 5.57. The density of `X ~ Exp(0.75)` is
`0.75 e^{-0.75 x}` for `x ≥ 0` (as an extended-real value). -/
@[kb "openstaxintrostats2e" "Exercise 5.57, p. 334"]
theorem ex_5_57_exponential_density :
    ∀ x : ℝ, 0 ≤ x → exponentialPDF (3 / 4) x = ENNReal.ofReal (3 / 4 * exp (-(3 / 4 * x))) := by
  intro x hx
  rw [exponentialPDF_eq, if_pos hx]

/-- OpenStax Introductory Statistics 2e Practice exercise 5.58. The distribution function of
`X ~ Exp(0.75)` is `F(x) = 1 - e^{-0.75 x}` for `x ≥ 0` (and `0` for `x < 0`). -/
@[kb "openstaxintrostats2e" "Exercise 5.58, p. 334"]
theorem ex_5_58_exponential_cdf :
    ∀ x : ℝ, cdf (expMeasure (3 / 4)) x = if 0 ≤ x then 1 - exp (-(3 / 4 * x)) else 0 := by
  intro x
  exact cdf_expMeasure_eq (by norm_num) x

/-- OpenStax Introductory Statistics 2e Practice exercise 5.60. For `X ~ Exp(0.75)`,
`P(X < 4) = 1 - e^{-3}`, strictly between `0.9502` and `0.9503`. -/
@[kb "openstaxintrostats2e" "Exercise 5.60, p. 334"]
theorem ex_5_60_exponential_below_four (hX : HasLaw X (expMeasure (3 / 4)) P) :
    P.real {ω | 0 < X ω ∧ X ω < 4} = 1 - exp (-3) ∧ 0.9502 < P.real {ω | 0 < X ω ∧ X ω < 4} ∧
      P.real {ω | 0 < X ω ∧ X ω < 4} < 0.9503 := by
  have h : P.real {ω | 0 < X ω ∧ X ω < 4} = 1 - exp (-3) := by
    rw [exp_between_real hX (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  expb [-3, -1, 0.367878, 0.36788, 3] as a1 a2
  norm_num at a1 a2
  refine ⟨h, ?_, ?_⟩ <;> rw [h] <;> linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 5.61. For `X ~ Exp(0.75)` the 30th
percentile is `k = -ln(0.7)/0.75`, with `P(X ≤ k) = 0.3`, strictly between `0.4754` and `0.4757`
(the book's `0.4756`). -/
@[kb "openstaxintrostats2e" "Exercise 5.61, p. 334"]
theorem ex_5_61_exponential_percentile_30 (hX : HasLaw X (expMeasure (3 / 4)) P) :
    P.real {ω | X ω ≤ -Real.log (1 - 3 / 10) / (3 / 4)} = 3 / 10 ∧
      0.4754 < -Real.log (1 - 3 / 10) / (3 / 4) ∧ -Real.log (1 - 3 / 10) / (3 / 4) < 0.4757 := by
  refine ⟨expMeasure_percentile_of_hasLaw hX (by norm_num) (by norm_num) (by norm_num), ?_⟩
  expb [-(7131 / 20000), -(7131 / 20000), 0.700087, 0.700088, 1] as a1 a2
  expb [-(14271 / 40000), -(14271 / 40000), 0.699929, 0.69993, 1] as b1 b2
  norm_num at a1 a2 b1 b2
  exact pct_bd (m := 3 / 4) (p := 3 / 10) (lo := 0.4754) (hi := 0.4757) (by norm_num) (by norm_num)
    (by norm_num; linarith) (by norm_num; linarith)

/-- OpenStax Introductory Statistics 2e Practice exercise 5.62. The median of `X ~ Exp(0.75)` is
`k = -ln(0.5)/0.75`, with `P(X ≤ k) = 1/2`, strictly between `0.9241` and `0.9243` (the book's
`0.9242`). -/
@[kb "openstaxintrostats2e" "Exercise 5.62, p. 334"]
theorem ex_5_62_exponential_median (hX : HasLaw X (expMeasure (3 / 4)) P) :
    P.real {ω | X ω ≤ -Real.log (1 - 1 / 2) / (3 / 4)} = 1 / 2 ∧
      0.9241 < -Real.log (1 - 1 / 2) / (3 / 4) ∧ -Real.log (1 - 1 / 2) / (3 / 4) < 0.9243 := by
  refine ⟨expMeasure_percentile_of_hasLaw hX (by norm_num) (by norm_num) (by norm_num), ?_⟩
  expb [-(27723 / 40000), -(27723 / 40000), 0.500036, 0.500037, 1] as a1 a2
  expb [-(27729 / 40000), -(27729 / 40000), 0.499961, 0.499962, 1] as b1 b2
  norm_num at a1 a2 b1 b2
  exact pct_bd (m := 3 / 4) (p := 1 / 2) (lo := 0.9241) (hi := 0.9243) (by norm_num) (by norm_num)
    (by norm_num; linarith) (by norm_num; linarith)

/-- OpenStax Introductory Statistics 2e Practice exercise 5.63. For `X ~ Exp(0.75)` the mean `4/3` is
larger than the median `ln 2 / 0.75 ≈ 0.9242`. -/
@[kb "openstaxintrostats2e" "Exercise 5.63, p. 334"]
theorem ex_5_63_mean_larger_than_median (hX : HasLaw X (expMeasure (3 / 4)) P) :
    P[X] = 4 / 3 ∧ -Real.log (1 - 1 / 2) / (3 / 4) < P[X] := by
  have hm : P[X] = 4 / 3 := by
    rw [expectation_of_hasLaw_exp hX (by norm_num)]; norm_num
  refine ⟨hm, ?_⟩
  rw [hm]
  have e : -Real.log (1 - 1 / 2) = Real.log 2 := by
    rw [show (1 : ℝ) - 1 / 2 = (2 : ℝ)⁻¹ by norm_num, Real.log_inv, neg_neg]
  rw [e, div_lt_iff₀ (by norm_num)]
  linarith [Real.log_two_lt_d9]

/-! ### Carbon-14, decay rate `m = 0.000121` (exercises 64-71) -/

/-- OpenStax Introductory Statistics 2e Practice exercise 5.69. With decay rate `0.000121`, the share
of carbon-14 that has decayed within `5730` years (the half-life) is `P(X < 5730) = 1 - e^{-0.69333}`,
strictly between `0.5000` and `0.5002` (the book's `0.5001`). -/
@[kb "openstaxintrostats2e" "Exercise 5.69, p. 334"]
theorem ex_5_69_carbon_decayed_half_life (hX : HasLaw X (expMeasure (121 / 1000000)) P) :
    P.real {ω | 0 < X ω ∧ X ω < 5730} = 1 - exp (-(69333 / 100000)) ∧
      0.5000 < P.real {ω | 0 < X ω ∧ X ω < 5730} ∧ P.real {ω | 0 < X ω ∧ X ω < 5730} < 0.5002 := by
  have h : P.real {ω | 0 < X ω ∧ X ω < 5730} = 1 - exp (-(69333 / 100000)) := by
    rw [exp_between_real hX (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  expb [-(69333 / 100000), -(69333 / 100000), 0.499908, 0.499909, 1] as a1 a2
  norm_num at a1 a2
  refine ⟨h, ?_, ?_⟩ <;> rw [h] <;> linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 5.70. With decay rate `0.000121`, the share
of carbon-14 lasting longer than 10,000 years is `P(X > 10000) = e^{-1.21}`, strictly between
`0.2981` and `0.2983`. -/
@[kb "openstaxintrostats2e" "Exercise 5.70, p. 335"]
theorem ex_5_70_carbon_longer_than_10000 (hX : HasLaw X (expMeasure (121 / 1000000)) P) :
    P.real {ω | 10000 < X ω} = exp (-(121 / 100)) ∧ 0.2981 < P.real {ω | 10000 < X ω} ∧
      P.real {ω | 10000 < X ω} < 0.2983 := by
  have h : P.real {ω | 10000 < X ω} = exp (-(121 / 100)) := by
    rw [expMeasure_survival_of_hasLaw hX (by norm_num) (by norm_num)]
    norm_num
  expb [-(121 / 100), -(121 / 200), 0.546074, 0.546075, 2] as a1 a2
  norm_num at a1 a2
  refine ⟨h, ?_, ?_⟩ <;> rw [h] <;> linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 5.71. With decay rate `0.000121`, 30% of the
carbon-14 decays within `k = -ln(0.7)/0.000121` years, i.e. `P(X ≤ k) = 0.3`, and `k` lies strictly
between `2947.6` and `2947.8` (the book's `2947.73`). -/
@[kb "openstaxintrostats2e" "Exercise 5.71, p. 335"]
theorem ex_5_71_carbon_percentile_30 (hX : HasLaw X (expMeasure (121 / 1000000)) P) :
    P.real {ω | X ω ≤ -Real.log (1 - 3 / 10) / (121 / 1000000)} = 3 / 10 ∧
      2947.6 < -Real.log (1 - 3 / 10) / (121 / 1000000) ∧
      -Real.log (1 - 3 / 10) / (121 / 1000000) < 2947.8 := by
  refine ⟨expMeasure_percentile_of_hasLaw hX (by norm_num) (by norm_num) (by norm_num), ?_⟩
  expb [-(891649 / 2500000), -(891649 / 2500000), 0.70001, 0.700011, 1] as a1 a2
  expb [-(1783419 / 5000000), -(1783419 / 5000000), 0.699993, 0.699994, 1] as b1 b2
  norm_num at a1 a2 b1 b2
  exact pct_bd (m := 121 / 1000000) (p := 3 / 10) (lo := 2947.6) (hi := 2947.8) (by norm_num)
    (by norm_num) (by norm_num; linarith) (by norm_num; linarith)

end Exponential

end UndergradKB.Statistics.Course.PracticeC5
