import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.MeanValue
import UndergradKB.Common.Attr
import UndergradKB.Statistics.NormalSample

/-!
# The empirical (68-95-99.7) rule (OpenStax *Introductory Statistics 2e*, §2.7 and §6.1)

For a standard normal `Z`, `P(|Z| < k)` is about `0.68`, `0.95`, `0.997` for `k = 1, 2, 3`.  We
prove explicit numerical enclosures.  The method: `P(|Z| < k) = (2 / √(2π)) ∫₀ᵏ exp(-x²/2) dx`;
the integrand is squeezed between alternating partial sums of the Taylor series of `exp(-y)`
(`y = x²/2`), which integrate termwise to rational numbers; `√(2π)` is bounded using the
decimal bounds on `π`.
-/

namespace UndergradKB.Statistics

open MeasureTheory ProbabilityTheory Real Set
open scoped Nat

/-! ### Alternating Taylor bounds for `exp(-y)` -/

/-- Partial sum of the Taylor series of `exp(-y)` with `n` terms. -/
noncomputable def empT (n : ℕ) (y : ℝ) : ℝ := ∑ j ∈ Finset.range n, (-y) ^ j / (j ! : ℝ)

lemma empT_hasDerivAt (n : ℕ) (y : ℝ) :
    HasDerivAt (fun y ↦ empT (n + 1) y) (-(empT n y)) y := by
  unfold empT
  simp_rw [Finset.sum_range_succ' _ n]
  have h : HasDerivAt (fun y : ℝ ↦ ∑ j ∈ Finset.range n, (-y) ^ (j + 1) / ((j + 1)! : ℝ))
      (∑ j ∈ Finset.range n, -((-y) ^ j / (j ! : ℝ))) y := by
    apply HasDerivAt.fun_sum
    intro j _
    have h1 : HasDerivAt (fun y : ℝ ↦ (-y) ^ (j + 1)) (((j + 1 : ℕ) : ℝ) * (-y) ^ j * (-1)) y := by
      simpa using (hasDerivAt_neg y).fun_pow (j + 1)
    have h2 := h1.div_const ((j + 1)! : ℝ)
    convert h2 using 1
    rw [Nat.factorial_succ]
    push_cast
    have : (j ! : ℝ) ≠ 0 := by positivity
    field_simp
  have h' := h.add_const 1
  simp only [Nat.factorial_zero, Nat.cast_one, pow_zero, div_one] at h' ⊢
  rw [Finset.sum_neg_distrib] at h'
  simpa using h'

lemma empT_zero_at (n : ℕ) : empT (n + 1) 0 = 1 := by
  unfold empT
  rw [Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, pow_zero, div_one]
  have : ∀ j ∈ Finset.range n, (-(0 : ℝ)) ^ (j + 1) / ((j + 1)! : ℝ) = 0 := by
    intro j _
    simp
  rw [Finset.sum_eq_zero this]
  simp

lemma exp_neg_empT (n : ℕ) : ∀ y : ℝ, 0 ≤ y → 0 ≤ (-1) ^ n * (rexp (-y) - empT n y) := by
  induction n with
  | zero =>
    intro y _
    simp [empT]
    positivity
  | succ n ih =>
    have hd : ∀ y : ℝ, HasDerivAt (fun y ↦ (-1 : ℝ) ^ (n + 1) * (rexp (-y) - empT (n + 1) y))
        ((-1) ^ n * (rexp (-y) - empT n y)) y := by
      intro y
      have h1 : HasDerivAt (fun y : ℝ ↦ rexp (-y)) (-rexp (-y)) y := by
        simpa using (hasDerivAt_neg y).exp
      have h2 := (h1.sub (empT_hasDerivAt n y)).const_mul ((-1 : ℝ) ^ (n + 1))
      convert h2 using 1
      rw [pow_succ]
      ring
    have hmono : MonotoneOn (fun y ↦ (-1 : ℝ) ^ (n + 1) * (rexp (-y) - empT (n + 1) y)) (Ici 0) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
        (f' := fun y ↦ (-1) ^ n * (rexp (-y) - empT n y))
      · exact fun x _ ↦ (hd x).continuousAt.continuousWithinAt
      · exact fun x _ ↦ (hd x).hasDerivWithinAt
      · intro x hx
        rw [interior_Ici] at hx
        exact ih x (le_of_lt hx)
    intro y hy
    have := hmono (a := 0) (b := y) (by simp) hy hy
    simpa [empT_zero_at] using this

lemma exp_neg_le_empT_odd (m : ℕ) {y : ℝ} (hy : 0 ≤ y) : rexp (-y) ≤ empT (2 * m + 1) y := by
  have := exp_neg_empT (2 * m + 1) y hy
  rw [pow_succ, pow_mul] at this
  simp at this
  linarith

lemma empT_even_le_exp_neg (m : ℕ) {y : ℝ} (hy : 0 ≤ y) : empT (2 * m) y ≤ rexp (-y) := by
  have := exp_neg_empT (2 * m) y hy
  rw [pow_mul] at this
  simp at this
  linarith

/-! ### Integrating the partial sums -/

/-- The rational partial sum `∑_{j<n} (-1)^j k^(2j+1) / (2^j j! (2j+1))` of `∫₀ᵏ exp(-x²/2)`. -/
noncomputable def empR (n : ℕ) (k : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, (-1) ^ j * k ^ (2 * j + 1) / (2 ^ j * (j ! : ℝ) * (2 * j + 1))

lemma integral_empT (n : ℕ) (k : ℝ) : ∫ x in (0 : ℝ)..k, empT n (x ^ 2 / 2) = empR n k := by
  unfold empT empR
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    have : ∀ x : ℝ, (-(x ^ 2 / 2)) ^ j / (j ! : ℝ) = ((-1) ^ j / (2 ^ j * (j ! : ℝ))) * x ^ (2 * j) := by
      intro x
      have : (-(x ^ 2 / 2)) ^ j = (-1) ^ j * (x ^ 2) ^ j / 2 ^ j := by
        rw [neg_eq_neg_one_mul, mul_pow, div_pow]; ring
      rw [this, ← pow_mul]
      ring
    simp_rw [this]
    rw [intervalIntegral.integral_const_mul, integral_pow]
    have : (2 * j + 1 : ℝ) ≠ 0 := by positivity
    have : (j ! : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  · intro j _
    apply Continuous.intervalIntegrable
    fun_prop

/-! ### Bounds on the integral -/

lemma intervalIntegrable_gauss (k : ℝ) :
    IntervalIntegrable (fun x : ℝ ↦ rexp (-(x ^ 2 / 2))) volume 0 k := by
  apply Continuous.intervalIntegrable
  fun_prop

lemma integral_gauss_le (m : ℕ) {k : ℝ} (hk : 0 ≤ k) :
    ∫ x in (0 : ℝ)..k, rexp (-(x ^ 2 / 2)) ≤ empR (2 * m + 1) k := by
  rw [← integral_empT]
  apply intervalIntegral.integral_mono_on hk (intervalIntegrable_gauss k)
  · apply Continuous.intervalIntegrable
    unfold empT
    fun_prop
  · intro x _
    exact exp_neg_le_empT_odd m (by positivity)

lemma le_integral_gauss (m : ℕ) {k : ℝ} (hk : 0 ≤ k) :
    empR (2 * m) k ≤ ∫ x in (0 : ℝ)..k, rexp (-(x ^ 2 / 2)) := by
  rw [← integral_empT]
  apply intervalIntegral.integral_mono_on hk _ (intervalIntegrable_gauss k)
  · intro x _
    exact empT_even_le_exp_neg m (by positivity)
  · apply Continuous.intervalIntegrable
    unfold empT
    fun_prop

/-! ### The central mass as an integral -/

lemma gaussianPDFReal_std (x : ℝ) :
    gaussianPDFReal 0 1 x = (√(2 * π))⁻¹ * rexp (-(x ^ 2 / 2)) := by
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one, neg_div]

lemma gaussianReal_real_Ioo_eq {k : ℝ} (hk : 0 ≤ k) :
    (gaussianReal 0 1).real (Ioo (-k) k) =
      2 * (∫ x in (0 : ℝ)..k, rexp (-(x ^ 2 / 2))) / √(2 * π) := by
  have h := gaussianReal_apply_eq_integral 0 (v := 1) one_ne_zero (Ioo (-k) k)
  unfold Measure.real
  rw [h, ENNReal.toReal_ofReal (integral_nonneg (fun x ↦ gaussianPDFReal_nonneg _ _ _))]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith)]
  simp_rw [gaussianPDFReal_std]
  rw [intervalIntegral.integral_const_mul]
  have hc : Continuous fun x : ℝ ↦ rexp (-(x ^ 2 / 2)) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have : ∫ x in (-k)..0, rexp (-(x ^ 2 / 2)) = ∫ x in (0 : ℝ)..k, rexp (-(x ^ 2 / 2)) := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := k)
      (fun x : ℝ ↦ rexp (-(x ^ 2 / 2)))
    simpa using this.symm
  rw [this]
  ring

/-! ### Bounds on `√(2π)` -/

lemma sqrt_two_pi_gt : (2.5066 : ℝ) < √(2 * π) := by
  have := Real.pi_gt_d6
  apply Real.lt_sqrt_of_sq_lt
  linarith

lemma sqrt_two_pi_lt : √(2 * π) < (2.5067 : ℝ) := by
  have := Real.pi_lt_d6
  rw [Real.sqrt_lt' (by norm_num)]
  linarith

/-! ### The three bounds for the standard normal -/

lemma emp_one :
    (0.68 : ℝ) < (gaussianReal 0 1).real (Ioo (-1) 1) ∧
      (gaussianReal 0 1).real (Ioo (-1) 1) < 0.69 := by
  have h := gaussianReal_real_Ioo_eq (k := 1) (by norm_num)
  have hl := le_integral_gauss 2 (k := 1) (by norm_num)
  have hu := integral_gauss_le 1 (k := 1) (by norm_num)
  have s1 := sqrt_two_pi_gt
  have s2 := sqrt_two_pi_lt
  simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero] at hl hu
  norm_num [Nat.factorial] at hl hu
  rw [h]
  have hp : 0 < √(2 * π) := by linarith
  constructor
  · rw [lt_div_iff₀ hp]; nlinarith
  · rw [div_lt_iff₀ hp]; nlinarith

lemma emp_two :
    (0.95 : ℝ) < (gaussianReal 0 1).real (Ioo (-2) 2) ∧
      (gaussianReal 0 1).real (Ioo (-2) 2) < 0.96 := by
  have h := gaussianReal_real_Ioo_eq (k := 2) (by norm_num)
  have hl := le_integral_gauss 4 (k := 2) (by norm_num)
  have hu := integral_gauss_le 4 (k := 2) (by norm_num)
  have s1 := sqrt_two_pi_gt
  have s2 := sqrt_two_pi_lt
  simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero] at hl hu
  norm_num [Nat.factorial] at hl hu
  rw [h]
  have hp : 0 < √(2 * π) := by linarith
  constructor
  · rw [lt_div_iff₀ hp]; nlinarith
  · rw [div_lt_iff₀ hp]; nlinarith

lemma emp_three :
    (0.997 : ℝ) < (gaussianReal 0 1).real (Ioo (-3) 3) ∧
      (gaussianReal 0 1).real (Ioo (-3) 3) < 0.998 := by
  have h := gaussianReal_real_Ioo_eq (k := 3) (by norm_num)
  have hl := le_integral_gauss 8 (k := 3) (by norm_num)
  have hu := integral_gauss_le 8 (k := 3) (by norm_num)
  have s1 := sqrt_two_pi_gt
  have s2 := sqrt_two_pi_lt
  simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero] at hl hu
  norm_num [Nat.factorial] at hl hu
  rw [h]
  have hp : 0 < √(2 * π) := by linarith
  constructor
  · rw [lt_div_iff₀ hp]; nlinarith
  · rw [div_lt_iff₀ hp]; nlinarith

/-! ### Headline statements -/

/-- OpenStax Introductory Statistics 2e §6.1 (ST-060), the empirical rule for the standard
normal distribution: the mass within one, two, three standard deviations of the mean lies in
`(0.68, 0.69)`, `(0.95, 0.96)`, `(0.997, 0.998)` respectively (true values about
`0.6827, 0.9545, 0.9973`). -/
@[kb "openstaxintrostats2e" "§6.1, p. 347"]
theorem empirical_rule_standard_normal :
    ((0.68 : ℝ) < (gaussianReal 0 1).real (Ioo (-1) 1) ∧
      (gaussianReal 0 1).real (Ioo (-1) 1) < 0.69) ∧
    ((0.95 : ℝ) < (gaussianReal 0 1).real (Ioo (-2) 2) ∧
      (gaussianReal 0 1).real (Ioo (-2) 2) < 0.96) ∧
    ((0.997 : ℝ) < (gaussianReal 0 1).real (Ioo (-3) 3) ∧
      (gaussianReal 0 1).real (Ioo (-3) 3) < 0.998) :=
  ⟨emp_one, emp_two, emp_three⟩

/-- Reduction to the standard normal: for `X ~ N(μ, σ²)`, `P(|X - μ| < kσ) = P(|Z| < k)`. -/
lemma real_abs_sub_lt_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {μ σ : ℝ} (hσ : 0 < σ) (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) (k : ℝ) :
    P.real {ω | |X ω - μ| < k * σ} = (gaussianReal 0 1).real (Ioo (-k) k) := by
  have hZ := hasLaw_standardize hσ hX
  have hset : {ω | |X ω - μ| < k * σ} = (fun ω ↦ (X ω - μ) / σ) ⁻¹' Ioo (-k) k := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage, mem_Ioo, abs_lt]
    rw [lt_div_iff₀ hσ, div_lt_iff₀ hσ]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  unfold Measure.real
  rw [hset, ← hZ.map_eq, Measure.map_apply_of_aemeasurable hZ.aemeasurable measurableSet_Ioo]

/-- OpenStax Introductory Statistics 2e §6.1 (ST-060), empirical rule for a general normal
variable `X ~ N(μ, σ²)`, `σ > 0`: the probability of landing within `σ`, `2σ`, `3σ` of the mean
lies in `(0.68, 0.69)`, `(0.95, 0.96)`, `(0.997, 0.998)`. -/
@[kb "openstaxintrostats2e" "§6.1, p. 347"]
theorem empirical_rule_normal {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {μ σ : ℝ} (hσ : 0 < σ) (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) :
    ((0.68 : ℝ) < P.real {ω | |X ω - μ| < 1 * σ} ∧ P.real {ω | |X ω - μ| < 1 * σ} < 0.69) ∧
    ((0.95 : ℝ) < P.real {ω | |X ω - μ| < 2 * σ} ∧ P.real {ω | |X ω - μ| < 2 * σ} < 0.96) ∧
    ((0.997 : ℝ) < P.real {ω | |X ω - μ| < 3 * σ} ∧ P.real {ω | |X ω - μ| < 3 * σ} < 0.998) := by
  rw [real_abs_sub_lt_eq hσ hX, real_abs_sub_lt_eq hσ hX, real_abs_sub_lt_eq hσ hX]
  have h1 := emp_one
  have h2 := emp_two
  have h3 := emp_three
  exact ⟨h1, h2, h3⟩

/-- OpenStax Introductory Statistics 2e §2.7 (ST-016), the empirical rule for bell-shaped data:
in a normal population (a random draw `X ~ N(μ, σ²)`), about 68%, 95%, 99.7% of the values lie
within one, two, three standard deviations of the mean; precisely, the probabilities of
`(μ - kσ, μ + kσ)` lie in `(0.68, 0.69)`, `(0.95, 0.96)`, `(0.997, 0.998)`. -/
@[kb "openstaxintrostats2e" "§2.7, p. 118"]
theorem empirical_rule_normal_population {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {μ σ : ℝ} (hσ : 0 < σ)
    (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) :
    ((0.68 : ℝ) < P.real {ω | X ω ∈ Ioo (μ - σ) (μ + σ)} ∧
      P.real {ω | X ω ∈ Ioo (μ - σ) (μ + σ)} < 0.69) ∧
    ((0.95 : ℝ) < P.real {ω | X ω ∈ Ioo (μ - 2 * σ) (μ + 2 * σ)} ∧
      P.real {ω | X ω ∈ Ioo (μ - 2 * σ) (μ + 2 * σ)} < 0.96) ∧
    ((0.997 : ℝ) < P.real {ω | X ω ∈ Ioo (μ - 3 * σ) (μ + 3 * σ)} ∧
      P.real {ω | X ω ∈ Ioo (μ - 3 * σ) (μ + 3 * σ)} < 0.998) := by
  have e : ∀ k : ℝ, {ω | X ω ∈ Ioo (μ - k * σ) (μ + k * σ)} = {ω | |X ω - μ| < k * σ} := by
    intro k
    ext ω
    simp only [mem_ofPred_eq, mem_Ioo, abs_lt]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have e1 := e 1
  rw [one_mul] at e1
  rw [e1, e 2, e 3]
  simpa only [one_mul] using empirical_rule_normal hσ hX

end UndergradKB.Statistics
