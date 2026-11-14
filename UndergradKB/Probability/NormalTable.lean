import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic
import UndergradKB.Common.Attr
import UndergradKB.Probability.ExamplesNormalApprox

/-! # Probability: certified values of the normal table (Grinstead–Snell, Examples 5.8, 9.2-9.10)

The book reads the values of the standard normal distribution function `Φ` from a table. Here they are
proved: for `t ≥ 0` the partial sums of the series of `e^{-t}` alternate around it, so integrating them
against `t = x²/2` brackets `∫₀^a e^{-x²/2} dx` between two explicit rational numbers, and
`Φ(a) = 1/2 + (2π)^{-1/2} ∫₀^a e^{-x²/2} dx`. The rational comparisons are checked by the kernel. -/

open MeasureTheory ProbabilityTheory Set Finset Real
open scoped ENNReal NNReal

namespace UndergradKB.Probability

/-! ## Alternating bounds for `e^{-t}` -/

/-- The partial sum `∑_{k<n} (-t)^k / k!` of the series of `e^{-t}`. -/
noncomputable def expNegPartial (n : ℕ) (t : ℝ) : ℝ := ∑ k ∈ range n, (-t) ^ k / k.factorial

lemma expNegPartial_succ_zero (n : ℕ) : expNegPartial (n + 1) 0 = 1 := by
  simp [expNegPartial, Finset.sum_range_succ']

lemma hasDerivAt_expNegPartial (n : ℕ) (t : ℝ) :
    HasDerivAt (expNegPartial (n + 1)) (-expNegPartial n t) t := by
  induction n with
  | zero =>
    have e : expNegPartial 1 = fun _ => 1 := by funext s; simp [expNegPartial]
    rw [e]; simpa [expNegPartial] using hasDerivAt_const t (1 : ℝ)
  | succ n ih =>
    have e : expNegPartial (n + 2) =
        fun s => expNegPartial (n + 1) s + (-s) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
      funext s; simp [expNegPartial, Finset.sum_range_succ _ (n + 1)]
    rw [e]
    have h2 : HasDerivAt (fun s : ℝ => (-s) ^ (n + 1) / ((n + 1).factorial : ℝ))
        (((n + 1 : ℕ) : ℝ) * (-t) ^ n * (-1) / ((n + 1).factorial : ℝ)) t := by
      have := ((hasDerivAt_neg t).pow (n + 1)).div_const ((n + 1).factorial : ℝ)
      simpa using this
    convert ih.add h2 using 1
    simp only [expNegPartial, Finset.sum_range_succ _ n, Nat.factorial_succ, Nat.cast_mul]
    have : (n.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring

/-- For `t ≥ 0`, `e^{-t} - ∑_{k<n} (-t)^k/k!` has the sign of `(-1)^n`. -/
lemma expNeg_alternating (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ (-1) ^ n * (rexp (-t) - expNegPartial n t) := by
  induction n generalizing t with
  | zero => simp [expNegPartial]; positivity
  | succ n ih =>
    set h : ℝ → ℝ := fun s => (-1) ^ (n + 1) * (rexp (-s) - expNegPartial (n + 1) s) with hh
    have hd : ∀ s, HasDerivAt h ((-1) ^ n * (rexp (-s) - expNegPartial n s)) s := by
      intro s
      have := (((hasDerivAt_neg s).exp).sub (hasDerivAt_expNegPartial n s)).const_mul
        ((-1 : ℝ) ^ (n + 1))
      convert this using 1
      ring
    have hmono : MonotoneOn h (Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      · exact fun s _ => (hd s).continuousAt.continuousWithinAt
      · exact fun s _ => (hd s).differentiableAt.differentiableWithinAt
      · intro s hs
        rw [interior_Ici] at hs
        rw [(hd s).deriv]
        exact ih (le_of_lt hs)
    have h0 : h 0 = 0 := by simp [hh, expNegPartial_succ_zero]
    have := hmono (Set.mem_Ici.2 le_rfl) ht ht
    rw [h0] at this
    exact this

lemma expNegPartial_le_even (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    expNegPartial (2 * m) t ≤ rexp (-t) := by
  have := expNeg_alternating (2 * m) ht
  rw [pow_mul, neg_one_sq, one_pow, one_mul] at this
  linarith

lemma le_expNegPartial_odd (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    rexp (-t) ≤ expNegPartial (2 * m + 1) t := by
  have := expNeg_alternating (2 * m + 1) ht
  rw [pow_succ, pow_mul, neg_one_sq, one_pow, one_mul] at this
  linarith

/-! ## Bracketing the Gaussian integral -/

/-- `∫₀^a` of the partial sum at `x²/2`: `∑_{k<n} (-1/2)^k / k! · a^{2k+1} / (2k+1)`. -/
noncomputable def gaussTaylor (n : ℕ) (a : ℝ) : ℝ :=
  ∑ k ∈ range n, (-1 / 2 : ℝ) ^ k / k.factorial * (a ^ (2 * k + 1) / (2 * k + 1))

/-- The same number, computed in `ℚ` (for kernel evaluation). -/
def gaussTaylorQ (n : ℕ) (a : ℚ) : ℚ :=
  ∑ k ∈ range n, (-1 / 2 : ℚ) ^ k / k.factorial * (a ^ (2 * k + 1) / (2 * k + 1))

lemma gaussTaylorQ_cast (n : ℕ) (a : ℚ) : ((gaussTaylorQ n a : ℚ) : ℝ) = gaussTaylor n a := by
  simp [gaussTaylorQ, gaussTaylor]

lemma integral_expNegPartial (n : ℕ) (a : ℝ) :
    ∫ x in (0 : ℝ)..a, expNegPartial n (x ^ 2 / 2) = gaussTaylor n a := by
  have e : (fun x : ℝ => expNegPartial n (x ^ 2 / 2)) =
      fun x => ∑ k ∈ range n, (-1 / 2 : ℝ) ^ k / k.factorial * x ^ (2 * k) := by
    funext x
    unfold expNegPartial
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_mul, show -(x ^ 2 / 2) = (-1 / 2) * x ^ 2 by ring, mul_pow]
    ring
  rw [e, intervalIntegral.integral_finsetSum (fun k _ => by
    exact (continuous_const.mul (continuous_pow _)).intervalIntegrable _ _)]
  unfold gaussTaylor
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_pow]
  push_cast
  ring

lemma gaussIntegral_bounds (m : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    gaussTaylor (2 * m) a ≤ ∫ x in (0 : ℝ)..a, rexp (-(x ^ 2 / 2)) ∧
      ∫ x in (0 : ℝ)..a, rexp (-(x ^ 2 / 2)) ≤ gaussTaylor (2 * m + 1) a := by
  have hc : ∀ n, Continuous fun x : ℝ => expNegPartial n (x ^ 2 / 2) := fun n => by
    unfold expNegPartial; fun_prop
  have he : Continuous fun x : ℝ => rexp (-(x ^ 2 / 2)) := by fun_prop
  constructor
  · rw [← integral_expNegPartial]
    exact intervalIntegral.integral_mono_on ha ((hc _).intervalIntegrable _ _)
      (he.intervalIntegrable _ _) fun x _ => expNegPartial_le_even m (by positivity)
  · rw [← integral_expNegPartial]
    exact intervalIntegral.integral_mono_on ha (he.intervalIntegrable _ _)
      ((hc _).intervalIntegrable _ _) fun x _ => le_expNegPartial_odd m (by positivity)

/-! ## The standard normal distribution function -/

/-- `Φ(0) = 1/2`. -/
lemma stdNormal_cdf_zero : cdf (gaussianReal 0 1) 0 = 1 / 2 := by
  have := normalApprox_cdf_neg 0
  rw [neg_zero] at this
  linarith

/-- For `a ≥ 0`, `Φ(a) = 1/2 + (2π)^{-1/2} ∫₀^a e^{-x²/2} dx`. -/
lemma stdNormal_cdf_eq {a : ℝ} (ha : 0 ≤ a) :
    cdf (gaussianReal 0 1) a = 1 / 2 + (√(2 * π))⁻¹ * ∫ x in (0 : ℝ)..a, rexp (-(x ^ 2 / 2)) := by
  have hdiff : Iic a \ Iic 0 = Ioc 0 a := by ext x; simp [and_comm]
  have h1 : cdf (gaussianReal 0 1) a - cdf (gaussianReal 0 1) 0 =
      (gaussianReal 0 1).real (Ioc 0 a) := by
    rw [cdf_eq_real, cdf_eq_real, ← hdiff,
      measureReal_sdiff (Set.Iic_subset_Iic.2 ha) measurableSet_Iic]
  have h2 : (gaussianReal 0 1).real (Ioc 0 a) = ∫ x in Ioc 0 a, gaussianPDFReal 0 1 x := by
    rw [measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero,
      ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioc
        fun x _ => gaussianPDFReal_nonneg 0 1 x)]
  rw [stdNormal_cdf_zero] at h1
  rw [← intervalIntegral.integral_of_le ha] at h2
  have h3 : ∫ x in (0 : ℝ)..a, gaussianPDFReal 0 1 x =
      (√(2 * π))⁻¹ * ∫ x in (0 : ℝ)..a, rexp (-(x ^ 2 / 2)) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext x
    simp [gaussianPDFReal, neg_div]
  linarith

/-- Rational bracket of `√(2π)`: `2.506628 < √(2π) < 2.506629`. -/
lemma sqrt_two_pi_bounds : (2.506628 : ℝ) < √(2 * π) ∧ √(2 * π) < 2.506629 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]
    nlinarith [pi_gt_d6]
  · rw [Real.sqrt_lt' (by norm_num)]
    nlinarith [pi_lt_d6]

/-- Certified bracket for `Φ` at a nonnegative rational point: if `L ≤ ∫₀^a`-lower-sum and the upper
sum `≤ U` (checked in `ℚ`), then `1/2 + L / 2.506629 < Φ(a) < 1/2 + U / 2.506628`. -/
lemma stdNormal_cdf_bracket (m : ℕ) {a : ℚ} (ha : 0 ≤ a) :
    1 / 2 + (gaussTaylorQ (2 * m) a : ℝ) / √(2 * π) ≤ cdf (gaussianReal 0 1) a ∧
      cdf (gaussianReal 0 1) a ≤ 1 / 2 + (gaussTaylorQ (2 * m + 1) a : ℝ) / √(2 * π) := by
  have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha
  obtain ⟨h1, h2⟩ := gaussIntegral_bounds m ha'
  rw [stdNormal_cdf_eq ha', gaussTaylorQ_cast, gaussTaylorQ_cast]
  have hs : 0 < √(2 * π) := Real.sqrt_pos.2 (by positivity)
  simp only [div_eq_inv_mul] at h1 h2 ⊢
  constructor
  · have := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hs.le); linarith
  · have := mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hs.le); linarith

/-- Numerical form: `Φ(a)` lies strictly between `lo` and `hi` as soon as two rational inequalities
(decidable by evaluation) hold. -/
lemma stdNormal_cdf_between (m : ℕ) {a lo hi : ℚ} (ha : 0 ≤ a)
    (hlo : (lo - 1 / 2) * (2506629 / 1000000) < gaussTaylorQ (2 * m) a)
    (hhi : gaussTaylorQ (2 * m + 1) a < (hi - 1 / 2) * (2506628 / 1000000))
    (hlo2 : 1 / 2 ≤ lo) (hhi' : 1 / 2 < hi) :
    (lo : ℝ) < cdf (gaussianReal 0 1) a ∧ cdf (gaussianReal 0 1) a < hi := by
  obtain ⟨b1, b2⟩ := stdNormal_cdf_bracket m ha
  obtain ⟨s1, s2⟩ := sqrt_two_pi_bounds
  have hs : 0 < √(2 * π) := by linarith
  have hlo' : ((lo : ℝ) - 1 / 2) * 2.506629 < (gaussTaylorQ (2 * m) a : ℝ) := by
    have := (Rat.cast_lt (K := ℝ)).2 hlo; push_cast at this; norm_num at this ⊢; linarith
  have hhi'' : (gaussTaylorQ (2 * m + 1) a : ℝ) < ((hi : ℝ) - 1 / 2) * 2.506628 := by
    have := (Rat.cast_lt (K := ℝ)).2 hhi; push_cast at this; norm_num at this ⊢; linarith
  have hhi3 : (1 : ℝ) / 2 < hi := by
    have := (Rat.cast_lt (K := ℝ)).2 hhi'; push_cast at this; exact this
  constructor
  · refine lt_of_lt_of_le ?_ b1
    rw [← sub_lt_iff_lt_add', lt_div_iff₀ hs]
    have h : (1 : ℝ) / 2 ≤ lo := by
      have := (Rat.cast_le (K := ℝ)).2 hlo2; push_cast at this; exact this
    nlinarith
  · refine lt_of_le_of_lt b2 ?_
    rw [← lt_sub_iff_add_lt', div_lt_iff₀ hs]
    nlinarith

/-! ## Values of `Φ` used by the book -/

/-- `Φ(-a) = 1 - Φ(a)`, so `NA(-a, b) = Φ(b) - Φ(-a) = Φ(b) + Φ(a) - 1`. -/
lemma stdNormal_interval (a b : ℝ) :
    cdf (gaussianReal 0 1) b - cdf (gaussianReal 0 1) (-a) =
      cdf (gaussianReal 0 1) b + cdf (gaussianReal 0 1) a - 1 := by
  rw [normalApprox_cdf_neg]; ring

/-- `.9772 < Φ(2) < .9773`. -/
lemma stdNormal_cdf_two :
    (0.9772 : ℝ) < cdf (gaussianReal 0 1) 2 ∧ cdf (gaussianReal 0 1) 2 < 0.9773 := by
  have := stdNormal_cdf_between 5 (a := 2) (lo := 9772 / 10000) (hi := 9773 / 10000)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num)
  push_cast at this; norm_num at this ⊢; exact this

/-- `.9821 < Φ(2.1) < .98215`. -/
lemma stdNormal_cdf_two_one :
    (0.9821 : ℝ) < cdf (gaussianReal 0 1) 2.1 ∧ cdf (gaussianReal 0 1) 2.1 < 0.98215 := by
  have := stdNormal_cdf_between 5 (a := 21 / 10) (lo := 9821 / 10000) (hi := 98215 / 100000)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num)
  push_cast at this; norm_num at this ⊢; exact this

/-- `.999 < Φ(3.1) < .99905`. -/
lemma stdNormal_cdf_three_one :
    (0.999 : ℝ) < cdf (gaussianReal 0 1) 3.1 ∧ cdf (gaussianReal 0 1) 3.1 < 0.99905 := by
  have := stdNormal_cdf_between 9 (a := 31 / 10) (lo := 999 / 1000) (hi := 99905 / 100000)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num)
  push_cast at this; norm_num at this ⊢; exact this

/-- `.9785 < Φ(2.025) < .9786`. -/
lemma stdNormal_cdf_two_025 :
    (0.9785 : ℝ) < cdf (gaussianReal 0 1) 2.025 ∧ cdf (gaussianReal 0 1) 2.025 < 0.9786 := by
  have := stdNormal_cdf_between 5 (a := 2025 / 1000) (lo := 9785 / 10000) (hi := 9786 / 10000)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num)
  push_cast at this; norm_num at this ⊢; exact this

/-- `.98927 < Φ(2.3) < .98928`. -/
lemma stdNormal_cdf_two_three :
    (0.98927 : ℝ) < cdf (gaussianReal 0 1) 2.3 ∧ cdf (gaussianReal 0 1) 2.3 < 0.98928 := by
  have := stdNormal_cdf_between 7 (a := 23 / 10) (lo := 98927 / 100000) (hi := 98928 / 100000)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num)
  push_cast at this; norm_num at this ⊢; exact this

/-- `.97778 < Φ(2.01) < .97779`. -/
lemma stdNormal_cdf_two_01 :
    (0.97778 : ℝ) < cdf (gaussianReal 0 1) 2.01 ∧ cdf (gaussianReal 0 1) 2.01 < 0.97779 := by
  have := stdNormal_cdf_between 6 (a := 201 / 100) (lo := 97778 / 100000) (hi := 97779 / 100000)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num)
  push_cast at this; norm_num at this ⊢; exact this

/-- `.5886 < Φ(.224) < .58865`. -/
lemma stdNormal_cdf_224 :
    (0.5886 : ℝ) < cdf (gaussianReal 0 1) 0.224 ∧ cdf (gaussianReal 0 1) 0.224 < 0.58865 := by
  have := stdNormal_cdf_between 1 (a := 224 / 1000) (lo := 5886 / 10000) (hi := 58865 / 100000)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num)
  push_cast at this; norm_num at this ⊢; exact this

/-- `.9986 < Φ(3) < .9987`. -/
lemma stdNormal_cdf_three :
    (0.9986 : ℝ) < cdf (gaussianReal 0 1) 3 ∧ cdf (gaussianReal 0 1) 3 < 0.9987 := by
  have := stdNormal_cdf_between 8 (a := 3) (lo := 9986 / 10000) (hi := 9987 / 10000)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num)
  push_cast at this; norm_num at this ⊢; exact this

section BookValues

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- Grinstead–Snell Example 5.8 (PR-200), the value. If `X` is normal with mean `10` and variance `9`,
then `P(4 ≤ X ≤ 16) = Φ(2) - Φ(-2)` lies in `(.9544, .9546)` (the book: `.9772 - .0228 = .9544`;
`Φ(2) = .97725` to five places, so the true value rounds to `.9545`). -/
@[kb "grinsteadsnell2006" "Example 5.8, p. 222"]
theorem normal_within_two_sd_value (hX : HasLaw X (gaussianReal 10 9) P) :
    0.9772 < cdf (gaussianReal 0 1) 2 ∧ cdf (gaussianReal 0 1) 2 < 0.9773 ∧
      0.0227 < cdf (gaussianReal 0 1) (-2) ∧ cdf (gaussianReal 0 1) (-2) < 0.0228 ∧
      0.9544 < P.real {ω | 4 ≤ X ω ∧ X ω ≤ 16} ∧ P.real {ω | 4 ≤ X ω ∧ X ω ≤ 16} < 0.9546 := by
  obtain ⟨h1, h2⟩ := normal_within_two_sd hX
  obtain ⟨c1, c2⟩ := stdNormal_cdf_two
  have hn := normalApprox_cdf_neg 2
  rw [h1, h2]
  refine ⟨c1, c2, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- Grinstead–Snell Example 9.2 (PR-204), the normal values. With the half-unit correction, the
estimate of `P(40 ≤ S₁₀₀ ≤ 60)` for `100` fair tosses is `NA(-2.1, 2.1) = Φ(2.1) - Φ(-2.1)`, which lies
in `(.9642, .9643)` (book: `.9642`), and the estimate of `P(35 ≤ S₁₀₀ ≤ 65)` is
`NA(-3.1, 3.1) ∈ (.9980, .9981)` (book: `.9980`). -/
@[kb "grinsteadsnell2006" "Example 9.2, p. 340"]
theorem coin_hundred_normal_values :
    0.9642 < cdf (gaussianReal 0 1) 2.1 - cdf (gaussianReal 0 1) (-2.1) ∧
      cdf (gaussianReal 0 1) 2.1 - cdf (gaussianReal 0 1) (-2.1) < 0.9643 ∧
      0.9980 < cdf (gaussianReal 0 1) 3.1 - cdf (gaussianReal 0 1) (-3.1) ∧
      cdf (gaussianReal 0 1) 3.1 - cdf (gaussianReal 0 1) (-3.1) < 0.9981 := by
  obtain ⟨a1, a2⟩ := stdNormal_cdf_two_one
  obtain ⟨b1, b2⟩ := stdNormal_cdf_three_one
  rw [stdNormal_interval, stdNormal_interval]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- Grinstead–Snell Example 9.3 (PR-205), the normal value. The estimate of the probability of too
many acceptances is `P(S* ≥ 2.025) = 1 - Φ(2.025)`, which lies in `(.0214, .0215)`. The book's
interpolated `.5 - .4784 = .0216` is slightly off (`NA(0, 2.025) = .47857`). -/
@[kb "grinsteadsnell2006" "Example 9.3, p. 340"]
theorem dartmouth_normal_value :
    0.0214 < 1 - cdf (gaussianReal 0 1) 2.025 ∧ 1 - cdf (gaussianReal 0 1) 2.025 < 0.0215 := by
  obtain ⟨a1, a2⟩ := stdNormal_cdf_two_025
  constructor <;> linarith

/-- Grinstead–Snell Example 9.5 (PR-205), the normal value. The estimate of `P(1400 ≤ S₄₂₀ ≤ 1550)`
for `420` rolls of a die is `NA(-2.01, 2.30) = Φ(2.30) - Φ(-2.01)`, which lies in `(.9670, .9671)`
(book: `.9670`). -/
@[kb "grinsteadsnell2006" "Example 9.5, p. 351"]
theorem die_sum_normal_value :
    0.9670 < cdf (gaussianReal 0 1) 2.3 - cdf (gaussianReal 0 1) (-2.01) ∧
      cdf (gaussianReal 0 1) 2.3 - cdf (gaussianReal 0 1) (-2.01) < 0.9671 := by
  obtain ⟨a1, a2⟩ := stdNormal_cdf_two_three
  obtain ⟨b1, b2⟩ := stdNormal_cdf_two_01
  rw [stdNormal_interval]
  constructor <;> linarith

/-- Grinstead–Snell Example 9.6 (PR-205), the normal value. The estimate for the grading errors is
`NA(-.224, .224) = Φ(.224) - Φ(-.224)`, which lies in `(.1772, .1773)` (book: `.1772`). -/
@[kb "grinsteadsnell2006" "Example 9.6, p. 351"]
theorem grading_error_normal_value :
    0.1772 < cdf (gaussianReal 0 1) 0.224 - cdf (gaussianReal 0 1) (-0.224) ∧
      cdf (gaussianReal 0 1) 0.224 - cdf (gaussianReal 0 1) (-0.224) < 0.1773 := by
  obtain ⟨a1, a2⟩ := stdNormal_cdf_224
  rw [stdNormal_interval]
  constructor <;> linarith

/-- Grinstead–Snell Example 9.10 (PR-206), the normal value. The surveyor's estimate is
`NA(-3, 3) = (2π)^{-1/2} ∫_{-3}^{3} e^{-x²/2} dx = Φ(3) - Φ(-3)`, which lies in `(.9972, .9974)`
(book: `.997`). -/
@[kb "grinsteadsnell2006" "Example 9.10, p. 367"]
theorem surveyor_normal_value :
    0.9972 < cdf (gaussianReal 0 1) 3 - cdf (gaussianReal 0 1) (-3) ∧
      cdf (gaussianReal 0 1) 3 - cdf (gaussianReal 0 1) (-3) < 0.9974 := by
  obtain ⟨a1, a2⟩ := stdNormal_cdf_three
  rw [stdNormal_interval]
  constructor <;> linarith

end BookValues

end UndergradKB.Probability
