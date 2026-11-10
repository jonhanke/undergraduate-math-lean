import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import UndergradKB.Common.Attr

/-! # Calculus: the Laplace transform

OpenStax Calculus 2, §3.7 Student Project: the Laplace transform of a function on `[0, ∞)`, and its behaviour on
derivatives and on integrals. -/

open Real Set Filter Topology MeasureTheory

namespace UndergradKB.Calculus

/-- OpenStax Calculus 2:§3.7 Student Project (CA-246). The Laplace transform
`F(s) = ∫_0^∞ e^{-st} f(t) dt` of `f`, as a Lebesgue integral over `(0, ∞)`
(Mathlib has no Laplace transform; the book's improper integral is this integral whenever it converges). -/
@[kb "openstaxcalculus2016" "2:§3.7 Student Project (Laplace transform definition), p. 306"]
noncomputable def laplace(f : ℝ → ℝ) (s : ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), Real.exp (-s * t) * f t

/-- The integrand of a Laplace transform is integrable when `f` is continuous on `[0, ∞)` and of exponential
order `a < s`. -/
theorem laplace_integrableOn {f : ℝ → ℝ} {M a s : ℝ} (hc : ContinuousOn f (Ici 0))
    (hb : ∀ t, 0 ≤ t → |f t| ≤ M * Real.exp (a * t)) (has : a < s) :
    IntegrableOn (fun t => Real.exp (-s * t) * f t) (Ioi 0) := by
  have hg : IntegrableOn (fun t : ℝ => M * Real.exp (-(s - a) * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul M
  refine Integrable.mono' hg ?_ ?_
  · have : ContinuousOn (fun t => Real.exp (-s * t) * f t) (Ioi 0) :=
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul
        (hc.mono Ioi_subset_Ici_self)
    exact this.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := le_of_lt ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-s * t) * |f t| ≤ Real.exp (-s * t) * (M * Real.exp (a * t)) :=
          mul_le_mul_of_nonneg_left (hb t ht0) (Real.exp_pos _).le
      _ = M * Real.exp (-(s - a) * t) := by
          rw [← mul_assoc, mul_comm (Real.exp _) M, mul_assoc, ← Real.exp_add]
          ring_nf

/-- The integrand of a Laplace transform tends to `0` at infinity for `f` of exponential order `a < s`. -/
theorem laplace_integrand_tendsto {f : ℝ → ℝ} {M a s : ℝ}
    (hb : ∀ t, 0 ≤ t → |f t| ≤ M * Real.exp (a * t)) (has : a < s) :
    Tendsto (fun t => Real.exp (-s * t) * f t) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => M * Real.exp (-(s - a) * t)) atTop (𝓝 (M * 0)) :=
    (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by linarith : -(s - a) < 0))).const_mul M
  rw [mul_zero] at h1
  have h2 : Tendsto (fun t : ℝ => -(M * Real.exp (-(s - a) * t))) atTop (𝓝 (-0)) := h1.neg
  rw [neg_zero] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h2 h1 ?_ ?_
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have := (abs_le.1 (hb t ht))
    have h3 : Real.exp (-s * t) * (-(M * Real.exp (a * t))) ≤ Real.exp (-s * t) * f t :=
      mul_le_mul_of_nonneg_left this.1 (Real.exp_pos _).le
    have h4 : Real.exp (-s * t) * (-(M * Real.exp (a * t))) = -(M * Real.exp (-(s - a) * t)) := by
      rw [mul_neg, ← mul_assoc, mul_comm (Real.exp _) M, mul_assoc, ← Real.exp_add]
      ring_nf
    linarith
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have := (abs_le.1 (hb t ht))
    have h3 : Real.exp (-s * t) * f t ≤ Real.exp (-s * t) * (M * Real.exp (a * t)) :=
      mul_le_mul_of_nonneg_left this.2 (Real.exp_pos _).le
    have h4 : Real.exp (-s * t) * (M * Real.exp (a * t)) = M * Real.exp (-(s - a) * t) := by
      rw [← mul_assoc, mul_comm (Real.exp _) M, mul_assoc, ← Real.exp_add]
      ring_nf
    linarith

/-- OpenStax Calculus 2:§3.7 Student Project (CA-247): `L{f'}(s) = s L{f}(s) - f(0)`. Hypotheses as in the book:
`f` has the continuous derivative `f'` on `[0, ∞)`, both of exponential order `a`, and `s > a`. -/
@[kb "openstaxcalculus2016" "2:§3.7 Student Project (transform of a derivative), p. 307"]
theorem laplace_deriv {f f' : ℝ → ℝ} {M M' a s : ℝ}
    (hf : ∀ t, 0 ≤ t → HasDerivAt f (f' t) t) (hf'c : ContinuousOn f' (Ici 0))
    (hb : ∀ t, 0 ≤ t → |f t| ≤ M * Real.exp (a * t))
    (hb' : ∀ t, 0 ≤ t → |f' t| ≤ M' * Real.exp (a * t)) (has : a < s) :
    laplace f' s = s * laplace f s - f 0 := by
  have hfc : ContinuousOn f (Ici 0) := fun t ht => (hf t ht).continuousAt.continuousWithinAt
  have i1 := laplace_integrableOn hfc hb has
  have i2 := laplace_integrableOn hf'c hb' has
  have hg : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun t => Real.exp (-s * t) * f t)
        (Real.exp (-s * t) * f' t - s * (Real.exp (-s * t) * f t)) t := by
    intro t ht
    have e : HasDerivAt (fun t => Real.exp (-s * t)) (Real.exp (-s * t) * (-s)) t :=
      (((hasDerivAt_id t).const_mul (-s)).exp).congr_deriv (by simp)
    have := e.mul (hf t ht)
    convert this using 1
    ring
  have := integral_Ioi_of_hasDerivAt_of_tendsto' hg ((i2.sub (i1.const_mul s)))
    (laplace_integrand_tendsto hb has)
  rw [integral_sub i2 (i1.const_mul s), integral_const_mul] at this
  simp only [mul_zero, Real.exp_zero, one_mul, zero_sub] at this
  unfold laplace
  linarith

/-- OpenStax Calculus 2:§3.7 Student Project (CA-248): the transform of the antiderivative
`g t = ∫_0^t f` (which vanishes at `0`) is `L{f}(s) / s`, for `f` continuous of exponential order `a < s`
and `s > 0`. -/
@[kb "openstaxcalculus2016" "2:§3.7 Student Project (transform of an integral), p. 307"]
theorem laplace_integral {f : ℝ → ℝ} {M a s : ℝ} (hc : Continuous f)
    (hb : ∀ t, 0 ≤ t → |f t| ≤ M * Real.exp (a * t)) (hs : 0 < s) (has : a < s) :
    laplace (fun t => ∫ u in (0 : ℝ)..t, f u) s = laplace f s / s := by
  set a' := max a (s / 2) with ha'
  have ha'pos : 0 < a' := lt_max_of_lt_right (by linarith)
  have ha's : a' < s := max_lt has (by linarith)
  have hM : 0 ≤ M := by
    have := hb 0 le_rfl
    simp only [mul_zero, Real.exp_zero, mul_one] at this
    exact (abs_nonneg _).trans this
  have hb2 : ∀ t, 0 ≤ t → |f t| ≤ M * Real.exp (a' * t) := fun t ht =>
    (hb t ht).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_left _ _) ht)) hM)
  have hint : ∀ t, 0 ≤ t → (∫ u in (0 : ℝ)..t, M * Real.exp (a' * u)) = M / a' * (Real.exp (a' * t) - 1) := by
    intro t ht
    have hF : ∀ u ∈ uIcc (0 : ℝ) t, HasDerivAt (fun u => M / a' * Real.exp (a' * u))
        (M * Real.exp (a' * u)) u := by
      intro u _
      have e : HasDerivAt (fun u => Real.exp (a' * u)) (Real.exp (a' * u) * a') u :=
        (((hasDerivAt_id u).const_mul a').exp).congr_deriv (by simp)
      refine (e.const_mul (M / a')).congr_deriv ?_
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
      ((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _)]
    simp only [mul_zero, Real.exp_zero]
    ring
  have hgb : ∀ t, 0 ≤ t → |∫ u in (0 : ℝ)..t, f u| ≤ M / a' * Real.exp (a' * t) := by
    intro t ht
    have h1 := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (f := f)
      (g := fun u => M * Real.exp (a' * u)) ht
      (Filter.Eventually.of_forall fun u hu => by
        rw [Real.norm_eq_abs]; exact hb2 u hu.1.le)
      ((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _)
    rw [hint t ht, Real.norm_eq_abs] at h1
    refine h1.trans ?_
    have : 0 ≤ M / a' := div_nonneg hM ha'pos.le
    nlinarith
  have hder : ∀ t, 0 ≤ t → HasDerivAt (fun t => ∫ u in (0 : ℝ)..t, f u) (f t) t :=
    fun t _ => (hc.integral_hasStrictDerivAt 0 t).hasDerivAt
  have key := laplace_deriv (f := fun t => ∫ u in (0 : ℝ)..t, f u) (f' := f) hder hc.continuousOn hgb hb2 ha's
  simp only [intervalIntegral.integral_same, sub_zero] at key
  field_simp
  linarith

end UndergradKB.Calculus
