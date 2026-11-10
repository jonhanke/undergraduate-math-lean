import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import UndergradKB.Common.Attr

namespace UndergradKB.Calculus

open Filter Finset Topology FormalMultilinearSeries
open scoped ENNReal NNReal Nat

/-! ## Taylor series -/

/-- The `n`th term `f⁽ⁿ⁾(a) (x - a)ⁿ / n!` of the Taylor series of `f` at `a` (the Maclaurin series for `a = 0`).
This is the book's notion of the Taylor series of a real function with derivatives of all orders. -/
noncomputable def taylorSeriesTerm (f : ℝ → ℝ) (a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  iteratedDeriv n f a / n ! * (x - a) ^ n

/-- The remainder `R_n(x) = f x - p_n(x)` of the `n`th Taylor polynomial of `f` at `a` (the book's notion). -/
noncomputable def taylorRemainder (f : ℝ → ℝ) (a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  f x - taylorWithinEval f n Set.univ a x

/-- OpenStax Calculus 2:§6.3 (CA-373, CA-375). The `n`th Taylor polynomial of `f` at `a` is the partial sum of
the Taylor series: `taylorWithinEval f n univ a x = ∑_{k ≤ n} f⁽ᵏ⁾(a) (x - a)ᵏ / k!`. -/
@[kb "openstaxcalculus2016" "2:§6.3 Definition (Taylor and Maclaurin series), p. 506"]
theorem taylorWithinEval_univ_eq_sum_taylorSeriesTerm (f : ℝ → ℝ) (a x : ℝ) (n : ℕ) :
    taylorWithinEval f n Set.univ a x = ∑ k ∈ range (n + 1), taylorSeriesTerm f a k x := by
  rw [taylor_within_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [iteratedDerivWithin_univ, smul_eq_mul, taylorSeriesTerm]
  ring

/-- OpenStax Calculus 2:§6.3 (CA-373). The Maclaurin series is the Taylor series at `a = 0`:
the terms are `f⁽ⁿ⁾(0) xⁿ / n!`. -/
@[kb "openstaxcalculus2016" "2:§6.3 Definition (Taylor and Maclaurin series), p. 506"]
theorem taylorSeriesTerm_zero (f : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    taylorSeriesTerm f 0 n x = iteratedDeriv n f 0 / n ! * x ^ n := by
  simp [taylorSeriesTerm]

/-- OpenStax Calculus 2:Theorem 6.6 and §6.3 (CA-373, CA-374). If `f` is analytic at `a`, then the formal
power series with coefficients `f⁽ⁿ⁾(a)/n!` represents `f` near `a`: the Taylor series is the power series of `f`. -/
@[kb "openstaxcalculus2016" "2:Theorem 6.6, p. 506"]
theorem hasFPowerSeriesAt_taylorSeries {f : ℝ → ℝ} {a : ℝ} (h : AnalyticAt ℝ f a) :
    HasFPowerSeriesAt f (ofScalars ℝ (fun n => iteratedDeriv n f a / n !)) a :=
  h.hasFPowerSeriesAt

/-- OpenStax Calculus 2:Theorem 6.8 (CA-378). The Taylor series of `f` at `a` converges to `f x` (its partial
sums `∑_{k<n} f⁽ᵏ⁾(a)(x-a)ᵏ/k!` tend to `f x`) if and only if the remainders `R_n(x)` of the Taylor
polynomials tend to `0`. -/
@[kb "openstaxcalculus2016" "2:Theorem 6.8, p. 516"]
theorem taylor_series_converges_iff_remainder_tendsto_zero (f : ℝ → ℝ) (a x : ℝ) :
    Tendsto (fun n => ∑ k ∈ range n, taylorSeriesTerm f a k x) atTop (𝓝 (f x)) ↔
      Tendsto (fun n => taylorRemainder f a n x) atTop (𝓝 0) := by
  have h1 : ∀ n, taylorRemainder f a n x = f x - ∑ k ∈ range (n + 1), taylorSeriesTerm f a k x := fun n => by
    rw [taylorRemainder, taylorWithinEval_univ_eq_sum_taylorSeriesTerm]
  simp_rw [h1]
  rw [← tendsto_add_atTop_iff_nat 1 (f := fun n => ∑ k ∈ range n, taylorSeriesTerm f a k x)]
  constructor
  · intro h
    simpa using (tendsto_const_nhds (x := f x)).sub h
  · intro h
    simpa using (tendsto_const_nhds (x := f x)).sub h

/-- OpenStax Calculus 2:Example 6.15 (CA-377). The Taylor series of `1/x` at `a = 1` has terms `(-1)ⁿ (x-1)ⁿ`:
the coefficients `f⁽ⁿ⁾(1)/n!` equal `(-1)ⁿ`. -/
@[kb "openstaxcalculus2016" "2:Example 6.15, p. 515"]
theorem taylorSeriesTerm_inv_at_one (n : ℕ) (x : ℝ) :
    taylorSeriesTerm (fun t : ℝ => 1 / t) 1 n x = (-1) ^ n * (x - 1) ^ n := by
  have : iteratedDeriv n (fun t : ℝ => 1 / t) 1 = (-1) ^ n * n ! := by
    rw [iteratedDeriv_eq_iterate]
    simp
  rw [taylorSeriesTerm, this]
  have : (n ! : ℝ) ≠ 0 := by positivity
  field_simp

/-- OpenStax Calculus 2:Example 6.15 (CA-377). For `0 < x < 2`, `1/x = ∑ (-1)ⁿ (x-1)ⁿ`; for `x ≤ 0` or `x ≥ 2`
the terms do not tend to `0`, so the partial sums have no limit. Hence the series converges exactly on `(0,2)`
and there it converges to `1/x`. -/
@[kb "openstaxcalculus2016" "2:Example 6.15, p. 515"]
theorem inv_taylor_series_at_one :
    (∀ x ∈ Set.Ioo (0 : ℝ) 2,
      HasSum (fun n : ℕ => (-1 : ℝ) ^ n * (x - 1) ^ n) (1 / x)) ∧
    (∀ x : ℝ, x ∉ Set.Ioo (0 : ℝ) 2 →
      ¬ Tendsto (fun n : ℕ => (-1 : ℝ) ^ n * (x - 1) ^ n) atTop (𝓝 0)) := by
  constructor
  · intro x hx
    have h := hasSum_geometric_of_abs_lt_one (r := 1 - x) (by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2])
    have hx0 : x ≠ 0 := hx.1.ne'
    have e : (1 - (1 - x))⁻¹ = 1 / x := by rw [sub_sub_cancel, one_div]
    rw [e] at h
    have : (fun n : ℕ => (-1 : ℝ) ^ n * (x - 1) ^ n) = fun n => (1 - x) ^ n := by
      funext n
      rw [← mul_pow]
      congr 1
      ring
    rw [this]
    exact h
  · intro x hx h0
    have h1 : 1 ≤ |x - 1| := by
      by_contra hlt
      rw [not_le, abs_lt] at hlt
      exact hx ⟨by linarith, by linarith⟩
    have h2 := (continuous_abs.tendsto 0).comp h0
    rw [abs_zero] at h2
    have key : ∀ n : ℕ, 1 ≤ |(-1 : ℝ) ^ n * (x - 1) ^ n| := fun n => by
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow]
      exact one_le_pow₀ h1
    have h3 := ge_of_tendsto h2 (Eventually.of_forall key)
    linarith

end UndergradKB.Calculus
