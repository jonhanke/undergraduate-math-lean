import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.RingTheory.Binomial
import UndergradKB.Common.Attr
import UndergradKB.Calculus.PowerSeries
import UndergradKB.Calculus.PowerSeriesAlgebra
import UndergradKB.Calculus.PowerSeriesDeriv
import UndergradKB.Calculus.AlternatingSeries
import UndergradKB.Calculus.SeriesArctanExp
import UndergradKB.Calculus.TaylorSeries

/-!
# OpenStax Calculus Volume 2, Chapter 6 (power series): course layer

Thin wrappers around Mathlib. A real power series `∑ c n (x - a)^n` is written with explicit
`HasSum` statements; where Mathlib's `FormalMultilinearSeries.ofScalars ℝ c` (the series with
coefficients `c`) is needed, it is used with its `radius`.
-/

namespace UndergradKB.Calculus.Course.V2C6

open Filter Topology Set FormalMultilinearSeries

/-- Auxiliary: a real power series `∑ c n (x - a)^n` that converges to `f x` for all `x` with
`|x - a| < ε` is a `HasFPowerSeriesOnBall` of radius `ε` around `a`. -/
theorem hasFPowerSeriesOnBall_of_hasSum {f : ℝ → ℝ} {a ε : ℝ} (hε : 0 < ε) (c : ℕ → ℝ)
    (h : ∀ x ∈ Ioo (a - ε) (a + ε), HasSum (fun n => c n * (x - a) ^ n) (f x)) :
    HasFPowerSeriesOnBall f (ofScalars ℝ c) a (ENNReal.ofReal ε) where
  r_le := by
    refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    have hr' : (r : ℝ) < ε := by
      simpa using (ENNReal.lt_ofReal_iff_toReal_lt (by simp)).mp hr
    have hmem : a + r ∈ Ioo (a - ε) (a + ε) := ⟨by linarith [r.coe_nonneg], by linarith⟩
    have h0 := (h _ hmem).summable.tendsto_atTop_zero
    simp only [add_sub_cancel_left] at h0
    refine le_radius_of_tendsto (ofScalars ℝ c) (l := 0) ?_
    have := tendsto_norm_zero.comp h0
    refine this.congr fun n => ?_
    simp
  r_pos := by simpa using hε
  hasSum := by
    intro y hy
    have hy' : |y| < ε := by
      simpa [Metric.mem_eball, edist_dist, Real.dist_eq, ENNReal.ofReal_lt_ofReal_iff hε] using hy
    have := h (a + y) ⟨by linarith [(abs_lt.mp hy').1], by linarith [(abs_lt.mp hy').2]⟩
    simpa [ofScalars_apply_eq, mul_comm] using this

/-- OpenStax Calculus 2:§6.1 Definition (interval and radius of convergence) (CA-362).
Let `R` be the radius of convergence of `∑ c n (x - a)^n`. Inside the radius (`|x - a| < R`) the
series converges (even absolutely), and outside (`R < |x - a|`) it diverges. -/
@[kb "openstaxcalculus2016" "2:§6.1 Definition (interval and radius of convergence), p. 480"]
theorem radius_of_convergence (c : ℕ → ℝ) (a x : ℝ) :
    (ENNReal.ofReal |x - a| < (ofScalars ℝ c).radius →
        Summable fun n => |c n * (x - a) ^ n|) ∧
      ((ofScalars ℝ c).radius < ENNReal.ofReal |x - a| →
        ¬ Summable fun n => c n * (x - a) ^ n) := by
  constructor
  · intro h
    have hx : (x - a) ∈ Metric.eball (0 : ℝ) (ofScalars ℝ c).radius := by
      simpa [Metric.mem_eball, edist_dist, Real.dist_eq] using h
    simpa [ofScalars_apply_eq, Real.norm_eq_abs, mul_comm] using
      (ofScalars ℝ c).summable_norm_apply hx
  · intro h hs
    have h0 := hs.tendsto_atTop_zero
    have : ((‖x - a‖₊ : NNReal) : ENNReal) ≤ (ofScalars ℝ c).radius := by
      refine le_radius_of_tendsto (ofScalars ℝ c) (l := 0) ?_
      refine (tendsto_norm_zero.comp h0).congr fun n => ?_
      simp
    have h2 : ((‖x - a‖₊ : NNReal) : ENNReal) = ENNReal.ofReal |x - a| := by
      rw [← Real.norm_eq_abs, ofReal_norm]; rfl
    rw [h2] at this
    exact absurd h (not_lt.mpr this)

/-- OpenStax Calculus 2:Example 6.1 (CA-363), ratio test for the radius, finite nonzero limit.
If `|c n / c (n+1)| → L` with `L ≠ 0` then the radius of convergence is `L`. -/
@[kb "openstaxcalculus2016" "2:Example 6.1, p. 481"]
theorem radius_eq_of_ratio_tendsto (c : ℕ → ℝ) {L : NNReal} (hL : L ≠ 0)
    (h : Tendsto (fun n => ‖c n‖ / ‖c (n + 1)‖) atTop (𝓝 (L : ℝ))) :
    (ofScalars ℝ c).radius = L :=
  ofScalars_radius_eq_of_tendsto ℝ c hL h

/-- OpenStax Calculus 2:Example 6.1 (CA-363), ratio test for the radius, infinite radius.
If the coefficients are eventually nonzero and `|c (n+1) / c n| → 0` then the radius is `∞`. -/
@[kb "openstaxcalculus2016" "2:Example 6.1, p. 481"]
theorem radius_eq_top_of_ratio_tendsto_zero (c : ℕ → ℝ) (hc : ∀ᶠ n in atTop, c n ≠ 0)
    (h : Tendsto (fun n => ‖c (n + 1)‖ / ‖c n‖) atTop (𝓝 0)) :
    (ofScalars ℝ c).radius = ⊤ :=
  ofScalars_radius_eq_top_of_tendsto ℝ c hc h

/-- OpenStax Calculus 2:Example 6.1 (CA-363), ratio test for the radius, radius zero.
If `|c (n+1) / c n| → ∞` then the radius is `0`. -/
@[kb "openstaxcalculus2016" "2:Example 6.1, p. 481"]
theorem radius_eq_zero_of_ratio_tendsto_atTop (c : ℕ → ℝ)
    (h : Tendsto (fun n => ‖c (n + 1)‖ / ‖c n‖) atTop atTop) :
    (ofScalars ℝ c).radius = 0 :=
  ofScalars_radius_eq_zero_of_tendsto ℝ c h

/-- OpenStax Calculus 2:§6.1 Geometric series as power series (6.3) (CA-364).
`1 / (1 - x) = ∑ x ^ n` for `|x| < 1`. -/
@[kb "openstaxcalculus2016" "2:§6.1 Geometric series as power series (6.3), p. 483"]
theorem geometric_power_series (x : ℝ) (hx : |x| < 1) :
    HasSum (fun n : ℕ => x ^ n) (1 / (1 - x)) := by
  simpa [one_div] using hasSum_geometric_of_abs_lt_one hx

/-- OpenStax Calculus 2:§6.1 Geometric series as power series (6.3) (CA-364).
The geometric series `∑ x ^ n` diverges for `|x| ≥ 1`. -/
@[kb "openstaxcalculus2016" "2:§6.1 Geometric series as power series (6.3), p. 483"]
theorem geometric_power_series_diverges (x : ℝ) (hx : 1 ≤ |x|) :
    ¬ Summable (fun n : ℕ => x ^ n) := by
  intro h
  have := summable_geometric_iff_norm_lt_one.mp h
  rw [Real.norm_eq_abs] at this
  linarith

/-- OpenStax Calculus 2:§6.1 Geometric series as power series (6.3) (CA-364).
`x ↦ 1 / (1 - x)` is represented by the geometric power series on the ball of radius `1`. -/
@[kb "openstaxcalculus2016" "2:§6.1 Geometric series as power series (6.3), p. 483"]
theorem one_div_one_sub_hasFPowerSeriesOnBall :
    HasFPowerSeriesOnBall (fun x : ℝ => 1 / (1 - x)) (ofScalars (𝕜 := ℝ) ℝ 1) 0 1 :=
  Real.one_div_one_sub_hasFPowerSeriesOnBall_zero

/-- OpenStax Calculus 2:Example 6.8 (CA-367).
`1 / (1 - x)^2 = ∑ (n + 1) x ^ n` for `|x| < 1`. -/
@[kb "openstaxcalculus2016" "2:Example 6.8, p. 496"]
theorem one_div_one_sub_sq_power_series (x : ℝ) (hx : |x| < 1) :
    HasSum (fun n : ℕ => ((n : ℝ) + 1) * x ^ n) (1 / (1 - x) ^ 2) := by
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one (r := x) (by rwa [Real.norm_eq_abs])
  have h2 := hasSum_geometric_of_abs_lt_one hx
  have h3 := h1.add h2
  have hne : (1 - x) ≠ 0 := by
    have := (abs_lt.mp hx).2
    linarith
  convert h3 using 1
  · funext n; ring
  · field_simp
    ring

/-- OpenStax Calculus 2:Example 6.8 (CA-367).
`∑ n x ^ n = x / (1 - x)^2` for `|x| < 1`. -/
@[kb "openstaxcalculus2016" "2:Example 6.8, p. 496"]
theorem sum_n_mul_geometric (x : ℝ) (hx : |x| < 1) :
    HasSum (fun n : ℕ => (n : ℝ) * x ^ n) (x / (1 - x) ^ 2) :=
  hasSum_coe_mul_geometric_of_norm_lt_one (by rwa [Real.norm_eq_abs])

/-- OpenStax Calculus 2:Example 6.9 (CA-367).
`∑ n / 2 ^ n = 2`. -/
@[kb "openstaxcalculus2016" "2:Example 6.9, p. 498"]
theorem sum_n_div_two_pow : HasSum (fun n : ℕ => (n : ℝ) / 2 ^ n) 2 := by
  have h := sum_n_mul_geometric (1 / 2) (by norm_num [abs_of_pos])
  convert h using 1
  · funext n; simp [div_eq_mul_inv]
  · norm_num

/-- OpenStax Calculus 2:§6.2 Abel's theorem (mentioned) (CA-371).
If `∑ f n` converges to `l`, then `∑ f n x ^ n → l` as `x → 1` from the left. -/
@[kb "openstaxcalculus2016" "2:§6.2 Abel's theorem (mentioned), p. 500"]
theorem abel_limit_theorem {f : ℕ → ℝ} {l : ℝ}
    (h : Tendsto (fun n => ∑ i ∈ Finset.range n, f i) atTop (𝓝 l)) :
    Tendsto (fun x : ℝ => ∑' n, f n * x ^ n) (𝓝[<] 1) (𝓝 l) :=
  Real.tendsto_tsum_powerSeries_nhdsWithin_lt h

/-- OpenStax Calculus 2:Theorem 6.5 (CA-372).
If two power series `∑ c n (x-a)^n` and `∑ d n (x-a)^n` converge to the same function `f` on an
open interval around `a`, then `c n = d n` for all `n`. -/
@[kb "openstaxcalculus2016" "2:Theorem 6.5, p. 500"]
theorem power_series_coefficients_unique {f : ℝ → ℝ} {a ε : ℝ} (hε : 0 < ε) (c d : ℕ → ℝ)
    (hc : ∀ x ∈ Ioo (a - ε) (a + ε), HasSum (fun n => c n * (x - a) ^ n) (f x))
    (hd : ∀ x ∈ Ioo (a - ε) (a + ε), HasSum (fun n => d n * (x - a) ^ n) (f x)) : c = d :=
  ofScalars_series_injective ℝ ℝ
    ((hasFPowerSeriesOnBall_of_hasSum hε c hc).hasFPowerSeriesAt.eq_formalMultilinearSeries
      (hasFPowerSeriesOnBall_of_hasSum hε d hd).hasFPowerSeriesAt)

/-- Auxiliary: the coefficients of a scalar power series representing `f` on a ball around `a` are
the Taylor coefficients `f^(n)(a) / n!`. -/
theorem coeff_eq_iteratedDeriv_div_factorial {f : ℝ → ℝ} {a : ℝ} {R : ENNReal} {c : ℕ → ℝ}
    (h : HasFPowerSeriesOnBall f (ofScalars ℝ c) a R) (n : ℕ) :
    c n = iteratedDeriv n f a / n.factorial := by
  have h1 := h.factorial_smul (y := 1) n
  simp only [ofScalars_apply_eq, one_pow, smul_eq_mul, mul_one, nsmul_eq_mul] at h1
  rw [iteratedDeriv_eq_iteratedFDeriv]
  have h' : (n.factorial : ℝ) * c n = iteratedFDeriv ℝ n f a fun _ => 1 := by simpa using h1
  rw [← h']
  field_simp

/-- OpenStax Calculus 2:Theorem 6.6 (CA-374).
If `f x = ∑ c n (x-a)^n` for `|x - a| < ε`, the series is the Taylor series of `f` at `a`:
`c n = f^(n)(a) / n!`. -/
@[kb "openstaxcalculus2016" "2:Theorem 6.6, p. 506"]
theorem power_series_is_taylor_series {f : ℝ → ℝ} {a ε : ℝ} (hε : 0 < ε) (c : ℕ → ℝ)
    (hc : ∀ x ∈ Ioo (a - ε) (a + ε), HasSum (fun n => c n * (x - a) ^ n) (f x)) (n : ℕ) :
    c n = iteratedDeriv n f a / n.factorial :=
  coeff_eq_iteratedDeriv_div_factorial (hasFPowerSeriesOnBall_of_hasSum hε c hc) n

/-- OpenStax Calculus 2:§6.3 Definition (Taylor and Maclaurin polynomials) (CA-375).
The `n`th Taylor polynomial of `f` at `a` is `∑_{k ≤ n} f^(k)(a) (x-a)^k / k!`
(Mathlib's `taylorWithinEval` relative to the whole line). -/
@[kb "openstaxcalculus2016" "2:§6.3 Definition (Taylor and Maclaurin polynomials), p. 507"]
theorem taylor_polynomial_formula (f : ℝ → ℝ) (n : ℕ) (a x : ℝ) :
    taylorWithinEval f n univ a x =
      ∑ k ∈ Finset.range (n + 1), iteratedDeriv k f a * (x - a) ^ k / k.factorial := by
  rw [taylor_within_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [iteratedDerivWithin_univ, smul_eq_mul]
  field_simp

/-- Auxiliary: the Taylor polynomial over the closed interval between `a` and `x` agrees with the
one built from ordinary derivatives when `f` is `C^n` on an open interval containing both points. -/
theorem taylorWithinEval_uIcc_eq {f : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I)
    {a x : ℝ} (ha : a ∈ I) (hne : a ≠ x) (n : ℕ) (hf : ContDiffOn ℝ (n + 1) f I) :
    taylorWithinEval f n (uIcc a x) a x =
      ∑ k ∈ Finset.range (n + 1), iteratedDeriv k f a * (x - a) ^ k / k.factorial := by
  rw [taylor_within_apply]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hca : ContDiffAt ℝ k f a :=
    ((hf.contDiffAt (hI.mem_nhds ha)).of_le (by exact_mod_cast hk'.trans (Nat.le_succ n)))
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hne) hca left_mem_uIcc, smul_eq_mul]
  field_simp

/-- OpenStax Calculus 2:Theorem 6.7 (CA-376), Taylor's theorem with remainder.
If `f` is `n+1` times continuously differentiable on an open interval `I` containing `a ≠ x`, then
`f x - p_n x = f^(n+1)(c) (x - a)^(n+1) / (n+1)!` for some `c` strictly between `a` and `x`. -/
@[kb "openstaxcalculus2016" "2:Theorem 6.7, p. 511"]
theorem taylor_theorem_lagrange_remainder {f : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I)
    (hord : I.OrdConnected) {a x : ℝ} (ha : a ∈ I) (hx : x ∈ I) (hne : a ≠ x) (n : ℕ)
    (hf : ContDiffOn ℝ (n + 1) f I) :
    ∃ c ∈ uIoo a x, f x - ∑ k ∈ Finset.range (n + 1), iteratedDeriv k f a * (x - a) ^ k / k.factorial
      = iteratedDeriv (n + 1) f c * (x - a) ^ (n + 1) / (n + 1).factorial := by
  obtain ⟨c, hc, h⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hne
    (hf.mono (hord.uIcc_subset ha hx))
  exact ⟨c, hc, by rw [← taylorWithinEval_uIcc_eq hI ha hne n hf]; exact h⟩

/-- OpenStax Calculus 2:Theorem 6.7 (CA-376), bound on the remainder.
If `|f^(n+1)| ≤ M` on `I`, then `|f x - p_n x| ≤ M |x - a|^(n+1) / (n+1)!`. -/
@[kb "openstaxcalculus2016" "2:§6.3 Definition (remainder R_n), p. 510"]
theorem taylor_remainder_bound {f : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I)
    (hord : I.OrdConnected) {a x : ℝ} (ha : a ∈ I) (hx : x ∈ I) (hne : a ≠ x) (n : ℕ)
    (hf : ContDiffOn ℝ (n + 1) f I) {M : ℝ} (hM : ∀ y ∈ I, |iteratedDeriv (n + 1) f y| ≤ M) :
    |f x - ∑ k ∈ Finset.range (n + 1), iteratedDeriv k f a * (x - a) ^ k / k.factorial| ≤
      M * |x - a| ^ (n + 1) / (n + 1).factorial := by
  obtain ⟨c, hc, h⟩ := taylor_theorem_lagrange_remainder hI hord ha hx hne n hf
  rw [h, abs_div, abs_mul, abs_pow, Nat.abs_cast]
  have hcI : c ∈ I := hord.uIcc_subset ha hx (Ioo_subset_Icc_self hc)
  gcongr
  exact hM c hcI

/-- OpenStax Calculus 2:Example 6.12 (part a) (CA-379).
`exp x = ∑ x ^ n / n!` for all real `x`. -/
@[kb "openstaxcalculus2016" "2:Example 6.12 (part a), p. 508"]
theorem exp_power_series (x : ℝ) :
    HasSum (fun n : ℕ => x ^ n / n.factorial) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp x

/-- OpenStax Calculus 2:Example 6.12 (part b) (CA-380).
`sin x = ∑ (-1)^n x^(2n+1) / (2n+1)!` for all real `x`. -/
@[kb "openstaxcalculus2016" "2:Example 6.12 (part b), p. 508"]
theorem sin_power_series (x : ℝ) :
    HasSum (fun n : ℕ => (-1) ^ n * x ^ (2 * n + 1) / (2 * n + 1).factorial) (Real.sin x) :=
  Real.hasSum_sin x

/-- OpenStax Calculus 2:Example 6.12 (part c) (CA-381).
`cos x = ∑ (-1)^n x^(2n) / (2n)!` for all real `x`. -/
@[kb "openstaxcalculus2016" "2:Example 6.12 (part c), p. 508"]
theorem cos_power_series (x : ℝ) :
    HasSum (fun n : ℕ => (-1) ^ n * x ^ (2 * n) / (2 * n).factorial) (Real.cos x) :=
  Real.hasSum_cos x

/-- OpenStax Calculus 2:§6.4 Binomial expansion (6.6)-(6.7) (CA-383).
For a natural number `r`, `(1 + x)^r = ∑_{k ≤ r} C(r, k) x^k`. -/
@[kb "openstaxcalculus2016" "2:§6.4 Binomial expansion and binomial coefficients (6.6)-(6.7), p. 521"]
theorem binomial_expansion (x : ℝ) (r : ℕ) :
    (1 + x) ^ r = ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) * x ^ k := by
  rw [add_comm, add_pow]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [mul_comm]

/-- OpenStax Calculus 2:§6.4 Binomial coefficient for real exponent (6.8) (CA-384).
The binomial coefficient of a real `r` is `r (r-1) ⋯ (r-n+1) / n!`. -/
@[kb "openstaxcalculus2016" "2:§6.4 Binomial coefficient for real exponent (6.8), p. 522"]
theorem binomial_coefficient_real_formula (r : ℝ) (n : ℕ) :
    Ring.choose r n = (∏ i ∈ Finset.range n, (r - i)) / n.factorial := by
  rw [Ring.choose_eq_smul, ← descPochhammer_eval_eq_prod_range]
  have : (descPochhammer ℤ n).smeval r = (descPochhammer ℝ n).eval r := by
    rw [← Polynomial.aeval_eq_smeval, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
      descPochhammer_map]
  rw [this, smul_eq_mul]
  field_simp

/-- OpenStax Calculus 2:§6.4 Binomial coefficient for real exponent (6.8) (CA-384).
For a natural exponent the real binomial coefficient is the usual `Nat.choose`. -/
@[kb "openstaxcalculus2016" "2:§6.4 Binomial coefficient for real exponent (6.8), p. 522"]
theorem binomial_coefficient_natCast (n k : ℕ) : Ring.choose (n : ℝ) k = (n.choose k : ℝ) :=
  Ring.choose_natCast n k

/-- OpenStax Calculus 2:§6.4 Binomial coefficient for real exponent (6.8) (CA-384).
The binomial coefficients are the Taylor coefficients of `(1 + x)^r` at `0`:
`Ring.choose r n = f^(n)(0) / n!` for `f x = (1 + x)^r`. -/
@[kb "openstaxcalculus2016" "2:§6.4 Binomial coefficient for real exponent (6.8), p. 522"]
theorem binomial_coefficient_eq_taylor_coefficient (r : ℝ) (n : ℕ) :
    Ring.choose r n = iteratedDeriv n (fun x : ℝ => (1 + x) ^ r) 0 / n.factorial :=
  coeff_eq_iteratedDeriv_div_factorial (c := fun n => Ring.choose r n)
    Real.one_add_rpow_hasFPowerSeriesOnBall_zero n

/-- OpenStax Calculus 2:§6.4 Definition (binomial series) (CA-385).
For `|x| < 1`, `∑ C(r, n) x^n = (1 + x)^r`. -/
@[kb "openstaxcalculus2016" "2:§6.4 Definition (binomial series), p. 522"]
theorem binomial_series_sum (r x : ℝ) (hx : |x| < 1) :
    HasSum (fun n : ℕ => Ring.choose r n * x ^ n) ((1 + x) ^ r) := by
  have h := Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := r)
  have hy : x ∈ Metric.eball (0 : ℝ) 1 := by
    simpa [Metric.mem_eball, edist_dist, Real.dist_eq] using hx
  simpa [binomialSeries, mul_comm] using h.hasSum hy

/-- OpenStax Calculus 2:§6.4 Definition (binomial series) (CA-385).
The binomial series has radius of convergence `1` unless `r` is a nonnegative integer. -/
@[kb "openstaxcalculus2016" "2:§6.4 Definition (binomial series), p. 522"]
theorem binomial_series_radius_eq_one (r : ℝ) (hr : ∀ k : ℕ, r ≠ k) :
    (ofScalars ℝ (fun n => Ring.choose r n)).radius = 1 :=
  binomialSeries_radius_eq_one (𝔸 := ℝ) hr

/-- OpenStax Calculus 2:§6.4 Definition (binomial series) (CA-385).
For a nonnegative integer exponent the binomial series is a polynomial (infinite radius). -/
@[kb "openstaxcalculus2016" "2:§6.4 Definition (binomial series), p. 522"]
theorem binomial_series_radius_eq_top_of_nat (r : ℕ) :
    (ofScalars ℝ (fun n => Ring.choose (r : ℝ) n)).radius = ⊤ :=
  binomialSeries_radius_eq_top_of_nat (𝔸 := ℝ) (𝕂 := ℝ)

/-! ## Results proved in undergrad-kb -/

open scoped ENNReal

/-- OpenStax Calculus 2:Theorem 6.1 (CA-361). Convergence of a power series `∑ c n (x - a)^n`,
with radius `R = (ofScalars ℝ c).radius`: absolute convergence for `|x - a| < R`, divergence for
`|x - a| > R`, `R = 0` exactly when it converges only at the center, and `R = ∞` exactly when it
converges for all real `x`. -/
@[kb "openstaxcalculus2016" "2:Theorem 6.1, p. 479"]
theorem power_series_convergence_trichotomy (c : ℕ → ℝ) (a : ℝ) :
    (∀ x : ℝ, (‖x - a‖₊ : ℝ≥0∞) < (ofScalars ℝ c).radius →
      Summable (fun n => |c n * (x - a) ^ n|)) ∧
    (∀ x : ℝ, (ofScalars ℝ c).radius < (‖x - a‖₊ : ℝ≥0∞) →
      ¬ Tendsto (fun n => c n * (x - a) ^ n) atTop (𝓝 0) ∧
      ∀ S : ℝ, ¬ Tendsto (fun n => ∑ i ∈ Finset.range n, c i * (x - a) ^ i) atTop (𝓝 S)) ∧
    ((ofScalars ℝ c).radius = 0 ↔ ∀ x : ℝ, x ≠ a →
      ∀ S : ℝ, ¬ Tendsto (fun n => ∑ i ∈ Finset.range n, c i * (x - a) ^ i) atTop (𝓝 S)) ∧
    ((ofScalars ℝ c).radius = ∞ ↔ ∀ x : ℝ, Summable (fun n => c n * (x - a) ^ n)) :=
  UndergradKB.Calculus.power_series_convergence_cases c a

/-- OpenStax Calculus 2:Theorem 6.2 (CA-365). If `∑ c n x^n → f x` and `∑ d n x^n → g x` on a set
`I`, then the sum series converges to `f + g`, `∑ c n b x^(n+m)` converges to `b x^m f x`, and
the series evaluated at `b x^m` converges to `f (b x^m)` whenever `b x^m ∈ I`. -/
@[kb "openstaxcalculus2016" "2:Theorem 6.2, p. 489"]
theorem power_series_sum_and_substitution {c d : ℕ → ℝ} {f g : ℝ → ℝ} {I : Set ℝ}
    (hf : ∀ x ∈ I, Tendsto (fun n => ∑ i ∈ Finset.range n, c i * x ^ i) atTop (𝓝 (f x)))
    (hg : ∀ x ∈ I, Tendsto (fun n => ∑ i ∈ Finset.range n, d i * x ^ i) atTop (𝓝 (g x)))
    (b : ℝ) (m : ℕ) :
    (∀ x ∈ I, Tendsto (fun n => ∑ i ∈ Finset.range n, (c i + d i) * x ^ i) atTop
      (𝓝 (f x + g x))) ∧
    (∀ x ∈ I, Tendsto (fun n => ∑ i ∈ Finset.range n, c i * b * x ^ (i + m)) atTop
      (𝓝 (b * x ^ m * f x))) ∧
    (∀ x : ℝ, b * x ^ m ∈ I →
      Tendsto (fun n => ∑ i ∈ Finset.range n, c i * (b * x ^ m) ^ i) atTop
        (𝓝 (f (b * x ^ m)))) :=
  UndergradKB.Calculus.power_series_algebra hf hg b m

/-- OpenStax Calculus 2:Theorem 6.3 (CA-366). Product of power series: where both series converge
absolutely (in particular for `|x|` below both radii), the Cauchy product with coefficients
`∑_{k ≤ n} a k b (n - k)` sums to the product of the two sums. -/
@[kb "openstaxcalculus2016" "2:Theorem 6.3, p. 495"]
theorem power_series_cauchy_product :
    (∀ {a b : ℕ → ℝ} {x : ℝ}, Summable (fun n => |a n * x ^ n|) →
      Summable (fun n => |b n * x ^ n|) →
      HasSum (fun n => (∑ k ∈ Finset.range (n + 1), a k * b (n - k)) * x ^ n)
        ((∑' n, a n * x ^ n) * ∑' n, b n * x ^ n)) ∧
    (∀ {a b : ℕ → ℝ} {x : ℝ}, (‖x‖₊ : ℝ≥0∞) < (ofScalars ℝ a).radius →
      (‖x‖₊ : ℝ≥0∞) < (ofScalars ℝ b).radius →
      HasSum (fun n => (∑ k ∈ Finset.range (n + 1), a k * b (n - k)) * x ^ n)
        ((∑' n, a n * x ^ n) * ∑' n, b n * x ^ n)) :=
  ⟨fun ha hb => UndergradKB.Calculus.power_series_product ha hb,
    fun hxa hxb => UndergradKB.Calculus.power_series_product_of_lt_radius hxa hxb⟩

/-- OpenStax Calculus 2:Theorem 6.4 (CA-368). Term-by-term differentiation and integration: for
`|y - a|` below the radius of `∑ c n (x - a)^n`, the sum is differentiable at `y` with derivative
the termwise derivative series (which converges absolutely), and the termwise integral series
has the original sum as its derivative. -/
@[kb "openstaxcalculus2016" "2:Theorem 6.4, p. 497"]
theorem power_series_term_by_term :
    (∀ {c : ℕ → ℝ} {a y : ℝ}, (‖y - a‖₊ : ℝ≥0∞) < (ofScalars ℝ c).radius →
      HasDerivAt (fun z => ∑' n, c n * (z - a) ^ n) (∑' n, c n * (n * (y - a) ^ (n - 1))) y ∧
      Summable (fun n : ℕ => |c n * (n * (y - a) ^ (n - 1))|)) ∧
    (∀ {c : ℕ → ℝ} {a y : ℝ}, (‖y - a‖₊ : ℝ≥0∞) < (ofScalars ℝ c).radius →
      HasDerivAt (fun z => ∑' n : ℕ, c n * (z - a) ^ (n + 1) / ((n : ℝ) + 1))
        (∑' n, c n * (y - a) ^ n) y) :=
  ⟨fun hy => UndergradKB.Calculus.power_series_hasDerivAt hy,
    fun hy => UndergradKB.Calculus.power_series_integral_hasDerivAt hy⟩

/-- OpenStax Calculus 2:Example 6.10, part a (CA-369). `ln (1 + x) = ∑_{n ≥ 1} (-1)^(n+1) x^n / n`
for `-1 < x ≤ 1`; at `x = 1` this is the alternating harmonic series with sum `ln 2`, and at
`x = -1` the series diverges (to `-∞`). -/
@[kb "openstaxcalculus2016" "2:Example 6.10 (part a), p. 499"]
theorem log_one_add_power_series :
    Tendsto (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i / ((i : ℝ) + 1)) atTop
        (𝓝 (Real.log 2)) ∧
    (∀ {x : ℝ}, -1 < x → x ≤ 1 →
      Tendsto (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * x ^ (i + 1) / ((i : ℝ) + 1)) atTop
        (𝓝 (Real.log (1 + x)))) ∧
    (Tendsto (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * (-1) ^ (i + 1) / ((i : ℝ) + 1))
        atTop atBot ∧
      ∀ S : ℝ, ¬ Tendsto
        (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * (-1) ^ (i + 1) / ((i : ℝ) + 1))
        atTop (𝓝 S)) :=
  ⟨UndergradKB.Calculus.alternating_harmonic_sum_eq_log_two,
    fun hx1 hx2 => UndergradKB.Calculus.log_one_add_series hx1 hx2,
    UndergradKB.Calculus.log_one_add_series_diverges_at_neg_one⟩

/-- OpenStax Calculus 2:Example 6.10, part b (CA-370). `arctan x = ∑ (-1)^n x^(2n+1) / (2n+1)`
for `|x| ≤ 1`. -/
@[kb "openstaxcalculus2016" "2:Example 6.10 (part b), p. 499"]
theorem arctan_power_series_interval {x : ℝ} (hx : |x| ≤ 1) :
    Tendsto (fun n => ∑ i ∈ Finset.range n,
        (-1 : ℝ) ^ i * x ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) atTop (𝓝 (Real.arctan x)) :=
  UndergradKB.Calculus.arctan_series hx

/-- OpenStax Calculus 2:Theorem 6.8 (CA-378). The Taylor series of `f` at `a` (terms
`UndergradKB.Calculus.taylorSeriesTerm`) converges to `f x` exactly when the remainder
`R_n(x)` (`UndergradKB.Calculus.taylorRemainder`) tends to `0`. -/
@[kb "openstaxcalculus2016" "2:Theorem 6.8, p. 516"]
theorem taylor_series_convergence_criterion (f : ℝ → ℝ) (a x : ℝ) :
    Tendsto (fun n => ∑ k ∈ Finset.range n, UndergradKB.Calculus.taylorSeriesTerm f a k x)
        atTop (𝓝 (f x)) ↔
      Tendsto (fun n => UndergradKB.Calculus.taylorRemainder f a n x) atTop (𝓝 0) :=
  UndergradKB.Calculus.taylor_series_converges_iff_remainder_tendsto_zero f a x

/-! ## Wave 3: further results -/

/-- OpenStax Calculus 2:§6.1 Definition (power series centered at a) (CA-360). A power series
centered at `a` is `∑ c n (x - a)^n`; in Mathlib it is `ofScalars ℝ c` evaluated at `x - a`, its
sum is the `tsum` of the terms, and the `n = 0` term is `c 0` even at `x = a`. -/
@[kb "openstaxcalculus2016" "2:§6.1 Definition (power series centered at a), p. 478"]
theorem power_series_centered_at (c : ℕ → ℝ) (a x : ℝ) :
    ofScalarsSum c (x - a) = ∑' n, c n * (x - a) ^ n ∧ ofScalarsSum c (0 : ℝ) = c 0 :=
  ⟨by simpa using ofScalars_sum_eq c (x - a), by simp⟩

/-- OpenStax Calculus 2:§6.3 Definition (Taylor and Maclaurin series) (CA-373). The `n`th term of
the Taylor series of `f` at `a` is `f⁽ⁿ⁾(a) (x - a)ⁿ / n!` (Maclaurin series: `a = 0`), and the
Taylor polynomial of degree `n` is the sum of the first `n + 1` terms. -/
@[kb "openstaxcalculus2016" "2:§6.3 Definition (Taylor and Maclaurin series), p. 506"]
theorem taylor_series_definition (f : ℝ → ℝ) (a x : ℝ) (n : ℕ) :
    UndergradKB.Calculus.taylorSeriesTerm f a n x =
      iteratedDeriv n f a / (Nat.factorial n : ℝ) * (x - a) ^ n ∧
    taylorWithinEval f n univ a x =
      ∑ k ∈ Finset.range (n + 1), UndergradKB.Calculus.taylorSeriesTerm f a k x :=
  ⟨rfl, UndergradKB.Calculus.taylorWithinEval_univ_eq_sum_taylorSeriesTerm f a x n⟩

/-- OpenStax Calculus 2:Example 6.15 (CA-377). The Taylor series of `1/x` at `a = 1` has terms
`(-1)ⁿ (x - 1)ⁿ`; it converges to `1/x` exactly on `(0, 2)`, and its terms do not tend to `0`
outside that interval. -/
@[kb "openstaxcalculus2016" "2:Example 6.15, p. 515"]
theorem taylor_series_of_reciprocal_at_one :
    (∀ (n : ℕ) (x : ℝ), UndergradKB.Calculus.taylorSeriesTerm (fun t : ℝ => 1 / t) 1 n x =
      (-1) ^ n * (x - 1) ^ n) ∧
    (∀ x ∈ Ioo (0 : ℝ) 2, HasSum (fun n : ℕ => (-1 : ℝ) ^ n * (x - 1) ^ n) (1 / x)) ∧
    (∀ x : ℝ, x ∉ Ioo (0 : ℝ) 2 →
      ¬ Tendsto (fun n : ℕ => (-1 : ℝ) ^ n * (x - 1) ^ n) atTop (𝓝 0)) :=
  ⟨UndergradKB.Calculus.taylorSeriesTerm_inv_at_one,
    UndergradKB.Calculus.inv_taylor_series_at_one.1,
    UndergradKB.Calculus.inv_taylor_series_at_one.2⟩

/-- OpenStax Calculus 2:§6.3 Student Project (e is irrational) (CA-382). The number `e = exp 1`
is irrational. -/
@[kb "openstaxcalculus2016" "2:§6.3 Student Project (e is irrational), p. 518"]
theorem e_is_irrational : Irrational (Real.exp 1) :=
  UndergradKB.Calculus.irrational_exp_one

end UndergradKB.Calculus.Course.V2C6
