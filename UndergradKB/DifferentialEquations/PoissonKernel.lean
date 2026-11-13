import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import UndergradKB.Common.Attr

/-! # The Dirichlet problem on the disc and the Poisson kernel

Lebl, *Notes on Diffy Qs*, §4.10.  The series solution
`u = a₀/2 + ∑ rⁿ (aₙ cos nθ + bₙ sin nθ)` is harmonic in the unit disc (it is the real part of the power series
`∑ cₙ zⁿ`, `cₙ = aₙ - i bₙ`), and when `aₙ, bₙ` are the Fourier coefficients of the boundary data `g` it equals
the Poisson integral `∫ P(r, θ, α) g(α) dα`, with the closed form of the kernel coming from the geometric series. -/

namespace UndergradKB.DifferentialEquations

open Real Complex MeasureTheory Filter Topology

/-- The Poisson kernel of the unit disc, `P(r,θ,α) = (1 - r²) / (2π (1 - 2r cos(θ-α) + r²))`. -/
noncomputable def poissonKernel (r θ α : ℝ) : ℝ :=
  (1 - r ^ 2) / (2 * π * (1 - 2 * r * Real.cos (θ - α) + r ^ 2))

lemma poisson_denom_pos {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (x : ℝ) :
    0 < 1 - 2 * r * Real.cos x + r ^ 2 := by
  have h1 : r * Real.cos x ≤ r := by
    have := Real.cos_le_one x
    nlinarith
  nlinarith

/-- The geometric series behind the Poisson kernel: for `0 ≤ r < 1`,
`∑_{n ≥ 1} rⁿ cos(nx) = (1 - r²) / (2 (1 - 2r cos x + r²)) - 1/2`. -/
theorem poisson_cos_series {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (x : ℝ) :
    HasSum (fun n : ℕ => r ^ (n + 1) * Real.cos ((n + 1 : ℝ) * x))
      ((1 - r ^ 2) / (2 * (1 - 2 * r * Real.cos x + r ^ 2)) - 1 / 2) := by
  set w : ℂ := (r : ℂ) * Complex.exp ((x : ℂ) * I) with hw
  have hnorm : ‖w‖ < 1 := by
    rw [hw, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0]
    exact hr
  have hg := hasSum_geometric_of_norm_lt_one hnorm
  have hre := Complex.hasSum_re hg
  have hterm : ∀ n : ℕ, ((w ^ n).re) = r ^ n * Real.cos (n * x) := by
    intro n
    rw [hw, mul_pow, ← Complex.exp_nat_mul, ← Complex.ofReal_pow]
    rw [show (n : ℂ) * ((x : ℂ) * I) = ((n * x : ℝ) : ℂ) * I by push_cast; ring]
    rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  simp only [hterm] at hre
  have hD := poisson_denom_pos hr0 hr x
  have hval : ((1 - w)⁻¹).re = (1 - r * Real.cos x) / (1 - 2 * r * Real.cos x + r ^ 2) := by
    have hw' : w = ((r * Real.cos x : ℝ) : ℂ) + ((r * Real.sin x : ℝ) : ℂ) * I := by
      rw [hw, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      push_cast; ring
    have hre1 : (1 - w).re = 1 - r * Real.cos x := by
      rw [hw', Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re]
      simp
    have him1 : (1 - w).im = -(r * Real.sin x) := by
      rw [hw', Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, Complex.I_im]
      simp
    rw [Complex.inv_re, Complex.normSq_apply, hre1, him1]
    congr 1
    linear_combination r ^ 2 * Real.sin_sq_add_cos_sq x
  rw [hval] at hre
  have h2 := (hasSum_nat_add_iff' 1).mpr hre
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.cast_zero, zero_mul, Real.cos_zero,
    mul_one] at h2
  have heq : (1 - r ^ 2) / (2 * (1 - 2 * r * Real.cos x + r ^ 2)) - 1 / 2
      = (1 - r * Real.cos x) / (1 - 2 * r * Real.cos x + r ^ 2) - 1 := by
    have hD' : (1 - 2 * r * Real.cos x + r ^ 2) ≠ 0 := hD.ne'
    rw [div_sub_one hD', div_sub_div _ _ (mul_ne_zero two_ne_zero hD') two_ne_zero,
      div_eq_div_iff (mul_ne_zero (mul_ne_zero two_ne_zero hD') two_ne_zero) hD']
    ring
  rw [heq]
  convert h2 using 1
  funext n; push_cast; ring_nf

/-- **Poisson kernel (DE-152).** For `0 ≤ r < 1`, `P(r,θ,α) = (1/π) (1/2 + ∑_{n≥1} rⁿ cos n(θ-α))`. -/
@[kb "lebldiffyqs2026" "§4.10 Poisson kernel, p. 269"]
theorem poissonKernel_hasSum {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (θ α : ℝ) :
    HasSum (fun n : ℕ => (1 / π) * (r ^ (n + 1) * Real.cos ((n + 1 : ℝ) * (θ - α))))
      (poissonKernel r θ α - 1 / (2 * π)) := by
  have h := (poisson_cos_series hr0 hr (θ - α)).mul_left (1 / π)
  convert h using 1
  have hD := poisson_denom_pos hr0 hr (θ - α)
  unfold poissonKernel
  field_simp

lemma poissonKernel_continuous {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (θ : ℝ) :
    Continuous (fun α => poissonKernel r θ α) := by
  have hc : Continuous fun α : ℝ => 2 * π * (1 - 2 * r * Real.cos (θ - α) + r ^ 2) := by fun_prop
  have hne : ∀ α : ℝ, 2 * π * (1 - 2 * r * Real.cos (θ - α) + r ^ 2) ≠ 0 := fun α =>
    ne_of_gt (mul_pos (mul_pos two_pos Real.pi_pos) (poisson_denom_pos hr0 hr (θ - α)))
  exact (continuous_const (y := 1 - r ^ 2)).div hc hne

/-- Fourier cosine coefficient on `[-π, π]`, `aₙ = (1/π) ∫ g(α) cos(nα) dα`. -/
noncomputable def discCoeffA (g : ℝ → ℝ) (n : ℕ) : ℝ := (1 / π) * ∫ α in (-π)..π, g α * Real.cos (n * α)

/-- Fourier sine coefficient on `[-π, π]`, `bₙ = (1/π) ∫ g(α) sin(nα) dα`. -/
noncomputable def discCoeffB (g : ℝ → ℝ) (n : ℕ) : ℝ := (1 / π) * ∫ α in (-π)..π, g α * Real.sin (n * α)

/-- **Dirichlet problem on the disc: series = Poisson integral (DE-151, DE-152).** For integrable boundary data
`g` on `[-π, π]` with Fourier coefficients `aₙ, bₙ` and `0 ≤ r < 1`,
`a₀/2 + ∑_{n≥1} rⁿ (aₙ cos nθ + bₙ sin nθ) = ∫_{-π}^{π} P(r,θ,α) g(α) dα`. -/
@[kb "lebldiffyqs2026" "§4.10 Poisson kernel, p. 269"]
theorem disc_series_eq_poisson {g : ℝ → ℝ} (hg : IntervalIntegrable g volume (-π) π) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < 1) (θ : ℝ) :
    HasSum (fun n : ℕ => r ^ (n + 1) * (discCoeffA g (n + 1) * Real.cos ((n + 1 : ℝ) * θ)
        + discCoeffB g (n + 1) * Real.sin ((n + 1 : ℝ) * θ)))
      ((∫ α in (-π)..π, poissonKernel r θ α * g α) - discCoeffA g 0 / 2) := by
  set F : ℕ → ℝ → ℝ := fun n α => (1 / π) * (r ^ (n + 1) * Real.cos ((n + 1 : ℝ) * (θ - α))) * g α
  have hterm : ∀ n : ℕ, r ^ (n + 1) * (discCoeffA g (n + 1) * Real.cos ((n + 1 : ℝ) * θ)
      + discCoeffB g (n + 1) * Real.sin ((n + 1 : ℝ) * θ)) = ∫ α in (-π)..π, F n α := by
    intro n
    have hc : IntervalIntegrable (fun α => g α * Real.cos ((n + 1 : ℕ) * α)) volume (-π) π :=
      hg.mul_continuousOn (by fun_prop)
    have hs : IntervalIntegrable (fun α => g α * Real.sin ((n + 1 : ℕ) * α)) volume (-π) π :=
      hg.mul_continuousOn (by fun_prop)
    simp only [F, discCoeffA, discCoeffB]
    rw [show (fun α => 1 / π * (r ^ (n + 1) * Real.cos ((n + 1 : ℝ) * (θ - α))) * g α)
        = fun α => (r ^ (n + 1) * (1 / π) * Real.cos ((n + 1 : ℝ) * θ)) * (g α * Real.cos ((n + 1 : ℕ) * α))
          + (r ^ (n + 1) * (1 / π) * Real.sin ((n + 1 : ℝ) * θ)) * (g α * Real.sin ((n + 1 : ℕ) * α)) by
      funext α
      rw [mul_sub, Real.cos_sub]
      push_cast; ring]
    rw [intervalIntegral.integral_add (hc.const_mul _) (hs.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    ring
  simp only [hterm]
  have hPint : IntervalIntegrable (fun α => poissonKernel r θ α * g α) volume (-π) π :=
    hg.continuousOn_mul (poissonKernel_continuous hr0 hr θ).continuousOn
  have hlim : ∀ α, HasSum (fun n => F n α) (poissonKernel r θ α * g α - (1 / (2 * π)) * g α) := by
    intro α
    have := (poissonKernel_hasSum hr0 hr θ α).mul_right (g α)
    simp only [F]
    convert this using 1
    ring
  have hmeas : AEStronglyMeasurable g (volume.restrict (Set.uIoc (-π) π)) :=
    hg.def'.aestronglyMeasurable
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := -π) (b := π) (F := F)
    (f := fun α => poissonKernel r θ α * g α - (1 / (2 * π)) * g α)
    (fun n α => (1 / π) * r ^ (n + 1) * |g α|)
    (fun n => ((by fun_prop : Continuous fun α : ℝ =>
        (1 / π) * (r ^ (n + 1) * Real.cos ((n + 1 : ℝ) * (θ - α)))).aestronglyMeasurable).mul hmeas)
    (fun n => Eventually.of_forall fun α _ => by
      simp only [F, norm_mul, Real.norm_eq_abs]
      rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / π), abs_of_nonneg (by positivity : (0 : ℝ) ≤ r ^ (n + 1))]
      have := Real.abs_cos_le_one ((n + 1 : ℝ) * (θ - α))
      have h0 : 0 ≤ |g α| := abs_nonneg _
      have hp : 0 ≤ r ^ (n + 1) := by positivity
      have hπ : 0 < 1 / π := by positivity
      calc 1 / π * (r ^ (n + 1) * |Real.cos ((n + 1 : ℝ) * (θ - α))|) * |g α|
          ≤ 1 / π * (r ^ (n + 1) * 1) * |g α| := by gcongr
        _ = 1 / π * r ^ (n + 1) * |g α| := by ring)
    (Eventually.of_forall fun α _ => by
      have : Summable fun n : ℕ => r ^ (n + 1) :=
        (summable_geometric_of_lt_one hr0 hr).comp_injective (add_left_injective 1)
      exact (this.mul_left (1 / π)).mul_right _)
    (by
      have : (fun α => ∑' n : ℕ, (1 / π) * r ^ (n + 1) * |g α|)
          = fun α => (∑' n : ℕ, (1 / π) * r ^ (n + 1)) * |g α| := by
        funext α; rw [tsum_mul_right]
      rw [this]
      exact hg.abs.const_mul _)
    (Eventually.of_forall fun α _ => hlim α)
  convert hsum using 1
  rw [intervalIntegral.integral_sub hPint (hg.const_mul _), intervalIntegral.integral_const_mul]
  simp only [discCoeffA, Nat.cast_zero, zero_mul, Real.cos_zero, mul_one]
  ring

/-- Complex coefficients `c₀ = a₀/2`, `cₙ = aₙ - i bₙ` of the disc series. -/
noncomputable def discCoeffC (a b : ℕ → ℝ) (n : ℕ) : ℂ :=
  if n = 0 then ((a 0 / 2 : ℝ) : ℂ) else (a n : ℂ) - (b n : ℂ) * I

/-- The disc series as a function on `ℂ`: `u(z) = Re ∑ cₙ zⁿ`. -/
noncomputable def discSeries (a b : ℕ → ℝ) (z : ℂ) : ℝ :=
  (∑' n : ℕ, discCoeffC a b n * z ^ n).re

lemma discCoeffC_norm_le {a b : ℕ → ℝ} {M : ℝ} (ha : ∀ n, |a n| ≤ M) (hb : ∀ n, |b n| ≤ M) (n : ℕ) :
    ‖discCoeffC a b n‖ ≤ 2 * M := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (ha 0)
  unfold discCoeffC
  split_ifs
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_two]
    have := ha 0
    linarith
  · calc ‖(a n : ℂ) - (b n : ℂ) * I‖ ≤ ‖(a n : ℂ)‖ + ‖(b n : ℂ) * I‖ := norm_sub_le _ _
      _ = |a n| + |b n| := by rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ 2 * M := by linarith [ha n, hb n]

lemma discSeries_analyticAt {a b : ℕ → ℝ} {M : ℝ} (ha : ∀ n, |a n| ≤ M) (hb : ∀ n, |b n| ≤ M)
    {z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticAt ℂ (fun w => ∑' n : ℕ, discCoeffC a b n * w ^ n) z := by
  set p := FormalMultilinearSeries.ofScalars ℂ (discCoeffC a b)
  have hrad : (1 : ENNReal) ≤ p.radius := by
    have := p.le_radius_of_bound (2 * M) (r := 1) (fun n => by
      rw [NNReal.coe_one, one_pow, mul_one, FormalMultilinearSeries.ofScalars_norm]
      exact discCoeffC_norm_le ha hb n)
    simpa using this
  have hpos : 0 < p.radius := lt_of_lt_of_le one_pos hrad
  have hball := p.hasFPowerSeriesOnBall hpos
  have hsum : p.sum = fun w => ∑' n : ℕ, discCoeffC a b n * w ^ n := by
    funext w
    simp only [FormalMultilinearSeries.sum, p, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  rw [← hsum]
  have hmem : z ∈ Metric.eball (0 : ℂ) p.radius := by
    rw [Metric.mem_eball, edist_zero_right]
    rw [← ofReal_norm]
    exact lt_of_lt_of_le (ENNReal.ofReal_lt_one.mpr hz) hrad
  have := hball.analyticAt_of_mem hmem
  simpa using this

/-- **The disc series is harmonic (DE-151).** For bounded coefficients `aₙ, bₙ`, the function
`u = Re ∑ cₙ zⁿ` (`c₀ = a₀/2`, `cₙ = aₙ - i bₙ`) is harmonic in the open unit disc. -/
@[kb "lebldiffyqs2026" "§4.10 series solution, p. 265"]
theorem discSeries_harmonic {a b : ℕ → ℝ} {M : ℝ} (ha : ∀ n, |a n| ≤ M) (hb : ∀ n, |b n| ≤ M) :
    InnerProductSpace.HarmonicOnNhd (discSeries a b) (Metric.ball (0 : ℂ) 1) := by
  intro z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  exact (discSeries_analyticAt ha hb hz).harmonicAt_re

/-- **The disc series in polar coordinates (DE-151).** At `z = r e^{iθ}`, `0 ≤ r < 1`,
`u = a₀/2 + ∑_{n≥1} rⁿ (aₙ cos nθ + bₙ sin nθ)`. -/
@[kb "lebldiffyqs2026" "§4.10 series solution, p. 265"]
theorem discSeries_polar {a b : ℕ → ℝ} {M : ℝ} (ha : ∀ n, |a n| ≤ M) (hb : ∀ n, |b n| ≤ M) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < 1) (θ : ℝ) :
    HasSum (fun n : ℕ => r ^ (n + 1) * (a (n + 1) * Real.cos ((n + 1 : ℝ) * θ)
        + b (n + 1) * Real.sin ((n + 1 : ℝ) * θ)))
      (discSeries a b ((r : ℂ) * Complex.exp ((θ : ℂ) * I)) - a 0 / 2) := by
  set z : ℂ := (r : ℂ) * Complex.exp ((θ : ℂ) * I)
  have hz : ‖z‖ = r := by
    simp only [z, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0]
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (ha 0)
  have hsumm : Summable fun n : ℕ => discCoeffC a b n * z ^ n := by
    refine Summable.of_norm_bounded (g := fun n : ℕ => 2 * M * r ^ n)
      ((summable_geometric_of_lt_one hr0 hr).mul_left _) (fun n => ?_)
    rw [norm_mul, norm_pow, hz]
    exact mul_le_mul_of_nonneg_right (discCoeffC_norm_le ha hb n) (by positivity)
  have hre := Complex.hasSum_re hsumm.hasSum
  have h2 := (hasSum_nat_add_iff' 1).mpr hre
  have hterm : ∀ n : ℕ, (discCoeffC a b (n + 1) * z ^ (n + 1)).re = r ^ (n + 1) * (a (n + 1) *
      Real.cos ((n + 1 : ℝ) * θ) + b (n + 1) * Real.sin ((n + 1 : ℝ) * θ)) := by
    intro n
    simp only [discCoeffC, Nat.add_one_ne_zero, ite_false, z]
    rw [mul_pow, ← Complex.exp_nat_mul, ← Complex.ofReal_pow,
      show ((n + 1 : ℕ) : ℂ) * ((θ : ℂ) * I) = (((n + 1 : ℝ) * θ : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.sub_im, Complex.add_re, Complex.add_im]
    ring
  simp only [hterm, Finset.range_one, Finset.sum_singleton, pow_zero, mul_one] at h2
  convert h2 using 1
  simp [discSeries, discCoeffC, z]

/-- The Fourier coefficients of integrable boundary data are bounded, `|aₙ|, |bₙ| ≤ (1/π) ∫ |g|`. -/
lemma discCoeff_bounded {g : ℝ → ℝ} (hg : IntervalIntegrable g volume (-π) π) :
    (∀ n, |discCoeffA g n| ≤ (1 / π) * ∫ α in (-π)..π, |g α|) ∧
      (∀ n, |discCoeffB g n| ≤ (1 / π) * ∫ α in (-π)..π, |g α|) := by
  have hle : -π ≤ π := by linarith [Real.pi_pos]
  have key : ∀ (h : ℝ → ℝ), Continuous h → (∀ α, |h α| ≤ 1) →
      |(1 / π) * ∫ α in (-π)..π, g α * h α| ≤ (1 / π) * ∫ α in (-π)..π, |g α| := by
    intro h hc h1
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / π)]
    gcongr
    calc |∫ α in (-π)..π, g α * h α| ≤ ∫ α in (-π)..π, |g α * h α| :=
          intervalIntegral.abs_integral_le_integral_abs hle
      _ ≤ ∫ α in (-π)..π, |g α| := by
          apply intervalIntegral.integral_mono_on hle (hg.mul_continuousOn hc.continuousOn).abs hg.abs
          intro α _
          rw [abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (h1 α)
  exact ⟨fun n => key _ (by fun_prop) (fun α => Real.abs_cos_le_one _),
    fun n => key _ (by fun_prop) (fun α => Real.abs_sin_le_one _)⟩

/-- **Solution of the Dirichlet problem on the disc (DE-151).** For integrable boundary data `g`, the series with
the Fourier coefficients of `g` defines a harmonic function in the unit disc whose value at `r e^{iθ}` is the
Poisson integral `∫ P(r,θ,α) g(α) dα`. (The boundary limit `r → 1` is not proved here.) -/
@[kb "lebldiffyqs2026" "§4.10 series solution, p. 265"]
theorem disc_dirichlet_poisson {g : ℝ → ℝ} (hg : IntervalIntegrable g volume (-π) π) :
    InnerProductSpace.HarmonicOnNhd (discSeries (discCoeffA g) (discCoeffB g)) (Metric.ball (0 : ℂ) 1) ∧
      ∀ r θ : ℝ, 0 ≤ r → r < 1 →
        discSeries (discCoeffA g) (discCoeffB g) ((r : ℂ) * Complex.exp ((θ : ℂ) * I))
          = ∫ α in (-π)..π, poissonKernel r θ α * g α := by
  obtain ⟨ha, hb⟩ := discCoeff_bounded hg
  refine ⟨discSeries_harmonic ha hb, fun r θ hr0 hr => ?_⟩
  have h1 := discSeries_polar ha hb hr0 hr θ
  have h2 := disc_series_eq_poisson hg hr0 hr θ
  have := h1.unique h2
  linarith

end UndergradKB.DifferentialEquations
