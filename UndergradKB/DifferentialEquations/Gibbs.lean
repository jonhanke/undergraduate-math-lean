import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import UndergradKB.Common.Attr
import UndergradKB.DifferentialEquations.FourierSeries

/-! # The Gibbs phenomenon for the square wave

Lebl, *Notes on Diffy Qs*, §4.2.  For the square wave (jump of size 2 at `0`) the partial sum
of the Fourier series through the term `n = 2M-1` at the point `π/(2M)` tends to
`(2/π) ∫_0^π sin t / t dt`, which exceeds `1.17`; the square wave itself is `1` there, so the
overshoot does not shrink as terms are added.  The ingredients are a midpoint Riemann sum
lemma and Taylor lower bounds for `sin`. -/

namespace UndergradKB.DifferentialEquations

open Real intervalIntegral MeasureTheory Set Filter Topology

/-! ## Midpoint Riemann sums -/

/-- Midpoint Riemann sums over `[0, π]` with `M` equal pieces converge to the integral of a
continuous function. -/
lemma tendsto_midpoint_sum {f : ℝ → ℝ} (hf : Continuous f) :
    Tendsto (fun M : ℕ => ∑ j ∈ Finset.range M, (π / M) * f ((2 * j + 1) * π / (2 * M)))
      atTop (𝓝 (∫ t in (0:ℝ)..π, f t)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have huc := (isCompact_Icc (a := (0:ℝ)) (b := π)).uniformContinuousOn_of_continuous
    hf.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδ'⟩ := huc (ε / (2 * π)) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (π / δ)
  refine ⟨N + 1, fun M hM => ?_⟩
  have hMpos : (0:ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hN' : π / δ < M := lt_of_lt_of_le hN (by exact_mod_cast (by omega : N ≤ M))
  have hstep : π / M < δ := by
    rw [div_lt_iff₀ hMpos]
    rw [div_lt_iff₀ hδ] at hN'
    linarith
  have hsplit : ∫ t in (0:ℝ)..π, f t
      = ∑ j ∈ Finset.range M, ∫ t in ((j:ℝ) * π / M)..(((j:ℝ) + 1) * π / M), f t := by
    have := intervalIntegral.sum_integral_adjacent_intervals (f := f) (μ := volume)
      (a := fun j : ℕ => (j:ℝ) * π / M) (n := M) (fun k _ => hf.intervalIntegrable _ _)
    simp only [Nat.cast_zero, zero_mul, zero_div, Nat.cast_add, Nat.cast_one] at this
    have hM : (M:ℝ) * π / M = π := by field_simp
    rw [hM] at this
    exact this.symm
  have hterm : ∀ j ∈ Finset.range M,
      |(∫ t in ((j:ℝ) * π / M)..(((j:ℝ) + 1) * π / M), f t)
        - (π / M) * f ((2 * j + 1) * π / (2 * M))| ≤ ε / (2 * π) * (π / M) := by
    intro j hj
    have hj' : (j:ℝ) + 1 ≤ M := by exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.1 hj)
    have hpM : 0 < π / M := by positivity
    have hpM2 : 0 < π / (2 * M) := by positivity
    have hb1 : ((j:ℝ) + 1) * π / M = (j:ℝ) * π / M + π / M := by ring
    have hc1 : (2 * (j:ℝ) + 1) * π / (2 * M) = (j:ℝ) * π / M + π / (2 * M) := by ring
    have hc2 : π / M = 2 * (π / (2 * M)) := by ring
    have ha0 : 0 ≤ (j:ℝ) * π / M := by positivity
    have hbπ : ((j:ℝ) + 1) * π / M ≤ π := by
      rw [div_le_iff₀ hMpos]
      nlinarith [pi_pos, mul_nonneg (sub_nonneg.2 hj') pi_pos.le]
    have hle : (j:ℝ) * π / M ≤ ((j:ℝ) + 1) * π / M := by linarith
    have hkey : (∫ t in ((j:ℝ) * π / M)..(((j:ℝ) + 1) * π / M), f t)
        - (π / M) * f ((2 * j + 1) * π / (2 * M))
        = ∫ t in ((j:ℝ) * π / M)..(((j:ℝ) + 1) * π / M), (f t - f ((2 * j + 1) * π / (2 * M))) := by
      rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _) intervalIntegrable_const,
        intervalIntegral.integral_const, smul_eq_mul]
      congr 2
      linarith
    rw [hkey]
    have hb : ∀ x ∈ Set.uIoc ((j:ℝ) * π / M) (((j:ℝ) + 1) * π / M),
        ‖f x - f ((2 * j + 1) * π / (2 * M))‖ ≤ ε / (2 * π) := by
      intro x hx
      rw [Set.uIoc_of_le hle] at hx
      obtain ⟨hx1, hx2⟩ := hx
      have := hδ' x ⟨by linarith, by linarith⟩ ((2 * j + 1) * π / (2 * M))
        ⟨by linarith, by linarith⟩ (by
          rw [Real.dist_eq, abs_lt]
          constructor <;> linarith)
      rw [Real.dist_eq] at this
      rw [Real.norm_eq_abs]
      exact this.le
    have := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [Real.norm_eq_abs] at this
    have h2 : |((j:ℝ) + 1) * π / M - (j:ℝ) * π / M| = π / M := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    rw [h2] at this
    exact this
  rw [Real.dist_eq, abs_sub_comm, hsplit, ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ j ∈ Finset.range M, |(∫ t in ((j:ℝ) * π / M)..(((j:ℝ) + 1) * π / M), f t)
        - (π / M) * f ((2 * j + 1) * π / (2 * M))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range M, ε / (2 * π) * (π / M) := Finset.sum_le_sum hterm
    _ = ε / 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp
    _ < ε := by linarith

/-! ## Taylor lower bound for sine -/

/-- A function with derivative `g ≥ 0` on `[0, ∞)` and value `0` at `0` is nonnegative there. -/
lemma nonneg_of_hasDerivAt {h g : ℝ → ℝ} (hd : ∀ t, HasDerivAt h (g t) t) (h0 : h 0 = 0)
    (hg : ∀ t, 0 ≤ t → 0 ≤ g t) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ h t := by
  have hmono : MonotoneOn h (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact (continuous_iff_continuousAt.2 fun x => (hd x).continuousAt).continuousOn
    · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hd x).deriv]
      exact hg x (le_of_lt (by simpa using hx))
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht
  linarith

lemma cos_le_taylor4 {t : ℝ} (ht : 0 ≤ t) : cos t ≤ 1 - t ^ 2 / 2 + t ^ 4 / 24 := by
  have h := nonneg_of_hasDerivAt (h := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - cos t)
    (g := fun t => -t + t ^ 3 / 6 + sin t) (fun t => by
      have h := (((hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_pow 2 t).div_const 2)).add
        ((hasDerivAt_pow 4 t).div_const 24)).sub (hasDerivAt_cos t)
      refine h.congr_deriv ?_
      simp
      ring) (by simp) (fun t ht => by
      rcases ht.eq_or_lt with h | h
      · subst h; simp
      · have := sin_gt_sub_cube h
        linarith) ht
  beta_reduce at h
  linarith

lemma sin_le_taylor5 {t : ℝ} (ht : 0 ≤ t) : sin t ≤ t - t ^ 3 / 6 + t ^ 5 / 120 := by
  have h := nonneg_of_hasDerivAt (h := fun t => t - t ^ 3 / 6 + t ^ 5 / 120 - sin t)
    (g := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - cos t) (fun t => by
      have h := (((hasDerivAt_id' t).sub ((hasDerivAt_pow 3 t).div_const 6)).add
        ((hasDerivAt_pow 5 t).div_const 120)).sub (hasDerivAt_sin t)
      refine h.congr_deriv ?_
      simp
      ring) (by simp) (fun t ht => by
      have := cos_le_taylor4 ht
      linarith) ht
  beta_reduce at h
  linarith

lemma cos_ge_taylor6 {t : ℝ} (ht : 0 ≤ t) :
    1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 ≤ cos t := by
  have h := nonneg_of_hasDerivAt (h := fun t => cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720))
    (g := fun t => t - t ^ 3 / 6 + t ^ 5 / 120 - sin t) (fun t => by
      have h := (hasDerivAt_cos t).sub
        ((((hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_pow 2 t).div_const 2)).add
        ((hasDerivAt_pow 4 t).div_const 24)).sub ((hasDerivAt_pow 6 t).div_const 720))
      refine h.congr_deriv ?_
      simp
      ring) (by simp) (fun t ht => by
      have := sin_le_taylor5 ht
      linarith) ht
  beta_reduce at h
  linarith

/-- For `t ≥ 0`: `t - t³/6 + t⁵/120 - t⁷/5040 ≤ sin t`. -/
lemma sin_ge_taylor7 {t : ℝ} (ht : 0 ≤ t) :
    t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 ≤ sin t := by
  have h := nonneg_of_hasDerivAt
    (h := fun t => sin t - (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040))
    (g := fun t => cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720)) (fun t => by
      have h := (hasDerivAt_sin t).sub
        ((((hasDerivAt_id' t).sub ((hasDerivAt_pow 3 t).div_const 6)).add
        ((hasDerivAt_pow 5 t).div_const 120)).sub ((hasDerivAt_pow 7 t).div_const 5040))
      refine h.congr_deriv ?_
      simp
      ring) (by simp) (fun t ht => by
      have := cos_ge_taylor6 ht
      linarith) ht
  beta_reduce at h
  linarith

lemma sinc_ge_poly {t : ℝ} (ht : 0 ≤ t) :
    1 - t ^ 2 / 6 + t ^ 4 / 120 - t ^ 6 / 5040 ≤ sinc t := by
  rcases ht.eq_or_lt with h | h
  · subst h; simp
  · rw [sinc_of_ne_zero h.ne', le_div_iff₀ h]
    have := sin_ge_taylor7 ht
    nlinarith

/-! ## The integral of sinc -/

/-- `∫_0^π sinc t dt` is at least the integral of the Taylor polynomial, which gives
`(2/π) ∫_0^π sin t / t dt > 1.17`. -/
theorem two_div_pi_mul_integral_sinc_gt : 1.17 < (2 / π) * ∫ t in (0:ℝ)..π, sinc t := by
  have hpoly : ∫ t in (0:ℝ)..π, (1 - t ^ 2 / 6 + t ^ 4 / 120 - t ^ 6 / 5040)
      = π - π ^ 3 / 18 + π ^ 5 / 600 - π ^ 7 / 35280 := by
    rw [integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => t - t ^ 3 / 18 + t ^ 5 / 600 - t ^ 7 / 35280)]
    · simp
    · intro t _
      have h := (((hasDerivAt_id' t).sub ((hasDerivAt_pow 3 t).div_const 18)).add
        ((hasDerivAt_pow 5 t).div_const 600)).sub ((hasDerivAt_pow 7 t).div_const 35280)
      refine h.congr_deriv ?_
      simp
      ring
    · exact (by fun_prop : Continuous fun t : ℝ => 1 - t ^ 2 / 6 + t ^ 4 / 120 - t ^ 6 / 5040)
        |>.intervalIntegrable _ _
  have hmono : ∫ t in (0:ℝ)..π, (1 - t ^ 2 / 6 + t ^ 4 / 120 - t ^ 6 / 5040)
      ≤ ∫ t in (0:ℝ)..π, sinc t := by
    apply intervalIntegral.integral_mono_on pi_pos.le
    · exact (by fun_prop : Continuous fun t : ℝ => 1 - t ^ 2 / 6 + t ^ 4 / 120 - t ^ 6 / 5040)
        |>.intervalIntegrable _ _
    · exact continuous_sinc.intervalIntegrable _ _
    · intro t ht
      exact sinc_ge_poly ht.1
  rw [hpoly] at hmono
  have hπ1 := pi_gt_d2
  have hπ2 := pi_lt_d4
  have hu : π ^ 2 ≤ 9.87 := by nlinarith
  have hu0 : 0 ≤ π ^ 2 := by positivity
  -- g(u) = 1 - u/18 + u²/600 - u³/35280 is decreasing on [0, 9.87]
  have hg : 0.5867 ≤ 1 - π ^ 2 / 18 + (π ^ 2) ^ 2 / 600 - (π ^ 2) ^ 3 / 35280 := by
    generalize π ^ 2 = u at hu hu0 ⊢
    have h1 : 0 ≤ 9.87 - u := by linarith
    have h2 : 0 ≤ 1 / 18 - (u + 9.87) / 600 + (u ^ 2 + u * 9.87 + 9.87 ^ 2) / 35280 := by
      nlinarith [sq_nonneg u]
    nlinarith [mul_nonneg h1 h2]
  have hπpos : 0 < π := pi_pos
  have : (2 / π) * (π - π ^ 3 / 18 + π ^ 5 / 600 - π ^ 7 / 35280)
      = 2 * (1 - π ^ 2 / 18 + (π ^ 2) ^ 2 / 600 - (π ^ 2) ^ 3 / 35280) := by
    field_simp
  calc (1.17:ℝ) < 2 * (1 - π ^ 2 / 18 + (π ^ 2) ^ 2 / 600 - (π ^ 2) ^ 3 / 35280) := by linarith
    _ = _ := this.symm
    _ ≤ (2 / π) * ∫ t in (0:ℝ)..π, sinc t :=
        mul_le_mul_of_nonneg_left hmono (by positivity)

/-! ## Partial sums of the square wave series -/

lemma sum_Icc_two_mul (g : ℕ → ℝ) (hg : ∀ j, g (2 * j + 2) = 0) (M : ℕ) :
    ∑ k ∈ Finset.Icc 1 (2 * M), g k = ∑ j ∈ Finset.range M, g (2 * j + 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have h : 2 * (M + 1) = (2 * M + 1) + 1 := by ring
    rw [h, Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega),
      Finset.sum_range_succ, ← ih, show 2 * M + 1 + 1 = 2 * M + 2 by ring, hg M]
    ring

/-- The partial sum of the square wave's Fourier series through the term `n = 2M` (the term
`n = 2M` vanishes) is `(4/π) ∑_{j<M} sin((2j+1)x)/(2j+1)`. -/
lemma trigPoly_squareWave (M : ℕ) (x : ℝ) :
    trigPoly π (fourierA squareWave π) (fourierB squareWave π) (2 * M) x
      = (4 / π) * ∑ j ∈ Finset.range M, sin ((2 * j + 1) * x) / (2 * j + 1) := by
  unfold trigPoly
  have hterm : ∀ k ∈ Finset.Icc 1 (2 * M),
      fourierA squareWave π k * cos (k * π / π * x) + fourierB squareWave π k * sin (k * π / π * x)
        = if Odd k then 4 / π * (sin (k * x) / k) else 0 := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.1 hk).1
    have hkπ : (k:ℝ) * π / π = k := by field_simp
    rw [fourierA_squareWave, fourierB_squareWave hk1, hkπ]
    split_ifs
    · ring
    · simp
  rw [Finset.sum_congr rfl hterm, fourierA_squareWave,
    sum_Icc_two_mul (fun k : ℕ => if Odd k then 4 / π * (sin (k * x) / k) else 0)
      (fun j => by
        have : ¬ Odd (2 * j + 2) := by
          rw [Nat.not_odd_iff_even]
          exact ⟨j + 1, by ring⟩
        simp [this]) M, Finset.mul_sum]
  simp only [zero_div, zero_add]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : Odd (2 * j + 1) := odd_two_mul_add_one j
  simp only [this, ite_true]
  push_cast
  ring

/-! ## The Gibbs phenomenon -/

/-- **Gibbs phenomenon (DE-125).** For the square wave of amplitude 1 (jump of size 2 at `0`),
let `S_M` be the partial sum of its Fourier series through `n = 2M-1` (the `n = 2M` term is
zero, so the code sums through `2M`).  Then (a) `S_M(π/(2M))` tends to
`(2/π) ∫_0^π sin t / t dt` (here `sinc t = sin t / t` with value `1` at `0`); (b) this limit is
larger than `1.17`; (c) hence for all large `M`, `S_M(π/(2M)) > 1.17` while the square wave
equals `1` at `π/(2M)`: the overshoot (about 9% of the jump) does not shrink. -/
@[kb "lebldiffyqs2026" "§4.2 Gibbs phenomenon, p. 205"]
theorem gibbs_phenomenon :
    Tendsto (fun M : ℕ =>
        trigPoly π (fourierA squareWave π) (fourierB squareWave π) (2 * M) (π / (2 * M)))
      atTop (𝓝 ((2 / π) * ∫ t in (0:ℝ)..π, sinc t)) ∧
    1.17 < (2 / π) * ∫ t in (0:ℝ)..π, sinc t ∧
    ∀ᶠ M : ℕ in atTop,
      1.17 < trigPoly π (fourierA squareWave π) (fourierB squareWave π) (2 * M) (π / (2 * M)) ∧
      squareWave (π / (2 * M)) = 1 := by
  have hlim : Tendsto (fun M : ℕ =>
        trigPoly π (fourierA squareWave π) (fourierB squareWave π) (2 * M) (π / (2 * M)))
      atTop (𝓝 ((2 / π) * ∫ t in (0:ℝ)..π, sinc t)) := by
    have h := (tendsto_midpoint_sum continuous_sinc).const_mul (2 / π)
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with M hM
    have hMpos : (0:ℝ) < M := by exact_mod_cast hM
    rw [trigPoly_squareWave, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have ht : (2 * (j:ℝ) + 1) * π / (2 * M) ≠ 0 := by positivity
    have e : (2 * (j:ℝ) + 1) * (π / (2 * M)) = (2 * j + 1) * π / (2 * M) := by ring
    rw [e, sinc_of_ne_zero ht]
    field_simp
    ring
  have hgt := two_div_pi_mul_integral_sinc_gt
  refine ⟨hlim, hgt, ?_⟩
  filter_upwards [hlim.eventually (lt_mem_nhds hgt), eventually_ge_atTop 1] with M hM hM1
  refine ⟨hM, ?_⟩
  have hMpos : (0:ℝ) < M := by exact_mod_cast hM1
  have hpos : 0 < π / (2 * (M:ℝ)) := by positivity
  simp [squareWave, not_le.2 hpos]

end UndergradKB.DifferentialEquations
