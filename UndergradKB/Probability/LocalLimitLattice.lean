import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-!
# Probability: local limit theorem for lattice variables (Grinstead–Snell, Theorem 9.3)

Fourier inversion on the circle for integer-valued random variables and the local limit theorem.
-/

open MeasureTheory Filter Complex Set
open scoped Topology Real

namespace UndergradKB.Probability

namespace LocalLattice

/-- `∫_{-π}^{π} e^{i t m} dt = 2π` if `m = 0` and `0` for a nonzero integer `m`. -/
theorem integral_exp_int (m : ℤ) :
    ∫ t in (-π)..π, cexp (I * t * m) = if m = 0 then (2 * π : ℂ) else 0 := by
  by_cases hm : m = 0
  · subst hm
    simp
    ring
  · simp only [hm, ↓reduceIte]
    have hc : I * (m : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hm)
    have : (fun t : ℝ => cexp (I * t * m)) = fun t : ℝ => cexp ((I * m) * t) := by
      funext t; ring_nf
    rw [this, integral_exp_mul_complex hc, div_eq_zero_iff]
    left
    rw [sub_eq_zero]
    have h1 : cexp (I * m * π) = cexp (I * m * (-π : ℝ)) * cexp (m * (2 * π * I)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [h1, Complex.exp_int_mul_two_pi_mul_I, mul_one]

section Inversion

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Fourier inversion on the circle for an integer-valued random variable:
`P(Y = j) = (1/2π) ∫_{-π}^{π} E[e^{i t (Y - j)}] dt`. -/
theorem inversion (Y : Ω → ℤ) (hY : Measurable Y) (j : ℤ) :
    ((P.real {ω | Y ω = j} : ℝ) : ℂ) =
      (1 / (2 * π) : ℂ) * ∫ t in (-π)..π, ∫ ω, cexp (I * t * ((Y ω - j : ℤ) : ℂ)) ∂P := by
  have hpi : -π ≤ π := by linarith [Real.pi_pos]
  have hmeas : Measurable fun ω => ((Y ω - j : ℤ) : ℂ) :=
    (measurable_of_countable (fun z : ℤ => ((z - j : ℤ) : ℂ))).comp hY
  have hint : Integrable (Function.uncurry fun (t : ℝ) (ω : Ω) => cexp (I * t * ((Y ω - j : ℤ) : ℂ)))
      ((volume.restrict (Ioc (-π) π)).prod P) := by
    refine Integrable.of_bound (C := 1) ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      have : Measurable fun p : ℝ × Ω => I * (p.1 : ℂ) * ((Y p.2 - j : ℤ) : ℂ) := by
        fun_prop
      exact this.cexp
    · refine Eventually.of_forall fun p => ?_
      simp only [Function.uncurry]
      rw [Complex.norm_exp]
      simp
  have hswap : ∫ t in (-π)..π, ∫ ω, cexp (I * t * ((Y ω - j : ℤ) : ℂ)) ∂P =
      ∫ ω, (∫ t in (-π)..π, cexp (I * t * ((Y ω - j : ℤ) : ℂ))) ∂P := by
    rw [intervalIntegral.integral_of_le hpi]
    rw [integral_integral_swap hint]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only
    rw [intervalIntegral.integral_of_le hpi]
  rw [hswap]
  have hinner : ∀ ω, ∫ t in (-π)..π, cexp (I * t * ((Y ω - j : ℤ) : ℂ)) =
      Set.indicator {ω | Y ω = j} (fun _ => (2 * π : ℂ)) ω := by
    intro ω
    rw [integral_exp_int]
    by_cases h : Y ω = j
    · simp [h]
    · have : Y ω - j ≠ 0 := sub_ne_zero.2 h
      simp [h, this]
  simp_rw [hinner]
  have hset : MeasurableSet {ω | Y ω = j} := hY (measurableSet_singleton j)
  rw [integral_indicator hset]
  simp only [setIntegral_const, Measure.real, Complex.real_smul]
  have : (2 * π : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp
  field_simp

end Inversion

section Core

/-- The Gaussian weight `e^{-u²/2}`. -/
noncomputable def gw (u : ℝ) : ℝ := Real.exp (-u ^ 2 / 2)

theorem gw_integrable : Integrable gw := by
  have := integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
  refine this.congr (Eventually.of_forall fun u => ?_)
  simp only [gw]; congr 1; ring

theorem gw_nonneg (u : ℝ) : 0 ≤ gw u := (Real.exp_pos _).le

theorem measurable_gw : Measurable gw := by unfold gw; fun_prop

/-- On `|u| ≤ s₁ √n` the `n`-th power of the (small-argument) characteristic function is below the
Gaussian `e^{-u²/4}`. -/
theorem pow_bound {ψ : ℝ → ℂ} {s1 : ℝ}
    (hsmall : ∀ s, |s| ≤ s1 → ‖ψ s‖ ≤ 1 - s ^ 2 / 4) {n : ℕ} (hn : 0 < n) {u : ℝ}
    (hu : |u| ≤ s1 * √(n : ℝ)) :
    ‖ψ ((√(n : ℝ))⁻¹ * u) ^ n‖ ≤ Real.exp (-u ^ 2 / 4) := by
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  set s := (√(n : ℝ))⁻¹ * u with hs_def
  have hsu : |s| ≤ s1 := by
    rw [hs_def, abs_mul, abs_inv, abs_of_pos hs, inv_mul_le_iff₀ hs]
    rw [mul_comm]; exact hu
  have h1 := hsmall s hsu
  have h2 : (0 : ℝ) ≤ ‖ψ s‖ := norm_nonneg _
  have h3 : ‖ψ s‖ ^ n ≤ (Real.exp (-(s ^ 2 / 4))) ^ n := by
    refine pow_le_pow_left₀ h2 (h1.trans ?_) n
    have := Real.add_one_le_exp (-(s ^ 2 / 4))
    linarith
  rw [norm_pow]
  refine h3.trans (le_of_eq ?_)
  rw [← Real.exp_nat_mul]
  congr 1
  have hsq : √(n : ℝ) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  rw [hs_def, mul_pow, inv_pow, hsq]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-- The `n`-th power of the rescaled characteristic function. -/
noncomputable def psiN (ψ : ℝ → ℂ) (n : ℕ) (u : ℝ) : ℂ := ψ ((√(n : ℝ))⁻¹ * u) ^ n

theorem integrable_gw4 : Integrable fun u : ℝ => Real.exp (-u ^ 2 / 4) := by
  have h : (fun u : ℝ => Real.exp (-u ^ 2 / 4)) = fun u : ℝ => Real.exp (-(1 / 4 : ℝ) * u ^ 2) := by
    funext u; congr 1; ring
  rw [h]
  exact integrable_exp_neg_mul_sq (by norm_num)

theorem gw_le_gw4 (u : ℝ) : gw u ≤ Real.exp (-u ^ 2 / 4) := by
  unfold gw
  refine Real.exp_le_exp.2 ?_
  nlinarith [sq_nonneg u]

section DCT

variable {ψ : ℝ → ℂ}

/-- The pointwise bound on the middle part of the integrand. -/
theorem T1_le {s1 : ℝ}
    (hsmall : ∀ s, |s| ≤ s1 → ‖ψ s‖ ≤ 1 - s ^ 2 / 4) (n : ℕ) (u : ℝ) :
    {u : ℝ | |u| ≤ s1 * √(n : ℝ)}.indicator (fun u => ‖psiN ψ n u - (gw u : ℂ)‖) u ≤
      2 * Real.exp (-u ^ 2 / 4) := by
  by_cases hu : |u| ≤ s1 * √(n : ℝ)
  · rw [Set.indicator_of_mem (show u ∈ {u : ℝ | |u| ≤ s1 * √(n : ℝ)} from hu)]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : u = 0 := by simpa using hu
      subst this
      simp [psiN, gw]
    · have h1 := pow_bound hsmall hn hu
      have h2 := gw_le_gw4 u
      have h3 : ‖psiN ψ n u - (gw u : ℂ)‖ ≤ ‖psiN ψ n u‖ + ‖(gw u : ℂ)‖ := norm_sub_le _ _
      rw [Complex.norm_real, Real.norm_of_nonneg (gw_nonneg u)] at h3
      have h4 : ‖psiN ψ n u‖ ≤ Real.exp (-u ^ 2 / 4) := h1
      linarith
  · rw [Set.indicator_of_notMem (show u ∉ {u : ℝ | |u| ≤ s1 * √(n : ℝ)} from hu)]
    positivity

theorem measurable_psiN (hψm : Measurable ψ) (n : ℕ) : Measurable (psiN ψ n) := by
  unfold psiN
  exact (hψm.comp (measurable_const.mul measurable_id)).pow_const n

theorem tendsto_sqrt_mul_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => c * √(n : ℝ)) atTop atTop :=
  (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hc

theorem tendsto_T1 (hψm : Measurable ψ)
    (hlim : ∀ u : ℝ, Tendsto (fun n : ℕ => psiN ψ n u) atTop (𝓝 ((gw u : ℝ) : ℂ)))
    {s1 : ℝ} (hs1 : 0 < s1) (hsmall : ∀ s, |s| ≤ s1 → ‖ψ s‖ ≤ 1 - s ^ 2 / 4) :
    Tendsto (fun n : ℕ => ∫ u, {u : ℝ | |u| ≤ s1 * √(n : ℝ)}.indicator
      (fun u => ‖psiN ψ n u - (gw u : ℂ)‖) u) atTop (𝓝 0) := by
  have hmeasset : ∀ n : ℕ, MeasurableSet {u : ℝ | |u| ≤ s1 * √(n : ℝ)} := fun n =>
    measurableSet_le (by fun_prop) (by fun_prop)
  have := tendsto_integral_of_dominated_convergence (μ := volume)
    (F := fun (n : ℕ) (u : ℝ) => {u : ℝ | |u| ≤ s1 * √(n : ℝ)}.indicator
      (fun u => ‖psiN ψ n u - (gw u : ℂ)‖) u)
    (f := fun _ => (0 : ℝ)) (fun u => 2 * Real.exp (-u ^ 2 / 4))
    (fun n => by
      refine Measurable.aestronglyMeasurable ?_
      refine Measurable.indicator ?_ (hmeasset n)
      have := measurable_psiN hψm n
      have h2 : Measurable fun u : ℝ => ((gw u : ℝ) : ℂ) := measurable_gw.complex_ofReal
      exact (this.sub h2).norm)
    (integrable_gw4.const_mul 2)
    (fun n => Eventually.of_forall fun u => by
      rw [Real.norm_of_nonneg (Set.indicator_nonneg (fun _ _ => norm_nonneg _) _)]
      exact T1_le hsmall n u)
    (Eventually.of_forall fun u => by
      have h := ((hlim u).sub_const ((gw u : ℝ) : ℂ)).norm
      simp only [sub_self, norm_zero] at h
      refine h.congr' ?_
      filter_upwards [(tendsto_sqrt_mul_atTop hs1).eventually_ge_atTop |u|] with n hn
      rw [Set.indicator_of_mem (show u ∈ {u : ℝ | |u| ≤ s1 * √(n : ℝ)} from hn)])
  simpa using this

theorem tendsto_T3 {s1 : ℝ} (hs1 : 0 < s1) :
    Tendsto (fun n : ℕ => ∫ u, {u : ℝ | |u| ≤ s1 * √(n : ℝ)}ᶜ.indicator gw u) atTop (𝓝 0) := by
  have hmeasset : ∀ n : ℕ, MeasurableSet {u : ℝ | |u| ≤ s1 * √(n : ℝ)}ᶜ := fun n =>
    (measurableSet_le (by fun_prop) (by fun_prop)).compl
  have := tendsto_integral_of_dominated_convergence (μ := volume)
    (F := fun (n : ℕ) (u : ℝ) => {u : ℝ | |u| ≤ s1 * √(n : ℝ)}ᶜ.indicator gw u)
    (f := fun _ => (0 : ℝ)) gw
    (fun n => (measurable_gw.indicator (hmeasset n)).aestronglyMeasurable)
    gw_integrable
    (fun n => Eventually.of_forall fun u => by
      rw [Real.norm_of_nonneg (Set.indicator_nonneg (fun u _ => gw_nonneg u) _)]
      exact Set.indicator_le_self' (fun u _ => gw_nonneg u) u)
    (Eventually.of_forall fun u => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [(tendsto_sqrt_mul_atTop hs1).eventually_ge_atTop |u|] with n hn
      rw [Set.indicator_of_notMem (show u ∉ {u : ℝ | |u| ≤ s1 * √(n : ℝ)}ᶜ by simpa using hn)])
  simpa using this

theorem integral_T2 (a r : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    ∫ u : ℝ, (Icc (-(a * √(n : ℝ))) (a * √(n : ℝ))).indicator (fun _ => r ^ n) u =
      (2 * a * √(n : ℝ)) * r ^ n := by
  rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le (by
    have : 0 ≤ a * √(n : ℝ) := by positivity
    linarith)]
  simp only [smul_eq_mul]
  ring

theorem tendsto_T2 {a r : ℝ} (ha : 0 ≤ a) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (fun n : ℕ => ∫ u : ℝ, (Icc (-(a * √(n : ℝ))) (a * √(n : ℝ))).indicator
      (fun _ => r ^ n) u) atTop (𝓝 0) := by
  simp_rw [integral_T2 a r ha]
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) * r ^ n) atTop (𝓝 0) :=
    tendsto_self_mul_const_pow_of_lt_one hr0 hr1
  have h2 : Tendsto (fun n : ℕ => 2 * a * ((n : ℝ) * r ^ n)) atTop (𝓝 0) := by
    simpa using h1.const_mul (2 * a)
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) h2
  have : √(n : ℝ) ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      calc √(n : ℝ) ≤ √(n : ℝ) * √(n : ℝ) := by
            have := Real.one_le_sqrt.2 this
            nlinarith [Real.sqrt_nonneg (n : ℝ)]
        _ = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
  have hrn : 0 ≤ r ^ n := by positivity
  calc 2 * a * √(n : ℝ) * r ^ n = 2 * a * (√(n : ℝ) * r ^ n) := by ring
    _ ≤ 2 * a * ((n : ℝ) * r ^ n) := by gcongr

theorem pointwise_le {s1 a r : ℝ} (hs1a : s1 ≤ a) (hr0 : 0 ≤ r)
    (hfar : ∀ s, s1 ≤ |s| → |s| ≤ a → ‖ψ s‖ ≤ r) (n : ℕ) (u : ℝ) :
    ‖{u : ℝ | |u| ≤ a * √(n : ℝ)}.indicator (psiN ψ n) u - (gw u : ℂ)‖ ≤
      {u : ℝ | |u| ≤ s1 * √(n : ℝ)}.indicator (fun u => ‖psiN ψ n u - (gw u : ℂ)‖) u +
      (Icc (-(a * √(n : ℝ))) (a * √(n : ℝ))).indicator (fun _ => r ^ n) u +
      {u : ℝ | |u| ≤ s1 * √(n : ℝ)}ᶜ.indicator gw u := by
  have hT1 : 0 ≤ {u : ℝ | |u| ≤ s1 * √(n : ℝ)}.indicator
      (fun u => ‖psiN ψ n u - (gw u : ℂ)‖) u := Set.indicator_nonneg (fun _ _ => norm_nonneg _) _
  have hT2 : 0 ≤ (Icc (-(a * √(n : ℝ))) (a * √(n : ℝ))).indicator (fun _ => r ^ n) u :=
    Set.indicator_nonneg (fun _ _ => by positivity) _
  have hT3 : 0 ≤ {u : ℝ | |u| ≤ s1 * √(n : ℝ)}ᶜ.indicator gw u :=
    Set.indicator_nonneg (fun u _ => gw_nonneg u) _
  have hsq : 0 ≤ √(n : ℝ) := Real.sqrt_nonneg _
  by_cases hB : |u| ≤ s1 * √(n : ℝ)
  · have hA : |u| ≤ a * √(n : ℝ) := hB.trans (mul_le_mul_of_nonneg_right hs1a hsq)
    rw [Set.indicator_of_mem (show u ∈ {u : ℝ | |u| ≤ a * √(n : ℝ)} from hA),
      Set.indicator_of_mem (show u ∈ {u : ℝ | |u| ≤ s1 * √(n : ℝ)} from hB)]
    linarith
  · have hB' : u ∈ {u : ℝ | |u| ≤ s1 * √(n : ℝ)}ᶜ := hB
    rw [Set.indicator_of_mem hB', Set.indicator_of_notMem (show u ∉ {u : ℝ | |u| ≤ s1 * √(n : ℝ)} from hB)]
    by_cases hA : |u| ≤ a * √(n : ℝ)
    · rw [Set.indicator_of_mem (show u ∈ {u : ℝ | |u| ≤ a * √(n : ℝ)} from hA)]
      have hn : 0 < n := by
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp at hA hB
          exact absurd hA (by simpa using hB)
        · exact hn
      have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
      have hmem : u ∈ Icc (-(a * √(n : ℝ))) (a * √(n : ℝ)) := abs_le.1 hA
      rw [Set.indicator_of_mem hmem]
      have h1 : s1 ≤ |(√(n : ℝ))⁻¹ * u| := by
        rw [abs_mul, abs_inv, abs_of_pos hs, le_inv_mul_iff₀ hs]
        linarith [not_le.1 hB]
      have h2 : |(√(n : ℝ))⁻¹ * u| ≤ a := by
        rw [abs_mul, abs_inv, abs_of_pos hs, inv_mul_le_iff₀ hs]
        linarith
      have h3 : ‖psiN ψ n u‖ ≤ r ^ n := by
        unfold psiN
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hfar _ h1 h2) n
      have h4 : ‖psiN ψ n u - (gw u : ℂ)‖ ≤ ‖psiN ψ n u‖ + gw u := by
        have := norm_sub_le (psiN ψ n u) (gw u : ℂ)
        rwa [Complex.norm_real, Real.norm_of_nonneg (gw_nonneg u)] at this
      linarith
    · rw [Set.indicator_of_notMem (show u ∉ {u : ℝ | |u| ≤ a * √(n : ℝ)} from hA)]
      rw [zero_sub, norm_neg, Complex.norm_real, Real.norm_of_nonneg (gw_nonneg u)]
      linarith

/-- The `L¹` distance between the truncated `ψ_n^n` and the Gaussian tends to zero. -/
theorem core_D_tendsto (hψm : Measurable ψ)
    (hlim : ∀ u : ℝ, Tendsto (fun n : ℕ => psiN ψ n u) atTop (𝓝 ((gw u : ℝ) : ℂ)))
    {s1 a r : ℝ} (hs1 : 0 < s1) (hs1a : s1 ≤ a)
    (hsmall : ∀ s, |s| ≤ s1 → ‖ψ s‖ ≤ 1 - s ^ 2 / 4)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hfar : ∀ s, s1 ≤ |s| → |s| ≤ a → ‖ψ s‖ ≤ r) :
    Tendsto (fun n : ℕ => ∫ u, ‖{u : ℝ | |u| ≤ a * √(n : ℝ)}.indicator (psiN ψ n) u -
      (gw u : ℂ)‖) atTop (𝓝 0) := by
  have ha : 0 ≤ a := hs1.le.trans hs1a
  have hsum := ((tendsto_T1 hψm hlim hs1 hsmall).add (tendsto_T2 ha hr0 hr1)).add (tendsto_T3 hs1)
  rw [add_zero, add_zero] at hsum
  refine squeeze_zero (fun n => integral_nonneg fun u => norm_nonneg _) (fun n => ?_) hsum
  have hmeasB : MeasurableSet {u : ℝ | |u| ≤ s1 * √(n : ℝ)} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  have i1 : Integrable fun u => {u : ℝ | |u| ≤ s1 * √(n : ℝ)}.indicator
      (fun u => ‖psiN ψ n u - (gw u : ℂ)‖) u := by
    refine Integrable.mono' (integrable_gw4.const_mul 2) ?_ (Eventually.of_forall fun u => ?_)
    · refine (Measurable.indicator ?_ hmeasB).aestronglyMeasurable
      have h2 : Measurable fun u : ℝ => ((gw u : ℝ) : ℂ) := measurable_gw.complex_ofReal
      exact ((measurable_psiN hψm n).sub h2).norm
    · rw [Real.norm_of_nonneg (Set.indicator_nonneg (fun _ _ => norm_nonneg _) _)]
      exact T1_le hsmall n u
  have i2 : Integrable fun u : ℝ => (Icc (-(a * √(n : ℝ))) (a * √(n : ℝ))).indicator
      (fun _ => r ^ n) u := by
    refine (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
  have i3 : Integrable fun u => {u : ℝ | |u| ≤ s1 * √(n : ℝ)}ᶜ.indicator gw u := by
    refine Integrable.mono' gw_integrable ?_ (Eventually.of_forall fun u => ?_)
    · exact (measurable_gw.indicator hmeasB.compl).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (Set.indicator_nonneg (fun u _ => gw_nonneg u) _)]
      exact Set.indicator_le_self' (fun u _ => gw_nonneg u) u
  calc _ ≤ ∫ u, ({u : ℝ | |u| ≤ s1 * √(n : ℝ)}.indicator
        (fun u => ‖psiN ψ n u - (gw u : ℂ)‖) u +
      (Icc (-(a * √(n : ℝ))) (a * √(n : ℝ))).indicator (fun _ => r ^ n) u +
      {u : ℝ | |u| ≤ s1 * √(n : ℝ)}ᶜ.indicator gw u) :=
        integral_mono_of_nonneg (Eventually.of_forall fun u => norm_nonneg _)
          ((i1.add i2).add i3) (Eventually.of_forall fun u => pointwise_le hs1a hr0 hfar n u)
    _ = _ := by
      refine (integral_add (i1.add i2) i3).trans ?_
      congr 1
      exact integral_add i1 i2

end DCT

/-- Fourier transform of the Gaussian weight. -/
theorem fourier_gw (x : ℝ) :
    ∫ u : ℝ, ((gw u : ℝ) : ℂ) * cexp (-(I * u * x)) = ((√(2 * π) * Real.exp (-x ^ 2 / 2) : ℝ) : ℂ) := by
  have h := fourierIntegral_gaussian (b := (1 / 2 : ℂ)) (by norm_num) (-(x : ℂ))
  have e1 : (fun u : ℝ => ((gw u : ℝ) : ℂ) * cexp (-(I * u * x))) =
      fun u : ℝ => cexp (I * (-(x : ℂ)) * u) * cexp (-(1 / 2 : ℂ) * u ^ 2) := by
    funext u
    unfold gw
    rw [Complex.ofReal_exp, mul_comm]
    congr 2
    · push_cast; ring
    · push_cast; ring
  rw [e1, h]
  have e2 : ((π : ℂ) / (1 / 2 : ℂ)) ^ (1 / 2 : ℂ) = ((√(2 * π) : ℝ) : ℂ) := by
    have : (π : ℂ) / (1 / 2 : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
    rw [this, Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    push_cast
    rfl
  rw [e2, Complex.ofReal_mul, Complex.ofReal_exp]
  congr 2
  push_cast
  ring

theorem norm_cexp_phase (u x : ℝ) : ‖cexp (-(I * u * x))‖ = 1 := by
  have : -(I * (u : ℂ) * x) = ((-(u * x) : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

/-- Uniform (in `x`) closeness of the truncated Fourier integrals to the Fourier transform of the
Gaussian weight. -/
theorem core_uniform {ψ : ℝ → ℂ} (hψm : Measurable ψ) (hψ1 : ∀ s, ‖ψ s‖ ≤ 1)
    (hlim : ∀ u : ℝ, Tendsto (fun n : ℕ => psiN ψ n u) atTop (𝓝 ((gw u : ℝ) : ℂ)))
    {s1 a r : ℝ} (hs1 : 0 < s1) (hs1a : s1 ≤ a)
    (hsmall : ∀ s, |s| ≤ s1 → ‖ψ s‖ ≤ 1 - s ^ 2 / 4)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hfar : ∀ s, s1 ≤ |s| → |s| ≤ a → ‖ψ s‖ ≤ r) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ (n : ℕ) (x : ℝ),
      ‖(∫ u : ℝ, {u : ℝ | |u| ≤ a * √(n : ℝ)}.indicator (psiN ψ n) u * cexp (-(I * u * x))) -
        ((√(2 * π) * Real.exp (-x ^ 2 / 2) : ℝ) : ℂ)‖ ≤ ε n := by
  refine ⟨_, core_D_tendsto hψm hlim hs1 hs1a hsmall hr0 hr1 hfar, fun n x => ?_⟩
  have ha : 0 ≤ a := hs1.le.trans hs1a
  have hmeasA : MeasurableSet {u : ℝ | |u| ≤ a * √(n : ℝ)} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  have hph : Measurable fun u : ℝ => cexp (-(I * (u : ℂ) * x)) := by fun_prop
  have f1 : Integrable fun u : ℝ => {u : ℝ | |u| ≤ a * √(n : ℝ)}.indicator (psiN ψ n) u *
      cexp (-(I * u * x)) := by
    have hbd : Integrable fun u : ℝ => (Icc (-(a * √(n : ℝ))) (a * √(n : ℝ))).indicator
        (fun _ => (1 : ℝ)) u :=
      (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
    refine Integrable.mono' hbd ?_ (Eventually.of_forall fun u => ?_)
    · exact (((measurable_psiN hψm n).indicator hmeasA).mul hph).aestronglyMeasurable
    · rw [norm_mul, norm_cexp_phase, mul_one]
      by_cases hA : |u| ≤ a * √(n : ℝ)
      · rw [Set.indicator_of_mem (show u ∈ {u : ℝ | |u| ≤ a * √(n : ℝ)} from hA),
          Set.indicator_of_mem (show u ∈ Icc (-(a * √(n : ℝ))) (a * √(n : ℝ)) from abs_le.1 hA)]
        unfold psiN
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg _) (hψ1 _)
      · rw [Set.indicator_of_notMem (show u ∉ {u : ℝ | |u| ≤ a * √(n : ℝ)} from hA)]
        simp only [norm_zero]
        exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have f2 : Integrable fun u : ℝ => ((gw u : ℝ) : ℂ) * cexp (-(I * u * x)) := by
    refine Integrable.mono' gw_integrable ?_ (Eventually.of_forall fun u => ?_)
    · exact (measurable_gw.complex_ofReal.mul hph).aestronglyMeasurable
    · rw [norm_mul, norm_cexp_phase, mul_one, Complex.norm_real, Real.norm_of_nonneg (gw_nonneg u)]
  rw [← fourier_gw x, ← integral_sub f1 f2]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  rw [← sub_mul, norm_mul, norm_cexp_phase, mul_one]

end Core

section Aperiodic

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- If `|E e^{itX}| = 1` then `t X - θ ∈ 2π ℤ` on every atom of `X`. -/
theorem lattice_of_norm_eq_one (X : Ω → ℤ) (hX : Measurable X) {t : ℝ}
    (h : ‖∫ ω, cexp (((t * (X ω : ℝ) : ℝ) : ℂ) * I) ∂P‖ = 1) :
    ∃ θ : ℝ, ∀ i : ℤ, 0 < P.real {ω | X ω = i} → ∃ k : ℤ, (k : ℝ) * (2 * π) = t * i - θ := by
  set c := ∫ ω, cexp (((t * (X ω : ℝ) : ℝ) : ℂ) * I) ∂P with hc
  set θ := Complex.arg c with hθ
  refine ⟨θ, fun i hi => ?_⟩
  have hXr : Measurable fun ω => (X ω : ℝ) := (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp hX
  have hint : ∀ θ : ℝ, Integrable (fun ω => cexp (((t * (X ω : ℝ) - θ : ℝ) : ℂ) * I)) P := by
    intro θ
    refine Integrable.of_bound (C := 1) ?_ (Eventually.of_forall fun ω => ?_)
    · exact (((hXr.const_mul t).sub_const θ).complex_ofReal.mul_const I).cexp.aestronglyMeasurable
    · rw [Complex.norm_exp_ofReal_mul_I]
  have hI : ∫ ω, cexp (((t * (X ω : ℝ) - θ : ℝ) : ℂ) * I) ∂P = 1 := by
    have : ∀ ω, cexp (((t * (X ω : ℝ) - θ : ℝ) : ℂ) * I) =
        cexp (-(θ : ℂ) * I) * cexp (((t * (X ω : ℝ) : ℝ) : ℂ) * I) := by
      intro ω; rw [← Complex.exp_add]; congr 1; push_cast; ring
    simp_rw [this]
    rw [integral_const_mul, ← hc]
    have hc' : c = cexp (θ * I) := by
      have := Complex.norm_mul_exp_arg_mul_I c
      rw [h] at this
      simpa using this.symm
    rw [hc', ← Complex.exp_add]
    simp
  have hre : ∫ ω, Real.cos (t * (X ω : ℝ) - θ) ∂P = 1 := by
    have h2 := integral_re (hint θ)
    have h3 : (∫ ω, (cexp (((t * (X ω : ℝ) - θ : ℝ) : ℂ) * I)).re ∂P) =
        ∫ ω, Real.cos (t * (X ω : ℝ) - θ) ∂P :=
      integral_congr_ae (Eventually.of_forall fun ω => Complex.exp_ofReal_mul_I_re _)
    rw [← h3]
    exact h2.trans ((congrArg RCLike.re hI).trans (by simp))
  have hcosint : Integrable (fun ω => Real.cos (t * (X ω : ℝ) - θ)) P := by
    refine Integrable.of_bound (C := 1) ?_ (Eventually.of_forall fun ω => ?_)
    · exact (((hXr.const_mul t).sub_const _).cos).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _
  have h0 : ∫ ω, (1 - Real.cos (t * (X ω : ℝ) - θ)) ∂P = 0 := by
    rw [integral_sub (integrable_const _) hcosint, hre]; simp
  have hae := (integral_eq_zero_iff_of_nonneg (fun ω => sub_nonneg.2 (Real.cos_le_one _))
    ((integrable_const _).sub hcosint)).1 h0
  have hne : P {ω | X ω = i} ≠ 0 := by
    intro h0
    have : P.real {ω | X ω = i} = 0 := by simp [Measure.real, h0]
    linarith
  obtain ⟨ω, hω, hω2⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hne (ae_restrict_of_ae hae)
  have hX' : X ω = i := hω
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at hω2
  rw [hX'] at hω2
  obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff _).1 hω2.symm
  exact ⟨k, hk⟩

/-- The additive subgroup `{m ∈ ℤ | t m ∈ 2π ℤ}`. -/
def periodGroup (t : ℝ) : AddSubgroup ℤ where
  carrier := {m | ∃ k : ℤ, (k : ℝ) * (2 * π) = t * m}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨k, hk⟩ ⟨l, hl⟩
    exact ⟨k + l, by push_cast; linarith⟩
  neg_mem' := by
    rintro a ⟨k, hk⟩
    exact ⟨-k, by push_cast; linarith⟩

/-- Aperiodic lattice law: `|E e^{itX}| < 1` for `0 < t < 2π`, when the gcd of the differences of the
support points of `X` is `1`. -/
theorem norm_lt_one_of_aperiodic (X : Ω → ℤ) (hX : Measurable X)
    (hgcd : ∀ m : ℤ, (∀ i j : ℤ, 0 < P.real {ω | X ω = i} → 0 < P.real {ω | X ω = j} →
      m ∣ i - j) → m ∣ 1) {t : ℝ} (ht0 : t ≠ 0) (ht : |t| < 2 * π) :
    ‖∫ ω, cexp (((t * (X ω : ℝ) : ℝ) : ℂ) * I) ∂P‖ < 1 := by
  have hXr : Measurable fun ω => (X ω : ℝ) := (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp hX
  have hle : ‖∫ ω, cexp (((t * (X ω : ℝ) : ℝ) : ℂ) * I) ∂P‖ ≤ 1 := by
    refine (norm_integral_le_of_norm_le_const (C := 1) (Eventually.of_forall fun ω => ?_)).trans (by simp)
    rw [Complex.norm_exp_ofReal_mul_I]
  refine lt_of_le_of_ne hle fun h => ?_
  obtain ⟨θ, hθ⟩ := lattice_of_norm_eq_one X hX h
  have hdiff : ∀ i j : ℤ, 0 < P.real {ω | X ω = i} → 0 < P.real {ω | X ω = j} →
      (i - j) ∈ periodGroup t := by
    intro i j hi hj
    obtain ⟨k, hk⟩ := hθ i hi
    obtain ⟨l, hl⟩ := hθ j hj
    exact ⟨k - l, by push_cast; linarith⟩
  have hcyc := AddSubgroup.isAddCyclic (periodGroup t)
  obtain ⟨g, hg⟩ := IsAddCyclic.exists_generator (α := periodGroup t)
  have hdvd : (g : ℤ) ∣ 1 := by
    refine hgcd g fun i j hi hj => ?_
    have := hg ⟨i - j, hdiff i j hi hj⟩
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 this
    have hv : ((n • g : periodGroup t) : ℤ) = i - j := congrArg Subtype.val hn
    refine ⟨n, ?_⟩
    rw [← hv]
    simp [mul_comm]
  obtain ⟨c, hc⟩ := hdvd
  have h1 : (1 : ℤ) ∈ periodGroup t := by
    have := (periodGroup t).zsmul_mem g.2 c
    have e : c • (g : ℤ) = 1 := by simp [mul_comm, hc]
    rwa [e] at this
  obtain ⟨k, hk⟩ := h1
  have hk' : (k : ℝ) * (2 * π) = t := by simpa using hk
  have hpi := Real.pi_pos
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk'
    exact ht0 hk'.symm
  have h1k : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk0
  have habs : |t| = |(k : ℝ)| * (2 * π) := by
    rw [← hk', abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  nlinarith

end Aperiodic

section Sums

open ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℤ}

theorem measurable_intCast_real : Measurable (fun z : ℤ => (z : ℝ)) := measurable_of_countable _

/-- The characteristic function of a sum of iid variables is the power of the common one. -/
theorem charFun_sum (hXm : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (n : ℕ) (t : ℝ) :
    charFun (P.map fun ω => ∑ i ∈ Finset.range n, (X i ω : ℝ)) t =
      (charFun (P.map fun ω => (X 0 ω : ℝ)) t) ^ n := by
  have hc := measurable_intCast_real
  have hind : iIndepFun (fun i ω => (X i ω : ℝ)) P :=
    hindep.comp (fun _ => fun z : ℤ => (z : ℝ)) (fun _ => hc)
  have hid : ∀ i, IdentDistrib (fun ω => (X i ω : ℝ)) (fun ω => (X 0 ω : ℝ)) P P :=
    fun i => (hident i).comp hc
  have mX : ∀ i ∈ Finset.range n, AEMeasurable (fun ω => (X i ω : ℝ)) P :=
    fun i _ => (hc.comp (hXm i)).aemeasurable
  rw [(hind.restrict _).charFun_map_fun_finsetSum_eq_prod mX]
  simp [fun i => (hid i).map_eq]

/-- Fourier inversion for the sum `S_n`. -/
theorem inversion_sum (hXm : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (n : ℕ) (j : ℤ) :
    ((P.real {ω | ∑ i ∈ Finset.range n, X i ω = j} : ℝ) : ℂ) =
      (1 / (2 * π) : ℂ) * ∫ t in (-π)..π,
        cexp (-(I * t * j)) * (charFun (P.map fun ω => (X 0 ω : ℝ)) t) ^ n := by
  have hY : Measurable fun ω => ∑ i ∈ Finset.range n, X i ω :=
    Finset.measurable_sum _ (fun i _ => hXm i)
  rw [inversion (fun ω => ∑ i ∈ Finset.range n, X i ω) hY j]
  congr 2
  funext t
  have hc := measurable_intCast_real
  have hYr : AEMeasurable (fun ω => ∑ i ∈ Finset.range n, (X i ω : ℝ)) P :=
    (Finset.measurable_sum _ (fun i _ => hc.comp (hXm i))).aemeasurable
  have h1 : ∀ ω, cexp (I * t * (((∑ i ∈ Finset.range n, X i ω) - j : ℤ) : ℂ)) =
      cexp (-(I * t * j)) * cexp (((t * ∑ i ∈ Finset.range n, (X i ω : ℝ) : ℝ) : ℂ) * I) := by
    intro ω
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [h1]
  rw [integral_const_mul, ← charFun_sum hXm hindep hident n t, charFun_apply_real,
    integral_map hYr (by fun_prop)]
  push_cast
  rfl

/-- Characteristic function of the standardized variable in terms of that of `X`. -/
theorem psi_eq (hXm : Measurable (X 0)) {μ σ : ℝ} (hσ : σ ≠ 0) (s : ℝ) :
    charFun (P.map fun ω => ((X 0 ω : ℝ) - μ) / σ) s =
      cexp (-(((s * μ / σ : ℝ)) : ℂ) * I) * charFun (P.map fun ω => (X 0 ω : ℝ)) (s / σ) := by
  have hc := measurable_intCast_real
  have h1 : AEMeasurable (fun ω => ((X 0 ω : ℝ) - μ) / σ) P :=
    (((hc.comp hXm).sub_const μ).div_const σ).aemeasurable
  have h2 : AEMeasurable (fun ω => (X 0 ω : ℝ)) P := (hc.comp hXm).aemeasurable
  rw [charFun_apply_real, charFun_apply_real, integral_map h1 (by fun_prop),
    integral_map h2 (by fun_prop), ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only
  rw [← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

/-- Change of variables `t = u / (σ √n)` in the inversion integral. -/
theorem change_of_variables (F : ℝ → ℂ) (μ σ : ℝ) (hσ : 0 < σ) (n : ℕ) (hn : 0 < n) (j : ℤ) :
    ((σ * √(n : ℝ) : ℝ) : ℂ) * ∫ t in (-π)..π, cexp (-(I * t * j)) * F t ^ n =
      ∫ u : ℝ, {u : ℝ | |u| ≤ (π * σ) * √(n : ℝ)}.indicator
        (psiN (fun s => cexp (-(((s * μ / σ : ℝ)) : ℂ) * I) * F (s / σ)) n) u *
        cexp (-(I * u * (((j - n * μ) / (σ * √(n : ℝ)) : ℝ) : ℂ))) := by
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsq : √(n : ℝ) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have hpos : 0 < σ * √(n : ℝ) := mul_pos hσ hs
  set g : ℝ → ℂ := fun t => cexp (-(I * t * j)) * F t ^ n with hg
  have h1 : ∫ t in (-π)..π, g t = ∫ t, (Icc (-π) π).indicator g t := by
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
      ← integral_Icc_eq_integral_Ioc, integral_indicator measurableSet_Icc]
  rw [h1]
  have h2 := Measure.integral_comp_mul_left ((Icc (-π) π).indicator g) ((σ * √(n : ℝ))⁻¹)
  rw [inv_inv, abs_of_pos hpos, Complex.real_smul] at h2
  rw [← h2]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  by_cases hu : |u| ≤ (π * σ) * √(n : ℝ)
  · have hmem : (σ * √(n : ℝ))⁻¹ * u ∈ Icc (-π) π := by
      rw [mem_Icc, ← abs_le, abs_mul, abs_inv, abs_of_pos hpos, inv_mul_le_iff₀ hpos]
      calc |u| ≤ π * σ * √(n : ℝ) := hu
        _ = σ * √(n : ℝ) * π := by ring
    rw [Set.indicator_of_mem hmem,
      Set.indicator_of_mem (show u ∈ {u : ℝ | |u| ≤ (π * σ) * √(n : ℝ)} from hu)]
    simp only [hg, psiN]
    have hne : σ ≠ 0 := hσ.ne'
    have hsne : √(n : ℝ) ≠ 0 := hs.ne'
    have hsarg : (√(n : ℝ))⁻¹ * u / σ = (σ * √(n : ℝ))⁻¹ * u := by field_simp
    rw [hsarg, mul_pow, ← Complex.exp_nat_mul]
    have e : cexp (-(I * (((σ * √(n : ℝ))⁻¹ * u : ℝ) : ℂ) * j)) =
        cexp ((n : ℂ) * (-(((((√(n : ℝ))⁻¹ * u) * μ / σ : ℝ)) : ℂ) * I)) *
          cexp (-(I * u * (((j - n * μ) / (σ * √(n : ℝ)) : ℝ) : ℂ))) := by
      rw [← Complex.exp_add]
      congr 1
      have hsqC : ((√(n : ℝ) : ℝ) : ℂ) ^ 2 = n := by exact_mod_cast hsq
      have hsC : ((√(n : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsne
      have hσC : (σ : ℂ) ≠ 0 := by exact_mod_cast hne
      push_cast
      field_simp
      rw [← hsqC]
      ring
    push_cast at e ⊢
    rw [e]
    ring
  · have hmem : (σ * √(n : ℝ))⁻¹ * u ∉ Icc (-π) π := by
      intro h
      apply hu
      rw [mem_Icc, ← abs_le, abs_mul, abs_inv, abs_of_pos hpos, inv_mul_le_iff₀ hpos] at h
      calc |u| ≤ σ * √(n : ℝ) * π := h
        _ = π * σ * √(n : ℝ) := by ring
    rw [Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem (show u ∉ {u : ℝ | |u| ≤ (π * σ) * √(n : ℝ)} from hu)]
    simp

/-- Uniform bound `‖φ(t)‖ ≤ r < 1` away from the origin on `[-π, π]`. -/
theorem far_bound (X : Ω → ℤ) (hX : Measurable X)
    (hgcd : ∀ m : ℤ, (∀ i j : ℤ, 0 < P.real {ω | X ω = i} → 0 < P.real {ω | X ω = j} →
      m ∣ i - j) → m ∣ 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ t : ℝ, δ ≤ |t| → |t| ≤ π →
      ‖charFun (P.map fun ω => (X ω : ℝ)) t‖ ≤ r := by
  have hc := measurable_intCast_real
  have hXr : AEMeasurable (fun ω => (X ω : ℝ)) P := (hc.comp hX).aemeasurable
  have hφ : ∀ t, charFun (P.map fun ω => (X ω : ℝ)) t =
      ∫ ω, cexp (((t * (X ω : ℝ) : ℝ) : ℂ) * I) ∂P := by
    intro t
    rw [charFun_apply_real, integral_map hXr (by fun_prop)]
    push_cast
    rfl
  have hlt : ∀ t : ℝ, δ ≤ |t| → |t| ≤ π → ‖charFun (P.map fun ω => (X ω : ℝ)) t‖ < 1 := by
    intro t h1 h2
    rw [hφ]
    exact norm_lt_one_of_aperiodic X hX hgcd (abs_pos.1 (hδ.trans_le h1))
      (by linarith [Real.pi_pos])
  set K : Set ℝ := Icc (-π) π ∩ {t | δ ≤ |t|} with hK
  have hKc : IsCompact K :=
    isCompact_Icc.inter_right (isClosed_le continuous_const continuous_abs)
  by_cases hne : K.Nonempty
  · have hcont : Continuous fun t => ‖charFun (P.map fun ω => (X ω : ℝ)) t‖ :=
      continuous_charFun.norm
    obtain ⟨t0, ht0, hmax⟩ := hKc.exists_isMaxOn hne hcont.continuousOn
    refine ⟨‖charFun (P.map fun ω => (X ω : ℝ)) t0‖, norm_nonneg _, ?_, fun t h1 h2 => ?_⟩
    · exact hlt t0 ht0.2 (abs_le.2 ht0.1)
    · exact hmax (show t ∈ K from ⟨abs_le.1 h2, h1⟩)
  · refine ⟨0, le_rfl, one_pos, fun t h1 h2 => ?_⟩
    exact absurd ⟨t, abs_le.1 h2, h1⟩ hne

/-- Moments of the standardized variable. -/
theorem standardized_moments (hXm : Measurable (X 0)) {μ σ : ℝ} (hσ : 0 < σ)
    (hL2 : MemLp (fun ω => (X 0 ω : ℝ)) 2 P) (hμ : ∫ ω, (X 0 ω : ℝ) ∂P = μ)
    (hv : Var[fun ω => (X 0 ω : ℝ); P] = σ ^ 2) :
    P[fun ω => ((X 0 ω : ℝ) - μ) / σ] = 0 ∧
      P[(fun ω => ((X 0 ω : ℝ) - μ) / σ) ^ 2] = 1 := by
  have hint : Integrable (fun ω => (X 0 ω : ℝ)) P := hL2.integrable (by norm_num)
  have hc := measurable_intCast_real
  constructor
  · rw [integral_div, integral_sub hint (integrable_const μ), hμ]
    simp
  · have h : Var[fun ω => (X 0 ω : ℝ); P] =
        ∫ ω, ((X 0 ω : ℝ) - ∫ x, (X 0 x : ℝ) ∂P) ^ 2 ∂P :=
      variance_eq_integral (μ := P) (hc.comp hXm).aemeasurable
    rw [hv, hμ] at h
    have : (fun ω => ((X 0 ω : ℝ) - μ) / σ) ^ 2 = fun ω => ((X 0 ω : ℝ) - μ) ^ 2 / σ ^ 2 := by
      funext ω; simp [div_pow]
    rw [this, integral_div, ← h]
    field_simp

/-- Properties of the characteristic function `ψ` of the standardized variable that feed the core
analytic estimate. -/
theorem psi_props (hXm : Measurable (X 0)) {μ σ : ℝ} (hσ : 0 < σ)
    (hL2 : MemLp (fun ω => (X 0 ω : ℝ)) 2 P) (hμ : ∫ ω, (X 0 ω : ℝ) ∂P = μ)
    (hv : Var[fun ω => (X 0 ω : ℝ); P] = σ ^ 2) :
    let ψ : ℝ → ℂ := fun s => charFun (P.map fun ω => ((X 0 ω : ℝ) - μ) / σ) s
    Measurable ψ ∧ (∀ s, ‖ψ s‖ ≤ 1) ∧
      (∀ u : ℝ, Tendsto (fun n : ℕ => psiN ψ n u) atTop (𝓝 ((gw u : ℝ) : ℂ))) ∧
      ∃ s1 : ℝ, 0 < s1 ∧ ∀ s, |s| ≤ s1 → ‖ψ s‖ ≤ 1 - s ^ 2 / 4 := by
  intro ψ
  have hc := measurable_intCast_real
  have hY : AEMeasurable (fun ω => ((X 0 ω : ℝ) - μ) / σ) P :=
    (((hc.comp hXm).sub_const μ).div_const σ).aemeasurable
  obtain ⟨h0, h1⟩ := standardized_moments hXm hσ hL2 hμ hv
  haveI : IsProbabilityMeasure (P.map fun ω => ((X 0 ω : ℝ) - μ) / σ) :=
    ⟨by rw [Measure.map_apply_of_aemeasurable hY MeasurableSet.univ]; simp⟩
  refine ⟨(continuous_charFun).measurable, fun s => norm_charFun_le_one s, fun u => ?_, ?_⟩
  · have := tendsto_charFun_inv_sqrt_mul_pow hY h0 h1 u
    refine this.congr (fun n => rfl) |>.trans_eq ?_
    simp only [gw]
    push_cast
    ring_nf
  · have ho := taylor_charFun_two hY h0 h1
    have hev := ho.def (show (0 : ℝ) < 1 / 4 by norm_num)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
    refine ⟨min (δ / 2) 1, by positivity, fun s hs => ?_⟩
    have hs1 : |s| ≤ δ / 2 := hs.trans (min_le_left _ _)
    have hs2 : |s| ≤ 1 := hs.trans (min_le_right _ _)
    have hb := hball (y := s) (by rw [Real.dist_eq, sub_zero]; linarith)
    simp only [Real.norm_eq_abs, norm_pow, sq_abs] at hb
    have hsq : s ^ 2 ≤ 1 := by nlinarith [abs_nonneg s, sq_abs s]
    have : ψ s = (ψ s - (1 - (s : ℂ) ^ 2 / 2)) + (1 - (s : ℂ) ^ 2 / 2) := by ring
    calc ‖ψ s‖ = ‖(ψ s - (1 - (s : ℂ) ^ 2 / 2)) + (1 - (s : ℂ) ^ 2 / 2)‖ := by rw [← this]
      _ ≤ ‖ψ s - (1 - (s : ℂ) ^ 2 / 2)‖ + ‖(1 - (s : ℂ) ^ 2 / 2)‖ := norm_add_le _ _
      _ ≤ 1 / 4 * s ^ 2 + (1 - s ^ 2 / 2) := by
        refine add_le_add (by simpa using hb) ?_
        have : (1 - (s : ℂ) ^ 2 / 2) = ((1 - s ^ 2 / 2 : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.norm_real, Real.norm_of_nonneg (by nlinarith)]
      _ = 1 - s ^ 2 / 4 := by ring

/-- Main estimate: a uniform bound for the local limit theorem. -/
theorem local_limit_aux (hXm : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hL2 : MemLp (fun ω => (X 0 ω : ℝ)) 2 P) {μ σ : ℝ} (hσ : 0 < σ)
    (hμ : ∫ ω, (X 0 ω : ℝ) ∂P = μ) (hv : Var[fun ω => (X 0 ω : ℝ); P] = σ ^ 2)
    (hgcd : ∀ m : ℤ, (∀ i j : ℤ, 0 < P.real {ω | X 0 ω = i} → 0 < P.real {ω | X 0 ω = j} →
      m ∣ i - j) → m ∣ 1) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ n : ℕ, 0 < n → ∀ j : ℤ,
      |σ * √(n : ℝ) * P.real {ω | ∑ i ∈ Finset.range n, X i ω = j} -
        Real.exp (-(((j - n * μ) / (σ * √(n : ℝ))) ^ 2) / 2) / √(2 * π)| ≤ ε n := by
  obtain ⟨hψm, hψ1, hlim, s1', hs1', hsmall'⟩ := psi_props (hXm 0) hσ hL2 hμ hv
  set ψ : ℝ → ℂ := fun s => charFun (P.map fun ω => ((X 0 ω : ℝ) - μ) / σ) s with hψdef
  have hpi := Real.pi_pos
  set s1 : ℝ := min s1' (π * σ) with hs1def
  have hs1 : 0 < s1 := lt_min hs1' (mul_pos hpi hσ)
  have hs1a : s1 ≤ π * σ := min_le_right _ _
  have hsmall : ∀ s, |s| ≤ s1 → ‖ψ s‖ ≤ 1 - s ^ 2 / 4 := fun s hs =>
    hsmall' s (hs.trans (min_le_left _ _))
  obtain ⟨r, hr0, hr1, hrb⟩ := far_bound (X 0) (hXm 0) hgcd (δ := s1 / σ) (div_pos hs1 hσ)
  have hfar : ∀ s, s1 ≤ |s| → |s| ≤ π * σ → ‖ψ s‖ ≤ r := by
    intro s h1 h2
    have e : ψ s = cexp (-(((s * μ / σ : ℝ)) : ℂ) * I) *
        charFun (P.map fun ω => (X 0 ω : ℝ)) (s / σ) := psi_eq (hXm 0) hσ.ne' s
    have hnorm : ‖cexp (-(((s * μ / σ : ℝ)) : ℂ) * I)‖ = 1 := by
      have : -(((s * μ / σ : ℝ)) : ℂ) * I = ((-(s * μ / σ) : ℝ) : ℂ) * I := by push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    rw [e, norm_mul, hnorm, one_mul]
    apply hrb
    · rw [abs_div, abs_of_pos hσ, le_div_iff₀ hσ, div_mul_cancel₀ _ hσ.ne']
      exact h1
    · rw [abs_div, abs_of_pos hσ, div_le_iff₀ hσ]
      linarith
  obtain ⟨ε, hε, hbound⟩ := core_uniform (a := π * σ) hψm hψ1 hlim hs1 hs1a hsmall hr0 hr1 hfar
  refine ⟨fun n => ε n / (2 * π), by simpa using hε.div_const (2 * π), fun n hn j => ?_⟩
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hψeq : ψ = fun s => cexp (-(((s * μ / σ : ℝ)) : ℂ) * I) *
      charFun (P.map fun ω => (X 0 ω : ℝ)) (s / σ) := by
    funext s; exact psi_eq (hXm 0) hσ.ne' s
  set x : ℝ := (j - n * μ) / (σ * √(n : ℝ)) with hx
  have key := change_of_variables (charFun (P.map fun ω => (X 0 ω : ℝ))) μ σ hσ n hn j
  rw [← hψeq] at key
  have inv := inversion_sum hXm hindep hident n j
  have hJ := hbound n x
  have e1 : ((σ * √(n : ℝ) * P.real {ω | ∑ i ∈ Finset.range n, X i ω = j} : ℝ) : ℂ) =
      (1 / (2 * π) : ℂ) * ∫ u : ℝ, {u : ℝ | |u| ≤ (π * σ) * √(n : ℝ)}.indicator (psiN ψ n) u *
        cexp (-(I * u * (x : ℂ))) := by
    rw [← key, Complex.ofReal_mul, inv]
    ring
  have h2pi : (0 : ℝ) < 2 * π := by positivity
  have hsq : √(2 * π) * √(2 * π) = 2 * π := Real.mul_self_sqrt h2pi.le
  have e2 : ((Real.exp (-x ^ 2 / 2) / √(2 * π) : ℝ) : ℂ) =
      (1 / (2 * π) : ℂ) * ((√(2 * π) * Real.exp (-x ^ 2 / 2) : ℝ) : ℂ) := by
    have hne : (√(2 * π) : ℝ) ≠ 0 := (Real.sqrt_pos.2 h2pi).ne'
    have hneC : ((√(2 * π) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hne
    have hsqC : ((√(2 * π) : ℝ) : ℂ) * ((√(2 * π) : ℝ) : ℂ) = 2 * π := by exact_mod_cast hsq
    have hpiC : (π : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
    push_cast
    rw [← hsqC]
    field_simp
  have hnorm : |σ * √(n : ℝ) * P.real {ω | ∑ i ∈ Finset.range n, X i ω = j} -
        Real.exp (-x ^ 2 / 2) / √(2 * π)| =
      ‖(1 / (2 * π) : ℂ) * ((∫ u : ℝ, {u : ℝ | |u| ≤ (π * σ) * √(n : ℝ)}.indicator (psiN ψ n) u *
        cexp (-(I * u * (x : ℂ)))) - ((√(2 * π) * Real.exp (-x ^ 2 / 2) : ℝ) : ℂ))‖ := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, Complex.ofReal_sub, e1, e2, mul_sub]
  rw [hnorm, norm_mul]
  have : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
    rw [norm_div, norm_one]
    have : ‖(2 * π : ℂ)‖ = 2 * π := by
      have : (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; rfl
      rw [this, Complex.norm_real, Real.norm_of_nonneg h2pi.le]
    rw [this]
  rw [this]
  calc 1 / (2 * π) * _ ≤ 1 / (2 * π) * ε n := by gcongr
    _ = ε n / (2 * π) := by ring

end Sums

end LocalLattice

open ProbabilityTheory LocalLattice in
/-- Grinstead–Snell Theorem 9.3 (PR-099), uniform form. Let `X₀, X₁, …` be independent identically
distributed integer-valued random variables with mean `μ` and variance `σ² > 0`, such that the greatest
common divisor of the differences of the values they take with positive probability is `1`
(every common divisor `m` of all these differences divides `1`). Put `S_n = X₀ + ⋯ + X_{n-1}` and
`x_j = (j - n μ) / (σ √n)`. Then `σ √n P(S_n = j) - φ(x_j)` tends to `0` uniformly in `j ∈ ℤ`,
where `φ(x) = e^{-x²/2} / √(2π)`: there is `ε_n → 0` bounding it for all `j` and all `n ≥ 1`. -/
@[kb "grinsteadsnell2006" "Theorem 9.3, p. 350"]
theorem local_limit_lattice {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℤ} (hXm : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hL2 : MemLp (fun ω => (X 0 ω : ℝ)) 2 P) {μ σ : ℝ} (hσ : 0 < σ)
    (hμ : ∫ ω, (X 0 ω : ℝ) ∂P = μ) (hv : Var[fun ω => (X 0 ω : ℝ); P] = σ ^ 2)
    (hgcd : ∀ m : ℤ, (∀ i j : ℤ, 0 < P.real {ω | X 0 ω = i} → 0 < P.real {ω | X 0 ω = j} →
      m ∣ i - j) → m ∣ 1) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ n : ℕ, 0 < n → ∀ j : ℤ,
      |σ * √(n : ℝ) * P.real {ω | ∑ i ∈ Finset.range n, X i ω = j} -
        Real.exp (-(((j - n * μ) / (σ * √(n : ℝ))) ^ 2) / 2) / √(2 * π)| ≤ ε n :=
  local_limit_aux hXm hindep hident hL2 hσ hμ hv hgcd

open ProbabilityTheory LocalLattice in
/-- Grinstead–Snell Theorem 9.3 (PR-099), asymptotic-equivalence form: if the standardized positions
`x_{j_n} = (j_n - n μ) / (σ √n)` stay bounded, then `P(S_n = j_n) ∼ φ(x_{j_n}) / (σ √n)`, i.e. the ratio
`σ √n P(S_n = j_n) / φ(x_{j_n})` tends to `1`. -/
@[kb "grinsteadsnell2006" "Theorem 9.3, p. 350"]
theorem local_limit_lattice_ratio {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ℕ → Ω → ℤ} (hXm : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hL2 : MemLp (fun ω => (X 0 ω : ℝ)) 2 P) {μ σ : ℝ} (hσ : 0 < σ)
    (hμ : ∫ ω, (X 0 ω : ℝ) ∂P = μ) (hv : Var[fun ω => (X 0 ω : ℝ); P] = σ ^ 2)
    (hgcd : ∀ m : ℤ, (∀ i j : ℤ, 0 < P.real {ω | X 0 ω = i} → 0 < P.real {ω | X 0 ω = j} →
      m ∣ i - j) → m ∣ 1) {j : ℕ → ℤ} {M : ℝ}
    (hM : ∀ n : ℕ, 0 < n → |((j n : ℝ) - n * μ) / (σ * √(n : ℝ))| ≤ M) :
    Tendsto (fun n : ℕ => σ * √(n : ℝ) * P.real {ω | ∑ i ∈ Finset.range n, X i ω = j n} /
      (Real.exp (-((((j n : ℝ) - n * μ) / (σ * √(n : ℝ))) ^ 2) / 2) / √(2 * π))) atTop (𝓝 1) := by
  obtain ⟨ε, hε, hb⟩ := local_limit_aux hXm hindep hident hL2 hσ hμ hv hgcd
  have h2pi : (0 : ℝ) < 2 * π := by positivity
  have hsq : 0 < √(2 * π) := Real.sqrt_pos.2 h2pi
  set c : ℝ := Real.exp (-M ^ 2 / 2) / √(2 * π) with hc
  have hcpos : 0 < c := by positivity
  have hlim : Tendsto (fun n : ℕ => ε n / c) atTop (𝓝 0) := by simpa using hε.div_const c
  have h0 : Tendsto (fun n : ℕ => σ * √(n : ℝ) * P.real {ω | ∑ i ∈ Finset.range n, X i ω = j n} /
      (Real.exp (-((((j n : ℝ) - n * μ) / (σ * √(n : ℝ))) ^ 2) / 2) / √(2 * π)) - 1) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_gt_atTop 0] with n hn
    set x : ℝ := ((j n : ℝ) - n * μ) / (σ * √(n : ℝ)) with hx
    set g : ℝ := Real.exp (-x ^ 2 / 2) / √(2 * π) with hg
    have hxM : |x| ≤ M := hM n hn
    have hgc : c ≤ g := by
      rw [hg, hc]
      have : x ^ 2 ≤ M ^ 2 := by
        rw [← sq_abs x]; exact pow_le_pow_left₀ (abs_nonneg _) hxM 2
      exact div_le_div_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) hsq.le
    have hgpos : 0 < g := hcpos.trans_le hgc
    have hbn := hb n hn (j n)
    rw [Real.norm_eq_abs]
    calc |σ * √(n : ℝ) * P.real {ω | ∑ i ∈ Finset.range n, X i ω = j n} / g - 1|
        = |σ * √(n : ℝ) * P.real {ω | ∑ i ∈ Finset.range n, X i ω = j n} - g| / g := by
          rw [← abs_of_pos hgpos, ← abs_div, abs_of_pos hgpos]
          congr 1
          field_simp
      _ ≤ ε n / g := div_le_div_of_nonneg_right hbn hgpos.le
      _ ≤ ε n / c := div_le_div_of_nonneg_left ((abs_nonneg _).trans hbn) hcpos hgc
  simpa using h0.add_const 1

end UndergradKB.Probability
