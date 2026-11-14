import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.Variance
import UndergradKB.Common.Attr
import UndergradKB.Statistics.FDistribution

/-!
# Shape of the chi-square and F distributions (OpenStax *Introductory Statistics 2e*, §11.1, §13.3)

The book describes both curves as skewed to the right, and gives the mean of the F distribution as
`d₂/(d₂ - 2)` (close to one when the denominator degrees of freedom are large). We prove:

* the third central moment of the chi-square law with `k` degrees of freedom is `8k > 0`, and its skewness
  coefficient `μ₃/σ³ = 4/√(2k)` is positive and tends to `0` as `k` grows (`chiSquared_right_skewed`);
* the moments of the F law, `E[Fᵖ] = (d₂/d₁)ᵖ Γ(d₁/2 + p) Γ(d₂/2 - p) / (Γ(d₁/2) Γ(d₂/2))` for
  `-d₁/2 < p < d₂/2`, from the representation `F = (U/d₁)/(V/d₂)` (`lintegral_rpow_fDistribution`);
* the mean `d₂/(d₂ - 2)` for `d₂ > 2`, tending to `1` as `d₂ → ∞` (`integral_id_fDistribution`,
  `tendsto_integral_id_fDistribution`); the variance `2 d₂² (d₁ + d₂ - 2) / (d₁ (d₂ - 2)² (d₂ - 4))` for `d₂ > 4`;
  and the third central moment `8 d₂³ (d₁ + d₂ - 2)(2 d₁ + d₂ - 2) / (d₁² (d₂ - 2)³ (d₂ - 4)(d₂ - 6)) > 0`
  for `d₂ > 6` (`fDistribution_right_skewed`).
-/

namespace UndergradKB.Statistics

open MeasureTheory ProbabilityTheory Real Set Filter Topology

/-! ### Third central moment of a law on `ℝ` -/

/-- `E[(X - m)³] = E[X³] - 3 m E[X²] + 2 m³` with `m = E[X]`. -/
lemma centralMoment_id_three {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h1 : Integrable (fun x ↦ x) μ) (h2 : Integrable (fun x ↦ x ^ 2) μ)
    (h3 : Integrable (fun x ↦ x ^ 3) μ) :
    centralMoment id 3 μ =
      ∫ x, x ^ 3 ∂μ - 3 * (∫ x, x ∂μ) * ∫ x, x ^ 2 ∂μ + 2 * (∫ x, x ∂μ) ^ 3 := by
  set m := ∫ x, x ∂μ with hm
  have e : (fun x : ℝ ↦ (x - m) ^ 3) =
      fun x ↦ (x ^ 3 - (3 * m) * x ^ 2) + ((3 * m ^ 2) * x - m ^ 3) := by
    funext x; ring
  have hc : centralMoment id 3 μ = ∫ x, (x - m) ^ 3 ∂μ := by
    simp only [centralMoment, Pi.pow_apply, Pi.sub_apply, id]
    rfl
  have i1' : Integrable (fun x : ℝ ↦ x ^ 3 - (3 * m) * x ^ 2) μ := h3.sub (h2.const_mul _)
  have i2' : Integrable (fun x : ℝ ↦ (3 * m ^ 2) * x - m ^ 3) μ := (h1.const_mul _).sub (integrable_const _)
  rw [hc, e, integral_add i1' i2',
    integral_sub h3 (h2.const_mul _), integral_sub (h1.const_mul _) (integrable_const _),
    integral_const_mul, integral_const_mul, integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  rw [← hm]
  ring

/-! ### The chi-square law is skewed to the right -/

/-- **Third central moment of the chi-square law**: `E[(X - k)³] = 8k`. -/
theorem centralMoment_three_chiSquared {k : ℝ} (hk : 0 < k) : centralMoment id 3 (chiSquared k) = 8 * k := by
  have := isProbabilityMeasure_chiSquared' hk
  have ha : 0 < k / 2 := by positivity
  have hG := Gamma_pos_of_pos ha
  obtain ⟨i1, e1⟩ := integral_pow_gammaMeasure (a := k / 2) (r := 1 / 2) ha (by norm_num) 1
  obtain ⟨i2, e2⟩ := integral_pow_gammaMeasure (a := k / 2) (r := 1 / 2) ha (by norm_num) 2
  obtain ⟨i3, e3⟩ := integral_pow_gammaMeasure (a := k / 2) (r := 1 / 2) ha (by norm_num) 3
  simp only [pow_one] at i1 e1
  have g1 : Gamma (k / 2 + ((1 : ℕ) : ℝ)) = k / 2 * Gamma (k / 2) := by
    rw [Nat.cast_one, Gamma_add_one ha.ne']
  have g2 : Gamma (k / 2 + ((2 : ℕ) : ℝ)) = (k / 2 + 1) * (k / 2) * Gamma (k / 2) := by
    rw [show k / 2 + ((2 : ℕ) : ℝ) = (k / 2 + 1) + 1 by norm_num; ring,
      Gamma_add_one (by positivity), Gamma_add_one ha.ne']
    ring
  have g3 : Gamma (k / 2 + ((3 : ℕ) : ℝ)) = (k / 2 + 2) * (k / 2 + 1) * (k / 2) * Gamma (k / 2) := by
    rw [show k / 2 + ((3 : ℕ) : ℝ) = (k / 2 + 2) + 1 by norm_num; ring, Gamma_add_one (by positivity),
      show k / 2 + 2 = (k / 2 + 1) + 1 by ring, Gamma_add_one (by positivity), Gamma_add_one ha.ne']
    ring
  have p1 : ((1 : ℝ) / 2) ^ ((1 : ℕ) : ℝ) = 1 / 2 := by norm_num
  have p2 : ((1 : ℝ) / 2) ^ ((2 : ℕ) : ℝ) = 1 / 4 := by norm_num
  have p3 : ((1 : ℝ) / 2) ^ ((3 : ℕ) : ℝ) = 1 / 8 := by norm_num
  rw [g1, p1] at e1
  rw [g2, p2] at e2
  rw [g3, p3] at e3
  have E1 : ∫ x, x ∂(gammaMeasure (k / 2) (1 / 2)) = k := by
    rw [e1]; field_simp
  have E2 : ∫ x, x ^ 2 ∂(gammaMeasure (k / 2) (1 / 2)) = k * (k + 2) := by
    rw [e2]; field_simp; ring
  have E3 : ∫ x, x ^ 3 ∂(gammaMeasure (k / 2) (1 / 2)) = k * (k + 2) * (k + 4) := by
    rw [e3]; field_simp; ring
  have : IsProbabilityMeasure (gammaMeasure (k / 2) (1 / 2)) := this
  change centralMoment id 3 (gammaMeasure (k / 2) (1 / 2)) = 8 * k
  rw [centralMoment_id_three i1 i2 i3, E1, E2, E3]
  ring

/-- **The chi-square curve is skewed to the right and becomes symmetric** (§11.1, ST-096). The chi-square law
with `k` degrees of freedom has positive third central moment `8k`, and its skewness coefficient
`E[(X - k)³]/σ³` equals `4/√(2k)`, which is positive and tends to `0` as `k` grows. -/
@[kb "openstaxintrostats2e" "§11.1, p. 575"]
theorem chiSquared_right_skewed {k : ℝ} (hk : 0 < k) :
    0 < centralMoment id 3 (chiSquared k) ∧
      centralMoment id 3 (chiSquared k) / √(variance id (chiSquared k)) ^ 3 = 4 / √(2 * k) ∧
      Tendsto (fun k : ℝ ↦ 4 / √(2 * k)) atTop (𝓝 0) := by
  refine ⟨by rw [centralMoment_three_chiSquared hk]; positivity, ?_, ?_⟩
  · rw [centralMoment_three_chiSquared hk, variance_id_chiSquared hk]
    have hs : 0 < √(2 * k) := Real.sqrt_pos.2 (by positivity)
    have h2 : √(2 * k) ^ 2 = 2 * k := Real.sq_sqrt (by positivity)
    rw [show √(2 * k) ^ 3 = 2 * k * √(2 * k) by rw [pow_succ, h2]]
    field_simp
    ring
  · have h : Tendsto (fun k : ℝ ↦ √(2 * k)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp (tendsto_id.const_mul_atTop two_pos)
    exact tendsto_const_nhds.div_atTop h

/-! ### Moments of the F law -/

/-- The gamma law has no mass on `(-∞, 0]`. -/
lemma ae_pos_gammaMeasure (a r : ℝ) : ∀ᵐ x ∂(gammaMeasure a r), 0 < x := by
  have hm : Measurable (gammaPDF a r) := (measurable_gammaPDFReal a r).ennreal_ofReal
  rw [gammaMeasure, ae_withDensity_iff hm]
  have h0 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by
    rw [ae_iff]
    simp
  filter_upwards [h0] with x hx0 hx
  rcases lt_or_gt_of_ne hx0 with h | h
  · exact absurd (gammaPDF_of_neg h) hx
  · exact h

/-- Moments of the gamma law with a real exponent: `∫ x^p dΓ(a, r) = Γ(a + p) / (Γ(a) r^p)` for
`a + p > 0`. -/
lemma lintegral_rpow_gammaMeasure' {a r p : ℝ} (ha : 0 < a) (hr : 0 < r) (hp : 0 < a + p) :
    ∫⁻ x, ENNReal.ofReal (max x 0 ^ p) ∂(gammaMeasure a r) =
      ENNReal.ofReal (Gamma (a + p) / (Gamma a * r ^ p)) := by
  rw [lintegral_gammaMeasure a r (by fun_prop)]
  have hG : 0 < Gamma a := Gamma_pos_of_pos ha
  calc ∫⁻ x in Ioi 0, ENNReal.ofReal (r ^ a / Gamma a * x ^ (a - 1) * exp (-(r * x))) *
          ENNReal.ofReal (max x 0 ^ p)
      = ∫⁻ x in Ioi 0, ENNReal.ofReal (r ^ a / Gamma a) *
          ENNReal.ofReal (x ^ (a + p - 1) * exp (-(r * x))) := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun x (hx : 0 < x) ↦ ?_
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          max_eq_left hx.le]
        congr 1
        rw [show a + p - 1 = (a - 1) + p by ring, rpow_add hx]
        ring
    _ = ENNReal.ofReal (r ^ a / Gamma a) * ENNReal.ofReal ((1 / r) ^ (a + p) * Gamma (a + p)) := by
        rw [lintegral_const_mul _ (by fun_prop), lintegral_rpow_mul_exp_neg_mul_Ioi hp hr]
    _ = ENNReal.ofReal (Gamma (a + p) / (Gamma a * r ^ p)) := by
        have := Gamma_pos_of_pos hp
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [div_rpow zero_le_one hr.le, one_rpow, rpow_add hr]
        field_simp

/-- **Moments of the F law** (real exponent `p` with `-d₁/2 < p < d₂/2`):
`E[Fᵖ] = (d₂/d₁)ᵖ Γ(d₁/2 + p) Γ(d₂/2 - p) / (Γ(d₁/2) Γ(d₂/2))`, from `F = (U/d₁)/(V/d₂)`. -/
theorem lintegral_rpow_fDistribution {d₁ d₂ p : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hp₁ : 0 < d₁ / 2 + p)
    (hp₂ : 0 < d₂ / 2 - p) :
    ∫⁻ x, ENNReal.ofReal (max x 0 ^ p) ∂(fDistribution d₁ d₂) =
      ENNReal.ofReal ((d₂ / d₁) ^ p * (Gamma (d₁ / 2 + p) * Gamma (d₂ / 2 - p)) /
        (Gamma (d₁ / 2) * Gamma (d₂ / 2))) := by
  have := isProbabilityMeasure_chiSquared' hd₁
  have := isProbabilityMeasure_chiSquared' hd₂
  have hG1 := Gamma_pos_of_pos (by positivity : 0 < d₁ / 2)
  have hG2 := Gamma_pos_of_pos (by positivity : 0 < d₂ / 2)
  have hG3 := Gamma_pos_of_pos hp₁
  have hG4 := Gamma_pos_of_pos hp₂
  rw [fDistribution, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  simp only [Pi.mul_apply]
  rw [← lintegral_f_ratio hd₁ hd₂ (F := fun x ↦ ENNReal.ofReal (max x 0 ^ p)) (by fun_prop)]
  have hae : ∀ᵐ q ∂((chiSquared d₁).prod (chiSquared d₂)), 0 < q.1 ∧ 0 < q.2 := by
    have h1 := (Measure.quasiMeasurePreserving_fst (μ := chiSquared d₁) (ν := chiSquared d₂)).ae
      (ae_pos_gammaMeasure (d₁ / 2) (1 / 2))
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := chiSquared d₁) (ν := chiSquared d₂)).ae
      (ae_pos_gammaMeasure (d₂ / 2) (1 / 2))
    filter_upwards [h1, h2] with q hq1 hq2 using ⟨hq1, hq2⟩
  rw [lintegral_congr_ae (g := fun q : ℝ × ℝ ↦ ENNReal.ofReal ((d₂ / d₁) ^ p) *
      (ENNReal.ofReal (max q.1 0 ^ p) * ENNReal.ofReal (max q.2 0 ^ (-p)))) ?_]
  · rw [lintegral_const_mul _ (by fun_prop),
      lintegral_prod_mul (f := fun x ↦ ENNReal.ofReal (max x 0 ^ p))
        (g := fun y ↦ ENNReal.ofReal (max y 0 ^ (-p))) (by fun_prop) (by fun_prop)]
    unfold chiSquared
    rw [lintegral_rpow_gammaMeasure' (by positivity) (by norm_num) hp₁,
      lintegral_rpow_gammaMeasure' (by positivity) (by norm_num) (by linarith),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [← sub_eq_add_neg, rpow_neg (by norm_num)]
    have : (0 : ℝ) < (1 / 2) ^ p := by positivity
    field_simp
  · filter_upwards [hae] with q ⟨hq1, hq2⟩
    have hr : 0 < (q.1 / d₁) / (q.2 / d₂) := by positivity
    rw [max_eq_left hr.le, max_eq_left hq1.le, max_eq_left hq2.le, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [show (q.1 / d₁) / (q.2 / d₂) = (d₂ / d₁) * (q.1 * q.2⁻¹) by field_simp,
      mul_rpow (by positivity) (by positivity), mul_rpow hq1.le (by positivity),
      inv_rpow hq2.le, rpow_neg hq2.le]

/-- The F law has no mass on `(-∞, 0]`. -/
lemma ae_pos_fDistribution (d₁ d₂ : ℝ) : ∀ᵐ x ∂(fDistribution d₁ d₂), 0 < x := by
  rw [ae_iff]
  convert fDistribution_Iic_zero d₁ d₂ using 2
  ext x
  simp

/-- Integer moments of the F law: for `2n < d₂`, `x ↦ xⁿ` is integrable and
`E[Fⁿ] = (d₂/d₁)ⁿ Γ(d₁/2 + n) Γ(d₂/2 - n) / (Γ(d₁/2) Γ(d₂/2))`. -/
theorem integral_pow_fDistribution {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (n : ℕ)
    (hn : 2 * (n : ℝ) < d₂) :
    Integrable (fun x ↦ x ^ n) (fDistribution d₁ d₂) ∧
      ∫ x, x ^ n ∂(fDistribution d₁ d₂) = (d₂ / d₁) ^ n * (Gamma (d₁ / 2 + n) * Gamma (d₂ / 2 - n)) /
        (Gamma (d₁ / 2) * Gamma (d₂ / 2)) := by
  have hG1 := Gamma_pos_of_pos (by positivity : 0 < d₁ / 2)
  have hG2 := Gamma_pos_of_pos (by positivity : 0 < d₂ / 2)
  have hG3 := Gamma_pos_of_pos (by positivity : 0 < d₁ / 2 + n)
  have hG4 := Gamma_pos_of_pos (by linarith : 0 < d₂ / 2 - n)
  have hae : (fun x : ℝ ↦ x ^ n) =ᵐ[fDistribution d₁ d₂] fun x ↦ max x 0 ^ (n : ℝ) := by
    filter_upwards [ae_pos_fDistribution d₁ d₂] with x hx
    rw [max_eq_left hx.le, rpow_natCast]
  have h := integrable_integral_of_lintegral (μ := fDistribution d₁ d₂) (f := fun x ↦ max x 0 ^ (n : ℝ))
    (by fun_prop) (ae_of_all _ fun x ↦ rpow_nonneg (le_max_right _ _) _) (by positivity)
    (lintegral_rpow_fDistribution hd₁ hd₂ (by positivity) (by linarith))
  refine ⟨h.1.congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, h.2, rpow_natCast]

/-- **Mean of the F distribution** (§13.3, ST-116): for `d₂ > 2` the F law with `d₁`, `d₂` degrees of freedom
has mean `d₂/(d₂ - 2)`. -/
@[kb "openstaxintrostats2e" "§13.3, p. 695"]
theorem integral_id_fDistribution {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 2 < d₂) :
    Integrable (fun x ↦ x) (fDistribution d₁ d₂) ∧ ∫ x, x ∂(fDistribution d₁ d₂) = d₂ / (d₂ - 2) := by
  obtain ⟨hi, he⟩ := integral_pow_fDistribution hd₁ (by linarith) 1 (by norm_num; linarith)
  simp only [pow_one, Nat.cast_one] at hi he
  refine ⟨hi, ?_⟩
  have hb : 0 < d₂ / 2 - 1 := by linarith
  have hGb := Gamma_pos_of_pos hb
  have hG1 := Gamma_pos_of_pos (by positivity : 0 < d₁ / 2)
  rw [he, Gamma_add_one (by positivity : d₁ / 2 ≠ 0),
    show d₂ / 2 = (d₂ / 2 - 1) + 1 by ring, Gamma_add_one hb.ne']
  have : d₂ - 2 ≠ 0 := by linarith
  field_simp
  ring

/-- **The mean of the F distribution is close to one for large denominator degrees of freedom** (§13.3,
ST-116): `E[F] = d₂/(d₂ - 2) → 1` as `d₂ → ∞`. -/
@[kb "openstaxintrostats2e" "§13.3, p. 695"]
theorem tendsto_integral_id_fDistribution {d₁ : ℝ} (hd₁ : 0 < d₁) :
    Tendsto (fun d₂ : ℝ ↦ ∫ x, x ∂(fDistribution d₁ d₂)) atTop (𝓝 1) := by
  have h : Tendsto (fun d₂ : ℝ ↦ 1 + 2 / (d₂ - 2)) atTop (𝓝 1) := by
    have : Tendsto (fun d₂ : ℝ ↦ d₂ - 2) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
    have h1 := ((tendsto_const_nhds (x := (2 : ℝ))).div_atTop this).const_add 1
    rwa [add_zero] at h1
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 2] with d₂ hd₂
  rw [(integral_id_fDistribution hd₁ hd₂).2]
  have : d₂ - 2 ≠ 0 := by linarith
  field_simp
  ring

/-- Second moment of the F law: `E[F²] = d₂² (d₁ + 2) / (d₁ (d₂ - 2)(d₂ - 4))` for `d₂ > 4`. -/
lemma integral_sq_fDistribution {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 4 < d₂) :
    Integrable (fun x ↦ x ^ 2) (fDistribution d₁ d₂) ∧
      ∫ x, x ^ 2 ∂(fDistribution d₁ d₂) = d₂ ^ 2 * (d₁ + 2) / (d₁ * (d₂ - 2) * (d₂ - 4)) := by
  obtain ⟨hi, he⟩ := integral_pow_fDistribution hd₁ (by linarith) 2 (by norm_num; linarith)
  rw [show ((2 : ℕ) : ℝ) = 2 by norm_num] at he
  refine ⟨hi, ?_⟩
  have hG1 := Gamma_pos_of_pos (by positivity : 0 < d₁ / 2)
  have g1 : Gamma (d₁ / 2 + 2) = (d₁ / 2 + 1) * (d₁ / 2) * Gamma (d₁ / 2) := by
    rw [show d₁ / 2 + 2 = (d₁ / 2 + 1) + 1 by ring,
      Gamma_add_one (by positivity), Gamma_add_one (by positivity)]
    ring
  obtain ⟨c, rfl⟩ : ∃ c, d₂ = 2 * c + 4 := ⟨(d₂ - 4) / 2, by ring⟩
  have hc : 0 < c := by linarith
  have hGc := Gamma_pos_of_pos hc
  rw [show (2 * c + 4) / 2 - 2 = c by ring, show (2 * c + 4) / 2 = (c + 1) + 1 by ring,
    Gamma_add_one (s := c + 1) (by positivity), Gamma_add_one (s := c) hc.ne', g1] at he
  rw [he, show 2 * c + 4 - 2 = 2 * (c + 1) by ring, show 2 * c + 4 - 4 = 2 * c by ring]
  generalize Gamma c = G at hGc ⊢
  generalize Gamma (d₁ / 2) = G₁ at hG1 ⊢
  rw [div_pow, div_mul_eq_mul_div, div_div, div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- **Variance of the F distribution** (§13.3): for `d₂ > 4`,
`Var F = 2 d₂² (d₁ + d₂ - 2) / (d₁ (d₂ - 2)² (d₂ - 4))`. -/
@[kb "openstaxintrostats2e" "§13.3, p. 695"]
theorem variance_id_fDistribution {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 4 < d₂) :
    variance id (fDistribution d₁ d₂) = 2 * d₂ ^ 2 * (d₁ + d₂ - 2) / (d₁ * (d₂ - 2) ^ 2 * (d₂ - 4)) := by
  have := isProbabilityMeasure_fDistribution hd₁ (by linarith : 0 < d₂)
  obtain ⟨i2, e2⟩ := integral_sq_fDistribution hd₁ hd₂
  have hm : MemLp id 2 (fDistribution d₁ d₂) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2 i2
  rw [variance_eq_sub hm]
  have e2' : ∫ x, (id ^ 2 : ℝ → ℝ) x ∂(fDistribution d₁ d₂) = ∫ x, x ^ 2 ∂(fDistribution d₁ d₂) := rfl
  have e1 : ∫ x, id x ∂(fDistribution d₁ d₂) = d₂ / (d₂ - 2) :=
    (integral_id_fDistribution hd₁ (by linarith)).2
  rw [e2', e2, e1]
  have h2 : d₂ - 2 ≠ 0 := by linarith
  have h4 : d₂ - 4 ≠ 0 := by linarith
  field_simp
  ring

/-- Third moment of the F law: `E[F³] = d₂³ (d₁ + 2)(d₁ + 4) / (d₁² (d₂ - 2)(d₂ - 4)(d₂ - 6))` for `d₂ > 6`. -/
lemma integral_cube_fDistribution {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 6 < d₂) :
    Integrable (fun x ↦ x ^ 3) (fDistribution d₁ d₂) ∧
      ∫ x, x ^ 3 ∂(fDistribution d₁ d₂) =
        d₂ ^ 3 * (d₁ + 2) * (d₁ + 4) / (d₁ ^ 2 * (d₂ - 2) * (d₂ - 4) * (d₂ - 6)) := by
  obtain ⟨hi, he⟩ := integral_pow_fDistribution hd₁ (by linarith) 3 (by norm_num; linarith)
  rw [show ((3 : ℕ) : ℝ) = 3 by norm_num] at he
  refine ⟨hi, ?_⟩
  have hG1 := Gamma_pos_of_pos (by positivity : 0 < d₁ / 2)
  have g1 : Gamma (d₁ / 2 + 3) =
      (d₁ / 2 + 2) * (d₁ / 2 + 1) * (d₁ / 2) * Gamma (d₁ / 2) := by
    rw [show d₁ / 2 + 3 = ((d₁ / 2 + 1) + 1) + 1 by ring,
      Gamma_add_one (by positivity), Gamma_add_one (by positivity), Gamma_add_one (by positivity)]
    ring
  obtain ⟨c, rfl⟩ : ∃ c, d₂ = 2 * c + 6 := ⟨(d₂ - 6) / 2, by ring⟩
  have hc : 0 < c := by linarith
  have hGc := Gamma_pos_of_pos hc
  rw [show (2 * c + 6) / 2 - 3 = c by ring, show (2 * c + 6) / 2 = ((c + 1) + 1) + 1 by ring,
    Gamma_add_one (s := c + 1 + 1) (by positivity), Gamma_add_one (s := c + 1) (by positivity),
    Gamma_add_one (s := c) hc.ne', g1] at he
  rw [he, show 2 * c + 6 - 2 = 2 * (c + 2) by ring, show 2 * c + 6 - 4 = 2 * (c + 1) by ring,
    show 2 * c + 6 - 6 = 2 * c by ring]
  generalize Gamma c = G at hGc ⊢
  generalize Gamma (d₁ / 2) = G₁ at hG1 ⊢
  rw [div_pow, div_mul_eq_mul_div, div_div, div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- **The F curve is skewed to the right** (§13.3, ST-116): for `d₂ > 6` the third central moment of the
F law is `8 d₂³ (d₁ + d₂ - 2)(2 d₁ + d₂ - 2) / (d₁² (d₂ - 2)³ (d₂ - 4)(d₂ - 6))`, which is positive. -/
@[kb "openstaxintrostats2e" "§13.3, p. 695"]
theorem fDistribution_right_skewed {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 6 < d₂) :
    centralMoment id 3 (fDistribution d₁ d₂) = 8 * d₂ ^ 3 * (d₁ + d₂ - 2) * (2 * d₁ + d₂ - 2) /
        (d₁ ^ 2 * (d₂ - 2) ^ 3 * (d₂ - 4) * (d₂ - 6)) ∧
      0 < centralMoment id 3 (fDistribution d₁ d₂) := by
  have := isProbabilityMeasure_fDistribution hd₁ (by linarith : 0 < d₂)
  obtain ⟨i1, e1⟩ := integral_id_fDistribution (d₂ := d₂) hd₁ (by linarith)
  obtain ⟨i2, e2⟩ := integral_sq_fDistribution (d₂ := d₂) hd₁ (by linarith)
  obtain ⟨i3, e3⟩ := integral_cube_fDistribution hd₁ hd₂
  have h : centralMoment id 3 (fDistribution d₁ d₂) = 8 * d₂ ^ 3 * (d₁ + d₂ - 2) * (2 * d₁ + d₂ - 2) /
      (d₁ ^ 2 * (d₂ - 2) ^ 3 * (d₂ - 4) * (d₂ - 6)) := by
    rw [centralMoment_id_three i1 i2 i3, e1, e2, e3]
    have h2 : d₂ - 2 ≠ 0 := by linarith
    have h4 : d₂ - 4 ≠ 0 := by linarith
    have h6 : d₂ - 6 ≠ 0 := by linarith
    field_simp
    ring
  refine ⟨h, ?_⟩
  rw [h]
  have h2 : 0 < d₂ - 2 := by linarith
  have h4 : 0 < d₂ - 4 := by linarith
  have h6 : 0 < d₂ - 6 := by linarith
  have h7 : 0 < d₁ + d₂ - 2 := by linarith
  have h8 : 0 < 2 * d₁ + d₂ - 2 := by linarith
  positivity

end UndergradKB.Statistics
