import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Sqrt
import UndergradKB.Common.Attr

/-! # Calculus: Kepler's third law for an elliptical orbit

A body moves in the plane along the focal conic `r = p/(1 + e cos θ)` (`0 ≤ e < 1`: an ellipse with a focus at the
origin, semimajor axis `a = p/(1 - e²)`), with constant angular momentum `r² θ' = h` (the law of equal areas,
Kepler's second law), and `p = h²/μ` (the focal parameter of the inverse-square orbit with `μ = G (M + m)`, see
`kepler_polar_equation` in `Kepler.lean`). Then the time `P` needed to go once around (`θ` from `0` to `2π`) satisfies
`P² = 4π² a³ / μ`.

The key computation is `∫₀^{2π} dθ/(1 + e cos θ)² = 2π/(1 - e²)^{3/2}`, done with an antiderivative that is smooth
on all of `ℝ`: the eccentric anomaly `E(θ) = θ - 2 arctan(β sin θ/(1 + β cos θ))`, `β = e/(1 + √(1 - e²))`, satisfies
`E' = √(1 - e²)/(1 + e cos θ)`, `E(0) = 0`, `E(2π) = 2π`. -/

namespace UndergradKB.Calculus

open Real intervalIntegral

/-- The eccentric anomaly as a smooth function of the polar angle `θ` (true anomaly), for eccentricity `e`. -/
noncomputable def eccentricAnomaly (e θ : ℝ) : ℝ :=
  θ - 2 * arctan (e / (1 + √(1 - e ^ 2)) * sin θ / (1 + e / (1 + √(1 - e ^ 2)) * cos θ))

section
variable {e : ℝ}

private theorem kepler3_s_pos (he0 : 0 ≤ e) (he1 : e < 1) : 0 < √(1 - e ^ 2) :=
  Real.sqrt_pos.2 (by nlinarith)

private theorem kepler3_beta (he0 : 0 ≤ e) (he1 : e < 1) :
    0 ≤ e / (1 + √(1 - e ^ 2)) ∧ e / (1 + √(1 - e ^ 2)) < 1 := by
  have hs := kepler3_s_pos he0 he1
  refine ⟨div_nonneg he0 (by linarith), ?_⟩
  rw [div_lt_one (by linarith)]
  linarith

private theorem kepler3_den_pos {β : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) (θ : ℝ) : 0 < 1 + β * cos θ := by
  have := neg_one_le_cos θ
  nlinarith

private theorem kepler3_hasDerivAt_aux {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (θ : ℝ) :
    HasDerivAt (fun x => x - 2 * arctan (β * sin x / (1 + β * cos x)))
      ((1 - β ^ 2) / (1 + 2 * β * cos θ + β ^ 2)) θ := by
  have hd := kepler3_den_pos hβ0 hβ1 θ
  have hq := ((hasDerivAt_sin θ).const_mul β).div
    (((hasDerivAt_cos θ).const_mul β).const_add 1) hd.ne'
  have hE := (hasDerivAt_id θ).sub ((hq.arctan).const_mul 2)
  convert hE using 1
  · rfl
  have hsc := sin_sq_add_cos_sq θ
  have h2 : 0 < 1 + 2 * β * cos θ + β ^ 2 := by nlinarith [neg_one_le_cos θ]
  have hN : β * cos θ * (1 + β * cos θ) - β * sin θ * (β * -sin θ) = β * cos θ + β ^ 2 := by
    linear_combination β ^ 2 * hsc
  have hK : 1 + (β * sin θ / (1 + β * cos θ)) ^ 2 =
      (1 + 2 * β * cos θ + β ^ 2) / (1 + β * cos θ) ^ 2 := by
    rw [div_pow, eq_div_iff (by positivity), add_mul, div_mul_cancel₀ _ (by positivity)]
    linear_combination β ^ 2 * hsc
  simp only [Pi.div_apply]
  rw [hN, hK]
  have hd' : (1 + β * cos θ) ^ 2 ≠ 0 := by positivity
  generalize hQ : 1 + 2 * β * cos θ + β ^ 2 = Q at h2 ⊢
  generalize (1 + β * cos θ) ^ 2 = D at hd' ⊢
  have h2' := h2.ne'
  field_simp
  linear_combination hQ

theorem hasDerivAt_eccentricAnomaly (he0 : 0 ≤ e) (he1 : e < 1) (θ : ℝ) :
    HasDerivAt (eccentricAnomaly e) (√(1 - e ^ 2) / (1 + e * cos θ)) θ := by
  have hs := kepler3_s_pos he0 he1
  have hss : √(1 - e ^ 2) ^ 2 = 1 - e ^ 2 := Real.sq_sqrt (by nlinarith)
  obtain ⟨hβ0, hβ1⟩ := kepler3_beta he0 he1
  have h := kepler3_hasDerivAt_aux hβ0 hβ1 θ
  unfold eccentricAnomaly
  convert h using 1
  generalize √(1 - e ^ 2) = s at hs hss h ⊢
  have hs1 : (1 + s) ≠ 0 := by positivity
  generalize hβ : e / (1 + s) = β at hβ0 hβ1 h ⊢
  have he : e = β * (1 + s) := by rw [← hβ]; field_simp
  subst he
  have hK : β ^ 2 * (1 + s) = 1 - s := by
    have h1 : (β ^ 2 * (1 + s) - (1 - s)) * (1 + s) = 0 := by linear_combination hss
    rcases mul_eq_zero.1 h1 with h1 | h1
    · linarith
    · exact absurd h1 hs1
  have hde : 0 < 1 + β * (1 + s) * cos θ := by
    have := kepler3_den_pos (β := β * (1 + s)) (by positivity) (by nlinarith) θ
    exact this
  have h2 : 0 < 1 + 2 * β * cos θ + β ^ 2 := by nlinarith [neg_one_le_cos θ]
  rw [div_eq_div_iff hde.ne' h2.ne']
  linear_combination (1 + β * cos θ) * hK

theorem eccentricAnomaly_zero (e : ℝ) : eccentricAnomaly e 0 = 0 := by
  simp [eccentricAnomaly]

theorem eccentricAnomaly_two_pi (e : ℝ) : eccentricAnomaly e (2 * π) = 2 * π := by
  simp [eccentricAnomaly]

/-- An antiderivative of `1/(1 + e cos θ)²` on all of `ℝ`, for `0 ≤ e < 1`. -/
theorem hasDerivAt_kepler_antideriv (he0 : 0 ≤ e) (he1 : e < 1) (θ : ℝ) :
    HasDerivAt (fun x => (eccentricAnomaly e x / √(1 - e ^ 2) - e * sin x / (1 + e * cos x)) / (1 - e ^ 2))
      (1 / (1 + e * cos θ) ^ 2) θ := by
  have hs := kepler3_s_pos he0 he1
  have hss : √(1 - e ^ 2) ^ 2 = 1 - e ^ 2 := Real.sq_sqrt (by nlinarith)
  have hde : 0 < 1 + e * cos θ := kepler3_den_pos he0 he1 θ
  have h1 := (hasDerivAt_eccentricAnomaly he0 he1 θ).div_const (√(1 - e ^ 2))
  have h2 := ((hasDerivAt_sin θ).const_mul e).div (((hasDerivAt_cos θ).const_mul e).const_add 1) hde.ne'
  have h3 := (h1.sub h2).div_const (1 - e ^ 2)
  convert h3 using 1
  have he2 : (1 - e ^ 2) ≠ 0 := by nlinarith
  have hsc := sin_sq_add_cos_sq θ
  generalize √(1 - e ^ 2) = s at hs hss ⊢
  have hs' := hs.ne'
  have hde' := hde.ne'
  field_simp
  rw [← hss]
  linear_combination e ^ 2 * hsc + hss

/-- `∫₀^{2π} dθ/(1 + e cos θ)² = 2π/(1 - e²)^{3/2}` for `0 ≤ e < 1`. -/
theorem integral_inv_one_add_mul_cos_sq (he0 : 0 ≤ e) (he1 : e < 1) :
    ∫ θ in (0)..(2 * π), 1 / (1 + e * cos θ) ^ 2 = 2 * π / ((1 - e ^ 2) * √(1 - e ^ 2)) := by
  rw [integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_kepler_antideriv he0 he1 x)]
  · simp only [eccentricAnomaly_zero, eccentricAnomaly_two_pi, sin_zero, sin_two_pi]
    have hs := kepler3_s_pos he0 he1
    have he2 : (1 - e ^ 2) ≠ 0 := by nlinarith
    field_simp
    ring
  · apply Continuous.intervalIntegrable
    refine continuous_const.div ((continuous_const.add (continuous_const.mul continuous_cos)).pow 2) ?_
    intro x
    exact (pow_pos (kepler3_den_pos he0 he1 x) 2).ne'

/-- The area enclosed by the focal ellipse `r = p/(1 + e cos θ)` (`0 ≤ e < 1`), computed with the polar area formula
`½ ∫₀^{2π} r² dθ`, is `π a b` with semimajor axis `a = p/(1 - e²)` and semiminor axis `b = a √(1 - e²)`. -/
theorem ellipse_focal_polar_area {p e : ℝ} (he0 : 0 ≤ e) (he1 : e < 1) :
    (1 / 2) * ∫ θ in (0)..(2 * π), (p / (1 + e * cos θ)) ^ 2 =
      π * (p / (1 - e ^ 2)) * (p / (1 - e ^ 2) * √(1 - e ^ 2)) := by
  have h : ∀ θ, (p / (1 + e * cos θ)) ^ 2 = p ^ 2 * (1 / (1 + e * cos θ) ^ 2) := fun θ => by
    rw [div_pow]; ring
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul, integral_inv_one_add_mul_cos_sq he0 he1]
  have hs := kepler3_s_pos he0 he1
  have hss : √(1 - e ^ 2) ^ 2 = 1 - e ^ 2 := Real.sq_sqrt (by nlinarith)
  have he2 : (1 - e ^ 2) ≠ 0 := by nlinarith
  generalize √(1 - e ^ 2) = s at hs hss ⊢
  have hs' := hs.ne'
  field_simp
  rw [hss]

/-- OpenStax Calculus 3:§3.4 Equation 3.30 (CA-503), Kepler's third law in Newton's form.
A body of mass `m` moves around a body of mass `M` along the focal ellipse `r = p/(1 + e cos θ)` (`0 ≤ e < 1`,
semimajor axis `a = p/(1 - e²)`), its polar angle `θ(t)` obeying the law of equal areas `r² θ' = h` (`h > 0`), and
`p = h²/(G (M + m))` (the focal parameter of the inverse-square orbit, `kepler_polar_equation`). If the body goes once
around in time `P` (`θ(0) = 0`, `θ(P) = 2π`), then `P² = 4π² a³/(G (M + m))`. -/
@[kb "openstaxcalculus2016" "3:§3.4 Equation 3.30, p. 295"]
theorem kepler_third_law {G M m h e p a P : ℝ} {θ θ' : ℝ → ℝ} (hGMm : 0 < G * (M + m)) (hh : 0 < h)
    (he0 : 0 ≤ e) (he1 : e < 1) (hp : p = h ^ 2 / (G * (M + m))) (ha : a = p / (1 - e ^ 2))
    (hθ : ∀ t, HasDerivAt θ (θ' t) t) (hareal : ∀ t, (p / (1 + e * cos (θ t))) ^ 2 * θ' t = h)
    (h0 : θ 0 = 0) (hP : θ P = 2 * π) :
    P ^ 2 = 4 * π ^ 2 * a ^ 3 / (G * (M + m)) := by
  have hp0 : 0 < p := by rw [hp]; positivity
  have hde : ∀ u, 0 < 1 + e * cos u := kepler3_den_pos he0 he1
  -- the angular speed is continuous
  have hθ'eq : ∀ t, θ' t = h * (1 + e * cos (θ t)) ^ 2 / p ^ 2 := fun t => by
    have := hareal t
    have := (hde (θ t)).ne'
    rw [div_pow] at *
    field_simp at *
    linarith
  have hθc : Continuous θ := continuous_iff_continuousAt.2 fun t => (hθ t).continuousAt
  have hθ'c : Continuous θ' := by
    rw [show θ' = fun t => h * (1 + e * cos (θ t)) ^ 2 / p ^ 2 from funext hθ'eq]
    fun_prop
  -- time = ∫ r²/h dθ
  have hg : Continuous fun u => (p / (1 + e * cos u)) ^ 2 / h :=
    ((continuous_const.div (continuous_const.add (continuous_const.mul continuous_cos))
      fun u => (hde u).ne').pow 2).div_const h
  have hcv := intervalIntegral.integral_comp_mul_deriv (a := 0) (b := P) (fun t _ => hθ t)
    hθ'c.continuousOn hg
  have hone : ∀ t, ((fun u => (p / (1 + e * cos u)) ^ 2 / h) ∘ θ) t * θ' t = 1 := fun t => by
    simp only [Function.comp]
    rw [div_mul_eq_mul_div, hareal t, div_self hh.ne']
  simp only [hone, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one, h0, hP] at hcv
  have harea := ellipse_focal_polar_area (p := p) he0 he1
  rw [intervalIntegral.integral_div] at hcv
  have hPv : P = 2 / h * (π * a * (a * √(1 - e ^ 2))) := by
    rw [hcv, ha, ← harea]; field_simp
  have hs := kepler3_s_pos he0 he1
  have hss : √(1 - e ^ 2) ^ 2 = 1 - e ^ 2 := Real.sq_sqrt (by nlinarith)
  have he2 : (1 - e ^ 2) ≠ 0 := by nlinarith
  rw [hPv, ha]
  have hGMm' : G * (M + m) = h ^ 2 / p := by rw [hp]; field_simp
  rw [hGMm']
  generalize √(1 - e ^ 2) = s at hs hss ⊢
  field_simp
  rw [hss]
  ring

end

end UndergradKB.Calculus
