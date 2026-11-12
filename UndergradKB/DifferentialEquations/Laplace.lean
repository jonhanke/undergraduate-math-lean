import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Analysis.Convolution
import UndergradKB.Common.Attr

/-! # The Laplace transform (Lebl, *Notes on Diffy Qs*, Chapter 6)

Mathlib has no Laplace transform, so `laplace f s = ∫_{(0,∞)} e^{-st} f(t) dt` is defined here as a Lebesgue
integral (it agrees with the book's improper integral whenever the latter converges absolutely, which is the case
for every function of exponential order and `s` large).

Conventions.
* `ExpOrder f M c` is the bound `|f t| ≤ M e^{ct}` for **all** `t ≥ 0` (the book asks it only for large `t`;
  for continuous `f` the two versions are equivalent after enlarging `M`, so we use the simpler one).
* "Piecewise continuous" is replaced by `ContinuousOn f (Ici 0)`, or just integrability of the integrand
  where the proof needs nothing more. -/

open Real Set Filter Topology MeasureTheory

namespace UndergradKB.DifferentialEquations

/-- The Laplace transform `F(s) = ∫_0^∞ e^{-st} f(t) dt`. -/
noncomputable def laplace (f : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0:ℝ), Real.exp (-(s * t)) * f t

/-- Lebl, §6.1 (DE-166): `f` is of exponential order `c` with constant `M`, i.e. `|f t| ≤ M e^{ct}` for `t ≥ 0`. -/
def ExpOrder (f : ℝ → ℝ) (M c : ℝ) : Prop := ∀ t, 0 ≤ t → |f t| ≤ M * Real.exp (c * t)

/-- The Heaviside step `u(t - a)`: `0` for `t < a`, `1` for `t ≥ a`. -/
noncomputable def heaviside (a : ℝ) : ℝ → ℝ := Set.indicator (Set.Ici a) 1

/-- Lebl, §6.3 (DE-178): the convolution `(f * g)(t) = ∫_0^t f(τ) g(t - τ) dτ`. -/
noncomputable def conv0 (f g : ℝ → ℝ) (t : ℝ) : ℝ := ∫ τ in (0:ℝ)..t, f τ * g (t - τ)

private lemma exp_bound_eq (M s c t : ℝ) :
    Real.exp (-(s * t)) * (M * Real.exp (c * t)) = M * Real.exp (-(s - c) * t) := by
  rw [← mul_assoc, mul_comm (Real.exp _) M, mul_assoc, ← Real.exp_add]
  ring_nf

/-- **DE-167 (integrability).** Lebl Theorem 6.1.2, p. 296 (continuous case): if `f` is continuous on `[0,∞)`
and of exponential order `c`, then `e^{-st} f(t)` is integrable on `(0,∞)` for `s > c`. -/
@[kb "lebldiffyqs2026" "Theorem 6.1.2, p. 296"]
theorem laplace_integrableOn {f : ℝ → ℝ} {M c s : ℝ} (hc : ContinuousOn f (Ici 0))
    (hb : ExpOrder f M c) (hcs : c < s) :
    IntegrableOn (fun t => Real.exp (-(s * t)) * f t) (Ioi 0) := by
  have hg : IntegrableOn (fun t : ℝ => M * Real.exp (-(s - c) * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul M
  refine Integrable.mono' hg ?_ ?_
  · have : ContinuousOn (fun t => Real.exp (-(s * t)) * f t) (Ioi 0) :=
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).continuousOn).mul
        (hc.mono Ioi_subset_Ici_self)
    exact this.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := le_of_lt ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), ← exp_bound_eq]
    exact mul_le_mul_of_nonneg_left (hb t ht0) (Real.exp_pos _).le

/-- The integrand of a Laplace transform tends to `0` at infinity for `f` of exponential order `c < s`. -/
theorem laplace_integrand_tendsto {f : ℝ → ℝ} {M c s : ℝ}
    (hb : ExpOrder f M c) (hcs : c < s) :
    Tendsto (fun t => Real.exp (-(s * t)) * f t) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => M * Real.exp (-(s - c) * t)) atTop (𝓝 (M * 0)) :=
    (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by linarith : -(s - c) < 0))).const_mul M
  rw [mul_zero] at h1
  have h2 := h1.neg
  rw [neg_zero] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h2 h1 ?_ ?_
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have h3 : Real.exp (-(s * t)) * (-(M * Real.exp (c * t))) ≤ Real.exp (-(s * t)) * f t :=
      mul_le_mul_of_nonneg_left (abs_le.1 (hb t ht)).1 (Real.exp_pos _).le
    rw [mul_neg, exp_bound_eq] at h3
    exact h3
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have h3 : Real.exp (-(s * t)) * f t ≤ Real.exp (-(s * t)) * (M * Real.exp (c * t)) :=
      mul_le_mul_of_nonneg_left (abs_le.1 (hb t ht)).2 (Real.exp_pos _).le
    rwa [exp_bound_eq] at h3

/-- **DE-167 (decay).** Lebl Theorem 6.1.2, p. 296: for `f` continuous of exponential order `c`,
`F(s) → 0` as `s → ∞`. -/
@[kb "lebldiffyqs2026" "Theorem 6.1.2, p. 296"]
theorem laplace_tendsto_zero {f : ℝ → ℝ} {M c : ℝ} (hb : ExpOrder f M c) :
    Tendsto (laplace f) atTop (𝓝 0) := by
  have hbound : ∀ s, c < s → |laplace f s| ≤ M / (s - c) := by
    intro s hcs
    have hg : IntegrableOn (fun t : ℝ => M * Real.exp (-(s - c) * t)) (Ioi 0) :=
      (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul M
    have h := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (0:ℝ)))
      (f := fun t => Real.exp (-(s * t)) * f t) (g := fun t => M * Real.exp (-(s - c) * t)) hg
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), ← exp_bound_eq]
        exact mul_le_mul_of_nonneg_left (hb t (le_of_lt ht)) (Real.exp_pos _).le)
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith)] at h
    simp only [mul_zero, Real.exp_zero] at h
    have e : M * (-1 / -(s - c)) = M / (s - c) := by
      rw [neg_div_neg_eq]; ring
    rw [Real.norm_eq_abs, e] at h
    exact h
  have h0 : Tendsto (fun s : ℝ => M / (s - c)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_id)
  have h0' : Tendsto (fun s : ℝ => M / (s - c)) atTop (𝓝 0) := by
    simpa [sub_eq_add_neg] using h0
  refine squeeze_zero_norm' ?_ h0'
  filter_upwards [eventually_gt_atTop c] with s hs
  rw [Real.norm_eq_abs]; exact hbound s hs

/-- **DE-165 linearity.** Lebl Theorem 6.1.1, p. 295 (under integrability of both integrands). -/
@[kb "lebldiffyqs2026" "Theorem 6.1.1, p. 295"]
theorem laplace_add_smul {f g : ℝ → ℝ} {s : ℝ} (A B : ℝ)
    (hf : IntegrableOn (fun t => Real.exp (-(s * t)) * f t) (Ioi 0))
    (hg : IntegrableOn (fun t => Real.exp (-(s * t)) * g t) (Ioi 0)) :
    laplace (fun t => A * f t + B * g t) s = A * laplace f s + B * laplace g s := by
  unfold laplace
  have : (fun t => Real.exp (-(s * t)) * (A * f t + B * g t)) =
      fun t => A * (Real.exp (-(s * t)) * f t) + B * (Real.exp (-(s * t)) * g t) := by
    ext t; ring
  rw [this, integral_add (hf.const_mul A) (hg.const_mul B), integral_const_mul, integral_const_mul]

/-! ### Table of transforms -/

/-- **DE-162.** Lebl Example 6.1.2, p. 294: `L{e^{at}}(s) = 1/(s-a)` for `s > a` (Example 6.1.2 is the case
with `-a`). -/
@[kb "lebldiffyqs2026" "Example 6.1.2, p. 294"]
theorem laplace_exp {a s : ℝ} (h : a < s) : laplace (fun t => Real.exp (a * t)) s = 1 / (s - a) := by
  unfold laplace
  have : (fun t : ℝ => Real.exp (-(s * t)) * Real.exp (a * t)) = fun t => Real.exp (-(s - a) * t) := by
    ext t; rw [← Real.exp_add]; ring_nf
  rw [this, integral_exp_mul_Ioi (by linarith)]
  simp only [mul_zero, Real.exp_zero]
  rw [neg_div_neg_eq]

/-- **DE-162.** Lebl Example 6.1.1, p. 294: `L{1}(s) = 1/s` for `s > 0`. -/
@[kb "lebldiffyqs2026" "Example 6.1.1, p. 294"]
theorem laplace_one {s : ℝ} (h : 0 < s) : laplace (fun _ => 1) s = 1 / s := by
  have := laplace_exp (a := 0) h
  simpa using this

/-- **DE-164.** Lebl Table 6.1, p. 295 (with Example 6.1.3 for `n = 1`):
`L{tⁿ}(s) = n! / s^(n+1)` for `s > 0`. -/
@[kb "lebldiffyqs2026" "Table 6.1, p. 295"]
theorem laplace_pow (n : ℕ) {s : ℝ} (h : 0 < s) :
    laplace (fun t => t ^ n) s = (n.factorial : ℝ) / s ^ (n + 1) := by
  unfold laplace
  have ha : (0:ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have key := Real.integral_rpow_mul_exp_neg_mul_Ioi ha h
  have e1 : ((n + 1 : ℕ) : ℝ) - 1 = (n : ℝ) := by push_cast; ring
  have g : Real.Gamma ((n + 1 : ℕ) : ℝ) = n.factorial := by
    rw [Nat.cast_succ]; exact Real.Gamma_nat_eq_factorial n
  rw [e1, g] at key
  simp_rw [Real.rpow_natCast] at key
  have : (fun t : ℝ => Real.exp (-(s * t)) * t ^ n) = fun t => t ^ n * Real.exp (-(s * t)) := by
    ext t; ring
  show ∫ t in Ioi (0:ℝ), Real.exp (-(s * t)) * t ^ n = _
  rw [this, key, one_div, inv_pow]
  field_simp

/-- **DE-162.** Lebl Example 6.1.3, p. 294: `L{t}(s) = 1/s²` for `s > 0`. -/
@[kb "lebldiffyqs2026" "Example 6.1.3, p. 294"]
theorem laplace_id {s : ℝ} (h : 0 < s) : laplace (fun t => t) s = 1 / s ^ 2 := by
  have := laplace_pow 1 h
  simpa using this

/-! ### Shifting -/

/-- **DE-171 first shifting.** Lebl §6.1, p. 298: `L{e^{-at} f(t)}(s) = F(s + a)`. -/
@[kb "lebldiffyqs2026" "First shifting property, p. 298"]
theorem laplace_exp_mul (f : ℝ → ℝ) (a s : ℝ) :
    laplace (fun t => Real.exp (-(a * t)) * f t) s = laplace f (s + a) := by
  unfold laplace
  congr 1; ext t
  rw [← mul_assoc, ← Real.exp_add]; congr 2; ring

/-- Shift of the integration domain: `∫_{(a,∞)} h = ∫_{(0,∞)} h(u + a)`. -/
lemma integral_Ioi_shift (h : ℝ → ℝ) (a : ℝ) :
    ∫ t in Ioi a, h t = ∫ u in Ioi 0, h (u + a) := by
  have e := (measurableEmbedding_addRight a).setIntegral_map (μ := volume) h (Ioi a)
  rw [(measurePreserving_add_right volume a).map_eq] at e
  rw [e]
  congr 1
  ext x; simp

/-- **DE-174 second shifting.** Lebl §6.2, p. 302: for `a ≥ 0`,
`L{f(t-a) u(t-a)}(s) = e^{-as} F(s)`. -/
@[kb "lebldiffyqs2026" "Second shifting property (6.1), p. 302"]
theorem laplace_shift {a : ℝ} (ha : 0 ≤ a) (f : ℝ → ℝ) (s : ℝ) :
    laplace (fun t => f (t - a) * heaviside a t) s = Real.exp (-(a * s)) * laplace f s := by
  unfold laplace heaviside
  have e1 : (fun t : ℝ => Real.exp (-(s * t)) * (f (t - a) * Set.indicator (Set.Ici a) 1 t)) =
      Set.indicator (Set.Ici a) (fun t => Real.exp (-(s * t)) * f (t - a)) := by
    ext t
    by_cases ht : t ∈ Set.Ici a <;> simp [ht]
  rw [e1, setIntegral_indicator measurableSet_Ici]
  have e2 : Ioi (0:ℝ) ∩ Ici a =ᵐ[volume] Ioi a := by
    have : Ioi (0:ℝ) ∩ Ioi a = Ioi a := by
      rw [Ioi_inter_Ioi, max_eq_right ha]
    rw [← this]
    exact ae_eq_set_inter (ae_eq_refl _) Ioi_ae_eq_Ici.symm
  rw [setIntegral_congr_set e2, integral_Ioi_shift, ← integral_const_mul]
  congr 1; ext u
  rw [add_sub_cancel_right, ← mul_assoc, ← Real.exp_add]
  congr 2; ring

/-- **DE-163.** Lebl Example 6.1.4, p. 294: `L{u(t-a)}(s) = e^{-as}/s` for `a ≥ 0`, `s > 0`. -/
@[kb "lebldiffyqs2026" "Example 6.1.4, p. 294"]
theorem laplace_heaviside {a s : ℝ} (ha : 0 ≤ a) (hs : 0 < s) :
    laplace (heaviside a) s = Real.exp (-(a * s)) / s := by
  have := laplace_shift ha (fun _ => 1) s
  rw [laplace_one hs] at this
  simp only [one_mul] at this
  rw [this]; ring

/-- Constants pull out of the transform (no hypotheses needed). -/
theorem laplace_const_mul (A : ℝ) (f : ℝ → ℝ) (s : ℝ) :
    laplace (fun t => A * f t) s = A * laplace f s := by
  unfold laplace
  rw [← integral_const_mul]
  congr 1; ext t; ring

/-! ### Derivatives -/

/-- **DE-172.** Lebl §6.2, Table 6.2, p. 300: `L{g'}(s) = s G(s) - g(0)`, where `g` is differentiable on
`[0,∞)` with continuous derivative `g'`, both of exponential order `c`, and `s > c`. -/
@[kb "lebldiffyqs2026" "Transforms of derivatives (Table 6.2), p. 300"]
theorem laplace_deriv {g g' : ℝ → ℝ} {M M' c s : ℝ}
    (hg : ∀ t, 0 ≤ t → HasDerivAt g (g' t) t) (hg'c : ContinuousOn g' (Ici 0))
    (hb : ExpOrder g M c) (hb' : ExpOrder g' M' c) (hcs : c < s) :
    laplace g' s = s * laplace g s - g 0 := by
  have hgc : ContinuousOn g (Ici 0) := fun t ht => (hg t ht).continuousAt.continuousWithinAt
  have i1 := laplace_integrableOn hgc hb hcs
  have i2 := laplace_integrableOn hg'c hb' hcs
  have hd : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun t => Real.exp (-(s * t)) * g t)
        (Real.exp (-(s * t)) * g' t - s * (Real.exp (-(s * t)) * g t)) t := by
    intro t ht
    have e : HasDerivAt (fun t => Real.exp (-(s * t))) (Real.exp (-(s * t)) * (-s)) t :=
      (((hasDerivAt_id' t).const_mul s).neg.exp).congr_deriv (by simp)
    have := e.mul (hg t ht)
    convert this using 1
    ring
  have := integral_Ioi_of_hasDerivAt_of_tendsto' hd ((i2.sub (i1.const_mul s)))
    (laplace_integrand_tendsto hb hcs)
  rw [integral_sub i2 (i1.const_mul s), integral_const_mul] at this
  simp only [mul_zero, Real.exp_zero, one_mul, zero_sub, neg_zero] at this
  unfold laplace
  linarith

/-- **DE-172 (second derivative).** Lebl Table 6.2, p. 300: `L{g''} = s² G - s g(0) - g'(0)`. All of `g, g', g''`
have exponential order `c`, `g''` is continuous on `[0,∞)`, and `s > c`. -/
@[kb "lebldiffyqs2026" "Transforms of derivatives (Table 6.2), p. 300"]
theorem laplace_deriv₂ {g g' g'' : ℝ → ℝ} {M M' M'' c s : ℝ}
    (hg : ∀ t, 0 ≤ t → HasDerivAt g (g' t) t) (hg' : ∀ t, 0 ≤ t → HasDerivAt g' (g'' t) t)
    (hg''c : ContinuousOn g'' (Ici 0))
    (hb : ExpOrder g M c) (hb' : ExpOrder g' M' c) (hb'' : ExpOrder g'' M'' c) (hcs : c < s) :
    laplace g'' s = s ^ 2 * laplace g s - s * g 0 - g' 0 := by
  have hg'c : ContinuousOn g' (Ici 0) := fun t ht => (hg' t ht).continuousAt.continuousWithinAt
  have h1 := laplace_deriv hg hg'c hb hb' hcs
  have h2 := laplace_deriv hg' hg''c hb' hb'' hcs
  rw [h2, h1]; ring

/-! ### Sine and cosine -/

private lemma expOrder_bdd {f : ℝ → ℝ} {C : ℝ} (h : ∀ t, |f t| ≤ C) : ExpOrder f C 0 := fun t _ => by
  simpa using h t

/-- **DE-164.** Lebl Table 6.1, p. 295: `L{sin ωt} = ω/(s²+ω²)` and `L{cos ωt} = s/(s²+ω²)` for `s > 0`
(proved together from the derivative rule). -/
@[kb "lebldiffyqs2026" "Table 6.1, p. 295"]
theorem laplace_sin_cos (ω : ℝ) {s : ℝ} (hs : 0 < s) :
    laplace (fun t => Real.sin (ω * t)) s = ω / (s ^ 2 + ω ^ 2) ∧
    laplace (fun t => Real.cos (ω * t)) s = s / (s ^ 2 + ω ^ 2) := by
  have hsin : ∀ t, |Real.sin (ω * t)| ≤ 1 := fun t => Real.abs_sin_le_one _
  have hcos : ∀ t, |Real.cos (ω * t)| ≤ 1 := fun t => Real.abs_cos_le_one _
  have hsin' : ∀ t, |ω * Real.cos (ω * t)| ≤ |ω| := fun t => by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have hcos' : ∀ t, |(-ω) * Real.sin (ω * t)| ≤ |ω| := fun t => by
    rw [abs_mul, abs_neg]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  have e1 := laplace_deriv (g := fun t => Real.sin (ω * t)) (g' := fun t => ω * Real.cos (ω * t))
    (c := 0) (s := s)
    (fun t _ => by
      have := ((hasDerivAt_id' t).const_mul ω).sin
      simpa [mul_comm] using this)
    (by fun_prop) (expOrder_bdd hsin) (expOrder_bdd hsin') hs
  have e2 := laplace_deriv (g := fun t => Real.cos (ω * t)) (g' := fun t => (-ω) * Real.sin (ω * t))
    (c := 0) (s := s)
    (fun t _ => by
      have := ((hasDerivAt_id' t).const_mul ω).cos
      convert this using 1
      simp; ring)
    (by fun_prop) (expOrder_bdd hcos) (expOrder_bdd hcos') hs
  rw [laplace_const_mul] at e1 e2
  simp only [mul_zero, Real.sin_zero, Real.cos_zero, sub_zero] at e1 e2
  have hpos : 0 < s ^ 2 + ω ^ 2 := by positivity
  constructor
  · rw [eq_div_iff hpos.ne']
    linear_combination (-ω) * e2 + (-s) * e1
  · rw [eq_div_iff hpos.ne']
    linear_combination (-s) * e2 + ω * e1

/-! ### Integrals, periodic functions, pulses -/

/-- **DE-176.** Lebl §6.2.5, p. 305: the transform of `t ↦ ∫_0^t f` is `F(s)/s`, for `f` continuous of
exponential order `c < s`, `s > 0`. (The book allows piecewise continuous `f`; we assume continuity on `ℝ`.) -/
@[kb "lebldiffyqs2026" "Transforms of integrals, p. 305"]
theorem laplace_integral {f : ℝ → ℝ} {M c s : ℝ} (hc : Continuous f)
    (hb : ExpOrder f M c) (hs : 0 < s) (hcs : c < s) :
    laplace (fun t => ∫ u in (0 : ℝ)..t, f u) s = laplace f s / s := by
  set a' := max c (s / 2) with ha'
  have ha'pos : 0 < a' := lt_max_of_lt_right (by linarith)
  have ha's : a' < s := max_lt hcs (by linarith)
  have hM : 0 ≤ M := by
    have := hb 0 le_rfl
    simp only [mul_zero, Real.exp_zero, mul_one] at this
    exact (abs_nonneg _).trans this
  have hb2 : ExpOrder f M a' := fun t ht =>
    (hb t ht).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_left _ _) ht)) hM)
  have hint : ∀ t, 0 ≤ t →
      (∫ u in (0 : ℝ)..t, M * Real.exp (a' * u)) = M / a' * (Real.exp (a' * t) - 1) := by
    intro t ht
    have hF : ∀ u ∈ uIcc (0 : ℝ) t, HasDerivAt (fun u => M / a' * Real.exp (a' * u))
        (M * Real.exp (a' * u)) u := by
      intro u _
      have e : HasDerivAt (fun u => Real.exp (a' * u)) (Real.exp (a' * u) * a') u :=
        (((hasDerivAt_id' u).const_mul a').exp).congr_deriv (by simp)
      refine (e.const_mul (M / a')).congr_deriv ?_
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
      ((continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul continuous_id))).intervalIntegrable _ _)]
    simp only [mul_zero, Real.exp_zero]
    ring
  have hgb : ExpOrder (fun t => ∫ u in (0 : ℝ)..t, f u) (M / a') a' := by
    intro t ht
    have h1 := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (f := f)
      (g := fun u => M * Real.exp (a' * u)) ht
      (Filter.Eventually.of_forall fun u hu => by
        rw [Real.norm_eq_abs]; exact hb2 u hu.1.le)
      ((continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul continuous_id))).intervalIntegrable _ _)
    rw [hint t ht, Real.norm_eq_abs] at h1
    refine h1.trans ?_
    have : 0 ≤ M / a' := div_nonneg hM ha'pos.le
    nlinarith
  have hder : ∀ t, 0 ≤ t → HasDerivAt (fun t => ∫ u in (0 : ℝ)..t, f u) (f t) t :=
    fun t _ => (hc.integral_hasStrictDerivAt 0 t).hasDerivAt
  have key := laplace_deriv (g := fun t => ∫ u in (0 : ℝ)..t, f u) (g' := f) hder hc.continuousOn
    hgb hb2 ha's
  simp only [intervalIntegral.integral_same, sub_zero] at key
  field_simp
  linarith

/-- **DE-177.** Lebl §6.2.6, p. 305: for `f` continuous and `P`-periodic and `s > 0`,
`F(s) = (1 - e^{-Ps})⁻¹ ∫_0^P e^{-st} f(t) dt`. -/
@[kb "lebldiffyqs2026" "Periodic functions, p. 305"]
theorem laplace_periodic {f : ℝ → ℝ} {P : ℝ} (hP : 0 < P) (hper : Function.Periodic f P)
    (hc : Continuous f) {s : ℝ} (hs : 0 < s) :
    laplace f s = (1 - Real.exp (-(P * s)))⁻¹ * ∫ t in (0 : ℝ)..P, Real.exp (-(s * t)) * f t := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (hper.isBounded_of_continuous hP.ne' hc)
  have hb : ExpOrder f C 0 := expOrder_bdd (fun t => by
    have := hC (f t) ⟨t, rfl⟩
    simpa using this)
  have hI := laplace_integrableOn hc.continuousOn hb hs
  have hsplit : laplace f s =
      (∫ t in Ioc 0 P, Real.exp (-(s * t)) * f t) + ∫ t in Ioi P, Real.exp (-(s * t)) * f t := by
    unfold laplace
    rw [← Ioc_union_Ioi_eq_Ioi hP.le]
    exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hI.mono_set Ioc_subset_Ioi_self)
      (hI.mono_set (Ioi_subset_Ioi hP.le))
  have hshift : ∫ t in Ioi P, Real.exp (-(s * t)) * f t = Real.exp (-(P * s)) * laplace f s := by
    rw [integral_Ioi_shift, laplace, ← integral_const_mul]
    congr 1; ext u
    rw [hper u, ← mul_assoc, ← Real.exp_add]; congr 2; ring
  have hlt : Real.exp (-(P * s)) < 1 := (by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by nlinarith))
  rw [intervalIntegral.integral_of_le hP.le]
  rw [hshift] at hsplit
  have hne : 1 - Real.exp (-(P * s)) ≠ 0 := by linarith
  rw [inv_mul_eq_div, eq_div_iff hne]
  linarith

/-- Integrability of `e^{-st} u(t-a)` on `(0,∞)` for `s > 0`. -/
lemma integrableOn_heaviside {s : ℝ} (hs : 0 < s) (a : ℝ) :
    IntegrableOn (fun t => Real.exp (-(s * t)) * heaviside a t) (Ioi 0) := by
  have h : (fun t => Real.exp (-(s * t)) * heaviside a t) =
      Set.indicator (Set.Ici a) (fun t => Real.exp (-(s * t))) := by
    ext t
    by_cases ht : t ∈ Set.Ici a <;> simp [heaviside, ht]
  rw [h]
  refine Integrable.indicator ?_ measurableSet_Ici
  have h2 : IntegrableOn (fun t : ℝ => Real.exp (-(s * t))) (Ioi 0) := by
    simpa [neg_mul] using integrableOn_exp_mul_Ioi (a := -s) (by linarith) 0
  exact h2

/-- **DE-183.** Lebl §6.4.1, p. 313: the rectangular pulse `M (u(t-a) - u(t-b))` (`a, b ≥ 0`) has transform
`M (e^{-as} - e^{-bs}) / s` for `s > 0`. -/
@[kb "lebldiffyqs2026" "Rectangular pulse, p. 313"]
theorem laplace_pulse {a b s : ℝ} (M : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 < s) :
    laplace (fun t => M * (heaviside a t - heaviside b t)) s =
      M * (Real.exp (-(a * s)) - Real.exp (-(b * s))) / s := by
  have := laplace_add_smul (f := heaviside a) (g := heaviside b) M (-M)
    (integrableOn_heaviside hs a) (integrableOn_heaviside hs b)
  rw [laplace_heaviside ha hs, laplace_heaviside hb hs] at this
  have e : (fun t => M * (heaviside a t - heaviside b t)) =
      fun t => M * heaviside a t + (-M) * heaviside b t := by ext t; ring
  rw [e, this]; ring

/-! ### Convolution: commutativity -/

/-- **DE-179.** Lebl §6.3, p. 309: `f * g = g * f` for the convolution on `[0,t]`. -/
@[kb "lebldiffyqs2026" "Properties of convolution, p. 309"]
theorem conv0_comm (f g : ℝ → ℝ) (t : ℝ) : conv0 f g t = conv0 g f t := by
  unfold conv0
  have := intervalIntegral.integral_comp_sub_left (a := 0) (b := t)
    (fun x => f x * g (t - x)) t
  simp only [sub_sub_cancel, sub_zero, sub_self] at this
  rw [← this]
  congr 1; ext x; ring

/-! ### Convolution theorem -/

/-- The convolution theorem under bare integrability: if `e^{-st} f(t)` and `e^{-st} g(t)` are integrable on
`(0,∞)`, then `L{f * g}(s) = F(s) G(s)`. (Proved from Mathlib's `integral_convolution` applied to the
functions `e^{-st} f(t)` and `e^{-st} g(t)` extended by zero to `t ≤ 0`.) -/
theorem laplace_conv0_of_integrable {f g : ℝ → ℝ} {s : ℝ}
    (hf : IntegrableOn (fun t => Real.exp (-(s * t)) * f t) (Ioi 0))
    (hg : IntegrableOn (fun t => Real.exp (-(s * t)) * g t) (Ioi 0)) :
    laplace (conv0 f g) s = laplace f s * laplace g s := by
  set f₁ : ℝ → ℝ := Set.indicator (Ioi 0) (fun t => Real.exp (-(s * t)) * f t) with hf₁
  set g₁ : ℝ → ℝ := Set.indicator (Ioi 0) (fun t => Real.exp (-(s * t)) * g t) with hg₁
  have h1 : Integrable f₁ := (integrable_indicator_iff measurableSet_Ioi).2 hf
  have h2 : Integrable g₁ := (integrable_indicator_iff measurableSet_Ioi).2 hg
  have key : ∀ t, convolution f₁ g₁ (ContinuousLinearMap.mul ℝ ℝ) volume t =
      if 0 < t then Real.exp (-(s * t)) * conv0 f g t else 0 := by
    intro t
    unfold convolution
    simp only [ContinuousLinearMap.mul_apply']
    by_cases ht : 0 < t
    · have e : (fun τ => f₁ τ * g₁ (t - τ)) =
          Set.indicator (Ioo 0 t) (fun τ => Real.exp (-(s * t)) * (f τ * g (t - τ))) := by
        ext τ
        by_cases h : τ ∈ Ioo 0 t
        · have h0 : τ ∈ Ioi (0:ℝ) := h.1
          have h0' : t - τ ∈ Ioi (0:ℝ) := sub_pos.2 h.2
          rw [Set.indicator_of_mem h, hf₁, hg₁, Set.indicator_of_mem h0, Set.indicator_of_mem h0']
          have : Real.exp (-(s * τ)) * Real.exp (-(s * (t - τ))) = Real.exp (-(s * t)) := by
            rw [← Real.exp_add]; congr 1; ring
          rw [← this]; ring
        · rw [Set.indicator_of_notMem h]
          by_cases h0 : τ ∈ Ioi (0:ℝ)
          · have h0' : t - τ ∉ Ioi (0:ℝ) := fun h' => h ⟨h0, by simp only [mem_Ioi] at h'; linarith⟩
            rw [hg₁, Set.indicator_of_notMem h0']; simp
          · rw [hf₁, Set.indicator_of_notMem h0]; simp
      simp only [ht, ↓reduceIte]
      rw [e, integral_indicator measurableSet_Ioo, integral_const_mul]
      unfold conv0
      rw [intervalIntegral.integral_of_le ht.le, integral_Ioc_eq_integral_Ioo]
    · simp only [ht, ↓reduceIte]
      have : (fun τ => f₁ τ * g₁ (t - τ)) = fun _ => 0 := by
        ext τ
        by_cases h0 : τ ∈ Ioi (0:ℝ)
        · have h0' : t - τ ∉ Ioi (0:ℝ) := fun h' => by
            simp only [mem_Ioi] at h0 h'; linarith
          rw [hg₁, Set.indicator_of_notMem h0']; simp
        · rw [hf₁, Set.indicator_of_notMem h0]; simp
      rw [this]; simp
  have hconv := integral_convolution (L := ContinuousLinearMap.mul ℝ ℝ) (μ := volume) (ν := volume) h1 h2
  simp only [ContinuousLinearMap.mul_apply'] at hconv
  have hI : ∀ (u : ℝ → ℝ), ∫ t, Set.indicator (Ioi 0) (fun t => Real.exp (-(s * t)) * u t) t =
      laplace u s := fun u => by
    rw [integral_indicator measurableSet_Ioi]; rfl
  have hint : laplace (conv0 f g) s = ∫ t, convolution f₁ g₁ (ContinuousLinearMap.mul ℝ ℝ) volume t := by
    have hz : ∀ t ∉ Ioi (0:ℝ),
        convolution f₁ g₁ (ContinuousLinearMap.mul ℝ ℝ) volume t = 0 := fun t ht => by
      have : ¬ 0 < t := by simpa using ht
      rw [key]; simp only [this, ↓reduceIte]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    unfold laplace
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have : 0 < t := ht
    rw [key]; simp only [this, ↓reduceIte]
  rw [hint, hconv]
  have a1 := hI f
  have a2 := hI g
  rw [hf₁, hg₁] at *
  rw [a1, a2]

/-- **DE-180.** Lebl Theorem 6.3.1, p. 309 (convolution theorem): for `f, g` continuous on `[0,∞)` of
exponential order `c` and `s > c`, `L{f * g}(s) = F(s) G(s)`. -/
@[kb "lebldiffyqs2026" "Theorem 6.3.1, p. 309"]
theorem laplace_conv0 {f g : ℝ → ℝ} {M N c s : ℝ} (hfc : ContinuousOn f (Ici 0))
    (hgc : ContinuousOn g (Ici 0)) (hf : ExpOrder f M c) (hg : ExpOrder g N c) (hcs : c < s) :
    laplace (conv0 f g) s = laplace f s * laplace g s :=
  laplace_conv0_of_integrable (laplace_integrableOn hfc hf hcs) (laplace_integrableOn hgc hg hcs)

/-- **DE-180 (exponential order of the convolution).** Lebl Theorem 6.3.1, p. 309: if `f, g` have exponential
order `c` then `f * g` has exponential order `c + ε` for every `ε > 0` (in fact `|f*g(t)| ≤ M N t e^{ct}`). -/
@[kb "lebldiffyqs2026" "Theorem 6.3.1, p. 309"]
theorem conv0_expOrder {f g : ℝ → ℝ} {M N c ε : ℝ} (hf : ExpOrder f M c) (hg : ExpOrder g N c)
    (hε : 0 < ε) : ExpOrder (conv0 f g) (M * N / ε) (c + ε) := by
  have hM : 0 ≤ M := by
    have := hf 0 le_rfl; simp only [mul_zero, Real.exp_zero, mul_one] at this
    exact (abs_nonneg _).trans this
  have hN : 0 ≤ N := by
    have := hg 0 le_rfl; simp only [mul_zero, Real.exp_zero, mul_one] at this
    exact (abs_nonneg _).trans this
  intro t ht
  have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
    (f := fun τ => f τ * g (t - τ)) (C := M * N * Real.exp (c * t)) (by
      intro τ hτ
      rw [uIoc_of_le ht] at hτ
      rw [Real.norm_eq_abs, abs_mul]
      calc |f τ| * |g (t - τ)| ≤ (M * Real.exp (c * τ)) * (N * Real.exp (c * (t - τ))) :=
            mul_le_mul (hf τ hτ.1.le) (hg _ (by linarith [hτ.2])) (abs_nonneg _)
              (mul_nonneg hM (Real.exp_pos _).le)
        _ = M * N * Real.exp (c * t) := by
            have : Real.exp (c * τ) * Real.exp (c * (t - τ)) = Real.exp (c * t) := by
              rw [← Real.exp_add]; congr 1; ring
            rw [← this]; ring)
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht] at h1
  unfold conv0
  refine h1.trans ?_
  have h2 : ε * t ≤ Real.exp (ε * t) := by linarith [Real.add_one_le_exp (ε * t)]
  have h3 : Real.exp ((c + ε) * t) = Real.exp (c * t) * Real.exp (ε * t) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h3]
  have hK : 0 ≤ M * N * Real.exp (c * t) := by positivity
  calc M * N * Real.exp (c * t) * t = (M * N / ε) * Real.exp (c * t) * (ε * t) := by
        field_simp
    _ ≤ (M * N / ε) * Real.exp (c * t) * Real.exp (ε * t) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

/-! ### Constant-coefficient equations -/

/-- **DE-173 / DE-175.** Lebl §6.2.4, p. 304 and §6.2 p. 301: for a solution `x` of `p x'' + q x' + r x = f(t)`
on `[0,∞)` (all of `x, x', x''` of exponential order `c`, `x''` continuous), and `s > c`,
`(p s² + q s + r) X(s) = F(s) + p (s x(0) + x'(0)) + q x(0)`. -/
@[kb "lebldiffyqs2026" "Solving ODEs with the Laplace transform, p. 301"]
theorem laplace_ode₂ {x x' x'' f : ℝ → ℝ} {p q r M M' M'' c s : ℝ}
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (x' t) t) (hx' : ∀ t, 0 ≤ t → HasDerivAt x' (x'' t) t)
    (hx''c : ContinuousOn x'' (Ici 0))
    (hb : ExpOrder x M c) (hb' : ExpOrder x' M' c) (hb'' : ExpOrder x'' M'' c) (hcs : c < s)
    (heq : ∀ t, 0 ≤ t → p * x'' t + q * x' t + r * x t = f t) :
    (p * s ^ 2 + q * s + r) * laplace x s =
      laplace f s + p * (s * x 0 + x' 0) + q * x 0 := by
  have hx'c : ContinuousOn x' (Ici 0) := fun t ht => (hx' t ht).continuousAt.continuousWithinAt
  have hxc : ContinuousOn x (Ici 0) := fun t ht => (hx t ht).continuousAt.continuousWithinAt
  have i0 := laplace_integrableOn hxc hb hcs
  have i1 := laplace_integrableOn hx'c hb' hcs
  have i2 := laplace_integrableOn hx''c hb'' hcs
  have hL : laplace f s = p * laplace x'' s + q * laplace x' s + r * laplace x s := by
    unfold laplace
    have j1 : IntegrableOn (fun t => p * (Real.exp (-(s * t)) * x'' t) +
        q * (Real.exp (-(s * t)) * x' t)) (Ioi 0) := (i2.const_mul p).add (i1.const_mul q)
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
      ← integral_add (i2.const_mul p) (i1.const_mul q), ← integral_add j1 (i0.const_mul r)]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [← heq t (le_of_lt ht)]; ring
  have d1 := laplace_deriv hx hx'c hb hb' hcs
  have d2 := laplace_deriv hx' hx''c hb' hb'' hcs
  rw [hL, d2, d1]; ring

/-- **DE-175 (transfer function).** Lebl §6.2.4, p. 304: with zero initial data, `(p s² + q s + r) X(s) = F(s)`,
i.e. `X = H F` with `H = 1/(p s² + q s + r)`. -/
@[kb "lebldiffyqs2026" "Transfer functions, p. 304"]
theorem laplace_transfer {x x' x'' f : ℝ → ℝ} {p q r M M' M'' c s : ℝ}
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (x' t) t) (hx' : ∀ t, 0 ≤ t → HasDerivAt x' (x'' t) t)
    (hx''c : ContinuousOn x'' (Ici 0))
    (hb : ExpOrder x M c) (hb' : ExpOrder x' M' c) (hb'' : ExpOrder x'' M'' c) (hcs : c < s)
    (heq : ∀ t, 0 ≤ t → p * x'' t + q * x' t + r * x t = f t) (h0 : x 0 = 0) (h0' : x' 0 = 0) :
    (p * s ^ 2 + q * s + r) * laplace x s = laplace f s := by
  have := laplace_ode₂ hx hx' hx''c hb hb' hb'' hcs heq
  rw [h0, h0'] at this
  linarith

/-- **DE-173 (Example 6.2.1).** Lebl p. 300: a solution of `x'' + x = cos 2t`, `x(0) = 0`, `x'(0) = 1`
(with the exponential-order hypotheses) has `(s² + 1) X(s) = s/(s² + 4) + 1` for `s > 0`. -/
@[kb "lebldiffyqs2026" "Example 6.2.1, p. 300"]
theorem laplace_example_cos2 {x x' x'' : ℝ → ℝ} {M M' M'' s : ℝ}
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (x' t) t) (hx' : ∀ t, 0 ≤ t → HasDerivAt x' (x'' t) t)
    (hx''c : ContinuousOn x'' (Ici 0))
    (hb : ExpOrder x M 0) (hb' : ExpOrder x' M' 0) (hb'' : ExpOrder x'' M'' 0) (hs : 0 < s)
    (heq : ∀ t, 0 ≤ t → x'' t + x t = Real.cos (2 * t)) (h0 : x 0 = 0) (h1 : x' 0 = 1) :
    (s ^ 2 + 1) * laplace x s = s / (s ^ 2 + 2 ^ 2) + 1 := by
  have := laplace_ode₂ (p := 1) (q := 0) (r := 1) (f := fun t => Real.cos (2 * t))
    hx hx' hx''c hb hb' hb'' hs (fun t ht => by have := heq t ht; linarith)
  rw [(laplace_sin_cos 2 hs).2, h0, h1] at this
  linarith

end UndergradKB.DifferentialEquations
