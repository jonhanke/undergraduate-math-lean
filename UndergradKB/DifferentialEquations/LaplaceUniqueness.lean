import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Calculus.MeanValue
import UndergradKB.DifferentialEquations.Laplace
import UndergradKB.Common.Attr

/-! # Uniqueness of the Laplace transform and related facts (Lebl, *Notes on Diffy Qs*, Chapters 6.1 to 6.4)

* Lerch's uniqueness theorem (DE-168), proved by Weierstrass approximation applied to the weight
  `w(t) = e^{-at} h(t)` and the continuous function `q` with `q(e^{-t}) = w(t)`;
* the inverse transform is well defined and linear (DE-169);
* the Duhamel formula and the impulse response (DE-181, DE-186);
* Volterra equations (DE-182);
* `sinh`, `cosh` (DE-164) and the limit of the rectangular pulse quotient (DE-183). -/

open Real Set Filter Topology MeasureTheory

namespace UndergradKB.DifferentialEquations

lemma lu_expOrder_nonneg {f : ℝ → ℝ} {M c : ℝ} (h : ExpOrder f M c) : 0 ≤ M := by
  have := h 0 le_rfl
  simp only [mul_zero, Real.exp_zero, mul_one] at this
  exact (abs_nonneg _).trans this

lemma lu_expOrder_mono {f : ℝ → ℝ} {M c d : ℝ} (h : ExpOrder f M c) (hcd : c ≤ d) :
    ExpOrder f M d := fun t ht =>
  (h t ht).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hcd ht)) (lu_expOrder_nonneg h))

lemma lu_expOrder_exp (a : ℝ) : ExpOrder (fun t => Real.exp (a * t)) 1 a := fun t _ => by
  rw [abs_of_pos (Real.exp_pos _), one_mul]

/-- Core of Lerch's theorem: if all the transforms `laplace h (a + n)` vanish, `h = 0` on `[0,∞)`. -/
theorem lu_core {h : ℝ → ℝ} {M c a : ℝ} (hc : ContinuousOn h (Ici 0)) (hb : ExpOrder h M c)
    (ha : c < a) (h0 : ∀ n : ℕ, laplace h (a + n) = 0) : ∀ t, 0 ≤ t → h t = 0 := by
  have hM := lu_expOrder_nonneg hb
  set w : ℝ → ℝ := fun t => Real.exp (-(a * t)) * h t with hw
  have hexpc : ContinuousOn (fun t : ℝ => Real.exp (-(a * t))) (Ici 0) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).continuousOn
  have hwc : ContinuousOn w (Ici 0) := hexpc.mul hc
  have hwint : IntegrableOn w (Ioi 0) := laplace_integrableOn hc hb ha
  have hwb : ∀ t, 0 ≤ t → |w t| ≤ M := by
    intro t ht
    have e : Real.exp (-(a * t)) * (M * Real.exp (c * t)) = M * Real.exp (-(a - c) * t) := by
      rw [← mul_assoc, mul_comm (Real.exp _) M, mul_assoc, ← Real.exp_add]
      ring_nf
    have h1 : Real.exp (-(a - c) * t) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    calc |w t| = Real.exp (-(a * t)) * |h t| := by
          rw [hw]; simp only [abs_mul, abs_of_pos (Real.exp_pos _)]
      _ ≤ Real.exp (-(a * t)) * (M * Real.exp (c * t)) :=
          mul_le_mul_of_nonneg_left (hb t ht) (Real.exp_pos _).le
      _ = M * Real.exp (-(a - c) * t) := e
      _ ≤ M := by nlinarith
  have hwlim : Tendsto w atTop (𝓝 0) := laplace_integrand_tendsto hb ha
  -- the function `q` with `q (e^{-t}) = w t`
  set q : ℝ → ℝ := fun u => if u ≤ 0 then 0 else w (max 0 (-Real.log u)) with hq
  have hqw : ∀ t, 0 ≤ t → q (Real.exp (-t)) = w t := by
    intro t ht
    have hp : ¬ Real.exp (-t) ≤ 0 := not_le.2 (Real.exp_pos _)
    simp only [hq, hp, ite_false, Real.log_exp, neg_neg]
    rw [max_eq_right ht]
  have hqc : ContinuousOn q (Icc 0 1) := by
    intro u hu
    by_cases hu0 : 0 < u
    · have h1 : ContinuousOn (fun u : ℝ => w (max 0 (-Real.log u))) (Ioi 0) := by
        refine hwc.comp (f := fun u : ℝ => max 0 (-Real.log u)) ?_ ?_
        · exact (continuous_const.max continuous_id).comp_continuousOn
            (Real.continuousOn_log.mono (fun x hx => ne_of_gt hx)).neg
        · intro x _; show (0:ℝ) ≤ max 0 (-Real.log x); exact le_max_left _ _
      have h2 : ContinuousAt (fun u : ℝ => w (max 0 (-Real.log u))) u :=
        h1.continuousAt (Ioi_mem_nhds hu0)
      have h3 : ∀ᶠ x in 𝓝 u, q x = w (max 0 (-Real.log x)) := by
        filter_upwards [Ioi_mem_nhds hu0] with x hx
        have hx' : ¬ x ≤ 0 := not_le.2 hx
        simp only [hq, hx', ite_false]
      exact (h2.congr (h3.mono fun x hx => hx.symm)).continuousWithinAt
    · have hu0' : u = 0 := le_antisymm (not_lt.1 hu0) hu.1
      subst hu0'
      rw [Metric.continuousWithinAt_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hwlim ε hε
      refine ⟨Real.exp (-(max N 0)), Real.exp_pos _, ?_⟩
      intro x _ hx
      have hq0 : q 0 = 0 := by simp [hq]
      rw [hq0]
      by_cases hx0 : x ≤ 0
      · simp [hq, hx0, hε]
      · have hxp : 0 < x := not_le.1 hx0
        have hlt : x < Real.exp (-(max N 0)) := by
          rw [Real.dist_eq, sub_zero, abs_of_pos hxp] at hx; exact hx
        have hl : Real.log x < -(max N 0) := by
          rw [Real.log_lt_iff_lt_exp hxp]; exact hlt
        have hm : max 0 (-Real.log x) = -Real.log x :=
          max_eq_right (by linarith [le_max_right N 0])
        simp only [hq, hx0, ite_false, hm]
        have := hN (-Real.log x) (by linarith [le_max_left N 0])
        simpa using this
  -- polynomials against the weight
  have hpoly : ∀ p : Polynomial ℝ,
      IntegrableOn (fun t => w t * p.eval (Real.exp (-t))) (Ioi 0) ∧
        ∫ t in Ioi (0:ℝ), w t * p.eval (Real.exp (-t)) = 0 := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq' =>
      have e : (fun t => w t * (p + q).eval (Real.exp (-t))) =
          fun t => w t * p.eval (Real.exp (-t)) + w t * q.eval (Real.exp (-t)) := by
        ext t; simp [Polynomial.eval_add, mul_add]
      rw [e]
      refine ⟨hp.1.add hq'.1, ?_⟩
      rw [integral_add hp.1 hq'.1, hp.2, hq'.2, add_zero]
    | monomial n k =>
      have e : (fun t => w t * (Polynomial.monomial n k).eval (Real.exp (-t))) =
          fun t => k * (Real.exp (-((a + n) * t)) * h t) := by
        ext t
        rw [Polynomial.eval_monomial, ← Real.exp_nat_mul]
        have : Real.exp (-((a + n) * t)) = Real.exp (-(a * t)) * Real.exp (n * -t) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [this, hw]; ring
      have hnn : (0:ℝ) ≤ n := n.cast_nonneg
      have hi := laplace_integrableOn hc hb (s := a + n) (by linarith)
      rw [e]
      refine ⟨hi.const_mul k, ?_⟩
      rw [integral_const_mul]
      have := h0 n
      unfold laplace at this
      rw [this, mul_zero]
  have hwwint : IntegrableOn (fun t => w t * w t) (Ioi 0) := by
    refine Integrable.mono' (hwint.norm.const_mul M) ?_ ?_
    · exact ((hwc.mono Ioi_subset_Ici_self).mul
        (hwc.mono Ioi_subset_Ici_self)).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.norm_eq_abs, abs_mul]
      calc |w t| * |w t| ≤ M * |w t| :=
            mul_le_mul_of_nonneg_right (hwb t (le_of_lt ht)) (abs_nonneg _)
        _ = M * ‖w t‖ := by rw [Real.norm_eq_abs]
  set K : ℝ := ∫ t in Ioi (0:ℝ), ‖w t‖ with hK
  have hK0 : 0 ≤ K := integral_nonneg (fun _ => norm_nonneg _)
  set I : ℝ := ∫ t in Ioi (0:ℝ), w t * w t with hI
  have hbound : ∀ ε, 0 < ε → |I| ≤ ε * K := by
    intro ε hε
    obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 q hqc ε hε
    have hI' : I = ∫ t in Ioi (0:ℝ), (w t * w t - w t * p.eval (Real.exp (-t))) := by
      rw [integral_sub hwwint (hpoly p).1, (hpoly p).2, sub_zero]
    have hn := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (0:ℝ)))
      (f := fun t => w t * w t - w t * p.eval (Real.exp (-t))) (g := fun t => ε * ‖w t‖)
      (hwint.norm.const_mul ε) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : 0 ≤ t := le_of_lt ht
        have hmem : Real.exp (-t) ∈ Icc (0:ℝ) 1 :=
          ⟨(Real.exp_pos _).le, by rw [Real.exp_le_one_iff]; linarith⟩
        have h1 := hp _ hmem
        rw [hqw t ht0] at h1
        rw [Real.norm_eq_abs, ← mul_sub, abs_mul, Real.norm_eq_abs, mul_comm ε]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [abs_sub_comm]; exact h1.le)
    rw [integral_const_mul, Real.norm_eq_abs, ← hI'] at hn
    exact hn
  have hI0 : I = 0 := by
    by_contra hne
    have hpos : 0 < |I| := abs_pos.2 hne
    have h1 := hbound (|I| / (K + 1)) (div_pos hpos (by linarith))
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)] at h1
    nlinarith
  have hae := (integral_eq_zero_iff_of_nonneg (μ := volume.restrict (Ioi (0:ℝ)))
    (f := fun t => w t * w t) (fun t => mul_self_nonneg (w t)) hwwint).1 hI0
  have hzero : EqOn (fun t => w t * w t) (fun _ => 0) (Ioi 0) :=
    Measure.eqOn_of_ae_eq (μ := volume) (s := Ioi (0:ℝ)) hae
      ((hwc.mono Ioi_subset_Ici_self).mul (hwc.mono Ioi_subset_Ici_self)) continuousOn_const
      (by rw [interior_Ioi]; exact subset_closure)
  have hw0 : EqOn w (fun _ => 0) (Ioi 0) := fun t ht => mul_self_eq_zero.1 (hzero ht)
  have hw0' : EqOn w (fun _ => 0) (Ici 0) :=
    hw0.of_subset_closure hwc continuousOn_const Ioi_subset_Ici_self (by rw [closure_Ioi])
  intro t ht
  have := hw0' ht
  simp only [hw] at this
  rcases mul_eq_zero.1 this with h1 | h1
  · exact absurd h1 (Real.exp_pos _).ne'
  · exact h1

/-- **DE-168 (Lerch uniqueness).** Lebl Theorem 6.1.3, p. 297: if `f, g` are continuous on `[0,∞)` and of
exponential order and their transforms agree for all large `s`, then `f = g` on `[0,∞)`. -/
@[kb "lebldiffyqs2026" "Theorem 6.1.3, p. 297"]
theorem laplace_unique {f g : ℝ → ℝ} {M N c d : ℝ} (hfc : ContinuousOn f (Ici 0))
    (hgc : ContinuousOn g (Ici 0)) (hf : ExpOrder f M c) (hg : ExpOrder g N d)
    (heq : ∀ᶠ s in atTop, laplace f s = laplace g s) : ∀ t, 0 ≤ t → f t = g t := by
  obtain ⟨s₀, hs₀⟩ := eventually_atTop.1 heq
  set e := max c d with he
  have hf' : ExpOrder f M e := lu_expOrder_mono hf (le_max_left _ _)
  have hg' : ExpOrder g N e := lu_expOrder_mono hg (le_max_right _ _)
  set a := max s₀ e + 1 with ha
  have hea : e < a := by have := le_max_right s₀ e; linarith
  have hs0a : s₀ ≤ a := by have := le_max_left s₀ e; linarith
  have hb : ExpOrder (fun t => 1 * f t + (-1) * g t) (M + N) e := by
    intro t ht
    have h1 := abs_le.1 (hf' t ht)
    have h2 := abs_le.1 (hg' t ht)
    rw [abs_le]
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
  have hc : ContinuousOn (fun t => 1 * f t + (-1) * g t) (Ici 0) :=
    (continuousOn_const.mul hfc).add (continuousOn_const.mul hgc)
  have h0 : ∀ n : ℕ, laplace (fun t => 1 * f t + (-1) * g t) (a + n) = 0 := by
    intro n
    have hnn : (0:ℝ) ≤ n := n.cast_nonneg
    rw [laplace_add_smul 1 (-1) (laplace_integrableOn hfc hf' (by linarith))
      (laplace_integrableOn hgc hg' (by linarith)), hs₀ (a + n) (by linarith)]
    ring
  intro t ht
  have := lu_core hc hb hea h0 t ht
  linarith

/-- **DE-168 (Lerch uniqueness, `s > s₀` form).** Lebl Theorem 6.1.3, p. 297. -/
@[kb "lebldiffyqs2026" "Theorem 6.1.3, p. 297"]
theorem laplace_unique_of_gt {f g : ℝ → ℝ} {M N c d s₀ : ℝ} (hfc : ContinuousOn f (Ici 0))
    (hgc : ContinuousOn g (Ici 0)) (hf : ExpOrder f M c) (hg : ExpOrder g N d)
    (heq : ∀ s, s₀ < s → laplace f s = laplace g s) : ∀ t, 0 ≤ t → f t = g t :=
  laplace_unique hfc hgc hf hg ((eventually_gt_atTop s₀).mono heq)

/-! ### The inverse transform (DE-169) -/

/-- `f` is an inverse Laplace transform of `F`: continuous on `[0,∞)`, of exponential order, with
`laplace f s = F s` for all large `s`. -/
def IsLaplaceInverse (f F : ℝ → ℝ) : Prop :=
  ContinuousOn f (Ici 0) ∧ (∃ M c, ExpOrder f M c) ∧ ∀ᶠ s in atTop, laplace f s = F s

/-- **DE-169 (well defined).** Lebl Theorem 6.1.3, p. 297: the inverse transform is unique on `[0,∞)`. -/
@[kb "lebldiffyqs2026" "Theorem 6.1.3, p. 297"]
theorem laplaceInverse_unique {f g F : ℝ → ℝ} (hf : IsLaplaceInverse f F)
    (hg : IsLaplaceInverse g F) : ∀ t, 0 ≤ t → f t = g t := by
  obtain ⟨hfc, ⟨M, c, hfb⟩, hfe⟩ := hf
  obtain ⟨hgc, ⟨N, d, hgb⟩, hge⟩ := hg
  exact laplace_unique hfc hgc hfb hgb (by filter_upwards [hfe, hge] with s h1 h2; rw [h1, h2])

/-- **DE-169 (linearity).** Lebl §6.1, p. 297: if `f` inverts `F` and `g` inverts `G` then `a f + b g` inverts
`a F + b G`. -/
@[kb "lebldiffyqs2026" "Theorem 6.1.3 (linearity of the inverse), p. 297"]
theorem laplaceInverse_linear {f g F G : ℝ → ℝ} (a b : ℝ) (hf : IsLaplaceInverse f F)
    (hg : IsLaplaceInverse g G) :
    IsLaplaceInverse (fun t => a * f t + b * g t) (fun s => a * F s + b * G s) := by
  obtain ⟨hfc, ⟨M, c, hfb⟩, hfe⟩ := hf
  obtain ⟨hgc, ⟨N, d, hgb⟩, hge⟩ := hg
  have hf' : ExpOrder f M (max c d) := lu_expOrder_mono hfb (le_max_left _ _)
  have hg' : ExpOrder g N (max c d) := lu_expOrder_mono hgb (le_max_right _ _)
  refine ⟨(continuousOn_const.mul hfc).add (continuousOn_const.mul hgc),
    ⟨|a| * M + |b| * N, max c d, ?_⟩, ?_⟩
  · intro t ht
    have h1 := hf' t ht
    have h2 := hg' t ht
    calc |a * f t + b * g t| ≤ |a * f t| + |b * g t| := abs_add_le _ _
      _ = |a| * |f t| + |b| * |g t| := by rw [abs_mul, abs_mul]
      _ ≤ |a| * (M * Real.exp (max c d * t)) + |b| * (N * Real.exp (max c d * t)) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
            (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
      _ = _ := by ring
  · filter_upwards [hfe, hge, eventually_gt_atTop (max c d)] with s h1 h2 h3
    rw [laplace_add_smul a b (laplace_integrableOn hfc hf' h3) (laplace_integrableOn hgc hg' h3), h1, h2]

/-- **DE-169 (the inverse of `a F + b G`).** Lebl Theorem 6.1.3, p. 297: any inverse of `a F + b G` equals
`a f + b g` on `[0,∞)`. -/
@[kb "lebldiffyqs2026" "Theorem 6.1.3 (linearity of the inverse), p. 297"]
theorem laplaceInverse_linear_eq {f g F G k : ℝ → ℝ} (a b : ℝ) (hf : IsLaplaceInverse f F)
    (hg : IsLaplaceInverse g G) (hk : IsLaplaceInverse k (fun s => a * F s + b * G s)) :
    ∀ t, 0 ≤ t → k t = a * f t + b * g t :=
  laplaceInverse_unique hk (laplaceInverse_linear a b hf hg)

/-! ### Duhamel's formula (DE-181) -/

/-- Lebl Example 6.3.4, p. 309: `x(t) = (1/ω) ∫_0^t f(τ) sin(ω(t-τ)) dτ`. -/
noncomputable def duhamelSol (ω : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ω⁻¹ * ∫ τ in (0:ℝ)..t, f τ * Real.sin (ω * (t - τ))

/-- Its velocity `x'(t) = ∫_0^t f(τ) cos(ω(t-τ)) dτ`. -/
noncomputable def duhamelVel (ω : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ τ in (0:ℝ)..t, f τ * Real.cos (ω * (t - τ))

private lemma lu_C_cont {f : ℝ → ℝ} (hf : Continuous f) (ω : ℝ) :
    Continuous fun τ => f τ * Real.cos (ω * τ) := by fun_prop

private lemma lu_S_cont {f : ℝ → ℝ} (hf : Continuous f) (ω : ℝ) :
    Continuous fun τ => f τ * Real.sin (ω * τ) := by fun_prop

private lemma lu_duhamelSol_eq {f : ℝ → ℝ} (hf : Continuous f) (ω t : ℝ) :
    duhamelSol ω f t = ω⁻¹ * (Real.sin (ω * t) * (∫ τ in (0:ℝ)..t, f τ * Real.cos (ω * τ)) -
      Real.cos (ω * t) * ∫ τ in (0:ℝ)..t, f τ * Real.sin (ω * τ)) := by
  unfold duhamelSol
  congr 1
  have ia : IntervalIntegrable (fun τ => Real.sin (ω * t) * (f τ * Real.cos (ω * τ))) volume 0 t :=
    (by have := lu_C_cont hf ω; fun_prop : Continuous _).intervalIntegrable _ _
  have ib : IntervalIntegrable (fun τ => Real.cos (ω * t) * (f τ * Real.sin (ω * τ))) volume 0 t :=
    (by have := lu_S_cont hf ω; fun_prop : Continuous _).intervalIntegrable _ _
  have e : (fun τ => f τ * Real.sin (ω * (t - τ))) = fun τ =>
      Real.sin (ω * t) * (f τ * Real.cos (ω * τ)) - Real.cos (ω * t) * (f τ * Real.sin (ω * τ)) := by
    ext τ; rw [mul_sub, Real.sin_sub]; ring
  rw [e, intervalIntegral.integral_sub ia ib, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]

private lemma lu_duhamelVel_eq {f : ℝ → ℝ} (hf : Continuous f) (ω t : ℝ) :
    duhamelVel ω f t = Real.cos (ω * t) * (∫ τ in (0:ℝ)..t, f τ * Real.cos (ω * τ)) +
      Real.sin (ω * t) * ∫ τ in (0:ℝ)..t, f τ * Real.sin (ω * τ) := by
  unfold duhamelVel
  have ia : IntervalIntegrable (fun τ => Real.cos (ω * t) * (f τ * Real.cos (ω * τ))) volume 0 t :=
    (by have := lu_C_cont hf ω; fun_prop : Continuous _).intervalIntegrable _ _
  have ib : IntervalIntegrable (fun τ => Real.sin (ω * t) * (f τ * Real.sin (ω * τ))) volume 0 t :=
    (by have := lu_S_cont hf ω; fun_prop : Continuous _).intervalIntegrable _ _
  have e : (fun τ => f τ * Real.cos (ω * (t - τ))) = fun τ =>
      Real.cos (ω * t) * (f τ * Real.cos (ω * τ)) + Real.sin (ω * t) * (f τ * Real.sin (ω * τ)) := by
    ext τ; rw [mul_sub, Real.cos_sub]; ring
  rw [e, intervalIntegral.integral_add ia ib, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]

/-- **DE-181.** Lebl Example 6.3.4, p. 309 (Duhamel's formula): for continuous `f` and `ω ≠ 0`, the function
`x(t) = (1/ω) ∫_0^t f(τ) sin(ω(t-τ)) dτ` has derivative `x'(t) = ∫_0^t f(τ) cos(ω(t-τ)) dτ`, whose derivative
is `f(t) - ω² x(t)` (so `x'' + ω² x = f`), and `x(0) = x'(0) = 0`. -/
@[kb "lebldiffyqs2026" "Example 6.3.4, p. 309"]
theorem duhamel {f : ℝ → ℝ} (hf : Continuous f) {ω : ℝ} (hω : ω ≠ 0) :
    (∀ t, HasDerivAt (duhamelSol ω f) (duhamelVel ω f t) t) ∧
    (∀ t, HasDerivAt (duhamelVel ω f) (f t - ω ^ 2 * duhamelSol ω f t) t) ∧
    duhamelSol ω f 0 = 0 ∧ duhamelVel ω f 0 = 0 := by
  have hC : ∀ t, HasDerivAt (fun u => ∫ τ in (0:ℝ)..u, f τ * Real.cos (ω * τ))
      (f t * Real.cos (ω * t)) t := fun t =>
    ((lu_C_cont hf ω).integral_hasStrictDerivAt 0 t).hasDerivAt
  have hS : ∀ t, HasDerivAt (fun u => ∫ τ in (0:ℝ)..u, f τ * Real.sin (ω * τ))
      (f t * Real.sin (ω * t)) t := fun t =>
    ((lu_S_cont hf ω).integral_hasStrictDerivAt 0 t).hasDerivAt
  have hsin : ∀ t, HasDerivAt (fun u => Real.sin (ω * u)) (Real.cos (ω * t) * (ω * 1)) t :=
    fun t => ((hasDerivAt_id' t).const_mul ω).sin
  have hcos : ∀ t, HasDerivAt (fun u => Real.cos (ω * u)) (-Real.sin (ω * t) * (ω * 1)) t :=
    fun t => ((hasDerivAt_id' t).const_mul ω).cos
  have hinv : ω⁻¹ * ω = 1 := inv_mul_cancel₀ hω
  have hs2 : ∀ t, Real.sin (ω * t) ^ 2 + Real.cos (ω * t) ^ 2 = 1 := fun t =>
    Real.sin_sq_add_cos_sq _
  have hx : duhamelSol ω f = fun t => ω⁻¹ * (Real.sin (ω * t) *
      (∫ τ in (0:ℝ)..t, f τ * Real.cos (ω * τ)) - Real.cos (ω * t) *
      ∫ τ in (0:ℝ)..t, f τ * Real.sin (ω * τ)) := funext (lu_duhamelSol_eq hf ω)
  have hv : duhamelVel ω f = fun t => Real.cos (ω * t) *
      (∫ τ in (0:ℝ)..t, f τ * Real.cos (ω * τ)) + Real.sin (ω * t) *
      ∫ τ in (0:ℝ)..t, f τ * Real.sin (ω * τ) := funext (lu_duhamelVel_eq hf ω)
  refine ⟨fun t => ?_, fun t => ?_, ?_, ?_⟩
  · rw [hx]
    have := (((hsin t).fun_mul (hC t)).fun_sub ((hcos t).fun_mul (hS t))).const_mul ω⁻¹
    convert this using 1
    rw [lu_duhamelVel_eq hf ω t]
    set Ct := ∫ τ in (0:ℝ)..t, f τ * Real.cos (ω * τ)
    set St := ∫ τ in (0:ℝ)..t, f τ * Real.sin (ω * τ)
    linear_combination (-(Real.cos (ω * t) * Ct + Real.sin (ω * t) * St)) * hinv
  · rw [hv]
    have := ((hcos t).fun_mul (hC t)).fun_add ((hsin t).fun_mul (hS t))
    convert this using 1
    rw [lu_duhamelSol_eq hf ω t]
    set Ct := ∫ τ in (0:ℝ)..t, f τ * Real.cos (ω * τ)
    set St := ∫ τ in (0:ℝ)..t, f τ * Real.sin (ω * τ)
    linear_combination (-(f t)) * (hs2 t) + (-ω * (Real.sin (ω * t) * Ct - Real.cos (ω * t) * St)) * hinv
  · simp [duhamelSol]
  · simp [duhamelVel]

/-! ### Impulse response (DE-186) -/

/-- **DE-186 (transform of the impulse response).** Lebl §6.4.2, p. 314: `h(t) = sin(ω₀ t)/ω₀` has
`H(s) = 1/(s² + ω₀²)` for `s > 0`. -/
@[kb "lebldiffyqs2026" "Impulse response, p. 314"]
theorem laplace_impulse_response {ω : ℝ} (hω : ω ≠ 0) {s : ℝ} (hs : 0 < s) :
    laplace (fun t => Real.sin (ω * t) / ω) s = 1 / (s ^ 2 + ω ^ 2) := by
  have e : (fun t => Real.sin (ω * t) / ω) = fun t => ω⁻¹ * Real.sin (ω * t) := by
    ext t; rw [div_eq_inv_mul]
  rw [e, laplace_const_mul, (laplace_sin_cos ω hs).1]
  have : s ^ 2 + ω ^ 2 ≠ 0 := by positivity
  field_simp

/-- The Duhamel solution is the convolution of `f` with the impulse response. -/
theorem duhamelSol_eq_conv0 (ω : ℝ) (f : ℝ → ℝ) :
    duhamelSol ω f = conv0 f (fun t => Real.sin (ω * t) / ω) := by
  ext t
  unfold duhamelSol conv0
  rw [← intervalIntegral.integral_const_mul]
  congr 1; ext τ
  simp only [div_eq_inv_mul]; ring

/-- **DE-186 (zero-data response is a convolution).** Lebl §6.4.2, p. 314: for `f` continuous and `ω₀ ≠ 0`, the
function `x = f * h` (`h(t) = sin(ω₀ t)/ω₀`) satisfies `x'' + ω₀² x = f`, `x(0) = x'(0) = 0`, with
`x'(t) = ∫_0^t f(τ) cos(ω₀(t-τ)) dτ`. -/
@[kb "lebldiffyqs2026" "Impulse response, p. 314"]
theorem conv0_impulse_solves {f : ℝ → ℝ} (hf : Continuous f) {ω : ℝ} (hω : ω ≠ 0) :
    (∀ t, HasDerivAt (conv0 f (fun t => Real.sin (ω * t) / ω)) (duhamelVel ω f t) t) ∧
    (∀ t, HasDerivAt (duhamelVel ω f)
      (f t - ω ^ 2 * conv0 f (fun t => Real.sin (ω * t) / ω) t) t) ∧
    conv0 f (fun t => Real.sin (ω * t) / ω) 0 = 0 ∧ duhamelVel ω f 0 = 0 := by
  rw [← duhamelSol_eq_conv0]
  exact duhamel hf hω

/-- **DE-186 (uniqueness of the zero-data solution).** Any `y` with `y'' = f - ω² y` on `[0,∞)` and
`y(0) = y'(0) = 0` equals `f * h` there. -/
@[kb "lebldiffyqs2026" "Impulse response, p. 314"]
theorem conv0_impulse_unique {f : ℝ → ℝ} (hf : Continuous f) {ω : ℝ} (hω : ω ≠ 0) {y y' : ℝ → ℝ}
    (hy : ∀ t, 0 ≤ t → HasDerivAt y (y' t) t)
    (hy' : ∀ t, 0 ≤ t → HasDerivAt y' (f t - ω ^ 2 * y t) t) (h0 : y 0 = 0) (h0' : y' 0 = 0) :
    ∀ t, 0 ≤ t → y t = conv0 f (fun t => Real.sin (ω * t) / ω) t := by
  obtain ⟨d1, d2, d3, d4⟩ := duhamel hf hω
  rw [← duhamelSol_eq_conv0]
  set E : ℝ → ℝ := fun t => (y' t - duhamelVel ω f t) ^ 2 + ω ^ 2 * (y t - duhamelSol ω f t) ^ 2
    with hE
  intro T hT
  have hcont : ContinuousOn E (Icc 0 T) := by
    intro t ht
    have a1 := (hy t ht.1).continuousAt
    have a2 := (hy' t ht.1).continuousAt
    have a3 := (d1 t).continuousAt
    have a4 := (d2 t).continuousAt
    exact ((((a2.sub a4).pow 2).add (continuousAt_const.mul ((a1.sub a3).pow 2)))).continuousWithinAt
  have hder : ∀ t ∈ Ico 0 T, HasDerivWithinAt E 0 (Ici t) t := by
    intro t ht
    have e1 := ((hy' t ht.1).fun_sub (d2 t)).fun_pow 2
    have e2 := (((hy t ht.1).fun_sub (d1 t)).fun_pow 2).const_mul (ω ^ 2)
    have := e1.fun_add e2
    refine (this.congr_deriv ?_).hasDerivWithinAt
    simp only [Nat.cast_ofNat]
    ring
  have := constant_of_has_deriv_right_zero hcont hder T ⟨hT, le_rfl⟩
  have hE0 : E 0 = 0 := by simp [hE, h0, h0', d3, d4]
  rw [hE0] at this
  simp only [hE] at this
  have hω2 : 0 < ω ^ 2 := by positivity
  have h1 : 0 ≤ (y' T - duhamelVel ω f T) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ ω ^ 2 * (y T - duhamelSol ω f T) ^ 2 := by positivity
  have h3 : ω ^ 2 * (y T - duhamelSol ω f T) ^ 2 = 0 := by linarith
  have h4 : (y T - duhamelSol ω f T) ^ 2 = 0 := by
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd h hω2.ne'
    · exact h
  have := pow_eq_zero_iff (two_ne_zero) |>.1 h4
  linarith

/-! ### Volterra integral equations (DE-182) -/

/-- **DE-182.** Lebl §6.3.2, p. 310: if `x = f + g * x` on `[0,∞)` with `f, g, x` continuous of exponential
order `c`, then for `s > c` with `G(s) ≠ 1`, `X(s) = F(s) / (1 - G(s))`. -/
@[kb "lebldiffyqs2026" "Integral equations, p. 310"]
theorem laplace_volterra {f g x : ℝ → ℝ} {M N P c s : ℝ} (hfc : ContinuousOn f (Ici 0))
    (hgc : ContinuousOn g (Ici 0)) (hxc : ContinuousOn x (Ici 0)) (hf : ExpOrder f M c)
    (hg : ExpOrder g N c) (hx : ExpOrder x P c) (hcs : c < s)
    (heq : ∀ t, 0 ≤ t → x t = f t + conv0 g x t) (hG : laplace g s ≠ 1) :
    laplace x s = laplace f s / (1 - laplace g s) := by
  have i1 := laplace_integrableOn hfc hf hcs
  have i2 := laplace_integrableOn hxc hx hcs
  have i3 := laplace_integrableOn hgc hg hcs
  have hconv := laplace_conv0_of_integrable i3 i2
  have h1 : laplace (conv0 g x) s = laplace x s - laplace f s := by
    unfold laplace
    rw [← integral_sub i2 i1]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have := heq t (le_of_lt ht)
    rw [← mul_sub]
    congr 1
    linarith
  have hne : 1 - laplace g s ≠ 0 := fun h => hG (by linarith)
  rw [eq_div_iff hne]
  rw [h1] at hconv
  linarith

/-! ### Hyperbolic functions (DE-164) -/

private lemma lu_laplace_sinh_cosh (ω : ℝ) {s : ℝ} (hs : |ω| < s) :
    laplace (fun t => (1/2 : ℝ) * Real.exp (ω * t) + (1/2 : ℝ) * Real.exp ((-ω) * t)) s =
      s / (s ^ 2 - ω ^ 2) ∧
    laplace (fun t => (1/2 : ℝ) * Real.exp (ω * t) + (-(1/2) : ℝ) * Real.exp ((-ω) * t)) s =
      ω / (s ^ 2 - ω ^ 2) := by
  have h1 : ω < s := lt_of_le_of_lt (le_abs_self ω) hs
  have h2 : -ω < s := lt_of_le_of_lt (neg_le_abs ω) hs
  have i1 := laplace_integrableOn (f := fun t => Real.exp (ω * t)) (M := 1) (c := ω) (s := s)
    (by fun_prop) (lu_expOrder_exp ω) h1
  have i2 := laplace_integrableOn (f := fun t => Real.exp ((-ω) * t)) (M := 1) (c := -ω) (s := s)
    (by fun_prop) (lu_expOrder_exp (-ω)) h2
  have e1 := laplace_exp h1
  have e2 := laplace_exp h2
  have hp : s - ω ≠ 0 := by linarith
  have hm : s - -ω ≠ 0 := by linarith
  have hne : s ^ 2 - ω ^ 2 ≠ 0 := by
    have : s ^ 2 - ω ^ 2 = (s - ω) * (s - -ω) := by ring
    rw [this]; exact mul_ne_zero hp hm
  constructor
  · rw [laplace_add_smul (1/2) (1/2) i1 i2, e1, e2]
    field_simp
    ring
  · rw [laplace_add_smul (1/2) (-(1/2)) i1 i2, e1, e2]
    field_simp
    ring

/-- **DE-164.** Lebl Table 6.1, p. 295: `L{sinh ωt}(s) = ω/(s² - ω²)` for `s > |ω|`. -/
@[kb "lebldiffyqs2026" "Table 6.1, p. 295"]
theorem laplace_sinh (ω : ℝ) {s : ℝ} (hs : |ω| < s) :
    laplace (fun t => Real.sinh (ω * t)) s = ω / (s ^ 2 - ω ^ 2) := by
  rw [← (lu_laplace_sinh_cosh ω hs).2]
  congr 1; ext t
  rw [Real.sinh_eq, neg_mul_eq_neg_mul]; ring

/-- **DE-164.** Lebl Table 6.1, p. 295: `L{cosh ωt}(s) = s/(s² - ω²)` for `s > |ω|`. -/
@[kb "lebldiffyqs2026" "Table 6.1, p. 295"]
theorem laplace_cosh (ω : ℝ) {s : ℝ} (hs : |ω| < s) :
    laplace (fun t => Real.cosh (ω * t)) s = s / (s ^ 2 - ω ^ 2) := by
  rw [← (lu_laplace_sinh_cosh ω hs).1]
  congr 1; ext t
  rw [Real.cosh_eq, neg_mul_eq_neg_mul]; ring

/-! ### The pulse quotient (DE-183) -/

/-- **DE-183.** Lebl §6.4.1, p. 313: for fixed `s > 0`, `(1 - e^{-bs})/(bs) → 1` as `b → 0⁺` (the pulse of
width `b` and height `1/b` has transform tending to `1`). -/
@[kb "lebldiffyqs2026" "Unit impulse (Dirac delta), p. 313"]
theorem tendsto_pulse_quotient {s : ℝ} (hs : 0 < s) :
    Tendsto (fun b : ℝ => (1 - Real.exp (-(b * s))) / (b * s)) (𝓝[>] 0) (𝓝 1) := by
  have hd : HasDerivAt (fun u : ℝ => Real.exp (-u)) (-1) 0 := by
    have := (hasDerivAt_id (0:ℝ)).neg.exp
    refine this.congr_deriv ?_
    simp
  have hsl := hasDerivAt_iff_tendsto_slope.1 hd
  have hmap : Tendsto (fun b : ℝ => b * s) (𝓝[>] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun b : ℝ => b * s) (𝓝 0) (𝓝 (0 * s)) :=
        (continuous_id.mul continuous_const).tendsto 0
      rw [zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with b hb
      exact mul_ne_zero (ne_of_gt hb) hs.ne'
  have := (hsl.comp hmap).neg
  rw [neg_neg] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with b hb
  simp only [Function.comp, slope_def_field, Real.exp_zero, neg_zero, sub_zero]
  rw [← neg_div, neg_sub]

end UndergradKB.DifferentialEquations
