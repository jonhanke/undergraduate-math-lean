import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Integral.Prod
import UndergradKB.DifferentialEquations.Laplace
import UndergradKB.Common.Attr

/-! # Convolution algebra, the Dirac delta and applications (Lebl, *Notes on Diffy Qs*, Chapter 6)

* DE-179: algebraic properties of the convolution `conv0` (distributivity, constants, associativity).
* DE-184 / DE-185: the Dirac delta as Mathlib's `Measure.dirac`; sifting, `δ * f = f`, the pulse limit,
  the transform `∫ e^{-st} dδ_a = e^{-as}` and the remark on `(s+1)/s`.
* DE-170: partial fractions for distinct real linear factors (Lagrange interpolation) and the inverse transform.
* DE-187: the point-load beam (Green's function), DE-189: the transport equation with a step,
  DE-188 (partial): transforming `y_t` and `y_x` in a PDE. -/

open Real Set Filter Topology MeasureTheory

namespace UndergradKB.DifferentialEquations

/-! ### DE-179: properties of convolution -/

/-- **DE-179 (distributivity).** Lebl §6.3, p. 309: `f * (g + h) = f * g + f * h` at `t`, when the two
integrands are interval integrable on `[0,t]`. -/
@[kb "lebldiffyqs2026" "Properties of convolution, p. 309"]
theorem conv0_add_right {f g h : ℝ → ℝ} {t : ℝ}
    (hg : IntervalIntegrable (fun τ => f τ * g (t - τ)) volume 0 t)
    (hh : IntervalIntegrable (fun τ => f τ * h (t - τ)) volume 0 t) :
    conv0 f (fun x => g x + h x) t = conv0 f g t + conv0 f h t := by
  unfold conv0
  rw [← intervalIntegral.integral_add hg hh]
  congr 1; ext τ; ring

/-- **DE-179 (distributivity, left).** Lebl §6.3, p. 309: `(f + g) * h = f * h + g * h` at `t`. -/
@[kb "lebldiffyqs2026" "Properties of convolution, p. 309"]
theorem conv0_add_left {f g h : ℝ → ℝ} {t : ℝ}
    (hf : IntervalIntegrable (fun τ => f τ * h (t - τ)) volume 0 t)
    (hg : IntervalIntegrable (fun τ => g τ * h (t - τ)) volume 0 t) :
    conv0 (fun x => f x + g x) h t = conv0 f h t + conv0 g h t := by
  unfold conv0
  rw [← intervalIntegral.integral_add hf hg]
  congr 1; ext τ; ring

/-- **DE-179 (constants).** Lebl §6.3, p. 309: `(c f) * g = c (f * g)`. -/
@[kb "lebldiffyqs2026" "Properties of convolution, p. 309"]
theorem conv0_const_mul_left (c : ℝ) (f g : ℝ → ℝ) (t : ℝ) :
    conv0 (fun x => c * f x) g t = c * conv0 f g t := by
  unfold conv0
  rw [← intervalIntegral.integral_const_mul]
  congr 1; ext τ; ring

/-- **DE-179 (constants, right).** Lebl §6.3, p. 309: `f * (c g) = c (f * g)`. -/
@[kb "lebldiffyqs2026" "Properties of convolution, p. 309"]
theorem conv0_const_mul_right (c : ℝ) (f g : ℝ → ℝ) (t : ℝ) :
    conv0 f (fun x => c * g x) t = c * conv0 f g t := by
  unfold conv0
  rw [← intervalIntegral.integral_const_mul]
  congr 1; ext τ; ring

/-- Swapping the order of integration over the triangle `0 ≤ u ≤ τ ≤ t` for a continuous integrand. -/
lemma triangle_swap {Φ : ℝ → ℝ → ℝ} (hΦ : Continuous (Function.uncurry Φ)) {t : ℝ} (ht : 0 ≤ t) :
    ∫ τ in (0:ℝ)..t, ∫ u in (0:ℝ)..τ, Φ u τ = ∫ u in (0:ℝ)..t, ∫ τ in u..t, Φ u τ := by
  set S : Set (ℝ × ℝ) := {p | p.1 ≤ p.2} with hS
  set G : ℝ → ℝ → ℝ := fun u τ => S.indicator (Function.uncurry Φ) (u, τ) with hG
  have hS' : MeasurableSet S := measurableSet_le measurable_fst measurable_snd
  have hint : Integrable (Function.uncurry G)
      ((volume.restrict (Ioc 0 t)).prod (volume.restrict (Ioc 0 t))) := by
    have h1 : IntegrableOn (Function.uncurry Φ) (Icc 0 t ×ˢ Icc 0 t) :=
      hΦ.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    have h2 : IntegrableOn (Function.uncurry Φ) (Ioc 0 t ×ˢ Ioc 0 t) :=
      h1.mono_set (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at h2
    exact h2.indicator hS'
  have swap := integral_integral_swap hint
  have lhs : ∫ τ in (0:ℝ)..t, ∫ u in (0:ℝ)..τ, Φ u τ =
      ∫ τ in Ioc 0 t, ∫ u in Ioc 0 t, G u τ := by
    rw [intervalIntegral.integral_of_le ht]
    refine setIntegral_congr_fun measurableSet_Ioc (fun τ hτ => ?_)
    have e : (fun u => G u τ) = Set.indicator (Iic τ) (fun u => Φ u τ) := by
      ext u
      by_cases h : u ≤ τ <;> simp [hG, hS, h, Set.indicator, Function.uncurry]
    simp only [e]
    rw [setIntegral_indicator measurableSet_Iic, intervalIntegral.integral_of_le hτ.1.le]
    congr 2
    ext u
    simp only [mem_Ioc, mem_inter_iff, mem_Iic]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by linarith [hτ.2]⟩, h2⟩
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
  have rhs : ∫ u in (0:ℝ)..t, ∫ τ in u..t, Φ u τ =
      ∫ u in Ioc 0 t, ∫ τ in Ioc 0 t, G u τ := by
    rw [intervalIntegral.integral_of_le ht]
    refine setIntegral_congr_fun measurableSet_Ioc (fun u hu => ?_)
    have e : (fun τ => G u τ) = Set.indicator (Ici u) (fun τ => Φ u τ) := by
      ext τ
      by_cases h : u ≤ τ <;> simp [hG, hS, h, Set.indicator, Function.uncurry]
    simp only [e]
    rw [setIntegral_indicator measurableSet_Ici, intervalIntegral.integral_of_le (hu.2),
      ← integral_Icc_eq_integral_Ioc]
    congr 2
    ext τ
    simp only [mem_Icc, mem_inter_iff, mem_Ioc, mem_Ici]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith [hu.1], h2⟩, h1⟩
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
  rw [lhs, rhs]
  exact swap.symm

/-- **DE-179 (associativity).** Lebl §6.3, p. 309: `(f * g) * h = f * (g * h)` for continuous `f, g, h`,
at every `t ≥ 0` (Fubini on the triangle `0 ≤ u ≤ τ ≤ t`). -/
@[kb "lebldiffyqs2026" "Properties of convolution, p. 309"]
theorem conv0_assoc {f g h : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    {t : ℝ} (ht : 0 ≤ t) :
    conv0 (conv0 f g) h t = conv0 f (conv0 g h) t := by
  have e1 : conv0 (conv0 f g) h t =
      ∫ τ in (0:ℝ)..t, ∫ u in (0:ℝ)..τ, f u * g (τ - u) * h (t - τ) := by
    unfold conv0
    congr 1; ext τ
    rw [← intervalIntegral.integral_mul_const]
  have key : ∀ u : ℝ, (∫ w in (0:ℝ)..(t - u), g w * h (t - u - w)) =
      ∫ τ in u..t, g (τ - u) * h (t - τ) := by
    intro u
    have := intervalIntegral.integral_comp_sub_right (a := u) (b := t)
      (fun w => g w * h (t - u - w)) u
    simp only [sub_self] at this
    rw [← this]
    congr 1; ext τ
    rw [show t - u - (τ - u) = t - τ by ring]
  have e2 : conv0 f (conv0 g h) t =
      ∫ u in (0:ℝ)..t, ∫ τ in u..t, f u * g (τ - u) * h (t - τ) := by
    unfold conv0
    congr 1; ext u
    rw [key u, ← intervalIntegral.integral_const_mul]
    congr 1; ext τ; ring
  rw [e1, e2]
  have hΦ : Continuous (Function.uncurry fun u τ : ℝ => f u * g (τ - u) * h (t - τ)) := by
    show Continuous (fun p : ℝ × ℝ => f p.1 * g (p.2 - p.1) * h (t - p.2))
    fun_prop
  exact triangle_swap hΦ ht

/-! ### DE-184: the Dirac delta -/

/-- **DE-184 (sifting).** Lebl §6.4.2, p. 314: the Dirac delta `δ_a` is Mathlib's `Measure.dirac a`, and
`∫ f dδ_a = f(a)` (for every function on `ℝ`, since points are measurable). -/
@[kb "lebldiffyqs2026" "The delta function, p. 314"]
theorem dirac_sifting (f : ℝ → ℝ) (a : ℝ) : ∫ x, f x ∂(Measure.dirac a) = f a :=
  integral_dirac f a

/-- **DE-184 (`δ * f = f`).** Lebl §6.4.2, p. 314: `∫ f(t - τ) dδ_0(τ) = f(t)`. -/
@[kb "lebldiffyqs2026" "The delta function, p. 314"]
theorem dirac_conv_self (f : ℝ → ℝ) (t : ℝ) : ∫ τ, f (t - τ) ∂(Measure.dirac (0:ℝ)) = f t := by
  rw [integral_dirac]; simp

/-- **DE-184 (shifted delta).** Convolving with `δ_a` translates: `∫ f(t - τ) dδ_a(τ) = f(t - a)`. -/
@[kb "lebldiffyqs2026" "The delta function, p. 314"]
theorem dirac_conv_shift (f : ℝ → ℝ) (a t : ℝ) : ∫ τ, f (t - τ) ∂(Measure.dirac a) = f (t - a) :=
  integral_dirac (fun τ => f (t - τ)) a

/-- **DE-184 (pulse limit).** Lebl §6.4.2, p. 314: if `f` is continuous, the averages over the unit-mass pulses
`(1/ε) 1_{[a,a+ε]}` converge to `f(a)`: `(1/ε) ∫_a^{a+ε} f → f(a)` as `ε → 0+`. (The book asks continuity
on an interval around `a`; we assume `f` continuous on `ℝ`.) -/
@[kb "lebldiffyqs2026" "The delta function, p. 314"]
theorem tendsto_pulse_average {f : ℝ → ℝ} (hf : Continuous f) (a : ℝ) :
    Tendsto (fun ε : ℝ => ε⁻¹ * ∫ x in a..(a + ε), f x) (𝓝[>] 0) (𝓝 (f a)) := by
  have h1 : HasDerivAt (fun x => ∫ u in a..x, f u) (f a) (a + 0) := by
    rw [add_zero]; exact (hf.integral_hasStrictDerivAt a a).hasDerivAt
  have h2 := HasDerivAt.comp_const_add a 0 h1
  have h3 := hasDerivAt_iff_tendsto_slope_zero.1 h2
  refine (h3.mono_left (nhdsWithin_mono _ (fun x hx => ne_of_gt hx))).congr (fun ε => ?_)
  simp

/-! ### DE-185: the transform of the delta -/

/-- **DE-185.** Lebl §6.4.2, p. 315: `L{δ(t - a)}(s) = ∫ e^{-st} dδ_a(t) = e^{-as}` (any real `a`,
in particular `a ≥ 0`). -/
@[kb "lebldiffyqs2026" "Laplace transform of delta, p. 315"]
theorem laplace_dirac (a s : ℝ) :
    ∫ t, Real.exp (-(s * t)) ∂(Measure.dirac a) = Real.exp (-(a * s)) := by
  rw [integral_dirac]; congr 2; ring

/-- **DE-185 (Remark 6.4.1 / Example 6.4.1).** Lebl p. 315: the measure `δ_0 + 1·dt` on `[0,∞)`
(the generalized function `δ + 1`) has Laplace transform `1 + 1/s = (s+1)/s` for `s > 0`. -/
@[kb "lebldiffyqs2026" "Remark 6.4.1, p. 315"]
theorem laplace_dirac_add_one {s : ℝ} (hs : 0 < s) :
    ∫ t, Real.exp (-(s * t)) ∂(Measure.dirac (0:ℝ) + volume.restrict (Ioi (0:ℝ))) = (s + 1) / s := by
  have h1 : Integrable (fun t : ℝ => Real.exp (-(s * t))) (Measure.dirac (0:ℝ)) :=
    integrable_dirac enorm_lt_top
  have h2 : Integrable (fun t : ℝ => Real.exp (-(s * t))) (volume.restrict (Ioi (0:ℝ))) := by
    have h2' : IntegrableOn (fun t : ℝ => Real.exp (-(s * t))) (Ioi 0) := by
      simpa [neg_mul] using integrableOn_exp_mul_Ioi (a := -s) (by linarith) 0
    exact h2'
  rw [integral_add_measure h1 h2, integral_dirac]
  have h3 := laplace_one hs
  unfold laplace at h3
  simp only [mul_one] at h3
  rw [h3]
  simp
  field_simp

/-! ### DE-170: partial fractions and their inverse transform -/

/-- **DE-170 (partial fractions, distinct real linear factors).** Lebl §6.1, p. 297: for a finite set `s` of
distinct real numbers `r` and a polynomial `p` with `deg p < |s|`, away from the roots,
`p(x) / ∏_{r∈s}(x - r) = ∑_{r∈s} (p(r) / ∏_{r'≠r}(r - r')) · 1/(x - r)`. (Lagrange interpolation.) -/
@[kb "lebldiffyqs2026" "Partial fractions, p. 297"]
theorem partial_fractions_distinct (s : Finset ℝ) (p : Polynomial ℝ) (hp : p.degree < s.card)
    {x : ℝ} (hx : ∀ i ∈ s, x ≠ i) :
    p.eval x / ∏ i ∈ s, (x - i) =
      ∑ i ∈ s, p.eval i / (∏ j ∈ s.erase i, (i - j)) * (1 / (x - i)) := by
  have hinj : Set.InjOn (id : ℝ → ℝ) s := Set.injOn_id _
  have hp' := Lagrange.eq_interpolate_of_eval_eq (v := id) (r := fun i => p.eval i) hinj hp
    (fun i _ => rfl)
  have h2 := Lagrange.eval_interpolate_not_at_node (s := s) (v := id) (fun i => p.eval i)
    (x := x) hx
  rw [← hp', Lagrange.eval_nodal] at h2
  have hn : ∏ i ∈ s, (x - i) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i hi => sub_ne_zero.2 (hx i hi)
  rw [div_eq_iff hn, h2, mul_comm]
  congr 1
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Lagrange.nodalWeight, Finset.prod_inv_distrib]
  simp only [id]
  ring

private lemma integrableOn_exp_term (c i x : ℝ) (h : i < x) :
    IntegrableOn (fun t => Real.exp (-(x * t)) * (c * Real.exp (i * t))) (Ioi 0) := by
  refine laplace_integrableOn (f := fun t => c * Real.exp (i * t)) (M := |c|) (c := i) ?_ ?_ h
  · exact (by fun_prop : Continuous fun t : ℝ => c * Real.exp (i * t)).continuousOn
  · intro t _
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]

/-- **DE-170 (inverse transform).** Lebl Example 6.1.6, p. 297: for distinct reals `s` and `deg p < |s|`,
the function `∑_{r∈s} c_r e^{rt}` with `c_r = p(r)/∏_{r'≠r}(r-r')` has Laplace transform
`p(x)/∏(x - r)` for every `x` larger than all of the roots. -/
@[kb "lebldiffyqs2026" "Partial fractions, p. 297"]
theorem laplace_partial_fractions (s : Finset ℝ) (p : Polynomial ℝ) (hp : p.degree < s.card)
    {x : ℝ} (hx : ∀ i ∈ s, i < x) :
    laplace (fun t => ∑ i ∈ s, p.eval i / (∏ j ∈ s.erase i, (i - j)) * Real.exp (i * t)) x =
      p.eval x / ∏ i ∈ s, (x - i) := by
  rw [partial_fractions_distinct s p hp (fun i hi => (hx i hi).ne')]
  unfold laplace
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i hi => integrableOn_exp_term _ i x (hx i hi))]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have := laplace_exp (hx i hi)
  unfold laplace at this
  rw [← this, ← integral_const_mul]
  congr 1; ext t; ring

/-! ### DE-187: a point load on a simply supported beam -/

/-- A cubic `c x³ + A x`. -/
def beamCubic (c A x : ℝ) : ℝ := c * x ^ 3 + A * x

/-- Left cubic coefficient `k(L-a)/(6L)`. -/
noncomputable def beamPL (k L a : ℝ) : ℝ := k * (L - a) / (6 * L)
/-- Left linear coefficient. -/
noncomputable def beamAL (k L a : ℝ) : ℝ := -(k * (L - a) * (L ^ 2 - (L - a) ^ 2)) / (6 * L)
/-- Right cubic coefficient `k a/(6L)` (in the variable `L - x`). -/
noncomputable def beamPR (k L a : ℝ) : ℝ := k * a / (6 * L)
/-- Right linear coefficient. -/
noncomputable def beamAR (k L a : ℝ) : ℝ := -(k * a * (L ^ 2 - a ^ 2)) / (6 * L)

/-- The deflection (Green's function) of a simply supported beam of length `L` under a point load at `a`,
`k = F/(EI)`: a cubic `p x³ + A x` on `x ≤ a` and the mirrored cubic in `L - x` on `x > a`. -/
noncomputable def beamDefl (k L a : ℝ) (x : ℝ) : ℝ :=
  if x ≤ a then beamCubic (beamPL k L a) (beamAL k L a) x
  else beamCubic (beamPR k L a) (beamAR k L a) (L - x)

/-- First derivative of `beamDefl`. -/
noncomputable def beamSlope (k L a : ℝ) (x : ℝ) : ℝ :=
  if x ≤ a then 3 * beamPL k L a * x ^ 2 + beamAL k L a
  else -(3 * beamPR k L a * (L - x) ^ 2 + beamAR k L a)

/-- Second derivative of `beamDefl` (the bending moment divided by `EI`, up to sign). -/
noncomputable def beamMoment (k L a : ℝ) (x : ℝ) : ℝ :=
  if x ≤ a then 6 * beamPL k L a * x else 6 * beamPR k L a * (L - x)

/-- Gluing two everywhere differentiable pieces that agree to first order at `a`. -/
lemma hasDerivAt_glue {f₁ f₂ f₁' f₂' : ℝ → ℝ} {a : ℝ} (h1 : ∀ x, HasDerivAt f₁ (f₁' x) x)
    (h2 : ∀ x, HasDerivAt f₂ (f₂' x) x) (hv : f₁ a = f₂ a) (hd : f₁' a = f₂' a) (x : ℝ) :
    HasDerivAt (fun x => if x ≤ a then f₁ x else f₂ x) (if x ≤ a then f₁' x else f₂' x) x := by
  rcases lt_trichotomy x a with hx | hx | hx
  · simp only [hx.le, ↓reduceIte]
    refine (h1 x).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hx] with y hy
    simp [le_of_lt (show y < a from hy)]
  · rw [hx]
    simp only [le_refl, ↓reduceIte]
    have hL : HasDerivWithinAt (fun x => if x ≤ a then f₁ x else f₂ x) (f₁' a) (Iic a) a := by
      refine (h1 a).hasDerivWithinAt.congr (fun y hy => ?_) (by simp)
      simp [mem_Iic.1 hy]
    have hR : HasDerivWithinAt (fun x => if x ≤ a then f₁ x else f₂ x) (f₁' a) (Ici a) a := by
      rw [hd]
      refine (h2 a).hasDerivWithinAt.congr (fun y hy => ?_) (by simp [hv])
      by_cases h : y ≤ a
      · have : y = a := le_antisymm h (mem_Ici.1 hy)
        rw [this]; simp [hv]
      · simp [h]
    have := hL.union hR
    rw [Iic_union_Ici, hasDerivWithinAt_univ] at this
    exact this
  · simp only [not_le.2 hx, ↓reduceIte]
    refine (h2 x).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hx] with y hy
    simp [not_le.2 (show a < y from hy)]

lemma hasDerivAt_beamCubic (c A x : ℝ) :
    HasDerivAt (fun x => beamCubic c A x) (3 * c * x ^ 2 + A) x := by
  have := ((hasDerivAt_pow 3 x).const_mul c).add ((hasDerivAt_id' x).const_mul A)
  exact this.congr_deriv (by norm_num; ring)

lemma hasDerivAt_beamCubic_refl (c A L x : ℝ) :
    HasDerivAt (fun x => beamCubic c A (L - x)) (-(3 * c * (L - x) ^ 2 + A)) x := by
  have := (hasDerivAt_beamCubic c A (L - x)).comp x ((hasDerivAt_id' x).const_sub L)
  exact this.congr_deriv (by ring)

/-- **DE-187.** Lebl Example 6.4.3, p. 317 (simply supported beam with a point load `F` at `a`, so
`E I y'''' = -F δ(x - a)` on `[0,L]`, `y(0) = y''(0) = y(L) = y''(L) = 0`). With `k = F/(EI)`, `0 ≤ a ≤ L`, `L > 0`,
the explicit solution `beamDefl` is `C²` on `ℝ` (here `y' = beamSlope`, `y'' = beamMoment`), is a cubic on `[0,a]`
and on `(a,L]`, satisfies the four end conditions, `y''' = k(L-a)/L` to the left of `a` and `-ka/L` to the right
(so `y'''' = 0` off `a`), and `y'''` jumps by `-F/(EI)` at `a`. -/
@[kb "lebldiffyqs2026" "Example 6.4.3, p. 317"]
theorem beam_point_load (F E I L a : ℝ) (hL : 0 < L) (ha : 0 ≤ a) (haL : a ≤ L) :
    let k := F / (E * I)
    (∀ x, HasDerivAt (beamDefl k L a) (beamSlope k L a x) x) ∧
    (∀ x, HasDerivAt (beamSlope k L a) (beamMoment k L a x) x) ∧
    Continuous (beamMoment k L a) ∧
    (∃ c₃ c₂ c₁ c₀ : ℝ, ∀ x ∈ Icc 0 a, beamDefl k L a x = c₃ * x ^ 3 + c₂ * x ^ 2 + c₁ * x + c₀) ∧
    (∃ c₃ c₂ c₁ c₀ : ℝ, ∀ x ∈ Ioc a L, beamDefl k L a x = c₃ * x ^ 3 + c₂ * x ^ 2 + c₁ * x + c₀) ∧
    beamDefl k L a 0 = 0 ∧ beamMoment k L a 0 = 0 ∧ beamDefl k L a L = 0 ∧ beamMoment k L a L = 0 ∧
    (∀ x, x < a → HasDerivAt (beamMoment k L a) (k * (L - a) / L) x) ∧
    (∀ x, a < x → HasDerivAt (beamMoment k L a) (-(k * a / L)) x) ∧
    HasDerivWithinAt (beamMoment k L a) (k * (L - a) / L) (Iic a) a ∧
    HasDerivWithinAt (beamMoment k L a) (-(k * a / L)) (Ici a) a ∧
    (-(k * a / L)) - k * (L - a) / L = -(F / (E * I)) := by
  intro k
  have hL' : L ≠ 0 := hL.ne'
  have hv : beamCubic (beamPL k L a) (beamAL k L a) a =
      beamCubic (beamPR k L a) (beamAR k L a) (L - a) := by
    unfold beamCubic beamPL beamAL beamPR beamAR
    field_simp
    ring
  have hd : 3 * beamPL k L a * a ^ 2 + beamAL k L a =
      -(3 * beamPR k L a * (L - a) ^ 2 + beamAR k L a) := by
    unfold beamPL beamAL beamPR beamAR
    field_simp
    ring
  have hm : 6 * beamPL k L a * a = 6 * beamPR k L a * (L - a) := by
    unfold beamPL beamPR
    field_simp
  have hM1 : ∀ x, HasDerivAt (fun x => 6 * beamPL k L a * x) (6 * beamPL k L a) x := fun x => by
    simpa using (hasDerivAt_id x).const_mul (6 * beamPL k L a)
  have hM2 : ∀ x, HasDerivAt (fun x => 6 * beamPR k L a * (L - x)) (-(6 * beamPR k L a)) x :=
    fun x => by
      simpa using ((hasDerivAt_id x).const_sub L).const_mul (6 * beamPR k L a)
  have hDeriv1 : ∀ x, HasDerivAt (beamDefl k L a) (beamSlope k L a x) x := fun x =>
    hasDerivAt_glue (f₁ := fun x => beamCubic (beamPL k L a) (beamAL k L a) x)
      (f₂ := fun x => beamCubic (beamPR k L a) (beamAR k L a) (L - x))
      (fun x => hasDerivAt_beamCubic _ _ x)
      (fun x => hasDerivAt_beamCubic_refl _ _ L x) hv hd x
  have hDeriv2 : ∀ x, HasDerivAt (beamSlope k L a) (beamMoment k L a x) x := by
    intro x
    have h1 : ∀ x, HasDerivAt (fun x => 3 * beamPL k L a * x ^ 2 + beamAL k L a)
        (6 * beamPL k L a * x) x := fun x => by
      have := ((hasDerivAt_pow 2 x).const_mul (3 * beamPL k L a)).add_const (beamAL k L a)
      exact this.congr_deriv (by norm_num; ring)
    have h2 : ∀ x, HasDerivAt (fun x => -(3 * beamPR k L a * (L - x) ^ 2 + beamAR k L a))
        (6 * beamPR k L a * (L - x)) x := fun x => by
      have := ((((hasDerivAt_id' x).const_sub L).pow 2).const_mul (3 * beamPR k L a)).add_const
        (beamAR k L a) |>.neg
      exact this.congr_deriv (by norm_num; ring)
    exact hasDerivAt_glue h1 h2 hd hm x
  have hcont : Continuous (beamMoment k L a) := by
    unfold beamMoment
    exact Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const
      (fun x hx => by rw [hx]; exact hm)
  have hmL : ∀ x, x < a → HasDerivAt (beamMoment k L a) (k * (L - a) / L) x := by
    intro x hx
    have := (hM1 x).congr_of_eventuallyEq (f₁ := beamMoment k L a) (by
      filter_upwards [Iio_mem_nhds hx] with y hy
      simp [beamMoment, le_of_lt (show y < a from hy)])
    convert this using 1
    unfold beamPL; field_simp
  have hmR : ∀ x, a < x → HasDerivAt (beamMoment k L a) (-(k * a / L)) x := by
    intro x hx
    have := (hM2 x).congr_of_eventuallyEq (f₁ := beamMoment k L a) (by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      simp [beamMoment, not_le.2 (show a < y from hy)])
    convert this using 1
    unfold beamPR; field_simp
  refine ⟨hDeriv1, hDeriv2, hcont, ?_, ?_, ?_, ?_, ?_, ?_, hmL, hmR, ?_, ?_, ?_⟩
  · refine ⟨beamPL k L a, 0, beamAL k L a, 0, fun x hx => ?_⟩
    simp [beamDefl, beamCubic, hx.2]
  · refine ⟨-beamPR k L a, 3 * beamPR k L a * L, -3 * beamPR k L a * L ^ 2 - beamAR k L a,
      beamPR k L a * L ^ 3 + beamAR k L a * L, fun x hx => ?_⟩
    simp only [beamDefl, not_le.2 hx.1, ↓reduceIte, beamCubic]
    ring
  · simp [beamDefl, beamCubic, ha]
  · simp [beamMoment, ha]
  · by_cases h : L ≤ a
    · have : a = L := le_antisymm haL h
      subst this
      simp [beamDefl, beamCubic, beamPL, beamAL]
    · simp [beamDefl, h, beamCubic]
  · by_cases h : L ≤ a
    · have : a = L := le_antisymm haL h
      subst this
      simp [beamMoment, beamPL]
    · simp [beamMoment, h]
  · have := (hM1 a).hasDerivWithinAt (s := Iic a)
    refine (this.congr (fun y hy => ?_) (by simp [beamMoment])) |>.congr_deriv ?_
    · simp [beamMoment, mem_Iic.1 hy]
    · unfold beamPL; field_simp
  · have := (hM2 a).hasDerivWithinAt (s := Ici a)
    refine (this.congr (fun y hy => ?_) (by simp [beamMoment, hm])) |>.congr_deriv ?_
    · by_cases h : y ≤ a
      · have : y = a := le_antisymm h (mem_Ici.1 hy)
        subst this; simp [beamMoment, hm]
      · simp [beamMoment, h]
    · unfold beamPR; field_simp
  · field_simp
    ring

/-! ### DE-189: the transport equation with a step -/

/-- The step solution `y(x,t) = C u(t - x/α)` of the transport equation. -/
noncomputable def transportStep (C α : ℝ) (x t : ℝ) : ℝ := C * heaviside 0 (t - x / α)

private lemma step_local (C : ℝ) {u : ℝ → ℝ} {z : ℝ} (hu : ContinuousAt u z) (hz : u z ≠ 0) :
    HasDerivAt (fun w => C * heaviside 0 (u w)) 0 z := by
  rcases lt_or_gt_of_ne hz with h | h
  · refine (hasDerivAt_const z (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [hu.eventually_lt continuousAt_const h] with w hw
    simp [heaviside, Set.indicator, not_le.2 hw]
  · refine (hasDerivAt_const z C).congr_of_eventuallyEq ?_
    filter_upwards [continuousAt_const.eventually_lt hu h] with w hw
    simp [heaviside, Set.indicator, hw.le]

/-- **DE-189.** Lebl Example 6.5.1, p. 320: for `α > 0`, `y(x,t) = C u(t - x/α)` satisfies `y_t + α y_x = 0` at
every `(x,t)` with `t ≠ x/α` (both partial derivatives exist and are `0` there), `y(0,t) = C` for `t > 0`,
and `y(x,0) = 0` for `x > 0`. -/
@[kb "lebldiffyqs2026" "Example 6.5.1, p. 320"]
theorem transport_step {α : ℝ} (hα : 0 < α) (C : ℝ) :
    (∀ x t : ℝ, t ≠ x / α →
      HasDerivAt (fun s => transportStep C α x s) 0 t ∧
      HasDerivAt (fun z => transportStep C α z t) 0 x ∧
      deriv (fun s => transportStep C α x s) t + α * deriv (fun z => transportStep C α z t) x = 0) ∧
    (∀ t : ℝ, 0 < t → transportStep C α 0 t = C) ∧
    (∀ x : ℝ, 0 < x → transportStep C α x 0 = 0) := by
  refine ⟨fun x t ht => ?_, fun t ht => ?_, fun x hx => ?_⟩
  · have hne : t - x / α ≠ 0 := sub_ne_zero.2 ht
    have h1 : HasDerivAt (fun s => transportStep C α x s) 0 t :=
      step_local C (u := fun s => s - x / α) (by fun_prop) hne
    have h2 : HasDerivAt (fun z => transportStep C α z t) 0 x :=
      step_local C (u := fun z => t - z / α) (by fun_prop) hne
    exact ⟨h1, h2, by rw [h1.deriv, h2.deriv]; ring⟩
  · simp [transportStep, heaviside, ht.le]
  · have h0 : 0 < x / α := div_pos hx hα
    have h : heaviside 0 (0 - x / α) = 0 :=
      Set.indicator_of_notMem (by simp only [mem_Ici, not_le]; linarith) _
    show C * heaviside 0 (0 - x / α) = 0
    rw [h, mul_zero]

/-! ### DE-188 (partial): transforming a PDE in `t` -/

/-- **DE-188 (`y_t`).** Lebl §6.5, p. 320: for each fixed `x`, if `t ↦ y(x,t)` has the stated derivative
`y_t(x,·)` and both have exponential order `c < s`, then `L{y_t(x,·)}(s) = s Y(x,s) - y(x,0)`. -/
@[kb "lebldiffyqs2026" "Laplace transform for PDEs, p. 320"]
theorem laplace_pde_time {y yt : ℝ → ℝ → ℝ} {M M' c s : ℝ} (x : ℝ)
    (hd : ∀ t, 0 ≤ t → HasDerivAt (y x) (yt x t) t) (hc : ContinuousOn (yt x) (Ici 0))
    (hb : ExpOrder (y x) M c) (hb' : ExpOrder (yt x) M' c) (hcs : c < s) :
    laplace (yt x) s = s * laplace (y x) s - y x 0 :=
  laplace_deriv hd hc hb hb' hcs

/-- **DE-188 (`y_x`, under domination).** Lebl §6.5, p. 320: `d/dx Y(x,s) = L{y_x(x,·)}(s)` at `x₀`, provided
the integrands are measurable, `e^{-st} y(x₀,t)` is integrable, `y(·,t)` has derivative `y_x` near `x₀`, and
`|e^{-st} y_x(x,t)| ≤ bound(t)` for `x` within `r` of `x₀`, `t > 0`, with `bound` integrable on `(0,∞)`. -/
@[kb "lebldiffyqs2026" "Laplace transform for PDEs, p. 320"]
theorem laplace_pde_space {y yx : ℝ → ℝ → ℝ} {s x₀ r : ℝ} {bound : ℝ → ℝ} (hr : 0 < r)
    (hmeas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (fun t => Real.exp (-(s * t)) * y x t)
      (volume.restrict (Ioi 0)))
    (hint : IntegrableOn (fun t => Real.exp (-(s * t)) * y x₀ t) (Ioi 0))
    (hmeas' : AEStronglyMeasurable (fun t => Real.exp (-(s * t)) * yx x₀ t) (volume.restrict (Ioi 0)))
    (hbound : ∀ t, 0 < t → ∀ x ∈ Metric.ball x₀ r, |Real.exp (-(s * t)) * yx x t| ≤ bound t)
    (hbint : IntegrableOn bound (Ioi 0))
    (hdiff : ∀ t, 0 < t → ∀ x ∈ Metric.ball x₀ r, HasDerivAt (fun x => y x t) (yx x t) x) :
    HasDerivAt (fun x => laplace (y x) s) (laplace (yx x₀) s) x₀ := by
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun x t => Real.exp (-(s * t)) * y x t) (F' := fun x t => Real.exp (-(s * t)) * yx x t)
    (bound := bound) (Metric.ball_mem_nhds x₀ hr) hmeas hint hmeas'
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht x hx
      rw [Real.norm_eq_abs]; exact hbound t ht x hx)
    hbint
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht x hx
      exact (hdiff t ht x hx).const_mul _)
  exact this.2

end UndergradKB.DifferentialEquations
