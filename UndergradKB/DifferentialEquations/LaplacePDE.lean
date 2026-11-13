import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import UndergradKB.DifferentialEquations.LaplaceDelta
import UndergradKB.DifferentialEquations.LaplaceUniqueness
import UndergradKB.Common.Attr

/-! # Solving a PDE with the Laplace transform (Lebl, *Notes on Diffy Qs*, §6.5, DE-188)

Example 6.5.2: `y_t + y_x + y = 0` on `x, t > 0`, `y(0,t) = sin t`, `y(x,0) = 0`, with the book's answer
`y(x,t) = e^{-x} sin(t-x) u(t-x)` (`yEx`).

* verification: `yEx` is continuous, satisfies both side conditions and the PDE off the characteristic `t = x`
  (where the book's solution has a corner; `example_652_solves`);
* transformed problem: for a classical solution (no corner) `Y(x) = L{y(x,·)}(s)` solves `Y' = -(s+1) Y`
  (`example_652_transformed`);
* solving the ODE: continuity at `x = 0` forces `Y(x) = Y(0) e^{ax}` (`ode_exp_of_cont`);
* inversion: Laplace uniqueness gives `y = yEx` (`example_652_unique`);
* the ill-posed variant `-y_t + y_x = 0` has no bounded-order solution (`example_652_illposed`). -/

open Real Set Filter Topology MeasureTheory

namespace UndergradKB.DifferentialEquations

/-- The book's solution of Example 6.5.2: `y(x,t) = e^{-x} sin(t-x) u(t-x)`. -/
noncomputable def yEx (x t : ℝ) : ℝ := Real.exp (-x) * (Real.sin (t - x) * heaviside x t)

/-- `y_t` of `yEx` away from the characteristic `t = x`. -/
noncomputable def yExT (x t : ℝ) : ℝ := if x < t then Real.exp (-x) * Real.cos (t - x) else 0

/-- `y_x` of `yEx` away from the characteristic `t = x`. -/
noncomputable def yExX (x t : ℝ) : ℝ :=
  if x < t then -(Real.exp (-x) * Real.sin (t - x)) - Real.exp (-x) * Real.cos (t - x) else 0

lemma heaviside_eq (a t : ℝ) : heaviside a t = if a ≤ t then 1 else 0 := by
  by_cases h : a ≤ t <;> simp [heaviside, h]

lemma yEx_eq_max (x t : ℝ) : yEx x t = Real.exp (-x) * Real.sin (max (t - x) 0) := by
  unfold yEx
  rw [heaviside_eq]
  by_cases h : x ≤ t
  · rw [max_eq_left (by linarith)]; simp [h]
  · rw [max_eq_right (by linarith)]; simp [h]

lemma continuous_yEx (x : ℝ) : Continuous (yEx x) := by
  have : yEx x = fun t => Real.exp (-x) * Real.sin (max (t - x) 0) := funext (yEx_eq_max x)
  rw [this]; fun_prop

lemma continuous_yEx_uncurry : Continuous (fun p : ℝ × ℝ => yEx p.1 p.2) := by
  have : (fun p : ℝ × ℝ => yEx p.1 p.2) =
      fun p => Real.exp (-p.1) * Real.sin (max (p.2 - p.1) 0) := funext fun p => yEx_eq_max p.1 p.2
  rw [this]; fun_prop

lemma yEx_of_lt {x t : ℝ} (h : x ≤ t) : yEx x t = Real.exp (-x) * Real.sin (t - x) := by
  unfold yEx; rw [heaviside_eq]; simp [h]

lemma yEx_of_gt {x t : ℝ} (h : t < x) : yEx x t = 0 := by
  unfold yEx; rw [heaviside_eq]; simp [not_le.2 h]

/-- **DE-188 (Example 6.5.2, verification).** Lebl Example 6.5.2, p. 322: the book's function
`y(x,t) = e^{-x} sin(t-x) u(t-x)` is continuous, has `y(0,t) = sin t` and `y(x,0) = 0`, and satisfies
`y_t + y_x + y = 0` at every point `x, t > 0` off the characteristic line `t = x` (where it has a corner,
so that the equation holds in the sense of distributions only). -/
@[kb "lebldiffyqs2026" "Example 6.5.2, p. 322"]
theorem example_652_solves :
    Continuous (fun p : ℝ × ℝ => yEx p.1 p.2) ∧ (∀ t, 0 ≤ t → yEx 0 t = Real.sin t) ∧
    (∀ x, 0 ≤ x → yEx x 0 = 0) ∧
    ∀ x, 0 < x → ∀ t, 0 < t → t ≠ x →
      HasDerivAt (yEx x) (yExT x t) t ∧ HasDerivAt (fun x => yEx x t) (yExX x t) x ∧
      yExT x t + yExX x t + yEx x t = 0 := by
  refine ⟨continuous_yEx_uncurry, ?_, ?_, ?_⟩
  · intro t ht
    rw [yEx_of_lt ht]; simp
  · intro x hx
    rw [yEx_eq_max, max_eq_right (by linarith)]; simp
  · intro x hx t ht hne
    rcases lt_or_gt_of_ne hne with h | h
    · -- t < x
      have e1 : yEx x =ᶠ[𝓝 t] fun _ => (0:ℝ) :=
        (eventually_lt_nhds h).mono fun u hu => yEx_of_gt hu
      have e2 : (fun x' => yEx x' t) =ᶠ[𝓝 x] fun _ => (0:ℝ) :=
        (eventually_gt_nhds h).mono fun u hu => yEx_of_gt hu
      have hT : yExT x t = 0 := by simp [yExT, not_lt.2 h.le]
      have hX : yExX x t = 0 := by simp [yExX, not_lt.2 h.le]
      refine ⟨?_, ?_, ?_⟩
      · rw [hT]; exact (hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq e1
      · rw [hX]; exact (hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq e2
      · rw [hT, hX, yEx_of_gt h]; ring
    · -- x < t
      have e1 : yEx x =ᶠ[𝓝 t] fun u => Real.exp (-x) * Real.sin (u - x) :=
        (eventually_gt_nhds h).mono fun u hu => yEx_of_lt hu.le
      have e2 : (fun x' => yEx x' t) =ᶠ[𝓝 x] fun x' => Real.exp (-x') * Real.sin (t - x') :=
        (eventually_lt_nhds h).mono fun u hu => yEx_of_lt hu.le
      have hT : yExT x t = Real.exp (-x) * Real.cos (t - x) := by simp [yExT, h]
      have hX : yExX x t = -(Real.exp (-x) * Real.sin (t - x)) - Real.exp (-x) * Real.cos (t - x) := by
        simp [yExX, h]
      refine ⟨?_, ?_, ?_⟩
      · rw [hT]
        have := (((hasDerivAt_id t).sub_const x).sin.const_mul (Real.exp (-x)))
        simp only [id, mul_one] at this
        exact this.congr_of_eventuallyEq e1
      · rw [hX]
        have h1 : HasDerivAt (fun x' : ℝ => Real.exp (-x')) (-Real.exp (-x)) x := by
          simpa using (hasDerivAt_neg x).exp
        have h2 : HasDerivAt (fun x' : ℝ => Real.sin (t - x')) (Real.cos (t - x) * (-1)) x :=
          ((hasDerivAt_id x).const_sub t).sin
        have := h1.mul h2
        refine (this.congr_of_eventuallyEq e2).congr_deriv ?_
        ring
      · rw [hT, hX, yEx_of_lt h.le]; ring

/-! ### The ODE in `x` -/

/-- Solving `Y' = a Y` on `x > 0` with `Y` continuous at `0` from the right: `Y(x) = Y(0) e^{ax}`.
(The one-sided continuity replaces the book's boundary condition `Y(0) = ...`.) -/
theorem ode_exp_of_cont {Y : ℝ → ℝ} {a : ℝ} (hc : ContinuousWithinAt Y (Ici 0) 0)
    (hd : ∀ x, 0 < x → HasDerivAt Y (a * Y x) x) : ∀ x, 0 ≤ x → Y x = Y 0 * Real.exp (a * x) := by
  set g : ℝ → ℝ := fun x => Y x * Real.exp (-(a * x)) with hg
  have hgd : ∀ x, 0 < x → HasDerivAt g 0 x := by
    intro x hx
    have e : HasDerivAt (fun x : ℝ => Real.exp (-(a * x))) (Real.exp (-(a * x)) * (-a)) x :=
      (((hasDerivAt_id' x).const_mul a).neg.exp).congr_deriv (by simp)
    have := (hd x hx).mul e
    refine this.congr_deriv ?_
    ring
  have hg0 : ContinuousWithinAt g (Ici 0) 0 :=
    hc.mul (by fun_prop : Continuous fun x : ℝ => Real.exp (-(a * x))).continuousWithinAt
  intro x hx
  rcases hx.eq_or_lt with h | h
  · subst h; simp
  have hconst : ∀ ε, 0 < ε → ε ≤ x → g ε = g x := by
    intro ε hε hεx
    have := constant_of_has_deriv_right_zero (f := g) (a := ε) (b := x)
      (fun u hu => (hgd u (by linarith [hu.1])).continuousAt.continuousWithinAt)
      (fun u hu => (hgd u (by linarith [hu.1])).hasDerivWithinAt) x ⟨hεx, le_rfl⟩
    exact this.symm
  have t1 : Tendsto g (𝓝[>] 0) (𝓝 (g 0)) := (hg0.mono Ioi_subset_Ici_self).tendsto
  have t2 : Tendsto g (𝓝[>] 0) (𝓝 (g x)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT h] with ε hε
    exact (hconst ε hε.1 hε.2.le).symm
  have := tendsto_nhds_unique t1 t2
  have hx' : Y x * Real.exp (-(a * x)) = Y 0 := by
    have := this.symm
    simpa [hg] using this
  have : Y x = Y 0 * Real.exp (a * x) := by
    rw [← hx', mul_assoc, ← Real.exp_add]; simp
  exact this

/-! ### Transform bookkeeping -/

lemma laplace_congr {f g : ℝ → ℝ} (s : ℝ) (h : ∀ t, 0 < t → f t = g t) : laplace f s = laplace g s := by
  unfold laplace
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [h t ht]

lemma abs_laplace_le {f : ℝ → ℝ} {M c s : ℝ} (hb : ExpOrder f M c) (hcs : c < s) :
    |laplace f s| ≤ M / (s - c) := by
  have hint : IntegrableOn (fun t : ℝ => M * Real.exp (-(s - c) * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul M
  have h1 := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi 0))
    (f := fun t => Real.exp (-(s * t)) * f t) hint (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 ≤ t := le_of_lt ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc Real.exp (-(s * t)) * |f t| ≤ Real.exp (-(s * t)) * (M * Real.exp (c * t)) :=
            mul_le_mul_of_nonneg_left (hb t ht0) (Real.exp_pos _).le
        _ = M * Real.exp (-(s - c) * t) := by
            rw [mul_left_comm, ← Real.exp_add]; congr 2; ring)
  have h2 : ∫ t in Ioi (0:ℝ), M * Real.exp (-(s - c) * t) = M / (s - c) := by
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith)]
    simp only [mul_zero, Real.exp_zero]
    rw [neg_div_neg_eq]; ring
  rw [h2] at h1
  simpa [laplace] using h1

/-- The transform of the book's solution: `L{y(x,·)}(s) = e^{-x} e^{-xs} / (s²+1)` for `x ≥ 0`, `s > 0`. -/
theorem laplace_yEx {x : ℝ} (hx : 0 ≤ x) {s : ℝ} (hs : 0 < s) :
    laplace (yEx x) s = Real.exp (-x) * (Real.exp (-(x * s)) * (1 / (s ^ 2 + 1))) := by
  have h1 : laplace (yEx x) s = Real.exp (-x) *
      laplace (fun t => (fun u => Real.sin u) (t - x) * heaviside x t) s := by
    rw [← laplace_const_mul]; rfl
  rw [h1, laplace_shift hx]
  have := (laplace_sin_cos 1 hs).1
  simp only [one_mul, one_pow] at this
  rw [this]

lemma expOrder_yEx {x : ℝ} (hx : 0 ≤ x) : ExpOrder (yEx x) 1 0 := by
  intro t _
  rw [yEx_eq_max, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 : Real.exp (-x) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  have h2 := Real.abs_sin_le_one (max (t - x) 0)
  simp only [zero_mul, Real.exp_zero, mul_one]
  calc Real.exp (-x) * |Real.sin (max (t - x) 0)| ≤ 1 * 1 :=
        mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- **DE-188 (Example 6.5.2, transformed problem).** Lebl Example 6.5.2, p. 322: if `y` is a *classical*
solution of `y_t + y_x + y = 0` (`x, t > 0`) with `y(x,0) = 0`, then for `s > c`, `Y(x) = L{y(x,·)}(s)` satisfies
`s Y + Y' + Y = 0`, i.e. `Y' = -(s+1) Y`.  Added hypotheses: for each `x > 0`, `y(x,·)` is differentiable on
`[0,∞)` with continuous derivative `y_t`, and `y`, `y_t` have exponential order `c` (the constants may depend on
`x`); and differentiation under the integral sign in `x` (`hYx`, available from `laplace_pde_space` under
domination). (The actual solution has a corner on `t = x`, so it is not a classical solution; see
`example_652_transform_ode` for the transform of the actual solution.) -/
@[kb "lebldiffyqs2026" "Example 6.5.2, p. 322"]
theorem example_652_transformed {y yt yx : ℝ → ℝ → ℝ} {c s : ℝ} (hcs : c < s)
    (hPDE : ∀ x, 0 < x → ∀ t, 0 < t → yt x t + yx x t + y x t = 0)
    (hdt : ∀ x, 0 < x → ∀ t, 0 ≤ t → HasDerivAt (y x) (yt x t) t)
    (hytc : ∀ x, 0 < x → ContinuousOn (yt x) (Ici 0))
    (hb : ∀ x, 0 < x → ∃ M, ExpOrder (y x) M c) (hb' : ∀ x, 0 < x → ∃ M, ExpOrder (yt x) M c)
    (hy0 : ∀ x, 0 < x → y x 0 = 0)
    (hYx : ∀ x, 0 < x → HasDerivAt (fun x => laplace (y x) s) (laplace (yx x) s) x) :
    ∀ x, 0 < x → HasDerivAt (fun x => laplace (y x) s) (-(s + 1) * laplace (y x) s) x := by
  intro x hx
  obtain ⟨M, hM⟩ := hb x hx
  obtain ⟨M', hM'⟩ := hb' x hx
  have hyc : ContinuousOn (y x) (Ici 0) := fun t ht => (hdt x hx t ht).continuousAt.continuousWithinAt
  have h1 := laplace_pde_time (y := y) (yt := yt) x (hdt x hx) (hytc x hx) hM hM' hcs
  have i1 := laplace_integrableOn (hytc x hx) hM' hcs
  have i2 := laplace_integrableOn hyc hM hcs
  have h2 : laplace (yx x) s = laplace (fun t => (-1) * yt x t + (-1) * y x t) s :=
    laplace_congr s fun t ht => by linarith [hPDE x hx t ht]
  refine (hYx x hx).congr_deriv ?_
  rw [h2, laplace_add_smul (-1) (-1) i1 i2, h1, hy0 x hx]
  ring

/-- **DE-188 (Example 6.5.2, transform of the actual solution).** Lebl Example 6.5.2, p. 322: for `s > 0`,
`Y(x) = L{yEx(x,·)}(s) = e^{-(s+1)x}/(s²+1)` satisfies `Y' = -(s+1) Y` for `x > 0`, `Y(0) = 1/(s²+1)`, and
`Y` is continuous at `0`. -/
@[kb "lebldiffyqs2026" "Example 6.5.2, p. 322"]
theorem example_652_transform_ode {s : ℝ} (hs : 0 < s) :
    (∀ x, 0 < x → HasDerivAt (fun x => laplace (yEx x) s) (-(s + 1) * laplace (yEx x) s) x) ∧
    laplace (yEx 0) s = 1 / (s ^ 2 + 1) ∧
    ContinuousWithinAt (fun x => laplace (yEx x) s) (Ici 0) 0 := by
  have key : ∀ x, 0 ≤ x → laplace (yEx x) s = 1 / (s ^ 2 + 1) * Real.exp (-(s + 1) * x) := by
    intro x hx
    rw [laplace_yEx hx hs]
    have : Real.exp (-(s + 1) * x) = Real.exp (-x) * Real.exp (-(x * s)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]; ring
  have hfun : (fun x => laplace (yEx x) s) =ᶠ[𝓝[Ici 0] 0] fun x => 1 / (s ^ 2 + 1) * Real.exp (-(s + 1) * x) :=
    eventually_nhdsWithin_of_forall fun x hx => key x hx
  have hE : ∀ x : ℝ, HasDerivAt (fun x : ℝ => 1 / (s ^ 2 + 1) * Real.exp (-(s + 1) * x))
      (-(s + 1) * (1 / (s ^ 2 + 1) * Real.exp (-(s + 1) * x))) x := by
    intro x
    have := (((hasDerivAt_id' x).const_mul (-(s + 1))).exp).const_mul (1 / (s ^ 2 + 1))
    refine this.congr_deriv ?_
    simp; ring
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have e : (fun x => laplace (yEx x) s) =ᶠ[𝓝 x] fun x => 1 / (s ^ 2 + 1) * Real.exp (-(s + 1) * x) :=
      (eventually_gt_nhds hx).mono fun u hu => key u hu.le
    rw [key x hx.le]
    exact (hE x).congr_of_eventuallyEq e
  · rw [key 0 le_rfl]; simp
  · have : ContinuousWithinAt (fun x : ℝ => 1 / (s ^ 2 + 1) * Real.exp (-(s + 1) * x)) (Ici 0) 0 :=
      (hE 0).continuousAt.continuousWithinAt
    exact this.congr_of_eventuallyEq hfun (by rw [key 0 le_rfl])

/-- **DE-188 (Example 6.5.2, solving and inverting).** Lebl Example 6.5.2, p. 322: suppose `y(x,·)` is continuous
and of exponential order `c` for each `x ≥ 0`, `y(0,t) = sin t`, and for every `s > max c 0` the transform
`Y(x) = L{y(x,·)}(s)` solves the transformed equation `Y' = -(s+1) Y` on `x > 0` and is continuous at `x = 0`
(the latter two follow from the PDE under `example_652_transformed`'s hypotheses; the initial condition
`y(x,0) = 0` entered through `s Y - y(x,0) = sY`). Then `y(x,t) = e^{-x} sin(t-x) u(t-x)` for all `x, t ≥ 0`. -/
@[kb "lebldiffyqs2026" "Example 6.5.2, p. 322"]
theorem example_652_unique {y : ℝ → ℝ → ℝ} {c : ℝ}
    (hcont : ∀ x, 0 ≤ x → ContinuousOn (y x) (Ici 0)) (hb : ∀ x, 0 ≤ x → ∃ M, ExpOrder (y x) M c)
    (hbc : ∀ t, 0 ≤ t → y 0 t = Real.sin t)
    (hODE : ∀ s, max c 0 < s → ∀ x, 0 < x →
      HasDerivAt (fun x => laplace (y x) s) (-(s + 1) * laplace (y x) s) x)
    (hY0 : ∀ s, max c 0 < s → ContinuousWithinAt (fun x => laplace (y x) s) (Ici 0) 0) :
    ∀ x, 0 ≤ x → ∀ t, 0 ≤ t → y x t = yEx x t := by
  intro x hx t ht
  obtain ⟨M, hM⟩ := hb x hx
  refine laplace_unique_of_gt (hcont x hx) (continuous_yEx x).continuousOn hM (expOrder_yEx hx)
    (s₀ := max c 0) ?_ t ht
  intro s hs
  have hs0 : 0 < s := lt_of_le_of_lt (le_max_right _ _) hs
  have hY0v : laplace (y 0) s = 1 / (s ^ 2 + 1) := by
    have := (laplace_sin_cos 1 hs0).1
    simp only [one_mul, one_pow] at this
    rw [← this]
    exact laplace_congr s fun t ht => by rw [hbc t ht.le]
  have := ode_exp_of_cont (hY0 s hs) (hODE s hs) x hx
  rw [this, hY0v, laplace_yEx hx hs0]
  have e : Real.exp (-(s + 1) * x) = Real.exp (-x) * Real.exp (-(x * s)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e]; ring

/-- **DE-188 (Example 6.5.2, complete).** Lebl Example 6.5.2, p. 322: a classical solution (hypotheses of
`example_652_transformed` for every `s > max c 0`, with continuity of `Y` at `x = 0`, i.e. of `y(x,·)` in the
transform sense as `x → 0+`) with the boundary data `y(0,t) = sin t` equals `e^{-x} sin(t-x) u(t-x)`. -/
@[kb "lebldiffyqs2026" "Example 6.5.2, p. 322"]
theorem example_652 {y yt yx : ℝ → ℝ → ℝ} {c : ℝ}
    (hPDE : ∀ x, 0 < x → ∀ t, 0 < t → yt x t + yx x t + y x t = 0)
    (hdt : ∀ x, 0 < x → ∀ t, 0 ≤ t → HasDerivAt (y x) (yt x t) t)
    (hytc : ∀ x, 0 < x → ContinuousOn (yt x) (Ici 0))
    (hb : ∀ x, 0 ≤ x → ∃ M, ExpOrder (y x) M c) (hb' : ∀ x, 0 < x → ∃ M, ExpOrder (yt x) M c)
    (hy0 : ∀ x, 0 < x → y x 0 = 0) (hbc : ∀ t, 0 ≤ t → y 0 t = Real.sin t)
    (hcont0 : ContinuousOn (y 0) (Ici 0))
    (hYx : ∀ s, max c 0 < s → ∀ x, 0 < x →
      HasDerivAt (fun x => laplace (y x) s) (laplace (yx x) s) x)
    (hY0 : ∀ s, max c 0 < s → ContinuousWithinAt (fun x => laplace (y x) s) (Ici 0) 0) :
    ∀ x, 0 ≤ x → ∀ t, 0 ≤ t → y x t = yEx x t := by
  have hcont : ∀ x, 0 ≤ x → ContinuousOn (y x) (Ici 0) := by
    intro x hx
    rcases hx.eq_or_lt with h | h
    · subst h; exact hcont0
    · exact fun t ht => (hdt x h t ht).continuousAt.continuousWithinAt
  refine example_652_unique hcont hb hbc (fun s hs x hx => ?_) hY0
  exact example_652_transformed (lt_of_le_of_lt (le_max_left _ _) hs) hPDE hdt hytc
    (fun x hx => hb x hx.le) hb' hy0 (hYx s hs) x hx

/-- **DE-188 (Example 6.5.2, the ill-posed variant).** Lebl Example 6.5.2, p. 323: for `-y_t + y_x = 0`,
`y(0,t) = sin t`, `y(x,0) = 0` the transformed problem is `Y' = s Y`, `Y(0) = 1/(s²+1)`, whose solution
`e^{sx}/(s²+1)` is unbounded in `x`. Precisely: there is no `y` with `y(x,·)` continuous and of exponential
order `c` with a constant `M` uniform in `x ≥ 0`, `y(0,t) = sin t`, whose transform satisfies `Y' = sY` for
`x > 0`, continuously at `x = 0`, for all `s > max c 0`. -/
@[kb "lebldiffyqs2026" "Example 6.5.2, p. 323"]
theorem example_652_illposed {y : ℝ → ℝ → ℝ} {M c : ℝ}
    (hb : ∀ x, 0 ≤ x → ExpOrder (y x) M c) (hbc : ∀ t, 0 ≤ t → y 0 t = Real.sin t)
    (hODE : ∀ s, max c 0 < s → ∀ x, 0 < x →
      HasDerivAt (fun x => laplace (y x) s) (s * laplace (y x) s) x)
    (hY0 : ∀ s, max c 0 < s → ContinuousWithinAt (fun x => laplace (y x) s) (Ici 0) 0) : False := by
  set s := max c 0 + 1 with hsdef
  have hs : max c 0 < s := by linarith
  have hs0 : 0 < s := by have := le_max_right c 0; linarith
  have hcs : c < s := by have := le_max_left c 0; linarith
  have hY0v : laplace (y 0) s = 1 / (s ^ 2 + 1) := by
    have := (laplace_sin_cos 1 hs0).1
    simp only [one_mul, one_pow] at this
    rw [← this]
    exact laplace_congr s fun t ht => by rw [hbc t ht.le]
  have hexp := ode_exp_of_cont (hY0 s hs) (hODE s hs)
  set K := M / (s - c) * (s ^ 2 + 1) with hK
  set x := (|K| + 1) / s with hx
  have hxpos : 0 ≤ x := by positivity
  have h1 := hexp x hxpos
  have h2 := abs_laplace_le (hb x hxpos) hcs
  rw [h1, hY0v] at h2
  have hpos : 0 < s ^ 2 + 1 := by positivity
  have h3 : Real.exp (s * x) ≤ K := by
    rw [abs_of_nonneg (by positivity), div_mul_eq_mul_div, one_mul, div_le_iff₀ hpos] at h2
    linarith
  have h4 : s * x + 1 ≤ Real.exp (s * x) := Real.add_one_le_exp _
  have h5 : s * x = |K| + 1 := by rw [hx]; field_simp
  have := le_abs_self K
  linarith

/-- **DE-188 (Example 6.5.3, the ODE step).** Lebl Example 6.5.3, p. 324: the transformed heat problem
`Y'' = s Y` (`s = r²`, `r > 0`) on `x > 0`, with `Y` bounded in `x`, and `Y'(0) = F(s)`, forces
`Y(x) = -(F/r) e^{-rx}`: the growing exponential is excluded by boundedness. Here `Y'` is the (named) derivative
`dY`, and `Y`, `dY` are assumed continuous at `0` from the right with `dY 0 = F`. Only this ODE step is proved;
the transformation of the PDE and the inversion to the convolution integral are not. -/
@[kb "lebldiffyqs2026" "Example 6.5.3, p. 324"]
theorem example_653_ode {Y dY : ℝ → ℝ} {r F B : ℝ} (hr : 0 < r)
    (hY : ∀ x, 0 < x → HasDerivAt Y (dY x) x) (hdY : ∀ x, 0 < x → HasDerivAt dY (r ^ 2 * Y x) x)
    (hc : ContinuousWithinAt Y (Ici 0) 0) (hdc : ContinuousWithinAt dY (Ici 0) 0)
    (hF : dY 0 = F) (hB : ∀ x, 0 ≤ x → |Y x| ≤ B) :
    ∀ x, 0 ≤ x → Y x = -(F / r) * Real.exp (-(r * x)) := by
  have hu := ode_exp_of_cont (Y := fun x => dY x + r * Y x) (a := r) (hdc.add (hc.const_mul r))
    (fun x hx => by
      have := (hdY x hx).add ((hY x hx).const_mul r)
      refine this.congr_deriv ?_
      ring)
  have hv := ode_exp_of_cont (Y := fun x => dY x - r * Y x) (a := -r) (hdc.sub (hc.const_mul r))
    (fun x hx => by
      have := (hdY x hx).sub ((hY x hx).const_mul r)
      refine this.congr_deriv ?_
      ring)
  set u0 := dY 0 + r * Y 0 with hu0
  set v0 := dY 0 - r * Y 0 with hv0
  have hrep : ∀ x, 0 ≤ x → 2 * r * Y x = u0 * Real.exp (r * x) - v0 * Real.exp (-r * x) := by
    intro x hx
    have a1 := hu x hx
    have a2 := hv x hx
    linarith
  have hu0z : u0 = 0 := by
    by_contra hne
    have hpos : 0 < |u0| := abs_pos.2 hne
    set K := 2 * r * B + |v0| with hK
    have hbd : ∀ x, 0 ≤ x → |u0| * Real.exp (r * x) ≤ K := by
      intro x hx
      have h1 := hrep x hx
      have h2 : Real.exp (-r * x) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
      have h3 : |2 * r * Y x| ≤ 2 * r * B := by
        rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * r)]
        exact mul_le_mul_of_nonneg_left (hB x hx) (by positivity)
      have h4 : |v0 * Real.exp (-r * x)| ≤ |v0| := by
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_of_le_one_right (abs_nonneg _) h2
      have h5 : u0 * Real.exp (r * x) = 2 * r * Y x + v0 * Real.exp (-r * x) := by linarith
      have h6 : |u0 * Real.exp (r * x)| ≤ K := by
        rw [h5]; exact (abs_add_le _ _).trans (add_le_add h3 h4)
      rwa [abs_mul, abs_of_pos (Real.exp_pos _)] at h6
    set x := (|K| / |u0| + 1) / r with hx
    have hx0 : 0 ≤ x := by positivity
    have h1 := hbd x hx0
    have h2 : r * x + 1 ≤ Real.exp (r * x) := Real.add_one_le_exp _
    have h3 : r * x = |K| / |u0| + 1 := by rw [hx]; field_simp
    have h4 : |u0| * (r * x + 1) ≤ |u0| * Real.exp (r * x) := mul_le_mul_of_nonneg_left h2 hpos.le
    have h5 : |u0| * (r * x + 1) = |K| + 2 * |u0| := by
      rw [h3]; field_simp; ring
    have := le_abs_self K
    linarith
  intro x hx
  have e0 : dY 0 = -(r * Y 0) := by linarith
  have hY0 : Y 0 = -(F / r) := by
    field_simp
    linarith
  have hrep' := hrep x hx
  rw [hu0z, zero_mul, zero_sub] at hrep'
  have e1 : Real.exp (-r * x) = Real.exp (-(r * x)) := by rw [neg_mul]
  rw [e1] at hrep'
  have hv0' : v0 = -(2 * r * Y 0) := by rw [hv0, e0]; ring
  rw [hv0'] at hrep'
  rw [hY0] at hrep'
  field_simp at hrep' ⊢
  linarith

end UndergradKB.DifferentialEquations
