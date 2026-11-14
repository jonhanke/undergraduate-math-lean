import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import UndergradKB.DifferentialEquations.BesselOscillation
import UndergradKB.Common.Attr

/-! # Every solution of Bessel's equation oscillates and is not periodic (Lebl, §7.3.3)

Closes the generality gap of `bessel_oscillate_not_periodic` (which treats only `J_p`, `p ≥ 0`).

Let `p` be any real number and let `y` solve Bessel's equation `x² y'' + x y' + (x² - p²) y = 0` on `(0, ∞)`,
where `y1`, `y2` are the first and second derivatives of `y` (hypotheses in the style of `sturm_zero`).

* `bessel_solution_infinite_zeros`: `y` has arbitrarily large zeros.  `u = √x y` solves
  `u'' + (1 + (1/4 - p²)/x²) u = 0`, and for `x ≥ 2|p| + 1` the coefficient is `≥ 1/4 = (1/2)²`, so the
  Sturm comparison lemma gives a zero in every interval `[a, a + 2π]`, `a ≥ 2|p| + 1`.  (This holds
  trivially also for `y = 0`, so no nontriviality hypothesis is needed.)
* `bessel_solution_not_periodic`: a nonzero solution is not periodic on `(0, ∞)`.  The wave 4 argument for
  `J_p` uses only the differential equation and periodicity (the ODE at `x, x+T, x+2T` forces
  `y' = 0`, `y'' + y = 0`, `p² y = 0`), and nonvanishing, not any property special to `J_p`; so it applies
  verbatim.

In particular `J_{-p}` (`p ∉ ℤ`) and `Y_n` are covered.
-/

namespace UndergradKB.DifferentialEquations

open Filter Topology Set

/-- Algebraic core: the ODE for `u = √x y` in terms of `s = √x`. -/
lemma sqrt_transform_ode {s y y1 y2 p : ℝ} (hs : s ≠ 0)
    (E : (s ^ 2) ^ 2 * y2 + s ^ 2 * y1 + ((s ^ 2) ^ 2 - p ^ 2) * y = 0) :
    -(1 / (4 * s ^ 3)) * y + (2 * s)⁻¹ * y1 + ((2 * s)⁻¹ * y1 + s * y2) +
      (1 + (1 / 4 - p ^ 2) / (s ^ 2) ^ 2) * (s * y) = 0 := by
  have h : -(1 / (4 * s ^ 3)) * y + (2 * s)⁻¹ * y1 + ((2 * s)⁻¹ * y1 + s * y2) +
      (1 + (1 / 4 - p ^ 2) / (s ^ 2) ^ 2) * (s * y) =
      ((s ^ 2) ^ 2 * y2 + s ^ 2 * y1 + ((s ^ 2) ^ 2 - p ^ 2) * y) / s ^ 3 := by
    field_simp
    ring
  rw [h, E, zero_div]

/-- The first derivative of `√x y(x)`. -/
lemma hasDerivAt_sqrt_mul {y y1 : ℝ → ℝ} {x : ℝ} (hx : 0 < x) (hy : HasDerivAt y (y1 x) x) :
    HasDerivAt (fun t => Real.sqrt t * y t) ((2 * Real.sqrt x)⁻¹ * y x + Real.sqrt x * y1 x) x := by
  have h := (Real.hasDerivAt_sqrt hx.ne').mul hy
  rw [one_div] at h
  exact h

/-- The second derivative of `√x y(x)`. -/
lemma hasDerivAt_sqrt_mul_deriv {y y1 y2 : ℝ → ℝ} {x : ℝ} (hx : 0 < x) (hy : HasDerivAt y (y1 x) x)
    (hy1 : HasDerivAt y1 (y2 x) x) :
    HasDerivAt (fun t => (2 * Real.sqrt t)⁻¹ * y t + Real.sqrt t * y1 t)
      (-(1 / (4 * Real.sqrt x ^ 3)) * y x + (2 * Real.sqrt x)⁻¹ * y1 x +
        ((2 * Real.sqrt x)⁻¹ * y1 x + Real.sqrt x * y2 x)) x := by
  have hs := Real.hasDerivAt_sqrt hx.ne'
  have hsq : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  have hw : HasDerivAt (fun t => (2 * Real.sqrt t)⁻¹) (-(1 / (4 * Real.sqrt x ^ 3))) x := by
    have h := (hs.const_mul 2).inv (by positivity)
    refine h.congr_deriv ?_
    have h2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
    field_simp
    nlinarith [h2]
  have h := (hw.mul hy).add (hs.mul hy1)
  rw [one_div (2 * Real.sqrt x)] at h
  exact h

/-- The ODE for `√x y(x)`. -/
lemma sqrt_mul_ode {y y1 y2 : ℝ → ℝ} {p x : ℝ} (hx : 0 < x)
    (E : x ^ 2 * y2 x + x * y1 x + (x ^ 2 - p ^ 2) * y x = 0) :
    -(1 / (4 * Real.sqrt x ^ 3)) * y x + (2 * Real.sqrt x)⁻¹ * y1 x +
        ((2 * Real.sqrt x)⁻¹ * y1 x + Real.sqrt x * y2 x) +
      (1 + (1 / 4 - p ^ 2) / x ^ 2) * (Real.sqrt x * y x) = 0 := by
  have hsq : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  have h2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have := sqrt_transform_ode (p := p) (y := y x) (y1 := y1 x) (y2 := y2 x) hsq (by rw [h2]; exact E)
  rw [h2] at this
  exact this

/-- **Every nontrivial solution of Bessel's equation oscillates** (Lebl §7.3.3): it has arbitrarily large
zeros.  Here `y1`, `y2` are the first and second derivatives of `y` on `(0, ∞)`; no hypothesis on `p` and
no nontriviality hypothesis is needed (the zero function trivially has zeros). -/
@[kb "lebldiffyqs2026" "§7.3.3 Properties of Bessel functions, p. 349"]
theorem bessel_solution_infinite_zeros {p : ℝ} {y y1 y2 : ℝ → ℝ}
    (h0 : ∀ x > 0, HasDerivAt y (y1 x) x) (h1 : ∀ x > 0, HasDerivAt y1 (y2 x) x)
    (hode : ∀ x > 0, x ^ 2 * y2 x + x * y1 x + (x ^ 2 - p ^ 2) * y x = 0) :
    ∀ R : ℝ, ∃ x > R, y x = 0 := by
  intro R
  set a := max R (2 * |p|) + 1 with ha
  have hRa : R < a := by have := le_max_left R (2 * |p|); linarith
  have hpa : 2 * |p| + 1 ≤ a := by have := le_max_right R (2 * |p|); linarith
  have hapos : 0 < a := by have := abs_nonneg p; linarith
  have hmem : ∀ x ∈ Icc a (a + Real.pi / (1 / 2)), 0 < x := fun x hx => lt_of_lt_of_le hapos hx.1
  obtain ⟨x, hx, hx0⟩ := sturm_zero
    (u := fun t => Real.sqrt t * y t)
    (u1 := fun t => (2 * Real.sqrt t)⁻¹ * y t + Real.sqrt t * y1 t)
    (u2 := fun t => -(1 / (4 * Real.sqrt t ^ 3)) * y t + (2 * Real.sqrt t)⁻¹ * y1 t +
        ((2 * Real.sqrt t)⁻¹ * y1 t + Real.sqrt t * y2 t))
    (q := fun x => 1 + (1 / 4 - p ^ 2) / x ^ 2) (a := a) (m := 1 / 2) (by norm_num)
    (fun x hx => hasDerivAt_sqrt_mul (hmem x hx) (h0 x (hmem x hx)))
    (fun x hx => hasDerivAt_sqrt_mul_deriv (hmem x hx) (h0 x (hmem x hx)) (h1 x (hmem x hx)))
    (fun x hx => sqrt_mul_ode (hmem x hx) (hode x (hmem x hx)))
    (fun x hx => by
      have hxp : 2 * |p| + 1 ≤ x := hpa.trans hx.1
      have hx0 : 0 < x := hmem x hx
      have hxa : 2 * |p| ≤ x := by linarith
      have h1' : (2 * |p|) * (2 * |p|) ≤ x * x :=
        mul_self_le_mul_self (by positivity) hxa
      have h1 : 4 * p ^ 2 ≤ x ^ 2 := by nlinarith [sq_abs p]
      have h2 : (p ^ 2 - 1 / 4) / x ^ 2 ≤ 3 / 4 := by
        rw [div_le_iff₀ (by positivity)]; nlinarith
      have : (1 / 4 - p ^ 2) / x ^ 2 = -((p ^ 2 - 1 / 4) / x ^ 2) := by ring
      show (1 / 2) ^ 2 ≤ 1 + (1 / 4 - p ^ 2) / x ^ 2
      rw [this]
      nlinarith)
  have hx0' := hmem x hx
  refine ⟨x, lt_of_lt_of_le hRa hx.1, ?_⟩
  rcases mul_eq_zero.mp hx0 with h | h
  · exact absurd h (Real.sqrt_pos.mpr hx0').ne'
  · exact h

/-- A periodic solution of Bessel's equation on `(0, ∞)` vanishes identically. -/
lemma bessel_solution_periodic_zero {p : ℝ} {y y1 y2 : ℝ → ℝ}
    (h0 : ∀ x > 0, HasDerivAt y (y1 x) x) (h1 : ∀ x > 0, HasDerivAt y1 (y2 x) x)
    (hode : ∀ x > 0, x ^ 2 * y2 x + x * y1 x + (x ^ 2 - p ^ 2) * y x = 0)
    {T : ℝ} (hT : 0 < T) (hper : ∀ x > 0, y (x + T) = y x) : ∀ x > 0, y x = 0 := by
  have d1 : ∀ x > 0, y1 (x + T) = y1 x := by
    intro x hx
    have e1 : HasDerivAt (fun z => y (z + T)) (y1 (x + T)) x :=
      (h0 (x + T) (by linarith)).comp_add_const x T
    have e2 : HasDerivAt (fun z => y (z + T)) (y1 x) x := by
      refine (h0 x hx).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hx] with z hz using hper z hz
    exact e1.unique e2
  have d2 : ∀ x > 0, y2 (x + T) = y2 x := by
    intro x hx
    have e1 : HasDerivAt (fun z => y1 (z + T)) (y2 (x + T)) x :=
      (h1 (x + T) (by linarith)).comp_add_const x T
    have e2 : HasDerivAt (fun z => y1 (z + T)) (y2 x) x := by
      refine (h1 x hx).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hx] with z hz using d1 z hz
    exact e1.unique e2
  have key : ∀ x > 0, y1 x = 0 ∧ y2 x + y x = 0 ∧ p ^ 2 * y x = 0 := by
    intro x hx
    have hxT : 0 < x + T := by linarith
    have e0 := hode x hx
    have e1 := hode (x + T) hxT
    have e2 := hode (x + T + T) (by linarith)
    rw [d1 _ hxT, d2 _ hxT, hper _ hxT, d1 x hx, d2 x hx, hper x hx] at e2
    rw [d1 x hx, d2 x hx, hper x hx] at e1
    have g1 : T * ((2 * x + T) * (y2 x + y x) + y1 x) = 0 := by
      linear_combination e1 - e0
    have g2 : T * ((2 * x + 3 * T) * (y2 x + y x) + y1 x) = 0 := by
      linear_combination e2 - e1
    have g1' := (mul_eq_zero.mp g1).resolve_left hT.ne'
    have g2' := (mul_eq_zero.mp g2).resolve_left hT.ne'
    have hA0 : y2 x + y x = 0 := by
      have : (2 * T) * (y2 x + y x) = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left (by positivity)
    have hB0 : y1 x = 0 := by
      rw [hA0] at g1'; linarith
    refine ⟨hB0, hA0, ?_⟩
    linear_combination x ^ 2 * hA0 + x * hB0 - e0
  intro x hx
  obtain ⟨-, hA, hC⟩ := key x hx
  by_cases hp' : p = 0
  · have e1 : HasDerivAt y1 (y2 x) x := h1 x hx
    have e1' : HasDerivAt y1 0 x := by
      refine (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hx] with z hz using (key z hz).1
    have := e1.unique e1'
    linarith
  · exact (mul_eq_zero.mp hC).resolve_left (pow_ne_zero 2 hp')

/-- A nonzero solution of Bessel's equation (of any real order) is not periodic on `(0, ∞)`.  The argument
of `besselJR_not_periodic` uses only the differential equation, so it applies to every solution. -/
theorem bessel_solution_not_periodic {p : ℝ} {y y1 y2 : ℝ → ℝ}
    (h0 : ∀ x > 0, HasDerivAt y (y1 x) x) (h1 : ∀ x > 0, HasDerivAt y1 (y2 x) x)
    (hode : ∀ x > 0, x ^ 2 * y2 x + x * y1 x + (x ^ 2 - p ^ 2) * y x = 0)
    (hne : ∃ x > 0, y x ≠ 0) :
    ¬ ∃ T > 0, ∀ x > 0, y (x + T) = y x := by
  rintro ⟨T, hT, hper⟩
  obtain ⟨x, hx, hyx⟩ := hne
  exact hyx (bessel_solution_periodic_zero h0 h1 hode hT hper x hx)

end UndergradKB.DifferentialEquations
