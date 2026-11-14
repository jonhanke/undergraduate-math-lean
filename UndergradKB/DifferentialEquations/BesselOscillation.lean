import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import UndergradKB.DifferentialEquations.BesselSeries
import UndergradKB.DifferentialEquations.BesselSecondKind
import UndergradKB.Common.Attr

/-! # Bessel functions oscillate without being periodic (Lebl, §7.3.3)

A Sturm comparison lemma (a solution of `u'' + q u = 0` with `q ≥ m²` has a zero in every closed interval of
length `π/m`), applied to `u = √x J_p(x)` which solves `u'' + (1 + (1/4 - p²)/x²) u = 0`, shows that `J_p`
(`p ≥ 0`) has arbitrarily large zeros.  Also `J_0` is not periodic.
-/

namespace UndergradKB.DifferentialEquations

open Filter Topology Set

/-- Sturm comparison, positive case: no positive solution on the whole interval. -/
lemma sturm_pos {u u1 u2 q : ℝ → ℝ} {a m : ℝ} (hm : 0 < m)
    (hu : ∀ x ∈ Icc a (a + Real.pi / m), HasDerivAt u (u1 x) x)
    (hu1 : ∀ x ∈ Icc a (a + Real.pi / m), HasDerivAt u1 (u2 x) x)
    (hode : ∀ x ∈ Icc a (a + Real.pi / m), u2 x + q x * u x = 0)
    (hq : ∀ x ∈ Icc a (a + Real.pi / m), m ^ 2 ≤ q x)
    (hpos : ∀ x ∈ Icc a (a + Real.pi / m), 0 < u x) : False := by
  set b := a + Real.pi / m with hb
  have hab : a ≤ b := by
    have : 0 ≤ Real.pi / m := by positivity
    linarith
  set W : ℝ → ℝ := fun x => u1 x * Real.sin (m * (x - a)) - u x * (m * Real.cos (m * (x - a))) with hW
  have hs : ∀ x : ℝ, HasDerivAt (fun x => Real.sin (m * (x - a))) (Real.cos (m * (x - a)) * m) x := by
    intro x
    have h := (((hasDerivAt_id x).sub_const a).const_mul m).sin
    simpa using h
  have hc : ∀ x : ℝ, HasDerivAt (fun x => m * Real.cos (m * (x - a))) (-(m ^ 2) * Real.sin (m * (x - a))) x := by
    intro x
    have h := ((((hasDerivAt_id x).sub_const a).const_mul m).cos).const_mul m
    refine (by simpa using h : HasDerivAt (fun x => m * Real.cos (m * (x - a)))
      (m * (-Real.sin (m * (x - a)) * m)) x).congr_deriv (by ring)
  have hWd : ∀ x ∈ Icc a b, HasDerivAt W ((m ^ 2 - q x) * u x * Real.sin (m * (x - a))) x := by
    intro x hx
    have h := ((hu1 x hx).mul (hs x)).sub ((hu x hx).mul (hc x))
    refine h.congr_deriv ?_
    have := hode x hx
    have e : u2 x = - q x * u x := by linarith
    rw [e]
    ring
  have hsin : ∀ x ∈ Icc a b, 0 ≤ Real.sin (m * (x - a)) := by
    intro x hx
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · exact mul_nonneg hm.le (by linarith [hx.1])
    · have h1 : x - a ≤ Real.pi / m := by linarith [hx.2]
      calc m * (x - a) ≤ m * (Real.pi / m) := by gcongr
        _ = Real.pi := by field_simp
  have hanti : AntitoneOn W (Icc a b) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc a b) ?_ ?_ ?_
    · exact fun x hx => (hWd x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hWd x (Ioo_subset_Icc_self hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx' := Ioo_subset_Icc_self hx
      rw [(hWd x hx').deriv]
      have h1 : m ^ 2 - q x ≤ 0 := by linarith [hq x hx']
      have h2 := hpos x hx'
      have h3 := hsin x hx'
      have : (m ^ 2 - q x) * u x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h1 h2.le
      exact mul_nonpos_of_nonpos_of_nonneg this h3
  have haI : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hbI : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hWa : W a = - (m * u a) := by
    simp [hW]; ring
  have hWb : W b = m * u b := by
    have e : m * (b - a) = Real.pi := by
      rw [hb]; field_simp; ring
    simp only [hW, e, Real.sin_pi, Real.cos_pi]
    ring
  have := hanti haI hbI hab
  have h1 := hpos a haI
  have h2 := hpos b hbI
  rw [hWa, hWb] at this
  nlinarith

/-- Sturm comparison lemma: if `u'' + q u = 0` on `[a, a + π/m]` with `q ≥ m² > 0`, then `u` has a zero in
`[a, a + π/m]`.  (`u1`, `u2` are the first and second derivatives of `u`.) -/
theorem sturm_zero {u u1 u2 q : ℝ → ℝ} {a m : ℝ} (hm : 0 < m)
    (hu : ∀ x ∈ Icc a (a + Real.pi / m), HasDerivAt u (u1 x) x)
    (hu1 : ∀ x ∈ Icc a (a + Real.pi / m), HasDerivAt u1 (u2 x) x)
    (hode : ∀ x ∈ Icc a (a + Real.pi / m), u2 x + q x * u x = 0)
    (hq : ∀ x ∈ Icc a (a + Real.pi / m), m ^ 2 ≤ q x) :
    ∃ x ∈ Icc a (a + Real.pi / m), u x = 0 := by
  by_contra hno
  push Not at hno
  set b := a + Real.pi / m with hb
  have hab : a ≤ b := by
    have : 0 ≤ Real.pi / m := by positivity
    linarith
  have haI : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hcont : ContinuousOn u (Icc a b) := fun x hx => (hu x hx).continuousAt.continuousWithinAt
  -- constant sign
  have sign : ∀ x ∈ Icc a b, 0 < u a → 0 < u x := by
    intro x hx ha
    by_contra hneg
    push Not at hneg
    obtain ⟨y, hy, hy0⟩ := isPreconnected_Icc.intermediate_value hx haI hcont ⟨hneg, ha.le⟩
    exact hno y hy hy0
  have sign' : ∀ x ∈ Icc a b, u a < 0 → u x < 0 := by
    intro x hx ha
    by_contra hneg
    push Not at hneg
    obtain ⟨y, hy, hy0⟩ := isPreconnected_Icc.intermediate_value haI hx hcont ⟨ha.le, hneg⟩
    exact hno y hy hy0
  rcases lt_or_gt_of_ne (hno a haI) with h | h
  · refine sturm_pos (u := fun x => - u x) (u1 := fun x => - u1 x) (u2 := fun x => - u2 x) (q := q) hm
      (fun x hx => (hu x hx).neg) (fun x hx => (hu1 x hx).neg) (fun x hx => ?_) hq
      (fun x hx => ?_)
    · have := hode x hx
      linarith
    · have := sign' x hx h
      linarith
  · exact sturm_pos hm hu hu1 hode hq (fun x hx => sign x hx h)

/-- The auxiliary function `√x J_p(x)`, its derivative and second derivative. -/
noncomputable def sqrtJ (p x : ℝ) : ℝ := Real.sqrt x * besselJR p x

/-- First derivative of `sqrtJ`. -/
noncomputable def sqrtJ1 (p x : ℝ) : ℝ := (2 * Real.sqrt x)⁻¹ * besselJR p x + Real.sqrt x * besselJ1 p x

/-- Second derivative of `sqrtJ`. -/
noncomputable def sqrtJ2 (p x : ℝ) : ℝ :=
  -(1 / (4 * Real.sqrt x ^ 3)) * besselJR p x + (Real.sqrt x)⁻¹ * besselJ1 p x +
    Real.sqrt x * besselJ2 p x

lemma hasDerivAt_sqrtJ (p : ℝ) (hp : ∀ m : ℕ, p + 1 ≠ -(m : ℝ)) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (sqrtJ p) (sqrtJ1 p x) x := by
  have hs := Real.hasDerivAt_sqrt hx.ne'
  have h := hs.mul (hasDerivAt_besselJR p hp hx)
  refine h.congr_deriv ?_
  unfold sqrtJ1
  have : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  field_simp

lemma hasDerivAt_sqrtJ1 (p : ℝ) (hp : ∀ m : ℕ, p + 1 ≠ -(m : ℝ)) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (sqrtJ1 p) (sqrtJ2 p x) x := by
  have hs := Real.hasDerivAt_sqrt hx.ne'
  have hsq : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  have hw : HasDerivAt (fun y => (2 * Real.sqrt y)⁻¹) (-(1 / (4 * Real.sqrt x ^ 3))) x := by
    have h := (hs.const_mul 2).inv (by positivity)
    refine h.congr_deriv ?_
    have h2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
    field_simp
    nlinarith [h2]
  have h := (hw.mul (hasDerivAt_besselJR p hp hx)).add (hs.mul (hasDerivAt_besselJ1 p hp hx))
  refine h.congr_deriv ?_
  unfold sqrtJ2
  field_simp
  ring

lemma sqrtJ2_ode (p : ℝ) (hp : ∀ m : ℕ, p + 1 ≠ -(m : ℝ)) {x : ℝ} (hx : 0 < x) :
    sqrtJ2 p x + (1 + (1 / 4 - p ^ 2) / x ^ 2) * sqrtJ p x = 0 := by
  have E := besselJ2_ode p hp hx
  have hsq : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  have h2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have hx0 : x ≠ 0 := hx.ne'
  unfold sqrtJ2 sqrtJ
  generalize besselJR p x = J at *
  generalize besselJ1 p x = J1 at *
  generalize besselJ2 p x = J2 at *
  generalize Real.sqrt x = s at *
  subst h2
  have hJ2 : J2 = (-(s ^ 2 * J1) - ((s ^ 2) ^ 2 - p ^ 2) * J) / (s ^ 2) ^ 2 := by
    field_simp
    linear_combination E
  rw [hJ2]
  field_simp
  ring

/-- `J_p` has arbitrarily large zeros for `p ≥ 0`. -/
theorem besselJR_infinite_zeros {p : ℝ} (hp : 0 ≤ p) (X : ℝ) : ∃ x > X, besselJR p x = 0 := by
  have hp' := hp_of_nonneg hp
  set a := max X (2 * p) + 1 with ha
  have hXa : X < a := by have := le_max_left X (2 * p); linarith
  have hpa : 2 * p + 1 ≤ a := by have := le_max_right X (2 * p); linarith
  have hapos : 0 < a := by linarith
  have hmem : ∀ x ∈ Icc a (a + Real.pi / (1 / 2)), 0 < x := fun x hx => lt_of_lt_of_le hapos hx.1
  obtain ⟨x, hx, hx0⟩ := sturm_zero (u := sqrtJ p) (u1 := sqrtJ1 p) (u2 := sqrtJ2 p)
    (q := fun x => 1 + (1 / 4 - p ^ 2) / x ^ 2) (a := a) (m := 1 / 2) (by norm_num)
    (fun x hx => hasDerivAt_sqrtJ p hp' (hmem x hx))
    (fun x hx => hasDerivAt_sqrtJ1 p hp' (hmem x hx))
    (fun x hx => sqrtJ2_ode p hp' (hmem x hx))
    (fun x hx => by
      have hxp : 2 * p + 1 ≤ x := hpa.trans hx.1
      have hx0 : 0 < x := hmem x hx
      have h1 : 4 * p ^ 2 ≤ x ^ 2 := by nlinarith
      have h2 : (p ^ 2 - 1 / 4) / x ^ 2 ≤ 3 / 4 := by
        rw [div_le_iff₀ (by positivity)]; nlinarith
      have : (1 / 4 - p ^ 2) / x ^ 2 = -((p ^ 2 - 1 / 4) / x ^ 2) := by ring
      show (1 / 2) ^ 2 ≤ 1 + (1 / 4 - p ^ 2) / x ^ 2
      rw [this]
      nlinarith)
  have hx0' := hmem x hx
  refine ⟨x, lt_of_lt_of_le hXa hx.1, ?_⟩
  unfold sqrtJ at hx0
  rcases mul_eq_zero.mp hx0 with h | h
  · exact absurd h (Real.sqrt_pos.mpr hx0').ne'
  · exact h

/-- `J_0` is not periodic on `(0, ∞)`. -/
theorem besselJR_zero_not_periodic : ¬ ∃ T > 0, ∀ x > 0, besselJR 0 (x + T) = besselJR 0 x := by
  rintro ⟨T, hT, hper⟩
  have hp0 := hp_of_nonneg (le_refl (0 : ℝ))
  -- shifted derivatives
  have d1 : ∀ x > 0, besselJ1 0 (x + T) = besselJ1 0 x := by
    intro x hx
    have h1 : HasDerivAt (fun y => besselJR 0 (y + T)) (besselJ1 0 (x + T)) x := by
      have := (hasDerivAt_besselJR 0 hp0 (by linarith : 0 < x + T)).comp_add_const x T
      exact this
    have h2 : HasDerivAt (fun y => besselJR 0 (y + T)) (besselJ1 0 x) x := by
      refine (hasDerivAt_besselJR 0 hp0 hx).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hx] with y hy using hper y hy
    exact h1.unique h2
  have d2 : ∀ x > 0, besselJ2 0 (x + T) = besselJ2 0 x := by
    intro x hx
    have h1 : HasDerivAt (fun y => besselJ1 0 (y + T)) (besselJ2 0 (x + T)) x :=
      (hasDerivAt_besselJ1 0 hp0 (by linarith : 0 < x + T)).comp_add_const x T
    have h2 : HasDerivAt (fun y => besselJ1 0 (y + T)) (besselJ2 0 x) x := by
      refine (hasDerivAt_besselJ1 0 hp0 hx).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hx] with y hy using d1 y hy
    exact h1.unique h2
  have ode : ∀ x > 0, x * besselJ2 0 x + besselJ1 0 x + x * besselJR 0 x = 0 := by
    intro x hx
    have := besselJ2_ode 0 hp0 hx
    have h : x * (x * besselJ2 0 x + besselJ1 0 x + x * besselJR 0 x) = 0 := by
      linear_combination this
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hx.ne'
    · exact h
  have hJ2 : ∀ x > 0, besselJ2 0 x = - besselJR 0 x := by
    intro x hx
    have e1 := ode x hx
    have e2 := ode (x + T) (by linarith)
    rw [d1 x hx, d2 x hx, hper x hx] at e2
    have : T * (besselJ2 0 x + besselJR 0 x) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hT.ne'
    · linarith
  have hJ1 : ∀ x > 0, besselJ1 0 x = 0 := by
    intro x hx
    have := ode x hx
    rw [hJ2 x hx] at this
    linarith
  have hJ2z : ∀ x > 0, besselJ2 0 x = 0 := by
    intro x hx
    have h1 := hasDerivAt_besselJ1 0 hp0 hx
    have h2 : HasDerivAt (besselJ1 0) 0 x := by
      refine (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hx] with y hy using hJ1 y hy
    exact h1.unique h2
  have hJz : ∀ x > 0, besselJR 0 x = 0 := by
    intro x hx
    have := hJ2 x hx
    rw [hJ2z x hx] at this
    linarith
  have h1 : Tendsto (besselJR 0) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [self_mem_nhdsWithin] with y hy using (hJz y hy).symm)
  exact one_ne_zero (tendsto_nhds_unique besselJR_zero_tendsto h1)

lemma evS_zero (p : ℝ) : evS (bcoef p) 0 = bcoef p 0 := by
  unfold evS
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    have : 2 * n ≠ 0 := by omega
    simp [this]

lemma besselJR_not_identically_zero {p : ℝ} (hp : ∀ m : ℕ, p + 1 ≠ -(m : ℝ)) :
    ¬ ∀ x > 0, besselJR p x = 0 := by
  intro hz
  have hev : ∀ x > 0, evS (bcoef p) x = 0 := by
    intro x hx
    have := hz x hx
    rw [besselJR_eq p x hx] at this
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (Real.rpow_pos_of_pos (by positivity) p).ne'
    · exact h
  have hc : ContinuousAt (evS (bcoef p)) 0 := (hasDerivAt_evS (bcoef_hsum p hp) 0).continuousAt
  have h1 : Tendsto (evS (bcoef p)) (𝓝[>] 0) (𝓝 (evS (bcoef p) 0)) :=
    hc.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (evS (bcoef p)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [self_mem_nhdsWithin] with y hy using (hev y hy).symm)
  have := tendsto_nhds_unique h1 h2
  rw [evS_zero] at this
  exact bcoef_ne p hp 0 this

/-- `J_p` is not periodic on `(0, ∞)`, for every `p ≥ 0`. -/
theorem besselJR_not_periodic {p : ℝ} (hp : 0 ≤ p) :
    ¬ ∃ T > 0, ∀ x > 0, besselJR p (x + T) = besselJR p x := by
  rintro ⟨T, hT, hper⟩
  have hp0 := hp_of_nonneg hp
  have d1 : ∀ x > 0, besselJ1 p (x + T) = besselJ1 p x := by
    intro x hx
    have h1 : HasDerivAt (fun y => besselJR p (y + T)) (besselJ1 p (x + T)) x :=
      (hasDerivAt_besselJR p hp0 (by linarith : 0 < x + T)).comp_add_const x T
    have h2 : HasDerivAt (fun y => besselJR p (y + T)) (besselJ1 p x) x := by
      refine (hasDerivAt_besselJR p hp0 hx).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hx] with y hy using hper y hy
    exact h1.unique h2
  have d2 : ∀ x > 0, besselJ2 p (x + T) = besselJ2 p x := by
    intro x hx
    have h1 : HasDerivAt (fun y => besselJ1 p (y + T)) (besselJ2 p (x + T)) x :=
      (hasDerivAt_besselJ1 p hp0 (by linarith : 0 < x + T)).comp_add_const x T
    have h2 : HasDerivAt (fun y => besselJ1 p (y + T)) (besselJ2 p x) x := by
      refine (hasDerivAt_besselJ1 p hp0 hx).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hx] with y hy using d1 y hy
    exact h1.unique h2
  -- at each `x₀`, the quadratic `y² (J'' + J) + y J' - p² J` vanishes at `x₀, x₀+T, x₀+2T`
  have key : ∀ x > 0, besselJ1 p x = 0 ∧ besselJ2 p x + besselJR p x = 0 ∧ p ^ 2 * besselJR p x = 0 := by
    intro x hx
    have hxT : 0 < x + T := by linarith
    have e0 := besselJ2_ode p hp0 hx
    have e1 := besselJ2_ode p hp0 hxT
    have e2 := besselJ2_ode p hp0 (by linarith : 0 < x + T + T)
    rw [d1 _ hxT, d2 _ hxT, hper _ hxT, d1 x hx, d2 x hx, hper x hx] at e2
    rw [d1 x hx, d2 x hx, hper x hx] at e1
    have g1 : T * ((2 * x + T) * (besselJ2 p x + besselJR p x) + besselJ1 p x) = 0 := by
      linear_combination e1 - e0
    have g2 : T * ((2 * x + 3 * T) * (besselJ2 p x + besselJR p x) + besselJ1 p x) = 0 := by
      linear_combination e2 - e1
    have g1' := (mul_eq_zero.mp g1).resolve_left hT.ne'
    have g2' := (mul_eq_zero.mp g2).resolve_left hT.ne'
    have hA0 : besselJ2 p x + besselJR p x = 0 := by
      have : (2 * T) * (besselJ2 p x + besselJR p x) = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left (by positivity)
    have hB0 : besselJ1 p x = 0 := by
      rw [hA0] at g1'; linarith
    refine ⟨hB0, hA0, ?_⟩
    linear_combination x ^ 2 * hA0 + x * hB0 - e0
  have hJz : ∀ x > 0, besselJR p x = 0 := by
    intro x hx
    obtain ⟨-, h2, h3⟩ := key x hx
    by_cases hp' : p = 0
    · have h1 : HasDerivAt (besselJ1 p) (besselJ2 p x) x := hasDerivAt_besselJ1 p hp0 hx
      have h1' : HasDerivAt (besselJ1 p) 0 x := by
        refine (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq ?_
        filter_upwards [Ioi_mem_nhds hx] with y hy using (key y hy).1
      have := h1.unique h1'
      linarith
    · exact (mul_eq_zero.mp h3).resolve_left (pow_ne_zero 2 hp')
  exact besselJR_not_identically_zero hp0 hJz

/-- DE-215: Bessel functions oscillate without being periodic.  For every `p ≥ 0`, `J_p` has arbitrarily
large zeros (it oscillates), and `J_p` is not periodic on `(0, ∞)`.  (The identities `J_0' = -J_1` and
`J_p' = (J_{p-1} - J_{p+1})/2` are `deriv_besselJR_zero` and `deriv_besselJR_half`.) -/
@[kb "lebldiffyqs2026" "§7.3.3 Properties of Bessel functions, p. 349"]
theorem bessel_oscillate_not_periodic {p : ℝ} (hp : 0 ≤ p) :
    (∀ X : ℝ, ∃ x > X, besselJR p x = 0) ∧
      ¬ ∃ T > 0, ∀ x > 0, besselJR p (x + T) = besselJR p x :=
  ⟨fun X => besselJR_infinite_zeros hp X, besselJR_not_periodic hp⟩

end UndergradKB.DifferentialEquations
