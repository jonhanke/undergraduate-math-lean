import UndergradKB.Common.Attr
import UndergradKB.DifferentialEquations.ConstantCoefficients
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Steady periodic solutions: forced vibrating string and underground temperature (Lebl §5.3)

Two examples where the forcing is periodic in time and one looks for a solution with the same period.

* A string with fixed ends driven by a cosine force, `y_tt = a² y_xx + F₀ cos(ωt)` with `y(0,t) = y(L,t) = 0`.
  The ansatz `y = X(x) cos(ωt)` reduces this to `a² X'' + ω² X + F₀ = 0`, `X(0) = X(L) = 0`.  We exhibit `X`
  when `sin(ωL/a) ≠ 0` and when `sin(ωL/a) = 0` with `cos(ωL/a) = 1`, and prove that such an `X` exists
  exactly outside the resonant case `sin(ωL/a) = 0`, `cos(ωL/a) = -1` (which means `ω = nπa/L`, `n` odd).
* The heat equation `u_t = k u_xx` on a half line with periodic boundary temperature: the damped travelling
  wave `A₀ e^{-cx} cos(ωt - cx)` with `c = √(ω/(2k))`.

Partial derivatives are written with nested `deriv`. -/

namespace UndergradKB.DifferentialEquations

/-- The spatial profile `(F₀/ω²)(cos(kx) + B sin(kx) - 1)` with `k = ω/a`. -/
noncomputable def stringX (a ω F₀ B x : ℝ) : ℝ :=
  F₀ / ω ^ 2 * (Real.cos (ω / a * x) + B * Real.sin (ω / a * x) - 1)

/-- First derivative of `stringX`. -/
noncomputable def stringX1 (a ω F₀ B x : ℝ) : ℝ :=
  F₀ / ω ^ 2 * (-((ω / a) * Real.sin (ω / a * x)) + B * ((ω / a) * Real.cos (ω / a * x)))

/-- Second derivative of `stringX`. -/
noncomputable def stringX2 (a ω F₀ B x : ℝ) : ℝ :=
  F₀ / ω ^ 2 * (-((ω / a) * ((ω / a) * Real.cos (ω / a * x))) +
    B * ((ω / a) * (-((ω / a) * Real.sin (ω / a * x)))))

lemma stringX_hasDerivAt (a ω F₀ B x : ℝ) :
    HasDerivAt (stringX a ω F₀ B) (stringX1 a ω F₀ B x) x := by
  have h := (((hasDerivAt_cos_mul' (ω / a) x).add
    ((hasDerivAt_sin_mul' (ω / a) x).const_mul B)).sub_const 1).const_mul (F₀ / ω ^ 2)
  exact h

lemma stringX1_hasDerivAt (a ω F₀ B x : ℝ) :
    HasDerivAt (stringX1 a ω F₀ B) (stringX2 a ω F₀ B x) x := by
  have h := ((((hasDerivAt_sin_mul' (ω / a) x).const_mul (ω / a)).neg).add
    (((hasDerivAt_cos_mul' (ω / a) x).const_mul (ω / a)).const_mul B)).const_mul (F₀ / ω ^ 2)
  exact h

lemma stringX_ode {a ω : ℝ} (ha : a ≠ 0) (hω : ω ≠ 0) (F₀ B x : ℝ) :
    a ^ 2 * stringX2 a ω F₀ B x + ω ^ 2 * stringX a ω F₀ B x + F₀ = 0 := by
  unfold stringX2 stringX
  have hk2 : a ^ 2 * (ω / a) ^ 2 = ω ^ 2 := by field_simp
  have hc : F₀ / ω ^ 2 * ω ^ 2 = F₀ := by field_simp
  linear_combination (-(F₀ / ω ^ 2 * (Real.cos (ω / a * x) + B * Real.sin (ω / a * x)))) * hk2 - hc

/-- The two boundary conditions and the forced wave equation `y_tt = a² y_xx + F₀ cos(ωt)` for `yp`. -/
def ForcedStringSolves (a ω L F₀ : ℝ) (yp : ℝ → ℝ → ℝ) : Prop :=
  (∀ x t, deriv (fun t => deriv (fun t => yp x t) t) t =
      a ^ 2 * deriv (fun x => deriv (fun x => yp x t) x) x + F₀ * Real.cos (ω * t)) ∧
    (∀ t, yp 0 t = 0) ∧ (∀ t, yp L t = 0)

/-- Separation of variables: if `X` solves the spatial ODE then `X(x) cos(ωt)` solves the wave equation. -/
lemma string_pde {X X1 X2 : ℝ → ℝ} (a ω F₀ : ℝ) (h1 : ∀ x, HasDerivAt X (X1 x) x)
    (h2 : ∀ x, HasDerivAt X1 (X2 x) x) (hode : ∀ x, a ^ 2 * X2 x + ω ^ 2 * X x + F₀ = 0) (x t : ℝ) :
    deriv (fun t => deriv (fun t => X x * Real.cos (ω * t)) t) t =
      a ^ 2 * deriv (fun x => deriv (fun x => X x * Real.cos (ω * t)) x) x +
        F₀ * Real.cos (ω * t) := by
  have ht : ∀ x t, HasDerivAt (fun t => X x * Real.cos (ω * t))
      (X x * (-(ω * Real.sin (ω * t)))) t :=
    fun x t => (hasDerivAt_cos_mul' ω t).const_mul (X x)
  have ht2 : ∀ x t, HasDerivAt (fun t => X x * (-(ω * Real.sin (ω * t))))
      (X x * (-(ω * (ω * Real.cos (ω * t))))) t :=
    fun x t => (((hasDerivAt_sin_mul' ω t).const_mul ω).neg).const_mul (X x)
  have hx : ∀ x t, HasDerivAt (fun x => X x * Real.cos (ω * t)) (X1 x * Real.cos (ω * t)) x :=
    fun x t => (h1 x).mul_const _
  have hx2 : ∀ x t, HasDerivAt (fun x => X1 x * Real.cos (ω * t)) (X2 x * Real.cos (ω * t)) x :=
    fun x t => (h2 x).mul_const _
  have A : deriv (fun t => deriv (fun t => X x * Real.cos (ω * t)) t) t =
      X x * (-(ω * (ω * Real.cos (ω * t)))) := by
    have : (fun t => deriv (fun t => X x * Real.cos (ω * t)) t) =
        fun t => X x * (-(ω * Real.sin (ω * t))) := funext fun t => (ht x t).deriv
    rw [this]
    exact (ht2 x t).deriv
  have B : deriv (fun x => deriv (fun x => X x * Real.cos (ω * t)) x) x =
      X2 x * Real.cos (ω * t) := by
    have : (fun x => deriv (fun x => X x * Real.cos (ω * t)) x) =
        fun x => X1 x * Real.cos (ω * t) := funext fun x => (hx x t).deriv
    rw [this]
    exact (hx2 x t).deriv
  rw [A, B]
  linear_combination (-Real.cos (ω * t)) * hode x

lemma stringX_solves {a ω L : ℝ} (ha : a ≠ 0) (hω : ω ≠ 0) (F₀ B : ℝ)
    (hL : stringX a ω F₀ B L = 0) :
    ForcedStringSolves a ω L F₀ (fun x t => stringX a ω F₀ B x * Real.cos (ω * t)) := by
  refine ⟨fun x t => string_pde a ω F₀ (stringX_hasDerivAt a ω F₀ B)
    (stringX1_hasDerivAt a ω F₀ B) (stringX_ode ha hω F₀ B) x t, fun t => ?_, fun t => ?_⟩
  · simp [stringX]
  · simp only [hL, zero_mul]

/-- **Forced string, non-resonant case** (Lebl §5.3.1): if `sin(ωL/a) ≠ 0`, then
`X(x) = (F₀/ω²)(cos(ωx/a) - ((cos(ωL/a) - 1)/sin(ωL/a)) sin(ωx/a) - 1)` gives a solution `X(x) cos(ωt)`
of `y_tt = a² y_xx + F₀ cos(ωt)` that vanishes at `x = 0` and `x = L`. (Here `ωx/a` is written `(ω/a) x`.) -/
@[kb "lebldiffyqs2026" "§5.3.1 Forced vibrating string, p. 287"]
theorem forced_string_particular {a ω L F₀ : ℝ} (ha : 0 < a) (hω : 0 < ω) (_hL : 0 < L)
    (hs : Real.sin (ω / a * L) ≠ 0) :
    ForcedStringSolves a ω L F₀ (fun x t =>
      F₀ / ω ^ 2 * (Real.cos (ω / a * x) -
        ((Real.cos (ω / a * L) - 1) / Real.sin (ω / a * L)) * Real.sin (ω / a * x) - 1) *
        Real.cos (ω * t)) := by
  have h := stringX_solves (L := L) ha.ne' hω.ne' F₀
    (-((Real.cos (ω / a * L) - 1) / Real.sin (ω / a * L))) (by
      unfold stringX
      have : -((Real.cos (ω / a * L) - 1) / Real.sin (ω / a * L)) * Real.sin (ω / a * L) =
          -(Real.cos (ω / a * L) - 1) := by rw [neg_mul, div_mul_cancel₀ _ hs]
      rw [this]; ring)
  convert h using 4 with x t
  unfold stringX
  ring

/-- **Forced string, `sin = 0`, `cos = 1`** (Lebl §5.3.1): if `sin(ωL/a) = 0` and `cos(ωL/a) = 1` (the
case `ω = nπa/L` with `n` even), then `X(x) = (F₀/ω²)(cos(ωx/a) - 1)` works. -/
theorem forced_string_even {a ω L F₀ : ℝ} (ha : 0 < a) (hω : 0 < ω) (_hL : 0 < L)
    (_hs : Real.sin (ω / a * L) = 0) (hc : Real.cos (ω / a * L) = 1) :
    ForcedStringSolves a ω L F₀ (fun x t =>
      F₀ / ω ^ 2 * (Real.cos (ω / a * x) - 1) * Real.cos (ω * t)) := by
  have h := stringX_solves (L := L) ha.ne' hω.ne' F₀ 0 (by simp [stringX, hc])
  convert h using 4 with x t
  simp [stringX]

/-- Reduction of `sin θ = 0 ∧ cos θ = -1` to `cos (θ - π) = 1`. -/
lemma res_iff_cos (θ : ℝ) :
    (Real.sin θ = 0 ∧ Real.cos θ = -1) ↔ Real.cos (θ - Real.pi) = 1 := by
  rw [Real.cos_sub_pi]
  constructor
  · rintro ⟨_, h⟩
    rw [h]; norm_num
  · intro h
    have hc : Real.cos θ = -1 := by linarith
    refine ⟨?_, hc⟩
    have h2 : Real.sin θ ^ 2 = 0 := by
      have := Real.sin_sq_add_cos_sq θ
      rw [hc] at this
      linarith
    exact pow_eq_zero_iff (two_ne_zero) |>.1 h2

lemma cd2 {X : ℝ → ℝ} (hX : ContDiff ℝ 2 X) :
    Differentiable ℝ X ∧ Differentiable ℝ (deriv X) := by
  have e2 : ((2 : WithTop ℕ∞)) = 1 + 1 := by norm_num
  rw [e2] at hX
  have h := contDiff_succ_iff_deriv.1 hX
  exact ⟨h.1, h.2.2.differentiable one_ne_zero⟩

/-- In the resonant case no spatial profile exists. -/
lemma no_profile {a ω L F₀ : ℝ} (ha : 0 < a) (hω : 0 < ω) (hF : F₀ ≠ 0)
    (hres : Real.sin (ω * L / a) = 0 ∧ Real.cos (ω * L / a) = -1) {X : ℝ → ℝ}
    (hX : ContDiff ℝ 2 X) (hode : ∀ x, a ^ 2 * deriv (deriv X) x + ω ^ 2 * X x + F₀ = 0)
    (h0 : X 0 = 0) (hLX : X L = 0) : False := by
  obtain ⟨hd1, hd2⟩ := cd2 hX
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha.ne'
  have hω2 : ω ^ 2 ≠ 0 := pow_ne_zero 2 hω.ne'
  have hZ : deriv (fun x => X x + F₀ / ω ^ 2) = deriv X :=
    funext fun x => deriv_add_const _
  have hsolve : SolvesCC 1 0 ((ω / a) ^ 2) (fun x => X x + F₀ / ω ^ 2) := by
    intro x
    refine ⟨(hd1 x).add_const _, ?_, ?_⟩
    · rw [hZ]; exact hd2 x
    · simp only [hZ]
      have hXdd : deriv (deriv X) x = -(ω ^ 2 * X x + F₀) / a ^ 2 := by
        rw [eq_div_iff ha2]
        linear_combination hode x
      have e : (ω / a) ^ 2 * (X x + F₀ / ω ^ 2) = (ω ^ 2 * X x + F₀) / a ^ 2 := by
        field_simp
      rw [e, hXdd]
      ring
  obtain ⟨C₁, C₂, hC⟩ := (fundamental_cos_sin (div_pos hω ha)).1 hsolve
  have e0 := hC 0
  have eL := hC L
  simp only [h0, mul_zero, Real.cos_zero, Real.sin_zero, zero_add, mul_one] at e0
  rw [hLX, zero_add] at eL
  have hs : Real.sin (ω / a * L) = 0 := by rw [← mul_div_right_comm]; exact hres.1
  have hc : Real.cos (ω / a * L) = -1 := by rw [← mul_div_right_comm]; exact hres.2
  rw [hs, hc] at eL
  have : F₀ / ω ^ 2 = 0 := by linarith
  rcases div_eq_zero_iff.1 this with h | h
  · exact hF h
  · exact hω2 h

/-- **Resonance criterion** (Lebl §5.3.1): for `F₀ ≠ 0`, the spatial problem
`a² X'' + ω² X + F₀ = 0`, `X(0) = X(L) = 0` has a (`C²`) solution exactly when we are not in the resonant case
`sin(ωL/a) = 0` and `cos(ωL/a) = -1`. -/
@[kb "lebldiffyqs2026" "§5.3.1 Forced vibrating string, p. 288"]
theorem forced_string_resonance {a ω L F₀ : ℝ} (ha : 0 < a) (hω : 0 < ω) (hL : 0 < L)
    (hF : F₀ ≠ 0) :
    (∃ X : ℝ → ℝ, ContDiff ℝ 2 X ∧ (∀ x, a ^ 2 * deriv (deriv X) x + ω ^ 2 * X x + F₀ = 0) ∧
        X 0 = 0 ∧ X L = 0) ↔
      ¬ (Real.sin (ω * L / a) = 0 ∧ Real.cos (ω * L / a) = -1) := by
  constructor
  · rintro ⟨X, hX, hode, h0, hLX⟩ hres
    exact no_profile ha hω hF hres hX hode h0 hLX
  · intro hres
    have hcd : ∀ B : ℝ, ContDiff ℝ 2 (stringX a ω F₀ B) := fun B => by
      unfold stringX; fun_prop
    have hder : ∀ B : ℝ, ∀ x, deriv (deriv (stringX a ω F₀ B)) x = stringX2 a ω F₀ B x := by
      intro B x
      have : deriv (stringX a ω F₀ B) = stringX1 a ω F₀ B :=
        funext fun x => (stringX_hasDerivAt a ω F₀ B x).deriv
      rw [this]
      exact (stringX1_hasDerivAt a ω F₀ B x).deriv
    have hkL : ω * L / a = ω / a * L := mul_div_right_comm _ _ _
    rw [hkL] at hres
    by_cases hs : Real.sin (ω / a * L) = 0
    · have hc : Real.cos (ω / a * L) = 1 := by
        have h1 := Real.sin_sq_add_cos_sq (ω / a * L)
        rw [hs] at h1
        have h2 : (Real.cos (ω / a * L) - 1) * (Real.cos (ω / a * L) + 1) = 0 := by nlinarith
        rcases mul_eq_zero.1 h2 with h | h
        · linarith
        · exact absurd ⟨hs, by linarith⟩ hres
      refine ⟨stringX a ω F₀ 0, hcd 0, fun x => ?_, by simp [stringX], by simp [stringX, hc]⟩
      rw [hder]; exact stringX_ode ha.ne' hω.ne' F₀ 0 x
    · refine ⟨stringX a ω F₀ (-((Real.cos (ω / a * L) - 1) / Real.sin (ω / a * L))),
        hcd _, fun x => ?_, by simp [stringX], ?_⟩
      · rw [hder]; exact stringX_ode ha.ne' hω.ne' F₀ _ x
      · unfold stringX
        have : -((Real.cos (ω / a * L) - 1) / Real.sin (ω / a * L)) * Real.sin (ω / a * L) =
            -(Real.cos (ω / a * L) - 1) := by rw [neg_mul, div_mul_cancel₀ _ hs]
        rw [this]; ring

/-- The resonant frequencies are `ω = nπa/L` with `n` odd. -/
theorem resonance_iff_odd {a ω L : ℝ} (ha : 0 < a) (hω : 0 < ω) (hL : 0 < L) :
    (Real.sin (ω * L / a) = 0 ∧ Real.cos (ω * L / a) = -1) ↔
      ∃ n : ℕ, Odd n ∧ ω = n * Real.pi * a / L := by
  rw [res_iff_cos, Real.cos_eq_one_iff]
  constructor
  · rintro ⟨m, hm⟩
    have hθ : ω * L / a = (2 * m + 1) * Real.pi := by linarith
    have hpos : 0 < ω * L / a := by positivity
    have hm0 : (0 : ℝ) < 2 * m + 1 := by
      by_contra hneg
      push Not at hneg
      nlinarith [Real.pi_pos]
    have hmi : (0 : ℤ) < 2 * m + 1 := by exact_mod_cast hm0
    refine ⟨(2 * m + 1).toNat, ?_, ?_⟩
    · rw [Nat.odd_iff]
      omega
    · have hn : (((2 * m + 1).toNat : ℕ) : ℝ) = 2 * m + 1 := by
        have : (((2 * m + 1).toNat : ℕ) : ℤ) = 2 * m + 1 := Int.toNat_of_nonneg hmi.le
        exact_mod_cast this
      rw [hn]
      have : ω = (2 * m + 1) * Real.pi * a / L := by
        field_simp
        field_simp at hθ
        linarith
      exact this
  · rintro ⟨n, ⟨k, hk⟩, hω'⟩
    have hθ : ω * L / a = n * Real.pi := by
      rw [hω']; field_simp
    have hn : (n : ℝ) = 2 * k + 1 := by exact_mod_cast hk
    refine ⟨(k : ℤ), ?_⟩
    rw [hθ, hn]
    push_cast
    ring

/-- The decay rate `c = √(ω/(2k))` of the steady periodic temperature wave. -/
noncomputable def undergroundRate (k ω : ℝ) : ℝ := Real.sqrt (ω / (2 * k))

/-- The damped wave `A₀ e^{-cx} cos(ωt - cx)`. -/
noncomputable def undergroundU (A₀ c ω x t : ℝ) : ℝ :=
  A₀ * Real.exp (-(c * x)) * Real.cos (ω * t - c * x)

lemma hasDerivAt_exp_neg_mul (c x : ℝ) :
    HasDerivAt (fun x => Real.exp (-(c * x))) (-c * Real.exp (-(c * x))) x := by
  have := ((hasDerivAt_id x).const_mul c).neg.exp
  exact this.congr_deriv (by simp only [Pi.neg_apply, id_eq, mul_one]; ring)

lemma hasDerivAt_cos_shift (c ω t x : ℝ) :
    HasDerivAt (fun x => Real.cos (ω * t - c * x)) (c * Real.sin (ω * t - c * x)) x := by
  have := (((hasDerivAt_id x).const_mul c).const_sub (ω * t)).cos
  exact this.congr_deriv (by simp only [Pi.neg_apply, id_eq, mul_one]; ring)

lemma hasDerivAt_sin_shift (c ω t x : ℝ) :
    HasDerivAt (fun x => Real.sin (ω * t - c * x)) (-(c * Real.cos (ω * t - c * x))) x := by
  have := (((hasDerivAt_id x).const_mul c).const_sub (ω * t)).sin
  exact this.congr_deriv (by simp only [Pi.neg_apply, id_eq, mul_one]; ring)

lemma undergroundU_t (A₀ c ω x t : ℝ) :
    deriv (fun t => undergroundU A₀ c ω x t) t =
      A₀ * Real.exp (-(c * x)) * (-Real.sin (ω * t - c * x) * ω) := by
  have h := (((hasDerivAt_id t).const_mul ω).sub_const (c * x)).cos
  have h2 := h.const_mul (A₀ * Real.exp (-(c * x)))
  have h3 : HasDerivAt (fun t => undergroundU A₀ c ω x t)
      (A₀ * Real.exp (-(c * x)) * (-Real.sin (ω * t - c * x) * ω)) t :=
    h2.congr_deriv (by simp only [id_eq, mul_one])
  exact h3.deriv

lemma undergroundU_x (A₀ c ω t x : ℝ) :
    HasDerivAt (fun x => undergroundU A₀ c ω x t)
      (A₀ * c * Real.exp (-(c * x)) * (Real.sin (ω * t - c * x) - Real.cos (ω * t - c * x))) x := by
  have h := ((hasDerivAt_exp_neg_mul c x).const_mul A₀).mul (hasDerivAt_cos_shift c ω t x)
  exact h.congr_deriv (by ring)

lemma undergroundU_xx (A₀ c ω x t : ℝ) :
    deriv (fun x => deriv (fun x => undergroundU A₀ c ω x t) x) x =
      A₀ * c * (-c * Real.exp (-(c * x))) * (Real.sin (ω * t - c * x) - Real.cos (ω * t - c * x)) +
        A₀ * c * Real.exp (-(c * x)) *
          (-(c * Real.cos (ω * t - c * x)) - c * Real.sin (ω * t - c * x)) := by
  have : (fun x => deriv (fun x => undergroundU A₀ c ω x t) x) = fun x =>
      A₀ * c * Real.exp (-(c * x)) * (Real.sin (ω * t - c * x) - Real.cos (ω * t - c * x)) :=
    funext fun x => (undergroundU_x A₀ c ω t x).deriv
  rw [this]
  exact (((hasDerivAt_exp_neg_mul c x).const_mul (A₀ * c)).mul
    ((hasDerivAt_sin_shift c ω t x).sub (hasDerivAt_cos_shift c ω t x))).deriv

lemma undergroundRate_spec {k ω : ℝ} (hk : 0 < k) (hω : 0 < ω) :
    2 * k * undergroundRate k ω ^ 2 = ω := by
  unfold undergroundRate
  rw [Real.sq_sqrt (by positivity)]
  field_simp

/-- **Underground temperature oscillation** (Lebl §5.3.2): with `c = √(ω/(2k))`, the function
`u(x,t) = A₀ e^{-cx} cos(ωt - cx)` solves the heat equation `u_t = k u_xx`, has boundary value
`u(0,t) = A₀ cos(ωt)`, and its amplitude decays: `|u(x,t)| ≤ |A₀| e^{-cx}`. -/
@[kb "lebldiffyqs2026" "§5.3.2 Underground temperature oscillations, p. 291"]
theorem underground_temperature {k ω : ℝ} (A₀ : ℝ) (hk : 0 < k) (hω : 0 < ω) :
    (∀ x t, deriv (fun t => undergroundU A₀ (undergroundRate k ω) ω x t) t =
      k * deriv (fun x => deriv (fun x => undergroundU A₀ (undergroundRate k ω) ω x t) x) x) ∧
    (∀ t, undergroundU A₀ (undergroundRate k ω) ω 0 t = A₀ * Real.cos (ω * t)) ∧
    (∀ x t, |undergroundU A₀ (undergroundRate k ω) ω x t| ≤
      |A₀| * Real.exp (-(undergroundRate k ω * x))) := by
  refine ⟨fun x t => ?_, fun t => ?_, fun x t => ?_⟩
  · rw [undergroundU_t, undergroundU_xx]
    have h := undergroundRate_spec hk hω
    set c := undergroundRate k ω
    linear_combination (A₀ * Real.exp (-(c * x)) * Real.sin (ω * t - c * x)) * h
  · simp [undergroundU]
  · unfold undergroundU
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)

end UndergradKB.DifferentialEquations
