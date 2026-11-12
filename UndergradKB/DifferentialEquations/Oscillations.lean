import UndergradKB.Common.Attr
import UndergradKB.DifferentialEquations.SecondOrderLinear
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Forced oscillations, resonance, reduction of order, variation of parameters, Cauchy-Euler
(Lebl §2.1, §2.5, §2.6)

`SolvesForced m c k F x` says that `x` is twice differentiable on `ℝ` and `m x'' + c x' + k x = F(t)`.
For `m ≠ 0` it is a case of `SolvesLin2`, so the uniqueness theorem `lin2_unique` gives completeness of
explicit solution families. This file imports only `SecondOrderLinear.lean`. -/

namespace UndergradKB.DifferentialEquations

open Set Filter Topology

/-- `x` solves `m x'' + c x' + k x = F(t)` on all of `ℝ`. -/
def SolvesForced (m c k : ℝ) (F : ℝ → ℝ) (x : ℝ → ℝ) : Prop :=
  ∀ t, DifferentiableAt ℝ x t ∧ DifferentiableAt ℝ (deriv x) t ∧
    m * deriv (deriv x) t + c * deriv x t + k * x t = F t

/-- The natural frequency `ω₀ = √(k/m)`. -/
noncomputable def omega0 (m k : ℝ) : ℝ := Real.sqrt (k / m)

lemma omega0_pos {m k : ℝ} (hm : 0 < m) (hk : 0 < k) : 0 < omega0 m k :=
  Real.sqrt_pos.2 (div_pos hk hm)

lemma omega0_spec {m k : ℝ} (hm : 0 < m) (hk : 0 < k) : k = m * omega0 m k ^ 2 := by
  unfold omega0
  rw [Real.sq_sqrt (div_pos hk hm).le]
  field_simp

lemma solvesForced_iff_of_hasDerivAt {m c k : ℝ} {F x x₁ x₂ : ℝ → ℝ}
    (h1 : ∀ t, HasDerivAt x (x₁ t) t) (h2 : ∀ t, HasDerivAt x₁ (x₂ t) t) :
    SolvesForced m c k F x ↔ ∀ t, m * x₂ t + c * x₁ t + k * x t = F t := by
  have e1 : deriv x = x₁ := funext fun t => (h1 t).deriv
  have e2 : deriv x₁ = x₂ := funext fun t => (h2 t).deriv
  unfold SolvesForced
  simp only [e1, e2]
  constructor
  · intro h t
    exact (h t).2.2
  · intro h t
    exact ⟨(h1 t).differentiableAt, (h2 t).differentiableAt, h t⟩

lemma SolvesForced.toLin2 {m c k : ℝ} (hm : m ≠ 0) {F x : ℝ → ℝ} (hx : SolvesForced m c k F x) :
    SolvesLin2 (fun _ => c / m) (fun _ => k / m) (fun t => F t / m) univ x := by
  intro t _
  obtain ⟨h1, h2, h3⟩ := hx t
  refine ⟨h1, h2, ?_⟩
  have : deriv (deriv x) t + c / m * deriv x t + k / m * x t =
      (m * deriv (deriv x) t + c * deriv x t + k * x t) / m := by field_simp
  show deriv (deriv x) t + c / m * deriv x t + k / m * x t = F t / m
  rw [this, h3]

/-- Uniqueness for `m x'' + c x' + k x = F`: equal initial data at `0` force equal solutions. -/
theorem forced_unique {m c k : ℝ} (hm : m ≠ 0) {F x z : ℝ → ℝ} (hx : SolvesForced m c k F x)
    (hz : SolvesForced m c k F z) (h0 : x 0 = z 0) (h1 : deriv x 0 = deriv z 0) : x = z :=
  funext fun t => lin2_unique ordConnected_univ continuousOn_const continuousOn_const
    (SolvesForced.toLin2 hm hx) (SolvesForced.toLin2 hm hz) (mem_univ 0) h0 h1 t (mem_univ t)

lemma osc_hasDerivAt_cos (β x : ℝ) :
    HasDerivAt (fun x => Real.cos (β * x)) (-(β * Real.sin (β * x))) x := by
  have := ((hasDerivAt_id x).const_mul β).cos
  exact this.congr_deriv (by simp only [id_eq, mul_one]; ring)

lemma osc_hasDerivAt_sin (β x : ℝ) :
    HasDerivAt (fun x => Real.sin (β * x)) (β * Real.cos (β * x)) x := by
  have := ((hasDerivAt_id x).const_mul β).sin
  exact this.congr_deriv (by simp only [id_eq, mul_one]; ring)

lemma osc_hasDerivAt_trig (A B ω t : ℝ) :
    HasDerivAt (fun t => A * Real.cos (ω * t) + B * Real.sin (ω * t))
      ((B * ω) * Real.cos (ω * t) + (-(A * ω)) * Real.sin (ω * t)) t :=
  (((osc_hasDerivAt_cos ω t).const_mul A).add ((osc_hasDerivAt_sin ω t).const_mul B)).congr_deriv
    (by ring)

lemma osc_hasDerivAt_cos' (P ω t : ℝ) :
    HasDerivAt (fun t => P * Real.cos (ω * t)) (-(P * ω) * Real.sin (ω * t)) t :=
  ((osc_hasDerivAt_cos ω t).const_mul P).congr_deriv (by ring)

/-! ### Undamped forced oscillation (§2.6.1) -/

/-- **Undamped forced oscillation, particular solution** (Lebl §2.6.1): for `m, k > 0`, `ω > 0`, `ω ≠ ω₀`, the
function `F₀/(m(ω₀²-ω²)) cos ωt` solves `m x'' + k x = F₀ cos ωt`, and the general solution is this plus
`A cos ω₀t + B sin ω₀t`. -/
@[kb "lebldiffyqs2026" "Section 2.6.1, p. 111"]
theorem forced_undamped_general {m k F₀ ω : ℝ} (hm : 0 < m) (hk : 0 < k) (hω : 0 < ω)
    (hne : ω ≠ omega0 m k) {x : ℝ → ℝ} :
    SolvesForced m 0 k (fun t => F₀ * Real.cos (ω * t)) x ↔ ∃ A B : ℝ, ∀ t,
      x t = F₀ / (m * (omega0 m k ^ 2 - ω ^ 2)) * Real.cos (ω * t) +
        A * Real.cos (omega0 m k * t) + B * Real.sin (omega0 m k * t) := by
  have hk' := omega0_spec hm hk
  have hw0 := omega0_pos hm hk
  set w := omega0 m k with hwdef
  have hden : m * (w ^ 2 - ω ^ 2) ≠ 0 := by
    refine mul_ne_zero hm.ne' (fun h => hne ?_)
    have : (w - ω) * (w + ω) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  obtain ⟨P, hPdef⟩ : ∃ P, P = F₀ / (m * (w ^ 2 - ω ^ 2)) := ⟨_, rfl⟩
  have hP : P * (m * (w ^ 2 - ω ^ 2)) = F₀ := by rw [hPdef]; exact div_mul_cancel₀ _ hden
  have d1 : ∀ A B t, HasDerivAt (fun t => P * Real.cos (ω * t) + (A * Real.cos (w * t) + B * Real.sin (w * t)))
      (-(P * ω) * Real.sin (ω * t) + ((B * w) * Real.cos (w * t) + (-(A * w)) * Real.sin (w * t))) t :=
    fun A B t => (osc_hasDerivAt_cos' P ω t).add (osc_hasDerivAt_trig A B w t)
  have d2 : ∀ A B t, HasDerivAt (fun t => -(P * ω) * Real.sin (ω * t) +
      ((B * w) * Real.cos (w * t) + (-(A * w)) * Real.sin (w * t)))
      (-(P * ω) * (ω * Real.cos (ω * t)) +
        (((-(A * w)) * w) * Real.cos (w * t) + (-((B * w) * w)) * Real.sin (w * t))) t :=
    fun A B t => (((osc_hasDerivAt_sin ω t).const_mul (-(P * ω))).add
      (osc_hasDerivAt_trig (B * w) (-(A * w)) w t))
  have fam : ∀ A B : ℝ, SolvesForced m 0 k (fun t => F₀ * Real.cos (ω * t))
      (fun t => P * Real.cos (ω * t) + (A * Real.cos (w * t) + B * Real.sin (w * t))) := by
    intro A B
    refine (solvesForced_iff_of_hasDerivAt (d1 A B) (d2 A B)).2 (fun t => ?_)
    linear_combination (Real.cos (ω * t)) * hP + (P * Real.cos (ω * t) + (A * Real.cos (w * t) +
      B * Real.sin (w * t))) * hk'
  constructor
  · intro hx
    refine ⟨x 0 - P, deriv x 0 / w, ?_⟩
    have := forced_unique hm.ne' hx (fam (x 0 - P) (deriv x 0 / w)) (by simp)
      (by rw [((d1 (x 0 - P) (deriv x 0 / w) 0)).deriv]; simp; field_simp)
    intro t
    rw [congrFun this t, hPdef]
    ring
  · rintro ⟨A, B, h⟩
    have : x = fun t => P * Real.cos (ω * t) + (A * Real.cos (w * t) + B * Real.sin (w * t)) :=
      funext fun t => by rw [h t, hPdef]; ring
    rw [this]
    exact fam A B

/-! ### Pure resonance (§2.6.1) -/

/-- **Pure resonance, particular solution** (Lebl §2.6.1, Example 2.6.1): for `m, k > 0`, the function
`F₀/(2 m ω₀) · t sin ω₀t` solves `m x'' + k x = F₀ cos ω₀t`. -/
@[kb "lebldiffyqs2026" "Example 2.6.1, p. 112"]
theorem resonance_particular {m k F₀ : ℝ} (hm : 0 < m) (hk : 0 < k) :
    SolvesForced m 0 k (fun t => F₀ * Real.cos (omega0 m k * t))
      (fun t => F₀ / (2 * m * omega0 m k) * t * Real.sin (omega0 m k * t)) := by
  have hk' := omega0_spec hm hk
  have hw0 := omega0_pos hm hk
  set w := omega0 m k with hwdef
  obtain ⟨Q, hQdef⟩ : ∃ Q, Q = F₀ / (2 * m * w) := ⟨_, rfl⟩
  have hQ : Q * (2 * m * w) = F₀ := by rw [hQdef]; exact div_mul_cancel₀ _ (by positivity)
  have d1 : ∀ t, HasDerivAt (fun t => Q * t * Real.sin (w * t))
      (Q * Real.sin (w * t) + Q * w * t * Real.cos (w * t)) t := fun t =>
    ((((hasDerivAt_id' t).const_mul Q).mul (osc_hasDerivAt_sin w t))).congr_deriv (by ring)
  have d2 : ∀ t, HasDerivAt (fun t => Q * Real.sin (w * t) + Q * w * t * Real.cos (w * t))
      (2 * Q * w * Real.cos (w * t) - Q * w ^ 2 * t * Real.sin (w * t)) t := fun t =>
    (((osc_hasDerivAt_sin w t).const_mul Q).add ((((hasDerivAt_id' t).const_mul (Q * w)).mul
      (osc_hasDerivAt_cos w t)))).congr_deriv (by ring)
  rw [← hQdef]
  refine (solvesForced_iff_of_hasDerivAt d1 d2).2 (fun t => ?_)
  linear_combination (Real.cos (w * t)) * hQ + (Q * t * Real.sin (w * t)) * hk'

/-- **Pure resonance is unbounded** (Lebl §2.6.1): for `F₀ ≠ 0` the resonant particular solution
`F₀/(2 m ω₀) · t sin ω₀t` is not bounded on `[0, ∞)`. -/
@[kb "lebldiffyqs2026" "Example 2.6.1, p. 112"]
theorem resonance_unbounded {m k F₀ : ℝ} (hm : 0 < m) (hk : 0 < k) (hF : F₀ ≠ 0) :
    ¬ ∃ M : ℝ, ∀ t, 0 ≤ t →
      |F₀ / (2 * m * omega0 m k) * t * Real.sin (omega0 m k * t)| ≤ M := by
  have hw0 := omega0_pos hm hk
  set w := omega0 m k with hwdef
  rintro ⟨M, hM⟩
  have hQ : 0 < |F₀ / (2 * m * w)| := abs_pos.2 (div_ne_zero hF (by positivity))
  set Q := |F₀ / (2 * m * w)| with hQdef
  obtain ⟨N, hN⟩ := exists_nat_ge ((|M| / Q + 1) * w)
  set t := (Real.pi / 2 + N * (2 * Real.pi)) / w with htdef
  have hpi := Real.pi_pos
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have ht0 : 0 ≤ t := by positivity
  have hsin : Real.sin (w * t) = 1 := by
    have : w * t = Real.pi / 2 + N * (2 * Real.pi) := by rw [htdef]; field_simp
    rw [this, Real.sin_add_nat_mul_two_pi, Real.sin_pi_div_two]
  have hbig : |M| / Q + 1 ≤ t := by
    rw [htdef, le_div_iff₀ hw0]
    nlinarith [mul_nonneg hN0 (by linarith [Real.two_le_pi] : (0 : ℝ) ≤ 2 * Real.pi - 1)]
  have h := hM t ht0
  rw [hsin, mul_one, abs_mul, abs_of_nonneg ht0] at h
  have h' : Q * t ≤ M := h
  have h2 : |M| + Q ≤ Q * t := by
    have := mul_le_mul_of_nonneg_left hbig hQ.le
    have e : Q * (|M| / Q + 1) = |M| + Q := by field_simp
    linarith
  linarith [le_abs_self M]

/-! ### Damped forced oscillation and practical resonance (§2.6.2) -/

/-- The denominator `(2ωp)² + (ω₀² - ω²)²` of the steady-state amplitude (Lebl §2.6.2). -/
def dampedDelta (ω₀ p ω : ℝ) : ℝ := (2 * ω * p) ^ 2 + (ω₀ ^ 2 - ω ^ 2) ^ 2

/-- The amplitude `C(ω) = F₀ / (m √((2ωp)² + (ω₀² - ω²)²))` of the steady periodic solution. -/
noncomputable def forcedAmp (m F₀ ω₀ p ω : ℝ) : ℝ := F₀ / (m * Real.sqrt (dampedDelta ω₀ p ω))

lemma dampedDelta_pos {ω₀ p ω : ℝ} (hp : 0 < p) (hω : 0 < ω) : 0 < dampedDelta ω₀ p ω := by
  unfold dampedDelta
  positivity

/-- **Steady periodic solution** (Lebl §2.6.2): for `m, c, k, ω > 0`, with `p = c/(2m)` and `ω₀ = √(k/m)`,
`x_sp = (F₀/m)((ω₀²-ω²) cos ωt + 2ωp sin ωt)/((2ωp)² + (ω₀²-ω²)²)` solves
`m x'' + c x' + k x = F₀ cos ωt`. -/
@[kb "lebldiffyqs2026" "Section 2.6.2, p. 114"]
theorem steady_state_solves {m c k F₀ ω : ℝ} (hm : 0 < m) (hc : 0 < c) (hk : 0 < k) (hω : 0 < ω) :
    SolvesForced m c k (fun t => F₀ * Real.cos (ω * t))
      (fun t => F₀ / m * (((omega0 m k ^ 2 - ω ^ 2) * Real.cos (ω * t) +
        2 * ω * (c / (2 * m)) * Real.sin (ω * t)) /
          dampedDelta (omega0 m k) (c / (2 * m)) ω)) := by
  have hk' := omega0_spec hm hk
  set w := omega0 m k with hwdef
  have hΔ := dampedDelta_pos (ω₀ := w) (div_pos hc (by positivity : (0 : ℝ) < 2 * m)) hω
  set p := c / (2 * m) with hpdef
  set Δ := dampedDelta w p ω with hΔdef
  have hΔe : Δ = (2 * ω * p) ^ 2 + (w ^ 2 - ω ^ 2) ^ 2 := rfl
  have hcv : c * ω = m * (2 * ω * p) := by rw [hpdef]; field_simp
  set g := F₀ / m with hgdef
  have hg : m * g = F₀ := by rw [hgdef]; field_simp
  set u := w ^ 2 - ω ^ 2 with hu
  set v := 2 * ω * p with hv
  set A := g * (u / Δ) with hA
  set B := g * (v / Δ) with hB
  have e1 : u * A + v * B = g := by
    apply mul_right_cancel₀ hΔ.ne'
    have a1 : A * Δ = g * u := by rw [hA]; field_simp
    have a2 : B * Δ = g * v := by rw [hB]; field_simp
    linear_combination u * a1 + v * a2 - g * hΔe
  have e2 : u * B - v * A = 0 := by
    apply mul_right_cancel₀ hΔ.ne'
    have a1 : A * Δ = g * u := by rw [hA]; field_simp
    have a2 : B * Δ = g * v := by rw [hB]; field_simp
    linear_combination u * a2 - v * a1
  have hform : (fun t => g * ((u * Real.cos (ω * t) + v * Real.sin (ω * t)) / Δ)) =
      fun t => A * Real.cos (ω * t) + B * Real.sin (ω * t) := by
    funext t
    rw [hA, hB]
    ring
  rw [hform]
  have d1 : ∀ t, HasDerivAt (fun t => A * Real.cos (ω * t) + B * Real.sin (ω * t))
      ((B * ω) * Real.cos (ω * t) + (-(A * ω)) * Real.sin (ω * t)) t :=
    fun t => osc_hasDerivAt_trig A B ω t
  have d2 : ∀ t, HasDerivAt (fun t => (B * ω) * Real.cos (ω * t) + (-(A * ω)) * Real.sin (ω * t))
      (((-(A * ω)) * ω) * Real.cos (ω * t) + (-((B * ω) * ω)) * Real.sin (ω * t)) t :=
    fun t => osc_hasDerivAt_trig (B * ω) (-(A * ω)) ω t
  refine (solvesForced_iff_of_hasDerivAt d1 d2).2 (fun t => ?_)
  linear_combination (A * Real.cos (ω * t) + B * Real.sin (ω * t)) * hk' +
    (B * Real.cos (ω * t) - A * Real.sin (ω * t)) * hcv +
    m * Real.cos (ω * t) * e1 + m * Real.sin (ω * t) * e2 + Real.cos (ω * t) * hg

/-- **Amplitude of the steady periodic solution** (Lebl §2.6.2): the coefficients `A, B` of
`x_sp = A cos ωt + B sin ωt` satisfy `A² + B² = C(ω)²` with `C(ω) = F₀ / (m √((2ωp)² + (ω₀²-ω²)²))`. -/
@[kb "lebldiffyqs2026" "Section 2.6.2, p. 114"]
theorem steady_state_amplitude {m F₀ ω₀ p ω : ℝ} (hm : 0 < m) (hp : 0 < p) (hω : 0 < ω) :
    (F₀ / m * ((ω₀ ^ 2 - ω ^ 2) / dampedDelta ω₀ p ω)) ^ 2 +
        (F₀ / m * (2 * ω * p / dampedDelta ω₀ p ω)) ^ 2 = forcedAmp m F₀ ω₀ p ω ^ 2 := by
  have hΔ := dampedDelta_pos (ω₀ := ω₀) hp hω
  unfold forcedAmp
  have hs : (m * Real.sqrt (dampedDelta ω₀ p ω)) ^ 2 = m ^ 2 * dampedDelta ω₀ p ω := by
    rw [mul_pow, Real.sq_sqrt hΔ.le]
  rw [div_pow F₀ (m * Real.sqrt (dampedDelta ω₀ p ω)) 2, hs]
  have :dampedDelta ω₀ p ω = (2 * ω * p) ^ 2 + (ω₀ ^ 2 - ω ^ 2) ^ 2 := rfl
  field_simp
  rw [this]
  ring

/-- **Practical resonance, with a maximum** (Lebl §2.6.2): for `m, F₀, p > 0` and `ω₀² - 2p² > 0`, the
amplitude `C(ω)` on `ω > 0` is maximal at `ω = √(ω₀² - 2p²)`. -/
@[kb "lebldiffyqs2026" "Section 2.6.2, p. 115"]
theorem practical_resonance_max {m F₀ ω₀ p : ℝ} (hm : 0 < m) (hF : 0 < F₀) (hp : 0 < p)
    (h : 0 < ω₀ ^ 2 - 2 * p ^ 2) :
    Real.sqrt (ω₀ ^ 2 - 2 * p ^ 2) ∈ Ioi (0 : ℝ) ∧
      IsMaxOn (forcedAmp m F₀ ω₀ p) (Ioi (0 : ℝ)) (Real.sqrt (ω₀ ^ 2 - 2 * p ^ 2)) := by
  have hs : Real.sqrt (ω₀ ^ 2 - 2 * p ^ 2) ^ 2 = ω₀ ^ 2 - 2 * p ^ 2 := Real.sq_sqrt h.le
  have hs0 : 0 < Real.sqrt (ω₀ ^ 2 - 2 * p ^ 2) := Real.sqrt_pos.2 h
  refine ⟨hs0, fun ω hω => ?_⟩
  have hω : 0 < ω := hω
  have hΔ1 := dampedDelta_pos (ω₀ := ω₀) hp hs0
  have hle : dampedDelta ω₀ p (Real.sqrt (ω₀ ^ 2 - 2 * p ^ 2)) ≤ dampedDelta ω₀ p ω := by
    unfold dampedDelta
    rw [mul_pow (2 * _), mul_pow (2 * _), hs]
    nlinarith [sq_nonneg (ω ^ 2 - (ω₀ ^ 2 - 2 * p ^ 2))]
  show forcedAmp m F₀ ω₀ p ω ≤ forcedAmp m F₀ ω₀ p (Real.sqrt (ω₀ ^ 2 - 2 * p ^ 2))
  unfold forcedAmp
  have h1 : 0 < m * Real.sqrt (dampedDelta ω₀ p (Real.sqrt (ω₀ ^ 2 - 2 * p ^ 2))) :=
    mul_pos hm (Real.sqrt_pos.2 hΔ1)
  exact div_le_div_of_nonneg_left hF.le h1
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hle) hm.le)

/-- **Practical resonance, no maximum** (Lebl §2.6.2): for `m, F₀, p > 0` and `ω₀² ≤ 2p²`, the amplitude
`C(ω)` is strictly decreasing on `ω > 0`, so it has no maximum there. -/
@[kb "lebldiffyqs2026" "Section 2.6.2, p. 115"]
theorem practical_resonance_decreasing {m F₀ ω₀ p : ℝ} (hm : 0 < m) (hF : 0 < F₀) (hp : 0 < p)
    (h : ω₀ ^ 2 ≤ 2 * p ^ 2) : StrictAntiOn (forcedAmp m F₀ ω₀ p) (Ioi (0 : ℝ)) := by
  intro a ha b hb hab
  have ha : 0 < a := ha
  have hΔa := dampedDelta_pos (ω₀ := ω₀) hp ha
  have hlt : dampedDelta ω₀ p a < dampedDelta ω₀ p b := by
    unfold dampedDelta
    nlinarith [mul_pos (sub_pos.2 (pow_lt_pow_left₀ hab ha.le two_ne_zero)) (mul_pos hp hp),
      mul_pos (sub_pos.2 (pow_lt_pow_left₀ hab ha.le two_ne_zero))
        (add_pos_of_pos_of_nonneg (pow_pos ha 2) (sub_nonneg.2 h)),
      mul_pos (sub_pos.2 (pow_lt_pow_left₀ hab ha.le two_ne_zero)) (pow_pos (lt_trans ha hab) 2)]
  show forcedAmp m F₀ ω₀ p b < forcedAmp m F₀ ω₀ p a
  unfold forcedAmp
  exact div_lt_div_of_pos_left hF (mul_pos hm (Real.sqrt_pos.2 hΔa))
    (mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt hΔa.le hlt) hm)

/-! ### Reduction of order, variation of parameters, Cauchy-Euler -/

/-- On an open set, explicit first and second derivatives of `y` turn the relation into `SolvesLin2`. -/
lemma solvesLin2_of_hasDerivAt {p q f : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I) {y y₁ y₂ : ℝ → ℝ}
    (h1 : ∀ t ∈ I, HasDerivAt y (y₁ t) t) (h2 : ∀ t ∈ I, HasDerivAt y₁ (y₂ t) t)
    (h : ∀ t ∈ I, y₂ t + p t * y₁ t + q t * y t = f t) : SolvesLin2 p q f I y := by
  intro t ht
  have e : deriv y =ᶠ[nhds t] y₁ :=
    Filter.eventually_of_mem (hI.mem_nhds ht) fun u hu => (h1 u hu).deriv
  have hd : HasDerivAt (deriv y) (y₂ t) t := (h2 t ht).congr_of_eventuallyEq e
  refine ⟨(h1 t ht).differentiableAt, hd.differentiableAt, ?_⟩
  rw [hd.deriv, e.self_of_nhds]
  exact h t ht

/-- **Reduction of order** (Lebl §2.1): let `u` solve `y'' + p y' + q y = 0` on an open set `I` and be nonzero
there, let `P' = p`, and let `v' = e^{-P}/u²` on `I`. Then `v u` is again a solution on `I`. -/
@[kb "lebldiffyqs2026" "Section 2.1 (reduction of order), p. 81"]
theorem reduction_of_order {p q : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I) {u P v : ℝ → ℝ}
    (hu : SolvesLin2 p q 0 I u) (hne : ∀ t ∈ I, u t ≠ 0) (hP : ∀ t ∈ I, HasDerivAt P (p t) t)
    (hv : ∀ t ∈ I, HasDerivAt v (Real.exp (-P t) / (u t) ^ 2) t) :
    SolvesLin2 p q 0 I (fun t => v t * u t) := by
  refine solvesLin2_of_hasDerivAt hI
    (y₁ := fun t => Real.exp (-P t) / u t + v t * deriv u t)
    (y₂ := fun t => (Real.exp (-P t) * (-(p t)) * u t - Real.exp (-P t) * deriv u t) / (u t) ^ 2 +
      (Real.exp (-P t) / (u t) ^ 2 * deriv u t + v t * deriv (deriv u) t)) ?_ ?_ ?_
  · intro t ht
    have := hne t ht
    exact ((hv t ht).mul (hu t ht).1.hasDerivAt).congr_deriv (by field_simp)
  · intro t ht
    have hE : HasDerivAt (fun t => Real.exp (-P t)) (Real.exp (-P t) * (-(p t))) t :=
      (hP t ht).neg.exp
    exact (hE.div (hu t ht).1.hasDerivAt (hne t ht)).add
      ((hv t ht).mul (hu t ht).2.1.hasDerivAt)
  · intro t ht
    have h3 := (hu t ht).2.2
    simp only [Pi.zero_apply] at h3 ⊢
    have := hne t ht
    have key : (Real.exp (-P t) * (-(p t)) * u t - Real.exp (-P t) * deriv u t) / (u t) ^ 2 +
        (Real.exp (-P t) / (u t) ^ 2 * deriv u t + v t * deriv (deriv u) t) +
        p t * (Real.exp (-P t) / u t + v t * deriv u t) + q t * (v t * u t) =
        v t * (deriv (deriv u) t + p t * deriv u t + q t * u t) := by
      field_simp
      ring
    rw [key, h3, mul_zero]

/-- **Variation of parameters** (Lebl §2.5.3): let `y₁, y₂` solve the homogeneous equation on an open set `I` with
nonvanishing Wronskian `W = y₁ y₂' - y₁' y₂`, and let `u₁' = -y₂ f / W`, `u₂' = y₁ f / W` on `I`. Then
`u₁ y₁ + u₂ y₂` solves `y'' + p y' + q y = f` on `I`. -/
@[kb "lebldiffyqs2026" "Section 2.5.3, p. 108"]
theorem variation_of_parameters {p q f : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I) {u₁ u₂ y₁ y₂ : ℝ → ℝ}
    (h1 : SolvesLin2 p q 0 I y₁) (h2 : SolvesLin2 p q 0 I y₂)
    (hW : ∀ t ∈ I, y₁ t * deriv y₂ t - deriv y₁ t * y₂ t ≠ 0)
    (hu1 : ∀ t ∈ I, HasDerivAt u₁
      (-(y₂ t) * f t / (y₁ t * deriv y₂ t - deriv y₁ t * y₂ t)) t)
    (hu2 : ∀ t ∈ I, HasDerivAt u₂
      (y₁ t * f t / (y₁ t * deriv y₂ t - deriv y₁ t * y₂ t)) t) :
    SolvesLin2 p q f I (fun t => u₁ t * y₁ t + u₂ t * y₂ t) := by
  refine solvesLin2_of_hasDerivAt hI
    (y₁ := fun t => u₁ t * deriv y₁ t + u₂ t * deriv y₂ t)
    (y₂ := fun t => (-(y₂ t) * f t / (y₁ t * deriv y₂ t - deriv y₁ t * y₂ t)) * deriv y₁ t +
      u₁ t * deriv (deriv y₁) t +
      ((y₁ t * f t / (y₁ t * deriv y₂ t - deriv y₁ t * y₂ t)) * deriv y₂ t +
        u₂ t * deriv (deriv y₂) t)) ?_ ?_ ?_
  · intro t ht
    exact (((hu1 t ht).mul (h1 t ht).1.hasDerivAt).add
      ((hu2 t ht).mul (h2 t ht).1.hasDerivAt)).congr_deriv (by ring)
  · intro t ht
    exact (((hu1 t ht).mul (h1 t ht).2.1.hasDerivAt).add
      ((hu2 t ht).mul (h2 t ht).2.1.hasDerivAt)).congr_deriv (by ring)
  · intro t ht
    have e1 := (h1 t ht).2.2
    have e2 := (h2 t ht).2.2
    simp only [Pi.zero_apply] at e1 e2
    have key : f t * (y₁ t * deriv y₂ t - deriv y₁ t * y₂ t) /
        (y₁ t * deriv y₂ t - deriv y₁ t * y₂ t) = f t := mul_div_cancel_right₀ _ (hW t ht)
    linear_combination key + u₁ t * e1 + u₂ t * e2

/-- `y` solves the Cauchy-Euler equation `a x² y'' + b x y' + c y = 0` on `x > 0` (Lebl §2.1 exercises). -/
def SolvesCauchyEuler (a b c : ℝ) (y : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 0 < x → DifferentiableAt ℝ y x ∧ DifferentiableAt ℝ (deriv y) x ∧
    a * x ^ 2 * deriv (deriv y) x + b * x * deriv y x + c * y x = 0

/-- **Cauchy-Euler ansatz** (Lebl §2.1, exercises on `a x² y'' + b x y' + c y = 0`): on `x > 0` the power function
`x^r` solves the equation exactly when `a r (r-1) + b r + c = 0`. -/
@[kb "lebldiffyqs2026" "Section 2.1 (Cauchy-Euler), p. 82"]
theorem cauchy_euler_rpow_iff (a b c r : ℝ) :
    SolvesCauchyEuler a b c (fun x => x ^ r) ↔ a * r * (r - 1) + b * r + c = 0 := by
  have d1 : ∀ x : ℝ, 0 < x → HasDerivAt (fun x : ℝ => x ^ r) (r * x ^ (r - 1)) x :=
    fun x hx => Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  have key : ∀ x : ℝ, 0 < x → ∃ hd : HasDerivAt (deriv fun x : ℝ => x ^ r)
      (r * ((r - 1) * x ^ (r - 1 - 1))) x, deriv (fun x : ℝ => x ^ r) x = r * x ^ (r - 1) := by
    intro x hx
    have e : (deriv fun x : ℝ => x ^ r) =ᶠ[nhds x] fun u => r * u ^ (r - 1) :=
      Filter.eventually_of_mem (Ioi_mem_nhds hx) fun u hu => (d1 u hu).deriv
    have d2 : HasDerivAt (fun u : ℝ => r * u ^ (r - 1)) (r * ((r - 1) * x ^ (r - 1 - 1))) x :=
      (Real.hasDerivAt_rpow_const (Or.inl hx.ne')).const_mul r
    exact ⟨d2.congr_of_eventuallyEq e, e.self_of_nhds⟩
  have ident : ∀ x : ℝ, 0 < x →
      a * x ^ 2 * deriv (deriv fun x : ℝ => x ^ r) x + b * x * deriv (fun x : ℝ => x ^ r) x +
        c * x ^ r = (a * r * (r - 1) + b * r + c) * x ^ r := by
    intro x hx
    obtain ⟨hd, hd1⟩ := key x hx
    rw [hd.deriv, hd1, Real.rpow_sub_one hx.ne' (r - 1), Real.rpow_sub_one hx.ne' r]
    have := hx.ne'
    field_simp
  constructor
  · intro h
    have h3 := (h 1 one_pos).2.2
    rw [ident 1 one_pos, Real.one_rpow, mul_one] at h3
    exact h3
  · intro h x hx
    obtain ⟨hd, -⟩ := key x hx
    refine ⟨(d1 x hx).differentiableAt, hd.differentiableAt, ?_⟩
    rw [ident x hx, h, zero_mul]

end UndergradKB.DifferentialEquations
