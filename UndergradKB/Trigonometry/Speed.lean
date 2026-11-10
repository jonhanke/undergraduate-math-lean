import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Topology.EMetricSpace.BoundedVariation
import UndergradKB.Common.Attr
import UndergradKB.Trigonometry.ArcLength

/-! # Speed, gears and phase (Corral §4.4, §5.2; OpenStax §7.1)

Average linear and angular speed of a point moving uniformly on a circle (`τ ↦ c + r e^{iωτ}`, the distance
travelled being the total variation of the path), the relation `ν = rω`, revolutions per minute, two
meshing gears, and the phase shift of sinusoids.
-/

namespace UndergradKB.Trigonometry

open Real Set

/-! ### Linear and angular speed (TR-106, TR-107) -/

/-- Average linear speed: distance travelled `s` divided by the elapsed time `t`. -/
noncomputable def avgLinearSpeed (s t : ℝ) : ℝ := s / t

/-- Average angular speed: angle swept `θ` divided by the elapsed time `t`. -/
noncomputable def avgAngularSpeed (θ t : ℝ) : ℝ := θ / t

/-- **Average linear speed**: a point moving on the circle of radius `r ≥ 0` with angle `ωτ` at time `τ`
(`ω ≥ 0`) travels, during a time `t > 0`, a distance whose average speed is `ω r`. (TR-106) -/
@[kb "corraltrig" "Box §4.4, p. 107"]
theorem avgLinearSpeed_uniform_circular (c : ℂ) {r ω t : ℝ} (hr : 0 ≤ r) (hω : 0 ≤ ω) (ht : 0 < t) :
    avgLinearSpeed
      (eVariationOn (fun τ : ℝ => c + r * Complex.exp ((ω * τ : ℝ) * Complex.I)) (Icc 0 t)).toReal t =
      ω * r := by
  rw [avgLinearSpeed, linear_speed c hr hω ht.le, ENNReal.toReal_ofReal (by positivity)]
  field_simp

/-- **Average angular speed and `ν = rω`**: the same motion sweeps the angle `ω t` in the time `t`, so its
average angular speed is `ω`, and the average linear speed is the radius times the average angular speed.
(TR-107) -/
@[kb "openstaxalgtrig2e" "§7.1, p. 692"]
theorem avgAngularSpeed_uniform_circular (c : ℂ) {r ω t : ℝ} (hr : 0 ≤ r) (hω : 0 ≤ ω) (ht : 0 < t) :
    avgAngularSpeed (ω * t) t = ω ∧
      avgLinearSpeed
        (eVariationOn (fun τ : ℝ => c + r * Complex.exp ((ω * τ : ℝ) * Complex.I)) (Icc 0 t)).toReal t =
        r * avgAngularSpeed (ω * t) t := by
  have h : avgAngularSpeed (ω * t) t = ω := by
    rw [avgAngularSpeed]; field_simp
  refine ⟨h, ?_⟩
  rw [avgLinearSpeed_uniform_circular c hr hω ht, h, mul_comm]

/-! ### Revolutions per minute (TR-109) -/

/-- `N` revolutions per minute, in radians per second. -/
noncomputable def rpmToRadPerSec (N : ℝ) : ℝ := 2 * π * N / 60

/-- An angular speed `w` in radians per second, in revolutions per minute. -/
noncomputable def radPerSecToRpm (w : ℝ) : ℝ := 60 * w / (2 * π)

/-- **Revolutions per minute**: the two conversions are inverse to each other, and one revolution per
minute is `2π/60` radians per second. (TR-109) -/
@[kb "corraltrig" "Box §4.4, p. 108"]
theorem rpm_conversions :
    (∀ N, radPerSecToRpm (rpmToRadPerSec N) = N) ∧ (∀ w, rpmToRadPerSec (radPerSecToRpm w) = w) ∧
      rpmToRadPerSec 1 = 2 * π / 60 := by
  have := pi_pos.ne'
  refine ⟨fun N => ?_, fun w => ?_, by unfold rpmToRadPerSec; ring⟩ <;>
    simp only [rpmToRadPerSec, radPerSecToRpm] <;> field_simp

/-! ### Meshing gears (TR-110) -/

/-- **Gears**: two wheels of radii `r₁, r₂ > 0` turning with angular speeds `ω₁, ω₂ ≥ 0` have contact points
that travel equal distances in every time `t ≥ 0` (no slipping) iff `ω₁ r₁ = ω₂ r₂`. (TR-110) -/
@[kb "corraltrig" "Box §4.4, p. 109 (4.11)"]
theorem gears_equal_distance_iff (c₁ c₂ : ℂ) {r₁ r₂ ω₁ ω₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hω₁ : 0 ≤ ω₁) (hω₂ : 0 ≤ ω₂) :
    (∀ t : ℝ, 0 ≤ t →
      eVariationOn (fun τ : ℝ => c₁ + r₁ * Complex.exp ((ω₁ * τ : ℝ) * Complex.I)) (Icc 0 t) =
      eVariationOn (fun τ : ℝ => c₂ + r₂ * Complex.exp ((ω₂ * τ : ℝ) * Complex.I)) (Icc 0 t)) ↔
    ω₁ * r₁ = ω₂ * r₂ := by
  constructor
  · intro h
    have := h 1 zero_le_one
    rw [linear_speed c₁ hr₁.le hω₁ zero_le_one, linear_speed c₂ hr₂.le hω₂ zero_le_one,
      ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)] at this
    linarith
  · intro h t ht
    rw [linear_speed c₁ hr₁.le hω₁ ht, linear_speed c₂ hr₂.le hω₂ ht, h]

/-! ### Phase (TR-125) -/

/-- Two functions are *in phase* when one is a positive multiple of the other. -/
def InPhase (f g : ℝ → ℝ) : Prop := ∃ c > 0, ∀ x, g x = c * f x

/-- `f` *leads* `g` by `d` when `f` reaches each value `d` earlier than `g`: `f x = g (x + d)`. -/
def Leads (f g : ℝ → ℝ) (d : ℝ) : Prop := ∀ x, f x = g (x + d)

/-- **In phase**: the sinusoids `A sin(ω(x - c₁))` and `A' sin(ω(x - c₂))` (`A, A', ω > 0`) are in phase iff
their phase shifts agree modulo the period `2π/ω`. (TR-125) -/
@[kb "corraltrig" "Box §5.2, p. 118"]
theorem inPhase_sin_iff {A A' ω c₁ c₂ : ℝ} (hA : 0 < A) (hA' : 0 < A') (hω : 0 < ω) :
    InPhase (fun x => A * sin (ω * (x - c₁))) (fun x => A' * sin (ω * (x - c₂))) ↔
      ∃ k : ℤ, c₁ - c₂ = k * (2 * π / ω) := by
  have hω' := hω.ne'
  constructor
  · rintro ⟨c, hc, h⟩
    obtain ⟨δ, hδ⟩ : ∃ δ, δ = ω * (c₁ - c₂) := ⟨_, rfl⟩
    have h0 := h c₁
    have h1 := h (c₁ + π / (2 * ω))
    beta_reduce at h0 h1
    have e1 : ω * (c₁ + π / (2 * ω) - c₂) = δ + π / 2 := by rw [hδ]; field_simp; ring
    have e2 : ω * (c₁ + π / (2 * ω) - c₁) = π / 2 := by field_simp; ring
    simp only [sub_self, mul_zero, sin_zero] at h0
    rw [← hδ] at h0
    rw [e1, e2, sin_pi_div_two, sin_add_pi_div_two] at h1
    have hs : sin δ = 0 := by
      have := mul_eq_zero.1 h0
      exact this.resolve_left hA'.ne'
    have hcos : cos δ = 1 := by
      have hpos : 0 < cos δ := by
        have h' : A' * cos δ = c * A := by linarith
        refine lt_of_not_ge fun hn => ?_
        nlinarith [mul_pos hc hA, mul_nonneg hA'.le (neg_nonneg.2 hn)]
      nlinarith [sin_sq_add_cos_sq δ]
    obtain ⟨k, hk⟩ := (cos_eq_one_iff δ).1 hcos
    refine ⟨k, ?_⟩
    rw [hδ] at hk
    field_simp
    linarith
  · rintro ⟨k, hk⟩
    refine ⟨A' / A, by positivity, fun x => ?_⟩
    have : ω * (x - c₂) = ω * (x - c₁) + k * (2 * π) := by
      have : c₂ = c₁ - k * (2 * π / ω) := by linarith
      rw [this]; field_simp; ring
    beta_reduce
    rw [this, sin_add_int_mul_two_pi]
    field_simp

/-- **Phase shift**: `sin(ω(x - c₁))` leads `sin(ω(x - c₂))` by `c₂ - c₁`. (TR-125) -/
theorem leads_sin_shift (ω c₁ c₂ : ℝ) :
    Leads (fun x => sin (ω * (x - c₁))) (fun x => sin (ω * (x - c₂))) (c₂ - c₁) := fun x => by
  beta_reduce
  congr 1; ring

end UndergradKB.Trigonometry
