import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import UndergradKB.Common.Attr
import UndergradKB.DifferentialEquations.Nonlinear

/-! # The pendulum released from rest

Lebl, *Notes on Diffy Qs*, §8.3.1 (period of the pendulum).  The period formula
`T = 4 ∫_0^{θ₀} dθ / √((2g/L)(cos θ - cos θ₀))` comes from the energy identity
`θ'² = (2g/L)(cos θ - cos θ₀)` for the pendulum released from rest at `θ₀`; we prove that identity, the resulting
bound `cos θ(t) ≥ cos θ₀` (the pendulum never swings past `±θ₀`), and the period `2π √(L/g)` of the linearized
pendulum.  The evaluation of the improper period integral is not proved here. -/

namespace UndergradKB.DifferentialEquations

open Real

/-- **Energy identity of the released pendulum (DE-228, the step behind the period formula).** If
`θ' = ω`, `ω' = -(g/L) sin θ` with `θ(0) = θ₀`, `ω(0) = 0`, then `ω(t)² = (2g/L)(cos θ(t) - cos θ₀)` for all `t`. -/
@[kb "lebldiffyqs2026" "§8.3.1 Period of the pendulum, p. 366"]
theorem pendulum_released_energy {g L θ₀ : ℝ} {θ ω : ℝ → ℝ} (hθ : ∀ t, HasDerivAt θ (ω t) t)
    (hω : ∀ t, HasDerivAt ω (-(g / L * Real.sin (θ t))) t) (h0 : θ 0 = θ₀) (hω0 : ω 0 = 0) (t : ℝ) :
    ω t ^ 2 = 2 * g / L * (Real.cos (θ t) - Real.cos θ₀) := by
  have := pendulum_energy_const hθ hω t 0
  rw [h0, hω0] at this
  have e : 2 * g / L * (Real.cos (θ t) - Real.cos θ₀)
      = 2 * (g / L * Real.cos (θ t)) - 2 * (g / L * Real.cos θ₀) := by ring
  rw [e]
  norm_num at this
  linarith

/-- **The released pendulum never swings past its starting angle (DE-228).** With `g/L > 0`,
`cos θ(t) ≥ cos θ₀` for all `t`; if moreover `θ(t) ∈ [-π, π]` and `0 ≤ θ₀ ≤ π`, then `|θ(t)| ≤ θ₀`. -/
@[kb "lebldiffyqs2026" "§8.3.1 Period of the pendulum, p. 366"]
theorem pendulum_released_bound {g L θ₀ : ℝ} (hgL : 0 < g / L) {θ ω : ℝ → ℝ} (hθ : ∀ t, HasDerivAt θ (ω t) t)
    (hω : ∀ t, HasDerivAt ω (-(g / L * Real.sin (θ t))) t) (h0 : θ 0 = θ₀) (hω0 : ω 0 = 0) (t : ℝ) :
    Real.cos θ₀ ≤ Real.cos (θ t) ∧
      (θ t ∈ Set.Icc (-π) π → 0 ≤ θ₀ → θ₀ ≤ π → |θ t| ≤ θ₀) := by
  have hE := pendulum_released_energy hθ hω h0 hω0 t
  have hcos : Real.cos θ₀ ≤ Real.cos (θ t) := by
    have h2 : 0 ≤ 2 * g / L * (Real.cos (θ t) - Real.cos θ₀) := hE ▸ sq_nonneg _
    have h2' : 0 < 2 * g / L := by rw [mul_div_assoc]; positivity
    have := (mul_nonneg_iff_of_pos_left h2').mp h2
    linarith
  refine ⟨hcos, fun hI hθ₀ hθπ => ?_⟩
  have habs : Real.cos (θ t) = Real.cos |θ t| := (Real.cos_abs _).symm
  rw [habs] at hcos
  by_contra hlt
  push Not at hlt
  have hπ : |θ t| ≤ π := abs_le.mpr ⟨hI.1, hI.2⟩
  have := Real.cos_lt_cos_of_nonneg_of_le_pi hθ₀ hπ hlt
  linarith

/-- **Period of the linearized pendulum (DE-228).** For `g/L > 0`, every solution `θ₀ cos(√(g/L) t)` of the
small-angle equation `θ'' = -(g/L) θ` has period `2π √(L/g)`. -/
@[kb "lebldiffyqs2026" "§8.3.1 Period of the pendulum, p. 366"]
theorem pendulum_linear_period {g L : ℝ} (hg : 0 < g) (hL : 0 < L) (θ₀ : ℝ) :
    Function.Periodic (fun t => θ₀ * Real.cos (Real.sqrt (g / L) * t)) (2 * π * Real.sqrt (L / g)) := by
  intro t
  have hs : Real.sqrt (g / L) * Real.sqrt (L / g) = 1 := by
    rw [← Real.sqrt_mul (by positivity), div_mul_div_comm, mul_comm g L, div_self (by positivity),
      Real.sqrt_one]
  simp only
  rw [show Real.sqrt (g / L) * (t + 2 * π * Real.sqrt (L / g))
      = Real.sqrt (g / L) * t + 2 * π * (Real.sqrt (g / L) * Real.sqrt (L / g)) by ring, hs, mul_one,
    Real.cos_add_two_pi]

end UndergradKB.DifferentialEquations
