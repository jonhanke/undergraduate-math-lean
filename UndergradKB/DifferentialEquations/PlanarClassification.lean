import UndergradKB.DifferentialEquations.MatrixSystems
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # Behaviour of solutions of `x' = A x` by eigenvalues (Lebl §3.5)

The long-time behaviour behind Lebl's classification of linear systems (sink, spiral sink, center), stated for an
`n × n` matrix: if all eigenvalues are negative (with a basis of eigenvectors) every solution tends to the origin;
for complex eigenvalues `a ± i b` the real solutions spiral into the origin when `a < 0` and are periodic (closed
orbits, a center) when `a = 0`. -/

namespace UndergradKB.DifferentialEquations

open Set Matrix Filter Topology

variable {n : ℕ}

lemma tendsto_exp_mul_atTop_of_neg {μ : ℝ} (hμ : μ < 0) :
    Tendsto (fun t => Real.exp (μ * t)) atTop (𝓝 0) :=
  Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hμ)

/-- **Sink** (Lebl, §3.5, eigenvalues both negative; general `n`): if `A` has `n` linearly independent eigenvectors
whose eigenvalues are all negative, then every solution of `x' = A x` tends to `0` as `t → ∞`. -/
@[kb "lebldiffyqs2026" "§3.5 sink, p. 147"]
theorem sink_tendsto_zero {A : Matrix (Fin n) (Fin n) ℝ} {v : Fin n → Fin n → ℝ} {μ : Fin n → ℝ}
    (hv : ∀ i, A *ᵥ v i = μ i • v i) (hli : LinearIndependent ℝ v) (hneg : ∀ i, μ i < 0)
    {y : ℝ → Fin n → ℝ} (hy : ∀ t, HasDerivAt y (A *ᵥ y t) t) : Tendsto y atTop (𝓝 0) := by
  obtain ⟨c, hc, -⟩ := eigen_general_solution hv hli hy
  have : Tendsto (fun t => ∑ i, c i • (Real.exp (μ i * t) • v i)) atTop (𝓝 (∑ i : Fin n, (0 : Fin n → ℝ))) :=
    tendsto_finsetSum _ fun i _ => by
      simpa using ((tendsto_exp_mul_atTop_of_neg (hneg i)).smul_const (v i)).const_smul (c i)
  simp only [Finset.sum_const_zero] at this
  exact this.congr fun t => (hc t).symm

/-- **Saddle** (Lebl, §3.5): along an eigenvector with positive eigenvalue the solution `v e^{λ t}` (`v ≠ 0`) is
unbounded, while along one with negative eigenvalue it tends to `0`. -/
@[kb "lebldiffyqs2026" "§3.5 saddle, p. 147"]
theorem saddle_behaviour {μ ν : ℝ} (hμ : 0 < μ) (hν : ν < 0) {v w : Fin n → ℝ} (hv : v ≠ 0) :
    Tendsto (fun t => ‖Real.exp (μ * t) • v‖) atTop atTop ∧
      Tendsto (fun t => Real.exp (ν * t) • w) atTop (𝓝 0) := by
  constructor
  · have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have h1 : Tendsto (fun t => Real.exp (μ * t)) atTop atTop :=
      Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hμ)
    have : Tendsto (fun t => Real.exp (μ * t) * ‖v‖) atTop atTop := h1.atTop_mul_const hn
    refine this.congr fun t => ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  · simpa using (tendsto_exp_mul_atTop_of_neg hν).smul_const w

/-- **Spiral sink** (Lebl, §3.5): for complex eigenvalues `a ± i b` with `a < 0`, the real solutions
`e^{at}(w cos bt - u sin bt)` and `e^{at}(w sin bt + u cos bt)` of `complex_eigen_solutions` tend to `0`. -/
@[kb "lebldiffyqs2026" "§3.5 spiral sink, p. 147"]
theorem spiral_sink_tendsto_zero {a b : ℝ} (ha : a < 0) (w u : Fin n → ℝ) :
    Tendsto (fun t => Real.exp (a * t) • (Real.cos (b * t) • w - Real.sin (b * t) • u)) atTop (𝓝 0) ∧
    Tendsto (fun t => Real.exp (a * t) • (Real.sin (b * t) • w + Real.cos (b * t) • u)) atTop (𝓝 0) := by
  have he := tendsto_exp_mul_atTop_of_neg ha
  have hc : ∀ (t : ℝ) (z : Fin n → ℝ), ‖Real.cos (b * t) • z‖ ≤ ‖z‖ := fun t z => by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _)
  have hs : ∀ (t : ℝ) (z : Fin n → ℝ), ‖Real.sin (b * t) • z‖ ≤ ‖z‖ := fun t z => by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one _)
  have hb1 : IsBoundedUnder (· ≤ ·) atTop
      (norm ∘ fun t => Real.cos (b * t) • w - Real.sin (b * t) • u) :=
    isBoundedUnder_of ⟨‖w‖ + ‖u‖, fun t =>
      (norm_sub_le _ _).trans (add_le_add (hc t w) (hs t u))⟩
  have hb2 : IsBoundedUnder (· ≤ ·) atTop
      (norm ∘ fun t => Real.sin (b * t) • w + Real.cos (b * t) • u) :=
    isBoundedUnder_of ⟨‖w‖ + ‖u‖, fun t =>
      (norm_add_le _ _).trans (add_le_add (hs t w) (hc t u))⟩
  exact ⟨he.zero_smul_isBoundedUnder_le hb1, he.zero_smul_isBoundedUnder_le hb2⟩

/-- **Center** (Lebl, §3.5): for purely imaginary eigenvalues `± i b` (`b ≠ 0`), the real solutions
`w cos bt - u sin bt` and `w sin bt + u cos bt` are periodic with period `2π / b` (closed trajectories). -/
@[kb "lebldiffyqs2026" "§3.5 center, p. 147"]
theorem center_periodic {b : ℝ} (hb : b ≠ 0) (w u : Fin n → ℝ) :
    Function.Periodic (fun t => Real.cos (b * t) • w - Real.sin (b * t) • u) (2 * Real.pi / b) ∧
    Function.Periodic (fun t => Real.sin (b * t) • w + Real.cos (b * t) • u) (2 * Real.pi / b) := by
  have h : ∀ t, b * (t + 2 * Real.pi / b) = b * t + 2 * Real.pi := fun t => by
    field_simp
  constructor <;> intro t <;> simp only [h, Real.cos_add_two_pi, Real.sin_add_two_pi]

end UndergradKB.DifferentialEquations
