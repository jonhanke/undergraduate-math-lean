/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import UndergradKB.DifferentialEquations.LaplaceUniqueness
import UndergradKB.DifferentialEquations.NthOrderLinear
import UndergradKB.DifferentialEquations.BoundaryValue
import UndergradKB.DifferentialEquations.FrobeniusAnalytic
import UndergradKB.DifferentialEquations.FourierDirichlet
import UndergradKB.DifferentialEquations.Gibbs

/-!
# Proofs of the differential equations headline statements

Proves the statements of `Challenge_DifferentialEquations.lean` from the library. `lake comparator` checks that each
statement here is exactly the one in `Challenge_DifferentialEquations.lean`.
-/

namespace UndergradKB.Headlines.DifferentialEquations

open Real Set Filter Topology MeasureTheory intervalIntegral UndergradKB.DifferentialEquations

theorem laplace_unique {f g : ℝ → ℝ} {M N c d : ℝ} (hfc : ContinuousOn f (Ici 0))
    (hgc : ContinuousOn g (Ici 0)) (hf : ExpOrder f M c) (hg : ExpOrder g N d)
    (heq : ∀ᶠ s in atTop, laplace f s = laplace g s) : ∀ t, 0 ≤ t → f t = g t :=
  UndergradKB.DifferentialEquations.laplace_unique hfc hgc hf hg heq

theorem linN_general_solution {n : ℕ} {a : Fin n → ℝ → ℝ} {I : Set ℝ} (hI : I.OrdConnected)
    (hne : I.Nonempty) (ha : ∀ k, ContinuousOn (a k) I) {D : Fin n → Fin (n + 1) → ℝ → ℝ}
    (hD : ∀ i, SolvesLinN a 0 I (D i)) (hli : LinearIndependent ℝ (fun i (t : I) => D i 0 t))
    {E : Fin (n + 1) → ℝ → ℝ} (hE : SolvesLinN a 0 I E) :
    ∃ C : Fin n → ℝ, ∀ k : Fin n, ∀ t ∈ I, E k.castSucc t = ∑ i, C i * D i k.castSucc t :=
  UndergradKB.DifferentialEquations.linN_general_solution hI hne ha hD hli hE

theorem wave_general_solution {a : ℝ} (ha : a ≠ 0) {y : ℝ → ℝ → ℝ}
    (hy : ContDiff ℝ 2 (fun p : ℝ × ℝ => y p.1 p.2)) (hwave : WaveEq a y) :
    ∃ F G : ℝ → ℝ, ContDiff ℝ 2 F ∧ ContDiff ℝ 2 G ∧
      ∀ x t, y x t = F (x + a * t) + G (x - a * t) :=
  UndergradKB.DifferentialEquations.wave_general_solution_converse ha hy hwave

theorem frobenius_analytic (P Q : ℕ → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hP : ∀ x : ℝ, |x| < ρ → Summable fun k => P k * x ^ k)
    (hQ : ∀ x : ℝ, |x| < ρ → Summable fun k => Q k * x ^ k) {r : ℝ}
    (hr : r * (r - 1) + P 0 * r + Q 0 = 0)
    (hF : ∀ k : ℕ, 1 ≤ k → (r + k) * (r + k - 1) + P 0 * (r + k) + Q 0 ≠ 0) :
    ∃ a : ℕ → ℝ, a 0 = 1 ∧ (∀ x : ℝ, |x| < ρ → Summable fun k => a k * x ^ k) ∧
      (∀ k : ℕ, 1 ≤ k → a k * ((r + k) * (r + k - 1) + P 0 * (r + k) + Q 0) =
        -∑ j ∈ Finset.range k, a j * ((r + (j : ℝ)) * P (k - j) + Q (k - j))) ∧
      (∀ x : ℝ, 0 < x → x < ρ →
        x ^ 2 * deriv (deriv (fun t : ℝ => t ^ r * ∑' k, a k * t ^ k)) x +
          x * (∑' k, P k * x ^ k) * deriv (fun t : ℝ => t ^ r * ∑' k, a k * t ^ k) x +
          (∑' k, Q k * x ^ k) * (x ^ r * ∑' k, a k * x ^ k) = 0) ∧
      ∃ x : ℝ, 0 < x ∧ x < ρ ∧ x ^ r * ∑' k, a k * x ^ k ≠ 0 :=
  UndergradKB.DifferentialEquations.frobenius_analytic P Q hρ hP hQ hr hF

theorem fourier_series_piecewise_smooth {f : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hper : Function.Periodic f (2 * L)) (hpw : PiecewiseSmoothOn f (-L) L) (t : ℝ) :
    ∃ l₁ l₂, Tendsto f (𝓝[>] t) (𝓝 l₁) ∧ Tendsto f (𝓝[<] t) (𝓝 l₂) ∧
      Tendsto (fun N : ℕ => trigPoly L (fourierA f L) (fourierB f L) N t) atTop (𝓝 ((l₁ + l₂) / 2)) :=
  UndergradKB.DifferentialEquations.fourier_series_piecewise_smooth hL hper hpw t

theorem gibbs_phenomenon :
    Tendsto (fun M : ℕ =>
        trigPoly π (fourierA squareWave π) (fourierB squareWave π) (2 * M) (π / (2 * M)))
      atTop (𝓝 ((2 / π) * ∫ t in (0:ℝ)..π, sinc t)) ∧
    1.17 < (2 / π) * ∫ t in (0:ℝ)..π, sinc t ∧
    ∀ᶠ M : ℕ in atTop,
      1.17 < trigPoly π (fourierA squareWave π) (fourierB squareWave π) (2 * M) (π / (2 * M)) ∧
      squareWave (π / (2 * M)) = 1 :=
  UndergradKB.DifferentialEquations.gibbs_phenomenon

end UndergradKB.Headlines.DifferentialEquations
