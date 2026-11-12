/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import UndergradKB.DifferentialEquations.LaplaceUniqueness
import UndergradKB.DifferentialEquations.NthOrderLinear
import UndergradKB.DifferentialEquations.BoundaryValue

/-!
# Proofs of the differential equations headline statements

Proves the statements of `Challenge_DifferentialEquations.lean` from the library. `lake comparator` checks that each
statement here is exactly the one in `Challenge_DifferentialEquations.lean`.
-/

namespace UndergradKB.Headlines.DifferentialEquations

open Real Set Filter Topology MeasureTheory UndergradKB.DifferentialEquations

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

end UndergradKB.Headlines.DifferentialEquations
