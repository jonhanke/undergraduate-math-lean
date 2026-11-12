/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import UndergradKB.DifferentialEquations.LaplaceUniqueness
import UndergradKB.DifferentialEquations.NthOrderLinear
import UndergradKB.DifferentialEquations.BoundaryValue

/-!
# Headline statements of undergraduate-math-lean 0.2.0: differential equations (Lebl, *Notes on Diffy Qs*)

The main results of this topic that Mathlib and Tau Ceti lack, one theorem each, with every proof a deliberate
`sorry`: the uniqueness of the Laplace transform (Lerch's theorem), the general solution of a homogeneous linear
equation of order `n` (`n` independent solutions span all solutions), and the general solution of the
one-dimensional wave equation as a sum of two travelling waves. To check what is claimed, read this file.
`Solution_DifferentialEquations.lean` proves the same statements from the library, and `lake comparator`
(configured by `comparator/DifferentialEquations.json`) checks that each proved statement is exactly the one here
and uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Each statement is the library's statement, copied. The statements were not yet reviewed by a human (see the README).

## Definitions used

Besides Mathlib, the statements use these definitions of the library (namespace `UndergradKB.DifferentialEquations`);
a reader checking a statement should check these too:

* `laplace f s = ∫ t in Ioi 0, exp (-(s * t)) * f t`, the Laplace transform (a Lebesgue integral; for the functions
  of the theorem it converges absolutely for all large `s`).
* `ExpOrder f M c`: `|f t| ≤ M * exp (c * t)` for every `t ≥ 0` (exponential order).
* `IsDerivChain I D` (for `D : Fin (n + 1) → ℝ → ℝ`): for every `k < n` and `t ∈ I`, `D k` has derivative
  `D (k + 1) t` at `t`; so `D 0, …, D n` are a function and its first `n` derivatives on `I`.
* `SolvesLinN a f I D`: `IsDerivChain I D` and `D n t + ∑ k, a k t * D k t = f t` for `t ∈ I`, i.e. `D 0` solves
  `y⁽ⁿ⁾ + aₙ₋₁(t) y⁽ⁿ⁻¹⁾ + ⋯ + a₀(t) y = f(t)` on `I`.
* `WaveEq a y`: `∂²y/∂t² = a² ∂²y/∂x²` at every point `(x, t)` of the plane (iterated one-variable derivatives).
-/

namespace UndergradKB.Headlines.DifferentialEquations

open Real Set Filter Topology MeasureTheory UndergradKB.DifferentialEquations

/-- **Uniqueness of the Laplace transform (Lerch's theorem)** (Lebl Theorem 6.1.3): two continuous functions of
exponential order on `[0, ∞)` whose Laplace transforms agree for all large `s` are equal on `[0, ∞)`. Related:
Mathlib has no Laplace transform of functions; Tau Ceti proves that finite positive measures on the half line are
determined by their Laplace transforms, which does not give this statement for functions of either sign. -/
theorem laplace_unique {f g : ℝ → ℝ} {M N c d : ℝ} (hfc : ContinuousOn f (Ici 0))
    (hgc : ContinuousOn g (Ici 0)) (hf : ExpOrder f M c) (hg : ExpOrder g N d)
    (heq : ∀ᶠ s in atTop, laplace f s = laplace g s) : ∀ t, 0 ≤ t → f t = g t := by
  sorry

/-- **The general solution of a homogeneous linear equation of order `n`** (Lebl Theorem 2.3.3; Theorem 2.1.3 for
order 2): on an interval where the coefficients are continuous, if `n` solutions are linearly independent, every
solution is a linear combination of them (and so are its first `n - 1` derivatives, with the same constants).
Related: Mathlib and Tau Ceti have existence and uniqueness for first-order systems; Tau Ceti has the Wronskian of
`y'' = q y`; neither states that the solution space of an equation of order `n` is spanned by `n` independent
solutions. -/
theorem linN_general_solution {n : ℕ} {a : Fin n → ℝ → ℝ} {I : Set ℝ} (hI : I.OrdConnected)
    (hne : I.Nonempty) (ha : ∀ k, ContinuousOn (a k) I) {D : Fin n → Fin (n + 1) → ℝ → ℝ}
    (hD : ∀ i, SolvesLinN a 0 I (D i)) (hli : LinearIndependent ℝ (fun i (t : I) => D i 0 t))
    {E : Fin (n + 1) → ℝ → ℝ} (hE : SolvesLinN a 0 I E) :
    ∃ C : Fin n → ℝ, ∀ k : Fin n, ∀ t ∈ I, E k.castSucc t = ∑ i, C i * D i k.castSucc t := by
  sorry

/-- **The general solution of the wave equation** (Lebl § 4.8, characteristic coordinates): every twice
continuously differentiable solution of `y_tt = a² y_xx` on the plane (`a ≠ 0`) is `F(x + at) + G(x - at)` for two
twice continuously differentiable functions `F` and `G` of one variable. Related: neither Mathlib nor Tau Ceti has
the wave equation. -/
theorem wave_general_solution {a : ℝ} (ha : a ≠ 0) {y : ℝ → ℝ → ℝ}
    (hy : ContDiff ℝ 2 (fun p : ℝ × ℝ => y p.1 p.2)) (hwave : WaveEq a y) :
    ∃ F G : ℝ → ℝ, ContDiff ℝ 2 F ∧ ContDiff ℝ 2 G ∧
      ∀ x t, y x t = F (x + a * t) + G (x - a * t) := by
  sorry

end UndergradKB.Headlines.DifferentialEquations
