/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import UndergradKB.Calculus.RiemannRearrangement
import UndergradKB.Calculus.Simpson

/-!
# Headline statements of undergraduate-math-lean 0.1.0: calculus (OpenStax Calculus)

The main results of this topic that Mathlib and Tau Ceti lack, one theorem each, with every proof a deliberate
`sorry`: Riemann's rearrangement theorem for conditionally convergent series, and the error bound of Simpson's rule.
To check what is claimed, read this file. `Solution_Calculus.lean` proves the same statements from the library, and
`lake comparator` (configured by `comparator/Calculus.json`) checks that each proved statement is exactly the one
here and uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Each statement is the library's statement, copied. The statements were not yet reviewed by a human (see the README).

## Definitions used

Besides Mathlib, the statements use these definitions of the library; a reader checking a statement should check
these too:

* `UndergradKB.Calculus.simpson` (OpenStax Calculus Volume 2, §3.6): Simpson's rule `S_n` for even `n`, which
  adds up `n/2` parabolic panels of width `2Δx`, where `Δx = (b-a)/n`, each contributing
  `(Δx/3)(f(x_{2j}) + 4 f(x_{2j+1}) + f(x_{2j+2}))`.
-/

namespace UndergradKB.Headlines.Calculus

open Set Finset intervalIntegral MeasureTheory Filter Topology

/-- **Riemann's rearrangement theorem** (OpenStax Calculus Volume 2, §5.5): if the series `∑ a n` converges (its
partial sums tend to some `S`) but not absolutely (`∑ |a n|` diverges), then for every real `L` there is a
bijection `σ` of the natural numbers such that the partial sums of the rearranged series `∑ a (σ n)` tend to `L`.
Related: Mathlib has only the rearrangement inequality, and Tau Ceti has no rearrangement theorem for series. -/
theorem riemann_rearrangement {a : ℕ → ℝ} {S : ℝ}
    (hS : Tendsto (fun n => ∑ i ∈ range n, a i) atTop (𝓝 S))
    (habs : ¬ Summable (fun n => |a n|)) (L : ℝ) :
    ∃ σ : ℕ ≃ ℕ, Tendsto (fun n => ∑ i ∈ range n, a (σ i)) atTop (𝓝 L) := by
  sorry

/-- **Error bound of Simpson's rule** (OpenStax Calculus Volume 2, §3.6): if `f` is four times continuously
differentiable and its fourth derivative is bounded by `M` on `[a, b]`, then
`|S_n - ∫_a^b f| ≤ M (b-a)^5 / (180 n^4)` for even `n > 0`. Related: neither Mathlib nor Tau Ceti has Simpson's
rule or any Newton-Cotes rule. -/
theorem simpson_error_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 4 f) {a b M : ℝ} (hab : a ≤ b) {n : ℕ}
    (hn : Even n) (hpos : 0 < n) (hM : ∀ x ∈ Icc a b, |iteratedDeriv 4 f x| ≤ M) :
    |UndergradKB.Calculus.simpson f a b n - ∫ x in a..b, f x| ≤ M * (b - a) ^ 5 / (180 * n ^ 4) := by
  sorry

end UndergradKB.Headlines.Calculus
