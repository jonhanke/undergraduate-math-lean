/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import UndergradKB.ComplexAnalysis.Singularities
import UndergradKB.ComplexAnalysis.Dedekind

/-!
# Headline statements of undergraduate-math-lean 0.2.0: complex analysis (Beck–Marchesi–Pixton–Sabalka)

The main results of this topic that Mathlib and Tau Ceti lack, one theorem each, with every proof a deliberate
`sorry`: the Casorati–Weierstrass theorem, and the reciprocity law for Dedekind sums. To check what is claimed, read
this file. `Solution_ComplexAnalysis.lean` proves the same statements from the library, and `lake comparator`
(configured by `comparator/ComplexAnalysis.json`) checks that each proved statement is exactly the one here and uses
only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Each statement is the library's statement, copied. The statements were not yet reviewed by a human (see the README).

## Definitions used

Besides Mathlib, the statements use these definitions of the library (namespace `UndergradKB.ComplexAnalysis`);
a reader checking a statement should check these too:

* `HasRemovableSingularity f z₀`: for some `R > 0` and some `g` holomorphic on the disc `ball z₀ R`, `f = g` on the
  punctured disc.
* `HasPole f z₀`: `‖f z‖ → ∞` as `z → z₀`, `z ≠ z₀`.
* `HasEssentialSingularity f z₀`: neither a removable singularity nor a pole (the book's definitions).
* `dedekindSumCot a b = (1 / (4b)) ∑_{k=1}^{b-1} cot (π k a / b) cot (π k / b)`, the Dedekind sum `s(a, b)`.
-/

namespace UndergradKB.Headlines.ComplexAnalysis

open Metric Set Filter Topology Finset Real UndergradKB.ComplexAnalysis

/-- **The Casorati–Weierstrass theorem** (Beck Theorem 9.1.9): near an essential singularity `z₀`, a holomorphic
function comes arbitrarily close to every complex number `w`: for all `ε, r > 0` there is `z` with
`0 < |z - z₀| < r` and `|f z - w| < ε`. Related: Mathlib has Riemann's removable singularity theorem; neither Mathlib
nor Tau Ceti has this theorem. -/
theorem casorati_weierstrass {f : ℂ → ℂ} {z₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball z₀ R \ {z₀})) (hess : HasEssentialSingularity f z₀)
    (w : ℂ) {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) :
    ∃ z : ℂ, 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ < r ∧ ‖f z - w‖ < ε := by
  sorry

/-- **The reciprocity law for Dedekind sums** (Beck § 10.4, Exercise 2): for coprime positive integers `a` and
`b`, `s(a, b) + s(b, a) = -1/4 + (a/b + 1/(ab) + b/a)/12`. The proof here is elementary (finite trigonometric sums
and counting lattice points), not by residues as in the book. Related: neither Mathlib nor Tau Ceti has Dedekind
sums. -/
theorem dedekind_sum_reciprocity {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) :
    dedekindSumCot a b + dedekindSumCot b a
      = -1 / 4 + ((a : ℝ) / b + 1 / ((a : ℝ) * b) + (b : ℝ) / a) / 12 := by
  sorry

end UndergradKB.Headlines.ComplexAnalysis
