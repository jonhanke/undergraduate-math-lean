/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import UndergradKB.RealAnalysis.RiemannLebesgue

/-!
# Headline statements of undergraduate-math-lean 0.2.1: real analysis (Lebl, *Basic Analysis I*)

The main result of this topic that Mathlib, Tau Ceti and ReasBook lack, with its proof a deliberate `sorry`: the
Riemann integral of Lebl's book (defined by Darboux sums) agrees with Mathlib's interval integral (defined by
Lebesgue's theory): a Riemann integrable function on `[a, b]` is Lebesgue integrable there, with the same integral.
So every theorem of Mathlib about the interval integral applies to the book's integral. To check what is claimed,
read this file. `Solution_RealAnalysis.lean` proves the same statement from the library, and `lake comparator`
(configured by `comparator/RealAnalysis.json`) checks that the proved statement is exactly the one here and uses only
the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Each statement is the library's statement, copied. The statements were not yet reviewed by a human (see the README).

## Definitions used

Besides Mathlib (`IntervalIntegrable`, the interval integral `∫ x in a..b, f x`, `MeasureTheory.volume`), the
statement uses these definitions of the library (namespace `UndergradKB.RealAnalysis`), which are **ported from
ReasBook** (https://github.com/optpku/ReasBook, Apache License 2.0, commit 35bcb693; by Zichen Wang and Zaiwen Wen;
see `NOTICE` and `docs/reasbook.md`); a reader checking the statement should check these too:

* `IntervalPartition a b`: a strictly increasing finite list `a = x₀ < x₁ < ⋯ < xₙ = b`;
* `lowerDarbouxSum f P`, `upperDarbouxSum f P`: the sums `∑ mᵢ Δxᵢ` and `∑ Mᵢ Δxᵢ`, with `mᵢ`, `Mᵢ` the infimum and
  supremum of `f` on `[xᵢ₋₁, xᵢ]` (Lebl Definition 5.1.1);
* `lowerDarbouxIntegral f a b`, `upperDarbouxIntegral f a b`: the supremum of the lower sums and the infimum of the
  upper sums over all partitions (Definition 5.1.3);
* `RiemannIntegrableOn f a b`: `f` is bounded on `[a, b]` and the lower and upper Darboux integrals are equal
  (Definition 5.1.9); `riemannIntegral f a b hf` is their common value.
-/

namespace UndergradKB.Headlines.RealAnalysis

open MeasureTheory UndergradKB.RealAnalysis

/-- **The Riemann integral is the Lebesgue integral** (Lebl Definition 5.1.9): a function Riemann integrable on
`[a, b]` in the sense of Darboux is interval integrable in Mathlib's (Lebesgue) sense, and its Riemann integral equals
Mathlib's interval integral. Related: Mathlib has no Darboux or Riemann integral of this kind (its `BoxIntegral` goes
the other way, from Lebesgue integrable functions to a gauge integral); ReasBook states the fundamental theorem of
calculus for Mathlib's interval integral but does not relate it to its Darboux integral; Tau Ceti has neither. -/
theorem riemann_integral_eq_lebesgue {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : RiemannIntegrableOn f a b) :
    IntervalIntegrable f volume a b ∧ riemannIntegral f a b hf = ∫ x in a..b, f x := by
  sorry

end UndergradKB.Headlines.RealAnalysis
