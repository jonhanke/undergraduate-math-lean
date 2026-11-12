/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import UndergradKB.Precalculus.DescartesParity

/-!
# Headline statements of undergraduate-math-lean 0.2.0: precalculus (Stitz–Zeager)

The main result of this topic that Mathlib and Tau Ceti lack, with every proof a deliberate `sorry`: Descartes'
rule of signs in its full form, with the parity of the difference, for positive and for negative zeros. To check
what is claimed, read this file. `Solution_Precalculus.lean` proves the same statements from the library, and
`lake comparator` (configured by `comparator/Precalculus.json`) checks that each proved statement is exactly the one
here and uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Each statement is the library's statement, copied. The statements were not yet reviewed by a human (see the README).

## Definitions used

Only Mathlib definitions: `Polynomial.signVariations` (the number of sign changes in the sequence of nonzero
coefficients), `Polynomial.roots` (the roots in `ℝ`, with multiplicity) and `Multiset.countP`.
-/

namespace UndergradKB.Headlines.Precalculus

open Polynomial

/-- **Descartes' rule of signs, positive zeros** (Stitz–Zeager Theorem 3.10): for a nonzero real polynomial, the
number of sign changes of its coefficients is the number of its positive zeros, counted with multiplicity, plus an
even number. Related: Mathlib proves the inequality (`Polynomial.roots_countP_pos_le_signVariations`) but not the
parity; Tau Ceti has only sign changes of lists. -/
theorem descartes_rule_of_signs (p : ℝ[X]) (hp : p ≠ 0) :
    ∃ k : ℕ, p.signVariations = p.roots.countP (0 < ·) + 2 * k := by
  sorry

/-- **Descartes' rule of signs, negative zeros** (Stitz–Zeager Theorem 3.10): the number of sign changes of the
coefficients of `p(-x)` is the number of negative zeros of `p`, counted with multiplicity, plus an even number.
Related: as above. -/
theorem descartes_rule_of_signs_neg (p : ℝ[X]) (hp : p ≠ 0) :
    ∃ k : ℕ, (p.comp (-X)).signVariations = p.roots.countP (· < 0) + 2 * k := by
  sorry

end UndergradKB.Headlines.Precalculus
