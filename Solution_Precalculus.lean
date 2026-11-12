/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import UndergradKB.Precalculus.DescartesParity

/-!
# Proofs of the precalculus headline statements

Proves the statements of `Challenge_Precalculus.lean` from the library. `lake comparator` checks that each
statement here is exactly the one in `Challenge_Precalculus.lean`.
-/

namespace UndergradKB.Headlines.Precalculus

open Polynomial

theorem descartes_rule_of_signs (p : ℝ[X]) (hp : p ≠ 0) :
    ∃ k : ℕ, p.signVariations = p.roots.countP (0 < ·) + 2 * k :=
  UndergradKB.Precalculus.descartes_rule_of_signs p hp

theorem descartes_rule_of_signs_neg (p : ℝ[X]) (hp : p ≠ 0) :
    ∃ k : ℕ, (p.comp (-X)).signVariations = p.roots.countP (· < 0) + 2 * k :=
  UndergradKB.Precalculus.descartes_rule_of_signs_neg p hp

end UndergradKB.Headlines.Precalculus
