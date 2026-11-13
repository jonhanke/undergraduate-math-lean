/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import UndergradKB.Precalculus.DescartesParity
import UndergradKB.Precalculus.ConicsClassify

/-!
# Proofs of the precalculus headline statements

Proves the statements of `Challenge_Precalculus.lean` from the library. `lake comparator` checks that each
statement here is exactly the one in `Challenge_Precalculus.lean`.
-/

namespace UndergradKB.Headlines.Precalculus

open Polynomial UndergradKB.Precalculus

theorem descartes_rule_of_signs (p : ℝ[X]) (hp : p ≠ 0) :
    ∃ k : ℕ, p.signVariations = p.roots.countP (0 < ·) + 2 * k :=
  UndergradKB.Precalculus.descartes_rule_of_signs p hp

theorem descartes_rule_of_signs_neg (p : ℝ[X]) (hp : p ≠ 0) :
    ∃ k : ℕ, (p.comp (-X)).signVariations = p.roots.countP (· < 0) + 2 * k :=
  UndergradKB.Precalculus.descartes_rule_of_signs_neg p hp

theorem discriminant_test (A B C D E F : ℝ) (hABC : ¬(A = 0 ∧ B = 0 ∧ C = 0)) :
    (B ^ 2 - 4 * A * C < 0 →
      conicGraph A B C D E F = ∅ ∨ (∃ p, conicGraph A B C D E F = {p}) ∨
        ∃ F₁ F₂ : ℝ × ℝ, ∃ a : ℝ, edist2 F₁ F₂ < 2 * a ∧
          conicGraph A B C D E F = ellipseSet F₁ F₂ (2 * a)) ∧
    (0 < B ^ 2 - 4 * A * C →
      (∃ F₁ F₂ : ℝ × ℝ, ∃ a : ℝ, 0 < a ∧ 2 * a < edist2 F₁ F₂ ∧
          conicGraph A B C D E F = hyperbolaSet F₁ F₂ (2 * a)) ∨
        ∃ a b c a' b' c' : ℝ, a * b' - a' * b ≠ 0 ∧
          conicGraph A B C D E F = lineSet a b c ∪ lineSet a' b' c') ∧
    (B ^ 2 - 4 * A * C = 0 →
      (∃ (Fc : ℝ × ℝ) (a b c : ℝ), a ^ 2 + b ^ 2 ≠ 0 ∧ a * Fc.1 + b * Fc.2 ≠ c ∧
          conicGraph A B C D E F = parabolaSet Fc a b c) ∨
        conicGraph A B C D E F = ∅ ∨
        (∃ a b c : ℝ, a ^ 2 + b ^ 2 ≠ 0 ∧ conicGraph A B C D E F = lineSet a b c) ∨
        ∃ a b c c' : ℝ, a ^ 2 + b ^ 2 ≠ 0 ∧ c ≠ c' ∧
          conicGraph A B C D E F = lineSet a b c ∪ lineSet a b c') :=
  UndergradKB.Precalculus.discriminant_test_classification A B C D E F hABC

end UndergradKB.Headlines.Precalculus
