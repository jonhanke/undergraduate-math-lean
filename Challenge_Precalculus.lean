/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import UndergradKB.Precalculus.DescartesParity
import UndergradKB.Precalculus.ConicsClassify

/-!
# Headline statements of undergraduate-math-lean 0.2.1: precalculus (Stitz–Zeager)

The main results of this topic that Mathlib and Tau Ceti lack, with every proof a deliberate `sorry`: Descartes'
rule of signs in its full form, with the parity of the difference, for positive and for negative zeros; and, added in
0.2.1, the discriminant classification of the graph of a general second-degree equation in two variables, with every
degenerate case listed. To check
what is claimed, read this file. `Solution_Precalculus.lean` proves the same statements from the library, and
`lake comparator` (configured by `comparator/Precalculus.json`) checks that each proved statement is exactly the one
here and uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Each statement is the library's statement, copied. The statements were not yet reviewed by a human (see the README).

## Definitions used

Besides Mathlib (`Polynomial.signVariations`, the number of sign changes in the sequence of nonzero coefficients;
`Polynomial.roots`, the roots in `ℝ` with multiplicity; `Multiset.countP`), the conic statement uses these
definitions of the library (namespace `UndergradKB.Precalculus`); a reader checking a statement should check these
too:

* `edist2 P Q`: the Euclidean distance `√((P.1 - Q.1)² + (P.2 - Q.2)²)` between points of `ℝ × ℝ`.
* `conicGraph A B C D E F`: the set of points `(x, y)` with `A x² + B x y + C y² + D x + E y + F = 0`.
* `lineSet a b c`: the set of points `(x, y)` with `a x + b y = c`.
* `ellipseSet F₁ F₂ d`: the points whose distances to `F₁` and `F₂` (`edist2`) add up to `d`.
* `hyperbolaSet F₁ F₂ d`: the points for which the absolute value of the difference of the distances to `F₁` and
  `F₂` is `d`.
* `parabolaSet F a b c`: the points whose distance to `F` equals their distance to the line `a x + b y = c`
  (the distance is `|a x + b y - c| / √(a² + b²)`).
-/

namespace UndergradKB.Headlines.Precalculus

open Polynomial UndergradKB.Precalculus

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

/-- **The discriminant test for second-degree equations** (Stitz–Zeager Theorem 11.11): let `A, B, C` be not all
zero and let `S` be the graph of `A x² + B x y + C y² + D x + E y + F = 0`. If `B² - 4AC < 0`, then `S` is empty, a
single point, or an ellipse (foci `F₁`, `F₂`, distance sum `2a` greater than the distance between the foci; a circle
when the foci coincide). If `B² - 4AC > 0`, then `S` is a hyperbola (distance difference `2a` with `0 < 2a` smaller
than the distance between the foci) or the union of two intersecting lines. If `B² - 4AC = 0`, then `S` is a
parabola (focus not on the directrix), empty, one line, or the union of two distinct parallel lines. The book states
the test only for graphs known to be non-degenerate conics; this version also lists all degenerate cases, so it is
stronger. Related: Mathlib has nothing on conic sections or quadrics; Tau Ceti has conics as curves of genus zero
over fields and Kepler orbits, but none relates the zero set of a general real quadratic in two variables to the
focal definitions of the ellipse, hyperbola and parabola. -/
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
          conicGraph A B C D E F = lineSet a b c ∪ lineSet a b c') := by
  sorry

end UndergradKB.Headlines.Precalculus
