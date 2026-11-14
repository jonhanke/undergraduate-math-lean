import UndergradKB.Precalculus.ConicsClassify
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 7 (Stitz-Zeager): exercises with the book's answers (wave 8), Section 7.5 (conic test) -/

namespace UndergradKB.Precalculus.Course

open UndergradKB.Precalculus

/-- Stitz-Zeager Exercise 7.5.34: if `A x² + C y² + D x + E y + F = 0` (`A`, `C` not both zero) has a
non-degenerate graph (not empty, not a point, not one or two lines), then `AC < 0` gives a hyperbola, `AC = 0` a
parabola, and `AC > 0` an ellipse (a circle when moreover `A = C`; the circle case is a special ellipse with equal
foci). This is the `B = 0` case of the discriminant test, where `B² - 4AC = -4AC`. -/
@[kb "stitzzeager2013" "Exercise 7.5.34, p. 555"]
theorem exer_7_5_34 (A C D E F : ℝ) (hAC : ¬(A = 0 ∧ C = 0))
    (hne : conicGraph A 0 C D E F ≠ ∅) (hpt : ∀ p, conicGraph A 0 C D E F ≠ {p})
    (hline : ∀ a b c a' b' c' : ℝ, conicGraph A 0 C D E F ≠ lineSet a b c ∪ lineSet a' b' c') :
    (A * C < 0 → ∃ F₁ F₂ : ℝ × ℝ, ∃ a : ℝ, 0 < a ∧ edist2 F₁ F₂ > 2 * a ∧
        conicGraph A 0 C D E F = hyperbolaSet F₁ F₂ (2 * a)) ∧
    (A * C = 0 → ∃ (Fc : ℝ × ℝ) (a b c : ℝ), a ^ 2 + b ^ 2 ≠ 0 ∧ a * Fc.1 + b * Fc.2 ≠ c ∧
        conicGraph A 0 C D E F = parabolaSet Fc a b c) ∧
    (0 < A * C → ∃ F₁ F₂ : ℝ × ℝ, ∃ a : ℝ, edist2 F₁ F₂ < 2 * a ∧
        conicGraph A 0 C D E F = ellipseSet F₁ F₂ (2 * a)) := by
  have hABC : ¬(A = 0 ∧ (0 : ℝ) = 0 ∧ C = 0) := fun h => hAC ⟨h.1, h.2.2⟩
  obtain ⟨he, hh, hp⟩ := discriminant_test_graph A 0 C D E F hABC hne hpt hline
  refine ⟨fun h => ?_, fun h => hp ?_, fun h => he ?_⟩
  · obtain ⟨F₁, F₂, a, h1, h2, h3⟩ := hh (by linarith)
    exact ⟨F₁, F₂, a, h1, h2, h3⟩
  · linear_combination (-4 : ℝ) * h
  · linarith

end UndergradKB.Precalculus.Course
