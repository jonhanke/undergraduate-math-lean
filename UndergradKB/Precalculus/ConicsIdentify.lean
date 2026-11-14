import UndergradKB.Precalculus.ConicsClassify

/-!
# Identifying conic sections without an `xy` term (Stitz-Zeager, Precalculus, end of §7.5)

The boxed strategy at the end of Section 7.5: for an equation `A x² + C y² + D x + E y + F = 0` whose graph is a
non-degenerate conic (a parabola, circle, ellipse or hyperbola), only one variable squared gives a parabola; both
squared with equal coefficients a circle; with coefficients of the same sign an ellipse; with coefficients of
opposite signs a hyperbola. (The box names the two coefficients `A` and `B` after writing the equation with `A` and
`C`; we use `A` and `C`, as in the equation.)

Non-degenerate is expressed as in `discriminant_test_graph`: the graph is not empty, not a single point and not one
line or the union of two lines. The parabola, ellipse and hyperbola cases follow from the discriminant test
(Theorem 11.11) with no `xy` term; the circle case is proved directly by completing the square.
-/

namespace UndergradKB.Precalculus

/-- The circle case of the strategy box: if `A ≠ 0` and the graph of `A x² + A y² + D x + E y + F = 0` is neither
empty nor a single point, it is the circle of some center and some radius `r > 0`. -/
@[kb "stitzzeager2013" "§7.5, p. 552"]
theorem conic_identify_circle (A D E F : ℝ) (hA : A ≠ 0) (hne : conicGraph A 0 A D E F ≠ ∅)
    (hpt : ∀ p, conicGraph A 0 A D E F ≠ {p}) :
    ∃ (c : ℝ × ℝ) (r : ℝ), 0 < r ∧ conicGraph A 0 A D E F = {P | edist2 P c = r} := by
  set h := -D / (2 * A)
  set k := -E / (2 * A)
  set R := h ^ 2 + k ^ 2 - F / A
  have key : ∀ P : ℝ × ℝ, P ∈ conicGraph A 0 A D E F ↔ (P.1 - h) ^ 2 + (P.2 - k) ^ 2 = R := by
    intro P
    simp only [conicGraph, quadForm, Set.mem_ofPred_eq, h, k, R]
    constructor
    · intro hP
      field_simp
      linear_combination (4 * A) * hP
    · intro hP
      field_simp at hP
      have h4 : (4 * A ^ 2) ≠ 0 := by positivity
      apply mul_left_cancel₀ hA
      linear_combination hP / 4
  have hR : 0 < R := by
    rcases lt_trichotomy R 0 with hR | hR | hR
    · exfalso; apply hne
      ext P
      simp only [Set.mem_empty_iff_false, iff_false, key]
      intro hP; nlinarith [sq_nonneg (P.1 - h), sq_nonneg (P.2 - k)]
    · exfalso; apply hpt (h, k)
      ext P
      simp only [Set.mem_singleton_iff, key, hR]
      constructor
      · intro hP
        have h1 : P.1 - h = 0 := by nlinarith [sq_nonneg (P.1 - h), sq_nonneg (P.2 - k)]
        have h2 : P.2 - k = 0 := by nlinarith [sq_nonneg (P.1 - h), sq_nonneg (P.2 - k)]
        exact Prod.ext (by linarith) (by linarith)
      · rintro rfl; simp
    · exact hR
  refine ⟨(h, k), √R, Real.sqrt_pos.2 hR, ?_⟩
  ext P
  rw [key, Set.mem_ofPred_eq, edist2]
  constructor
  · intro hP; rw [hP]
  · intro hP
    have h0 : 0 ≤ (P.1 - h) ^ 2 + (P.2 - k) ^ 2 := by positivity
    rw [Real.sqrt_inj h0 hR.le] at hP
    exact hP

/-- Strategies for identifying conic sections (box at the end of §7.5): for `A x² + C y² + D x + E y + F = 0`
(`A`, `C` not both zero) whose graph is a non-degenerate conic, only one variable squared (`A C = 0`) gives a
parabola, coefficients of the same sign an ellipse (a circle when `A = C`), and of opposite signs a hyperbola. -/
@[kb "stitzzeager2013" "§7.5, p. 552"]
theorem conic_identify_strategies (A C D E F : ℝ) (hAC : ¬(A = 0 ∧ C = 0))
    (hne : conicGraph A 0 C D E F ≠ ∅) (hpt : ∀ p, conicGraph A 0 C D E F ≠ {p})
    (hline : ∀ a b c a' b' c' : ℝ, conicGraph A 0 C D E F ≠ lineSet a b c ∪ lineSet a' b' c') :
    (A * C = 0 → ∃ (Fc : ℝ × ℝ) (a b c : ℝ), a ^ 2 + b ^ 2 ≠ 0 ∧ a * Fc.1 + b * Fc.2 ≠ c ∧
        conicGraph A 0 C D E F = parabolaSet Fc a b c) ∧
    (A = C → ∃ (c : ℝ × ℝ) (r : ℝ), 0 < r ∧ conicGraph A 0 C D E F = {P | edist2 P c = r}) ∧
    (0 < A * C → ∃ F₁ F₂ : ℝ × ℝ, ∃ a : ℝ, edist2 F₁ F₂ < 2 * a ∧
        conicGraph A 0 C D E F = ellipseSet F₁ F₂ (2 * a)) ∧
    (A * C < 0 → ∃ F₁ F₂ : ℝ × ℝ, ∃ a : ℝ, 0 < a ∧ 2 * a < edist2 F₁ F₂ ∧
        conicGraph A 0 C D E F = hyperbolaSet F₁ F₂ (2 * a)) := by
  have hABC : ¬(A = 0 ∧ (0 : ℝ) = 0 ∧ C = 0) := fun h => hAC ⟨h.1, h.2.2⟩
  obtain ⟨he, hh, hp⟩ := discriminant_test_graph A 0 C D E F hABC hne hpt hline
  refine ⟨fun h => hp ?_, fun h => ?_, fun h => he ?_, fun h => hh ?_⟩
  · linear_combination (-4 : ℝ) * h
  rotate_left
  · linarith
  · linarith
  subst h
  have hA : A ≠ 0 := fun h0 => hAC ⟨h0, h0⟩
  exact conic_identify_circle A D E F hA hne hpt

end UndergradKB.Precalculus
