import UndergradKB.Common.Attr
import UndergradKB.DifferentialEquations.SpiralType

/-! # Sources and spiral sources by time reversal (Lebl, *Notes on Diffy Qs*, Table 8.1)

The node and spiral behavior of Table 8.1 is proved in `SpiralType.lean` for solutions tending to the critical point
as `t → ∞`.  For a source or spiral source (trace `> 0`) the solutions near the point tend to it as `t → -∞`.
Reversing time, `t ↦ (x(-t), y(-t))` solves the system with the field `(-f, -g)`, whose linearization has the opposite
matrix: trace `-(a + d)`, the same determinant and the same discriminant.  So the results for sinks give: solutions on
`t ≤ 0` starting near a source tend to it as `t → -∞`, winding around it (complex eigenvalues) or eventually staying on
one side of a line (distinct real eigenvalues) as `t → -∞`. -/

namespace UndergradKB.DifferentialEquations

open Filter Topology Set

/-- `(x, y)` solves `x' = f(x, y)`, `y' = g(x, y)` for all `t ≤ 0`. -/
def IsPlanarSolBack (f g : ℝ → ℝ → ℝ) (x y : ℝ → ℝ) : Prop :=
  ∀ t, t ≤ 0 → HasDerivAt x (f (x t) (y t)) t ∧ HasDerivAt y (g (x t) (y t)) t

/-- Time reversal: a solution on `t ≤ 0` gives a solution on `t ≥ 0` of the reversed system `(-f, -g)`. -/
theorem isPlanarSol_reverse {f g : ℝ → ℝ → ℝ} {x y : ℝ → ℝ} (h : IsPlanarSolBack f g x y) :
    IsPlanarSol (fun u v => -f u v) (fun u v => -g u v) (fun t => x (-t)) (fun t => y (-t)) := by
  intro t ht
  obtain ⟨hx, hy⟩ := h (-t) (by linarith)
  refine ⟨?_, ?_⟩
  · exact (hx.comp t (hasDerivAt_neg t)).congr_deriv (by ring)
  · exact (hy.comp t (hasDerivAt_neg t)).congr_deriv (by ring)

/-- The reversed field is almost linear with the opposite matrix. -/
theorem almost_linear_reverse {f g : ℝ → ℝ → ℝ} {x₀ y₀ a b c d : ℝ}
    (hlin : ∀ ε > 0, ∃ ρ > 0, ∀ u v, u ^ 2 + v ^ 2 < ρ ^ 2 →
      (f (x₀ + u) (y₀ + v) - (a * u + b * v)) ^ 2 + (g (x₀ + u) (y₀ + v) - (c * u + d * v)) ^ 2
        ≤ ε * (u ^ 2 + v ^ 2)) :
    ∀ ε > 0, ∃ ρ > 0, ∀ u v, u ^ 2 + v ^ 2 < ρ ^ 2 →
      ((fun u v => -f u v) (x₀ + u) (y₀ + v) - (-a * u + -b * v)) ^ 2 +
        ((fun u v => -g u v) (x₀ + u) (y₀ + v) - (-c * u + -d * v)) ^ 2 ≤ ε * (u ^ 2 + v ^ 2) := by
  intro ε hε
  obtain ⟨ρ, hρ, h⟩ := hlin ε hε
  refine ⟨ρ, hρ, fun u v huv => ?_⟩
  have := h u v huv
  calc _ = (f (x₀ + u) (y₀ + v) - (a * u + b * v)) ^ 2 + (g (x₀ + u) (y₀ + v) - (c * u + d * v)) ^ 2 := by
        ring
    _ ≤ _ := this

lemma tendsto_comp_neg_atTop {x : ℝ → ℝ} {p : ℝ} (h : Tendsto x atBot (𝓝 p)) :
    Tendsto (fun t => x (-t)) atTop (𝓝 p) :=
  h.comp tendsto_neg_atTop_atBot

lemma tendsto_atBot_of_comp_neg {x : ℝ → ℝ} {p : ℝ} (h : Tendsto (fun t => x (-t)) atTop (𝓝 p)) :
    Tendsto x atBot (𝓝 p) := by
  refine (h.comp tendsto_neg_atBot_atTop).congr fun t => ?_
  simp

/-- **Spiral sources wind (Lebl, Table 8.1), backward in time.**  At an almost linear critical point whose matrix has
complex eigenvalues, a solution on `t ≤ 0` tending to the point as `t → -∞` (and never equal to it) crosses every
line through the point at arbitrarily negative times. -/
@[kb "lebldiffyqs2026" "Table 8.1, p. 358"]
theorem spiral_point_winds_backward {f g : ℝ → ℝ → ℝ} {x₀ y₀ a b c d : ℝ}
    (hlin : ∀ ε > 0, ∃ ρ > 0, ∀ u v, u ^ 2 + v ^ 2 < ρ ^ 2 →
      (f (x₀ + u) (y₀ + v) - (a * u + b * v)) ^ 2 + (g (x₀ + u) (y₀ + v) - (c * u + d * v)) ^ 2
        ≤ ε * (u ^ 2 + v ^ 2))
    (hD : (a + d) ^ 2 < 4 * (a * d - b * c)) {x y : ℝ → ℝ} (hsol : IsPlanarSolBack f g x y)
    (hne : ∀ t, t ≤ 0 → ¬(x t = x₀ ∧ y t = y₀))
    (hx : Tendsto x atBot (𝓝 x₀)) (hy : Tendsto y atBot (𝓝 y₀)) {w₁ w₂ : ℝ}
    (hw : w₁ ≠ 0 ∨ w₂ ≠ 0) :
    ∀ T, ∃ t₁, t₁ ≤ T ∧ ∃ t₂, t₂ ≤ T ∧
      0 < w₁ * (y t₁ - y₀) - w₂ * (x t₁ - x₀) ∧ w₁ * (y t₂ - y₀) - w₂ * (x t₂ - x₀) < 0 := by
  have hD' : (-a + -d) ^ 2 < 4 * (-a * -d - -b * -c) := by nlinarith
  have H := spiral_point_winds (f := fun u v => -f u v) (g := fun u v => -g u v) (a := -a) (b := -b) (c := -c)
    (d := -d) (x := fun t => x (-t)) (y := fun t => y (-t)) (almost_linear_reverse hlin) hD' (isPlanarSol_reverse hsol)
    (fun t ht => hne (-t) (by linarith)) (tendsto_comp_neg_atTop hx) (tendsto_comp_neg_atTop hy) hw
  intro T
  obtain ⟨t₁, ht₁, t₂, ht₂, h1, h2⟩ := H (-T)
  exact ⟨-t₁, by linarith, -t₂, by linarith, h1, h2⟩

/-- **Sources and saddles with distinct real eigenvalues do not wind (Lebl, Table 8.1), backward in time.**  At an
almost linear critical point whose matrix has distinct real eigenvalues, a solution on `t ≤ 0` tending to the point
as `t → -∞` (and never equal to it) eventually (as `t → -∞`) stays on one side of some line through the point. -/
@[kb "lebldiffyqs2026" "Table 8.1, p. 358"]
theorem node_point_no_winding_backward {f g : ℝ → ℝ → ℝ} {x₀ y₀ a b c d : ℝ}
    (hlin : ∀ ε > 0, ∃ ρ > 0, ∀ u v, u ^ 2 + v ^ 2 < ρ ^ 2 →
      (f (x₀ + u) (y₀ + v) - (a * u + b * v)) ^ 2 + (g (x₀ + u) (y₀ + v) - (c * u + d * v)) ^ 2
        ≤ ε * (u ^ 2 + v ^ 2))
    (hD : 4 * (a * d - b * c) < (a + d) ^ 2) {x y : ℝ → ℝ} (hsol : IsPlanarSolBack f g x y)
    (hne : ∀ t, t ≤ 0 → ¬(x t = x₀ ∧ y t = y₀))
    (hx : Tendsto x atBot (𝓝 x₀)) (hy : Tendsto y atBot (𝓝 y₀)) :
    ∃ w₁ w₂ T : ℝ, (w₁ ≠ 0 ∨ w₂ ≠ 0) ∧
      ((∀ t, t ≤ T → 0 ≤ w₁ * (y t - y₀) - w₂ * (x t - x₀)) ∨
        (∀ t, t ≤ T → w₁ * (y t - y₀) - w₂ * (x t - x₀) ≤ 0)) := by
  have hD' : 4 * (-a * -d - -b * -c) < (-a + -d) ^ 2 := by nlinarith
  obtain ⟨w₁, w₂, T, hw, h⟩ := node_point_no_winding (f := fun u v => -f u v) (g := fun u v => -g u v) (a := -a)
    (b := -b) (c := -c) (d := -d) (x := fun t => x (-t)) (y := fun t => y (-t)) (almost_linear_reverse hlin) hD'
    (isPlanarSol_reverse hsol)
    (fun t ht => hne (-t) (by linarith)) (tendsto_comp_neg_atTop hx) (tendsto_comp_neg_atTop hy)
  refine ⟨w₁, w₂, -T, hw, ?_⟩
  rcases h with h | h
  · exact Or.inl fun t ht => by simpa using h (-t) (by linarith)
  · exact Or.inr fun t ht => by simpa using h (-t) (by linarith)

/-- **Sources and spiral sources (Lebl, Table 8.1, trace `> 0`, determinant `> 0`).**  Solutions on `t ≤ 0` starting
near the point and never equal to it tend to the point as `t → -∞`; with complex eigenvalues they cross every line
through the point at arbitrarily negative times (spiral source), with distinct real eigenvalues they eventually stay
on one side of a line (source). -/
@[kb "lebldiffyqs2026" "Table 8.1, p. 358"]
theorem almost_linear_type_source {f g : ℝ → ℝ → ℝ} {x₀ y₀ a b c d : ℝ}
    (hlin : ∀ ε > 0, ∃ ρ > 0, ∀ u v, u ^ 2 + v ^ 2 < ρ ^ 2 →
      (f (x₀ + u) (y₀ + v) - (a * u + b * v)) ^ 2 + (g (x₀ + u) (y₀ + v) - (c * u + d * v)) ^ 2
        ≤ ε * (u ^ 2 + v ^ 2))
    (htr : 0 < a + d) (hdet : 0 < a * d - b * c) :
    ((a + d) ^ 2 < 4 * (a * d - b * c) →
      ∃ δ > 0, ∀ x y : ℝ → ℝ, IsPlanarSolBack f g x y →
        (x 0 - x₀) ^ 2 + (y 0 - y₀) ^ 2 < δ ^ 2 → (∀ t, t ≤ 0 → ¬(x t = x₀ ∧ y t = y₀)) →
        Tendsto x atBot (𝓝 x₀) ∧ Tendsto y atBot (𝓝 y₀) ∧
        ∀ w₁ w₂ : ℝ, (w₁ ≠ 0 ∨ w₂ ≠ 0) → ∀ T, ∃ t₁, t₁ ≤ T ∧ ∃ t₂, t₂ ≤ T ∧
          0 < w₁ * (y t₁ - y₀) - w₂ * (x t₁ - x₀) ∧ w₁ * (y t₂ - y₀) - w₂ * (x t₂ - x₀) < 0) ∧
    (4 * (a * d - b * c) < (a + d) ^ 2 →
      ∃ δ > 0, ∀ x y : ℝ → ℝ, IsPlanarSolBack f g x y →
        (x 0 - x₀) ^ 2 + (y 0 - y₀) ^ 2 < δ ^ 2 → (∀ t, t ≤ 0 → ¬(x t = x₀ ∧ y t = y₀)) →
        Tendsto x atBot (𝓝 x₀) ∧ Tendsto y atBot (𝓝 y₀) ∧
        ∃ w₁ w₂ T : ℝ, (w₁ ≠ 0 ∨ w₂ ≠ 0) ∧
          ((∀ t, t ≤ T → 0 ≤ w₁ * (y t - y₀) - w₂ * (x t - x₀)) ∨
            (∀ t, t ≤ T → w₁ * (y t - y₀) - w₂ * (x t - x₀) ≤ 0))) := by
  have htr' : -a + -d < 0 := by linarith
  have hdet' : 0 < -a * -d - -b * -c := by linarith
  obtain ⟨H1, H2⟩ := almost_linear_type_sink (f := fun u v => -f u v) (g := fun u v => -g u v) (a := -a) (b := -b)
    (c := -c) (d := -d) (almost_linear_reverse hlin) htr' hdet'
  refine ⟨fun hD => ?_, fun hD => ?_⟩
  · have hD' : (-a + -d) ^ 2 < 4 * (-a * -d - -b * -c) := by nlinarith
    obtain ⟨δ, hδ, H⟩ := H1 hD'
    refine ⟨δ, hδ, fun x y hsol h0 hne => ?_⟩
    obtain ⟨hx, hy, hw⟩ := H _ _ (isPlanarSol_reverse hsol) (by simpa using h0)
      (fun t ht => hne (-t) (by linarith))
    refine ⟨tendsto_atBot_of_comp_neg hx, tendsto_atBot_of_comp_neg hy, fun w₁ w₂ hw' T => ?_⟩
    obtain ⟨t₁, ht₁, t₂, ht₂, h1, h2⟩ := hw w₁ w₂ hw' (-T)
    exact ⟨-t₁, by linarith, -t₂, by linarith, h1, h2⟩
  · have hD' : 4 * (-a * -d - -b * -c) < (-a + -d) ^ 2 := by nlinarith
    obtain ⟨δ, hδ, H⟩ := H2 hD'
    refine ⟨δ, hδ, fun x y hsol h0 hne => ?_⟩
    obtain ⟨hx, hy, w₁, w₂, T, hw, h⟩ := H _ _ (isPlanarSol_reverse hsol) (by simpa using h0)
      (fun t ht => hne (-t) (by linarith))
    refine ⟨tendsto_atBot_of_comp_neg hx, tendsto_atBot_of_comp_neg hy, w₁, w₂, -T, hw, ?_⟩
    rcases h with h | h
    · exact Or.inl fun t ht => by simpa using h (-t) (by linarith)
    · exact Or.inr fun t ht => by simpa using h (-t) (by linarith)

end UndergradKB.DifferentialEquations
