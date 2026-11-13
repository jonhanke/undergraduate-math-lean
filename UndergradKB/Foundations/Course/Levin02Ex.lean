import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import UndergradKB.Common

/-!
# Course layer: Levin, Discrete Mathematics, Chapter 2, worked examples
-/

namespace UndergradKB.Foundations.Course

/-- Levin Example 2.1.10: a graph on 7 vertices with degree sequence `(4,4,3,3,3,2,1)` has 10 edges. -/
@[kb "levin2025" "Example 2.1.10, p. 128"]
theorem levin_ex_2_1_10_edges_from_degrees (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj]
    (h : ∀ v, G.degree v = (![4, 4, 3, 3, 3, 2, 1] : Fin 7 → ℕ) v) :
    G.edgeFinset.card = 10 := by
  have := G.sum_degrees_eq_twice_card_edges
  simp only [h, Fin.sum_univ_succ] at this
  simp at this
  omega

/-- Levin Example 2.1.11: no graph on 9 vertices has every vertex of degree 7. -/
@[kb "levin2025" "Example 2.1.11, p. 129"]
theorem levin_ex_2_1_11_no_regular_nine_seven (G : SimpleGraph (Fin 9)) [DecidableRel G.Adj] :
    ¬ G.IsRegularOfDegree 7 := by
  intro h
  have := G.sum_degrees_eq_twice_card_edges
  simp [h.degree_eq] at this
  omega

/-- Levin Example 2.5.3: the complete graph on 6 vertices has chromatic number 6. -/
@[kb "levin2025" "Example 2.5.3, p. 173"]
theorem levin_ex_2_5_3_k6_chromatic_number :
    (⊤ : SimpleGraph (Fin 6)).chromaticNumber = 6 := by
  rw [SimpleGraph.chromaticNumber_top]
  simp

end UndergradKB.Foundations.Course
