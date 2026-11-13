import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Insert
import Mathlib.Logic.Relation
import UndergradKB.Common

/-!
# Course layer: Hammack, Book of Proof, Chapter 11, worked examples
-/

namespace UndergradKB.Foundations.Course

/-- Hammack Example 11.7: on `A = {b, c, d, e}` (encoded `0, 1, 2, 3`) the relation consisting of the nine pairs
among `b, c, d` is symmetric and transitive but not reflexive. -/
@[kb "hammack2018" "Example 11.7, p. 218"]
theorem hammack_ex_11_7_relation_properties (R : Fin 4 → Fin 4 → Prop)
    (hR : ∀ x y, R x y ↔ (x, y) ∈
      ({(0, 0), (0, 1), (1, 0), (1, 1), (2, 2), (0, 2), (2, 0), (1, 2), (2, 1)} :
        Finset (Fin 4 × Fin 4))) :
    ¬ (∀ x, R x x) ∧ (∀ x y, R x y → R y x) ∧ (∀ x y z, R x y → R y z → R x z) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have := (hR 3 3).mp (h 3)
    revert this
    decide
  · simp only [hR]
    decide
  · simp only [hR]
    decide

end UndergradKB.Foundations.Course
