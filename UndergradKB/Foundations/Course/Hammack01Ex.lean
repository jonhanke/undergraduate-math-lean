import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Group.Int.Defs
import UndergradKB.Common

/-!
# Course layer: Hammack, Book of Proof, Chapter 1, worked examples
-/

namespace UndergradKB.Foundations.Course

/-- Hammack Example 1.2: the set `{7a + 3b : a, b ∈ ℤ}` is all of `ℤ`. -/
@[kb "hammack2018" "Example 1.2, p. 18"]
theorem hammack_ex_1_2_seven_three_integers :
    {x : ℤ | ∃ a b : ℤ, x = 7 * a + 3 * b} = Set.univ := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact ⟨x, -2 * x, by ring⟩

end UndergradKB.Foundations.Course
