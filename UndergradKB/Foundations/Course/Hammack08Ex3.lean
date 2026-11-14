import Mathlib.Data.Int.ModEq
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Ring
import UndergradKB.Common

/-!
# Course layer: Hammack, Book of Proof, Chapter 8, worked examples (wave 4)
-/

namespace UndergradKB.Foundations.Course

/-- Hammack Example 8.3: in the set `B` of integer pairs `(x, y)` with `x ≡ y (mod 5)`, the pairs `(8, 23)`,
`(100, 75)`, `(102, 77)` belong, `(6, 10)` does not, and `(4n + 3, 9n - 2)` belongs for every integer `n`. -/
@[kb "hammack2018" "Example 8.3, p. 171"]
theorem hammack_ex_8_3_congruence_pairs :
    let B : Set (ℤ × ℤ) := {p | p.1 ≡ p.2 [ZMOD 5]}
    (8, 23) ∈ B ∧ (100, 75) ∈ B ∧ (102, 77) ∈ B ∧ (6, 10) ∉ B ∧ ∀ n : ℤ, (4 * n + 3, 9 * n - 2) ∈ B := by
  intro B
  refine ⟨by decide, by decide, by decide, by decide, fun n => ?_⟩
  have h : (4 * n + 3) ≡ (9 * n - 2) [ZMOD 5] := by
    symm
    rw [Int.modEq_iff_dvd]
    exact ⟨1 - n, by ring⟩
  exact h

end UndergradKB.Foundations.Course
