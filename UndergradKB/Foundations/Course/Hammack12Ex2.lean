import Mathlib.Data.Set.Basic
import Mathlib.Data.Int.NatAbs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
import UndergradKB.Common

/-!
# Course layer: Hammack, Book of Proof, Chapter 12, further worked examples
-/

namespace UndergradKB.Foundations.Course

/-- Hammack Example 12.1: the set of pairs `{(n, |n| + 2)}` in `ℤ × ℕ` is the graph of a function, since every
integer is the first coordinate of exactly one pair; it contains `(1, 3)` and `(-3, 5)`. -/
@[kb "hammack2018" "Example 12.1, p. 236"]
theorem hammack_ex_12_1_abs_plus_two_graph :
    let f : Set (ℤ × ℕ) := {p | p.2 = p.1.natAbs + 2}
    (∀ a : ℤ, ∃! b : ℕ, (a, b) ∈ f) ∧ (1, 3) ∈ f ∧ ((-3 : ℤ), 5) ∈ f := by
  intro f
  refine ⟨fun a => ⟨a.natAbs + 2, rfl, fun b hb => hb⟩, rfl, rfl⟩

/-- Hammack Example 12.2: the set of pairs `{(p,0), (q,1), (r,2), (s,2)}` in `A × B` (with `A = {p,q,r,s}` encoded
`0..3` and `B = {0,1,2}`) is the graph of a function, since each element of `A` is the first coordinate of exactly one
pair; its range is all of `B`. -/
@[kb "hammack2018" "Example 12.2, p. 237"]
theorem hammack_ex_12_2_small_function :
    let f : Finset (Fin 4 × Fin 3) := {(0, 0), (1, 1), (2, 2), (3, 2)};
    (∀ a : Fin 4, ∃ b : Fin 3, (a, b) ∈ f ∧ ∀ b' : Fin 3, (a, b') ∈ f → b' = b) ∧ (∀ b : Fin 3, ∃ a : Fin 4, (a, b) ∈ f) := by
  intro f
  exact ⟨by decide, by decide⟩

end UndergradKB.Foundations.Course
