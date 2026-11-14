import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Order.Fin.Basic
import UndergradKB.Common

/-!
# Course layer: Levin, Discrete Mathematics, Chapter 3, worked examples (wave 4)
-/

namespace UndergradKB.Foundations.Course

/-- Levin Example 3.5.3: three handfuls of ten jelly beans over six flavors (R,G,B,Y,P,O = `0..5`), as
multisets of flavors, correspond to the number strings `2,3,4,1,0,0`, `10,0,0,0,0,0`, `1,1,1,1,1,5`
(count of each flavor); each has total 10. -/
@[kb "levin2025" "Example 3.5.3, p. 268"]
theorem levin_ex_3_5_3_jelly_beans :
    let m1 : Multiset (Fin 6) := {0, 0, 1, 1, 1, 2, 2, 2, 2, 3}
    let m2 : Multiset (Fin 6) := {0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    let m3 : Multiset (Fin 6) := {0, 1, 2, 3, 4, 5, 5, 5, 5, 5}
    Multiset.card m1 = 10 ∧ Multiset.card m2 = 10 ∧ Multiset.card m3 = 10 ∧
    (List.finRange 6).map (fun f => m1.count f) = [2, 3, 4, 1, 0, 0] ∧
    (List.finRange 6).map (fun f => m2.count f) = [10, 0, 0, 0, 0, 0] ∧
    (List.finRange 6).map (fun f => m3.count f) = [1, 1, 1, 1, 1, 5] := by
  decide

/-- Levin Example 3.5.4: twelve identical books on five shelves, given as strings of five shelf counts
`3,3,3,2,1`, `0,0,12,0,0`, `1,1,1,1,8` (each sums to 12), with the corresponding multisets of shelf
labels `{1,1,1,2,2,2,3,3,4,5}`, `{3 twelve times}`, `{1,2,3,4,5,5,5,5,5,5,5,5}`. -/
@[kb "levin2025" "Example 3.5.4, p. 268"]
theorem levin_ex_3_5_4_books_on_shelves :
    ([3, 3, 3, 2, 1] : List ℕ).sum = 12 ∧ ([0, 0, 12, 0, 0] : List ℕ).sum = 12 ∧
    ([1, 1, 1, 1, 8] : List ℕ).sum = 12 ∧
    (List.finRange 5).map (fun f => ({0, 0, 0, 1, 1, 1, 2, 2, 3, 4} : Multiset (Fin 5)).count f) =
      [3, 3, 2, 1, 1] := by
  decide

/-- Levin Example 3.8.9: distributing 3 different games to 5 friends with no friend getting two is counting
injective functions `Fin 3 → Fin 5`, of which there are `P(5,3) = 60` (out of `5^3 = 125` functions);
distributing 8 different games with no restriction counts all functions `Fin 8 → Fin 5`, namely `5^8`. -/
@[kb "levin2025" "Example 3.8.9, p. 317"]
theorem levin_ex_3_8_9_gifts_as_functions :
    Fintype.card (Fin 3 → Fin 5) = 125 ∧ Fintype.card (Fin 3 ↪ Fin 5) = 60 ∧
    Fintype.card (Fin 8 → Fin 5) = 5 ^ 8 := by
  refine ⟨by rw [Fintype.card_fun]; simp, ?_, by rw [Fintype.card_fun]; simp⟩
  rw [Fintype.card_embedding_eq]
  simp [Nat.descFactorial]

end UndergradKB.Foundations.Course
