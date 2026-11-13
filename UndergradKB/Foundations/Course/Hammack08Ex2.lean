import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Tactic.NormNum
import UndergradKB.Common

/-!
# Course layer: Hammack, Book of Proof, Chapter 8, worked examples on membership in set-builder sets
-/

namespace UndergradKB.Foundations.Course

/-- Hammack Example 8.1: in `A = {x ∈ ℕ : 7 ∣ x}` the numbers `7, 14, 21, 28, 35` are members while `8` is not. -/
@[kb "hammack2018" "Example 8.1, p. 170"]
theorem hammack_ex_8_1_multiples_of_seven :
    let A : Set ℕ := {x | 7 ∣ x}
    7 ∈ A ∧ 14 ∈ A ∧ 21 ∈ A ∧ 28 ∈ A ∧ 35 ∈ A ∧ 8 ∉ A := by
  intro A
  simp only [A, Set.mem_ofPred_eq]
  decide

/-- Hammack Example 8.2: among finite sets of naturals, `{4, 13, 45}`, `{1, 2, 3}` and `{10, 854, 3}` have exactly three
elements and so belong to `{X : |X| = 3}`, while `{1, 2, 3, 4}` does not. -/
@[kb "hammack2018" "Example 8.2, p. 170"]
theorem hammack_ex_8_2_three_element_sets :
    let A : Set (Finset ℕ) := {X | X.card = 3}
    ({4, 13, 45} : Finset ℕ) ∈ A ∧ ({1, 2, 3} : Finset ℕ) ∈ A ∧ ({10, 854, 3} : Finset ℕ) ∈ A ∧
      ({1, 2, 3, 4} : Finset ℕ) ∉ A := by
  intro A
  simp only [A, Set.mem_ofPred_eq]
  decide

/-- Hammack Example 8.4: in `C = {3x³ + 2 : x ∈ ℤ}` the numbers `-22`, `-1` and `5` occur (at `x = -2, -1, 1`), while
`0` and `12` do not. -/
@[kb "hammack2018" "Example 8.4, p. 171"]
theorem hammack_ex_8_4_three_cubed_plus_two :
    let C : Set ℤ := {y | ∃ x : ℤ, y = 3 * x ^ 3 + 2};
    -22 ∈ C ∧ -1 ∈ C ∧ 5 ∈ C ∧ 0 ∉ C ∧ 12 ∉ C := by
  intro C
  refine ⟨⟨-2, by norm_num⟩, ⟨-1, by norm_num⟩, ⟨1, by norm_num⟩, ?_, ?_⟩
  · rintro ⟨x, hx⟩
    generalize x ^ 3 = t at hx
    omega
  · rintro ⟨x, hx⟩
    generalize x ^ 3 = t at hx
    omega

end UndergradKB.Foundations.Course
