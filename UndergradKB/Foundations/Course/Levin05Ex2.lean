import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Insert
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FinCases
import UndergradKB.Common

/-!
# Course layer: Levin, Discrete Mathematics, Chapter 5, worked examples (second batch)
-/

namespace UndergradKB.Foundations.Course

/-- Levin Example 5.1.4: for `A = {1..6}`, `B = {2,4,6}`, `C = {1,2,3}`, the statements
`A ⊂ B` fails, `B ⊂ A`, `∅ ⊂ A`, `3 ∈ C`, `{3} ⊂ C` hold. -/
@[kb "levin2025" "Example 5.1.4, p. 413"]
theorem levin_ex_5_1_4_subset_statements :
    let A : Finset ℕ := {1, 2, 3, 4, 5, 6}
    let B : Finset ℕ := {2, 4, 6}
    let C : Finset ℕ := {1, 2, 3}
    ¬ (A ⊂ B) ∧ B ⊂ A ∧ (∅ : Finset ℕ) ⊂ A ∧ 3 ∈ C ∧ ({3} : Finset ℕ) ⊂ C := by
  decide +kernel

/-- Levin Example 5.1.8: adding 4 to `{1,2,3}` and removing 2 gives new sets and leaves the
original unchanged. -/
@[kb "levin2025" "Example 5.1.8, p. 417"]
theorem levin_ex_5_1_8_add_remove :
    let A : Finset ℕ := {1, 2, 3}
    A ∪ {4} = {1, 2, 3, 4} ∧ A \ {2} = {1, 3} ∧ 4 ∈ A ∪ {4} ∧ 4 ∉ A := by
  decide +kernel

/-- Levin Example 5.2.1: tripling on `ℤ` has range the multiples of 3; `g` sending `1 ↦ c`,
`2 ↦ a`, `3 ↦ a` (letters `a, b, c` as `0, 1, 2`) has range `{a, c}`; the table function
`h` sending `1,2,3,4` to `3,6,9,12` is `x ↦ 3x`. -/
@[kb "levin2025" "Example 5.2.1, p. 423"]
theorem levin_ex_5_2_1_function_ranges :
    Set.range (fun n : ℤ => 3 * n) = {m : ℤ | 3 ∣ m} ∧
      Set.range (![2, 0, 0] : Fin 3 → Fin 3) = {0, 2} ∧
      ∀ x : Fin 4, (![3, 6, 9, 12] : Fin 4 → ℕ) x = 3 * (x.val + 1) := by
  refine ⟨?_, ?_, by decide⟩
  · ext m
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨n, rfl⟩
  · ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩

/-- Levin Example 5.2.4: for `f 0 = 0` and `f (n+1) = f n + 2n + 1`, the value `f 6` is 36. -/
@[kb "levin2025" "Example 5.2.4, p. 427"]
theorem levin_ex_5_2_4_recursive_value (f : ℕ → ℕ) (h0 : f 0 = 0)
    (h : ∀ n, f (n + 1) = f n + 2 * n + 1) : f 6 = 36 := by
  have h1 : f 1 = 1 := by rw [h 0, h0]
  have h2 : f 2 = 4 := by rw [h 1, h1]
  have h3 : f 3 = 9 := by rw [h 2, h2]
  have h4 : f 4 = 16 := by rw [h 3, h3]
  have h5 : f 5 = 25 := by rw [h 4, h4]
  rw [h 5, h5]

/-- Levin Example 5.2.10: the only function from `{1,..,5}` to `ℕ` with five elements in the
preimage of 7 is the constant function 7. -/
@[kb "levin2025" "Example 5.2.10, p. 433"]
theorem levin_ex_5_2_10_preimage_size (f : Fin 5 → ℕ) :
    (Finset.univ.filter (fun i => f i = 7)).card = 5 ↔ f = fun _ => 7 := by
  constructor
  · intro h
    have hu : Finset.univ.filter (fun i => f i = 7) = Finset.univ :=
      Finset.eq_univ_of_card _ (by simpa using h)
    funext i
    have : i ∈ Finset.univ.filter (fun i => f i = 7) := by rw [hu]; exact Finset.mem_univ i
    simpa using this
  · rintro rfl
    simp

end UndergradKB.Foundations.Course
