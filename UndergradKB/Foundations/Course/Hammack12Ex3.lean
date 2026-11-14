import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import UndergradKB.Common

/-!
# Course layer: Hammack, Book of Proof, Chapter 12, worked examples (wave 4)

Functions are encoded as their graphs, finite subsets of `ℕ × ℕ`.
-/

namespace UndergradKB.Foundations.Course

/-- Hammack Example 12.9: with `A = {a, b, c}` (encoded `0, 1, 2`), `B = {0, 1}`, `C = {1, 2, 3}`, the sets
`f = {(a,0), (b,1), (c,0)}` and `g = {(1,0), (2,1), (3,1)}` are functions `A → B` and `C → B`, but the codomain `B`
of `f` is neither equal to nor contained in the domain `C` of `g`, so `g ∘ f` is not defined. -/
@[kb "hammack2018" "Example 12.9, p. 248"]
theorem hammack_ex_12_9_composition_undefined :
    let A : Finset ℕ := {0, 1, 2}
    let B : Finset ℕ := {0, 1}
    let C : Finset ℕ := {1, 2, 3}
    let f : Finset (ℕ × ℕ) := {(0, 0), (1, 1), (2, 0)}
    let g : Finset (ℕ × ℕ) := {(1, 0), (2, 1), (3, 1)}
    (∀ a ∈ A, ∃! b, b ∈ B ∧ (a, b) ∈ f) ∧ (∀ p ∈ f, p.1 ∈ A) ∧
    (∀ c ∈ C, ∃! b, b ∈ B ∧ (c, b) ∈ g) ∧ (∀ p ∈ g, p.1 ∈ C) ∧
    B ≠ C ∧ ¬ B ⊆ C := by
  intro A B C f g
  refine ⟨?_, by decide, ?_, by decide, by decide, by decide⟩
  · intro a ha
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact ⟨0, by decide, fun b hb => by simp [B, f] at hb; omega⟩
    · exact ⟨1, by decide, fun b hb => by simp [B, f] at hb; omega⟩
    · exact ⟨0, by decide, fun b hb => by simp [B, f] at hb; omega⟩
  · intro c hc
    simp only [C, Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl
    · exact ⟨0, by decide, fun b hb => by simp [B, g] at hb; omega⟩
    · exact ⟨1, by decide, fun b hb => by simp [B, g] at hb; omega⟩
    · exact ⟨1, by decide, fun b hb => by simp [B, g] at hb; omega⟩

end UndergradKB.Foundations.Course
