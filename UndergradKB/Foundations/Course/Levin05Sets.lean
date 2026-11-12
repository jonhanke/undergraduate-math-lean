import Mathlib.Data.Set.Basic
import UndergradKB.Common

/-!
# Course layer: Levin, Discrete Mathematics, Chapter 5 (sets)

Thin theorems for set rows of the Foundations checklist that only Levin states and that are in Mathlib.
-/

namespace UndergradKB.Foundations.Course

/-- FO-013. `A ⊂ B` means `A ⊆ B` and `A ≠ B`. -/
@[kb "levin2025" "Sec 5.1.2, p. 413"]
theorem levin_s5_1_2_proper_subset {α : Type*} (A B : Set α) : A ⊂ B ↔ A ⊆ B ∧ A ≠ B :=
  ⟨fun h => ⟨h.subset, h.ne⟩, fun h => h.1.ssubset_of_ne h.2⟩

/-- FO-022. The difference `A \ B` equals `A` intersected with the complement of `B`. -/
@[kb "levin2025" "Sec 5.1.3, p. 416"]
theorem levin_s5_1_3_diff_eq_inter_compl {α : Type*} (A B : Set α) : A \ B = A ∩ Bᶜ :=
  rfl

end UndergradKB.Foundations.Course
