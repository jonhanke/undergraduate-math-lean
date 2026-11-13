import Mathlib.Logic.Function.Basic
import UndergradKB.Common

/-!
# Course layer: Levin, Discrete Mathematics, Chapter 1, worked examples
-/

namespace UndergradKB.Foundations.Course

/-- Levin Example 1.3.11: `(P ∨ Q) → R` implies `(P → R) ∨ (Q → R)`, but the two statements are not logically
equivalent. -/
@[kb "levin2025" "Example 1.3.11, p. 71"]
theorem levin_ex_1_3_11_not_equivalent :
    (∀ P Q R : Prop, ((P ∨ Q) → R) → ((P → R) ∨ (Q → R))) ∧
    ¬ ∀ P Q R : Prop, ((P ∨ Q) → R) ↔ ((P → R) ∨ (Q → R)) := by
  constructor
  · intro P Q R h
    by_cases hP : P
    · exact Or.inl (fun _ => h (Or.inl hP))
    · by_cases hQ : Q
      · exact Or.inr (fun _ => h (Or.inr hQ))
      · exact Or.inl (fun hp => absurd hp hP)
  · intro h
    exact (h True False False).mpr (Or.inr fun x => x) (Or.inl trivial)

end UndergradKB.Foundations.Course
