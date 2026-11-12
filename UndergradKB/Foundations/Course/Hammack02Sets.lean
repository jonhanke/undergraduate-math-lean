import Mathlib.Basic.Logic.Basic
import Mathlib.Data.Set.Basic
import UndergradKB.Common

/-!
# Course layer: Hammack, Book of Proof, Chapter 2 (logic)

Thin theorems in the book's terms for the logic rows of the Foundations checklist that are already in Mathlib.
-/

namespace UndergradKB.Foundations.Course

/-- FO-044. Contrapositive law: `P → Q` is equivalent to `¬Q → ¬P`. -/
@[kb "hammack2018" "Eq (2.1), p. 64", kb "levin2025" "Theorem 1.3.6, p. 68"]
theorem hammack_eq_2_1_contrapositive (P Q : Prop) : (P → Q) ↔ (¬Q → ¬P) :=
  not_imp_not.symm

/-- FO-045. De Morgan's laws for a conjunction and a disjunction. -/
@[kb "hammack2018" "Fact 2.1, p. 63", kb "hammack2018" "Eq (2.2), p. 64", kb "levin2025" "Theorem 1.3.8, p. 69"]
theorem hammack_fact_2_1_de_morgan (P Q : Prop) :
    (¬(P ∧ Q) ↔ ¬P ∨ ¬Q) ∧ (¬(P ∨ Q) ↔ ¬P ∧ ¬Q) :=
  ⟨not_and_or, not_or⟩

/-- FO-046. Conjunction and disjunction are commutative. -/
@[kb "hammack2018" "Eq (2.3), p. 64"]
theorem hammack_eq_2_3_comm (P Q : Prop) : (P ∧ Q ↔ Q ∧ P) ∧ (P ∨ Q ↔ Q ∨ P) :=
  ⟨and_comm, or_comm⟩

/-- FO-047. Each of "and" and "or" distributes over the other. -/
@[kb "hammack2018" "Eq (2.4), p. 64"]
theorem hammack_eq_2_4_distrib (P Q R : Prop) :
    (P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R)) ∧ (P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R)) :=
  ⟨and_or_left, or_and_left⟩

/-- FO-048. Conjunction and disjunction are associative. -/
@[kb "hammack2018" "Eq (2.5), p. 64"]
theorem hammack_eq_2_5_assoc (P Q R : Prop) :
    ((P ∧ Q) ∧ R ↔ P ∧ (Q ∧ R)) ∧ ((P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R)) :=
  ⟨and_assoc, or_assoc⟩

/-- FO-050. The negation of `P → Q` says `P` holds and `Q` fails. -/
@[kb "hammack2018" "Eq (2.10), p. 73", kb "levin2025" "Theorem 1.3.10, p. 71"]
theorem hammack_eq_2_10_not_imp (P Q : Prop) : ¬(P → Q) ↔ P ∧ ¬Q :=
  Classical.not_imp

/-- FO-054. Negating a universal statement gives an existential one, and conversely. -/
@[kb "hammack2018" "Eq (2.8), p. 72", kb "hammack2018" "Eq (2.9), p. 72", kb "levin2025" "Sec 1.3.4, p. 72"]
theorem hammack_eq_2_8_negate_quantifiers {α : Type*} (X : Set α) (P : α → Prop) :
    ((¬ ∀ x, P x) ↔ ∃ x, ¬ P x) ∧ ((¬ ∃ x, P x) ↔ ∀ x, ¬ P x) ∧
      ((¬ ∀ x ∈ X, P x) ↔ ∃ x ∈ X, ¬ P x) :=
  ⟨not_forall, not_exists, by simp⟩

end UndergradKB.Foundations.Course
