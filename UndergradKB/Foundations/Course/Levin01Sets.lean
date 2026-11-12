import Mathlib.Basic.Logic.Basic
import UndergradKB.Common

/-!
# Course layer: Levin, Discrete Mathematics, Chapter 1 (logic)

Thin theorems for logic rows of the Foundations checklist that only Levin states and that are in Mathlib.
-/

namespace UndergradKB.Foundations.Course

/-- FO-040. An implication `P → Q` is the same as `¬P ∨ Q`. -/
@[kb "levin2025" "Sec 1.3.3, p. 70"]
theorem levin_s1_3_3_imp_iff_not_or (P Q : Prop) : (P → Q) ↔ (¬P ∨ Q) :=
  imp_iff_not_or

/-- FO-049. Double negation: `¬¬P` is equivalent to `P`. -/
@[kb "levin2025" "Sec 1.3.3, p. 70"]
theorem levin_s1_3_3_double_negation (P : Prop) : ¬¬P ↔ P :=
  not_not

end UndergradKB.Foundations.Course
