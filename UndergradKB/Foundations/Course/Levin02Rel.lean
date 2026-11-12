import Mathlib.Basic.Rel
import Mathlib.Order.Basic
import UndergradKB.Common

/-!
# Course layer: Levin, Discrete Mathematics, Chapter 2 (relations)

Thin theorems for relation rows of the Foundations checklist that only Levin states and that are in Mathlib.
-/

namespace UndergradKB.Foundations.Course

/-- FO-074. A partial order is reflexive, antisymmetric and transitive. -/
@[kb "levin2025" "Remark 2.6.15, p. 193"]
theorem levin_rem_2_6_15_partial_order {α : Type*} [PartialOrder α] :
    (∀ a : α, a ≤ a) ∧ (∀ a b : α, a ≤ b → b ≤ a → a = b) ∧ (∀ a b c : α, a ≤ b → b ≤ c → a ≤ c) :=
  ⟨le_refl, fun _ _ => le_antisymm, fun _ _ _ => le_trans⟩

/-- FO-075. A relation is symmetric iff it equals its inverse. -/
@[kb "levin2025" "Text §2.6.3, p. 192"]
theorem levin_s2_6_3_symmetric_iff_inv_eq {α : Type*} (R : SetRel α α) : R.inv = R ↔ R.IsSymm :=
  SetRel.inv_eq_self_iff

/-- FO-077. `(a, c)` is in the composite `S ∘ R` when some `b` has `(a, b)` in `R` and `(b, c)` in `S`
(Mathlib's `R ○ S` applies `R` first). -/
@[kb "levin2025" "Def 2.6.7, p. 188"]
theorem levin_def_2_6_7_comp {α β γ : Type*} (R : SetRel α β) (S : SetRel β γ) (a : α) (c : γ) :
    (a, c) ∈ R.comp S ↔ ∃ b, (a, b) ∈ R ∧ (b, c) ∈ S :=
  SetRel.mem_comp

end UndergradKB.Foundations.Course
