import Mathlib.Data.Set.Basic
import Mathlib.Order.Setoid.Partition
import Mathlib.Data.Int.ModEq
import Mathlib.Logic.Function.Basic
import UndergradKB.Common.Attr

/-! # Judson–Beezer, chapter 1: preliminaries (course layer)

Thin wrappers around Mathlib for the results of chapter 1 on sets, maps and equivalence relations. -/

namespace UndergradKB.AbstractAlgebra.Course

/-- AA-001. Union and intersection of sets are associative, commutative and distribute over each
other. -/
@[kb "judson2026" "Proposition 1.2.2, p. 17"]
theorem judson_1_2_2 {α : Type*} (A B C : Set α) :
    A ∪ (B ∪ C) = (A ∪ B) ∪ C ∧ A ∩ (B ∩ C) = (A ∩ B) ∩ C ∧
    A ∪ B = B ∪ A ∧ A ∩ B = B ∩ A ∧
    A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) ∧ A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) :=
  ⟨(Set.union_assoc A B C).symm, (Set.inter_assoc A B C).symm, Set.union_comm A B,
    Set.inter_comm A B, Set.inter_union_distrib_left A B C, Set.union_inter_distrib_left A B C⟩

/-- AA-002. De Morgan's laws: the complement of a union is the intersection of complements, and the
complement of an intersection is the union of complements. -/
@[kb "judson2026" "Theorem 1.2.3, p. 18"]
theorem judson_1_2_3 {α : Type*} (A B : Set α) :
    (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ ∧ (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ :=
  ⟨Set.compl_union A B, Set.compl_inter A B⟩

/-- AA-005. Composition of maps is associative. -/
@[kb "judson2026" "Theorem 1.2.15, p. 21"]
theorem judson_1_2_15 {α β γ δ : Type*} (f : α → β) (g : β → γ) (h : γ → δ) :
    h ∘ (g ∘ f) = (h ∘ g) ∘ f :=
  Function.comp_assoc h g f

/-- AA-006. A map is invertible (has a two-sided inverse) exactly when it is one-to-one and onto. -/
@[kb "judson2026" "Theorem 1.2.20, p. 23"]
theorem judson_1_2_20 {α β : Type*} (f : α → β) :
    Function.Bijective f ↔ ∃ g : β → α, Function.LeftInverse g f ∧ Function.RightInverse g f :=
  Function.bijective_iff_has_inverse

/-- AA-009. The equivalence classes of an equivalence relation partition the set. -/
@[kb "judson2026" "Theorem 1.2.25, p. 24"]
theorem judson_1_2_25 {α : Type*} (r : Setoid α) : Setoid.IsPartition r.classes :=
  Setoid.isPartition_classes r

/-- AA-009. Two equivalence classes are either equal or disjoint. -/
@[kb "judson2026" "Corollary 1.2.26, p. 25"]
theorem judson_1_2_26 {α : Type*} (r : Setoid α) {s t : Set α} (hs : s ∈ r.classes)
    (ht : t ∈ r.classes) : s = t ∨ Disjoint s t := by
  by_cases h : Disjoint s t
  · exact Or.inr h
  · left
    obtain ⟨a, has, hat⟩ := Set.not_disjoint_iff.mp h
    exact Setoid.eq_of_mem_classes hs has ht hat

/-- AA-010. Congruence modulo `n` is an equivalence relation on the integers. -/
@[kb "judson2026" "Example 1.2.30, p. 25"]
theorem judson_1_2_30 (n : ℤ) : Equivalence (Int.ModEq n) :=
  ⟨fun a => Int.ModEq.refl a, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

end UndergradKB.AbstractAlgebra.Course
