import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Int.Lemmas
import Mathlib.Order.WellFounded
import Mathlib.Tactic.Linarith
import UndergradKB.Common

/-!
# Course layer: Hammack, Book of Proof, Chapter 1 (sets)

Thin theorems in the book's terms for the rows of the Foundations checklist (section "Sets and logic") that are
already in Mathlib.
-/

namespace UndergradKB.Foundations.Course

/-- FO-002. Two sets are equal exactly when they have the same members. -/
@[kb "hammack2018" "Def §1.1, p. 15", kb "levin2025" "Sec 0.2.2, p. 26"]
theorem hammack_s1_1_set_ext {α : Type*} (A B : Set α) : A = B ↔ ∀ x, x ∈ A ↔ x ∈ B :=
  Set.ext_iff

/-- FO-005. A finite set has no elements exactly when its size is zero. -/
@[kb "hammack2018" "Def §1.1, p. 16", kb "levin2025" "Sec 5.1.2, p. 414"]
theorem hammack_s1_1_card_eq_zero {α : Type*} (A : Finset α) : A.card = 0 ↔ A = ∅ :=
  Finset.card_eq_zero

/-- FO-006. The empty set has no members, and it is different from the set whose only member is the empty set. -/
@[kb "hammack2018" "Def §1.1, p. 16", kb "levin2025" "Sec 5.1.1, p. 410"]
theorem hammack_s1_1_empty_ne_singleton_empty {α : Type*} :
    (∀ x : α, x ∉ (∅ : Set α)) ∧ (∅ : Set (Set α)) ≠ {∅} :=
  ⟨fun _ => id, (Set.singleton_ne_empty _).symm⟩

/-- FO-009. A pair lies in `A × B` iff its first entry is in `A` and its second is in `B`. -/
@[kb "hammack2018" "Def 1.2, p. 20", kb "levin2025" "Sec 5.1.3, p. 417"]
theorem hammack_def_1_2_mem_prod {α β : Type*} (A : Set α) (B : Set β) (p : α × β) :
    p ∈ A ×ˢ B ↔ p.1 ∈ A ∧ p.2 ∈ B :=
  Set.mem_prod

/-- FO-010. For finite sets, the size of `A × B` is `|A| |B|`. -/
@[kb "hammack2018" "Fact 1.1, p. 21", kb "levin2025" "Example 5.1.9, p. 417"]
theorem hammack_fact_1_1_card_prod {α β : Type*} (A : Finset α) (B : Finset β) :
    (A ×ˢ B).card = A.card * B.card :=
  Finset.card_product A B

/-- FO-012. `A ⊆ B` means every element of `A` is in `B`; every set is a subset of itself. -/
@[kb "hammack2018" "Def 1.3, p. 24", kb "levin2025" "Sec 5.1.2, p. 413"]
theorem hammack_def_1_3_subset {α : Type*} (A B : Set α) :
    (A ⊆ B ↔ ∀ x, x ∈ A → x ∈ B) ∧ A ⊆ A :=
  ⟨Iff.of_eq Set.subset_def, Set.Subset.refl A⟩

/-- FO-014. The empty set is a subset of every set. -/
@[kb "hammack2018" "Fact 1.2, p. 24", kb "levin2025" "Sec 5.1.2, p. 414"]
theorem hammack_fact_1_2_empty_subset {α : Type*} (A : Set α) : (∅ : Set α) ⊆ A :=
  Set.empty_subset A

/-- FO-015. A finite set with `n` elements has `2^n` subsets. -/
@[kb "hammack2018" "Fact 1.3, p. 25", kb "hammack2018" "Fact 1.4, p. 27", kb "levin2025" "Example 5.1.6, p. 415"]
theorem hammack_fact_1_4_card_powerset {α : Type*} (A : Finset α) :
    A.powerset.card = 2 ^ A.card :=
  Finset.card_powerset A

/-- FO-016. The power set of `A` consists of exactly the subsets of `A`. -/
@[kb "hammack2018" "Def 1.4, p. 27", kb "levin2025" "Sec 5.1.2, p. 414"]
theorem hammack_def_1_4_mem_powerset {α : Type*} (A X : Set α) : X ∈ 𝒫 A ↔ X ⊆ A :=
  Set.mem_powerset_iff X A

/-- FO-017. Membership in a union, an intersection and a difference of two sets. -/
@[kb "hammack2018" "Def 1.5, p. 30", kb "levin2025" "Sec 5.1.3, p. 415"]
theorem hammack_def_1_5_union_inter_diff {α : Type*} (A B : Set α) (x : α) :
    (x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B) ∧ (x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B) ∧ (x ∈ A \ B ↔ x ∈ A ∧ x ∉ B) :=
  ⟨Set.mem_union x A B, Set.mem_inter_iff x A B, Set.mem_sdiff x⟩

/-- FO-018. Union and intersection are commutative. -/
@[kb "hammack2018" "Def 1.5, p. 30"]
theorem hammack_def_1_5_comm {α : Type*} (A B : Set α) : A ∪ B = B ∪ A ∧ A ∩ B = B ∩ A :=
  ⟨Set.union_comm A B, Set.inter_comm A B⟩

/-- FO-019. Union and intersection are associative. -/
@[kb "hammack2018" "Sec 1.7, p. 35"]
theorem hammack_s1_7_assoc {α : Type*} (A B C : Set α) :
    (A ∪ B) ∪ C = A ∪ (B ∪ C) ∧ (A ∩ B) ∩ C = A ∩ (B ∩ C) :=
  ⟨Set.union_assoc A B C, Set.inter_assoc A B C⟩

/-- FO-026. Well-ordering: every nonempty set of natural numbers has a least element. -/
@[kb "hammack2018" "Sec 1.9, p. 42"]
theorem hammack_s1_9_well_ordering (S : Set ℕ) (h : S.Nonempty) : ∃ m ∈ S, ∀ n ∈ S, m ≤ n := by
  obtain ⟨m, hm, hmin⟩ := WellFounded.has_min wellFounded_lt S h
  exact ⟨m, hm, fun n hn => not_lt.mp (hmin n hn)⟩

/-- FO-027. Division algorithm: for `b > 0` the quotient and remainder with `a = qb + r`, `0 ≤ r < b` exist
and are unique. -/
@[kb "hammack2018" "Fact 1.5, p. 42"]
theorem hammack_fact_1_5_division_algorithm (a b : ℤ) (hb : 0 < b) :
    ∃! p : ℤ × ℤ, a = p.1 * b + p.2 ∧ 0 ≤ p.2 ∧ p.2 < b := by
  have hb' : b ≠ 0 := hb.ne'
  have key : ∀ q r : ℤ, (a / b = q ∧ a % b = r) ↔ (r + b * q = a ∧ 0 ≤ r ∧ r < b) := by
    intro q r
    have := Int.ediv_emod_unique'' (a := a) (r := r) (q := q) hb'
    rwa [abs_of_pos hb] at this
  refine ⟨(a / b, a % b), ?_, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := (key (a / b) (a % b)).1 ⟨rfl, rfl⟩
    exact ⟨(by linarith), h2, h3⟩
  · rintro ⟨q, r⟩ ⟨h1, h2, h3⟩
    obtain ⟨e1, e2⟩ := (key q r).2 ⟨(by linarith), h2, h3⟩
    simp [e1, e2]

end UndergradKB.Foundations.Course
