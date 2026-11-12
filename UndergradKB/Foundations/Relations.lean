import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Order.Interval.Finset.Nat
import UndergradKB.Common

/-! # Relations and functions

Hammack, *Book of Proof*, Chapters 11-12, and Levin, *Discrete Mathematics*, Sections 1.5 and 2.6: relation classes of an
arbitrary relation (FO-067), equality of equivalence classes (FO-068), transitivity (FO-168), a pigeonhole application to
subset sums (FO-085) and bijectivity through the inverse relation (FO-090).

A relation on `α` is a predicate `R : α → α → Prop` (`R a b` is "`a R b`", i.e. `(a, b) ∈ R`).
-/

namespace UndergradKB.Foundations

/-! ## Relation classes (FO-067, FO-068) -/

/-- The relation class of `a` for a relation `R` (Levin): the set of all `b` with `(a, b) ∈ R`. -/
def relClass {α : Type*} (R : α → α → Prop) (a : α) : Set α := {b | R a b}

/-- FO-067. Membership in a relation class: `b ∈ [a]` iff `a R b`. -/
@[kb "levin2025" "Def 2.6.18, p. 194"]
theorem mem_relClass {α : Type*} (R : α → α → Prop) (a b : α) : b ∈ relClass R a ↔ R a b :=
  Iff.rfl

/-- The equivalence class of `a` as Hammack writes it: `[a] = {x : x R a}`. -/
def eqvClass {α : Type*} (R : α → α → Prop) (a : α) : Set α := {x | R x a}

/-- FO-068 (Hammack Theorem 11.1). For an equivalence relation `R`, `[a] = [b]` iff `a R b`; the book's proof. -/
@[kb "hammack2018" "Thm 11.1, p. 227"]
theorem eqvClass_eq_iff {α : Type*} {R : α → α → Prop} (hR : Equivalence R) (a b : α) :
    eqvClass R a = eqvClass R b ↔ R a b := by
  constructor
  · intro h
    have ha : a ∈ eqvClass R a := hR.refl a
    rw [h] at ha
    exact ha
  · intro hab
    ext c
    exact ⟨fun hca => hR.trans hca hab, fun hcb => hR.trans hcb (hR.symm hab)⟩

/-- FO-068. For an equivalence relation the two conventions for the class agree (Levin's `{b | a R b}` and Hammack's
`{x | x R a}`), so Levin's relation classes satisfy the same criterion. -/
@[kb "levin2025" "Def 2.6.18, p. 194"]
theorem relClass_eq_iff {α : Type*} {R : α → α → Prop} (hR : Equivalence R) (a b : α) :
    relClass R a = eqvClass R a ∧ (relClass R a = relClass R b ↔ R a b) := by
  have key : ∀ x, relClass R x = eqvClass R x := fun x => by
    ext y; exact ⟨hR.symm, hR.symm⟩
  rw [key a, key b]
  exact ⟨rfl, eqvClass_eq_iff hR a b⟩

/-! ## Transitive relations (FO-168) -/

/-- FO-168. A relation is transitive when `a R b` and `b R c` imply `a R c`; Mathlib's class `IsTrans` says exactly
this. -/
@[kb "levin2025" "Definition 1.5.13, p. 110"]
theorem transitive_iff {α : Type*} (R : α → α → Prop) :
    IsTrans α R ↔ ∀ a b c, R a b → R b c → R a c :=
  ⟨fun h => h.trans, fun h => ⟨h⟩⟩

/-! ## Pigeonhole: equal subset sums (FO-085) -/

/-- FO-085 (Hammack, §12.3). Among any ten distinct integers between 1 and 100 there are two different subsets with the
same sum: there are `2^10 = 1024` subsets but only `1001` possible sums `0, …, 1000`. -/
@[kb "hammack2018" "Prop §12.3, p. 246"]
theorem exists_subsets_eq_sum (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 100) (hcard : S.card = 10) :
    ∃ X ⊆ S, ∃ Y ⊆ S, X ≠ Y ∧ ∑ x ∈ X, x = ∑ y ∈ Y, y := by
  have hmaps : ∀ X ∈ S.powerset, (∑ x ∈ X, x) ∈ Finset.range 1001 := by
    intro X hX
    rw [Finset.mem_powerset] at hX
    have h1 : ∑ x ∈ X, x ≤ ∑ x ∈ S, x := Finset.sum_le_sum_of_subset hX
    have h2 : ∑ x ∈ S, x ≤ S.card • 100 :=
      Finset.sum_le_card_nsmul S _ 100 fun x hx => (Finset.mem_Icc.mp (hS hx)).2
    rw [hcard, smul_eq_mul] at h2
    rw [Finset.mem_range]
    omega
  have hlt : (Finset.range 1001).card < S.powerset.card := by
    rw [Finset.card_range, Finset.card_powerset, hcard]
    norm_num
  obtain ⟨X, hX, Y, hY, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  exact ⟨X, Finset.mem_powerset.mp hX, Y, Finset.mem_powerset.mp hY, hne, heq⟩

/-! ## Bijections and the inverse relation (FO-090) -/

/-- The inverse relation of a function `f : α → β`, as a set of pairs: `f⁻¹ = {(f x, x)}`. -/
def inverseRelation {α β : Type*} (f : α → β) : Set (β × α) := {p | f p.2 = p.1}

/-- FO-090 (Hammack Theorem 12.3). A function `f : A → B` is bijective iff its inverse relation is a function from `B`
to `A`, i.e. every `b ∈ B` is related to exactly one `a ∈ A`. -/
@[kb "hammack2018" "Thm 12.3, p. 252"]
theorem bijective_iff_inverseRelation_function {α β : Type*} (f : α → β) :
    Function.Bijective f ↔ ∀ b, ∃! a, (b, a) ∈ inverseRelation f :=
  Function.bijective_iff_existsUnique f

end UndergradKB.Foundations
