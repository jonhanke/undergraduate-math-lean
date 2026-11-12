import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Set.Lattice.Image
import Mathlib.Data.Set.Lattice.Order
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import UndergradKB.Common

/-!
# Course layer: Levin, Chapter 1 (proof techniques, sets, functions, graphs)
-/

namespace UndergradKB.Foundations.Course

/-- FO-103. If `a + b` is odd then `a` is odd or `b` is odd. -/
@[kb "levin2025" "Ex 1.4.12, p. 90"]
theorem levin_ex_1_4_12_odd_sum_odd_summand (a b : ℤ) (h : Odd (a + b)) : Odd a ∨ Odd b := by
  by_contra hc
  rw [not_or, Int.not_odd_iff_even, Int.not_odd_iff_even] at hc
  exact (Int.not_even_iff_odd.mpr h) (hc.1.add hc.2)

/-- FO-148. If `A ⊆ B` then `A ∪ B ⊆ B`; in fact `A ⊆ B` iff `A ∪ B = B`. -/
@[kb "levin2025" "Example 1.5.5, p. 106"]
theorem levin_ex_1_5_5_union_subset {α : Type*} (A B : Set α) :
    (A ⊆ B → A ∪ B ⊆ B) ∧ (A ⊆ B ↔ A ∪ B = B) :=
  ⟨fun h => Set.union_subset h subset_rfl, Set.union_eq_right.symm⟩

/-- FO-162. Pigeonhole principle: more pigeons than holes means two pigeons share a hole. -/
@[kb "levin2025" "Example 1.4.18, p. 94"]
theorem levin_ex_1_4_18_pigeonhole {α : Type*} [Fintype α] (n : ℕ) (h : n < Fintype.card α)
    (f : α → Fin n) : ∃ x y, x ≠ y ∧ f x = f y :=
  Fintype.exists_ne_map_eq_of_card_lt f (by simpa using h)

/-- FO-163. A function is injective iff every element of the codomain has at most one
preimage. -/
@[kb "levin2025" "Definition 1.5.6, p. 107"]
theorem levin_def_1_5_6_injective {α β : Type*} (f : α → β) :
    Function.Injective f ↔ ∀ b : β, ∀ a a' : α, f a = b → f a' = b → a = a' :=
  ⟨fun h _ _ _ ha ha' => h (ha.trans ha'.symm), fun h a a' e => h _ a a' e rfl⟩

/-- FO-164. If the domain is bigger than the codomain (both finite), no function is injective. -/
@[kb "levin2025" "Proposition 1.5.8, p. 108"]
theorem levin_prop_1_5_8_not_injective {α β : Type*} [Fintype α] [Fintype β]
    (h : Fintype.card β < Fintype.card α) (f : α → β) : ¬ Function.Injective f :=
  fun hf => absurd (Fintype.card_le_of_injective f hf) (not_le.mpr h)

/-- FO-165. The image of `A` under `f` is the set of values `f a` with `a ∈ A`. -/
@[kb "levin2025" "Definition 1.5.10, p. 108"]
theorem levin_def_1_5_10_image {α β : Type*} (f : α → β) (A : Set α) (b : β) :
    b ∈ f '' A ↔ ∃ a, a ∈ A ∧ f a = b :=
  Iff.rfl

/-- FO-166. If `A ⊆ B` then `f(A) ⊆ f(B)`. -/
@[kb "levin2025" "Proposition 1.5.12, p. 109"]
theorem levin_prop_1_5_12_image_mono {α β : Type*} (f : α → β) {A B : Set α} (h : A ⊆ B) :
    f '' A ⊆ f '' B :=
  Set.image_mono h

/-- FO-167. The inverse image of `B` consists of the `x` with `f x ∈ B`. -/
@[kb "levin2025" "Def §1.5.7, p. 115"]
theorem levin_def_1_5_7_preimage {α β : Type*} (f : α → β) (B : Set β) (x : α) :
    x ∈ f ⁻¹' B ↔ f x ∈ B :=
  Iff.rfl

/-- FO-169. The degree of a vertex is the number of edges containing it. -/
@[kb "levin2025" "Definition 1.5.16, p. 111"]
theorem levin_def_1_5_16_degree {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) : G.degree v = (G.incidenceFinset v).card :=
  (G.card_incidenceFinset_eq_degree v).symm

/-- FO-170. Every graph has an even number of vertices of odd degree. -/
@[kb "levin2025" "Proposition 1.5.18, p. 112"]
theorem levin_prop_1_5_18_even_odd_vertices {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Even (Finset.univ.filter fun v => Odd (G.degree v)).card :=
  G.even_card_odd_degree_vertices

end UndergradKB.Foundations.Course
