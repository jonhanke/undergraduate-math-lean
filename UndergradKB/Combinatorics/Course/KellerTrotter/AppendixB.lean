import Mathlib.Data.Set.Prod
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Order.Setoid.Partition
import Mathlib.Data.Rat.Lemmas
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Basic.Real.Basic
import Mathlib.Order.SetNotation
import UndergradKB.Common.Attr

/-!
# Keller–Trotter, Appendix B (review of background material): thin wrappers over Mathlib
-/

namespace UndergradKB.Combinatorics.Course.KellerTrotter

/-- CO-019. Intersection and union of sets are commutative, associative and distribute over each
other. -/
@[kb "kellertrotter2017" "text (set operations), p. 359"]
theorem text_p359_union_inter {α : Type*} (X Y Z : Set α) :
    X ∩ Y = Y ∩ X ∧ X ∪ Y = Y ∪ X ∧ (X ∩ Y) ∩ Z = X ∩ (Y ∩ Z) ∧ (X ∪ Y) ∪ Z = X ∪ (Y ∪ Z) ∧
      X ∩ (Y ∪ Z) = (X ∩ Y) ∪ (X ∩ Z) ∧ X ∪ (Y ∩ Z) = (X ∪ Y) ∩ (X ∪ Z) :=
  ⟨Set.inter_comm _ _, Set.union_comm _ _, Set.inter_assoc _ _ _, Set.union_assoc _ _ _,
    Set.inter_union_distrib_left _ _ _, Set.union_inter_distrib_left _ _ _⟩

/-- CO-020. A set with no elements is the empty set, and `X ∩ ∅ = ∅`, `X ∪ ∅ = X`. -/
@[kb "kellertrotter2017" "text (the empty set), p. 360"]
theorem text_p360_empty {α : Type*} (X : Set α) :
    (∀ S : Set α, (∀ x, x ∉ S) → S = ∅) ∧ X ∩ ∅ = ∅ ∧ X ∪ ∅ = X :=
  ⟨fun _ h => Set.eq_empty_iff_forall_notMem.2 h, Set.inter_empty _, Set.union_empty _⟩

/-- CO-022. Two sets are equal iff each is a subset of the other. -/
@[kb "kellertrotter2017" "text (set equality test), p. 360"]
theorem text_p360_set_eq {α : Type*} (X Y : Set α) : X = Y ↔ X ⊆ Y ∧ Y ⊆ X :=
  Set.Subset.antisymm_iff

/-- CO-023. The cartesian product is empty when either factor is empty. -/
@[kb "kellertrotter2017" "text (cartesian product), p. 361"]
theorem text_p361_prod_empty {α β : Type*} (X : Set α) (Y : Set β) :
    X ×ˢ (∅ : Set β) = ∅ ∧ (∅ : Set α) ×ˢ Y = ∅ :=
  ⟨Set.prod_empty, Set.empty_prod⟩

/-- CO-340. Every positive integer has a base-`b` expansion with digits in `0..b-1`, recovering the
number. -/
@[kb "kellertrotter2017" "text (base b notation), p. 372"]
theorem text_p372_base_digits {b : ℕ} (hb : 2 ≤ b) (n : ℕ) :
    Nat.ofDigits b (Nat.digits b n) = n ∧ ∀ d ∈ Nat.digits b n, d < b :=
  ⟨Nat.ofDigits_digits b n, fun _ hd => Nat.digits_lt_base hb hd⟩

/-- CO-341. The equivalence classes of an equivalence relation partition the set. -/
@[kb "kellertrotter2017" "text (equivalence classes), p. 374"]
theorem text_p374_classes_partition {α : Type*} (r : Setoid α) : Setoid.IsPartition r.classes :=
  Setoid.isPartition_classes r


/-! ### Definitions of Appendix B in the book's terms -/

/-- CO-018. The intersection `A ∩ B` consists of the elements in both sets. -/
@[kb "kellertrotter2017" "Definition (unnumbered) intersection, p. 357"]
theorem def_p357_intersection {α : Type*} (A B : Set α) (x : α) : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B :=
  Iff.rfl

/-- CO-018. The union `A ∪ B` consists of the elements in at least one of the sets. -/
@[kb "kellertrotter2017" "Definition (unnumbered) union, p. 359"]
theorem def_p359_union {α : Type*} (A B : Set α) (x : α) : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B :=
  Iff.rfl

/-- CO-021. `[n] = {1, ..., n}` has `n` elements, and the zero-based set `{0, ..., n-1}`
is `Finset.range n`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) [n], p. 360"]
theorem def_p360_bracket_n (n : ℕ) :
    (Finset.Icc 1 n).card = n ∧ (∀ k, k ∈ Finset.Icc 1 n ↔ 1 ≤ k ∧ k ≤ n) ∧
      (∀ k, k ∈ Finset.range n ↔ k < n) :=
  ⟨by simp, fun _ => Finset.mem_Icc, fun _ => Finset.mem_range⟩

/-- CO-336. Injection, surjection and bijection: the target is hit at most once, at least once,
exactly once. -/
@[kb "kellertrotter2017" "Definition (unnumbered) injection, surjection, bijection, p. 362"]
theorem def_p362_functions {α β : Type*} (f : α → β) :
    (Function.Injective f ↔ ∀ y, ∀ a b, f a = y → f b = y → a = b) ∧
      (Function.Surjective f ↔ ∀ y, ∃ a, f a = y) ∧
      (Function.Bijective f ↔ ∀ y, ∃! a, f a = y) :=
  ⟨⟨fun h _ _ _ ha hb => h (ha.trans hb.symm), fun h a b hab => h _ a b hab rfl⟩,
    Iff.rfl, Function.bijective_iff_existsUnique f⟩

/-- CO-337. A set is finite when it is in bijection with an initial segment `Fin n` of the
naturals (the empty set, with `n = 0`, has cardinality `0`). -/
@[kb "kellertrotter2017" "Definition (unnumbered) finite set, p. 363"]
theorem def_p363_finite {α : Type*} (s : Set α) :
    s.Finite ↔ ∃ n : ℕ, Nonempty (s ≃ Fin n) := by
  rw [← Set.finite_coe_iff]
  exact finite_iff_exists_equiv_fin

/-- CO-337. The empty set has cardinality `0`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) cardinality, p. 363"]
theorem def_p363_card_empty {α : Type*} : Nat.card (∅ : Set α) = 0 := by
  simp

/-- CO-339. A partial order is reflexive, antisymmetric and transitive; `x < y` means
`x ≤ y` and `x ≠ y`; sets ordered by inclusion form a partial order. -/
@[kb "kellertrotter2017" "Definition (unnumbered) partial order, p. 370"]
theorem def_p370_partial_order {α : Type*} [PartialOrder α] (x y : α) :
    (x < y ↔ x ≤ y ∧ x ≠ y) ∧ (∀ A B : Set α, A ≤ B ↔ A ⊆ B) :=
  ⟨lt_iff_le_and_ne, fun _ _ => Iff.rfl⟩

/-- CO-342. A rational number is a fraction `numerator / denominator` in lowest terms with positive
denominator. -/
@[kb "kellertrotter2017" "Definition (unnumbered) fraction numerator denominator, p. 378"]
theorem def_p378_rational (q : ℚ) :
    q = q.num / q.den ∧ 0 < q.den ∧ Nat.Coprime q.num.natAbs q.den :=
  ⟨(Rat.num_div_den q).symm, q.den_pos, q.reduced⟩

/-- CO-344. A real number is algebraic if it is a root of a nonzero integer polynomial, and
transcendental otherwise. -/
@[kb "kellertrotter2017" "Definition (unnumbered) algebraic, p. 381"]
theorem def_p381_algebraic (x : ℝ) :
    (IsAlgebraic ℤ x ↔ ∃ p : Polynomial ℤ, p ≠ 0 ∧ Polynomial.aeval x p = 0) ∧
      (Transcendental ℤ x ↔ ¬ IsAlgebraic ℤ x) :=
  ⟨Iff.rfl, Iff.rfl⟩

end UndergradKB.Combinatorics.Course.KellerTrotter
