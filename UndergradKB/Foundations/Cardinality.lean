import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Data.Fintype.Prod
import Mathlib.Basic.Denumerable
import Mathlib.Basic.Countable.Basic
import UndergradKB.Common

/-!
# Foundations: countable sets and the order on cardinalities

Gap rows from Hammack's chapter 14. "Countably infinite" is expressed as `Nonempty (ℕ ≃ A)`
(Mathlib's `Denumerable` carries the bijection as data).
-/

namespace UndergradKB.Foundations

universe u v

/-- FO-295. A set is countably infinite exactly when it is countable (in Mathlib's sense of
finite or countably infinite) and infinite. -/
@[kb "hammack2018" "Definition 14.2, p. 287"]
theorem hammack_def_14_2_countably_infinite_iff (A : Type u) :
    Nonempty (ℕ ≃ A) ↔ Countable A ∧ Infinite A := by
  rw [← nonempty_denumerable_iff]
  constructor
  · rintro ⟨e⟩
    exact ⟨Denumerable.mk' e.symm⟩
  · rintro ⟨d⟩
    exact ⟨(Denumerable.eqv A).symm⟩

/-- FO-295. A set is countable iff it is finite or countably infinite. -/
@[kb "hammack2018" "Definition 14.2, p. 287"]
theorem hammack_def_14_2_countable_iff (A : Type u) :
    Countable A ↔ Finite A ∨ Nonempty (ℕ ≃ A) := by
  rw [hammack_def_14_2_countably_infinite_iff]
  constructor
  · intro h
    by_cases hf : Finite A
    · exact Or.inl hf
    · exact Or.inr ⟨h, not_finite_iff_infinite.mp hf⟩
  · rintro (h | ⟨h, _⟩)
    · exact Finite.to_countable
    · exact h

/-- FO-295. A set is uncountable iff it is neither finite nor countably infinite. -/
@[kb "hammack2018" "Definition 14.2, p. 287"]
theorem hammack_def_14_2_uncountable_iff (A : Type u) :
    Uncountable A ↔ ¬ (Finite A ∨ Nonempty (ℕ ≃ A)) := by
  rw [← hammack_def_14_2_countable_iff, not_countable_iff]

/-- FO-297. A set is countably infinite iff its elements can be arranged in an infinite list
in which each element appears exactly once. -/
@[kb "hammack2018" "Theorem 14.3, p. 288"]
theorem hammack_thm_14_3_list (A : Type u) :
    Nonempty (ℕ ≃ A) ↔ ∃ a : ℕ → A, Function.Injective a ∧ Function.Surjective a := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e, e.injective, e.surjective⟩
  · rintro ⟨a, hi, hs⟩
    exact ⟨Equiv.ofBijective a ⟨hi, hs⟩⟩

/-- FO-297. Equivalently, an infinite set is countably infinite iff some infinite list
(repetitions allowed) contains all its elements. -/
@[kb "hammack2018" "Theorem 14.3, p. 288"]
theorem hammack_thm_14_3_list_with_repeats (A : Type u) :
    Nonempty (ℕ ≃ A) ↔ Infinite A ∧ ∃ a : ℕ → A, Function.Surjective a := by
  rw [hammack_def_14_2_countably_infinite_iff]
  constructor
  · rintro ⟨hc, hi⟩
    obtain ⟨a, ha⟩ := exists_surjective_nat A
    exact ⟨hi, a, ha⟩
  · rintro ⟨hi, a, ha⟩
    exact ⟨ha.countable, hi⟩

/-- FO-300. A product of `n ≥ 2` countably infinite sets is countably infinite. -/
@[kb "hammack2018" "Corollary 14.1, p. 291"]
theorem hammack_cor_14_1_finite_product (n : ℕ) (hn : 2 ≤ n) (A : Fin n → Type u)
    (h : ∀ i, Nonempty (ℕ ≃ A i)) : Nonempty (ℕ ≃ ((i : Fin n) → A i)) := by
  rw [hammack_def_14_2_countably_infinite_iff]
  have hc : ∀ i, Countable (A i) := fun i => ((hammack_def_14_2_countably_infinite_iff _).1 (h i)).1
  have hi : ∀ i, Infinite (A i) := fun i => ((hammack_def_14_2_countably_infinite_iff _).1 (h i)).2
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  exact ⟨inferInstance, inferInstance⟩

/-- FO-302. `|A| < |B|` in the book's sense (an injection but no bijection) agrees with the
strict order on cardinals. -/
@[kb "hammack2018" "Definition 14.4, p. 293"]
theorem hammack_def_14_4_lt_iff (A B : Type u) :
    Cardinal.mk A < Cardinal.mk B ↔
      (∃ f : A → B, Function.Injective f) ∧ ¬ ∃ g : A → B, Function.Bijective g := by
  constructor
  · intro h
    obtain ⟨f⟩ := (Cardinal.le_def A B).1 h.le
    refine ⟨⟨f, f.injective⟩, fun ⟨g, hg⟩ => h.ne ?_⟩
    exact Cardinal.mk_congr (Equiv.ofBijective g hg)
  · rintro ⟨⟨f, hf⟩, hno⟩
    refine lt_of_le_of_ne (Cardinal.mk_le_of_injective hf) fun heq => hno ?_
    obtain ⟨e⟩ := Cardinal.eq.1 heq
    exact ⟨e, e.bijective⟩

/-- FO-302. `|A| ≤ |B|` in the book's sense (an injection) agrees with the order on cardinals. -/
@[kb "hammack2018" "Definition 14.4, p. 293"]
theorem hammack_def_14_4_le_iff (A B : Type u) :
    Cardinal.mk A ≤ Cardinal.mk B ↔ ∃ f : A → B, Function.Injective f := by
  rw [Cardinal.le_def A B]
  exact ⟨fun ⟨f⟩ => ⟨f, f.injective⟩, fun ⟨f, hf⟩ => ⟨⟨f, hf⟩⟩⟩

end UndergradKB.Foundations
