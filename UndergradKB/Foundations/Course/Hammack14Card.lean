import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Analysis.Real.Cardinality
import Mathlib.SetTheory.Cardinal.Rat
import Mathlib.Logic.Equiv.Nat
import UndergradKB.Common

/-!
# Course layer: Hammack, Chapter 14 (cardinality of sets)

Thin statements in the book's terms for the rows FO-289 to FO-308 classified `in Mathlib`.
-/

open Cardinal

universe u v

namespace UndergradKB.Foundations.Course

/-- FO-289. Two sets have the same cardinality exactly when a bijection joins them. -/
@[kb "hammack2018" "Definition 14.1, p. 281"]
theorem hammack_def_14_1_card_eq_iff {A : Type u} {B : Type u} :
    #A = #B ↔ Nonempty (A ≃ B) :=
  Cardinal.eq

/-- FO-291. There is a bijection between the naturals and the integers. -/
@[kb "hammack2018" "Theorem 14.1, p. 283", kb "hammack2018" "Example 14.2, p. 282"]
theorem hammack_thm_14_1_nat_int : Nonempty (ℕ ≃ ℤ) ∧ #ℕ = #ℤ :=
  ⟨⟨Equiv.intEquivNat.symm⟩, by simp⟩

/-- FO-292. There is no surjection from the naturals onto the reals, so `|ℕ| < |ℝ|`. -/
@[kb "hammack2018" "Theorem 14.2, p. 284"]
theorem hammack_thm_14_2_nat_not_real :
    (¬ ∃ f : ℕ → ℝ, Function.Surjective f) ∧ #ℕ < #ℝ := by
  refine ⟨?_, by simp⟩
  rintro ⟨f, hf⟩
  exact Cardinal.not_countable_real (by rw [← hf.range_eq]; exact Set.countable_range f)

/-- FO-293. The intervals `(0, ∞)`, `(0, 1)` and `ℝ` all have the same cardinality. -/
@[kb "hammack2018" "Example 14.3, p. 285", kb "hammack2018" "Example 14.4, p. 285"]
theorem hammack_ex_14_3_interval_cards :
    #(Set.Ioi (0 : ℝ)) = #(Set.Ioo (0 : ℝ) 1) ∧ #(Set.Ioo (0 : ℝ) 1) = #ℝ := by
  rw [Cardinal.mk_Ioi_real, Cardinal.mk_Ioo_real one_pos, Cardinal.mk_real]
  exact ⟨rfl, rfl⟩

/-- FO-294. Having the same cardinality is reflexive, symmetric and transitive. -/
@[kb "hammack2018" "§14.1, p. 285"]
theorem hammack_s14_1_card_eq_equivalence :
    (∀ A : Type u, Nonempty (A ≃ A)) ∧
    (∀ A B : Type u, Nonempty (A ≃ B) → Nonempty (B ≃ A)) ∧
    (∀ A B C : Type u, Nonempty (A ≃ B) → Nonempty (B ≃ C) → Nonempty (A ≃ C)) :=
  ⟨fun _ => ⟨Equiv.refl _⟩, fun _ _ ⟨e⟩ => ⟨e.symm⟩, fun _ _ _ ⟨e⟩ ⟨e'⟩ => ⟨e.trans e'⟩⟩

/-- FO-296. The cardinality of the naturals is `ℵ₀`. -/
@[kb "hammack2018" "Definition 14.3, p. 287"]
theorem hammack_def_14_3_aleph0 : #ℕ = ℵ₀ :=
  Cardinal.mk_nat

/-- FO-298. The rationals are countably infinite. -/
@[kb "hammack2018" "Theorem 14.4, p. 288"]
theorem hammack_thm_14_4_rat_countably_infinite : #ℚ = ℵ₀ :=
  Cardinal.mkRat

/-- FO-299. A product of two countably infinite sets is countably infinite. -/
@[kb "hammack2018" "Theorem 14.5, p. 290"]
theorem hammack_thm_14_5_prod_countably_infinite {A : Type u} {B : Type v}
    [Countable A] [Infinite A] [Countable B] [Infinite B] :
    Countable (A × B) ∧ Infinite (A × B) := by
  have := Infinite.nonempty B
  exact ⟨inferInstance, inferInstance⟩

/-- FO-301. The union of two countably infinite sets is countably infinite. -/
@[kb "hammack2018" "Theorem 14.6, p. 291"]
theorem hammack_thm_14_6_union_countably_infinite {α : Type u} (A B : Set α)
    (hA : A.Countable) (hAi : A.Infinite) (hB : B.Countable) (_hBi : B.Infinite) :
    (A ∪ B).Countable ∧ (A ∪ B).Infinite :=
  ⟨hA.union hB, hAi.mono Set.subset_union_left⟩

/-- FO-303. Cantor's theorem: every set is strictly smaller than its power set. -/
@[kb "hammack2018" "Theorem 14.7, p. 293"]
theorem hammack_thm_14_7_cantor {A : Type u} : #A < #(Set A) := by
  rw [Cardinal.mk_set]
  exact Cardinal.cantor _

/-- FO-304. An infinite subset of a countably infinite set is countably infinite. -/
@[kb "hammack2018" "Theorem 14.8, p. 294"]
theorem hammack_thm_14_8_infinite_subset {α : Type u} (A B : Set α) (hB : B ⊆ A)
    (hA : A.Countable) (hBi : B.Infinite) : B.Countable ∧ B.Infinite :=
  ⟨hA.mono hB, hBi⟩

/-- FO-305. A set containing an uncountable subset is uncountable. -/
@[kb "hammack2018" "Theorem 14.9, p. 295"]
theorem hammack_thm_14_9_superset_uncountable {α : Type u} (A B : Set α) (hAB : A ⊆ B)
    (hA : ¬ A.Countable) : ¬ B.Countable :=
  fun hB => hA (hB.mono hAB)

/-- FO-306. Cantor-Bernstein-Schroeder: injections both ways yield a bijection. -/
@[kb "hammack2018" "Theorem 14.10, p. 298"]
theorem hammack_thm_14_10_cantor_bernstein {A : Type u} {B : Type v} (f : A → B) (g : B → A)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ h : A → B, Function.Bijective h :=
  Function.Embedding.schroeder_bernstein hf hg

/-- FO-307. The intervals `[0, 1)` and `(0, 1)` have the same cardinality. -/
@[kb "hammack2018" "Example 14.6, p. 300"]
theorem hammack_ex_14_6_Ico_Ioo : #(Set.Ico (0 : ℝ) 1) = #(Set.Ioo (0 : ℝ) 1) := by
  rw [Cardinal.mk_Ico_real one_pos, Cardinal.mk_Ioo_real one_pos]

/-- FO-308. The reals and the power set of the naturals have the same cardinality. -/
@[kb "hammack2018" "Theorem 14.11, p. 300"]
theorem hammack_thm_14_11_real_powerset_nat : #ℝ = #(Set ℕ) := by
  rw [Cardinal.mk_real, Cardinal.mk_set_nat]

end UndergradKB.Foundations.Course
