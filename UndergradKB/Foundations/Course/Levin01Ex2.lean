import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Insert
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Linarith
import Mathlib.Combinatorics.Pigeonhole
import UndergradKB.Common

/-!
# Course layer: Levin, Discrete Mathematics, Chapter 1, worked examples (second batch)
-/

namespace UndergradKB.Foundations.Course

/-- Levin Example 1.1.11: truth values of compound statements about the primality of 17, 18, 19. -/
@[kb "levin2025" "Example 1.1.11, p. 40"]
theorem levin_ex_1_1_11_connectives_primes :
    (Nat.Prime 17 ∧ Odd 17) ∧ ¬ (Nat.Prime 17 ∧ Nat.Prime 18) ∧
    (Nat.Prime 17 ∨ Nat.Prime 18) ∧ (Nat.Prime 17 ∨ Nat.Prime 19) ∧
    (Nat.Prime 17 → Nat.Prime 19) ∧ (Nat.Prime 17 ↔ Nat.Prime 19) ∧
    (¬ Nat.Prime 17 ↔ ¬ Nat.Prime 19) := by
  have h17 : Nat.Prime 17 := by norm_num
  have h19 : Nat.Prime 19 := by norm_num
  have h18 : ¬ Nat.Prime 18 := by norm_num
  have hodd : Odd 17 := by decide
  tauto

/-- Levin Example 1.2.5: implications with a false hypothesis or a true conclusion are true. -/
@[kb "levin2025" "Example 1.2.5, p. 53"]
theorem levin_ex_1_2_5_vacuous_implications :
    ((0 : ℕ) = 1 → (1 : ℕ) = 1) ∧ (∀ Q : Prop, Nat.Prime 8 → Q) ∧
      (∀ P : Prop, P → (2 + 2 : ℕ) = 4) := by
  refine ⟨fun _ => rfl, fun Q h => absurd h (by norm_num), fun _ _ => rfl⟩

/-- Levin Example 1.2.10: any nine cards from a deck contain three of one suit
(cards modelled as pairs of a suit in `Fin 4` and a value in `Fin 13`). -/
@[kb "levin2025" "Example 1.2.10, p. 56"]
theorem levin_ex_1_2_10_nine_cards_three_suit (hand : Finset (Fin 4 × Fin 13))
    (h : hand.card = 9) : ∃ i : Fin 4, 3 ≤ (hand.filter (fun c => c.1 = i)).card := by
  have := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := hand) (t := (Finset.univ : Finset (Fin 4))) (f := Prod.fst) (n := 2)
    (fun _ _ => Finset.mem_univ _) (by simp [h])
  obtain ⟨i, -, hi⟩ := this
  exact ⟨i, hi⟩

/-- Levin Example 1.3.4: `(P → Q) ∨ (Q → R)` is a tautology. -/
@[kb "levin2025" "Example 1.3.4, p. 67"]
theorem levin_ex_1_3_4_tautology (P Q R : Prop) : (P → Q) ∨ (Q → R) := by
  by_cases hq : Q
  · exact Or.inl fun _ => hq
  · exact Or.inr fun h => absurd h hq

/-- Levin Example 1.3.7: "not (P or Q)" is equivalent to "not P and not Q". -/
@[kb "levin2025" "Example 1.3.7, p. 69"]
theorem levin_ex_1_3_7_not_or (P Q : Prop) : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q := not_or

/-- Levin Example 1.3.9: `¬(P → Q)` is equivalent to `P ∧ ¬Q`. -/
@[kb "levin2025" "Example 1.3.9, p. 70"]
theorem levin_ex_1_3_9_not_implies (P Q : Prop) : ¬ (P → Q) ↔ P ∧ ¬ Q := Classical.not_imp

/-- Levin Example 1.3.12: "there is no smallest integer" is equivalent to
"for every `x` there is a `y < x`". -/
@[kb "levin2025" "Example 1.3.12, p. 73"]
theorem levin_ex_1_3_12_no_smallest : (¬ ∃ x : ℤ, ∀ y : ℤ, x ≤ y) ↔ ∀ x : ℤ, ∃ y : ℤ, y < x := by
  simp only [not_exists, not_forall, not_le]

/-- Levin Example 1.5.3: `{x < 5}` properly contains `{x² < 10}` among natural numbers. -/
@[kb "levin2025" "Example 1.5.3, p. 105"]
theorem levin_ex_1_5_3_proper_subset :
    {x : ℕ | x ^ 2 < 10} ⊂ {x : ℕ | x < 5} := by
  refine ⟨fun x hx => ?_, fun h => ?_⟩
  · have hx : x ^ 2 < 10 := hx
    show x < 5
    by_contra hc
    nlinarith
  · have := h (show (4 : ℕ) ∈ {x : ℕ | x < 5} by simp)
    simp at this

/-- Levin Example 1.5.7: of the two listed functions on `{1,2,3}`, the first is injective and the
second is not. -/
@[kb "levin2025" "Example 1.5.7, p. 107"]
theorem levin_ex_1_5_7_injective :
    Function.Injective (![2, 8, 6] : Fin 3 → ℕ) ∧ ¬ Function.Injective (![4, 6, 4] : Fin 3 → ℕ) := by
  constructor
  · decide
  · intro h
    have := @h 0 2 (by decide)
    exact absurd this (by decide)

/-- Levin Corollary 1.5.9: among 25 students and 12 birth months, two students share a month. -/
@[kb "levin2025" "Corollary 1.5.9, p. 108"]
theorem levin_cor_1_5_9_birth_months (month : Fin 25 → Fin 12) :
    ∃ a b : Fin 25, a ≠ b ∧ month a = month b := by
  obtain ⟨a, b, hab, h⟩ := Fintype.exists_ne_map_eq_of_card_lt month (by simp)
  exact ⟨a, b, hab, h⟩

/-- Levin Example 1.5.11: the image of `{1,2,3}` under doubling is `{2,4,6}`. -/
@[kb "levin2025" "Example 1.5.11, p. 108"]
theorem levin_ex_1_5_11_image_doubling :
    (fun n : ℕ => 2 * n) '' ({1, 2, 3} : Set ℕ) = {2, 4, 6} := by
  simp [Set.image_insert_eq]

/-- Levin Example 1.5.17: degrees in the graph on `{1,2,3,4}` with edges `12, 13, 14, 23`
are `3, 2, 2, 1`, and they sum to twice the number of edges. -/
@[kb "levin2025" "Example 1.5.17, p. 111"]
theorem levin_ex_1_5_17_degrees :
    let E : Finset (Finset ℕ) := {{1, 2}, {1, 3}, {1, 4}, {2, 3}}
    let d : ℕ → ℕ := fun v => (E.filter (fun e => v ∈ e)).card
    d 1 = 3 ∧ d 2 = 2 ∧ d 3 = 2 ∧ d 4 = 1 ∧ d 1 + d 2 + d 3 + d 4 = 2 * E.card := by
  decide +kernel

end UndergradKB.Foundations.Course
