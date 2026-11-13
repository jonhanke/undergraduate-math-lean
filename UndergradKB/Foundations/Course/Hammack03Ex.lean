import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.Ring.Nat
import UndergradKB.Common

/-!
# Course layer: Hammack, Book of Proof, Chapter 3, worked examples

Thin theorems for the numerical counting examples of Hammack Chapter 3.
-/

namespace UndergradKB.Foundations.Course

/-- Hammack Example 3.8(a): there are `7!` repetition-free lists of length 7 from a 7-letter alphabet. -/
@[kb "hammack2018" "Example 3.8, p. 91"]
theorem hammack_ex_3_8_injective_lists :
    Fintype.card (Fin 7 ↪ Fin 7) = 5040 := by
  rw [Fintype.card_embedding_eq]
  decide +kernel

/-- Hammack Example 3.8(c): lists of length 7 from 7 letters with some repetition number `7^7 - 7!`. -/
@[kb "hammack2018" "Example 3.8, p. 91"]
theorem hammack_ex_3_8_repeated_lists :
    Fintype.card {f : Fin 7 → Fin 7 // ¬ Function.Injective f} = 818503 := by
  rw [Fintype.card_subtype_compl, Fintype.card_fun]
  rw [Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding (Fin 7) (Fin 7))]
  rw [Fintype.card_embedding_eq]
  decide +kernel

/-- Hammack Example 3.9: the number of first-second-third rankings among ten runners is `P(10, 3) = 720`. -/
@[kb "hammack2018" "Example 3.9, p. 95"]
theorem hammack_ex_3_9_rankings :
    Fintype.card (Fin 3 ↪ Fin 10) = 720 := by
  rw [Fintype.card_embedding_eq]
  decide +kernel

/-- Hammack Example 3.10: lineups of five cards that are all red or all clubs number `P(26,5) + P(13,5)`. -/
@[kb "hammack2018" "Example 3.10, p. 95"]
theorem hammack_ex_3_10_red_or_clubs :
    Nat.descFactorial 26 5 + Nat.descFactorial 13 5 = 8048040 := by
  decide +kernel

/-- Hammack Example 3.11: the set `{1, ..., 9}` has 126 subsets of size 4. -/
@[kb "hammack2018" "Example 3.11, p. 99"]
theorem hammack_ex_3_11_four_subsets :
    (Finset.powersetCard 4 (Finset.Icc 1 9)).card = 126 := by
  decide +kernel

/-- Hammack Example 3.12: exactly 60 five-element subsets of `{1, ..., 9}` have exactly two even elements. -/
@[kb "hammack2018" "Example 3.12, p. 99"]
theorem hammack_ex_3_12_two_even :
    ((Finset.powersetCard 5 (Finset.Icc 1 9)).filter
      (fun s => (s.filter Even).card = 2)).card = 60 := by
  decide +kernel

/-- Hammack Example 3.13: a 52-card deck has 2,598,960 five-card hands. -/
@[kb "hammack2018" "Example 3.13, p. 99"]
theorem hammack_ex_3_13_five_card_hands : Nat.choose 52 5 = 2598960 := by
  decide +kernel

/-- Hammack Example 3.14: there are 22,308 five-card hands with two clubs and three hearts. -/
@[kb "hammack2018" "Example 3.14, p. 100"]
theorem hammack_ex_3_14_clubs_hearts : Nat.choose 13 2 * Nat.choose 13 3 = 22308 := by
  decide +kernel

/-- Hammack Example 3.15: a lottery ticket of six numbers out of 36 has `C(36, 6) = 1947792` possibilities. -/
@[kb "hammack2018" "Example 3.15, p. 100"]
theorem hammack_ex_3_15_lottery : Nat.choose 36 6 = 1947792 := by
  decide +kernel

/-- Hammack Example 3.16: exactly 64 binary strings of length 7 contain an odd number of 1's. -/
@[kb "hammack2018" "Example 3.16, p. 100"]
theorem hammack_ex_3_16_odd_weight :
    (Finset.univ.filter (fun s : Fin 7 → Bool =>
      Odd (Finset.univ.filter (fun i => s i = true)).card)).card = 64 := by
  decide +kernel

/-- Hammack Example 3.17: three-card hands that are all red or all face cards number
`C(26,3) + C(12,3) - C(6,3) = 2800`. -/
@[kb "hammack2018" "Example 3.17, p. 105"]
theorem hammack_ex_3_17_red_or_face :
    Nat.choose 26 3 + Nat.choose 12 3 - Nat.choose 6 3 = 2800 := by
  decide +kernel

/-- Hammack Example 3.18: the remaining three-card hands number `C(52,3) - 2800 = 19300`. -/
@[kb "hammack2018" "Example 3.18, p. 106"]
theorem hammack_ex_3_18_complement :
    Nat.choose 52 3 - (Nat.choose 26 3 + Nat.choose 12 3 - Nat.choose 6 3) = 19300 := by
  decide +kernel

/-- Hammack Example 3.22: the multiset with multiplicities 1, 4, 4, 2 has `11!/(1! 4! 4! 2!) = 34650`
permutations. -/
@[kb "hammack2018" "Example 3.22, p. 114"]
theorem hammack_ex_3_22_mississippi :
    Nat.multinomial Finset.univ (![1, 4, 4, 2] : Fin 4 → ℕ) = 34650 := by
  decide +kernel

/-- Hammack Example 3.23: the multiset `[1,1,1,1,5,5,10,25,25]` has `9!/(4! 2! 1! 2!) = 3780` permutations. -/
@[kb "hammack2018" "Example 3.23, p. 114"]
theorem hammack_ex_3_23_coin_multiset :
    Nat.multinomial Finset.univ (![4, 2, 1, 2] : Fin 4 → ℕ) = 3780 := by
  decide +kernel

end UndergradKB.Foundations.Course
