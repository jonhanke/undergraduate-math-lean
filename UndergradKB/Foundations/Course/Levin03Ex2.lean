import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum
import UndergradKB.Common

/-!
# Course layer: Levin, Discrete Mathematics, Chapter 3, worked examples (second batch)
-/

namespace UndergradKB.Foundations.Course

/-- Levin Example 3.2.4: there are 52 two-letter words starting with A or B. -/
@[kb "levin2025" "Example 3.2.4, p. 228"]
theorem levin_ex_3_2_4_words_start_a_or_b :
    (Finset.univ.filter (fun w : Fin 26 × Fin 26 => w.1 = 0 ∨ w.1 = 1)).card = 52 := by
  decide +kernel

/-- Levin Example 3.2.5: 98 ten-bit strings of weight 6 start with 11 or 00 (a string is
the set of positions of its 1 bits). -/
@[kb "levin2025" "Example 3.2.5, p. 228"]
theorem levin_ex_3_2_5_weight_six_prefix :
    ((Finset.univ.powersetCard 6 : Finset (Finset (Fin 10))).filter
      (fun s => (0 ∈ s ∧ 1 ∈ s) ∨ (0 ∉ s ∧ 1 ∉ s))).card = 98 := by
  decide +kernel

/-- Levin Example 3.2.7: 130 two-letter words start with one of the five vowels (sum principle:
five blocks of 26). -/
@[kb "levin2025" "Example 3.2.7, p. 229"]
theorem levin_ex_3_2_7_vowel_words_sum :
    (Finset.univ.filter (fun w : Fin 26 × Fin 26 =>
      w.1 = 0 ∨ w.1 = 4 ∨ w.1 = 8 ∨ w.1 = 14 ∨ w.1 = 20)).card = 130 ∧
      26 + 26 + 26 + 26 + 26 = 130 := by
  refine ⟨by decide +kernel, rfl⟩

/-- Levin Example 3.2.9: the same count by the product principle, five vowels times 26 letters. -/
@[kb "levin2025" "Example 3.2.9, p. 230"]
theorem levin_ex_3_2_9_vowel_words_product :
    (({0, 4, 8, 14, 20} : Finset (Fin 26)) ×ˢ (Finset.univ : Finset (Fin 26))).card = 130 := by
  decide +kernel

/-- Levin Example 3.2.10: lattice paths from `(0,0)` to `(10,10)` through `(4,7)`:
`C(11,4) * C(9,3) = 330 * 84 = 27720`. -/
@[kb "levin2025" "Example 3.2.10, p. 231"]
theorem levin_ex_3_2_10_paths_through_point :
    Nat.choose 11 4 = 330 ∧ Nat.choose 9 3 = 84 ∧ Nat.choose 11 4 * Nat.choose 9 3 = 27720 := by
  decide +kernel

/-- Levin Example 3.2.11: three letters followed by three digits give `26^3 * 10^3` plates. -/
@[kb "levin2025" "Example 3.2.11, p. 231"]
theorem levin_ex_3_2_11_license_plates :
    Fintype.card ((Fin 3 → Fin 26) × (Fin 3 → Fin 10)) = 17576000 := by
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun]
  simp

/-- Levin Example 3.2.15: lattice paths from `(0,0)` to `(9,9)` through `(2,6)` or `(6,2)`:
`3360 + 3360 = 6720`. -/
@[kb "levin2025" "Example 3.2.15, p. 234"]
theorem levin_ex_3_2_15_paths_through_either :
    Nat.choose 8 2 * Nat.choose 10 7 = 3360 ∧ Nat.choose 8 6 * Nat.choose 10 3 = 3360 ∧
      3360 + 3360 = 6720 := by
  decide +kernel

/-- Levin Example 3.3.3: among 7-bit strings of weight 4, ten start with 11, five end with 00,
three do both, so twelve do at least one. -/
@[kb "levin2025" "Example 3.3.3, p. 240"]
theorem levin_ex_3_3_3_start_or_end :
    let S : Finset (Finset (Fin 7)) := Finset.univ.powersetCard 4
    let A := S.filter (fun s => 0 ∈ s ∧ 1 ∈ s)
    let B := S.filter (fun s => 5 ∉ s ∧ 6 ∉ s)
    A.card = 10 ∧ B.card = 5 ∧ (A ∩ B).card = 3 ∧ (A ∪ B).card = 12 := by
  decide +kernel

/-- Levin Example 3.3.4: if 12, 5, 8 students failed A, B, C and the pairwise overlaps have
2, 6, 3 students and the triple overlap 1, then 15 students failed at least one subject. -/
@[kb "levin2025" "Example 3.3.4, p. 241"]
theorem levin_ex_3_3_4_failed_subjects {α : Type*} [DecidableEq α] (A B C : Finset α)
    (hA : A.card = 12) (hB : B.card = 5) (hC : C.card = 8)
    (hAB : (A ∩ B).card = 2) (hAC : (A ∩ C).card = 6) (hBC : (B ∩ C).card = 3)
    (hABC : (A ∩ B ∩ C).card = 1) : (A ∪ B ∪ C).card = 15 := by
  have h1 := Finset.card_union_add_card_inter A B
  have h2 := Finset.card_union_add_card_inter (A ∪ B) C
  have h3 := Finset.card_union_add_card_inter (A ∩ C) (B ∩ C)
  have e1 : (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) := Finset.union_inter_distrib_right A B C
  have e2 : (A ∩ C) ∩ (B ∩ C) = A ∩ B ∩ C := by
    ext x
    simp only [Finset.mem_inter]
    tauto
  rw [e1] at h2
  rw [e2] at h3
  omega

/-- Levin Example 3.3.6: the same 7-bit count via the two-set union formula,
`10 + 5 - 3 = 12`. -/
@[kb "levin2025" "Example 3.3.6, p. 243"]
theorem levin_ex_3_3_6_union_formula :
    Nat.choose 5 2 = 10 ∧ Nat.choose 5 4 = 5 ∧ Nat.choose 3 2 = 3 ∧ 10 + 5 - 3 = 12 := by
  decide +kernel

/-- Levin Example 3.3.10: for words with letters in alphabetical order, the number of choices of
the second letter varies: 4 after `w` but 26 after `a`. -/
@[kb "levin2025" "Example 3.3.10, p. 246"]
theorem levin_ex_3_3_10_varying_choices :
    (Finset.univ.filter (fun b : Fin 26 => (22 : Fin 26) ≤ b)).card = 4 ∧
      (Finset.univ.filter (fun b : Fin 26 => (0 : Fin 26) ≤ b)).card = 26 := by
  decide +kernel

/-- Levin Example 3.7.3: the probability of two heads when flipping two coins is `1/4`. -/
@[kb "levin2025" "Example 3.7.3, p. 296"]
theorem levin_ex_3_7_3_two_heads :
    ((Finset.univ.filter (fun x : Bool × Bool => x = (true, true))).card : ℚ) /
      (Finset.univ : Finset (Bool × Bool)).card = 1 / 4 := by
  decide +kernel

/-- Levin Example 3.7.5: the probability of rolling an even number is `1/2`. -/
@[kb "levin2025" "Example 3.7.5, p. 296"]
theorem levin_ex_3_7_5_even_roll :
    (((Finset.Icc 1 6).filter (fun n => n % 2 = 0)).card : ℚ) / (Finset.Icc 1 6).card = 1 / 2 := by
  decide +kernel

/-- Levin Example 3.7.6: counts for four of a kind among five-card hands, and the equality of the
combination and permutation computations. -/
@[kb "levin2025" "Example 3.7.6, p. 297"]
theorem levin_ex_3_7_6_four_of_a_kind :
    Nat.choose 52 5 = 2598960 ∧ 13 * 48 = 624 ∧ Nat.descFactorial 52 5 = 311875200 ∧
      (13 * 48 : ℚ) / Nat.choose 52 5 = (13 * 48 * Nat.factorial 5) / Nat.descFactorial 52 5 := by
  refine ⟨by decide +kernel, rfl, by decide +kernel, ?_⟩
  rw [show Nat.choose 52 5 = 2598960 by decide +kernel,
    show Nat.descFactorial 52 5 = 311875200 by decide +kernel]
  norm_num [Nat.factorial]

/-- Levin Example 3.7.8: of the 1024 sequences of ten coin flips, 1023 contain a head. -/
@[kb "levin2025" "Example 3.7.8, p. 298"]
theorem levin_ex_3_7_8_at_least_one_head :
    (Finset.univ.filter (fun f : Fin 10 → Bool => ∃ i, f i = true)).card = 1023 ∧
      Fintype.card (Fin 10 → Bool) = 1024 := by
  refine ⟨by decide +kernel, ?_⟩
  rw [Fintype.card_fun]
  simp

/-- Levin Example 3.7.9: at least one 6 in four rolls has probability `671/1296`, above one half,
while at least one double 6 in 24 rolls of two dice has probability below one half. -/
@[kb "levin2025" "Example 3.7.9, p. 299"]
theorem levin_ex_3_7_9_de_mere :
    ((Finset.univ.filter (fun f : Fin 4 → Fin 6 => ∃ i, f i = 5)).card : ℚ) / 1296 = 671 / 1296 ∧
      (1 : ℚ) / 2 < 1 - (5 / 6) ^ 4 ∧ 1 - (35 / 36 : ℚ) ^ 24 < 1 / 2 := by
  refine ⟨?_, by norm_num, by norm_num⟩
  have : (Finset.univ.filter (fun f : Fin 4 → Fin 6 => ∃ i, f i = 5)).card = 671 := by
    decide +kernel
  rw [this]
  norm_num

/-- Levin Example 3.7.11: rolling an even number or a number below 3 has four favourable
outcomes out of six, matching `3 + 2 - 1`. -/
@[kb "levin2025" "Example 3.7.11, p. 300"]
theorem levin_ex_3_7_11_even_or_small :
    ((Finset.Icc 1 6).filter (fun n => n % 2 = 0 ∨ n < 3)).card = 4 ∧
      ((Finset.Icc 1 6).filter (fun n => n % 2 = 0)).card = 3 ∧
      ((Finset.Icc 1 6).filter (fun n => n < 3)).card = 2 ∧
      ((Finset.Icc 1 6).filter (fun n => n % 2 = 0 ∧ n < 3)).card = 1 := by
  decide +kernel

/-- Levin Example 3.7.12: an even die roll together with a head has probability `1/4`
(die faces are `i + 1` for `i : Fin 6`). -/
@[kb "levin2025" "Example 3.7.12, p. 300"]
theorem levin_ex_3_7_12_die_and_coin :
    ((Finset.univ.filter (fun x : Fin 6 × Bool => (x.1.val + 1) % 2 = 0 ∧ x.2 = true)).card : ℚ) /
      (Finset.univ : Finset (Fin 6 × Bool)).card = 1 / 4 := by
  decide +kernel

/-- Levin Example 3.7.14: on a 12-sided die, multiples of 3 and of 4 are independent, multiples of
3 and numbers below 7 are independent, but multiples of 4 and numbers below 7 are not. -/
@[kb "levin2025" "Example 3.7.14, p. 302"]
theorem levin_ex_3_7_14_independence :
    let S : Finset ℕ := Finset.Icc 1 12
    let P : Finset ℕ → ℚ := fun E => (E.card : ℚ) / S.card
    let A := S.filter (fun n => 3 ∣ n)
    let B := S.filter (fun n => 4 ∣ n)
    let C := S.filter (fun n => n < 7)
    P (A ∩ B) = P A * P B ∧ P (A ∩ C) = P A * P C ∧ P (B ∩ C) ≠ P B * P C := by
  decide +kernel

/-- Levin Example 3.7.16: two dice, given that at least one shows a 4, the chance the sum is 7
is `2/11` (die faces are `i + 1`). -/
@[kb "levin2025" "Example 3.7.16, p. 304"]
theorem levin_ex_3_7_16_sum_given_four :
    let S : Finset (Fin 6 × Fin 6) := Finset.univ
    let B := S.filter (fun x => x.1.val = 3 ∨ x.2.val = 3)
    let A := S.filter (fun x => x.1.val + x.2.val + 2 = 7)
    ((A ∩ B).card : ℚ) / B.card = 2 / 11 ∧ (A.card : ℚ) / S.card = 1 / 6 := by
  decide +kernel

/-- Levin Example 3.7.17: drawing two cards in order, the chance the second is a face card given
the first is red is `3/13`, and the chance the first is red given the second is a face card is
`1/2` (card `(suit, value)`; suits 0 and 1 are red, values 10 to 12 are face cards). -/
@[kb "levin2025" "Example 3.7.17, p. 304"]
theorem levin_ex_3_7_17_red_face :
    let S : Finset ((Fin 4 × Fin 13) × (Fin 4 × Fin 13)) :=
      Finset.univ.filter (fun x => x.1 ≠ x.2)
    let A := S.filter (fun x => x.1.1.val < 2)
    let B := S.filter (fun x => 10 ≤ x.2.2.val)
    let AB := S.filter (fun x => x.1.1.val < 2 ∧ 10 ≤ x.2.2.val)
    S.card = 52 * 51 ∧ (AB.card : ℚ) / A.card = 3 / 13 ∧ (AB.card : ℚ) / B.card = 1 / 2 := by
  intro S A B AB
  have h1 : S.card = 2652 := by decide +kernel
  have h2 : A.card = 1326 := by decide +kernel
  have h3 : B.card = 612 := by decide +kernel
  have h4 : AB.card = 306 := by decide +kernel
  rw [h1, h2, h3, h4]
  norm_num

end UndergradKB.Foundations.Course
