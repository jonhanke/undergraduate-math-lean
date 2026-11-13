import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Interval
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Interval.Finset.Nat
import UndergradKB.Common

/-!
# Course layer: Hammack, Book of Proof, Chapter 3, further worked examples

The multiplication, addition and subtraction examples (3.1 to 3.7) and the pigeonhole applications (3.24 to 3.26).
Symbols `A, ..., G` are encoded as `0, ..., 6`.
-/

namespace UndergradKB.Foundations.Course

/-- Hammack Example 3.1: license plates made of three letters followed by four digits number
`26^3 * 10^4 = 175760000`. -/
@[kb "hammack2018" "Example 3.1, p. 81"]
theorem hammack_ex_3_1_license_plates :
    Fintype.card ((Fin 3 → Fin 26) × (Fin 4 → Fin 10)) = 175760000 := by
  simp

/-- Hammack Example 3.2: a drink order (milk, size, shots) with 3, 3 and 2 options has 18 outcomes. -/
@[kb "hammack2018" "Example 3.2, p. 81"]
theorem hammack_ex_3_2_latte_choices :
    Fintype.card (Fin 3 × Fin 3 × Fin 2) = 18 := by
  simp

/-- Hammack Example 3.4: repetition-free lists `(x₁, ..., x₅)` from `A..G` whose first entry is `B`, `C` or `D`
and whose last entry is a vowel (`A` or `E`) number `3 * 5 * 4 * 3 * 2 = 360`. -/
@[kb "hammack2018" "Example 3.4, p. 84"]
theorem hammack_ex_3_4_restricted_lists :
    (({1, 2, 3} ×ˢ Finset.range 7 ×ˢ Finset.range 7 ×ˢ Finset.range 7 ×ˢ {0, 4} :
        Finset (ℕ × ℕ × ℕ × ℕ × ℕ)).filter
      (fun l => l.1 ≠ l.2.1 ∧ l.1 ≠ l.2.2.1 ∧ l.1 ≠ l.2.2.2.1 ∧ l.1 ≠ l.2.2.2.2 ∧
        l.2.1 ≠ l.2.2.1 ∧ l.2.1 ≠ l.2.2.2.1 ∧ l.2.1 ≠ l.2.2.2.2 ∧
        l.2.2.1 ≠ l.2.2.2.1 ∧ l.2.2.1 ≠ l.2.2.2.2 ∧ l.2.2.2.1 ≠ l.2.2.2.2)).card = 360 := by
  decide +kernel

/-- Hammack Example 3.5: repetition-free lists of length 4 from `A..G` that contain an `E` number 480. -/
@[kb "hammack2018" "Example 3.5, p. 86"]
theorem hammack_ex_3_5_lists_with_E :
    ((Finset.range 7 ×ˢ Finset.range 7 ×ˢ Finset.range 7 ×ˢ Finset.range 7 :
        Finset (ℕ × ℕ × ℕ × ℕ)).filter
      (fun l => l.1 ≠ l.2.1 ∧ l.1 ≠ l.2.2.1 ∧ l.1 ≠ l.2.2.2 ∧ l.2.1 ≠ l.2.2.1 ∧ l.2.1 ≠ l.2.2.2 ∧
        l.2.2.1 ≠ l.2.2.2 ∧ (l.1 = 4 ∨ l.2.1 = 4 ∨ l.2.2.1 = 4 ∨ l.2.2.2 = 4))).card = 480 := by
  decide +kernel

/-- Hammack Example 3.6: the even five-digit numbers with no digit 0 and exactly one digit 6 number 10240.
A number is a 5-tuple of digits from `1..9` (no zero) whose last digit lies in `{2, 4, 6, 8}` (even) and which has
exactly one entry equal to 6. -/
@[kb "hammack2018" "Example 3.6, p. 87"]
theorem hammack_ex_3_6_even_numbers_one_six :
    ((Finset.Icc 1 9 ×ˢ Finset.Icc 1 9 ×ˢ Finset.Icc 1 9 ×ˢ Finset.Icc 1 9 ×ˢ ({2, 4, 6, 8} : Finset ℕ) :
        Finset (ℕ × ℕ × ℕ × ℕ × ℕ)).filter
      (fun l => (if l.1 = 6 then 1 else 0) + (if l.2.1 = 6 then 1 else 0) + (if l.2.2.1 = 6 then 1 else 0) +
          (if l.2.2.2.1 = 6 then 1 else 0) + (if l.2.2.2.2 = 6 then 1 else 0) = 1)).card = 10240 := by
  decide +kernel

/-- Hammack Example 3.7: lists of length 4 from `A..G`, with repetition allowed, that contain at least
one `E` number `7^4 - 6^4 = 1105`. -/
@[kb "hammack2018" "Example 3.7, p. 88"]
theorem hammack_ex_3_7_lists_at_least_one_E :
    Fintype.card {f : Fin 4 → Fin 7 // ∃ i, f i = 4} = 1105 := by
  decide +kernel

/-- Hammack Example 3.24: any six distinct integers chosen from `0..9` contain two that add up to 9. -/
@[kb "hammack2018" "Example 3.24, p. 117"]
theorem hammack_ex_3_24_six_integers_sum_nine (S : Finset ℕ) (hS : S ⊆ Finset.range 10)
    (hcard : S.card = 6) : ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ a + b = 9 := by
  have hmaps : ∀ x ∈ S, min x (9 - x) ∈ Finset.range 5 := by
    intro x hx
    have := Finset.mem_range.mp (hS hx)
    simp only [Finset.mem_range]
    omega
  obtain ⟨a, ha, b, hb, hab, h⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (t := Finset.range 5) (by simp [hcard]) hmaps
  refine ⟨a, ha, b, hb, hab, ?_⟩
  have h1 := Finset.mem_range.mp (hS ha)
  have h2 := Finset.mem_range.mp (hS hb)
  omega

/-- Hammack Example 3.24 (sharpness): five integers from `0..9`, namely `0, 1, 2, 3, 4`, need not contain
two that add up to 9. -/
@[kb "hammack2018" "Example 3.24, p. 117"]
theorem hammack_ex_3_24_five_integers_no_pair :
    ∃ S : Finset ℕ, S ⊆ Finset.range 10 ∧ S.card = 5 ∧ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → a + b ≠ 9 := by
  refine ⟨{0, 1, 2, 3, 4}, by decide, by decide, ?_⟩
  decide

/-- Hammack Example 3.25: among any 49 gumballs of four colours, some colour occurs at least 13 times. -/
@[kb "hammack2018" "Example 3.25, p. 118"]
theorem hammack_ex_3_25_forty_nine_gumballs (color : Fin 49 → Fin 4) :
    ∃ c, 13 ≤ (Finset.univ.filter (fun i => color i = c)).card := by
  obtain ⟨c, hc⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card color (n := 12) (by simp)
  exact ⟨c, by simpa [Nat.succ_le_iff] using hc⟩

/-- Hammack Example 3.25 (49 is the least number): with 48 gumballs, 12 of each colour is possible, so no
colour need reach 13. -/
@[kb "hammack2018" "Example 3.25, p. 118"]
theorem hammack_ex_3_25_forty_eight_not_enough :
    ∃ color : Fin 48 → Fin 4, ∀ c, (Finset.univ.filter (fun i => color i = c)).card < 13 := by
  refine ⟨fun i => ⟨i.val % 4, by omega⟩, ?_⟩
  decide +kernel

/-- Hammack Example 3.26 (only the pigeonhole step; the area bound for a triangle cut into four congruent
quarter triangles is not formalised): if nine points are each assigned one of four regions, some three distinct
points are assigned the same region. -/
@[kb "hammack2018" "Example 3.26, p. 119"]
theorem hammack_ex_3_26_nine_points_four_regions (region : Fin 9 → Fin 4) :
    ∃ i j k, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ region i = region j ∧ region j = region k := by
  obtain ⟨c, hc⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card region (n := 2) (by simp)
  obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk⟩ := Finset.two_lt_card.mp hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj hk
  exact ⟨i, j, k, hij, hjk, hik, hi.trans hj.symm, hj.trans hk.symm⟩

end UndergradKB.Foundations.Course
