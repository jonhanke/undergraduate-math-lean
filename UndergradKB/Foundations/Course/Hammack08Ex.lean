import Mathlib.Data.Set.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Order.Group.Int
import UndergradKB.Common

/-!
# Course layer: Hammack, Book of Proof, Chapter 8, worked examples
-/

namespace UndergradKB.Foundations.Course

/-- Hammack Example 8.5: every integer divisible by 18 is divisible by 6. -/
@[kb "hammack2018" "Example 8.5, p. 172"]
theorem hammack_ex_8_5_dvd_18_subset_dvd_6 :
    {x : ℤ | 18 ∣ x} ⊆ {x : ℤ | 6 ∣ x} := by
  intro a ha
  simp only [Set.mem_ofPred_eq] at ha ⊢
  omega

/-- Hammack Example 8.6: an integer divisible by both 2 and 9 is divisible by 6. -/
@[kb "hammack2018" "Example 8.6, p. 172"]
theorem hammack_ex_8_6_dvd_2_inter_dvd_9 :
    {x : ℤ | 2 ∣ x} ∩ {x : ℤ | 9 ∣ x} ⊆ {x : ℤ | 6 ∣ x} := by
  intro a ha
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at ha ⊢
  omega

/-- Hammack Example 8.7: congruence mod 6 of a pair implies congruence mod 3. -/
@[kb "hammack2018" "Example 8.7, p. 172"]
theorem hammack_ex_8_7_modeq_six_subset_three :
    {p : ℤ × ℤ | p.1 ≡ p.2 [ZMOD 6]} ⊆ {p : ℤ × ℤ | p.1 ≡ p.2 [ZMOD 3]} := by
  intro p hp
  simp only [Set.mem_ofPred_eq, Int.ModEq] at hp ⊢
  omega

end UndergradKB.Foundations.Course
