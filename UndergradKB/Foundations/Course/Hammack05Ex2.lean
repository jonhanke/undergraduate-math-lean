import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Order.Group.Int
import UndergradKB.Common

/-!
# Course layer: Hammack, Book of Proof, Chapter 5, further worked examples
-/

namespace UndergradKB.Foundations.Course

/-- Hammack Example 5.1: the five sample congruences `9 ≡ 1 (mod 4)`, `6 ≡ 10 (mod 4)`, `14 ≢ 8 (mod 4)`,
`20 ≡ 4 (mod 8)` and `17 ≡ -4 (mod 3)`. -/
@[kb "hammack2018" "Example 5.1, p. 143"]
theorem hammack_ex_5_1_sample_congruences :
    (9 ≡ 1 [ZMOD 4]) ∧ (6 ≡ 10 [ZMOD 4]) ∧ ¬ (14 ≡ 8 [ZMOD 4]) ∧ (20 ≡ 4 [ZMOD 8]) ∧
      (17 ≡ -4 [ZMOD 3]) := by
  decide

/-- Hammack Example 5.1 (the divisibility reading): the same five facts, stated as `n ∣ (a - b)` or its
negation. -/
@[kb "hammack2018" "Example 5.1, p. 143"]
theorem hammack_ex_5_1_divisibility_form :
    (4 : ℤ) ∣ 9 - 1 ∧ (4 : ℤ) ∣ 6 - 10 ∧ ¬ (4 : ℤ) ∣ 14 - 8 ∧ (8 : ℤ) ∣ 20 - 4 ∧ (3 : ℤ) ∣ 17 - (-4) := by
  decide

/-- Hammack Example 5.1 (remainder reading): `6` and `10` leave the same remainder `2` on division by `4`,
while `14` and `8` leave different remainders `2` and `0`. -/
@[kb "hammack2018" "Example 5.1, p. 143"]
theorem hammack_ex_5_1_remainders :
    (6 : ℤ) % 4 = 2 ∧ (10 : ℤ) % 4 = 2 ∧ (14 : ℤ) % 4 = 2 ∧ (8 : ℤ) % 4 = 0 := by
  decide

end UndergradKB.Foundations.Course
