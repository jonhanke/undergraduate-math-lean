import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Digits.Div
import UndergradKB.Common

/-!
# Course layer: Levin, Chapter 6 (congruences)
-/

namespace UndergradKB.Foundations.Course

/-- FO-120. Congruence modulo `n` is reflexive, symmetric and transitive. -/
@[kb "levin2025" "Box §6.2.3, p. 457"]
theorem levin_box_6_2_3_modEq_equivalence (n : ℤ) : Equivalence (Int.ModEq n) :=
  ⟨Int.ModEq.refl, Int.ModEq.symm, Int.ModEq.trans⟩

/-- FO-123. Cancellation: `a d ≡ b d (mod n)` gives `a ≡ b (mod n / gcd(n, d))`. -/
@[kb "levin2025" "Box §6.2.3, p. 460", kb "levin2025" "Ex 6.2.5, p. 460"]
theorem levin_box_6_2_3_cancel (n a b d : ℤ) (hn : 0 < n) (h : a * d ≡ b * d [ZMOD n]) :
    a ≡ b [ZMOD n / (Int.gcd n d : ℤ)] :=
  Int.ModEq.cancel_right_div_gcd hn h

/-- FO-126. A natural number is congruent to its digit sum modulo 9 and modulo 3, which gives
the divisibility tests. -/
@[kb "levin2025" "Ex 6.2.3, p. 459"]
theorem levin_ex_6_2_3_digit_sum (n : ℕ) :
    n ≡ (Nat.digits 10 n).sum [MOD 9] ∧ n ≡ (Nat.digits 10 n).sum [MOD 3] ∧
      (9 ∣ n ↔ 9 ∣ (Nat.digits 10 n).sum) ∧ (3 ∣ n ↔ 3 ∣ (Nat.digits 10 n).sum) :=
  ⟨Nat.modEq_nine_digits_sum n, Nat.modEq_three_digits_sum n, Nat.nine_dvd_iff n,
    Nat.three_dvd_iff n⟩

end UndergradKB.Foundations.Course
