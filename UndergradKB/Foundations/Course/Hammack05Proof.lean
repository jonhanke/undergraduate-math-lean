import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith
import UndergradKB.Common

/-!
# Course layer: Hammack, Chapter 5 (contrapositive proof; congruence)
-/

namespace UndergradKB.Foundations.Course

/-- FO-118. Congruence mod `n` in the book's form: `a ≡ b (mod n)` iff `n ∣ a - b`. -/
@[kb "hammack2018" "Definition 5.1, p. 143", kb "levin2025" "Box §6.2.2, p. 456"]
theorem hammack_def_5_1_modEq_iff_dvd (a b n : ℤ) : a ≡ b [ZMOD n] ↔ n ∣ a - b := by
  rw [Int.modEq_iff_dvd]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨-c, by linarith⟩
  · rintro ⟨c, hc⟩
    exact ⟨-c, by linarith⟩

/-- FO-119. Same remainder, divisibility of the difference, and `a = b + k n` all agree. -/
@[kb "hammack2018" "Prop §5.2, p. 143", kb "levin2025" "Box §6.2.2, p. 457"]
theorem hammack_s5_2_modEq_equiv (a b n : ℤ) :
    (a % n = b % n ↔ n ∣ a - b) ∧ (n ∣ a - b ↔ ∃ k : ℤ, a = b + k * n) := by
  refine ⟨hammack_def_5_1_modEq_iff_dvd a b n, ?_⟩
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, by linarith⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by linarith⟩

/-- FO-121. Congruence mod `n` is compatible with sums, differences and products, and
`a ≡ b` gives `a c ≡ b c`. -/
@[kb "hammack2018" "Prop §5.2, p. 144", kb "levin2025" "Box §6.2.3, p. 458"]
theorem hammack_s5_2_modEq_arith {n a b c d : ℤ} (h : a ≡ b [ZMOD n]) (h' : c ≡ d [ZMOD n]) :
    a + c ≡ b + d [ZMOD n] ∧ a - c ≡ b - d [ZMOD n] ∧ a * c ≡ b * d [ZMOD n] ∧
      a * c ≡ b * c [ZMOD n] :=
  ⟨h.add h', h.sub h', h.mul h', h.mul_right c⟩

/-- FO-122. If `a ≡ b (mod n)` then `a ^ p ≡ b ^ p (mod n)`; in particular for squares. -/
@[kb "hammack2018" "Prop §5.2, p. 144", kb "levin2025" "Ex 6.2.4, p. 459"]
theorem hammack_s5_2_modEq_pow {n a b : ℤ} (h : a ≡ b [ZMOD n]) (p : ℕ) :
    a ^ p ≡ b ^ p [ZMOD n] :=
  h.pow p

/-- FO-139. An implication is equivalent to its contrapositive. -/
@[kb "hammack2018" "Outline §5.1, p. 141", kb "levin2025" "Sec 1.4.3, p. 89"]
theorem hammack_o5_1_contrapositive (P Q : Prop) : (P → Q) ↔ (¬Q → ¬P) :=
  not_imp_not.symm

end UndergradKB.Foundations.Course
