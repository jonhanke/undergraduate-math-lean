import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic.TFAE
import UndergradKB.Common

/-!
# Course layer: Hammack, Chapter 7 (proving non-conditional statements)
-/

namespace UndergradKB.Foundations.Course

/-- FO-109. There is an even prime, and every prime is `2` or odd. -/
@[kb "hammack2018" "Prop §7.3, p. 163", kb "levin2025" "Ex 1.4.13, p. 91"]
theorem hammack_s7_3_even_prime :
    (∃ p : ℕ, p.Prime ∧ Even p) ∧ ∀ p : ℕ, p.Prime → p = 2 ∨ Odd p :=
  ⟨⟨2, Nat.prime_two, even_two⟩, fun _ hp => hp.eq_two_or_odd'⟩

/-- FO-114. Bezout: `gcd(a, b) = a k + b l` for some integers `k`, `l`. -/
@[kb "hammack2018" "Proposition 7.1, p. 164"]
theorem hammack_prop_7_1_bezout (a b : ℕ) :
    ∃ k l : ℤ, (Nat.gcd a b : ℤ) = a * k + b * l :=
  ⟨Nat.gcdA a b, Nat.gcdB a b, Nat.gcd_eq_gcd_ab a b⟩

/-- FO-124. `a ≡ b (mod 6)` iff `a ≡ b (mod 2)` and `a ≡ b (mod 3)`. -/
@[kb "hammack2018" "Prop §7.1, p. 160"]
theorem hammack_s7_1_modEq_six (a b : ℤ) :
    a ≡ b [ZMOD 6] ↔ a ≡ b [ZMOD 2] ∧ a ≡ b [ZMOD 3] := by
  simp only [Int.ModEq]
  omega

/-- FO-142. To show three statements equivalent it suffices to prove a cycle of implications. -/
@[kb "hammack2018" "Prop §7.2, p. 161"]
theorem hammack_s7_2_cycle_tfae (P Q R : Prop) (h1 : P → Q) (h2 : Q → R) (h3 : R → P) :
    [P, Q, R].TFAE := by
  tfae_have 1 → 2 := h1
  tfae_have 2 → 3 := h2
  tfae_have 3 → 1 := h3
  tfae_finish

end UndergradKB.Foundations.Course
