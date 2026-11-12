import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.Nat.Prime.Infinite
import UndergradKB.Common

/-!
# Course layer: Hammack, Chapter 6 (proof by contradiction)
-/

namespace UndergradKB.Foundations.Course

/-- FO-130. A real number is irrational iff it is not a quotient `a / b` of integers
with `b ≠ 0`. -/
@[kb "hammack2018" "Definition 6.1, p. 151"]
theorem hammack_def_6_1_irrational_iff (x : ℝ) :
    Irrational x ↔ ∀ a b : ℤ, b ≠ 0 → x ≠ a / b := by
  rw [irrational_iff_ne_rational]

/-- FO-131. The square root of 2 is irrational. -/
@[kb "hammack2018" "Prop §6.1, p. 151", kb "levin2025" "Ex 1.4.16, p. 93"]
theorem hammack_s6_1_sqrt_two_irrational : Irrational (Real.sqrt 2) :=
  irrational_sqrt_two

/-- FO-133. There are infinitely many primes: above every `n` lies a prime. -/
@[kb "hammack2018" "Prop §6.1, p. 152"]
theorem hammack_s6_1_infinitely_many_primes :
    (∀ n : ℕ, ∃ p, n ≤ p ∧ p.Prime) ∧ {p : ℕ | p.Prime}.Infinite :=
  ⟨Nat.exists_infinite_primes, Nat.infinite_setOfPred_prime⟩

/-- FO-140. Proof by contradiction: to show `P`, refute `¬P`; to show `P → Q`, assume `P`
and `¬Q` and reach a contradiction. -/
@[kb "hammack2018" "Outline §6.1, p. 150", kb "hammack2018" "Outline §6.2, p. 153",
  kb "levin2025" "Sec 1.4.4, p. 91", kb "levin2025" "Sec 1.4.5, p. 94"]
theorem hammack_o6_1_contradiction (P Q : Prop) :
    ((¬P → False) → P) ∧ ((P ∧ ¬Q → False) → P → Q) :=
  ⟨fun h => Classical.by_contradiction h,
    fun h hp => Classical.by_contradiction fun hq => h ⟨hp, hq⟩⟩

end UndergradKB.Foundations.Course
