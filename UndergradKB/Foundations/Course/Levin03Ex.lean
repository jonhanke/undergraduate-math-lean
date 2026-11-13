import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import UndergradKB.Common

/-!
# Course layer: Levin, Discrete Mathematics, Chapter 3, worked examples
-/

namespace UndergradKB.Foundations.Course

/-- Levin Example 3.1.11: the binomial expansion of `(x + y)^5`, with coefficients from row 5 of Pascal's
triangle. -/
@[kb "levin2025" "Example 3.1.11, p. 222"]
theorem levin_ex_3_1_11_binomial_expansion (x y : ℤ) :
    (x + y) ^ 5 = x ^ 5 + 5 * x ^ 4 * y + 10 * x ^ 3 * y ^ 2 + 10 * x ^ 2 * y ^ 3 + 5 * x * y ^ 4 + y ^ 5 := by
  ring

/-- Levin Example 3.2.16: exactly 13 two-digit numbers with digits from `{1,...,5}` have an even digit sum. -/
@[kb "levin2025" "Example 3.2.16, p. 235"]
theorem levin_ex_3_2_16_even_digit_sum :
    ((Finset.Icc 1 5 ×ˢ Finset.Icc 1 5).filter (fun p : ℕ × ℕ => Even (p.1 + p.2))).card = 13 := by
  decide +kernel

/-- Levin Example 3.3.8: 36 of the numbers in `{1,...,50}` are multiples of 2, 3, or 5. -/
@[kb "levin2025" "Example 3.3.8, p. 244"]
theorem levin_ex_3_3_8_multiples_2_3_5 :
    ((Finset.Icc 1 50).filter (fun n : ℕ => 2 ∣ n ∨ 3 ∣ n ∨ 5 ∣ n)).card = 36 := by
  decide +kernel

/-- Levin Example 3.4.2: six distinct letters can be arranged in `6! = 720` ways. -/
@[kb "levin2025" "Example 3.4.2, p. 252"]
theorem levin_ex_3_4_2_six_letter_arrangements : Fintype.card (Equiv.Perm (Fin 6)) = 720 := by
  rw [Fintype.card_perm]
  decide +kernel

/-- Levin Example 3.4.5: there are 840 four-letter words from `a` through `g` without repeated letters. -/
@[kb "levin2025" "Example 3.4.5, p. 253"]
theorem levin_ex_3_4_5_four_letter_words : Fintype.card (Fin 4 ↪ Fin 7) = 840 := by
  rw [Fintype.card_embedding_eq]
  decide +kernel

/-- Levin Example 3.8.2: sharing 11 cookies among 3 kids with at most 4 each can be done in 3 ways. -/
@[kb "levin2025" "Example 3.8.2, p. 312"]
theorem levin_ex_3_8_2_cookies_at_most_four :
    (Finset.univ.filter (fun x : Fin 3 → Fin 5 => ∑ i, (x i : ℕ) = 11)).card = 3 := by
  decide +kernel

/-- Levin Example 3.8.3: 10 cookies cannot be given to 4 kids with at most 2 each; the count is 0. -/
@[kb "levin2025" "Example 3.8.3, p. 313"]
theorem levin_ex_3_8_3_cookies_at_most_two :
    (Finset.univ.filter (fun x : Fin 4 → Fin 3 => ∑ i, (x i : ℕ) = 10)).card = 0 := by
  decide +kernel

/-- Levin Example 3.8.4: 15 solutions of `x₁ + ... + x₅ = 13` have every `xᵢ` between 0 and 3. -/
@[kb "levin2025" "Example 3.8.4, p. 314"]
theorem levin_ex_3_8_4_bounded_solutions :
    (Finset.univ.filter (fun x : Fin 5 → Fin 4 => ∑ i, (x i : ℕ) = 13)).card = 15 := by
  decide +kernel

end UndergradKB.Foundations.Course
