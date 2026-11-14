import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Algebra.Group.Int.Even
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime
import UndergradKB.Common

/-!
# Course layer: Hammack, Book of Proof, Chapter 2, worked examples (wave 4)

Quantified statements, their translations and their negations, with the truth values the book asserts.
-/

namespace UndergradKB.Foundations.Course

/-- Every real number has a real cube root (helper for Examples 2.5-2.13). -/
theorem hammack_real_cube_root (x : ℝ) : ∃ y : ℝ, y ^ 3 = x := by
  rcases le_total 0 x with h | h
  · refine ⟨x ^ ((1 : ℝ) / 3), ?_⟩
    rw [← Real.rpow_natCast, ← Real.rpow_mul h]
    norm_num
  · refine ⟨-((-x) ^ ((1 : ℝ) / 3)), ?_⟩
    have h' : 0 ≤ -x := by linarith
    have : ((-x) ^ ((1 : ℝ) / 3)) ^ 3 = -x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul h']
      norm_num
    calc (-((-x) ^ ((1 : ℝ) / 3))) ^ 3 = -(((-x) ^ ((1 : ℝ) / 3)) ^ 3) := by ring
      _ = x := by rw [this]; ring

/-- Hammack Example 2.5: the four translated statements are all true: every non-odd integer is even, some integer is
not even, every real has a real cube root, and the product of two rationals is rational. -/
@[kb "hammack2018" "Example 2.5, p. 66"]
theorem hammack_ex_2_5_true_translations :
    (∀ n : ℤ, ¬ Odd n → Even n) ∧ (∃ n : ℤ, ¬ Even n) ∧ (∀ x : ℝ, ∃ y : ℝ, y ^ 3 = x) ∧
      (∀ a b : ℝ, a ∈ Set.range ((↑) : ℚ → ℝ) → b ∈ Set.range ((↑) : ℚ → ℝ) →
        a * b ∈ Set.range ((↑) : ℚ → ℝ)) := by
  refine ⟨fun n h => by simpa using h, ⟨1, by decide⟩, hammack_real_cube_root, ?_⟩
  rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
  exact ⟨a * b, by push_cast; rfl⟩

/-- Hammack Example 2.6: the four translated statements are all false: not every integer is even, no integer squares
to 2, not every real is a square, and the square root of a product of rationals need not be rational. -/
@[kb "hammack2018" "Example 2.6, p. 66"]
theorem hammack_ex_2_6_false_translations :
    ¬ (∀ n : ℤ, Even n) ∧ ¬ (∃ n : ℤ, n ^ 2 = 2) ∧ ¬ (∀ x : ℝ, ∃ y : ℝ, y ^ 2 = x) ∧
      ¬ (∀ a b : ℚ, ∃ q : ℚ, (q : ℝ) = Real.sqrt ((a : ℝ) * b)) := by
  refine ⟨fun h => by simpa using h 1, ?_, ?_, ?_⟩
  · rintro ⟨n, hn⟩
    have h1 : n ≤ 1 := by nlinarith
    have h2 : -1 ≤ n := by nlinarith
    interval_cases n <;> omega
  · intro h
    obtain ⟨y, hy⟩ := h (-1)
    nlinarith [sq_nonneg y]
  · intro h
    obtain ⟨q, hq⟩ := h 1 2
    apply irrational_sqrt_two
    exact ⟨q, by rw [hq]; norm_num⟩

/-- Hammack Example 2.8: the Mean Value Theorem in its conditional form: continuity on `[a, b]` and
differentiability on `(a, b)` give a point `c` in `(a, b)` with `f' c = (f b - f a) / (b - a)`. -/
@[kb "hammack2018" "Example 2.8, p. 69"]
theorem hammack_ex_2_8_mean_value (f : ℝ → ℝ) (a b : ℝ) (hab : a < b) :
    (ContinuousOn f (Set.Icc a b) ∧ DifferentiableOn ℝ f (Set.Ioo a b)) →
      ∃ c ∈ Set.Ioo a b, deriv f c = (f b - f a) / (b - a) :=
  fun h => exists_deriv_eq_slope f hab h.1 h.2

/-- Hammack Example 2.9: Goldbach's conjecture quantifies over `X = {4, 6, 8, ...}`, the even integers above 2; this set
is the range of `k ↦ 2k + 4`, and the first few members of `X` are sums of two primes (the full conjecture is open). -/
@[kb "hammack2018" "Example 2.9, p. 70"]
theorem hammack_ex_2_9_goldbach_setup :
    {n : ℕ | Even n ∧ 2 < n} = Set.range (fun k : ℕ => 2 * k + 4) ∧
      (∀ n ∈ ({4, 6, 8, 10, 12, 14, 16, 18, 20} : Finset ℕ),
        ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q) := by
  refine ⟨?_, ?_⟩
  · ext n
    simp only [Set.mem_ofPred_eq, Set.mem_range]
    constructor
    · rintro ⟨⟨m, hm⟩, h⟩
      exact ⟨m - 2, by omega⟩
    · rintro ⟨k, rfl⟩
      exact ⟨⟨k + 2, by ring⟩, by omega⟩
  · intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨2, 2, by norm_num, by norm_num, rfl⟩
    · exact ⟨3, 3, by norm_num, by norm_num, rfl⟩
    · exact ⟨3, 5, by norm_num, by norm_num, rfl⟩
    · exact ⟨3, 7, by norm_num, by norm_num, rfl⟩
    · exact ⟨5, 7, by norm_num, by norm_num, rfl⟩
    · exact ⟨3, 11, by norm_num, by norm_num, rfl⟩
    · exact ⟨3, 13, by norm_num, by norm_num, rfl⟩
    · exact ⟨5, 13, by norm_num, by norm_num, rfl⟩
    · exact ⟨3, 17, by norm_num, by norm_num, rfl⟩

/-- Hammack Example 2.10: De Morgan's law for "or": it is not the case that (P or Q) exactly when not P and not Q. -/
@[kb "hammack2018" "Example 2.10, p. 72"]
theorem hammack_ex_2_10_not_or (P Q : Prop) : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q := not_or

/-- Hammack Example 2.11: for integers `x, y`, "x and y are both odd" fails exactly when `x` is even or `y` is even. -/
@[kb "hammack2018" "Example 2.11, p. 72"]
theorem hammack_ex_2_11_not_both_odd (x y : ℤ) : ¬ (Odd x ∧ Odd y) ↔ Even x ∨ Even y := by
  rw [not_and_or, Int.not_odd_iff_even, Int.not_odd_iff_even]

/-- Hammack Example 2.12: the negation of "every real square is non-negative" is "some real has negative square";
the original is true, so the negation is false. -/
@[kb "hammack2018" "Example 2.12, p. 73"]
theorem hammack_ex_2_12_neg_square_nonneg :
    ((¬ ∀ x : ℝ, x ^ 2 ≥ 0) ↔ ∃ x : ℝ, x ^ 2 < 0) ∧ (∀ x : ℝ, x ^ 2 ≥ 0) := by
  refine ⟨by simp, fun x => sq_nonneg x⟩

/-- Hammack Example 2.13: the negation of "every real has a real cube root" is "some real `x` has `y ^ 3 ≠ x` for every
`y`"; the original statement is true, so this negation is false. -/
@[kb "hammack2018" "Example 2.13, p. 73"]
theorem hammack_ex_2_13_neg_cube_root :
    ((¬ ∀ x : ℝ, ∃ y : ℝ, y ^ 3 = x) ↔ ∃ x : ℝ, ∀ y : ℝ, y ^ 3 ≠ x) ∧
      ¬ ∃ x : ℝ, ∀ y : ℝ, y ^ 3 ≠ x := by
  refine ⟨by simp, ?_⟩
  rintro ⟨x, hx⟩
  obtain ⟨y, hy⟩ := hammack_real_cube_root x
  exact hx y hy

/-- Hammack Example 2.14: for a fixed integer `a`, the negation of "if `a` is odd then `a ^ 2` is odd" is "`a` is odd
and `a ^ 2` is not odd"; the original conditional is true. -/
@[kb "hammack2018" "Example 2.14, p. 74"]
theorem hammack_ex_2_14_neg_odd_square (a : ℤ) :
    (¬ (Odd a → Odd (a ^ 2)) ↔ Odd a ∧ ¬ Odd (a ^ 2)) ∧ (Odd a → Odd (a ^ 2)) :=
  ⟨not_imp, fun h => h.pow⟩

/-- Hammack Example 2.15: the negation of "for every integer `x`, `x` odd implies `x ^ 2` odd" is "some odd integer
has a square that is not odd"; the original is true, so the negation is false. -/
@[kb "hammack2018" "Example 2.15, p. 74"]
theorem hammack_ex_2_15_neg_odd_square_forall :
    ((¬ ∀ x : ℤ, Odd x → Odd (x ^ 2)) ↔ ∃ x : ℤ, Odd x ∧ ¬ Odd (x ^ 2)) ∧
      ∀ x : ℤ, Odd x → Odd (x ^ 2) := by
  refine ⟨by simp, fun x hx => hx.pow⟩

end UndergradKB.Foundations.Course
