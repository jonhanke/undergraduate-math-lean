import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import UndergradKB.Common

/-!
# Course layer: Levin, Discrete Mathematics, Chapter 4, worked examples
-/

namespace UndergradKB.Foundations.Course

/-- Levin Example 4.1.7: the rice-grain sequence with `a 1 = 1` and `a (n+1) = 2 * a n + 1` has
`a n = 2^n - 1`, so day 30 brings `2^30 - 1` grains. -/
@[kb "levin2025" "Example 4.1.7, p. 335"]
theorem levin_ex_4_1_7_rice_grains (a : ℕ → ℕ) (h1 : a 1 = 1) (hrec : ∀ n, 1 ≤ n → a (n + 1) = 2 * a n + 1) :
    (∀ n, 1 ≤ n → a n + 1 = 2 ^ n) ∧ a 30 = 2 ^ 30 - 1 := by
  have key : ∀ n, 1 ≤ n → a n + 1 = 2 ^ n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp [h1]
    | succ n hn ih =>
      rw [hrec n hn, pow_succ]
      omega
  refine ⟨key, ?_⟩
  have := key 30 (by norm_num)
  omega

/-- Levin Example 4.3.4: the sequence `2, 3, 7, 14, 24, 37, ...` with `a 0 = 2` and
`a n = a (n-1) + 3n - 2` satisfies `2 * a n = 4 + 3n^2 - n`, i.e. `a n = 2 + n(3n-1)/2`. -/
@[kb "levin2025" "Example 4.3.4, p. 361"]
theorem levin_ex_4_3_4_partial_sums_closed_form (a : ℕ → ℤ) (h0 : a 0 = 2)
    (hrec : ∀ n : ℕ, a (n + 1) = a n + 3 * ((n : ℤ) + 1) - 2) :
    ∀ n : ℕ, 2 * a n = 4 + 3 * (n : ℤ) ^ 2 - n := by
  intro n
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    rw [hrec n]
    push_cast
    nlinarith [ih]

/-- Levin Example 4.4.4: the repeating decimal `0.464646...`, as the geometric series with first term
`0.46` and ratio `0.01`, sums to `46/99`. -/
@[kb "levin2025" "Example 4.4.4, p. 376"]
theorem levin_ex_4_4_4_repeating_decimal :
    HasSum (fun n : ℕ => (46 / 100 : ℝ) * (1 / 100) ^ n) (46 / 99) := by
  have h := (hasSum_geometric_of_lt_one (r := (1 / 100 : ℝ)) (by norm_num) (by norm_num)).mul_left (46 / 100)
  convert h using 1
  norm_num

end UndergradKB.Foundations.Course
