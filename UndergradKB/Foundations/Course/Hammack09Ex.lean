import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum.Prime
import UndergradKB.Common

/-!
# Course layer: Hammack, Book of Proof, Chapter 9, worked examples
-/

namespace UndergradKB.Foundations.Course

/-- Hammack Example 9.1: `n^2 - n + 11` is not prime for every integer `n`; `n = 11` is a counterexample. -/
@[kb "hammack2018" "Example 9.1, p. 187"]
theorem hammack_ex_9_1_not_always_prime :
    ¬ ∀ n : ℤ, (n ^ 2 - n + 11).natAbs.Prime := by
  intro h
  have := h 11
  norm_num at this

/-- Hammack Example 9.2: `A - (B ∩ C) = (A - B) ∩ (A - C)` fails in general
(take `A = {1,2,3}`, `B = {1,2}`, `C = {2,3}`). -/
@[kb "hammack2018" "Example 9.2, p. 188"]
theorem hammack_ex_9_2_set_diff_counterexample :
    ¬ ∀ A B C : Set ℕ, A \ (B ∩ C) = (A \ B) ∩ (A \ C) := by
  intro h
  have h1 := Set.ext_iff.mp (h {1, 2, 3} {1, 2} {2, 3}) 1
  simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  norm_num at h1

/-- Hammack Example 9.4: three distinct integers above 1 with `x ^ y = y ^ z` exist, namely 2, 16, 4. -/
@[kb "hammack2018" "Example 9.4, p. 189"]
theorem hammack_ex_9_4_exists_pow_triple :
    ∃ x y z : ℕ, 1 < x ∧ 1 < y ∧ 1 < z ∧ x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ x ^ y = y ^ z :=
  ⟨2, 16, 4, by norm_num⟩

end UndergradKB.Foundations.Course
