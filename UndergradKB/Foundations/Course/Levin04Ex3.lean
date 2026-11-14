import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.List.Range
import Mathlib.Tactic.Ring
import UndergradKB.Common

/-!
# Course layer: Levin, Discrete Mathematics, Chapter 4, worked examples (wave 4)
-/

namespace UndergradKB.Foundations.Course

/-- Levin Example 4.1.3: the triangular numbers `T n = n(n+1)/2` give `1,3,6,10,15,21` for `n = 1..6` with
next term `T 7 = 28`; the powers of two `2^n` give `1,2,4,8,16,32`, next `64`; the Fibonacci numbers
(`Nat.fib`) give `1,1,2,3,5,8,13`, next `21`. -/
@[kb "levin2025" "Example 4.1.3, p. 333"]
theorem levin_ex_4_1_3_next_terms :
    (List.range' 1 6).map (fun n => n * (n + 1) / 2) = [1, 3, 6, 10, 15, 21] ∧ 7 * 8 / 2 = 28 ∧
    (List.range 6).map (fun n => 2 ^ n) = [1, 2, 4, 8, 16, 32] ∧ 2 ^ 6 = 64 ∧
    (List.range' 1 7).map Nat.fib = [1, 1, 2, 3, 5, 8, 13] ∧ Nat.fib 8 = 21 := by
  decide

/-- Levin Example 4.1.9: the closed formulas found for the eight sequences (all starting at `n = 0`)
reproduce the listed terms: `b n = n(n+1)/2 + 1`, `c n = 2^(n+1) + 1`, `d n = n(n+1)`,
`e n = (n+2)(n+3)/2`, `f n = 2^n - 1`, `g n = 3 * 2^n`, `h n = 2^(n+2) + 2`,
`j n = 3((n+2)(n+3) - 1)`. -/
@[kb "levin2025" "Example 4.1.9, p. 338"]
theorem levin_ex_4_1_9_closed_formulas :
    (List.range 7).map (fun n => n * (n + 1) / 2 + 1) = [1, 2, 4, 7, 11, 16, 22] ∧
    (List.range 5).map (fun n => 2 ^ (n + 1) + 1) = [3, 5, 9, 17, 33] ∧
    (List.range 7).map (fun n => n * (n + 1)) = [0, 2, 6, 12, 20, 30, 42] ∧
    (List.range 6).map (fun n => (n + 2) * (n + 3) / 2) = [3, 6, 10, 15, 21, 28] ∧
    (List.range 6).map (fun n => 2 ^ n - 1) = [0, 1, 3, 7, 15, 31] ∧
    (List.range 5).map (fun n => 3 * 2 ^ n) = [3, 6, 12, 24, 48] ∧
    (List.range 5).map (fun n => 2 ^ (n + 2) + 2) = [6, 10, 18, 34, 66] ∧
    (List.range 5).map (fun n => 3 * ((n + 2) * (n + 3) - 1)) = [15, 33, 57, 87, 123] := by
  decide

/-- Levin Example 4.1.9 (second solution of part 7): `2(2^n + 1)`-style identity: `h n = 2 * c n`, i.e.
`2^(n+2) + 2 = 2 * (2^(n+1) + 1)` for all `n`; and part 4's shift `e n = T (n+2)`. -/
@[kb "levin2025" "Example 4.1.9, p. 339"]
theorem levin_ex_4_1_9_sequence_identities :
    (∀ n : ℕ, 2 ^ (n + 2) + 2 = 2 * (2 ^ (n + 1) + 1)) ∧
    (∀ n : ℕ, (n + 2) * (n + 3) / 2 = (n + 2) * ((n + 2) + 1) / 2) := by
  refine ⟨fun n => by ring, fun n => ?_⟩
  ring_nf

end UndergradKB.Foundations.Course
