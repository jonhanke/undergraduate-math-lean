import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Basic
import UndergradKB.Common.Attr

/-!
# Collatz sequences

Source: Keller--Trotter, *Applied Combinatorics* (2017), Example 1.8 (p. 33).
From a positive integer `n` the next term is `3n + 1` if `n` is odd and `n / 2` if `n` is even; the
sequence halts when it reaches `1`. Whether every start reaches `1` is the open Collatz problem
(posed in the book as a question, not a result).
-/

namespace UndergradKB.Combinatorics

/-- CO-326. One Collatz step: `n ↦ 3n + 1` for odd `n`, `n ↦ n / 2` for even `n`. -/
@[kb "kellertrotter2017" "Example 1.8, p. 33"]
def collatzStep (n : ℕ) : ℕ := if n % 2 = 1 then 3 * n + 1 else n / 2

/-- CO-326. The Collatz sequence from `n` reaches `1` (and so halts) if some iterate of the step
equals `1`. -/
@[kb "kellertrotter2017" "Example 1.8, p. 33"]
def CollatzReachesOne (n : ℕ) : Prop := ∃ k, collatzStep^[k] n = 1

/-- The first `k + 1` terms `n, step n, …, step^k n` of the Collatz sequence from `n`. -/
def collatzList (n : ℕ) (k : ℕ) : List ℕ := (List.range (k + 1)).map fun i => collatzStep^[i] n

/-- CO-326, Example 1.8. Starting from `28` the sequence is
`28, 14, 7, 22, 11, 34, 17, 52, 26, 13, 40, 20, 10, 5, 16, 8, 4, 2, 1`. -/
@[kb "kellertrotter2017" "Example 1.8, p. 33"]
theorem collatzList_28 :
    collatzList 28 18 = [28, 14, 7, 22, 11, 34, 17, 52, 26, 13, 40, 20, 10, 5, 16, 8, 4, 2, 1] := by
  decide

/-- CO-326, Example 1.8. Starting from `19` the first terms are `19, 58, 29, 88, 44, 22`. -/
@[kb "kellertrotter2017" "Example 1.8, p. 33"]
theorem collatzList_19 : collatzList 19 5 = [19, 58, 29, 88, 44, 22] := by decide

/-- CO-326, Example 1.8. Once two Collatz sequences share a term they agree from there on; in
particular the sequence from `19` reaches `1` because it meets the sequence from `28` at `22`. -/
@[kb "kellertrotter2017" "Example 1.8, p. 33"]
theorem collatzReachesOne_19 : CollatzReachesOne 19 := ⟨20, by decide⟩

/-- Two Collatz sequences that meet agree from then on. -/
theorem collatz_merge {m n i j : ℕ} (h : collatzStep^[i] m = collatzStep^[j] n) (k : ℕ) :
    collatzStep^[i + k] m = collatzStep^[j + k] n := by
  rw [Nat.add_comm i, Nat.add_comm j, Function.iterate_add_apply, Function.iterate_add_apply, h]

end UndergradKB.Combinatorics
