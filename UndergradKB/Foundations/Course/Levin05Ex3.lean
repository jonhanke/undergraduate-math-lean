import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Ring
import UndergradKB.Common

/-!
# Course layer: Levin, Discrete Mathematics, Chapter 5, worked examples (wave 4)

Digits/letters: `X = {1,2,3,4}` is `Fin 4` (`1..4` are `0..3`), `Y = {a,b,c,d}` is `Fin 4`.
-/

namespace UndergradKB.Foundations.Course

/-- Levin Example 5.2.3: of the three arrow diagrams `X → Y`, `f = (d a c b)` and `g = (d a a b)` are
functions (every input has exactly one output), while the relation of `h` (nothing at 1, both `a` and `c`
at 2, `d` at 3, `b` at 4) is not: input 1 has no output and input 2 has two. -/
@[kb "levin2025" "Example 5.2.3, p. 426"]
theorem levin_ex_5_2_3_which_are_functions :
    let rf : Fin 4 → Fin 4 → Prop := fun x y => y = ![3, 0, 2, 1] x
    let rg : Fin 4 → Fin 4 → Prop := fun x y => y = ![3, 0, 0, 1] x
    let rh : Fin 4 → Fin 4 → Prop := fun x y =>
      (x = 1 ∧ (y = 0 ∨ y = 2)) ∨ (x = 2 ∧ y = 3) ∨ (x = 3 ∧ y = 1)
    (∀ x, ∃! y, rf x y) ∧ (∀ x, ∃! y, rg x y) ∧ ¬ (∀ x, ∃! y, rh x y) ∧
    (¬ ∃ y, rh 0 y) ∧ (¬ ∃! y, rh 1 y) := by
  refine ⟨fun x => ⟨_, rfl, fun y h => h⟩, fun x => ⟨_, rfl, fun y h => h⟩, ?_, ?_, ?_⟩
  · intro h
    obtain ⟨y, hy, -⟩ := h 0
    revert y; decide
  · intro ⟨y, hy⟩
    revert y; decide
  · rintro ⟨y, -, hu⟩
    have h0 := hu 0 (by simp)
    have h2 := hu 2 (by simp)
    exact absurd (h0.trans h2.symm) (by decide)

/-- Levin Example 5.2.5: the recursive definitions `f 0 = 3, f (n+1) = 2 f n`, `g 0 = 7, g (n+1) = g n + 2`,
`h 0 = 1, h (n+1) = (n+1) h n` determine `f n = 3 * 2^n`, `g n = 7 + 2n`, and `h n = n!`. -/
@[kb "levin2025" "Example 5.2.5, p. 428"]
theorem levin_ex_5_2_5_recursive_definitions :
    (∀ f : ℕ → ℕ, f 0 = 3 → (∀ n, f (n + 1) = 2 * f n) → ∀ n, f n = 3 * 2 ^ n) ∧
    (∀ g : ℕ → ℕ, g 0 = 7 → (∀ n, g (n + 1) = g n + 2) → ∀ n, g n = 7 + 2 * n) ∧
    (∀ h : ℕ → ℕ, h 0 = 1 → (∀ n, h (n + 1) = (n + 1) * h n) → ∀ n, h n = n.factorial) := by
  refine ⟨fun f h0 hs n => ?_, fun g h0 hs n => ?_, fun h h0 hs n => ?_⟩
  · induction n with
    | zero => simpa using h0
    | succ n ih => rw [hs, ih]; ring
  · induction n with
    | zero => simpa using h0
    | succ n ih => rw [hs, ih]; ring
  · induction n with
    | zero => simpa using h0
    | succ n ih => rw [hs, ih, Nat.factorial_succ]

end UndergradKB.Foundations.Course
