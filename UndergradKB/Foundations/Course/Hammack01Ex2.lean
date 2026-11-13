import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Lattice.Indexed
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import UndergradKB.Common

/-!
# Course layer: Hammack, Book of Proof, Chapter 1, further worked examples

Numeric set computations of Hammack Chapter 1 (dice pairs, power sets, small set operations, indexed unions).
In Example 1.8 the letters `a, b, c, d, e, f` are encoded as `0, ..., 5` and the numbers `1, 2, 3` as `11, 12, 13`.
-/

namespace UndergradKB.Foundations.Course

/-- Hammack Example 1.3: the set of outcomes of two rolls of a six-sided die has `6 * 6 = 36` elements. -/
@[kb "hammack2018" "Example 1.3, p. 21"]
theorem hammack_ex_1_3_dice_pairs :
    Fintype.card (Fin 6 × Fin 6) = 36 := by
  simp

/-- Hammack Example 1.7(1): the power set of `{0, 1, 3}` is listed by its eight subsets. -/
@[kb "hammack2018" "Example 1.7, p. 28"]
theorem hammack_ex_1_7_powerset_three :
    ({0, 1, 3} : Finset ℕ).powerset =
      {∅, {0}, {1}, {3}, {0, 1}, {0, 3}, {1, 3}, {0, 1, 3}} := by
  decide +kernel

/-- Hammack Example 1.7(2): the power set of `{1, 2}` has the four subsets `∅, {1}, {2}, {1, 2}`. -/
@[kb "hammack2018" "Example 1.7, p. 28"]
theorem hammack_ex_1_7_powerset_two :
    ({1, 2} : Finset ℕ).powerset = {∅, {1}, {2}, {1, 2}} := by
  decide +kernel

/-- Hammack Example 1.7(3)-(4): the power set of a singleton has two members and the power set of the
empty set has exactly one member, the empty set. -/
@[kb "hammack2018" "Example 1.7, p. 28"]
theorem hammack_ex_1_7_powerset_small :
    ({1} : Finset ℕ).powerset = {∅, {1}} ∧ (∅ : Finset ℕ).powerset = {∅} := by
  decide +kernel

/-- Hammack Example 1.7 (the pattern the book points out): in each instance the power set of a finite
set `A` has `2 ^ |A|` elements. -/
@[kb "hammack2018" "Example 1.7, p. 28"]
theorem hammack_ex_1_7_card_powerset (A : Finset ℕ) :
    A.powerset.card = 2 ^ A.card := by
  exact Finset.card_powerset A

/-- Hammack Example 1.7(7): the product of the power set of a one-element set with the power set of
the empty set has two members, namely `(∅, ∅)` and `({a}, ∅)`. -/
@[kb "hammack2018" "Example 1.7, p. 28"]
theorem hammack_ex_1_7_powerset_product :
    ({1} : Finset ℕ).powerset ×ˢ (∅ : Finset ℕ).powerset =
      ({(∅, ∅), ({1}, ∅)} : Finset (Finset ℕ × Finset ℕ)) := by
  decide +kernel

/-- Hammack Example 1.8(1)-(5): for `A = {a,b,c,d,e}` and `B = {d,e,f}` (letters encoded `0..5`) the union
is `{a,..,f}`, the intersection `{d,e}`, `A - B = {a,b,c}`, `B - A = {f}` and the symmetric difference is
`{a,b,c,f}`. -/
@[kb "hammack2018" "Example 1.8, p. 30"]
theorem hammack_ex_1_8_set_operations :
    let A : Finset ℕ := {0, 1, 2, 3, 4}
    let B : Finset ℕ := {3, 4, 5}
    A ∪ B = {0, 1, 2, 3, 4, 5} ∧ A ∩ B = {3, 4} ∧ A \ B = {0, 1, 2} ∧ B \ A = {5} ∧
      (A \ B) ∪ (B \ A) = {0, 1, 2, 5} := by
  decide +kernel

/-- Hammack Example 1.8(6)-(9): with `C = {1, 2, 3}` (encoded `{11, 12, 13}`, so it shares nothing with the
letters), `A ∪ C` is the eight-element set, `A ∩ C = ∅`, `A - C = A` and `(A ∩ C) ∪ (A - C) = A`. -/
@[kb "hammack2018" "Example 1.8, p. 30"]
theorem hammack_ex_1_8_with_numbers :
    let A : Finset ℕ := {0, 1, 2, 3, 4}
    let C : Finset ℕ := {11, 12, 13}
    A ∪ C = {0, 1, 2, 3, 4, 11, 12, 13} ∧ A ∩ C = ∅ ∧ A \ C = {0, 1, 2, 3, 4} ∧
      (A ∩ C) ∪ (A \ C) = {0, 1, 2, 3, 4} := by
  decide +kernel

/-- Hammack Example 1.8(10)-(11): `(A ∩ B) × B` is the six pairs `(d,d),(d,e),(d,f),(e,d),(e,e),(e,f)`
and `(A × C) ∩ (B × C)` is the six pairs with first entry `d` or `e` and second entry in `C`. -/
@[kb "hammack2018" "Example 1.8, p. 30"]
theorem hammack_ex_1_8_products :
    let A : Finset ℕ := {0, 1, 2, 3, 4}
    let B : Finset ℕ := {3, 4, 5}
    let C : Finset ℕ := {11, 12, 13}
    (A ∩ B) ×ˢ B = {(3, 3), (3, 4), (3, 5), (4, 3), (4, 4), (4, 5)} ∧
      (A ×ˢ C) ∩ (B ×ˢ C) = {(3, 11), (3, 12), (3, 13), (4, 11), (4, 12), (4, 13)} := by
  decide +kernel

/-- Hammack Example 1.12: for `A₁ = {0,2,5}`, `A₂ = {1,2,5}`, `A₃ = {2,5,7}` the indexed union is
`{0,1,2,5,7}` and the indexed intersection is `{2,5}`. -/
@[kb "hammack2018" "Example 1.12, p. 37"]
theorem hammack_ex_1_12_indexed_union_inter :
    let A : Fin 3 → Set ℕ := ![{0, 2, 5}, {1, 2, 5}, {2, 5, 7}]
    (⋃ i, A i) = {0, 1, 2, 5, 7} ∧ (⋂ i, A i) = {2, 5} := by
  intro A
  constructor
  · ext x
    simp only [Set.mem_iUnion, Fin.exists_fin_succ, A]
    simp [Matrix.cons_val_zero, Matrix.cons_val_succ]
    omega
  · ext x
    simp only [Set.mem_iInter, Fin.forall_fin_succ, A]
    simp [Matrix.cons_val_zero, Matrix.cons_val_succ]
    omega

/-- Hammack Example 1.13: for `Aᵢ = {-i, 0, i}`, the union over all `i ≥ 1` is all of `ℤ` and the
intersection over all `i ≥ 1` is `{0}`. -/
@[kb "hammack2018" "Example 1.13, p. 38"]
theorem hammack_ex_1_13_union_inter_integers :
    let A : ℕ → Set ℤ := fun i => {-(i : ℤ), 0, (i : ℤ)}
    (⋃ i, ⋃ (_ : 1 ≤ i), A i) = Set.univ ∧ (⋂ i, ⋂ (_ : 1 ≤ i), A i) = {0} := by
  intro A
  constructor
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true, A]
    refine ⟨max x.natAbs 1, by omega, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  · ext x
    simp only [Set.mem_iInter, Set.mem_singleton_iff, A, Set.mem_insert_iff]
    constructor
    · intro h
      have h1 := h (x.natAbs + 1) (by omega)
      omega
    · intro h i hi
      right; left; exact h

end UndergradKB.Foundations.Course
