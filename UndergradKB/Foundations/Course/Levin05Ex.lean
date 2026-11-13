import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Insert
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import UndergradKB.Common

/-!
# Course layer: Levin, Discrete Mathematics, Chapter 5, worked examples
-/

namespace UndergradKB.Foundations.Course

/-- Levin Example 5.1.5: the power set of `{1,2,3}` has the eight listed subsets. -/
@[kb "levin2025" "Example 5.1.5, p. 414"]
theorem levin_ex_5_1_5_powerset_three :
    ({1, 2, 3} : Finset ℕ).powerset =
      {∅, {1}, {2}, {3}, {1, 2}, {1, 3}, {2, 3}, {1, 2, 3}} := by
  decide +kernel

/-- Levin Example 5.1.6: `{23, ..., 38}` has 16 elements, and the power set of a 3-element set has 8. -/
@[kb "levin2025" "Example 5.1.6, p. 415"]
theorem levin_ex_5_1_6_cardinalities :
    (Finset.Icc 23 38).card = 16 ∧ (({1, 2, 3} : Finset ℕ).powerset).card = 8 := by
  decide +kernel

/-- Levin Example 5.1.7: some set operations on `A = {1..6}`, `B = {2,4,6}`, `C = {1,2,3}`, `D = {7,8,9}`. -/
@[kb "levin2025" "Example 5.1.7, p. 416"]
theorem levin_ex_5_1_7_set_operations :
    ({1, 2, 3, 4, 5, 6} : Finset ℕ) ∪ {2, 4, 6} = {1, 2, 3, 4, 5, 6} ∧
    ({1, 2, 3, 4, 5, 6} : Finset ℕ) ∩ {2, 4, 6} = {2, 4, 6} ∧
    ({2, 4, 6} : Finset ℕ) ∩ {1, 2, 3} = {2} ∧
    ({1, 2, 3, 4, 5, 6} : Finset ℕ) ∩ {7, 8, 9} = ∅ ∧
    ({2, 4, 6} : Finset ℕ) ∪ {1, 2, 3} = {1, 2, 3, 4, 6} ∧
    ({1, 2, 3, 4, 5, 6} : Finset ℕ) \ {2, 4, 6} = {1, 3, 5} := by
  decide +kernel

/-- Levin Example 5.1.9: the Cartesian product `{1,2} × {3,4,5}` is the six listed pairs, and `{3,4,5} × {3,4,5}`
has 9 elements. -/
@[kb "levin2025" "Example 5.1.9, p. 417"]
theorem levin_ex_5_1_9_cartesian_product :
    ({1, 2} : Finset ℕ) ×ˢ ({3, 4, 5} : Finset ℕ) = {(1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5)} ∧
    (({3, 4, 5} : Finset ℕ) ×ˢ ({3, 4, 5} : Finset ℕ)).card = 9 := by
  decide +kernel

/-- Levin Example 5.2.6: `n ↦ 3n` on `ℤ` is not surjective; its range is the multiples of 3. -/
@[kb "levin2025" "Example 5.2.6, p. 429"]
theorem levin_ex_5_2_6_triple_not_surjective :
    ¬ Function.Surjective (fun n : ℤ => 3 * n) ∧ Set.range (fun n : ℤ => 3 * n) = {x : ℤ | 3 ∣ x} := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h 1
    simp only at hn
    omega
  · ext x
    simp only [Set.mem_range, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k, rfl⟩

/-- Levin Example 5.2.7: `n ↦ 3n` on `ℤ` is injective. -/
@[kb "levin2025" "Example 5.2.7, p. 430"]
theorem levin_ex_5_2_7_triple_injective : Function.Injective (fun n : ℤ => 3 * n) := by
  intro a b h
  simp only at h
  omega

/-- Levin Example 5.2.8: for `f` sending `1..6` to `a, a, b, b, b, c` (encoded `0..5 ↦ 0,0,1,1,1,2` into
`{a,b,c,d} = {0,1,2,3}`), the image of the first three is `{a, b}`, the preimage of `{a, b}` is the first five,
and the preimage of `d` is empty. -/
@[kb "levin2025" "Example 5.2.8, p. 432"]
theorem levin_ex_5_2_8_image_preimage :
    let f : Fin 6 → Fin 4 := ![0, 0, 1, 1, 1, 2]
    f '' {0, 1, 2} = {0, 1} ∧ f ⁻¹' {0, 1} = {0, 1, 2, 3, 4} ∧ f ⁻¹' {3} = ∅ := by
  intro f
  refine ⟨?_, ?_, ?_⟩
  · ext y
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases hx with rfl | rfl | rfl <;> simp [f]
    · rintro (rfl | rfl)
      · exact ⟨0, by simp, by simp [f]⟩
      · exact ⟨2, by simp, by simp [f]⟩
  · ext x
    fin_cases x <;> simp [f]
  · ext x
    fin_cases x <;> simp [f]

/-- Levin Example 5.2.9: for `g n = n^2 + 1` on `ℤ`: `g 1 = 2`, `g '' {1} = {2}`, `g⁻¹ {1} = {0}`,
`g⁻¹ {2} = {-1, 1}` and `g⁻¹ {3} = ∅`. -/
@[kb "levin2025" "Example 5.2.9, p. 432"]
theorem levin_ex_5_2_9_square_plus_one :
    let g : ℤ → ℤ := fun n => n ^ 2 + 1
    g 1 = 2 ∧ g '' {1} = {2} ∧ g ⁻¹' {1} = {0} ∧ g ⁻¹' {2} = {-1, 1} ∧ g ⁻¹' {3} = ∅ := by
  intro g
  refine ⟨by norm_num [g], by simp [g], ?_, ?_, ?_⟩
  · ext n
    simp only [g, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h; nlinarith [sq_nonneg n]
    · rintro rfl; norm_num
  · ext n
    simp only [g, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_insert_iff]
    constructor
    · intro h
      have h1 : n ≤ 1 := by nlinarith
      have h2 : -1 ≤ n := by nlinarith
      interval_cases n <;> simp_all
    · rintro (rfl | rfl) <;> norm_num
  · ext n
    simp only [g, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    intro h
    have h1 : n ≤ 1 := by nlinarith
    have h2 : -1 ≤ n := by nlinarith
    interval_cases n <;> simp_all

end UndergradKB.Foundations.Course
