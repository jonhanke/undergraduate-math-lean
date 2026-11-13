import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Order.Interval.Finset.Nat
import UndergradKB.Common

/-!
# Course layer: Levin, Discrete Mathematics, Chapter 2, worked examples (second batch)
-/

namespace UndergradKB.Foundations.Course

/-- Levin Example 2.3.6: three triangles and six pentagons would give 39/2 edges, which is
impossible; adding five heptagons gives 37 edges but then Euler's formula and degree at least 3
force a contradiction. -/
@[kb "levin2025" "Example 2.3.6, p. 155"]
theorem levin_ex_2_3_6_no_polyhedra :
    (¬ ∃ e : ℕ, 2 * e = 3 * 3 + 6 * 5) ∧ 3 * 3 + 6 * 5 + 5 * 7 = 2 * 37 ∧
      ¬ ∃ v e : ℕ, 2 * e = 3 * 3 + 6 * 5 + 5 * 7 ∧ (v : ℤ) - e + 14 = 2 ∧ 3 * v ≤ 2 * e := by
  refine ⟨?_, by norm_num, ?_⟩
  · rintro ⟨e, he⟩
    omega
  · rintro ⟨v, e, h1, h2, h3⟩
    omega

/-- Levin Example 2.5.8: the complete graph on six vertices has an edge colouring with five
colours (a symmetric colouring of the pairs, differing on any two edges at a common vertex), but
none with four colours, since the five edges at one vertex need distinct colours. -/
@[kb "levin2025" "Example 2.5.8, p. 177"]
theorem levin_ex_2_5_8_k6_chromatic_index :
    (∃ c : Fin 6 → Fin 6 → ℕ, (∀ a b, a ≠ b → c a b < 5) ∧ (∀ a b, c a b = c b a) ∧
      ∀ a b d, a ≠ b → a ≠ d → b ≠ d → c a b ≠ c a d) ∧
    ¬ ∃ c : Fin 6 → Fin 6 → ℕ, (∀ a b, a ≠ b → c a b < 4) ∧
      ∀ a b d, a ≠ b → a ≠ d → b ≠ d → c a b ≠ c a d := by
  constructor
  · refine ⟨fun a b => if a.val = 5 then (2 * b.val) % 5
      else if b.val = 5 then (2 * a.val) % 5 else (a.val + b.val) % 5, ?_, ?_, ?_⟩ <;> decide
  · rintro ⟨c, hb, hp⟩
    let g : {j : Fin 6 // j ≠ 0} → Fin 4 := fun j => ⟨c 0 j.1, hb 0 j.1 (Ne.symm j.2)⟩
    have hg : Function.Injective g := by
      intro j k hjk
      by_contra hne
      have hne' : j.1 ≠ k.1 := fun h => hne (Subtype.ext h)
      exact hp 0 j.1 k.1 (Ne.symm j.2) (Ne.symm k.2) hne' (by simpa [g] using hjk)
    have := Fintype.card_le_of_injective g hg
    simp at this

-- students Al, Bob, Cat, Dirk, Eva are 0..4; courses Calculus, Discrete, Statistics are 0..2;
-- professors X, L, S are 0..2

/-- Levin Example 2.6.8: composing "is taking" with "is taught by" gives the ten listed pairs. -/
@[kb "levin2025" "Example 2.6.8, p. 189"]
theorem levin_ex_2_6_8_composition :
    let T : Finset (Fin 5 × Fin 3) :=
      {(0, 0), (1, 0), (2, 0), (4, 0), (1, 1), (4, 1), (0, 2), (2, 2), (3, 2)}
    let P : Finset (Fin 3 × Fin 3) := {(0, 0), (1, 1), (2, 0), (2, 2)}
    ((T ×ˢ P).filter (fun x => x.1.2 = x.2.1)).image (fun x => (x.1.1, x.2.2)) =
      ({(0, 0), (0, 2), (1, 0), (1, 1), (2, 0), (2, 2), (3, 0), (3, 2), (4, 0), (4, 1)} :
        Finset (Fin 5 × Fin 3)) := by
  decide +kernel

/-- Levin Example 2.6.9: two students are related by `T⁻¹ ∘ T` exactly when they share a class;
the only unrelated pairs are Dirk with Bob and Dirk with Eva. -/
@[kb "levin2025" "Example 2.6.9, p. 189"]
theorem levin_ex_2_6_9_common_class :
    let T : Finset (Fin 5 × Fin 3) :=
      {(0, 0), (1, 0), (2, 0), (4, 0), (1, 1), (4, 1), (0, 2), (2, 2), (3, 2)}
    ∀ a b : Fin 5, (∃ c : Fin 3, (a, c) ∈ T ∧ (b, c) ∈ T) ↔
      ¬ ((a = 3 ∧ (b = 1 ∨ b = 4)) ∨ (b = 3 ∧ (a = 1 ∨ a = 4))) := by
  decide +kernel

/-- Levin Example 2.6.11: reflexive and non-reflexive relations on the integers. -/
@[kb "levin2025" "Example 2.6.11, p. 191"]
theorem levin_ex_2_6_11_reflexive :
    (∀ a : ℤ, a ≤ a) ∧ (∀ a : ℤ, |a - a| ≤ 3) ∧ (∀ a : ℤ, a ∣ a) ∧
      ¬ (∀ a : ℤ, a + a = 0) := by
  refine ⟨fun a => le_refl a, fun a => by simp, fun a => dvd_refl a, fun h => ?_⟩
  have := h (1 : ℤ)
  omega

/-- Levin Example 2.6.12: symmetric and non-symmetric relations on the integers. -/
@[kb "levin2025" "Example 2.6.12, p. 191"]
theorem levin_ex_2_6_12_symmetric :
    (∀ a b : ℤ, |a - b| ≤ 3 → |b - a| ≤ 3) ∧ (∀ a b : ℤ, a + b = 0 → b + a = 0) ∧
      ¬ (∀ a b : ℤ, a ≤ b → b ≤ a) ∧ ¬ (∀ a b : ℤ, a ∣ b → b ∣ a) := by
  refine ⟨fun a b h => by rwa [abs_sub_comm], fun a b h => by omega, fun h => ?_, fun h => ?_⟩
  · have := h 3 4 (by decide)
    revert this
    decide
  · have := h 2 6 (by decide)
    revert this
    decide

/-- Levin Example 2.6.13: transitive and non-transitive relations on the integers. -/
@[kb "levin2025" "Example 2.6.13, p. 192"]
theorem levin_ex_2_6_13_transitive :
    (∀ a b c : ℤ, a ≤ b → b ≤ c → a ≤ c) ∧ (∀ a b c : ℤ, a ∣ b → b ∣ c → a ∣ c) ∧
      ¬ (∀ a b c : ℤ, |a - b| ≤ 3 → |b - c| ≤ 3 → |a - c| ≤ 3) ∧
      ¬ (∀ a b c : ℤ, a + b = 0 → b + c = 0 → a + c = 0) := by
  refine ⟨fun a b c => le_trans, fun a b c h1 h2 => dvd_trans h1 h2, fun h => ?_, fun h => ?_⟩
  · have := h 1 3 5 (by decide) (by decide)
    revert this
    decide
  · have := h 5 (-5) 5 (by decide) (by decide)
    omega

/-- Levin Example 2.6.17: having the same degree sequence (the multiset of vertex degrees) is an
equivalence relation on graphs with the same vertex set. -/
@[kb "levin2025" "Example 2.6.17, p. 194"]
theorem levin_ex_2_6_17_same_degree_sequence (n : ℕ) :
    Equivalence (fun G H : SimpleGraph (Fin n) =>
      Multiset.map (fun v => (G.neighborSet v).ncard) Finset.univ.val =
        Multiset.map (fun v => (H.neighborSet v).ncard) Finset.univ.val) :=
  ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

/-- Levin Example 2.6.19: the sets of divisors within `{1,...,6}` of each of `1,...,6`
(the relation classes of "is a multiple of"). -/
@[kb "levin2025" "Example 2.6.19, p. 194"]
theorem levin_ex_2_6_19_multiple_classes :
    let cls : ℕ → Finset ℕ := fun a => (Finset.Icc 1 6).filter (fun b => b ∣ a)
    cls 1 = {1} ∧ cls 2 = {1, 2} ∧ cls 3 = {1, 3} ∧ cls 4 = {1, 2, 4} ∧ cls 5 = {1, 5} ∧
      cls 6 = {1, 2, 3, 6} := by
  decide +kernel

/-- Levin Example 2.6.20: congruence mod 2 has exactly two classes on `ℤ`, the odd integers and
the even integers. -/
@[kb "levin2025" "Example 2.6.20, p. 195"]
theorem levin_ex_2_6_20_mod_two_classes :
    {b : ℤ | 1 ≡ b [ZMOD 2]} = {b | Odd b} ∧ {b : ℤ | 2 ≡ b [ZMOD 2]} = {b | Even b} ∧
      ∀ a : ℤ, {b : ℤ | a ≡ b [ZMOD 2]} = {b | 1 ≡ b [ZMOD 2]} ∨
        {b : ℤ | a ≡ b [ZMOD 2]} = {b | 2 ≡ b [ZMOD 2]} := by
  refine ⟨?_, ?_, fun a => ?_⟩
  · ext b
    simp only [Set.mem_ofPred_eq, Int.odd_iff, Int.ModEq]
    omega
  · ext b
    simp only [Set.mem_ofPred_eq, Int.even_iff, Int.ModEq]
    omega
  · by_cases h : a % 2 = 1
    · left
      ext b
      simp only [Set.mem_ofPred_eq, Int.ModEq]
      omega
    · right
      ext b
      simp only [Set.mem_ofPred_eq, Int.ModEq]
      omega

/-- Levin Example 2.6.22: four partitions of `{1,...,5}` (each part is non-empty, inside the set,
and every element lies in exactly one part). -/
@[kb "levin2025" "Example 2.6.22, p. 196"]
theorem levin_ex_2_6_22_partitions :
    let A : Finset ℕ := {1, 2, 3, 4, 5}
    ∀ P ∈ ([{{1, 2, 3}, {4, 5}}, {{1}, {2}, {3}, {4}, {5}}, {{1, 3, 5}, {2, 4}}, {A}] :
        List (Finset (Finset ℕ))),
      (∀ s ∈ P, s.Nonempty ∧ s ⊆ A) ∧ ∀ a ∈ A, (P.filter (fun s => a ∈ s)).card = 1 := by
  decide +kernel

end UndergradKB.Foundations.Course
