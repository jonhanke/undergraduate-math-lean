import Mathlib.Data.Int.ModEq
import Mathlib.Order.Setoid.Partition
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Tactic.ComputeDegree
import UndergradKB.Common

/-!
# Course layer: Hammack, Book of Proof, Chapter 11, further worked examples

Congruence modulo 3 as an equivalence relation on `ℤ` and its three classes.
-/

namespace UndergradKB.Foundations.Course

/-- Congruence modulo 3 as a `Setoid` on the integers. -/
def hammackModThree : Setoid ℤ where
  r a b := a ≡ b [ZMOD 3]
  iseqv := ⟨fun _ => Int.ModEq.refl _, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- Two integers are related by `hammackModThree` exactly when they leave the same remainder on division by 3. -/
@[simp] theorem hammackModThree_iff (a b : ℤ) : hammackModThree a b ↔ a % 3 = b % 3 := Iff.rfl

/-- Hammack Example 11.13: the equivalence class of `0` modulo 3 is the set of multiples of 3; the class
of `1` is the integers leaving remainder `1`, and the class of `2` those leaving remainder `2`. -/
@[kb "hammack2018" "Example 11.13, p. 224"]
theorem hammack_ex_11_13_classes_mod_three :
    {x : ℤ | hammackModThree x 0} = {x | 3 ∣ x} ∧
      {x : ℤ | hammackModThree x 1} = {x | x % 3 = 1} ∧
      {x : ℤ | hammackModThree x 2} = {x | x % 3 = 2} := by
  refine ⟨?_, ?_, ?_⟩ <;> ext x <;> simp <;> omega

/-- Hammack Example 11.13 (repeated names): `[0] = [3] = [6]` and `[1] = [4]`, while `[0]`, `[1]`, `[2]`
are pairwise different. -/
@[kb "hammack2018" "Example 11.13, p. 224"]
theorem hammack_ex_11_13_class_names :
    {x : ℤ | hammackModThree x 0} = {x | hammackModThree x 3} ∧
      {x : ℤ | hammackModThree x 0} = {x | hammackModThree x 6} ∧
      {x : ℤ | hammackModThree x 1} = {x | hammackModThree x 4} ∧
      {x : ℤ | hammackModThree x 0} ≠ {x | hammackModThree x 1} ∧
      {x : ℤ | hammackModThree x 1} ≠ {x | hammackModThree x 2} ∧
      {x : ℤ | hammackModThree x 0} ≠ {x | hammackModThree x 2} := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext x; simp
  · ext x; simp
  · ext x; simp
  · intro h
    have := Set.ext_iff.mp h 0
    simp at this
  · intro h
    have := Set.ext_iff.mp h 1
    simp at this
  · intro h
    have := Set.ext_iff.mp h 0
    simp at this

/-- Hammack Example 11.16: the equivalence classes of congruence mod 3 are exactly the three sets
`[0]`, `[1]`, `[2]`, and they form a partition of `ℤ`. -/
@[kb "hammack2018" "Example 11.16, p. 228"]
theorem hammack_ex_11_16_mod_three_partition :
    hammackModThree.classes =
      {{x : ℤ | x % 3 = 0}, {x | x % 3 = 1}, {x | x % 3 = 2}} ∧
    Setoid.IsPartition hammackModThree.classes := by
  refine ⟨?_, Setoid.isPartition_classes _⟩
  ext s
  constructor
  · rintro ⟨y, rfl⟩
    have : y % 3 = 0 ∨ y % 3 = 1 ∨ y % 3 = 2 := by omega
    rcases this with h | h | h
    · left; ext x; simp [h]
    · right; left; ext x; simp [h]
    · right; right; ext x; simp [h]
  · intro hs
    rcases hs with rfl | rfl | rfl
    · exact ⟨0, by ext x; simp⟩
    · exact ⟨1, by ext x; simp⟩
    · exact ⟨2, by ext x; simp⟩

/-- Hammack Example 11.1: the ten pairs listed form a relation on `{1, 2, 3, 4}`, and it is the relation `≥`; for
instance `(3, 4)` is not in it. -/
@[kb "hammack2018" "Example 11.1, p. 214"]
theorem hammack_ex_11_1_geq_relation :
    let A : Finset ℕ := {1, 2, 3, 4};
    let R : Finset (ℕ × ℕ) := {(1, 1), (2, 1), (2, 2), (3, 3), (3, 2), (3, 1), (4, 4), (4, 3), (4, 2), (4, 1)};
    R ⊆ A ×ˢ A ∧ R = (A ×ˢ A).filter (fun p => p.2 ≤ p.1) ∧ (3, 4) ∉ R := by
  intro A R
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- Hammack Example 11.2: the eight listed pairs on `{1, 2, 3, 4}` are the relation "has the same parity as"; for
instance `(3, 4)` and `(2, 1)` are not in it. -/
@[kb "hammack2018" "Example 11.2, p. 214"]
theorem hammack_ex_11_2_same_parity :
    let A : Finset ℕ := {1, 2, 3, 4};
    let S : Finset (ℕ × ℕ) := {(1, 1), (1, 3), (3, 1), (3, 3), (2, 2), (2, 4), (4, 2), (4, 4)};
    S = (A ×ˢ A).filter (fun p => p.1 % 2 = p.2 % 2) ∧ (3, 4) ∉ S ∧ (2, 1) ∉ S := by
  intro A S
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- Hammack Example 11.3: the intersection of the relations `≥` and "same parity" on `{1, 2, 3, 4}` consists of the six
pairs `(1,1), (2,2), (3,3), (3,1), (4,4), (4,2)`, i.e. the pairs `(x, y)` with `x ≥ y` and `x`, `y` of equal parity. -/
@[kb "hammack2018" "Example 11.3, p. 214"]
theorem hammack_ex_11_3_intersection :
    let A : Finset ℕ := {1, 2, 3, 4};
    let R : Finset (ℕ × ℕ) := (A ×ˢ A).filter (fun p => p.2 ≤ p.1);
    let S : Finset (ℕ × ℕ) := (A ×ˢ A).filter (fun p => p.1 % 2 = p.2 % 2);
    R ∩ S = {(1, 1), (2, 2), (3, 3), (3, 1), (4, 4), (4, 2)} := by
  intro A R S
  decide

/-- Hammack Example 11.4: a relation need not mean anything; the five pairs `(1,3), (3,3), (5,2), (2,5), (4,2)` form a
relation on `{0, ..., 5}`, being a subset of the square of that set. The alphabetical-order relation on four letters
(encoded `0, 1, 2, 3`) is the six pairs `(a,b), (a,c), (a,d), (b,c), (b,d), (c,d)`. -/
@[kb "hammack2018" "Example 11.4, p. 215"]
theorem hammack_ex_11_4_arbitrary_relation :
    let B : Finset ℕ := Finset.range 6;
    let U : Finset (ℕ × ℕ) := {(1, 3), (3, 3), (5, 2), (2, 5), (4, 2)};
    U ⊆ B ×ˢ B ∧
      (Finset.univ.filter (fun p : Fin 4 × Fin 4 => p.1 < p.2)) =
        {(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)} := by
  intro B U
  exact ⟨by decide, by decide⟩

/-- Hammack Example 11.5: the set of integer pairs `(x, y)` with `x - y` a positive integer is the relation `>` on `ℤ`. -/
@[kb "hammack2018" "Example 11.5, p. 215"]
theorem hammack_ex_11_5_greater_than_on_int :
    {p : ℤ × ℤ | ∃ n : ℕ, 0 < n ∧ p.1 - p.2 = n} = {p | p.2 < p.1} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨n, hn, h⟩
    omega
  · intro h
    exact ⟨(x - y).toNat, by omega, by omega⟩

/-- Hammack Example 11.6: the set of pairs `(x, x)` with `x` real is the relation `=` on `ℝ`. -/
@[kb "hammack2018" "Example 11.6, p. 215"]
theorem hammack_ex_11_6_equality_relation :
    {p : ℝ × ℝ | ∃ x : ℝ, p = (x, x)} = {p | p.1 = p.2} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨z, rfl, rfl⟩
    rfl
  · intro h
    exact ⟨x, rfl, h.symm⟩

/-- Hammack Example 11.9: on `{-1, 1, 2, 3, 4}` the equality relation has every element related only to itself, so the
class of `2` is `{2}` (and likewise for the other four) and there are five distinct classes. -/
@[kb "hammack2018" "Example 11.9, p. 223"]
theorem hammack_ex_11_9_equality_classes :
    let A : Finset ℤ := {-1, 1, 2, 3, 4};
    A.filter (fun x => x = 2) = {2} ∧ A.filter (fun x => x = -1) = {-1} ∧ A.filter (fun x => x = 1) = {1} ∧
      A.filter (fun x => x = 3) = {3} ∧ A.filter (fun x => x = 4) = {4} ∧
      (A.image (fun a => A.filter (fun x => x = a))).card = 5 := by
  intro A
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Hammack Example 11.10: on `{-1, 1, 2, 3, 4}` with "same parity", the class of `2` (and of `4`) is `{2, 4}`, the
class of `1` (and of `-1`, `3`) is `{-1, 1, 3}`, and there are exactly two classes. -/
@[kb "hammack2018" "Example 11.10, p. 223"]
theorem hammack_ex_11_10_parity_classes :
    let A : Finset ℤ := {-1, 1, 2, 3, 4};
    A.filter (fun x => x % 2 = 2 % 2) = {2, 4} ∧ A.filter (fun x => x % 2 = 4 % 2) = {2, 4} ∧
      A.filter (fun x => x % 2 = 1 % 2) = {-1, 1, 3} ∧ A.filter (fun x => x % 2 = (-1) % 2) = {-1, 1, 3} ∧
      A.filter (fun x => x % 2 = 3 % 2) = {-1, 1, 3} ∧
      (A.image (fun a => A.filter (fun x => x % 2 = a % 2))).card = 2 := by
  intro A
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

open Polynomial in
/-- Hammack Example 11.12: "having the same degree" is an equivalence relation on real polynomials; `x² + 3x - 4` is
related to `3x² - 2` but `x³ + 3x² - 4` is not, and the class of `3x² + 2` is the set of degree-2 polynomials. -/
@[kb "hammack2018" "Example 11.12, p. 224"]
theorem hammack_ex_11_12_same_degree :
    let R : ℝ[X] → ℝ[X] → Prop := fun f g => f.natDegree = g.natDegree;
    Equivalence R ∧ R (X ^ 2 + 3 * X - 4) (3 * X ^ 2 - 2) ∧ ¬ R (X ^ 3 + 3 * X ^ 2 - 4) (3 * X ^ 2 - 2) ∧
      {g | R (3 * X ^ 2 + 2) g} = {g | g.natDegree = 2} := by
  intro R
  have h1 : (X ^ 2 + 3 * X - 4 : ℝ[X]).natDegree = 2 := by compute_degree!
  have h2 : (3 * X ^ 2 - 2 : ℝ[X]).natDegree = 2 := by compute_degree!
  have h3 : (X ^ 3 + 3 * X ^ 2 - 4 : ℝ[X]).natDegree = 3 := by compute_degree!
  have h4 : (3 * X ^ 2 + 2 : ℝ[X]).natDegree = 2 := by compute_degree!
  refine ⟨⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩, ?_, ?_, ?_⟩
  · show _ = _
    rw [h1, h2]
  · show ¬ _ = _
    rw [h3, h2]
    omega
  · ext g
    simp only [Set.mem_ofPred_eq, R, h4]
    exact eq_comm

/-- Hammack Example 11.14: for the four-element set `{a, b, c, d}` (encoded `0, 1, 2, 3`), each of the five listed
families, such as `{{a, b}, {c}, {d}}` and `{{a, b, c, d}}`, consists of non-empty subsets, has union the whole set, and
has pairwise disjoint members. -/
@[kb "hammack2018" "Example 11.14, p. 228"]
theorem hammack_ex_11_14_partitions_of_four :
    ∀ P ∈ ([{{0, 1}, {2}, {3}}, {{0, 1}, {2, 3}}, {{0, 2}, {1}, {3}}, {{0}, {1}, {2}, {3}}, {{0, 1, 2, 3}}] :
        List (Finset (Finset ℕ))),
      ∅ ∉ P ∧ (∀ a ∈ Finset.range 4, ∃ x ∈ P, a ∈ x) ∧ (∀ x ∈ P, x ⊆ Finset.range 4) ∧
        ∀ x ∈ P, ∀ y ∈ P, x ≠ y → x ∩ y = ∅ := by
  decide

end UndergradKB.Foundations.Course
