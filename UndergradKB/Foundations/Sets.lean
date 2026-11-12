import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Set.Lattice.Indexed
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.SetTheory.ZFC.Basic
import UndergradKB.Common

/-! # Sets: complements, indexed families, power sets, von Neumann naturals, Russell's paradox

Hammack, *Book of Proof*, Chapter 1 (and Levin, Section 5.1), the items Mathlib has only in a different shape.

* Hammack works with sets of anything, with a universal set `U`; Lean's sets are typed (`Set α`, the type `α` playing the
  role of the universe), and a complement relative to an arbitrary `U` is the difference `U \ A` (FO-021).
* Indexed unions and intersections over `1 ≤ i ≤ n` and over a nonempty index set `I` (FO-024, FO-025).
* Natural numbers as sets (von Neumann, FO-028), Russell's paradox (FO-029) and the axiom of foundation (FO-030),
  stated inside Mathlib's model `ZFSet` of Zermelo-Fraenkel set theory.
-/

namespace UndergradKB.Foundations

open Set

/-! ## Basic notions (FO-001, FO-007, FO-008, FO-011) -/

/-- FO-001. A set is determined by its membership relation (`Set α` is `α → Prop`); a set is infinite exactly when it
is not finite. -/
@[kb "hammack2018" "Def §1.1, p. 15", kb "levin2025" "Sec 5.1, p. 409"]
theorem set_membership_finite_infinite {α : Type*} (A : Set α) (p : α → Prop) (a : α) :
    (a ∈ {x | p x} ↔ p a) ∧ (A.Infinite ↔ ¬ A.Finite) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- FO-007. Interval notation on `ℝ`: the closed, open and half-open intervals and the five kinds of infinite
intervals, by their membership conditions. -/
@[kb "hammack2018" "Def §1.1, p. 19"]
theorem interval_notation (a b x : ℝ) :
    (x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b) ∧ (x ∈ Ioo a b ↔ a < x ∧ x < b) ∧
    (x ∈ Ico a b ↔ a ≤ x ∧ x < b) ∧ (x ∈ Ioc a b ↔ a < x ∧ x ≤ b) ∧
    (x ∈ Ioi a ↔ a < x) ∧ (x ∈ Ici a ↔ a ≤ x) ∧ (x ∈ Iio b ↔ x < b) ∧ (x ∈ Iic b ↔ x ≤ b) ∧
    x ∈ (univ : Set ℝ) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, trivial⟩

/-- FO-008. Two ordered pairs are equal exactly when their first entries agree and their second entries agree. -/
@[kb "hammack2018" "Def 1.1, p. 20", kb "levin2025" "Sec 0.2.4, p. 28"]
theorem ordered_pair_eq_iff {α β : Type*} (a c : α) (b d : β) : (a, b) = (c, d) ↔ a = c ∧ b = d :=
  Prod.mk.injEq a b c d ▸ Iff.rfl

/-- FO-011. The Cartesian power `A^n` is modelled by `n`-tuples `Fin n → α` with every entry in `A` (the set
`Set.pi univ (fun _ => A)`); for a finite set `S`, `|S^n| = |S|^n`. -/
@[kb "hammack2018" "Def §1.2, p. 22", kb "hammack2018" "Example 1.4, p. 23", kb "levin2025" "Sec 5.1.3, p. 417"]
theorem cartesian_power {α : Type*} (A : Set α) (n : ℕ) (x : Fin n → α) (S : Type*) [Fintype S]
    [DecidableEq (Fin n)] :
    (x ∈ Set.pi univ (fun _ => A) ↔ ∀ i, x i ∈ A) ∧ Fintype.card (Fin n → S) = Fintype.card S ^ n := by
  refine ⟨by simp, ?_⟩
  simp

/-! ## Complement relative to a universal set (FO-021) -/

/-- FO-021. With a universal set `U` containing `A`, the complement `U - A` consists of the elements of `U` not in `A`;
it is `U ∩ Aᶜ`, complementing twice gives `A` back, and when `U` is the whole type it is Mathlib's `Aᶜ`. -/
@[kb "hammack2018" "Def 1.6, p. 32", kb "levin2025" "Sec 5.1.3, p. 416"]
theorem complement_in_universe {α : Type*} (U A : Set α) (hA : A ⊆ U) (x : α) :
    (x ∈ U \ A ↔ x ∈ U ∧ x ∉ A) ∧ U \ A = U ∩ Aᶜ ∧ U \ (U \ A) = A ∧ univ \ A = Aᶜ := by
  refine ⟨Iff.rfl, sdiff_eq U A, sdiff_sdiff_cancel_left hA, ?_⟩
  ext; simp

/-! ## Indexed unions and intersections (FO-024, FO-025) -/

/-- FO-024. For sets `A₁, …, Aₙ`: `x` is in `A₁ ∪ ⋯ ∪ Aₙ` iff `x ∈ Aᵢ` for at least one `1 ≤ i ≤ n`, and in
`A₁ ∩ ⋯ ∩ Aₙ` iff `x ∈ Aᵢ` for every `1 ≤ i ≤ n`. -/
@[kb "hammack2018" "Def 1.7, p. 37"]
theorem mem_finite_indexed_union_inter {α : Type*} (A : ℕ → Set α) (n : ℕ) (x : α) :
    (x ∈ ⋃ i ∈ Finset.Icc 1 n, A i ↔ ∃ i, 1 ≤ i ∧ i ≤ n ∧ x ∈ A i) ∧
      (x ∈ ⋂ i ∈ Finset.Icc 1 n, A i ↔ ∀ i, 1 ≤ i → i ≤ n → x ∈ A i) := by
  simp only [mem_iUnion, mem_iInter, Finset.mem_Icc, exists_prop, and_assoc, and_imp]
  exact ⟨trivial, trivial⟩

/-- FO-025. For a family `A_α` indexed by a nonempty index set `I`: `x ∈ ⋃_{α ∈ I} A_α` iff `x ∈ A_α` for at least one
`α ∈ I`, and `x ∈ ⋂_{α ∈ I} A_α` iff `x ∈ A_α` for every `α ∈ I`; nonemptiness of `I` makes the intersection a
subset of some member of the family. -/
@[kb "hammack2018" "Def 1.8, p. 38"]
theorem mem_indexed_union_inter {ι α : Type*} (I : Set ι) (hI : I.Nonempty) (A : ι → Set α) (x : α) :
    (x ∈ ⋃ i ∈ I, A i ↔ ∃ i ∈ I, x ∈ A i) ∧ (x ∈ ⋂ i ∈ I, A i ↔ ∀ i ∈ I, x ∈ A i) ∧
      ∃ i ∈ I, (⋂ j ∈ I, A j) ⊆ A i := by
  refine ⟨by simp, by simp, ?_⟩
  obtain ⟨i, hi⟩ := hI
  exact ⟨i, hi, biInter_subset_of_mem hi⟩

/-! ## Power sets (FO-151) -/

/-- FO-151 (Hammack Example 8.8). `P(A) ∪ P(B) ⊆ P(A ∪ B)`. -/
@[kb "hammack2018" "Example 8.8, p. 173"]
theorem powerset_union_subset {α : Type*} (A B : Set α) : 𝒫 A ∪ 𝒫 B ⊆ 𝒫 (A ∪ B) := by
  rintro X (hX | hX)
  · exact hX.trans subset_union_left
  · exact hX.trans subset_union_right

/-- FO-151. The inclusion can be strict: for `A = {0}` and `B = {1}`, the set `{0, 1}` is in `P(A ∪ B)` but in
neither `P(A)` nor `P(B)`. -/
@[kb "hammack2018" "Example 8.8, p. 173"]
theorem powerset_union_ne : 𝒫 ({0} : Set ℕ) ∪ 𝒫 {1} ≠ 𝒫 ({0} ∪ {1}) := by
  intro h
  have : ({0, 1} : Set ℕ) ∈ 𝒫 ({0} ∪ {1}) := by
    intro x hx; simp only [mem_insert_iff, mem_singleton_iff] at hx; simp [hx.symm]
  rw [← h] at this
  rcases this with h0 | h1
  · have : (1 : ℕ) ∈ ({0} : Set ℕ) := h0 (by simp)
    simp at this
  · have : (0 : ℕ) ∈ ({1} : Set ℕ) := h1 (by simp)
    simp at this

/-! ## Natural numbers as sets (FO-028) -/

/-- The von Neumann natural number `n` as a set: `0 = ∅` and `n + 1 = n ∪ {n}`. -/
def vonNeumann : ℕ → ZFSet
  | 0 => ∅
  | n + 1 => insert (vonNeumann n) (vonNeumann n)

/-- FO-028. Viewed as a set, each natural number is the set of its predecessors: `n = {0, 1, …, n - 1}`. -/
@[kb "hammack2018" "Sec 1.9, p. 43"]
theorem mem_vonNeumann (n : ℕ) (x : ZFSet) : x ∈ vonNeumann n ↔ ∃ k < n, x = vonNeumann k := by
  induction n with
  | zero => simp [vonNeumann, ZFSet.notMem_empty]
  | succ n ih =>
    rw [vonNeumann, ZFSet.mem_insert_iff, ih]
    constructor
    · rintro (h | ⟨k, hk, rfl⟩)
      · exact ⟨n, Nat.lt_succ_self n, h⟩
      · exact ⟨k, Nat.lt_succ_of_lt hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact Or.inr ⟨k, hk, rfl⟩
      · exact Or.inl rfl

/-! ## Russell's paradox and foundation (FO-029, FO-030) -/

/-- FO-029. Russell's paradox, in its general logical form: for any membership relation on any collection of objects,
there is no object whose members are exactly the objects that are not members of themselves. -/
@[kb "hammack2018" "Sec 1.10, p. 44"]
theorem russell_paradox {α : Type*} (mem : α → α → Prop) : ¬ ∃ R, ∀ x, mem x R ↔ ¬ mem x x := by
  rintro ⟨R, hR⟩
  have h := hR R
  by_cases hRR : mem R R
  · exact h.mp hRR hRR
  · exact hRR (h.mpr hRR)

/-- FO-029. In Zermelo-Fraenkel set theory (Mathlib's `ZFSet`) there is no set of all sets that are not members of
themselves. -/
@[kb "hammack2018" "Sec 1.10, p. 44"]
theorem russell_paradox_zfset : ¬ ∃ R : ZFSet, ∀ x, x ∈ R ↔ x ∉ x :=
  russell_paradox (· ∈ ·)

/-- FO-030. The axiom of foundation (regularity) in `ZFSet`: every nonempty set `X` has a member disjoint from `X`;
in particular no set is a member of itself. -/
@[kb "hammack2018" "Sec 1.10, p. 44"]
theorem foundation (X : ZFSet) (hX : X ≠ ∅) : (∃ y ∈ X, X ∩ y = ∅) ∧ X ∉ X :=
  ⟨ZFSet.regularity X hX, ZFSet.mem_irrefl X⟩

end UndergradKB.Foundations
