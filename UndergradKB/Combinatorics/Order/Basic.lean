import Mathlib.Order.Antichain
import Mathlib.Order.Preorder.Chain
import Mathlib.Order.Minimal
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import UndergradKB.Common.Attr

/-!
# Finite posets: comparability, width, height, Mirsky's theorem

Source: Keller--Trotter, *Applied Combinatorics* (2017), Chapter 6.
Chains and antichains are Mathlib's `IsChain (· ≤ ·)` and `IsAntichain (· ≤ ·)`.
-/

namespace UndergradKB.Combinatorics.Order

open Finset

variable {α : Type*} [PartialOrder α]

/-- CO-139. Two points are comparable when they are distinct and one is below the other. -/
@[kb "kellertrotter2017" "Definition (unnumbered) comparable, p. 142"]
def Comparable (x y : α) : Prop := x ≠ y ∧ (x ≤ y ∨ y ≤ x)

/-- CO-139. Two points are incomparable (`x ∥ y`) when neither is below the other. -/
@[kb "kellertrotter2017" "Definition (unnumbered) incomparable, p. 142"]
def Incomparable (x y : α) : Prop := ¬ x ≤ y ∧ ¬ y ≤ x

theorem incomparable_iff_not_comparable {x y : α} :
    Incomparable x y ↔ x ≠ y ∧ ¬ Comparable x y := by
  unfold Incomparable Comparable
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun h => h1 (h ▸ le_rfl), fun h => by tauto⟩
  · rintro ⟨h1, h2⟩
    constructor <;> intro h <;> exact h2 ⟨by rintro rfl; exact h1 rfl, by tauto⟩

/-- A set is a chain iff its distinct points are pairwise comparable. -/
theorem isChain_iff_comparable {s : Set α} :
    IsChain (· ≤ ·) s ↔ s.Pairwise Comparable := by
  constructor
  · intro h x hx y hy hxy
    exact ⟨hxy, h hx hy hxy⟩
  · intro h x hx y hy hxy
    exact (h hx hy hxy).2

/-- A set is an antichain iff its distinct points are pairwise incomparable. -/
theorem isAntichain_iff_incomparable {s : Set α} :
    IsAntichain (· ≤ ·) s ↔ s.Pairwise Incomparable := by
  constructor
  · intro h x hx y hy hxy
    exact ⟨h hx hy hxy, h hy hx hxy.symm⟩
  · intro h x hx y hy hxy
    exact (h hx hy hxy).1

variable (α) in
/-- CO-140. The comparability graph of a poset. -/
@[kb "kellertrotter2017" "Definition (unnumbered) comparability graph, p. 142"]
def comparabilityGraph : SimpleGraph α := SimpleGraph.fromRel (fun x y : α => x ≤ y)

variable (α) in
/-- CO-140. The incomparability graph of a poset. -/
@[kb "kellertrotter2017" "Definition (unnumbered) incomparability graph, p. 142"]
def incomparabilityGraph : SimpleGraph α := (comparabilityGraph α)ᶜ

theorem comparabilityGraph_adj {x y : α} : (comparabilityGraph α).Adj x y ↔ Comparable x y :=
  Iff.rfl

theorem incomparabilityGraph_adj {x y : α} :
    (incomparabilityGraph α).Adj x y ↔ x ≠ y ∧ Incomparable x y := by
  rw [incomparabilityGraph, SimpleGraph.compl_adj, comparabilityGraph_adj]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (incomparable_iff_not_comparable.2 ⟨h1, h2⟩)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (incomparable_iff_not_comparable.1 h2).2⟩

variable (α) in
/-- CO-153. A poset is connected if its comparability graph is connected. -/
@[kb "kellertrotter2017" "Definition (unnumbered) connected poset, p. 144"]
def IsConnectedPoset : Prop := (comparabilityGraph α).Connected

/-! ### Down sets and up sets (CO-161, CO-162) -/

/-- CO-161. `D(S)`: points strictly below some point of `S`. -/
def downSet (S : Set α) : Set α := {y | ∃ x ∈ S, y < x}

/-- CO-161. `U(S)`: points strictly above some point of `S`. -/
def upSet (S : Set α) : Set α := {y | ∃ x ∈ S, x < y}

/-- CO-162. For a maximal antichain `A`, the ground set is the disjoint union of
`A`, `D(A)` and `U(A)`. -/
@[kb "kellertrotter2017" "text (unnumbered) A, D(A), U(A) partition, p. 147"]
theorem maximal_antichain_partition {A : Set α} (hA : Maximal (IsAntichain (· ≤ ·)) A) :
    A ∪ downSet A ∪ upSet A = Set.univ ∧ Disjoint A (downSet A) ∧ Disjoint A (upSet A) ∧
      Disjoint (downSet A) (upSet A) := by
  obtain ⟨hAc, hmax⟩ := hA
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine Set.eq_univ_of_forall fun z => ?_
    by_contra hz
    simp only [Set.mem_union, not_or, downSet, upSet, Set.mem_ofPred_eq, not_exists, not_and] at hz
    obtain ⟨⟨hzA, hd⟩, hu⟩ := hz
    have : IsAntichain (· ≤ ·) (insert z A) := by
      refine isAntichain_insert.2 ⟨hAc, fun b hb hne => ⟨fun h => ?_, fun h => ?_⟩⟩
      · exact hd b hb (lt_of_le_of_ne h hne)
      · exact hu b hb (lt_of_le_of_ne h (Ne.symm hne))
    exact hzA (hmax this (Set.subset_insert _ _) (Set.mem_insert _ _))
  · rw [Set.disjoint_left]
    rintro a ha ⟨b, hb, hab⟩
    exact hAc ha hb hab.ne hab.le
  · rw [Set.disjoint_left]
    rintro a ha ⟨b, hb, hab⟩
    exact hAc hb ha hab.ne hab.le
  · rw [Set.disjoint_left]
    rintro a ⟨b, hb, hab⟩ ⟨c, hc, hca⟩
    exact hAc hc hb (hca.trans hab).ne (hca.trans hab).le

/-! ### Width and height -/

variable (α) [Fintype α]

open Classical in
/-- The antichains of a finite poset, as a finset of finsets. -/
noncomputable def antichains : Finset (Finset α) :=
  univ.filter fun s : Finset α => IsAntichain (· ≤ ·) (s : Set α)

open Classical in
/-- The chains of a finite poset, as a finset of finsets. -/
noncomputable def chains : Finset (Finset α) :=
  univ.filter fun s : Finset α => IsChain (· ≤ ·) (s : Set α)

open Classical in
/-- The chains of a finite poset all of whose points are `≤ x`. -/
noncomputable def chainsBelow {β : Type*} [PartialOrder β] [Fintype β] (x : β) :
    Finset (Finset β) :=
  univ.filter fun s : Finset β => IsChain (· ≤ ·) (s : Set β) ∧ ∀ y ∈ s, y ≤ x

variable {α}

@[simp] theorem mem_antichains {s : Finset α} :
    s ∈ antichains α ↔ IsAntichain (· ≤ ·) (s : Set α) := by simp [antichains]

@[simp] theorem mem_chains {s : Finset α} :
    s ∈ chains α ↔ IsChain (· ≤ ·) (s : Set α) := by simp [chains]

@[simp] theorem mem_chainsBelow {x : α} {s : Finset α} :
    s ∈ chainsBelow x ↔ IsChain (· ≤ ·) (s : Set α) ∧ ∀ y ∈ s, y ≤ x := by simp [chainsBelow]

variable (α)

/-- CO-145. The width of a finite poset: the largest size of an antichain. -/
@[kb "kellertrotter2017" "Definition (unnumbered) width, p. 143"]
noncomputable def width : ℕ := (antichains α).sup Finset.card

/-- CO-144. The height of a finite poset: the largest size of a chain. -/
@[kb "kellertrotter2017" "Definition (unnumbered) height, p. 143"]
noncomputable def height : ℕ := (chains α).sup Finset.card

variable {α}

theorem card_le_width {s : Finset α} (h : IsAntichain (· ≤ ·) (s : Set α)) :
    s.card ≤ width α :=
  Finset.le_sup (f := Finset.card) (mem_antichains.2 h)

theorem exists_antichain_card_eq_width :
    ∃ s : Finset α, IsAntichain (· ≤ ·) (s : Set α) ∧ s.card = width α := by
  obtain ⟨s, hs, h⟩ := Finset.exists_mem_eq_sup (antichains α) ⟨∅, by simp⟩ Finset.card
  exact ⟨s, mem_antichains.1 hs, h.symm⟩

theorem card_le_height {s : Finset α} (h : IsChain (· ≤ ·) (s : Set α)) :
    s.card ≤ height α :=
  Finset.le_sup (f := Finset.card) (mem_chains.2 h)

theorem exists_chain_card_eq_height :
    ∃ s : Finset α, IsChain (· ≤ ·) (s : Set α) ∧ s.card = height α := by
  obtain ⟨s, hs, h⟩ := Finset.exists_mem_eq_sup (chains α) ⟨∅, by simp⟩ Finset.card
  exact ⟨s, mem_chains.1 hs, h.symm⟩

/-! ### Mirsky's theorem (dual of Dilworth) -/

/-- The largest size of a chain all of whose points are `≤ x` (the book's `height(x)`). -/
noncomputable def pointHeight (x : α) : ℕ := (chainsBelow x).sup Finset.card

theorem pointHeight_pos (x : α) : 0 < pointHeight x := by
  have : ({x} : Finset α).card ≤ pointHeight x :=
    Finset.le_sup (f := Finset.card) (mem_chainsBelow.2 ⟨by simp, by simp⟩)
  simp only [Finset.card_singleton] at this
  omega

theorem pointHeight_le_height (x : α) : pointHeight x ≤ height α :=
  Finset.sup_le fun _ hs => card_le_height (mem_chainsBelow.1 hs).1

theorem pointHeight_lt_of_lt {x y : α} (h : x < y) : pointHeight x < pointHeight y := by
  classical
  obtain ⟨s, hs, hcard⟩ := Finset.exists_mem_eq_sup (chainsBelow x) ⟨∅, by simp⟩ Finset.card
  obtain ⟨hch, hle⟩ := mem_chainsBelow.1 hs
  have hy : y ∉ s := fun hy => absurd (hle y hy) (not_le_of_gt h)
  have hmem : insert y s ∈ chainsBelow y := by
    refine mem_chainsBelow.2 ⟨?_, ?_⟩
    · rw [Finset.coe_insert]
      exact hch.insert fun b hb _ => Or.inr ((hle b hb).trans h.le)
    · intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact le_rfl
      · exact (hle z hz).trans h.le
  have h3 : (insert y s).card ≤ pointHeight y := Finset.le_sup (f := Finset.card) hmem
  rw [Finset.card_insert_of_notMem hy] at h3
  have h2 : pointHeight x = s.card := hcard
  omega

omit [Fintype α] in
/-- A map from a chain to pieces of an antichain partition is injective. -/
theorem injOn_of_antichain_fibers {ι : Type*} {g : α → ι}
    (hg : ∀ i, IsAntichain (· ≤ ·) (g ⁻¹' {i})) {s : Set α} (hs : IsChain (· ≤ ·) s) :
    Set.InjOn g s := by
  intro x hx y hy hxy
  by_contra hne
  rcases hs hx hy hne with h | h
  · exact hg (g x) (show x ∈ g ⁻¹' {g x} from rfl) (show y ∈ g ⁻¹' {g x} from hxy.symm) hne h
  · exact hg (g x) (show y ∈ g ⁻¹' {g x} from hxy.symm) (show x ∈ g ⁻¹' {g x} from rfl)
      (Ne.symm hne) h

/-- CO-157. Mirsky's theorem (dual of Dilworth), covering part: a finite poset of height `h`
is partitioned into `h` antichains. -/
@[kb "kellertrotter2017" "Theorem 6.18, p. 146"]
theorem mirsky_exists_partition :
    ∃ f : α → Fin (height α), ∀ i, IsAntichain (· ≤ ·) (f ⁻¹' {i}) := by
  have hlt : ∀ x : α, pointHeight x - 1 < height α := fun x => by
    have := pointHeight_pos x; have := pointHeight_le_height x; omega
  refine ⟨fun x => ⟨pointHeight x - 1, hlt x⟩, fun i x hx y hy hne hxy => ?_⟩
  have h1 := pointHeight_lt_of_lt (lt_of_le_of_ne hxy hne)
  have h2 : (⟨pointHeight x - 1, hlt x⟩ : Fin (height α)) = ⟨pointHeight y - 1, hlt y⟩ :=
    hx.trans hy.symm
  have := pointHeight_pos x
  have := Fin.mk.inj h2
  omega

/-- CO-157. Mirsky's theorem, optimality part: no partition into fewer than `height` antichains. -/
@[kb "kellertrotter2017" "Theorem 6.18, p. 146"]
theorem height_le_card_of_antichain_partition {ι : Type*} [Fintype ι] (g : α → ι)
    (hg : ∀ i, IsAntichain (· ≤ ·) (g ⁻¹' {i})) : height α ≤ Fintype.card ι := by
  classical
  obtain ⟨s, hs, hcard⟩ := exists_chain_card_eq_height (α := α)
  rw [← hcard]
  calc s.card ≤ (Finset.univ : Finset ι).card :=
        Finset.card_le_card_of_injOn g (fun _ _ => Finset.mem_univ _)
          (injOn_of_antichain_fibers hg hs)
    _ = Fintype.card ι := Finset.card_univ

/-- CO-157, book-shaped: partition into exactly `h` antichains and no partition into fewer. -/
theorem mirsky :
    (∃ f : α → Fin (height α), ∀ i, IsAntichain (· ≤ ·) (f ⁻¹' {i})) ∧
    ∀ (n : ℕ) (g : α → Fin n), (∀ i, IsAntichain (· ≤ ·) (g ⁻¹' {i})) → height α ≤ n := by
  refine ⟨mirsky_exists_partition, fun n g hg => ?_⟩
  simpa using height_le_card_of_antichain_partition g hg

end UndergradKB.Combinatorics.Order
