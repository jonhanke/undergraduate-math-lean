import Mathlib.Order.Antichain
import Mathlib.Order.Preorder.Chain
import Mathlib.Order.Minimal
import Mathlib.Order.Preorder.Finite
import Mathlib.Order.Hom.Set
import Mathlib.Order.Zorn
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Card
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.Order.Basic

/-!
# Finite posets: ones and zeros, duals, maximal versus maximum chains, the subset lattice

Source: Keller--Trotter, *Applied Combinatorics* (2017), Chapter 6.
-/

namespace UndergradKB.Combinatorics.Order

open Finset

variable {α : Type*} [PartialOrder α]

/-! ### CO-151: one and zero -/

/-- CO-151. In a finite poset, there is exactly one maximal point if and only if there is a
greatest point (the book's `1`). -/
@[kb "kellertrotter2017" "Definition (unnumbered) one and zero, p. 144"]
theorem existsUnique_isMax_iff_exists_isGreatest [Finite α] :
    (∃! x : α, IsMax x) ↔ ∃ x : α, ∀ y, y ≤ x := by
  constructor
  · rintro ⟨x, hx, huniq⟩
    refine ⟨x, fun y => ?_⟩
    obtain ⟨b, hyb, hb⟩ := Finite.exists_le_maximal (p := fun _ : α => True) (a := y) trivial
    have : b = x := huniq b (maximal_true.1 hb)
    exact this ▸ hyb
  · rintro ⟨x, hx⟩
    exact ⟨x, fun b _ => hx b, fun y hy => le_antisymm (hx y) (hy (hx y))⟩

/-- CO-151 (dual form). In a finite poset, there is exactly one minimal point if and only if there
is a least point (the book's `0`). -/
@[kb "kellertrotter2017" "Definition (unnumbered) one and zero, p. 144"]
theorem existsUnique_isMin_iff_exists_isLeast [Finite α] :
    (∃! x : α, IsMin x) ↔ ∃ x : α, ∀ y, x ≤ y := by
  constructor
  · rintro ⟨x, hx, huniq⟩
    refine ⟨x, fun y => ?_⟩
    obtain ⟨b, hyb, hb⟩ := Finite.exists_le_maximal (α := αᵒᵈ) (p := fun _ => True)
      (a := OrderDual.toDual y) trivial
    have hb' : IsMin (OrderDual.ofDual b) := maximal_true.1 hb
    have : OrderDual.ofDual b = x := huniq _ hb'
    exact this ▸ hyb
  · rintro ⟨x, hx⟩
    exact ⟨x, fun b hb => hx b, fun y hy => le_antisymm (hy (hx y)) (hx y)⟩

/-! ### CO-152: duals and self-dual posets -/

/-- CO-152. A poset is self-dual if it is order-isomorphic to its dual (Mathlib's `OrderDual`,
the poset with all comparabilities reversed). -/
@[kb "kellertrotter2017" "Definition (unnumbered) dual and self-dual, p. 144"]
def IsSelfDual (α : Type*) [PartialOrder α] : Prop := Nonempty (α ≃o αᵒᵈ)

/-- CO-152. The dual reverses the order: `x ≤ y` in `α` iff `y ≤ x` in the dual. -/
theorem dual_le_iff {x y : α} : OrderDual.toDual x ≤ OrderDual.toDual y ↔ y ≤ x := Iff.rfl

/-- CO-152. The dual of a self-dual poset is self-dual. -/
theorem IsSelfDual.dual (h : IsSelfDual α) : IsSelfDual αᵒᵈ := ⟨h.some.dual⟩

/-- CO-152. The subset lattice of a finite set is self-dual (via complement). -/
theorem isSelfDual_finset (t : ℕ) : IsSelfDual (Finset (Fin t)) := ⟨OrderIso.compl _⟩

/-- CO-152. The chain `ℕ` has a least point but no greatest point, so it is not self-dual. -/
theorem not_isSelfDual_nat : ¬ IsSelfDual ℕ := by
  rintro ⟨e⟩
  have h : e 0 ≤ e (e.symm (OrderDual.toDual (OrderDual.ofDual (e 0) + 1))) :=
    e.le_iff_le.2 (Nat.zero_le _)
  rw [e.apply_symm_apply] at h
  have := OrderDual.ofDual_le_ofDual.2 h
  simp at this

/-! ### CO-160: maximal and maximum chains and antichains -/

/-- CO-160. A chain (a finite set of points) is maximum if no chain has more points. -/
@[kb "kellertrotter2017" "Definition (unnumbered) maximal/maximum chain, p. 147"]
def IsMaximumChain (s : Finset α) : Prop :=
  IsChain (· ≤ ·) (s : Set α) ∧ ∀ t : Finset α, IsChain (· ≤ ·) (t : Set α) → t.card ≤ s.card

/-- CO-160. An antichain is maximum if no antichain has more points. -/
@[kb "kellertrotter2017" "Definition (unnumbered) maximal/maximum antichain, p. 147"]
def IsMaximumAntichain (s : Finset α) : Prop :=
  IsAntichain (· ≤ ·) (s : Set α) ∧
    ∀ t : Finset α, IsAntichain (· ≤ ·) (t : Set α) → t.card ≤ s.card

/-- CO-160. In a finite poset a maximum chain is maximal (Mathlib's `IsMaxChain`). -/
@[kb "kellertrotter2017" "text (unnumbered) maximum implies maximal, p. 147"]
theorem IsMaximumChain.isMaxChain [Finite α] {s : Finset α} (h : IsMaximumChain s) :
    IsMaxChain (· ≤ ·) (s : Set α) := by
  classical
  refine ⟨h.1, fun c hc hsc => ?_⟩
  have := Fintype.ofFinite α
  have hfin : c.Finite := c.toFinite
  have hsub : s ⊆ hfin.toFinset := fun x hx => by simpa using hsc hx
  have hle := h.2 hfin.toFinset (by simpa using hc)
  have := Finset.eq_of_subset_of_card_le hsub hle
  rw [← Set.Finite.coe_toFinset hfin, this]

/-- CO-160. In a finite poset a maximum antichain is maximal. -/
@[kb "kellertrotter2017" "text (unnumbered) maximum implies maximal, p. 147"]
theorem IsMaximumAntichain.maximal [Finite α] {s : Finset α} (h : IsMaximumAntichain s) :
    Maximal (IsAntichain (· ≤ ·)) (s : Set α) := by
  classical
  refine ⟨h.1, fun c hc hsc => ?_⟩
  have := Fintype.ofFinite α
  have hfin : c.Finite := c.toFinite
  have hsub : s ⊆ hfin.toFinset := fun x hx => by simpa using hsc hx
  have hle := h.2 hfin.toFinset (by simpa using hc)
  have := Finset.eq_of_subset_of_card_le hsub hle
  rw [← Set.Finite.coe_toFinset hfin, this]

/-- A four-point poset: `∅ < {0} < {0,1}` together with `∅ < {2}`, as a subposet of the subsets
of `{0,1,2}`. -/
abbrev Ex160 : Type := {s : Finset (Fin 3) // s = ∅ ∨ s = {0} ∨ s = {0, 1} ∨ s = {2}}

namespace Ex160

/-- The bottom point. -/
def a : Ex160 := ⟨∅, by decide⟩
/-- The point `{0}`. -/
def b : Ex160 := ⟨{0}, by decide⟩
/-- The point `{0,1}`. -/
def c : Ex160 := ⟨{0, 1}, by decide⟩
/-- The point `{2}`. -/
def d : Ex160 := ⟨{2}, by decide⟩

theorem cases (x : Ex160) : x = a ∨ x = b ∨ x = c ∨ x = d := by
  obtain ⟨s, hs⟩ := x
  rcases hs with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

theorem a_le (x : Ex160) : a ≤ x := Subtype.mk_le_mk.2 (Finset.empty_subset _)

theorem not_b_le_d : ¬ b ≤ d := by decide

theorem not_d_le_b : ¬ d ≤ b := by decide

theorem not_c_le_d : ¬ c ≤ d := by decide

theorem not_d_le_c : ¬ d ≤ c := by decide

theorem b_le_c : b ≤ c := by decide

end Ex160

/-- CO-160. Maximal chains need not be maximum: `{∅, {2}}` is a maximal chain of `Ex160` of
two points, while `{∅, {0}, {0,1}}` is a chain of three points. -/
@[kb "kellertrotter2017" "text (unnumbered) maximal need not be maximum, p. 147"]
theorem exists_maxChain_not_maximum :
    ∃ s : Finset Ex160, IsMaxChain (· ≤ ·) (s : Set Ex160) ∧ ¬ IsMaximumChain s := by
  classical
  refine ⟨{Ex160.a, Ex160.d}, ⟨?_, ?_⟩, ?_⟩
  · intro x hx y hy _
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Or.inl le_rfl
    · exact Or.inl (Ex160.a_le _)
    · exact Or.inr (Ex160.a_le _)
    · exact Or.inl le_rfl
  · intro C hC hsC
    refine Set.Subset.antisymm hsC ?_
    intro x hx
    have hd : Ex160.d ∈ C := hsC (by simp)
    rw [Finset.mem_coe]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases Ex160.cases x with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · rcases hC hx hd (by decide) with h | h
      · exact absurd h Ex160.not_b_le_d
      · exact absurd h Ex160.not_d_le_b
    · rcases hC hx hd (by decide) with h | h
      · exact absurd h Ex160.not_c_le_d
      · exact absurd h Ex160.not_d_le_c
    · exact Or.inr rfl
  · intro h
    have := h.2 {Ex160.a, Ex160.b, Ex160.c} (by
      intro x hx y hy hxy
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
      all_goals first
        | exact absurd rfl hxy
        | exact Or.inl (Ex160.a_le _)
        | exact Or.inr (Ex160.a_le _)
        | exact Or.inl Ex160.b_le_c
        | exact Or.inr Ex160.b_le_c)
    revert this
    decide

/-- CO-160. Maximal antichains need not be maximum: `{∅}` is a maximal antichain of `Ex160`
of one point, while `{{0,1}, {2}}` is an antichain of two points. -/
@[kb "kellertrotter2017" "text (unnumbered) maximal need not be maximum, p. 147"]
theorem exists_maximal_antichain_not_maximum :
    ∃ s : Finset Ex160, Maximal (IsAntichain (· ≤ ·)) (s : Set Ex160) ∧ ¬ IsMaximumAntichain s := by
  classical
  refine ⟨{Ex160.a}, ⟨?_, ?_⟩, ?_⟩
  · simp
  · intro C hC hsC x hx
    have ha : Ex160.a ∈ C := hsC (by simp)
    by_cases hxa : x = Ex160.a
    · simp [hxa]
    · exact absurd (Ex160.a_le x) (hC ha hx (Ne.symm hxa))
  · intro h
    have := h.2 {Ex160.c, Ex160.d} (by
      intro x hx y hy hxy
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact absurd rfl hxy
      · exact Ex160.not_c_le_d
      · exact Ex160.not_d_le_c
      · exact absurd rfl hxy)
    revert this
    decide

/-! ### CO-154: the class of comparability graphs and of cover graphs -/

universe u

/-- CO-154. A graph is a comparability graph if it is isomorphic to the comparability graph of
some poset. -/
@[kb "kellertrotter2017" "Definition (unnumbered) comparability graph class, p. 144"]
def IsComparabilityGraph {V : Type u} (G : SimpleGraph V) : Prop :=
  ∃ (P : Type u) (_ : PartialOrder P), Nonempty (G ≃g comparabilityGraph P)

/-- CO-154. A graph is a cover graph if it is isomorphic to the cover (Hasse) graph of some poset;
the cover graph is Mathlib's `SimpleGraph.hasse`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) cover graph class, p. 145"]
def IsCoverGraph {V : Type u} (G : SimpleGraph V) : Prop :=
  ∃ (P : Type u) (_ : PartialOrder P), Nonempty (G ≃g SimpleGraph.hasse P)

/-- CO-154. The comparability graph of a poset is a comparability graph. -/
theorem isComparabilityGraph_comparabilityGraph {P : Type u} [PartialOrder P] :
    IsComparabilityGraph (comparabilityGraph P) := ⟨P, inferInstance, ⟨SimpleGraph.Iso.refl⟩⟩

/-- CO-154. The cover graph of a poset is a cover graph. -/
theorem isCoverGraph_hasse {P : Type u} [PartialOrder P] :
    IsCoverGraph (SimpleGraph.hasse P) := ⟨P, inferInstance, ⟨SimpleGraph.Iso.refl⟩⟩

/-- CO-154 (Discussion 6.16, item 2). A poset and its dual have the same comparability graph. -/
theorem comparabilityGraph_dual {P : Type u} [PartialOrder P] :
    Nonempty (comparabilityGraph Pᵒᵈ ≃g comparabilityGraph P) := by
  refine ⟨⟨OrderDual.ofDual, fun {x y} => ?_⟩⟩
  simp only [comparabilityGraph_adj, Comparable]
  exact ⟨fun h => ⟨fun e => h.1 (congrArg OrderDual.toDual e), h.2.symm⟩,
    fun h => ⟨fun e => h.1 (congrArg OrderDual.ofDual e), h.2.symm⟩⟩

/-! ### CO-165: the subset lattice -/

section SubsetLattice

variable (t : ℕ)

/-- The cardinalities of the members of a chain of subsets are distinct. -/
theorem card_injOn_chain {C : Finset (Finset (Fin t))} (hC : IsChain (· ≤ ·) (C : Set (Finset (Fin t)))) :
    Set.InjOn Finset.card (C : Set (Finset (Fin t))) := by
  intro x hx y hy hxy
  by_contra hne
  rcases hC hx hy hne with h | h
  · exact hne (Finset.eq_of_subset_of_card_le h hxy.ge)
  · exact hne (Finset.eq_of_subset_of_card_le h hxy.le).symm

theorem chain_card_le {C : Finset (Finset (Fin t))} (hC : IsChain (· ≤ ·) (C : Set (Finset (Fin t)))) :
    C.card ≤ t + 1 := by
  have h := Finset.card_le_card_of_injOn (t := Finset.range (t + 1)) Finset.card
    (fun x _ => by
      simpa [Nat.lt_succ_iff] using (by simpa using Finset.card_le_univ x : x.card ≤ t))
    (card_injOn_chain t hC)
  simpa using h

/-- CO-165, part 1. Every maximal chain of the subset lattice `2^t` has exactly `t + 1` points. -/
@[kb "kellertrotter2017" "text (unnumbered) subset lattice, p. 150"]
theorem card_of_isMaxChain {M : Finset (Finset (Fin t))}
    (hM : IsMaxChain (· ≤ ·) (M : Set (Finset (Fin t)))) : M.card = t + 1 := by
  classical
  refine le_antisymm (chain_card_le t hM.1) ?_
  by_contra hlt
  rw [not_le] at hlt
  have hlt' : (M.image Finset.card).card < (Finset.range (t + 1)).card := by
    rw [Finset.card_range]
    exact lt_of_le_of_lt Finset.card_image_le (by omega)
  obtain ⟨k, hk, hkM⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt'
  have hkt : k ≤ t := by simpa [Nat.lt_succ_iff] using hk
  have hkM' : ∀ x ∈ M, x.card ≠ k := fun x hx e => hkM (Finset.mem_image.2 ⟨x, hx, e⟩)
  have hch := hM.1
  -- the largest member below level `k`
  obtain ⟨A, hA0, hA1, hA2⟩ : ∃ A : Finset (Fin t), (A = ∅ ∨ (A ∈ M ∧ A.card < k)) ∧
      (∀ x ∈ M, x.card < k → x ⊆ A) ∧ (∀ x ∈ M, k < x.card → A ⊆ x) := by
    by_cases hL : (M.filter fun x => x.card < k).Nonempty
    · obtain ⟨A, hA, hmax⟩ := Finset.exists_max_image _ Finset.card hL
      rw [Finset.mem_filter] at hA
      refine ⟨A, Or.inr hA, fun x hx hxk => ?_, fun x hx hxk => ?_⟩
      · by_cases hxA : x = A
        · exact hxA ▸ subset_rfl
        · rcases hch hx hA.1 hxA with h | h
          · exact h
          · exact (Finset.eq_of_subset_of_card_le h
              (hmax x (Finset.mem_filter.2 ⟨hx, hxk⟩))).symm ▸ subset_rfl
      · by_cases hxA : A = x
        · exact hxA ▸ subset_rfl
        · rcases hch hA.1 hx hxA with h | h
          · exact h
          · have := Finset.card_le_card h
            omega
    · refine ⟨∅, Or.inl rfl, fun x hx hxk => ?_, fun x _ _ => Finset.empty_subset _⟩
      exact absurd ⟨x, Finset.mem_filter.2 ⟨hx, hxk⟩⟩ hL
  obtain ⟨B, hB0, hB1, hB2⟩ : ∃ B : Finset (Fin t), k ≤ B.card ∧
      (∀ x ∈ M, k < x.card → B ⊆ x) ∧ (∀ x ∈ M, x.card < k → x ⊆ B) := by
    by_cases hH : (M.filter fun x => k < x.card).Nonempty
    · obtain ⟨B, hB, hmin⟩ := Finset.exists_min_image _ Finset.card hH
      rw [Finset.mem_filter] at hB
      refine ⟨B, hB.2.le, fun x hx hxk => ?_, fun x hx hxk => ?_⟩
      · by_cases hxB : B = x
        · exact hxB ▸ subset_rfl
        · rcases hch hB.1 hx hxB with h | h
          · exact h
          · exact (Finset.eq_of_subset_of_card_le h
              (hmin x (Finset.mem_filter.2 ⟨hx, hxk⟩))).symm ▸ subset_rfl
      · by_cases hxB : x = B
        · exact hxB ▸ subset_rfl
        · rcases hch hx hB.1 hxB with h | h
          · exact h
          · have := Finset.card_le_card h
            omega
    · refine ⟨Finset.univ, by simpa using hkt, fun x hx hxk => ?_, fun x _ _ =>
        Finset.subset_univ _⟩
      exact absurd ⟨x, Finset.mem_filter.2 ⟨hx, hxk⟩⟩ hH
  have hAB : A ⊆ B := by
    rcases hA0 with rfl | ⟨hAM, _⟩
    · exact Finset.empty_subset _
    · exact hB2 A hAM (by tauto)
  have hAk : A.card ≤ k := by
    rcases hA0 with rfl | ⟨_, h⟩
    · simp
    · exact h.le
  obtain ⟨X, hAX, hXB, hXk⟩ := Finset.exists_subsuperset_card_eq hAB hAk hB0
  have hXM : insert X M = M := by
    have := hM.2 (t := ((insert X M : Finset (Finset (Fin t))) : Set (Finset (Fin t)))) ?_ ?_
    · exact_mod_cast this.symm
    · rw [Finset.coe_insert]
      refine hch.insert fun x hx hne => ?_
      rcases lt_trichotomy x.card k with h | h | h
      · exact Or.inr ((hA1 x hx h).trans hAX)
      · exact absurd h (hkM' x hx)
      · exact Or.inl (hXB.trans (hB1 x hx h))
    · rw [Finset.coe_insert]
      exact Set.subset_insert _ _
  have : X ∈ M := hXM ▸ Finset.mem_insert_self X M
  exact hkM' X this hXk

/-- CO-165, part 1. The subset lattice `2^t` has height `t + 1`. -/
@[kb "kellertrotter2017" "text (unnumbered) subset lattice, p. 150"]
theorem height_finset : height (Finset (Fin t)) = t + 1 := by
  classical
  refine le_antisymm ?_ ?_
  · obtain ⟨s, hs, hcard⟩ := exists_chain_card_eq_height (α := Finset (Fin t))
    rw [← hcard]
    exact chain_card_le t hs
  · obtain ⟨M, hM, -⟩ := (IsChain.empty (r := (· ≤ ·)) (α := Finset (Fin t))).exists_maxChain
    have hfin : M.Finite := M.toFinite
    have := card_of_isMaxChain t (M := hfin.toFinset) (by simpa using hM)
    rw [← this]
    exact card_le_height (by simpa using hM.1)

/-- CO-165, part 2. The `i`-th rank of `2^t`: the `i`-element subsets. -/
def rank (i : ℕ) : Finset (Finset (Fin t)) := Finset.powersetCard i Finset.univ

/-- CO-165, part 2. The size of `2^t` is `2^t`. -/
@[kb "kellertrotter2017" "text (unnumbered) subset lattice, p. 150"]
theorem card_subsets : Fintype.card (Finset (Fin t)) = 2 ^ t := by simp

/-- CO-165, part 2. Each rank is an antichain. -/
@[kb "kellertrotter2017" "text (unnumbered) subset lattice, p. 150"]
theorem isAntichain_rank (i : ℕ) : IsAntichain (· ≤ ·) (rank t i : Set (Finset (Fin t))) := by
  intro x hx y hy hne h
  simp only [rank, Finset.mem_coe, Finset.mem_powersetCard] at hx hy
  exact hne (Finset.eq_of_subset_of_card_le h (by omega))

/-- CO-165, part 2. The ranks `A_0, …, A_t` partition the subsets: each subset lies in exactly
the rank given by its size, and that is at most `t`. -/
@[kb "kellertrotter2017" "text (unnumbered) subset lattice, p. 150"]
theorem rank_partition (s : Finset (Fin t)) : ∃! i, s ∈ rank t i := by
  refine ⟨s.card, by simp [rank], fun i hi => ?_⟩
  simp only [rank, Finset.mem_powersetCard] at hi
  exact hi.2.symm

/-- CO-165, part 2. `|A_i| = C(t, i)`. -/
@[kb "kellertrotter2017" "text (unnumbered) subset lattice, p. 150"]
theorem card_rank (i : ℕ) : (rank t i).card = Nat.choose t i := by
  simp [rank]

/-- CO-165, part 3. The largest rank is at `⌊t/2⌋`: `C(t, i) ≤ C(t, ⌊t/2⌋)` for every `i`. -/
@[kb "kellertrotter2017" "text (unnumbered) subset lattice, p. 150"]
theorem card_rank_le_middle (i : ℕ) : (rank t i).card ≤ (rank t (t / 2)).card := by
  simp only [card_rank]
  exact Nat.choose_le_middle i t

/-- CO-165, part 3. When `t` is odd, the ranks `⌊t/2⌋` and `⌊t/2⌋ + 1` are the two largest and have
equal size. -/
theorem card_rank_middle_odd (h : t % 2 = 1) : (rank t (t / 2)).card = (rank t (t / 2 + 1)).card := by
  simp only [card_rank]
  have : t - t / 2 = t / 2 + 1 := by omega
  rw [← Nat.choose_symm (show t / 2 ≤ t by omega), this]

end SubsetLattice

end UndergradKB.Combinatorics.Order
