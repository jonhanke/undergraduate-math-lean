import Mathlib.Order.Antichain
import Mathlib.Order.Preorder.Chain
import Mathlib.Order.Preorder.Finite
import Mathlib.Logic.Relation
import Mathlib.Data.Fintype.Card
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.Order.Basic
import UndergradKB.Combinatorics.Order.Dilworth
import UndergradKB.Combinatorics.Flow.MaxFlowMinCut
import UndergradKB.Combinatorics.Flow.Matching

/-!
# Chain partitions from network flows (Keller--Trotter, Section 14.3)

The chain-partition network of a poset has a source `S`, a sink `T`, and two copies `x'`, `x''` of
every point; its edges are `S → x'`, `x' → y''` when `x < y`, and `y'' → T`, all of capacity one.
This is exactly the matching network (Section 14.2, `Flow/Matching.lean`) of the bipartite graph
`x < y`, so integral flows of value `v` are matchings of size `v`. A matching of size `v` links
the points into paths `x_1 < x_2 < ...`; the paths are chains, and there are `|P| - v` of them.
-/

namespace UndergradKB.Combinatorics.Order

open UndergradKB.Combinatorics.Flow

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

variable (α) in
/-- CO-305. The chain-partition network of a finite poset: source to every `x'`, `x' → y''`
whenever `x < y`, every `y''` to the sink, all capacities one. (The vertex of `x'` is
`some (some (Sum.inl x))`, that of `y''` is `some (some (Sum.inr y))`.) -/
@[kb "kellertrotter2017" "text (poset network), p. 308"]
noncomputable def chainNetwork : Network (Option (Option (α ⊕ α))) :=
  matchingNetwork (fun x y : α => x < y)

omit [Fintype α] [DecidableEq α] in
/-- CO-305. The edges of the chain-partition network are exactly the three kinds described by the
book, and each has capacity one. -/
@[kb "kellertrotter2017" "text (poset network), p. 308"]
theorem chainNetwork_adj_iff (u v : Option (Option (α ⊕ α))) :
    (chainNetwork α).adj u v ↔
      (u = none ∧ ∃ x, v = some (some (Sum.inl x))) ∨
      (∃ x y : α, x < y ∧ u = some (some (Sum.inl x)) ∧ v = some (some (Sum.inr y))) ∨
      ((∃ y, u = some (some (Sum.inr y))) ∧ v = some none) := by
  rcases u with _ | _ | x | x <;> rcases v with _ | _ | y | y <;>
    simp [chainNetwork, matchingNetwork, MatchingNetwork.adj]

omit [Fintype α] [DecidableEq α] in
/-- CO-305. Every edge of the chain-partition network has capacity one. -/
theorem chainNetwork_cap (u v : Option (Option (α ⊕ α))) (h : (chainNetwork α).adj u v) :
    (chainNetwork α).cap u v = 1 := by
  have h' : MatchingNetwork.adj (fun x y : α => x < y) u v := h
  simp [chainNetwork, matchingNetwork, h']

/-! ### From a matching to a chain partition -/

section FromMatching

variable {M : Finset (α × α)}

/-- The successor relation of a matching of the strict order: `x` is matched to `y`. -/
def succRel (M : Finset (α × α)) (x y : α) : Prop := (x, y) ∈ M

omit [Fintype α] [DecidableEq α] in
theorem reflTransGen_succRel_le (hM : IsMatching (fun x y : α => x < y) M) {x y : α}
    (h : Relation.ReflTransGen (succRel M) x y) : x ≤ y := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih => exact ih.trans (hM.1 _ hbc).le

omit [DecidableEq α] in
theorem exists_head (hM : IsMatching (fun x y : α => x < y) M) (x : α) :
    ∃ h, (¬ ∃ w, succRel M w h) ∧ Relation.ReflTransGen (succRel M) h x := by
  induction x using WellFoundedLT.induction with
  | _ x ih =>
    by_cases hx : ∃ w, succRel M w x
    · obtain ⟨w, hw⟩ := hx
      obtain ⟨h, hh, hr⟩ := ih w (hM.1 _ hw)
      exact ⟨h, hh, hr.tail hw⟩
    · exact ⟨x, hx, Relation.ReflTransGen.refl⟩

open Classical in
theorem card_noPredecessor (hM : IsMatching (fun x y : α => x < y) M) :
    Fintype.card {z : α // ¬ ∃ w, succRel M w z} = Fintype.card α - M.card := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype]
  congr 1
  have : (Finset.univ.filter fun z : α => ∃ w, succRel M w z) = M.image Prod.snd := by
    ext z
    constructor
    · intro hz
      obtain ⟨w, hw⟩ := (Finset.mem_filter.1 hz).2
      exact Finset.mem_image.2 ⟨(w, z), hw, rfl⟩
    · intro hz
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hz
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, p.1, hp⟩
  rw [this, Finset.card_image_of_injOn]
  intro p hp q hq hpq
  exact hM.2.2 p hp q hq hpq

open Classical in
/-- CO-307. A matching of size `v` in the bipartite graph of the strict order yields a partition of
the poset into `|P| - v` chains: follow the matched edges `x → y` into paths. -/
@[kb "kellertrotter2017" "text (chains from flow edges), p. 310"]
theorem chain_partition_of_matching (hM : IsMatching (fun x y : α => x < y) M) :
    ∃ g : α → Fin (Fintype.card α - M.card), ∀ i, IsChain (· ≤ ·) (g ⁻¹' {i}) := by
  choose head hhead1 hhead2 using exists_head hM
  let e : {z : α // ¬ ∃ w, succRel M w z} ≃ Fin (Fintype.card α - M.card) :=
    Fintype.equivFinOfCardEq (card_noPredecessor hM)
  refine ⟨fun x => e ⟨head x, hhead1 x⟩, fun i x hx y hy hxy => ?_⟩
  have hx' : e ⟨head x, hhead1 x⟩ = i := hx
  have hy' : e ⟨head y, hhead1 y⟩ = i := hy
  have hh : head x = head y := by
    have := e.injective (hx'.trans hy'.symm)
    exact congrArg Subtype.val this
  have hru : Relator.RightUnique (succRel M) := fun a b c hab hac =>
    congrArg Prod.snd (hM.2.1 _ hab _ hac rfl)
  have h1 := hhead2 x
  have h2 := hhead2 y
  rw [hh] at h1
  rcases Relation.ReflTransGen.total_of_right_unique hru h1 h2 with h | h
  · exact Or.inl (reflTransGen_succRel_le hM h)
  · exact Or.inr (reflTransGen_succRel_le hM h)

end FromMatching

/-- CO-306/CO-307. **Chain partitions from flows.** An integral flow of value `v` in the
chain-partition network of a finite poset gives a partition of the poset into `|P| - v` chains
(the chains are the paths of points joined by the edges `x' → y''` carrying flow). -/
@[kb "kellertrotter2017" "text (chains from flow edges), p. 310"]
theorem chain_partition_of_flow {φ : Option (Option (α ⊕ α)) → Option (Option (α ⊕ α)) → ℝ}
    (hφ : (chainNetwork α).IsFlow φ) (hint : ∀ x y, ∃ n : ℕ, φ x y = n) {v : ℕ}
    (hv : (chainNetwork α).value φ = v) :
    ∃ g : α → Fin (Fintype.card α - v), ∀ i, IsChain (· ≤ ·) (g ⁻¹' {i}) := by
  obtain ⟨M, hM, hcard⟩ := exists_matching_of_flow hφ hint
  have : M.card = v := by
    have h : (M.card : ℝ) = v := hcard.trans hv
    exact_mod_cast h
  rw [← this]
  exact chain_partition_of_matching hM

/-- CO-306. A maximum flow in the chain-partition network (which exists and may be taken integral)
yields a chain partition into `|P| - v` chains, where `v` is its value; moreover `v` is the largest
possible size of a matching of the strict order. -/
@[kb "kellertrotter2017" "text (poset network algorithm), p. 308"]
theorem exists_maxFlow_chain_partition :
    ∃ (φ : Option (Option (α ⊕ α)) → Option (Option (α ⊕ α)) → ℝ) (v : ℕ),
      (chainNetwork α).IsFlow φ ∧ (chainNetwork α).value φ = v ∧
      (∀ ψ, (chainNetwork α).IsFlow ψ → (chainNetwork α).value ψ ≤ v) ∧
      ∃ g : α → Fin (Fintype.card α - v), ∀ i, IsChain (· ≤ ·) (g ⁻¹' {i}) := by
  obtain ⟨M, φ, hM, hφ, hcard, hmax, -⟩ := maxMatching_eq_maxFlow (fun x y : α => x < y)
  refine ⟨φ, M.card, hφ, hcard.symm, fun ψ hψ => ?_, ?_⟩
  · exact (hmax ψ hψ).trans_eq hcard.symm
  · exact chain_partition_of_matching hM

/-! ### From a chain partition to a matching, and Dilworth's theorem via flows -/

section ToMatching

open Classical

omit [DecidableEq α] in
theorem card_matching_le (M : Finset (α × α)) (hM : IsMatching (fun x y : α => x < y) M) :
    M.card ≤ Fintype.card α := by
  classical
  have : (M.image Prod.snd).card = M.card := by
    apply Finset.card_image_of_injOn
    intro p hp q hq hpq
    exact hM.2.2 p hp q hq hpq
  rw [← this]
  exact Finset.card_le_univ _

/-- A partition of the poset into `k` chains yields a matching of the strict order of size at least
`|P| - k`: match each point to the least larger point of its own chain. -/
theorem exists_matching_of_chain_partition {k : ℕ} (g : α → Fin k)
    (hg : ∀ i, IsChain (· ≤ ·) (g ⁻¹' {i})) :
    ∃ M : Finset (α × α), IsMatching (fun x y : α => x < y) M ∧ Fintype.card α - k ≤ M.card := by
  let S : α → Finset α := fun x => Finset.univ.filter fun y => x < y ∧ g y = g x
  have hcomp : ∀ x y, g x = g y → x ≠ y → x < y ∨ y < x := by
    intro x y hxy hne
    rcases hg (g y) (show x ∈ g ⁻¹' {g y} from hxy) (show y ∈ g ⁻¹' {g y} from rfl) hne with h | h
    · exact Or.inl (lt_of_le_of_ne h hne)
    · exact Or.inr (lt_of_le_of_ne h (Ne.symm hne))
  have hs : ∀ x, (S x).Nonempty → ∃ y ∈ S x, ∀ z ∈ S x, y ≤ z := by
    intro x hne
    obtain ⟨y, hy⟩ := Finset.exists_minimal hne
    refine ⟨y, hy.1, fun z hz => ?_⟩
    by_cases hzy : z = y
    · exact hzy.ge
    have hgy := (Finset.mem_filter.1 hy.1).2.2
    have hgz := (Finset.mem_filter.1 hz).2.2
    rcases hcomp z y (hgz.trans hgy.symm) hzy with h | h
    · exact (hy.2 hz h.le)
    · exact h.le
  choose! nxt hnxt using hs
  let A : Finset α := Finset.univ.filter fun x => (S x).Nonempty
  let M : Finset (α × α) := A.image fun x => (x, nxt x)
  have hnxtS : ∀ x, (S x).Nonempty → x < nxt x ∧ g (nxt x) = g x := fun x hx =>
    (Finset.mem_filter.1 (hnxt x hx).1).2
  have hmatch : IsMatching (fun x y : α => x < y) M := by
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hp
      exact (hnxtS x (Finset.mem_filter.1 hx).2).1
    · intro p hp q hq hpq
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hp
      obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hq
      have : x = x' := hpq
      rw [this]
    · intro p hp q hq hpq
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hp
      obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hq
      have hpq' : nxt x = nxt x' := hpq
      have hx1 := hnxtS x (Finset.mem_filter.1 hx).2
      have hx2 := hnxtS x' (Finset.mem_filter.1 hx').2
      by_contra hne
      have hxx : x ≠ x' := fun h => hne (by rw [h])
      have hg' : g x = g x' := hx1.2.symm.trans (hpq' ▸ hx2.2)
      rcases hcomp x x' hg' hxx with h | h
      · have hm : x' ∈ S x := Finset.mem_filter.2 ⟨Finset.mem_univ _, h, hg'.symm⟩
        have := (hnxt x (Finset.mem_filter.1 hx).2).2 x' hm
        rw [hpq'] at this
        exact lt_irrefl x' (hx2.1.trans_le this)
      · have hm : x ∈ S x' := Finset.mem_filter.2 ⟨Finset.mem_univ _, h, hg'⟩
        have := (hnxt x' (Finset.mem_filter.1 hx').2).2 x hm
        rw [← hpq'] at this
        exact lt_irrefl x (hx1.1.trans_le this)
  refine ⟨M, hmatch, ?_⟩
  have hMA : M.card = A.card := by
    apply Finset.card_image_of_injOn
    intro x _ y _ hxy
    exact (Prod.mk.inj hxy).1
  have hB : (Finset.univ.filter fun x : α => ¬ (S x).Nonempty).card ≤ k := by
    have : (Finset.univ.filter fun x : α => ¬ (S x).Nonempty).card ≤
        (Finset.univ : Finset (Fin k)).card := by
      apply Finset.card_le_card_of_injOn g (fun _ _ => Finset.mem_univ _)
      intro x hx y hy hxy
      by_contra hne
      have hx' := (Finset.mem_filter.1 hx).2
      have hy' := (Finset.mem_filter.1 hy).2
      rcases hcomp x y hxy hne with h | h
      · exact hx' ⟨y, Finset.mem_filter.2 ⟨Finset.mem_univ _, h, hxy.symm⟩⟩
      · exact hy' ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ _, h, hxy⟩⟩
    simpa using this
  have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset α))
    (fun x : α => (S x).Nonempty)
  rw [Finset.card_univ] at hsum
  rw [hMA]
  show Fintype.card α - k ≤ (Finset.univ.filter fun x => (S x).Nonempty).card
  omega

end ToMatching

/-- CO-306. **Dilworth's theorem through flows.** In the chain-partition network of a finite poset
there is an integral maximum flow, and its value is `|P| - width(P)`; the chains read off its flow
edges form a partition into exactly `width(P)` chains. -/
@[kb "kellertrotter2017" "text (poset network algorithm), p. 308"]
theorem exists_maxFlow_value_eq_card_sub_width :
    ∃ φ : Option (Option (α ⊕ α)) → Option (Option (α ⊕ α)) → ℝ,
      (chainNetwork α).IsFlow φ ∧ (∀ x y, ∃ n : ℕ, φ x y = n) ∧
      (chainNetwork α).value φ = ((Fintype.card α - width α : ℕ) : ℝ) ∧
      (∀ ψ, (chainNetwork α).IsFlow ψ → (chainNetwork α).value ψ ≤ (chainNetwork α).value φ) ∧
      ∃ g : α → Fin (width α), ∀ i, IsChain (· ≤ ·) (g ⁻¹' {i}) := by
  obtain ⟨M, φ0, hM, hφ0, hcard, hmax, hmaxM⟩ := maxMatching_eq_maxFlow (fun x y : α => x < y)
  obtain ⟨g, hg⟩ := chain_partition_of_matching hM
  have hw1 : width α ≤ Fintype.card α - M.card := by
    simpa using width_le_card_of_chain_partition g hg
  obtain ⟨f, hf⟩ := dilworth_exists_partition (α := α)
  obtain ⟨M', hM', hM'card⟩ := exists_matching_of_chain_partition f hf
  have h1 := hmaxM M' hM'
  have h2 := card_matching_le M hM
  have hv : M.card = Fintype.card α - width α := by omega
  obtain ⟨φ, hφ, hint, hval⟩ := exists_flow_of_matching hM
  have hval' : (chainNetwork α).value φ = M.card := hval
  refine ⟨φ, hφ, hint, ?_, fun ψ hψ => ?_, ?_⟩
  · rw [hval', hv]
  · rw [hval']
    exact (hmax ψ hψ).trans_eq hcard.symm
  · exact ⟨f, hf⟩

end UndergradKB.Combinatorics.Order
