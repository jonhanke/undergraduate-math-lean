import Mathlib.Order.Antichain
import Mathlib.Order.Preorder.Chain
import Mathlib.Order.Minimal
import Mathlib.Order.Hom.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import UndergradKB.Combinatorics.Order.Basic
import UndergradKB.Combinatorics.Order.Components
import UndergradKB.Combinatorics.Order.Dilworth
import UndergradKB.Combinatorics.Order.IntervalOrder
import UndergradKB.Combinatorics.Order.Posets2
import UndergradKB.Combinatorics.Order.Posets3
import UndergradKB.Combinatorics.Order.Posets4
import UndergradKB.Combinatorics.Order.Posets5
import UndergradKB.Combinatorics.Order.FirstFit
import UndergradKB.Common.Attr

/-!
# Keller–Trotter, Chapter 6: course wrappers of results proved in this library (wave 3)
-/

namespace UndergradKB.Combinatorics.Course.KellerTrotter.Ch06b

universe u

variable {α : Type*} [PartialOrder α]

/-- CO-138. Standard posets: a family of sets under inclusion, positive integers under
divisibility, real `t`-tuples under the coordinatewise order, and the intersection of several
linear orders on one set (a partial order). -/
@[kb "kellertrotter2017" "Example 6.7, p. 141"]
theorem ex_6_7_standard_posets {β ι : Type*} [Nonempty ι] (F : Set (Set β)) {t : ℕ}
    (X : Set (Fin t → ℝ)) (r : ι → β → β → Prop) (h : ∀ i, IsLinearOrder β (r i)) :
    (∀ A B : F, A ≤ B ↔ (A : Set β) ⊆ B) ∧
    (∀ m n : Order.DvdPos, m ≤ n ↔ m.val ∣ n.val) ∧
    (∀ a b : X, a ≤ b ↔ ∀ i, (a : Fin t → ℝ) i ≤ (b : Fin t → ℝ) i) ∧
    IsPartialOrder β (fun x y => ∀ i, r i x y) :=
  ⟨Order.family_le_iff F, Order.dvdPos_le_iff, Order.tuple_le_iff X,
   Order.isPartialOrder_inter r h⟩

/-- CO-139. Two points are comparable if distinct and one is below the other, and incomparable
if neither is below the other; chains (antichains) are the sets of pairwise (in)comparable
points. -/
@[kb "kellertrotter2017" "Definition (unnumbered) comparable, p. 142"]
theorem def_6_comparable :
    (∀ x y : α, Order.Incomparable x y ↔ x ≠ y ∧ ¬ Order.Comparable x y) ∧
    (∀ s : Set α, IsChain (· ≤ ·) s ↔ s.Pairwise Order.Comparable) ∧
    (∀ s : Set α, IsAntichain (· ≤ ·) s ↔ s.Pairwise Order.Incomparable) :=
  ⟨fun _ _ => Order.incomparable_iff_not_comparable, fun _ => Order.isChain_iff_comparable,
   fun _ => Order.isAntichain_iff_incomparable⟩

/-- CO-140. The comparability (incomparability) graph of a poset joins exactly the comparable
(incomparable) pairs. -/
@[kb "kellertrotter2017" "Definition (unnumbered) comparability graph, p. 142"]
theorem def_6_comparability_graph :
    (∀ x y : α, (Order.comparabilityGraph α).Adj x y ↔ Order.Comparable x y) ∧
    (∀ x y : α, (Order.incomparabilityGraph α).Adj x y ↔ x ≠ y ∧ Order.Incomparable x y) :=
  ⟨fun _ _ => Order.comparabilityGraph_adj, fun _ _ => Order.incomparabilityGraph_adj⟩

/-- CO-144. The height of a finite poset is the largest size of a chain: no chain is larger and
some chain attains it. -/
@[kb "kellertrotter2017" "Definition (unnumbered) height, p. 143"]
theorem def_6_height [Fintype α] :
    (∀ s : Finset α, IsChain (· ≤ ·) (s : Set α) → s.card ≤ Order.height α) ∧
    ∃ s : Finset α, IsChain (· ≤ ·) (s : Set α) ∧ s.card = Order.height α :=
  ⟨fun _ h => Order.card_le_height h, Order.exists_chain_card_eq_height⟩

/-- CO-145. The width of a finite poset is the largest size of an antichain: no antichain is
larger and some antichain attains it. -/
@[kb "kellertrotter2017" "Definition (unnumbered) width, p. 143"]
theorem def_6_width [Fintype α] :
    (∀ s : Finset α, IsAntichain (· ≤ ·) (s : Set α) → s.card ≤ Order.width α) ∧
    ∃ s : Finset α, IsAntichain (· ≤ ·) (s : Set α) ∧ s.card = Order.width α :=
  ⟨fun _ h => Order.card_le_width h, Order.exists_antichain_card_eq_width⟩

/-- CO-150. Every (finite) poset is isomorphic to a poset of sets under inclusion, of positive
integers under divisibility, of real tuples under the coordinatewise order, and to an
intersection of linear orders. -/
@[kb "kellertrotter2017" "Discussion 6.12, p. 143"]
theorem disc_6_12_embeddings [Fintype α] :
    Nonempty (α ↪o Set α) ∧ Nonempty (α ↪o Finset α) ∧
    (∃ f : α → ℕ, (∀ x, 0 < f x) ∧ ∀ x y, x ≤ y ↔ f x ∣ f y) ∧
    (∃ f : α → (Fin (Fintype.card α) → ℝ), ∀ x y, x ≤ y ↔ f x ≤ f y) ∧
    (∃ (t : ℕ) (r : Fin t → α → α → Prop), Order.IsRealizer r) :=
  ⟨⟨Order.downSetEmbedding⟩, ⟨Order.finsetDownSetEmbedding⟩, Order.exists_divisibility_embedding,
   Order.exists_realTuple_embedding, Order.exists_linearOrder_intersection⟩

/-- CO-151. A finite poset has a unique maximal point exactly when it has a one (a greatest
element), and a unique minimal point exactly when it has a zero. -/
@[kb "kellertrotter2017" "Definition (unnumbered) one and zero, p. 144"]
theorem def_6_one_zero [Finite α] :
    ((∃! x : α, IsMax x) ↔ ∃ x : α, ∀ y, y ≤ x) ∧ ((∃! x : α, IsMin x) ↔ ∃ x : α, ∀ y, x ≤ y) :=
  ⟨Order.existsUnique_isMax_iff_exists_isGreatest, Order.existsUnique_isMin_iff_exists_isLeast⟩

/-- CO-152. The dual of a poset reverses the order; a poset is self-dual if isomorphic to its
dual (the dual of a self-dual poset is self-dual, the subset lattice is self-dual, and `ℕ` is
not). -/
@[kb "kellertrotter2017" "Definition (unnumbered) dual and self-dual, p. 144"]
theorem def_6_dual_self_dual :
    (∀ x y : α, OrderDual.toDual x ≤ OrderDual.toDual y ↔ y ≤ x) ∧
    (Order.IsSelfDual α → Order.IsSelfDual αᵒᵈ) ∧
    (∀ t : ℕ, Order.IsSelfDual (Finset (Fin t))) ∧ ¬ Order.IsSelfDual ℕ :=
  ⟨fun _ _ => Order.dual_le_iff, fun h => h.dual, Order.isSelfDual_finset,
   Order.not_isSelfDual_nat⟩

/-- CO-153. A poset is connected if its comparability graph is connected; components are the
supports of connected components of that graph (every point lies in exactly one, and a
singleton component is an isolated point). -/
@[kb "kellertrotter2017" "Definition (unnumbered) connected poset, p. 144"]
theorem def_6_connected_component :
    (Order.IsConnectedPoset α ↔ (Order.comparabilityGraph α).Connected) ∧
    (∀ Y : Set α, Order.IsComponent Y ↔
      ∃ C : (Order.comparabilityGraph α).ConnectedComponent, C.supp = Y) ∧
    (∀ x : α, ∃! Y : Set α, Order.IsComponent Y ∧ x ∈ Y) ∧
    (∀ {x : α}, Order.IsComponent ({x} : Set α) → IsMin x ∧ IsMax x) :=
  ⟨Iff.rfl, Order.isComponent_iff, Order.existsUnique_component,
   fun h => Order.isMin_isMax_of_isComponent_singleton h⟩

/-- CO-154. A graph is a comparability graph (cover graph) if isomorphic to the comparability
(cover) graph of some poset; the graphs of a poset are such, and a poset and its dual have the
same comparability graph. -/
@[kb "kellertrotter2017" "Definition (unnumbered) comparability graph class, p. 144"]
theorem def_6_comparability_cover_graph {P : Type u} [PartialOrder P] :
    Order.IsComparabilityGraph (Order.comparabilityGraph P) ∧
    Order.IsCoverGraph (SimpleGraph.hasse P) ∧
    Nonempty (Order.comparabilityGraph Pᵒᵈ ≃g Order.comparabilityGraph P) :=
  ⟨Order.isComparabilityGraph_comparabilityGraph, Order.isCoverGraph_hasse,
   Order.comparabilityGraph_dual⟩

/-- CO-156. Dilworth: if a finite poset has width `w`, its points split into `w` chains, and no
partition into fewer chains exists. -/
@[kb "kellertrotter2017" "Theorem 6.17, p. 146"]
theorem thm_6_17_dilworth [Fintype α] :
    (∃ f : α → Fin (Order.width α), ∀ i, IsChain (· ≤ ·) (f ⁻¹' {i})) ∧
    ∀ (n : ℕ) (g : α → Fin n), (∀ i, IsChain (· ≤ ·) (g ⁻¹' {i})) → Order.width α ≤ n :=
  Order.dilworth

/-- CO-157. Mirsky: if a finite poset has height `h`, its points split into `h` antichains, and
no partition into fewer antichains exists. -/
@[kb "kellertrotter2017" "Theorem 6.18, p. 146"]
theorem thm_6_18_mirsky [Fintype α] :
    (∃ f : α → Fin (Order.height α), ∀ i, IsAntichain (· ≤ ·) (f ⁻¹' {i})) ∧
    ∀ (n : ℕ) (g : α → Fin n), (∀ i, IsAntichain (· ≤ ·) (g ⁻¹' {i})) → Order.height α ≤ n :=
  Order.mirsky

/-- CO-159. Algorithm: repeatedly removing the set of minimal points gives levels that are
antichains, partition the poset, and are nonempty exactly for the first `height` stages. -/
@[kb "kellertrotter2017" "text (algorithm after Theorem 6.18), p. 146"]
theorem text_6_18_levels_algorithm [Fintype α] :
    (∀ k, IsAntichain (· ≤ ·) ((Order.level k : Finset α) : Set α)) ∧
    (∀ x : α, ∃! k, x ∈ (Order.level k : Finset α)) ∧
    (∀ k, (Order.level k : Finset α).Nonempty ↔ k < Order.height α) :=
  Order.levels_partition

/-- CO-160. A maximum chain (antichain) of a finite poset is maximal, but a maximal chain
(antichain) need not be maximum. -/
@[kb "kellertrotter2017" "Definition (unnumbered) maximal/maximum chain, p. 147"]
theorem def_6_maximal_maximum [Finite α] :
    (∀ s : Finset α, Order.IsMaximumChain s → IsMaxChain (· ≤ ·) (s : Set α)) ∧
    (∀ s : Finset α, Order.IsMaximumAntichain s → Maximal (IsAntichain (· ≤ ·)) (s : Set α)) ∧
    (∃ s : Finset Order.Ex160, IsMaxChain (· ≤ ·) (s : Set Order.Ex160) ∧
      ¬ Order.IsMaximumChain s) ∧
    (∃ s : Finset Order.Ex160, Maximal (IsAntichain (· ≤ ·)) (s : Set Order.Ex160) ∧
      ¬ Order.IsMaximumAntichain s) :=
  ⟨fun _ h => h.isMaxChain, fun _ h => h.maximal, Order.exists_maxChain_not_maximum,
   Order.exists_maximal_antichain_not_maximum⟩

/-- CO-162. For a maximal antichain `A`, the poset is the disjoint union of `A`, `D(A)` and
`U(A)`. -/
@[kb "kellertrotter2017" "text (unnumbered) A, D(A), U(A) partition, p. 147"]
theorem text_6_maximal_antichain_partition {A : Set α} (hA : Maximal (IsAntichain (· ≤ ·)) A) :
    A ∪ Order.downSet A ∪ Order.upSet A = Set.univ ∧ Disjoint A (Order.downSet A) ∧
      Disjoint A (Order.upSet A) ∧ Disjoint (Order.downSet A) (Order.upSet A) :=
  Order.maximal_antichain_partition hA

/-- CO-165. The subset lattice `2^t` has height `t + 1`, all maximal chains have `t + 1` points,
the ranks are antichains partitioning it with `C(t,i)` points in rank `i`, and the middle rank is
largest. -/
@[kb "kellertrotter2017" "text (unnumbered) subset lattice, p. 150"]
theorem text_6_subset_lattice (t : ℕ) :
    (∀ M : Finset (Finset (Fin t)), IsMaxChain (· ≤ ·) (M : Set (Finset (Fin t))) →
      M.card = t + 1) ∧
    Order.height (Finset (Fin t)) = t + 1 ∧ Fintype.card (Finset (Fin t)) = 2 ^ t ∧
    (∀ i, IsAntichain (· ≤ ·) (Order.rank t i : Set (Finset (Fin t)))) ∧
    (∀ s : Finset (Fin t), ∃! i, s ∈ Order.rank t i) ∧
    (∀ i, (Order.rank t i).card = Nat.choose t i) ∧
    (∀ i, (Order.rank t i).card ≤ (Order.rank t (t / 2)).card) ∧
    (t % 2 = 1 → (Order.rank t (t / 2)).card = (Order.rank t (t / 2 + 1)).card) :=
  ⟨fun _ hM => Order.card_of_isMaxChain t hM, Order.height_finset t, Order.card_subsets t,
   Order.isAntichain_rank t, Order.rank_partition t, Order.card_rank t, Order.card_rank_le_middle t,
   fun h => Order.card_rank_middle_odd t h⟩

/-- CO-166. Sperner: the width of the subset lattice of a finite set `β` is
`C(|β|, ⌊|β|/2⌋)`. -/
@[kb "kellertrotter2017" "Theorem 6.27, p. 151"]
theorem thm_6_27_sperner (β : Type*) [DecidableEq β] [Fintype β] :
    Order.width (Finset β) = (Fintype.card β).choose (Fintype.card β / 2) :=
  Order.width_finset β

/-- CO-167. A poset is an interval order if each point `x` gets a closed interval `[a x, b x]`
so that `x < y` iff the interval of `x` lies entirely to the left of that of `y`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) interval order, p. 152"]
theorem def_6_interval_order :
    Order.IsIntervalOrder α ↔ ∃ a b : α → ℝ, (∀ x, a x ≤ b x) ∧ ∀ x y, x < y ↔ b x < a y :=
  Iff.rfl

/-- CO-168. Every finite interval order has a distinguishing representation: all intervals
non-degenerate and all endpoints distinct. -/
@[kb "kellertrotter2017" "text (distinguishing representation), p. 152"]
theorem text_6_distinguishing_representation [Fintype α] (h : Order.IsIntervalOrder α) :
    ∃ a b : α → ℝ, (∀ x, a x < b x) ∧ Function.Injective a ∧ Function.Injective b ∧
      (∀ x y, a x ≠ b y) ∧ ∀ x y, x < y ↔ b x < a y :=
  Order.IsIntervalOrder.exists_distinguishing h

/-- CO-169. The disjoint sum `2 + 2` of two 2-point chains embeds in a poset iff the poset has
four points `a < b`, `c < d` with no comparabilities between `{a,b}` and `{c,d}`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) P + Q, 2 + 2, p. 152"]
theorem def_6_two_plus_two :
    Order.ContainsPoset α (Fin 2 ⊕ Fin 2) ↔ ∃ a b c d : α, Order.TwoPlusTwo a b c d :=
  Order.containsPoset_two_plus_two_iff

/-- CO-170. A finite poset is an interval order iff it excludes `2 + 2`. -/
@[kb "kellertrotter2017" "Theorem 6.29, p. 153"]
theorem thm_6_29_interval_order_iff [Fintype α] :
    Order.IsIntervalOrder α ↔ ¬ Order.ContainsPoset α (Fin 2 ⊕ Fin 2) :=
  Order.isIntervalOrder_iff_excludes_two_plus_two

/-- CO-171. Algorithm: if two strict down sets are incomparable under inclusion, a copy of
`2 + 2` is produced; otherwise the down sets (and the up sets) form chains under inclusion. -/
@[kb "kellertrotter2017" "text, p. 153"]
theorem text_6_29_down_sets_algorithm [Fintype α] :
    (∀ {x y : α}, ¬ Order.dnFin x ⊆ Order.dnFin y → ¬ Order.dnFin y ⊆ Order.dnFin x →
      ∃ z w : α, z ∈ Order.dnFin x ∧ z ∉ Order.dnFin y ∧ w ∈ Order.dnFin y ∧
        w ∉ Order.dnFin x ∧ Order.TwoPlusTwo z x w y) ∧
    ((∀ x y : α, Order.dnFin x ⊆ Order.dnFin y ∨ Order.dnFin y ⊆ Order.dnFin x) ∨
      Order.ContainsPoset α (Fin 2 ⊕ Fin 2)) ∧
    (¬ Order.ContainsPoset α (Fin 2 ⊕ Fin 2) →
      (∀ x y : α, Order.dnFin x ⊆ Order.dnFin y ∨ Order.dnFin y ⊆ Order.dnFin x) ∧
      ∀ x y : α, Order.upFin x ⊆ Order.upFin y ∨ Order.upFin y ⊆ Order.upFin x) :=
  ⟨fun h1 h2 => Order.two_plus_two_of_incomparable_dnFins h1 h2,
   Order.dnFins_chain_or_two_plus_two,
   fun hne => ⟨Order.dnFin_chain hne, Order.upFin_chain hne⟩⟩

/-- CO-172. For a finite poset excluding `2 + 2`: the numbers of distinct down sets and up sets
agree, the intervals `[downIndex x, upIndex x]` are well formed and represent the order, they
form an integer representation with endpoints in `[|𝔇|]`, no integer representation uses fewer
points, and that one is unique. -/
@[kb "kellertrotter2017" "Theorem 6.30, p. 154"]
theorem thm_6_30_integer_representation [Fintype α]
    (hne : ¬ Order.ContainsPoset α (Fin 2 ⊕ Fin 2)) :
    (Order.dnFins α).card = (Order.upFins α).card ∧
    (∀ x : α, Order.downIndex x ≤ Order.upIndex x) ∧
    (∀ x y : α, x < y ↔ Order.upIndex x < Order.downIndex y) ∧
    Order.IsIntRep (Order.dnFins α).card (Order.downIndex (α := α)) (Order.upIndex (α := α)) ∧
    (∀ {n : ℕ} {a b : α → ℕ}, Order.IsIntRep n a b → (Order.dnFins α).card ≤ n) ∧
    (∀ {a b : α → ℕ}, Order.IsIntRep (Order.dnFins α).card a b →
      a = Order.downIndex ∧ b = Order.upIndex) :=
  ⟨Order.card_dnFins_eq_card_upFins hne, Order.downIndex_le_upIndex hne,
   Order.lt_iff_upIndex_lt_downIndex hne, Order.isIntRep_downIndex_upIndex hne,
   fun h => Order.dnFins_card_le_of_isIntRep h, fun h => Order.isIntRep_unique h⟩

/-- CO-173. For an interval order, First Fit along the left-endpoint order gives a partition
into `width` chains (an optimal chain partition). -/
@[kb "kellertrotter2017" "text (interval orders and First Fit), p. 155"]
theorem text_6_first_fit_interval_order [Fintype α] (h : Order.IsIntervalOrder α) :
    ∃ σ : α → ℕ, Function.Injective σ ∧
      ∃ g : α → Fin (Order.width α), (∀ i, IsChain (· ≤ ·) (g ⁻¹' {i})) ∧
        ∀ x, (g x : ℕ) = Order.firstFit σ x :=
  Order.IsIntervalOrder.firstFit_optimal h

/-- CO-174. First Fit: processing points in a fixed linear order and putting each in the first
chain where it is comparable with all points already there gives a partition into chains. -/
@[kb "kellertrotter2017" "text (First Fit), p. 156"]
theorem text_6_first_fit_algorithm [Fintype α] {σ : α → ℕ} (hσ : Function.Injective σ) :
    (∀ i : ℕ, IsChain (· ≤ ·) (Order.firstFit σ ⁻¹' {i})) ∧
    ∃ (n : ℕ) (g : α → Fin n), (∀ i, IsChain (· ≤ ·) (g ⁻¹' {i})) ∧
      ∀ x, (g x : ℕ) = Order.firstFit σ x :=
  ⟨fun i => Order.firstFit_isChain hσ i, Order.firstFit_chain_partition hσ⟩

/-- CO-175. First Fit can be forced to use many antichains on a height-2 poset (the two-level
poset has no 3-chain, yet its First Fit labels go up to `t`) and many chains on a width-2 poset. -/
@[kb "kellertrotter2017" "Example 6.32, p. 156"]
theorem ex_6_32_first_fit_bad (t : ℕ) :
    (¬ ∃ a b c : Order.TwoLevel t, a < b ∧ b < c) ∧
    (∀ a : Order.TwoLevel t, Order.firstFitAnti (Order.TwoLevel.pos (t := t)) a = a.idx) ∧
    (¬ ∃ x y z : Order.WidthTwo t, (¬ x ≤ y ∧ ¬ y ≤ x) ∧ (¬ x ≤ z ∧ ¬ z ≤ x) ∧
      (¬ y ≤ z ∧ ¬ z ≤ y)) ∧
    (∀ x : Order.WidthTwo t, Order.firstFit (Order.WidthTwo.pos t) x = x.1.2) :=
  ⟨Order.twoLevel_no_three_chain, Order.firstFitAnti_twoLevel t,
   Order.widthTwo_no_three_antichain, Order.firstFit_widthTwo t⟩

/-- CO-176. The dimension of a finite poset is the least number of linear orders whose
intersection is the poset: such a family exists, and none with fewer members does. -/
@[kb "kellertrotter2017" "Exercise 6.21, p. 163"]
theorem ex_6_21_dimension [Finite α] :
    (∃ r : Fin (Order.dimension α) → α → α → Prop, Order.IsRealizer r) ∧
    ∀ (t : ℕ) (r : Fin t → α → α → Prop), Order.IsRealizer r → Order.dimension α ≤ t :=
  Order.dimension_spec

end UndergradKB.Combinatorics.Course.KellerTrotter.Ch06b
