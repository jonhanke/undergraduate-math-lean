import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import UndergradKB.Common.Attr

/-!
# Spanning trees: weights, the exchange principle, and Lemma 12.6 (Keller–Trotter, Chapter 12)

A spanning tree of `G : SimpleGraph V` is a graph `T ≤ G` on the same vertex type which is a tree
(`SimpleGraph.IsTree`).  Weights are a function `w : Sym2 V → ℝ` on edges.
-/

namespace UndergradKB.Combinatorics.SpanningTree

open SimpleGraph

open scoped Classical

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V]

/-! ### Weighted graphs and spanning trees -/

/-- CO-269. The weight `w(S)` of a set of edges is the sum of the weights of its members. -/
@[kb "kellertrotter2017" "Definition (unnumbered) weight of an edge set, p. 263"]
noncomputable def edgeSetWeight (w : Sym2 V → ℝ) (S : Finset (Sym2 V)) : ℝ := ∑ e ∈ S, w e

/-- CO-269. The weight of a subgraph is the weight of its edge set. -/
@[kb "kellertrotter2017" "Definition (unnumbered) weight of an edge set, p. 263"]
noncomputable def weight (w : Sym2 V → ℝ) (H : SimpleGraph V) : ℝ := edgeSetWeight w H.edgeFinset

/-- CO-269. A weighted graph `(G, w)`: `G` is connected and the weights on its edges are
nonnegative. -/
@[kb "kellertrotter2017" "Definition (unnumbered) weighted graph, p. 263"]
def IsWeighted (G : SimpleGraph V) (w : Sym2 V → ℝ) : Prop :=
  G.Connected ∧ ∀ e ∈ G.edgeSet, 0 ≤ w e

/-- CO-083. A minimum weight spanning tree of `G`: a spanning tree `T ≤ G` whose weight is at
most that of every spanning tree of `G`. -/
@[kb "kellertrotter2017" "Problem 12.2, p. 264"]
def IsMinSpanningTree (G : SimpleGraph V) (w : Sym2 V → ℝ) (T : SimpleGraph V) : Prop :=
  T.IsTree ∧ T ≤ G ∧ ∀ T' : SimpleGraph V, T'.IsTree → T' ≤ G → weight w T ≤ weight w T'

/-- A spanning tree of minimum weight among the spanning trees of `G` containing a given forest
`F` (the notion used in Lemma 12.6). -/
def IsMinSpanningTreeContaining (G : SimpleGraph V) (w : Sym2 V → ℝ) (F T : SimpleGraph V) :
    Prop :=
  T.IsTree ∧ F ≤ T ∧ T ≤ G ∧
    ∀ T' : SimpleGraph V, T'.IsTree → F ≤ T' → T' ≤ G → weight w T ≤ weight w T'

/-- CO-083. Existence of a spanning tree of a connected graph (Mathlib). -/
@[kb "kellertrotter2017" "Exercise 1.19 (spanning tree), p. 38"]
theorem exists_spanning_tree {G : SimpleGraph V} (h : G.Connected) : ∃ T ≤ G, T.IsTree :=
  h.exists_isTree_le

/-- CO-083. A connected weighted graph has a minimum weight spanning tree. -/
@[kb "kellertrotter2017" "Problem 12.2, p. 264"]
theorem exists_isMinSpanningTree {G : SimpleGraph V} (w : Sym2 V → ℝ) (h : G.Connected) :
    ∃ T, IsMinSpanningTree G w T := by
  obtain ⟨T0, hT0, hT0t⟩ := h.exists_isTree_le
  have hne : (Finset.univ.filter fun T : SimpleGraph V => T.IsTree ∧ T ≤ G).Nonempty :=
    ⟨T0, by simp [hT0t, hT0]⟩
  obtain ⟨T, hT, hmin⟩ := Finset.exists_min_image _ (weight w) hne
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT hmin
  exact ⟨T, hT.1, hT.2, fun T' h1 h2 => hmin T' ⟨h1, h2⟩⟩

/-! ### Proposition 12.3: forests -/

/-- CO-131. Proposition 12.3. A spanning forest (acyclic graph) `H` on `n` vertices has at most
`n - 1` edges, and if it has `n - k` edges it has `k` components. -/
@[kb "kellertrotter2017" "Proposition 12.3, p. 264"]
theorem forest_edges_le_and_components [Finite V] [Nonempty V] (H : SimpleGraph V)
    (hH : H.IsAcyclic) :
    H.edgeSet.ncard + 1 ≤ Nat.card V ∧
      ∀ k : ℕ, H.edgeSet.ncard + k = Nat.card V → Nat.card H.ConnectedComponent = k := by
  refine ⟨hH.ncard_edgeSet_add_one_le_card, fun k hk => ?_⟩
  have := hH.ncard_edgeSet_add_card_connectedComponent
  omega

/-- CO-131. Proposition 12.3, last clause: a spanning forest is a spanning tree iff it has exactly
`n - 1` edges. -/
@[kb "kellertrotter2017" "Proposition 12.3, p. 264"]
theorem forest_isTree_iff [Finite V] (H : SimpleGraph V) (hH : H.IsAcyclic) :
    H.IsTree ↔ H.edgeSet.ncard + 1 = Nat.card V :=
  ⟨fun h => h.ncard_edgeSet_add_one, fun h =>
    isTree_iff_isAcyclic_and_ncard_edgeSet_add_one_eq_card.2 ⟨hH, h⟩⟩

/-! ### Proposition 12.4: the exchange principle -/

/-- The graph obtained from `T` by adding the edge `e` and deleting the edge `f`. -/
def exchange (T : SimpleGraph V) (e f : Sym2 V) : SimpleGraph V :=
  fromEdgeSet (insert e (T.edgeSet \ {f}))

lemma exchange_adj {T : SimpleGraph V} {e f : Sym2 V} {a b : V} :
    (exchange T e f).Adj a b ↔ (s(a, b) = e ∨ (T.Adj a b ∧ s(a, b) ≠ f)) ∧ a ≠ b := by
  simp [exchange, fromEdgeSet_adj]

lemma exchange_edgeSet {T : SimpleGraph V} {e f : Sym2 V} (he : ¬ e.IsDiag) :
    (exchange T e f).edgeSet = insert e (T.edgeSet \ {f}) := by
  ext g
  induction g using Sym2.ind with
  | _ a b =>
    simp only [mem_edgeSet, exchange_adj, Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h | h, _⟩
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact ⟨Or.inl h, by rintro rfl; exact he (by simp [← h])⟩
      · exact ⟨Or.inr h, h.1.ne⟩

lemma weight_exchange (w : Sym2 V → ℝ) {T : SimpleGraph V} {e f : Sym2 V} (he : ¬ e.IsDiag)
    (heT : e ∉ T.edgeSet) (hf : f ∈ T.edgeSet) :
    weight w (exchange T e f) = weight w T - w f + w e := by
  have hE : (exchange T e f).edgeFinset = insert e (T.edgeFinset.erase f) := by
    ext g
    simp only [mem_edgeFinset, exchange_edgeSet he, Set.mem_insert_iff, Set.mem_sdiff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_erase]
    tauto
  have hen : e ∉ T.edgeFinset.erase f := by simp [heT]
  have hfm : f ∈ T.edgeFinset := by simpa using hf
  unfold weight edgeSetWeight
  rw [hE, Finset.sum_insert hen, Finset.sum_erase_eq_sub hfm]
  ring

/-- If `T` has all edges other than `f` inside `H`, and the endpoints `x`, `y` of a path in `T`
through `f = uv` are `H`-reachable, then `u` and `v` are `H`-reachable. -/
lemma reachable_of_mem_edges_path {T H : SimpleGraph V} {f : Sym2 V} {u v : V}
    (hf : f = s(u, v)) (hH : ∀ a b, T.Adj a b → s(a, b) ≠ f → H.Adj a b)
    {x y : V} (p : T.Walk x y) (hp : p.IsPath) (hfp : f ∈ p.edges) :
    (H.Reachable x u ∧ H.Reachable v y) ∨ (H.Reachable x v ∧ H.Reachable u y) := by
  have avoid : ∀ {c b : V} (q : T.Walk c b), f ∉ q.edges → H.Reachable c b := by
    intro c b q
    induction q with
    | nil => intro _; exact Reachable.refl _
    | cons h q ih =>
      intro hq
      rw [Walk.edges_cons, List.mem_cons, not_or] at hq
      exact (Adj.reachable (hH _ _ h (Ne.symm hq.1))).trans (ih hq.2)
  induction p with
  | nil => simp at hfp
  | @cons a c b h q ih =>
    rw [Walk.cons_isPath_iff] at hp
    rw [Walk.edges_cons, List.mem_cons] at hfp
    have hnd := (Walk.cons h q |>.isPath_def |>.1 (by rw [Walk.cons_isPath_iff]; exact hp))
    have hnodup : (Walk.cons h q).edges.Nodup :=
      Walk.edges_nodup_of_support_nodup hnd
    rw [Walk.edges_cons, List.nodup_cons] at hnodup
    rcases hfp with hfe | hfq
    · have hq : f ∉ q.edges := hfe ▸ hnodup.1
      have hqr := avoid q hq
      rw [hfe] at hf
      rcases Sym2.eq_iff.1 hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨Reachable.refl _, hqr⟩
      · exact Or.inr ⟨Reachable.refl _, hqr⟩
    · have hne : s(a, c) ≠ f := fun h' => hnodup.1 (h' ▸ hfq)
      have har := Adj.reachable (hH _ _ h hne)
      rcases ih hp.1 hfq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨har.trans h1, h2⟩
      · exact Or.inr ⟨har.trans h1, h2⟩

/-- CO-271. Proposition 12.4 (Exchange Principle), part 2, for a path `p` in the tree `T` from `x`
to `y`: if `xy` is an edge of `G` not in `T`, and `f` is any edge on the path, then replacing `f`
by `xy` gives a spanning tree. -/
@[kb "kellertrotter2017" "Proposition 12.4, p. 265"]
theorem exchange_isTree {T : SimpleGraph V} (hT : T.IsTree) {x y : V} (hxy : x ≠ y)
    (hxyT : ¬ T.Adj x y) (p : T.Walk x y) (hp : p.IsPath) {f : Sym2 V} (hfp : f ∈ p.edges) :
    (exchange T s(x, y) f).IsTree := by
  have hfT : f ∈ T.edgeSet := p.edges_subset_edgeSet hfp
  have hdiag : ¬ (s(x, y)).IsDiag := by simpa using hxy
  have hxyT' : s(x, y) ∉ T.edgeSet := by simpa using hxyT
  induction f using Sym2.ind with
  | _ u v =>
  have hH : ∀ a b, T.Adj a b → s(a, b) ≠ s(u, v) → (exchange T s(x, y) s(u, v)).Adj a b := by
    intro a b hab hne
    exact exchange_adj.2 ⟨Or.inr ⟨hab, hne⟩, hab.ne⟩
  have hxyH : (exchange T s(x, y) s(u, v)).Reachable x y :=
    Adj.reachable (exchange_adj.2 ⟨Or.inl rfl, hxy⟩)
  have huv : (exchange T s(x, y) s(u, v)).Reachable u v := by
    rcases reachable_of_mem_edges_path rfl hH p hp hfp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h1.symm.trans (hxyH.trans h2.symm)
    · exact h2.trans (hxyH.symm.trans h1)
  have hall : ∀ a b, T.Adj a b → (exchange T s(x, y) s(u, v)).Reachable a b := by
    intro a b hab
    by_cases hne : s(a, b) = s(u, v)
    · rcases Sym2.eq_iff.1 hne with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact huv
      · exact huv.symm
    · exact Adj.reachable (hH a b hab hne)
  have hconn : (exchange T s(x, y) s(u, v)).Connected := by
    have hnon := hT.connected.nonempty
    refine ⟨fun a b => ?_⟩
    obtain ⟨q⟩ := hT.connected.preconnected a b
    clear hp hfp
    induction q with
    | nil => exact Reachable.refl _
    | cons h q ih => exact (hall _ _ h).trans ih
  rw [isTree_iff_connected_and_card]
  refine ⟨hconn, ?_⟩
  have hcard := hT.ncard_edgeSet_add_one
  rw [Nat.card_coe_set_eq, exchange_edgeSet hdiag]
  rw [Set.ncard_insert_of_notMem (by simp [hxyT']) (T.edgeSet.toFinite.sdiff),
    ← hcard]
  have := Set.ncard_sdiff_singleton_add_one hfT T.edgeSet.toFinite
  omega

/-- CO-271. Proposition 12.4 (Exchange Principle), part 1: in a tree there is a unique path from
`x` to `y`. -/
@[kb "kellertrotter2017" "Proposition 12.4, p. 265"]
theorem tree_existsUnique_path {T : SimpleGraph V} (hT : T.IsTree) (x y : V) :
    ∃! p : T.Walk x y, p.IsPath :=
  hT.existsUnique_path x y

end UndergradKB.Combinatorics.SpanningTree
