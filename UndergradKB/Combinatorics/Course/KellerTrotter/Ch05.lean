import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Clique
import UndergradKB.Common.Attr

/-!
# Keller–Trotter, Chapter 5 (Graph Theory): thin course wrappers
-/

namespace UndergradKB.Combinatorics.Course.KellerTrotter

open Finset

section
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- CO-094. The degrees of a graph sum to twice the number of edges. -/
@[kb "kellertrotter2017" "Theorem 5.9, p. 98"]
theorem thm_5_9 : ∑ v, G.degree v = 2 * #G.edgeFinset :=
  G.sum_degrees_eq_twice_card_edges

/-- CO-095. The number of vertices of odd degree is even. -/
@[kb "kellertrotter2017" "Corollary 5.10, p. 98"]
theorem cor_5_10 : Even #{v | Odd (G.degree v)} :=
  G.even_card_odd_degree_vertices

/-- CO-096. A tree on at least two vertices has two distinct leaves (vertices of degree 1). -/
@[kb "kellertrotter2017" "Proposition 5.11, p. 98"]
theorem prop_5_11 [Nontrivial V] (hG : G.IsTree) :
    ∃ u v, u ≠ v ∧ G.degree u = 1 ∧ G.degree v = 1 :=
  hG.exists_ne_and_degree_eq_one

omit [Fintype V] [DecidableRel G.Adj] in
/-- CO-108. `χ(G) ≥ ω(G)`: the chromatic number is at least the clique number. -/
@[kb "kellertrotter2017" "text (chi at least omega), p. 107"]
theorem text_p107_chi_ge_omega : G.cliqueNum ≤ G.chromaticNumber :=
  G.cliqueNum_le_chromaticNumber

omit [DecidableRel G.Adj] in
/-- CO-123. A tree on `n` vertices has `n - 1` edges. -/
@[kb "kellertrotter2017" "Exercise 5.9.6, p. 126"]
theorem ex_5_9_6 [Fintype G.edgeSet] (hG : G.IsTree) :
    #G.edgeFinset + 1 = Fintype.card V :=
  hG.card_edgeFinset

end

/-- CO-125. A tree on at least two vertices has chromatic number exactly 2. -/
@[kb "kellertrotter2017" "Exercise 5.9.17, p. 130"]
theorem ex_5_9_17 {V : Type*} [Nontrivial V] {G : SimpleGraph V} (hG : G.IsTree) :
    G.chromaticNumber = 2 := by
  obtain ⟨u, v, huv⟩ := exists_pair_ne V
  obtain ⟨p⟩ := hG.connected.preconnected u v
  have hadj : ∃ a b, G.Adj a b := by
    cases p with
    | nil => exact absurd rfl huv
    | cons h _ => exact ⟨_, _, h⟩
  obtain ⟨a, b, hab⟩ := hadj
  exact le_antisymm hG.chromaticNumber_le_two (SimpleGraph.two_le_chromaticNumber_of_adj hab)

/-- CO-078. Generalized pigeonhole: if `|X| ≥ (m-1)|Y| + 1` and `f : X → Y`, some `y` has at
least `m` preimages. -/
@[kb "kellertrotter2017" "Proposition 5.24, p. 109"]
theorem prop_5_24 {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y] (f : X → Y) (m : ℕ)
    (h : (m - 1) * Fintype.card Y + 1 ≤ Fintype.card X) :
    ∃ y : Y, m ≤ #{x | f x = y} := by
  obtain ⟨y, hy⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card f
    (n := m - 1) (by rw [mul_comm]; omega)
  exact ⟨y, by omega⟩

/-! ### Definitions of Section 5.1--5.4 in the book's terms -/

section Definitions

variable {V : Type*} (G : SimpleGraph V)

/-- CO-084. Neighbors: `w` is a neighbor of `v` exactly when `vw` is an edge of the graph. -/
@[kb "kellertrotter2017" "Definition (unnumbered) neighbors, p. 94"]
theorem def_p94_neighborSet (v w : V) : w ∈ G.neighborSet v ↔ s(v, w) ∈ G.edgeSet :=
  by rw [SimpleGraph.mem_neighborSet, SimpleGraph.mem_edgeSet]

/-- CO-085. The degree of a vertex is the number of its neighbors, which is also the number of
edges incident with it. -/
@[kb "kellertrotter2017" "Definition (unnumbered) degree, p. 94"]
theorem def_p94_degree [Fintype V] [DecidableRel G.Adj] (v : V) :
    G.degree v = #(G.neighborFinset v) ∧ G.degree v = #(G.incidenceFinset v) :=
  ⟨(G.card_neighborFinset_eq_degree v).symm, (G.card_incidenceFinset_eq_degree v).symm⟩

/-- CO-086. A subgraph is spanning when it has all vertices. -/
@[kb "kellertrotter2017" "Definition (unnumbered) spanning, p. 94"]
theorem def_p94_spanning (H : G.Subgraph) : H.IsSpanning ↔ H.verts = Set.univ :=
  SimpleGraph.Subgraph.isSpanning_iff

/-- CO-086. The induced subgraph on `W` has, as its edges, all edges of `G` inside `W`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) induced, p. 94"]
theorem def_p94_induced (W : Set V) (u v : W) : (G.induce W).Adj u v ↔ G.Adj u v :=
  SimpleGraph.induce_adj

/-- CO-087. In the complete graph any two distinct vertices are adjacent; the independent
(edgeless) graph has no adjacent pair. -/
@[kb "kellertrotter2017" "Definition (unnumbered) complete graph, p. 94"]
theorem def_p94_complete (u v : V) :
    (⊤ : SimpleGraph V).Adj u v ↔ u ≠ v :=
  SimpleGraph.top_adj u v

/-- CO-087. The independent graph has no edges. -/
@[kb "kellertrotter2017" "Definition (unnumbered) independent graph, p. 94"]
theorem def_p94_independent (u v : V) : ¬ (⊥ : SimpleGraph V).Adj u v :=
  fun h => h

/-- CO-088. A path is a walk with distinct vertices. -/
@[kb "kellertrotter2017" "Definition (unnumbered) path, p. 95"]
theorem def_p95_path {u v : V} (p : G.Walk u v) : p.IsPath ↔ p.support.Nodup :=
  SimpleGraph.Walk.isPath_def p

/-- CO-088. A cycle is a closed walk, not trivial, using no edge twice and no vertex twice (apart
from the start). -/
@[kb "kellertrotter2017" "Definition (unnumbered) cycle, p. 95"]
theorem def_p95_cycle [DecidableEq V] {u : V} (p : G.Walk u u) :
    p.IsCycle ↔ p.IsTrail ∧ p ≠ SimpleGraph.Walk.nil ∧ p.support.tail.Nodup :=
  SimpleGraph.Walk.isCycle_def p

/-- CO-088. In the path graph `P_n` consecutive vertices are adjacent and nothing else. -/
@[kb "kellertrotter2017" "Definition (unnumbered) P_n, p. 95"]
theorem def_p95_pathGraph (n : ℕ) (u v : Fin n) :
    (SimpleGraph.pathGraph n).Adj u v ↔ u.val + 1 = v.val ∨ v.val + 1 = u.val :=
  SimpleGraph.pathGraph_adj

/-- CO-088. In the cycle graph `C_{n+2}` two vertices are adjacent when they differ by one
modulo `n + 2`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) C_n, p. 95"]
theorem def_p95_cycleGraph (n : ℕ) (u v : Fin (n + 2)) :
    (SimpleGraph.cycleGraph (n + 2)).Adj u v ↔ u - v = 1 ∨ v - u = 1 :=
  SimpleGraph.cycleGraph_adj

/-- CO-089. An isomorphism of graphs is an adjacency-preserving (and reflecting) bijection of the
vertex sets. -/
@[kb "kellertrotter2017" "Definition (unnumbered) isomorphic, p. 96"]
theorem def_p96_isomorphism {W : Type*} {H : SimpleGraph W} (f : G ≃g H) :
    Function.Bijective f ∧ ∀ v w, H.Adj (f v) (f w) ↔ G.Adj v w :=
  ⟨f.toEquiv.bijective, fun _ _ => f.map_adj_iff⟩

/-- CO-089. `G` contains `H` when some subgraph of `G` is isomorphic to `H`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) contains, p. 96"]
theorem def_p96_contains {W : Type*} (H : SimpleGraph W) :
    SimpleGraph.IsContained H G ↔ ∃ G' : G.Subgraph, Nonempty (H ≃g G'.coe) :=
  SimpleGraph.isContained_iff_exists_iso_subgraph

/-- CO-090. A graph is connected when it is nonempty and any two vertices are joined by a path. -/
@[kb "kellertrotter2017" "Definition (unnumbered) connected, p. 97"]
theorem def_p97_connected :
    G.Connected ↔ Nonempty V ∧ ∀ u v : V, ∃ p : G.Walk u v, p.IsPath := by
  rw [SimpleGraph.connected_iff]
  refine ⟨fun ⟨h, hne⟩ => ⟨hne, fun u v => (h u v).exists_isPath⟩,
    fun ⟨hne, h⟩ => ⟨fun u v => ?_, hne⟩⟩
  obtain ⟨p, -⟩ := h u v
  exact ⟨p⟩

/-- CO-090. Two vertices lie in the same component exactly when they are joined by a path. -/
@[kb "kellertrotter2017" "Definition (unnumbered) component, p. 97"]
theorem def_p97_component (u v : V) :
    G.connectedComponentMk u = G.connectedComponentMk v ↔ ∃ p : G.Walk u v, p.IsPath := by
  rw [SimpleGraph.ConnectedComponent.eq]
  exact ⟨fun h => h.exists_isPath, fun ⟨p, _⟩ => ⟨p⟩⟩

/-- CO-091. A tree is a connected acyclic graph. -/
@[kb "kellertrotter2017" "Definition (unnumbered) tree, p. 97"]
theorem def_p97_tree : G.IsTree ↔ G.Connected ∧ G.IsAcyclic :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- CO-091. Every connected graph has a spanning tree (a tree `T ≤ G` on the same vertex set). -/
@[kb "kellertrotter2017" "Definition (unnumbered) spanning tree, p. 97"]
theorem def_p97_spanningTree (h : G.Connected) : ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree :=
  h.exists_isTree_le

/-- CO-097. A walk is eulerian when it is a trail containing every edge of the graph. -/
@[kb "kellertrotter2017" "Definition (unnumbered) eulerian, p. 99"]
theorem def_p99_eulerian [DecidableEq V] {u v : V} (p : G.Walk u v) :
    p.IsEulerian ↔ p.IsTrail ∧ ∀ e, e ∈ G.edgeSet → e ∈ p.edges :=
  SimpleGraph.Walk.isEulerian_iff p

/-- CO-100. A hamiltonian cycle is a cycle through every vertex. -/
@[kb "kellertrotter2017" "Definition (unnumbered) hamiltonian cycle, p. 103"]
theorem def_p103_hamiltonianCycle [DecidableEq V] {u : V} (p : G.Walk u u) :
    p.IsHamiltonianCycle ↔ p.IsCycle ∧ ∀ v, v ∈ p.support :=
  SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_forall_mem_support

/-- CO-103. In a proper coloring adjacent vertices get different colors; `χ(G) ≤ n` exactly when
`G` has a proper coloring with `n` colors. -/
@[kb "kellertrotter2017" "Definition (unnumbered) proper coloring, p. 105"]
theorem def_p105_proper_coloring {α : Type*} (C : G.Coloring α) (u v : V) (h : G.Adj u v) :
    C u ≠ C v :=
  C.valid h

/-- CO-103. The chromatic number is at most `n` iff the graph is `n`-colorable. -/
@[kb "kellertrotter2017" "Definition (unnumbered) chromatic number, p. 105"]
theorem def_p105_chromaticNumber (n : ℕ) : G.chromaticNumber ≤ n ↔ G.Colorable n :=
  SimpleGraph.chromaticNumber_le_iff_colorable

/-- CO-104. A graph is 2-colorable (`χ ≤ 2`) exactly when it is bipartite. -/
@[kb "kellertrotter2017" "Definition (unnumbered) bipartite graph, p. 107"]
theorem def_p107_bipartite : G.chromaticNumber ≤ 2 ↔ G.IsBipartite :=
  SimpleGraph.chromaticNumber_le_two_iff_isBipartite

/-- CO-106. In the complete bipartite graph `K_{m,n}` exactly the pairs with one end in each part
are adjacent. -/
@[kb "kellertrotter2017" "Definition (unnumbered) complete bipartite, p. 107"]
theorem def_p107_completeBipartite {W : Type*} (a b : V ⊕ W) :
    (completeBipartiteGraph V W).Adj a b ↔
      (a.isLeft ∧ b.isRight) ∨ (a.isRight ∧ b.isLeft) :=
  Iff.rfl

/-- CO-107. A clique is a set of pairwise adjacent vertices, and no clique is larger than the
clique number `ω(G)`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) clique number, p. 107"]
theorem def_p107_clique [Finite V] (t : Finset V) (ht : G.IsClique (t : Set V)) :
    (t.card : ℕ∞) ≤ G.cliqueNum :=
  by exact_mod_cast ht.card_le_cliqueNum

end Definitions

end UndergradKB.Combinatorics.Course.KellerTrotter
