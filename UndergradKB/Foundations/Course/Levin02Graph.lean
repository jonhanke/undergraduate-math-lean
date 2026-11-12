import Mathlib.Combinatorics.Graph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Hall
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Trails
import UndergradKB.Common

/-!
# Course layer: Levin, Chapter 2 (graph theory)

Thin statements in the book's terms for the graph rows classified `in Mathlib` that only Levin
treats (the rows shared with Hammack are in `Hammack10Graph`).
-/

namespace UndergradKB.Foundations.Course

open SimpleGraph

variable {V W : Type*}

/-- FO-311. In a multigraph a link from a vertex to itself is a loop. -/
@[kb "levin2025" "Glossary §2.1, p. 130", kb "levin2025" "Intro §2.1, p. 120"]
theorem levin_s2_1_multigraph_loop {α β : Type*} (G : Graph α β) (e : β) (x : α) :
    G.IsLink e x x ↔ G.IsLoopAt e x :=
  Graph.isLink_self_iff

/-- FO-312. An isomorphism of simple graphs preserves adjacency in both directions. -/
@[kb "levin2025" "Def 2.1.5, p. 124"]
theorem levin_def_2_1_5_iso_adj {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H) (u v : V) :
    G.Adj u v ↔ H.Adj (f u) (f v) :=
  f.map_adj_iff.symm

/-- FO-313. In the induced subgraph on `s`, two vertices are adjacent iff they are in `G`. -/
@[kb "levin2025" "Def 2.1.7, p. 126"]
theorem levin_def_2_1_7_induce_adj (G : SimpleGraph V) (s : Set V) (u v : s) :
    (G.induce s).Adj u v ↔ G.Adj u v :=
  Iff.rfl

/-- FO-315. In the complete graph, two vertices are adjacent iff they are distinct. -/
@[kb "levin2025" "Text §2.1, p. 127"]
theorem levin_s2_1_complete_adj (u v : V) : (completeGraph V).Adj u v ↔ u ≠ v :=
  SimpleGraph.top_adj u v

/-- FO-316. The complete graph on `n` vertices has `n(n-1)/2 = C(n,2)` edges. -/
@[kb "levin2025" "Text §2.1, p. 128"]
theorem levin_s2_1_complete_edges [Fintype V] [DecidableEq V] :
    (⊤ : SimpleGraph V).edgeFinset.card = (Fintype.card V).choose 2 :=
  SimpleGraph.card_edgeFinset_top_eq_card_choose_two

/-- FO-317. The degree of a vertex is the number of edges incident to it. -/
@[kb "levin2025" "Text §2.1, p. 128"]
theorem levin_s2_1_degree_incident_edges [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) : G.degree v = (G.incidenceFinset v).card :=
  (SimpleGraph.card_incidenceFinset_eq_degree G v).symm

/-- FO-319. Handshake lemma: the sum of the degrees is twice the number of edges. -/
@[kb "levin2025" "Lemma 2.1.9, p. 128"]
theorem levin_lem_2_1_9_handshake [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ v, G.degree v = 2 * G.edgeFinset.card :=
  G.sum_degrees_eq_twice_card_edges

/-- FO-320. The number of vertices of odd degree is even. -/
@[kb "levin2025" "Prop 2.1.12, p. 129"]
theorem levin_prop_2_1_12_even_odd_vertices [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Even (Finset.univ.filter fun v => Odd (G.degree v)).card :=
  G.even_card_odd_degree_vertices

/-- FO-321. A graph is bipartite iff its vertices split into two sets with all edges between them. -/
@[kb "levin2025" "Text §2.1, p. 129", kb "levin2025" "Glossary §2.1, p. 130"]
theorem levin_s2_1_bipartite_iff_partition (G : SimpleGraph V) :
    G.IsBipartite ↔ ∃ s t : Set V, G.IsBipartiteWith s t :=
  SimpleGraph.isBipartite_iff_exists_isBipartiteWith

/-- FO-321. In the complete bipartite graph, a vertex on the left is adjacent to every one
on the right. -/
@[kb "levin2025" "Text §2.1, p. 129", kb "levin2025" "Glossary §2.1, p. 130"]
theorem levin_s2_1_complete_bipartite_adj (a : V) (b : W) :
    (completeBipartiteGraph V W).Adj (Sum.inl a) (Sum.inr b) := by
  simp

/-- FO-322. Adjacency in the cycle graph `C_n`: vertices differing by one step around the cycle. -/
@[kb "levin2025" "Text §2.1, p. 129"]
theorem levin_s2_1_cycle_graph_adj {n : ℕ} (u v : Fin n) :
    (cycleGraph n).Adj u v ↔ (u - v).val = 1 ∨ (v - u).val = 1 :=
  cycleGraph_adj'

/-- FO-322. Adjacency in the path graph: consecutive vertices. -/
@[kb "levin2025" "Text §2.1, p. 130"]
theorem levin_s2_1_path_graph_adj {n : ℕ} (u v : Fin n) :
    (pathGraph n).Adj u v ↔ u.val + 1 = v.val ∨ v.val + 1 = u.val :=
  pathGraph_adj

/-- FO-323. A trail repeats no edge, and a path repeats no vertex. -/
@[kb "levin2025" "Glossary §2.1, p. 131", kb "levin2025" "Text §2.4, p. 161"]
theorem levin_s2_1_trail_path {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    (p.IsTrail ↔ p.edges.Nodup) ∧ (p.IsPath ↔ p.support.Nodup) :=
  ⟨SimpleGraph.Walk.isTrail_def p, SimpleGraph.Walk.isPath_def p⟩

/-- FO-327. A graph is a tree iff it has a vertex and any two vertices are joined by a unique path. -/
@[kb "levin2025" "Prop 2.2.3, p. 139"]
theorem levin_prop_2_2_3_tree_unique_path (G : SimpleGraph V) :
    G.IsTree ↔ Nonempty V ∧ ∀ v w : V, ∃! p : G.Walk v w, p.IsPath :=
  SimpleGraph.isTree_iff_existsUnique_path

/-- FO-328. A graph is a forest iff any two vertices are joined by at most one path. -/
@[kb "levin2025" "Cor 2.2.4, p. 140"]
theorem levin_cor_2_2_4_forest_unique_path (G : SimpleGraph V) :
    G.IsAcyclic ↔ ∀ u v : V, Subsingleton (G.Path u v) :=
  SimpleGraph.isAcyclic_iff_subsingleton_path

/-- FO-329. A finite tree with at least two vertices has two distinct leaves. -/
@[kb "levin2025" "Prop 2.2.5, p. 140"]
theorem levin_prop_2_2_5_tree_two_leaves [Nontrivial V] (G : SimpleGraph V) [Finite G.edgeSet]
    [G.LocallyFinite] (h : G.IsTree) : ∃ u v, u ≠ v ∧ G.degree u = 1 ∧ G.degree v = 1 :=
  h.exists_ne_and_degree_eq_one

/-- FO-331. A spanning subgraph of `G` on the same vertex set is a graph `T ≤ G`
(adjacent in `T` implies adjacent in `G`). -/
@[kb "levin2025" "Def 2.2.7, p. 142"]
theorem levin_def_2_2_7_spanning_le (G T : SimpleGraph V) :
    T ≤ G ↔ ∀ u v, T.Adj u v → G.Adj u v :=
  Iff.rfl

/-- FO-332. Every connected graph has a spanning tree. -/
@[kb "levin2025" "Thm 2.2.8, p. 142"]
theorem levin_thm_2_2_8_spanning_tree (G : SimpleGraph V) (h : G.Connected) :
    ∃ T ≤ G, T.IsTree :=
  h.exists_isTree_le

/-- FO-336. Every tree is bipartite, and so is every forest. -/
@[kb "levin2025" "Example 2.2.11, p. 144"]
theorem levin_ex_2_2_11_forest_bipartite (G : SimpleGraph V) (h : G.IsAcyclic) :
    G.IsBipartite :=
  h.isBipartite

/-- FO-336. A tree is 2-colourable. -/
@[kb "levin2025" "Example 2.2.11, p. 144"]
theorem levin_ex_2_2_11_tree_two_colorable (G : SimpleGraph V) (h : G.IsTree) :
    G.Colorable 2 :=
  h.colorable_two

/-- FO-341. The girth is infinite (no cycle at all) exactly for forests. -/
@[kb "levin2025" "Text §2.3, p. 154"]
theorem levin_s2_3_girth_top_iff_acyclic (G : SimpleGraph V) :
    G.egirth = ⊤ ↔ G.IsAcyclic :=
  SimpleGraph.egirth_eq_top

/-- FO-341. Every cycle is at least as long as the girth. -/
@[kb "levin2025" "Text §2.3, p. 154"]
theorem levin_s2_3_girth_le_cycle {G : SimpleGraph V} {v : V} (c : G.Walk v v) (h : c.IsCycle) :
    G.girth ≤ c.length :=
  h.girth_le_length

/-- FO-345. An Euler trail uses every edge exactly once; an Euler circuit is a closed one. -/
@[kb "levin2025" "Text §2.4, p. 161", kb "levin2025" "Glossary §2.4, p. 131"]
theorem levin_s2_4_euler_trail [DecidableEq V] {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    p.IsEulerian ↔ ∀ e ∈ G.edgeSet, p.edges.count e = 1 :=
  Iff.rfl

/-- FO-345. A circuit is a nonempty closed trail. -/
@[kb "levin2025" "Text §2.4, p. 161", kb "levin2025" "Glossary §2.4, p. 131"]
theorem levin_s2_4_euler_circuit {G : SimpleGraph V} {u : V} (p : G.Walk u u) :
    p.IsCircuit ↔ p.IsTrail ∧ p ≠ SimpleGraph.Walk.nil :=
  SimpleGraph.Walk.isCircuit_def p

/-- FO-347. A Hamilton path visits each vertex exactly once. -/
@[kb "levin2025" "Text §2.4, p. 164"]
theorem levin_s2_4_hamilton_path [DecidableEq V] {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    p.IsHamiltonian ↔ ∀ a, p.support.count a = 1 :=
  Iff.rfl

/-- FO-347. A Hamilton cycle is a cycle through all vertices. -/
@[kb "levin2025" "Text §2.4, p. 164"]
theorem levin_s2_4_hamilton_cycle [DecidableEq V] {G : SimpleGraph V} {u : V} (p : G.Walk u u) :
    p.IsHamiltonianCycle ↔ p.IsCycle ∧ p.tail.IsHamiltonian :=
  ⟨fun h => ⟨h.isCycle, h.isHamiltonian_tail⟩, fun h => ⟨h.1, h.2⟩⟩

/-- FO-348. In a proper colouring, adjacent vertices get different colours. -/
@[kb "levin2025" "Text §2.5, p. 171"]
theorem levin_s2_5_proper_coloring {α : Type*} {G : SimpleGraph V} (c : G.Coloring α)
    {u v : V} (h : G.Adj u v) : c u ≠ c v :=
  c.valid h

/-- FO-348. A graph is `n`-colourable iff it has a proper colouring with `n` colours. -/
@[kb "levin2025" "Text §2.5, p. 171"]
theorem levin_s2_5_colorable_iff (G : SimpleGraph V) (n : ℕ) :
    G.Colorable n ↔ Nonempty (G.Coloring (Fin n)) :=
  Iff.rfl

/-- FO-349. The chromatic number is at most `n` iff `n` colours suffice. -/
@[kb "levin2025" "Intro §2.1, p. 122", kb "levin2025" "Text §2.5, p. 171"]
theorem levin_s2_5_chromatic_le_iff (G : SimpleGraph V) (n : ℕ) :
    G.chromaticNumber ≤ n ↔ G.Colorable n :=
  SimpleGraph.chromaticNumber_le_iff_colorable

/-- FO-350. The complete graph on `n` vertices needs `n` colours. -/
@[kb "levin2025" "Text §2.5, p. 174"]
theorem levin_s2_5_chromatic_complete [Fintype V] :
    (⊤ : SimpleGraph V).chromaticNumber = Fintype.card V :=
  SimpleGraph.chromaticNumber_top

/-- FO-350. A bipartite graph with an edge has chromatic number `2`. -/
@[kb "levin2025" "Example 2.5.3, p. 173"]
theorem levin_ex_2_5_3_bipartite_chromatic_two {G : SimpleGraph V} (h : G.IsBipartite)
    {u v : V} (huv : G.Adj u v) : G.chromaticNumber = 2 :=
  le_antisymm (SimpleGraph.chromaticNumber_le_two_iff_isBipartite.mpr h)
    (SimpleGraph.two_le_chromaticNumber_of_adj huv)

/-- FO-350. The complete bipartite graph with both sides nonempty has chromatic number `2`. -/
@[kb "levin2025" "Example 2.5.3, p. 173"]
theorem levin_ex_2_5_3_complete_bipartite_chromatic [Nonempty V] [Nonempty W] :
    (completeBipartiteGraph V W).chromaticNumber = 2 :=
  SimpleGraph.CompleteBipartiteGraph.chromaticNumber

/-- FO-351. For a finite nonempty graph, `1 ≤ χ(G) ≤ |V|`. -/
@[kb "levin2025" "Text §2.5, p. 176"]
theorem levin_s2_5_chromatic_bounds [Fintype V] [Nonempty V] (G : SimpleGraph V) :
    1 ≤ G.chromaticNumber ∧ G.chromaticNumber ≤ Fintype.card V :=
  ⟨Order.one_le_iff_pos.mpr (SimpleGraph.Colorable.chromaticNumber_pos (n := Fintype.card V)
      G.colorable_of_fintype),
   SimpleGraph.chromaticNumber_le_card⟩

/-- FO-353. An `n`-clique is a set of `n` pairwise adjacent vertices. -/
@[kb "levin2025" "Text §2.5, p. 176"]
theorem levin_s2_5_nclique_iff (G : SimpleGraph V) (n : ℕ) (s : Finset V) :
    G.IsNClique n s ↔ G.IsClique s ∧ s.card = n :=
  SimpleGraph.isNClique_iff G

/-- FO-354. The chromatic number is at least the clique number. -/
@[kb "levin2025" "Thm 2.5.6, p. 176"]
theorem levin_thm_2_5_6_clique_le_chromatic (G : SimpleGraph V) :
    G.cliqueNum ≤ G.chromaticNumber :=
  SimpleGraph.cliqueNum_le_chromaticNumber

/-- FO-361. A matching: every vertex of the matching lies on exactly one edge of it. -/
@[kb "levin2025" "Text §2.7, p. 201"]
theorem levin_s2_7_matching_def {G : SimpleGraph V} (M : G.Subgraph) :
    M.IsMatching ↔ ∀ v ∈ M.verts, ∃! w, M.Adj v w :=
  Iff.rfl

/-- FO-361. A perfect matching is a matching that covers all vertices. -/
@[kb "levin2025" "Text §2.7, p. 201"]
theorem levin_s2_7_perfect_matching_def {G : SimpleGraph V} (M : G.Subgraph) :
    M.IsPerfectMatching ↔ M.IsMatching ∧ M.IsSpanning :=
  Iff.rfl

/-- FO-362. Hall's theorem (sufficiency): if every set `S` in part `A` has at least `|S|`
neighbours, there is a matching covering `A`. -/
@[kb "levin2025" "Thm 2.7.2, p. 202"]
theorem levin_thm_2_7_2_hall {G : SimpleGraph V} [G.LocallyFinite] {A B : Set V}
    (hG : G.IsBipartiteWith A B)
    (h : ∀ s ⊆ A, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard) :
    ∃ M : G.Subgraph, A ⊆ M.verts ∧ M.IsMatching :=
  SimpleGraph.exists_isMatching_of_forall_ncard_le hG h

/-- FO-362. Hall's theorem for finite families: a system of distinct representatives exists
iff every subfamily has a large enough union. -/
@[kb "levin2025" "Thm 2.7.2, p. 202"]
theorem levin_thm_2_7_2_hall_family {ι α : Type*} [DecidableEq α] (t : ι → Finset α) [Finite ι] :
    (∀ s : Finset ι, s.card ≤ (s.biUnion t).card) ↔
      ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x :=
  Finset.all_card_le_biUnion_card_iff_exists_injective t

end UndergradKB.Foundations.Course
