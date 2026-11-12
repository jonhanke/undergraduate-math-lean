import UndergradKB.Combinatorics.Graph.SpanningTree
import UndergradKB.Combinatorics.Graph.SpanningTreeGreedy
import UndergradKB.Combinatorics.Graph.Digraph
import UndergradKB.Combinatorics.Graph.ShortestPath
import UndergradKB.Common.Attr

/-!
# Keller–Trotter, Chapter 12: course wrappers of results proved in this library (wave 3)
-/

namespace UndergradKB.Combinatorics.Course.KellerTrotter.Ch12b

open SpanningTree

/-- CO-131. A spanning forest with `n - k` edges on `n` vertices has `k` components, so it has at
most `n - 1` edges, and it is a spanning tree exactly when it has `n - 1` edges. -/
@[kb "kellertrotter2017" "Proposition 12.3, p. 264"]
theorem prop_12_3_forest_edges {V : Type*} [Fintype V] [Nonempty V] (H : SimpleGraph V)
    (hH : H.IsAcyclic) :
    (H.edgeSet.ncard + 1 ≤ Nat.card V ∧
        ∀ k : ℕ, H.edgeSet.ncard + k = Nat.card V → Nat.card H.ConnectedComponent = k) ∧
      (H.IsTree ↔ H.edgeSet.ncard + 1 = Nat.card V) :=
  ⟨forest_edges_le_and_components H hH, forest_isTree_iff H hH⟩

/-- CO-271. Adding a non-tree edge `xy` to a spanning tree and deleting any edge on the tree path
from `x` to `y` gives another spanning tree. -/
@[kb "kellertrotter2017" "Proposition 12.4, p. 265"]
theorem prop_12_4_exchange {V : Type*} [Fintype V] {T : SimpleGraph V} (hT : T.IsTree) {x y : V}
    (hxy : x ≠ y) (hadj : ¬T.Adj x y) (p : T.Walk x y) (hp : p.IsPath) {f : Sym2 V}
    (hf : f ∈ p.edges) : (exchange T s(x, y) f).IsTree :=
  exchange_isTree hT hxy hadj p hp hf

/-- CO-272. If `F` is a spanning forest contained in a minimum spanning tree, `C` a component of
`F` and `xy` a minimum-weight edge leaving `C`, then some minimum spanning tree containing `F`
contains `xy`. -/
@[kb "kellertrotter2017" "Lemma 12.6, p. 266"]
theorem lem_12_6_min_edge_leaving_component {V : Type*} [Fintype V] {G F T : SimpleGraph V}
    (w : Sym2 V → ℝ) (C : F.ConnectedComponent) (hT : IsMinSpanningTreeContaining G w F T)
    {x y : V} (hx : F.connectedComponentMk x = C) (hy : F.connectedComponentMk y ≠ C)
    (hxy : G.Adj x y)
    (hmin : ∀ a b : V, G.Adj a b → F.connectedComponentMk a = C → F.connectedComponentMk b ≠ C →
      w s(x, y) ≤ w s(a, b)) :
    ∃ T' : SimpleGraph V, IsMinSpanningTreeContaining G w F T' ∧ T'.Adj x y :=
  lemma_12_6 w C hT hx hy hxy hmin

/-- CO-273. Kruskal's algorithm: with the edges sorted by weight, repeatedly adding the next edge
that creates no cycle yields a minimum weight spanning tree of a connected graph. -/
@[kb "kellertrotter2017" "Algorithm 12.8, p. 267"]
theorem alg_12_8_kruskal {V : Type*} [Fintype V] {G : SimpleGraph V} (hG : G.Connected)
    (w : Sym2 V → ℝ) :
    ∃ l : List (Sym2 V), List.Pairwise (fun a b => w a ≤ w b) l ∧
      IsMinSpanningTree G w (kruskal l) :=
  kruskal_sorted_isMinSpanningTree hG w

/-- CO-274. For any list of the edges of a connected graph sorted by weight, Kruskal's algorithm
outputs a minimum weight spanning tree. -/
@[kb "kellertrotter2017" "text (Kruskal correctness), p. 267"]
theorem text_p267_kruskal_correct {V : Type*} [Fintype V] {G : SimpleGraph V} (hG : G.Connected)
    (w : Sym2 V → ℝ) (l : List (Sym2 V)) (hl : List.Pairwise (fun a b => w a ≤ w b) l)
    (hedges : ∀ e : Sym2 V, e ∈ l ↔ e ∈ G.edgeSet) :
    IsMinSpanningTree G w (kruskal l) :=
  kruskal_isMinSpanningTree hG w l hl hedges

/-- CO-276. Prim's algorithm: a tree grown from a root by repeatedly adding the lightest edge
leaving the current vertex set is, once it reaches every vertex, a minimum weight spanning tree. -/
@[kb "kellertrotter2017" "text (Prim correctness), p. 268"]
theorem text_p268_prim_correct {V : Type*} [Fintype V] {G : SimpleGraph V} (hG : G.Connected)
    {w : Sym2 V → ℝ} {r : V} {F : SimpleGraph V} (hF : PrimReach G w r F)
    (hall : ∀ v : V, F.Reachable r v) : IsMinSpanningTree G w F :=
  PrimReach.isMinSpanningTree hG hF hall

/-- CO-132. Digraphs, directed paths and cycles: a single vertex is a directed path, and two
distinct vertices joined by arcs in both directions form a directed cycle. -/
@[kb "kellertrotter2017" "Definition (unnumbered) digraph, directed path, directed cycle, p. 269"]
theorem def_p269_digraph {V : Type*} (G : Digraph V) :
    (∀ v : V, DigraphKT.IsDirectedPath G [v]) ∧
      ∀ {u v : V}, u ≠ v → G.Adj u v → G.Adj v u → DigraphKT.IsDirectedCycle G [u, v] :=
  ⟨DigraphKT.isDirectedPath_singleton G, fun h huv hvu => DigraphKT.isDirectedCycle_pair G h huv hvu⟩

/-- CO-278. With nonnegative edge lengths (values in `[0, ∞]`), the distance from `r` to `x` is the
minimum length of a directed path, and it is attained by a shortest path whenever it is finite. -/
@[kb "kellertrotter2017" "Definition (unnumbered) length and distance, p. 269"]
theorem def_p269_distance {V : Type*} [Fintype V] [DecidableEq V] (w : V → V → ENNReal)
    (a b : V) (h : ShortestPath.dist w a b ≠ ⊤) :
    ∃ p : ShortestPath.Walk w a b, p.IsShortest :=
  ShortestPath.exists_isShortest w a b h

/-- CO-280. Every initial and final segment of a shortest path is a shortest path. -/
@[kb "kellertrotter2017" "Proposition 12.16, p. 275"]
theorem prop_12_16_segments_shortest {V : Type*} {w : V → V → ENNReal} {r u x : V}
    {Q : ShortestPath.Walk w r u} {R : ShortestPath.Walk w u x} (h : (Q.append R).IsShortest) :
    Q.IsShortest ∧ R.IsShortest :=
  ShortestPath.Walk.IsShortest.of_append h

/-- CO-281. Dijkstra's algorithm makes vertices permanent in nondecreasing order of their labels
`δ`; the list of permanent vertices has no repeats, starts at the root and contains every vertex. -/
@[kb "kellertrotter2017" "Proposition 12.17, p. 275"]
theorem prop_12_17_dijkstra_order {V : Type*} [Fintype V] [DecidableEq V] (w : V → V → ENNReal)
    (r : V) :
    List.Pairwise (fun x1 x2 : ENNReal => x1 ≤ x2)
        ((ShortestPath.dijkstra w r).1.map (ShortestPath.dijkstra w r).2) ∧
      (ShortestPath.dijkstra w r).1.Nodup ∧ (ShortestPath.dijkstra w r).1.head? = some r ∧
      ∀ x : V, x ∈ (ShortestPath.dijkstra w r).1 :=
  ShortestPath.dijkstra_sorted w r

/-- CO-282. Dijkstra's algorithm terminates with `δ(x)` equal to the true distance from the root
to `x`, and a shortest path to every vertex at finite distance. -/
@[kb "kellertrotter2017" "Theorem 12.18, p. 275"]
theorem thm_12_18_dijkstra_correct {V : Type*} [Fintype V] [DecidableEq V] (w : V → V → ENNReal)
    (r x : V) :
    (ShortestPath.dijkstra w r).2 x = ShortestPath.dist w r x ∧
      (ShortestPath.dist w r x ≠ ⊤ → ∃ p : ShortestPath.Walk w r x, p.IsShortest) :=
  ShortestPath.dijkstra_dist w r x

end UndergradKB.Combinatorics.Course.KellerTrotter.Ch12b
