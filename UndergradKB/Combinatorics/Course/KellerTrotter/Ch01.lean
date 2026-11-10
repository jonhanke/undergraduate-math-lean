import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Paths
import UndergradKB.Common.Attr

/-!
# Keller–Trotter, Chapter 1 (Introduction): thin course wrappers for definitions
-/

namespace UndergradKB.Combinatorics.Course.KellerTrotter

section

variable {V : Type*} (G : SimpleGraph V)

/-- CO-079. A graph is a vertex set with a set of 2-element subsets (edges); two vertices are
adjacent exactly when the pair is an edge. -/
@[kb "kellertrotter2017" "Definition (unnumbered) graph, p. 29"]
theorem def_p29_graph_adj (u v : V) : G.Adj u v ↔ s(u, v) ∈ G.edgeSet :=
  by rw [SimpleGraph.mem_edgeSet]

/-- CO-080. A path is a walk (consecutive vertices adjacent) with no repeated vertex. -/
@[kb "kellertrotter2017" "Definition (unnumbered) path, p. 30"]
theorem def_p30_path {u v : V} (p : G.Walk u v) : p.IsPath ↔ p.support.Nodup :=
  SimpleGraph.Walk.isPath_def p

/-- CO-080. A cycle is a closed non-trivial walk using no edge twice and no vertex twice (except
the common start and end). -/
@[kb "kellertrotter2017" "Definition (unnumbered) cycle, p. 30"]
theorem def_p30_cycle [DecidableEq V] {u : V} (p : G.Walk u u) :
    p.IsCycle ↔ p.IsTrail ∧ p ≠ SimpleGraph.Walk.nil ∧ p.support.tail.Nodup :=
  SimpleGraph.Walk.isCycle_def p

/-- CO-081. A graph is connected when it has a vertex and any two vertices are joined by a walk. -/
@[kb "kellertrotter2017" "Definition (unnumbered) connected, p. 30"]
theorem def_p30_connected : G.Connected ↔ Nonempty V ∧ ∀ u v : V, G.Reachable u v := by
  rw [SimpleGraph.connected_iff]
  exact ⟨fun ⟨h, hne⟩ => ⟨hne, h⟩, fun ⟨hne, h⟩ => ⟨h, hne⟩⟩

/-- CO-081. The components are the classes of the relation "joined by a walk". -/
@[kb "kellertrotter2017" "Definition (unnumbered) component, p. 30"]
theorem def_p30_component (u v : V) :
    G.connectedComponentMk u = G.connectedComponentMk v ↔ G.Reachable u v :=
  SimpleGraph.ConnectedComponent.eq

/-- CO-082. A clique is a set of pairwise adjacent vertices. -/
@[kb "kellertrotter2017" "Definition (unnumbered) clique, p. 30"]
theorem def_p30_clique (s : Set V) : G.IsClique s ↔ ∀ u ∈ s, ∀ v ∈ s, u ≠ v → G.Adj u v :=
  Iff.rfl

/-- CO-082. An independent set is a set of pairwise non-adjacent vertices. -/
@[kb "kellertrotter2017" "Definition (unnumbered) independent set, p. 30"]
theorem def_p30_independent (s : Set V) :
    G.IsIndepSet s ↔ ∀ u ∈ s, ∀ v ∈ s, u ≠ v → ¬ G.Adj u v :=
  Iff.rfl

end

end UndergradKB.Combinatorics.Course.KellerTrotter
