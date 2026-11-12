import Mathlib.Combinatorics.SimpleGraph.Acyclic
import UndergradKB.Common

/-!
# Course layer: Hammack, Chapter 10 (graph theory, rows shared with Levin)

Thin statements for the graph rows FO-310, FO-314, FO-324, FO-326 and FO-330 classified `in Mathlib`.
-/

namespace UndergradKB.Foundations.Course

variable {V : Type*}

/-- FO-310. Every edge of a simple graph is a 2-element set of distinct vertices. -/
@[kb "hammack2018" "Def §10.2, p. 201", kb "levin2025" "Def 2.1.2, p. 122"]
theorem hammack_s10_2_edge_two_vertices (G : SimpleGraph V) :
    ∀ e ∈ G.edgeSet, ∃ u v : V, u ≠ v ∧ e = s(u, v) := by
  intro e he
  induction e using Sym2.ind with
  | _ u v => exact ⟨u, v, G.ne_of_adj he, rfl⟩

/-- FO-314. A graph is connected when a walk joins any two vertices (and it has a vertex). -/
@[kb "hammack2018" "Def §10.2, p. 201", kb "levin2025" "Text §2.1, p. 127"]
theorem hammack_s10_2_connected_iff (G : SimpleGraph V) :
    G.Connected ↔ Nonempty V ∧ ∀ u v : V, Nonempty (G.Walk u v) := by
  rw [SimpleGraph.connected_iff]
  exact and_comm

/-- FO-324. A cycle is a nonempty trail whose vertices, other than the start, are all distinct. -/
@[kb "hammack2018" "Def §10.2, p. 201", kb "levin2025" "Intro §2.1, p. 122"]
theorem hammack_s10_2_cycle_def {u : V} (G : SimpleGraph V) (p : G.Walk u u) :
    p.IsCycle ↔ p.IsTrail ∧ p ≠ SimpleGraph.Walk.nil ∧ p.support.tail.Nodup :=
  SimpleGraph.Walk.isCycle_def p

/-- FO-326. A tree is a connected graph with no cycles. -/
@[kb "hammack2018" "Def §10.2, p. 201", kb "levin2025" "Def 2.2.2, p. 137"]
theorem hammack_s10_2_tree_def (G : SimpleGraph V) :
    G.IsTree ↔ G.Connected ∧ ∀ (v : V) (c : G.Walk v v), ¬ c.IsCycle :=
  SimpleGraph.isTree_iff G

/-- FO-330. A tree with `n` vertices has `n - 1` edges, and conversely a connected graph
with `n - 1` edges is a tree. -/
@[kb "hammack2018" "Prop §10.2, p. 202", kb "levin2025" "Prop 2.2.6, p. 141"]
theorem hammack_s10_2_tree_iff_card_edges [Finite V] (G : SimpleGraph V) :
    G.IsTree ↔ G.Connected ∧ Nat.card G.edgeSet + 1 = Nat.card V :=
  SimpleGraph.isTree_iff_connected_and_card

end UndergradKB.Foundations.Course
