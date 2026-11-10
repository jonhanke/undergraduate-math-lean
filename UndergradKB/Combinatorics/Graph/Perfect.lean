import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.Finite
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.Graph.Coloring

/-!
# Leaves and perfect graphs

Source: Keller--Trotter, *Applied Combinatorics* (2017), Chapter 5.
-/

namespace UndergradKB.Combinatorics

open SimpleGraph

section Leaf

variable {V : Type*} (G : SimpleGraph V) [G.LocallyFinite]

/-- CO-092. A leaf of a graph (typically a tree) is a vertex of degree one. -/
@[kb "kellertrotter2017" "Definition (unnumbered) leaf, p. 98"]
def IsLeafVertex (v : V) : Prop := G.degree v = 1

/-- CO-092. A leaf is a vertex with exactly one neighbour. -/
theorem isLeafVertex_iff (v : V) : IsLeafVertex G v ↔ ∃! u, G.Adj v u :=
  degree_eq_one_iff_existsUnique_adj

/-- CO-092 (Proposition 5.11, via Mathlib). A tree on at least two vertices has at least two
leaves. -/
@[kb "kellertrotter2017" "Proposition 5.11, p. 98"]
theorem IsTree.exists_two_leaves [Finite G.edgeSet] [Nontrivial V] (h : G.IsTree) :
    ∃ u v, u ≠ v ∧ IsLeafVertex G u ∧ IsLeafVertex G v :=
  h.exists_ne_and_degree_eq_one

end Leaf

/-! ### Perfect graphs -/

section Perfect

variable {V : Type*}

/-- CO-112. A graph is perfect if every induced subgraph `H` has chromatic number equal to its
clique number (`χ(H) = ω(H)`; the inequality `ω ≤ χ` always holds). -/
@[kb "kellertrotter2017" "Definition (unnumbered) perfect graph, p. 112"]
def IsPerfect (G : SimpleGraph V) : Prop :=
  ∀ s : Set V, (G.induce s).chromaticNumber = (G.induce s).cliqueNum

/-- CO-112. An induced subgraph of an interval graph is an interval graph. -/
theorem IsIntervalGraph.induce {G : SimpleGraph V} (hG : IsIntervalGraph G) (s : Set V) :
    IsIntervalGraph (G.induce s) := by
  obtain ⟨a, b, hab, rfl⟩ := hG
  refine ⟨fun v => a v, fun v => b v, fun v => hab v, ?_⟩
  ext u v
  simp [SimpleGraph.induce, intersectionGraph, Subtype.ext_iff]

/-- CO-112. Interval graphs (on finitely many vertices) are perfect: an induced subgraph of an
interval graph is an interval graph, and Theorem 5.28 applies to it. -/
@[kb "kellertrotter2017" "text (unnumbered) interval graphs are perfect, p. 112"]
theorem IsIntervalGraph.isPerfect [Finite V] {G : SimpleGraph V} (hG : IsIntervalGraph G) :
    IsPerfect G := fun s => (hG.induce s).chromaticNumber_eq_cliqueNum

end Perfect

end UndergradKB.Combinatorics
