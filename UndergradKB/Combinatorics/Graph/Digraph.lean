import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.List.Nodup
import UndergradKB.Common.Attr

/-!
# Digraphs, directed paths and directed cycles

Source: Keller--Trotter, *Applied Combinatorics* (2017), Section 12.1 (p. 269).
The book's digraph is a vertex set with a set of ordered pairs of distinct vertices (directed
edges). Mathlib's `Digraph V` is an arbitrary relation `Adj` (loops allowed); the book's notion is a
`Digraph` whose relation is irreflexive. Directed paths and cycles are lists of distinct vertices.
-/

namespace UndergradKB.Combinatorics.DigraphKT

variable {V : Type*}

/-- CO-132. A digraph in the book's sense: a `Digraph` with no loops (directed edges join distinct
vertices). -/
@[kb "kellertrotter2017" "Definition (unnumbered) digraph, p. 269"]
def IsLoopless (G : Digraph V) : Prop := ∀ v, ¬ G.Adj v v

/-- CO-132. A directed path: a nonempty list `x₀, x₁, …, x_t` of distinct vertices with a directed
edge `(x_i, x_{i+1})` for each `i < t`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) directed path, p. 269"]
def IsDirectedPath (G : Digraph V) (l : List V) : Prop :=
  l ≠ [] ∧ l.Nodup ∧ l.IsChain G.Adj

/-- CO-132. A directed cycle: a directed path `x₀, …, x_t` with `t ≥ 1` together with the closing
directed edge `(x_t, x₀)`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) directed cycle, p. 269"]
def IsDirectedCycle (G : Digraph V) (l : List V) : Prop :=
  IsDirectedPath G l ∧ 2 ≤ l.length ∧ ∃ h : l ≠ [], G.Adj (l.getLast h) (l.head h)

/-- CO-132. A single vertex is a directed path. -/
theorem isDirectedPath_singleton (G : Digraph V) (v : V) : IsDirectedPath G [v] :=
  ⟨List.cons_ne_nil _ _, List.nodup_singleton v, List.isChain_singleton v⟩

/-- CO-132. Two vertices joined by a directed edge in both directions form a directed cycle of
length two. -/
theorem isDirectedCycle_pair (G : Digraph V) {u v : V} (huv : u ≠ v) (h1 : G.Adj u v)
    (h2 : G.Adj v u) : IsDirectedCycle G [u, v] := by
  refine ⟨⟨List.cons_ne_nil _ _, ?_, ?_⟩, le_rfl, List.cons_ne_nil _ _, ?_⟩
  · simp [huv]
  · simp [h1]
  · simpa using h2

end UndergradKB.Combinatorics.DigraphKT
