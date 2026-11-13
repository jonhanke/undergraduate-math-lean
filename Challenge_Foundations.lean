/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import UndergradKB.Foundations.VizingTheorem

/-!
# Headline statements of undergraduate-math-lean 0.2.1: proofs, logic and sets (Hammack, *Book of Proof*; Levin, *Discrete Mathematics*)

The main result of this topic that Mathlib and Tau Ceti lack, with its proof a deliberate `sorry`: Vizing's theorem,
that the chromatic index of a finite simple graph is its maximum degree or one more. To check what is claimed, read
this file. `Solution_Foundations.lean` proves the same statement from the library, and `lake comparator` (configured
by `comparator/Foundations.json`) checks that each proved statement is exactly the one here and uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Each statement is the library's statement, copied. The statements were not yet reviewed by a human (see the README).

## Definitions used

Besides Mathlib (`SimpleGraph`, `SimpleGraph.maxDegree`, `SimpleGraph.edgeSet`), the statement uses these definitions
of the library (namespace `UndergradKB.Foundations`); a reader checking the statement should check these too:

* `IsProperEdgeColoring G c`: the edge colouring `c : G.edgeSet → α` is proper, i.e. any two distinct edges sharing
  an endpoint get different colours.
* `EdgeColorable G n`: there is a proper edge colouring of `G` with colours in `Fin n`, i.e. using at most `n` colours.
* `chromaticIndex G`: the least `n` such that `G` is `EdgeColorable G n`, as an element of `ℕ∞` (it is `⊤` if there is
  no such `n`; this is the infimum of the set of such `n`).
-/

namespace UndergradKB.Headlines.Foundations

open UndergradKB.Foundations

/-- **Vizing's theorem** (Levin Theorem 2.5.9): the chromatic index of a finite simple graph `G` is either its
maximum degree `Δ(G)` or `Δ(G) + 1`. Hypotheses beyond the book: the vertex type is finite (the book treats finite
graphs) and the graph is simple, with decidable adjacency (so that `maxDegree` is defined). Related: Mathlib has edge
labelings (`SimpleGraph.EdgeLabeling`) but no chromatic index; Tau Ceti has Kőnig's edge-colouring theorem for bipartite graphs and the
equivalence of edge colourings with partitions into matchings, but not the bound `Δ + 1` for general graphs. -/
theorem vizing {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    chromaticIndex G = G.maxDegree ∨ chromaticIndex G = G.maxDegree + 1 := by
  sorry

end UndergradKB.Headlines.Foundations
