/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import UndergradKB.Foundations.VizingTheorem
import UndergradKB.Foundations.Hilbert10

/-!
# Headline statements of undergraduate-math-lean 0.2.2: proofs, logic and sets (Hammack, *Book of Proof*; Levin, *Discrete Mathematics*)

The main results of this topic that Mathlib and Tau Ceti lack, with every proof a deliberate `sorry`: Vizing's
theorem, that the chromatic index of a finite simple graph is its maximum degree or one more; and, added in 0.2.2, the
theorem of Davis, Putnam, Robinson and Matiyasevich (every recursively enumerable set of natural numbers is
Diophantine) and its consequence, the negative answer to Hilbert's tenth problem. To check what is claimed, read this
file. `Solution_Foundations.lean` proves the same statements from the library, and `lake comparator` (configured by
`comparator/Foundations.json`) checks that each proved statement is exactly the one here and uses only the standard
axioms `propext`, `Classical.choice` and `Quot.sound`.

Each statement is the library's statement, copied. The statements were not yet reviewed by a human (see the README).

## Definitions used

The statements of Hilbert's tenth problem use only Mathlib: `REPred` (a predicate on `ℕ` is recursively
enumerable: it is the domain of a partial recursive function), `Dioph S` (Mathlib's Diophantine sets: there are a type
`β` and a polynomial `p` with integer coefficients in the variables `α ⊕ β` such that `v ∈ S` if and only if
`p (v, t) = 0` for some `t : β → ℕ`), `ComputablePred` (a decidable predicate computed by a computable function) and
`MvPolynomial`. Besides Mathlib (`SimpleGraph`, `SimpleGraph.maxDegree`, `SimpleGraph.edgeSet`), Vizing's theorem uses
these definitions of the library (namespace `UndergradKB.Foundations`); a reader checking the statement should check
these too:

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

/-- **The Davis–Putnam–Robinson–Matiyasevich theorem** (behind Levin's remark in § 6.2.5): every
recursively enumerable predicate `P` on the natural numbers is Diophantine: there is a polynomial `p` with integer
coefficients such that `P n` holds if and only if `p (n, t) = 0` for some natural numbers `t`. Related: Mathlib proves
that exponentiation is Diophantine (`Dioph.pow_dioph`, Matiyasevich's step via the Pell equation) and lists the rest of
Hilbert's tenth problem as a to-do item; Tau Ceti does not have it. -/
theorem dprm (P : ℕ → Prop) (hP : REPred P) : Dioph {v : Fin 1 → ℕ | P (v 0)} := by
  sorry

/-- **Hilbert's tenth problem has a negative answer** (Matiyasevich's theorem; Levin § 6.2.5, remark): there is a
polynomial `q (n, z₁, z₂, …)` with integer coefficients such that no algorithm decides, given `n`, whether
`q (n, z) = 0` has a solution in integers `z`; so no algorithm decides the solvability of all Diophantine equations.
Related: neither Mathlib nor Tau Ceti has it. -/
theorem hilbert_tenth :
    ∃ (γ : Type) (q : MvPolynomial (Option γ) ℤ),
      ¬ ComputablePred fun n : ℕ => ∃ z : γ → ℤ, MvPolynomial.eval (fun o => o.elim (n : ℤ) z) q = 0 := by
  sorry

end UndergradKB.Headlines.Foundations
