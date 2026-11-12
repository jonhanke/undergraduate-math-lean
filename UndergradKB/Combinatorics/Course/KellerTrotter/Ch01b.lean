import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Nat.Choose.Basic
import UndergradKB.Combinatorics.Recurrence.Collatz
import UndergradKB.Combinatorics.Recurrence.Examples
import UndergradKB.Combinatorics.Recurrence.Wave2Solve
import UndergradKB.Combinatorics.Graph.SpanningTree
import UndergradKB.Common.Attr

/-!
# Keller–Trotter, Chapter 1: course wrappers of results proved in this library (wave 3)
-/

namespace UndergradKB.Combinatorics.Course.KellerTrotter.Ch01b

/-- CO-326. The Collatz sequence (`n ↦ 3n+1` for odd `n`, `n ↦ n/2` for even `n`): the worked
sequences from `28` and `19`, and `19` reaches `1`. -/
@[kb "kellertrotter2017" "Example 1.8, p. 33"]
theorem ex_1_8_collatz :
    collatzList 28 18 = [28, 14, 7, 22, 11, 34, 17, 52, 26, 13, 40, 20, 10, 5, 16, 8, 4, 2, 1] ∧
    collatzList 19 5 = [19, 58, 29, 88, 44, 22] ∧ CollatzReachesOne 19 :=
  ⟨collatzList_28, collatzList_19, collatzReachesOne_19⟩

/-- CO-214. `n` lines in general position cut the plane into `r n` regions, where `r 1 = 2` and
`r n = n + r (n-1)`; closed forms `1 + C(n+1,2)` and `1 + n(n+1)/2`. -/
@[kb "kellertrotter2017" "Example 1.12, p. 36"]
theorem ex_1_12_lines_regions (r : ℕ → ℕ) (h1 : r 1 = 2) (hs : ∀ n, 2 ≤ n → r n = n + r (n - 1)) :
    (∀ n, 1 ≤ n → r n = 1 + (n + 1).choose 2) ∧ (∀ n, 1 ≤ n → r n = 1 + n * (n + 1) / 2) :=
  ⟨Recurrence.lines_regions_closed_form' r h1 hs, Recurrence.lines_regions_explicit' r h1 hs⟩

/-- CO-083. Every connected graph has a spanning tree, and every connected weighted graph has a
minimum weight spanning tree. -/
@[kb "kellertrotter2017" "Exercise 1.19 (spanning tree), p. 38"]
theorem ex_1_19_min_spanning_tree {V : Type*} [Fintype V] {G : SimpleGraph V} (w : Sym2 V → ℝ)
    (h : G.Connected) :
    (∃ T ≤ G, T.IsTree) ∧ ∃ T, SpanningTree.IsMinSpanningTree G w T :=
  ⟨SpanningTree.exists_spanning_tree h, SpanningTree.exists_isMinSpanningTree w h⟩

end UndergradKB.Combinatorics.Course.KellerTrotter.Ch01b
