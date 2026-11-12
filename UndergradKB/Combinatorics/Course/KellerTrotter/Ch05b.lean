import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Basic.Real.Basic
import UndergradKB.Combinatorics.Graph.Perfect
import UndergradKB.Combinatorics.Graph.Multigraph
import UndergradKB.Combinatorics.Graph.RamseyEulerMore
import UndergradKB.Combinatorics.Graph.Euler
import UndergradKB.Combinatorics.Graph.Hamilton
import UndergradKB.Combinatorics.Graph.Coloring
import UndergradKB.Combinatorics.Graph.TriangleFree
import UndergradKB.Combinatorics.Graph.PruferTree
import UndergradKB.Combinatorics.Graph.Prufer
import UndergradKB.Combinatorics.Graph.Cayley
import UndergradKB.Combinatorics.Graph.Brooks
import UndergradKB.Common.Attr

/-!
# Keller–Trotter, Chapter 5: course wrappers of results proved in this library (wave 3)
-/

namespace UndergradKB.Combinatorics.Course.KellerTrotter.Ch05b

open SimpleGraph

/-- CO-092. A leaf of a tree is a vertex of degree one (equivalently with a unique neighbour),
and a tree on at least two vertices has at least two leaves. -/
@[kb "kellertrotter2017" "Proposition 5.11, p. 98"]
theorem prop_5_11_leaves {V : Type*} (G : SimpleGraph V) [G.LocallyFinite] :
    (∀ v, IsLeafVertex G v ↔ ∃! u, G.Adj v u) ∧
    (∀ [Finite G.edgeSet] [Nontrivial V], G.IsTree →
      ∃ u v, u ≠ v ∧ IsLeafVertex G u ∧ IsLeafVertex G v) :=
  ⟨fun v => isLeafVertex_iff G v, fun h => IsTree.exists_two_leaves G h⟩

open scoped Classical in
/-- CO-098. Theorem 5.13: a finite graph is eulerian iff it is connected and every vertex has
even degree; in that case there is an eulerian circuit, and with exactly two odd-degree vertices
`a`, `b` an eulerian trail from `a` to `b`. -/
@[kb "kellertrotter2017" "Theorem 5.13, p. 101"]
theorem thm_5_13_eulerian {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Euler.IsEulerianGraph G ↔ G.Connected ∧ ∀ v, Even (G.degree v)) ∧
    (G.Connected → (∀ v, Even (G.degree v)) →
      ∃ (u : V) (p : G.Walk u u), p.IsEulerian ∧ ∀ v, v ∈ p.support) ∧
    (G.Connected → (∀ v, Even (G.degree v)) → G.edgeSet.Nonempty →
      ∃ (u : V) (p : G.Walk u u), p.IsEulerian ∧ p.IsCircuit ∧ ∀ v, v ∈ p.support) ∧
    (∀ a b : V, G.Connected → (∀ x, Odd (G.degree x) ↔ (a ≠ b ∧ (x = a ∨ x = b))) →
      ∃ p : G.Walk a b, p.IsEulerian ∧ ∀ v, v ∈ p.support) :=
  ⟨Euler.isEulerianGraph_iff, fun hc he => Euler.exists_eulerian_circuit hc he,
   fun hc he hE => Euler.exists_eulerian_isCircuit hc he hE,
   fun a b hc hodd => Euler.exists_eulerian_trail_between hc a b hodd⟩

/-- CO-099. Theorem 5.13 also holds for loopless multigraphs: a connected loopless finite
multigraph is eulerian iff all degrees are even. -/
@[kb "kellertrotter2017" "text, p. 102"]
theorem text_5_13_multigraph_eulerian {V E : Type*} [Fintype V] [Fintype E] (M : Multigraph V E)
    (hM : M.Loopless) (hc : M.Connected) : M.IsEulerian ↔ ∀ v, Even (M.degree v) :=
  Multigraph.isEulerian_iff_even_degree M hM hc

/-- CO-101. The Petersen graph is not hamiltonian. -/
@[kb "kellertrotter2017" "text (Figure 5.17), p. 103"]
theorem text_5_17_petersen_not_hamiltonian : ¬ Hamilton.petersen.IsHamiltonian :=
  Hamilton.petersen_not_isHamiltonian

/-- CO-102. Dirac: if every vertex of a graph on `n ≥ 3` vertices has at least `⌈n/2⌉` neighbours
then the graph is hamiltonian. -/
@[kb "kellertrotter2017" "Theorem 5.18, p. 104"]
theorem thm_5_18_dirac {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (hn3 : 3 ≤ Fintype.card V)
    (hdeg : ∀ v, ⌈(Fintype.card V : ℚ) / 2⌉₊ ≤ G.degree v) : G.IsHamiltonian :=
  Hamilton.dirac hn3 hdeg

/-- CO-105. A graph is 2-colorable iff it contains no odd cycle. -/
@[kb "kellertrotter2017" "Theorem 5.21, p. 106"]
theorem thm_5_21_two_colorable {V : Type*} (G : SimpleGraph V) :
    G.Colorable 2 ↔ ∀ (x : V) (c : G.Walk x x), c.IsCycle → ¬ Odd c.length :=
  colorable_two_iff_no_odd_cycle G

/-- CO-109. For every `t ≥ 3` there is a (finite) graph with chromatic number `t` and clique
number `2`, i.e. triangle-free with an edge (Mycielski's construction). -/
@[kb "kellertrotter2017" "Proposition 5.25, p. 109"]
theorem prop_5_25_triangle_free_chromatic (t : ℕ) (ht : 3 ≤ t) :
    ∃ (W : Type) (_ : Fintype W) (G : SimpleGraph W),
      G.CliqueFree 3 ∧ ¬ G.CliqueFree 2 ∧ G.chromaticNumber = t :=
  Mycielski.exists_chromaticNumber_eq_cliqueNum_two t ht

/-- CO-268. First Fit coloring: colour the vertices in a fixed (well) order, each with the least
colour not used on its earlier neighbours; it is a proper colouring. -/
@[kb "kellertrotter2017" "text, p. 110"]
theorem text_5_first_fit_coloring {V : Type*} (G : SimpleGraph V) [LinearOrder V]
    [WellFoundedLT V] [Finite V] :
    (∀ v, firstFit G v = sInf {c : ℕ | ∀ u, u < v → G.Adj u v → firstFit G u ≠ c}) ∧
    (∀ {u v : V}, u < v → G.Adj u v → firstFit G u ≠ firstFit G v) :=
  ⟨fun v => firstFit_eq G v, fun huv h => firstFit_ne G huv h⟩

/-- CO-110. Intersection graph of a family of sets (adjacent iff distinct with intersecting
sets); an interval graph is one given by closed real intervals `[a v, b v]`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) interval graph, p. 111"]
theorem def_5_interval_graph {V : Type*} (G : SimpleGraph V) (hG : IsIntervalGraph G) :
    ∃ a b : V → ℝ, (∀ v, a v ≤ b v) ∧
      ∀ x y, G.Adj x y ↔ x ≠ y ∧ (Set.Icc (a x) (b x) ∩ Set.Icc (a y) (b y)).Nonempty := by
  obtain ⟨a, b, hab, rfl⟩ := hG
  exact ⟨a, b, hab, fun _ _ => Iff.rfl⟩

/-- CO-111. For an interval graph on finitely many vertices, `χ(G) = ω(G)`. -/
@[kb "kellertrotter2017" "Theorem 5.28, p. 111"]
theorem thm_5_28_interval_chromatic {V : Type*} [Finite V] {G : SimpleGraph V}
    (hG : IsIntervalGraph G) : G.chromaticNumber = G.cliqueNum :=
  hG.chromaticNumber_eq_cliqueNum

/-- CO-112. A graph is perfect if `χ(H) = ω(H)` for every induced subgraph `H`; interval graphs
are perfect (induced subgraphs of interval graphs are interval graphs). -/
@[kb "kellertrotter2017" "Definition (unnumbered) perfect graph, p. 112"]
theorem def_5_perfect_interval {V : Type*} [Finite V] {G : SimpleGraph V}
    (hG : IsIntervalGraph G) : IsPerfect G ∧ ∀ s : Set V, IsIntervalGraph (G.induce s) :=
  ⟨hG.isPerfect, fun s => hG.induce s⟩

/-- CO-016. Cayley: the number of labeled trees on `n ≥ 2` vertices is `n^(n-2)`. -/
@[kb "kellertrotter2017" "Theorem 5.39, p. 121"]
theorem thm_5_39_cayley (n : ℕ) (hn : 2 ≤ n) :
    Nat.card {T : SimpleGraph (Fin n) // T.IsTree} = n ^ (n - 2) :=
  Prufer.cayley_of_two_le n hn

/-- CO-121. The Prüfer code of a tree on a label set `S` with `|S| ≥ 2` has length `|S| - 2`
and its symbols are labels from `S`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) Prüfer code, p. 121"]
theorem def_5_prufer_code {α : Type*} [LinearOrder α] {S : Finset α} {G : SimpleGraph α}
    (hG : Prufer.IsTreeOn S G) (h2 : 2 ≤ S.card) :
    (Prufer.prufer S G).length = S.card - 2 ∧ ∀ x ∈ Prufer.prufer S G, x ∈ S :=
  Prufer.prufer_length_mem hG h2

/-- CO-122. The Prüfer code is a bijection from labeled trees on `[n]` to strings of length
`n - 2` over `[n]`, and a label is a leaf iff it does not occur in the code. -/
@[kb "kellertrotter2017" "Theorem 5.39 (proof), p. 122"]
theorem thm_5_39_prufer_bijection (n : ℕ) (hn : 2 ≤ n) :
    Function.Bijective (Prufer.pruferVec n hn) ∧
    (∀ {α : Type} [LinearOrder α] {S : Finset α} {G : SimpleGraph α},
      Prufer.IsTreeOn S G → 2 ≤ S.card → ∀ {w : α}, w ∈ S →
        (Prufer.IsLeaf G w ↔ w ∉ Prufer.prufer S G)) :=
  ⟨Prufer.pruferVec_bijective n hn,
   fun hG h2 _ hw => Prufer.isLeaf_iff_notMem_prufer hG h2 hw⟩

/-- CO-124. Exercise 5.9.11: a graph has an eulerian trail iff it is connected and has at most
two vertices of odd degree. -/
@[kb "kellertrotter2017" "Exercise 5.9.11, p. 128"]
theorem ex_5_9_11_eulerian_trail {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] :
    Euler.HasEulerianTrail G ↔
      G.Connected ∧ (Finset.univ.filter fun v => Odd (G.degree v)).card ≤ 2 :=
  Euler.hasEulerianTrail_iff

/-- CO-126. Exercise 5.9.27: if every degree is at most `D` then `χ(G) ≤ D + 1`. -/
@[kb "kellertrotter2017" "Exercise 5.9.27, p. 131"]
theorem ex_5_9_27_degree_coloring {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (D : ℕ) (h : ∀ v, G.degree v ≤ D) :
    G.Colorable (D + 1) ∧ G.chromaticNumber ≤ D + 1 :=
  ⟨colorable_of_degree_le G D h, chromaticNumber_le_of_degree_le G D h⟩

/-- CO-128. Exercise 5.9.43: Brooks' theorem. For a connected graph of maximum degree at most
`k ≥ 3`, `χ(G) ≤ k` unless `G` is `K_{k+1}`; for `k = 2` a connected graph with no odd cycle is
2-colorable (and a non-2-colorable graph has an odd cycle). -/
@[kb "kellertrotter2017" "Exercise 5.9.43, p. 134"]
theorem ex_5_9_43_brooks {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] :
    (∀ {k : ℕ}, 3 ≤ k → G.Connected → (∀ v, G.degree v ≤ k) →
      ¬ (G = ⊤ ∧ Fintype.card V = k + 1) → G.Colorable k ∧ G.chromaticNumber ≤ k) ∧
    (G.Connected → (∀ (x : V) (c : G.Walk x x), c.IsCycle → ¬ Odd c.length) → G.Colorable 2) ∧
    (¬ G.Colorable 2 → ∃ (x : V) (c : G.Walk x x), c.IsCycle ∧ Odd c.length) :=
  ⟨fun hk hconn hdeg hK =>
      ⟨brooks_of_not_complete_succ hk hconn hdeg hK, chromaticNumber_le_of_brooks hk hconn hdeg hK⟩,
   fun hconn hno => brooks_two hconn hno, fun h => exists_odd_cycle_of_not_colorable_two h⟩

end UndergradKB.Combinatorics.Course.KellerTrotter.Ch05b
