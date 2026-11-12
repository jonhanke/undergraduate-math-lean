import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.IncMatrix
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.ENat.Lattice
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import UndergradKB.Common

/-!
# Foundations: graph-theory gaps (Levin, Chapter 2)

Degree sequences, closed neighbourhoods, proper edge colourings and the chromatic index,
alternating and augmenting paths for a matching, and the arithmetic core of the classification
of the regular polyhedra.
-/

namespace UndergradKB.Foundations

open SimpleGraph

variable {V : Type*}

/-! ### Degree sequence -/

/-- The degree sequence of a finite graph: the degrees listed in non-increasing order. -/
noncomputable def degreeSequence [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : List ℕ :=
  (Finset.univ.val.map fun v => G.degree v).sort (· ≥ ·)

/-- FO-318. The degree sequence has one entry per vertex. -/
@[kb "levin2025" "Text §2.1, p. 128"]
theorem levin_s2_1_degreeSequence_length [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (degreeSequence G).length = Fintype.card V := by
  unfold degreeSequence
  rw [← Multiset.coe_card, Multiset.sort_eq]
  simp

/-- FO-318. The degree sequence is listed in non-increasing order. -/
@[kb "levin2025" "Text §2.1, p. 128"]
theorem levin_s2_1_degreeSequence_sorted [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (degreeSequence G).Pairwise (· ≥ ·) :=
  Multiset.pairwise_sort _ _

/-- FO-318. The entries of the degree sequence sum to twice the number of edges. -/
@[kb "levin2025" "Text §2.1, p. 128"]
theorem levin_s2_1_degreeSequence_sum [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (degreeSequence G).sum = 2 * G.edgeFinset.card := by
  unfold degreeSequence
  rw [← Multiset.sum_coe, Multiset.sort_eq]
  exact G.sum_degrees_eq_twice_card_edges

/-- FO-318. A vertex of degree `d` contributes `d` to the degree sequence. -/
@[kb "levin2025" "Text §2.1, p. 128"]
theorem levin_s2_1_degreeSequence_mem [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) : d ∈ degreeSequence G ↔ ∃ v, G.degree v = d := by
  unfold degreeSequence
  rw [← Multiset.mem_coe, Multiset.sort_eq]
  simp

/-! ### Closed neighbourhood -/

/-- The closed neighbourhood `N[v]`: the vertex `v` together with its neighbours. -/
def closedNeighborSet (G : SimpleGraph V) (v : V) : Set V := insert v (G.neighborSet v)

/-- FO-325. A vertex lies in `N[v]` iff it is `v` or adjacent to `v`. -/
@[kb "levin2025" "Exercise 2.1.5.11, p. 134"]
theorem levin_ex_2_1_5_11_mem_closedNeighborSet (G : SimpleGraph V) (v w : V) :
    w ∈ closedNeighborSet G v ↔ w = v ∨ G.Adj v w := by
  simp [closedNeighborSet]

/-- FO-325. The open neighbourhood is the closed one without `v`. -/
@[kb "levin2025" "Exercise 2.1.5.11, p. 134"]
theorem levin_ex_2_1_5_11_neighborSet_eq_diff (G : SimpleGraph V) (v : V) :
    G.neighborSet v = closedNeighborSet G v \ {v} := by
  ext w
  simp only [closedNeighborSet, Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff,
    mem_neighborSet]
  constructor
  · intro h
    exact ⟨Or.inr h, (G.ne_of_adj h).symm⟩
  · rintro ⟨h | h, hne⟩
    · exact absurd h hne
    · exact h

/-- FO-325. In a finite graph, `|N[v]| = deg v + 1`. -/
@[kb "levin2025" "Exercise 2.1.5.11, p. 134"]
theorem levin_ex_2_1_5_11_card_closedNeighborSet [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) :
    (closedNeighborSet G v).ncard = G.degree v + 1 := by
  classical
  have : closedNeighborSet G v = ↑(insert v (G.neighborFinset v)) := by
    ext w; simp [closedNeighborSet]
  rw [this, Set.ncard_coe_finset, Finset.card_insert_of_notMem (by simp), card_neighborFinset_eq_degree]

/-! ### Edge colourings -/

/-- A proper edge colouring with colours in `α`: edges sharing an endpoint get different colours. -/
def IsProperEdgeColoring (G : SimpleGraph V) {α : Type*} (c : G.edgeSet → α) : Prop :=
  ∀ e e' : G.edgeSet, e ≠ e' → (∃ v, v ∈ e.1 ∧ v ∈ e'.1) → c e ≠ c e'

/-- `G` has a proper edge colouring using `n` colours. -/
def EdgeColorable (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ c : G.edgeSet → Fin n, IsProperEdgeColoring G c

/-- The chromatic index `χ'(G)`: the least number of colours in a proper edge colouring
(`⊤` if there is none). -/
noncomputable def chromaticIndex (G : SimpleGraph V) : ℕ∞ :=
  ⨅ n : {n : ℕ // EdgeColorable G n}, (n.1 : ℕ∞)

/-- FO-358. A proper edge colouring with `n` colours forces `Δ(G) ≤ n`. -/
@[kb "levin2025" "Text §2.5, p. 177"]
theorem levin_s2_5_maxDegree_le_of_edgeColorable [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {n : ℕ} (h : EdgeColorable G n) : G.maxDegree ≤ n := by
  obtain ⟨c, hc⟩ := h
  refine G.maxDegree_le_of_forall_degree_le n fun v => ?_
  classical
  rw [← card_incidenceSet_eq_degree]
  have hinj : Function.Injective
      (fun e : G.incidenceSet v => c ⟨e.1, G.incidenceSet_subset v e.2⟩) := by
    intro e e' hee
    by_contra hne
    refine hc ⟨e.1, G.incidenceSet_subset v e.2⟩ ⟨e'.1, G.incidenceSet_subset v e'.2⟩
      (fun h => hne (Subtype.ext (Subtype.mk.inj h))) ⟨v, e.2.2, e'.2.2⟩ hee
  simpa using Fintype.card_le_of_injective _ hinj

/-- FO-358. The chromatic index is at least the maximum degree: `χ'(G) ≥ Δ(G)`. -/
@[kb "levin2025" "Text §2.5, p. 177"]
theorem levin_s2_5_maxDegree_le_chromaticIndex [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : (G.maxDegree : ℕ∞) ≤ chromaticIndex G := by
  unfold chromaticIndex
  refine le_iInf fun n => ?_
  exact_mod_cast levin_s2_5_maxDegree_le_of_edgeColorable G n.2

/-! ### Alternating and augmenting paths -/

/-- A walk is alternating for a matching `M` when consecutive edges alternate between lying in
`M` and not lying in `M`. -/
def IsAlternatingWalk {G : SimpleGraph V} (M : G.Subgraph) {u v : V} (p : G.Walk u v) : Prop :=
  List.IsChain (fun e e' => (e ∈ M.edgeSet) ≠ (e' ∈ M.edgeSet)) p.edges

/-- An augmenting path: an alternating path with at least one edge whose first and last edges
are not in the matching. -/
def IsAugmentingPath {G : SimpleGraph V} (M : G.Subgraph) {u v : V} (p : G.Walk u v) : Prop :=
  p.IsPath ∧ IsAlternatingWalk M p ∧ p.edges ≠ [] ∧
    p.edges.head? ∉ ({some e | e ∈ M.edgeSet} : Set (Option (Sym2 V))) ∧
    p.edges.getLast? ∉ ({some e | e ∈ M.edgeSet} : Set (Option (Sym2 V)))

/-- Reversing an alternating walk gives an alternating walk. -/
theorem IsAlternatingWalk.reverse {G : SimpleGraph V} {M : G.Subgraph} {u v : V}
    {p : G.Walk u v} (h : IsAlternatingWalk M p) : IsAlternatingWalk M p.reverse := by
  unfold IsAlternatingWalk at *
  rw [SimpleGraph.Walk.edges_reverse, List.isChain_reverse]
  exact h.imp fun a b hab => hab.symm

/-- Parity along an alternating list: the last edge is in the matching iff the first is and the
list has an odd number of further steps... precisely, iff `P a ↔ Even (length l)`. -/
theorem alternating_last_iff {α : Type*} (P : α → Prop) :
    ∀ (l : List α) (a : α), List.IsChain (fun x y => P x ≠ P y) (a :: l) →
      (P ((a :: l).getLast (List.cons_ne_nil a l)) ↔ (P a ↔ Even l.length))
  | [], a, _ => by simp
  | b :: l', a, h => by
    have hab : P a ≠ P b := (List.isChain_cons_cons.1 h).1
    have ih := alternating_last_iff P l' b (List.isChain_cons_cons.1 h).2
    have hl : (a :: b :: l').getLast (List.cons_ne_nil _ _) =
        (b :: l').getLast (List.cons_ne_nil _ _) := by simp
    rw [hl, ih, List.length_cons, Nat.even_add_one]
    by_cases hp : P a <;> by_cases hq : P b <;> simp_all

/-- FO-363. An augmenting path has an odd number of edges. -/
@[kb "levin2025" "Exercise 2.7.3, p. 204"]
theorem levin_ex_2_7_3_augmenting_odd_length {G : SimpleGraph V} {M : G.Subgraph} {u v : V}
    {p : G.Walk u v} (h : IsAugmentingPath M p) : Odd p.edges.length := by
  obtain ⟨-, halt, hne, hhead, hlast⟩ := h
  unfold IsAlternatingWalk at halt
  obtain ⟨a, l, hal⟩ := List.exists_cons_of_ne_nil hne
  rw [hal] at halt hhead hlast ⊢
  have key := alternating_last_iff (fun e => e ∈ M.edgeSet) l a halt
  have h1 : a ∉ M.edgeSet := fun h => hhead ⟨a, h, by simp⟩
  have h2 : (a :: l).getLast (List.cons_ne_nil a l) ∉ M.edgeSet := fun h =>
    hlast ⟨_, h, by simp [List.getLast?_eq_getLast_of_ne_nil (List.cons_ne_nil a l)]⟩
  have : Even l.length := by
    by_contra he
    exact h2 (key.2 (iff_of_false h1 he))
  rw [List.length_cons]
  exact this.add_one

/-! ### Regular polyhedra: the arithmetic core -/

/-- FO-344. For integers `p, q ≥ 3`, `1/p + 1/q > 1/2` holds exactly for the five pairs
`(3,3), (3,4), (4,3), (3,5), (5,3)` (the Platonic solids' face and vertex sizes). -/
@[kb "levin2025" "Thm 2.3.7, p. 156"]
theorem levin_thm_2_3_7_platonic_pairs (p q : ℕ) (hp : 3 ≤ p) (hq : 3 ≤ q) :
    (1 : ℚ) / p + 1 / q > 1 / 2 ↔
      (p, q) = (3, 3) ∨ (p, q) = (3, 4) ∨ (p, q) = (4, 3) ∨ (p, q) = (3, 5) ∨ (p, q) = (5, 3) := by
  have hp' : (0 : ℚ) < p := by exact_mod_cast (by omega : 0 < p)
  have hq' : (0 : ℚ) < q := by exact_mod_cast (by omega : 0 < q)
  have key : (1 : ℚ) / p + 1 / q > 1 / 2 ↔ p * q < 2 * (p + q) := by
    have e : (1 : ℚ) / p + 1 / q - 1 / 2 = (2 * (p + q) - p * q) / (2 * p * q) := by
      field_simp
      ring
    have hpq : (0 : ℚ) < 2 * p * q := by
      have := mul_pos hp' hq'
      linarith
    rw [gt_iff_lt, ← sub_pos, e]
    constructor
    · intro h
      have h1 : 0 < 2 * ((p : ℚ) + q) - p * q := by
        by_contra hn
        rw [not_lt] at hn
        have := div_nonpos_of_nonpos_of_nonneg hn hpq.le
        linarith
      have : (p : ℚ) * q < 2 * (p + q) := by linarith
      exact_mod_cast this
    · intro h
      have : (p : ℚ) * q < 2 * (p + q) := by exact_mod_cast h
      exact div_pos (by linarith) hpq
  rw [key]
  constructor
  · intro h
    have hp5 : p ≤ 5 := by nlinarith
    have hq5 : q ≤ 5 := by nlinarith
    interval_cases p <;> interval_cases q <;> simp_all
  · rintro (h | h | h | h | h) <;> simp only [Prod.mk.injEq] at h <;> rcases h with ⟨rfl, rfl⟩ <;> norm_num

end UndergradKB.Foundations
