import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Order.Lattice.Nat
import UndergradKB.Common.Attr

/-!
# Eulerian graphs (Keller–Trotter, Chapter 5.3)

A finite graph is eulerian iff it is connected and all degrees are even (Theorem 5.13).  The
necessity direction is in Mathlib; we prove sufficiency by the "longest trail and splice" argument:
a longest trail ending at `b` is saturated at its first vertex, hence (by parity) starts at the
other odd vertex (or closes up); if an edge were unused at a vertex of the trail, the unused edges
carry a closed trail through that vertex, which can be spliced into the longest trail.

The same argument gives Eulerian trails when there are at most two odd vertices (Exercise 5.9.11).
The proof is not the book's deterministic labelling algorithm (CO-267), but a non-constructive
extremal argument.
-/

namespace UndergradKB.Combinatorics.Euler

open SimpleGraph SimpleGraph.Walk

open scoped Classical

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- A trail has at most as many edges as the graph. -/
lemma trail_length_le {u v : V} (p : G.Walk u v) (hp : p.IsTrail) :
    p.length ≤ Nat.card G.edgeSet := by
  have : Fintype G.edgeSet := Fintype.ofFinite _
  rw [← p.length_edges, ← List.toFinset_card_of_nodup hp.edges_nodup, Nat.card_eq_fintype_card,
    ← G.edgeFinset_card]
  apply Finset.card_le_card
  intro e he
  simpa using p.edges_subset_edgeSet (List.mem_toFinset.mp he)

/-- There is a trail of maximum length among the trails ending at `b`. -/
lemma exists_longest_trail_to (G : SimpleGraph V) (b : V) :
    ∃ (y : V) (p : G.Walk y b), p.IsTrail ∧
      ∀ (y' : V) (q : G.Walk y' b), q.IsTrail → q.length ≤ p.length := by
  let S : Set ℕ := {n | ∃ (y : V) (p : G.Walk y b), p.IsTrail ∧ p.length = n}
  have hne : S.Nonempty := ⟨0, b, Walk.nil, by simp, rfl⟩
  have hb : BddAbove S := ⟨Nat.card G.edgeSet, by
    rintro n ⟨u, p, hp, rfl⟩
    exact trail_length_le p hp⟩
  obtain ⟨u, p, hp, hl⟩ := Nat.sSup_mem hne hb
  refine ⟨u, p, hp, fun u' q hq => ?_⟩
  rw [hl]
  exact le_csSup hb ⟨u', q, hq, rfl⟩

/-- If every edge of `G` at `x` lies on the trail `p`, then the number of edges of `p` at `x`
is the degree of `x`. -/
lemma countP_eq_degree [DecidableRel G.Adj] {u v : V} (p : G.Walk u v) (hp : p.IsTrail) {x : V}
    (hsat : ∀ y, G.Adj x y → s(x, y) ∈ p.edges) :
    p.edges.countP (fun e => x ∈ e) = G.degree x := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hp.edges_nodup.filter _),
    ← card_incidenceFinset_eq_degree]
  congr 1
  ext e
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, mem_incidenceFinset]
  constructor
  · rintro ⟨he, hx⟩
    exact ⟨p.edges_subset_edgeSet he, hx⟩
  · rintro ⟨he, hx⟩
    induction e using Sym2.ind with
    | _ a b =>
      rcases Sym2.mem_iff.mp hx with rfl | rfl
      · exact ⟨hsat _ he, hx⟩
      · rw [Sym2.eq_swap]; exact ⟨hsat _ he.symm, by simp⟩

/-- If an odd number of edges of a trail are at a vertex of even degree, some edge at the vertex
is unused. -/
lemma exists_unused_edge [DecidableRel G.Adj] {u v : V} (p : G.Walk u v) (hp : p.IsTrail) {x : V}
    (hd : Even (G.degree x)) (hodd : ¬ Even (p.edges.countP fun e => x ∈ e)) :
    ∃ y, G.Adj x y ∧ s(x, y) ∉ p.edges := by
  by_contra hcon
  push Not at hcon
  exact hodd (by rw [countP_eq_degree p hp hcon]; exact hd)

/-- In a longest trail `p` ending at `b`, every edge at the first vertex lies on `p`. -/
lemma front_saturated {u b : V} (p : G.Walk u b) (hp : p.IsTrail)
    (hmax : ∀ (u' : V) (q : G.Walk u' b), q.IsTrail → q.length ≤ p.length) :
    ∀ y, G.Adj u y → s(u, y) ∈ p.edges := by
  intro y hy
  by_contra hn
  have h := hmax _ (Walk.cons hy.symm p) (by
    rw [isTrail_cons]
    exact ⟨hp, by rwa [Sym2.eq_swap]⟩)
  simp at h

/-- In a finite graph all of whose degrees are even, a vertex with an edge lies on a nonempty
closed trail. -/
lemma exists_closed_trail [DecidableRel G.Adj] (he : ∀ v, Even (G.degree v)) (b : V)
    (hb : ∃ w, G.Adj b w) : ∃ r : G.Walk b b, r.IsTrail ∧ 0 < r.length := by
  obtain ⟨y, p, hp, hmax⟩ := exists_longest_trail_to G b
  have hfront := front_saturated p hp hmax
  have hyb : y = b := by
    by_contra hne
    have hodd : ¬ Even (p.edges.countP fun e => y ∈ e) := by
      rw [hp.even_countP_edges_iff]
      intro h
      exact (h hne).1 rfl
    obtain ⟨z, hz, hn⟩ := exists_unused_edge p hp (he y) hodd
    exact hn (hfront z hz)
  subst hyb
  obtain ⟨w, hw⟩ := hb
  refine ⟨p, hp, ?_⟩
  have h1 := hmax w (Walk.cons hw.symm Walk.nil) (by simp [isTrail_cons])
  have h2 : 1 ≤ p.length := by simpa using h1
  omega

/-- The number of edges at `x` not on the trail `p`. -/
lemma degree_deleteEdges [DecidableRel G.Adj] {u v : V} (p : G.Walk u v) (hp : p.IsTrail) (x : V)
    [DecidableRel (G.deleteEdges {e | e ∈ p.edges}).Adj] :
    (G.deleteEdges {e | e ∈ p.edges}).degree x + p.edges.countP (fun e => x ∈ e) =
      G.degree x := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hp.edges_nodup.filter _),
    ← card_incidenceFinset_eq_degree, ← card_incidenceFinset_eq_degree,
    ← Finset.card_union_of_disjoint]
  · congr 1
    ext e
    simp only [Finset.mem_union, mem_incidenceFinset, List.mem_toFinset, List.mem_filter,
      decide_eq_true_eq, incidenceSet, Set.mem_ofPred_eq, edgeSet_deleteEdges, Set.mem_sdiff]
    constructor
    · rintro (⟨⟨he, hn⟩, hx⟩ | ⟨he, hx⟩)
      · exact ⟨he, hx⟩
      · exact ⟨p.edges_subset_edgeSet he, hx⟩
    · rintro ⟨he, hx⟩
      by_cases hm : e ∈ p.edges
      · exact Or.inr ⟨hm, hx⟩
      · exact Or.inl ⟨⟨he, hm⟩, hx⟩
  · rw [Finset.disjoint_left]
    intro e h1 h2
    simp only [mem_incidenceFinset, List.mem_toFinset, List.mem_filter, decide_eq_true_eq,
      incidenceSet, Set.mem_ofPred_eq, edgeSet_deleteEdges, Set.mem_sdiff] at h1 h2
    exact h1.1.2 h2.1

/-- CO-098 (sufficiency half, in a general form also giving CO-124).  Let `G` be a finite
connected graph whose odd-degree vertices are exactly `a` and `b` (when `a ≠ b`), or which has no
odd-degree vertex (when `a = b`).  Then there is a trail from `a` to `b` using every edge exactly
once and passing through every vertex. -/
theorem exists_eulerian_trail_between [DecidableRel G.Adj] (hc : G.Connected) (a b : V)
    (hodd : ∀ x, Odd (G.degree x) ↔ (a ≠ b ∧ (x = a ∨ x = b))) :
    ∃ p : G.Walk a b, p.IsEulerian ∧ ∀ v, v ∈ p.support := by
  have : Nonempty V := hc.nonempty
  have hpar : ∀ x, Even (G.degree x) ↔ (a ≠ b → x ≠ a ∧ x ≠ b) := by
    intro x
    rw [← Nat.not_odd_iff_even, hodd]
    tauto
  obtain ⟨y, p, hp, hmax⟩ := exists_longest_trail_to G b
  have hfront := front_saturated p hp hmax
  -- the longest trail starts at `a`
  have hya : y = a := by
    by_cases hyb : y = b
    · subst hyb
      have hev : Even (p.edges.countP fun e => y ∈ e) := by
        rw [hp.even_countP_edges_iff]; intro h; exact absurd rfl h
      rw [countP_eq_degree p hp hfront, hpar] at hev
      by_contra hne
      exact (hev (Ne.symm hne)).2 rfl
    · by_contra hya
      have hodd' : ¬ Even (p.edges.countP fun e => y ∈ e) := by
        rw [hp.even_countP_edges_iff]
        intro h
        exact (h hyb).1 rfl
      have hd : Even (G.degree y) := (hpar y).mpr fun _ => ⟨hya, hyb⟩
      obtain ⟨z, hz, hn⟩ := exists_unused_edge p hp hd hodd'
      exact hn (hfront z hz)
  subst hya
  -- every edge at a vertex of the trail is on the trail
  by_cases hall : ∀ d ∈ p.support, ∀ c, G.Adj d c → s(d, c) ∈ p.edges
  · have hsupp : ∀ d ∈ p.support, ∀ c, G.Adj d c → c ∈ p.support :=
      fun d hd c hdc => p.snd_mem_support_of_mem_edges (hall d hd c hdc)
    have hallv : ∀ w, w ∈ p.support := by
      intro w
      obtain ⟨q⟩ := hc.preconnected y w
      have key : ∀ {s t : V} (q : G.Walk s t), s ∈ p.support → t ∈ p.support := by
        intro s t q
        induction q with
        | nil => exact id
        | cons h _ ih => exact fun hs => ih (hsupp _ hs _ h)
      exact key q p.start_mem_support
    refine ⟨p, hp.isEulerian_of_forall_mem ?_, hallv⟩
    intro e he'
    induction e using Sym2.ind with
    | _ a b => exact hall a (hallv a) b he'
  · exfalso
    push Not at hall
    obtain ⟨d, hd, c, hdc, hn⟩ := hall
    -- the unused edges have all degrees even
    set H := G.deleteEdges {e | e ∈ p.edges} with hH
    have hevenH : ∀ x, Even (H.degree x) := by
      intro x
      have h1 := degree_deleteEdges p hp x
      have h2 : Even (p.edges.countP fun e => x ∈ e) ↔ (y ≠ b → x ≠ y ∧ x ≠ b) :=
        hp.even_countP_edges_iff x
      have h3 := hpar x
      have h4 : Even (H.degree x + p.edges.countP fun e => x ∈ e) ↔
          (Even (H.degree x) ↔ Even (p.edges.countP fun e => x ∈ e)) := Nat.even_add
      rw [h1] at h4
      tauto
    have hHadj : H.Adj d c := by
      rw [hH, deleteEdges_adj]
      exact ⟨hdc, hn⟩
    obtain ⟨r, hr, hrlen⟩ := exists_closed_trail hevenH d ⟨c, hHadj⟩
    let r' : G.Walk d d := r.mapLe (by rw [hH]; exact deleteEdges_le _)
    have hr'edges : r'.edges = r.edges := edges_mapLe_eq_edges _ r
    have hr'trail : r'.IsTrail := hr.mapLe _
    have hr'len : r'.length = r.length := by simp [r']
    have hdisj : ∀ e ∈ r'.edges, e ∉ p.edges := by
      intro e he hep
      rw [hr'edges] at he
      have := r.edges_subset_edgeSet he
      rw [hH, edgeSet_deleteEdges] at this
      exact this.2 hep
    let p1 := p.takeUntil d hd
    let p2 := p.dropUntil d hd
    have hspec : p1.append p2 = p := take_spec p hd
    have hpe : p.edges = p1.edges ++ p2.edges := by
      conv_lhs => rw [← hspec]
      rw [edges_append]
    let q : G.Walk y b := p1.append (r'.append p2)
    have hqedges : q.edges = p1.edges ++ (r'.edges ++ p2.edges) := by
      simp [q, edges_append]
    have hqtrail : q.IsTrail := by
      rw [isTrail_def, hqedges]
      have hnd : (p1.edges ++ p2.edges).Nodup := hpe ▸ hp.edges_nodup
      rw [List.nodup_append] at hnd ⊢
      obtain ⟨h1, h2, h12⟩ := hnd
      rw [List.nodup_append]
      refine ⟨h1, ?_, ?_⟩
      · refine ⟨hr'trail.edges_nodup, h2, fun e he f hf hef => ?_⟩
        exact hdisj e he (hef ▸ hpe ▸ List.mem_append_right _ hf)
      · intro e he f hf
        rcases List.mem_append.mp hf with hf | hf
        · intro hef
          exact hdisj f hf (hef ▸ hpe ▸ List.mem_append_left _ he)
        · exact h12 e he f hf
    have hlen := hmax y q hqtrail
    have : q.length = p.length + r.length := by
      have h1 : p.length = p1.length + p2.length := by
        conv_lhs => rw [← hspec]
        rw [length_append]
      simp only [q, length_append, hr'len]
      omega
    omega

/-- CO-098 (sufficiency half). A finite connected graph all of whose degrees are even has an
Euler circuit: a closed trail using every edge exactly once and passing through every vertex. -/
theorem exists_eulerian_circuit [DecidableRel G.Adj] (hc : G.Connected)
    (he : ∀ v, Even (G.degree v)) :
    ∃ (u : V) (p : G.Walk u u), p.IsEulerian ∧ ∀ v, v ∈ p.support := by
  obtain ⟨u⟩ := hc.nonempty
  obtain ⟨p, hp⟩ := exists_eulerian_trail_between hc u u (by
    intro x
    simpa using (Nat.not_even_iff_odd.symm.trans (not_iff_not.mpr (iff_of_true (he x) trivial))))
  exact ⟨u, p, hp⟩

/-- A graph is *eulerian* (book's definition) if it has an eulerian circuit: a closed walk using
every edge exactly once and passing through every vertex. -/
def IsEulerianGraph (G : SimpleGraph V) : Prop :=
  ∃ (u : V) (p : G.Walk u u), p.IsEulerian ∧ ∀ v, v ∈ p.support

/-- A walk using every edge exactly once and passing through every vertex (not nec. closed). -/
def HasEulerianTrail (G : SimpleGraph V) : Prop :=
  ∃ (u v : V) (p : G.Walk u v), p.IsEulerian ∧ ∀ w, w ∈ p.support

/-- A walk passing through every vertex shows that the graph is connected. -/
lemma connected_of_covering {u v : V} (p : G.Walk u v) (hall : ∀ w, w ∈ p.support) :
    G.Connected :=
  { preconnected := fun a b =>
      ⟨((p.takeUntil a (hall a)).reverse.append (p.takeUntil b (hall b)))⟩
    nonempty := ⟨u⟩ }

/-- CO-098. Theorem 5.13: a finite graph is eulerian iff it is connected and every vertex has
even degree. -/
@[kb "kellertrotter2017" "Theorem 5.13, p. 101"]
theorem isEulerianGraph_iff [DecidableRel G.Adj] :
    IsEulerianGraph G ↔ G.Connected ∧ ∀ v, Even (G.degree v) := by
  constructor
  · rintro ⟨u, p, hp, hall⟩
    exact ⟨connected_of_covering p hall, fun w => by simpa using hp.even_degree_iff (w := w)⟩
  · rintro ⟨hc, he⟩
    exact exists_eulerian_circuit hc he

/-- CO-098. An Euler circuit, when the graph has an edge, is a genuine circuit
(`SimpleGraph.Walk.IsCircuit`, i.e. a nonempty closed trail). -/
theorem exists_eulerian_isCircuit [DecidableRel G.Adj] (hc : G.Connected)
    (he : ∀ v, Even (G.degree v)) (hE : G.edgeSet.Nonempty) :
    ∃ (u : V) (p : G.Walk u u), p.IsEulerian ∧ p.IsCircuit ∧ ∀ v, v ∈ p.support := by
  obtain ⟨u, p, hp, hall⟩ := exists_eulerian_circuit hc he
  refine ⟨u, p, hp, ⟨hp.isTrail, ?_⟩, hall⟩
  rintro rfl
  obtain ⟨e, he⟩ := hE
  have := (hp.mem_edges_iff).mpr he
  simp at this

/-- CO-124. Exercise 5.9.11: a graph has an eulerian trail (a walk using every edge exactly once
and meeting every vertex) iff it is connected and has at most two vertices of odd degree. -/
@[kb "kellertrotter2017" "Exercise 5.9.11, p. 128"]
theorem hasEulerianTrail_iff [DecidableRel G.Adj] :
    HasEulerianTrail G ↔
      G.Connected ∧ (Finset.univ.filter fun v => Odd (G.degree v)).card ≤ 2 := by
  constructor
  · rintro ⟨u, v, p, hp, hall⟩
    refine ⟨connected_of_covering p hall, ?_⟩
    have := hp.card_filter_odd_degree (s := Finset.univ.filter fun v => Odd (G.degree v)) rfl
    omega
  · rintro ⟨hc, hcard⟩
    have hev := G.even_card_odd_degree_vertices
    set s := Finset.univ.filter fun v => Odd (G.degree v) with hs
    have hmem : ∀ x, x ∈ s ↔ Odd (G.degree x) := by simp [hs]
    have h01 : s.card = 0 ∨ s.card = 2 := by
      obtain ⟨k, hk⟩ := hev
      omega
    rcases h01 with h0 | h2
    · have he : ∀ v, Even (G.degree v) := by
        intro v
        rw [← Nat.not_odd_iff_even, ← hmem, Finset.card_eq_zero.mp h0]
        simp
      obtain ⟨u, p, hp⟩ := exists_eulerian_circuit hc he
      exact ⟨u, u, p, hp⟩
    · obtain ⟨a, b, hab, hsab⟩ := Finset.card_eq_two.mp h2
      obtain ⟨p, hp⟩ := exists_eulerian_trail_between hc a b (by
        intro x
        rw [← hmem, hsab]
        simp [hab])
      exact ⟨a, b, p, hp⟩

end UndergradKB.Combinatorics.Euler
