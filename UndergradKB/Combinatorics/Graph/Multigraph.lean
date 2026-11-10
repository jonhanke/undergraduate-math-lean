import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Sym.Sym2
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.Graph.Euler

/-!
# Multigraphs and Euler's theorem for loopless multigraphs

Source: Keller--Trotter, *Applied Combinatorics* (2017), Section 5.2 (multigraphs, p. 98) and the
remark after Theorem 5.13 (p. 102).

A multigraph is given by a type of vertices, a type of edges, and an endpoint map to `Sym2 V`
(a loop is an edge whose endpoint pair is on the diagonal).  Euler's theorem for loopless
multigraphs is deduced from the simple graph version by subdividing every edge.
-/

namespace UndergradKB.Combinatorics

open SimpleGraph

open scoped Classical

/-- CO-093. A multigraph: loops and parallel edges are allowed.  An edge `e` has the unordered
pair `ends e` of endpoints (a loop has both ends equal). -/
@[kb "kellertrotter2017" "Definition (unnumbered) multigraph, p. 98"]
structure Multigraph (V E : Type*) where
  /-- The endpoints of an edge. -/
  ends : E → Sym2 V

namespace Multigraph

variable {V E : Type*} (M : Multigraph V E)

/-- A multigraph is loopless if no edge has both ends equal. -/
def Loopless : Prop := ∀ e, ¬ (M.ends e).IsDiag

/-- The degree of a vertex: the number of edge ends at it (a loop counts twice). -/
noncomputable def degree [Fintype E] (v : V) : ℕ := ∑ e, (M.ends e).toMultiset.count v

/-- The underlying simple graph: two distinct vertices are adjacent iff some edge joins them. -/
def underlying : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ e, M.ends e = s(u, v)
  symm := ⟨fun _ _ h => ⟨h.1.symm, by
    obtain ⟨e, he⟩ := h.2
    exact ⟨e, by rw [he, Sym2.eq_swap]⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- A multigraph is connected if its underlying simple graph is. -/
def Connected : Prop := M.underlying.Connected

/-- A multigraph is *eulerian* (book's definition, for multigraphs): there is a closed sequence of
vertices `x 0, ..., x n = x 0` and edges `e 0, ..., e (n-1)` with `e i` joining `x i` and
`x (i+1)`, such that every edge occurs as `e i` for exactly one index `i`. -/
def IsEulerian : Prop :=
  ∃ (n : ℕ) (x : Fin (n + 1) → V) (e : Fin n → E), x (Fin.last n) = x 0 ∧
    (∀ i : Fin n, M.ends (e i) = s(x i.castSucc, x i.succ)) ∧ ∀ ε : E, ∃! i, e i = ε

/-! ### The subdivision graph -/

/-- The subdivision: a simple graph on `V ⊕ E` where an edge-vertex is adjacent to its ends. -/
def subdivision : SimpleGraph (V ⊕ E) where
  Adj a b := match a, b with
    | Sum.inl v, Sum.inr e => v ∈ M.ends e
    | Sum.inr e, Sum.inl v => v ∈ M.ends e
    | _, _ => False
  symm := ⟨fun a b h => by
    rcases a with a | a <;> rcases b with b | b <;> simp_all⟩
  loopless := ⟨fun a h => by rcases a with a | a <;> simp_all⟩

@[simp] lemma subdivision_adj_inl_inr {v : V} {e : E} :
    M.subdivision.Adj (Sum.inl v) (Sum.inr e) ↔ v ∈ M.ends e := Iff.rfl

@[simp] lemma subdivision_adj_inr_inl {v : V} {e : E} :
    M.subdivision.Adj (Sum.inr e) (Sum.inl v) ↔ v ∈ M.ends e := Iff.rfl

@[simp] lemma subdivision_adj_inl_inl {u v : V} : ¬ M.subdivision.Adj (Sum.inl u) (Sum.inl v) :=
  fun h => h

@[simp] lemma subdivision_adj_inr_inr {d e : E} : ¬ M.subdivision.Adj (Sum.inr d) (Sum.inr e) :=
  fun h => h

lemma count_toMultiset_of_not_isDiag {z : Sym2 V} (hz : ¬ z.IsDiag) (v : V) :
    z.toMultiset.count v = if v ∈ z then 1 else 0 := by
  induction z using Sym2.ind with
  | _ a b =>
    rw [Sym2.mk_isDiag_iff] at hz
    simp only [Sym2.toMultiset, Sym2.lift_mk, Multiset.coe_count]
    by_cases ha : v = a
    · subst ha
      simp [hz]
    · by_cases hb : v = b
      · subst hb
        simp [Ne.symm hz, Ne.symm ha]
      · simp [ha, hb, Ne.symm ha, Ne.symm hb]

variable [Fintype V] [Fintype E]

omit [Fintype V] in
lemma degree_eq_card (hM : M.Loopless) (v : V) :
    M.degree v = (Finset.univ.filter fun e => v ∈ M.ends e).card := by
  rw [Finset.card_filter, degree]
  exact Finset.sum_congr rfl fun e _ => count_toMultiset_of_not_isDiag (hM e) v

lemma subdivision_degree_inl (v : V) :
    M.subdivision.degree (Sum.inl v) = (Finset.univ.filter fun e => v ∈ M.ends e).card := by
  rw [← card_neighborFinset_eq_degree]
  have : M.subdivision.neighborFinset (Sum.inl v) =
      (Finset.univ.filter fun e => v ∈ M.ends e).map ⟨Sum.inr, Sum.inr_injective⟩ := by
    ext x
    rcases x with x | x <;> simp
  rw [this, Finset.card_map]

lemma subdivision_degree_inr (hM : M.Loopless) (e : E) :
    M.subdivision.degree (Sum.inr e) = 2 := by
  rw [← card_neighborFinset_eq_degree]
  have : M.subdivision.neighborFinset (Sum.inr e) =
      (M.ends e).toFinset.map ⟨Sum.inl, Sum.inl_injective⟩ := by
    ext x
    rcases x with x | x <;> simp
  rw [this, Finset.card_map, Sym2.card_toFinset_of_not_isDiag _ (hM e)]

omit [Fintype V] [Fintype E] in
lemma subdivision_connected (hc : M.Connected) : M.subdivision.Connected := by
  have lift : ∀ u v, M.underlying.Adj u v → M.subdivision.Reachable (Sum.inl u) (Sum.inl v) := by
    rintro u v ⟨_, e, he⟩
    have hu : u ∈ M.ends e := by rw [he]; exact Sym2.mem_mk_left _ _
    have hv : v ∈ M.ends e := by rw [he]; exact Sym2.mem_mk_right _ _
    exact (Adj.reachable (M.subdivision_adj_inl_inr.2 hu)).trans
      (Adj.reachable (M.subdivision_adj_inr_inl.2 hv))
  have key : ∀ u v, M.underlying.Reachable u v → M.subdivision.Reachable (Sum.inl u) (Sum.inl v) := by
    rintro u v ⟨p⟩
    induction p with
    | nil => exact Reachable.refl _
    | cons h _ ih => exact (lift _ _ h).trans ih
  have near : ∀ a : V ⊕ E, ∃ v, M.subdivision.Reachable a (Sum.inl v) := by
    rintro (a | e)
    · exact ⟨a, Reachable.refl _⟩
    · obtain ⟨v, hv⟩ : ∃ v, v ∈ M.ends e := ⟨(M.ends e).out.1, Sym2.out_fst_mem _⟩
      exact ⟨v, Adj.reachable (M.subdivision_adj_inr_inl.2 hv)⟩
  exact { preconnected := fun a b => by
            obtain ⟨u, hu⟩ := near a
            obtain ⟨v, hv⟩ := near b
            exact hu.trans ((key u v (hc.preconnected u v)).trans hv.symm)
          nonempty := ⟨Sum.inl hc.nonempty.some⟩ }

omit [Fintype V] [Fintype E] in
lemma sym2_eq_of_mem {z : Sym2 V} (hz : ¬ z.IsDiag) {u w : V} (hu : u ∈ z) (hw : w ∈ z)
    (huw : u ≠ w) : z = s(u, w) := by
  induction z using Sym2.ind with
  | _ a b =>
    rw [Sym2.mk_isDiag_iff] at hz
    rw [Sym2.mem_iff] at hu hw
    rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
    · exact absurd rfl huw
    · rfl
    · exact Sym2.eq_swap
    · exact absurd rfl huw

/-- An Euler circuit of the subdivision graph, starting at a vertex of `M`, gives an Euler
circuit of the loopless multigraph `M`. -/
theorem isEulerian_of_subdivision_walk (hM : M.Loopless) {a : V}
    (p : M.subdivision.Walk (Sum.inl a) (Sum.inl a)) (hp : p.IsEulerian) : M.IsEulerian := by
  have hT : p.edges.Nodup := hp.isTrail.edges_nodup
  have par : ∀ i, i ≤ p.length → ((∃ v, p.getVert i = Sum.inl v) ∧ Even i) ∨
      ((∃ ε, p.getVert i = Sum.inr ε) ∧ Odd i) := by
    intro i
    induction i with
    | zero => intro _; left; exact ⟨⟨a, p.getVert_zero⟩, ⟨0, rfl⟩⟩
    | succ i ih =>
      intro hi
      have h := p.adj_getVert_succ (show i < p.length by omega)
      rcases ih (by omega) with ⟨⟨v, hv⟩, he⟩ | ⟨⟨ε, hε⟩, ho⟩
      · rw [hv] at h
        rcases hx : p.getVert (i + 1) with w | ε
        · rw [hx] at h; exact absurd h (by simp)
        · right; exact ⟨⟨ε, rfl⟩, he.add_one⟩
      · rw [hε] at h
        rcases hx : p.getVert (i + 1) with w | ε'
        · left; exact ⟨⟨w, rfl⟩, ho.add_one⟩
        · rw [hx] at h; exact absurd h (by simp)
  obtain ⟨n, hn⟩ : ∃ n, p.length = 2 * n := by
    rcases par p.length le_rfl with ⟨_, he⟩ | ⟨⟨ε, h⟩, _⟩
    · obtain ⟨k, hk⟩ := he; exact ⟨k, by omega⟩
    · rw [p.getVert_length] at h; simp at h
  have hev : ∀ i, 2 * i ≤ p.length → ∃ v, p.getVert (2 * i) = Sum.inl v := by
    intro i hi
    rcases par (2 * i) hi with ⟨h, _⟩ | ⟨_, ⟨k, hk⟩⟩
    · exact h
    · omega
  have hod : ∀ i, 2 * i + 1 ≤ p.length → ∃ ε, p.getVert (2 * i + 1) = Sum.inr ε := by
    intro i hi
    rcases par (2 * i + 1) hi with ⟨_, ⟨k, hk⟩⟩ | ⟨h, _⟩
    · omega
    · exact h
  let x : Fin (n + 1) → V := fun i => Classical.choose (hev i.1 (by have := i.2; omega))
  let e : Fin n → E := fun i => Classical.choose (hod i.1 (by have := i.2; omega))
  have hx : ∀ i : Fin (n + 1), p.getVert (2 * i.val) = Sum.inl (x i) := fun i =>
    Classical.choose_spec (hev i.1 (by have := i.2; omega))
  have he : ∀ i : Fin n, p.getVert (2 * i.val + 1) = Sum.inr (e i) := fun i =>
    Classical.choose_spec (hod i.1 (by have := i.2; omega))
  have hx0 : ∀ i : Fin n, p.getVert (2 * i.val) = Sum.inl (x i.castSucc) := fun i => by
    have h := hx i.castSucc
    rwa [Fin.val_castSucc] at h
  have hx1 : ∀ i : Fin n, p.getVert (2 * i.val + 1 + 1) = Sum.inl (x i.succ) := fun i => by
    have h := hx i.succ
    rwa [Fin.val_succ, show 2 * (i.val + 1) = 2 * i.val + 1 + 1 by omega] at h
  have hlen : p.edges.length = 2 * n := by rw [p.length_edges, hn]
  have hE0 : ∀ i : Fin n, ∃ h : 2 * i.val < p.edges.length,
      p.edges[2 * i.val] = s(Sum.inl (x i.castSucc), Sum.inr (e i)) := by
    intro i
    have h : 2 * i.val < p.edges.length := by have := i.2; omega
    exact ⟨h, by rw [SimpleGraph.Walk.getElem_edges h, hx0 i, he i]⟩
  have hE1 : ∀ i : Fin n, ∃ h : 2 * i.val + 1 < p.edges.length,
      p.edges[2 * i.val + 1] = s(Sum.inr (e i), Sum.inl (x i.succ)) := by
    intro i
    have h : 2 * i.val + 1 < p.edges.length := by have := i.2; omega
    exact ⟨h, by rw [SimpleGraph.Walk.getElem_edges h, he i, hx1 i]⟩
  have hmem1 : ∀ i : Fin n, x i.castSucc ∈ M.ends (e i) := fun i => by
    have h := p.adj_getVert_succ (show 2 * i.val < p.length by have := i.2; omega)
    rwa [hx0 i, he i] at h
  have hmem2 : ∀ i : Fin n, x i.succ ∈ M.ends (e i) := fun i => by
    have h := p.adj_getVert_succ (show 2 * i.val + 1 < p.length by have := i.2; omega)
    rwa [he i, hx1 i] at h
  have hne : ∀ i : Fin n, x i.castSucc ≠ x i.succ := by
    intro i heq
    obtain ⟨h0, e0⟩ := hE0 i
    obtain ⟨h1, e1⟩ := hE1 i
    have : p.edges[2 * i.val] = p.edges[2 * i.val + 1] := by
      rw [e0, e1, heq, Sym2.eq_swap]
    have := (hT.getElem_inj_iff).1 this
    omega
  have hends : ∀ i : Fin n, M.ends (e i) = s(x i.castSucc, x i.succ) := fun i =>
    sym2_eq_of_mem (hM _) (hmem1 i) (hmem2 i) (hne i)
  refine ⟨n, x, e, ?_, hends, fun ε => ?_⟩
  · have h1 := hx (Fin.last n)
    have h2 := hx 0
    rw [Fin.val_last, ← hn, p.getVert_length] at h1
    rw [Fin.val_zero, Nat.mul_zero, p.getVert_zero] at h2
    exact Sum.inl_injective (h1.symm.trans h2)
  · have huniq : ∀ i i' : Fin n, e i = e i' → i = i' := by
      intro i i' h
      have hu' : x i'.castSucc ∈ s(x i.castSucc, x i.succ) := by
        rw [← hends i, h]; exact hmem1 i'
      have hw' : x i'.succ ∈ s(x i.castSucc, x i.succ) := by
        rw [← hends i, h]; exact hmem2 i'
      rw [Sym2.mem_iff] at hu' hw'
      obtain ⟨h0, e0⟩ := hE0 i
      obtain ⟨h0', e0'⟩ := hE0 i'
      obtain ⟨h1', e1'⟩ := hE1 i'
      rcases hu' with hu' | hu'
      · have h5 : p.edges[2 * i'.val] = p.edges[2 * i.val] := by
          rw [e0, e0', hu', h]
        have := (hT.getElem_inj_iff).1 h5
        exact Fin.ext (by omega)
      · rcases hw' with hw' | hw'
        · have h5 : p.edges[2 * i'.val + 1] = p.edges[2 * i.val] := by
            rw [e1', e0, hw', h, Sym2.eq_swap]
          have := (hT.getElem_inj_iff).1 h5
          omega
        · exact absurd (hu'.trans hw'.symm) (hne i')
    have hex : ∃ i, e i = ε := by
      obtain ⟨v, hv⟩ : ∃ v, v ∈ M.ends ε := ⟨(M.ends ε).out.1, Sym2.out_fst_mem _⟩
      have hadj : M.subdivision.Adj (Sum.inl v) (Sum.inr ε) := hv
      have hin : s(Sum.inl v, Sum.inr ε) ∈ p.edges := hp.mem_edges_iff.2 hadj
      obtain ⟨j, hj, hjeq⟩ := (SimpleGraph.Walk.mk_mem_edges_iff_exists p).1 hin
      obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' j
      · rw [Sym2.eq_iff] at hjeq
        have hk : k < n := by omega
        rcases hjeq with ⟨-, h2⟩ | ⟨h1, -⟩
        · have h3 := he ⟨k, hk⟩
          simp only at h3
          rw [h3] at h2
          exact ⟨⟨k, hk⟩, Sum.inr_injective h2⟩
        · have h3 := hx ⟨k, by omega⟩
          simp only at h3
          rw [h3] at h1
          exact absurd h1 (by simp)
      · rw [Sym2.eq_iff] at hjeq
        have hk : k < n := by omega
        rcases hjeq with ⟨h1, -⟩ | ⟨h1, -⟩
        · have h3 := he ⟨k, hk⟩
          simp only at h3
          rw [h3] at h1
          exact absurd h1 (by simp)
        · have h3 := he ⟨k, hk⟩
          simp only at h3
          rw [h3] at h1
          exact ⟨⟨k, hk⟩, Sum.inr_injective h1⟩
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, hi, fun i' hi' => huniq i' i (hi'.trans hi.symm)⟩

/-- CO-099 (with CO-093). Theorem 5.13 for loopless multigraphs: a finite connected loopless
multigraph all of whose vertices have even degree is eulerian (there is a closed trail using each
edge exactly once). -/
@[kb "kellertrotter2017" "text, p. 102"]
theorem isEulerian_of_even_degree (hM : M.Loopless) (hc : M.Connected)
    (he : ∀ v, Even (M.degree v)) : M.IsEulerian := by
  have hconn := M.subdivision_connected hc
  obtain ⟨v0⟩ := hc.nonempty
  have hdeg : ∀ y, Even (M.subdivision.degree y) := by
    rintro (v | e)
    · rw [M.subdivision_degree_inl, ← M.degree_eq_card hM]; exact he v
    · rw [M.subdivision_degree_inr hM]; exact even_two
  obtain ⟨p, hp, -⟩ := Euler.exists_eulerian_trail_between hconn (Sum.inl v0) (Sum.inl v0) (by
    intro y
    constructor
    · intro ho; exact absurd (hdeg y) (Nat.not_even_iff_odd.2 ho)
    · rintro ⟨h, -⟩; exact absurd rfl h)
  exact M.isEulerian_of_subdivision_walk hM p (by convert hp)

end Multigraph

end UndergradKB.Combinatorics
