import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Set.Card
import UndergradKB.Common.Attr

/-!
# Elementary subdivisions and homeomorphic graphs (Keller–Trotter, Section 5.4)

Mathlib has no graph subdivision.  We model the elementary subdivision of an edge `uv` of
`G : SimpleGraph V` on the vertex type `Option V` (the new vertex is `none`).
-/

namespace UndergradKB.Combinatorics.Graph

open SimpleGraph

universe u

variable {V : Type u}

/-- CO-117. The elementary subdivision of the edge `uv` of `G`: a new vertex `none` is added, the
edge `uv` is removed and the edges `none–u`, `none–v` are added. -/
@[kb "kellertrotter2017" "Definition (elementary subdivision), p. 116"]
def elemSubdiv (G : SimpleGraph V) (u v : V) : SimpleGraph (Option V) :=
  SimpleGraph.fromEdgeSet
    (Sym2.map some '' (G.edgeSet \ {s(u, v)}) ∪ {s(none, some u), s(none, some v)})

theorem edgeSet_elemSubdiv (G : SimpleGraph V) (u v : V) :
    (elemSubdiv G u v).edgeSet =
      Sym2.map some '' (G.edgeSet \ {s(u, v)}) ∪ {s(none, some u), s(none, some v)} := by
  unfold elemSubdiv
  rw [edgeSet_fromEdgeSet]
  ext e
  simp only [Set.mem_sdiff, Set.mem_union, Set.mem_image, Set.mem_insert_iff,
    Set.mem_singleton_iff, ]
  constructor
  · exact fun h => h.1
  · refine fun h => ⟨h, ?_⟩
    rcases h with ⟨x, _, rfl⟩ | rfl | rfl
    · induction x using Sym2.ind with
      | h a b =>
        have : a ≠ b := fun hab => by simp_all
        simp [Sym2.map_mk, this]
    · simp
    · simp

/-- Adjacency of the subdivision at the new vertex. -/
theorem elemSubdiv_adj_none (G : SimpleGraph V) (u v w : V) (huv : G.Adj u v) :
    (elemSubdiv G u v).Adj none (some w) ↔ w = u ∨ w = v := by
  rw [← mem_edgeSet, edgeSet_elemSubdiv]
  simp only [Set.mem_union, Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (⟨x, _, hx⟩ | h | h)
    · induction x using Sym2.ind with
      | h a b => simp [Sym2.map_mk] at hx
    · simp at h; exact Or.inl h
    · simp at h; exact Or.inr h
  · rintro (rfl | rfl) <;> simp

/-- CO-117. The subdivided graph has one more vertex. -/
@[kb "kellertrotter2017" "Definition (elementary subdivision), p. 116"]
theorem card_elemSubdiv [Fintype V] (_G : SimpleGraph V) (_u _v : V) :
    Fintype.card (Option V) = Fintype.card V + 1 :=
  Fintype.card_option

/-- CO-117. The subdivided graph has one more edge (counted with `Set.ncard`). -/
@[kb "kellertrotter2017" "Definition (elementary subdivision), p. 116"]
theorem ncard_edgeSet_elemSubdiv [Finite V] (G : SimpleGraph V) (u v : V) (huv : G.Adj u v) :
    (elemSubdiv G u v).edgeSet.ncard = G.edgeSet.ncard + 1 := by
  have hu : u ≠ v := huv.ne
  have hfin : (G.edgeSet).Finite := Set.toFinite _
  have hmem : s(u, v) ∈ G.edgeSet := huv
  have h1 : (G.edgeSet \ {s(u, v)}).ncard + 1 = G.edgeSet.ncard := by
    have := Set.ncard_sdiff_singleton_add_one hmem hfin
    exact this
  have hne : s((none : Option V), some u) ≠ s(none, some v) := by
    simp [hu]
  have hdisj : Disjoint (Sym2.map some '' (G.edgeSet \ {s(u, v)}))
      {s((none : Option V), some u), s(none, some v)} := by
    rw [Set.disjoint_left]
    rintro e ⟨x, _, rfl⟩ he
    induction x using Sym2.ind with
    | h a b =>
      simp only [Sym2.map_mk, Set.mem_insert_iff, Set.mem_singleton_iff] at he
      rcases he with h | h <;> simp at h
  rw [edgeSet_elemSubdiv, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
    Set.ncard_image_of_injective _ (Sym2.map.injective (Option.some_injective V)),
    Set.ncard_pair hne, ← h1]

/-- CO-117. Subdividing an edge of a connected graph gives a connected graph. -/
@[kb "kellertrotter2017" "Definition (elementary subdivision), p. 116"]
theorem Connected.elemSubdiv {G : SimpleGraph V} (hG : G.Connected) (u v : V) (huv : G.Adj u v) :
    (UndergradKB.Combinatorics.Graph.elemSubdiv G u v).Connected := by
  set H := UndergradKB.Combinatorics.Graph.elemSubdiv G u v with hH
  have hnu : H.Adj none (some u) := (elemSubdiv_adj_none G u v u huv).2 (Or.inl rfl)
  have hnv : H.Adj none (some v) := (elemSubdiv_adj_none G u v v huv).2 (Or.inr rfl)
  -- adjacent vertices of `G` stay reachable
  have hstep : ∀ a b, G.Adj a b → H.Reachable (some a) (some b) := by
    intro a b hab
    by_cases he : s(a, b) = s(u, v)
    · have : (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by simpa [Sym2.eq_iff] using he
      rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hnu.symm.reachable.trans hnv.reachable
      · exact hnv.symm.reachable.trans hnu.reachable
    · refine Adj.reachable ?_
      rw [← mem_edgeSet, edgeSet_elemSubdiv]
      exact Or.inl ⟨s(a, b), ⟨hab, he⟩, by simp [Sym2.map_mk]⟩
  have hreach : ∀ a b, G.Reachable a b → H.Reachable (some a) (some b) := by
    intro a b ⟨p⟩
    induction p with
    | nil => exact Reachable.refl _
    | cons h _ ih => exact (hstep _ _ h).trans ih
  have hall : ∀ x : Option V, H.Reachable x (some u) := by
    intro x
    cases x with
    | none => exact hnu.reachable
    | some a => exact hreach a u (hG.preconnected a u)
  have : Nonempty (Option V) := ⟨none⟩
  exact ⟨fun x y => (hall x).trans (hall y).symm⟩

/-- CO-117. `IsSubdivisionOf G H`: `H` is obtained from `G` by a (possibly trivial) sequence of
elementary subdivisions, graphs being taken up to isomorphism. -/
@[kb "kellertrotter2017" "Definition (homeomorphic graphs), p. 116"]
inductive IsSubdivisionOf {V : Type u} (G : SimpleGraph V) : ∀ {W : Type u}, SimpleGraph W → Prop
  | iso {W : Type u} {H : SimpleGraph W} (e : G ≃g H) : IsSubdivisionOf G H
  | step {W : Type u} {H : SimpleGraph W} (hH : IsSubdivisionOf G H) (u v : W) (h : H.Adj u v)
      {K : Type u} {K' : SimpleGraph K} (e : elemSubdiv H u v ≃g K') : IsSubdivisionOf G K'

/-- CO-117. Two graphs are homeomorphic if both are subdivisions of one common graph. -/
@[kb "kellertrotter2017" "Definition (homeomorphic graphs), p. 116"]
def Homeomorphic {V W : Type u} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ (X : Type u) (K : SimpleGraph X), IsSubdivisionOf K G ∧ IsSubdivisionOf K H

theorem IsSubdivisionOf.refl (G : SimpleGraph V) : IsSubdivisionOf G G :=
  .iso (Iso.refl)

/-- An elementary subdivision is a subdivision. -/
theorem isSubdivisionOf_elemSubdiv (G : SimpleGraph V) (u v : V) (h : G.Adj u v) :
    IsSubdivisionOf G (elemSubdiv G u v) :=
  .step (.refl G) u v h Iso.refl

/-- CO-117. Every graph is homeomorphic to itself. -/
@[kb "kellertrotter2017" "Definition (homeomorphic graphs), p. 116"]
theorem Homeomorphic.refl (G : SimpleGraph V) : Homeomorphic G G :=
  ⟨V, G, .refl G, .refl G⟩

/-- CO-117. Homeomorphism of graphs is symmetric. -/
@[kb "kellertrotter2017" "Definition (homeomorphic graphs), p. 116"]
theorem Homeomorphic.symm {W : Type u} {G : SimpleGraph V} {H : SimpleGraph W}
    (h : Homeomorphic G H) : Homeomorphic H G := by
  obtain ⟨X, K, h1, h2⟩ := h
  exact ⟨X, K, h2, h1⟩

/-- A graph is homeomorphic to its elementary subdivisions. -/
theorem homeomorphic_elemSubdiv (G : SimpleGraph V) (u v : V) (h : G.Adj u v) :
    Homeomorphic G (elemSubdiv G u v) :=
  ⟨V, G, .refl G, isSubdivisionOf_elemSubdiv G u v h⟩

end UndergradKB.Combinatorics.Graph
