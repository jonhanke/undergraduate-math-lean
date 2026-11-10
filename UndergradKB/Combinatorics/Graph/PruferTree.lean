import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Operations
import UndergradKB.Common.Attr

/-!
# Trees on a finite vertex set, and leaf surgery (Keller–Trotter, Section 5.6)

The Prüfer code of a tree is defined by repeatedly deleting a leaf, so we need trees whose vertex set
varies.  We keep the ambient vertex type `α` fixed and describe "a tree with vertex set `S`" as a
`SimpleGraph α` all of whose edges lie inside the finset `S`, which is connected on `S` and acyclic
(`IsTreeOn`).  A leaf is a vertex with exactly one neighbour (`IsLeaf`).  This file contains the
graph-theoretic lemmas: existence of leaves, deleting a leaf from a tree, attaching a new leaf, and the
effect of these on the set of leaves.
-/

namespace UndergradKB.Combinatorics.Prufer

open SimpleGraph

variable {α : Type*} {S : Finset α} {G : SimpleGraph α}

/-- `v` is a leaf of `G`: it has exactly one neighbour. -/
def IsLeaf (G : SimpleGraph α) (v : α) : Prop := ∃ u, G.Adj v u ∧ ∀ w, G.Adj v w → w = u

/-- `G` is a tree with vertex set `S`: all its edges lie in `S`, any two vertices of `S` are
connected, and it has no cycle. -/
structure IsTreeOn (S : Finset α) (G : SimpleGraph α) : Prop where
  nonempty : S.Nonempty
  mem_left : ∀ {a b}, G.Adj a b → a ∈ S
  reachable : ∀ a ∈ S, ∀ b ∈ S, G.Reachable a b
  acyclic : G.IsAcyclic

theorem IsTreeOn.mem_right (h : IsTreeOn S G) {a b : α} (hab : G.Adj a b) : b ∈ S :=
  h.mem_left hab.symm

/-- Every vertex of a tree with at least two vertices has a neighbour. -/
theorem IsTreeOn.exists_adj (h : IsTreeOn S G) (h2 : 2 ≤ S.card) {w : α} (hw : w ∈ S) :
    ∃ x, G.Adj w x := by
  obtain ⟨b, hb, hbw⟩ := Finset.exists_mem_ne (by omega : 1 < S.card) w
  obtain ⟨p⟩ := h.reachable w hw b hb
  exact ⟨_, p.adj_snd (Walk.not_nil_of_ne hbw.symm)⟩

theorem walk_support_mem (hS' : ∀ {a b}, G.Adj a b → b ∈ S)
    {a b : α} (p : G.Walk a b) (ha : a ∈ S) : ∀ z ∈ p.support, z ∈ S := by
  induction p with
  | nil => simpa using ha
  | cons h p ih =>
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact ha
    · exact ih (hS' h) z hz

/-- A tree on at least two vertices has a leaf. -/
theorem IsTreeOn.exists_leaf (h : IsTreeOn S G) (h2 : 2 ≤ S.card) : ∃ v ∈ S, IsLeaf G v := by
  classical
  have hT : (G.induce (S : Set α)).IsTree := by
    refine ⟨(connected_iff _).2 ⟨fun a b => ?_, ?_⟩, ?_⟩
    · obtain ⟨p⟩ := h.reachable a a.2 b b.2
      exact ⟨p.induce (S : Set α) (walk_support_mem h.mem_right p a.2)⟩
    · obtain ⟨x, hx⟩ := h.nonempty
      exact ⟨⟨x, hx⟩⟩
    · exact h.acyclic.induce _
  have : Nontrivial (S : Set α) := by
    rw [← Fintype.one_lt_card_iff_nontrivial]
    simpa using (by omega : 1 < S.card)
  obtain ⟨v, hv⟩ := hT.exists_vert_degree_one_of_nontrivial
  obtain ⟨u, hu, huniq⟩ := degree_eq_one_iff_existsUnique_adj.1 hv
  refine ⟨v, v.2, u, hu, fun w hw => ?_⟩
  have hwS : w ∈ S := h.mem_right hw
  exact congrArg Subtype.val (huniq ⟨w, hwS⟩ hw)

theorem IsLeaf.eq_of_adj {v u w : α} (hl : IsLeaf G v) (hu : G.Adj v u) (hw : G.Adj v w) :
    w = u := by
  obtain ⟨x, -, hx⟩ := hl
  rw [hx w hw, hx u hu]

/-- Deleting a leaf `v` does not disconnect two other vertices. -/
theorem reachable_deleteIncidenceSet {a b v : α} (hG : G.Reachable a b) (ha : a ≠ v) (hb : b ≠ v)
    (hv : IsLeaf G v) : (G.deleteIncidenceSet v).Reachable a b := by
  classical
  obtain ⟨p⟩ := hG
  let q := p.toPath
  have hsub : (G.neighborSet v).Subsingleton := by
    intro x hx y hy
    exact (hv.eq_of_adj hx hy).symm
  have hv' : v ∉ q.1.support :=
    q.2.isTrail.notMem_support_of_subsingleton_neighborSet (Ne.symm ha) (Ne.symm hb) hsub
  refine ⟨q.1.transfer _ fun e he => ?_⟩
  induction e using Sym2.ind with
  | _ x y =>
    have hxy : G.Adj x y := q.1.adj_of_mem_edges he
    have hx : x ∈ q.1.support := q.1.fst_mem_support_of_mem_edges he
    have hy : y ∈ q.1.support := q.1.snd_mem_support_of_mem_edges he
    rw [mem_edgeSet, deleteIncidenceSet_adj]
    exact ⟨hxy, fun h => hv' (h ▸ hx), fun h => hv' (h ▸ hy)⟩

/-- Deleting a leaf from a tree gives a tree on the remaining vertices. -/
theorem IsTreeOn.deleteLeaf [DecidableEq α] (h : IsTreeOn S G) (h2 : 2 ≤ S.card) {v : α}
    (hl : IsLeaf G v) : IsTreeOn (S.erase v) (G.deleteIncidenceSet v) := by
  refine ⟨?_, ?_, ?_, h.acyclic.anti (deleteIncidenceSet_le _ _)⟩
  · rw [← Finset.card_pos]
    have := Finset.pred_card_le_card_erase (s := S) (a := v)
    omega
  · intro a b hab
    rw [deleteIncidenceSet_adj] at hab
    exact Finset.mem_erase.2 ⟨hab.2.1, h.mem_left hab.1⟩
  · intro a ha b hb
    rw [Finset.mem_erase] at ha hb
    exact reachable_deleteIncidenceSet (h.reachable a ha.2 b hb.2) ha.1 hb.1 hl

/-- Attaching a new leaf `v` to a vertex `i` of a tree on `S` gives a tree on `insert v S`. -/
theorem IsTreeOn.addLeaf [DecidableEq α] (h : IsTreeOn S G) {v i : α} (hv : v ∉ S) (hi : i ∈ S) :
    IsTreeOn (insert v S) (G ⊔ edge v i) := by
  have hvi : v ≠ i := fun e => hv (e ▸ hi)
  have hAdj : (G ⊔ edge v i).Adj v i := by simp [edge_adj, hvi]
  have hr : ∀ a ∈ insert v S, (G ⊔ edge v i).Reachable a i := by
    intro a ha
    rcases Finset.mem_insert.1 ha with rfl | ha
    · exact hAdj.reachable
    · exact (h.reachable a ha i hi).mono le_sup_left
  refine ⟨⟨v, Finset.mem_insert_self _ _⟩, ?_, fun a ha b hb => (hr a ha).trans (hr b hb).symm, ?_⟩
  · intro a b hab
    rw [sup_adj, edge_adj] at hab
    rcases hab with hab | ⟨⟨rfl, -⟩ | ⟨rfl, -⟩, -⟩
    · exact Finset.mem_insert_of_mem (h.mem_left hab)
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem hi
  · refine h.acyclic.sup_edge_of_not_reachable fun hreach => ?_
    obtain ⟨p⟩ := hreach
    exact hv (h.mem_left (p.adj_snd (Walk.not_nil_of_ne hvi)))

/-- A graph with a leaf `v` (neighbour `u`) is the leaf-deleted graph plus the edge `v u`. -/
theorem eq_deleteIncidenceSet_sup_edge {v u : α} (hl : IsLeaf G v) (hvu : G.Adj v u) :
    G = G.deleteIncidenceSet v ⊔ edge v u := by
  ext a b
  simp only [sup_adj, deleteIncidenceSet_adj, edge_adj]
  constructor
  · intro hab
    by_cases ha : a = v
    · subst ha
      exact Or.inr ⟨Or.inl ⟨rfl, hl.eq_of_adj hvu hab⟩, hab.ne⟩
    by_cases hb : b = v
    · subst hb
      exact Or.inr ⟨Or.inr ⟨hl.eq_of_adj hvu hab.symm, rfl⟩, hab.ne⟩
    exact Or.inl ⟨hab, ha, hb⟩
  · rintro (⟨hab, -, -⟩ | ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, -⟩)
    · exact hab
    · exact hvu
    · exact hvu.symm

/-- Removing the newly attached vertex recovers the original graph. -/
theorem deleteIncidenceSet_sup_edge {v i : α} (hv : ∀ x, ¬ G.Adj v x) :
    (G ⊔ edge v i).deleteIncidenceSet v = G := by
  ext a b
  simp only [deleteIncidenceSet_adj, sup_adj, edge_adj]
  constructor
  · rintro ⟨hab | ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, -⟩, ha, hb⟩
    · exact hab
    · exact absurd rfl ha
    · exact absurd rfl hb
  · intro hab
    refine ⟨Or.inl hab, ?_, ?_⟩
    · rintro rfl; exact hv _ hab
    · rintro rfl; exact hv _ hab.symm

/-- A vertex with exactly the neighbour `i` after attaching it to `i`. -/
theorem isLeaf_sup_edge {v i : α} (hvi : v ≠ i) (hv : ∀ x, ¬ G.Adj v x) :
    IsLeaf (G ⊔ edge v i) v := by
  refine ⟨i, by simp [edge_adj, hvi], fun w hw => ?_⟩
  rw [sup_adj, edge_adj] at hw
  rcases hw with hw | ⟨⟨-, rfl⟩ | ⟨rfl, -⟩, -⟩
  · exact absurd hw (hv _)
  · rfl
  · exact absurd rfl hvi

/-- The leaves of `G` other than the deleted leaf `v` and its neighbour `u` are the leaves of
`G` with `v` deleted. -/
theorem isLeaf_iff_deleteIncidenceSet {v u w : α} (hl : IsLeaf G v) (hvu : G.Adj v u) (hwv : w ≠ v)
    (hwu : w ≠ u) : IsLeaf G w ↔ IsLeaf (G.deleteIncidenceSet v) w := by
  have hnv : ∀ x, G.Adj w x → x ≠ v := by
    rintro x hx rfl
    exact hwu (hl.eq_of_adj hvu hx.symm)
  constructor
  · rintro ⟨y, hy, huniq⟩
    refine ⟨y, ?_, fun x hx => ?_⟩
    · rw [deleteIncidenceSet_adj]; exact ⟨hy, hwv, hnv _ hy⟩
    · rw [deleteIncidenceSet_adj] at hx
      exact huniq x hx.1
  · rintro ⟨y, hy, huniq⟩
    rw [deleteIncidenceSet_adj] at hy
    exact ⟨y, hy.1, fun x hx => huniq x ((deleteIncidenceSet_adj).2 ⟨hx, hwv, hnv _ hx⟩)⟩

/-- The neighbour `u` of a deleted leaf `v` is not a leaf, provided it still has a neighbour after
the deletion. -/
theorem not_isLeaf_of_deleteIncidenceSet {v u : α} (hvu : G.Adj v u)
    (hx : ∃ x, (G.deleteIncidenceSet v).Adj u x) : ¬ IsLeaf G u := by
  obtain ⟨x, hx⟩ := hx
  rw [deleteIncidenceSet_adj] at hx
  rintro ⟨y, -, huniq⟩
  exact hx.2.2 ((huniq x hx.1).trans (huniq v hvu.symm).symm)

/-- A tree on two vertices is the edge between them. -/
theorem IsTreeOn.adj_iff_of_card_eq_two (h : IsTreeOn S G) (h2 : S.card = 2) {a b : α} :
    G.Adj a b ↔ a ∈ S ∧ b ∈ S ∧ a ≠ b := by
  classical
  constructor
  · intro hab
    exact ⟨h.mem_left hab, h.mem_right hab, hab.ne⟩
  · rintro ⟨ha, hb, hab⟩
    obtain ⟨x, hx⟩ := h.exists_adj (by omega) ha
    have hxS := h.mem_right hx
    obtain ⟨p, q, -, rfl⟩ := Finset.card_eq_two.1 h2
    have : x = b := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hxS
      have := hx.ne
      grind
    exact this ▸ hx

/-- Both vertices of a tree on two vertices are leaves. -/
theorem IsTreeOn.isLeaf_of_card_eq_two (h : IsTreeOn S G) (h2 : S.card = 2) {w : α} (hw : w ∈ S) :
    IsLeaf G w := by
  classical
  obtain ⟨x, hx⟩ := h.exists_adj (by omega) hw
  refine ⟨x, hx, fun y hy => ?_⟩
  have hyS := h.mem_right hy
  have hxS := h.mem_right hx
  obtain ⟨p, q, -, rfl⟩ := Finset.card_eq_two.1 h2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw hyS hxS
  have := hx.ne
  have := hy.ne
  grind

/-- The one-vertex tree. -/
theorem isTreeOn_singleton [LinearOrder α] (v : α) : IsTreeOn {v} (⊥ : SimpleGraph α) :=
  ⟨⟨v, by simp⟩, fun h => by simp at h, fun a ha b hb => by
    simp only [Finset.mem_singleton] at ha hb; subst ha; subst hb; exact Reachable.refl _,
    (isAcyclic_hasse_of_linearOrder α).anti bot_le⟩

/-- Over `Finset.univ`, `IsTreeOn` is Mathlib's `IsTree`. -/
theorem isTreeOn_univ_iff [Fintype α] : IsTreeOn Finset.univ G ↔ G.IsTree := by
  constructor
  · intro h
    refine ⟨(connected_iff _).2 ⟨fun a b => h.reachable a (Finset.mem_univ _) b (Finset.mem_univ _),
      ?_⟩, h.acyclic⟩
    obtain ⟨x, -⟩ := h.nonempty
    exact ⟨x⟩
  · intro h
    exact ⟨Finset.univ_nonempty_iff.2 h.1.nonempty, fun _ => Finset.mem_univ _,
      fun a _ b _ => h.1.preconnected a b, h.2⟩

end UndergradKB.Combinatorics.Prufer
