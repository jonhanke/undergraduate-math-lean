import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Finset.Max
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.Graph.PruferTree

/-!
# The Prüfer code of a labelled tree (Keller–Trotter, Section 5.6)

Labels are elements of a linearly ordered type `α` (the book uses positive integers).  A tree with label
set `S` is a `SimpleGraph α` with `IsTreeOn S G` (see `PruferTree.lean`).

The Prüfer code of a tree on `k ≥ 2` labels is obtained by repeatedly deleting the leaf with the
smallest label and recording the label of its neighbour; the recursion stops when two vertices remain.
We run the recursion with an explicit step budget `k - 2` (`pruferAux`), which is exactly the length
of the code.

Main results.
* `prufer_length_mem`, `isLeaf_iff_notMem_prufer`: the code has length `k - 2`, its symbols are labels,
  and a label is a leaf exactly when it does not occur in the code (CO-122).
* `pruferAux_inj`, `pruferAux_surj`: the code is injective, and every string of length `k - 2` over
  `S` is the code of some tree on `S` (the inverse construction by induction, CO-122).
-/

namespace UndergradKB.Combinatorics.Prufer

open SimpleGraph
open scoped Classical

variable {α : Type*} [LinearOrder α] {S : Finset α} {G : SimpleGraph α}

/-- The smallest leaf of `G` among the vertices of `S` (given that there is a leaf). -/
noncomputable def minLeaf (S : Finset α) (G : SimpleGraph α) (h : ∃ v ∈ S, IsLeaf G v) : α :=
  (S.filter (IsLeaf G)).min' (by obtain ⟨v, hv, hl⟩ := h; exact ⟨v, by simp [hv, hl]⟩)

/-- The neighbour of `v` (for a leaf `v`, its unique neighbour). -/
noncomputable def leafNbr (G : SimpleGraph α) (v : α) : α :=
  if h : ∃ u, G.Adj v u then h.choose else v

/-- The recursion of the Prüfer code with an explicit step budget: if `S` has a leaf, delete the
smallest one, record its neighbour and continue with budget one less. -/
noncomputable def pruferAux : ℕ → Finset α → SimpleGraph α → List α
  | 0, _, _ => []
  | m + 1, S, G =>
    if h : ∃ v ∈ S, IsLeaf G v then
      leafNbr G (minLeaf S G h) ::
        pruferAux m (S.erase (minLeaf S G h)) (G.deleteIncidenceSet (minLeaf S G h))
    else []

/-- CO-121. The Prüfer code of a tree `G` with label set `S` (`|S| ≥ 2`): repeatedly delete the leaf
with the smallest label and record the label of its neighbour; a string of length `|S| - 2`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) Prüfer code, p. 121"]
noncomputable def prufer (S : Finset α) (G : SimpleGraph α) : List α :=
  pruferAux (S.card - 2) S G

theorem minLeaf_mem (h : ∃ v ∈ S, IsLeaf G v) : minLeaf S G h ∈ S ∧ IsLeaf G (minLeaf S G h) := by
  have := Finset.min'_mem (S.filter (IsLeaf G)) (by obtain ⟨v, hv, hl⟩ := h; exact ⟨v, by simp [hv, hl]⟩)
  simpa [minLeaf] using this

theorem minLeaf_le (h : ∃ v ∈ S, IsLeaf G v) {w : α} (hw : w ∈ S) (hl : IsLeaf G w) :
    minLeaf S G h ≤ w :=
  Finset.min'_le _ _ (by simp [hw, hl])

omit [LinearOrder α] in
theorem adj_leafNbr {v : α} (hl : IsLeaf G v) : G.Adj v (leafNbr G v) := by
  have h : ∃ u, G.Adj v u := by obtain ⟨u, hu, -⟩ := hl; exact ⟨u, hu⟩
  simpa [leafNbr, h] using h.choose_spec

/-- The least leaf is determined by `v ∈ S`, being a leaf, and being below all other leaves. -/
theorem le_antisymm_leaf {v v' : α} (hv : v ∈ S ∧ IsLeaf G v) (hv' : v' ∈ S ∧ IsLeaf G v')
    (h1 : ∀ w ∈ S, IsLeaf G w → v ≤ w) (h2 : ∀ w ∈ S, IsLeaf G w → v' ≤ w) : v = v' :=
  le_antisymm (h1 _ hv'.1 hv'.2) (h2 _ hv.1 hv.2)

/-- One step of the recursion, for a tree on `m + 3` labels. -/
theorem pruferAux_succ {m : ℕ} (hG : IsTreeOn S G) (hc : S.card = m + 3) :
    ∃ v u, v ∈ S ∧ IsLeaf G v ∧ G.Adj v u ∧ (∀ w ∈ S, IsLeaf G w → v ≤ w) ∧
      pruferAux (m + 1) S G = u :: pruferAux m (S.erase v) (G.deleteIncidenceSet v) := by
  have h : ∃ v ∈ S, IsLeaf G v := hG.exists_leaf (by omega)
  obtain ⟨h1, h2⟩ := minLeaf_mem h
  refine ⟨minLeaf S G h, leafNbr G (minLeaf S G h), h1, h2, adj_leafNbr h2,
    fun w hw hl => minLeaf_le h hw hl, ?_⟩
  simp [pruferAux, h]

/-- The leaves of a tree on `m + 3` labels in terms of the leaves of the tree with the leaf `v`
deleted: `u` (the neighbour of `v`) is not a leaf, and the other labels keep their status. -/
theorem isLeaf_iff_succ {m : ℕ} (hG : IsTreeOn S G) (hc : S.card = m + 3) {v u w : α} (hv : v ∈ S)
    (hl : IsLeaf G v) (hvu : G.Adj v u) (hw : w ∈ S) :
    IsLeaf G w ↔ w = v ∨ (w ≠ u ∧ IsLeaf (G.deleteIncidenceSet v) w) := by
  have hT := hG.deleteLeaf (by omega) hl
  have hcard : (S.erase v).card = m + 2 := by rw [Finset.card_erase_of_mem hv]; omega
  by_cases hwv : w = v
  · subst hwv; simp [hl]
  by_cases hwu : w = u
  · subst hwu
    have hmem : w ∈ S.erase v := Finset.mem_erase.2 ⟨hwv, hw⟩
    have := not_isLeaf_of_deleteIncidenceSet hvu (hT.exists_adj (by omega) hmem)
    simp [this, hwv]
  · rw [isLeaf_iff_deleteIncidenceSet hl hvu hwv hwu]
    simp [hwv, hwu]

/-- CO-122 (key lemma). For a tree on `m + 2` labels, the code has length `m`, uses only labels of
`S`, and a label is a leaf exactly when it does not occur in the code. -/
theorem pruferAux_spec : ∀ (m : ℕ) (S : Finset α) (G : SimpleGraph α), IsTreeOn S G →
    S.card = m + 2 → ((pruferAux m S G).length = m ∧ ∀ x ∈ pruferAux m S G, x ∈ S) ∧
      ∀ w ∈ S, (IsLeaf G w ↔ w ∉ pruferAux m S G) := by
  intro m
  induction m with
  | zero =>
    intro S G hG hc
    refine ⟨by simp [pruferAux], fun w hw => ?_⟩
    simp [pruferAux, hG.isLeaf_of_card_eq_two (by omega) hw]
  | succ m ih =>
    intro S G hG hc
    obtain ⟨v, u, hv, hl, hvu, -, hcode⟩ := pruferAux_succ hG (by omega : S.card = m + 3)
    have hT := hG.deleteLeaf (by omega) hl
    have hcard : (S.erase v).card = m + 2 := by rw [Finset.card_erase_of_mem hv]; omega
    obtain ⟨⟨hlen, hmem⟩, hleaf⟩ := ih _ _ hT hcard
    rw [hcode]
    refine ⟨⟨by simp [hlen], ?_⟩, fun w hw => ?_⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hG.mem_right hvu
      · exact Finset.mem_of_mem_erase (hmem x hx)
    · rw [isLeaf_iff_succ hG (by omega) hv hl hvu hw]
      by_cases hwv : w = v
      · subst hwv
        have : w ∉ pruferAux m (S.erase w) (G.deleteIncidenceSet w) := fun h =>
          (Finset.notMem_erase _ _) (hmem _ h)
        simp [this, hvu.ne]
      · have hw' : w ∈ S.erase v := Finset.mem_erase.2 ⟨hwv, hw⟩
        rw [hleaf w hw']
        simp [hwv, not_or]

theorem prufer_length_mem (hG : IsTreeOn S G) (h2 : 2 ≤ S.card) :
    (prufer S G).length = S.card - 2 ∧ ∀ x ∈ prufer S G, x ∈ S :=
  (pruferAux_spec (S.card - 2) S G hG (by omega)).1

/-- CO-122. In a tree with at least two vertices, a label is a leaf iff it does not occur in the
Prüfer code (equivalently the labels occurring in the code are exactly the non-leaves). -/
@[kb "kellertrotter2017" "text (proof of Theorem 5.39), p. 122"]
theorem isLeaf_iff_notMem_prufer (hG : IsTreeOn S G) (h2 : 2 ≤ S.card) {w : α} (hw : w ∈ S) :
    IsLeaf G w ↔ w ∉ prufer S G :=
  (pruferAux_spec (S.card - 2) S G hG (by omega)).2 w hw

/-- CO-122. The Prüfer code determines the tree (injectivity half of the bijection). -/
@[kb "kellertrotter2017" "text (proof of Theorem 5.39), p. 122"]
theorem pruferAux_inj : ∀ (m : ℕ) (S : Finset α) (G₁ G₂ : SimpleGraph α), IsTreeOn S G₁ →
    IsTreeOn S G₂ → S.card = m + 2 → pruferAux m S G₁ = pruferAux m S G₂ → G₁ = G₂ := by
  intro m
  induction m with
  | zero =>
    intro S G₁ G₂ h₁ h₂ hc _
    ext a b
    rw [h₁.adj_iff_of_card_eq_two hc, h₂.adj_iff_of_card_eq_two hc]
  | succ m ih =>
    intro S G₁ G₂ h₁ h₂ hc hcode
    have hc3 : S.card = m + 3 := by omega
    obtain ⟨v₁, u₁, hv₁, hl₁, hu₁, hmin₁, hc₁⟩ := pruferAux_succ h₁ hc3
    obtain ⟨v₂, u₂, hv₂, hl₂, hu₂, hmin₂, hc₂⟩ := pruferAux_succ h₂ hc3
    have hleaf : ∀ w ∈ S, IsLeaf G₁ w ↔ IsLeaf G₂ w := by
      intro w hw
      have e₁ := (pruferAux_spec (m + 1) S G₁ h₁ hc).2 w hw
      have e₂ := (pruferAux_spec (m + 1) S G₂ h₂ hc).2 w hw
      rw [e₁, e₂, hcode]
    have hv : v₁ = v₂ := le_antisymm
      (hmin₁ _ hv₂ ((hleaf _ hv₂).2 hl₂)) (hmin₂ _ hv₁ ((hleaf _ hv₁).1 hl₁))
    subst hv
    rw [hc₁, hc₂] at hcode
    obtain ⟨rfl, hcode'⟩ := List.cons.inj hcode
    have hcard : (S.erase v₁).card = m + 2 := by rw [Finset.card_erase_of_mem hv₁]; omega
    have := ih _ _ _ (h₁.deleteLeaf (by omega) hl₁) (h₂.deleteLeaf (by omega) hl₂) hcard hcode'
    rw [eq_deleteIncidenceSet_sup_edge hl₁ hu₁, eq_deleteIncidenceSet_sup_edge hl₂ hu₂, this]

/-- CO-122 (inverse construction). Every string of length `m` over a label set `S` of size `m + 2`
is the Prüfer code of some tree on `S`.  The tree is built by induction: the first leaf removed is the
smallest label not occurring in the string, and it is attached to the first symbol. -/
@[kb "kellertrotter2017" "text (proof of Theorem 5.39), p. 122"]
theorem pruferAux_surj : ∀ (m : ℕ) (S : Finset α), S.card = m + 2 → ∀ l : List α,
    l.length = m → (∀ x ∈ l, x ∈ S) → ∃ G, IsTreeOn S G ∧ pruferAux m S G = l := by
  intro m
  induction m with
  | zero =>
    intro S hc l hl _
    obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.1 hc
    have := (isTreeOn_singleton q).addLeaf (v := p) (by simpa using hpq) (Finset.mem_singleton_self q)
    exact ⟨_, this, by simp [pruferAux, List.length_eq_zero_iff.1 hl]⟩
  | succ m ih =>
    intro S hc l hl hlS
    obtain ⟨i, l', rfl⟩ : ∃ i l', l = i :: l' := by
      cases l with
      | nil => simp at hl
      | cons i l' => exact ⟨i, l', rfl⟩
    have hc3 : S.card = m + 3 := by omega
    -- the smallest label not in the string
    have hex : ∃ e ∈ S, e ∉ (i :: l').toFinset := by
      apply Finset.exists_mem_notMem_of_card_lt_card
      have := List.toFinset_card_le (i :: l')
      omega
    obtain ⟨v, hvS, hvl, hvle⟩ : ∃ v ∈ S, v ∉ i :: l' ∧ ∀ w ∈ S, w ∉ i :: l' → v ≤ w := by
      have hne : (S \ (i :: l').toFinset).Nonempty := by
        obtain ⟨e, he, he'⟩ := hex; exact ⟨e, by simp_all⟩
      have hvmem : (S \ (i :: l').toFinset).min' hne ∈ S \ (i :: l').toFinset :=
        Finset.min'_mem _ _
      exact ⟨_, (Finset.mem_sdiff.1 hvmem).1, by simpa using (Finset.mem_sdiff.1 hvmem).2,
        fun w hw hwl => Finset.min'_le _ _
          (Finset.mem_sdiff.2 ⟨hw, fun h => hwl (List.mem_toFinset.1 h)⟩)⟩
    have hvi : v ≠ i := fun e => hvl (by simp [e])
    have hcard : (S.erase v).card = m + 2 := by rw [Finset.card_erase_of_mem hvS]; omega
    have hiS' : i ∈ S.erase v := Finset.mem_erase.2 ⟨hvi.symm, hlS i (by simp)⟩
    have hl'S : ∀ x ∈ l', x ∈ S.erase v := fun x hx =>
      Finset.mem_erase.2 ⟨fun e => hvl (by rw [← e]; exact List.mem_cons_of_mem _ hx),
        hlS x (List.mem_cons_of_mem _ hx)⟩
    obtain ⟨G', hG', hcG'⟩ := ih (S.erase v) hcard l' (by simpa using hl) hl'S
    have hnot : v ∉ S.erase v := Finset.notMem_erase _ _
    have hT : IsTreeOn S (G' ⊔ edge v i) := by
      have := hG'.addLeaf hnot hiS'
      rwa [Finset.insert_erase hvS] at this
    have hiso : ∀ x, ¬ G'.Adj v x := fun x hx => hnot (hG'.mem_left hx)
    have hleaf : IsLeaf (G' ⊔ edge v i) v := isLeaf_sup_edge hvi hiso
    have hadj : (G' ⊔ edge v i).Adj v i := by simp [edge_adj, hvi]
    have hdel : (G' ⊔ edge v i).deleteIncidenceSet v = G' := deleteIncidenceSet_sup_edge hiso
    refine ⟨G' ⊔ edge v i, hT, ?_⟩
    obtain ⟨v', u', hv', hl', hvu', hmin', hcode⟩ := pruferAux_succ hT hc3
    have hmin : ∀ w ∈ S, IsLeaf (G' ⊔ edge v i) w → v ≤ w := by
      intro w hw hwl
      rw [isLeaf_iff_succ hT hc3 hvS hleaf hadj hw, hdel] at hwl
      rcases hwl with h | ⟨hwi, hwl'⟩
      · exact le_of_eq h.symm
      · by_cases hwv : w = v
        · exact le_of_eq hwv.symm
        · have hw' : w ∈ S.erase v := Finset.mem_erase.2 ⟨hwv, hw⟩
          have hnm := ((pruferAux_spec m _ G' hG' hcard).2 w hw').1 hwl'
          rw [hcG'] at hnm
          exact hvle w hw (by simp [hwi, hnm])
    have hvv : v' = v := le_antisymm (hmin' v hvS hleaf) (hmin v' hv' hl')
    rw [hvv] at hcode hvu'
    have hu : u' = i := hleaf.eq_of_adj hadj hvu'
    rw [hcode, hdel, hu, hcG']

end UndergradKB.Combinatorics.Prufer
