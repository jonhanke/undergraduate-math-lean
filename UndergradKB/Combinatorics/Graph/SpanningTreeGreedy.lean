import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.Graph.SpanningTree

/-!
# Lemma 12.6 and the greedy algorithms of Kruskal and Prim (Keller–Trotter, Chapter 12)

The algorithms are formalised abstractly.  Kruskal's algorithm processes a list of edges that is
sorted by weight and contains every edge of `G`; it keeps an edge iff its endpoints lie in different
components of the current forest (equivalently, adding it creates no cycle).  Prim's algorithm is an
inductive relation `PrimReach`: a step adds *some* lightest edge leaving the component of the root.
Correctness follows the book: the invariant "the current forest lies in a minimum weight spanning
tree", maintained by Lemma 12.6.
-/

namespace UndergradKB.Combinatorics.SpanningTree

open SimpleGraph

open scoped Classical

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V]

/-! ### Lemma 12.6 -/

/-- The exchange step behind Lemma 12.6: `T` is a spanning tree of `G` containing `F`, `C` a vertex
set closed under `F`, and `xy` an edge of `G` leaving `C` of minimum weight among such edges.  Then
there is a spanning tree `T'` containing `F` and `xy`, of weight at most that of `T`. -/
theorem exists_exchange_edge {G F T : SimpleGraph V} (w : Sym2 V → ℝ) (hT : T.IsTree)
    (hFT : F ≤ T) (hTG : T ≤ G) (C : Set V) (hC : ∀ a b, F.Adj a b → a ∈ C → b ∈ C)
    {x y : V} (hx : x ∈ C) (hy : y ∉ C) (hxy : G.Adj x y)
    (hmin : ∀ a b, G.Adj a b → a ∈ C → b ∉ C → w s(x, y) ≤ w s(a, b)) :
    ∃ T' : SimpleGraph V, T'.IsTree ∧ F ≤ T' ∧ T' ≤ G ∧ T'.Adj x y ∧
      weight w T' ≤ weight w T := by
  by_cases hadj : T.Adj x y
  · exact ⟨T, hT, hFT, hTG, hadj, le_rfl⟩
  obtain ⟨p, hp, -⟩ := hT.existsUnique_path x y
  obtain ⟨d, hd, hd1, hd2⟩ := p.exists_boundary_dart C hx hy
  have hxy' : x ≠ y := fun h => hy (h ▸ hx)
  have hfp : s(d.fst, d.snd) ∈ p.edges := List.mem_map.2 ⟨d, hd, rfl⟩
  have hdT : T.Adj d.fst d.snd := d.adj
  have hFd : ¬ F.Adj d.fst d.snd := fun h => hd2 (hC _ _ h hd1)
  refine ⟨exchange T s(x, y) s(d.fst, d.snd), exchange_isTree hT hxy' hadj p hp hfp, ?_, ?_, ?_,
    ?_⟩
  · intro a b hab
    refine exchange_adj.2 ⟨Or.inr ⟨hFT hab, fun h => hFd ?_⟩, hab.ne⟩
    rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]; exact hab
    · rw [← h1, ← h2]; exact hab.symm
  · intro a b hab
    rcases exchange_adj.1 hab with ⟨h | h, _⟩
    · rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hxy
      · exact hxy.symm
    · exact hTG h.1
  · exact exchange_adj.2 ⟨Or.inl rfl, hxy'⟩
  · rw [weight_exchange w (by simpa using hxy') (by simpa using hadj)
      (p.edges_subset_edgeSet hfp)]
    have := hmin d.fst d.snd (hTG hdT) hd1 hd2
    linarith

/-- CO-272. Lemma 12.6. Let `F` be a spanning forest of `G`, `C` a component of `F`, and `xy` an
edge of `G` of minimum weight among those with exactly one endpoint in `C`.  If `T` is a minimum
weight spanning tree among those containing `F`, then some minimum weight spanning tree among
those containing `F` contains the edge `xy`. -/
@[kb "kellertrotter2017" "Lemma 12.6, p. 266"]
theorem lemma_12_6 {G F T : SimpleGraph V} (w : Sym2 V → ℝ) (C : F.ConnectedComponent)
    (hT : IsMinSpanningTreeContaining G w F T) {x y : V}
    (hx : F.connectedComponentMk x = C) (hy : F.connectedComponentMk y ≠ C) (hxy : G.Adj x y)
    (hmin : ∀ a b, G.Adj a b → F.connectedComponentMk a = C → F.connectedComponentMk b ≠ C →
      w s(x, y) ≤ w s(a, b)) :
    ∃ T' : SimpleGraph V, IsMinSpanningTreeContaining G w F T' ∧ T'.Adj x y := by
  obtain ⟨hTt, hFT, hTG, hTmin⟩ := hT
  obtain ⟨T', h1, h2, h3, h4, h5⟩ := exists_exchange_edge (C := {v | F.connectedComponentMk v = C})
    w hTt hFT hTG
    (fun a b hab ha => by
      simp only [Set.mem_ofPred_eq] at ha ⊢
      rw [← ha]
      exact ConnectedComponent.eq.2 hab.reachable.symm) hx hy hxy
    hmin
  exact ⟨T', ⟨h1, h2, h3, fun T'' a b c => h5.trans (hTmin T'' a b c)⟩, h4⟩

/-- CO-272. Lemma 12.6, in the form used by the algorithms: if `F` lies in a minimum weight
spanning tree `T` of `G` and `xy` is a lightest edge of `G` leaving a set `C` closed under `F`
(for example a component of `F`), then `F` and `xy` both lie in some minimum weight spanning
tree. -/
@[kb "kellertrotter2017" "Lemma 12.6, p. 266"]
theorem lemma_12_6_global {G F T : SimpleGraph V} (w : Sym2 V → ℝ) (hT : IsMinSpanningTree G w T)
    (hFT : F ≤ T) (C : Set V) (hC : ∀ a b, F.Adj a b → a ∈ C → b ∈ C) {x y : V} (hx : x ∈ C)
    (hy : y ∉ C) (hxy : G.Adj x y)
    (hmin : ∀ a b, G.Adj a b → a ∈ C → b ∉ C → w s(x, y) ≤ w s(a, b)) :
    ∃ T' : SimpleGraph V, IsMinSpanningTree G w T' ∧ F ≤ T' ∧ T'.Adj x y := by
  obtain ⟨hTt, hTG, hTmin⟩ := hT
  obtain ⟨T', h1, h2, h3, h4, h5⟩ := exists_exchange_edge w hTt hFT hTG C hC hx hy hxy hmin
  exact ⟨T', ⟨h1, h3, fun T'' a b => h5.trans (hTmin T'' a b)⟩, h2, h4⟩

/-- A connected spanning subgraph of a tree is the tree. -/
lemma eq_of_reachable_le {F T : SimpleGraph V} (hT : T.IsTree) (hFT : F ≤ T)
    (hc : ∀ u v, F.Reachable u v) : F = T := by
  have := hT.connected.nonempty
  have hF : F.IsTree := ⟨⟨hc⟩, hT.isAcyclic.anti hFT⟩
  have h1 := hF.ncard_edgeSet_add_one
  have h2 := hT.ncard_edgeSet_add_one
  have hsub : F.edgeSet ⊆ T.edgeSet := edgeSet_mono hFT
  have := Set.eq_of_subset_of_ncard_le hsub (by omega) T.edgeSet.toFinite
  exact edgeSet_injective this

/-! ### Kruskal's algorithm -/

/-- One step of Kruskal's algorithm: add the edge `e` to the forest `F` iff its endpoints lie in
different components of `F` (i.e. iff no cycle is created). -/
noncomputable def kruskalStep (F : SimpleGraph V) (e : Sym2 V) : SimpleGraph V :=
  if ∃ a b, e = s(a, b) ∧ ¬ F.Reachable a b then F ⊔ fromEdgeSet {e} else F

/-- CO-273. Kruskal's algorithm run on the list `l` of edges (to be sorted by weight): start with
the empty forest and process the edges in order. -/
@[kb "kellertrotter2017" "Algorithm 12.8, p. 267"]
noncomputable def kruskal (l : List (Sym2 V)) : SimpleGraph V :=
  l.foldl kruskalStep ⊥

lemma le_kruskalStep (F : SimpleGraph V) (e : Sym2 V) : F ≤ kruskalStep F e := by
  unfold kruskalStep
  split_ifs
  · exact le_sup_left
  · exact le_rfl

lemma fromEdgeSet_le_of_adj {T : SimpleGraph V} {a b : V} (h : T.Adj a b) :
    fromEdgeSet {s(a, b)} ≤ T := by
  intro p q hpq
  rw [fromEdgeSet_adj] at hpq
  rcases Sym2.eq_iff.1 (Set.mem_singleton_iff.1 hpq.1) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h
  · exact h.symm

/-- The invariant of Kruskal's algorithm: `F` lies in a minimum weight spanning tree, and every
edge of `G` not among the remaining edges `rest` already has endpoints in one component of `F`. -/
def KruskalInv (G : SimpleGraph V) (w : Sym2 V → ℝ) (rest : List (Sym2 V)) (F : SimpleGraph V) :
    Prop :=
  (∃ T, IsMinSpanningTree G w T ∧ F ≤ T) ∧
    ∀ g ∈ G.edgeSet, g ∉ rest → ∀ a b, g = s(a, b) → F.Reachable a b

lemma kruskalInv_step {G : SimpleGraph V} {w : Sym2 V → ℝ} {e : Sym2 V} {rest : List (Sym2 V)}
    {F : SimpleGraph V} (hsorted : (e :: rest).Pairwise fun a b => w a ≤ w b)
    (heG : e ∈ G.edgeSet) (hinv : KruskalInv G w (e :: rest) F) :
    KruskalInv G w rest (kruskalStep F e) := by
  obtain ⟨⟨T, hT, hFT⟩, hreach⟩ := hinv
  rw [List.pairwise_cons] at hsorted
  have hold : ∀ g ∈ G.edgeSet, g ∉ rest → g ≠ e → ∀ a b, g = s(a, b) → F.Reachable a b :=
    fun g hg h1 h2 => hreach g hg (by simp [h1, h2])
  unfold kruskalStep
  split_ifs with hex
  · obtain ⟨a, b, rfl, hab⟩ := hex
    have hGab : G.Adj a b := heG
    have hne : a ≠ b := fun h => hab (h ▸ Reachable.refl _)
    obtain ⟨T1, hT1, hFT1, hT1ab⟩ := lemma_12_6_global w hT hFT {v | F.Reachable a v}
      (fun p q hpq hp => hp.trans hpq.reachable) (x := a) (y := b) (Reachable.refl _) hab hGab
      (by
        intro c d hcd hc hd
        have hmem : s(c, d) ∈ G.edgeSet := hcd
        by_cases hg : s(c, d) ∈ s(a, b) :: rest
        · rcases List.mem_cons.1 hg with h | h
          · rw [h]
          · exact hsorted.1 _ h
        · exact (hd (hc.trans (hreach _ hmem hg c d rfl))).elim
          )
    refine ⟨⟨T1, hT1, sup_le hFT1 (fromEdgeSet_le_of_adj hT1ab)⟩, ?_⟩
    intro g hg hgr c d hcd
    by_cases hge : g = s(a, b)
    · have hadj : (F ⊔ fromEdgeSet {s(a, b)}).Adj a b :=
        Or.inr (by rw [fromEdgeSet_adj]; exact ⟨rfl, hne⟩)
      rcases Sym2.eq_iff.1 (hcd ▸ hge : s(c, d) = s(a, b)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hadj.reachable
      · exact hadj.reachable.symm
    · exact (hold g hg hgr hge c d hcd).mono le_sup_left
  · push Not at hex
    refine ⟨⟨T, hT, hFT⟩, ?_⟩
    intro g hg hgr c d hcd
    by_cases hge : g = e
    · exact hex c d (hge.symm.trans hcd)
    · exact hold g hg hgr hge c d hcd

lemma kruskalInv_foldl {G : SimpleGraph V} {w : Sym2 V → ℝ} :
    ∀ (rest : List (Sym2 V)) (F : SimpleGraph V),
      rest.Pairwise (fun a b => w a ≤ w b) → (∀ e ∈ rest, e ∈ G.edgeSet) →
      KruskalInv G w rest F → KruskalInv G w [] (rest.foldl kruskalStep F)
  | [], F, _, _, h => h
  | e :: rest, F, hs, hG, h => by
    rw [List.foldl_cons]
    exact kruskalInv_foldl rest _ (List.Pairwise.of_cons hs)
      (fun g hg => hG g (List.mem_cons_of_mem _ hg))
      (kruskalInv_step hs (hG e List.mem_cons_self) h)

/-- CO-274. Correctness of Kruskal's algorithm: run on a list of the edges of the connected graph
`G` sorted by weight, it outputs a minimum weight spanning tree. -/
@[kb "kellertrotter2017" "text (correctness of Kruskal's Algorithm), p. 267"]
theorem kruskal_isMinSpanningTree {G : SimpleGraph V} (hG : G.Connected) (w : Sym2 V → ℝ)
    (l : List (Sym2 V)) (hsorted : l.Pairwise fun a b => w a ≤ w b)
    (hl : ∀ e, e ∈ l ↔ e ∈ G.edgeSet) : IsMinSpanningTree G w (kruskal l) := by
  obtain ⟨T0, hT0⟩ := exists_isMinSpanningTree w hG
  have hinv : KruskalInv G w l ⊥ := ⟨⟨T0, hT0, bot_le⟩, fun g hg hgl => absurd ((hl g).2 hg) hgl⟩
  obtain ⟨⟨T, hT, hFT⟩, hreach⟩ := kruskalInv_foldl l ⊥ hsorted (fun e he => (hl e).1 he) hinv
  have hc : ∀ u v, (kruskal l).Reachable u v := by
    intro u v
    obtain ⟨q⟩ := hG.preconnected u v
    induction q with
    | nil => exact Reachable.refl _
    | cons h q ih =>
      exact (hreach _ h (by simp) _ _ rfl).trans (ih)
  have : kruskal l = T := eq_of_reachable_le hT.1 hFT hc
  rw [this]
  exact hT

/-- The edges of `G` can be listed (without the sorting step being specified further) in order of
nondecreasing weight, as the first step of Kruskal's algorithm requires. -/
theorem exists_sorted_edge_list (G : SimpleGraph V) (w : Sym2 V → ℝ) :
    ∃ l : List (Sym2 V), l.Pairwise (fun a b => w a ≤ w b) ∧ ∀ e, e ∈ l ↔ e ∈ G.edgeSet := by
  have : Std.Total (fun a b : Sym2 V => w a ≤ w b) := ⟨fun a b => le_total _ _⟩
  have : IsTrans (Sym2 V) (fun a b : Sym2 V => w a ≤ w b) := ⟨fun _ _ _ => le_trans⟩
  refine ⟨(G.edgeFinset.toList).insertionSort (fun a b => w a ≤ w b),
    List.pairwise_insertionSort _ _, fun e => ?_⟩
  rw [List.mem_insertionSort, Finset.mem_toList, mem_edgeFinset]

/-- CO-273, CO-274. Kruskal's algorithm in full: sort the edges of the connected graph `G` by
weight, then run `kruskal`; the result is a minimum weight spanning tree. -/
@[kb "kellertrotter2017" "Algorithm 12.8, p. 267"]
theorem kruskal_sorted_isMinSpanningTree {G : SimpleGraph V} (hG : G.Connected)
    (w : Sym2 V → ℝ) :
    ∃ l : List (Sym2 V), l.Pairwise (fun a b => w a ≤ w b) ∧ IsMinSpanningTree G w (kruskal l) := by
  obtain ⟨l, hs, hl⟩ := exists_sorted_edge_list G w
  exact ⟨l, hs, kruskal_isMinSpanningTree hG w l hs hl⟩

/-! ### Prim's algorithm -/

/-- CO-275. Prim's algorithm, grown from the root `r`: `PrimReach G w r F` says `F` is a forest that
can arise by starting from the empty graph and repeatedly adding a lightest edge `ab` of `G` with
`a` in the component of `r` and `b` outside it (ties broken arbitrarily). -/
@[kb "kellertrotter2017" "Algorithm 12.10, p. 268"]
inductive PrimReach (G : SimpleGraph V) (w : Sym2 V → ℝ) (r : V) : SimpleGraph V → Prop
  | start : PrimReach G w r ⊥
  | step {F : SimpleGraph V} {a b : V} : PrimReach G w r F → G.Adj a b → F.Reachable r a →
      ¬ F.Reachable r b →
      (∀ c d, G.Adj c d → F.Reachable r c → ¬ F.Reachable r d → w s(a, b) ≤ w s(c, d)) →
      PrimReach G w r (F ⊔ fromEdgeSet {s(a, b)})

/-- Prim's invariant: every graph produced lies in a minimum weight spanning tree. -/
theorem PrimReach.exists_le {G : SimpleGraph V} (hG : G.Connected) {w : Sym2 V → ℝ} {r : V}
    {F : SimpleGraph V} (h : PrimReach G w r F) : ∃ T, IsMinSpanningTree G w T ∧ F ≤ T := by
  induction h with
  | start =>
    obtain ⟨T0, hT0⟩ := exists_isMinSpanningTree w hG
    exact ⟨T0, hT0, bot_le⟩
  | @step F a b _ hab ha hb hmin ih =>
    obtain ⟨T, hT, hFT⟩ := ih
    obtain ⟨T1, hT1, hFT1, hT1ab⟩ := lemma_12_6_global w hT hFT {v | F.Reachable r v}
      (fun p q hpq hp => hp.trans hpq.reachable) ha hb hab hmin
    exact ⟨T1, hT1, sup_le hFT1 (fromEdgeSet_le_of_adj hT1ab)⟩

/-- CO-276. Correctness of Prim's algorithm: a run that has reached every vertex outputs a minimum
weight spanning tree. -/
@[kb "kellertrotter2017" "text (correctness of Prim's Algorithm), p. 268"]
theorem PrimReach.isMinSpanningTree {G : SimpleGraph V} (hG : G.Connected) {w : Sym2 V → ℝ}
    {r : V} {F : SimpleGraph V} (h : PrimReach G w r F) (hall : ∀ v, F.Reachable r v) :
    IsMinSpanningTree G w F := by
  obtain ⟨T, hT, hFT⟩ := h.exists_le hG
  have : F = T := eq_of_reachable_le hT.1 hFT fun u v => (hall u).symm.trans (hall v)
  rw [this]
  exact hT

/-- A Prim run that reaches every vertex exists (the algorithm terminates) when `G` is connected. -/
theorem prim_exists_complete {G : SimpleGraph V} (hG : G.Connected) (w : Sym2 V → ℝ) (r : V) :
    ∃ F, PrimReach G w r F ∧ ∀ v, F.Reachable r v := by
  have key : ∀ n : ℕ, ∀ F, PrimReach G w r F →
      (Finset.univ.filter fun v => ¬ F.Reachable r v).card = n →
      ∃ F', PrimReach G w r F' ∧ ∀ v, F'.Reachable r v := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro F hF hn
      by_cases hall : ∀ v, F.Reachable r v
      · exact ⟨F, hF, hall⟩
      push Not at hall
      obtain ⟨v, hv⟩ := hall
      obtain ⟨q⟩ := hG.preconnected r v
      obtain ⟨d, -, hd1, hd2⟩ := q.exists_boundary_dart {u | F.Reachable r u}
        (Reachable.refl _) hv
      have hne : (Finset.univ.filter fun p : V × V =>
          G.Adj p.1 p.2 ∧ F.Reachable r p.1 ∧ ¬ F.Reachable r p.2).Nonempty :=
        ⟨(d.fst, d.snd), Finset.mem_filter.2 ⟨Finset.mem_univ _, d.adj, hd1, hd2⟩⟩
      obtain ⟨⟨a, b⟩, hab, hmin⟩ := Finset.exists_min_image _ (fun p : V × V => w s(p.1, p.2)) hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hab hmin
      have hstep := PrimReach.step hF hab.1 hab.2.1 hab.2.2
        (fun c d hcd hc hd => hmin (c, d) ⟨hcd, hc, hd⟩)
      have hne' : a ≠ b := fun h => hab.2.2 (h ▸ hab.2.1)
      have hadj : (F ⊔ fromEdgeSet {s(a, b)}).Adj a b :=
        Or.inr (by rw [fromEdgeSet_adj]; exact ⟨rfl, hne'⟩)
      have hlt : (Finset.univ.filter fun v => ¬ (F ⊔ fromEdgeSet {s(a, b)}).Reachable r v).card <
          n := by
        rw [← hn]
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨b, ?_, ?_⟩
          · simpa using hab.2.2
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
            exact (hab.2.1.mono le_sup_left).trans hadj.reachable
        · intro u hu
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
          exact fun h => hu (h.mono le_sup_left)
      exact ih _ (hn ▸ hlt) _ hstep rfl
  exact key _ ⊥ PrimReach.start rfl

end UndergradKB.Combinatorics.SpanningTree
