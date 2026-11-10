import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Finset.Max
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.Graph.Coloring

/-!
# Brooks' theorem (Keller–Trotter, Exercise 5.9.43)

* CO-128: a connected graph of maximum degree at most `k` is `k`-colourable, unless it is a
  complete graph `K_{k+1}` or (for `k = 2`) an odd cycle.

The proof follows Lovász (1975).  The basic tool is a greedy colouring along "decreasing distance
from a deficient vertex" (`greedy`).  A connected graph with a vertex of degree `< k` is
`k`-colourable; for a `k`-regular graph one either glues colourings along a cut vertex, or finds
a vertex `u` with non-adjacent neighbours `a, b` such that `G - a - b` is connected, colours
`a, b` alike, and then colours greedily towards `u`.
-/

namespace UndergradKB.Combinatorics

open SimpleGraph

set_option linter.unusedSectionVars false

namespace Brooks

variable {V : Type*}

/-- The graph `G` restricted to the vertex set `S`, kept as a graph on all of `V`. -/
def restrict (G : SimpleGraph V) (S : Set V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ a ∈ S ∧ b ∈ S
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩

/-- Walk distance from `v` to the set `Z` in `H`. -/
noncomputable def zdist (H : SimpleGraph V) (Z : Set V) (v : V) : ℕ :=
  sInf {n | ∃ z ∈ Z, ∃ p : H.Walk v z, p.length = n}

lemma exists_closer (H : SimpleGraph V) (Z : Set V) {v : V} (hv : v ∉ Z)
    (hr : ∃ z ∈ Z, H.Reachable v z) : ∃ w, H.Adj v w ∧ zdist H Z w < zdist H Z v := by
  obtain ⟨z, hz, ⟨p0⟩⟩ := hr
  have hne : {n | ∃ z ∈ Z, ∃ p : H.Walk v z, p.length = n}.Nonempty := ⟨_, z, hz, p0, rfl⟩
  obtain ⟨z', hz', p, hp⟩ := Nat.sInf_mem hne
  cases p with
  | nil => exact absurd hz' hv
  | @cons _ w _ h q =>
    refine ⟨w, h, ?_⟩
    have h1 : zdist H Z w ≤ q.length := Nat.sInf_le ⟨z', hz', q, rfl⟩
    have h2 : (Walk.cons h q).length = zdist H Z v := hp
    rw [Walk.length_cons] at h2
    omega

/-- A colouring `c` is proper on the vertex set `S`. -/
def ProperOn (G : SimpleGraph V) {k : ℕ} (c : V → Fin k) (S : Set V) : Prop :=
  ∀ ⦃v w⦄, v ∈ S → w ∈ S → G.Adj v w → c v ≠ c w

lemma ProperOn.mono {G : SimpleGraph V} {k : ℕ} {c : V → Fin k} {S S' : Set V}
    (h : ProperOn G c S) (hS : S' ⊆ S) : ProperOn G c S' :=
  fun _ _ hv hw hvw => h (hS hv) (hS hw) hvw

lemma colorable_of_properOn_univ {G : SimpleGraph V} {k : ℕ} {c : V → Fin k}
    (h : ProperOn G c Set.univ) : G.Colorable k :=
  ⟨Coloring.mk c fun hadj => h trivial trivial hadj⟩

/-- Adding one vertex `a` with a colour avoiding its coloured neighbours keeps the colouring
proper. -/
lemma ProperOn.insert_update [DecidableEq V] {G : SimpleGraph V} {k : ℕ} {c : V → Fin k}
    {S : Set V} (h : ProperOn G c S) {a : V} (ha : a ∉ S) {col : Fin k}
    (hcol : ∀ w ∈ S, G.Adj a w → c w ≠ col) :
    ProperOn G (Function.update c a col) (insert a S) := by
  intro v w hv hw hvw
  by_cases hva : v = a
  · subst hva
    have hwa : w ≠ v := (G.ne_of_adj hvw).symm
    have hwS : w ∈ S := (Set.mem_insert_iff.mp hw).resolve_left hwa
    rw [Function.update_self, Function.update_of_ne hwa]
    exact (hcol w hwS hvw).symm
  · by_cases hwa : w = a
    · subst hwa
      have hvS : v ∈ S := (Set.mem_insert_iff.mp hv).resolve_left hva
      rw [Function.update_self, Function.update_of_ne hva]
      exact hcol v hvS hvw.symm
    · have hvS : v ∈ S := (Set.mem_insert_iff.mp hv).resolve_left hva
      have hwS : w ∈ S := (Set.mem_insert_iff.mp hw).resolve_left hwa
      rw [Function.update_of_ne hva, Function.update_of_ne hwa]
      exact h hvS hwS hvw

/-- A set of fewer than `k` vertices leaves a free colour among `Fin k`. -/
lemma exists_free_colour {k : ℕ} (c : V → Fin k) (N : Finset V) (hN : N.card < k) :
    ∃ col : Fin k, ∀ w ∈ N, c w ≠ col := by
  classical
  by_contra hcon
  push Not at hcon
  have hsub : (Finset.univ : Finset (Fin k)) ⊆ N.image c := by
    intro col _
    obtain ⟨w, hw, hwc⟩ := hcon col
    exact Finset.mem_image.mpr ⟨w, hw, hwc⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_image_le (s := N) (f := c)
  simp only [Finset.card_univ, Fintype.card_fin] at h1
  omega

section Greedy

variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The greedy lemma.  Starting from a colouring `c₀` that is proper on `S₀`, the vertices of `T`
can be coloured one after another (farthest from the outside of `S₀ ∪ T` first, distances taken
in `G - S₀`), provided each has a path, avoiding `S₀`, to a vertex outside `S₀ ∪ T`. -/
lemma greedy {k : ℕ} (hdeg : ∀ v, G.degree v ≤ k) (S₀ T : Finset V) (hd : Disjoint S₀ T)
    (c₀ : V → Fin k) (hc₀ : ProperOn G c₀ S₀)
    (hreach : ∀ v ∈ T, ∃ z, z ∉ S₀ ∧ z ∉ T ∧ (restrict G ((S₀ : Set V)ᶜ)).Reachable v z) :
    ∃ c : V → Fin k, (∀ v ∈ S₀, c v = c₀ v) ∧ ProperOn G c ↑(S₀ ∪ T) := by
  set H := restrict G ((S₀ : Set V)ᶜ) with hH
  set Z : Set V := {z | z ∉ S₀ ∧ z ∉ T} with hZ
  let f : V → ℤ := fun v => -(zdist H Z v : ℤ)
  have key : ∀ T' : Finset V, T' ⊆ T →
      ∃ c : V → Fin k, (∀ v ∈ S₀, c v = c₀ v) ∧ ProperOn G c ↑(S₀ ∪ T') := by
    intro T'
    induction T' using Finset.induction_on_max_value f with
    | empty =>
      intro _
      exact ⟨c₀, fun _ _ => rfl, by simpa using hc₀⟩
    | insert a s has hmax ih =>
      intro hsub
      have hsT : s ⊆ T := (Finset.subset_insert a s).trans hsub
      obtain ⟨c, hc1, hc2⟩ := ih hsT
      have haT : a ∈ T := hsub (Finset.mem_insert_self a s)
      have haS : a ∉ S₀ := fun h => Finset.disjoint_left.mp hd h haT
      obtain ⟨z, hz1, hz2, hzr⟩ := hreach a haT
      have haZ : a ∉ Z := fun h => h.2 haT
      obtain ⟨w, hw, hwlt⟩ := exists_closer H Z haZ ⟨z, ⟨hz1, hz2⟩, hzr⟩
      have hwG : G.Adj a w := hw.1
      have hwS : w ∉ S₀ := hw.2.2
      have hws : w ∉ s := by
        intro hws
        have := hmax w hws
        simp only [f] at this
        omega
      have hcard : ((G.neighborFinset a).filter (fun x => x ∈ S₀ ∪ s)).card < k := by
        have hsub2 : (G.neighborFinset a).filter (fun x => x ∈ S₀ ∪ s) ⊆
            (G.neighborFinset a).erase w := by
          intro x hx
          rw [Finset.mem_filter] at hx
          refine Finset.mem_erase.mpr ⟨?_, hx.1⟩
          rintro rfl
          rcases Finset.mem_union.mp hx.2 with h | h
          · exact hwS h
          · exact hws h
        have h1 := Finset.card_le_card hsub2
        rw [Finset.card_erase_of_mem ((mem_neighborFinset _ _ _).mpr hwG),
          card_neighborFinset_eq_degree] at h1
        have h2 := hdeg a
        have h3 : 0 < G.degree a := by
          rw [← card_neighborFinset_eq_degree]
          exact Finset.card_pos.mpr ⟨w, (mem_neighborFinset _ _ _).mpr hwG⟩
        omega
      obtain ⟨col, hcol⟩ := exists_free_colour c _ hcard
      refine ⟨Function.update c a col, fun v hv => ?_, ?_⟩
      · rw [Function.update_of_ne (by rintro rfl; exact haS hv)]
        exact hc1 v hv
      · have hins : (↑(S₀ ∪ insert a s) : Set V) = insert a ↑(S₀ ∪ s) := by
          ext x; simp
        rw [hins]
        refine ProperOn.insert_update hc2 ?_ ?_
        · intro h
          rcases Finset.mem_union.mp (Finset.mem_coe.mp h) with h | h
          · exact haS h
          · exact has h
        · intro x hx hax
          exact hcol x (Finset.mem_filter.mpr ⟨(mem_neighborFinset _ _ _).mpr hax,
            Finset.mem_coe.mp hx⟩)
  exact key T le_rfl

/-- A proper induced subgraph of a connected graph of maximum degree `≤ k` has a proper
`k`-colouring. -/
lemma exists_properOn_of_ne_univ {k : ℕ} (hk : 0 < k) (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v ≤ k)
    (S : Finset V) (hS : S ≠ Finset.univ) : ∃ c : V → Fin k, ProperOn G c ↑S := by
  obtain ⟨z, hz⟩ : ∃ z, z ∉ S := by
    by_contra h
    push Not at h
    exact hS (Finset.eq_univ_iff_forall.mpr h)
  obtain ⟨c, -, hc⟩ := greedy G hdeg ∅ S (Finset.disjoint_empty_left _)
    (fun _ => (⟨0, hk⟩ : Fin k)) (by intro v w hv; simp at hv)
    (by
      intro v _
      refine ⟨z, by simp, hz, ?_⟩
      refine Reachable.mono ?_ (hconn.preconnected v z)
      intro a b hab
      exact ⟨hab, by simp, by simp⟩)
  exact ⟨c, by simpa using hc⟩

/-- Case A. A connected graph of maximum degree `≤ k` with a vertex of degree `< k` is
`k`-colourable. -/
lemma colorable_of_deficient {k : ℕ} (hconn : G.Connected) (hdeg : ∀ v, G.degree v ≤ k)
    (r : V) (hr : G.degree r < k) : G.Colorable k := by
  obtain ⟨c, hc⟩ := exists_properOn_of_ne_univ G (by omega) hconn hdeg (Finset.univ.erase r) (by
    intro h
    have h1 := Finset.mem_univ r
    rw [← h] at h1
    simp at h1)
  have hcard : (G.neighborFinset r).card < k := by
    rw [card_neighborFinset_eq_degree]; exact hr
  obtain ⟨col, hcol⟩ := exists_free_colour c _ hcard
  refine colorable_of_properOn_univ (c := Function.update c r col) ?_
  have hins : (Set.univ : Set V) = insert r ↑(Finset.univ.erase r) := by
    ext x; simp
  rw [hins]
  refine ProperOn.insert_update hc (by simp) ?_
  intro x _ hax
  exact hcol x ((mem_neighborFinset _ _ _).mpr hax)

/-- Lovász' colouring step.  If `a, b` are non-adjacent neighbours of `u` and `G - a - b` is
connected, then `G` is `k`-colourable: give `a, b` the same colour and colour the rest greedily,
farthest from `u` first. -/
lemma colorable_of_triple {k : ℕ} (hk : 0 < k) (hdeg : ∀ v, G.degree v ≤ k) {u a b : V}
    (hua : G.Adj u a) (hub : G.Adj u b) (hab : ¬ G.Adj a b) (hne : a ≠ b)
    (hreach : ∀ v, v ≠ a → v ≠ b →
      (restrict G ((({a, b} : Finset V) : Set V)ᶜ)).Reachable v u) :
    G.Colorable k := by
  have hua' : u ≠ a := G.ne_of_adj hua
  have hub' : u ≠ b := G.ne_of_adj hub
  set S₀ : Finset V := {a, b} with hS₀
  set T : Finset V := Finset.univ \ insert u S₀ with hT
  have hdisj : Disjoint S₀ T :=
    Finset.disjoint_left.mpr fun x hx hxT =>
      (Finset.mem_sdiff.mp hxT).2 (Finset.mem_insert_of_mem hx)
  have huS : u ∉ S₀ := by simp [hS₀, hua', hub']
  have huT : u ∉ T := by simp [hT]
  obtain ⟨c, hc1, hc2⟩ := greedy G hdeg S₀ T hdisj (fun _ => (⟨0, hk⟩ : Fin k))
    (by
      intro v w hv hw hvw
      simp only [hS₀, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hv hw
      rcases hv with rfl | rfl <;> rcases hw with rfl | rfl <;>
        first
        | exact absurd hvw hab
        | exact absurd hvw.symm hab
        | exact absurd hvw (G.loopless.irrefl _))
    (by
      intro v hv
      have hv' := Finset.mem_sdiff.mp hv
      refine ⟨u, huS, huT, hreach v ?_ ?_⟩
      · intro h; exact hv'.2 (by simp [hS₀, h])
      · intro h; exact hv'.2 (by simp [hS₀, h]))
  have ca : c a = ⟨0, hk⟩ := hc1 a (by simp [hS₀])
  have cb : c b = ⟨0, hk⟩ := hc1 b (by simp [hS₀])
  have haN : a ∈ (G.neighborFinset u).erase b :=
    Finset.mem_erase.mpr ⟨hne, (mem_neighborFinset _ _ _).mpr hua⟩
  have hcard : ((G.neighborFinset u).erase b).card < k := by
    rw [Finset.card_erase_of_mem ((mem_neighborFinset _ _ _).mpr hub),
      card_neighborFinset_eq_degree]
    have := hdeg u
    omega
  obtain ⟨col, hcol⟩ := exists_free_colour c _ hcard
  refine colorable_of_properOn_univ (c := Function.update c u col) ?_
  have hins : (Set.univ : Set V) = insert u ↑(S₀ ∪ T) := by
    ext x
    by_cases hx : x = u
    · simp [hx]
    · have : x ∈ S₀ ∨ x ∈ T := by
        by_cases h : x ∈ S₀
        · exact Or.inl h
        · exact Or.inr (by simp [hT, hx, h])
      simp [this]
  rw [hins]
  refine ProperOn.insert_update hc2 (by simp [huS, huT]) ?_
  intro w _ huw
  by_cases hwb : w = b
  · subst hwb
    rw [cb, ← ca]
    exact hcol a haN
  · exact hcol w (Finset.mem_erase.mpr ⟨hwb, (mem_neighborFinset _ _ _).mpr huw⟩)

end Greedy

/-! ### Separations and cut vertices -/

section Sep

variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `C` is cut off from the rest of the graph by `Z`: `C` is nonempty, some vertex lies outside
`Z ∪ C`, and all neighbours of `C` lie in `Z ∪ C`. -/
def IsSep (Z C : Finset V) : Prop :=
  C.Nonempty ∧ Disjoint Z C ∧ (∃ r, r ∉ Z ∧ r ∉ C) ∧ ∀ v ∈ C, ∀ w, G.Adj v w → w ∈ Z ∨ w ∈ C

/-- Gluing at a cut vertex. -/
lemma colorable_of_cut {k : ℕ} (hk : 0 < k) (hconn : G.Connected) (hdeg : ∀ v, G.degree v ≤ k)
    {x : V} {C : Finset V} (h : IsSep G {x} C) : G.Colorable k := by
  obtain ⟨⟨q, hq⟩, hdis, ⟨r, hrx, hrC⟩, hN⟩ := h
  have hrx' : r ≠ x := by simpa using hrx
  have hxC : x ∉ C := fun hx => Finset.disjoint_left.mp hdis (Finset.mem_singleton_self x) hx
  have hqx : q ≠ x := fun h => hxC (h ▸ hq)
  set R : Finset V := Finset.univ.filter (fun v => v ≠ x ∧ v ∉ C) with hR
  have hRmem : ∀ v, v ∈ R ↔ v ≠ x ∧ v ∉ C := by intro v; simp [hR]
  have hno : ∀ v ∈ C, ∀ w ∈ R, ¬ G.Adj v w := by
    intro v hv w hw hvw
    rcases hN v hv w hvw with h | h
    · exact ((hRmem w).mp hw).1 (by simpa using h)
    · exact ((hRmem w).mp hw).2 h
  obtain ⟨c1, hc1⟩ := exists_properOn_of_ne_univ G hk hconn hdeg (insert x C) (by
    intro h
    have h1 := Finset.mem_univ r
    rw [← h] at h1
    simp only [Finset.mem_insert] at h1
    tauto)
  obtain ⟨c2, hc2⟩ := exists_properOn_of_ne_univ G hk hconn hdeg (insert x R) (by
    intro h
    have h1 := Finset.mem_univ q
    rw [← h] at h1
    simp only [Finset.mem_insert, hRmem] at h1
    tauto)
  set σ : Equiv.Perm (Fin k) := Equiv.swap (c2 x) (c1 x) with hσ
  let c : V → Fin k := fun v => if v ∈ R then σ (c2 v) else c1 v
  have hcx : c x = c1 x := by
    have : x ∉ R := fun h => ((hRmem x).mp h).1 rfl
    simp [c, this]
  have hRcase : ∀ v w, G.Adj v w → v ∈ R → c v ≠ c w := by
    intro v w hvw hv
    have hvc : c v = σ (c2 v) := by simp [c, hv]
    by_cases hwR : w ∈ R
    · have hwc : c w = σ (c2 w) := by simp [c, hwR]
      rw [hvc, hwc]
      intro he
      exact hc2 (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hv))
        (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hwR)) hvw (σ.injective he)
    · have hwx : w = x := by
        by_contra hwx
        have hwC : w ∈ C := by
          by_contra hwC
          exact hwR ((hRmem w).mpr ⟨hwx, hwC⟩)
        exact hno w hwC v hv hvw.symm
      subst hwx
      rw [hvc, hcx]
      have : c1 w = σ (c2 w) := by simp [hσ]
      rw [this]
      intro he
      exact hc2 (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hv))
        (Finset.mem_coe.mpr (Finset.mem_insert_self _ _)) hvw (σ.injective he)
  have hNR : ∀ v w, G.Adj v w → v ∉ R → w ∉ R → c v ≠ c w := by
    intro v w hvw hv hw
    have hvc : c v = c1 v := by simp [c, hv]
    have hwc : c w = c1 w := by simp [c, hw]
    have hmem : ∀ y, y ∉ R → y ∈ (insert x C : Finset V) := by
      intro y hy
      by_cases hyx : y = x
      · simp [hyx]
      · have : y ∈ C := by
          by_contra hyC; exact hy ((hRmem y).mpr ⟨hyx, hyC⟩)
        simp [this]
    rw [hvc, hwc]
    exact hc1 (Finset.mem_coe.mpr (hmem v hv)) (Finset.mem_coe.mpr (hmem w hw)) hvw
  refine colorable_of_properOn_univ (c := c) (fun v w _ _ hvw => ?_)
  by_cases hv : v ∈ R
  · exact hRcase v w hvw hv
  · by_cases hw : w ∈ R
    · exact (hRcase w v hvw.symm hw).symm
    · exact hNR v w hvw hv hw

open Classical in
/-- The vertices outside `Z` that cannot reach `u` in `G - Z`. -/
noncomputable def Lset (Z : Finset V) (u : V) : Finset V :=
  Finset.univ.filter fun w => w ∉ Z ∧ ¬ (restrict G ((Z : Set V)ᶜ)).Reachable w u

lemma mem_Lset {Z : Finset V} {u w : V} :
    w ∈ Lset G Z u ↔ w ∉ Z ∧ ¬ (restrict G ((Z : Set V)ᶜ)).Reachable w u := by
  classical
  simp [Lset]

lemma Lset_closed {Z : Finset V} {u w x : V} (hw : w ∈ Lset G Z u) (hwx : G.Adj w x) :
    x ∈ Z ∨ x ∈ Lset G Z u := by
  by_contra h
  push Not at h
  rw [mem_Lset] at hw h
  have hx : (restrict G ((Z : Set V)ᶜ)).Reachable x u := by
    by_contra hx; exact h.2 ⟨h.1, hx⟩
  apply hw.2
  have hadj : (restrict G ((Z : Set V)ᶜ)).Adj w x := ⟨hwx, hw.1, h.1⟩
  exact hadj.reachable.trans hx

lemma self_notMem_Lset (Z : Finset V) (u : V) : u ∉ Lset G Z u := by
  rw [mem_Lset]
  exact fun h => h.2 (Reachable.refl u)

lemma isSep_Lset {Z : Finset V} {u : V} (hu : u ∉ Z) (hne : (Lset G Z u).Nonempty) :
    IsSep G Z (Lset G Z u) :=
  ⟨hne, Finset.disjoint_left.mpr fun w hwZ hwL => ((mem_Lset G).mp hwL).1 hwZ,
    ⟨u, hu, self_notMem_Lset G Z u⟩, fun _ hv _ hvw => Lset_closed G hv hvw⟩

/-- In a connected graph that is not complete, some vertex has two non-adjacent neighbours. -/
lemma exists_vee (hconn : G.Connected) (hG : G ≠ ⊤) :
    ∃ u a b, G.Adj u a ∧ G.Adj u b ∧ a ≠ b ∧ ¬ G.Adj a b := by
  by_contra hcon
  push Not at hcon
  have hwalk : ∀ {s t : V} (p : G.Walk s t), s = t ∨ G.Adj s t := by
    intro s t p
    induction p with
    | nil => exact Or.inl rfl
    | @cons s s' t h p ih =>
      rcases ih with rfl | hadj
      · exact Or.inr h
      · by_cases hst : s = t
        · exact Or.inl hst
        · exact Or.inr (hcon s' s t h.symm hadj hst)
  apply hG
  ext p q
  simp only [top_adj]
  constructor
  · exact fun h => G.ne_of_adj h
  · intro hpq
    obtain ⟨w⟩ := hconn.preconnected p q
    exact (hwalk w).resolve_left hpq

lemma card_lt_of_erase {C D : Finset V} {a : V} (hD : D ⊆ C) (ha : a ∈ C) (haD : a ∉ D) :
    D.card < C.card :=
  Finset.card_lt_card ((Finset.ssubset_iff_of_subset hD).mpr ⟨a, ha, haD⟩)

/-- The heart of Lovász' argument: if `{u, y}` cuts off a fragment `C` of minimal size and the
graph has no cut vertex and all degrees are at least `3`, there is a triple `u, a, b` with
`a, b` non-adjacent neighbours of `u` and `G - a - b` connected. -/
lemma exists_triple_of_min (h3 : ∀ v, 3 ≤ G.degree v) (hnc : ∀ x C, ¬ IsSep G {x} C)
    {u y : V} {C : Finset V} (hsep : IsSep G {u, y} C)
    (hmin : ∀ p q D, IsSep G {p, q} D → C.card ≤ D.card) :
    ∃ u a b, G.Adj u a ∧ G.Adj u b ∧ ¬ G.Adj a b ∧ a ≠ b ∧
      ∀ v, v ≠ a → v ≠ b → (restrict G ((({a, b} : Finset V) : Set V)ᶜ)).Reachable v u := by
  have hsep' := hsep
  obtain ⟨hCne, hdis, ⟨r0, hr0Z, hr0C⟩, hN⟩ := hsep
  have huC : u ∉ C := fun h => Finset.disjoint_left.mp hdis (by simp) h
  have hyC : y ∉ C := fun h => Finset.disjoint_left.mp hdis (by simp) h
  have hCnbr : ∀ v ∈ C, ∀ w, G.Adj v w → w = u ∨ w = y ∨ w ∈ C := by
    intro v hv w hvw
    simpa [or_assoc] using hN v hv w hvw
  have hr0u : r0 ≠ u := fun h => hr0Z (by simp [h])
  have hr0y : r0 ≠ y := fun h => hr0Z (by simp [h])
  have huy : u ≠ y := by
    intro h
    subst h
    exact hnc u C (by simpa using hsep')
  obtain ⟨q0, hq0⟩ := hCne
  -- the part of the graph beyond `{u, y}`
  set Rs : Finset V := Finset.univ.filter (fun v => v ≠ u ∧ v ≠ y ∧ v ∉ C) with hRs
  have hRsmem : ∀ v, v ∈ Rs ↔ v ≠ u ∧ v ≠ y ∧ v ∉ C := by intro v; simp [hRs]
  have hr0R : r0 ∈ Rs := (hRsmem r0).mpr ⟨hr0u, hr0y, hr0C⟩
  -- `u` has a neighbour in `C`
  obtain ⟨a, haC, hua⟩ : ∃ a ∈ C, G.Adj u a := by
    by_contra hno
    push Not at hno
    refine hnc y C ⟨⟨q0, hq0⟩, ?_, ⟨r0, by simpa using hr0y, hr0C⟩, ?_⟩
    · simpa using hyC
    · intro v hv w hvw
      rcases hCnbr v hv w hvw with h | h | h
      · exact absurd (h ▸ hvw.symm) (hno v hv)
      · simp [h]
      · exact Or.inr h
  -- `u` has a neighbour in `Rs`
  obtain ⟨b, hbR, hub⟩ : ∃ b ∈ Rs, G.Adj u b := by
    by_contra hno
    push Not at hno
    refine hnc y Rs ⟨⟨r0, hr0R⟩, ?_, ⟨q0, by simpa using (fun h : q0 = y => hyC (h ▸ hq0)),
      fun h => ((hRsmem q0).mp h).2.2 hq0⟩, ?_⟩
    · simpa [hRsmem] using fun _ => rfl
    · intro v hv w hvw
      by_cases hwR : w ∈ Rs
      · exact Or.inr hwR
      · by_cases hwC : w ∈ C
        · exfalso
          have := hCnbr w hwC v hvw.symm
          have hv' := (hRsmem v).mp hv
          tauto
        · by_cases hwu : w = u
          · subst hwu; exact absurd hvw.symm (hno v hv)
          · by_cases hwy : w = y
            · simp [hwy]
            · exact absurd ((hRsmem w).mpr ⟨hwu, hwy, hwC⟩) hwR
  have hbR' := (hRsmem b).mp hbR
  have hbC : b ∉ C := hbR'.2.2
  have hab : ¬ G.Adj a b := by
    intro h
    rcases hCnbr a haC b h with h | h | h
    · exact hbR'.1 h
    · exact hbR'.2.1 h
    · exact hbC h
  have hne : a ≠ b := fun h => hbC (h ▸ haC)
  have hau : u ≠ a := G.ne_of_adj hua
  have hbu : u ≠ b := G.ne_of_adj hub
  have hay : y ≠ a := fun h => hyC (h ▸ haC)
  have hbCa : ∀ v ∈ C, v ≠ b := fun v hv h => hbC (h ▸ hv)
  have hbnb : ∀ v ∈ C, ¬ G.Adj v b := by
    intro v hv h
    rcases hCnbr v hv b h with h | h | h
    · exact hbR'.1 h
    · exact hbR'.2.1 h
    · exact hbC h
  refine ⟨u, a, b, hua, hub, hab, hne, ?_⟩
  intro v hva hvb
  by_contra hnr
  set Z : Finset V := {a, b} with hZ
  set L : Finset V := Lset G Z u with hL
  have hvZ : v ∉ Z := by simp [hZ, hva, hvb]
  have hvL : v ∈ L := (mem_Lset G).mpr ⟨hvZ, hnr⟩
  have huZ : u ∉ Z := by simp [hZ, hau, hbu]
  have huL : u ∉ L := self_notMem_Lset G Z u
  have haL : a ∉ L := fun h => ((mem_Lset G).mp h).1 (by simp [hZ])
  have hLcl : ∀ w ∈ L, ∀ x, G.Adj w x → x = a ∨ x = b ∨ x ∈ L := by
    intro w hw x hwx
    simpa [hZ, or_assoc] using Lset_closed G hw hwx
  -- the vertex `y` is not cut off
  have hyL : y ∉ L := by
    intro hyL
    -- vertices of `C` not in `L`
    have hD1 : C.filter (fun w => w ≠ a ∧ w ∉ L) = ∅ := by
      by_contra hne1
      have hne1' : (C.filter (fun w => w ≠ a ∧ w ∉ L)).Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr hne1
      have hs : IsSep G {a, u} (C.filter (fun w => w ≠ a ∧ w ∉ L)) := by
        refine ⟨hne1', ?_, ⟨y, ?_, ?_⟩, ?_⟩
        · refine Finset.disjoint_left.mpr fun x hx hx2 => ?_
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          simp only [Finset.mem_filter] at hx2
          rcases hx with rfl | rfl
          · exact hx2.2.1 rfl
          · exact huC hx2.1
        · simp [hay, huy.symm]
        · simp [hyC]
        · intro v hv w hvw
          simp only [Finset.mem_filter] at hv
          rcases hCnbr v hv.1 w hvw with h | h | h
          · simp [h]
          · exfalso
            rw [h] at hvw
            rcases hLcl y hyL v hvw.symm with h' | h' | h'
            · exact hv.2.1 h'
            · exact hbCa v hv.1 h'
            · exact hv.2.2 h'
          · by_cases hwa : w = a
            · simp [hwa]
            · right
              simp only [Finset.mem_filter]
              refine ⟨h, hwa, fun hwL => ?_⟩
              rcases hLcl w hwL v hvw.symm with h' | h' | h'
              · exact hv.2.1 h'
              · exact hbCa v hv.1 h'
              · exact hv.2.2 h'
      have h1 := hmin a u _ hs
      have h2 := card_lt_of_erase (Finset.filter_subset (fun w => w ≠ a ∧ w ∉ L) C) haC
        (by simp)
      omega
    have hD2 : C.filter (fun w => w ∈ L) = ∅ := by
      by_contra hne1
      have hne1' : (C.filter (fun w => w ∈ L)).Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr hne1
      have hs : IsSep G {a, y} (C.filter (fun w => w ∈ L)) := by
        refine ⟨hne1', ?_, ⟨u, ?_, ?_⟩, ?_⟩
        · refine Finset.disjoint_left.mpr fun x hx hx2 => ?_
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          simp only [Finset.mem_filter] at hx2
          rcases hx with rfl | rfl
          · exact haL hx2.2
          · exact hyC hx2.1
        · simp [hau, huy]
        · simp [huC]
        · intro v hv w hvw
          simp only [Finset.mem_filter] at hv
          rcases hLcl v hv.2 w hvw with h | h | h
          · simp [h]
          · exact absurd (h ▸ hvw) (hbnb v hv.1)
          · rcases hCnbr v hv.1 w hvw with h' | h' | h'
            · exact absurd (h' ▸ h) huL
            · simp [h']
            · right
              simp only [Finset.mem_filter]
              exact ⟨h', h⟩
      have h1 := hmin a y _ hs
      have h2 := card_lt_of_erase (Finset.filter_subset (fun w => w ∈ L) C) haC
        (by simp [haL])
      omega
    -- hence `C = {a}`, contradicting the degree of `a`
    have hsub : G.neighborFinset a ⊆ {u, y} := by
      intro w hw
      rw [mem_neighborFinset] at hw
      rcases hCnbr a haC w hw with h | h | h
      · simp [h]
      · simp [h]
      · exfalso
        have hwa : w ≠ a := (G.ne_of_adj hw).symm
        by_cases hwL : w ∈ L
        · have : w ∈ C.filter (fun w => w ∈ L) := Finset.mem_filter.mpr ⟨h, hwL⟩
          rw [hD2] at this; simp at this
        · have : w ∈ C.filter (fun w => w ≠ a ∧ w ∉ L) :=
            Finset.mem_filter.mpr ⟨h, hwa, hwL⟩
          rw [hD1] at this; simp at this
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_le_two (a := u) (b := y)
    have h4 := h3 a
    rw [← card_neighborFinset_eq_degree] at h4
    omega
  -- now `y` is in the same class as `u`; the rest of `L` would be cut off by `a` or `b`
  have hL1 : L.filter (fun w => w ∈ C) = ∅ := by
    by_contra hne1
    refine hnc a _ ⟨Finset.nonempty_iff_ne_empty.mpr hne1, ?_, ⟨u, by simpa using hau, ?_⟩, ?_⟩
    · exact Finset.disjoint_left.mpr fun x hx hx2 => by
        simp only [Finset.mem_singleton] at hx
        subst hx
        exact haL (Finset.mem_filter.mp hx2).1
    · simp [huL]
    · intro v hv w hvw
      simp only [Finset.mem_filter] at hv
      rcases hLcl v hv.1 w hvw with h | h | h
      · simp [h]
      · exact absurd (h ▸ hvw) (hbnb v hv.2)
      · rcases hCnbr v hv.2 w hvw with h' | h' | h'
        · exact absurd (h' ▸ h) huL
        · exact absurd (h' ▸ h) hyL
        · right
          simp only [Finset.mem_filter]
          exact ⟨h, h'⟩
  have hL2 : L.filter (fun w => w ∉ C) = ∅ := by
    by_contra hne1
    refine hnc b _ ⟨Finset.nonempty_iff_ne_empty.mpr hne1, ?_, ⟨u, by simpa using hbu, ?_⟩, ?_⟩
    · refine Finset.disjoint_left.mpr fun x hx hx2 => ?_
      simp only [Finset.mem_singleton] at hx
      subst hx
      exact ((mem_Lset G).mp (Finset.mem_filter.mp hx2).1).1 (by simp [hZ])
    · simp [huL]
    · intro v hv w hvw
      simp only [Finset.mem_filter] at hv
      rcases hLcl v hv.1 w hvw with h | h | h
      · exfalso
        subst h
        rcases hCnbr w haC v hvw.symm with h' | h' | h'
        · exact huL (h' ▸ hv.1)
        · exact hyL (h' ▸ hv.1)
        · exact hv.2 h'
      · simp [h]
      · by_cases hwC : w ∈ C
        · exfalso
          rcases hCnbr w hwC v hvw.symm with h' | h' | h'
          · exact huL (h' ▸ hv.1)
          · exact hyL (h' ▸ hv.1)
          · exact hv.2 h'
        · right
          simp only [Finset.mem_filter]
          exact ⟨h, hwC⟩
  by_cases hvC : v ∈ C
  · have : v ∈ L.filter (fun w => w ∈ C) := Finset.mem_filter.mpr ⟨hvL, hvC⟩
    rw [hL1] at this; simp at this
  · have : v ∈ L.filter (fun w => w ∉ C) := Finset.mem_filter.mpr ⟨hvL, hvC⟩
    rw [hL2] at this; simp at this

/-- Existence of a Lovász triple in a 2-connected (cut-vertex free) graph with all degrees `≥ 3`
that is connected and not complete. -/
lemma exists_triple (hconn : G.Connected) (hG : G ≠ ⊤) (h3 : ∀ v, 3 ≤ G.degree v)
    (hnc : ∀ x C, ¬ IsSep G {x} C) :
    ∃ u a b, G.Adj u a ∧ G.Adj u b ∧ ¬ G.Adj a b ∧ a ≠ b ∧
      ∀ v, v ≠ a → v ≠ b → (restrict G ((({a, b} : Finset V) : Set V)ᶜ)).Reachable v u := by
  classical
  by_cases h2 : ∃ y z C, IsSep G {y, z} C
  · have hex : ∃ n, ∃ y z C, IsSep G {y, z} C ∧ C.card = n := by
      obtain ⟨y, z, C, h⟩ := h2
      exact ⟨_, y, z, C, h, rfl⟩
    obtain ⟨u, y, C, hsep, hcard⟩ := Nat.find_spec hex
    refine exists_triple_of_min G h3 hnc hsep fun p q D hD => ?_
    rw [hcard]
    exact Nat.find_min' hex ⟨p, q, D, hD, rfl⟩
  · obtain ⟨u, a, b, hua, hub, hne, hab⟩ := exists_vee G hconn hG
    refine ⟨u, a, b, hua, hub, hab, hne, ?_⟩
    intro v hva hvb
    by_contra hnr
    have hvZ : v ∉ ({a, b} : Finset V) := by simp [hva, hvb]
    have huZ : u ∉ ({a, b} : Finset V) := by
      simp [(G.ne_of_adj hua), (G.ne_of_adj hub)]
    exact h2 ⟨a, b, Lset G {a, b} u, isSep_Lset G huZ ⟨v, (mem_Lset G).mpr ⟨hvZ, hnr⟩⟩⟩

end Sep

end Brooks

section Main

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- CO-128 (the case of a vertex of small degree).  A connected graph of maximum degree at most
`k` that has a vertex of degree less than `k` is `k`-colourable (so Brooks' theorem holds for
all non-regular connected graphs). -/
@[kb "kellertrotter2017" "Exercise 5.9.43, p. 134"]
theorem colorable_of_connected_of_degree_lt {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (hconn : G.Connected) (hdeg : ∀ v, G.degree v ≤ k) {r : V} (hr : G.degree r < k) :
    G.Colorable k :=
  Brooks.colorable_of_deficient G hconn hdeg r hr

/-- CO-128. **Brooks' theorem** for `k ≥ 3`: a connected graph all of whose degrees are at most
`k` and which is not complete is `k`-colourable. -/
@[kb "kellertrotter2017" "Exercise 5.9.43, p. 134"]
theorem brooks {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ} (hk : 3 ≤ k)
    (hconn : G.Connected) (hdeg : ∀ v, G.degree v ≤ k) (hG : G ≠ ⊤) : G.Colorable k := by
  by_cases hlow : ∃ r, G.degree r < k
  · obtain ⟨r, hr⟩ := hlow
    exact Brooks.colorable_of_deficient G hconn hdeg r hr
  · push Not at hlow
    have h3 : ∀ v, 3 ≤ G.degree v := fun v => le_trans hk (hlow v)
    by_cases hcut : ∃ x C, Brooks.IsSep G {x} C
    · obtain ⟨x, C, h⟩ := hcut
      exact Brooks.colorable_of_cut G (by omega) hconn hdeg h
    · push Not at hcut
      obtain ⟨u, a, b, hua, hub, hab, hne, hreach⟩ := Brooks.exists_triple G hconn hG h3 hcut
      exact Brooks.colorable_of_triple G (by omega) hdeg hua hub hab hne hreach

/-- CO-128. Brooks' theorem for `k ≥ 3` in the book's shape: the graph is `k`-colourable unless it
is the complete graph `K_{k+1}`. -/
@[kb "kellertrotter2017" "Exercise 5.9.43, p. 134"]
theorem brooks_of_not_complete_succ {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (hk : 3 ≤ k) (hconn : G.Connected) (hdeg : ∀ v, G.degree v ≤ k)
    (hK : ¬ (G = ⊤ ∧ Fintype.card V = k + 1)) : G.Colorable k := by
  by_cases hG : G = ⊤
  · subst hG
    obtain ⟨v⟩ := hconn.nonempty
    have h1 : Fintype.card V - 1 ≤ k := by
      have h0 := hdeg v
      have hnb : (⊤ : SimpleGraph V).neighborFinset v = Finset.univ.erase v := by
        ext w; simp [mem_neighborFinset, eq_comm]
      rw [← card_neighborFinset_eq_degree, hnb, Finset.card_erase_of_mem (Finset.mem_univ v),
        Finset.card_univ] at h0
      exact h0
    have h2 : Fintype.card V ≤ k := by
      have : Fintype.card V ≠ k + 1 := fun h => hK ⟨rfl, h⟩
      omega
    refine ⟨Coloring.mk (fun w => Fin.castLE h2 (Fintype.equivFin V w)) ?_⟩
    intro w w' hw he
    exact (SimpleGraph.top_adj w w').mp hw
      ((Fintype.equivFin V).injective (Fin.castLE_injective h2 he))
  · exact brooks hk hconn hdeg hG

/-- CO-128. Brooks' theorem as a bound on the chromatic number. -/
@[kb "kellertrotter2017" "Exercise 5.9.43, p. 134"]
theorem chromaticNumber_le_of_brooks {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (hk : 3 ≤ k) (hconn : G.Connected) (hdeg : ∀ v, G.degree v ≤ k)
    (hK : ¬ (G = ⊤ ∧ Fintype.card V = k + 1)) : G.chromaticNumber ≤ k :=
  (brooks_of_not_complete_succ hk hconn hdeg hK).chromaticNumber_le

/-- CO-128, the case `k = 2`.  A graph of maximum degree at most `2` is a disjoint union of paths
and cycles; it is `2`-colourable unless it contains an odd cycle (and a connected graph of maximum
degree `2` containing an odd cycle *is* that odd cycle).  Stated contrapositively: a connected
graph of maximum degree at most `2` that is not `2`-colourable has an odd cycle. -/
@[kb "kellertrotter2017" "Exercise 5.9.43, p. 134"]
theorem brooks_two {G : SimpleGraph V} (_hconn : G.Connected)
    (hno : ∀ (x : V) (c : G.Walk x x), c.IsCycle → ¬ Odd c.length) : G.Colorable 2 :=
  (colorable_two_iff_no_odd_cycle G).mpr hno

/-- CO-128, the case `k = 2`, contrapositive form: a graph that is not `2`-colourable contains an
odd cycle. -/
theorem exists_odd_cycle_of_not_colorable_two {G : SimpleGraph V} (h : ¬ G.Colorable 2) :
    ∃ (x : V) (c : G.Walk x x), c.IsCycle ∧ Odd c.length := by
  by_contra hcon
  push Not at hcon
  exact h ((colorable_two_iff_no_odd_cycle G).mpr hcon)

end Main

end UndergradKB.Combinatorics
