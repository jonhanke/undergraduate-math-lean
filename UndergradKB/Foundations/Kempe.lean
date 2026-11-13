import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.Linarith
import UndergradKB.Common

/-!
# Foundations: partial edge colourings and Kempe chains

Tools for the proofs of Vizing's theorem and König's edge-colouring theorem (Levin, Section 2.5):

* partial edge colourings `c : Sym2 V → Option κ` of a fixed graph (`none` = not yet coloured), proper when two
  different edges at a vertex never get the same colour, and the colours *missing* at a vertex;
* the *Kempe graph* of two colours `a, b`: the edges coloured `a` or `b`; exchanging `a` and `b` on one of its
  connected components keeps the colouring proper (`IsProperPartial.kempeSwap`);
* a counting lemma: in a finite graph of maximum degree at most two, no connected component contains three
  vertices of degree at most one (a component is a path or a cycle, and a path has two ends);
* rotation of a fan of edges at a vertex (`exists_extend_of_fan`), the recolouring step of Vizing's proof.
-/

namespace UndergradKB.Foundations

open SimpleGraph

namespace EdgeColoring

variable {V κ : Type*} (G : SimpleGraph V)

/-- A partial edge colouring (`none` means uncoloured) is proper when two different edges at a vertex never get the
same colour. -/
def IsProperPartial (c : Sym2 V → Option κ) : Prop :=
  ∀ ⦃v w w' : V⦄, G.Adj v w → G.Adj v w' → w ≠ w' → ∀ a, c s(v, w) = some a → c s(v, w') ≠ some a

/-- The colour `a` is missing at `v`: no edge at `v` has colour `a`. -/
def Missing (c : Sym2 V → Option κ) (v : V) (a : κ) : Prop :=
  ∀ ⦃w⦄, G.Adj v w → c s(v, w) ≠ some a

variable {G}

theorem isProperPartial_none : IsProperPartial G (fun _ => (none : Option κ)) := by
  intro v w w' _ _ _ a h; simp at h

/-- If every edge at `v` with colour `a` under `c'` already had colour `a` under `c`, a colour missing at `v` under
`c` stays missing. -/
theorem Missing.of_imp {c c' : Sym2 V → Option κ} {v : V} {a : κ} (h : Missing G c v a)
    (himp : ∀ e, c' e = some a → c e = some a) : Missing G c' v a :=
  fun _ hw hc => h hw (himp _ hc)

/-- Under a proper colouring, a colour used on the edge `v w` is used on no other edge at `v`. -/
theorem IsProperPartial.ne_of_ne {c : Sym2 V → Option κ} (hc : IsProperPartial G c) {v w w' : V}
    (hw : G.Adj v w) (hw' : G.Adj v w') {a : κ} (ha : c s(v, w) = some a) (ha' : c s(v, w') = some a) : w = w' :=
  by_contra fun hne => hc hw hw' hne a ha ha'

/-- Uncolouring an edge keeps a colouring proper. -/
theorem IsProperPartial.erase [DecidableEq V] {c : Sym2 V → Option κ} (hc : IsProperPartial G c) (e : Sym2 V) :
    IsProperPartial G (Function.update c e none) := by
  intro v w w' hw hw' hne a h h'
  rw [Function.update_apply] at h h'
  split_ifs at h h' with h1 h2
  exact hc hw hw' hne a h h'

theorem Missing.erase [DecidableEq V] {c : Sym2 V → Option κ} {v : V} {a : κ} (h : Missing G c v a)
    (e : Sym2 V) : Missing G (Function.update c e none) v a :=
  h.of_imp fun e' he' => by
    rw [Function.update_apply] at he'
    split_ifs at he'
    exact he'

/-- Colouring the edge `x y` with a colour missing at both ends keeps a colouring proper. -/
theorem IsProperPartial.update [DecidableEq V] {c : Sym2 V → Option κ} (hc : IsProperPartial G c) {x y : V}
    {g : κ} (hx : Missing G c x g) (hy : Missing G c y g) :
    IsProperPartial G (Function.update c s(x, y) (some g)) := by
  intro v w w' hw hw' hne a h h'
  have hne' : s(v, w) ≠ s(v, w') := fun he => hne (Sym2.congr_right.1 he)
  rw [Function.update_apply] at h h'
  by_cases e1 : s(v, w) = s(x, y)
  · simp only [e1, ↓reduceIte] at h
    have e2 : s(v, w') ≠ s(x, y) := fun e2 => hne' (e1.trans e2.symm)
    simp only [e2, ↓reduceIte] at h'
    cases h
    have hv : v = x ∨ v = y := by
      rcases Sym2.eq_iff.1 e1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
    rcases hv with rfl | rfl
    · exact hx hw' h'
    · exact hy hw' h'
  · simp only [e1, ↓reduceIte] at h
    by_cases e2 : s(v, w') = s(x, y)
    · simp only [e2, ↓reduceIte] at h'
      cases h'
      have hv : v = x ∨ v = y := by
        rcases Sym2.eq_iff.1 e2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
      rcases hv with rfl | rfl
      · exact hx hw h
      · exact hy hw h
    · simp only [e2, ↓reduceIte] at h'
      exact hc hw hw' hne a h h'

/-! ### Missing colours exist when the degree is small -/

/-- If fewer than `|κ|` edges meet `v`, some colour is missing at `v`. -/
theorem exists_missing [Fintype κ] (c : Sym2 V → Option κ) (v : V) [Fintype (G.neighborSet v)]
    (h : G.degree v < Fintype.card κ) : ∃ a, Missing G c v a := by
  by_contra hcon
  simp only [Missing, not_exists, not_forall, not_not] at hcon
  choose f hf hfc using hcon
  have hinj : Function.Injective (fun a : κ => (⟨f a, hf a⟩ : G.neighborSet v)) := by
    intro a b hab
    have hab' : f a = f b := congrArg Subtype.val hab
    have := hfc a
    rw [hab', hfc b] at this
    exact (Option.some_injective _ this).symm
  have := Fintype.card_le_of_injective _ hinj
  rw [card_neighborSet_eq_degree] at this
  omega

/-- If at most `|κ|` edges meet `v` and one of them is uncoloured, some colour is missing at `v`. -/
theorem exists_missing_of_none [Fintype κ] (c : Sym2 V → Option κ) (v : V) [Fintype (G.neighborSet v)]
    {w₀ : V} (hw₀ : G.Adj v w₀) (hnone : c s(v, w₀) = none)
    (h : G.degree v ≤ Fintype.card κ) : ∃ a, Missing G c v a := by
  by_contra hcon
  simp only [Missing, not_exists, not_forall, not_not] at hcon
  choose f hf hfc using hcon
  let F : Option κ → G.neighborSet v := fun o => o.elim ⟨w₀, hw₀⟩ fun a => ⟨f a, hf a⟩
  have hF : ∀ o, c s(v, (F o).1) = o := by
    intro o; cases o with
    | none => exact hnone
    | some a => exact hfc a
  have hinj : Function.Injective F := by
    intro o o' h
    rw [← hF o, ← hF o', h]
  have := Fintype.card_le_of_injective _ hinj
  rw [card_neighborSet_eq_degree, Fintype.card_option] at this
  omega

/-! ### Kempe chains -/

/-- The Kempe graph of the colours `a` and `b`: the edges of `G` coloured `a` or `b`. -/
def kempeGraph (c : Sym2 V → Option κ) (a b : κ) : SimpleGraph V where
  Adj v w := G.Adj v w ∧ (c s(v, w) = some a ∨ c s(v, w) = some b)
  symm := ⟨fun v w h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun v h => G.irrefl h.1⟩

variable (G) in
/-- Exchange the colours `a` and `b` on the edges with both ends in the Kempe chain of `v₀` (its connected
component in the Kempe graph); other colours are fixed by the exchange, so only edges of the chain change. -/
noncomputable def kempeSwap [DecidableEq κ] (c : Sym2 V → Option κ) (a b : κ) (v₀ : V) : Sym2 V → Option κ :=
  open Classical in
  fun e => if ∀ x ∈ e, (kempeGraph (G := G) c a b).Reachable v₀ x then (c e).map (Equiv.swap a b) else c e

section Swap

variable [DecidableEq κ] {c : Sym2 V → Option κ} {a b : κ} {v₀ : V}

set_option quotPrecheck false in
local notation "K" => (kempeGraph (G := G) c a b).Reachable v₀

open Classical in
theorem kempeSwap_mk (v w : V) :
    kempeSwap G c a b v₀ s(v, w) = if K v ∧ K w then (c s(v, w)).map (Equiv.swap a b) else c s(v, w) := by
  classical
  unfold kempeSwap
  congr 1
  simp

/-- At a vertex of the chain, every edge has its colour exchanged. -/
theorem kempeSwap_of_mem {v w : V} (hv : K v) (hw : G.Adj v w) :
    kempeSwap G c a b v₀ s(v, w) = (c s(v, w)).map (Equiv.swap a b) := by
  rw [kempeSwap_mk]
  by_cases hk : K w
  · simp only [hv, hk, and_self, ↓reduceIte]
  · simp only [hk, and_false, ↓reduceIte]
    rcases hcv : c s(v, w) with _ | d
    · rfl
    · have hda : d ≠ a := fun h => hk (hv.trans (Adj.reachable ⟨hw, Or.inl (hcv.trans (by rw [h]))⟩))
      have hdb : d ≠ b := fun h => hk (hv.trans (Adj.reachable ⟨hw, Or.inr (hcv.trans (by rw [h]))⟩))
      simp [Equiv.swap_apply_of_ne_of_ne hda hdb]

/-- At a vertex outside the chain, no edge changes. -/
theorem kempeSwap_of_not_mem {v w : V} (hv : ¬ K v) : kempeSwap G c a b v₀ s(v, w) = c s(v, w) := by
  simp only [kempeSwap_mk, hv, false_and, ↓reduceIte]

theorem kempeSwap_eq_none_iff (e : Sym2 V) : kempeSwap G c a b v₀ e = none ↔ c e = none := by
  induction e using Sym2.ind with
  | _ v w => rw [kempeSwap_mk]; split_ifs <;> simp

/-- A colour other than `a` and `b` is used on exactly the same edges after the exchange. -/
theorem kempeSwap_eq_some_of_ne {d : κ} (hda : d ≠ a) (hdb : d ≠ b) (e : Sym2 V) :
    kempeSwap G c a b v₀ e = some d ↔ c e = some d := by
  induction e using Sym2.ind with
  | _ v w =>
    rw [kempeSwap_mk]
    split_ifs
    · rcases c s(v, w) with _ | d'
      · simp
      · simp only [Option.map_some, Option.some.injEq]
        constructor
        · intro h
          rw [← h, Equiv.swap_apply_of_ne_of_ne] <;> rintro rfl
          · exact hdb (by rw [← h]; simp)
          · exact hda (by rw [← h]; simp)
        · rintro rfl; exact Equiv.swap_apply_of_ne_of_ne hda hdb
    · rfl

/-- Exchanging two colours on a Kempe chain keeps a colouring proper. -/
theorem IsProperPartial.kempeSwap (hc : IsProperPartial G c) :
    IsProperPartial G (kempeSwap G c a b v₀) := by
  intro v w w' hw hw' hne d h h'
  by_cases hv : K v
  · rw [kempeSwap_of_mem hv hw] at h
    rw [kempeSwap_of_mem hv hw'] at h'
    obtain ⟨d₁, h₁, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨d₂, h₂, he⟩ := Option.map_eq_some_iff.1 h'
    rw [(Equiv.swap a b).injective he] at h₂
    exact hc hw hw' hne d₁ h₁ h₂
  · rw [kempeSwap_of_not_mem hv] at h h'
    exact hc hw hw' hne d h h'

/-- At a vertex of the chain, the missing colours are exchanged. -/
theorem missing_kempeSwap_of_mem {v : V} (hv : K v) {d : κ} (h : Missing G c v d) :
    Missing G (kempeSwap G c a b v₀) v (Equiv.swap a b d) := by
  intro w hw hc
  rw [kempeSwap_of_mem hv hw] at hc
  obtain ⟨d', h₁, he⟩ := Option.map_eq_some_iff.1 hc
  rw [(Equiv.swap a b).injective he] at h₁
  exact h hw h₁

/-- At a vertex outside the chain, the missing colours do not change. -/
theorem missing_kempeSwap_of_not_mem {v : V} (hv : ¬ K v) {d : κ} (h : Missing G c v d) :
    Missing G (kempeSwap G c a b v₀) v d := by
  intro w hw hc
  rw [kempeSwap_of_not_mem hv] at hc
  exact h hw hc

end Swap

/-! ### Degrees in a Kempe graph -/

section Degree

variable [Fintype V] {c : Sym2 V → Option κ} {a b : κ}

/-- In the Kempe graph of a proper colouring every vertex has degree at most two. -/
theorem kempeGraph_degree_le_two (hc : IsProperPartial G c) (v : V)
    [DecidableRel (kempeGraph (G := G) c a b).Adj] : (kempeGraph (G := G) c a b).degree v ≤ 2 := by
  classical
  have hsub : ((kempeGraph (G := G) c a b).neighborFinset v).image (fun w => c s(v, w)) ⊆ {some a, some b} := by
    intro o ho
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 ho
    rw [mem_neighborFinset] at hw
    rcases hw.2 with h | h <;> simp [h]
  have hinj : Set.InjOn (fun w => c s(v, w)) ((kempeGraph (G := G) c a b).neighborFinset v) := by
    intro w hw w' hw' he
    rw [Finset.mem_coe, mem_neighborFinset] at hw hw'
    rcases hw.2 with h | h
    · exact hc.ne_of_ne hw.1 hw'.1 h (he.symm.trans h)
    · exact hc.ne_of_ne hw.1 hw'.1 h (he.symm.trans h)
  rw [← card_neighborFinset_eq_degree, ← Finset.card_image_of_injOn hinj]
  exact (Finset.card_le_card hsub).trans (Finset.card_le_two)

/-- In the Kempe graph of `a` and `b`, a vertex missing `b` has degree at most one. -/
theorem kempeGraph_degree_le_one (hc : IsProperPartial G c) {v : V} (hm : Missing G c v b)
    [DecidableRel (kempeGraph (G := G) c a b).Adj] : (kempeGraph (G := G) c a b).degree v ≤ 1 := by
  rw [← card_neighborFinset_eq_degree, Finset.card_le_one]
  intro w hw w' hw'
  rw [mem_neighborFinset] at hw hw'
  have ha : c s(v, w) = some a := hw.2.resolve_right (hm hw.1)
  have ha' : c s(v, w') = some a := hw'.2.resolve_right (hm hw'.1)
  exact hc.ne_of_ne hw.1 hw'.1 ha ha'

/-- In the Kempe graph of `a` and `b`, a vertex missing `a` has degree at most one. -/
theorem kempeGraph_degree_le_one_left (hc : IsProperPartial G c) {v : V} (hm : Missing G c v a)
    [DecidableRel (kempeGraph (G := G) c a b).Adj] : (kempeGraph (G := G) c a b).degree v ≤ 1 := by
  rw [← card_neighborFinset_eq_degree, Finset.card_le_one]
  intro w hw w' hw'
  rw [mem_neighborFinset] at hw hw'
  have ha : c s(v, w) = some b := hw.2.resolve_left (hm hw.1)
  have ha' : c s(v, w') = some b := hw'.2.resolve_left (hm hw'.1)
  exact hc.ne_of_ne hw.1 hw'.1 ha ha'

end Degree

/-! ### Three ends in one component are impossible -/

/-- In a finite graph whose vertices all have degree at most two, no connected component contains three different
vertices of degree at most one: by `|V| ≤ |E| + 1` for a connected graph, the degree sum of a component is at least
`2 |C| - 2`, while three vertices of degree at most one force it below `2 |C| - 3`. -/
theorem not_three_ends {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (h2 : ∀ v, H.degree v ≤ 2) {x y z : W} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : H.degree x ≤ 1) (hy : H.degree y ≤ 1) (hz : H.degree z ≤ 1)
    (ry : H.Reachable x y) (rz : H.Reachable x z) : False := by
  classical
  set C := H.connectedComponentMk x
  have hxC : x ∈ C.supp := rfl
  have hyC : y ∈ C.supp := (ConnectedComponent.eq.2 ry).symm
  have hzC : z ∈ C.supp := (ConnectedComponent.eq.2 rz).symm
  let K := C.toSimpleGraph
  have hconn : K.Connected := C.connected_toSimpleGraph
  have hcard := hconn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← edgeFinset_card] at hcard
  have hsum := K.sum_degrees_eq_twice_card_edges
  -- degrees in the component are degrees in `H`
  have hdeg : ∀ v : C, K.degree v = H.degree v.1 := by
    intro v
    rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
    refine Finset.card_bij (fun w _ => w.1) ?_ ?_ ?_
    · intro w hw
      rw [mem_neighborFinset] at hw ⊢
      exact hw
    · intro w _ w' _ h; exact Subtype.ext h
    · intro w hw
      rw [mem_neighborFinset] at hw
      have hwC : w ∈ C.supp := C.mem_supp_of_adj_mem_supp v.2 hw
      exact ⟨⟨w, hwC⟩, by rw [mem_neighborFinset]; exact hw, rfl⟩
  let x' : C := ⟨x, hxC⟩
  let y' : C := ⟨y, hyC⟩
  let z' : C := ⟨z, hzC⟩
  set T : Finset C := {x', y', z'}
  have hT : T.card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · exact fun h => hyz (congrArg Subtype.val h)
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hxy (congrArg Subtype.val h), fun h => hxz (congrArg Subtype.val h)⟩
  have hTsum : ∑ v ∈ T, K.degree v ≤ T.card • 1 := by
    refine Finset.sum_le_card_nsmul _ _ _ fun v hv => ?_
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl <;> rw [hdeg] <;> assumption
  have hRsum : ∑ v ∈ Finset.univ \ T, K.degree v ≤ (Finset.univ \ T).card • 2 :=
    Finset.sum_le_card_nsmul _ _ _ fun v _ => by rw [hdeg]; exact h2 _
  have hsplit : ∑ v ∈ Finset.univ \ T, K.degree v + ∑ v ∈ T, K.degree v = ∑ v, K.degree v :=
    Finset.sum_sdiff (Finset.subset_univ T)
  have hcardR : (Finset.univ \ T).card + T.card = Fintype.card C := by
    rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T), Finset.card_univ]
  simp only [smul_eq_mul] at hTsum hRsum
  omega

/-! ### Fans -/

variable (G) in
/-- The fan condition at `x`, starting from `y`: for the list `[y₁, …, y_k]`, every `y_i` is a neighbour of `x`
and the edge `x y_i` has a colour missing at `y_{i-1}` (with `y₀ = y`). -/
def FanChain (c : Sym2 V → Option κ) (x : V) : V → List V → Prop
  | _, [] => True
  | y, z :: l => G.Adj x z ∧ (∃ d, c s(x, z) = some d ∧ Missing G c y d) ∧ FanChain c x z l

/-- The last vertex of the fan `y :: l`. -/
def fanLast : V → List V → V
  | y, [] => y
  | _, z :: l => fanLast z l

@[simp] theorem fanLast_nil (y : V) : fanLast y [] = y := rfl
@[simp] theorem fanLast_cons (y z : V) (l : List V) : fanLast y (z :: l) = fanLast z l := rfl

theorem fanLast_append (y : V) (A B : List V) : fanLast y (A ++ B) = fanLast (fanLast y A) B := by
  induction A generalizing y with
  | nil => rfl
  | cons z A ih => exact ih z

theorem fanLast_mem (y : V) (l : List V) : fanLast y l ∈ y :: l := by
  induction l generalizing y with
  | nil => simp
  | cons z l ih => exact List.mem_cons_of_mem _ (ih z)

theorem fanLast_mem_of_ne_nil (y : V) {l : List V} (hl : l ≠ []) : fanLast y l ∈ l := by
  cases l with
  | nil => exact absurd rfl hl
  | cons z l => exact fanLast_mem z l

theorem FanChain.append_iff {c : Sym2 V → Option κ} {x : V} (y : V) (A B : List V) :
    FanChain G c x y (A ++ B) ↔ FanChain G c x y A ∧ FanChain G c x (fanLast y A) B := by
  induction A generalizing y with
  | nil => simp [FanChain]
  | cons z A ih =>
    simp only [List.cons_append, FanChain, fanLast_cons, ih z]
    tauto

theorem FanChain.adj {c : Sym2 V → Option κ} {x : V} {y : V} {l : List V} (h : FanChain G c x y l) :
    ∀ w ∈ l, G.Adj x w := by
  induction l generalizing y with
  | nil => simp
  | cons z l ih =>
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact h.1
    · exact ih h.2.2 w hw

/-- A fan survives a change of colouring that keeps the colours of its edges at `x` and keeps every colour used
there missing wherever it was missing. -/
theorem FanChain.imp {c c' : Sym2 V → Option κ} {x : V} {y : V} {l : List V} (h : FanChain G c x y l)
    (hedge : ∀ w ∈ l, c' s(x, w) = c s(x, w))
    (hcol : ∀ w ∈ l, ∀ d, c s(x, w) = some d → ∀ e, c' e = some d → c e = some d) :
    FanChain G c' x y l := by
  induction l generalizing y with
  | nil => trivial
  | cons z l ih =>
    obtain ⟨hz, ⟨d, hd, hm⟩, hrest⟩ := h
    refine ⟨hz, ⟨d, (hedge z (by simp)).trans hd, hm.of_imp (hcol z (by simp) d hd)⟩, ?_⟩
    exact ih hrest (fun w hw => hedge w (by simp [hw])) (fun w hw => hcol w (by simp [hw]))

/-- **Fan rotation.** Let `x y` be uncoloured, and `y, y₁, …, y_k` a fan at `x` with distinct vertices. If a colour
`g` is missing both at `x` and at `y_k`, shift the colours of the fan edges one step (`x y_{i-1}` gets the colour of
`x y_i`) and give `x y_k` the colour `g`: this colours `x y` and keeps every coloured edge coloured. -/
theorem exists_extend_of_fan [DecidableEq V] {x : V} :
    ∀ (l : List V) (y : V) (c : Sym2 V → Option κ), IsProperPartial G c → G.Adj x y → c s(x, y) = none →
      FanChain G c x y l → (y :: l).Nodup → ∀ g, Missing G c x g → Missing G c (fanLast y l) g →
      ∃ c' : Sym2 V → Option κ, IsProperPartial G c' ∧ (∀ e, c e ≠ none → c' e ≠ none) ∧ c' s(x, y) ≠ none := by
  intro l
  induction l with
  | nil =>
    intro y c hc _ _ _ _ g hx hy
    refine ⟨Function.update c s(x, y) (some g), hc.update hx hy, ?_, by simp⟩
    intro e he
    rw [Function.update_apply]; split_ifs <;> simp_all
  | cons z l ih =>
    intro y c hc hxy hnone hfan hnd g hgx hgl
    obtain ⟨hxz, ⟨d, hd, hdy⟩, hrest⟩ := hfan
    have hyz : y ≠ z := fun h => (List.nodup_cons.1 hnd).1 (h ▸ List.mem_cons_self ..)
    have hnd' : (z :: l).Nodup := (List.nodup_cons.1 hnd).2
    have hyl : y ∉ l := fun h => (List.nodup_cons.1 hnd).1 (List.mem_cons_of_mem _ h)
    have hzl : z ∉ l := (List.nodup_cons.1 hnd').1
    have exy_xz : s(x, y) ≠ s(x, z) := fun h => hyz (Sym2.congr_right.1 h)
    -- uncolour `x z` and give `x y` the colour `d` of `x z`
    set c₀ := Function.update c s(x, z) none with hc₀
    set c₁ := Function.update c₀ s(x, y) (some d) with hc₁
    have hdx₀ : Missing G c₀ x d := by
      intro w hw h
      rw [hc₀, Function.update_apply] at h
      split_ifs at h with hwz
      exact hwz (by rw [hc.ne_of_ne hw hxz h hd])
    have hp₁ : IsProperPartial G c₁ := (hc.erase _).update hdx₀ (hdy.erase _)
    have hdg : d ≠ g := fun h => hgx hxz (h ▸ hd)
    -- the colour of a fan edge `x w` with `w ∈ l` differs from `d`
    have hcolne : ∀ w ∈ l, ∀ d', c s(x, w) = some d' → d' ≠ d := by
      intro w hw d' hd' hdd
      subst hdd
      have := hc.ne_of_ne (hrest.adj w hw) hxz hd' hd
      exact hzl (this ▸ hw)
    have himp : ∀ d', d' ≠ d → ∀ e, c₁ e = some d' → c e = some d' := by
      intro d' hd' e he
      rw [hc₁, Function.update_apply] at he
      split_ifs at he with h1
      · exact absurd (Option.some_injective _ he).symm hd'
      · rw [hc₀, Function.update_apply] at he
        split_ifs at he
        exact he
    have hnone₁ : c₁ s(x, z) = none := by
      rw [hc₁, Function.update_of_ne exy_xz.symm, hc₀, Function.update_self]
    have hfan₁ : FanChain G c₁ x z l := by
      refine hrest.imp ?_ ?_
      · intro w hw
        have h1 : s(x, w) ≠ s(x, y) := fun h => hyl (Sym2.congr_right.1 h ▸ hw)
        have h2 : s(x, w) ≠ s(x, z) := fun h => hzl (Sym2.congr_right.1 h ▸ hw)
        rw [hc₁, Function.update_of_ne h1, hc₀, Function.update_of_ne h2]
      · intro w hw d' hd' e he
        exact himp d' (hcolne w hw d' hd') e he
    obtain ⟨c₂, hp₂, hmono, hxz₂⟩ := ih z c₁ hp₁ hxz hnone₁ hfan₁ hnd' g
      (hgx.of_imp (himp g hdg.symm)) (hgl.of_imp (himp g hdg.symm))
    refine ⟨c₂, hp₂, ?_, ?_⟩
    · intro e he
      by_cases hez : e = s(x, z)
      · rw [hez]; exact hxz₂
      · apply hmono
        rw [hc₁, Function.update_apply]
        split_ifs
        · simp
        · rw [hc₀, Function.update_of_ne hez]; exact he
    · apply hmono
      rw [hc₁, Function.update_self]
      simp

end EdgeColoring

end UndergradKB.Foundations
