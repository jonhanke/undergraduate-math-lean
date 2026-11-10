import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.ZMod.Basic
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.Graph.Ramsey

/-!
# Exact small Ramsey numbers: `R(3,4) = 9` and `R(4,4) = 18` (Keller–Trotter, p. 254)

Lower bounds come from explicit circulant graphs (the Paley graph on `ZMod 17` and the Möbius
ladder on `ZMod 8`), checked by `decide`; upper bounds from the recurrence
`R(m,n) ≤ R(m-1,n) + R(m,n-1)` in the case needed here and a degree/parity argument for
`R(3,4) ≤ 9`.
-/

namespace UndergradKB.Combinatorics

open Finset SimpleGraph

/-! ### Generic lemmas -/

lemma cliqueFree_four_of {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (h : ∀ a b c d, G.Adj a b → G.Adj a c → G.Adj a d → G.Adj b c → G.Adj b d → G.Adj c d →
      False) : G.CliqueFree 4 := by
  intro t ht
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_four.1 ht.card_eq
  have adj : ∀ x y, x ∈ ({a, b, c, d} : Finset V) → y ∈ ({a, b, c, d} : Finset V) → x ≠ y →
      G.Adj x y := fun x y hx hy hxy =>
    ht.isClique (Finset.mem_coe.2 hx) (Finset.mem_coe.2 hy) hxy
  exact h a b c d (adj a b (by simp) (by simp) hab) (adj a c (by simp) (by simp) hac)
    (adj a d (by simp) (by simp) had) (adj b c (by simp) (by simp) hbc)
    (adj b d (by simp) (by simp) hbd) (adj c d (by simp) (by simp) hcd)

/-- A clique or independent set in the induced graph on a finset lifts to the whole graph. -/
lemma lift_sub {V : Type*} (G : SimpleGraph V) (S : Finset V) (m n : ℕ) (t : Finset S)
    (h : (G.comap (Subtype.val : S → V)).IsNClique m t ∨
      (G.comap (Subtype.val : S → V))ᶜ.IsNClique n t) :
    ∃ u ⊆ S, G.IsNClique m u ∨ Gᶜ.IsNClique n u := by
  classical
  refine ⟨t.map (Function.Embedding.subtype _), ?_, ?_⟩
  · intro x hx
    obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 hx
    exact a.2
  · rcases h with h | h
    · left
      refine ⟨?_, by rw [Finset.card_map]; exact h.card_eq⟩
      intro x hx y hy hxy
      simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe,
        Function.Embedding.coe_subtype] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact h.isClique ha hb (fun e => hxy (by rw [e]))
    · right
      refine ⟨?_, by rw [Finset.card_map]; exact h.card_eq⟩
      intro x hx y hy hxy
      simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe,
        Function.Embedding.coe_subtype] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      have := h.isClique ha hb (fun e => hxy (by rw [e]))
      rw [compl_adj] at this ⊢
      exact ⟨fun e => this.1 (Subtype.ext e), this.2⟩

/-! ### `R(3,4) ≤ 9` -/

/-- Every graph on at least nine vertices has a triangle or an independent 4-set. -/
theorem exists_clique3_or_indep4 {V : Type*} [Fintype V] (G : SimpleGraph V)
    (h : 9 ≤ Fintype.card V) : ∃ t : Finset V, G.IsNClique 3 t ∨ Gᶜ.IsNClique 4 t := by
  classical
  by_contra hno
  push Not at hno
  have hdeg : ∀ v, G.degree v ≤ 3 := by
    intro v
    by_contra hlt
    push Not at hlt
    obtain ⟨t, ht, hc⟩ := Finset.exists_subset_card_eq (s := G.neighborFinset v) (n := 4)
      (by rw [card_neighborFinset_eq_degree]; omega)
    refine (hno t).2 ⟨?_, hc⟩
    intro x hx y hy hxy
    rw [compl_adj]
    refine ⟨hxy, fun hadj => (hno {v, x, y}).1 ?_⟩
    rw [is3Clique_triple_iff]
    exact ⟨(G.mem_neighborFinset v x).1 (ht hx), (G.mem_neighborFinset v y).1 (ht hy), hadj⟩
  have hnon : ∀ v, (univ.filter (fun w => ¬ G.Adj v w)).card ≤ 6 := by
    intro v
    set M' := univ.filter (fun w => ¬ G.Adj v w) with hM'
    have hv : v ∈ M' := by simp [hM']
    by_contra hlt
    push Not at hlt
    have hM : Nat.choose (2 + 2) 2 ≤ (M'.erase v).card := by
      rw [Finset.card_erase_of_mem hv]; simp [Nat.choose]; omega
    obtain ⟨t, ht, h1 | h1⟩ := ramsey_finset G 2 2 (M'.erase v) hM
    · exact (hno t).1 h1
    · refine (hno (insert v t)).2 (h1.insert fun b hb => ?_)
      have := Finset.mem_erase.1 (ht hb)
      rw [compl_adj]
      exact ⟨fun e => this.1 e.symm, by simpa [hM'] using this.2⟩
  have hsum : ∀ v, G.degree v + (univ.filter (fun w => ¬ G.Adj v w)).card = Fintype.card V := by
    intro v
    rw [← card_neighborFinset_eq_degree]
    have : G.neighborFinset v = univ.filter (fun w => G.Adj v w) := by
      ext w; simp
    rw [this, Finset.card_filter_add_card_filter_not, Finset.card_univ]
  have hd3 : ∀ v, G.degree v = 3 := fun v => by
    have := hdeg v; have := hnon v; have := hsum v; omega
  have hcard : Fintype.card V = 9 := by
    obtain ⟨v⟩ : Nonempty V := Fintype.card_pos_iff.1 (by omega)
    have := hdeg v; have := hnon v; have := hsum v; omega
  have := G.sum_degrees_eq_twice_card_edges
  simp only [hd3, Finset.sum_const, Finset.card_univ, hcard, smul_eq_mul] at this
  omega

/-- Finset form of `exists_clique3_or_indep4`. -/
theorem exists_clique3_or_indep4_finset {V : Type*} (G : SimpleGraph V) (S : Finset V)
    (h : 9 ≤ S.card) : ∃ u ⊆ S, G.IsNClique 3 u ∨ Gᶜ.IsNClique 4 u := by
  obtain ⟨t, ht⟩ := exists_clique3_or_indep4 (G.comap (Subtype.val : S → V))
    (by rw [Fintype.card_coe]; exact h)
  exact lift_sub G S 3 4 t ht

/-! ### Lower bound graphs -/

/-- The Möbius ladder on `ZMod 8`: vertices at difference `±1` or `4` are adjacent. -/
def mobius8 : SimpleGraph (ZMod 8) where
  Adj a b := (a - b) ∈ ({1, 4, 7} : Finset (ZMod 8))
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel mobius8.Adj := fun a b =>
  inferInstanceAs (Decidable ((a - b) ∈ ({1, 4, 7} : Finset (ZMod 8))))

instance : DecidableRel mobius8ᶜ.Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ ¬ mobius8.Adj a b))

lemma mobius8_triangleFree: mobius8.CliqueFree 3 := by
  intro t ht
  rw [is3Clique_iff] at ht
  obtain ⟨a, b, c, h1, h2, h3, rfl⟩ := ht
  revert a b c
  decide +revert

lemma mobius8_compl_cliqueFree : mobius8ᶜ.CliqueFree 4 := by
  apply cliqueFree_four_of
  decide

/-- The Paley graph on `ZMod 17`: adjacent iff the difference is a nonzero square. -/
def paley17 : SimpleGraph (ZMod 17) where
  Adj a b := (a - b) ∈ ({1, 2, 4, 8, 9, 13, 15, 16} : Finset (ZMod 17))
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel paley17.Adj := fun a b =>
  inferInstanceAs (Decidable ((a - b) ∈ ({1, 2, 4, 8, 9, 13, 15, 16} : Finset (ZMod 17))))

instance : DecidableRel paley17ᶜ.Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ ¬ paley17.Adj a b))

lemma paley17_cliqueFree: paley17.CliqueFree 4 := by
  apply cliqueFree_four_of
  decide +kernel

lemma paley17_compl_cliqueFree : paley17ᶜ.CliqueFree 4 := by
  apply cliqueFree_four_of
  decide +kernel

/-! ### The values -/

lemma not_ramseyProp_three_four_eight : ¬ RamseyProp 3 4 8 := by
  intro h
  rcases h (ZMod 8) (by simp) mobius8 with h | h
  · exact h mobius8_triangleFree
  · exact h mobius8_compl_cliqueFree

lemma ramseyProp_three_four_nine : RamseyProp 3 4 9 := by
  intro V _ hV G
  obtain ⟨t, h | h⟩ := exists_clique3_or_indep4 G hV
  · exact Or.inl h.not_cliqueFree
  · exact Or.inr h.not_cliqueFree

/-- `R(3,4) = 9`. -/
@[kb "kellertrotter2017" "text, p. 254"]
theorem ramseyNumber_three_four : ramseyNumber 3 4 = 9 := by
  apply le_antisymm (Nat.sInf_le ramseyProp_three_four_nine)
  by_contra hlt
  push Not at hlt
  exact not_ramseyProp_three_four_eight
    ((Nat.sInf_mem (s := {N | RamseyProp 3 4 N}) ⟨9, ramseyProp_three_four_nine⟩).mono
      (by omega))

lemma not_ramseyProp_four_four_seventeen : ¬ RamseyProp 4 4 17 := by
  intro h
  rcases h (ZMod 17) (by simp) paley17 with h | h
  · exact h paley17_cliqueFree
  · exact h paley17_compl_cliqueFree

lemma ramseyProp_four_four_eighteen : RamseyProp 4 4 18 := by
  classical
  intro V _ hV G
  obtain ⟨v⟩ : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  set Nb := (univ.erase v).filter (G.Adj v) with hNb
  set Mb := (univ.erase v).filter (fun x => ¬ G.Adj v x) with hMb
  have hsum : Nb.card + Mb.card = Fintype.card V - 1 := by
    rw [hNb, hMb, Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem
      (Finset.mem_univ v), Finset.card_univ]
  by_cases hc : 9 ≤ Nb.card
  · obtain ⟨t, ht, h | h⟩ := exists_clique3_or_indep4_finset G Nb hc
    · have htS : ∀ x ∈ t, G.Adj v x := fun x hx => (Finset.mem_filter.1 (ht hx)).2
      exact Or.inl (h.insert htS).not_cliqueFree
    · exact Or.inr h.not_cliqueFree
  · have hM : 9 ≤ Mb.card := by omega
    obtain ⟨t, ht, h | h⟩ := exists_clique3_or_indep4_finset Gᶜ Mb hM
    · have htS : ∀ x ∈ t, Gᶜ.Adj v x := by
        intro x hx
        have hx' := Finset.mem_filter.1 (ht hx)
        rw [compl_adj]
        exact ⟨fun e => (Finset.ne_of_mem_erase hx'.1) e.symm, hx'.2⟩
      exact Or.inr (by simpa using (h.insert htS).not_cliqueFree)
    · rw [compl_compl] at h
      exact Or.inl h.not_cliqueFree

/-- CO-260. The known value `R(4,4) = 18` (the lower bound via the Paley graph on 17 vertices,
the upper bound via `R(4,4) ≤ R(3,4) + R(4,3)` and `R(3,4) ≤ 9`). `R(3,3) = 6` is
`ramseyNumber_three_three`; the bounds `43 ≤ R(5,5) ≤ 49` are computer results and are not
formalized. -/
@[kb "kellertrotter2017" "text, p. 254"]
theorem ramseyNumber_four_four : ramseyNumber 4 4 = 18 := by
  apply le_antisymm (Nat.sInf_le ramseyProp_four_four_eighteen)
  by_contra hlt
  push Not at hlt
  exact not_ramseyProp_four_four_seventeen
    ((Nat.sInf_mem (s := {N | RamseyProp 4 4 N}) ⟨18, ramseyProp_four_four_eighteen⟩).mono
      (by omega))

end UndergradKB.Combinatorics
