import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Positivity
import UndergradKB.Common.Attr

/-!
# Ramsey numbers for graphs (Keller–Trotter, Chapter 11)

An independent `k`-set of `G` is a `k`-clique of the complement `Gᶜ`.
-/

namespace UndergradKB.Combinatorics

open Finset SimpleGraph

/-- `RamseyProp m n N`: every graph on at least `N` vertices has an `m`-clique or an independent
set of size `n` (an `n`-clique of the complement). -/
def RamseyProp (m n N : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V], N ≤ Fintype.card V → ∀ G : SimpleGraph V,
    ¬ G.CliqueFree m ∨ ¬ Gᶜ.CliqueFree n

lemma RamseyProp.mono {m n N N' : ℕ} (h : RamseyProp m n N) (hN : N ≤ N') : RamseyProp m n N' :=
  fun V _ hV G => h V (hN.trans hV) G

/-- The Ramsey number `R(m,n)` (the least `N` with `RamseyProp m n N`; `0` if none exists). -/
noncomputable def ramseyNumber (m n : ℕ) : ℕ := sInf {N | RamseyProp m n N}

/-- Finset form of the Ramsey statement, with the induction of the book: a set `S` of at least
`C(m+n, m)` vertices contains a `(m+1)`-clique or an independent `(n+1)`-set. -/
theorem ramsey_finset {V : Type*} (G : SimpleGraph V) :
    ∀ (m n : ℕ) (S : Finset V), Nat.choose (m + n) m ≤ S.card →
      ∃ t ⊆ S, G.IsNClique (m + 1) t ∨ Gᶜ.IsNClique (n + 1) t := by
  classical
  have main : ∀ k m n : ℕ, m + n = k → ∀ (S : Finset V), Nat.choose (m + n) m ≤ S.card →
      ∃ t ⊆ S, G.IsNClique (m + 1) t ∨ Gᶜ.IsNClique (n + 1) t := by
   intro k
   induction k with
   | zero =>
    intro m n h
    obtain ⟨rfl, rfl⟩ : m = 0 ∧ n = 0 := by omega
    intro S hS
    obtain ⟨v, hv⟩ := Finset.card_pos.1 (by simpa using hS)
    exact ⟨{v}, by simpa using hv, Or.inl (by simp)⟩
   | succ k ih =>
    intro m n h S hS
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have : 0 < S.card := by simpa using hS
      obtain ⟨v, hv⟩ := Finset.card_pos.1 this
      exact ⟨{v}, by simpa using hv, Or.inl (by simp)⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : 0 < S.card := lt_of_lt_of_le (Nat.choose_pos (by omega)) hS
      obtain ⟨v, hv⟩ := Finset.card_pos.1 this
      exact ⟨{v}, by simpa using hv, Or.inr (by simp)⟩
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have hpas : Nat.choose (m + 1 + (n + 1)) (m + 1) =
        Nat.choose (m + (n + 1)) m + Nat.choose ((m + 1) + n) (m + 1) := by
      have : m + 1 + (n + 1) = (m + (n + 1)) + 1 := by omega
      rw [this, Nat.choose_succ_succ]
      congr 2
      omega
    have hSpos : 0 < S.card := lt_of_lt_of_le (Nat.choose_pos (by omega)) hS
    obtain ⟨v, hv⟩ := Finset.card_pos.1 hSpos
    set Nb := (S.erase v).filter (G.Adj v) with hNb
    set Mb := (S.erase v).filter (fun x => ¬ G.Adj v x) with hMb
    have hsum : Nb.card + Mb.card = S.card - 1 := by
      rw [hNb, hMb, Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem hv]
    have hA : 0 < Nat.choose (m + (n + 1)) m := Nat.choose_pos (by omega)
    have hB : 0 < Nat.choose ((m + 1) + n) (m + 1) := Nat.choose_pos (by omega)
    by_cases hcase : Nat.choose (m + (n + 1)) m ≤ Nb.card
    · obtain ⟨t, ht, h | h⟩ := ih m (n + 1) (by omega) Nb hcase
      · have htS : ∀ x ∈ t, G.Adj v x := fun x hx => (mem_filter.1 (ht hx)).2
        have hvt : v ∉ t := fun hvt => G.loopless.irrefl v (htS v hvt)
        refine ⟨insert v t, ?_, Or.inl (h.insert htS)⟩
        intro x hx
        rcases mem_insert.1 hx with rfl | hx
        · exact hv
        · exact mem_of_mem_erase (mem_filter.1 (ht hx)).1
      · exact ⟨t, fun x hx => mem_of_mem_erase (mem_filter.1 (ht hx)).1, Or.inr h⟩
    · have hM : Nat.choose ((m + 1) + n) (m + 1) ≤ Mb.card := by omega
      obtain ⟨t, ht, h | h⟩ := ih (m + 1) n (by omega) Mb hM
      · exact ⟨t, fun x hx => mem_of_mem_erase (mem_filter.1 (ht hx)).1, Or.inl h⟩
      · have htS : ∀ x ∈ t, Gᶜ.Adj v x := by
          intro x hx
          have hx' := mem_filter.1 (ht hx)
          rw [compl_adj]
          exact ⟨fun h => (Finset.ne_of_mem_erase hx'.1) h.symm, hx'.2⟩
        refine ⟨insert v t, ?_, Or.inr (h.insert htS)⟩
        intro x hx
        rcases mem_insert.1 hx with rfl | hx
        · exact hv
        · exact mem_of_mem_erase (mem_filter.1 (ht hx)).1

  intro m n
  exact main _ m n rfl

/-- CO-259. Ramsey's theorem for graphs: for `m, n ≥ 1`, every graph on at least
`C(m+n-2, m-1)` vertices has an `m`-clique or an independent `n`-set. -/
@[kb "kellertrotter2017" "Theorem 11.2, p. 254"]
theorem ramseyProp_choose (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    RamseyProp m n (Nat.choose (m + n - 2) (m - 1)) := by
  intro V _ hV G
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have e : m + 1 + (n + 1) - 2 = m + n := by omega
  simp only [e, Nat.add_sub_cancel] at hV
  obtain ⟨t, -, h | h⟩ := ramsey_finset G m n Finset.univ (by simpa using hV)
  · exact Or.inl h.not_cliqueFree
  · exact Or.inr h.not_cliqueFree

/-- CO-259 (existence). The Ramsey property holds for some `N`, and `R(m,n)` is at most
`C(m+n-2, m-1)`. -/
@[kb "kellertrotter2017" "Theorem 11.2, p. 254"]
theorem ramseyNumber_le (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    RamseyProp m n (ramseyNumber m n) ∧ ramseyNumber m n ≤ Nat.choose (m + n - 2) (m - 1) :=
  ⟨Nat.sInf_mem (s := {N | RamseyProp m n N}) ⟨_, ramseyProp_choose m n hm hn⟩, Nat.sInf_le (ramseyProp_choose m n hm hn)⟩

/-- The 5-cycle has no triangle. -/
lemma cycleGraph_five_cliqueFree : (cycleGraph 5).CliqueFree 3 := by
  intro t ht
  rw [is3Clique_iff] at ht
  obtain ⟨a, b, c, h1, h2, h3, rfl⟩ := ht
  revert a b c
  decide +revert

/-- The 5-cycle has no independent 3-set. -/
lemma cycleGraph_five_compl_cliqueFree : (cycleGraph 5)ᶜ.CliqueFree 3 := by
  intro t ht
  rw [is3Clique_iff] at ht
  obtain ⟨a, b, c, h1, h2, h3, rfl⟩ := ht
  revert a b c
  decide +revert

/-- CO-258. Every graph on at least six vertices has a triangle or an independent 3-set. -/
@[kb "kellertrotter2017" "Lemma 11.1, p. 253"]
theorem six_vertices_triangle_or_independent (V : Type) [Fintype V] (h : 6 ≤ Fintype.card V)
    (G : SimpleGraph V) : ¬ G.CliqueFree 3 ∨ ¬ Gᶜ.CliqueFree 3 :=
  ramseyProp_choose 3 3 (by decide) (by decide) V (by simpa [Nat.choose] using h) G

/-- CO-258 (sharpness). The 5-cycle on five vertices has neither a triangle nor an independent
3-set, so six cannot be replaced by five. -/
@[kb "kellertrotter2017" "Lemma 11.1, p. 253"]
theorem cycleGraph_five_no_triangle_no_independent :
    (cycleGraph 5).CliqueFree 3 ∧ (cycleGraph 5)ᶜ.CliqueFree 3 :=
  ⟨cycleGraph_five_cliqueFree, cycleGraph_five_compl_cliqueFree⟩

lemma not_ramseyProp_three_five : ¬ RamseyProp 3 3 5 := by
  intro h
  have := h (Fin 5) (by simp) (cycleGraph 5)
  rcases this with h | h
  · exact h cycleGraph_five_cliqueFree
  · exact h cycleGraph_five_compl_cliqueFree

/-- CO-260 (the part proved in the book's setting): `R(3,3) = 6`. -/
@[kb "kellertrotter2017" "text, p. 254"]
theorem ramseyNumber_three_three : ramseyNumber 3 3 = 6 := by
  have h6 : RamseyProp 3 3 6 := fun V _ hV G => six_vertices_triangle_or_independent V hV G
  apply le_antisymm (Nat.sInf_le h6)
  by_contra hlt
  push Not at hlt
  exact not_ramseyProp_three_five
    ((Nat.sInf_mem (s := {N | RamseyProp 3 3 N}) ⟨6, h6⟩).mono (by omega))

/-! ### Erdős' lower bound by counting graphs -/

section Counting

variable {X : Type*} [DecidableEq X]

/-- Counting edge sets containing a fixed set `A ⊆ T`. -/
lemma card_powerset_filter_superset (T A : Finset X) (hA : A ⊆ T) :
    (T.powerset.filter (fun E => A ⊆ E)).card = 2 ^ (T.card - A.card) := by
  rw [← Finset.card_sdiff_of_subset hA, ← Finset.card_powerset]
  refine Finset.card_nbij' (fun E => E \ A) (fun F => F ∪ A) ?_ ?_ ?_ ?_
  · intro E hE
    simp only [mem_coe, mem_filter, mem_powerset] at hE ⊢
    exact sdiff_subset_sdiff hE.1 le_rfl
  · intro F hF
    simp only [mem_coe, mem_filter, mem_powerset] at hF ⊢
    exact ⟨union_subset (hF.trans sdiff_subset) hA, subset_union_right⟩
  · intro E hE
    simp only [mem_coe, mem_filter, mem_powerset] at hE
    exact sdiff_union_of_subset hE.2
  · intro F hF
    simp only [mem_coe, mem_filter, mem_powerset] at hF
    exact (union_sdiff_right F A).trans
      (sdiff_eq_self_of_disjoint (disjoint_of_subset_left hF sdiff_disjoint))

/-- Counting edge sets disjoint from a fixed set `A ⊆ T`. -/
lemma card_powerset_filter_disjoint (T A : Finset X) (hA : A ⊆ T) :
    (T.powerset.filter (fun E => Disjoint A E)).card = 2 ^ (T.card - A.card) := by
  rw [← Finset.card_sdiff_of_subset hA, ← Finset.card_powerset]
  congr 1
  ext E
  simp only [mem_filter, mem_powerset, subset_sdiff]
  tauto

end Counting

/-- CO-262 (Erdős' counting argument). If `2 * C(N,n) < 2^C(n,2)` then some graph on `N`
vertices has neither an `n`-clique nor an independent `n`-set. -/
@[kb "kellertrotter2017" "Theorem 11.4, p. 256"]
theorem exists_graph_no_clique_no_independent (N n : ℕ)
    (h : 2 * N.choose n < 2 ^ n.choose 2) :
    ∃ G : SimpleGraph (Fin N), G.CliqueFree n ∧ Gᶜ.CliqueFree n := by
  classical
  let T : Finset (Sym2 (Fin N)) := (univ : Finset (Fin N)).offDiag.image Sym2.mk.uncurry
  let A : Finset (Fin N) → Finset (Sym2 (Fin N)) := fun s => s.offDiag.image Sym2.mk.uncurry
  have hT : T.card = N.choose 2 := by
    simpa [T] using Sym2.card_image_offDiag (univ : Finset (Fin N))
  have hA : ∀ s, (A s).card = s.card.choose 2 := fun s => Sym2.card_image_offDiag s
  have hAT : ∀ s, A s ⊆ T := fun s => image_subset_image (offDiag_mono (subset_univ s))
  by_contra hcon
  have hbad : ∀ E ∈ T.powerset, ∃ s ∈ powersetCard n (univ : Finset (Fin N)),
      A s ⊆ E ∨ Disjoint (A s) E := by
    intro E _
    have hG := fun hc => hcon ⟨SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin N))), hc⟩
    by_cases h1 : (SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin N)))).CliqueFree n
    · obtain ⟨s, hs⟩ : ∃ s, (SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin N))))ᶜ.IsNClique n s := by
        by_contra hne
        exact hG ⟨h1, fun t ht => hne ⟨t, ht⟩⟩
      refine ⟨s, mem_powersetCard.2 ⟨subset_univ _, by simpa using hs.card_eq⟩, Or.inr ?_⟩
      rw [Finset.disjoint_left]
      intro e he heE
      obtain ⟨⟨x, y⟩, hp, rfl⟩ := mem_image.1 he
      rw [mem_offDiag] at hp
      have := hs.1 (by exact_mod_cast hp.1) (by exact_mod_cast hp.2.1) hp.2.2
      rw [SimpleGraph.compl_adj] at this
      exact this.2 (by rw [SimpleGraph.fromEdgeSet_adj]; exact ⟨by simpa using heE, hp.2.2⟩)
    · obtain ⟨s, hs⟩ : ∃ s, (SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin N)))).IsNClique n s := by
        by_contra hne
        exact h1 fun t ht => hne ⟨t, ht⟩
      refine ⟨s, mem_powersetCard.2 ⟨subset_univ _, by simpa using hs.card_eq⟩, Or.inl ?_⟩
      intro e he
      obtain ⟨⟨x, y⟩, hp, rfl⟩ := mem_image.1 he
      rw [mem_offDiag] at hp
      have := hs.1 (by exact_mod_cast hp.1) (by exact_mod_cast hp.2.1) hp.2.2
      rw [SimpleGraph.fromEdgeSet_adj] at this
      simpa using this.1
  have hsub : T.powerset ⊆ (powersetCard n (univ : Finset (Fin N))).biUnion
      (fun s => T.powerset.filter (fun E => A s ⊆ E) ∪ T.powerset.filter (fun E => Disjoint (A s) E)) := by
    intro E hE
    obtain ⟨s, hs, hE'⟩ := hbad E hE
    rw [mem_biUnion]
    refine ⟨s, hs, ?_⟩
    rcases hE' with h' | h'
    · exact mem_union_left _ (mem_filter.2 ⟨hE, h'⟩)
    · exact mem_union_right _ (mem_filter.2 ⟨hE, h'⟩)
  have hle : 2 ^ (N.choose 2) ≤ N.choose n * (2 * 2 ^ (N.choose 2 - n.choose 2)) := by
    calc 2 ^ (N.choose 2) = T.powerset.card := by rw [card_powerset, hT]
      _ ≤ _ := card_le_card hsub
      _ ≤ ∑ s ∈ powersetCard n (univ : Finset (Fin N)),
            (T.powerset.filter (fun E => A s ⊆ E) ∪ T.powerset.filter (fun E => Disjoint (A s) E)).card :=
          card_biUnion_le
      _ ≤ ∑ s ∈ powersetCard n (univ : Finset (Fin N)), (2 * 2 ^ (N.choose 2 - n.choose 2)) := by
          refine sum_le_sum fun s hs => ?_
          have hsn : s.card = n := (mem_powersetCard.1 hs).2
          refine (card_union_le _ _).trans ?_
          rw [card_powerset_filter_superset T _ (hAT s), card_powerset_filter_disjoint T _ (hAT s),
            hT, hA, hsn]
          omega
      _ = N.choose n * (2 * 2 ^ (N.choose 2 - n.choose 2)) := by
          simp [sum_const, card_powersetCard]
  rcases le_or_gt n N with hnN | hnN
  · have hd : n.choose 2 ≤ N.choose 2 := Nat.choose_le_choose 2 hnN
    have h2 : 2 ^ (N.choose 2) = 2 ^ (n.choose 2) * 2 ^ (N.choose 2 - n.choose 2) := by
      rw [← pow_add]; congr 1; omega
    rw [h2] at hle
    have hpos : 0 < 2 ^ (N.choose 2 - n.choose 2) := by positivity
    have : 2 ^ (n.choose 2) ≤ N.choose n * 2 := by
      refine Nat.le_of_mul_le_mul_right ?_ hpos
      calc _ ≤ _ := hle
        _ = _ := by ring
    omega
  · rw [Nat.choose_eq_zero_of_lt hnN] at hle
    simp at hle

/-- CO-262, in the form printed in the book: if `C(N,n) * 2^(1 - C(n,2)) < 1` then some graph on
`N` vertices has no `n`-clique and no independent `n`-set. -/
@[kb "kellertrotter2017" "Theorem 11.4, p. 256"]
theorem exists_graph_no_clique_no_independent_real (N n : ℕ)
    (h : (N.choose n : ℝ) * (2 : ℝ) ^ (1 - (n.choose 2 : ℤ)) < 1) :
    ∃ G : SimpleGraph (Fin N), G.CliqueFree n ∧ Gᶜ.CliqueFree n := by
  apply exists_graph_no_clique_no_independent
  have hpos : (0 : ℝ) < 2 ^ n.choose 2 := by positivity
  rw [zpow_sub₀ (by norm_num), zpow_one, zpow_natCast, ← mul_div_assoc, div_lt_one hpos] at h
  have : ((2 * N.choose n : ℕ) : ℝ) < ((2 ^ n.choose 2 : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast this

/-- CO-262, consequence for Ramsey numbers: under the counting hypothesis `R(n,n) > N`. -/
@[kb "kellertrotter2017" "Theorem 11.4, p. 256"]
theorem not_ramseyProp_of_counting (N n : ℕ) (h : 2 * N.choose n < 2 ^ n.choose 2) :
    ¬ RamseyProp n n N := by
  intro hR
  obtain ⟨G, h1, h2⟩ := exists_graph_no_clique_no_independent N n h
  rcases hR (Fin N) (by simp) G with h | h
  · exact h h1
  · exact h h2

end UndergradKB.Combinatorics
