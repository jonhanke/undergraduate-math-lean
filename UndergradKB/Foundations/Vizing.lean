import UndergradKB.Foundations.Graphs
import Mathlib.Tactic.Linarith

/-!
# Foundations: edge colourings, bounds towards Vizing's theorem

Partial progress on Levin Thm 2.5.9 (`χ'(G) ≤ Δ(G) + 1`): the greedy bound
`χ'(G) ≤ 2 Δ(G) - 1`, together with the lower bound `Δ ≤ χ'` proved in `Graphs.lean`.
Vizing's theorem itself is not proved here.
-/

namespace UndergradKB.Foundations

open SimpleGraph

variable {V : Type*}

open Classical in
/-- Greedy step: a finite set of edges can be coloured with natural numbers `< k` so that edges
sharing a vertex differ, as soon as `2 Δ ≤ k + 1` (an edge meets at most `2 (Δ - 1)` others). -/
theorem exists_partial_edge_coloring [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hk : 2 * G.maxDegree ≤ k + 1) :
    ∀ S : Finset (Sym2 V), (↑S : Set (Sym2 V)) ⊆ G.edgeSet →
      ∃ c : Sym2 V → ℕ, (∀ e ∈ S, c e < k) ∧
        ∀ e ∈ S, ∀ e' ∈ S, e ≠ e' → (∃ v, v ∈ e ∧ v ∈ e') → c e ≠ c e' := by
  intro S
  induction S using Finset.induction_on with
  | empty => intro _; exact ⟨fun _ => 0, by simp, by simp⟩
  | insert e S heS ih =>
    intro hsub
    obtain ⟨c, hlt, hprop⟩ := ih (fun x hx => hsub (by simp [hx]))
    have heG : e ∈ G.edgeSet := hsub (by simp)
    -- the edges of `S` meeting `e`
    set N : Finset (Sym2 V) := S.filter (fun e' => ∃ v, v ∈ e ∧ v ∈ e') with hN
    have hNcard : N.card ≤ 2 * G.maxDegree - 2 := by
      induction e using Sym2.ind with
      | _ a b =>
      have hab : G.Adj a b := heG
      have hsubN : N ⊆ ((G.incidenceFinset a).erase s(a, b)) ∪
          ((G.incidenceFinset b).erase s(a, b)) := by
        intro e' he'
        rw [hN, Finset.mem_filter] at he'
        obtain ⟨he'S, v, hv, hv'⟩ := he'
        have hne : e' ≠ s(a, b) := fun h => heS (h ▸ he'S)
        have he'G : e' ∈ G.edgeSet := hsub (by simp [he'S])
        rw [Sym2.mem_iff] at hv
        rw [Finset.mem_union, Finset.mem_erase, Finset.mem_erase]
        rcases hv with rfl | rfl
        · exact Or.inl ⟨hne, by simp [mem_incidenceFinset, incidenceSet, he'G, hv']⟩
        · exact Or.inr ⟨hne, by simp [mem_incidenceFinset, incidenceSet, he'G, hv']⟩
      have hma : (G.incidenceFinset a).card ≤ G.maxDegree := by
        rw [card_incidenceFinset_eq_degree]; exact G.degree_le_maxDegree a
      have hmb : (G.incidenceFinset b).card ≤ G.maxDegree := by
        rw [card_incidenceFinset_eq_degree]; exact G.degree_le_maxDegree b
      have hea : s(a, b) ∈ G.incidenceFinset a := by
        simp [mem_incidenceFinset, incidenceSet, hab]
      have heb : s(a, b) ∈ G.incidenceFinset b := by
        simp [mem_incidenceFinset, incidenceSet, hab]
      calc N.card ≤ _ := Finset.card_le_card hsubN
        _ ≤ ((G.incidenceFinset a).erase s(a, b)).card +
              ((G.incidenceFinset b).erase s(a, b)).card := Finset.card_union_le _ _
        _ = (G.incidenceFinset a).card - 1 + ((G.incidenceFinset b).card - 1) := by
              rw [Finset.card_erase_of_mem hea, Finset.card_erase_of_mem heb]
        _ ≤ 2 * G.maxDegree - 2 := by omega
    have hpos : 1 ≤ G.maxDegree := by
      induction e using Sym2.ind with
      | _ a b =>
      have hab : G.Adj a b := heG
      calc 1 ≤ G.degree a := by
            rw [← card_neighborFinset_eq_degree]
            exact Finset.card_pos.2 ⟨b, by simpa using hab⟩
        _ ≤ G.maxDegree := G.degree_le_maxDegree a
    -- pick a colour below `k` not used on `N`
    have himg : (N.image c).card < k := by
      calc (N.image c).card ≤ N.card := Finset.card_image_le
        _ < k := by omega
    obtain ⟨col, hcolk, hcol⟩ : ∃ col, col < k ∧ col ∉ N.image c := by
      by_contra hcon
      push Not at hcon
      have : Finset.range k ⊆ N.image c := fun x hx => hcon x (Finset.mem_range.1 hx)
      have := Finset.card_le_card this
      simp at this
      omega
    refine ⟨Function.update c e col, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · simpa using hcolk
      · have hne : x ≠ e := fun h => heS (h ▸ hx)
        simpa [Function.update_of_ne hne] using hlt x hx
    · intro x hx y hy hxy hshare
      rcases Finset.mem_insert.1 hx with hxe | hxS <;> rcases Finset.mem_insert.1 hy with hye | hyS
      · exact absurd (hxe.trans hye.symm) hxy
      · subst hxe
        have hyne : y ≠ x := fun h => heS (h ▸ hyS)
        have hyN : y ∈ N := by rw [hN, Finset.mem_filter]; exact ⟨hyS, hshare.imp fun v hv => ⟨hv.1, hv.2⟩⟩
        have : c y ≠ col := fun h => hcol (Finset.mem_image.2 ⟨y, hyN, h⟩)
        simp [Function.update_of_ne hyne]
        exact fun h => this h.symm
      · subst hye
        have hxne : x ≠ y := fun h => heS (h ▸ hxS)
        have hxN : x ∈ N := by
          rw [hN, Finset.mem_filter]
          obtain ⟨v, hv1, hv2⟩ := hshare
          exact ⟨hxS, v, hv2, hv1⟩
        have : c x ≠ col := fun h => hcol (Finset.mem_image.2 ⟨x, hxN, h⟩)
        simp [Function.update_of_ne hxne]
        exact this
      · have hxne : x ≠ e := fun h => heS (h ▸ hxS)
        have hyne : y ≠ e := fun h => heS (h ▸ hyS)
        simp only [Function.update_of_ne hxne, Function.update_of_ne hyne]
        exact hprop x hxS y hyS hxy hshare

/-- The greedy bound: a finite graph has a proper edge colouring with `k` colours whenever
`2 Δ ≤ k + 1`. -/
theorem edgeColorable_of_two_mul_maxDegree_le [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ) (hk : 2 * G.maxDegree ≤ k + 1) : EdgeColorable G k := by
  classical
  obtain ⟨c, hlt, hprop⟩ := exists_partial_edge_coloring G k hk G.edgeFinset (by simp)
  refine ⟨fun e => ⟨c e.1, hlt e.1 (by simp)⟩, ?_⟩
  intro e e' hne hshare h
  exact hprop e.1 (by simp) e'.1 (by simp) (fun h => hne (Subtype.ext h)) hshare
    (congrArg Fin.val h)

/-- Greedy upper bound on the chromatic index: `χ'(G) ≤ 2 Δ(G) - 1` (for `Δ ≥ 1`). -/
theorem chromaticIndex_le_two_mul_maxDegree_sub_one [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (h : 1 ≤ G.maxDegree) :
    chromaticIndex G ≤ ((2 * G.maxDegree - 1 : ℕ) : ℕ∞) := by
  unfold chromaticIndex
  exact iInf_le_of_le ⟨2 * G.maxDegree - 1, edgeColorable_of_two_mul_maxDegree_le G _ (by omega)⟩
    le_rfl

/-- FO-359 (partial, towards Vizing's theorem). What is proved here: `Δ ≤ χ' ≤ 2 Δ - 1` for a finite graph with an edge. -/
theorem maxDegree_le_chromaticIndex_le [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : 1 ≤ G.maxDegree) :
    (G.maxDegree : ℕ∞) ≤ chromaticIndex G ∧
      chromaticIndex G ≤ ((2 * G.maxDegree - 1 : ℕ) : ℕ∞) :=
  ⟨levin_s2_5_maxDegree_le_chromaticIndex G, chromaticIndex_le_two_mul_maxDegree_sub_one G h⟩

end UndergradKB.Foundations
