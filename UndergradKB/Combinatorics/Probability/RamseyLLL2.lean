import UndergradKB.Combinatorics.Probability.RamseyLLL1
import UndergradKB.Common.Attr

/-!
# R(3,n) ≥ c n² / ln² n via the Local Lemma, part 2

The probability space on edge sets of `Fin N`, the bad events (triangles and independent
`n`-sets) and the independence hypothesis of the Local Lemma for them.
-/

namespace UndergradKB.Combinatorics

open Finset

namespace RamseyLLL

open ErdosGirth UndergradKB.Combinatorics.Probability

section Setup

variable (N n : ℕ)

/-- The random graph `G(N, p)` as a finite probability space on edge sets. -/
noncomputable def space (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    FinProbSpace (Finset (Sym2 (Fin N))) where
  p := wt p
  p_nonneg := wt_nonneg h0 h1
  sum_p := sum_wt p

lemma space_prob (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (A : Finset (Finset (Sym2 (Fin N)))) :
    (space N p h0 h1).prob A = ∑ S ∈ A, wt p S := rfl

/-- The sets of vertices carrying a bad event: triples and `n`-sets. -/
def good (X : Finset (Fin N)) : Prop := X.card = 3 ∨ X.card = n

/-- The bad event attached to a vertex set `X`: a triangle on `X` (if `|X| = 3`), no edge inside
`X` (if `|X| = n`), and the empty event otherwise. -/
noncomputable def ev (X : Finset (Fin N)) : Finset (Finset (Sym2 (Fin N))) :=
  open Classical in
  if X.card = 3 then univ.filter (fun S => DA X ⊆ S)
  else if X.card = n then univ.filter (fun S => Disjoint S (DA X)) else ∅

/-- Two vertex sets are neighbours if both carry events and they share a potential edge. -/
noncomputable def nbr (i : Finset (Fin N)) : Finset (Finset (Fin N)) :=
  open Classical in
  univ.filter (fun j => good N n j ∧ j ≠ i ∧ ¬ Disjoint (DA i) (DA j))

variable {N n}

lemma ev_eq_empty {X : Finset (Fin N)} (h : ¬ good N n X) : ev N n X = ∅ := by
  unfold good at h
  push Not at h
  unfold ev
  rw [if_neg h.1, if_neg h.2]

lemma depOn_ev (X : Finset (Fin N)) : DepOn (ev N n X) (DA X) := by
  classical
  intro S S' h
  unfold ev
  by_cases h3 : X.card = 3
  · rw [if_pos h3]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have e1 : DA X ⊆ S ↔ S ∩ DA X = DA X := Finset.inter_eq_right.symm
    have e2 : DA X ⊆ S' ↔ S' ∩ DA X = DA X := Finset.inter_eq_right.symm
    rw [e1, e2, h]
  · rw [if_neg h3]
    by_cases hn : X.card = n
    · rw [if_pos hn]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_iff_inter_eq_empty, h]
    · rw [if_neg hn]
      simp

lemma depOn_mono {A : Finset (Finset (Sym2 (Fin N)))} {F G : Finset (Sym2 (Fin N))}
    (hA : DepOn A F) (hFG : F ⊆ G) : DepOn A G := by
  intro S S' h
  apply hA
  rw [← Finset.inter_eq_right.mpr hFG, ← Finset.inter_assoc, ← Finset.inter_assoc, h]

open Classical in
lemma depOn_noneOf (S : Finset (Finset (Fin N))) :
    DepOn (noneOf (ev N n) S) ((S.filter (good N n)).biUnion DA) := by
  classical
  intro ω ω' h
  rw [← Finset.mem_coe, ← Finset.mem_coe] at *
  simp only [Finset.mem_coe, mem_noneOf]
  refine forall₂_congr fun j hj => ?_
  by_cases hg : good N n j
  · have hsub : DA j ⊆ (S.filter (good N n)).biUnion DA :=
      Finset.subset_biUnion_of_mem DA (Finset.mem_filter.mpr ⟨hj, hg⟩)
    rw [not_iff_not]
    exact depOn_mono (depOn_ev j) hsub ω ω' h
  · rw [ev_eq_empty hg]
    simp

/-- The Local Lemma's independence hypothesis holds for the bad events. -/
lemma lllIndep (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    LLLIndep (space N p h0 h1) (ev N n) (nbr N n) := by
  classical
  intro i S hiS hdis
  by_cases hg : good N n i
  · have hdisj : Disjoint (DA i) ((S.filter (good N n)).biUnion DA) := by
      rw [Finset.disjoint_biUnion_right]
      intro j hj
      have hj' := Finset.mem_filter.mp hj
      by_contra hcon
      apply Finset.disjoint_left.mp hdis hj'.1
      unfold nbr
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hj'.2, fun hji => hiS (hji ▸ hj'.1), hcon⟩
    simp only [space_prob]
    exact sum_wt_inter_depOn p (depOn_ev i) (depOn_noneOf S) hdisj
  · rw [ev_eq_empty hg]
    simp [FinProbSpace.prob]

end Setup

end RamseyLLL

end UndergradKB.Combinatorics
