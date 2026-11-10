import Mathlib.Combinatorics.SimpleGraph.Hall
import Mathlib.Combinatorics.SimpleGraph.Matching
import UndergradKB.Common.Attr

/-!
# Keller–Trotter, Chapter 14 (matchings): thin wrappers over Mathlib
-/

namespace UndergradKB.Combinatorics.Course.KellerTrotter
open SimpleGraph

/-- CO-304. Hall's theorem for a finite bipartite graph with parts `p₁`, `p₂`: there is a matching
saturating `p₁` iff every `A ⊆ p₁` has at least `|A|` neighbours. -/
@[kb "kellertrotter2017" "Theorem 14.7, p. 307"]
theorem thm_14_7 {V : Type*} [Finite V] {G : SimpleGraph V} {p₁ p₂ : Set V}
    (h : G.IsBipartiteWith p₁ p₂) :
    (∃ M : G.Subgraph, p₁ ⊆ M.verts ∧ M.IsMatching) ↔
      ∀ s ⊆ p₁, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard := by
  classical
  have :=Fintype.ofFinite V
  constructor
  · rintro ⟨M, hM1, hM⟩ s hs
    have : ∀ v : V, ∃ w, v ∈ M.verts → M.Adj v w := fun v => by
      by_cases hv : v ∈ M.verts
      · obtain ⟨w, hw, _⟩ := hM hv
        exact ⟨w, fun _ => hw⟩
      · exact ⟨v, fun h => (hv h).elim⟩
    choose f hf using this
    refine Set.ncard_le_ncard_of_injOn f (fun x hx => ?_) (fun x hx y hy hxy => ?_)
      (Set.toFinite _)
    · simp only [Set.mem_iUnion, mem_neighborSet]
      exact ⟨x, hx, (hf x (hM1 (hs hx))).adj_sub⟩
    · have hx' := (hf x (hM1 (hs hx))).symm
      have hy' := (hf y (hM1 (hs hy))).symm
      rw [← hxy] at hy'
      obtain ⟨u, _, hu⟩ := hM (hx'.fst_mem)
      exact (hu x hx').trans (hu y hy').symm
  · exact exists_isMatching_of_forall_ncard_le h


/-- CO-301. A matching is a subgraph in which every vertex it contains has exactly one partner
(so no two of its edges share an endpoint). -/
@[kb "kellertrotter2017" "Definition (unnumbered) matching, p. 304"]
theorem def_p304_matching {V : Type*} {G : SimpleGraph V} (M : G.Subgraph) :
    M.IsMatching ↔ ∀ v ∈ M.verts, ∃! w, M.Adj v w :=
  Iff.rfl

end UndergradKB.Combinatorics.Course.KellerTrotter
