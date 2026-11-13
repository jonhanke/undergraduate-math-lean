import Mathlib.Topology.Neighborhoods
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation
import UndergradKB.Topology.FilterFacts
import UndergradKB.Common.Attr

/-!
# The equality in Morris, Proposition A6.1.30 fails in general

The topology built from a family of filters `S x` (`topologyOfFilters S`) has each `F ∈ S x`
converging to `x` (proved in `FilterFacts.lean`), so the neighbourhood filter of `x` is finer than the
intersection of the `S x`.  The book claims they are equal; on a three point set they are not.
-/

open Filter Set

namespace UndergradKB.Topology

/-- Morris, Topology Without Tears, Proposition A6.1.30 (TP-666), counterexample to the last equality.
On `Fin 3` take `S 0 = {𝓟 {0,1}}`, `S 1 = {𝓟 {1,2}}`, `S 2 = {𝓟 {2}}` (each non-empty, each filter
containing its point in all its members).  In the topology built from them the intersection of the
filters at `0` (here `𝓟 {0,1}`) is strictly smaller than the neighbourhood filter of `0` (the open set
containing `0` must contain `1`, hence `2`): `{0,1}` belongs to the intersection but is not a
neighbourhood of `0`.  So the neighbourhood filter is not, in general, the intersection of the filters
of `S x`; only the inclusion proved in `le_nhds_topologyOfFilters` holds. -/
@[kb "morris2024" "Proposition A6.1.30, p. 637"]
theorem nhds_ne_iSup_topologyOfFilters :
    ∃ S : Fin 3 → Set (Filter (Fin 3)), (∀ x, (S x).Nonempty) ∧
      (∀ x, ∀ F ∈ S x, ∀ s ∈ F, x ∈ s) ∧
      (⨆ G ∈ S 0, G) ≠ @nhds (Fin 3) (topologyOfFilters S) 0 := by
  let P : Fin 3 → Set (Fin 3) := ![{0, 1}, {1, 2}, {2}]
  have hP : ∀ x, x ∈ P x := by
    intro x
    fin_cases x <;> simp [P]
  refine ⟨fun x => {𝓟 (P x)}, fun x => ⟨_, rfl⟩, ?_, ?_⟩
  · intro x F hF s hs
    rw [Set.mem_singleton_iff] at hF
    subst hF
    exact mem_principal.1 hs (hP x)
  · intro h
    let S : Fin 3 → Set (Filter (Fin 3)) := fun x => {𝓟 (P x)}
    have hmem : ({0, 1} : Set (Fin 3)) ∈ (⨆ G ∈ S 0, G : Filter (Fin 3)) := by
      simp [S, P]
    letI := topologyOfFilters S
    rw [h, mem_nhds_iff] at hmem
    obtain ⟨O, hOs, hO, h0⟩ := hmem
    have hO' := (isOpen_topologyOfFilters_iff S).1 hO
    have h1 : (1 : Fin 3) ∈ O := by
      have := hO' 0 h0 (𝓟 (P 0)) rfl
      exact mem_principal.1 this (by simp [P])
    have h2 : (2 : Fin 3) ∈ O := by
      have := hO' 1 h1 (𝓟 (P 1)) rfl
      exact mem_principal.1 this (by simp [P])
    have := hOs h2
    simp at this

end UndergradKB.Topology
