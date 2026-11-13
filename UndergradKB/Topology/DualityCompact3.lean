import UndergradKB.Topology.DualityCompact
import UndergradKB.Topology.DualityDiscrete3
import UndergradKB.Topology.DualityDiscrete4
import UndergradKB.Common.Attr

/-!
# Products of compact groups and extension of characters from subgroups of discrete groups

* Morris, Theorem A5.11.8 (TP-591), now without a separation hypothesis: for compact Hausdorff abelian
  `Kᵢ` the characters separate points (`DualityCompact.lean`).
* Morris, Corollary A5.14.4 (TP-620), discrete case.
-/

open Topology Set

universe u

namespace UndergradKB.Topology

noncomputable section

/-- Morris, Topology Without Tears, Theorem A5.11.8 (TP-591). The dual group of a product of compact
Hausdorff abelian groups is algebraically isomorphic to the restricted direct product of the dual
groups, via `γ ↦ (g ↦ ∏ᵢ γᵢ(gᵢ))`. -/
@[kb "morris2024" "Theorem A5.11.8, p. 578"]
def dualProdEquivOfCompact {ι : Type*} (K : ι → Type u) [∀ i, CommGroup (K i)]
    [∀ i, TopologicalSpace (K i)] [∀ i, IsTopologicalGroup (K i)] [∀ i, CompactSpace (K i)]
    [∀ i, T2Space (K i)] :
    restrictedDirectProduct (fun i => PontryaginDual (K i)) ≃* PontryaginDual (∀ i, K i) :=
  dualProdEquiv K fun _ _ _ hxy => characters_separate_points_of_compact hxy

/-- Morris, Topology Without Tears, Theorem A5.11.8 (TP-591). Every continuous character of a product of
compact Hausdorff abelian groups is trivial on all but finitely many factors. -/
@[kb "morris2024" "Theorem A5.11.8, p. 578"]
theorem dualProd_finite_support_of_compact {ι : Type*} [DecidableEq ι] (K : ι → Type u)
    [∀ i, CommGroup (K i)] [∀ i, TopologicalSpace (K i)] [∀ i, IsTopologicalGroup (K i)]
    [∀ i, CompactSpace (K i)] [∀ i, T2Space (K i)] (χ : PontryaginDual (∀ i, K i)) :
    {i | ∃ x : K i, χ (Pi.mulSingle i x) ≠ 1}.Finite :=
  dualProd_finite_support K (fun _ _ _ hxy => characters_separate_points_of_compact hxy) χ

/-- Morris, Topology Without Tears, Corollary A5.14.4 (TP-620), discrete case: every character of a
subgroup of a discrete abelian group extends to the group. -/
@[kb "morris2024" "Corollary A5.14.4, p. 603"]
theorem exists_extend_char_subgroup_of_discrete {B : Type*} [CommGroup B] [TopologicalSpace B]
    [DiscreteTopology B] (H : Subgroup B) (ψ : PontryaginDual H) :
    ∃ χ : PontryaginDual B, ∀ k : H, χ k = ψ k := by
  obtain ⟨χ, hχ⟩ := (PontryaginDual_map_isQuotientMap_subgroup_discrete H).1 ψ
  exact ⟨χ, fun k => DFunLike.congr_fun hχ k⟩

end

end UndergradKB.Topology
