import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Compactness.Compact
import UndergradKB.Topology.DualityDiscrete
import UndergradKB.Topology.Characters
import UndergradKB.Topology.ClassicalDuals
import UndergradKB.Topology.GroupsMore2
import UndergradKB.Common.Attr

/-!
# Duality for discrete groups, and a non-discrete topology on infinite abelian groups

Morris, Topology Without Tears, Appendix 5: the Pontryagin-van Kampen duality theorem for discrete
abelian groups (A5.11.6), the finite discrete factors of A5.9.4, injectivity of the Bohr map for
discrete groups, and the existence of non-discrete Hausdorff group topologies (A5.3.9).
-/

open Set Topology

namespace UndergradKB.Topology

noncomputable section

/-! ### TP-589: duality for discrete groups -/

section Discrete

variable (G : Type*) [CommGroup G] [TopologicalSpace G] [DiscreteTopology G]

/-- Every character of an abelian group, viewed as a continuous character of the discrete group. -/
def discreteChar (φ : G →* Circle) : PontryaginDual G :=
  ⟨φ, continuous_of_discreteTopology⟩

theorem toDualDual_injective : Function.Injective (toDualDual G) := by
  intro g h hgh
  by_contra hne
  obtain ⟨φ, hφ⟩ := exists_monoidHom_circle_apply_ne hne
  exact hφ (DFunLike.congr_fun hgh (discreteChar G φ))

theorem toDualDual_surjective : Function.Surjective (toDualDual G) := by
  let S : Subgroup (PontryaginDual (PontryaginDual G)) := (toDualDual G).toMonoidHom.range
  have hS : S = ⊤ := by
    refine subgroup_dual_eq_top_of_separatesPoints S fun χ χ' hne => ?_
    obtain ⟨g, hg⟩ : ∃ g, χ g ≠ χ' g := by
      by_contra h
      push Not at h
      exact hne (PontryaginDual.ext h)
    exact ⟨toDualDual G g, ⟨g, rfl⟩, hg⟩
  intro z
  have : z ∈ S := by rw [hS]; trivial
  obtain ⟨g, hg⟩ := this
  exact ⟨g, hg⟩

/-- Morris, Topology Without Tears, Theorem A5.11.6 (TP-589), Pontryagin-van Kampen duality for
discrete abelian groups. The canonical map `α : G → Γ^*`, `α g χ = χ g`, from a discrete abelian
group to the dual of its dual group is an isomorphism of topological groups. -/
@[kb "morris2024" "Theorem A5.11.6, p. 577"]
theorem exists_continuousMulEquiv_dualDual_of_discrete :
    ∃ e : G ≃ₜ* PontryaginDual (PontryaginDual G), ∀ g χ, e g χ = χ g := by
  have hbij : Function.Bijective (toDualDual G).toMonoidHom :=
    ⟨toDualDual_injective G, toDualDual_surjective G⟩
  refine ⟨{ toMulEquiv := MulEquiv.ofBijective _ hbij
            continuous_toFun := continuous_of_discreteTopology
            continuous_invFun := continuous_of_discreteTopology }, fun g χ => rfl⟩

/-- Duality in the form used by `DualityHolds`. -/
theorem dualityHolds_of_discrete : DualityHolds G :=
  exists_continuousMulEquiv_dualDual_of_discrete G

/-- Morris, Topology Without Tears, Corollary A5.9.4 (TP-575), the finite discrete factors: any
discrete abelian group (in particular a finite or finitely generated one) satisfies the duality
property, and so do all products `ℝᵃ × Tᵇ × D`. -/
@[kb "morris2024" "Corollary A5.9.4, p. 567"]
theorem dualityHolds_real_circle_pow_discrete (a b : ℕ) :
    DualityHolds (((Fin a → Multiplicative ℝ) × (Fin b → Circle)) × G) := by
  haveI : IsTopologicalGroup G := ⟨⟩
  exact ((DualityHolds.pi fun _ => dualityHolds_real).prod
    (DualityHolds.pi fun _ => dualityHolds_circle)).prod (dualityHolds_of_discrete G)

/-- Morris, Topology Without Tears, Corollary A5.9.4 (TP-575), the full statement: a finite product
`ℝᵃ × Tᵇ × ℤᶜ × F` with `F` a discrete abelian group satisfies the duality property. -/
@[kb "morris2024" "Corollary A5.9.4, p. 567"]
theorem dualityHolds_real_circle_int_pow_discrete (a b c : ℕ) :
    DualityHolds ((((Fin a → Multiplicative ℝ) × (Fin b → Circle)) × (Fin c → Multiplicative ℤ)) × G) := by
  haveI : IsTopologicalGroup G := ⟨⟩
  exact DualityHolds.prod (dualityHolds_real_circle_int_pow a b c) (dualityHolds_of_discrete G)

end Discrete

/-! ### TP-611: the Bohr map is injective for discrete groups -/

section Bohr

/-- Morris, Topology Without Tears, Exercises A5.13 #6 (TP-611). For a discrete abelian group the
canonical map `G → bG` into its Bohr compactification is injective: characters separate points. -/
@[kb "morris2024" "Exercises A5.13, p. 600"]
theorem injective_bohrMap_of_discrete (G : Type*) [CommGroup G] [TopologicalSpace G]
    [DiscreteTopology G] : Function.Injective (bohrMap G) := by
  rw [injective_bohrMap_iff]
  intro g h hgh
  obtain ⟨φ, hφ⟩ := exists_monoidHom_circle_apply_ne hgh
  exact ⟨discreteChar G φ, hφ⟩

end Bohr

/-! ### TP-531: a non-discrete Hausdorff group topology on an infinite abelian group -/

section NonDiscrete

/-- The evaluation embedding of an abelian group into the product of circles indexed by its
characters. -/
def evalChars (G : Type*) [CommGroup G] : G →* ((G →* Circle) → Circle) where
  toFun g φ := φ g
  map_one' := funext fun φ => map_one φ
  map_mul' g h := funext fun φ => map_mul φ g h

theorem evalChars_injective (G : Type*) [CommGroup G] : Function.Injective (evalChars G) := by
  intro g h hgh
  by_contra hne
  obtain ⟨φ, hφ⟩ := exists_monoidHom_circle_apply_ne hne
  exact hφ (congrFun hgh φ)

/-- Morris, Topology Without Tears, Theorem A5.3.9 (TP-531). Every infinite abelian group admits a
non-discrete Hausdorff group topology (the one induced by all its characters into the circle). -/
@[kb "morris2024" "Theorem A5.3.9, p. 532"]
theorem exists_nonDiscrete_t2_topologicalGroup (G : Type*) [CommGroup G] [Infinite G] :
    ∃ t : TopologicalSpace G, @IsTopologicalGroup G t _ ∧ @T2Space G t ∧ ¬ @DiscreteTopology G t := by
  let t : TopologicalSpace G := TopologicalSpace.induced (evalChars G) inferInstance
  letI := t
  have hind : IsInducing (evalChars G) := ⟨rfl⟩
  have hemb : IsEmbedding (evalChars G) := ⟨hind, evalChars_injective G⟩
  refine ⟨t, ?_, ?_, ?_⟩
  · exact IsInducing.isTopologicalGroup (evalChars G) hind
  · exact hemb.t2Space
  · intro hdisc
    let H : Subgroup ((G →* Circle) → Circle) := (evalChars G).range
    have hdiscH : DiscreteTopology H := by
      have : DiscreteTopology (Set.range (evalChars G)) := hemb.toHomeomorph.symm.isEmbedding.discreteTopology
      exact this
    have hclosed : IsClosed (H : Set ((G →* Circle) → Circle)) := Subgroup.isClosed_of_discreteTopology
    have hce : IsClosedEmbedding (evalChars G) :=
      ⟨hemb, by rw [← MonoidHom.coe_range]; exact hclosed⟩
    haveI : CompactSpace G := hce.compactSpace
    haveI : Finite G := finite_of_compact_of_discrete
    exact not_finite G

end NonDiscrete

end

end UndergradKB.Topology
