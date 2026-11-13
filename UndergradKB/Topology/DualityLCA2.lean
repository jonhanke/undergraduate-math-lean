import UndergradKB.Topology.DualityLCA
import UndergradKB.Topology.DualityCompact2
import UndergradKB.Topology.ClassicalDuals
import UndergradKB.Topology.GroupsExtra
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Topology.Instances.ZMod
import UndergradKB.Common.Attr

/-!
# Compact groups with finitely generated dual; closed subgroups of the torus

Morris, Topology Without Tears, Appendix 5.  A compact Hausdorff abelian group whose dual group is
finitely generated is topologically isomorphic to `Tᵃ × F` with `F` finite and discrete (structure of
finitely generated abelian groups plus duality).  Consequences: closed subgroups of `Tⁿ`, and
Corollary A5.10.4 (TP-583) in the book's form.
-/

open Topology Set

set_option linter.unusedSectionVars false

universe u

namespace UndergradKB.Topology

noncomputable section

/-- A topological group is a finite-dimensional torus times a finite discrete group. -/
def IsTorusTimesFinite (G : Type u) [CommGroup G] [TopologicalSpace G] : Prop :=
  ∃ (a : ℕ) (F : Type) (_ : CommGroup F) (_ : TopologicalSpace F),
    Finite F ∧ DiscreteTopology F ∧ Nonempty (G ≃ₜ* (Fin a → Circle) × F)

/-- Reindexing a product of copies of a group along a bijection of the index sets. -/
def reindexPi {ι κ : Type*} (e : ι ≃ κ) (G : Type*) [CommGroup G] [TopologicalSpace G] :
    (ι → G) ≃ₜ* (κ → G) where
  toFun f k := f (e.symm k)
  invFun g i := g (e i)
  left_inv f := by funext i; simp
  right_inv g := by funext k; simp
  map_mul' _ _ := rfl
  continuous_toFun := continuous_pi fun k => continuous_apply _
  continuous_invFun := continuous_pi fun i => continuous_apply _

/-- A compact Hausdorff abelian group whose dual group is finitely generated is topologically
isomorphic to `Tᵃ × F` with `F` finite discrete. -/
theorem isTorusTimesFinite_of_fg_dual {K : Type u} [CommGroup K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [T2Space K] (hfg : Group.FG (PontryaginDual K)) :
    IsTorusTimesFinite K := by
  classical
  obtain ⟨ι, j, _, _, p, hp, ex, ⟨φ⟩⟩ :=
    CommGroup.equiv_free_prod_prod_multiplicative_zmod (PontryaginDual K)
  haveI : ∀ i, NeZero (p i ^ ex i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  let ψ : PontryaginDual K ≃ₜ*
      ((j → Multiplicative ℤ) × ((i : ι) → Multiplicative (ZMod (p i ^ ex i)))) :=
    { toMulEquiv := φ
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  obtain ⟨d, -⟩ := exists_continuousMulEquiv_dualDual_of_compact (K := K)
  let toCircle : PontryaginDual (j → Multiplicative ℤ) ≃ₜ* (j → Circle) :=
    (pontryaginDualPiEquiv (G := fun _ : j => Multiplicative ℤ)).trans
      (piCongr fun _ => dualIntEquivCircle)
  let T1 : K ≃ₜ* (j → Circle) ×
      PontryaginDual ((i : ι) → Multiplicative (ZMod (p i ^ ex i))) :=
    d.trans ((dualCongr ψ).trans ((pontryaginDualProdEquiv (j → Multiplicative ℤ)
      ((i : ι) → Multiplicative (ZMod (p i ^ ex i)))).trans
        (prodCongr toCircle (ContinuousMulEquiv.refl _))))
  exact ⟨Fintype.card j, PontryaginDual ((i : ι) → Multiplicative (ZMod (p i ^ ex i))),
    inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨T1.trans (prodCongr (reindexPi (Fintype.equivFin j) Circle) (ContinuousMulEquiv.refl _))⟩⟩

/-- Every closed subgroup of the torus `Tⁿ` is topologically isomorphic to `Tᵃ × F` with `F` finite
and discrete. -/
theorem isTorusTimesFinite_of_closedSubgroup (n : ℕ) (S : Subgroup (Fin n → Circle))
    (hS : IsClosed (S : Set (Fin n → Circle))) : IsTorusTimesFinite S := by
  haveI : CompactSpace S := isCompact_iff_compactSpace.1 hS.isCompact
  refine isTorusTimesFinite_of_fg_dual ?_
  let i : S →ₜ* (Fin n → Circle) := ⟨S.subtype, continuous_subtype_val⟩
  obtain ⟨hsurj, -⟩ := PontryaginDual_map_surjective_isQuotientMap_of_injective_compact i
    S.subtype_injective (fun _ _ hxy => characters_separate_points_of_compact hxy)
  obtain ⟨c⟩ := (exists_continuousMulEquiv_dual_circle_int_pow n).1
  haveI : Group.FG (PontryaginDual (Fin n → Circle)) := by
    have : Group.FG (Fin n → Multiplicative ℤ) := inferInstance
    exact Group.fg_of_surjective (f := c.symm.toMulEquiv.toMonoidHom) c.symm.surjective
  exact Group.fg_of_surjective (f := (PontryaginDual.map i).toMonoidHom) hsurj

/-- Morris, Topology Without Tears, Corollary A5.10.4 (TP-583), the book's form. Every neighbourhood
`U` of the identity in a compact Hausdorff abelian group `K` contains a closed subgroup `H` such that
`K / H` is topologically isomorphic to `Tᵃ × F` with `F` a finite discrete group. -/
@[kb "morris2024" "Corollary A5.10.4, p. 573"]
theorem exists_closedSubgroup_sub_nhds_quotient_torus_prod_finite {K : Type u} [CommGroup K]
    [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K] {U : Set K}
    (hU : U ∈ 𝓝 (1 : K)) :
    ∃ H : Subgroup K, IsClosed (H : Set K) ∧ (H : Set K) ⊆ U ∧ IsTorusTimesFinite (K ⧸ H) := by
  obtain ⟨H, n, e, hHc, hHU, hinj, hemb⟩ := exists_closedSubgroup_sub_nhds_quotient_closedEmbedding hU
  refine ⟨H, hHc, hHU, ?_⟩
  let S : Subgroup (Fin n → Circle) := (e : K ⧸ H →* (Fin n → Circle)).range
  have hSc : IsClosed (S : Set (Fin n → Circle)) := by
    have h2 : (S : Set (Fin n → Circle)) = Set.range e := MonoidHom.coe_range _
    rw [h2]
    exact hemb.isClosed_range
  obtain ⟨a, F, i1, i2, hF, hFd, ⟨T⟩⟩ := isTorusTimesFinite_of_closedSubgroup n S hSc
  let e0 : K ⧸ H ≃* S := MonoidHom.ofInjective (f := (e : K ⧸ H →* (Fin n → Circle))) hinj
  have hcont : Continuous e0 := Continuous.subtype_mk e.continuous (fun x => ⟨x, rfl⟩)
  haveI : CompactSpace (K ⧸ H) := inferInstance
  let h0 : (K ⧸ H) ≃ₜ S := hcont.homeoOfEquivCompactToT2 (f := e0.toEquiv)
  let E : K ⧸ H ≃ₜ* S :=
    { toMulEquiv := e0
      continuous_toFun := hcont
      continuous_invFun := h0.symm.continuous }
  exact ⟨a, F, i1, i2, hF, hFd, ⟨E.trans T⟩⟩

/-- The statement of `exists_closedSubgroup_sub_nhds_quotient_torus_prod_finite` unfolded: a closed
subgroup `H ⊆ U` and a topological group isomorphism `K / H ≃ₜ* Tᵃ × F` with `F` finite discrete. -/
theorem exists_closedSubgroup_sub_nhds_quotient_continuousMulEquiv {K : Type u} [CommGroup K]
    [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K] {U : Set K}
    (hU : U ∈ 𝓝 (1 : K)) :
    ∃ H : Subgroup K, IsClosed (H : Set K) ∧ (H : Set K) ⊆ U ∧
      ∃ (a : ℕ) (F : Type) (_ : CommGroup F) (_ : TopologicalSpace F),
        Finite F ∧ DiscreteTopology F ∧ Nonempty ((K ⧸ H) ≃ₜ* (Fin a → Circle) × F) := by
  obtain ⟨H, h1, h2, h3⟩ := exists_closedSubgroup_sub_nhds_quotient_torus_prod_finite hU
  exact ⟨H, h1, h2, h3⟩

end

end UndergradKB.Topology
