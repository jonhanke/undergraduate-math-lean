import UndergradKB.Topology.DualityTheorem
import UndergradKB.Topology.DualityPlumbing
import UndergradKB.Topology.DualityExtension
import UndergradKB.Topology.DualityWave2b
import UndergradKB.Topology.DualityCompact2
import UndergradKB.Topology.TopGroups
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Algebra.Group.CompactOpen
import UndergradKB.Common.Attr

/-!
# Consequences of the duality theorem for locally compact abelian groups

Morris, Topology Without Tears, Appendix 5: Theorem A5.14.3 (TP-619) and Corollary A5.14.4 (TP-620).
-/

open Topology Set

set_option linter.unusedSectionVars false

universe u

namespace UndergradKB.Topology

namespace LCA

section Annihilator

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G]

/-- Precomposition with the quotient map by a closed subgroup is an embedding for the compact-open
topologies. -/
theorem isInducing_precomp_quotient_of_isClosed (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    Topology.IsInducing
      (fun ψ : C(G ⧸ H, Circle) => ψ.comp (⟨QuotientGroup.mk' H, QuotientGroup.continuous_mk⟩ :
        C(G, G ⧸ H))) := by
  haveI : IsClosed (H : Set G) := hH
  refine ⟨le_antisymm ?_ ?_⟩
  · exact continuous_iff_le_induced.1 (ContinuousMap.continuous_precomp _)
  · rw [ContinuousMap.compactOpen_eq]
    apply le_generateFrom
    rintro _ ⟨C', hC', U, hU, rfl⟩
    obtain ⟨C, hC, hC'C⟩ := exists_isCompact_lift H hC'
    have hS : IsCompact (C ∩ (QuotientGroup.mk : G → G ⧸ H) ⁻¹' C') :=
      hC.inter_right (hC'.isClosed.preimage QuotientGroup.continuous_mk)
    have himg : (QuotientGroup.mk : G → G ⧸ H) ''
        (C ∩ (QuotientGroup.mk : G → G ⧸ H) ⁻¹' C') = C' := by
      ext y
      constructor
      · rintro ⟨s, ⟨-, hs⟩, rfl⟩
        exact hs
      · intro hy
        obtain ⟨c, hc, rfl⟩ := hC'C hy
        exact ⟨c, ⟨hc, hy⟩, rfl⟩
    rw [isOpen_induced_iff]
    refine ⟨{φ : C(G, Circle) | Set.MapsTo φ (C ∩ (QuotientGroup.mk : G → G ⧸ H) ⁻¹' C') U},
      ContinuousMap.isOpen_setOfPred_mapsTo hS hU, ?_⟩
    ext ψ
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    constructor
    · intro h y hy
      rw [← himg] at hy
      obtain ⟨s, hs, rfl⟩ := hy
      exact h hs
    · intro h s hs
      exact h (himg ▸ ⟨s, hs, rfl⟩)

/-- For a closed subgroup `H`, the map `(G/H)^ → G^` is an embedding onto the annihilator of `H`. -/
theorem dual_quotient_embedding (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    Function.Injective (PontryaginDual.map (quotHom H)) ∧
      Set.range (PontryaginDual.map (quotHom H)) = (annih H : Set (PontryaginDual G)) ∧
      Topology.IsEmbedding (PontryaginDual.map (quotHom H)) := by
  haveI : IsClosed (H : Set G) := hH
  have hinj : Function.Injective (PontryaginDual.map (quotHom H)) :=
    PontryaginDual_map_injective_of_surjective (quotHom H) (QuotientGroup.mk'_surjective H)
  have hrange : Set.range (PontryaginDual.map (quotHom H)) =
      (annih H : Set (PontryaginDual G)) := by
    ext χ
    constructor
    · rintro ⟨ψ, rfl⟩ k hk
      show ψ (QuotientGroup.mk k) = 1
      rw [(QuotientGroup.eq_one_iff k).2 hk]
      exact map_one ψ
    · intro hχ
      obtain ⟨ψ, hψ⟩ := exists_char_quotient_of_trivial H χ hχ
      exact ⟨ψ, PontryaginDual.ext fun y => hψ y⟩
  have hind : Topology.IsInducing (PontryaginDual.map (quotHom H)) := by
    have h1 := ContinuousMonoidHom.isInducing_toContinuousMap G Circle
    have h2 := ContinuousMonoidHom.isInducing_toContinuousMap (G ⧸ H) Circle
    have h3 := (isInducing_precomp_quotient_of_isClosed H hH).comp h2
    refine Topology.IsInducing.of_comp (PontryaginDual.map (quotHom H)).continuous h1.continuous ?_
    exact h3
  exact ⟨hinj, hrange, ⟨hind, hinj⟩⟩

/-- The topological isomorphism `(G/H)^ ≃ Ω(H)`, `ψ ↦ ψ ∘ (G → G/H)`. -/
noncomputable def dualQuotientEquivAnnih (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    PontryaginDual (G ⧸ H) ≃ₜ* ↥(annih H) :=
  let hd := dual_quotient_embedding H hH
  let f : PontryaginDual (G ⧸ H) →* ↥(annih H) :=
    (PontryaginDual.map (quotHom H)).toMonoidHom.codRestrict (annih H) (fun ψ => by
      have : PontryaginDual.map (quotHom H) ψ ∈ Set.range (PontryaginDual.map (quotHom H)) :=
        ⟨ψ, rfl⟩
      rw [hd.2.1] at this
      exact this)
  have hbij : Function.Bijective f :=
    ⟨fun a b h => hd.1 (congrArg Subtype.val h), fun y => by
      have : (y : PontryaginDual G) ∈ Set.range (PontryaginDual.map (quotHom H)) := by
        rw [hd.2.1]
        exact y.2
      obtain ⟨ψ, hψ⟩ := this
      exact ⟨ψ, Subtype.ext hψ⟩⟩
  { toMulEquiv := MulEquiv.ofBijective f hbij
    continuous_toFun := Continuous.subtype_mk (PontryaginDual.map (quotHom H)).continuous _
    continuous_invFun := by
      have hg : ∀ y, PontryaginDual.map (quotHom H) ((MulEquiv.ofBijective f hbij).symm y) =
          (y : PontryaginDual G) := fun y =>
        congrArg Subtype.val ((MulEquiv.ofBijective f hbij).apply_symm_apply y)
      show Continuous (MulEquiv.ofBijective f hbij).symm
      refine hd.2.2.isInducing.continuous_iff.2 ?_
      have : (PontryaginDual.map (quotHom H)) ∘ (MulEquiv.ofBijective f hbij).symm =
          Subtype.val := funext hg
      rw [this]
      exact continuous_subtype_val }

theorem dualQuotientEquivAnnih_apply (H : Subgroup G) (hH : IsClosed (H : Set G))
    (ψ : PontryaginDual (G ⧸ H)) (y : G) :
    ((dualQuotientEquivAnnih H hH ψ : ↥(annih H)) : PontryaginDual G) y = ψ (y : G ⧸ H) := rfl

/-- Morris, Topology Without Tears, Theorem A5.14.3 (TP-619) and Corollary A5.14.4 (TP-620). Let `H`
be a closed subgroup of a locally compact Hausdorff abelian group `G`, with annihilator `Ω` in the dual
group `Γ`.  Then `Γ / Ω` is topologically isomorphic to `H^`, by an isomorphism taking the class of `γ`
to the restriction `γ|_H`. -/
theorem exists_dual_closedSubgroup_equiv (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    ∃ Θ : (PontryaginDual G ⧸ annih H) ≃ₜ* PontryaginDual H,
      ∀ γ : PontryaginDual G, Θ (γ : PontryaginDual G ⧸ annih H) =
        PontryaginDual.map (inclHom H) γ := by
  have hΩc : IsClosed ((annih H : Subgroup (PontryaginDual G)) : Set (PontryaginDual G)) :=
    isClosed_characterAnnihilator H
  haveI : IsClosed ((annih H : Subgroup (PontryaginDual G)) : Set (PontryaginDual G)) := hΩc
  let E1 := dualQuotientEquivAnnih (G := PontryaginDual G) (annih H) hΩc
  obtain ⟨e0, he0⟩ := dualityHolds_of_LCA (G := G)
  have hmem : ∀ x : G, x ∈ H ↔ e0 x ∈ annih (annih H) := by
    intro x
    constructor
    · intro hx χ hχ
      show e0 x χ = 1
      rw [he0]
      exact hχ x hx
    · intro hx
      by_contra hxH
      obtain ⟨χ, hχ1, hχ2⟩ := exists_char_trivial_on_ne_of_LCA H hH hxH
      have : e0 x χ = 1 := hx χ hχ1
      rw [he0] at this
      exact hχ2 this
  let E2 : ↥H ≃ₜ* ↥(annih (annih H)) :=
    { toFun := fun h => ⟨e0 (h : G), (hmem h).1 h.2⟩
      invFun := fun y => ⟨e0.symm y, (hmem _).2 (by rw [e0.apply_symm_apply]; exact y.2)⟩
      left_inv := fun h => Subtype.ext (e0.symm_apply_apply (h : G))
      right_inv := fun y => Subtype.ext (e0.apply_symm_apply y)
      map_mul' := fun a b => Subtype.ext (map_mul e0 (a : G) (b : G))
      continuous_toFun := Continuous.subtype_mk (e0.continuous.comp continuous_subtype_val) _
      continuous_invFun :=
        Continuous.subtype_mk (e0.symm.continuous.comp continuous_subtype_val) _ }
  let e : ↥H ≃ₜ* PontryaginDual (PontryaginDual G ⧸ annih H) := E2.trans E1.symm
  have he : ∀ (h : H) (γ : PontryaginDual G), e h (γ : PontryaginDual G ⧸ annih H) = γ h := by
    intro h γ
    have h1 : E1 (e h) = E2 h := E1.apply_symm_apply (E2 h)
    have h2 := congrArg (fun z : ↥(annih (annih H)) => (z : PontryaginDual (PontryaginDual G)) γ) h1
    exact h2.trans (he0 (h : G) γ)
  obtain ⟨d, hd⟩ := dualityHolds_of_LCA (G := PontryaginDual G ⧸ annih H)
  refine ⟨d.trans (dualCongr e).symm, fun γ => ?_⟩
  refine PontryaginDual.ext fun h => ?_
  show (dualCongr e).symm (d (γ : PontryaginDual G ⧸ annih H)) h = γ h
  rw [dualCongr_symm_apply, hd]
  exact he h γ

/-- Morris, Topology Without Tears, Corollary A5.14.4 (TP-620). Every character of a closed subgroup of
a locally compact Hausdorff abelian group extends to a character of the group. -/
@[kb "morris2024" "Corollary A5.14.4, p. 603"]
theorem exists_extend_char_closedSubgroup (H : Subgroup G) (hH : IsClosed (H : Set G))
    (ψ : PontryaginDual H) : ∃ χ : PontryaginDual G, ∀ k : H, χ k = ψ k := by
  obtain ⟨Θ, hΘ⟩ := exists_dual_closedSubgroup_equiv H hH
  obtain ⟨γ, hγ⟩ := QuotientGroup.mk_surjective (Θ.symm ψ)
  refine ⟨γ, fun k => ?_⟩
  have h1 : Θ (γ : PontryaginDual G ⧸ annih H) = ψ := by
    rw [hγ]
    exact Θ.apply_symm_apply ψ
  rw [hΘ γ] at h1
  exact DFunLike.congr_fun h1 k

/-- Morris, Topology Without Tears, Theorem A5.14.3 (TP-619). For a closed subgroup `H` of a locally
compact Hausdorff abelian group `G`: the annihilator of `H` is topologically isomorphic to the dual
`(G/H)^` of `G/H` (by `ψ ↦ ψ ∘ (G → G/H)`), and the dual `H^` of `H` is topologically isomorphic to
`G^ / Ω(H)` (by restriction of characters). -/
@[kb "morris2024" "Theorem A5.14.3, p. 603"]
theorem annih_and_dual_of_closedSubgroup (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    (∃ E : PontryaginDual (G ⧸ H) ≃ₜ* ↥(annih H), ∀ (ψ : PontryaginDual (G ⧸ H)) (y : G),
        ((E ψ : ↥(annih H)) : PontryaginDual G) y = ψ (y : G ⧸ H)) ∧
      ∃ Θ : (PontryaginDual G ⧸ annih H) ≃ₜ* PontryaginDual H,
        ∀ γ : PontryaginDual G, Θ (γ : PontryaginDual G ⧸ annih H) =
          PontryaginDual.map (inclHom H) γ :=
  ⟨⟨dualQuotientEquivAnnih H hH, fun ψ y => rfl⟩, exists_dual_closedSubgroup_equiv H hH⟩

end Annihilator

/-! ### Metrizability and σ-compactness of the dual -/

section Metrizable

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G]

/-- Morris, Topology Without Tears, Theorem A5.15.1 (TP-625). A locally compact Hausdorff abelian group
is metrizable if and only if its dual group is σ-compact. -/
@[kb "morris2024" "Theorem A5.15.1, p. 608"]
theorem metrizableSpace_iff_sigmaCompactSpace_dual :
    TopologicalSpace.MetrizableSpace G ↔ SigmaCompactSpace (PontryaginDual G) := by
  constructor
  · intro hG
    obtain ⟨x, hx⟩ := (𝓝 (1 : G)).exists_antitone_basis
    have hxn : ∀ n, x n ∈ 𝓝 (1 : G) := fun n => hx.mem n
    choose C hCn hCsub hCc using fun n => local_compact_nhds (hxn n)
    have hP : ∀ n, charsMapping (C n) (arcVa (1 / 5)) ∈ 𝓝 (1 : PontryaginDual G) ∧
        IsCompact (closure (charsMapping (C n) (arcVa (1 / 5)))) := fun n =>
      compact_nhds_charsMapping (C n) (hCc n) (hCn n) (a := 1 / 5) (by norm_num) (by norm_num)
    refine ⟨⟨fun n => closure (charsMapping (C n) (arcVa (1 / 5))), fun n => (hP n).2, ?_⟩⟩
    refine Set.eq_univ_of_forall fun γ => ?_
    have hV : arcVa (1 / 5) ∈ 𝓝 (1 : Circle) := by
      rw [arcVa_eq_centeredArc]
      refine (Circle.isOpen_centeredArc _).mem_nhds ⟨0, ?_, Circle.exp_zero⟩
      show |(0 : ℝ)| < 2 * Real.pi * (1 / 5)
      rw [abs_zero]
      positivity
    have h1 : (γ : G → Circle) ⁻¹' arcVa (1 / 5) ∈ 𝓝 (1 : G) := by
      have h0 : (γ : G → Circle) 1 = 1 := map_one γ
      have := γ.continuous.continuousAt (x := (1 : G))
      exact this.preimage_mem_nhds (show arcVa (1 / 5) ∈ 𝓝 ((γ : G → Circle) 1) by rw [h0]; exact hV)
    obtain ⟨n, -, hn⟩ := hx.toHasBasis.mem_iff.1 h1
    exact Set.mem_iUnion.2 ⟨n, subset_closure (fun y hy => hn (hCsub n hy))⟩
  · intro hσ
    haveI : SigmaCompactSpace (PontryaginDual G) := hσ
    haveI : (uniformity Circle).IsCountablyGenerated := by
      have : (@uniformity Circle Circle.instMetricSpace.toUniformSpace).IsCountablyGenerated :=
        inferInstance
      exact this
    haveI : TopologicalSpace.MetrizableSpace C(PontryaginDual G, Circle) :=
      UniformSpace.metrizableSpace
    have hemb := ContinuousMonoidHom.isEmbedding_toContinuousMap (PontryaginDual G) Circle
    haveI : TopologicalSpace.MetrizableSpace (PontryaginDual (PontryaginDual G)) :=
      hemb.metrizableSpace
    obtain ⟨e0, -⟩ := dualityHolds_of_LCA (G := G)
    exact e0.toHomeomorph.isEmbedding.metrizableSpace

/-- Morris, Topology Without Tears, Corollary A5.15.2 (TP-626). A locally compact Hausdorff abelian
group is compact and metrizable if and only if its dual group is countable. -/
@[kb "morris2024" "Corollary A5.15.2, p. 609"]
theorem compactSpace_and_metrizableSpace_iff_countable_dual :
    (CompactSpace G ∧ TopologicalSpace.MetrizableSpace G) ↔ Countable (PontryaginDual G) := by
  constructor
  · rintro ⟨hc, hm⟩
    exact UndergradKB.Topology.metrizableSpace_iff_countable_dual.1 hm
  · intro hcount
    haveI : DiscreteTopology (PontryaginDual G) := discreteTopology_of_countable_locallyCompact
    obtain ⟨e0, -⟩ := dualityHolds_of_LCA (G := G)
    haveI : CompactSpace (PontryaginDual (PontryaginDual G)) := inferInstance
    refine ⟨e0.toHomeomorph.symm.compactSpace, ?_⟩
    rw [metrizableSpace_iff_sigmaCompactSpace_dual]
    exact inferInstance

end Metrizable

/-! ### Compact elements of the dual and the identity component -/

section CompactElements

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G]

/-- Morris, Topology Without Tears, Theorem A5.15.8 (TP-630), the inclusion "compact elements of the
dual annihilate the identity component". A compact element of the dual group `Γ` of a locally compact
Hausdorff abelian group `G` is trivial on the connected component of the identity of `G`. -/
@[kb "morris2024" "Theorem A5.15.8, p. 611"]
theorem char_eq_one_on_connectedComponent_of_isCompactElement (γ : PontryaginDual G)
    (hγ : IsCompactElement γ) {g : G} (hg : g ∈ connectedComponent (1 : G)) : γ g = 1 := by
  obtain ⟨K, hKdef⟩ : ∃ K : Subgroup (PontryaginDual G),
      K = (Subgroup.zpowers γ).topologicalClosure := ⟨_, rfl⟩
  have hKc : IsCompact (K : Set (PontryaginDual G)) := by rw [hKdef]; exact hγ
  have hκ : γ ∈ K := by rw [hKdef]; exact Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers γ)
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  have hev : ∀ x : G, Continuous (fun χ : G →ₜ* Circle => χ x) := fun x => continuous_eval_const x
  let Λ : G → PontryaginDual K := fun x =>
    { toFun := fun κ => (κ : PontryaginDual G) x
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      continuous_toFun := (hev x).comp continuous_subtype_val }
  have hjoint : Continuous (fun p : G × ↥K => ((p.2 : PontryaginDual G) : G →ₜ* Circle) p.1) := by
    have h : Continuous (fun p : (G →ₜ* Circle) × G => p.1 p.2) := continuous_eval
    have hsnd : Continuous (fun p : G × ↥K => (p.2 : PontryaginDual G)) :=
      continuous_subtype_val.comp continuous_snd
    exact h.comp (hsnd.prodMk continuous_fst)
  have hΛ : Continuous Λ :=
    ContinuousMonoidHom.continuous_of_continuous_uncurry Λ hjoint
  have hconst := isPreconnected_connectedComponent.constant hΛ.continuousOn hg mem_connectedComponent
  have := DFunLike.congr_fun hconst ⟨γ, hκ⟩
  exact this.trans (map_one γ)

/-- Morris, Topology Without Tears, Corollary A5.15.10 (TP-631), one direction. If a locally compact
Hausdorff abelian group `G` is connected, its dual group has no non-trivial compact subgroup. -/
@[kb "morris2024" "Corollary A5.15.10, p. 612"]
theorem eq_bot_of_isCompact_subgroup_dual_of_connectedSpace [ConnectedSpace G]
    (K : Subgroup (PontryaginDual G)) (hK : IsCompact (K : Set (PontryaginDual G))) : K = ⊥ := by
  rw [eq_bot_iff]
  intro γ hγ
  have hc : IsCompactElement γ := by
    refine hK.of_isClosed_subset (Subgroup.isClosed_topologicalClosure _) ?_
    exact (Subgroup.topologicalClosure_minimal _ ((Subgroup.zpowers_le).2 hγ)
      hK.isClosed : _ ≤ K)
  rw [Subgroup.mem_bot]
  refine PontryaginDual.ext fun g => ?_
  have hg : g ∈ connectedComponent (1 : G) := by
    rw [PreconnectedSpace.connectedComponent_eq_univ]
    trivial
  rw [char_eq_one_on_connectedComponent_of_isCompactElement γ hc hg]
  rfl

end CompactElements

end LCA

end UndergradKB.Topology
