import UndergradKB.Topology.StructureWave2c
import UndergradKB.Topology.DualityPlumbing
import UndergradKB.Topology.DualityExtension3
import UndergradKB.Common.Attr

/-!
# The Pontryagin-van Kampen duality theorem (Morris, Theorems A5.13.5 and A5.13.6)

* Theorem A5.13.5 (TP-607): a compactly generated locally compact Hausdorff abelian group satisfies
  the duality theorem.  By Proposition A5.12.10 (`exists_compact_subgroup_quotient_real_circle_int_finite`)
  there is a compact subgroup `K` with `G / K ≅ ℝᵃ × Tᶜ × ℤᵇ × F`, which satisfies duality, and
  duality extends along compact subgroups (`dualityHolds_of_compact_subgroup`).
* Theorem A5.13.6 (TP-572): every locally compact Hausdorff abelian group satisfies the duality
  theorem: it has an open compactly generated subgroup, and duality extends from open σ-compact
  subgroups (`dualityHolds_of_open_subgroup`).
-/

open Topology Set Pointwise

set_option linter.unusedSectionVars false

namespace UndergradKB.Topology

namespace LCA

universe u

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G]

/-- If `G = V · ⟨g₁, …, g_m⟩` with `V` compact, then `G` is σ-compact. -/
theorem sigmaCompactSpace_of_generated (V : Set G) (hV : IsCompact V) {m : ℕ} (g : Fin m → G)
    (hgen : ∀ y : G, ∃ v ∈ V, ∃ w ∈ Subgroup.closure (Set.range g), y = v * w) :
    SigmaCompactSpace G := by
  set S : Set G := (V ∪ Set.range g) ∪ (V ∪ Set.range g)⁻¹
  have hS : IsCompact S :=
    (hV.union (Set.finite_range g).isCompact).union (hV.union (Set.finite_range g).isCompact).inv
  have hSinv : S⁻¹ ⊆ S := by rw [Set.union_inv, inv_inv, Set.union_comm]
  have htop : (Subgroup.closure S : Set G) = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨v, hv, w, hw, rfl⟩ := hgen y
    refine mul_mem (Subgroup.subset_closure (Or.inl (Or.inl hv))) ?_
    exact Subgroup.closure_mono (fun z hz => Or.inl (Or.inr hz)) hw
  have := isSigmaCompact_closure_of_isCompact hS hSinv
  rw [htop] at this
  exact isSigmaCompact_univ_iff.1 this

/-- Morris, Topology Without Tears, Theorem A5.13.5 (TP-607). A compactly generated locally compact
Hausdorff abelian group (`G = V · ⟨g₁, …, g_m⟩`, `V` compact) satisfies the Pontryagin-van Kampen
duality theorem. -/
@[kb "morris2024" "Theorem A5.13.5, p. 595"]
theorem dualityHolds_of_generated (V : Set G) (hV : IsCompact V) {m : ℕ} (g : Fin m → G)
    (hgen : ∀ y : G, ∃ v ∈ V, ∃ w ∈ Subgroup.closure (Set.range g), y = v * w) :
    DualityHolds G := by
  have := sigmaCompactSpace_of_generated V hV g hgen
  obtain ⟨K, hK, a, b, c, F, _, _, _, _, ⟨e⟩⟩ :=
    exists_compact_subgroup_quotient_real_circle_int_finite V hV g hgen
  have : IsTopologicalGroup F := ⟨⟩
  have hE := dualityHolds_real_int_circle_discrete a b c F
  let e2 : ((((Fin a → Multiplicative ℝ) × (Fin c → Circle)) × (Fin b → Multiplicative ℤ)) × F) ≃ₜ*
      ((((Fin a → Multiplicative ℝ) × (Fin b → Multiplicative ℤ)) × (Fin c → Circle)) × F) :=
    prodCongr (swapLastTwo _ _ _) (ContinuousMulEquiv.refl F)
  exact dualityHolds_of_compact_subgroup K hK
    (DualityHolds.of_continuousMulEquiv (e.trans e2) hE)

/-- Every locally compact Hausdorff abelian group has an open subgroup `H` which is `V · ⟨g₁, …, g_m⟩`
for a compact `V ⊆ H` (Corollary A5.12.8 in the form used here). -/
theorem exists_open_generated_subgroup :
    ∃ H : Subgroup G, IsOpen (H : Set G) ∧ ∃ (V : Set H), IsCompact V ∧ ∃ (m : ℕ) (g : Fin m → H),
      ∀ y : H, ∃ v ∈ V, ∃ w ∈ Subgroup.closure (Set.range g), y = v * w := by
  classical
  obtain ⟨W, hWc, hW1⟩ := exists_compact_mem_nhds (1 : G)
  set V : Set G := W ∪ W⁻¹ with hVdef
  have hVc : IsCompact V := hWc.union hWc.inv
  have hVn : V ∈ 𝓝 (1 : G) := Filter.mem_of_superset hW1 fun y hy => Or.inl hy
  have hV1 : (1 : G) ∈ V := mem_of_mem_nhds hVn
  have hVinv : ∀ y ∈ V, y⁻¹ ∈ V := by
    rintro y (hy | hy)
    · exact Or.inr (by simpa using hy)
    · exact Or.inl hy
  obtain ⟨t, ht⟩ := (hVc.mul hVc).elim_nhds_subcover' (fun y _ => (fun z => y⁻¹ * z) ⁻¹' V)
    (fun y _ => (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds
      (by simpa using hVn))
  let F : Finset G := t.image (↑)
  have hFV : ∀ y ∈ V * V, ∃ f ∈ (F : Set G), ∃ v ∈ V, y = f * v := by
    intro y hy
    obtain ⟨f, hft, hyf⟩ := Set.mem_iUnion₂.1 (ht hy)
    exact ⟨f, Finset.mem_coe.2 (Finset.mem_image_of_mem _ hft), (f : G)⁻¹ * y, hyf,
      (mul_inv_cancel_left _ _).symm⟩
  set H := Subgroup.closure V
  have hgen : ∀ z ∈ H, ∃ v ∈ V, ∃ w ∈ Subgroup.closure (F : Set G), z = v * w := by
    intro z hz
    induction hz using Subgroup.closure_induction with
    | mem z hz => exact ⟨z, hz, 1, one_mem _, (mul_one z).symm⟩
    | one => exact ⟨1, hV1, 1, one_mem _, (mul_one 1).symm⟩
    | mul a b _ _ ha hb =>
      obtain ⟨v1, hv1, w1, hw1, rfl⟩ := ha
      obtain ⟨v2, hv2, w2, hw2, rfl⟩ := hb
      obtain ⟨f, hf, v3, hv3, h3⟩ := hFV (v1 * v2) (Set.mul_mem_mul hv1 hv2)
      refine ⟨v3, hv3, f * (w1 * w2), mul_mem (Subgroup.subset_closure hf) (mul_mem hw1 hw2), ?_⟩
      calc v1 * w1 * (v2 * w2) = (v1 * v2) * (w1 * w2) := by ac_rfl
        _ = v3 * (f * (w1 * w2)) := by rw [h3]; ac_rfl
    | inv a _ ha =>
      obtain ⟨v, hv, w, hw, rfl⟩ := ha
      exact ⟨v⁻¹, hVinv v hv, w⁻¹, inv_mem hw, by rw [mul_inv]⟩
  have hHo : IsOpen (H : Set G) :=
    Subgroup.isOpen_of_mem_nhds H (g := 1) (Filter.mem_of_superset hVn Subgroup.subset_closure)
  have hHcl : IsClosed (H : Set G) := Subgroup.isClosed_of_isOpen H hHo
  have hFH : ∀ f ∈ (F : Set G), f ∈ H := by
    intro f hf
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hf)
    obtain ⟨a, ha, b, hb, hab⟩ := y.2
    rw [← hab]
    exact mul_mem (Subgroup.subset_closure ha) (Subgroup.subset_closure hb)
  set m := F.card
  let e : Fin m → G := fun i => (F.equivFin.symm i : G)
  let gH : Fin m → H := fun i => ⟨e i, hFH _ (F.equivFin.symm i).2⟩
  have hmap : (Subgroup.closure (Set.range gH)).map H.subtype = Subgroup.closure (F : Set G) := by
    rw [MonoidHom.map_closure]
    congr 1
    ext y
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact (F.equivFin.symm i).2
    · intro hy
      refine ⟨gH (F.equivFin ⟨y, hy⟩), ⟨_, rfl⟩, ?_⟩
      simp [gH, e]
  refine ⟨H, hHo, (↑) ⁻¹' V, hHcl.isClosedEmbedding_subtypeVal.isCompact_preimage hVc, m, gH,
    fun y => ?_⟩
  obtain ⟨v, hv, w, hw, hy⟩ := hgen y y.2
  have hwH : w ∈ (Subgroup.closure (Set.range gH)).map H.subtype := hmap ▸ hw
  obtain ⟨wH, hwH', hwHeq⟩ := hwH
  refine ⟨⟨v, Subgroup.subset_closure hv⟩, hv, wH, hwH', Subtype.ext ?_⟩
  simp only [Subgroup.coe_mul]
  rw [hy]
  congr 1
  exact hwHeq.symm

/-- Morris, Topology Without Tears, Theorem A5.13.6 (TP-572). **Pontryagin-van Kampen duality**:
for every locally compact Hausdorff abelian group `G` the canonical map `G → G^^`, `g ↦ (χ ↦ χ g)`, is
an isomorphism of topological groups. -/
@[kb "morris2024" "Theorem A5.13.6, p. 596"]
theorem dualityHolds_of_LCA : DualityHolds G := by
  obtain ⟨H, hHo, V, hVc, m, g, hgen⟩ := exists_open_generated_subgroup (G := G)
  have : LocallyCompactSpace H := hHo.isOpenEmbedding_subtypeVal.locallyCompactSpace
  have := sigmaCompactSpace_of_generated V hVc g hgen
  exact dualityHolds_of_open_subgroup H hHo (dualityHolds_of_generated V hVc g hgen)

/-- Morris, Topology Without Tears, Remark A5.8.1 and Theorem A5.13.6 (TP-572), explicit form. -/
@[kb "morris2024" "Remark A5.8.1, p. 563"]
theorem exists_continuousMulEquiv_dualDual_of_LCA :
    ∃ e : G ≃ₜ* PontryaginDual (PontryaginDual G), ∀ g χ, e g χ = χ g :=
  dualityHolds_of_LCA

end LCA

end UndergradKB.Topology
