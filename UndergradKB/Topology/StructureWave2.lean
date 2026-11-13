import UndergradKB.Topology.LCASeparation
import UndergradKB.Topology.DualityLCA2
import UndergradKB.Common.Attr

/-!
# Proposition A5.12.10 (Morris, Topology Without Tears): the quotient step

For a compactly generated locally compact Hausdorff abelian group `G` (given as `G = V · ⟨g₁, …, g_m⟩`
with `V` compact) we carry out the part of the book's proof of Proposition A5.12.10 that does not need
Theorem A5.5.25: there are a compact subgroup `K` and a discrete subgroup `D` of `G` with `K ∩ D = 1`
such that the image `D'` of `D` in `G / K` is discrete and `(G / K) / D'` is topologically isomorphic
to `Tⁿ × E` with `E` finite discrete.
-/

open Topology Set Filter

set_option linter.unusedSectionVars false

universe u

namespace UndergradKB.Topology

/-- Two quotient maps out of the same group with the same kernel have topologically isomorphic
targets. -/
theorem exists_continuousMulEquiv_of_isQuotientMap_of_ker_eq {G X Y : Type*} [CommGroup G]
    [CommGroup X] [CommGroup Y] [TopologicalSpace G] [TopologicalSpace X] [TopologicalSpace Y]
    (π1 : G →* X) (π2 : G →* Y) (h1 : IsQuotientMap π1) (h2 : IsQuotientMap π2)
    (hker : π1.ker = π2.ker) : Nonempty (X ≃ₜ* Y) := by
  have hf : ∀ a b : G, π1 a = π1 b → π2 a = π2 b := by
    intro a b hab
    have : a * b⁻¹ ∈ π1.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab, mul_inv_cancel]
    rw [hker, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at this
    exact this
  have hg : ∀ a b : G, π2 a = π2 b → π1 a = π1 b := by
    intro a b hab
    have : a * b⁻¹ ∈ π2.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab, mul_inv_cancel]
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at this
    exact this
  let φ0 : X → Y := fun x => π2 (Function.surjInv h1.surjective x)
  let ψ0 : Y → X := fun y => π1 (Function.surjInv h2.surjective y)
  have hφ0 : ∀ a, φ0 (π1 a) = π2 a := fun a =>
    hf _ _ (Function.surjInv_eq h1.surjective (π1 a))
  have hψ0 : ∀ a, ψ0 (π2 a) = π1 a := fun a =>
    hg _ _ (Function.surjInv_eq h2.surjective (π2 a))
  have hφc : Continuous φ0 := by
    rw [h1.continuous_iff]
    have : φ0 ∘ π1 = π2 := funext hφ0
    rw [this]
    exact h2.continuous
  have hψc : Continuous ψ0 := by
    rw [h2.continuous_iff]
    have : ψ0 ∘ π2 = π1 := funext hψ0
    rw [this]
    exact h1.continuous
  let φ : C(X, Y) := ⟨φ0, hφc⟩
  let ψ : C(Y, X) := ⟨ψ0, hψc⟩
  have hφ : ∀ a, φ (π1 a) = π2 a := hφ0
  have hψ : ∀ a, ψ (π2 a) = π1 a := hψ0
  refine ⟨{ toFun := φ
            invFun := ψ
            left_inv := ?_
            right_inv := ?_
            map_mul' := ?_
            continuous_toFun := φ.continuous
            continuous_invFun := ψ.continuous }⟩
  · intro x
    obtain ⟨a, rfl⟩ := h1.surjective x
    show ψ (φ (π1 a)) = π1 a
    rw [hφ, hψ]
  · intro y
    obtain ⟨a, rfl⟩ := h2.surjective y
    show φ (ψ (π2 a)) = π2 a
    rw [hψ, hφ]
  · intro x y
    obtain ⟨a, rfl⟩ := h1.surjective x
    obtain ⟨b, rfl⟩ := h1.surjective y
    show φ (π1 a * π1 b) = φ (π1 a) * φ (π1 b)
    rw [← map_mul, hφ, hφ, hφ, map_mul]

section Main

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G]

/-- A discrete subgroup is separated from `1` by a symmetric compact neighbourhood `N` of `1` with
`N³ ∩ D = {1}`. -/
theorem exists_compact_symm_nhds_cube_inter (D : Subgroup G) [DiscreteTopology D] :
    ∃ N : Set G, IsCompact N ∧ N ∈ 𝓝 (1 : G) ∧ (∀ x ∈ N, x⁻¹ ∈ N) ∧
      ∀ a ∈ N, ∀ b ∈ N, ∀ c ∈ N, a * b * c ∈ D → a * b * c = 1 := by
  obtain ⟨O, hOo, hO⟩ := isOpen_induced_iff.1 (isOpen_discrete ({1} : Set D))
  have h1O : (1 : G) ∈ O := by
    have : (1 : D) ∈ ((↑) : D → G) ⁻¹' O := by rw [hO]; rfl
    exact this
  have hDO : ∀ d ∈ D, d ∈ O → d = 1 := by
    intro d hd hdO
    have : (⟨d, hd⟩ : D) ∈ ((↑) : D → G) ⁻¹' O := hdO
    rw [hO, Set.mem_singleton_iff] at this
    exact congrArg Subtype.val this
  obtain ⟨V, hV, hVO⟩ := exists_nhds_one_split (hOo.mem_nhds h1O)
  obtain ⟨V', hV', hV'V⟩ := exists_nhds_one_split hV
  have hX : V' ∩ V ∩ (V' ∩ V)⁻¹ ∈ 𝓝 (1 : G) :=
    Filter.inter_mem (Filter.inter_mem hV' hV) (inv_mem_nhds_one G (Filter.inter_mem hV' hV))
  obtain ⟨C0, hC0n, hC0X, hC0c⟩ := local_compact_nhds hX
  refine ⟨C0 ∩ C0⁻¹, hC0c.inter_right hC0c.inv.isClosed,
    Filter.inter_mem hC0n (inv_mem_nhds_one G hC0n), fun x hx => ⟨hx.2, by simpa using hx.1⟩, ?_⟩
  intro a ha b hb c hc habc
  have haX : a ∈ V' ∩ V := (hC0X ha.1).1
  have hbX : b ∈ V' ∩ V := (hC0X hb.1).1
  have hcX : c ∈ V := (hC0X hc.1).1.2
  have hab : a * b ∈ V := hV'V a haX.1 b hbX.1
  exact hDO _ habc (hVO _ hab c hcX)

/-- The common structure result: `K` compact, `D` discrete, `K ∩ D = 1`, the image of `D` in `G / K`
is discrete and the quotient of `G / K` by it is `Tⁿ × E`. -/
theorem exists_compact_subgroup_discrete_quotient_torus_prod_finite
    (V : Set G) (hV : IsCompact V) {m : ℕ} (g : Fin m → G)
    (hgen : ∀ y : G, ∃ v ∈ V, ∃ w ∈ Subgroup.closure (Set.range g), y = v * w) :
    ∃ (K D : Subgroup G), IsCompact (K : Set G) ∧ DiscreteTopology D ∧
      (∀ k ∈ K, k ∈ D → k = 1) ∧ DiscreteTopology (D.map (QuotientGroup.mk' K)) ∧
      IsTorusTimesFinite ((G ⧸ K) ⧸ D.map (QuotientGroup.mk' K)) := by
  classical
  -- (a) a discrete cocompact subgroup
  obtain ⟨D, hDdisc, C, hC, hcov⟩ : ∃ D : Subgroup G, DiscreteTopology D ∧
      ∃ C : Set G, IsCompact C ∧ ∀ y, ∃ c ∈ C, ∃ a ∈ D, y = c * a := by
    by_cases hx : ∃ x : G, x ≠ 1
    · obtain ⟨x, hx⟩ := hx
      obtain ⟨A, hA, -, C, hC, hcov⟩ := LCA.exists_discrete_cocompact m G V hV g hgen x hx
      exact ⟨A, hA, C, hC, hcov⟩
    · push Not at hx
      exact ⟨⊥, inferInstance, {1}, isCompact_singleton, fun y => ⟨1, rfl, 1, one_mem _, by
        rw [hx y]; simp⟩⟩
  haveI := hDdisc
  have hDclosed : IsClosed (D : Set G) := Subgroup.isClosed_of_discreteTopology
  haveI := hDclosed
  have hcompact : CompactSpace (G ⧸ D) := ⟨by
    have : (Set.univ : Set (G ⧸ D)) = QuotientGroup.mk '' C := by
      ext z
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
      simp only [mem_univ, true_iff]
      obtain ⟨c, hc, a, ha, rfl⟩ := hcov y
      exact ⟨c, hc, by rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff a).2 ha, mul_one]⟩
    rw [this]
    exact hC.image QuotientGroup.continuous_mk⟩
  haveI := hcompact
  -- (b) the neighbourhood N
  obtain ⟨N, hNc, hNn, hNsymm, hN3⟩ := exists_compact_symm_nhds_cube_inter D
  have h1N : (1 : G) ∈ N := mem_of_mem_nhds hNn
  have hopenmap : IsOpenMap (QuotientGroup.mk : G → G ⧸ D) := QuotientGroup.isOpenMap_coe
  have hfN : QuotientGroup.mk '' N ∈ 𝓝 (1 : G ⧸ D) := by
    have := hopenmap.image_mem_nhds hNn
    rwa [QuotientGroup.mk_one] at this
  obtain ⟨B, hBc, hBU, a, E, i1, i2, hE, hEd, ⟨T⟩⟩ :=
    exists_closedSubgroup_sub_nhds_quotient_continuousMulEquiv hfN
  -- K' and K
  let K' : Subgroup G := B.comap (QuotientGroup.mk' D)
  have hK'closed : IsClosed (K' : Set G) := hBc.preimage QuotientGroup.continuous_mk
  have hmemK' : ∀ x, x ∈ K' ↔ (QuotientGroup.mk x : G ⧸ D) ∈ B := fun x => Iff.rfl
  have hex : ∀ x ∈ K', ∃ z ∈ N, z ∈ K' ∧ z⁻¹ * x ∈ D := by
    intro x hx
    obtain ⟨z, hzN, hz⟩ := hBU ((hmemK' x).1 hx)
    refine ⟨z, hzN, (hmemK' z).2 (hz ▸ (hmemK' x).1 hx), ?_⟩
    exact (QuotientGroup.eq).1 hz
  let S : Set G := {x | x ∈ K' ∧ x ∈ N}
  have hSdiv : ∀ x ∈ S, ∀ y ∈ S, x * y⁻¹ ∈ S := by
    intro x hx y hy
    have hxy : x * y⁻¹ ∈ K' := K'.mul_mem hx.1 (K'.inv_mem hy.1)
    obtain ⟨z, hzN, hzK', hzD⟩ := hex _ hxy
    have h3 : z⁻¹ * x * y⁻¹ = 1 := by
      refine hN3 _ (hNsymm z hzN) x hx.2 _ (hNsymm y hy.2) ?_
      rw [mul_assoc]
      exact hzD
    have : x * y⁻¹ = z := by
      have := h3
      rw [mul_assoc, inv_mul_eq_one] at this
      exact this.symm
    exact ⟨hxy, this ▸ hzN⟩
  let K : Subgroup G := Subgroup.ofDiv S ⟨1, K'.one_mem, h1N⟩ hSdiv
  have hmemK : ∀ x, x ∈ K ↔ x ∈ K' ∧ x ∈ N := fun x => Iff.rfl
  have hKcompact : IsCompact (K : Set G) := by
    have : (K : Set G) = (K' : Set G) ∩ N := rfl
    rw [this]
    exact hNc.inter_left hK'closed
  have hKD : ∀ k ∈ K, k ∈ D → k = 1 := by
    intro k hk hkD
    have h := hN3 k ((hmemK k).1 hk).2 1 h1N 1 h1N (by simpa using hkD)
    simpa using h
  have hDK' : ∀ d ∈ D, d ∈ K' := fun d hd =>
    (hmemK' d).2 (by rw [(QuotientGroup.eq_one_iff d).2 hd]; exact B.one_mem)
  have hK'KD : ∀ x ∈ K', ∃ k ∈ K, ∃ d ∈ D, x = k * d := by
    intro x hx
    obtain ⟨z, hzN, hzK', hzD⟩ := hex x hx
    exact ⟨z, (hmemK z).2 ⟨hzK', hzN⟩, z⁻¹ * x, hzD, by simp⟩
  -- (c) the discrete image of D in G / K
  have hDisc : DiscreteTopology (D.map (QuotientGroup.mk' K)) := by
    apply discreteTopology_of_isOpen_singleton_one
    have hO' : IsOpen ((QuotientGroup.mk : G → G ⧸ K) '' interior N) :=
      QuotientGroup.isOpenMap_coe _ isOpen_interior
    refine isOpen_induced_iff.2 ⟨_, hO', ?_⟩
    ext ⟨q, hq⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨w, hw, hwq⟩
      obtain ⟨d, hd, hdq⟩ := Subgroup.mem_map.1 hq
      have h1 : w⁻¹ * d ∈ K := QuotientGroup.eq.1 (hwq.trans hdq.symm)
      have h2 := (hmemK _).1 h1
      have hd1 : d = 1 := by
        have := hN3 w (interior_subset hw) (w⁻¹ * d) h2.2 1 h1N (by simpa using hd)
        simpa using this
      refine Subtype.ext ?_
      show q = 1
      rw [← hdq, hd1]
      exact map_one _
    · intro h
      have : q = 1 := congrArg Subtype.val h
      rw [this]
      exact ⟨1, mem_interior_iff_mem_nhds.2 hNn, QuotientGroup.mk_one K⟩
  refine ⟨K, D, hKcompact, hDdisc, hKD, hDisc, ?_⟩
  let D' : Subgroup (G ⧸ K) := D.map (QuotientGroup.mk' K)
  let π1 : G →* (G ⧸ K) ⧸ D' := (QuotientGroup.mk' D').comp (QuotientGroup.mk' K)
  let π2 : G →* (G ⧸ D) ⧸ B := (QuotientGroup.mk' B).comp (QuotientGroup.mk' D)
  have hq1 : IsQuotientMap π1 :=
    (QuotientGroup.isQuotientMap_mk D').comp (QuotientGroup.isQuotientMap_mk K)
  have hq2 : IsQuotientMap π2 :=
    (QuotientGroup.isQuotientMap_mk B).comp (QuotientGroup.isQuotientMap_mk D)
  have hker : π1.ker = π2.ker := by
    ext x
    have e2 : x ∈ π2.ker ↔ x ∈ K' := by
      show (QuotientGroup.mk (QuotientGroup.mk x : G ⧸ D) : (G ⧸ D) ⧸ B) = 1 ↔ _
      rw [QuotientGroup.eq_one_iff]
      exact Iff.rfl
    have e1 : x ∈ π1.ker ↔ x ∈ K' := by
      show (QuotientGroup.mk (QuotientGroup.mk x : G ⧸ K) : (G ⧸ K) ⧸ D') = 1 ↔ _
      rw [QuotientGroup.eq_one_iff]
      constructor
      · intro h
        obtain ⟨d, hd, hdx⟩ := Subgroup.mem_map.1 h
        have hk : d⁻¹ * x ∈ K := QuotientGroup.eq.1 hdx
        have hx : x = d * (d⁻¹ * x) := by simp
        rw [hx]
        exact K'.mul_mem (hDK' d hd) ((hmemK _).1 hk).1
      · intro hx
        obtain ⟨k, hk, d, hd, rfl⟩ := hK'KD x hx
        refine Subgroup.mem_map.2 ⟨d, hd, ?_⟩
        show (QuotientGroup.mk d : G ⧸ K) = QuotientGroup.mk (k * d)
        rw [QuotientGroup.eq, mul_comm k d, ← mul_assoc, inv_mul_cancel, one_mul]
        exact hk
    rw [e1, e2]
  obtain ⟨e⟩ := exists_continuousMulEquiv_of_isQuotientMap_of_ker_eq π1 π2 hq1 hq2 hker
  exact ⟨a, E, i1, i2, hE, hEd, ⟨e.trans T⟩⟩

end Main

end UndergradKB.Topology
