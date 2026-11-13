import UndergradKB.Topology.ClosedSubgroupsRn
import UndergradKB.Topology.GroupsMore
import UndergradKB.Topology.GroupsMore2
import UndergradKB.Topology.GroupsExtra
import UndergradKB.Common.Attr

/-!
# Wave 2: groups locally isomorphic to `ℝⁿ` (Morris, Appendix 5.5, Theorem A5.5.25)

* the quotient of a finite-dimensional real vector space `E` by a discrete subgroup of rank `q` is
  `ℝ^(dim E - q) × T^q` (the dimension count is the new information);
* a Hausdorff abelian group locally isomorphic to `ℝⁿ` is `ℝ^a × T^b × D` with `a + b = n`.
-/

open Set Filter
open scoped Topology

namespace UndergradKB.Topology

open ClosedSubgroupsRn

section Quotient

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Morris, Topology Without Tears, Theorem A5.5.13 (TP-547), discrete case with dimension count. If
`L` is a discrete subgroup of a finite-dimensional real normed space `E`, of rank `q`, then `E ⧸ L` is
topologically isomorphic to `ℝ^c × T^q` with `c + q = dim E`. -/
theorem quotient_discrete_subgroup_equiv (L : AddSubgroup E) [DiscreteTopology L] :
    ∃ c q : ℕ, c + q = Module.finrank ℝ E ∧
      Nonempty ((E ⧸ L) ≃ₜ+ ((Fin c → ℝ) × (Fin q → AddCircle (1 : ℝ)))) := by
  classical
  obtain ⟨q, b, hb, hLmem⟩ := exists_lattice_basis L
  let B := Module.Basis.sumExtend hb
  have hB : ∀ j, B (Sum.inl j) = b j := fun j => by
    simp only [B, Module.Basis.sumExtend, Module.Basis.reindex_apply, Equiv.symm_symm,
      Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.Set.sumDiffSubset_apply_inl,
      Equiv.ofInjective_apply, Module.Basis.coe_extend]
    rfl
  have hfin : Finite (Fin q ⊕ Module.Basis.sumExtendIndex hb) := Module.Finite.finite_basis B
  have hfinS : Finite (Module.Basis.sumExtendIndex hb) :=
    Finite.of_injective (Sum.inr : _ → Fin q ⊕ Module.Basis.sumExtendIndex hb) Sum.inr_injective
  let _ := Fintype.ofFinite (Module.Basis.sumExtendIndex hb)
  let e : ((Fin 0 ⊕ Fin q) ⊕ Module.Basis.sumExtendIndex hb) ≃ (Fin q ⊕ Module.Basis.sumExtendIndex hb) :=
    Equiv.sumCongr (Equiv.emptySum (Fin 0) (Fin q)) (Equiv.refl _)
  let B0 := B.reindex e.symm
  have hB0 : ∀ j, B0 (Sum.inl (Sum.inr j)) = b j := fun j => by
    simp only [B0, Module.Basis.reindex_apply, Equiv.symm_symm]
    have : e (Sum.inl (Sum.inr j)) = Sum.inl j := rfl
    rw [this]
    exact hB j
  let φ : E →+ (Module.Basis.sumExtendIndex hb → ℝ) × (Fin q → AddCircle (1 : ℝ)) :=
    (modelMap (Fin 0) (Fin q) (Module.Basis.sumExtendIndex hb)).comp
      B0.equivFun.toLinearMap.toAddMonoidHom
  have hrep : ∀ m k, B0.repr (B0 m) k = if m = k then 1 else 0 := by
    intro m k
    simp [Module.Basis.repr_self, Finsupp.single_apply]
  have hker : ∀ x, x ∈ L ↔ φ x = 0 := by
    intro x
    change x ∈ L ↔ modelMap (Fin 0) (Fin q) _ (B0.equivFun x) = 0
    rw [modelMap_eq_zero_iff]
    simp only [Module.Basis.equivFun_apply]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := (hLmem x).1 hx
      have hls : x = ∑ j, n j • B0 (Sum.inl (Sum.inr j)) := by simp only [hB0]; exact hn
      refine ⟨fun s => ?_, fun j => ⟨n j, ?_⟩⟩
      · rw [hls]
        simp [map_sum, hrep]
      · rw [hls]
        simp [map_sum, Finsupp.single_apply]
    · rintro ⟨h1, h2⟩
      choose n hn using h2
      have hx := B0.sum_repr x
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at hx
      have h3 : ∑ s, B0.repr x (Sum.inr s) • B0 (Sum.inr s) = 0 := by simp [h1]
      rw [h3, add_zero] at hx
      rw [hLmem]
      refine ⟨n, ?_⟩
      rw [← hx]
      simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hn j, Int.cast_smul_eq_zsmul, hB0]
  have hcont : Continuous φ :=
    (continuous_modelMap _ _ _).comp (LinearMap.continuous_of_finiteDimensional _)
  have hopen : IsOpenMap φ :=
    (isOpenMap_modelMap _ _ _).comp (LinearMap.isOpenMap_of_finiteDimensional _ B0.equivFun.surjective)
  have hsurj : Function.Surjective φ := (surjective_modelMap _ _ _).comp B0.equivFun.surjective
  obtain ⟨Φ⟩ := quotient_equiv L φ hcont hopen hsurj hker
  let c := Fintype.card (Module.Basis.sumExtendIndex hb)
  let eS : (Module.Basis.sumExtendIndex hb → ℝ) ≃ₗ[ℝ] (Fin c → ℝ) :=
    LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin (Module.Basis.sumExtendIndex hb)).symm
  let Ψ : (Module.Basis.sumExtendIndex hb → ℝ) ≃ₜ+ (Fin c → ℝ) :=
    mkCAE eS.toAddEquiv (LinearMap.continuous_of_finiteDimensional eS.toLinearMap)
      (LinearMap.continuous_of_finiteDimensional eS.symm.toLinearMap)
  refine ⟨c, q, ?_, ⟨Φ.trans (prodCAE Ψ (ContinuousAddEquiv.refl _))⟩⟩
  rw [Module.finrank_eq_card_basis B0]
  simp [c, Fintype.card_sum, add_comm]

end Quotient

/-! ### Local isomorphism with `ℝⁿ` -/

section LocalIso

/-- Additive form of Morris, Definition A5.5.21 (TP-551): `H` is locally isomorphic to `G` if there are
neighbourhoods `V` of `0` in `G`, `U` of `0` in `H` and a homeomorphism `V ≃ U` that is additive whenever
`x`, `y`, `x + y` all lie in `V`. -/
def AddLocallyIsomorphic (G H : Type*) [AddGroup G] [TopologicalSpace G] [AddGroup H]
    [TopologicalSpace H] : Prop :=
  ∃ (V : Set G) (U : Set H) (f : V ≃ₜ U), V ∈ 𝓝 (0 : G) ∧ U ∈ 𝓝 (0 : H) ∧
    ∀ (x y : V) (hxy : (x : G) + y ∈ V), ((f ⟨x + y, hxy⟩ : U) : H) = (f x : H) + (f y : H)

/-- The additive notion agrees with `LocallyIsomorphic` on the multiplicative copies. -/
theorem addLocallyIsomorphic_iff (G H : Type*) [AddGroup G] [TopologicalSpace G] [AddGroup H]
    [TopologicalSpace H] :
    LocallyIsomorphic (Multiplicative G) (Multiplicative H) ↔ AddLocallyIsomorphic G H :=
  Iff.rfl

variable {n : ℕ} {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]

/-- A group locally isomorphic to `ℝⁿ` receives a continuous open homomorphism from `ℝⁿ` with discrete
kernel (the extension of the local isomorphism, Lemma A5.5.24). -/
theorem exists_open_hom_of_addLocallyIsomorphic (h : AddLocallyIsomorphic (Fin n → ℝ) G) :
    ∃ φ : (Fin n → ℝ) →+ G, Continuous φ ∧ IsOpenMap φ ∧ DiscreteTopology φ.ker := by
  classical
  obtain ⟨V, U, f, hV, hU, hadd⟩ := h
  have h0V : (0 : Fin n → ℝ) ∈ V := mem_of_mem_nhds hV
  have hf0 : ((f ⟨0, h0V⟩ : U) : G) = 0 := by
    have := hadd ⟨0, h0V⟩ ⟨0, h0V⟩ (by simpa using h0V)
    have h2 : (⟨(0 : Fin n → ℝ) + 0, by simpa using h0V⟩ : V) = ⟨0, h0V⟩ := Subtype.ext (by simp)
    rw [h2] at this
    simpa using this
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.1 hV
  let f' : (Fin n → ℝ) → G := fun x => if hx : x ∈ V then ((f ⟨x, hx⟩ : U) : G) else 0
  have hf'V : ∀ x (hx : x ∈ V), f' x = ((f ⟨x, hx⟩ : U) : G) := fun x hx => dif_pos hx
  have hloc : IsLocalAddHom r f' := by
    intro x hx y hy hxy
    rw [hf'V x (hrV hx), hf'V y (hrV hy), hf'V (x + y) (hrV hxy)]
    exact hadd ⟨x, hrV hx⟩ ⟨y, hrV hy⟩ (hrV hxy)
  have hcont : ContinuousOn f' (Metric.ball (0 : Fin n → ℝ) r) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : (Metric.ball (0 : Fin n → ℝ) r).domRestrict f' =
        fun x : Metric.ball (0 : Fin n → ℝ) r => ((f ⟨(x : Fin n → ℝ), hrV x.2⟩ : U) : G) :=
      funext fun x => hf'V _ _
    rw [this]
    exact continuous_subtype_val.comp
      (f.continuous.comp (Continuous.subtype_mk continuous_subtype_val _))
  obtain ⟨φ, hφc, hφ⟩ := hloc.exists_extension hr hcont
  -- images of neighbourhoods of `0` are neighbourhoods of `0`
  have hnhd : ∀ N ∈ 𝓝 (0 : Fin n → ℝ), φ '' N ∈ 𝓝 (0 : G) := by
    intro N hN
    let N' : Set (Fin n → ℝ) := interior N ∩ Metric.ball 0 r
    have hN'o : IsOpen N' := isOpen_interior.inter Metric.isOpen_ball
    have hN'V : N' ⊆ V := fun x hx => hrV hx.2
    have hT : IsOpen ((Subtype.val : V → Fin n → ℝ) ⁻¹' N') := hN'o.preimage continuous_subtype_val
    obtain ⟨O, hOo, hO⟩ := isOpen_induced_iff.1 (f.isOpenMap _ hT)
    have h0N' : (0 : Fin n → ℝ) ∈ N' := ⟨mem_interior_iff_mem_nhds.2 hN, Metric.mem_ball_self hr⟩
    have h0O : (0 : G) ∈ O := by
      have : f ⟨0, h0V⟩ ∈ f '' ((Subtype.val : V → Fin n → ℝ) ⁻¹' N') := ⟨⟨0, h0V⟩, h0N', rfl⟩
      rw [← hO] at this
      simpa [hf0] using this
    refine Filter.mem_of_superset (inter_mem (hOo.mem_nhds h0O) hU) ?_
    rintro y ⟨hyO, hyU⟩
    have : (⟨y, hyU⟩ : U) ∈ Subtype.val ⁻¹' O := hyO
    rw [hO] at this
    obtain ⟨t, ht, hty⟩ := this
    refine ⟨t.1, interior_subset ht.1, ?_⟩
    rw [hφ t.1 ht.2, hf'V t.1 t.2]
    exact congrArg Subtype.val hty
  have hopen : IsOpenMap φ := by
    intro S hS
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨x, hxS, rfl⟩
    have h1 : ((fun z => x + z) ⁻¹' S) ∈ 𝓝 (0 : Fin n → ℝ) :=
      (hS.preimage (continuous_const.add continuous_id)).mem_nhds (by simpa using hxS)
    have h2 := hnhd _ h1
    have h3 : (fun z => φ x + z) '' (φ '' ((fun z => x + z) ⁻¹' S)) ∈ 𝓝 (φ x) := by
      have e : 𝓝 (φ x) = Filter.map (fun z => φ x + z) (𝓝 (0 : G)) := by
        simpa using ((Homeomorph.addLeft (φ x)).map_nhds_eq (0 : G)).symm
      rw [e]
      exact Filter.image_mem_map h2
    refine Filter.mem_of_superset h3 ?_
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨x + z, hz, by simp⟩
  refine ⟨φ, hφc, hopen, ?_⟩
  refine discreteTopology_of_isOpen_singleton_zero ?_
  have : ({0} : Set φ.ker) = Subtype.val ⁻¹' Metric.ball (0 : Fin n → ℝ) r := by
    ext ⟨x, hx⟩
    constructor
    · intro hmem
      have h0 : (⟨x, hx⟩ : φ.ker) = 0 := hmem
      have hx0 : x = 0 := congrArg Subtype.val h0
      show x ∈ Metric.ball (0 : Fin n → ℝ) r
      rw [hx0]
      exact Metric.mem_ball_self hr
    · intro hxb
      have hxb' : x ∈ Metric.ball (0 : Fin n → ℝ) r := hxb
      have hker : φ x = 0 := hx
      rw [hφ x hxb', hf'V x (hrV hxb')] at hker
      have : f ⟨x, hrV hxb'⟩ = f ⟨0, h0V⟩ := Subtype.ext (by rw [hker, hf0])
      have h5 := congrArg Subtype.val (f.injective this)
      show (⟨x, hx⟩ : φ.ker) = 0
      exact Subtype.ext h5
  rw [this]
  exact Metric.isOpen_ball.preimage continuous_subtype_val

end LocalIso

/-! ### Theorem A5.5.25 and Corollary A5.5.26 -/

section Structure

universe u

variable {n : ℕ} {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]

/-- Morris, Topology Without Tears, Theorem A5.5.25 (TP-554). A Hausdorff abelian topological group `G`
locally isomorphic to `ℝⁿ` is topologically isomorphic to `ℝ^a × T^b × D` with `D` discrete and
`a + b = n`. (`T = ℝ/ℤ`; Hausdorffness is not needed in this argument.) -/
@[kb "morris2024" "Theorem A5.5.25, p. 549"]
theorem exists_equiv_real_circle_discrete_of_addLocallyIsomorphic [T2Space G]
    (h : AddLocallyIsomorphic (Fin n → ℝ) G) :
    ∃ (a b : ℕ) (D : Type u) (_ : AddCommGroup D) (_ : TopologicalSpace D),
      DiscreteTopology D ∧ a + b = n ∧
        Nonempty (G ≃ₜ+ (((Fin a → ℝ) × (Fin b → AddCircle (1 : ℝ))) × D)) := by
  classical
  obtain ⟨φ, hφc, hφo, hK⟩ := exists_open_hom_of_addLocallyIsomorphic h
  obtain ⟨c, q, hcq, ⟨e2⟩⟩ := quotient_discrete_subgroup_equiv φ.ker
  rw [Module.finrank_fin_fun] at hcq
  let H : AddSubgroup G := φ.range
  have hHo : IsOpen (H : Set G) := by
    have := hφo.isOpen_range
    rwa [← AddMonoidHom.coe_range] at this
  let φ' : (Fin n → ℝ) →+ H := φ.rangeRestrict
  have hφ'c : Continuous φ' := Continuous.subtype_mk hφc _
  have hφ'o : IsOpenMap φ' := by
    intro S hS
    rw [isOpen_induced_iff]
    refine ⟨φ '' S, hφo S hS, ?_⟩
    ext ⟨y, hy⟩
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, Subtype.ext hxy⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, congrArg Subtype.val hxy⟩
  obtain ⟨e1⟩ := ClosedSubgroupsRn.quotient_equiv φ.ker φ' hφ'c hφ'o
    (fun y => by
      obtain ⟨x, hx⟩ := y.2
      exact ⟨x, Subtype.ext hx⟩)
    (fun x => by
      rw [AddMonoidHom.mem_ker]
      exact ⟨fun h0 => Subtype.ext h0, fun h0 => congrArg Subtype.val h0⟩)
  have hdiv : IsDivisibleGroup H := by
    intro m hm y
    obtain ⟨x, hx⟩ := y.2
    refine ⟨φ' (((m : ℝ)⁻¹) • x), Subtype.ext ?_⟩
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    show m • φ (((m : ℝ)⁻¹) • x) = (y : G)
    rw [← map_nsmul, ← hx, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hm', one_smul]
  obtain ⟨e3, -⟩ := exists_continuousAddEquiv_prod_quotient H hHo hdiv
  have : DiscreteTopology (G ⧸ H) := QuotientAddGroup.discreteTopology hHo
  refine ⟨c, q, G ⧸ H, inferInstance, inferInstance, this, hcq, ⟨e3.trans ?_⟩⟩
  exact prodCAE (e1.symm.trans e2) (ContinuousAddEquiv.refl _)

/-- Morris, Topology Without Tears, Corollary A5.5.26 (TP-554). A connected Hausdorff abelian group
locally isomorphic to `ℝⁿ` is topologically isomorphic to `ℝ^a × T^b` with `a + b = n`. -/
@[kb "morris2024" "Corollary A5.5.26, p. 549"]
theorem exists_equiv_real_circle_of_addLocallyIsomorphic [T2Space G] [ConnectedSpace G]
    (h : AddLocallyIsomorphic (Fin n → ℝ) G) :
    ∃ a b : ℕ, a + b = n ∧ Nonempty (G ≃ₜ+ ((Fin a → ℝ) × (Fin b → AddCircle (1 : ℝ)))) := by
  classical
  obtain ⟨φ, hφc, hφo, hK⟩ := exists_open_hom_of_addLocallyIsomorphic h
  obtain ⟨c, q, hcq, ⟨e2⟩⟩ := quotient_discrete_subgroup_equiv φ.ker
  rw [Module.finrank_fin_fun] at hcq
  have hHo : IsOpen (φ.range : Set G) := by
    have := hφo.isOpen_range
    rwa [← AddMonoidHom.coe_range] at this
  have hHc : IsClosed (φ.range : Set G) := AddSubgroup.isClosed_of_isOpen _ hHo
  have huniv : (φ.range : Set G) = Set.univ :=
    IsClopen.eq_univ ⟨hHc, hHo⟩ ⟨0, φ.range.zero_mem⟩
  obtain ⟨e1⟩ := ClosedSubgroupsRn.quotient_equiv φ.ker φ hφc hφo
    (fun y => by
      have : y ∈ (φ.range : Set G) := by rw [huniv]; trivial
      exact this)
    (fun x => AddMonoidHom.mem_ker)
  exact ⟨c, q, hcq, ⟨e1.symm.trans e2⟩⟩

end Structure

end UndergradKB.Topology
