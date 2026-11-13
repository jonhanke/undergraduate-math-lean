import UndergradKB.Topology.DualityCompact
import UndergradKB.Topology.DualityDiscrete2
import UndergradKB.Topology.DualityDiscrete
import UndergradKB.Topology.Characters
import UndergradKB.Topology.ClassicalDuals
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Analysis.Complex.Polynomial.Basic
import UndergradKB.Common.Attr

/-!
# Duality for compact abelian groups, consequences (Morris, Appendix 5, A5.11 to A5.15)

Using that the characters of a compact Hausdorff abelian group separate points
(`DualityCompact.lean`):

* Theorem A5.11.2 / A5.0.16: Pontryagin-van Kampen duality for compact groups;
* Corollaries A5.11.4, A5.11.5 and (compact case) A5.14.4: extension of characters;
* Theorem A5.12.4: monothetic compact groups;
* Corollaries A5.15.11, A5.15.12, A5.15.15: torsion of the dual and the identity component.
-/

open Topology Set Filter Real

set_option linter.unusedSectionVars false

universe u

namespace UndergradKB.Topology

/-! ### Duality for compact groups -/

section Duality

variable {K : Type u} [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [T2Space K]

theorem toDualDual_injective_compact : Function.Injective (toDualDual K) := by
  intro x y h
  by_contra hne
  obtain ⟨χ, hχ⟩ := characters_separate_points_of_compact hne
  exact hχ (DFunLike.congr_fun h χ)

theorem toDualDual_surjective_compact : Function.Surjective (toDualDual K) := by
  let S : Subgroup (PontryaginDual (PontryaginDual K)) := (toDualDual K).toMonoidHom.range
  have hdense : Dense (S : Set (PontryaginDual (PontryaginDual K))) := by
    refine dense_of_separatesPoints_discrete (D := PontryaginDual K) S fun χ χ' hne => ?_
    obtain ⟨x, hx⟩ : ∃ x, χ x ≠ χ' x := by
      by_contra h
      push Not at h
      exact hne (PontryaginDual.ext h)
    exact ⟨toDualDual K x, ⟨x, rfl⟩, hx⟩
  have hcomp : IsCompact (S : Set (PontryaginDual (PontryaginDual K))) := by
    have : (S : Set (PontryaginDual (PontryaginDual K))) = Set.range (toDualDual K) := by
      ext z
      simp [S]
    rw [this]
    exact isCompact_range (toDualDual K).continuous
  intro z
  have hz : z ∈ closure (S : Set (PontryaginDual (PontryaginDual K))) := by
    rw [hdense.closure_eq]
    trivial
  rw [hcomp.isClosed.closure_eq] at hz
  obtain ⟨x, hx⟩ := hz
  exact ⟨x, hx⟩

/-- Morris, Topology Without Tears, Theorem A5.11.2 (TP-585). Pontryagin-van Kampen duality for
compact Hausdorff abelian groups: the canonical map `α : K → K^**`, `α g χ = χ g`, is an isomorphism
of topological groups. -/
@[kb "morris2024" "Theorem A5.11.2, p. 576"]
theorem exists_continuousMulEquiv_dualDual_of_compact :
    ∃ e : K ≃ₜ* PontryaginDual (PontryaginDual K), ∀ g χ, e g χ = χ g := by
  have hbij : Function.Bijective (toDualDual K).toMonoidHom :=
    ⟨toDualDual_injective_compact, toDualDual_surjective_compact⟩
  let e0 : K ≃* PontryaginDual (PontryaginDual K) := MulEquiv.ofBijective _ hbij
  have hcont : Continuous e0 := (toDualDual K).continuous
  let h : K ≃ₜ PontryaginDual (PontryaginDual K) := hcont.homeoOfEquivCompactToT2
  exact ⟨{ toMulEquiv := e0
           continuous_toFun := hcont
           continuous_invFun := h.symm.continuous }, fun g χ => rfl⟩

/-- Morris, Topology Without Tears, Theorem A5.0.16 (TP-490). Duality for compact abelian groups, in
the form of the duality property `DualityHolds`. -/
@[kb "morris2024" "Theorem A5.0.16, p. 504"]
theorem dualityHolds_of_compact : DualityHolds K :=
  exists_continuousMulEquiv_dualDual_of_compact

end Duality

/-! ### Extension of characters -/

section Extension

variable {A B : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] [CompactSpace A]
  [T2Space A] [CommGroup B] [TopologicalSpace B]

/-- Morris, Topology Without Tears, Corollary A5.11.5 (TP-588). Let `f` be a continuous one-one
homomorphism of a compact group `A` into an abelian topological group `B` whose characters separate
points.  Then `f* : B* → A*` is onto and a quotient map (onto the discrete group `A*`). -/
@[kb "morris2024" "Corollary A5.11.5, p. 576"]
theorem PontryaginDual_map_surjective_isQuotientMap_of_injective_compact (f : A →ₜ* B)
    (hf : Function.Injective f)
    (hsep : ∀ x y : B, x ≠ y → ∃ χ : PontryaginDual B, χ x ≠ χ y) :
    Function.Surjective (PontryaginDual.map f) ∧ IsQuotientMap (PontryaginDual.map f) := by
  let S : Subgroup (PontryaginDual A) := (PontryaginDual.map f).toMonoidHom.range
  have hS : S = ⊤ := by
    refine subgroup_dual_eq_top_of_separatesPoints S fun x y hxy => ?_
    obtain ⟨χ, hχ⟩ := hsep (f x) (f y) (hf.ne hxy)
    exact ⟨PontryaginDual.map f χ, ⟨χ, rfl⟩, hχ⟩
  have hsurj : Function.Surjective (PontryaginDual.map f) := by
    intro ψ
    have : ψ ∈ S := by rw [hS]; trivial
    obtain ⟨χ, hχ⟩ := this
    exact ⟨χ, hχ⟩
  refine ⟨hsurj, ⟨?_⟩, hsurj⟩
  have h1 : instTopologicalSpacePontryaginDual A = ⊥ := DiscreteTopology.eq_bot
  exact le_antisymm (h1.le.trans bot_le)
    (continuous_iff_coinduced_le.1 (map_continuous (PontryaginDual.map f)))

/-- Morris, Topology Without Tears, Corollary A5.11.4 (TP-587). Let `B` be a Hausdorff abelian
topological group whose characters separate points (an LCA-group with enough characters) and `K` a
compact subgroup.  Then every character of `K` extends to a character of `B`. -/
@[kb "morris2024" "Corollary A5.11.4, p. 576"]
theorem exists_extend_char_of_compact_subgroup {B : Type*} [CommGroup B] [TopologicalSpace B]
    [IsTopologicalGroup B] [T2Space B]
    (hsep : ∀ x y : B, x ≠ y → ∃ χ : PontryaginDual B, χ x ≠ χ y)
    (K : Subgroup B) (hK : IsCompact (K : Set B)) (ψ : PontryaginDual K) :
    ∃ χ : PontryaginDual B, ∀ k : K, χ k = ψ k := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let i : K →ₜ* B := ⟨K.subtype, continuous_subtype_val⟩
  obtain ⟨hsurj, -⟩ := PontryaginDual_map_surjective_isQuotientMap_of_injective_compact i
    K.subtype_injective hsep
  obtain ⟨χ, hχ⟩ := hsurj ψ
  exact ⟨χ, fun k => DFunLike.congr_fun hχ k⟩

/-- Morris, Topology Without Tears, Corollary A5.14.4 (TP-620), for compact Hausdorff abelian groups
(which have enough characters): every character of a closed subgroup extends to the group. -/
@[kb "morris2024" "Corollary A5.14.4, p. 603"]
theorem exists_extend_char_closedSubgroup_of_compact {B : Type u} [CommGroup B]
    [TopologicalSpace B] [IsTopologicalGroup B] [CompactSpace B] [T2Space B]
    (H : Subgroup B) (hH : IsClosed (H : Set B)) (ψ : PontryaginDual H) :
    ∃ χ : PontryaginDual B, ∀ k : H, χ k = ψ k :=
  exists_extend_char_of_compact_subgroup (fun _ _ hxy => characters_separate_points_of_compact hxy)
    H hH.isCompact ψ

end Extension

/-! ### Monothetic compact groups -/

section Monothetic

variable {K : Type u} [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [T2Space K]

/-- Morris, Topology Without Tears, Theorem A5.12.4 (TP-597). A compact Hausdorff abelian group is
monothetic iff its dual group embeds algebraically in the circle (that is, in the discrete circle
group). -/
@[kb "morris2024" "Theorem A5.12.4, p. 583"]
theorem isMonothetic_iff_exists_injective_dual_circle :
    IsMonothetic K ↔ ∃ φ : PontryaginDual K →* Circle, Function.Injective φ := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨{ toFun := fun χ => χ g
              map_one' := rfl
              map_mul' := fun _ _ => rfl }, fun χ χ' h => ?_⟩
    have h' : χ g = χ' g := h
    refine PontryaginDual.ext fun x => ?_
    have : (χ : K → Circle) = χ' := by
      refine Continuous.ext_on hg χ.continuous χ'.continuous fun y hy => ?_
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      rw [map_zpow, map_zpow, h']
    exact congrFun this x
  · rintro ⟨φ, hφ⟩
    let ψ : PontryaginDual (PontryaginDual K) := ⟨φ, continuous_of_discreteTopology⟩
    obtain ⟨g, hg⟩ := toDualDual_surjective_compact ψ
    have hgφ : ∀ χ : PontryaginDual K, χ g = φ χ := fun χ => DFunLike.congr_fun hg χ
    refine ⟨g, ?_⟩
    let H := Subgroup.zpowers g
    have hall : ∀ x : K, x ∈ H.topologicalClosure := by
      intro x
      by_contra hx
      obtain ⟨χ, hχH, hχx⟩ := exists_char_trivial_on_ne H.topologicalClosure
        H.isClosed_topologicalClosure hx
      have h1 : χ g = 1 := hχH g (H.le_topologicalClosure (Subgroup.mem_zpowers g))
      have h2 : φ χ = φ 1 := by rw [← hgφ, h1, map_one]
      exact hχx (by rw [hφ h2]; rfl)
    rw [dense_iff_closure_eq]
    ext x
    simp only [mem_univ, iff_true]
    have := hall x
    rwa [← SetLike.mem_coe, Subgroup.topologicalClosure_coe] at this

end Monothetic

/-! ### Torsion of the dual and the identity component -/

section Components

variable {K : Type u} [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [T2Space K]

theorem exists_isClopen_subset_of_connectedComponent_one {W : Set K} (hW : IsOpen W)
    (h : connectedComponent (1 : K) ⊆ W) : ∃ s : Set K, IsClopen s ∧ (1 : K) ∈ s ∧ s ⊆ W := by
  let N := { s : Set K // IsClopen s ∧ (1 : K) ∈ s }
  haveI : Nonempty N := ⟨⟨univ, isClopen_univ, mem_univ 1⟩⟩
  have hdir : Directed (· ⊇ ·) fun s : N => s.val := by
    rintro ⟨s, hs, hxs⟩ ⟨t, ht, hxt⟩
    exact ⟨⟨s ∩ t, hs.inter ht, ⟨hxs, hxt⟩⟩, inter_subset_left, inter_subset_right⟩
  have hU : W ∈ 𝓝ˢ (⋂ s : N, s.val) := by
    rw [← connectedComponent_eq_iInter_isClopen]
    exact hW.mem_nhdsSet.2 h
  obtain ⟨⟨s, hs, hs1⟩, hsW⟩ := exists_subset_nhds_of_compactSpace hdir (fun s => s.2.1.1) hU
  exact ⟨s, hs, hs1, hsW⟩

theorem dual_pow_apply' (χ : PontryaginDual K) (n : ℕ) (x : K) : (χ ^ n) x = χ x ^ n :=
  ContinuousMonoidHom.pow_apply (E := Circle) χ n x

theorem exists_char_trivial_on_connectedComponent_ne {x : K} (hx : x ∉ connectedComponent (1 : K)) :
    ∃ χ : PontryaginDual K, (∀ y ∈ connectedComponent (1 : K), χ y = 1) ∧ χ x ≠ 1 := by
  have hc : IsClosed ((Subgroup.connectedComponentOfOne K : Subgroup K) : Set K) :=
    isClosed_connectedComponent
  exact exists_char_trivial_on_ne (Subgroup.connectedComponentOfOne K) hc hx

/-- A character of finite order is trivial on the identity component. -/
theorem char_trivial_on_connectedComponent_of_isOfFinOrder {χ : PontryaginDual K}
    (hχ : IsOfFinOrder χ) {x : K} (hx : x ∈ connectedComponent (1 : K)) : χ x = 1 := by
  obtain ⟨n, hn, hn1⟩ := isOfFinOrder_iff_pow_eq_one.1 hχ
  let T : Set Circle := {z | z ^ n = 1}
  have hfin : T.Finite := by
    have hsub : T ⊆ (fun z : Circle => (z : ℂ)) ⁻¹'
        (Polynomial.nthRootsFinset n (1 : ℂ) : Set ℂ) := by
      intro z hz
      have hz' : z ^ n = 1 := hz
      show (z : ℂ) ∈ (Polynomial.nthRootsFinset n (1 : ℂ) : Set ℂ)
      rw [Finset.mem_coe, Polynomial.mem_nthRootsFinset hn, ← Circle.coe_pow, hz']
      rfl
    exact (Set.Finite.preimage (fun a _ b _ h => Subtype.ext h) (Finset.finite_toSet _)).subset hsub
  haveI : Finite T := hfin.to_subtype
  have hmaps : MapsTo (χ : K → Circle) (connectedComponent (1 : K)) T := by
    intro y _
    show (χ y) ^ n = 1
    have e : (χ ^ n) y = 1 := congrArg (fun ψ : PontryaginDual K => ψ y) hn1
    exact (dual_pow_apply' χ n y).symm.trans e
  have := isPreconnected_connectedComponent.constant_of_mapsTo
    (isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology T))
    (f := (χ : K → Circle)) χ.continuous.continuousOn hmaps hx mem_connectedComponent
  rw [this]
  exact map_one χ

/-- A character trivial on the identity component has finite order. -/
theorem isOfFinOrder_of_trivial_on_connectedComponent {χ : PontryaginDual K}
    (hχ : ∀ x ∈ connectedComponent (1 : K), χ x = 1) : IsOfFinOrder χ := by
  have hopen : IsOpen ((χ : K → Circle) ⁻¹' Circle.centeredArc (π / 2)) :=
    (Circle.isOpen_centeredArc _).preimage χ.continuous
  have hsub : connectedComponent (1 : K) ⊆ (χ : K → Circle) ⁻¹' Circle.centeredArc (π / 2) := by
    intro x hx
    show χ x ∈ Circle.centeredArc (π / 2)
    rw [hχ x hx, Circle.mem_centeredArc (by linarith [Real.pi_pos])]
    simpa using by positivity
  obtain ⟨s, hs, hs1, hsW⟩ := exists_isClopen_subset_of_connectedComponent_one hopen hsub
  obtain ⟨H, hH⟩ := IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one hs hs1
  have hker : ∀ h ∈ H.toSubgroup, χ h = 1 := by
    intro h hh
    refine Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two fun n _ => ?_
    rw [← map_pow]
    exact hsW (hH (H.toSubgroup.pow_mem hh n))
  haveI : Subgroup.FiniteIndex H.toSubgroup := H.finiteIndex_of_finite_quotient
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨H.toSubgroup.index, Subgroup.index_pos, ?_⟩
  refine PontryaginDual.ext fun x => ?_
  rw [dual_pow_apply', ← map_pow]
  exact hker _ (H.toSubgroup.pow_index_mem x)

/-- Morris, Topology Without Tears, Corollary A5.15.11 (TP-632). For a compact Hausdorff abelian
group `K`, the torsion subgroup of the dual is the annihilator of the identity component `C`, and
`C` is the annihilator of the torsion subgroup. -/
@[kb "morris2024" "Corollary A5.15.11, p. 612"]
theorem torsion_dual_eq_annihilator_connectedComponent :
    {χ : PontryaginDual K | IsOfFinOrder χ} = annihilator (connectedComponent (1 : K)) ∧
      connectedComponent (1 : K) = coannihilator {χ : PontryaginDual K | IsOfFinOrder χ} := by
  have h1 : {χ : PontryaginDual K | IsOfFinOrder χ} = annihilator (connectedComponent (1 : K)) := by
    ext χ
    constructor
    · intro h x hx
      exact char_trivial_on_connectedComponent_of_isOfFinOrder (χ := χ) h hx
    · intro h
      exact isOfFinOrder_of_trivial_on_connectedComponent (χ := χ) fun x hx => h x hx
  refine ⟨h1, ?_⟩
  ext x
  constructor
  · intro hx χ hχ
    have hχ' : IsOfFinOrder χ := hχ
    have hx' : x ∈ connectedComponent (1 : K) := hx
    exact char_trivial_on_connectedComponent_of_isOfFinOrder hχ' hx'
  · intro hx
    by_contra hxC
    obtain ⟨χ, hχC, hχx⟩ := exists_char_trivial_on_connectedComponent_ne hxC
    have h3 : IsOfFinOrder χ := isOfFinOrder_of_trivial_on_connectedComponent hχC
    exact hχx (hx χ h3)

/-- Morris, Topology Without Tears, Corollaries A5.15.12 and A5.15.15 (TP-633). A compact Hausdorff
abelian group is connected iff its dual group is torsion free. -/
@[kb "morris2024" "Corollary A5.15.12, p. 612"]
theorem connectedSpace_iff_torsionFree_dual :
    ConnectedSpace K ↔ ∀ χ : PontryaginDual K, IsOfFinOrder χ → χ = 1 := by
  constructor
  · intro hK χ hχ
    refine PontryaginDual.ext fun x => ?_
    have hx : x ∈ connectedComponent (1 : K) := by
      rw [PreconnectedSpace.connectedComponent_eq_univ]
      trivial
    rw [char_trivial_on_connectedComponent_of_isOfFinOrder hχ hx]
    rfl
  · intro h
    have hC : connectedComponent (1 : K) = univ := by
      ext x
      simp only [mem_univ, iff_true]
      by_contra hxC
      obtain ⟨χ, hχC, hχx⟩ := exists_char_trivial_on_connectedComponent_ne hxC
      have := h χ (isOfFinOrder_of_trivial_on_connectedComponent hχC)
      exact hχx (by rw [this]; rfl)
    haveI : PreconnectedSpace K := ⟨by rw [← hC]; exact isPreconnected_connectedComponent⟩
    exact { toNonempty := ⟨1⟩ }

end Components

/-! ### Properties of a compact group read off from its dual -/

section DualProperties

variable {K : Type u} [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [T2Space K]

/-- The `n`-th power map as a continuous homomorphism of an abelian topological group. -/
def powHom (n : ℕ) : K →ₜ* K := ⟨powMonoidHom n, continuous_pow n⟩

theorem map_powHom (n : ℕ) (ψ : PontryaginDual K) : PontryaginDual.map (powHom n) ψ = ψ ^ n :=
  PontryaginDual.ext fun x => by
    show ψ (x ^ n) = (ψ ^ n) x
    rw [dual_pow_apply', map_pow]

/-- Morris, Topology Without Tears, Proposition A5.0.18 (TP-491), torsion free versus divisible: a
compact Hausdorff abelian group is torsion free iff its dual group is divisible. -/
@[kb "morris2024" "Proposition A5.0.18, p. 504"]
theorem torsionFree_iff_dual_divisible :
    (∀ (x : K) (n : ℕ), 0 < n → x ^ n = 1 → x = 1) ↔
      ∀ (χ : PontryaginDual K) (n : ℕ), 0 < n → ∃ ψ : PontryaginDual K, ψ ^ n = χ := by
  constructor
  · intro h χ n hn
    have hinj : Function.Injective (powHom (K := K) n) := by
      intro x y hxy
      have hxy' : x ^ n = y ^ n := hxy
      have : (x * y⁻¹) ^ n = 1 := by rw [mul_pow, inv_pow, hxy', mul_inv_cancel]
      exact mul_inv_eq_one.1 (h _ n hn this)
    obtain ⟨hsurj, -⟩ := PontryaginDual_map_surjective_isQuotientMap_of_injective_compact
      (powHom n) hinj (fun _ _ hxy => characters_separate_points_of_compact hxy)
    obtain ⟨ψ, hψ⟩ := hsurj χ
    exact ⟨ψ, by rw [← map_powHom]; exact hψ⟩
  · intro h x n hn hx
    by_contra hx1
    obtain ⟨χ, hχ⟩ := exists_char_ne_one_of_compact hx1
    obtain ⟨ψ, hψ⟩ := h χ n hn
    apply hχ
    rw [← hψ, dual_pow_apply', ← map_pow, hx, map_one]

/-- Morris, Topology Without Tears, Proposition A5.0.18 (TP-491), metrizability: a compact Hausdorff
abelian group is metrizable iff its dual group is countable. -/
@[kb "morris2024" "Proposition A5.0.18, p. 504"]
theorem metrizableSpace_iff_countable_dual :
    TopologicalSpace.MetrizableSpace K ↔ Countable (PontryaginDual K) := by
  constructor
  · intro hK
    haveI : SecondCountableTopology K := inferInstance
    haveI : SecondCountableTopology C(K, Circle) := inferInstance
    haveI : SecondCountableTopology (PontryaginDual K) :=
      (ContinuousMonoidHom.isInducing_toContinuousMap K Circle).secondCountableTopology
    obtain ⟨s, hs, hd⟩ := TopologicalSpace.exists_countable_dense (PontryaginDual K)
    rw [dense_discrete] at hd
    rw [hd] at hs
    exact Set.countable_univ_iff.1 hs
  · intro hc
    exact isClosedEmbedding_evalChars'.isEmbedding.metrizableSpace

end DualProperties

end UndergradKB.Topology
