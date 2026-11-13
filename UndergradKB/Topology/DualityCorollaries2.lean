import UndergradKB.Topology.DualityCorollaries
import UndergradKB.Topology.StructureTheorems
import UndergradKB.Common.Attr

/-!
# Compact elements of the dual and the identity component (Morris, A5.15.8 to A5.15.10)

Uses the principal structure theorem (an open subgroup `ℝᵃ × K` with `K` compact): a character of `G`
trivial on the identity component is trivial on an open subgroup of `G`, hence lies in a compact
annihilator, hence is a compact element.
-/

open Topology Set

set_option linter.unusedSectionVars false

universe u

namespace UndergradKB.Topology

namespace LCA

theorem finite_circle_nthRoots {n : ℕ} (hn : 0 < n) : {z : Circle | z ^ n = 1}.Finite := by
  have hsub : {z : Circle | z ^ n = 1} ⊆ (fun z : Circle => (z : ℂ)) ⁻¹'
      (Polynomial.nthRootsFinset n (1 : ℂ) : Set ℂ) := by
    intro z hz
    have hz' : z ^ n = 1 := hz
    show (z : ℂ) ∈ (Polynomial.nthRootsFinset n (1 : ℂ) : Set ℂ)
    rw [Finset.mem_coe, Polynomial.mem_nthRootsFinset hn, ← Circle.coe_pow, hz']
    rfl
  exact (Set.Finite.preimage (fun a _ b _ h => Subtype.ext h) (Finset.finite_toSet _)).subset hsub

/-- The kernel of a character of finite order is open. -/
theorem isOpen_ker_of_isOfFinOrder {K : Type*} [CommGroup K] [TopologicalSpace K]
    (ψ : PontryaginDual K) (hψ : IsOfFinOrder ψ) : IsOpen (((ψ : K →* Circle).ker : Set K)) := by
  obtain ⟨n, hn, hn1⟩ := isOfFinOrder_iff_pow_eq_one.1 hψ
  have hT : ∀ x, ψ x ∈ {z : Circle | z ^ n = 1} := by
    intro x
    show (ψ x) ^ n = 1
    have e : (ψ ^ n) x = 1 := congrArg (fun χ : PontryaginDual K => χ x) hn1
    exact (dual_pow_apply K ψ n x).symm.trans e
  let F : Set Circle := {z : Circle | z ^ n = 1} \ {1}
  have hF : F.Finite := (finite_circle_nthRoots hn).sdiff
  have heq : ((ψ : K →* Circle).ker : Set K) = (ψ : K → Circle) ⁻¹' Fᶜ := by
    ext x
    constructor
    · intro hx h
      exact h.2 hx
    · intro hx
      by_contra hne
      exact hx ⟨hT x, hne⟩
  rw [heq]
  exact hF.isClosed.isOpen_compl.preimage ψ.continuous

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G]

/-- A point outside the identity component is separated from it by a character trivial on it. -/
theorem exists_char_trivial_on_connectedComponent_ne_of_LCA {x : G}
    (hx : x ∉ connectedComponent (1 : G)) :
    ∃ χ : PontryaginDual G, (∀ y ∈ connectedComponent (1 : G), χ y = 1) ∧ χ x ≠ 1 := by
  have hc : IsClosed ((Subgroup.connectedComponentOfOne G : Subgroup G) : Set G) :=
    isClosed_connectedComponent
  exact exists_char_trivial_on_ne_of_LCA (Subgroup.connectedComponentOfOne G) hc hx

/-- A character trivial on the identity component is trivial on some open subgroup. -/
theorem exists_open_subgroup_char_trivial_of_trivial_on_connectedComponent (γ : PontryaginDual G)
    (hγ : ∀ g ∈ connectedComponent (1 : G), γ g = 1) :
    ∃ H : Subgroup G, IsOpen (H : Set G) ∧ ∀ h ∈ H, γ h = 1 := by
  obtain ⟨S, hSo, a, K, iK1, iK2, iK3, iK4, iK5, ⟨e⟩⟩ := exists_open_subgroup_equiv_real_compact
    (G := G)
  let Φ : (Fin a → Multiplicative ℝ) × K →* G := S.subtype.comp e.symm.toMulEquiv.toMonoidHom
  have hΦc : Continuous Φ := continuous_subtype_val.comp e.symm.continuous
  have hΦo : IsOpenMap Φ := hSo.isOpenMap_subtype_val.comp e.symm.toHomeomorph.isOpenMap
  haveI : ConnectedSpace (Multiplicative ℝ) := inferInstanceAs (ConnectedSpace ℝ)
  haveI : PreconnectedSpace (Fin a → Multiplicative ℝ) := inferInstance
  have hC1 : ∀ x : Fin a → Multiplicative ℝ, γ (Φ (x, 1)) = 1 := by
    have hfc : Continuous (fun x : Fin a → Multiplicative ℝ => Φ (x, 1)) :=
      hΦc.comp (continuous_id.prodMk continuous_const)
    have h1 : (1 : G) ∈ Set.range (fun x : Fin a → Multiplicative ℝ => Φ (x, 1)) :=
      ⟨1, map_one Φ⟩
    intro x
    exact hγ _ ((isPreconnected_range hfc).subset_connectedComponent h1 ⟨x, rfl⟩)
  let ψ : PontryaginDual K :=
    ⟨(γ : G →* Circle).comp (Φ.comp (MonoidHom.inr _ K)),
      γ.continuous.comp (hΦc.comp (continuous_const.prodMk continuous_id))⟩
  have hψ : ψ ∈ UndergradKB.Topology.annihilator (connectedComponent (1 : K)) := by
    intro k hk
    have hf : Continuous (fun k : K => Φ ((1 : Fin a → Multiplicative ℝ), k)) :=
      hΦc.comp (continuous_const.prodMk continuous_id)
    have := hf.image_connectedComponent_subset (1 : K) ⟨k, hk, rfl⟩
    have h1 : Φ ((1 : Fin a → Multiplicative ℝ), (1 : K)) = 1 := map_one Φ
    rw [h1] at this
    exact hγ _ this
  have hfin : IsOfFinOrder ψ := by
    have := (torsion_dual_eq_annihilator_connectedComponent (K := K)).1
    rw [← this] at hψ
    exact hψ
  have hkerO := isOpen_ker_of_isOfFinOrder ψ hfin
  refine ⟨(Subgroup.prod ⊤ (ψ : K →* Circle).ker).map Φ, ?_, ?_⟩
  · have : (((Subgroup.prod ⊤ (ψ : K →* Circle).ker).map Φ : Subgroup G) : Set G) =
        Φ '' (Set.univ ×ˢ ((ψ : K →* Circle).ker : Set K)) := by
      rw [Subgroup.coe_map, Subgroup.coe_prod]
      rfl
    rw [this]
    exact hΦo _ (isOpen_univ.prod hkerO)
  · rintro _ ⟨⟨x, k⟩, ⟨-, hk⟩, rfl⟩
    have hk' : γ (Φ (1, k)) = 1 := hk
    have : Φ (x, k) = Φ (x, 1) * Φ (1, k) := by
      rw [← map_mul]
      simp
    rw [this, map_mul, hC1 x, hk', one_mul]

/-- A character trivial on the identity component is a compact element. -/
theorem isCompactElement_of_trivial_on_connectedComponent (γ : PontryaginDual G)
    (hγ : ∀ g ∈ connectedComponent (1 : G), γ g = 1) : IsCompactElement γ := by
  obtain ⟨H, hHo, hH⟩ := exists_open_subgroup_char_trivial_of_trivial_on_connectedComponent γ hγ
  have hc := isCompact_annih H hHo
  have hγH : γ ∈ annih H := fun h hh => hH h hh
  refine hc.of_isClosed_subset (Subgroup.isClosed_topologicalClosure _) ?_
  exact (Subgroup.topologicalClosure_minimal _ ((Subgroup.zpowers_le).2 hγH) hc.isClosed :
    _ ≤ annih H)

/-- Morris, Topology Without Tears, Theorem A5.15.8 (TP-630). For a locally compact Hausdorff abelian
group `G` with dual group `Γ`: the set of compact elements of `Γ` is the annihilator of the identity
component `C` of `G`, and `C` is the annihilator in `G` of the compact elements of `Γ`. -/
@[kb "morris2024" "Theorem A5.15.8, p. 611"]
theorem compactElements_dual_eq_annihilator_connectedComponent :
    {γ : PontryaginDual G | IsCompactElement γ} =
        {γ | ∀ g ∈ connectedComponent (1 : G), γ g = 1} ∧
      connectedComponent (1 : G) = {g | ∀ γ : PontryaginDual G, IsCompactElement γ → γ g = 1} := by
  have h1 : {γ : PontryaginDual G | IsCompactElement γ} =
      {γ | ∀ g ∈ connectedComponent (1 : G), γ g = 1} := by
    ext γ
    exact ⟨fun h g hg => char_eq_one_on_connectedComponent_of_isCompactElement γ h hg,
      isCompactElement_of_trivial_on_connectedComponent γ⟩
  refine ⟨h1, ?_⟩
  ext g
  constructor
  · intro hg γ hγ
    exact char_eq_one_on_connectedComponent_of_isCompactElement γ hγ hg
  · intro hg
    by_contra hgC
    obtain ⟨χ, hχC, hχg⟩ := exists_char_trivial_on_connectedComponent_ne_of_LCA hgC
    have : IsCompactElement χ := isCompactElement_of_trivial_on_connectedComponent χ hχC
    exact hχg (hg χ this)

/-- Morris, Topology Without Tears, Corollary A5.15.9 (TP-631). A locally compact Hausdorff abelian
group is totally disconnected iff every element of its dual group is compact. -/
@[kb "morris2024" "Corollary A5.15.9, p. 611"]
theorem totallyDisconnectedSpace_iff_forall_isCompactElement_dual :
    TotallyDisconnectedSpace G ↔ ∀ γ : PontryaginDual G, IsCompactElement γ := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_one]
  constructor
  · intro h γ
    refine isCompactElement_of_trivial_on_connectedComponent γ fun g hg => ?_
    rw [h] at hg
    rw [Set.mem_singleton_iff.1 hg]
    exact map_one γ
  · intro h
    ext g
    constructor
    · intro hg
      by_contra hg1
      obtain ⟨χ, hχ⟩ := exists_char_ne_one_of_LCA (Set.mem_singleton_iff.not.1 hg1)
      exact hχ (char_eq_one_on_connectedComponent_of_isCompactElement χ (h χ) hg)
    · intro hg
      rw [Set.mem_singleton_iff.1 hg]
      exact mem_connectedComponent

/-- Morris, Topology Without Tears, Corollary A5.15.10 (TP-631). A locally compact Hausdorff abelian
group is connected iff its dual group has no non-trivial compact subgroup. -/
@[kb "morris2024" "Corollary A5.15.10, p. 612"]
theorem connectedSpace_iff_forall_isCompact_subgroup_dual :
    ConnectedSpace G ↔ ∀ K : Subgroup (PontryaginDual G),
      IsCompact (K : Set (PontryaginDual G)) → K = ⊥ := by
  constructor
  · intro hG K hK
    exact eq_bot_of_isCompact_subgroup_dual_of_connectedSpace K hK
  · intro h
    have hC : connectedComponent (1 : G) = univ := by
      rw [(compactElements_dual_eq_annihilator_connectedComponent (G := G)).2]
      ext g
      simp only [mem_setOf_eq, mem_univ, iff_true]
      intro γ hγ
      have hK : (Subgroup.zpowers γ).topologicalClosure = ⊥ := h _ hγ
      have : γ ∈ (Subgroup.zpowers γ).topologicalClosure :=
        Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers γ)
      rw [hK, Subgroup.mem_bot] at this
      rw [this]
      rfl
    haveI : PreconnectedSpace G := ⟨by rw [← hC]; exact isPreconnected_connectedComponent⟩
    exact { toNonempty := ⟨1⟩ }

end LCA

end UndergradKB.Topology
