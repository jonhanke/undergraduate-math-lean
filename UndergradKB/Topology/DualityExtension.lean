import UndergradKB.Topology.LCASeparation
import UndergradKB.Topology.GroupsWave2g
import UndergradKB.Topology.DualityCompact2
import UndergradKB.Topology.DualityDiscrete2
import UndergradKB.Topology.DualityDiscrete3
import Mathlib.Topology.Algebra.Group.OpenMapping
import UndergradKB.Common.Attr

/-!
# Extending the duality theorem along compact subgroups and open subgroups

Ingredients of Morris, *Topology Without Tears*, Theorems A5.13.5 and A5.13.6 (TP-607, TP-572), in a
direct form that replaces the diagram chase of Propositions A5.13.2-A5.13.4 by explicit arguments:

* if `K` is a compact subgroup of a locally compact Hausdorff abelian group `G` and `G / K`
  satisfies the duality theorem, then the canonical map `G → G^^` is bijective (and a topological
  isomorphism when `G` is σ-compact, by the open mapping theorem);
* if `A` is an open subgroup of `G` satisfying the duality theorem, then so does `G`.
-/

open Topology Set

set_option linter.unusedSectionVars false

namespace UndergradKB.Topology

namespace LCA

universe u

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G]

theorem toDualDual_injective_LCA : Function.Injective (toDualDual G) := by
  intro x y h
  by_contra hne
  obtain ⟨χ, hχ⟩ := characters_separate_points_of_LCA hne
  exact hχ (DFunLike.congr_fun h χ)

/-- Characters of `G` trivial on a closed subgroup `K` come from characters of `G / K`. -/
theorem exists_char_quotient_of_trivial (K : Subgroup G) (χ : PontryaginDual G)
    (hχ : ∀ k ∈ K, χ k = 1) :
    ∃ ψ : PontryaginDual (G ⧸ K), ∀ y : G, ψ (y : G ⧸ K) = χ y := by
  let ψ0 : G ⧸ K →* Circle := QuotientGroup.lift K (χ : G →* Circle) fun k hk => hχ k hk
  have hc : Continuous ψ0 := by
    refine (QuotientGroup.isQuotientMap_mk K).continuous_iff.2 ?_
    exact χ.continuous
  exact ⟨⟨ψ0, hc⟩, fun y => rfl⟩

/-- If `K` is a compact subgroup and `G / K` satisfies the duality theorem, the canonical map
`G → G^^` is onto. -/
theorem toDualDual_surjective_of_compact_subgroup (K : Subgroup G) (hK : IsCompact (K : Set G))
    (hQ : DualityHolds (G ⧸ K)) : Function.Surjective (toDualDual G) := by
  classical
  have : IsClosed (K : Set G) := hK.isClosed
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  intro Φ
  obtain ⟨e, he⟩ := hQ
  let q : G →ₜ* G ⧸ K := ⟨QuotientGroup.mk' K, QuotientGroup.continuous_mk⟩
  let Φ' : PontryaginDual (PontryaginDual (G ⧸ K)) := Φ.comp (PontryaginDual.map q)
  obtain ⟨x, hx⟩ := e.surjective Φ'
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hΦq : ∀ ψ : PontryaginDual (G ⧸ K), Φ (PontryaginDual.map q ψ) = ψ (g : G ⧸ K) := by
    intro ψ
    have h1 := congrArg (fun z : PontryaginDual (PontryaginDual (G ⧸ K)) => z ψ) hx
    simp only [he] at h1
    exact h1.symm
  let Ψ : PontryaginDual (PontryaginDual G) := Φ * (toDualDual G g)⁻¹
  have hΨapp : ∀ χ, Ψ χ = Φ χ * (χ g)⁻¹ := fun χ => rfl
  have hΨ : ∀ χ : PontryaginDual G, (∀ k ∈ K, χ k = 1) → Ψ χ = 1 := by
    intro χ hχ
    obtain ⟨ψ, hψ⟩ := exists_char_quotient_of_trivial K χ hχ
    have hχψ : PontryaginDual.map q ψ = χ := PontryaginDual.ext fun y => hψ y
    have h1 := hΦq ψ
    rw [hχψ, hψ] at h1
    rw [hΨapp, h1, mul_inv_cancel]
  -- the induced character of the discrete dual of `K`
  have hext : ∀ η : PontryaginDual K, ∃ χ : PontryaginDual G, ∀ k : K, χ k = η k :=
    fun η => exists_extend_char_of_compact_subgroup_LCA K hK η
  choose ext hext using hext
  have hkey : ∀ (χ : PontryaginDual G) (η : PontryaginDual K), (∀ k : K, χ k = η k) →
      Ψ χ = Ψ (ext η) := by
    intro χ η hχη
    have htriv : ∀ k ∈ K, (χ * (ext η)⁻¹) k = 1 := by
      intro k hk
      show χ k * (ext η k)⁻¹ = 1
      rw [hχη ⟨k, hk⟩, hext η ⟨k, hk⟩, mul_inv_cancel]
    have h1 := hΨ _ htriv
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1
  let ψK0 : PontryaginDual K →* Circle :=
    { toFun := fun η => Ψ (ext η)
      map_one' := by
        rw [← hkey 1 1 (fun k => rfl), map_one]
      map_mul' := fun η η' => by
        rw [← hkey (ext η * ext η') (η * η') (fun k => by
          show ext η k * ext η' k = η k * η' k
          rw [hext, hext]), map_mul] }
  let ψK : PontryaginDual (PontryaginDual K) := ⟨ψK0, continuous_of_discreteTopology⟩
  obtain ⟨k, hk⟩ := toDualDual_surjective_compact (K := K) ψK
  refine ⟨(k : G) * g, PontryaginDual.ext fun χ => ?_⟩
  show χ ((k : G) * g) = Φ χ
  let η : PontryaginDual K := PontryaginDual.map ⟨K.subtype, continuous_subtype_val⟩ χ
  have hη : ∀ k' : K, χ k' = η k' := fun k' => rfl
  have h1 : Ψ χ = χ k := by
    rw [hkey χ η hη]
    have := DFunLike.congr_fun hk η
    exact this.symm
  have h2 : Φ χ = Ψ χ * χ g := by rw [hΨapp, inv_mul_cancel_right]
  rw [h2, h1, map_mul]

/-- The canonical map of a σ-compact group onto its double dual, when bijective, is a topological
isomorphism (open mapping theorem). -/
theorem dualityHolds_of_bijective [SigmaCompactSpace G] (hbij : Function.Bijective (toDualDual G)) :
    DualityHolds G := by
  have hopen : IsOpenMap (toDualDual G) :=
    MonoidHom.isOpenMap_of_sigmaCompact (toDualDual G).toMonoidHom hbij.2 (toDualDual G).continuous
  let e0 : G ≃* PontryaginDual (PontryaginDual G) := MulEquiv.ofBijective _ hbij
  let h0 : G ≃ₜ PontryaginDual (PontryaginDual G) :=
    e0.toEquiv.toHomeomorphOfContinuousOpen (toDualDual G).continuous hopen
  exact ⟨{ toMulEquiv := e0
           continuous_toFun := h0.continuous
           continuous_invFun := h0.symm.continuous }, fun g χ => rfl⟩

/-- Morris, Topology Without Tears, Theorem A5.13.5 (TP-607), reduction step: a σ-compact locally
compact Hausdorff abelian group with a compact subgroup `K` such that `G / K` satisfies the duality
theorem satisfies the duality theorem. -/
theorem dualityHolds_of_compact_subgroup [SigmaCompactSpace G] (K : Subgroup G)
    (hK : IsCompact (K : Set G)) (hQ : DualityHolds (G ⧸ K)) : DualityHolds G :=
  dualityHolds_of_bijective ⟨toDualDual_injective_LCA,
    toDualDual_surjective_of_compact_subgroup K hK hQ⟩

end LCA

end UndergradKB.Topology
