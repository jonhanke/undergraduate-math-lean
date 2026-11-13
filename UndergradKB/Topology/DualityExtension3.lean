import UndergradKB.Topology.DualityExtension2
import UndergradKB.Common.Attr

/-!
# The dual sequence of an open subgroup (Morris, Proposition A5.13.3, TP-605)

For an open subgroup `A` of a locally compact Hausdorff abelian group `G`, with inclusion
`f₁ : A → G` and quotient map `f₂ : G → G ⧸ A`, the dual sequence
`0 ← A^ ← G^ ← (G ⧸ A)^ ← 0` is exact, `f₁^*` is open and `f₂^*` is a homeomorphism onto its image.
-/

open Topology Set

set_option linter.unusedSectionVars false

namespace UndergradKB.Topology

namespace LCA

universe u

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G]

/-- Morris, Topology Without Tears, Proposition A5.13.3 (TP-605). For an open subgroup `A` of a
locally compact Hausdorff abelian group `G`, restriction `G^ → A^` is onto and open, its kernel is the
annihilator of `A`, and the dual of the quotient map `G → G ⧸ A` is a closed embedding of the compact
group `(G ⧸ A)^` onto that annihilator. -/
@[kb "morris2024" "Proposition A5.13.3, p. 593"]
theorem dual_sequence_of_open_subgroup (A : Subgroup G) (hA : IsOpen (A : Set G)) :
    let q : G →ₜ* G ⧸ A := ⟨QuotientGroup.mk' A, QuotientGroup.continuous_mk⟩
    Function.Surjective (PontryaginDual.map (inclHom A)) ∧
      IsOpenMap (PontryaginDual.map (inclHom A)) ∧
      (∀ χ : PontryaginDual G, PontryaginDual.map (inclHom A) χ = 1 ↔ χ ∈ annih A) ∧
      Function.Injective (PontryaginDual.map q) ∧
      IsClosedEmbedding (PontryaginDual.map q) ∧
      Set.range (PontryaginDual.map q) = (annih A : Set (PontryaginDual G)) := by
  intro q
  have : DiscreteTopology (G ⧸ A) := QuotientGroup.discreteTopology hA
  have hinj : Function.Injective (PontryaginDual.map q) := by
    intro ψ ψ' h
    refine PontryaginDual.ext fun x => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    exact DFunLike.congr_fun h y
  have hrange : Set.range (PontryaginDual.map q) = (annih A : Set (PontryaginDual G)) := by
    ext χ
    constructor
    · rintro ⟨ψ, rfl⟩ y hy
      show ψ (y : G ⧸ A) = 1
      rw [(QuotientGroup.eq_one_iff y).2 hy, map_one]
    · intro hχ
      obtain ⟨ψ, hψ⟩ := exists_char_quotient_of_trivial A χ hχ
      exact ⟨ψ, PontryaginDual.ext fun y => hψ y⟩
  refine ⟨restrict_surjective_of_isOpen A hA, restrict_isOpenMap_of_isOpen A hA, fun χ => ?_,
    hinj, (PontryaginDual.map q).continuous.isClosedEmbedding hinj, hrange⟩
  constructor
  · intro h y hy
    exact DFunLike.congr_fun h ⟨y, hy⟩
  · intro h
    exact PontryaginDual.ext fun a => h a a.2

end LCA

end UndergradKB.Topology
