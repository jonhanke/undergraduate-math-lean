import UndergradKB.Topology.ClassicalDuals
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.PontryaginDual
import UndergradKB.Common.Attr

/-!
# Density of point-separating subgroups of the dual (Appendix 5 of Morris, wave 3)

Proposition A5.9.10 (TP-579) in the book's generality: if an abelian topological group `G`
satisfies the duality theorem (`DualityHolds G`) and every nontrivial Hausdorff quotient of the
dual group `Ĝ` has a nontrivial character, then every subgroup of `Ĝ` that separates the points of
`G` is dense in `Ĝ`.

The proof is the book's: if the closure `H` of the subgroup `S` is not all of `Ĝ`, the Hausdorff
quotient `Ĝ / H` is nontrivial, so it has a nontrivial character `ψ`; composing with the quotient
map gives a nontrivial character `Ψ` of `Ĝ` that is trivial on `S`. By duality `Ψ` is evaluation
at some `g ≠ 1` of `G`, and then no character in `S` separates `g` from `1`.
-/

open Topology Set

set_option linter.unusedSectionVars false

namespace UndergradKB.Topology

section DenseOfDuality

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The book's hypothesis on the dual group: every nontrivial Hausdorff quotient of `Ĝ` (the
quotient by a closed subgroup other than `Ĝ`) has a nontrivial character. -/
def QuotientsOfDualHaveCharacters (G : Type*) [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] : Prop :=
  ∀ H : Subgroup (PontryaginDual G), IsClosed (H : Set (PontryaginDual G)) → H ≠ ⊤ →
    ∃ ψ : PontryaginDual (PontryaginDual G ⧸ H), ψ ≠ 1

/-- Morris, Topology Without Tears, Proposition A5.9.10 (TP-579). Let `G` be an abelian
topological group satisfying the duality theorem, such that every nontrivial Hausdorff quotient
group of its dual `Ĝ` has a nontrivial character. Then every subgroup of `Ĝ` that separates the
points of `G` is dense in `Ĝ`. -/
@[kb "morris2024" "Proposition A5.9.10, p. 570"]
theorem dense_of_separatesPoints_of_dualityHolds (hG : DualityHolds G)
    (hq : QuotientsOfDualHaveCharacters G) (S : Subgroup (PontryaginDual G))
    (hS : ∀ x y : G, x ≠ y → ∃ χ ∈ S, χ x ≠ χ y) : Dense (S : Set (PontryaginDual G)) := by
  obtain ⟨e, he⟩ := hG
  let H := S.topologicalClosure
  have hHc : IsClosed (H : Set (PontryaginDual G)) := S.isClosed_topologicalClosure
  by_contra hne
  have hHtop : H ≠ ⊤ := by
    intro htop
    apply hne
    rw [dense_iff_closure_eq, ← Subgroup.topologicalClosure_coe]
    change ((H : Set (PontryaginDual G))) = univ
    rw [htop]
    rfl
  obtain ⟨ψ, hψ⟩ := hq H hHc hHtop
  -- the character `Ψ = ψ ∘ π` of the dual group
  let Ψ : PontryaginDual (PontryaginDual G) :=
    ψ.comp ⟨QuotientGroup.mk' H, continuous_quot_mk⟩
  have hΨ : ∀ χ, Ψ χ = ψ (QuotientGroup.mk χ) := fun _ => rfl
  have hΨ1 : Ψ ≠ 1 := by
    intro h1
    apply hψ
    ext q
    obtain ⟨χ, rfl⟩ := QuotientGroup.mk_surjective q
    have := DFunLike.congr_fun h1 χ
    rw [hΨ] at this
    exact congrArg Subtype.val this
  set g := e.symm Ψ with hg
  have heg : e g = Ψ := by rw [hg]; exact e.apply_symm_apply Ψ
  have hg1 : g ≠ 1 := by
    intro h
    apply hΨ1
    rw [← heg, h, map_one]
  obtain ⟨χ, hχS, hχ⟩ := hS g 1 hg1
  apply hχ
  rw [map_one, ← he g χ, heg, hΨ]
  have hχH : χ ∈ H := S.le_topologicalClosure hχS
  rw [(QuotientGroup.eq_one_iff χ).mpr hχH, map_one]

end DenseOfDuality

end UndergradKB.Topology
