import UndergradKB.Topology.BanachMazur
import Mathlib.Topology.MetricSpace.Kuratowski
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.UnitInterval
import UndergradKB.Common.Attr

/-!
# The Kleiber-Pervin theorem, countable case (Morris, Remark 12.2.31, TP-373)

Statement in the book: `C([0,1]^ℵ, ℝ)` with the uniform metric has density character `ℵ`, and every
metric space of density character `ℵ` embeds isometrically in it.

Proved here: the case `ℵ = ℵ₀`.  A separable metric space `α` embeds isometrically (Kuratowski) into
`ℓ^∞(ℕ)`, hence into the closed linear span `B` of the image, a separable Banach space; Banach-Mazur
embeds `B` linearly isometrically into `C([0,1])`, and `C([0,1]) → C([0,1]^ℕ)`, `f ↦ f ∘ pr₀`, is a linear
isometry.  The space `C([0,1]^ℕ, ℝ)` is separable.

Not proved: the uncountable case `ℵ > ℵ₀`.  Route: `α` embeds in a Banach space `B` of density `≤ ℵ`
(closed span of the Kuratowski image); `B` embeds linearly isometrically in `C(K)` for the weak-* dual ball
`K`, a compact Hausdorff space of weight `≤ ℵ`, which is a closed subspace of `[0,1]^ℵ`.  The missing lemma
is an isometric (e.g. linear, norm one) extension operator `C(K) → C([0,1]^ℵ)` for a closed subset `K` of the
cube of weight `≤ ℵ` (Tietze extension is norm preserving on single functions but not additive, and the
cube is not metrizable for `ℵ > ℵ₀`, so McShane-type formulae are unavailable), together with the bound
`density(C([0,1]^ℵ)) ≤ ℵ`.
-/

open Set
open scoped ENNReal lp

namespace UndergradKB.Topology

universe u

/-- A separable metric space embeds isometrically in `C([0,1], ℝ)` (Kuratowski, then Banach-Mazur on the
closed linear span of the Kuratowski image). -/
theorem exists_isometry_unitInterval_of_separable (α : Type u) [MetricSpace α] [TopologicalSpace.SeparableSpace α] :
    ∃ φ : α → C(unitInterval, ℝ), Isometry φ := by
  have hf : Isometry (kuratowskiEmbedding α) := kuratowskiEmbedding.isometry α
  let S : Submodule ℝ ℓ^∞(ℕ, ℝ) := (Submodule.span ℝ (range (kuratowskiEmbedding α))).topologicalClosure
  have hsep : TopologicalSpace.IsSeparable (S : Set ℓ^∞(ℕ, ℝ)) := by
    rw [show (S : Set ℓ^∞(ℕ, ℝ)) = closure (Submodule.span ℝ (range (kuratowskiEmbedding α)) : Set ℓ^∞(ℕ, ℝ))
      from Submodule.topologicalClosure_coe _]
    exact (TopologicalSpace.isSeparable_range hf.continuous).span.closure
  haveI : TopologicalSpace.SeparableSpace S := hsep.separableSpace
  let g : α → S := fun a => ⟨kuratowskiEmbedding α a,
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨a, rfl⟩)⟩
  have hg : Isometry g := Isometry.of_dist_eq fun a b => hf.dist_eq a b
  obtain ⟨T⟩ := banach_mazur S
  exact ⟨fun a => T (g a), T.isometry.comp hg⟩

/-- Morris, Topology Without Tears, Remark 12.2.31 (TP-373), the case `ℵ = ℵ₀` of the Kleiber-Pervin
theorem. Every separable metric space embeds isometrically in `C([0,1]^ℕ, ℝ)`. -/
@[kb "morris2024" "Remark 12.2.31, p. 387"]
theorem exists_isometry_hilbertCube_of_separable (α : Type u) [MetricSpace α]
    [TopologicalSpace.SeparableSpace α] :
    ∃ φ : α → C(ℕ → unitInterval, ℝ), Isometry φ := by
  obtain ⟨φ, hφ⟩ := exists_isometry_unitInterval_of_separable α
  let p : C(ℕ → unitInterval, unitInterval) := ⟨fun c => c 0, continuous_apply 0⟩
  have hp : Function.Surjective p := fun t => ⟨fun _ => t, rfl⟩
  exact ⟨fun a => compSurjLI p hp (φ a), (compSurjLI p hp).isometry.comp hφ⟩

/-- Morris, Topology Without Tears, Remark 12.2.31 (TP-373), the case `ℵ = ℵ₀`: `C([0,1]^ℕ, ℝ)` is
separable (density character `ℵ₀`). -/
@[kb "morris2024" "Remark 12.2.31, p. 387"]
theorem separableSpace_continuousMap_hilbertCube :
    TopologicalSpace.SeparableSpace C(ℕ → unitInterval, ℝ) := by
  have : SecondCountableTopology C(ℕ → unitInterval, ℝ) := inferInstance
  infer_instance

end UndergradKB.Topology
