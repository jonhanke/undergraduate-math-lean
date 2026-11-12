import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Topology.ContinuousMap.Compact
import UndergradKB.Common.Attr

/-! # Every Banach space is a space of continuous functions (Morris, Remark 12.2.31)

Every real normed space `E` embeds linearly and isometrically into `C(X, ℝ)` for a compact Hausdorff space `X`: take
for `X` the closed unit ball of the dual space with the weak-* topology (compact by the Banach-Alaoglu theorem) and
send `x` to the evaluation `φ ↦ φ x`; the embedding is isometric by the Hahn-Banach theorem. -/

open Metric

namespace UndergradKB.Topology

universe u

variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The closed unit ball of the dual of `E`, with the weak-* topology. -/
noncomputable def dualUnitBall : Set (WeakDual ℝ E) := WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ E) 1

instance : CompactSpace (dualUnitBall E) :=
  isCompact_iff_compactSpace.mp (WeakDual.isCompact_closedBall 0 1)

/-- The evaluation map `E → C(B, ℝ)`, `x ↦ (φ ↦ φ x)`, on the weak-* closed unit ball `B` of the dual. -/
noncomputable def evalOnDualBall : E →ₗ[ℝ] C(dualUnitBall E, ℝ) where
  toFun x := ⟨fun φ ↦ (φ : WeakDual ℝ E) x, (WeakDual.eval_continuous x).comp continuous_subtype_val⟩
  map_add' x y := by ext φ; simp
  map_smul' c x := by ext φ; simp

lemma norm_evalOnDualBall (x : E) : ‖evalOnDualBall E x‖ = ‖x‖ := by
  apply le_antisymm
  · refine (ContinuousMap.norm_le _ (norm_nonneg x)).mpr fun φ ↦ ?_
    have hφ : ‖WeakDual.toStrongDual (φ : WeakDual ℝ E)‖ ≤ 1 := by
      simpa [dualUnitBall] using φ.2
    calc ‖(evalOnDualBall E x) φ‖ = ‖WeakDual.toStrongDual (φ : WeakDual ℝ E) x‖ := rfl
      _ ≤ ‖WeakDual.toStrongDual (φ : WeakDual ℝ E)‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖x‖ := by gcongr
      _ = ‖x‖ := one_mul _
  · obtain ⟨g, hg, hgx⟩ := exists_dual_vector'' ℝ x
    let φ : dualUnitBall E := ⟨StrongDual.toWeakDual g, by simpa [dualUnitBall] using hg⟩
    calc ‖x‖ = ‖(evalOnDualBall E x) φ‖ := by
          change ‖x‖ = ‖g x‖
          rw [hgx]; simp
      _ ≤ ‖evalOnDualBall E x‖ := ContinuousMap.norm_coe_le_norm _ _

/-- Morris, Topology Without Tears, Remark 12.2.31 (TP-372). Every (real) Banach space, indeed every real normed
space, is linearly isometric to a subspace of `C(X, ℝ)` for some compact Hausdorff space `X`. -/
@[kb "morris2024" "Remark 12.2.31, p. 387"]
theorem exists_linearIsometry_continuousMap :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : CompactSpace X) (_ : T2Space X),
      Nonempty (E →ₗᵢ[ℝ] C(X, ℝ)) :=
  ⟨dualUnitBall E, inferInstance, inferInstance, inferInstance,
    ⟨⟨evalOnDualBall E, norm_evalOnDualBall E⟩⟩⟩

end UndergradKB.Topology
