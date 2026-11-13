import UndergradKB.Topology.DualityCompact
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Complex.Circle
import UndergradKB.Common.Attr

/-!
# Wave 2: compact abelian groups embed in products of `SO(2)` (Morris, Appendix 5.0 and 5.10)

The abelian case of the Peter-Weyl theorem: since the circle group is `SO(2)` and the characters of a
compact Hausdorff abelian group separate points, such a group is a closed subgroup of a power of `SO(2)`.
The nonabelian case (unitary or orthogonal representations of dimension `> 1`) is not available.
-/

open Set Topology

universe u

namespace UndergradKB.Topology

/-- The rotation matrix of a unit complex number. -/
noncomputable def circleToSO2 : Circle →* Matrix.specialOrthogonalGroup (Fin 2) ℝ where
  toFun z := ⟨!![(z : ℂ).re, -(z : ℂ).im; (z : ℂ).im, (z : ℂ).re], by
    rw [Matrix.of_mem_specialOrthogonalGroup_fin_two_iff]
    refine ⟨rfl, rfl, ?_⟩
    have h1 : Complex.normSq (z : ℂ) = 1 := by
      rw [← Complex.sq_norm, Circle.norm_coe]; norm_num
    rw [Complex.normSq_apply] at h1
    nlinarith⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' z w := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

theorem continuous_circleToSO2 : Continuous circleToSO2 := by
  refine Continuous.subtype_mk (continuous_matrix fun i j => ?_) _
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem circleToSO2_injective : Function.Injective circleToSO2 := by
  intro z w h
  have h' := congrArg Subtype.val h
  have h00 := congrFun (congrFun h' 0) 0
  have h10 := congrFun (congrFun h' 1) 0
  simp [circleToSO2] at h00 h10
  exact Subtype.ext (Complex.ext h00 h10)

theorem isClosedEmbedding_circleToSO2 : IsClosedEmbedding circleToSO2 :=
  continuous_circleToSO2.isClosedEmbedding circleToSO2_injective

/-- Morris, Topology Without Tears, Theorem A5.0.12 (TP-486) and Theorem A5.10.1 (TP-580), abelian case.
A compact Hausdorff abelian group is topologically isomorphic to a closed subgroup of a product of copies
of `SO(2)` (the circle group, as rotation matrices). The general (nonabelian) Peter-Weyl theorem, with
orthogonal groups of higher dimension, is not proved. -/
@[kb "morris2024" "Theorem A5.0.12, p. 502"]
theorem exists_isClosedEmbedding_specialOrthogonal_pow (K : Type u) [CommGroup K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [T2Space K] :
    ∃ (ι : Type u) (f : K →* (ι → Matrix.specialOrthogonalGroup (Fin 2) ℝ)), IsClosedEmbedding f := by
  obtain ⟨ι, f, hf⟩ := exists_isClosedEmbedding_circle_pow (K := K)
  let g : (ι → Circle) →* (ι → Matrix.specialOrthogonalGroup (Fin 2) ℝ) :=
    MonoidHom.pi fun i => circleToSO2.comp (Pi.evalMonoidHom (fun _ : ι => Circle) i)
  refine ⟨ι, g.comp f, ?_⟩
  have h2 : IsClosedEmbedding (Pi.map fun _ : ι => circleToSO2) :=
    IsClosedEmbedding.piMap fun _ => isClosedEmbedding_circleToSO2
  exact h2.comp hf

end UndergradKB.Topology
