import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.SetTheory.Ordinal.CantorNormalForm
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Exponential
import Mathlib.Topology.UniformSpace.Ascoli
import UndergradKB.Common.Attr

/-!
# Course layer: extra wrappers (Polish spaces, smooth/analytic, ordinals, Ascoli)
-/

open Filter Set
open scoped Topology ContDiff

namespace UndergradKB.Topology.Course

universe u

/-- Morris, Topology Without Tears, Definition 6.3.18 (TP-135). A separable complete metric space
is Polish. -/
@[kb "morris2024" "Definition 6.3.18, p. 155"]
theorem morris_6_3_18 (X : Type u) [MetricSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] :
    PolishSpace X :=
  inferInstance

/-- Morris, Topology Without Tears, Definition 6.3.18 (TP-135). A space is Polish iff it is
separable and completely metrizable. -/
@[kb "morris2024" "Definition 6.3.18, p. 155"]
theorem morris_6_3_18_b (X : Type u) [TopologicalSpace X] :
    PolishSpace X ↔ TopologicalSpace.SeparableSpace X ∧ TopologicalSpace.IsCompletelyMetrizableSpace X := by
  constructor
  · intro h
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨h1, h2⟩
    letI := TopologicalSpace.upgradeIsCompletelyMetrizable X
    haveI : SecondCountableTopology X := UniformSpace.secondCountable_of_separable X
    exact {}

/-- Morris, Topology Without Tears, Definition 12.1.15 (TP-338). A function on an open set is
smooth iff it is `n` times differentiable for every `n`; it is analytic at a point iff it is given
near the point by a convergent power series. -/
@[kb "morris2024" "Definition 12.1.15, p. 367"]
theorem morris_12_1_15 (f : ℝ → ℝ) (U : Set ℝ) (x : ℝ) :
    (ContDiffOn ℝ ∞ f U ↔ ∀ n : ℕ, ContDiffOn ℝ n f U) ∧
      (AnalyticAt ℝ f x ↔ ∃ p : FormalMultilinearSeries ℝ ℝ ℝ, HasFPowerSeriesAt f p x) :=
  ⟨contDiffOn_infty, Iff.rfl⟩

/-- Morris, Topology Without Tears, Definition 12.1.18 (TP-340). `f' : ℝⁿ → ℝᵐ` linear is the
derivative of `f` at `x` iff `f y - f x - f' (y - x)` is `o(‖y - x‖)`, in epsilon-delta form. -/
@[kb "morris2024" "Definition 12.1.18, p. 369"]
theorem morris_12_1_18 {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (x : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt f f' x ↔
      ∀ ε > 0, ∃ δ > 0, ∀ y, ‖y - x‖ < δ → ‖f y - f x - f' (y - x)‖ ≤ ε * ‖y - x‖ := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  refine forall₂_congr fun ε hε => ?_
  rw [Metric.eventually_nhds_iff]
  simp only [dist_eq_norm]

/-- Morris, Topology Without Tears, Definition A1.4.13 and Remark A1.4.14 (TP-422). Ordinal
addition and multiplication are associative but addition is not commutative: `1 + ω = ω` while
`ω + 1 ≠ ω`. -/
@[kb "morris2024" "Definition A1.4.13, p. 420"]
theorem morris_A1_4_13 :
    (∀ a b c : Ordinal.{u}, a + b + c = a + (b + c)) ∧ (∀ a b c : Ordinal.{u}, a * b * c = a * (b * c)) ∧
      (1 + Ordinal.omega0.{u} = Ordinal.omega0.{u}) ∧
        (Ordinal.omega0.{u} + 1 ≠ Ordinal.omega0.{u}) :=
  ⟨add_assoc, mul_assoc, Ordinal.one_add_omega0, (lt_add_one Ordinal.omega0.{u}).ne'⟩

/-- Morris, Topology Without Tears, Definition A1.4.16 and Remarks A1.4.15, A1.4.17 (TP-423). The
initial segment `{b | b < a}` of the ordinals has order type `a`, and every nonempty set of ordinals
has a least element. -/
@[kb "morris2024" "Definition A1.4.16, p. 421"]
theorem morris_A1_4_16 (a : Ordinal.{u}) :
    Ordinal.type (α := Set.Iio a) (· < ·) = Ordinal.lift.{u + 1} a ∧
      ∀ s : Set Ordinal.{u}, s.Nonempty → ∃ m ∈ s, ∀ b ∈ s, m ≤ b := by
  refine ⟨(Ordinal.type_Iio_lt a).trans (Ordinal.typein_ordinal a), fun s hs => ?_⟩
  exact ⟨sInf s, csInf_mem hs, fun b hb => csInf_le' hb⟩

/-- Morris, Topology Without Tears, Proposition A1.4.32 (TP-431). Cantor normal form: for a base
`b > 1` every ordinal `o` is the finite sum `b^e₁ c₁ + ... + b^eₖ cₖ` with strictly decreasing
exponents and coefficients `0 < cᵢ < b`. -/
@[kb "morris2024" "Proposition A1.4.32, p. 425"]
theorem morris_A1_4_32 (b o : Ordinal.{u}) (hb : 1 < b) :
    (Ordinal.CNF b o).foldr (fun p r => b ^ p.1 * p.2 + r) 0 = o ∧
      ((Ordinal.CNF b o).map Prod.fst).SortedGT ∧
      ∀ p ∈ Ordinal.CNF b o, 0 < p.2 ∧ p.2 < b :=
  ⟨Ordinal.CNF.foldr b o, Ordinal.CNF.sortedGT b o,
    fun _ hp => ⟨Ordinal.CNF.snd_pos hp, Ordinal.CNF.snd_lt hb hp⟩⟩

/-- Morris, Topology Without Tears, Theorem A5.6.11 (TP-563). Ascoli: a subset `S` of `C(E, F)`
(`F` a Hausdorff uniform space) that is closed for the pointwise topology, pointwise relatively
compact and equicontinuous is compact in the compact-open topology. -/
@[kb "morris2024" "Theorem A5.6.11, p. 555"]
theorem morris_A5_6_11 {E F : Type*} [TopologicalSpace E] [UniformSpace F] [T2Space F]
    (S : Set C(E, F)) (hcl : IsClosed (ContinuousMap.toFun '' S))
    (hpt : ∀ x : E, IsCompact (closure ((fun f : C(E, F) => f x) '' S)))
    (heq : Equicontinuous ((↑) : S → E → F)) : IsCompact S := by
  apply ArzelaAscoli.isCompact_of_equicontinuous S _ heq
  have hK : IsCompact (Set.pi Set.univ fun x : E => closure ((fun f : C(E, F) => f x) '' S)) :=
    isCompact_univ_pi hpt
  refine hK.of_isClosed_subset hcl ?_
  rintro _ ⟨f, hf, rfl⟩ x -
  exact subset_closure ⟨f, hf, rfl⟩

end UndergradKB.Topology.Course
