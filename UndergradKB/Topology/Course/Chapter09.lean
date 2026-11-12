import Mathlib.Topology.Instances.CantorSet
import Mathlib.Topology.MetricSpace.HausdorffAlexandroff
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.Metrizable.CompletelyMetrizable
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Bases
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Separation.Hausdorff
import UndergradKB.Common.Attr

/-!
# Course layer, Chapter 9 of Morris, Topology Without Tears

Countable products, the Cantor set, metrizability (thin wrappers of Mathlib results).
-/

namespace UndergradKB.Topology.Course

open Set TopologicalSpace Filter

/-- Morris, Topology Without Tears, Remark 9.1.1 (TP-204). The Cantor set is the intersection of the
finite stages obtained by deleting open middle thirds, and it is closed (indeed compact). -/
@[kb "morris2024" "Remark 9.1.1, p. 223"]
theorem morris_9_1_1 :
    cantorSet = ⋂ n, preCantorSet n ∧ IsClosed cantorSet ∧ IsCompact cantorSet :=
  ⟨rfl, isClosed_cantorSet, isCompact_cantorSet⟩

/-- Morris, Topology Without Tears, Definition 9.2.1 (TP-205). Basic open sets of a countable product
restrict finitely many coordinates to open sets. -/
@[kb "morris2024" "Definition 9.2.1, p. 225"]
theorem morris_9_2_1 {X : ℕ → Type*} [∀ i, TopologicalSpace (X i)] :
    IsTopologicalBasis { S : Set (∀ i, X i) | ∃ (U : ∀ i, Set (X i)) (F : Finset ℕ),
      (∀ i, i ∈ F → IsOpen (U i)) ∧ S = (F : Set ℕ).pi U } :=
  isTopologicalBasis_pi fun _ => isTopologicalBasis_opens

/-- Morris, Topology Without Tears, Proposition 9.2.4 (TP-206). Projections of a countable product are
continuous, open, and (for nonempty factors) surjective; the product topology is the coarsest making
them continuous. -/
@[kb "morris2024" "Proposition 9.2.4, p. 226"]
theorem morris_9_2_4 {X : ℕ → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, Nonempty (X i)] :
    (∀ i, Continuous (fun x : ∀ j, X j => x i)) ∧ (∀ i, IsOpenMap (fun x : ∀ j, X j => x i)) ∧
    (∀ i, Function.Surjective (fun x : ∀ j, X j => x i)) ∧
    (∀ t : TopologicalSpace (∀ j, X j), (∀ i, @Continuous _ _ t _ (fun x : ∀ j, X j => x i)) →
      t ≤ Pi.topologicalSpace) :=
  ⟨fun i => continuous_apply i, fun i => isOpenMap_eval i, fun i => Function.surjective_eval i,
    fun _ h => le_iInf fun i => continuous_iff_le_induced.1 (h i)⟩

/-- Morris, Topology Without Tears, Proposition 9.2.5 (TP-207). A product of continuous maps between
countable products is continuous. -/
@[kb "morris2024" "Proposition 9.2.5, p. 227"]
theorem morris_9_2_5 {X Y : ℕ → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
    {h : ∀ i, X i → Y i} (hh : ∀ i, Continuous (h i)) : Continuous (Pi.map h) :=
  Continuous.piMap hh

/-- Morris, Topology Without Tears, Proposition 9.3.2 (TP-208). The Cantor set is homeomorphic to the
countable product of two-point discrete spaces. -/
@[kb "morris2024" "Proposition 9.3.2, p. 229"]
theorem morris_9_3_2 : Nonempty (cantorSet ≃ₜ (ℕ → Bool)) :=
  ⟨cantorSetHomeomorphNatToBool⟩

/-- Morris, Topology Without Tears, Proposition 9.3.5 (TP-210). The interval [0,1] is a continuous
image of the Cantor space. -/
@[kb "morris2024" "Proposition 9.3.5, p. 231"]
theorem morris_9_3_5 :
    ∃ f : (ℕ → Bool) → Icc (0 : ℝ) 1, Continuous f ∧ Function.Surjective f :=
  ⟨Real.fromBinary, Real.fromBinary_continuous, Real.fromBinary_surjective⟩

/-- Morris, Topology Without Tears, Theorem 9.3.8 (TP-212). The Hilbert cube is compact. -/
@[kb "morris2024" "Theorem 9.3.8, p. 232"]
theorem morris_9_3_8 : CompactSpace (ℕ → Icc (0 : ℝ) 1) :=
  inferInstance

/-- Morris, Topology Without Tears, Proposition 9.3.9 (TP-213). A countable product of metrizable
spaces is metrizable. -/
@[kb "morris2024" "Proposition 9.3.9, p. 233"]
theorem morris_9_3_9 {X : ℕ → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, MetrizableSpace (X i)] :
    MetrizableSpace (∀ i, X i) := by
  letI := fun i => metrizableSpaceMetric (X i)
  letI : MetricSpace (∀ i, X i) := PiCountable.metricSpace
  infer_instance

/-- Morris, Topology Without Tears, Corollary 9.3.10 (TP-214). The Hilbert cube is metrizable. -/
@[kb "morris2024" "Corollary 9.3.10, p. 234"]
theorem morris_9_3_10 : MetrizableSpace (ℕ → Icc (0 : ℝ) 1) :=
  morris_9_3_9

/-- Morris, Topology Without Tears, Proposition 9.3.11 (TP-215). A countable product of completely
metrizable spaces is completely metrizable. -/
@[kb "morris2024" "Proposition 9.3.11, p. 234"]
theorem morris_9_3_11 {X : ℕ → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, IsCompletelyMetrizableSpace (X i)] : IsCompletelyMetrizableSpace (∀ i, X i) :=
  inferInstance

/-- Morris, Topology Without Tears, Definition 9.4.1 (TP-216). A space is separable iff it has a
countable dense subset. -/
@[kb "morris2024" "Definition 9.4.1, p. 237"]
theorem morris_9_4_1 {X : Type*} [TopologicalSpace X] :
    SeparableSpace X ↔ ∃ s : Set X, s.Countable ∧ Dense s :=
  ⟨fun _ => exists_countable_dense X, fun ⟨s, hs, hd⟩ => ⟨⟨s, hs, hd⟩⟩⟩

/-- Morris, Topology Without Tears, Proposition 9.4.4 (TP-217). A compact metrizable space is
separable. -/
@[kb "morris2024" "Proposition 9.4.4, p. 237"]
theorem morris_9_4_4 {X : Type*} [TopologicalSpace X] [MetrizableSpace X] [CompactSpace X] :
    SeparableSpace X := by
  letI := metrizableSpaceMetric X
  infer_instance

/-- Morris, Topology Without Tears, Corollary 9.4.5 (TP-218). The Hilbert cube is separable. -/
@[kb "morris2024" "Corollary 9.4.5, p. 237"]
theorem morris_9_4_5 : SeparableSpace (ℕ → Icc (0 : ℝ) 1) :=
  inferInstance

/-- Morris, Topology Without Tears, Proposition 9.4.6 (TP-219). A map into a countable product is
continuous iff each coordinate is. -/
@[kb "morris2024" "Proposition 9.4.6, p. 238"]
theorem morris_9_4_6 {Z : Type*} {X : ℕ → Type*} [TopologicalSpace Z] [∀ i, TopologicalSpace (X i)]
    (f : Z → ∀ i, X i) : Continuous f ↔ ∀ i, Continuous (fun z => f z i) :=
  continuous_pi_iff

/-- Morris, Topology Without Tears, Definition 9.4.8 (TP-221). A space is T1 iff every singleton is
closed. -/
@[kb "morris2024" "Definition 9.4.8, p. 240"]
theorem morris_9_4_8 {X : Type*} [TopologicalSpace X] : T1Space X ↔ ∀ x : X, IsClosed ({x} : Set X) :=
  ⟨fun _ _ => isClosed_singleton, fun h => ⟨h⟩⟩

/-- Morris, Topology Without Tears, Theorem 9.4.11 (TP-222). A separable metric space embeds in the
Hilbert cube. -/
@[kb "morris2024" "Theorem 9.4.11, p. 241"]
theorem morris_9_4_11 {X : Type*} [MetricSpace X] [SeparableSpace X] :
    ∃ F : X → ℕ → Icc (0 : ℝ) 1, _root_.Topology.IsEmbedding F :=
  Metric.PiNatEmbed.exists_embedding_to_hilbert_cube

/-- Morris, Topology Without Tears, Corollary 9.4.13 (TP-224). A countable product of compact
metrizable spaces is compact and metrizable. -/
@[kb "morris2024" "Corollary 9.4.13, p. 241"]
theorem morris_9_4_13 {X : ℕ → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, MetrizableSpace (X i)]
    [∀ i, CompactSpace (X i)] : CompactSpace (∀ i, X i) ∧ MetrizableSpace (∀ i, X i) :=
  ⟨inferInstance, morris_9_3_9⟩

/-- Morris, Topology Without Tears, Definition 9.4.14 (TP-225). A space is second countable iff it has
a countable basis. -/
@[kb "morris2024" "Definition 9.4.14, p. 242"]
theorem morris_9_4_14 {X : Type*} [TopologicalSpace X] :
    SecondCountableTopology X ↔ ∃ B : Set (Set X), B.Countable ∧ IsTopologicalBasis B :=
  ⟨fun _ => let ⟨b, hb, _, h⟩ := exists_countable_basis X; ⟨b, hb, h⟩,
    fun ⟨_, hc, hb⟩ => hb.secondCountableTopology hc⟩

/-- Morris, Topology Without Tears, Proposition 9.4.17 (TP-226). A metric space is separable iff it is
second countable. -/
@[kb "morris2024" "Proposition 9.4.17, p. 242"]
theorem morris_9_4_17 {X : Type*} [PseudoMetricSpace X] :
    SeparableSpace X ↔ SecondCountableTopology X :=
  ⟨fun _ => UniformSpace.secondCountable_of_separable X, fun _ => inferInstance⟩

/-- Morris, Topology Without Tears, Theorem 9.4.19 (TP-227). A space is separable metrizable iff it is
homeomorphic to a subspace of the Hilbert cube (embeds in it). -/
@[kb "morris2024" "Theorem 9.4.19, p. 243"]
theorem morris_9_4_19 {X : Type*} [TopologicalSpace X] :
    (SeparableSpace X ∧ MetrizableSpace X) ↔ ∃ F : X → ℕ → Icc (0 : ℝ) 1, _root_.Topology.IsEmbedding F := by
  constructor
  · rintro ⟨h1, h2⟩
    letI := metrizableSpaceMetric X
    exact Metric.PiNatEmbed.exists_embedding_to_hilbert_cube
  · rintro ⟨F, hF⟩
    haveI : MetrizableSpace X := hF.metrizableSpace
    haveI : SecondCountableTopology X := hF.secondCountableTopology
    exact ⟨inferInstance, inferInstance⟩

/-- Morris, Topology Without Tears, Proposition 9.5.3 (TP-229). Every nonempty closed subset of the
Cantor space is a continuous image of the Cantor space. -/
@[kb "morris2024" "Proposition 9.5.3, p. 249"]
theorem morris_9_5_3 {A : Set (ℕ → Bool)} (hA : IsClosed A) (hne : A.Nonempty) :
    ∃ f : (ℕ → Bool) → (ℕ → Bool), Continuous f ∧ range f = A :=
  exists_retractionCantorSet hA hne

/-- Morris, Topology Without Tears, Theorem 9.5.4 (TP-230). Alexandroff-Urysohn: every nonempty
compact metrizable space is a continuous image of the Cantor space. -/
@[kb "morris2024" "Theorem 9.5.4, p. 251"]
theorem morris_9_5_4 {X : Type*} [TopologicalSpace X] [MetrizableSpace X] [CompactSpace X]
    [Nonempty X] : ∃ f : (ℕ → Bool) → X, Continuous f ∧ Function.Surjective f := by
  letI := metrizableSpaceMetric X
  exact exists_nat_bool_continuous_surjective_of_compact X

/-- Morris, Topology Without Tears, Definition 9.5.10 (TP-234). A space is locally connected iff every
point has arbitrarily small connected open neighbourhoods. -/
@[kb "morris2024" "Definition 9.5.10, p. 253"]
theorem morris_9_5_10 {X : Type*} [TopologicalSpace X] :
    LocallyConnectedSpace X ↔
      ∀ x : X, ∀ U : Set X, IsOpen U → x ∈ U → ∃ V : Set X, V ⊆ U ∧ IsOpen V ∧ x ∈ V ∧ IsConnected V := by
  rw [locallyConnectedSpace_iff_subsets_isOpen_isConnected]
  constructor
  · intro h x U hU hx
    exact h x U (hU.mem_nhds hx)
  · intro h x U hU
    obtain ⟨V, hVU, hVo, hxV, hc⟩ :=
      h x (interior U) isOpen_interior (mem_interior_iff_mem_nhds.2 hU)
    exact ⟨V, hVU.trans interior_subset, hVo, hxV, hc⟩

end UndergradKB.Topology.Course
