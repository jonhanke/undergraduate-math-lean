import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Separation.Hausdorff
import UndergradKB.Common.Attr

/-! # Course layer, Morris Chapter 7: compactness -/

open Filter Topology Set Metric

namespace UndergradKB.Topology.Course

universe u

/-- Morris, Topology Without Tears, Definition 7.1.1 (TP-161). A subset `A` is compact iff every cover of `A` by
open sets has a finite subcover. -/
@[kb "morris2024" "Definition 7.1.1, p. 177"]
theorem morris_7_1_1 {X : Type u} [TopologicalSpace X] (A : Set X) :
    IsCompact A ↔ ∀ {ι : Type u} (U : ι → Set X), (∀ i, IsOpen (U i)) → A ⊆ ⋃ i, U i →
      ∃ t : Finset ι, A ⊆ ⋃ i ∈ t, U i :=
  isCompact_iff_finite_subcover

/-- Morris, Topology Without Tears, Definition 7.1.6 (TP-161). A space is compact iff every open cover of the
whole space has a finite subcover. -/
@[kb "morris2024" "Definition 7.1.6, p. 178"]
theorem morris_7_1_6 {X : Type u} [TopologicalSpace X] :
    CompactSpace X ↔ ∀ {ι : Type u} (U : ι → Set X), (∀ i, IsOpen (U i)) → (⋃ i, U i) = univ →
      ∃ t : Finset ι, (⋃ i ∈ t, U i) = univ := by
  rw [← isCompact_univ_iff, isCompact_iff_finite_subcover]
  simp only [univ_subset_iff]

/-- Morris, Topology Without Tears, Remark 7.1.8 (TP-162). A subset is compact in `X` iff it is compact as a
subspace. -/
@[kb "morris2024" "Remark 7.1.8, p. 178"]
theorem morris_7_1_8 {X : Type*} [TopologicalSpace X] (A : Set X) : IsCompact A ↔ CompactSpace A :=
  isCompact_iff_compactSpace

/-- Morris, Topology Without Tears, Example 7.1.3 (TP-163). Every finite subset of a space is compact. -/
@[kb "morris2024" "Example 7.1.3, p. 177"]
theorem morris_7_1_3 {X : Type*} [TopologicalSpace X] (A : Set X) (hA : A.Finite) : IsCompact A :=
  hA.isCompact

/-- Morris, Topology Without Tears, Example 7.1.5 (TP-163). In a discrete space a subset is compact iff it is
finite. -/
@[kb "morris2024" "Example 7.1.5, p. 177"]
theorem morris_7_1_5 {X : Type*} [TopologicalSpace X] [DiscreteTopology X] (A : Set X) :
    IsCompact A ↔ A.Finite :=
  isCompact_iff_finite

/-- Morris, Topology Without Tears, Proposition 7.1.9 (TP-164). The closed interval `[0, 1]` is compact. -/
@[kb "morris2024" "Proposition 7.1.9, p. 179"]
theorem morris_7_1_9 : IsCompact (Icc (0 : ℝ) 1) :=
  isCompact_Icc

/-- Morris, Topology Without Tears, Proposition 7.2.1 (TP-165). The image of a compact space under a continuous
map is compact (the image `f '' A` of a compact subset). -/
@[kb "morris2024" "Proposition 7.2.1, p. 181"]
theorem morris_7_2_1 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) (hf : Continuous f)
    (A : Set X) (hA : IsCompact A) : IsCompact (f '' A) :=
  hA.image hf

/-- Morris, Topology Without Tears, Corollary 7.2.2 (TP-165). A continuous surjection from a compact space has
compact codomain. -/
@[kb "morris2024" "Corollary 7.2.2, p. 181"]
theorem morris_7_2_2 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] (f : X → Y)
    (hf : Continuous f) (hs : Function.Surjective f) : CompactSpace Y :=
  hs.compactSpace hf

/-- Morris, Topology Without Tears, Proposition 7.2.4 (TP-167). A closed subset of a compact space is compact. -/
@[kb "morris2024" "Proposition 7.2.4, p. 182"]
theorem morris_7_2_4 {X : Type*} [TopologicalSpace X] [CompactSpace X] (A : Set X) (hA : IsClosed A) :
    IsCompact A :=
  hA.isCompact

/-- Morris, Topology Without Tears, Proposition 7.2.5 (TP-168). A compact subset of a Hausdorff space is
closed. -/
@[kb "morris2024" "Proposition 7.2.5, p. 183"]
theorem morris_7_2_5 {X : Type*} [TopologicalSpace X] [T2Space X] (A : Set X) (hA : IsCompact A) :
    IsClosed A :=
  hA.isClosed

/-- Morris, Topology Without Tears, Corollary 7.2.6 (TP-168). A compact subset of a metric space is closed. -/
@[kb "morris2024" "Corollary 7.2.6, p. 183"]
theorem morris_7_2_6 {X : Type*} [MetricSpace X] (A : Set X) (hA : IsCompact A) : IsClosed A :=
  hA.isClosed

/-- Morris, Topology Without Tears, Proposition 7.2.8 (TP-170). A compact subset of `ℝ` is bounded. -/
@[kb "morris2024" "Proposition 7.2.8, p. 183"]
theorem morris_7_2_8 (A : Set ℝ) (hA : IsCompact A) : ∃ M : ℝ, ∀ x ∈ A, |x| ≤ M := by
  obtain ⟨M, hM⟩ := hA.isBounded.subset_closedBall 0
  exact ⟨M, fun x hx => by simpa [Real.dist_eq] using hM hx⟩

/-- Morris, Topology Without Tears, Theorem 7.2.9 (TP-171), Heine-Borel. A closed bounded subset of `ℝ` is
compact. -/
@[kb "morris2024" "Theorem 7.2.9, p. 183"]
theorem morris_7_2_9 (A : Set ℝ) (hc : IsClosed A) (hb : Bornology.IsBounded A) : IsCompact A :=
  Metric.isCompact_of_isClosed_isBounded hc hb

/-- Morris, Topology Without Tears, Proposition 7.2.10 (TP-171). A compact subset of `ℝ` is closed and
bounded. -/
@[kb "morris2024" "Proposition 7.2.10, p. 184"]
theorem morris_7_2_10 (A : Set ℝ) (hA : IsCompact A) : IsClosed A ∧ Bornology.IsBounded A :=
  ⟨hA.isClosed, hA.isBounded⟩

/-- Morris, Topology Without Tears, Definition 7.2.11 (TP-172). A subset of a metric space is bounded iff its
pairwise distances are uniformly bounded. -/
@[kb "morris2024" "Definition 7.2.11, p. 184"]
theorem morris_7_2_11 {X : Type*} [MetricSpace X] (A : Set X) :
    Bornology.IsBounded A ↔ ∃ C : ℝ, ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ C :=
  Metric.isBounded_iff

/-- Morris, Topology Without Tears, Proposition 7.2.12 (TP-173). A compact subset of a metric space is closed and
bounded. -/
@[kb "morris2024" "Proposition 7.2.12, p. 184"]
theorem morris_7_2_12 {X : Type*} [MetricSpace X] (A : Set X) (hA : IsCompact A) :
    IsClosed A ∧ Bornology.IsBounded A :=
  ⟨hA.isClosed, hA.isBounded⟩

/-- Morris, Topology Without Tears, Theorem 7.2.13 (TP-174), generalized Heine-Borel. A subset of Euclidean
space `ℝⁿ` is compact iff it is closed and bounded. -/
@[kb "morris2024" "Theorem 7.2.13, p. 185"]
theorem morris_7_2_13 (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n))) :
    IsCompact A ↔ IsClosed A ∧ Bornology.IsBounded A :=
  Metric.isCompact_iff_isClosed_bounded

/-- Morris, Topology Without Tears, Proposition 7.2.14 (TP-175). A continuous real function on a nonempty compact
space attains a least and a greatest value. -/
@[kb "morris2024" "Proposition 7.2.14, p. 185"]
theorem morris_7_2_14 {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X] (f : X → ℝ)
    (hf : Continuous f) : (∃ a, ∀ x, f a ≤ f x) ∧ ∃ b, ∀ x, f x ≤ f b := by
  obtain ⟨a, -, ha⟩ := isCompact_univ.exists_isMinOn univ_nonempty hf.continuousOn
  obtain ⟨b, -, hb⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hf.continuousOn
  exact ⟨⟨a, fun x => ha (mem_univ x)⟩, ⟨b, fun x => hb (mem_univ x)⟩⟩

/-- Morris, Topology Without Tears, Section 7.2 (TP-199). A space is locally compact (weak form, as in the book)
iff each point has a compact neighbourhood. -/
@[kb "morris2024" "Definition 7.2, p. 190"]
theorem morris_7_2_locallyCompact {X : Type*} [TopologicalSpace X] :
    WeaklyLocallyCompactSpace X ↔ ∀ x : X, ∃ K : Set X, IsCompact K ∧ K ∈ 𝓝 x :=
  ⟨fun h => h.exists_compact_mem_nhds, fun h => ⟨h⟩⟩

/-- Morris, Topology Without Tears, Section 7.2 (TP-200). A space is sequentially compact iff every sequence has
a convergent subsequence. -/
@[kb "morris2024" "Definition 7.2, p. 191"]
theorem morris_7_2_seqCompact {X : Type*} [TopologicalSpace X] :
    SeqCompactSpace X ↔ ∀ u : ℕ → X, ∃ (x : X) (φ : ℕ → ℕ), StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 x) := by
  constructor
  · intro h u
    obtain ⟨x, -, φ, hφ, hx⟩ := h.isSeqCompact_univ (fun n => mem_univ (u n))
    exact ⟨x, φ, hφ, hx⟩
  · intro h
    refine ⟨fun u _ => ?_⟩
    obtain ⟨x, φ, hφ, hx⟩ := h u
    exact ⟨x, mem_univ x, φ, hφ, hx⟩

end UndergradKB.Topology.Course
