import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Metrizable.CompletelyMetrizable
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.MonotoneConvergence
import UndergradKB.Common.Attr

/-! # Course layer, Morris Chapter 6 (second half): completeness, Baire, normed spaces -/

open Filter Topology Set

namespace UndergradKB.Topology.Course

universe u

/-- Morris, Topology Without Tears, Definition 6.3.1 (TP-122). A sequence is Cauchy iff beyond some index
all pairs of terms are within any given `ε`. -/
@[kb "morris2024" "Definition 6.3.1, p. 149"]
theorem morris_6_3_1 {X : Type*} [MetricSpace X] (u : ℕ → X) :
    CauchySeq u ↔ ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, dist (u m) (u n) < ε :=
  Metric.cauchySeq_iff

/-- Morris, Topology Without Tears, Proposition 6.3.2 (TP-123). A convergent sequence in a metric space is
Cauchy. -/
@[kb "morris2024" "Proposition 6.3.2, p. 150"]
theorem morris_6_3_2 {X : Type*} [MetricSpace X] (u : ℕ → X) (x : X) (h : Tendsto u atTop (𝓝 x)) :
    CauchySeq u :=
  h.cauchySeq

/-- Morris, Topology Without Tears, Definition 6.3.4 (TP-124). A metric space is complete iff every Cauchy
sequence converges. -/
@[kb "morris2024" "Definition 6.3.4, p. 150"]
theorem morris_6_3_4 {X : Type*} [MetricSpace X] :
    CompleteSpace X ↔ ∀ u : ℕ → X, CauchySeq u → ∃ x, Tendsto u atTop (𝓝 x) :=
  ⟨fun _ _ hu => cauchySeq_tendsto_of_complete hu, Metric.complete_of_cauchySeq_tendsto⟩

/-- Morris, Topology Without Tears, Proposition 6.3.9 (TP-128). A monotone real sequence converges iff it is
bounded (increasing case: bounded above; the decreasing case is symmetric). -/
@[kb "morris2024" "Proposition 6.3.9, p. 152"]
theorem morris_6_3_9 (u : ℕ → ℝ) (hu : Monotone u) :
    (∃ l, Tendsto u atTop (𝓝 l)) ↔ BddAbove (range u) :=
  ⟨fun ⟨_, hl⟩ => hl.bddAbove_range, fun hb => ⟨_, tendsto_atTop_ciSup hu hb⟩⟩

/-- Morris, Topology Without Tears, Proposition 6.3.9 (TP-128), decreasing case. -/
@[kb "morris2024" "Proposition 6.3.9, p. 152"]
theorem morris_6_3_9_b (u : ℕ → ℝ) (hu : Antitone u) :
    (∃ l, Tendsto u atTop (𝓝 l)) ↔ BddBelow (range u) :=
  ⟨fun ⟨_, hl⟩ => hl.bddBelow_range, fun hb => ⟨_, tendsto_atTop_ciInf hu hb⟩⟩

/-- Morris, Topology Without Tears, Theorem 6.3.10 (TP-129), Bolzano-Weierstrass. A bounded real sequence has a
convergent subsequence. -/
@[kb "morris2024" "Theorem 6.3.10, p. 152"]
theorem morris_6_3_10 (u : ℕ → ℝ) (hb : ∃ M, ∀ n, |u n| ≤ M) :
    ∃ (φ : ℕ → ℕ) (l : ℝ), StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 l) := by
  obtain ⟨M, hM⟩ := hb
  obtain ⟨l, -, φ, hφ, h⟩ := tendsto_subseq_of_bounded (Metric.isBounded_closedBall (x := (0 : ℝ)) (r := M))
    (x := u) (fun n => by simpa [Real.dist_eq] using hM n)
  exact ⟨φ, l, hφ, h⟩

/-- Morris, Topology Without Tears, Corollary 6.3.11 (TP-130). The real line is complete. -/
@[kb "morris2024" "Corollary 6.3.11, p. 153"]
theorem morris_6_3_11 : CompleteSpace ℝ := inferInstance

/-- Morris, Topology Without Tears, Corollary 6.3.12 (TP-131). Euclidean space `ℝᵐ` is complete. -/
@[kb "morris2024" "Corollary 6.3.12, p. 154"]
theorem morris_6_3_12 (m : ℕ) : CompleteSpace (EuclideanSpace ℝ (Fin m)) := inferInstance

/-- Morris, Topology Without Tears, Proposition 6.3.13 (TP-132). A closed subset of a complete metric space is
complete. -/
@[kb "morris2024" "Proposition 6.3.13, p. 154"]
theorem morris_6_3_13 {X : Type*} [MetricSpace X] [CompleteSpace X] (A : Set X) (hA : IsClosed A) :
    CompleteSpace A :=
  hA.completeSpace_coe

/-- Morris, Topology Without Tears, Proposition 6.3.13 (TP-132). A complete subspace of a metric space is
closed. -/
@[kb "morris2024" "Proposition 6.3.13, p. 154"]
theorem morris_6_3_13_b {X : Type*} [MetricSpace X] (A : Set X) (hA : CompleteSpace A) : IsClosed A :=
  (completeSpace_coe_iff_isComplete.mp hA).isClosed

/-- Morris, Topology Without Tears, Definition 6.3.15 (TP-133). A space is completely metrizable iff some metric
inducing its topology is complete. -/
@[kb "morris2024" "Definition 6.3.15, p. 154"]
theorem morris_6_3_15 {X : Type*} [t : TopologicalSpace X] :
    TopologicalSpace.IsCompletelyMetrizableSpace X ↔
      ∃ m : MetricSpace X, m.toUniformSpace.toTopologicalSpace = t ∧
        @CompleteSpace X m.toUniformSpace :=
  ⟨fun h => h.complete, fun h => ⟨h⟩⟩

/-- Morris, Topology Without Tears, Definition 6.3.17 (TP-134). A space is separable iff it has a countable
dense subset. -/
@[kb "morris2024" "Definition 6.3.17, p. 155"]
theorem morris_6_3_17 {X : Type*} [TopologicalSpace X] :
    TopologicalSpace.SeparableSpace X ↔ ∃ s : Set X, s.Countable ∧ Dense s :=
  ⟨fun h => h.exists_countable_dense, fun h => ⟨h⟩⟩

/-- Morris, Topology Without Tears, Definition 6.3.20 (TP-138). A map between metric spaces is an isometry
iff it preserves distances; isometric spaces are linked by a surjective such map (an isometric equivalence). -/
@[kb "morris2024" "Definition 6.3.20, p. 156"]
theorem morris_6_3_20 {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) :
    Isometry f ↔ ∀ x y, dist (f x) (f y) = dist x y :=
  isometry_iff_dist_eq

/-- Morris, Topology Without Tears, Definition 6.3.21 (TP-139). An isometric embedding is a distance-preserving
map; it is injective and a topological embedding. -/
@[kb "morris2024" "Definition 6.3.21, p. 156"]
theorem morris_6_3_21 {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y)
    (hf : ∀ x y, dist (f x) (f y) = dist x y) :
    Function.Injective f ∧ IsEmbedding f :=
  ⟨(isometry_iff_dist_eq.mpr hf).injective, (isometry_iff_dist_eq.mpr hf).isEmbedding⟩

/-- Morris, Topology Without Tears, Definition 6.3.22 (TP-140). The canonical map into the completion of a
metric space is an isometric embedding with dense image into a complete metric space. -/
@[kb "morris2024" "Definition 6.3.22, p. 156"]
theorem morris_6_3_22 (X : Type*) [MetricSpace X] :
    CompleteSpace (UniformSpace.Completion X) ∧
      Isometry (fun x : X => (x : UniformSpace.Completion X)) ∧
      DenseRange (fun x : X => (x : UniformSpace.Completion X)) :=
  ⟨inferInstance, UniformSpace.Completion.coe_isometry, UniformSpace.Completion.denseRange_coe⟩

/-- Morris, Topology Without Tears, Proposition 6.3.23 (TP-141). Every metric space has a completion: a complete
metric space with an isometric embedding of dense image. -/
@[kb "morris2024" "Proposition 6.3.23, p. 158"]
theorem morris_6_3_23 (X : Type u) [MetricSpace X] :
    ∃ (Y : Type u) (_ : MetricSpace Y) (_ : CompleteSpace Y) (f : X → Y), Isometry f ∧ DenseRange f :=
  ⟨UniformSpace.Completion X, inferInstance, inferInstance, _, UniformSpace.Completion.coe_isometry,
    UniformSpace.Completion.denseRange_coe⟩

/-- Morris, Topology Without Tears, Definition 6.4.2 (TP-145). A contraction is a self-map with a constant
`r < 1` such that distances shrink by at least the factor `r`. -/
@[kb "morris2024" "Definition 6.4.2, p. 162"]
theorem morris_6_4_2 {X : Type*} [MetricSpace X] (f : X → X) :
    (∃ K : NNReal, ContractingWith K f) ↔
      ∃ r : ℝ, r < 1 ∧ 0 ≤ r ∧ ∀ x y, dist (f x) (f y) ≤ r * dist x y := by
  constructor
  · rintro ⟨K, hK, hf⟩
    exact ⟨K, hK, K.2, hf.dist_le_mul⟩
  · rintro ⟨r, hr, hr0, h⟩
    refine ⟨⟨r, hr0⟩, ?_, LipschitzWith.of_dist_le_mul h⟩
    exact_mod_cast hr

/-- Morris, Topology Without Tears, Proposition 6.4.3 (TP-146). A contraction mapping is continuous. -/
@[kb "morris2024" "Proposition 6.4.3, p. 162"]
theorem morris_6_4_3 {X : Type*} [MetricSpace X] (f : X → X) (K : NNReal) (hf : ContractingWith K f) :
    Continuous f :=
  hf.toLipschitzWith.continuous

/-- Morris, Topology Without Tears, Theorem 6.4.4 (TP-147), Contraction Mapping Theorem. A contraction of a
nonempty complete metric space has exactly one fixed point. -/
@[kb "morris2024" "Theorem 6.4.4, p. 163"]
theorem morris_6_4_4 {X : Type*} [MetricSpace X] [Nonempty X] [CompleteSpace X] (f : X → X) (K : NNReal)
    (hf : ContractingWith K f) : ∃! x, f x = x := by
  obtain ⟨x, hx, -⟩ := hf.exists_fixedPoint (Classical.arbitrary X) (edist_ne_top _ _)
  exact ⟨x, hx.eq, fun y hy => hf.eq_or_edist_eq_top_of_fixedPoints hy.symm.symm hx |>.resolve_right
    (edist_ne_top _ _)⟩

/-- Morris, Topology Without Tears, Theorem 6.5.1 (TP-148), Baire Category Theorem. In a complete metric space a
countable intersection of dense open sets is dense. -/
@[kb "morris2024" "Theorem 6.5.1, p. 165"]
theorem morris_6_5_1 {X : Type*} [MetricSpace X] [CompleteSpace X] (U : ℕ → Set X)
    (ho : ∀ n, IsOpen (U n)) (hd : ∀ n, Dense (U n)) : Dense (⋂ n, U n) :=
  dense_iInter_of_isOpen_nat ho hd

/-- Morris, Topology Without Tears, Definition 6.5.3 (TP-150). A set is nowhere dense iff its closure has empty
interior. -/
@[kb "morris2024" "Definition 6.5.3, p. 166"]
theorem morris_6_5_3 {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsNowhereDense A ↔ interior (closure A) = ∅ :=
  Iff.rfl

/-- Morris, Topology Without Tears, Corollary 6.5.4 (TP-151). A nonempty complete metric space is not a countable
union of nowhere dense sets. -/
@[kb "morris2024" "Corollary 6.5.4, p. 166"]
theorem morris_6_5_4 {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X] (A : ℕ → Set X)
    (hA : ∀ n, IsNowhereDense (A n)) : ⋃ n, A n ≠ univ := by
  intro h
  have hm : IsMeagre (⋃ n, A n) := by
    rw [isMeagre_iff_countable_union_isNowhereDense]
    refine ⟨range A, ?_, countable_range _, by simp [sUnion_range]⟩
    rintro _ ⟨n, rfl⟩
    exact hA n
  rw [h] at hm
  exact not_isMeagre_of_isOpen isOpen_univ univ_nonempty hm

/-- Morris, Topology Without Tears, Definition 6.5.5 (TP-152). A space is a Baire space iff every countable
family of dense open sets has dense intersection. -/
@[kb "morris2024" "Definition 6.5.5, p. 166"]
theorem morris_6_5_5 {X : Type*} [TopologicalSpace X] :
    BaireSpace X ↔ ∀ U : ℕ → Set X, (∀ n, IsOpen (U n)) → (∀ n, Dense (U n)) → Dense (⋂ n, U n) :=
  ⟨fun h _ ho hd => h.baire_property _ ho hd, fun h => ⟨fun U ho hd => h U ho hd⟩⟩

/-- Morris, Topology Without Tears, Corollary 6.5.6 (TP-153). Every completely metrizable space is a Baire
space. -/
@[kb "morris2024" "Corollary 6.5.6, p. 166"]
theorem morris_6_5_6 {X : Type*} [TopologicalSpace X] [TopologicalSpace.IsCompletelyMetrizableSpace X] :
    BaireSpace X :=
  inferInstance

/-- Morris, Topology Without Tears, Definition 6.5.10 (TP-155). A set is of first category (meagre) iff it is
contained in a countable union of nowhere dense sets. -/
@[kb "morris2024" "Definition 6.5.10, p. 167"]
theorem morris_6_5_10 {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsMeagre A ↔ ∃ S : Set (Set X), (∀ t ∈ S, IsNowhereDense t) ∧ S.Countable ∧ A ⊆ ⋃₀ S :=
  isMeagre_iff_countable_union_isNowhereDense

/-- Morris, Topology Without Tears, Proposition 6.5.11 (TP-156). In a Baire space a first category set has empty
interior. -/
@[kb "morris2024" "Proposition 6.5.11, p. 168"]
theorem morris_6_5_11 {X : Type*} [TopologicalSpace X] [BaireSpace X] (A : Set X) (hA : IsMeagre A) :
    interior A = ∅ := by
  by_contra h
  exact not_isMeagre_of_isOpen isOpen_interior (nonempty_iff_ne_empty.mpr h)
    (hA.mono interior_subset)

/-- Morris, Topology Without Tears, Theorem 6.5.15 (TP-159), Open Mapping Theorem. A continuous linear
surjection between Banach spaces is an open map. -/
@[kb "morris2024" "Theorem 6.5.15, p. 169"]
theorem morris_6_5_15 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (T : E →L[ℝ] F)
    (hT : Function.Surjective T) : IsOpenMap T :=
  ContinuousLinearMap.isOpenMap T hT

/-- Morris, Topology Without Tears, Corollary 6.5.16 (TP-160). A bijective continuous linear map between Banach
spaces is a homeomorphism. -/
@[kb "morris2024" "Corollary 6.5.16, p. 170"]
theorem morris_6_5_16 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (T : E →L[ℝ] F)
    (hT : Function.Bijective T) : ∃ h : E ≃ₜ F, ⇑h = T := by
  let e := ContinuousLinearEquiv.ofBijective T (LinearMap.ker_eq_bot.mpr hT.1)
    (LinearMap.range_eq_top.mpr hT.2)
  exact ⟨e.toHomeomorph, rfl⟩

end UndergradKB.Topology.Course
