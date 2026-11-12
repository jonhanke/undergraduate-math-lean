import Mathlib.Topology.Compactness.CountablyCompact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Metrizable.CompletelyMetrizable
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Sequences
import UndergradKB.Common.Attr

/-!
# Compactness (Morris, Topology Without Tears, Chapters 7, 8 and 10)

Heine-Borel consequences on intervals, continua, compacta, relatively compact sets, supercompact,
countably compact and pseudocompact spaces, and the finite intersection property.
-/

namespace UndergradKB.Topology

open Set Filter TopologicalSpace

/-! ### Intervals -/

/-- Morris, Topology Without Tears, Corollary 7.2.3 (TP-166). For `a < b` the closed interval is
compact while the open interval is not. -/
@[kb "morris2024" "Corollary 7.2.3, p. 182"]
theorem isCompact_Icc_and_not_isCompact_Ioo {a b : ℝ} (h : a < b) :
    IsCompact (Icc a b) ∧ ¬ IsCompact (Ioo a b) := by
  refine ⟨isCompact_Icc, fun hc => ?_⟩
  have h1 : closure (Ioo a b) = Icc a b := closure_Ioo h.ne
  rw [hc.isClosed.closure_eq] at h1
  have : a ∈ Ioo a b := by rw [h1]; exact left_mem_Icc.2 h.le
  exact lt_irrefl _ this.1

/-- Morris, Topology Without Tears, Proposition 7.2.15 (TP-176). A continuous real function on a
closed interval `[a,b]` has as image a closed interval `[c,d]`. -/
@[kb "morris2024" "Proposition 7.2.15, p. 185"]
theorem image_Icc_eq_Icc_of_continuousOn {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) : ∃ c d : ℝ, c ≤ d ∧ f '' Icc a b = Icc c d := by
  have hne : (Icc a b).Nonempty := ⟨a, left_mem_Icc.2 hab⟩
  obtain ⟨x, hx, hxmin⟩ := isCompact_Icc.exists_isMinOn hne hf
  obtain ⟨y, hy, hymax⟩ := isCompact_Icc.exists_isMaxOn hne hf
  refine ⟨f x, f y, hxmin hy, ?_⟩
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨hxmin hz, hymax hz⟩
  · exact (isPreconnected_Icc.image f hf).Icc_subset (mem_image_of_mem f hx)
      (mem_image_of_mem f hy)

/-! ### Continua and compacta -/

/-- Morris, Topology Without Tears, Definition 8.4.7 (TP-193). A continuum is a compact connected
space (connected spaces are nonempty in Mathlib). -/
def IsContinuum (X : Type*) [TopologicalSpace X] : Prop :=
  CompactSpace X ∧ ConnectedSpace X

theorem isContinuum_iff {X : Type*} [TopologicalSpace X] :
    IsContinuum X ↔ CompactSpace X ∧ ConnectedSpace X := Iff.rfl

/-- Morris, Topology Without Tears, Definition 8.4.7 (TP-193). A space is a continuum iff
its whole set is a compact connected set. -/
@[kb "morris2024" "Definition 8.4.7, p. 216"]
theorem isContinuum_iff_isCompact_isConnected {X : Type*} [TopologicalSpace X] :
    IsContinuum X ↔ IsCompact (univ : Set X) ∧ IsConnected (univ : Set X) := by
  rw [IsContinuum, connectedSpace_iff_univ, ← isCompact_univ_iff]

/-- A continuous surjective image of a continuum is a continuum. -/
theorem IsContinuum.of_surjective {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (hX : IsContinuum X) {f : X → Y} (hf : Continuous f) (hs : Function.Surjective f) :
    IsContinuum Y :=
  have := hX.1
  have := hX.2
  ⟨Function.Surjective.compactSpace hf hs, hs.connectedSpace hf⟩

/-- Morris, Topology Without Tears, Proposition 8.4.8 (TP-194). A finite product of spaces is a
continuum iff each factor is a continuum. -/
@[kb "morris2024" "Proposition 8.4.8, p. 216"]
theorem isContinuum_pi_iff {ι : Type*} [Finite ι] {X : ι → Type*} [∀ i, TopologicalSpace (X i)] :
    IsContinuum (∀ i, X i) ↔ ∀ i, IsContinuum (X i) := by
  constructor
  · intro h i
    classical
    obtain ⟨x⟩ := h.2.toNonempty
    exact h.of_surjective (continuous_apply i) fun y => ⟨Function.update x i y, by simp⟩
  · intro h
    have : ∀ i, CompactSpace (X i) := fun i => (h i).1
    have : ∀ i, ConnectedSpace (X i) := fun i => (h i).2
    exact ⟨inferInstance, inferInstance⟩

/-- Morris, Topology Without Tears, Proposition 8.4.8 (TP-194), the book's form with factors
indexed by `Fin n`. -/
@[kb "morris2024" "Proposition 8.4.8, p. 216"]
theorem isContinuum_fin_pi_iff {n : ℕ} {X : Fin n → Type*} [∀ i, TopologicalSpace (X i)] :
    IsContinuum (∀ i, X i) ↔ ∀ i, IsContinuum (X i) :=
  isContinuum_pi_iff

/-- Morris, Topology Without Tears, Proposition 8.4.8 (TP-194), binary products. -/
theorem isContinuum_prod_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    IsContinuum (X × Y) ↔ IsContinuum X ∧ IsContinuum Y := by
  constructor
  · intro h
    obtain ⟨x, y⟩ := h.2.toNonempty
    exact ⟨h.of_surjective continuous_fst fun a => ⟨(a, y), rfl⟩,
      h.of_surjective continuous_snd fun b => ⟨(x, b), rfl⟩⟩
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    exact ⟨inferInstance, inferInstance⟩

/-- Morris, Topology Without Tears, §8.4 (TP-202). A compactum is a compact metrizable space. -/
def IsCompactum (X : Type*) [TopologicalSpace X] : Prop :=
  CompactSpace X ∧ MetrizableSpace X

/-- Morris, Topology Without Tears, §8.4 (TP-202). A space is a compactum iff some metric inducing
its topology makes it compact (i.e. iff it is compact and metrizable). -/
@[kb "morris2024" "Definition (compactum), p. 216"]
theorem isCompactum_iff {X : Type*} [TopologicalSpace X] :
    IsCompactum X ↔ CompactSpace X ∧ ∃ m : MetricSpace X, m.toUniformSpace.toTopologicalSpace =
      ‹TopologicalSpace X› := by
  refine and_congr_right fun hc => ?_
  constructor
  · intro h
    let := metrizableSpaceMetric X
    exact ⟨inferInstance, rfl⟩
  · rintro ⟨m, hm⟩
    subst hm
    infer_instance

/-- A compact metric space is a compactum. -/
theorem isCompactum_of_metric (X : Type*) [MetricSpace X] [CompactSpace X] : IsCompactum X :=
  ⟨inferInstance, inferInstance⟩

/-- A closed subspace of a compactum is a compactum. -/
theorem IsCompactum.closedSubspace {X : Type*} [TopologicalSpace X] (h : IsCompactum X)
    {s : Set X} (hs : IsClosed s) : IsCompactum s := by
  have := h.1
  have := h.2
  have : CompactSpace s := isCompact_iff_compactSpace.1 hs.isCompact
  exact ⟨inferInstance, inferInstance⟩

/-- A finite product of compacta is a compactum. -/
theorem isCompactum_pi {ι : Type*} [Finite ι] {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    (h : ∀ i, IsCompactum (X i)) : IsCompactum (∀ i, X i) := by
  have : ∀ i, CompactSpace (X i) := fun i => (h i).1
  have : ∀ i, MetrizableSpace (X i) := fun i => (h i).2
  exact ⟨inferInstance, inferInstance⟩

/-! ### Relatively compact sets -/

/-- Morris, Topology Without Tears, Exercises 7.2 #15 (TP-196). A subset is relatively compact
when its closure is compact. -/
def IsRelativelyCompact {X : Type*} [TopologicalSpace X] (A : Set X) : Prop :=
  IsCompact (closure A)

/-- In a Hausdorff space every compact set is relatively compact. -/
@[kb "morris2024" "Exercises 7.2, p. 189"]
theorem IsCompact.isRelativelyCompact {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X}
    (h : IsCompact A) : IsRelativelyCompact A := by
  unfold IsRelativelyCompact
  rwa [h.isClosed.closure_eq]

/-- In a Hausdorff space a subset of a compact set is relatively compact. -/
@[kb "morris2024" "Exercises 7.2, p. 189"]
theorem isRelativelyCompact_of_subset {X : Type*} [TopologicalSpace X] [T2Space X] {A B : Set X}
    (hB : IsCompact B) (h : A ⊆ B) : IsRelativelyCompact A :=
  hB.of_isClosed_subset isClosed_closure (closure_minimal h hB.isClosed)

/-- The open interval `(0,1)` is relatively compact in `ℝ`. -/
@[kb "morris2024" "Exercises 7.2, p. 189"]
theorem isRelativelyCompact_Ioo_zero_one : IsRelativelyCompact (Ioo (0 : ℝ) 1) :=
  isRelativelyCompact_of_subset isCompact_Icc Ioo_subset_Icc_self

/-- The integers are not a relatively compact subset of `ℝ`. -/
@[kb "morris2024" "Exercises 7.2, p. 189"]
theorem not_isRelativelyCompact_range_intCast : ¬ IsRelativelyCompact (range ((↑) : ℤ → ℝ)) := by
  intro h
  rw [IsRelativelyCompact, Int.isClosedEmbedding_coe_real.isClosed_range.closure_eq] at h
  obtain ⟨C, hC⟩ := h.isBounded.bddAbove
  have := hC ⟨⌈C⌉ + 1, rfl⟩
  have h2 := Int.le_ceil C
  push_cast at this
  linarith

/-- The rationals are not a relatively compact subset of `ℝ` (their closure is all of `ℝ`). -/
@[kb "morris2024" "Exercises 7.2, p. 189"]
theorem not_isRelativelyCompact_range_ratCast : ¬ IsRelativelyCompact (range ((↑) : ℚ → ℝ)) := by
  intro h
  rw [IsRelativelyCompact, Rat.denseRange_cast.closure_range] at h
  exact (NoncompactSpace.noncompact_univ (X := ℝ)) h

/-! ### Supercompact spaces -/

/-- Morris, Topology Without Tears, Exercises 7.2 #16 (TP-197). A space is supercompact if some
subbasis `S` for its topology is such that every cover of the space by members of `S` has a
subcover consisting of two members. -/
def IsSupercompact (X : Type*) [t : TopologicalSpace X] : Prop :=
  ∃ S : Set (Set X), t = generateFrom S ∧
    ∀ C ⊆ S, ⋃₀ C = univ → ∃ U ∈ C, ∃ V ∈ C, U ∪ V = univ

/-- A supercompact space is compact (Alexander's subbasis theorem). -/
@[kb "morris2024" "Exercises 7.2, p. 189"]
theorem IsSupercompact.compactSpace {X : Type*} [TopologicalSpace X] (h : IsSupercompact X) :
    CompactSpace X := by
  obtain ⟨S, hS, hC⟩ := h
  refine compactSpace_generateFrom hS fun P hP hU => ?_
  obtain ⟨U, hU, V, hV, hUV⟩ := hC P hP hU
  refine ⟨{U, V}, ?_, by simp, ?_⟩
  · intro x hx
    rcases hx with rfl | rfl
    · exact hU
    · exact hV
  · simpa [sUnion_pair] using hUV

/-! ### Countably compact spaces -/

/-- Morris, Topology Without Tears, Exercises 7.2 #17 (TP-198). Mathlib's `CountablyCompactSpace`
is the book's notion: every countable open cover has a finite subcover. -/
@[kb "morris2024" "Exercises 7.2, p. 190"]
theorem countablyCompactSpace_iff_countable_open_cover {X : Type*} [TopologicalSpace X] :
    CountablyCompactSpace X ↔ ∀ C : Set (Set X), C.Countable → (∀ U ∈ C, IsOpen U) →
      ⋃₀ C = univ → ∃ F ⊆ C, F.Finite ∧ ⋃₀ F = univ := by
  rw [← isCountablyCompact_univ_iff]
  constructor
  · intro h C hC ho hU
    obtain ⟨F, hF, hfin, hsub⟩ := h.elim_finite_subcover_image (U := id) hC
      (fun U hU => ho U hU) (by rw [← hU]; simp [sUnion_eq_biUnion])
    refine ⟨F, hF, hfin, ?_⟩
    apply eq_univ_of_univ_subset
    simpa [sUnion_eq_biUnion] using hsub
  · intro h
    rw [isCountablyCompact_iff_countable_open_cover]
    intro U hUo hcov
    obtain ⟨F, hF, hfin, hFU⟩ := h (range U) (countable_range U) (by rintro _ ⟨i, rfl⟩; exact hUo i)
      (by apply eq_univ_of_univ_subset; simpa [sUnion_range] using hcov)
    obtain ⟨T, -, hT, hTF⟩ := (exists_subset_image_finite_and (f := U) (s := univ)
      (p := fun T => ⋃₀ T = univ)).1 ⟨F, by simpa using hF, hfin, hFU⟩
    refine ⟨hT.toFinset, ?_⟩
    intro x _
    have : x ∈ ⋃₀ (U '' T) := by rw [hTF]; trivial
    simpa [sUnion_image] using this

/-- Every compact space is countably compact. -/
@[kb "morris2024" "Exercises 7.2, p. 190"]
theorem countablyCompactSpace_of_compactSpace {X : Type*} [TopologicalSpace X] [CompactSpace X] :
    CountablyCompactSpace X := inferInstance

/-- A metrizable space is countably compact iff it is compact. -/
@[kb "morris2024" "Exercises 7.2, p. 190"]
theorem countablyCompactSpace_iff_compactSpace_of_metrizable {X : Type*} [TopologicalSpace X]
    [MetrizableSpace X] :
    CountablyCompactSpace X ↔ CompactSpace X := by
  constructor
  · intro h
    have : SeqCompactSpace X := inferInstance
    exact compactSpace_iff_seqCompactSpace.2 this
  · intro h
    infer_instance

/-- A continuous image of a countably compact space is countably compact. -/
@[kb "morris2024" "Exercises 7.2, p. 190"]
theorem CountablyCompactSpace.of_surjective {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CountablyCompactSpace X] {f : X → Y} (hf : Continuous f) (hs : Function.Surjective f) :
    CountablyCompactSpace Y := by
  rw [← isCountablyCompact_univ_iff, ← hs.range_eq, ← image_univ]
  exact (isCountablyCompact_univ_iff.2 ‹_›).image hf

/-! ### Pseudocompact spaces -/

/-- Morris, Topology Without Tears, Exercises 7.2 #20 (TP-201). A space is pseudocompact if every
continuous real function on it is bounded. -/
def IsPseudocompactSpace (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ f : X → ℝ, Continuous f → ∃ C : ℝ, ∀ x, |f x| ≤ C

theorem exists_abs_le_of_isCompact_range {X : Type*} {f : X → ℝ} (h : IsCompact (range f)) :
    ∃ C : ℝ, ∀ x, |f x| ≤ C := by
  obtain ⟨M, hM⟩ := h.bddAbove
  obtain ⟨m, hm⟩ := h.bddBelow
  exact ⟨max M (-m), fun x => abs_le.2 ⟨by linarith [hm ⟨x, rfl⟩, le_max_right M (-m)],
    (hM ⟨x, rfl⟩).trans (le_max_left _ _)⟩⟩

/-- Every compact space is pseudocompact. -/
@[kb "morris2024" "Exercises 7.2, p. 191"]
theorem isPseudocompactSpace_of_compactSpace {X : Type*} [TopologicalSpace X] [CompactSpace X] :
    IsPseudocompactSpace X := fun _ hf => exists_abs_le_of_isCompact_range (isCompact_range hf)

/-- Every countably compact space is pseudocompact. -/
@[kb "morris2024" "Exercises 7.2, p. 191"]
theorem isPseudocompactSpace_of_countablyCompactSpace {X : Type*} [TopologicalSpace X]
    [CountablyCompactSpace X] : IsPseudocompactSpace X := fun f hf => by
  have h : IsCountablyCompact (range f) := by
    rw [← image_univ]
    exact CountablyCompactSpace.isCountablyCompact_univ.image hf
  exact exists_abs_le_of_isCompact_range h.isCompact

/-- A continuous image of a pseudocompact space is pseudocompact. -/
@[kb "morris2024" "Exercises 7.2, p. 191"]
theorem IsPseudocompactSpace.of_surjective {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (hX : IsPseudocompactSpace X) {f : X → Y} (hf : Continuous f) (hs : Function.Surjective f) :
    IsPseudocompactSpace Y := fun g hg => by
  obtain ⟨C, hC⟩ := hX (g ∘ f) (hg.comp hf)
  refine ⟨C, fun y => ?_⟩
  obtain ⟨x, rfl⟩ := hs y
  exact hC x

end UndergradKB.Topology
