import Mathlib.Topology.Constructions
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Instances.Irrational
import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.UpperLowerSetTopology
import Mathlib.Analysis.SpecificLimits.Basic
import UndergradKB.Common.Attr

/-! # Course layer, Morris: exercises of Chapters 1-3 (wave 4, part a)

Thin theorems for the standard facts that Morris, *Topology Without Tears*, sets as exercises in
Chapters 1 (topological spaces), 2 (the euclidean topology) and 3 (limit points).  The statements follow
the book; the proofs are Mathlib lemmas or a few lines.
-/

open _root_.Topology

namespace UndergradKB.Topology.Course

open Set Filter TopologicalSpace

section Chapter1

variable {X Y : Type*}

/-- Morris, Topology Without Tears, Exercises 1.1 #4. A finite intersection of open sets of a
topological space is open. -/
@[kb "morris2024" "Exercises 1.1 #4, p. 30"]
theorem morris_exercise_1_1_4 [TopologicalSpace X] (𝒰 : Set (Set X)) (h : 𝒰.Finite)
    (hU : ∀ U ∈ 𝒰, IsOpen U) : IsOpen (⋂₀ 𝒰) :=
  h.isOpen_sInter hU

/-- Two disjoint infinite subsets of the complement of a finite set (auxiliary). -/
private lemma two_infinite_disjoint [Infinite X] (F : Set X) (hF : F.Finite) :
    ∃ A B : Set X, A.Infinite ∧ B.Infinite ∧ A ∩ B ⊆ ∅ ∧ A ∩ F = ∅ ∧ B ∩ F = ∅ := by
  have hinf : Fᶜ.Infinite := hF.infinite_compl
  let f : ℕ ↪ (Fᶜ : Set X) := hinf.natEmbedding
  refine ⟨range fun n => (f (2 * n) : X), range fun n => (f (2 * n + 1) : X), ?_, ?_, ?_, ?_, ?_⟩
  · refine infinite_range_of_injective fun m n h => ?_
    have := f.injective (Subtype.ext h)
    omega
  · refine infinite_range_of_injective fun m n h => ?_
    have := f.injective (Subtype.ext h)
    omega
  · rintro x ⟨⟨m, rfl⟩, ⟨n, hn⟩⟩
    have := f.injective (Subtype.ext hn)
    omega
  · ext x
    simp only [mem_inter_iff, mem_range, mem_empty_iff_false, iff_false, not_and]
    rintro ⟨n, rfl⟩
    exact fun h => (f (2 * n)).2 h
  · ext x
    simp only [mem_inter_iff, mem_range, mem_empty_iff_false, iff_false, not_and]
    rintro ⟨n, rfl⟩
    exact fun h => (f (2 * n + 1)).2 h

/-- Morris, Topology Without Tears, Exercises 1.1 #8. On an infinite set, a topology in which every
infinite subset is open is the discrete topology. -/
@[kb "morris2024" "Exercises 1.1 #8, p. 31"]
theorem morris_exercise_1_1_8 [TopologicalSpace X] [Infinite X] (h : ∀ s : Set X, s.Infinite → IsOpen s) :
    DiscreteTopology X := by
  refine discreteTopology_iff_isOpen_singleton.2 fun x => ?_
  obtain ⟨A, B, hA, hB, hAB, hAF, hBF⟩ := two_infinite_disjoint ({x} : Set X) (finite_singleton x)
  have h1 : IsOpen (A ∪ {x}) := h _ (hA.mono subset_union_left)
  have h2 : IsOpen (B ∪ {x}) := h _ (hB.mono subset_union_left)
  convert h1.inter h2 using 1
  ext y
  simp only [mem_singleton_iff, mem_inter_iff, mem_union]
  constructor
  · rintro rfl; simp
  · rintro ⟨hy1 | hy1, hy2 | hy2⟩
    · exact absurd (hAB ⟨hy1, hy2⟩) (by simp)
    · exact hy2
    · exact hy1
    · exact hy1

/-- Morris, Topology Without Tears, Exercises 1.2 #2. If every subset of a topological space is
closed, the space is discrete. -/
@[kb "morris2024" "Exercises 1.2 #2, p. 36"]
theorem morris_exercise_1_2_2 [TopologicalSpace X] (h : ∀ s : Set X, IsClosed s) : DiscreteTopology X :=
  discreteTopology_iff_forall_isClosed.2 h

/-- Morris, Topology Without Tears, Exercises 1.2 #4. On an infinite set, a topology in which every
infinite subset is closed is the discrete topology. -/
@[kb "morris2024" "Exercises 1.2 #4, p. 37"]
theorem morris_exercise_1_2_4 [TopologicalSpace X] [Infinite X] (h : ∀ s : Set X, s.Infinite → IsClosed s) :
    DiscreteTopology X := by
  refine discreteTopology_iff_forall_isClosed.2 fun s => ?_
  by_cases hs : s.Infinite
  · exact h s hs
  · rw [not_infinite] at hs
    obtain ⟨A, B, hA, hB, hAB, hAF, hBF⟩ := two_infinite_disjoint s hs
    have h1 : IsClosed (A ∪ s) := h _ (hA.mono subset_union_left)
    have h2 : IsClosed (B ∪ s) := h _ (hB.mono subset_union_left)
    convert h1.inter h2 using 1
    ext y
    simp only [mem_inter_iff, mem_union]
    constructor
    · intro hy; exact ⟨Or.inr hy, Or.inr hy⟩
    · rintro ⟨hy1 | hy1, hy2 | hy2⟩
      · exact absurd (hAB ⟨hy1, hy2⟩) (by simp)
      · exact hy2
      · exact hy1
      · exact hy1

/-- Morris, Topology Without Tears, Exercises 1.3 #1(a). The inverse image of a union of subsets of
`Y` is the union of the inverse images. -/
@[kb "morris2024" "Exercises 1.3 #1(a), p. 44"]
theorem morris_exercise_1_3_1_a {J : Type*} (f : X → Y) (B : J → Set Y) :
    f ⁻¹' (⋃ j, B j) = ⋃ j, f ⁻¹' B j :=
  preimage_iUnion

/-- Morris, Topology Without Tears, Exercises 1.3 #1(b). The inverse image of an intersection of two
subsets of `Y` is the intersection of the inverse images. -/
@[kb "morris2024" "Exercises 1.3 #1(b), p. 44"]
theorem morris_exercise_1_3_1_b (f : X → Y) (B₁ B₂ : Set Y) : f ⁻¹' (B₁ ∩ B₂) = f ⁻¹' B₁ ∩ f ⁻¹' B₂ :=
  preimage_inter

/-- Morris, Topology Without Tears, Exercises 1.3 #3(i). Every discrete space is a T1-space. -/
@[kb "morris2024" "Exercises 1.3 #3(i), p. 44"]
theorem morris_exercise_1_3_3_i [TopologicalSpace X] [DiscreteTopology X] : T1Space X :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 1.3 #3(ii). An indiscrete space with at least two
points is not a T1-space. -/
@[kb "morris2024" "Exercises 1.3 #3(ii), p. 44"]
theorem morris_exercise_1_3_3_ii [TopologicalSpace X] (h : ∀ U : Set X, IsOpen U → U = ∅ ∨ U = univ)
    (a b : X) (hab : a ≠ b) : ¬ T1Space X := by
  intro hT
  have ho : IsOpen ({a}ᶜ : Set X) := isClosed_singleton.isOpen_compl
  rcases h _ ho with h0 | h0
  · exact (eq_empty_iff_forall_notMem.1 h0 b) (by simpa using hab.symm)
  · have : a ∈ ({a}ᶜ : Set X) := by rw [h0]; trivial
    exact this rfl

/-- Morris, Topology Without Tears, Exercises 1.3 #3(iii). A set with the finite-closed (cofinite)
topology is a T1-space. -/
@[kb "morris2024" "Exercises 1.3 #3(iii), p. 44"]
theorem morris_exercise_1_3_3_iii : T1Space (CofiniteTopology X) :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 1.3 #4. If the finite-closed topology on a set is
discrete, the set is finite. -/
@[kb "morris2024" "Exercises 1.3 #4, p. 45"]
theorem morris_exercise_1_3_4 (h : DiscreteTopology (CofiniteTopology X)) : Finite X := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x⟩⟩
  · exact Finite.of_subsingleton
  · have ho : IsOpen ({CofiniteTopology.of x} : Set (CofiniteTopology X)) := isOpen_discrete _
    have hfin := (CofiniteTopology.isOpen_iff.1 ho) (singleton_nonempty _)
    have : (univ : Set (CofiniteTopology X)).Finite := by
      have := hfin.union (finite_singleton (CofiniteTopology.of x))
      simpa using this
    exact (CofiniteTopology.of (X := X)).finite_iff.2 (finite_univ_iff.1 this)

/-- Morris, Topology Without Tears, Exercises 1.3 #5(i). Every T1-space is a T0-space. -/
@[kb "morris2024" "Exercises 1.3 #5(i), p. 45"]
theorem morris_exercise_1_3_5_i [TopologicalSpace X] [T1Space X] : T0Space X :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 1.3 #5(iii). The Sierpinski space `Prop`, whose open
sets are `∅`, `{True}` and the whole space, is a T0-space but not a T1-space. -/
@[kb "morris2024" "Exercises 1.3 #5(iii), p. 45"]
theorem morris_exercise_1_3_5_iii :
    @T0Space Prop sierpinskiSpace ∧ ¬ @T1Space Prop sierpinskiSpace := by
  let _ := sierpinskiSpace
  refine ⟨inferInstance, fun hT => ?_⟩
  have key : ∀ s : Set Prop, IsOpen s → False ∈ s → True ∈ s := by
    intro s hs
    induction hs with
    | basic u hu => rcases hu with rfl; simp
    | univ => intro _; trivial
    | inter a b _ _ iha ihb => exact fun h => ⟨iha h.1, ihb h.2⟩
    | sUnion S _ ih =>
      rintro ⟨t, ht, h⟩
      exact ⟨t, ht, ih t ht h⟩
  have ho : IsOpen ({True}ᶜ : Set Prop) := isClosed_singleton.isOpen_compl
  have := key _ ho (by simp)
  simp at this

/-- Morris, Topology Without Tears, Exercises 1.3 #6. On any set, the family of subsets that are
either the whole set or countable is the family of closed sets of a topology (the countable-closed
topology). -/
@[kb "morris2024" "Exercises 1.3 #6, p. 45"]
theorem morris_exercise_1_3_6 (X : Type*) :
    ∃ t : TopologicalSpace X, ∀ s : Set X, IsClosed[t] s ↔ (s = univ ∨ s.Countable) := by
  have h1 : (∅ : Set X) ∈ {s : Set X | s = univ ∨ s.Countable} := Or.inr countable_empty
  have h2 : ∀ A : Set (Set X), A ⊆ {s : Set X | s = univ ∨ s.Countable} →
      ⋂₀ A ∈ {s : Set X | s = univ ∨ s.Countable} := by
    intro A hA
    by_cases h : ∀ a ∈ A, a = univ
    · left
      exact sInter_eq_univ.2 h
    · push Not at h
      obtain ⟨a, ha, hne⟩ := h
      right
      exact ((hA ha).resolve_left hne).mono (sInter_subset_of_mem ha)
  have h3 : ∀ A ∈ {s : Set X | s = univ ∨ s.Countable}, ∀ B ∈ {s : Set X | s = univ ∨ s.Countable},
      A ∪ B ∈ {s : Set X | s = univ ∨ s.Countable} := by
    rintro a (rfl | ha) b (rfl | hb)
    · left; simp
    · left; simp
    · left; simp
    · exact Or.inr (ha.union hb)
  let t : TopologicalSpace X := TopologicalSpace.ofClosed _ h1 h2 h3
  refine ⟨t, fun s => ?_⟩
  refine (@isOpen_compl_iff X s t).symm.trans ?_
  change sᶜᶜ ∈ {s : Set X | s = univ ∨ s.Countable} ↔ _
  rw [compl_compl]
  rfl

/-- Morris, Topology Without Tears, Exercises 1.3 #7(ii). The intersection of two topologies on a set
is a topology; its open sets are the sets open in both (Mathlib's order on topologies has finer
topologies smaller, so the intersection is the supremum `⊔`). -/
@[kb "morris2024" "Exercises 1.3 #7(ii), p. 46"]
theorem morris_exercise_1_3_7_ii (t₁ t₂ : TopologicalSpace X) (s : Set X) :
    IsOpen[t₁ ⊔ t₂] s ↔ IsOpen[t₁] s ∧ IsOpen[t₂] s :=
  isOpen_sup

/-- Morris, Topology Without Tears, Exercises 1.3 #7(iii). If two topologies on a set are T1, so is
their intersection (in Mathlib's order, where finer topologies are smaller, the intersection of the
families of open sets is the supremum `⊔`). -/
@[kb "morris2024" "Exercises 1.3 #7(iii), p. 46"]
theorem morris_exercise_1_3_7_iii (t₁ t₂ : TopologicalSpace X) (h₁ : @T1Space X t₁) (h₂ : @T1Space X t₂) :
    @T1Space X (t₁ ⊔ t₂) := by
  refine @T1Space.mk X (t₁ ⊔ t₂) fun x => ?_
  rw [← @isOpen_compl_iff X _ (t₁ ⊔ t₂)]
  exact isOpen_sup.2 ⟨@isClosed_singleton X t₁ h₁ x |>.isOpen_compl, @isClosed_singleton X t₂ h₂ x |>.isOpen_compl⟩

end Chapter1

end UndergradKB.Topology.Course
