import Mathlib.Order.OrderIsoNat
import Mathlib.Order.Monotone.Basic
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.Instances.Rat
import Mathlib.Analysis.Normed.Field.Lemmas
import UndergradKB.Common.Attr

/-!
# Monotone subsequences, Souslin spaces, completions, Baire category

Morris, *Topology Without Tears* (2024), Chapter 6: every real sequence has a monotone subsequence
(peak points), Souslin spaces and analytic sets, extension of isometries between dense subspaces of
complete metric spaces, interior/exterior/boundary, `ℚ` is not a Baire space, and the complement of
a first category set in a Baire space.
-/

namespace UndergradKB.Topology

open Set Filter

/-! ### Monotone subsequences (TP-127) -/

/-- Morris, Topology Without Tears, Definition 6.3.7 (TP-127). An index `n₀` is a peak point of the
real sequence `x` if `x n ≤ x n₀` for all `n ≥ n₀`. -/
@[kb "morris2024" "Definition 6.3.7, p. 151"]
def IsPeakPoint (x : ℕ → ℝ) (n₀ : ℕ) : Prop := ∀ n, n₀ ≤ n → x n ≤ x n₀

/-- Morris, Topology Without Tears, Lemma 6.3.8 (TP-127), first case of the proof. If a real
sequence has infinitely many peak points, it has a decreasing subsequence (along peak points). -/
@[kb "morris2024" "Lemma 6.3.8, p. 151"]
theorem exists_antitone_subseq_of_infinite_peakPoints {x : ℕ → ℝ}
    (h : {n | IsPeakPoint x n}.Infinite) : ∃ φ : ℕ → ℕ, StrictMono φ ∧ Antitone (x ∘ φ) := by
  obtain ⟨φ, hφ, hP⟩ := Nat.exists_strictMono_subsequence (P := IsPeakPoint x) (fun N => by
    obtain ⟨n, hn, hN⟩ := h.exists_gt N
    exact ⟨n, hN, hn⟩)
  exact ⟨φ, hφ, fun m n hmn => hP m (φ n) (hφ.monotone hmn)⟩

/-- Morris, Topology Without Tears, Lemma 6.3.8 (TP-127). Every real sequence has a monotone
subsequence (increasing or decreasing). -/
@[kb "morris2024" "Lemma 6.3.8, p. 151"]
theorem exists_strictMono_subseq_monotone_or_antitone (x : ℕ → ℝ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ (Monotone (x ∘ φ) ∨ Antitone (x ∘ φ)) := by
  obtain ⟨g, h | h⟩ := exists_increasing_or_nonincreasing_subseq (α := ℝ) (· < ·) x
  · refine ⟨g, g.strictMono, Or.inl fun m n hmn => ?_⟩
    rcases hmn.lt_or_eq with hlt | rfl
    · exact (h m n hlt).le
    · exact le_rfl
  · refine ⟨g, g.strictMono, Or.inr fun m n hmn => ?_⟩
    rcases hmn.lt_or_eq with hlt | rfl
    · exact not_lt.1 (h m n hlt)
    · exact le_rfl

/-! ### Souslin spaces and analytic sets (TP-136, TP-137) -/

/-- Morris, Topology Without Tears, Definition 6.3.19 (TP-136). A Souslin space is a Hausdorff space
that is a continuous image of a Polish space. -/
@[kb "morris2024" "Definition 6.3.19, p. 155"]
def IsSouslinSpace (X : Type*) [TopologicalSpace X] : Prop :=
  T2Space X ∧ ∃ (P : Type) (t : TopologicalSpace P) (_ : @PolishSpace P t) (f : P → X),
    @Continuous P X t _ f ∧ Function.Surjective f

/-- Morris, Topology Without Tears, Definition 6.3.19 (TP-136). Every Polish space is a Souslin
space. -/
@[kb "morris2024" "Definition 6.3.19, p. 155"]
theorem PolishSpace.isSouslinSpace (X : Type) [TopologicalSpace X] [PolishSpace X] :
    IsSouslinSpace X :=
  ⟨inferInstance, X, inferInstance, inferInstance, id, continuous_id, Function.surjective_id⟩

/-- Morris, Topology Without Tears, Definition 6.3.19 (TP-136). Every countable Hausdorff space is a
Souslin space (it is a continuous image of the discrete space `ℕ`). -/
@[kb "morris2024" "Definition 6.3.19, p. 155"]
theorem isSouslinSpace_of_countable (X : Type*) [TopologicalSpace X] [T2Space X] [Countable X] :
    IsSouslinSpace X := by
  rcases isEmpty_or_nonempty X with h | h
  · exact ⟨inferInstance, Empty, inferInstance, inferInstance, Empty.elim,
      continuous_of_discreteTopology, fun x => h.elim x⟩
  · obtain ⟨f, hf⟩ := exists_surjective_nat X
    exact ⟨inferInstance, ℕ, inferInstance, inferInstance, f, continuous_of_discreteTopology, hf⟩

/-- Morris, Topology Without Tears, Definition 6.3.19 (TP-137). In a Hausdorff space, a subset is
analytic (Mathlib's `MeasureTheory.AnalyticSet`: empty or a continuous image of a Polish space) if
and only if it is a Souslin space in the subspace topology. -/
@[kb "morris2024" "Definition 6.3.19, p. 155"]
theorem analyticSet_iff_isSouslinSpace {α : Type*} [TopologicalSpace α] [T2Space α] (s : Set α) :
    MeasureTheory.AnalyticSet s ↔ IsSouslinSpace s := by
  constructor
  · intro h
    obtain ⟨β, tβ, hP, f, hc, hr⟩ := MeasureTheory.analyticSet_iff_exists_polishSpace_range.1 h
    let _ := tβ
    have := hP
    have hmem : ∀ b, f b ∈ s := fun b => by rw [← hr]; exact mem_range_self b
    refine ⟨inferInstance, β, tβ, hP, fun b => ⟨f b, hmem b⟩, hc.subtype_mk hmem, ?_⟩
    rintro ⟨y, hy⟩
    rw [← hr] at hy
    obtain ⟨b, rfl⟩ := hy
    exact ⟨b, rfl⟩
  · rintro ⟨_, β, tβ, hP, f, hc, hs⟩
    let _ := tβ
    have := hP
    have := MeasureTheory.analyticSet_range_of_polishSpace (continuous_subtype_val.comp hc)
    have e : Set.range (Subtype.val ∘ f) = s := by
      rw [Set.range_comp, hs.range_eq, Set.image_univ, Subtype.range_coe]
    rwa [e] at this

/-! ### Uniqueness of completions (TP-142) -/

/-- Extension of an isometry from a dense subset of a complete metric space `A` to a complete metric
space `B`, when the image is dense: the extension is an isometry of `A` onto `B`. -/
theorem exists_isometryEquiv_extend {A B : Type*} [MetricSpace A] [MetricSpace B] [CompleteSpace A]
    [CompleteSpace B] {X : Set A} (hX : Dense X) {f : X → B} (hf : Isometry f)
    (hd : DenseRange f) : ∃ g : A ≃ᵢ B, ∀ x : X, g x = f x := by
  have huc : UniformContinuous f := hf.uniformContinuous
  let g : A → B := hX.extend f
  have hg_ext : ∀ x : X, g x = f x := fun x => hX.extend_of_ind huc x
  have hgc : Continuous g := (hX.uniformContinuous_extend huc).continuous
  have h1 : ∀ a : A, ∀ x : X, dist (g a) (g (x : A)) = dist a (x : A) := by
    intro a x
    have hfun : (fun a : A => dist (g a) (g (x : A))) = fun a : A => dist a (x : A) := by
      refine Continuous.ext_on hX (hgc.dist continuous_const) (continuous_id.dist continuous_const) ?_
      intro y hy
      show dist (g y) (g (x : A)) = dist y (x : A)
      rw [show g y = f ⟨y, hy⟩ from hg_ext ⟨y, hy⟩, hg_ext x, hf.dist_eq]
      rfl
    exact congrFun hfun a
  have hiso : Isometry g := by
    refine Isometry.of_dist_eq fun a b => ?_
    have hfun : (fun b => dist (g a) (g b)) = fun b => dist a b := by
      refine Continuous.ext_on hX (continuous_const.dist hgc) (continuous_const.dist continuous_id) ?_
      intro y hy
      exact h1 a ⟨y, hy⟩
    exact congrFun hfun b
  have hclosed : IsClosed (range g) := hiso.isUniformInducing.isComplete_range.isClosed
  have hdense : Dense (range g) := by
    refine Dense.mono ?_ hd
    rintro _ ⟨x, rfl⟩
    exact ⟨x, hg_ext x⟩
  have hsurj : Function.Surjective g := by
    intro b
    have h2 := hdense.closure_eq
    rw [hclosed.closure_eq] at h2
    have : b ∈ range g := h2 ▸ mem_univ b
    exact this
  exact ⟨{ toEquiv := Equiv.ofBijective g ⟨hiso.injective, hsurj⟩, isometry_toFun := hiso },
    hg_ext⟩

/-- Morris, Topology Without Tears, Proposition 6.3.24 (TP-142). If `X` is dense in a complete metric
space `A`, `Y` is dense in a complete metric space `B`, and `f : X → Y` is an isometry (distance
preserving bijection), then `f` extends to an isometry of `A` onto `B`. -/
@[kb "morris2024" "Proposition 6.3.24, p. 159"]
theorem exists_isometryEquiv_extend_of_dense {A B : Type*} [MetricSpace A] [MetricSpace B]
    [CompleteSpace A] [CompleteSpace B] {X : Set A} {Y : Set B} (hX : Dense X) (hY : Dense Y)
    (f : X → Y) (hf : Isometry f) (hsurj : Function.Surjective f) :
    ∃ g : A ≃ᵢ B, ∀ x : X, g x = (f x : B) := by
  have hf' : Isometry (fun x : X => (f x : B)) := Isometry.of_dist_eq fun a b => hf.dist_eq a b
  have hd : DenseRange (fun x : X => (f x : B)) := by
    have : range (fun x : X => (f x : B)) = Y := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩; exact (f x).2
      · intro hy; obtain ⟨x, hx⟩ := hsurj ⟨y, hy⟩; exact ⟨x, congrArg Subtype.val hx⟩
    rw [DenseRange, this]
    exact hY
  exact exists_isometryEquiv_extend hX hf' hd

/-! ### Interior, exterior, boundary (TP-149) -/

/-- Morris, Topology Without Tears, Definition 6.5.2 (TP-149). The exterior of `A`, the interior of
its complement. (Mathlib's `exterior` is an unrelated notion, hence the different name.) -/
@[kb "morris2024" "Definition 6.5.2, p. 165"]
def bookExterior {X : Type*} [TopologicalSpace X] (A : Set X) : Set X := interior Aᶜ

/-- Morris, Topology Without Tears, Definition 6.5.2 (TP-149). The interior of `A` is its largest open
subset. -/
@[kb "morris2024" "Definition 6.5.2, p. 165"]
theorem isGreatest_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsGreatest {U : Set X | IsOpen U ∧ U ⊆ A} (interior A) :=
  ⟨⟨isOpen_interior, interior_subset⟩, fun _ hU => interior_maximal hU.2 hU.1⟩

/-- Morris, Topology Without Tears, Definition 6.5.2 (TP-149). The boundary of `A` (Mathlib's
`frontier`) is the closure of `A` minus the interior of `A`; this is the reading under which the
book's remark that `X` is the disjoint union of the interior, exterior and boundary holds (the printed
text has lost the closure bar). -/
@[kb "morris2024" "Definition 6.5.2, p. 165"]
theorem frontier_eq_closure_sdiff_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier A = closure A \ interior A := rfl

/-- Morris, Topology Without Tears, Definition 6.5.2 (TP-149). The exterior is the complement of the
closure. -/
theorem bookExterior_eq_compl_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    bookExterior A = (closure A)ᶜ := interior_compl

/-- Morris, Topology Without Tears, Definition 6.5.2 (TP-149). The space is the union of the interior,
the exterior and the boundary of `A`. -/
@[kb "morris2024" "Definition 6.5.2, p. 165"]
theorem interior_union_bookExterior_union_frontier {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior A ∪ bookExterior A ∪ frontier A = univ := by
  ext x
  simp only [mem_union, mem_univ, iff_true, bookExterior_eq_compl_closure, frontier_eq_closure_sdiff_interior,
    mem_compl_iff, Set.mem_sdiff]
  by_cases h1 : x ∈ interior A
  · exact Or.inl (Or.inl h1)
  · by_cases h2 : x ∈ closure A
    · exact Or.inr ⟨h2, h1⟩
    · exact Or.inl (Or.inr h2)

/-- Morris, Topology Without Tears, Definition 6.5.2 (TP-149). The interior, the exterior and the
boundary of `A` are pairwise disjoint. -/
@[kb "morris2024" "Definition 6.5.2, p. 165"]
theorem pairwise_disjoint_interior_bookExterior_frontier {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    Disjoint (interior A) (bookExterior A) ∧ Disjoint (interior A) (frontier A) ∧
      Disjoint (bookExterior A) (frontier A) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Set.disjoint_left]
    intro x hx hx'
    rw [bookExterior_eq_compl_closure] at hx'
    exact hx' (interior_subset.trans subset_closure hx)
  · rw [Set.disjoint_left]
    intro x hx hx'
    exact hx'.2 hx
  · rw [Set.disjoint_left]
    intro x hx hx'
    rw [bookExterior_eq_compl_closure] at hx
    exact hx hx'.1

/-! ### Baire category (TP-154, TP-157) -/

/-- Morris, Topology Without Tears, Example 6.5.8 (TP-154). The rationals are not a Baire space. -/
@[kb "morris2024" "Example 6.5.8, p. 167"]
theorem not_baireSpace_rat : ¬ BaireSpace ℚ := by
  intro h
  have hd := dense_iInter_of_isOpen (X := ℚ) (f := fun q : ℚ => ({q}ᶜ : Set ℚ))
    (fun q => isOpen_compl_singleton) (fun q => dense_compl_singleton q)
  have hempty : (⋂ q : ℚ, ({q}ᶜ : Set ℚ)) = ∅ := by
    ext x
    simp only [mem_iInter, mem_compl_iff, mem_singleton_iff, mem_empty_iff_false, iff_false, not_forall,
      not_not]
    exact ⟨x, rfl⟩
  rw [hempty] at hd
  exact (hd.nonempty).ne_empty rfl

/-- Morris, Topology Without Tears, Example 6.5.8 (TP-154). The rationals are not completely
metrizable (so, in particular, not a Polish space). -/
@[kb "morris2024" "Example 6.5.8, p. 167"]
theorem not_isCompletelyMetrizableSpace_rat : ¬ TopologicalSpace.IsCompletelyMetrizableSpace ℚ :=
  fun _ => not_baireSpace_rat inferInstance

/-- Morris, Topology Without Tears, Example 6.5.8 (TP-154). The rationals are not a Polish space. -/
@[kb "morris2024" "Example 6.5.8, p. 167"]
theorem not_polishSpace_rat : ¬ PolishSpace ℚ :=
  fun _ => not_isCompletelyMetrizableSpace_rat inferInstance

/-- Morris, Topology Without Tears, Corollary 6.5.12 (TP-157). In a (non-empty) Baire space the
complement of a first category (meagre) set is not of first category, i.e. is of second category. -/
@[kb "morris2024" "Corollary 6.5.12, p. 168"]
theorem not_isMeagre_compl_of_isMeagre {X : Type*} [TopologicalSpace X] [BaireSpace X]
    [Nonempty X] {Y : Set X} (hY : IsMeagre Y) : ¬ IsMeagre Yᶜ := by
  intro h
  have : IsMeagre (Set.univ : Set X) := by
    have := hY.union h
    rwa [Set.union_compl_self] at this
  exact not_isMeagre_of_isOpen isOpen_univ univ_nonempty this

/-- Morris, Topology Without Tears, Corollary 6.5.12 (TP-157), in the book's terms: if `Y` is a
countable union of nowhere dense sets in a non-empty Baire space, then `Yᶜ` is not contained in
a countable union of nowhere dense sets. -/
@[kb "morris2024" "Corollary 6.5.12, p. 168"]
theorem not_countable_union_nowhereDense_compl {X : Type*} [TopologicalSpace X] [BaireSpace X]
    [Nonempty X] {Y : Set X} {S : Set (Set X)} (hS : ∀ t ∈ S, IsNowhereDense t) (hc : S.Countable)
    (hY : Y ⊆ ⋃₀ S) :
    ¬ ∃ S' : Set (Set X), (∀ t ∈ S', IsNowhereDense t) ∧ S'.Countable ∧ Yᶜ ⊆ ⋃₀ S' :=
  fun h => not_isMeagre_compl_of_isMeagre (isMeagre_iff_countable_union_isNowhereDense.2
    ⟨S, hS, hc, hY⟩) (isMeagre_iff_countable_union_isNowhereDense.2 h)

end UndergradKB.Topology
