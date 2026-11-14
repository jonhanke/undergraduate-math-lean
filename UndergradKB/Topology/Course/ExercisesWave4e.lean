import Mathlib.Topology.Constructions
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Instances.RatLemmas
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Bases
import Mathlib.Topology.Sequences
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Order.IntermediateValue
import UndergradKB.Common.Attr

/-! # Course layer, Morris: exercises of Chapter 5 (wave 4, part e)

Thin theorems for standard facts that Morris, *Topology Without Tears*, sets as exercises in Chapter 5
(continuous mappings, the intermediate value theorem, path-connectedness, components and totally
disconnected spaces).
-/

open _root_.Topology

namespace UndergradKB.Topology.Course

open Set Filter TopologicalSpace

section Chapter5

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Morris, Topology Without Tears, Exercises 5.1 #5. A map is continuous iff the inverse image of
every member of a basis of the target is open. -/
@[kb "morris2024" "Exercises 5.1 #5, p. 116"]
theorem morris_exercise_5_1_5 {B : Set (Set Y)} (hB : IsTopologicalBasis B) (f : X → Y) :
    Continuous f ↔ ∀ U ∈ B, IsOpen (f ⁻¹' U) :=
  hB.continuous_iff

/-- Morris, Topology Without Tears, Exercises 5.1 #6. Every map out of a discrete space is
continuous. -/
@[kb "morris2024" "Exercises 5.1 #6, p. 116"]
theorem morris_exercise_5_1_6 [DiscreteTopology X] (f : X → Y) : Continuous f :=
  continuous_of_discreteTopology

/-- Morris, Topology Without Tears, Exercises 5.1 #7. Every map into an indiscrete space is
continuous. -/
@[kb "morris2024" "Exercises 5.1 #7, p. 116"]
theorem morris_exercise_5_1_7 (h : ∀ U : Set Y, IsOpen U → U = ∅ ∨ U = univ) (f : X → Y) :
    Continuous f := by
  refine continuous_def.2 fun U hU => ?_
  rcases h U hU with rfl | rfl
  · rw [preimage_empty]; exact isOpen_empty
  · rw [preimage_univ]; exact isOpen_univ

/-- Morris, Topology Without Tears, Exercises 5.1 #8. The restriction of a continuous map `f` to a
subset `A`, as a map `A → f(A)` between subspaces, is continuous. -/
@[kb "morris2024" "Exercises 5.1 #8, p. 116"]
theorem morris_exercise_5_1_8 {f : X → Y} (hf : Continuous f) (A : Set X) :
    Continuous ((mapsTo_image f A).restrict f A (f '' A)) :=
  hf.restrict _

/-- Morris, Topology Without Tears, Exercises 5.1 #9. A map `f` is continuous iff for every point `x`
and every neighbourhood `N` of `f x` there is a neighbourhood `M` of `x` with `f '' M ⊆ N`. -/
@[kb "morris2024" "Exercises 5.1 #9, p. 116"]
theorem morris_exercise_5_1_9 (f : X → Y) :
    Continuous f ↔ ∀ x, ∀ N ∈ 𝓝 (f x), ∃ M ∈ 𝓝 x, f '' M ⊆ N := by
  rw [continuous_iff_continuousAt]
  refine forall_congr' fun x => ?_
  rw [ContinuousAt, tendsto_def]
  constructor
  · intro h N hN
    exact ⟨f ⁻¹' N, h N hN, image_preimage_subset f N⟩
  · intro h N hN
    obtain ⟨M, hM, hMN⟩ := h N hN
    exact mem_of_superset hM (image_subset_iff.1 hMN)

/-- Morris, Topology Without Tears, Exercises 5.1 #10(i). The euclidean topology on `ℝ` is finer than
the finite-closed topology: the identity map from `ℝ` to `ℝ` with the finite-closed topology is
continuous. -/
@[kb "morris2024" "Exercises 5.1 #10(i), p. 116"]
theorem morris_exercise_5_1_10_i : Continuous (CofiniteTopology.of : ℝ → CofiniteTopology ℝ) := by
  refine continuous_def.2 fun U hU => ?_
  by_cases hne : (CofiniteTopology.of ⁻¹' U).Nonempty
  · have h1 : U.Nonempty := by
      obtain ⟨x, hx⟩ := hne
      exact ⟨_, hx⟩
    have h2 := (CofiniteTopology.isOpen_iff.1 hU) h1
    have h3 : (CofiniteTopology.of ⁻¹' Uᶜ).Finite :=
      h2.preimage (CofiniteTopology.of.injective.injOn)
    have h4 := h3.isClosed.isOpen_compl
    rwa [← preimage_compl, compl_compl] at h4
  · rw [not_nonempty_iff_eq_empty] at hne
    rw [hne]; exact isOpen_empty

/-- Morris, Topology Without Tears, Exercises 5.1 #10(ii). The identity map `(X, τ₁) → (X, τ₂)` is
continuous iff `τ₁` is finer than `τ₂` (every `τ₂`-open set is `τ₁`-open). -/
@[kb "morris2024" "Exercises 5.1 #10(ii), p. 116"]
theorem morris_exercise_5_1_10_ii {Z : Type*} (t₁ t₂ : TopologicalSpace Z) :
    Continuous[t₁, t₂] (id : Z → Z) ↔ ∀ U : Set Z, IsOpen[t₂] U → IsOpen[t₁] U :=
  continuous_def

/-- Morris, Topology Without Tears, Exercises 5.1 #11. A continuous function `ℝ → ℝ` vanishing at all
rational numbers is identically zero. -/
@[kb "morris2024" "Exercises 5.1 #11, p. 117"]
theorem morris_exercise_5_1_11 {f : ℝ → ℝ} (hf : Continuous f) (h : ∀ q : ℚ, f q = 0) : ∀ x, f x = 0 := by
  intro x
  have := hf.ext_on (g := fun _ => (0 : ℝ)) (s := range ((↑) : ℚ → ℝ)) Rat.denseRange_cast
    continuous_const (by rintro _ ⟨q, rfl⟩; exact h q)
  exact congrFun this x

/-- Morris, Topology Without Tears, Exercises 5.1 #12(i). If `f` is a continuous injection into a
Hausdorff space, the domain is Hausdorff. -/
@[kb "morris2024" "Exercises 5.1 #12(i), p. 117"]
theorem morris_exercise_5_1_12_i [T2Space Y] {f : X → Y} (hf : Continuous f) (hinj : Function.Injective f) :
    T2Space X :=
  T2Space.of_injective_continuous hinj hf

/-- Morris, Topology Without Tears, Exercises 5.1 #12(ii). If `f` is a continuous injection into a
T1-space, the domain is a T1-space. -/
@[kb "morris2024" "Exercises 5.1 #12(ii), p. 117"]
theorem morris_exercise_5_1_12_ii [T1Space Y] {f : X → Y} (hf : Continuous f) (hinj : Function.Injective f) :
    T1Space X :=
  t1Space_of_injective_of_continuous hinj hf

/-- Morris, Topology Without Tears, Exercises 5.1 #13. A map `f` is continuous iff
`f(closure A) ⊆ closure (f A)` for every subset `A`. -/
@[kb "morris2024" "Exercises 5.1 #13, p. 117"]
theorem morris_exercise_5_1_13 (f : X → Y) : Continuous f ↔ ∀ A : Set X, f '' closure A ⊆ closure (f '' A) :=
  continuous_iff_image_closure_subset_closure_image

/-- Morris, Topology Without Tears, Exercises 5.2 #1. A continuous image of a path-connected space is
path-connected. -/
@[kb "morris2024" "Exercises 5.2 #1, p. 120"]
theorem morris_exercise_5_2_1 {F : Set X} (hF : IsPathConnected F) {f : X → Y} (hf : Continuous f) :
    IsPathConnected (f '' F) :=
  hF.image hf

/-- Morris, Topology Without Tears, Exercises 5.2 #2. A continuous map of a closed interval `[a, b]`
into itself has a fixed point. -/
@[kb "morris2024" "Exercises 5.2 #2, p. 120"]
theorem morris_exercise_5_2_2 {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (hmaps : MapsTo f (Icc a b) (Icc a b)) : ∃ c ∈ Icc a b, f c = c :=
  exists_mem_Icc_isFixedPt hf hab.le (hmaps (left_mem_Icc.2 hab.le)).1
    (hmaps (right_mem_Icc.2 hab.le)).2

/-- Morris, Topology Without Tears, Exercises 5.2 #3(v). The fixed-point property is invariant under
homeomorphism. -/
@[kb "morris2024" "Exercises 5.2 #3(v), p. 120"]
theorem morris_exercise_5_2_3_v (h : X ≃ₜ Y) (hX : ∀ g : X → X, Continuous g → ∃ x, g x = x) :
    ∀ g : Y → Y, Continuous g → ∃ y, g y = y := by
  intro g hg
  obtain ⟨x, hx⟩ := hX (h.symm ∘ g ∘ h) (by fun_prop)
  refine ⟨h x, ?_⟩
  have : g (h x) = h (h.symm (g (h x))) := (h.apply_symm_apply _).symm
  rw [this, show h.symm (g (h x)) = x from hx]

/-- Morris, Topology Without Tears, Exercises 5.2 #4. The union of a family of connected subspaces with
a common point is connected. -/
@[kb "morris2024" "Exercises 5.2 #4, p. 121"]
theorem morris_exercise_5_2_4 {J : Type*} {A : J → Set X} (hA : ∀ j, IsPreconnected (A j))
    (hne : (⋂ j, A j).Nonempty) : IsPreconnected (⋃ j, A j) :=
  isPreconnected_iUnion hne hA

/-- Morris, Topology Without Tears, Exercises 5.2 #5. If `A` is connected and `A ⊆ B ⊆ closure A`, then
`B` is connected. -/
@[kb "morris2024" "Exercises 5.2 #5, p. 121"]
theorem morris_exercise_5_2_5 {A B : Set X} (hA : IsPreconnected A) (h₁ : A ⊆ B) (h₂ : B ⊆ closure A) :
    IsPreconnected B :=
  hA.subset_closure h₁ h₂

/-- Morris, Topology Without Tears, Exercises 5.2 #9(i). The component of a point is connected. -/
@[kb "morris2024" "Exercises 5.2 #9(i), p. 121"]
theorem morris_exercise_5_2_9_i (x : X) : IsConnected (connectedComponent x) :=
  isConnected_connectedComponent

/-- Morris, Topology Without Tears, Exercises 5.2 #9(ii). The component of `x` is the largest connected
set containing `x`. -/
@[kb "morris2024" "Exercises 5.2 #9(ii), p. 121"]
theorem morris_exercise_5_2_9_ii (x : X) {S : Set X} (hS : IsPreconnected S) (hx : x ∈ S) :
    S ⊆ connectedComponent x :=
  hS.subset_connectedComponent hx

/-- Morris, Topology Without Tears, Exercises 5.2 #9(iii). The component of a point is closed. -/
@[kb "morris2024" "Exercises 5.2 #9(iii), p. 121"]
theorem morris_exercise_5_2_9_iii (x : X) : IsClosed (connectedComponent x) :=
  isClosed_connectedComponent

/-- Morris, Topology Without Tears, Exercises 5.2 #10(i). A space is totally disconnected iff the
component of each point is that point alone. -/
@[kb "morris2024" "Exercises 5.2 #10(i), p. 121"]
theorem morris_exercise_5_2_10_i :
    TotallyDisconnectedSpace X ↔ ∀ x : X, connectedComponent x = {x} :=
  totallyDisconnectedSpace_iff_connectedComponent_singleton

/-- Morris, Topology Without Tears, Exercises 5.2 #10(ii). The rationals are totally disconnected. -/
@[kb "morris2024" "Exercises 5.2 #10(ii), p. 121"]
theorem morris_exercise_5_2_10_ii : TotallyDisconnectedSpace ℚ :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 5.2 #10(iv). A continuous map from `ℝ` to `ℚ` is
constant. -/
@[kb "morris2024" "Exercises 5.2 #10(iv), p. 121"]
theorem morris_exercise_5_2_10_iv {f : ℝ → ℚ} (hf : Continuous f) (x y : ℝ) : f x = f y :=
  (isPreconnected_range hf).subsingleton ⟨x, rfl⟩ ⟨y, rfl⟩

/-- Morris, Topology Without Tears, Exercises 5.2 #10(v). Every subspace of a totally disconnected
space is totally disconnected. -/
@[kb "morris2024" "Exercises 5.2 #10(v), p. 121"]
theorem morris_exercise_5_2_10_v [TotallyDisconnectedSpace X] (S : Set X) : TotallyDisconnectedSpace S :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 5.2 #14. Every local homeomorphism is continuous. -/
@[kb "morris2024" "Exercises 5.2 #14, p. 122"]
theorem morris_exercise_5_2_14 {f : X → Y} (hf : IsLocalHomeomorph f) : Continuous f :=
  hf.continuous

end Chapter5

end UndergradKB.Topology.Course
