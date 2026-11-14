import Mathlib.Topology.Constructions
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Instances.Irrational
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Bases
import UndergradKB.Common.Attr

/-! # Course layer, Morris: exercises of Chapter 4 (wave 4, part d)

Thin theorems for standard facts that Morris, *Topology Without Tears*, sets as exercises in Chapter 4:
subspaces (and their separation and countability properties), connected unions, Hausdorff and regular
spaces, invariants of homeomorphisms, and local homeomorphisms.
-/

open _root_.Topology

namespace UndergradKB.Topology.Course

open Set Filter TopologicalSpace

section Chapter4

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Morris, Topology Without Tears, Exercises 4.1 #4. A subspace of a subspace is a subspace: for
`A ⊆ B ⊆ X`, the topology induced on `A` from `X` is the one induced from the subspace `B`. -/
@[kb "morris2024" "Exercises 4.1 #4, p. 93"]
theorem morris_exercise_4_1_4 {A B : Set X} (h : A ⊆ B) : IsInducing (Set.inclusion h) := by
  refine IsInducing.of_comp (continuous_inclusion h) continuous_subtype_val ?_
  exact IsInducing.subtypeVal

/-- Morris, Topology Without Tears, Exercises 4.1 #5. A subset `Z` of a subspace `Y` is closed in `Y`
iff it is the trace on `Y` of a closed subset of `X`. -/
@[kb "morris2024" "Exercises 4.1 #5, p. 93"]
theorem morris_exercise_4_1_5 (Y : Set X) (Z : Set Y) :
    IsClosed Z ↔ ∃ A : Set X, IsClosed A ∧ Z = Subtype.val ⁻¹' A := by
  rw [isClosed_induced_iff]
  constructor
  · rintro ⟨t, ht, h⟩; exact ⟨t, ht, h.symm⟩
  · rintro ⟨t, ht, h⟩; exact ⟨t, ht, h.symm⟩

/-- Morris, Topology Without Tears, Exercises 4.1 #6. Every subspace of a discrete space is
discrete. -/
@[kb "morris2024" "Exercises 4.1 #6, p. 94"]
theorem morris_exercise_4_1_6 [DiscreteTopology X] (Y : Set X) : DiscreteTopology Y :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 4.1 #7. Every subspace of an indiscrete space is
indiscrete. -/
@[kb "morris2024" "Exercises 4.1 #7, p. 94"]
theorem morris_exercise_4_1_7 (h : ∀ U : Set X, IsOpen U → U = ∅ ∨ U = univ) (Y : Set X) :
    ∀ V : Set Y, IsOpen V → V = ∅ ∨ V = univ := by
  intro V hV
  obtain ⟨U, hU, rfl⟩ := isOpen_induced_iff.1 hV
  rcases h U hU with rfl | rfl
  · left; exact preimage_empty
  · right; exact preimage_univ

/-- Morris, Topology Without Tears, Exercises 4.1 #9. A subspace of a connected space need not be
connected: the two-point subspace `{0, 1}` of `ℝ` is not connected. -/
@[kb "morris2024" "Exercises 4.1 #9, p. 94"]
theorem morris_exercise_4_1_9 : ¬ ∀ S : Set ℝ, IsPreconnected S := by
  intro h
  have h2 := (isPreconnected_iff_ordConnected.1 (h {0, 1})).out
    (mem_insert (0 : ℝ) {1}) (mem_insert_of_mem _ (mem_singleton (1 : ℝ)))
    (show (1 / 2 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
  norm_num at h2

/-- Morris, Topology Without Tears, Exercises 4.1 #10. The topology of a subspace `Y` is contained in
the topology of `X` (every open subset of `Y` is open in `X`) iff `Y` is open in `X`. -/
@[kb "morris2024" "Exercises 4.1 #10, p. 94"]
theorem morris_exercise_4_1_10 (Y : Set X) :
    (∀ V : Set Y, IsOpen V → IsOpen (Subtype.val '' V)) ↔ IsOpen Y := by
  constructor
  · intro h
    simpa using h univ isOpen_univ
  · intro hY V hV
    exact hY.isOpenMap_subtype_val V hV

/-- Morris, Topology Without Tears, Exercises 4.1 #11. If `A` and `B` are connected subspaces with
`A ∩ B` non-empty, then `A ∪ B` is connected. -/
@[kb "morris2024" "Exercises 4.1 #11, p. 94"]
theorem morris_exercise_4_1_11 {A B : Set X} (hA : IsPreconnected A) (hB : IsPreconnected B)
    (hAB : (A ∩ B).Nonempty) : IsPreconnected (A ∪ B) := by
  obtain ⟨x, hxA, hxB⟩ := hAB
  exact hA.union x hxA hxB hB

/-- Morris, Topology Without Tears, Exercises 4.1 #12. Every subspace of a T1-space is a T1-space. -/
@[kb "morris2024" "Exercises 4.1 #12, p. 94"]
theorem morris_exercise_4_1_12 [T1Space X] (Y : Set X) : T1Space Y :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 4.1 #13(i). The real line is Hausdorff. -/
@[kb "morris2024" "Exercises 4.1 #13(i), p. 94"]
theorem morris_exercise_4_1_13_i : T2Space ℝ :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 4.1 #13(ii). Every discrete space is Hausdorff. -/
@[kb "morris2024" "Exercises 4.1 #13(ii), p. 94"]
theorem morris_exercise_4_1_13_ii [DiscreteTopology X] : T2Space X :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 4.1 #13(iii). Every Hausdorff space is a T1-space. -/
@[kb "morris2024" "Exercises 4.1 #13(iii), p. 94"]
theorem morris_exercise_4_1_13_iii [T2Space X] : T1Space X :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 4.1 #13(iv). An infinite set with the finite-closed
topology (for instance `ℤ`) is a T1-space but not Hausdorff. -/
@[kb "morris2024" "Exercises 4.1 #13(iv), p. 94"]
theorem morris_exercise_4_1_13_iv (Z : Type*) [Infinite Z] :
    T1Space (CofiniteTopology Z) ∧ ¬ T2Space (CofiniteTopology Z) := by
  refine ⟨inferInstance, fun h => ?_⟩
  obtain ⟨a, b, hab⟩ := exists_pair_ne (CofiniteTopology Z)
  obtain ⟨u, v, hu, hv, ha, hb, huv⟩ := t2_separation hab
  have hu' := CofiniteTopology.isOpen_iff.1 hu ⟨a, ha⟩
  have hv' := CofiniteTopology.isOpen_iff.1 hv ⟨b, hb⟩
  have hsub : v ⊆ uᶜ := fun x hx hxu => (disjoint_left.1 huv hxu) hx
  have hvfin : v.Finite := hu'.subset hsub
  have : (univ : Set (CofiniteTopology Z)).Finite := by
    have := hvfin.union hv'
    simpa using this
  have hfin : Finite Z := (CofiniteTopology.of (X := Z)).finite_iff.2 (finite_univ_iff.1 this)
  exact not_finite Z

/-- Morris, Topology Without Tears, Exercises 4.1 #13(v). Every subspace of a Hausdorff space is
Hausdorff. -/
@[kb "morris2024" "Exercises 4.1 #13(v), p. 94"]
theorem morris_exercise_4_1_13_v [T2Space X] (Y : Set X) : T2Space Y :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 4.1 #14. Every subspace of a space satisfying the second
axiom of countability satisfies it as well. -/
@[kb "morris2024" "Exercises 4.1 #14, p. 94"]
theorem morris_exercise_4_1_14 [SecondCountableTopology X] (Y : Set X) : SecondCountableTopology Y :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 4.1 #15. For `a ≤ b`, the closed interval `[a, b]` is
connected. -/
@[kb "morris2024" "Exercises 4.1 #15, p. 94"]
theorem morris_exercise_4_1_15 (a b : ℝ) : IsPreconnected (Icc a b) :=
  isPreconnected_Icc

/-- Morris, Topology Without Tears, Exercises 4.1 #17(i). Every subspace of a regular space is
regular. -/
@[kb "morris2024" "Exercises 4.1 #17(i), p. 95"]
theorem morris_exercise_4_1_17_i [RegularSpace X] (Y : Set X) : RegularSpace Y :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 4.1 #17(ii). The real line is a regular space. -/
@[kb "morris2024" "Exercises 4.1 #17(ii), p. 95"]
theorem morris_exercise_4_1_17_ii : RegularSpace ℝ :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 4.1 #17(iii). A regular T1-space is a Hausdorff space. -/
@[kb "morris2024" "Exercises 4.1 #17(iii), p. 95"]
theorem morris_exercise_4_1_17_iii [RegularSpace X] [T1Space X] : T2Space X :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 4.2 #2. The discrete spaces `ℕ` and `ℤ` are
homeomorphic. -/
@[kb "morris2024" "Exercises 4.2 #2, p. 100"]
theorem morris_exercise_4_2_2 : Nonempty (ℤ ≃ₜ ℕ) :=
  ⟨{ toEquiv := Equiv.intEquivNat
     continuous_toFun := continuous_of_discreteTopology
     continuous_invFun := continuous_of_discreteTopology }⟩

/-- Morris, Topology Without Tears, Exercises 4.2 #3. The line `y = m x + c`, as a subspace of `ℝ²`, is
homeomorphic to `ℝ`. -/
@[kb "morris2024" "Exercises 4.2 #3, p. 100"]
theorem morris_exercise_4_2_3 (m c : ℝ) : Nonempty ({p : ℝ × ℝ | p.2 = m * p.1 + c} ≃ₜ ℝ) :=
  ⟨{ toFun := fun p => p.1.1
     invFun := fun x => ⟨(x, m * x + c), rfl⟩
     left_inv := by
       rintro ⟨⟨x, y⟩, h⟩
       exact Subtype.ext (Prod.ext rfl h.symm)
     right_inv := fun x => rfl
     continuous_toFun := by fun_prop
     continuous_invFun := by fun_prop }⟩

/-- Morris, Topology Without Tears, Exercises 4.2 #7(i). Homeomorphic spaces: if one is T0, so is the
other. -/
@[kb "morris2024" "Exercises 4.2 #7(i), p. 101"]
theorem morris_exercise_4_2_7_i [T0Space X] (h : X ≃ₜ Y) : T0Space Y :=
  h.t0Space

/-- Morris, Topology Without Tears, Exercises 4.2 #7(ii). Homeomorphic spaces: if one is T1, so is the
other. -/
@[kb "morris2024" "Exercises 4.2 #7(ii), p. 101"]
theorem morris_exercise_4_2_7_ii [T1Space X] (h : X ≃ₜ Y) : T1Space Y :=
  h.t1Space

/-- Morris, Topology Without Tears, Exercises 4.2 #7(iii). Homeomorphic spaces: if one is Hausdorff,
so is the other. -/
@[kb "morris2024" "Exercises 4.2 #7(iii), p. 101"]
theorem morris_exercise_4_2_7_iii [T2Space X] (h : X ≃ₜ Y) : T2Space Y :=
  h.t2Space

/-- Morris, Topology Without Tears, Exercises 4.2 #7(iv). Homeomorphic spaces: if one satisfies the
second axiom of countability, so does the other. -/
@[kb "morris2024" "Exercises 4.2 #7(iv), p. 101"]
theorem morris_exercise_4_2_7_iv [SecondCountableTopology Y] (h : X ≃ₜ Y) : SecondCountableTopology X :=
  h.secondCountableTopology

/-- Morris, Topology Without Tears, Exercises 4.2 #7(v). Homeomorphic spaces: if one is separable, so
is the other. -/
@[kb "morris2024" "Exercises 4.2 #7(v), p. 101"]
theorem morris_exercise_4_2_7_v [SeparableSpace X] (h : X ≃ₜ Y) : SeparableSpace Y :=
  h.surjective.denseRange.separableSpace h.continuous

/-- Morris, Topology Without Tears, Exercises 4.3 #2. A countable subspace of `ℝ` with more than one
point is disconnected. -/
@[kb "morris2024" "Exercises 4.3 #2, p. 106"]
theorem morris_exercise_4_3_2 {S : Set ℝ} (hc : S.Countable) (hS : S.Nontrivial) : ¬ IsPreconnected S :=
  fun h => hS.not_subsingleton (hc.isTotallyDisconnected S subset_rfl h)

/-- Morris, Topology Without Tears, Exercises 4.3 #9(i). A homeomorphism is a local homeomorphism. -/
@[kb "morris2024" "Exercises 4.3 #9(i), p. 108"]
theorem morris_exercise_4_3_9_i (h : X ≃ₜ Y) : IsLocalHomeomorph h :=
  h.isLocalHomeomorph

/-- Morris, Topology Without Tears, Exercises 4.3 #9(ii). The inclusion of an open subspace is a local
homeomorphism. -/
@[kb "morris2024" "Exercises 4.3 #9(ii), p. 108"]
theorem morris_exercise_4_3_9_ii {U : Set X} (hU : IsOpen U) : IsLocalHomeomorph ((↑) : U → X) :=
  hU.isOpenEmbedding_subtypeVal.isLocalHomeomorph

/-- Morris, Topology Without Tears, Exercises 4.3 #9(iii). A local homeomorphism maps open sets to
open sets. -/
@[kb "morris2024" "Exercises 4.3 #9(iii), p. 108"]
theorem morris_exercise_4_3_9_iii {f : X → Y} (hf : IsLocalHomeomorph f) {U : Set X} (hU : IsOpen U) :
    IsOpen (f '' U) :=
  hf.isOpenMap U hU

/-- Morris, Topology Without Tears, Exercises 4.3 #10(i). Every open set is semi-open: it lies between
an open set and the closure of that open set. -/
@[kb "morris2024" "Exercises 4.3 #10(i), p. 108"]
theorem morris_exercise_4_3_10_i {A : Set X} (hA : IsOpen A) :
    ∃ O : Set X, IsOpen O ∧ O ⊆ A ∧ A ⊆ closure O :=
  ⟨A, hA, subset_rfl, subset_closure⟩

end Chapter4

end UndergradKB.Topology.Course
