import Mathlib.Topology.Constructions
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Bases
import Mathlib.Topology.DerivedSet
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Metrizable.Basic
import UndergradKB.Common.Attr

/-! # Course layer, Morris: exercises of Chapters 3 and 4 (wave 4, part c)

Thin theorems for standard facts that Morris, *Topology Without Tears*, sets as exercises in Chapter 3
(limit points, closure, interior, connectedness) and Chapter 4 (subspaces, Hausdorff and regular spaces,
homeomorphisms, local homeomorphisms).
-/

open _root_.Topology

namespace UndergradKB.Topology.Course

open Set Filter TopologicalSpace

section Chapter3

variable {X : Type*} [TopologicalSpace X]

/-- Morris, Topology Without Tears, Exercises 3.1 #4(b). A real number `a` lies in the closure of `S`
iff for every positive integer `n` some point of `S` is within `1/n` of `a`. -/
@[kb "morris2024" "Exercises 3.1 #4(b), p. 80"]
theorem morris_exercise_3_1_4_b (S : Set ℝ) (a : ℝ) :
    a ∈ closure S ↔ ∀ n : ℕ, ∃ x ∈ S, |x - a| < 1 / ((n : ℝ) + 1) := by
  rw [Metric.mem_closure_iff]
  constructor
  · intro h n
    obtain ⟨b, hb, hd⟩ := h (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨b, hb, by rwa [Real.dist_eq, abs_sub_comm] at hd⟩
  · intro h ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    obtain ⟨x, hx, hd⟩ := h n
    exact ⟨x, hx, by rw [Real.dist_eq, abs_sub_comm]; exact hd.trans hn⟩

/-- Morris, Topology Without Tears, Exercises 3.1 #5(i). If `S ⊆ T`, every limit point of `S` is a
limit point of `T`. -/
@[kb "morris2024" "Exercises 3.1 #5(i), p. 80"]
theorem morris_exercise_3_1_5_i {S T : Set X} (h : S ⊆ T) : derivedSet S ⊆ derivedSet T :=
  derivedSet_mono S T h

/-- Morris, Topology Without Tears, Exercises 3.1 #5(ii). If `S ⊆ T`, then `closure S ⊆ closure T`. -/
@[kb "morris2024" "Exercises 3.1 #5(ii), p. 80"]
theorem morris_exercise_3_1_5_ii {S T : Set X} (h : S ⊆ T) : closure S ⊆ closure T :=
  closure_mono h

/-- Morris, Topology Without Tears, Exercises 3.1 #5(iii). If `S ⊆ T` and `S` is dense, then `T` is
dense. -/
@[kb "morris2024" "Exercises 3.1 #5(iii), p. 80"]
theorem morris_exercise_3_1_5_iii {S T : Set X} (h : S ⊆ T) (hS : Dense S) : Dense T :=
  hS.mono h

/-- Morris, Topology Without Tears, Exercises 3.2 #1. A set `A` is dense iff every neighbourhood of
each point outside `A` meets `A`. -/
@[kb "morris2024" "Exercises 3.2 #1, p. 82"]
theorem morris_exercise_3_2_1 (A : Set X) :
    Dense A ↔ ∀ x ∈ Aᶜ, ∀ N ∈ 𝓝 x, (N ∩ A).Nonempty := by
  constructor
  · intro h x _ N hN
    exact mem_closure_iff_nhds.1 (h x) N hN
  · intro h x
    by_cases hx : x ∈ A
    · exact subset_closure hx
    · exact mem_closure_iff_nhds.2 (h x hx)

/-- Morris, Topology Without Tears, Exercises 3.2 #2(i). The closure of an intersection lies in the
intersection of the closures. -/
@[kb "morris2024" "Exercises 3.2 #2(i), p. 82"]
theorem morris_exercise_3_2_2_i (A B : Set X) : closure (A ∩ B) ⊆ closure A ∩ closure B :=
  closure_inter_subset_inter_closure A B

/-- Morris, Topology Without Tears, Exercises 3.2 #4(vi). An uncountable discrete space is not
separable. -/
@[kb "morris2024" "Exercises 3.2 #4(vi), p. 83"]
theorem morris_exercise_3_2_4_vi [DiscreteTopology X] [Uncountable X] : ¬ SeparableSpace X := by
  intro h
  have : Countable X := separableSpace_iff_countable.1 h
  exact not_countable (α := X) inferInstance

/-- Morris, Topology Without Tears, Exercises 3.2 #4(viii). A space satisfying the second axiom of
countability is separable. -/
@[kb "morris2024" "Exercises 3.2 #4(viii), p. 83"]
theorem morris_exercise_3_2_4_viii [SecondCountableTopology X] : SeparableSpace X :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 3.2 #5(iii). If `A` is open then `Int A = A`. -/
@[kb "morris2024" "Exercises 3.2 #5(iii), p. 83"]
theorem morris_exercise_3_2_5_iii {A : Set X} (h : IsOpen A) : interior A = A :=
  h.interior_eq

/-- Morris, Topology Without Tears, Exercises 3.2 #5(i). In `ℝ`, the interior of `[0, 1]` is
`(0, 1)`. -/
@[kb "morris2024" "Exercises 3.2 #5(i), p. 83"]
theorem morris_exercise_3_2_5_i : interior (Icc (0 : ℝ) 1) = Ioo 0 1 :=
  interior_Icc

/-- Morris, Topology Without Tears, Exercises 3.2 #5(iv). In `ℝ`, the interior of `{3}` is empty. -/
@[kb "morris2024" "Exercises 3.2 #5(iv), p. 83"]
theorem morris_exercise_3_2_5_iv : interior ({3} : Set ℝ) = ∅ :=
  interior_singleton 3

/-- Morris, Topology Without Tears, Exercises 3.2 #5(v). In an indiscrete space, every proper subset
has empty interior. -/
@[kb "morris2024" "Exercises 3.2 #5(v), p. 83"]
theorem morris_exercise_3_2_5_v (h : ∀ U : Set X, IsOpen U → U = ∅ ∨ U = univ) (A : Set X)
    (hA : A ≠ univ) : interior A = ∅ := by
  rcases h _ isOpen_interior with h0 | h0
  · exact h0
  · exact absurd (univ_subset_iff.1 (h0 ▸ interior_subset)) hA

/-- Morris, Topology Without Tears, Exercises 3.2 #6. The interior of `A` is the complement of the
closure of the complement of `A`. -/
@[kb "morris2024" "Exercises 3.2 #6, p. 83"]
theorem morris_exercise_3_2_6 (A : Set X) : interior A = (closure Aᶜ)ᶜ :=
  interior_eq_compl_closure_compl

/-- Morris, Topology Without Tears, Exercises 3.2 #7. A set `A` is dense iff the interior of its
complement is empty. -/
@[kb "morris2024" "Exercises 3.2 #7, p. 83"]
theorem morris_exercise_3_2_7 (A : Set X) : Dense A ↔ interior Aᶜ = ∅ := by
  rw [interior_compl, compl_empty_iff]
  exact dense_iff_closure_eq

/-- Morris, Topology Without Tears, Exercises 3.2 #8(i). The interior of an intersection is the
intersection of the interiors. -/
@[kb "morris2024" "Exercises 3.2 #8(i), p. 84"]
theorem morris_exercise_3_2_8_i (A₁ A₂ : Set X) : interior (A₁ ∩ A₂) = interior A₁ ∩ interior A₂ :=
  interior_inter

/-- Morris, Topology Without Tears, Exercises 3.2 #8(iii). The closure of a union of two sets is the
union of their closures. -/
@[kb "morris2024" "Exercises 3.2 #8(iii), p. 84"]
theorem morris_exercise_3_2_8_iii (A₁ A₂ : Set X) : closure (A₁ ∪ A₂) = closure A₁ ∪ closure A₂ :=
  closure_union

/-- Morris, Topology Without Tears, Exercises 3.2 #9. If `S` is dense and `U` is open, then the
closure of `S ∩ U` is the closure of `U`. -/
@[kb "morris2024" "Exercises 3.2 #9, p. 84"]
theorem morris_exercise_3_2_9 {S U : Set X} (hS : Dense S) (hU : IsOpen U) :
    closure (S ∩ U) = closure U := by
  refine subset_antisymm (closure_mono inter_subset_right) ?_
  refine closure_minimal ?_ isClosed_closure
  intro x hx
  exact hU.closure_inter (by rw [hS.closure_eq]; exact ⟨mem_univ x, hx⟩)

/-- Morris, Topology Without Tears, Exercises 3.2 #10. If `S` and `T` are dense and `T` is open, then
`S ∩ T` is dense. -/
@[kb "morris2024" "Exercises 3.2 #10, p. 84"]
theorem morris_exercise_3_2_10 {S T : Set X} (hS : Dense S) (hT : Dense T) (hTo : IsOpen T) :
    Dense (S ∩ T) :=
  (hT.inter_of_isOpen_left hS hTo).mono (inter_comm T S ▸ subset_rfl)

/-- Morris, Topology Without Tears, Exercises 3.3 #3. A space is not connected iff it is the union of
two disjoint non-empty open sets. -/
@[kb "morris2024" "Exercises 3.3 #3, p. 88"]
theorem morris_exercise_3_3_3 :
    ¬ PreconnectedSpace X ↔
      ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ A.Nonempty ∧ B.Nonempty ∧ A ∩ B = ∅ ∧ A ∪ B = univ := by
  rw [preconnectedSpace_iff_clopen]
  constructor
  · intro h
    push Not at h
    obtain ⟨s, hs, hne, hne'⟩ := h
    refine ⟨s, sᶜ, hs.isOpen, hs.isClosed.isOpen_compl, hne, ?_, inter_compl_self s,
      union_compl_self s⟩
    simpa [nonempty_compl] using hne'
  · rintro ⟨A, B, hA, hB, hAne, hBne, hAB, hABu⟩ h
    have hBc : B = Aᶜ := by
      ext x
      constructor
      · intro hx hxA
        have : x ∈ A ∩ B := ⟨hxA, hx⟩
        rw [hAB] at this
        exact this
      · intro hx
        have : x ∈ A ∪ B := by rw [hABu]; exact mem_univ x
        exact this.resolve_left hx
    have hcl : IsClopen A := ⟨by rw [hBc] at hB; exact isOpen_compl_iff.1 hB, hA⟩
    rcases h A hcl with h0 | h0
    · exact hAne.ne_empty h0
    · rw [h0, compl_univ] at hBc
      exact hBne.ne_empty hBc

end Chapter3

end UndergradKB.Topology.Course
