import Mathlib.Topology.DerivedSet
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Connected.PathConnected
import UndergradKB.Common.Attr

/-! # Course layer, Morris Chapter 3: closure, interior, neighbourhoods, connectedness basics

Thin wrappers of Mathlib results, stated in the terms of Morris, *Topology Without Tears*, Chapter 3.
-/

open _root_.Topology

namespace UndergradKB.Topology.Course

open Set Filter

section Chapter03

variable {X : Type*} [TopologicalSpace X]

/-- Morris, Topology Without Tears, Definition 3.1.1 (TP-037). A point `x` is a limit point of `A` when every
open set containing `x` contains a point of `A` other than `x`. -/
@[kb "morris2024" "Definition 3.1.1, p. 73"]
theorem morris_3_1_1 (A : Set X) (x : X) :
    x ∈ derivedSet A ↔ ∀ U : Set X, IsOpen U → x ∈ U → ∃ y ∈ U ∩ A, y ≠ x := by
  rw [mem_derivedSet]
  constructor
  · intro h U hU hx
    exact accPt_iff_nhds.1 h U (hU.mem_nhds hx)
  · intro h
    refine accPt_iff_nhds.2 fun U hU => ?_
    obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.1 hU
    obtain ⟨y, hy, hne⟩ := h V hV hxV
    exact ⟨y, ⟨hVU hy.1, hy.2⟩, hne⟩

/-- Morris, Topology Without Tears, Proposition 3.1.6 (TP-038). A set is closed iff it contains all its limit
points. -/
@[kb "morris2024" "Proposition 3.1.6, p. 76"]
theorem morris_3_1_6 (A : Set X) : IsClosed A ↔ derivedSet A ⊆ A :=
  isClosed_iff_derivedSet_subset A

/-- Morris, Topology Without Tears, Proposition 3.1.8 (TP-039). A set together with its limit points is
closed. -/
@[kb "morris2024" "Proposition 3.1.8, p. 77"]
theorem morris_3_1_8 (A : Set X) : IsClosed (A ∪ derivedSet A) := by
  rw [← closure_eq_self_union_derivedSet]
  exact isClosed_closure

/-- Morris, Topology Without Tears, Definition 3.1.9 (TP-040). The closure of `A` is `A` together with its
limit points. -/
@[kb "morris2024" "Definition 3.1.9, p. 77"]
theorem morris_3_1_9 (A : Set X) : closure A = A ∪ derivedSet A :=
  closure_eq_self_union_derivedSet A

/-- Morris, Topology Without Tears, Remark 3.1.10 (TP-041). The closure of `A` is the smallest closed set
containing `A`, the intersection of all closed supersets. -/
@[kb "morris2024" "Remark 3.1.10, p. 77"]
theorem morris_3_1_10 (A : Set X) :
    IsClosed (closure A) ∧ A ⊆ closure A ∧ (∀ C : Set X, IsClosed C → A ⊆ C → closure A ⊆ C) ∧
      closure A = ⋂₀ {C : Set X | IsClosed C ∧ A ⊆ C} :=
  ⟨isClosed_closure, subset_closure, fun _ hC hAC => closure_minimal hAC hC, rfl⟩

/-- Morris, Topology Without Tears, Example 3.1.12 (TP-042). The closure of the rationals in `ℝ` is `ℝ`. -/
@[kb "morris2024" "Example 3.1.12, p. 78"]
theorem morris_3_1_12 : closure (range ((↑) : ℚ → ℝ)) = univ :=
  Rat.denseRange_cast.closure_range

/-- Morris, Topology Without Tears, Definition 3.1.13 (TP-043). A set is dense when its closure is the whole
space. -/
@[kb "morris2024" "Definition 3.1.13, p. 78"]
theorem morris_3_1_13 (A : Set X) : Dense A ↔ closure A = univ :=
  dense_iff_closure_eq

/-- Morris, Topology Without Tears, Proposition 3.1.15 (TP-044). A set is dense iff it meets every nonempty
open set. -/
@[kb "morris2024" "Proposition 3.1.15, p. 79"]
theorem morris_3_1_15 (A : Set X) :
    Dense A ↔ ∀ U : Set X, IsOpen U → U.Nonempty → (U ∩ A).Nonempty :=
  dense_iff_inter_open

/-- Morris, Topology Without Tears, Definition 3.2.1 (TP-045). `N` is a neighbourhood of `p` when some open
`U` has `p ∈ U ⊆ N`. -/
@[kb "morris2024" "Definition 3.2.1, p. 81"]
theorem morris_3_2_1 (N : Set X) (p : X) : N ∈ 𝓝 p ↔ ∃ U : Set X, IsOpen U ∧ p ∈ U ∧ U ⊆ N := by
  rw [mem_nhds_iff]
  exact ⟨fun ⟨U, hUN, hU, hp⟩ => ⟨U, hU, hp, hUN⟩, fun ⟨U, hU, hp, hUN⟩ => ⟨U, hUN, hU, hp⟩⟩

/-- Morris, Topology Without Tears, Exercise 3.2.4 (TP-046). An open set is a neighbourhood of each of its
points. -/
@[kb "morris2024" "Exercise 3.2.4, p. 81"]
theorem morris_3_2_4 {U : Set X} (hU : IsOpen U) (x : X) (hx : x ∈ U) : U ∈ 𝓝 x :=
  hU.mem_nhds hx

/-- Morris, Topology Without Tears, Exercise 3.2.5 (TP-047). A superset of a neighbourhood of `p` is a
neighbourhood of `p`. -/
@[kb "morris2024" "Exercise 3.2.5, p. 81"]
theorem morris_3_2_5 {N M : Set X} {p : X} (hN : N ∈ 𝓝 p) (hNM : N ⊆ M) : M ∈ 𝓝 p :=
  Filter.mem_of_superset hN hNM

/-- Morris, Topology Without Tears, Proposition 3.2.6 (TP-048). `x` is a limit point of `A` iff every
neighbourhood of `x` contains a point of `A` other than `x`. -/
@[kb "morris2024" "Proposition 3.2.6, p. 81"]
theorem morris_3_2_6 (A : Set X) (x : X) :
    x ∈ derivedSet A ↔ ∀ N ∈ 𝓝 x, ∃ y ∈ N ∩ A, y ≠ x := by
  rw [mem_derivedSet]
  exact accPt_iff_nhds

/-- Morris, Topology Without Tears, Corollary 3.2.7 (TP-049). A set is closed iff every point outside it has a
neighbourhood contained in the complement. -/
@[kb "morris2024" "Corollary 3.2.7, p. 82"]
theorem morris_3_2_7 (A : Set X) : IsClosed A ↔ ∀ x, x ∉ A → ∃ N ∈ 𝓝 x, N ⊆ Aᶜ := by
  constructor
  · exact fun h x hx => ⟨Aᶜ, h.isOpen_compl.mem_nhds hx, subset_rfl⟩
  · intro h
    refine isOpen_compl_iff.1 (isOpen_iff_mem_nhds.2 fun x hx => ?_)
    obtain ⟨N, hN, hsub⟩ := h x hx
    exact Filter.mem_of_superset hN hsub

/-- Morris, Topology Without Tears, Corollary 3.2.8 (TP-050). A set is open iff it is a neighbourhood of each
of its points. -/
@[kb "morris2024" "Corollary 3.2.8, p. 82"]
theorem morris_3_2_8 (A : Set X) : IsOpen A ↔ ∀ x ∈ A, A ∈ 𝓝 x :=
  isOpen_iff_mem_nhds

/-- Morris, Topology Without Tears, Corollary 3.2.9 (TP-051). A set is open iff each of its points lies in an
open set contained in it. -/
@[kb "morris2024" "Corollary 3.2.9, p. 82"]
theorem morris_3_2_9 (A : Set X) :
    IsOpen A ↔ ∀ x ∈ A, ∃ U : Set X, U ⊆ A ∧ IsOpen U ∧ x ∈ U :=
  isOpen_iff_forall_mem_open

/-- Morris, Topology Without Tears, Axiom in Section 3.3 (TP-052). Least upper bound axiom: a nonempty set of
reals that is bounded above has a least upper bound. -/
@[kb "morris2024" "Axiom 3.3, p. 85"]
theorem morris_3_3_lub (S : Set ℝ) (hne : S.Nonempty) (hbdd : BddAbove S) : ∃ x : ℝ, IsLUB S x :=
  Real.exists_isLUB hne hbdd

/-- Morris, Topology Without Tears, Lemma 3.3.2 (TP-053). A closed, nonempty, bounded-above subset of `ℝ`
contains its supremum. -/
@[kb "morris2024" "Lemma 3.3.2, p. 85"]
theorem morris_3_3_2 (S : Set ℝ) (hS : IsClosed S) (hne : S.Nonempty) (hbdd : BddAbove S) :
    sSup S ∈ S :=
  hS.csSup_mem hne hbdd

/-- Morris, Topology Without Tears, Proposition 3.3.3 (TP-054). The only clopen subsets of `ℝ` are `∅` and
`ℝ`. -/
@[kb "morris2024" "Proposition 3.3.3, p. 86"]
theorem morris_3_3_3 (S : Set ℝ) : IsClopen S ↔ S = ∅ ∨ S = univ :=
  isClopen_iff

/-- Morris, Topology Without Tears, Definition 3.3.4 (TP-055). A space is connected when its only clopen sets
are `∅` and the whole space. -/
@[kb "morris2024" "Definition 3.3.4, p. 86"]
theorem morris_3_3_4 : PreconnectedSpace X ↔ ∀ A : Set X, IsClopen A → A = ∅ ∨ A = univ :=
  preconnectedSpace_iff_clopen

/-- Morris, Topology Without Tears, Exercise 3.3.6 (TP-056). A discrete space with more than one point is not
connected. -/
@[kb "morris2024" "Exercise 3.3.6, p. 86"]
theorem morris_3_3_6 [DiscreteTopology X] (h : ∃ x y : X, x ≠ y) : ¬ PreconnectedSpace X := by
  intro hp
  obtain ⟨x, y, hxy⟩ := h
  have := PreconnectedSpace.trivial_of_discrete (X := X)
  exact hxy (Subsingleton.elim x y)

end Chapter03

end UndergradKB.Topology.Course
