import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Clopen
import Mathlib.Topology.Order
import Mathlib.Topology.Constructions
import UndergradKB.Common.Attr

/-! # Course layer, Morris Chapter 1: topological spaces

Thin wrappers of Mathlib results, stated in the terms of Morris, *Topology Without Tears*, Chapter 1.
-/

open _root_.Topology

namespace UndergradKB.Topology.Course

open Set

section Chapter01

variable {X Y : Type*}

/-- Morris, Topology Without Tears, Definition 1.1.1 (TP-001). The open sets contain `X` and `∅`, are closed
under arbitrary unions and under binary intersections. -/
@[kb "morris2024" "Definition 1.1.1, p. 25"]
theorem morris_1_1_1 [TopologicalSpace X] :
    IsOpen (univ : Set X) ∧ IsOpen (∅ : Set X) ∧
      (∀ F : Set (Set X), (∀ s ∈ F, IsOpen s) → IsOpen (⋃₀ F)) ∧
      (∀ s t : Set X, IsOpen s → IsOpen t → IsOpen (s ∩ t)) :=
  ⟨isOpen_univ, isOpen_empty, fun _ h => isOpen_sUnion h, fun _ _ hs ht => hs.inter ht⟩

/-- Morris, Topology Without Tears, Definition 1.1.6 (TP-002). A topology is discrete when every subset is
open. -/
@[kb "morris2024" "Definition 1.1.6, p. 26"]
theorem morris_1_1_6 [TopologicalSpace X] : DiscreteTopology X ↔ ∀ s : Set X, IsOpen s :=
  ⟨fun _ s => isOpen_discrete s, fun h => discreteTopology_iff_forall_isOpen.2 h⟩

/-- Morris, Topology Without Tears, Definition 1.1.7 (TP-003). A topology is indiscrete when the only open
sets are `∅` and `X`. -/
@[kb "morris2024" "Definition 1.1.7, p. 27"]
theorem morris_1_1_7 (t : TopologicalSpace X) :
    t = ⊤ ↔ ∀ s : Set X, IsOpen[t] s → s = ∅ ∨ s = univ := by
  constructor
  · rintro rfl s hs
    exact (TopologicalSpace.isOpen_top_iff s).1 hs
  · intro h
    exact eq_top_iff.2 fun s hs => (TopologicalSpace.isOpen_top_iff s).2 (h s hs)

/-- Morris, Topology Without Tears, Proposition 1.1.9 (TP-004). If all singletons are open the space is
discrete. -/
@[kb "morris2024" "Proposition 1.1.9, p. 29"]
theorem morris_1_1_9 [TopologicalSpace X] (h : ∀ x : X, IsOpen ({x} : Set X)) : DiscreteTopology X :=
  discreteTopology_iff_isOpen_singleton.2 h

/-- Morris, Topology Without Tears, Proposition 1.2.2 (TP-006). `X` and `∅` are open, arbitrary unions and
finite intersections of open sets are open. -/
@[kb "morris2024" "Proposition 1.2.2, p. 33"]
theorem morris_1_2_2 [TopologicalSpace X] :
    IsOpen (univ : Set X) ∧ IsOpen (∅ : Set X) ∧
      (∀ F : Set (Set X), (∀ s ∈ F, IsOpen s) → IsOpen (⋃₀ F)) ∧
      (∀ F : Set (Set X), F.Finite → (∀ s ∈ F, IsOpen s) → IsOpen (⋂₀ F)) :=
  ⟨isOpen_univ, isOpen_empty, fun _ h => isOpen_sUnion h, fun _ hF h => hF.isOpen_sInter h⟩

/-- Morris, Topology Without Tears, Definition 1.2.4 (TP-008). A set is closed when its complement is open. -/
@[kb "morris2024" "Definition 1.2.4, p. 34"]
theorem morris_1_2_4 [TopologicalSpace X] (A : Set X) : IsClosed A ↔ IsOpen Aᶜ :=
  isOpen_compl_iff.symm

/-- Morris, Topology Without Tears, Proposition 1.2.5 (TP-009). `X` and `∅` are closed, arbitrary
intersections and finite unions of closed sets are closed. -/
@[kb "morris2024" "Proposition 1.2.5, p. 35"]
theorem morris_1_2_5 [TopologicalSpace X] :
    IsClosed (univ : Set X) ∧ IsClosed (∅ : Set X) ∧
      (∀ F : Set (Set X), (∀ s ∈ F, IsClosed s) → IsClosed (⋂₀ F)) ∧
      (∀ s t : Set X, IsClosed s → IsClosed t → IsClosed (s ∪ t)) :=
  ⟨isClosed_univ, isClosed_empty, fun _ h => isClosed_sInter h, fun _ _ hs ht => hs.union ht⟩

/-- Morris, Topology Without Tears, Definition 1.2.6 (TP-010). A clopen set is both open and closed. -/
@[kb "morris2024" "Definition 1.2.6, p. 36"]
theorem morris_1_2_6 [TopologicalSpace X] (A : Set X) : IsClopen A ↔ IsOpen A ∧ IsClosed A :=
  ⟨fun h => ⟨h.isOpen, h.isClosed⟩, fun h => ⟨h.2, h.1⟩⟩

/-- Morris, Topology Without Tears, Definition 1.3.1 (TP-011). In the finite-closed topology the closed sets
are `X` and the finite sets. -/
@[kb "morris2024" "Definition 1.3.1, p. 39"]
theorem morris_1_3_1 (A : Set (CofiniteTopology X)) : IsClosed A ↔ A = univ ∨ A.Finite :=
  CofiniteTopology.isClosed_iff

/-- Morris, Topology Without Tears, Proposition 1.3.6 (TP-014), existence part. A function has an inverse
exactly when it is bijective. -/
@[kb "morris2024" "Proposition 1.3.6, p. 41"]
theorem morris_1_3_6_a (f : X → Y) :
    Function.Bijective f ↔ ∃ g : Y → X, Function.LeftInverse g f ∧ Function.RightInverse g f :=
  Function.bijective_iff_has_inverse

/-- Morris, Topology Without Tears, Proposition 1.3.6 (TP-014), uniqueness part. Two inverses of a function
coincide. -/
@[kb "morris2024" "Proposition 1.3.6, p. 41"]
theorem morris_1_3_6_b (f : X → Y) (g₁ g₂ : Y → X)
    (h₁ : Function.LeftInverse g₁ f ∧ Function.RightInverse g₁ f)
    (h₂ : Function.LeftInverse g₂ f ∧ Function.RightInverse g₂ f) : g₁ = g₂ :=
  funext fun y =>
    calc g₁ y = g₁ (f (g₂ y)) := by rw [h₂.2 y]
      _ = g₂ y := h₁.1 _

/-- Morris, Topology Without Tears, Definition 1.3.7 (TP-015). The inverse image of `S` is the set of points
whose image lies in `S`. -/
@[kb "morris2024" "Definition 1.3.7, p. 42"]
theorem morris_1_3_7 (f : X → Y) (S : Set Y) (x : X) : x ∈ f ⁻¹' S ↔ f x ∈ S :=
  Iff.rfl

/-- Morris, Topology Without Tears, Exercise 1.3.9 (TP-016). The inverse images of open sets of `Y` form a
topology on `X`: the open sets of the induced topology are exactly these inverse images. -/
@[kb "morris2024" "Exercise 1.3.9, p. 42"]
theorem morris_1_3_9 [t : TopologicalSpace Y] (f : X → Y) (U : Set X) :
    IsOpen[TopologicalSpace.induced f t] U ↔ ∃ V : Set Y, IsOpen V ∧ f ⁻¹' V = U :=
  isOpen_induced_iff

/-- Morris, Topology Without Tears, Section 1.3 (TP-017). A space is `T₁` when every singleton is closed. -/
@[kb "morris2024" "Section 1.3, p. 44"]
theorem morris_1_3_T1 [TopologicalSpace X] : T1Space X ↔ ∀ x : X, IsClosed ({x} : Set X) :=
  ⟨fun _ _ => isClosed_singleton, fun h => ⟨h⟩⟩

/-- Morris, Topology Without Tears, Section 1.3 (TP-018). A space is `T₀` when any two distinct points are
separated by an open set containing exactly one of them. -/
@[kb "morris2024" "Section 1.3, p. 45"]
theorem morris_1_3_T0 [TopologicalSpace X] :
    T0Space X ↔ ∀ x y : X, x ≠ y → ∃ U : Set X, IsOpen U ∧ Xor (x ∈ U) (y ∈ U) :=
  t0Space_iff_exists_isOpen_xor_mem X

end Chapter01

end UndergradKB.Topology.Course
