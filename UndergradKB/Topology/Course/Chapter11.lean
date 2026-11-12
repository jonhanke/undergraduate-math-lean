import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.Setoid.Basic
import UndergradKB.Common.Attr

/-!
# Course layer, Chapter 11 of Morris, Topology Without Tears

Quotient spaces (sections 11.1 and 11.2), as thin wrappers of Mathlib results.
-/

namespace UndergradKB.Topology.Course

open Set Function

/-- Morris, Topology Without Tears, Definition 11.1.1 (TP-256). A map `f` is a quotient map iff it is
surjective and `U` is open exactly when its preimage is open; every quotient map is continuous. -/
@[kb "morris2024" "Definition 11.1.1, p. 339"]
theorem morris_11_1_1 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    _root_.Topology.IsQuotientMap f ↔ Surjective f ∧ ∀ U : Set Y, IsOpen U ↔ IsOpen (f ⁻¹' U) :=
  ⟨fun h => ⟨h.surjective, fun _ => h.isOpen_preimage.symm⟩,
    fun ⟨hs, h⟩ => (_root_.Topology.isQuotientMap_iff f).2
      ⟨_root_.Topology.isCoinducing_iff.2 fun U => (h U).symm, hs⟩⟩

/-- Morris, Topology Without Tears, Remark 11.1.2 (TP-256). Every quotient map is continuous. -/
@[kb "morris2024" "Remark 11.1.2, p. 339"]
theorem morris_11_1_2 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : _root_.Topology.IsQuotientMap f) : Continuous f :=
  hf.continuous

/-- Morris, Topology Without Tears, Remark 11.1.3 (TP-257). A surjection is a quotient map iff a set is
closed exactly when its preimage is closed. -/
@[kb "morris2024" "Remark 11.1.3, p. 340"]
theorem morris_11_1_3 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    _root_.Topology.IsQuotientMap f ↔ Surjective f ∧ ∀ A : Set Y, IsClosed A ↔ IsClosed (f ⁻¹' A) :=
  _root_.Topology.isQuotientMap_iff_isClosed

/-- Morris, Topology Without Tears, Proposition 11.1.5 (TP-259). A continuous surjection from a compact
space to a Hausdorff space is a quotient map. -/
@[kb "morris2024" "Proposition 11.1.5, p. 340"]
theorem morris_11_1_5 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X]
    [T2Space Y] {f : X → Y} (hs : Surjective f) (hc : Continuous f) :
    _root_.Topology.IsQuotientMap f :=
  _root_.Topology.IsQuotientMap.of_surjective_continuous hs hc

/-- Morris, Topology Without Tears, Corollary 11.1.6 (TP-260). A continuous bijection from a compact
space onto a Hausdorff space is a homeomorphism. -/
@[kb "morris2024" "Corollary 11.1.6, p. 340"]
theorem morris_11_1_6 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X]
    [T2Space Y] {f : X → Y} (hb : Bijective f) (hc : Continuous f) :
    ∃ e : X ≃ₜ Y, ⇑e = f :=
  ⟨(isHomeomorph_iff_continuous_bijective.2 ⟨hc, hb⟩).homeomorph f, rfl⟩

/-- Morris, Topology Without Tears, Definition 11.1.7 (TP-261). A map is closed iff it sends closed sets
to closed sets. -/
@[kb "morris2024" "Definition 11.1.7, p. 341"]
theorem morris_11_1_7 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    IsClosedMap f ↔ ∀ A : Set X, IsClosed A → IsClosed (f '' A) :=
  Iff.rfl

/-- Morris, Topology Without Tears, Definition 11.1.7 (TP-261). A map is open iff it sends open sets to
open sets. -/
@[kb "morris2024" "Definition 11.1.7, p. 341"]
theorem morris_11_1_7_b {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    IsOpenMap f ↔ ∀ U : Set X, IsOpen U → IsOpen (f '' U) :=
  Iff.rfl

/-- Morris, Topology Without Tears, Proposition 11.1.10 (TP-263). A continuous map from a compact space
to a Hausdorff space is a closed map. -/
@[kb "morris2024" "Proposition 11.1.10, p. 341"]
theorem morris_11_1_10 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X]
    [T2Space Y] {f : X → Y} (hc : Continuous f) : IsClosedMap f :=
  hc.isClosedMap

/-- Morris, Topology Without Tears, Definition 11.2.1 (TP-264). A relation is an equivalence relation iff
it is reflexive, symmetric and transitive. -/
@[kb "morris2024" "Definition 11.2.1, p. 343"]
theorem morris_11_2_1 {α : Type*} (r : α → α → Prop) :
    Equivalence r ↔ (∀ a, r a a) ∧ (∀ a b, r a b → r b a) ∧ (∀ a b c, r a b → r b c → r a c) :=
  ⟨fun h => ⟨h.refl, fun _ _ => h.symm, fun _ _ _ => h.trans⟩,
    fun ⟨h1, h2, h3⟩ => ⟨h1, fun {a b} => h2 a b, fun {a b c} => h3 a b c⟩⟩

/-- Morris, Topology Without Tears, Remark 11.2.3 (TP-265). The class map onto the quotient set of an
equivalence relation is a quotient map for the quotient topology. -/
@[kb "morris2024" "Remark 11.2.3, p. 343"]
theorem morris_11_2_3 {X : Type*} [TopologicalSpace X] (s : Setoid X) :
    _root_.Topology.IsQuotientMap (Quotient.mk s) :=
  isQuotientMap_quotient_mk'

/-- Morris, Topology Without Tears, Remark 11.2.4 (TP-265). A surjection induces an equivalence relation
(having the same image), and the quotient set is in bijection with the codomain compatibly with the
class map. -/
@[kb "morris2024" "Remark 11.2.4, p. 344"]
theorem morris_11_2_4 {X Y : Type*} {f : X → Y} (hf : Surjective f) :
    ∃ e : Quotient (Setoid.ker f) ≃ Y, ∀ x, e (Quotient.mk _ x) = f x :=
  ⟨(Setoid.quotientKerEquivOfSurjective f hf), fun _ => rfl⟩

end UndergradKB.Topology.Course
