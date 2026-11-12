import Mathlib.Topology.Bases
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Instances.Int
import UndergradKB.Common.Attr

/-!
# Course layer: Morris, Topology Without Tears, Chapter 4

Thin wrappers of Mathlib results (subspaces, separation, homeomorphisms, connectedness of intervals).
-/

open Set Topology TopologicalSpace Filter

namespace UndergradKB.Topology.Course

/-- Morris, Topology Without Tears, Definition 4.1.1 (TP-059). A subset of a subspace `Y` is open iff it is the
trace on `Y` of an open set of `X`. -/
@[kb "morris2024" "Definition 4.1.1, p. 91"]
theorem morris_4_1_1 {X : Type*} [TopologicalSpace X] (Y : Set X) (V : Set Y) :
    IsOpen V ↔ ∃ U : Set X, IsOpen U ∧ Subtype.val ⁻¹' U = V := by
  rw [isOpen_induced_iff (f := (Subtype.val : Y → X)) (t := inferInstance)]

/-- Morris, Topology Without Tears, Exercise 4.1.4 (TP-060). Intersecting a basis of `X` with `Y` gives a basis of
the subspace `Y`. -/
@[kb "morris2024" "Exercise 4.1.4, p. 91"]
theorem morris_4_1_4 {X : Type*} [TopologicalSpace X] {B : Set (Set X)} (hB : IsTopologicalBasis B)
    (Y : Set X) :
    IsTopologicalBasis ((fun b : Set X => (Subtype.val : Y → X) ⁻¹' b) '' B) :=
  isTopologicalBasis_subtype hB _

/-- Morris, Topology Without Tears, Exercise 4.1.6 (TP-061). The subspace of the real line on the integers is
discrete. -/
@[kb "morris2024" "Exercise 4.1.6, p. 92"]
theorem morris_4_1_6 : DiscreteTopology (Set.range ((↑) : ℤ → ℝ)) := by
  let e := Int.isClosedEmbedding_coe_real.isEmbedding.toHomeomorph
  exact e.symm.isEmbedding.discreteTopology

/-- Morris, Topology Without Tears, Exercises 4.1 (TP-062). Hausdorff: distinct points have disjoint open
neighbourhoods. -/
@[kb "morris2024" "Exercises 4.1, p. 94"]
theorem morris_ex_4_1_a {X : Type*} [TopologicalSpace X] :
    T2Space X ↔ ∀ x y : X, x ≠ y → ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ Disjoint U V :=
  ⟨fun h x y hxy => h.t2 hxy, fun h => ⟨fun x y hxy => h x y hxy⟩⟩

/-- Morris, Topology Without Tears, Exercises 4.1 (TP-063). Regular: a closed set and a point outside it have
disjoint open neighbourhoods; `T3` is regular together with `T1`. -/
@[kb "morris2024" "Exercises 4.1, p. 95"]
theorem morris_ex_4_1_b {X : Type*} [TopologicalSpace X] :
    RegularSpace X ↔ ∀ (A : Set X) (x : X), IsClosed A → x ∉ A →
      ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ A ⊆ V ∧ U ∩ V = ∅ := by
  constructor
  · intro h A x hA hx
    have hd : Disjoint (𝓝ˢ A) (𝓝 x) := RegularSpace.regular hA hx
    rw [← nhdsSet_singleton] at hd
    obtain ⟨V, U, hV, hU, hAV, hxU, hd'⟩ := (separatedNhds_iff_disjoint.2 hd)
    exact ⟨U, V, hU, hV, singleton_subset_iff.1 hxU, hAV, by rw [Set.inter_comm]; exact hd'.inter_eq⟩
  · intro h
    refine ⟨fun {A x} hA hx => ?_⟩
    obtain ⟨U, V, hU, hV, hxU, hAV, hUV⟩ := h A x hA hx
    rw [← nhdsSet_singleton]
    refine separatedNhds_iff_disjoint.1 ⟨V, U, hV, hU, hAV, singleton_subset_iff.2 hxU, ?_⟩
    rw [Set.disjoint_iff_inter_eq_empty, Set.inter_comm]
    exact hUV

/-- Morris, Topology Without Tears, Exercises 4.1 (TP-063). A `T3` space is a regular `T1` space. -/
@[kb "morris2024" "Exercises 4.1, p. 95"]
theorem morris_ex_4_1_c {X : Type*} [TopologicalSpace X] :
    T3Space X ↔ RegularSpace X ∧ T1Space X :=
  ⟨fun h => ⟨inferInstance, inferInstance⟩, fun ⟨h1, h2⟩ => { }⟩

/-- Morris, Topology Without Tears, Definition 4.2.1 (TP-064). A homeomorphism is a continuous bijection with
continuous inverse; here the book's data packaged as a `Homeomorph`. -/
@[kb "morris2024" "Definition 4.2.1, p. 96"]
theorem morris_4_2_1 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    (∃ e : X ≃ₜ Y, ⇑e = f) ↔ Continuous f ∧ Function.Bijective f ∧
      ∃ g : Y → X, Continuous g ∧ Function.LeftInverse g f ∧ Function.RightInverse g f := by
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨e.continuous, e.bijective, e.symm, e.symm.continuous, e.left_inv, e.right_inv⟩
  · rintro ⟨hf, hb, g, hg, hl, hr⟩
    exact ⟨{ toEquiv := ⟨f, g, hl, hr⟩, continuous_toFun := hf, continuous_invFun := hg }, rfl⟩

/-- Morris, Topology Without Tears, Exercise 4.2.2 and Remark 4.2.3 (TP-065). Being homeomorphic is an
equivalence relation on topological spaces. -/
@[kb "morris2024" "Exercise 4.2.2, p. 97"]
theorem morris_4_2_2 {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] :
    Nonempty (X ≃ₜ X) ∧ (Nonempty (X ≃ₜ Y) → Nonempty (Y ≃ₜ X)) ∧
      (Nonempty (X ≃ₜ Y) → Nonempty (Y ≃ₜ Z) → Nonempty (X ≃ₜ Z)) :=
  ⟨⟨Homeomorph.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

/-- Morris, Topology Without Tears, Remark 4.2.7 (TP-068). Any two closed bounded intervals `[a,b]`, `[c,d]`
with `a < b`, `c < d` are homeomorphic. -/
@[kb "morris2024" "Remark 4.2.7, p. 99"]
theorem morris_4_2_7 {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    Nonempty (Set.Icc a b ≃ₜ Set.Icc c d) :=
  ⟨(iccHomeoI a b hab).trans (iccHomeoI c d hcd).symm⟩

/-- Morris, Topology Without Tears, Proposition 4.3.2 (TP-069). Connectedness is preserved by
homeomorphisms. -/
@[kb "morris2024" "Proposition 4.3.2, p. 102"]
theorem morris_4_3_2 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    ConnectedSpace X ↔ ConnectedSpace Y :=
  e.connectedSpace_iff

/-- Morris, Topology Without Tears, Definition 4.3.3 (TP-070). A subset of `ℝ` is an interval when it contains
every point between two of its points. -/
@[kb "morris2024" "Definition 4.3.3, p. 104"]
theorem morris_4_3_3 (I : Set ℝ) :
    I.OrdConnected ↔ ∀ x ∈ I, ∀ y ∈ I, ∀ z : ℝ, x < z → z < y → z ∈ I := by
  constructor
  · intro h x hx y hy z hxz hzy
    exact h.out hx hy ⟨hxz.le, hzy.le⟩
  · intro h
    refine ⟨fun x hx y hy z hz => ?_⟩
    rcases eq_or_lt_of_le hz.1 with rfl | h1
    · exact hx
    rcases eq_or_lt_of_le hz.2 with rfl | h2
    · exact hy
    exact h x hx y hy z h1 h2

/-- Morris, Topology Without Tears, Proposition 4.3.5 (TP-071). A subspace of `ℝ` is connected iff it is an
interval (here with the empty set counted as preconnected). -/
@[kb "morris2024" "Proposition 4.3.5, p. 104"]
theorem morris_4_3_5_a (I : Set ℝ) : PreconnectedSpace I ↔ I.OrdConnected := by
  rw [← isPreconnected_iff_preconnectedSpace]
  exact isPreconnected_iff_ordConnected

/-- Morris, Topology Without Tears, Proposition 4.3.5 (TP-071). A nonempty subspace of `ℝ` is connected iff it is
an interval. -/
@[kb "morris2024" "Proposition 4.3.5, p. 104"]
theorem morris_4_3_5_b (I : Set ℝ) (hI : I.Nonempty) : ConnectedSpace I ↔ I.OrdConnected := by
  rw [← isConnected_iff_connectedSpace, IsConnected, ← isPreconnected_iff_ordConnected]
  exact ⟨fun h => h.2, fun h => ⟨hI, h⟩⟩

/-- Morris, Topology Without Tears, Exercises 4.3 (TP-074). A local homeomorphism: every point has an open
neighbourhood on which the map is a homeomorphism onto an open set (an open embedding of the neighbourhood). -/
@[kb "morris2024" "Exercises 4.3, p. 108"]
theorem morris_ex_4_3 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    IsLocalHomeomorph f ↔ ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsOpenEmbedding (U.domRestrict f) := by
  rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
  constructor
  · intro h x
    obtain ⟨U, hU, hf⟩ := h x
    refine ⟨interior U, isOpen_interior, mem_interior_iff_mem_nhds.2 hU, ?_⟩
    have : (interior U).domRestrict f = (U.domRestrict f) ∘ Set.inclusion interior_subset := rfl
    rw [this]
    exact hf.comp (IsOpenEmbedding.inclusion interior_subset
      (isOpen_interior.preimage continuous_subtype_val))
  · intro h x
    obtain ⟨U, hU, hx, hf⟩ := h x
    exact ⟨U, hU.mem_nhds hx, hf⟩
