import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Polynomial.Basic
import UndergradKB.Common.Attr

/-! # Course layer, Morris Chapter 8: products, components -/

open Filter Topology Set

namespace UndergradKB.Topology.Course

/-- Morris, Topology Without Tears, Definition 8.1.1 (TP-177). The product topology on `X × Y` has as basis the
products of open sets. -/
@[kb "morris2024" "Definition 8.1.1, p. 195"]
theorem morris_8_1_1 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    TopologicalSpace.IsTopologicalBasis (image2 (· ×ˢ ·) {U : Set X | IsOpen U} {V : Set Y | IsOpen V}) :=
  (TopologicalSpace.isTopologicalBasis_opens).prod TopologicalSpace.isTopologicalBasis_opens

/-- Morris, Topology Without Tears, Proposition 8.1.2 (TP-178). Products of basis elements of the factors form a
basis of the product topology. -/
@[kb "morris2024" "Proposition 8.1.2, p. 196"]
theorem morris_8_1_2 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (B : Set (Set X))
    (C : Set (Set Y)) (hB : TopologicalSpace.IsTopologicalBasis B) (hC : TopologicalSpace.IsTopologicalBasis C) :
    TopologicalSpace.IsTopologicalBasis (image2 (· ×ˢ ·) B C) :=
  hB.prod hC

/-- Morris, Topology Without Tears, Proposition 8.1.4 (TP-179). A product of closed sets is closed in the product
space. -/
@[kb "morris2024" "Proposition 8.1.4, p. 196"]
theorem morris_8_1_4 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (A : Set X) (B : Set Y)
    (hA : IsClosed A) (hB : IsClosed B) : IsClosed (A ×ˢ B) :=
  hA.prod hB

/-- Morris, Topology Without Tears, Definition 8.2.1 (TP-180). A topology `t₁` is finer than `t₂` iff every
`t₂`-open set is `t₁`-open. -/
@[kb "morris2024" "Definition 8.2.1, p. 199"]
theorem morris_8_2_1 {X : Type*} (t₁ t₂ : TopologicalSpace X) :
    t₁ ≤ t₂ ↔ ∀ U : Set X, IsOpen[t₂] U → IsOpen[t₁] U :=
  TopologicalSpace.le_def.trans Iff.rfl

/-- Morris, Topology Without Tears, Definition 8.2.3 (TP-181). A map is open iff it sends open sets to open
sets. -/
@[kb "morris2024" "Definition 8.2.3, p. 199"]
theorem morris_8_2_3 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    IsOpenMap f ↔ ∀ U : Set X, IsOpen U → IsOpen (f '' U) :=
  Iff.rfl

/-- Morris, Topology Without Tears, Definition 8.2.3 (TP-181). A map is closed iff it sends closed sets to
closed sets. -/
@[kb "morris2024" "Definition 8.2.3, p. 199"]
theorem morris_8_2_3_b {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    IsClosedMap f ↔ ∀ A : Set X, IsClosed A → IsClosed (f '' A) :=
  Iff.rfl

/-- Morris, Topology Without Tears, Proposition 8.2.5 (TP-183). The projections of a product of nonempty spaces
are continuous, surjective and open. -/
@[kb "morris2024" "Proposition 8.2.5, p. 200"]
theorem morris_8_2_5 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X] [Nonempty Y] :
    (Continuous (Prod.fst : X × Y → X) ∧ Function.Surjective (Prod.fst : X × Y → X) ∧
        IsOpenMap (Prod.fst : X × Y → X)) ∧
      (Continuous (Prod.snd : X × Y → Y) ∧ Function.Surjective (Prod.snd : X × Y → Y) ∧
        IsOpenMap (Prod.snd : X × Y → Y)) :=
  ⟨⟨continuous_fst, Prod.fst_surjective, isOpenMap_fst⟩, ⟨continuous_snd, Prod.snd_surjective, isOpenMap_snd⟩⟩

/-- Morris, Topology Without Tears, Corollary 8.2.7 (TP-183). The product topology is the coarsest topology on
`X × Y` making both projections continuous. -/
@[kb "morris2024" "Corollary 8.2.7, p. 201"]
theorem morris_8_2_7 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (t : TopologicalSpace (X × Y))
    (h1 : Continuous[t, inferInstance] (Prod.fst : X × Y → X))
    (h2 : Continuous[t, inferInstance] (Prod.snd : X × Y → Y)) :
    t ≤ instTopologicalSpaceProd :=
  by
  rw [continuous_iff_le_induced] at h1 h2
  exact le_inf h1 h2

/-- Morris, Topology Without Tears, Proposition 8.2.8 (TP-184). Each factor is homeomorphic to a subspace of the
product: `x ↦ (x, y)` is an embedding onto the slice `X × {y}`. -/
@[kb "morris2024" "Proposition 8.2.8, p. 202"]
theorem morris_8_2_8 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (y : Y) :
    IsEmbedding (fun x : X => (x, y)) ∧ range (fun x : X => (x, y)) = (univ : Set X) ×ˢ ({y} : Set Y) := by
  refine ⟨isEmbedding_prodMkLeft y, ?_⟩
  ext ⟨a, b⟩
  simp [eq_comm]

/-- Morris, Topology Without Tears, Theorem 8.3.1 (TP-185). A product of two compact spaces is compact. -/
@[kb "morris2024" "Theorem 8.3.1, p. 204"]
theorem morris_8_3_1 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X]
    [CompactSpace Y] : CompactSpace (X × Y) :=
  inferInstance

/-- Morris, Topology Without Tears, Theorem 8.3.1 (TP-185). A finite product of compact spaces is compact. -/
@[kb "morris2024" "Theorem 8.3.1, p. 204"]
theorem morris_8_3_1_b (n : ℕ) {X : Fin n → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, CompactSpace (X i)] :
    CompactSpace (∀ i, X i) :=
  inferInstance

/-- Morris, Topology Without Tears, Proposition 8.3.2 (TP-186). If the product of two nonempty spaces is compact,
so is each factor. -/
@[kb "morris2024" "Proposition 8.3.2, p. 205"]
theorem morris_8_3_2 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X] [Nonempty Y]
    [CompactSpace (X × Y)] : CompactSpace X ∧ CompactSpace Y :=
  ⟨Function.Surjective.compactSpace (f := (Prod.fst : X × Y → X)) continuous_fst Prod.fst_surjective,
    Function.Surjective.compactSpace (f := (Prod.snd : X × Y → Y)) continuous_snd Prod.snd_surjective⟩

/-- Morris, Topology Without Tears, Example 8.3.4 (TP-187). The unit sphere in `ℝⁿ⁺¹` is compact. -/
@[kb "morris2024" "Example 8.3.4, p. 206"]
theorem morris_8_3_4 (n : ℕ) : IsCompact (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  isCompact_sphere 0 1

/-- Morris, Topology Without Tears, Example 8.3.5 (TP-187). The cylinder `S¹ × [0, 1]` is compact. -/
@[kb "morris2024" "Example 8.3.5, p. 207"]
theorem morris_8_3_5 :
    IsCompact (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ Icc (0 : ℝ) 1) :=
  (isCompact_sphere 0 1).prod isCompact_Icc

/-- Morris, Topology Without Tears, Theorem 8.3.3 (TP-174). A subset of `ℝⁿ` is compact iff it is closed and
bounded. -/
@[kb "morris2024" "Theorem 8.3.3, p. 205"]
theorem morris_8_3_3 (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n))) :
    IsCompact A ↔ IsClosed A ∧ Bornology.IsBounded A :=
  Metric.isCompact_iff_isClosed_bounded

/-- Morris, Topology Without Tears, Definition 8.4.1 (TP-188). The component of `x` is the union of all connected
subsets containing `x`. -/
@[kb "morris2024" "Definition 8.4.1, p. 214"]
theorem morris_8_4_1 {X : Type*} [TopologicalSpace X] (x : X) :
    connectedComponent x = ⋃₀ {S : Set X | IsPreconnected S ∧ x ∈ S} :=
  rfl

/-- Morris, Topology Without Tears, Proposition 8.4.2 (TP-189). The component of `x` is connected, contains `x`,
and contains every connected set containing `x`. -/
@[kb "morris2024" "Proposition 8.4.2, p. 214"]
theorem morris_8_4_2 {X : Type*} [TopologicalSpace X] (x : X) :
    IsConnected (connectedComponent x) ∧ x ∈ connectedComponent x ∧
      ∀ S : Set X, IsPreconnected S → x ∈ S → S ⊆ connectedComponent x :=
  ⟨isConnected_connectedComponent, mem_connectedComponent, fun _ hS hx => hS.subset_connectedComponent hx⟩

/-- Morris, Topology Without Tears, Lemma 8.4.4 (TP-190). If a connected set contains `a` and `b`, their
components coincide. -/
@[kb "morris2024" "Lemma 8.4.4, p. 215"]
theorem morris_8_4_4 {X : Type*} [TopologicalSpace X] (S : Set X) (hS : IsPreconnected S) (a b : X)
    (ha : a ∈ S) (hb : b ∈ S) : connectedComponent a = connectedComponent b :=
  connectedComponent_eq (hS.subset_connectedComponent ha hb)

/-- Morris, Topology Without Tears, Proposition 8.4.5 (TP-191). A product of two spaces is connected iff each
factor is connected. -/
@[kb "morris2024" "Proposition 8.4.5, p. 215"]
theorem morris_8_4_5 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    ConnectedSpace (X × Y) ↔ ConnectedSpace X ∧ ConnectedSpace Y := by
  constructor
  · intro h
    have : Nonempty X := h.toNonempty.map Prod.fst
    have : Nonempty Y := h.toNonempty.map Prod.snd
    exact ⟨Function.Surjective.connectedSpace (Prod.fst_surjective (β := Y)) continuous_fst,
      Function.Surjective.connectedSpace (Prod.snd_surjective (α := X)) continuous_snd⟩
  · rintro ⟨h1, h2⟩
    infer_instance

/-- Morris, Topology Without Tears, Remark 8.4.6 (TP-192). Every component is a closed set. -/
@[kb "morris2024" "Remark 8.4.6, p. 216"]
theorem morris_8_4_6 {X : Type*} [TopologicalSpace X] (x : X) : IsClosed (connectedComponent x) :=
  isClosed_connectedComponent

/-- Morris, Topology Without Tears, Theorem 8.5.1 (TP-195), Fundamental Theorem of Algebra. Every nonconstant
complex polynomial has a complex root. -/
@[kb "morris2024" "Theorem 8.5.1, p. 218"]
theorem morris_8_5_1 (f : Polynomial ℂ) (hf : 0 < f.degree) : ∃ z : ℂ, f.IsRoot z :=
  Complex.exists_root hf

/-- Morris, Topology Without Tears, Section 8.4 (TP-203). A space is locally connected iff it has a basis of
connected open sets. -/
@[kb "morris2024" "Definition 8.4, p. 217"]
theorem morris_8_4_locallyConnected {X : Type*} [TopologicalSpace X] :
    LocallyConnectedSpace X ↔
      TopologicalSpace.IsTopologicalBasis {S : Set X | IsOpen S ∧ IsPreconnected S} :=
  locallyConnectedSpace_iff_isTopologicalBasis_isOpen_isPreconnected

end UndergradKB.Topology.Course
