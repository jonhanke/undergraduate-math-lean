import Mathlib.Topology.Bases
import Mathlib.Topology.Constructions
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Separation.NotNormal
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Order.Zorn
import UndergradKB.Common.Attr

/-!
# Course layer, Chapter 10 of Morris, Topology Without Tears

Sections 10.1 (arbitrary products), 10.2 (Zorn's lemma) and 10.3 (separation axioms, Urysohn,
Tietze), as thin wrappers of Mathlib results.
-/

namespace UndergradKB.Topology.Course

open Set TopologicalSpace Filter

/-! ### 10.1 Arbitrary products -/

/-- Morris, Topology Without Tears, Definition 10.1.1 (TP-240). Basic open sets of an arbitrary
product restrict finitely many coordinates to open sets. -/
@[kb "morris2024" "Definition 10.1.1, p. 261"]
theorem morris_10_1_1 {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] :
    IsTopologicalBasis { S : Set (∀ i, X i) | ∃ (U : ∀ i, Set (X i)) (F : Finset ι),
      (∀ i, i ∈ F → IsOpen (U i)) ∧ S = (F : Set ι).pi U } :=
  isTopologicalBasis_pi fun _ => isTopologicalBasis_opens

/-- Morris, Topology Without Tears, Proposition 10.1.3 (TP-241). A product of closed subsets is
closed in the product. -/
@[kb "morris2024" "Proposition 10.1.3, p. 262"]
theorem morris_10_1_3 {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    {A : ∀ i, Set (X i)} (hA : ∀ i, IsClosed (A i)) : IsClosed ((univ : Set ι).pi A) :=
  isClosed_set_pi fun i _ => hA i

/-- Morris, Topology Without Tears, Proposition 10.1.4 (TP-242). Bases of the factors give a basis of
the product, consisting of boxes of basic open sets restricted at finitely many coordinates. -/
@[kb "morris2024" "Proposition 10.1.4, p. 262"]
theorem morris_10_1_4 {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    {T : ∀ i, Set (Set (X i))} (hT : ∀ i, IsTopologicalBasis (T i)) :
    IsTopologicalBasis { S : Set (∀ i, X i) | ∃ (U : ∀ i, Set (X i)) (F : Finset ι),
      (∀ i, i ∈ F → U i ∈ T i) ∧ S = (F : Set ι).pi U } :=
  isTopologicalBasis_pi hT

/-- Morris, Topology Without Tears, Proposition 10.1.7 (TP-245). A product of continuous maps is
continuous on the product spaces. -/
@[kb "morris2024" "Proposition 10.1.7, p. 263"]
theorem morris_10_1_7 {ι : Type*} {X Y : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] {h : ∀ i, X i → Y i} (hh : ∀ i, Continuous (h i)) :
    Continuous (Pi.map h) :=
  Continuous.piMap hh

/-- Morris, Topology Without Tears, Proposition 10.1.8 (TP-246). A map into a product is continuous
iff each composite with a projection is continuous. -/
@[kb "morris2024" "Proposition 10.1.8, p. 263"]
theorem morris_10_1_8 {ι : Type*} {Z : Type*} {X : ι → Type*} [TopologicalSpace Z]
    [∀ i, TopologicalSpace (X i)] (f : Z → ∀ i, X i) :
    Continuous f ↔ ∀ i, Continuous (fun z => f z i) :=
  continuous_pi_iff

/-- Morris, Topology Without Tears, Definition 10.1.11 (TP-248). A map is an embedding iff it is a
homeomorphism of the domain onto its image (with the subspace topology), composed with inclusion. -/
@[kb "morris2024" "Definition 10.1.11, p. 264"]
theorem morris_10_1_11 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    _root_.Topology.IsEmbedding f ↔ ∃ e : X ≃ₜ range f, ∀ x, (e x : Y) = f x := by
  constructor
  · intro hf
    exact ⟨hf.toHomeomorph, fun _ => rfl⟩
  · rintro ⟨e, he⟩
    have : f = Subtype.val ∘ e := funext fun x => (he x).symm
    rw [this]
    exact _root_.Topology.IsEmbedding.subtypeVal.comp e.isEmbedding

/-! ### 10.2 Zorn's lemma -/

/-- Morris, Topology Without Tears, Definition 10.2.1 (TP-249). A partial order is a reflexive,
antisymmetric, transitive relation. -/
@[kb "morris2024" "Definition 10.2.1, p. 266"]
theorem morris_10_2_1 {α : Type*} (r : α → α → Prop) :
    IsPartialOrder α r ↔ (∀ a, r a a) ∧ (∀ a b, r a b → r b a → a = b) ∧
      (∀ a b c, r a b → r b c → r a c) := by
  constructor
  · intro h
    exact ⟨fun a => refl_of r a, fun a b => antisymm_of r, fun a b c => trans_of r⟩
  · rintro ⟨h1, h2, h3⟩
    exact
      { refl := h1
        trans := h3
        antisymm := h2 }

/-- Morris, Topology Without Tears, Definition 10.2.9 (TP-251). A partially ordered set is linearly
ordered iff any two elements are comparable (the whole set is a chain). -/
@[kb "morris2024" "Definition 10.2.9, p. 269"]
theorem morris_10_2_9 {α : Type*} [PartialOrder α] :
    IsChain (· ≤ ·) (univ : Set α) ↔ ∀ a b : α, a ≤ b ∨ b ≤ a := by
  constructor
  · intro h a b
    by_cases e : a = b
    · exact Or.inl e.le
    · exact h (mem_univ a) (mem_univ b) e
  · intro h a _ b _ _
    exact h a b

/-- Morris, Topology Without Tears, Definition 10.2.11 (TP-252). `a` is the greatest element of a
poset iff every element is below `a`. -/
@[kb "morris2024" "Definition 10.2.11, p. 269"]
theorem morris_10_2_11 {α : Type*} [PartialOrder α] (a : α) :
    IsGreatest (univ : Set α) a ↔ ∀ b : α, b ≤ a :=
  ⟨fun h b => h.2 (mem_univ b), fun h => ⟨mem_univ a, fun b _ => h b⟩⟩

/-- Morris, Topology Without Tears, Definition 10.2.12 (TP-253). `a` is an upper bound of a subset iff
it is above every element of the subset. -/
@[kb "morris2024" "Definition 10.2.12, p. 269"]
theorem morris_10_2_12 {α : Type*} [PartialOrder α] (S : Set α) (a : α) :
    a ∈ upperBounds S ↔ ∀ s ∈ S, s ≤ a :=
  Iff.rfl

/-- Morris, Topology Without Tears, Definition 10.2.13 (TP-254). An element is maximal iff nothing is
strictly above it. -/
@[kb "morris2024" "Definition 10.2.13, p. 270"]
theorem morris_10_2_13 {α : Type*} [PartialOrder α] (a : α) :
    IsMax a ↔ ¬ ∃ b : α, a < b := by
  rw [isMax_iff_forall_not_lt, not_exists]

/-- Morris, Topology Without Tears, Axiom 10.2.16 (TP-255). Zorn's lemma: a nonempty poset in which
every chain has an upper bound has a maximal element. -/
@[kb "morris2024" "Axiom 10.2.16, p. 270"]
theorem morris_10_2_16 {α : Type*} [PartialOrder α] [Nonempty α]
    (h : ∀ c : Set α, IsChain (· ≤ ·) c → BddAbove c) : ∃ m : α, IsMax m :=
  zorn_le h

/-! ### 10.3 Separation axioms, Urysohn, Tietze -/

/-- Morris, Topology Without Tears, Corollary 10.3.6 (TP-277). Every cube `I^A` is compact; for
`A = ℕ` this is the Hilbert cube. -/
@[kb "morris2024" "Corollary 10.3.6, p. 275"]
theorem morris_10_3_6 (A : Type*) : CompactSpace (A → Icc (0 : ℝ) 1) :=
  inferInstance

/-- Morris, Topology Without Tears, Definition 10.3.8 (TP-279). A space is completely regular iff a
point and an open neighbourhood are separated by a continuous map to `[0,1]`. -/
@[kb "morris2024" "Definition 10.3.8, p. 275"]
theorem morris_10_3_8 {X : Type*} [TopologicalSpace X] :
    CompletelyRegularSpace X ↔ ∀ x : X, ∀ U : Set X, IsOpen U → x ∈ U →
      ∃ f : X → Icc (0 : ℝ) 1, Continuous f ∧ f x = 0 ∧ ∀ y ∈ Uᶜ, f y = 1 :=
  completelyRegularSpace_iff_isOpen

/-- Morris, Topology Without Tears, Definition 10.3.8 (TP-279). A Tychonoff space is a completely
regular Hausdorff space. -/
@[kb "morris2024" "Definition 10.3.8, p. 275"]
theorem morris_10_3_8_b {X : Type*} [TopologicalSpace X] :
    T35Space X ↔ CompletelyRegularSpace X ∧ T2Space X := by
  constructor
  · intro h
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨h1, h2⟩
    exact {}

/-- Morris, Topology Without Tears, Proposition 10.3.9 (TP-280). Every metric space is a Tychonoff
space. -/
@[kb "morris2024" "Proposition 10.3.9, p. 276"]
theorem morris_10_3_9 {X : Type*} [MetricSpace X] : T35Space X :=
  inferInstance

/-- Morris, Topology Without Tears, Corollary 10.3.10 (TP-280). The interval `[0,1]` is a Tychonoff
space. -/
@[kb "morris2024" "Corollary 10.3.10, p. 276"]
theorem morris_10_3_10 : T35Space (Icc (0 : ℝ) 1) :=
  inferInstance

/-- Morris, Topology Without Tears, Proposition 10.3.11 (TP-281). A product of completely regular
spaces is completely regular. -/
@[kb "morris2024" "Proposition 10.3.11, p. 276"]
theorem morris_10_3_11 {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, CompletelyRegularSpace (X i)] : CompletelyRegularSpace (∀ i, X i) :=
  inferInstance

/-- Morris, Topology Without Tears, Proposition 10.3.12 (TP-282). A product of Hausdorff spaces is
Hausdorff. -/
@[kb "morris2024" "Proposition 10.3.12, p. 277"]
theorem morris_10_3_12 {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, T2Space (X i)] : T2Space (∀ i, X i) :=
  Pi.t2Space

/-- Morris, Topology Without Tears, Corollary 10.3.13 (TP-283). A product of Tychonoff spaces is
Tychonoff. -/
@[kb "morris2024" "Corollary 10.3.13, p. 277"]
theorem morris_10_3_13 {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, T35Space (X i)] : T35Space (∀ i, X i) :=
  inferInstance

/-- Morris, Topology Without Tears, Corollary 10.3.14 (TP-283). Every cube `I^A` is Tychonoff. -/
@[kb "morris2024" "Corollary 10.3.14, p. 277"]
theorem morris_10_3_14 (A : Type*) : T35Space (A → Icc (0 : ℝ) 1) :=
  inferInstance

/-- Morris, Topology Without Tears, Proposition 10.3.15 (TP-284). A subspace of a completely regular
space is completely regular. -/
@[kb "morris2024" "Proposition 10.3.15, p. 277"]
theorem morris_10_3_15 {X : Type*} [TopologicalSpace X] [CompletelyRegularSpace X] (A : Set X) :
    CompletelyRegularSpace A :=
  inferInstance

/-- Morris, Topology Without Tears, Corollary 10.3.16 (TP-284). A subspace of a Tychonoff space is
Tychonoff. -/
@[kb "morris2024" "Corollary 10.3.16, p. 277"]
theorem morris_10_3_16 {X : Type*} [TopologicalSpace X] [T35Space X] (A : Set X) : T35Space A :=
  inferInstance

/-- Morris, Topology Without Tears, Definition 10.3.20 (TP-287). A space is normal iff disjoint closed
sets have disjoint open neighbourhoods. -/
@[kb "morris2024" "Definition 10.3.20, p. 278"]
theorem morris_10_3_20 {X : Type*} [TopologicalSpace X] :
    NormalSpace X ↔ ∀ s t : Set X, IsClosed s → IsClosed t → Disjoint s t →
      ∃ u v : Set X, IsOpen u ∧ IsOpen v ∧ s ⊆ u ∧ t ⊆ v ∧ Disjoint u v :=
  ⟨fun h s t hs ht hd => h.normal s t hs ht hd, fun h => ⟨fun s t hs ht hd => h s t hs ht hd⟩⟩

/-- Morris, Topology Without Tears, Definition 10.3.20 (TP-287). A T4-space is a normal Hausdorff
space. -/
@[kb "morris2024" "Definition 10.3.20, p. 278"]
theorem morris_10_3_20_b {X : Type*} [TopologicalSpace X] :
    T4Space X ↔ NormalSpace X ∧ T2Space X := by
  constructor
  · intro h
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨h1, h2⟩
    exact {}

/-- Morris, Topology Without Tears, Remark 10.3.21 (TP-288). Every metrizable space is normal. -/
@[kb "morris2024" "Remark 10.3.21, p. 278"]
theorem morris_10_3_21 {X : Type*} [TopologicalSpace X] [MetrizableSpace X] : NormalSpace X := by
  letI := metrizableSpaceMetric X
  infer_instance

/-- Morris, Topology Without Tears, Theorem 10.3.22 (TP-289). Urysohn's lemma: disjoint closed sets of
a normal space are separated by a continuous map to `[0,1]`, equal to 0 on one and 1 on the other. -/
@[kb "morris2024" "Theorem 10.3.22, p. 279"]
theorem morris_10_3_22 {X : Type*} [TopologicalSpace X] [NormalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hd : Disjoint A B) :
    ∃ f : X → Icc (0 : ℝ) 1, Continuous f ∧ (∀ x ∈ A, f x = 0) ∧ ∀ x ∈ B, f x = 1 := by
  obtain ⟨f, h0, h1, hI⟩ := exists_continuous_zero_one_of_isClosed hA hB hd
  exact ⟨fun x => ⟨f x, hI x⟩, f.continuous.subtype_mk _,
    fun x hx => Subtype.ext (h0 hx), fun x hx => Subtype.ext (h1 hx)⟩

/-- Morris, Topology Without Tears, Corollary 10.3.23 (TP-290). A normal Hausdorff space is a Tychonoff
space. -/
@[kb "morris2024" "Corollary 10.3.23, p. 280"]
theorem morris_10_3_23 {X : Type*} [TopologicalSpace X] [NormalSpace X] [T2Space X] : T35Space X := by
  have : T4Space X := {}
  infer_instance

/-- Morris, Topology Without Tears, Proposition 10.3.24 (TP-291). Every compact Hausdorff space is
normal. -/
@[kb "morris2024" "Proposition 10.3.24, p. 280"]
theorem morris_10_3_24 {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    NormalSpace X :=
  inferInstance

/-- Morris, Topology Without Tears, Definition 10.3.27 (TP-293). A space is regular iff a point and a
closed set not containing it have disjoint open neighbourhoods. -/
@[kb "morris2024" "Definition 10.3.27, p. 281"]
theorem morris_10_3_27 {X : Type*} [TopologicalSpace X] :
    RegularSpace X ↔ ∀ (x : X) (C : Set X), IsClosed C → x ∉ C →
      ∃ u v : Set X, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ C ⊆ v ∧ Disjoint u v := by
  rw [regularSpace_iff]
  constructor
  · intro h x C hC hx
    have := (separatedNhds_iff_disjoint.2 (by simpa using (h hC hx).symm) :
      SeparatedNhds ({x} : Set X) C)
    obtain ⟨u, v, hu, hv, hxu, hCv, hd⟩ := this
    exact ⟨u, v, hu, hv, hxu rfl, hCv, hd⟩
  · intro h C x hC hx
    obtain ⟨u, v, hu, hv, hxu, hCv, hd⟩ := h x C hC hx
    have : SeparatedNhds ({x} : Set X) C :=
      ⟨u, v, hu, hv, by simpa using hxu, hCv, hd⟩
    simpa [nhdsSet_singleton] using (separatedNhds_iff_disjoint.1 this).symm

/-- Morris, Topology Without Tears, Definition 10.3.27 (TP-293). A T3-space is a regular Hausdorff
space. -/
@[kb "morris2024" "Definition 10.3.27, p. 281"]
theorem morris_10_3_27_b {X : Type*} [TopologicalSpace X] :
    T3Space X ↔ RegularSpace X ∧ T2Space X := by
  constructor
  · intro h
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨h1, h2⟩
    exact {}

/-- Morris, Topology Without Tears, Remark 10.3.28 (TP-294). A normal T1 space is regular (T4 implies
T3). -/
@[kb "morris2024" "Remark 10.3.28, p. 282"]
theorem morris_10_3_28 {X : Type*} [TopologicalSpace X] [NormalSpace X] [T1Space X] :
    RegularSpace X :=
  inferInstance

/-- Morris, Topology Without Tears, Proposition 10.3.29 (TP-295). Every normal second countable
Hausdorff space is metrizable. -/
@[kb "morris2024" "Proposition 10.3.29, p. 284"]
theorem morris_10_3_29 {X : Type*} [TopologicalSpace X] [NormalSpace X] [T2Space X]
    [SecondCountableTopology X] : MetrizableSpace X := by
  have : T4Space X := {}
  infer_instance

/-- Morris, Topology Without Tears, Lemma 10.3.30 (TP-296). Every regular second countable space is
normal. -/
@[kb "morris2024" "Lemma 10.3.30, p. 285"]
theorem morris_10_3_30 {X : Type*} [TopologicalSpace X] [RegularSpace X]
    [SecondCountableTopology X] : NormalSpace X :=
  inferInstance

/-- Morris, Topology Without Tears, Theorem 10.3.31 (TP-297). Urysohn's metrization theorem: every
regular second countable Hausdorff space is metrizable. -/
@[kb "morris2024" "Theorem 10.3.31, p. 285"]
theorem morris_10_3_31 {X : Type*} [TopologicalSpace X] [RegularSpace X] [T2Space X]
    [SecondCountableTopology X] : MetrizableSpace X := by
  have : T3Space X := {}
  infer_instance

/-- Morris, Topology Without Tears, Lemma 10.3.45 (TP-308). If every map from `S` to `Y` extends to
`X` and `Z` is homeomorphic to `Y`, then every map from `S` to `Z` extends to `X`. -/
@[kb "morris2024" "Lemma 10.3.45, p. 293"]
theorem morris_10_3_45 {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (S : Set X) (e : Y ≃ₜ Z)
    (h : ∀ f : C(S, Y), ∃ g : C(X, Y), ∀ s : S, g s = f s) :
    ∀ f : C(S, Z), ∃ g : C(X, Z), ∀ s : S, g s = f s := by
  intro f
  obtain ⟨g, hg⟩ := h ⟨e.symm ∘ f, e.symm.continuous.comp f.continuous⟩
  refine ⟨⟨e ∘ g, e.continuous.comp g.continuous⟩, fun s => ?_⟩
  simp [hg s]

/-- Morris, Topology Without Tears, Lemma 10.3.49 (TP-311). If `Z` is a retract of `Y` and every map
from `S` to `Y` extends to `X`, then every map from `S` to `Z` extends to `X`. -/
@[kb "morris2024" "Lemma 10.3.49, p. 294"]
theorem morris_10_3_49 {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (S : Set X) (i : C(Z, Y)) (r : C(Y, Z)) (hri : ∀ z, r (i z) = z)
    (h : ∀ f : C(S, Y), ∃ g : C(X, Y), ∀ s : S, g s = f s) :
    ∀ f : C(S, Z), ∃ g : C(X, Z), ∀ s : S, g s = f s := by
  intro f
  obtain ⟨g, hg⟩ := h (i.comp f)
  refine ⟨r.comp g, fun s => ?_⟩
  simp [hg s, hri]

/-- Morris, Topology Without Tears, Lemma 10.3.50 (TP-312). If maps from `S` into each `Y i` extend to
`X`, then maps from `S` into the product of the `Y i` extend to `X`. -/
@[kb "morris2024" "Lemma 10.3.50, p. 295"]
theorem morris_10_3_50 {X : Type*} [TopologicalSpace X] {ι : Type*} {Y : ι → Type*}
    [∀ i, TopologicalSpace (Y i)] (S : Set X)
    (h : ∀ i, ∀ f : C(S, Y i), ∃ g : C(X, Y i), ∀ s : S, g s = f s) :
    ∀ f : C(S, ∀ i, Y i), ∃ g : C(X, ∀ i, Y i), ∀ s : S, g s = f s := by
  intro f
  choose g hg using fun i =>
    h i ⟨fun s => f s i, (continuous_apply i).comp f.continuous⟩
  refine ⟨ContinuousMap.pi g, fun s => ?_⟩
  funext i
  exact hg i s

end UndergradKB.Topology.Course
