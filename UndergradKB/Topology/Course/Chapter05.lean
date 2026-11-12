import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.InductiveDimension.Classes
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import UndergradKB.Common.Attr

/-!
# Course layer: Morris, Topology Without Tears, Chapter 5

Thin wrappers of Mathlib results (continuity, connectedness, path-connectedness, components).
-/

open Set Topology TopologicalSpace Filter

namespace UndergradKB.Topology.Course

/-- Morris, Topology Without Tears, Lemma 5.1.2 and Proposition 5.1.7 (TP-077). A map is continuous iff for each
point and each open `U` around its image there is an open `V` around the point with `f(V) ⊆ U`. -/
@[kb "morris2024" "Lemma 5.1.2, p. 112"]
theorem morris_5_1_2 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    Continuous f ↔ ∀ a : X, ∀ U : Set Y, IsOpen U → f a ∈ U → ∃ V : Set X, IsOpen V ∧ a ∈ V ∧ f '' V ⊆ U := by
  constructor
  · intro h a U hU ha
    exact ⟨f ⁻¹' U, hU.preimage h, ha, image_preimage_subset f U⟩
  · intro h
    rw [continuous_def]
    intro U hU
    rw [isOpen_iff_forall_mem_open]
    intro a ha
    obtain ⟨V, hV, haV, hs⟩ := h a U hU ha
    exact ⟨V, fun v hv => hs ⟨v, hv, rfl⟩, hV, haV⟩

/-- Morris, Topology Without Tears, Lemma 5.1.1 (TP-076). A function `ℝ → ℝ` is continuous iff for every point
and open `U` around its image there is an open `V` around the point with `f(V) ⊆ U`. -/
@[kb "morris2024" "Lemma 5.1.1, p. 111"]
theorem morris_5_1_1 (f : ℝ → ℝ) :
    Continuous f ↔ ∀ a : ℝ, ∀ U : Set ℝ, IsOpen U → f a ∈ U → ∃ V : Set ℝ, IsOpen V ∧ a ∈ V ∧ f '' V ⊆ U :=
  morris_5_1_2 f

/-- Morris, Topology Without Tears, Definition 5.1.3 (TP-078). A map is continuous iff preimages of open sets are
open. -/
@[kb "morris2024" "Definition 5.1.3, p. 112"]
theorem morris_5_1_3 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    Continuous f ↔ ∀ U : Set Y, IsOpen U → IsOpen (f ⁻¹' U) :=
  continuous_def

/-- Morris, Topology Without Tears, Proposition 5.1.8 (TP-079). A composite of continuous maps is continuous. -/
@[kb "morris2024" "Proposition 5.1.8, p. 114"]
theorem morris_5_1_8 {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : X → Y} {g : Y → Z} (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) :=
  hg.comp hf

/-- Morris, Topology Without Tears, Proposition 5.1.9 (TP-080). A map is continuous iff preimages of closed sets
are closed. -/
@[kb "morris2024" "Proposition 5.1.9, p. 114"]
theorem morris_5_1_9 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    Continuous f ↔ ∀ C : Set Y, IsClosed C → IsClosed (f ⁻¹' C) :=
  continuous_iff_isClosed

/-- Morris, Topology Without Tears, Proposition 5.1.11 (TP-081). A bijection is a homeomorphism iff it and its
inverse are continuous. -/
@[kb "morris2024" "Proposition 5.1.11, p. 115"]
theorem morris_5_1_11 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ Y) :
    (Continuous e ∧ Continuous e.symm) ↔ ∃ h : X ≃ₜ Y, h.toEquiv = e := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨e, h1, h2⟩, rfl⟩
  · rintro ⟨h, rfl⟩
    exact ⟨h.continuous, h.symm.continuous⟩

/-- Morris, Topology Without Tears, Proposition 5.1.12 (TP-082). The restriction of a continuous map to a
subspace is continuous. -/
@[kb "morris2024" "Proposition 5.1.12, p. 115"]
theorem morris_5_1_12 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : Continuous f) (A : Set X) : Continuous (A.domRestrict f) :=
  hf.comp continuous_subtype_val

/-- Morris, Topology Without Tears, Exercises 5.1 (TP-083). `τ₁` is finer than `τ₂` (every `τ₂`-open set is
`τ₁`-open) iff the identity is continuous from `τ₁` to `τ₂`. -/
@[kb "morris2024" "Exercises 5.1, p. 116"]
theorem morris_ex_5_1_a {X : Type*} (t₁ t₂ : TopologicalSpace X) :
    (∀ U : Set X, IsOpen[t₂] U → IsOpen[t₁] U) ↔ Continuous[t₁, t₂] (id : X → X) :=
  continuous_def.symm

/-- Morris, Topology Without Tears, Exercises 5.1 (TP-083). Being finer is Mathlib's order `t₁ ≤ t₂`. -/
@[kb "morris2024" "Exercises 5.1, p. 116"]
theorem morris_ex_5_1_b {X : Type*} (t₁ t₂ : TopologicalSpace X) :
    (∀ U : Set X, IsOpen[t₂] U → IsOpen[t₁] U) ↔ t₁ ≤ t₂ := by
  rw [← continuous_id_iff_le]
  exact continuous_def.symm

/-- Morris, Topology Without Tears, Proposition 5.2.1 (TP-084). The continuous image of a connected space is
connected. -/
@[kb "morris2024" "Proposition 5.2.1, p. 117"]
theorem morris_5_2_1 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [ConnectedSpace X]
    {f : X → Y} (hf : Continuous f) : IsConnected (Set.range f) :=
  isConnected_range hf

/-- Morris, Topology Without Tears, Proposition 5.2.1 (TP-084). A continuous surjective image of a connected
space is connected. -/
@[kb "morris2024" "Proposition 5.2.1, p. 117"]
theorem morris_5_2_1_b {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [ConnectedSpace X]
    {f : X → Y} (hf : Continuous f) (hs : Function.Surjective f) : ConnectedSpace Y :=
  hs.connectedSpace hf

/-- Morris, Topology Without Tears, Definition 5.2.3 (TP-085). A nonempty space is path-connected iff any two
points are joined by a continuous path from `[0,1]`. -/
@[kb "morris2024" "Definition 5.2.3, p. 118"]
theorem morris_5_2_3 {X : Type*} [TopologicalSpace X] [Nonempty X] :
    PathConnectedSpace X ↔
      ∀ x y : X, ∃ γ : C(unitInterval, X), γ 0 = x ∧ γ 1 = y := by
  constructor
  · intro h x y
    obtain ⟨p⟩ := PathConnectedSpace.joined x y
    exact ⟨p.toContinuousMap, p.source, p.target⟩
  · intro h
    refine ⟨inferInstance, fun x y => ?_⟩
    obtain ⟨γ, h0, h1⟩ := h x y
    exact ⟨⟨γ, h0, h1⟩⟩

/-- Morris, Topology Without Tears, Proposition 5.2.6 (TP-087). Every path-connected space is connected. -/
@[kb "morris2024" "Proposition 5.2.6, p. 118"]
theorem morris_5_2_6 {X : Type*} [TopologicalSpace X] [PathConnectedSpace X] : ConnectedSpace X :=
  inferInstance

/-- Morris, Topology Without Tears, Theorem 5.2.9 (TP-090). Intermediate value theorem: a function continuous
on `[a,b]` attains every value between `f a` and `f b`. -/
@[kb "morris2024" "Theorem 5.2.9, p. 119"]
theorem morris_5_2_9 {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b))
    {y : ℝ} (hy : y ∈ Set.uIcc (f a) (f b)) : ∃ c ∈ Set.Icc a b, f c = y := by
  rw [← uIcc_of_le hab] at hf ⊢
  exact intermediate_value_uIcc hf hy

/-- Morris, Topology Without Tears, Corollary 5.2.10 (TP-091). A function continuous on `[a,b]` with
`f a > 0 > f b` has a zero in `[a,b]`. -/
@[kb "morris2024" "Corollary 5.2.10, p. 119"]
theorem morris_5_2_10 {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b))
    (ha : 0 < f a) (hb : f b < 0) : ∃ c ∈ Set.Icc a b, f c = 0 :=
  intermediate_value_Icc' hab hf ⟨hb.le, ha.le⟩

/-- Morris, Topology Without Tears, Exercises 5.2 (TP-094). The component of a point is the union of all
connected sets containing it; it is connected, closed, and contains every connected set through the point. -/
@[kb "morris2024" "Exercises 5.2, p. 121"]
theorem morris_ex_5_2_a {X : Type*} [TopologicalSpace X] (x : X) :
    connectedComponent x = ⋃₀ {S : Set X | IsConnected S ∧ x ∈ S} := by
  ext y
  constructor
  · intro hy
    exact ⟨connectedComponent x, ⟨isConnected_connectedComponent, mem_connectedComponent⟩, hy⟩
  · rintro ⟨S, ⟨hS, hxS⟩, hyS⟩
    exact hS.isPreconnected.subset_connectedComponent hxS hyS

/-- Morris, Topology Without Tears, Exercises 5.2 (TP-094). The component of a point is connected and closed. -/
@[kb "morris2024" "Exercises 5.2, p. 121"]
theorem morris_ex_5_2_b {X : Type*} [TopologicalSpace X] (x : X) :
    IsConnected (connectedComponent x) ∧ IsClosed (connectedComponent x) :=
  ⟨isConnected_connectedComponent, isClosed_connectedComponent⟩

/-- Morris, Topology Without Tears, Exercises 5.2 (TP-095). A space is totally disconnected iff every nonempty
connected subset is a singleton. -/
@[kb "morris2024" "Exercises 5.2, p. 122"]
theorem morris_ex_5_2_c {X : Type*} [TopologicalSpace X] :
    TotallyDisconnectedSpace X ↔ ∀ S : Set X, IsConnected S → ∃ x, S = {x} := by
  constructor
  · intro h S hS
    obtain ⟨x, hx⟩ := hS.nonempty
    exact ⟨x, (isTotallyDisconnected_of_totallyDisconnectedSpace S S subset_rfl hS.isPreconnected
      |>.eq_singleton_of_mem hx)⟩
  · intro h
    refine ⟨fun s _ hs => ?_⟩
    rcases s.eq_empty_or_nonempty with rfl | hne
    · exact subsingleton_empty
    · obtain ⟨x, rfl⟩ := h s ⟨hne, hs⟩
      exact subsingleton_singleton

/-- Morris, Topology Without Tears, Exercises 5.2 (TP-096). A space is zero-dimensional iff it has a basis of
clopen sets. -/
@[kb "morris2024" "Exercises 5.2, p. 122"]
theorem morris_ex_5_2_d {X : Type*} [TopologicalSpace X] :
    ZeroDimensionalSpace X ↔ ∃ B : Set (Set X), IsTopologicalBasis B ∧ ∀ U ∈ B, IsClopen U :=
  ⟨fun h => ⟨_, zeroDimensionalSpace_iff_isTopologicalBasis_isClopen.1 h, fun _ hU => hU⟩,
    fun ⟨_, hB, hc⟩ => ZeroDimensionalSpace.of_isTopologicalBasis hc hB⟩

end UndergradKB.Topology.Course
