import Mathlib.Topology.Bases
import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.Instances.Int
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Basic
import UndergradKB.Common.Attr

/-! # Course layer, Morris Chapter 2: the euclidean topology and bases

Thin wrappers of Mathlib results, stated in the terms of Morris, *Topology Without Tears*, Chapter 2.
-/

namespace UndergradKB.Topology.Course

open Set

section Chapter02

variable {X Y : Type*}

/-- Morris, Topology Without Tears, Remark 2.1.2 (ii), (iii) (TP-020). Open intervals and open rays are open
in `ℝ`. -/
@[kb "morris2024" "Remark 2.1.2, p. 52"]
theorem morris_2_1_2_a (r s : ℝ) :
    IsOpen (Ioo r s) ∧ IsOpen (Ioi r) ∧ IsOpen (Iio r) :=
  ⟨isOpen_Ioo, isOpen_Ioi, isOpen_Iio⟩

/-- Morris, Topology Without Tears, Remark 2.1.2 (vi), (vii), (viii) (TP-022). Closed intervals and singletons
are closed in `ℝ`, so `ℝ` is a `T₁` space. -/
@[kb "morris2024" "Remark 2.1.2, p. 53"]
theorem morris_2_1_2_b (c d : ℝ) :
    IsClosed (Icc c d) ∧ (∀ a : ℝ, IsClosed ({a} : Set ℝ)) ∧ T1Space ℝ :=
  ⟨isClosed_Icc, fun _ => isClosed_singleton, inferInstance⟩

/-- Morris, Topology Without Tears, Remark 2.1.2 (ix) (TP-023). The set of integers is closed in `ℝ`. -/
@[kb "morris2024" "Remark 2.1.2, p. 54"]
theorem morris_2_1_2_c : IsClosed (range ((↑) : ℤ → ℝ)) :=
  Int.isClosedEmbedding_coe_real.isClosed_range

/-- Morris, Topology Without Tears, Section 2.1 (TP-025). A `G_δ` set is a countable intersection of open
sets. -/
@[kb "morris2024" "Section 2.1, p. 55"]
theorem morris_2_1_Gdelta [TopologicalSpace X] (A : Set X) :
    IsGδ A ↔ ∃ T : Set (Set X), (∀ t ∈ T, IsOpen t) ∧ T.Countable ∧ A = ⋂₀ T :=
  Iff.rfl

/-- Morris, Topology Without Tears, Definition 2.2.2 (TP-028). A collection `B` of open sets is a basis for
the topology when every open set is a union of members of `B`. -/
@[kb "morris2024" "Definition 2.2.2, p. 57"]
theorem morris_2_2_2 [TopologicalSpace X] (B : Set (Set X)) (hB : ∀ b ∈ B, IsOpen b) :
    TopologicalSpace.IsTopologicalBasis B ↔ ∀ U : Set X, IsOpen U → ∃ S ⊆ B, U = ⋃₀ S := by
  refine ⟨fun h U hU => h.open_eq_sUnion hU, fun h => ?_⟩
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds hB fun a U ha hU => ?_
  obtain ⟨S, hS, rfl⟩ := h U hU
  obtain ⟨b, hb, hab⟩ := mem_sUnion.1 ha
  exact ⟨b, hS hb, hab, subset_sUnion_of_mem hb⟩

/-- Morris, Topology Without Tears, Proposition 2.2.1 (TP-027). A subset of `ℝ` is open iff it is a union of
open intervals. -/
@[kb "morris2024" "Proposition 2.2.1, p. 56"]
theorem morris_2_2_1 (U : Set ℝ) :
    IsOpen U ↔ ∃ F : Set (Set ℝ), (∀ I ∈ F, ∃ a b : ℝ, I = Ioo a b) ∧ U = ⋃₀ F := by
  have hB : TopologicalSpace.IsTopologicalBasis {s : Set ℝ | ∃ a b : ℝ, s = Ioo a b} := by
    refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro _ ⟨a, b, rfl⟩
      exact isOpen_Ioo
    · intro a V ha hV
      obtain ⟨l, u, hlu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 (hV.mem_nhds ha)
      exact ⟨Ioo l u, ⟨l, u, rfl⟩, hlu, hsub⟩
  rw [hB.open_iff_eq_sUnion]
  exact ⟨fun ⟨S, hS, h⟩ => ⟨S, fun I hI => hS hI, h⟩, fun ⟨S, hS, h⟩ => ⟨S, fun I hI => hS I hI, h⟩⟩

/-- Morris, Topology Without Tears, Exercise 2.2.3 (TP-027). The open intervals form a basis of `ℝ`. -/
@[kb "morris2024" "Exercise 2.2.3, p. 57"]
theorem morris_2_2_3 :
    TopologicalSpace.IsTopologicalBasis {s : Set ℝ | ∃ a b : ℝ, s = Ioo a b} := by
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro _ ⟨a, b, rfl⟩
    exact isOpen_Ioo
  · intro a V ha hV
    obtain ⟨l, u, hlu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 (hV.mem_nhds ha)
    exact ⟨Ioo l u, ⟨l, u, rfl⟩, hlu, hsub⟩

/-- Morris, Topology Without Tears, Remark 2.2.6 (TP-029). The topology is a basis for itself, and any family
lying between a basis and the topology is again a basis. -/
@[kb "morris2024" "Remark 2.2.6, p. 58"]
theorem morris_2_2_6 [TopologicalSpace X] :
    TopologicalSpace.IsTopologicalBasis {U : Set X | IsOpen U} ∧
      ∀ B C : Set (Set X), TopologicalSpace.IsTopologicalBasis B → B ⊆ C → (∀ u ∈ C, IsOpen u) →
        TopologicalSpace.IsTopologicalBasis C :=
  ⟨TopologicalSpace.isTopologicalBasis_opens, fun _ _ hB hBC hC =>
    hB.of_isOpen_of_subset hC hBC⟩

/-- Morris, Topology Without Tears, Proposition 2.3.2 (TP-032). A family of open sets is a basis iff each open
set around each point contains a member of the family around that point. -/
@[kb "morris2024" "Proposition 2.3.2, p. 64"]
theorem morris_2_3_2 [TopologicalSpace X] (B : Set (Set X)) (hB : ∀ b ∈ B, IsOpen b) :
    TopologicalSpace.IsTopologicalBasis B ↔
      ∀ (U : Set X) (x : X), IsOpen U → x ∈ U → ∃ b ∈ B, x ∈ b ∧ b ⊆ U :=
  ⟨fun h _ _ hU hx => h.exists_subset_of_mem_open hx hU, fun h =>
    TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds hB fun a U ha hU => h U a hU ha⟩

/-- Morris, Topology Without Tears, Proposition 2.3.3 (TP-033). With a basis `B`, a set is open iff each of its
points lies in a member of `B` inside the set. -/
@[kb "morris2024" "Proposition 2.3.3, p. 64"]
theorem morris_2_3_3 [TopologicalSpace X] {B : Set (Set X)} (hB : TopologicalSpace.IsTopologicalBasis B)
    (U : Set X) : IsOpen U ↔ ∀ x ∈ U, ∃ b ∈ B, x ∈ b ∧ b ⊆ U :=
  hB.isOpen_iff

/-- Morris, Topology Without Tears, Section 2.3 (TP-035). The products of members of bases of `X` and `Y` form
a basis of the product topology on `X × Y`. -/
@[kb "morris2024" "Section 2.3, p. 63"]
theorem morris_2_3_product [TopologicalSpace X] [TopologicalSpace Y] {B₁ : Set (Set X)}
    {B₂ : Set (Set Y)} (h₁ : TopologicalSpace.IsTopologicalBasis B₁)
    (h₂ : TopologicalSpace.IsTopologicalBasis B₂) :
    TopologicalSpace.IsTopologicalBasis (image2 (· ×ˢ ·) B₁ B₂) :=
  h₁.prod h₂

end Chapter02

end UndergradKB.Topology.Course
