import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.Zorn
import UndergradKB.Common.Attr

/-!
# The finite intersection property and Tychonoff's theorem (Morris, Chapter 10.3)
-/

namespace UndergradKB.Topology

open Set

/-- Morris, Topology Without Tears, Definition 10.3.1 (TP-273). A family of subsets has the finite
intersection property if every finite subfamily has nonempty intersection (for the empty
subfamily the intersection is the whole space, so over an empty space no family has it). -/
def HasFIP {X : Type*} (F : Set (Set X)) : Prop :=
  ∀ s : Finset (Set X), (↑s : Set (Set X)) ⊆ F → (⋂₀ (↑s : Set (Set X))).Nonempty

/-- Morris, Topology Without Tears, Definition 10.3.1 (TP-273). The book's formulation with
`n ≥ 1` members `F₁, ..., Fₙ`. -/
@[kb "morris2024" "Definition 10.3.1, p. 272"]
theorem hasFIP_iff {X : Type*} {F : Set (Set X)} [Nonempty X] :
    HasFIP F ↔ ∀ s : Finset (Set X), s.Nonempty → (↑s : Set (Set X)) ⊆ F →
      (⋂₀ (↑s : Set (Set X))).Nonempty := by
  refine ⟨fun h s _ hs => h s hs, fun h s hs => ?_⟩
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  · exact h s hne hs

theorem HasFIP.mono {X : Type*} {F G : Set (Set X)} (h : HasFIP G) (hFG : F ⊆ G) : HasFIP F :=
  fun s hs => h s (hs.trans hFG)

/-- Morris, Topology Without Tears, Proposition 10.3.2 (TP-274). A space is compact iff every
family of closed sets with the finite intersection property has nonempty intersection. -/
@[kb "morris2024" "Proposition 10.3.2, p. 273"]
theorem compactSpace_iff_fip {X : Type*} [TopologicalSpace X] :
    CompactSpace X ↔ ∀ F : Set (Set X), (∀ A ∈ F, IsClosed A) → HasFIP F → (⋂₀ F).Nonempty := by
  classical
  constructor
  · intro hc F hcl hF
    have := hc
    have := isCompact_univ.inter_iInter_nonempty (fun A : F => (A : Set X))
      (fun A => hcl A A.2) (fun u => by
        have := hF (u.image Subtype.val) (by
          intro A hA
          obtain ⟨B, -, rfl⟩ := Finset.mem_image.1 hA
          exact B.2)
        simpa [sInter_image] using this)
    simpa [sInter_eq_iInter] using this
  · intro h
    refine ⟨isCompact_of_finite_subfamily_closed fun {ι} t ht hd => ?_⟩
    by_contra hcon
    push Not at hcon
    have hF : HasFIP (range t) := by
      intro s hs
      by_contra hemp
      rw [not_nonempty_iff_eq_empty] at hemp
      obtain ⟨T, -, hTf, hT⟩ := (exists_subset_image_finite_and (f := t) (s := univ)
        (p := fun T : Set (Set X) => ⋂₀ T = ∅)).1 ⟨s, by simpa using hs, s.finite_toSet, hemp⟩
      refine hcon hTf.toFinset ?_
      rw [Set.univ_disjoint]
      simpa [sInter_image] using hT
    obtain ⟨x, hx⟩ := h (range t) (by rintro _ ⟨i, rfl⟩; exact ht i) hF
    rw [Set.univ_disjoint] at hd
    rw [sInter_range, hd] at hx
    exact hx

/-- Morris, Topology Without Tears, Lemma 10.3.3 (TP-275). Every family of subsets with the finite
intersection property is contained in a maximal family of subsets with the finite intersection
property (Zorn's lemma). -/
@[kb "morris2024" "Lemma 10.3.3, p. 273"]
theorem exists_maximal_hasFIP {X : Type*} {F : Set (Set X)} (hF : HasFIP F) :
    ∃ H : Set (Set X), F ⊆ H ∧ HasFIP H ∧ ∀ H' : Set (Set X), HasFIP H' → H ⊆ H' → H' = H := by
  obtain ⟨m, hFm, hm⟩ := zorn_subset_nonempty {H : Set (Set X) | HasFIP H} (fun c hcS hch hne => by
    refine ⟨⋃₀ c, fun s hs => ?_, fun H hH => subset_sUnion_of_mem hH⟩
    obtain ⟨H, hHc, hsH⟩ := DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion hne
      hch.directedOn s.finite_toSet hs
    exact hcS hHc s hsH) F hF
  exact ⟨m, hFm, hm.1, fun H' h1 h2 => (hm.2 h1 h2).antisymm h2⟩

/-- Morris, Topology Without Tears, Theorem 10.3.4 (TP-276), Tychonoff's theorem. An arbitrary
product of (nonempty) spaces is compact iff each factor is compact. -/
@[kb "morris2024" "Theorem 10.3.4, p. 274"]
theorem compactSpace_pi_iff {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, Nonempty (X i)] : CompactSpace (∀ i, X i) ↔ ∀ i, CompactSpace (X i) := by
  classical
  constructor
  · intro h i
    obtain ⟨x⟩ : Nonempty (∀ i, X i) := inferInstance
    exact Function.Surjective.compactSpace (continuous_apply i)
      (fun y => ⟨Function.update x i y, by simp⟩)
  · intro h
    infer_instance

end UndergradKB.Topology
