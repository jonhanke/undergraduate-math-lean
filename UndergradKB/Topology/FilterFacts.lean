import Mathlib.Topology.Ultrafilter
import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Filter.Bases.Basic
import Mathlib.Order.Zorn
import UndergradKB.Common.Attr

/-!
# Filters and ultrafilters (Morris, Appendix 6, Sections 1, 2 and 4)

Ultrafilter dichotomy, a filter as the intersection of the ultrafilters finer than it, compactness by
finer convergent filters, topologies from families of filters, refinement of filterbases, and filters
of closed sets (the Wallman setting) with the existence of maximal ones.

Order convention: in Mathlib a finer filter is a smaller one, and the book's intersection of a family of
filters (as families of sets) is the supremum `⨆` in `Filter X`.
-/

open Filter Topology Set

set_option linter.unusedSectionVars false

namespace UndergradKB.Topology

universe u

variable {X : Type u}

/-! ### Ultrafilters -/

/-- Morris, Topology Without Tears, Corollary A6.1.15 (TP-655). An ultrafilter either contains a
singleton, and is then the principal ultrafilter at that point with intersection that singleton, or
the intersection of its members is empty. -/
@[kb "morris2024" "Corollary A6.1.15, p. 627"]
theorem ultrafilter_singleton_or_sInter_eq_empty (U : Ultrafilter X) :
    (∃ x, ({x} : Set X) ∈ U ∧ U = pure x ∧ ⋂₀ {s : Set X | s ∈ U} = {x}) ∨
      ⋂₀ {s : Set X | s ∈ U} = ∅ := by
  by_cases h : ∃ x, ({x} : Set X) ∈ U
  · obtain ⟨x, hx⟩ := h
    obtain ⟨y, hy, hUy⟩ := U.eq_pure_of_finite_mem (Set.finite_singleton x) hx
    have hyx : y = x := hy
    have hUx : U = pure x := hyx ▸ hUy
    left
    refine ⟨x, hx, hUx, ?_⟩
    ext z
    simp only [mem_sInter, mem_singleton_iff]
    constructor
    · intro hz
      exact hz {x} hx
    · rintro rfl s hs
      have : s ∈ (pure z : Ultrafilter X) := hUx ▸ hs
      exact Ultrafilter.mem_pure.1 this
  · right
    ext z
    simp only [mem_sInter, mem_empty_iff_false, iff_false]
    intro hz
    have : ({z} : Set X)ᶜ ∈ U := Ultrafilter.compl_mem_iff_notMem.2 (fun hz' => h ⟨z, hz'⟩)
    exact hz _ this rfl

/-- Morris, Topology Without Tears, Proposition A6.1.17 (TP-657). A set belongs to a filter `F` iff it
belongs to every ultrafilter finer than `F`. -/
@[kb "morris2024" "Proposition A6.1.17, p. 628"]
theorem mem_iff_forall_ultrafilter {F : Filter X} {s : Set X} :
    s ∈ F ↔ ∀ U : Ultrafilter X, (U : Filter X) ≤ F → s ∈ U := by
  rw [← le_principal_iff, Filter.le_iff_ultrafilter]
  simp only [le_principal_iff]
  exact Iff.rfl

/-- Morris, Topology Without Tears, Proposition A6.1.17 (TP-657). A filter is the intersection of all
the ultrafilters finer than it (the intersection of families of sets is the supremum of filters). -/
@[kb "morris2024" "Proposition A6.1.17, p. 628"]
theorem eq_iSup_ultrafilters (F : Filter X) :
    F = ⨆ U : {U : Ultrafilter X // (U : Filter X) ≤ F}, (U.1 : Filter X) := by
  ext s
  rw [mem_iSup, mem_iff_forall_ultrafilter, Subtype.forall]
  exact Iff.rfl

/-- Morris, Topology Without Tears, Proposition A6.1.23 (TP-660). A space is compact iff every (proper)
filter has a finer (proper) filter that converges. -/
@[kb "morris2024" "Proposition A6.1.23, p. 630"]
theorem compactSpace_iff_exists_finer_converges [TopologicalSpace X] : CompactSpace X ↔
    ∀ F : Filter X, F.NeBot → ∃ G : Filter X, G.NeBot ∧ G ≤ F ∧ ∃ x, G ≤ 𝓝 x := by
  constructor
  · intro _ F hF
    obtain ⟨x, hx⟩ := exists_clusterPt_of_compactSpace F
    exact ⟨𝓝 x ⊓ F, hx, inf_le_right, x, inf_le_left⟩
  · intro h
    refine ⟨isCompact_iff_ultrafilter_le_nhds.2 fun U _ => ?_⟩
    obtain ⟨G, hG, hGU, x, hx⟩ := h (U : Filter X) inferInstance
    have := Ultrafilter.unique U hGU
    rw [this] at hx
    exact ⟨x, mem_univ _, hx⟩

/-! ### Topologies from filters -/

set_option warn.classDefReducibility false in
/-- Morris, Topology Without Tears, Proposition A6.1.30 (TP-666). Given for each point `x` a set `S x`
of filters, the sets `O` that belong to every filter of `S x` at each of their points `x` form a
topology. -/
def topologyOfFilters (S : X → Set (Filter X)) : TopologicalSpace X where
  IsOpen O := ∀ x ∈ O, ∀ F ∈ S x, O ∈ F
  isOpen_univ := fun _ _ _ _ => univ_mem
  isOpen_inter := fun _ _ hs ht x hx F hF => inter_mem (hs x hx.1 F hF) (ht x hx.2 F hF)
  isOpen_sUnion := fun _ h x hx F hF => by
    obtain ⟨O, hO, hxO⟩ := hx
    exact mem_of_superset (h O hO x hxO F hF) (subset_sUnion_of_mem hO)

theorem isOpen_topologyOfFilters_iff (S : X → Set (Filter X)) {O : Set X} :
    @IsOpen X (topologyOfFilters S) O ↔ ∀ x ∈ O, ∀ F ∈ S x, O ∈ F :=
  Iff.rfl

/-- Morris, Topology Without Tears, Proposition A6.1.30 (TP-666). In the topology built from the
filters `S x`, each filter `F ∈ S x` converges to `x`, so the neighbourhood sets of `x` lie in the
intersection of the filters of `S x`. (The final equality of the neighbourhood filter with the
intersection is not proved: see the report.) -/
@[kb "morris2024" "Proposition A6.1.30, p. 637"]
theorem le_nhds_topologyOfFilters (S : X → Set (Filter X)) {x : X} {F : Filter X} (hF : F ∈ S x) :
    F ≤ @nhds X (topologyOfFilters S) x ∧
      (⨆ G ∈ S x, G) ≤ @nhds X (topologyOfFilters S) x := by
  let _ := topologyOfFilters S
  have h1 : ∀ G ∈ S x, G ≤ 𝓝 x := by
    intro G hG s hs
    obtain ⟨O, hOs, hO, hxO⟩ := mem_nhds_iff.1 hs
    exact mem_of_superset ((isOpen_topologyOfFilters_iff S).1 hO x hxO G hG) hOs
  exact ⟨h1 F hF, iSup₂_le h1⟩

/-- Morris, Topology Without Tears, Corollary A6.1.31 (TP-667). A topology is recovered from the
ultrafilters converging to each point: building the topology of the previous result from the sets of
ultrafilters converging to `x` gives back the original topology. -/
@[kb "morris2024" "Corollary A6.1.31, p. 637"]
theorem topologyOfFilters_ultrafilters [t : TopologicalSpace X] :
    topologyOfFilters
      (fun x => {F : Filter X | ∃ U : Ultrafilter X, (U : Filter X) = F ∧ (U : Filter X) ≤ 𝓝 x}) =
        t := by
  refine TopologicalSpace.ext (funext fun O => propext ?_)
  refine (isOpen_topologyOfFilters_iff _).trans ?_
  rw [isOpen_iff_ultrafilter]
  constructor
  · intro h x hx U hU
    exact h x hx _ ⟨U, rfl, hU⟩
  · rintro h x hx F ⟨U, rfl, hU⟩
    exact h x hx U hU

/-! ### Filterbases -/

/-- Morris, Topology Without Tears, Definition A6.2.4 (TP-669). The filterbase `G₁` is finer than `G₂`
(equivalently `G₂` is coarser than `G₁`, or `G₁` is a refinement of `G₂`): every set of `G₂` contains
a set of `G₁`. -/
def FilterBasisFiner (G₁ G₂ : FilterBasis X) : Prop :=
  ∀ B₂ ∈ G₂, ∃ B₁ ∈ G₁, B₁ ⊆ B₂

/-- Morris, Topology Without Tears, Definition A6.2.4 (TP-669). Two filterbases are equivalent when each
is finer than the other. -/
def FilterBasisEquiv (G₁ G₂ : FilterBasis X) : Prop :=
  FilterBasisFiner G₁ G₂ ∧ FilterBasisFiner G₂ G₁

/-- Morris, Topology Without Tears, Definition A6.2.4 (TP-669). A filterbase is finer than another iff
the filter it generates is finer. -/
@[kb "morris2024" "Definition A6.2.4, p. 642"]
theorem filterBasisFiner_iff {G₁ G₂ : FilterBasis X} :
    FilterBasisFiner G₁ G₂ ↔ G₁.filter ≤ G₂.filter := by
  constructor
  · intro h U hU
    obtain ⟨B₂, hB₂, hBU⟩ := (FilterBasis.mem_filter_iff _).1 hU
    obtain ⟨B₁, hB₁, hB⟩ := h B₂ hB₂
    exact (FilterBasis.mem_filter_iff _).2 ⟨B₁, hB₁, hB.trans hBU⟩
  · intro h B₂ hB₂
    exact (FilterBasis.mem_filter_iff _).1 (h (G₂.mem_filter_of_mem hB₂))

/-- Morris, Topology Without Tears, Definition A6.2.4 (TP-669). Two filterbases are equivalent iff they
generate the same filter. -/
@[kb "morris2024" "Definition A6.2.4, p. 642"]
theorem filterBasisEquiv_iff {G₁ G₂ : FilterBasis X} :
    FilterBasisEquiv G₁ G₂ ↔ G₁.filter = G₂.filter := by
  rw [FilterBasisEquiv, filterBasisFiner_iff, filterBasisFiner_iff, le_antisymm_iff]

/-! ### Filters of closed sets -/

section Closed

variable [TopologicalSpace X]

/-- Morris, Topology Without Tears, Definition A6.4.1 (TP-694). A filter in the lattice `C` of closed
sets: a nonempty family of closed sets, closed under intersections and under closed supersets, not
containing the empty set. -/
structure IsClosedFilter (F : Set (Set X)) : Prop where
  /-- nonempty -/
  nonempty : F.Nonempty
  /-- members are closed -/
  closed : ∀ A ∈ F, IsClosed A
  /-- closed under binary intersection -/
  inter_mem : ∀ A ∈ F, ∀ B ∈ F, A ∩ B ∈ F
  /-- closed under closed supersets -/
  superset : ∀ A ∈ F, ∀ B, IsClosed B → A ⊆ B → B ∈ F
  /-- the empty set is not a member -/
  empty_notMem : ∅ ∉ F

/-- Morris, Topology Without Tears, Definition A6.4.1 (TP-694). An ultrafilter in `C`: a filter in `C`
that no filter in `C` strictly refines (strictly contains). -/
def IsClosedUltrafilter (U : Set (Set X)) : Prop :=
  IsClosedFilter U ∧ ∀ G : Set (Set X), IsClosedFilter G → U ⊆ G → G = U

/-- Morris, Topology Without Tears, Definition A6.4.1 (TP-694). A free ultrafilter in `C`: one with empty
intersection. -/
def IsFreeClosedUltrafilter (U : Set (Set X)) : Prop :=
  IsClosedUltrafilter U ∧ ⋂₀ U = ∅

/-- Morris, Topology Without Tears, Definition A6.4.1 (TP-694). The closed members of a proper filter
on `X` form a filter in `C`. -/
@[kb "morris2024" "Definition A6.4.1, p. 661"]
theorem isClosedFilter_closed_mem (G : Filter X) [G.NeBot] :
    IsClosedFilter {A : Set X | IsClosed A ∧ A ∈ G} where
  nonempty := ⟨univ, isClosed_univ, univ_mem⟩
  closed := fun _ h => h.1
  inter_mem := fun _ hA _ hB => ⟨hA.1.inter hB.1, inter_mem hA.2 hB.2⟩
  superset := fun _ hA _ hB hAB => ⟨hB, mem_of_superset hA.2 hAB⟩
  empty_notMem := fun h => Filter.empty_notMem G h.2

private theorem sInter_mem_of_finite {F : Set (Set X)} (hF : IsClosedFilter F) :
    ∀ T : Set (Set X), T.Finite → T ⊆ F → ⋂₀ T ∈ F := by
  intro T hT
  refine Set.Finite.induction_on (motive := fun T _ => T ⊆ F → ⋂₀ T ∈ F) T hT ?_ ?_
  · intro _
    obtain ⟨A, hA⟩ := hF.nonempty
    rw [sInter_empty]
    exact hF.superset A hA univ isClosed_univ (subset_univ _)
  · intro a s _ _ ih hsub
    rw [sInter_insert]
    exact hF.inter_mem a (hsub (mem_insert _ _)) _ (ih (fun b hb => hsub (mem_insert_of_mem _ hb)))

/-- Morris, Topology Without Tears, Definition A6.4.1 (TP-694). Conversely, a filter in `C` is exactly
the family of closed members of the filter of `X` that it generates, which is proper. -/
@[kb "morris2024" "Definition A6.4.1, p. 661"]
theorem IsClosedFilter.closed_mem_generate {F : Set (Set X)} (hF : IsClosedFilter F) :
    (Filter.generate F).NeBot ∧ {A : Set X | IsClosed A ∧ A ∈ Filter.generate F} = F := by
  have key : ∀ A, A ∈ Filter.generate F → ∃ T : Set (Set X), T ⊆ F ∧ T.Finite ∧ ⋂₀ T ⊆ A :=
    fun A hA => Filter.mem_generate_iff.1 hA
  refine ⟨?_, ?_⟩
  · refine Filter.generate_neBot_iff.2 fun T hTF hT => ?_
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    exact hF.empty_notMem (hne ▸ sInter_mem_of_finite hF T hT hTF)
  · ext A
    constructor
    · rintro ⟨hA, hAg⟩
      obtain ⟨T, hTF, hTfin, hTA⟩ := key A hAg
      exact hF.superset _ (sInter_mem_of_finite hF T hTfin hTF) A hA hTA
    · intro hA
      exact ⟨hF.closed A hA, Filter.mem_generate_of_mem hA⟩

/-- Morris, Topology Without Tears, Proposition A6.4.2 (TP-695). Every filter in `C` lies in an
ultrafilter in `C` (Zorn's lemma). -/
@[kb "morris2024" "Proposition A6.4.2, p. 662"]
theorem IsClosedFilter.exists_closedUltrafilter {F : Set (Set X)} (hF : IsClosedFilter F) :
    ∃ U : Set (Set X), F ⊆ U ∧ IsClosedUltrafilter U := by
  let S : Set (Set (Set X)) := {G | IsClosedFilter G ∧ F ⊆ G}
  have H : ∀ c ⊆ S, IsChain (· ⊆ ·) c → c.Nonempty → ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub := by
    intro c hcS hc hne
    obtain ⟨G₀, hG₀⟩ := hne
    refine ⟨⋃₀ c, ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩, fun s hs => subset_sUnion_of_mem hs⟩
    · obtain ⟨A, hA⟩ := (hcS hG₀).1.nonempty
      exact ⟨A, G₀, hG₀, hA⟩
    · rintro A ⟨G, hG, hAG⟩
      exact (hcS hG).1.closed A hAG
    · rintro A ⟨G₁, hG₁, hA⟩ B ⟨G₂, hG₂, hB⟩
      rcases hc.total hG₁ hG₂ with h | h
      · exact ⟨G₂, hG₂, (hcS hG₂).1.inter_mem A (h hA) B hB⟩
      · exact ⟨G₁, hG₁, (hcS hG₁).1.inter_mem A hA B (h hB)⟩
    · rintro A ⟨G, hG, hAG⟩ B hB hAB
      exact ⟨G, hG, (hcS hG).1.superset A hAG B hB hAB⟩
    · rintro ⟨G, hG, hEG⟩
      exact (hcS hG).1.empty_notMem hEG
    · exact (hcS hG₀).2.trans (subset_sUnion_of_mem hG₀)
  obtain ⟨m, hFm, hmax⟩ := zorn_subset_nonempty S H F ⟨hF, Subset.rfl⟩
  refine ⟨m, hFm, hmax.prop.1, fun G hG hmG => ?_⟩
  exact Subset.antisymm (hmax.2 ⟨hG, hFm.trans hmG⟩ hmG) hmG

/-- Morris, Topology Without Tears, Proposition A6.4.2 (TP-695). Every nonempty family of closed sets
with the finite intersection property lies in an ultrafilter in `C`. -/
@[kb "morris2024" "Proposition A6.4.2, p. 662"]
theorem exists_closedUltrafilter_of_fip {𝒮 : Set (Set X)} (hne : 𝒮.Nonempty)
    (hcl : ∀ A ∈ 𝒮, IsClosed A)
    (hfip : ∀ T : Set (Set X), T ⊆ 𝒮 → T.Finite → T.Nonempty → (⋂₀ T).Nonempty) :
    ∃ U : Set (Set X), 𝒮 ⊆ U ∧ IsClosedUltrafilter U := by
  let F₀ : Set (Set X) := {B | IsClosed B ∧ ∃ T : Set (Set X), T ⊆ 𝒮 ∧ T.Finite ∧ ⋂₀ T ⊆ B}
  have hF₀ : IsClosedFilter F₀ := by
    refine ⟨⟨univ, isClosed_univ, ∅, empty_subset _, finite_empty, by simp⟩, fun A hA => hA.1, ?_, ?_, ?_⟩
    · rintro A ⟨hA, T₁, h₁, f₁, s₁⟩ B ⟨hB, T₂, h₂, f₂, s₂⟩
      refine ⟨hA.inter hB, T₁ ∪ T₂, union_subset h₁ h₂, f₁.union f₂, ?_⟩
      rw [sInter_union]
      exact inter_subset_inter s₁ s₂
    · rintro A ⟨hA, T, h₁, f₁, s₁⟩ _ hB hAB
      exact ⟨hB, T, h₁, f₁, s₁.trans hAB⟩
    · rintro ⟨-, T, hT, hTf, hTE⟩
      obtain ⟨A, hA⟩ := hne
      obtain ⟨x, hx⟩ := hfip (insert A T) (insert_subset hA hT) (hTf.insert A) (insert_nonempty _ _)
      rw [sInter_insert] at hx
      exact hTE hx.2
  obtain ⟨U, hFU, hU⟩ := hF₀.exists_closedUltrafilter
  refine ⟨U, fun A hA => hFU ⟨hcl A hA, {A}, singleton_subset_iff.2 hA, finite_singleton A, ?_⟩, hU⟩
  simp

end Closed

end UndergradKB.Topology
