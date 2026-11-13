import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Constructions
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Basic
import UndergradKB.Topology.TopGroups
import UndergradKB.Common.Attr

/-!
# Wave 2: restricted direct products (Morris, Appendix 5, Proposition A5.3.3 (ii))

The restricted direct product of a family of groups with the topology induced from the product is locally
compact Hausdorff iff each factor is and all but finitely many factors are trivial.
-/

open Set Filter Function Topology

namespace UndergradKB.Topology

section Restricted

variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]

/-- Bridging definition for the restricted direct product `∏ʳ Gᵢ` of Morris, Section A5.3: the elements
of the product that are the identity in all but finitely many coordinates, with the subspace topology. -/
abbrev RestrictedProd (G : ι → Type*) [∀ i, Group (G i)] :=
  {f : ∀ i, G i // {i | f i ≠ 1}.Finite}

/-- The element of the restricted product with a single coordinate. -/
def RestrictedProd.single [DecidableEq ι] (j : ι) (g : G j) : RestrictedProd G :=
  ⟨update 1 j g, (Set.finite_singleton j).subset fun i hi => by
    by_contra h
    have h' : i ≠ j := h
    exact hi (by rw [update_of_ne h']; rfl)⟩

theorem RestrictedProd.continuous_single [DecidableEq ι] (j : ι) :
    Continuous (RestrictedProd.single (G := G) j) :=
  Continuous.subtype_mk (continuous_const.update j continuous_id) _

theorem RestrictedProd.continuous_eval (j : ι) :
    Continuous (fun f : RestrictedProd G => f.1 j) :=
  (continuous_apply j).comp continuous_subtype_val

theorem RestrictedProd.t2Space_factor [T2Space (RestrictedProd G)] (j : ι) : T2Space (G j) := by
  classical
  have hl : LeftInverse (fun f : RestrictedProd G => f.1 j) (RestrictedProd.single j) :=
    fun g => by simp [RestrictedProd.single]
  exact (hl.isEmbedding (RestrictedProd.continuous_eval j)
    (RestrictedProd.continuous_single j)).t2Space

theorem RestrictedProd.locallyCompact_factor [∀ i, T2Space (G i)]
    [LocallyCompactSpace (RestrictedProd G)] (j : ι) : LocallyCompactSpace (G j) := by
  classical
  have hl : LeftInverse (fun f : RestrictedProd G => f.1 j) (RestrictedProd.single j) :=
    fun g => by simp [RestrictedProd.single]
  have hemb := hl.isEmbedding (RestrictedProd.continuous_eval j) (RestrictedProd.continuous_single j)
  have hrange : IsClosed (range (RestrictedProd.single (G := G) j)) := by
    have : range (RestrictedProd.single (G := G) j) =
        ⋂ i, ⋂ (_ : i ≠ j), {f : RestrictedProd G | f.1 i = 1} := by
      ext f
      simp only [mem_range, mem_iInter, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨g, rfl⟩ i hi
        simp [RestrictedProd.single, update_of_ne hi]
      · intro h
        refine ⟨f.1 j, Subtype.ext (funext fun i => ?_)⟩
        by_cases hi : i = j
        · subst hi; simp [RestrictedProd.single]
        · simp [RestrictedProd.single, update_of_ne hi, h i hi]
    rw [this]
    exact isClosed_iInter fun i => isClosed_iInter fun _ =>
      isClosed_eq (RestrictedProd.continuous_eval i) continuous_const
  exact (IsClosedEmbedding.mk hemb hrange).locallyCompactSpace

/-- If the restricted product is locally compact and Hausdorff, only finitely many factors are
nontrivial. -/
theorem RestrictedProd.finite_nontrivial [∀ i, T2Space (G i)]
    [LocallyCompactSpace (RestrictedProd G)] : {i | Nontrivial (G i)}.Finite := by
  classical
  by_contra hinf
  obtain ⟨K, hKn, -, hKc⟩ :=
    LocallyCompactSpace.local_compact_nhds (⟨1, by simp⟩ : RestrictedProd G) Set.univ univ_mem
  rw [nhds_subtype_eq_comap, mem_comap] at hKn
  obtain ⟨N, hN, hNK⟩ := hKn
  rw [nhds_pi, Filter.mem_pi] at hN
  obtain ⟨I, hI, t, ht, hsub⟩ := hN
  have hclosed : IsClosed (Subtype.val '' K : Set (∀ i, G i)) :=
    (hKc.image continuous_subtype_val).isClosed
  have hcover : ∀ f : ∀ i, G i, (∀ i ∈ I, f i ∈ t i) → f ∈ (Subtype.val '' K : Set (∀ i, G i)) := by
    intro f hf
    rw [← hclosed.closure_eq, mem_closure_iff_nhds]
    intro N' hN'
    rw [nhds_pi, Filter.mem_pi] at hN'
    obtain ⟨I', hI', t', ht', hsub'⟩ := hN'
    let g : ∀ i, G i := fun i => if i ∈ I ∪ I' then f i else 1
    have hgfin : {i | g i ≠ 1}.Finite := by
      refine (hI.union hI').subset fun i hi => ?_
      by_contra h
      exact hi (ite_eq_right_iff.2 fun hh => absurd hh h)
    have hgI : g ∈ I.pi t := fun i hi => by simpa [g, hi] using hf i hi
    have hgI' : g ∈ I'.pi t' := fun i hi => by
      have := mem_of_mem_nhds (ht' i)
      simpa [g, hi] using this
    exact ⟨g, hsub' hgI', ⟨g, hgfin⟩, hNK (hsub hgI), rfl⟩
  have hc : ∀ j, ∃ g : G j, Nontrivial (G j) → g ≠ 1 := fun j => by
    by_cases h : Nontrivial (G j)
    · obtain ⟨g, hg⟩ := exists_ne (1 : G j)
      exact ⟨g, fun _ => hg⟩
    · exact ⟨1, fun hn => absurd hn h⟩
  choose c hc using hc
  let f : ∀ i, G i := fun i => if i ∈ I then 1 else c i
  obtain ⟨⟨f', hf'⟩, -, hff'⟩ := hcover f fun i hi => by
    simpa [f, hi] using mem_of_mem_nhds (ht i)
  have hff : f' = f := hff'
  subst hff
  refine (hinf ?_)
  refine (hf'.union hI).subset fun i hi => ?_
  by_cases hiI : i ∈ I
  · exact Or.inr hiI
  · left
    have := hc i hi
    simpa [f, hiI] using this

/-- Morris, Topology Without Tears, Proposition A5.3.3 (ii) (TP-526). The restricted direct product of
a family of groups (with the topology induced from the product) is locally compact Hausdorff if and only
if each factor is locally compact Hausdorff and all but finitely many factors are the trivial group. -/
@[kb "morris2024" "Proposition A5.3.3, p. 531"]
theorem locallyCompact_t2_restrictedProd_iff :
    (LocallyCompactSpace (RestrictedProd G) ∧ T2Space (RestrictedProd G)) ↔
      (∀ i, LocallyCompactSpace (G i) ∧ T2Space (G i)) ∧ {i | Nontrivial (G i)}.Finite := by
  classical
  constructor
  · rintro ⟨hlc, ht2⟩
    have hfac : ∀ i, T2Space (G i) := fun i => RestrictedProd.t2Space_factor i
    exact ⟨fun i => ⟨RestrictedProd.locallyCompact_factor i, hfac i⟩, RestrictedProd.finite_nontrivial⟩
  · rintro ⟨hfac, hfin⟩
    have hsub : ∀ i, i ∉ {i | Nontrivial (G i)} → Subsingleton (G i) := fun i hi =>
      not_nontrivial_iff_subsingleton.1 hi
    have hall : ∀ f : ∀ i, G i, {i | f i ≠ 1}.Finite := fun f =>
      hfin.subset fun i hi => by
        by_contra h
        exact hi (@Subsingleton.elim _ (hsub i h) _ _)
    let e : RestrictedProd G ≃ₜ (∀ i, G i) :=
      { toFun := Subtype.val
        invFun := fun f => ⟨f, hall f⟩
        left_inv := fun f => rfl
        right_inv := fun f => rfl
        continuous_toFun := continuous_subtype_val
        continuous_invFun := Continuous.subtype_mk continuous_id _ }
    have : ∀ i, T2Space (G i) := fun i => (hfac i).2
    have : ∀ i, LocallyCompactSpace (G i) := fun i => (hfac i).1
    have hpi : LocallyCompactSpace (∀ i, G i) := by
      refine (locallyCompactSpace_pi_iff G).2 ⟨inferInstance, hfin.subset fun i hi => ?_⟩
      by_contra h
      haveI := hsub i h
      haveI : Finite (G i) := Finite.of_subsingleton
      exact hi inferInstance
    exact ⟨e.isOpenEmbedding.locallyCompactSpace, e.isEmbedding.t2Space⟩

end Restricted

end UndergradKB.Topology
