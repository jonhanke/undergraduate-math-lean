import Mathlib.Topology.Compactification.StoneCech
import Mathlib.Topology.Bases
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.DenseEmbedding
import Mathlib.Order.Zorn
import Mathlib.Order.Filter.Ultrafilter.Cardinality
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.MetricSpace.Bounded
import UndergradKB.Common.Attr

/-!
# The Wallman compactification (Morris, Topology Without Tears, Appendix 6.4)

A closed-set ultrafilter of a topological space `X` is a maximal family of closed sets with the
finite intersection property. `Wallman X` is the set of all of them, topologised by the basic sets
`O* = {u | ∃ F ∈ u, F ⊆ O}`, `O` open. For a T1 space the fixed ultrafilters `{F closed | x ∈ F}`
give a dense embedding of `X`; this is the book's `ωX = X ∪ {free ultrafilters}`.
-/

namespace UndergradKB.Topology

open Set TopologicalSpace

/-- The finite intersection property: every finite subfamily has nonempty intersection (for the
empty subfamily the intersection is the whole space). -/
def Wallman.FIP {X : Type*} (F : Set (Set X)) : Prop :=
  ∀ s : Finset (Set X), (↑s : Set (Set X)) ⊆ F → (⋂₀ (↑s : Set (Set X))).Nonempty

/-- Morris, Topology Without Tears, Definitions A6.4.1 (TP-696). An ultrafilter in the lattice of
closed sets: a maximal family of closed sets with the finite intersection property (Proposition
`Wallman.union_mem_iff` etc. show that it is a filter in the sense of the book). -/
@[ext]
structure Wallman (X : Type*) [TopologicalSpace X] where
  /-- the closed sets belonging to the ultrafilter -/
  sets : Set (Set X)
  isClosed : ∀ A ∈ sets, IsClosed A
  fip : Wallman.FIP sets
  maximal : ∀ B : Set (Set X), (∀ A ∈ B, IsClosed A) → Wallman.FIP B → sets ⊆ B → B ⊆ sets

namespace Wallman

variable {X : Type*} [TopologicalSpace X] (u v : Wallman X)

theorem mem_of_forall_inter_nonempty {G : Set X} (hG : IsClosed G)
    (h : ∀ s : Finset (Set X), (↑s : Set (Set X)) ⊆ u.sets → (G ∩ ⋂₀ (↑s : Set (Set X))).Nonempty) :
    G ∈ u.sets := by
  classical
  have hfip : FIP (insert G u.sets) := by
    intro s hs
    have hsub : (↑(s.erase G) : Set (Set X)) ⊆ u.sets := by
      intro A hA
      have hA' := Finset.mem_erase.1 (Finset.mem_coe.1 hA)
      rcases hs (Finset.mem_coe.2 hA'.2) with rfl | h
      · exact absurd rfl hA'.1
      · exact h
    obtain ⟨x, hxG, hx⟩ := h _ hsub
    refine ⟨x, fun A hA => ?_⟩
    by_cases hAG : A = G
    · subst hAG; exact hxG
    · exact hx A (by simp [hAG, hA])
  exact u.maximal _ (by
    intro A hA
    rcases hA with rfl | hA
    · exact hG
    · exact u.isClosed A hA) hfip (subset_insert _ _) (mem_insert _ _)

theorem univ_mem : (univ : Set X) ∈ u.sets :=
  u.mem_of_forall_inter_nonempty isClosed_univ fun s hs => by simpa using u.fip s hs

theorem mem_of_subset {A G : Set X} (hA : A ∈ u.sets) (hAG : A ⊆ G) (hG : IsClosed G) :
    G ∈ u.sets := by
  classical
  refine u.mem_of_forall_inter_nonempty hG fun s hs => ?_
  obtain ⟨x, hx⟩ := u.fip (insert A s) (by
    rw [Finset.coe_insert]; exact insert_subset hA hs)
  rw [Finset.coe_insert, sInter_insert] at hx
  exact ⟨x, hAG hx.1, hx.2⟩

theorem inter_mem {A B : Set X} (hA : A ∈ u.sets) (hB : B ∈ u.sets) : A ∩ B ∈ u.sets := by
  classical
  refine u.mem_of_forall_inter_nonempty ((u.isClosed A hA).inter (u.isClosed B hB)) fun s hs => ?_
  obtain ⟨x, hx⟩ := u.fip (insert A (insert B s)) (by
    rw [Finset.coe_insert, Finset.coe_insert]; exact insert_subset hA (insert_subset hB hs))
  rw [Finset.coe_insert, Finset.coe_insert, sInter_insert, sInter_insert] at hx
  exact ⟨x, ⟨hx.1, hx.2.1⟩, hx.2.2⟩

theorem empty_not_mem : (∅ : Set X) ∉ u.sets := by
  intro h
  obtain ⟨x, hx⟩ := u.fip {∅} (by simpa using h)
  simp at hx

theorem sInter_mem : ∀ s : Finset (Set X), (↑s : Set (Set X)) ⊆ u.sets → ⋂₀ (↑s : Set (Set X)) ∈ u.sets := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => intro _; simpa using u.univ_mem
  | insert a s ha ih =>
    intro hs
    rw [Finset.coe_insert, sInter_insert]
    exact u.inter_mem (hs (by simp)) (ih fun A hA => hs (by simp [hA]))

/-- Morris, Topology Without Tears, Proposition A6.4.3 (vii) (TP-696). A closed set belongs to an
ultrafilter iff it meets every member. -/
@[kb "morris2024" "Proposition A6.4.3, p. 663"]
theorem mem_iff {A : Set X} (hA : IsClosed A) :
    A ∈ u.sets ↔ ∀ F ∈ u.sets, (A ∩ F).Nonempty := by
  constructor
  · intro h F hF
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    exact u.empty_not_mem (hne ▸ u.inter_mem h hF)
  · intro h
    exact u.mem_of_forall_inter_nonempty hA fun s hs => h _ (u.sInter_mem s hs)

/-- Morris, Topology Without Tears, Proposition A6.4.3 (ix) (TP-696). A closed set is missing from
an ultrafilter iff it is disjoint from some member. -/
@[kb "morris2024" "Proposition A6.4.3, p. 663"]
theorem not_mem_iff {A : Set X} (hA : IsClosed A) :
    A ∉ u.sets ↔ ∃ F ∈ u.sets, Disjoint A F := by
  rw [u.mem_iff hA]
  push Not
  simp [Set.disjoint_iff_inter_eq_empty]

/-- Morris, Topology Without Tears, Proposition A6.4.3 (x) (TP-696). The complement of an open set
is missing from an ultrafilter iff some member lies inside the open set. -/
@[kb "morris2024" "Proposition A6.4.3, p. 663"]
theorem compl_not_mem_iff {O : Set X} (hO : IsOpen O) :
    Oᶜ ∉ u.sets ↔ ∃ F ∈ u.sets, F ⊆ O := by
  rw [u.not_mem_iff hO.isClosed_compl]
  simp [disjoint_compl_left_iff]

/-- Morris, Topology Without Tears, Proposition A6.4.3 (vi) (TP-696). The prime property: a union
of two closed sets lies in an ultrafilter iff one of them does. -/
@[kb "morris2024" "Proposition A6.4.3, p. 663"]
theorem union_mem_iff {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) :
    A ∪ B ∈ u.sets ↔ A ∈ u.sets ∨ B ∈ u.sets := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    obtain ⟨F, hF, hAF⟩ := (u.not_mem_iff hA).1 hne.1
    obtain ⟨G, hG, hBG⟩ := (u.not_mem_iff hB).1 hne.2
    obtain ⟨x, hx⟩ := (u.mem_iff (hA.union hB)).1 h _ (u.inter_mem hF hG)
    rcases hx.1 with hxA | hxB
    · exact Set.disjoint_left.1 hAF hxA hx.2.1
    · exact Set.disjoint_left.1 hBG hxB hx.2.2
  · rintro (h | h)
    · exact u.mem_of_subset h subset_union_left (hA.union hB)
    · exact u.mem_of_subset h subset_union_right (hA.union hB)

theorem exists_mem_not_mem (h : u ≠ v) : ∃ A ∈ u.sets, A ∉ v.sets := by
  by_contra hcon
  push Not at hcon
  exact h (Wallman.ext (Subset.antisymm hcon (u.maximal v.sets v.isClosed v.fip hcon)))

/-- Morris, Topology Without Tears, Proposition A6.4.3 (viii) (TP-696). Two ultrafilters differ iff
some member of one is disjoint from some member of the other. -/
@[kb "morris2024" "Proposition A6.4.3, p. 663"]
theorem ne_iff_exists_disjoint : u ≠ v ↔ ∃ A ∈ u.sets, ∃ B ∈ v.sets, Disjoint A B := by
  constructor
  · intro h
    obtain ⟨A, hA, hAv⟩ := u.exists_mem_not_mem v h
    obtain ⟨B, hB, hAB⟩ := (v.not_mem_iff (u.isClosed A hA)).1 hAv
    exact ⟨A, hA, B, hB, hAB⟩
  · rintro ⟨A, hA, B, hB, hAB⟩ rfl
    have := u.inter_mem hA hB
    rw [Set.disjoint_iff_inter_eq_empty.1 hAB] at this
    exact u.empty_not_mem this

/-- Morris, Topology Without Tears, Proposition A6.4.2 (TP-696). Every family of closed sets with
the finite intersection property lies in a closed-set ultrafilter. -/
@[kb "morris2024" "Proposition A6.4.2, p. 662"]
theorem exists_of_fip {F : Set (Set X)} (hcl : ∀ A ∈ F, IsClosed A) (hF : FIP F) :
    ∃ u : Wallman X, F ⊆ u.sets := by
  obtain ⟨m, hFm, hm⟩ := zorn_subset_nonempty {H : Set (Set X) | (∀ A ∈ H, IsClosed A) ∧ FIP H}
    (fun c hcS hch hne => by
      refine ⟨⋃₀ c, ⟨fun A hA => ?_, fun s hs => ?_⟩, fun H hH => subset_sUnion_of_mem hH⟩
      · obtain ⟨H, hH, hAH⟩ := hA
        exact (hcS hH).1 A hAH
      · obtain ⟨H, hHc, hsH⟩ := DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion hne
          hch.directedOn s.finite_toSet hs
        exact (hcS hHc).2 s hsH) F ⟨hcl, hF⟩
  exact ⟨⟨m, hm.1.1, hm.1.2, fun B hB hf hmB => hm.2 ⟨hB, hf⟩ hmB⟩, hFm⟩

/-! ### The topology -/

/-- The basic open set `O*` of the Wallman space: the ultrafilters having a member inside `O`
(equivalently, those not containing the closed set `Oᶜ`). -/
def star (O : Set X) : Set (Wallman X) := {u | ∃ F ∈ u.sets, F ⊆ O}

theorem mem_star {O : Set X} : u ∈ star O ↔ ∃ F ∈ u.sets, F ⊆ O := Iff.rfl

theorem star_univ : star (univ : Set X) = univ :=
  eq_univ_of_forall fun u => ⟨univ, u.univ_mem, subset_rfl⟩

theorem star_empty : star (∅ : Set X) = ∅ :=
  eq_empty_of_forall_notMem fun u ⟨F, hF, hFO⟩ => by
    rw [subset_empty_iff] at hFO
    exact u.empty_not_mem (hFO ▸ hF)

theorem star_inter (O₁ O₂ : Set X) : star (O₁ ∩ O₂) = star O₁ ∩ star O₂ := by
  ext u
  constructor
  · rintro ⟨F, hF, hFO⟩
    exact ⟨⟨F, hF, hFO.trans inter_subset_left⟩, ⟨F, hF, hFO.trans inter_subset_right⟩⟩
  · rintro ⟨⟨F₁, hF₁, h₁⟩, ⟨F₂, hF₂, h₂⟩⟩
    exact ⟨F₁ ∩ F₂, u.inter_mem hF₁ hF₂, inter_subset_inter h₁ h₂⟩

/-- Morris, Topology Without Tears, Remarks A6.4.4 (TP-697). The Wallman topology, generated by the
sets `O*` for `O` open. -/
instance instTopologicalSpace : TopologicalSpace (Wallman X) :=
  generateFrom {s | ∃ O : Set X, IsOpen O ∧ s = star O}

theorem isOpen_star {O : Set X} (hO : IsOpen O) : IsOpen (star O : Set (Wallman X)) :=
  isOpen_generateFrom_of_mem ⟨O, hO, rfl⟩

/-- The sets `O*`, `O` open, form a basis of the Wallman topology. -/
@[kb "morris2024" "Remarks A6.4.4, p. 665"]
theorem isTopologicalBasis_star :
    IsTopologicalBasis {s : Set (Wallman X) | ∃ O : Set X, IsOpen O ∧ s = star O} where
  exists_subset_inter := by
    rintro _ ⟨O₁, h₁, rfl⟩ _ ⟨O₂, h₂, rfl⟩ x hx
    refine ⟨star (O₁ ∩ O₂), ⟨_, h₁.inter h₂, rfl⟩, ?_, ?_⟩
    · rw [star_inter]; exact hx
    · rw [star_inter]
  sUnion_eq := eq_univ_of_forall fun u => ⟨star univ, ⟨_, isOpen_univ, rfl⟩, by rw [star_univ]; trivial⟩
  eq_generateFrom := rfl

/-- Morris, Topology Without Tears, Remarks A6.4.4 (6) (TP-697). The complement of `O*` is the set
of ultrafilters containing the closed set `Oᶜ`. -/
@[kb "morris2024" "Remarks A6.4.4, p. 665"]
theorem compl_star {O : Set X} (hO : IsOpen O) : (star O)ᶜ = {u : Wallman X | Oᶜ ∈ u.sets} := by
  ext u
  simp only [mem_compl_iff]
  change ¬ u ∈ star O ↔ Oᶜ ∈ u.sets
  rw [← not_iff_not, not_not]
  exact (u.compl_not_mem_iff hO).symm

/-- The set `A⁺` of ultrafilters containing the closed set `A` is closed. -/
theorem isClosed_plus {A : Set X} (hA : IsClosed A) : IsClosed {u : Wallman X | A ∈ u.sets} := by
  have h := compl_star hA.isOpen_compl
  rw [compl_compl] at h
  rw [← h, isClosed_compl_iff]
  exact isOpen_star hA.isOpen_compl

/-! ### Fixed ultrafilters -/

/-- Morris, Topology Without Tears, Definition A6.4.5 (TP-697). The fixed ultrafilter at a point of
a T1 space (all closed sets containing the point); `Wallman X` is then `ωX`, the points of `X`
together with the free ultrafilters. -/
@[kb "morris2024" "Definition A6.4.5, p. 666"]
def pt [T1Space X] (x : X) : Wallman X where
  sets := {A | IsClosed A ∧ x ∈ A}
  isClosed _ h := h.1
  fip _ hs := ⟨x, fun _ hA => (hs hA).2⟩
  maximal B hB hf hsub A hA := by
    classical
    refine ⟨hB A hA, ?_⟩
    by_contra hx
    have h1 : ({x} : Set X) ∈ B := hsub ⟨isClosed_singleton, rfl⟩
    obtain ⟨y, hy⟩ := hf {{x}, A} (by
      intro C hC
      simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff, mem_singleton_iff] at hC
      rcases hC with rfl | rfl
      · exact h1
      · exact hA)
    have hy1 : y ∈ ({x} : Set X) := hy {x} (by simp)
    have hy2 : y ∈ A := hy A (by simp)
    rw [mem_singleton_iff] at hy1
    exact hx (hy1 ▸ hy2)

theorem mem_pt_iff [T1Space X] {x : X} {A : Set X} : A ∈ (pt x).sets ↔ IsClosed A ∧ x ∈ A := Iff.rfl

theorem pt_mem_star [T1Space X] {x : X} {O : Set X} : pt x ∈ star O ↔ x ∈ O :=
  ⟨fun ⟨_, hF, hFO⟩ => hFO hF.2, fun h => ⟨{x}, ⟨isClosed_singleton, rfl⟩, by simpa using h⟩⟩

theorem pt_injective [T1Space X] : Function.Injective (pt : X → Wallman X) := by
  intro x y h
  have : ({x} : Set X) ∈ (pt y).sets := h ▸ (⟨isClosed_singleton, rfl⟩ : ({x} : Set X) ∈ (pt x).sets)
  exact (mem_singleton_iff.1 this.2).symm

theorem continuous_pt [T1Space X] : Continuous (pt : X → Wallman X) := by
  refine continuous_generateFrom_iff.2 ?_
  rintro _ ⟨O, hO, rfl⟩
  have : (pt : X → Wallman X) ⁻¹' star O = O := by ext x; exact pt_mem_star
  rw [this]; exact hO

/-- Morris, Topology Without Tears, Theorem A6.4.6 (TP-698). `X` is a subspace of `Wallman X`. -/
@[kb "morris2024" "Theorem A6.4.6, p. 667"]
theorem isEmbedding_pt [T1Space X] : Topology.IsEmbedding (pt : X → Wallman X) := by
  refine ⟨⟨le_antisymm (continuous_iff_le_induced.1 continuous_pt) ?_⟩, pt_injective⟩
  change induced pt (generateFrom {s | ∃ O : Set X, IsOpen O ∧ s = star O}) ≤ _
  rw [induced_generateFrom_eq]
  intro O hO
  have : (pt : X → Wallman X) ⁻¹' star O = O := by ext x; exact pt_mem_star
  exact isOpen_generateFrom_of_mem ⟨star O, ⟨O, hO, rfl⟩, this⟩

/-- Morris, Topology Without Tears, Theorem A6.4.6 (TP-698). `X` is dense in `Wallman X`. -/
@[kb "morris2024" "Theorem A6.4.6, p. 667"]
theorem denseRange_pt [T1Space X] : DenseRange (pt : X → Wallman X) := by
  rw [DenseRange, isTopologicalBasis_star.dense_iff]
  rintro _ ⟨O, hO, rfl⟩ ⟨u, F, hF, hFO⟩
  obtain ⟨x, hx⟩ : F.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    exact u.empty_not_mem (h ▸ hF)
  exact ⟨pt x, pt_mem_star.2 (hFO hx), x, rfl⟩

/-! ### Separation and compactness -/

/-- Morris, Topology Without Tears, Theorem A6.4.6 (TP-698): `Wallman X` is T1. -/
instance instT1Space : T1Space (Wallman X) where
  t1 u := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro v hv
    have huv : u ≠ v := fun h => hv (by simp [h])
    obtain ⟨A, hA, hAv⟩ := u.exists_mem_not_mem v huv
    have hO : IsOpen Aᶜ := (u.isClosed A hA).isOpen_compl
    refine ⟨star Aᶜ, ?_, isOpen_star hO, ?_⟩
    · intro w hw hwu
      rw [mem_singleton_iff] at hwu
      subst hwu
      have := (w.compl_not_mem_iff hO).2 hw
      rw [compl_compl] at this
      exact this hA
    · exact (v.compl_not_mem_iff hO).1 (by rwa [compl_compl])

/-- Morris, Topology Without Tears, Theorem A6.4.6 (TP-698): `Wallman X` is compact. -/
instance instCompactSpace : CompactSpace (Wallman X) := by
  refine compactSpace_generateFrom (S := {s | ∃ O : Set X, IsOpen O ∧ s = star O}) rfl ?_
  intro P hP hcov
  choose! O hO hsO using fun s (hs : s ∈ P) => hP hs
  by_cases hF : FIP ((fun s => (O s)ᶜ) '' P)
  · exfalso
    obtain ⟨u, hu⟩ := exists_of_fip (by rintro _ ⟨s, hs, rfl⟩; exact (hO s hs).isClosed_compl) hF
    obtain ⟨s, hsP, hus⟩ : u ∈ ⋃₀ P := hcov ▸ mem_univ u
    rw [hsO s hsP] at hus
    exact ((u.compl_not_mem_iff (hO s hsP)).2 hus) (hu ⟨s, hsP, rfl⟩)
  · unfold FIP at hF
    push Not at hF
    obtain ⟨t, ht, hemp⟩ := hF
    obtain ⟨T, hTP, hTf, hT⟩ := (exists_subset_image_finite_and (f := fun s => (O s)ᶜ) (s := P)
      (p := fun T => ⋂₀ T = ∅)).1 ⟨t, ht, t.finite_toSet, hemp⟩
    refine ⟨T, hTP, hTf, eq_univ_of_forall fun u => ?_⟩
    by_contra hnot
    simp only [mem_sUnion, not_exists, not_and] at hnot
    classical
    have hsub : (↑(hTf.toFinset.image fun s => (O s)ᶜ) : Set (Set X)) ⊆ u.sets := by
      intro A hA
      simp only [Finset.coe_image, Set.Finite.coe_toFinset, mem_image] at hA
      obtain ⟨s, hs, rfl⟩ := hA
      by_contra hc
      exact hnot s hs (by
        rw [hsO s (hTP hs)]; exact (u.compl_not_mem_iff (hO s (hTP hs))).1 hc)
    have := u.sInter_mem _ hsub
    rw [Finset.coe_image, Set.Finite.coe_toFinset, hT] at this
    exact u.empty_not_mem this

/-- Morris, Topology Without Tears, Proposition A6.4.7 (TP-699). For a T1 space `X`, the Wallman
space is Hausdorff iff `X` is normal. -/
@[kb "morris2024" "Proposition A6.4.7, p. 669"]
theorem t2Space_iff_normalSpace [T1Space X] : T2Space (Wallman X) ↔ NormalSpace X := by
  constructor
  · intro h
    refine ⟨fun C₁ C₂ h₁ h₂ hd => ?_⟩
    have hN : NormalSpace (Wallman X) := inferInstance
    have hdis : Disjoint {u : Wallman X | C₁ ∈ u.sets} {u : Wallman X | C₂ ∈ u.sets} := by
      rw [Set.disjoint_left]
      intro u hu1 hu2
      have := u.inter_mem hu1 hu2
      rw [Set.disjoint_iff_inter_eq_empty.1 hd] at this
      exact u.empty_not_mem this
    obtain ⟨V₁, V₂, hV₁, hV₂, hs₁, hs₂, hVd⟩ :=
      hN.normal _ _ (isClosed_plus h₁) (isClosed_plus h₂) hdis
    refine ⟨pt ⁻¹' V₁, pt ⁻¹' V₂, hV₁.preimage continuous_pt, hV₂.preimage continuous_pt,
      fun x hx => hs₁ ⟨h₁, hx⟩, fun x hx => hs₂ ⟨h₂, hx⟩, ?_⟩
    exact hVd.preimage _
  · intro h
    refine ⟨fun u v huv => ?_⟩
    obtain ⟨A, hA, B, hB, hAB⟩ := (ne_iff_exists_disjoint u v).1 huv
    obtain ⟨U, V, hU, hV, hAU, hBV, hUV⟩ :=
      NormalSpace.normal A B (u.isClosed A hA) (v.isClosed B hB) hAB
    have hd : Disjoint (star U) (star V) := by
      rw [Set.disjoint_iff_inter_eq_empty, ← star_inter, Set.disjoint_iff_inter_eq_empty.1 hUV,
        star_empty]
    exact ⟨star U, star V, isOpen_star hU, isOpen_star hV, ⟨A, hA, hAU⟩, ⟨B, hB, hBV⟩, hd⟩

/-! ### Extension of maps into compact Hausdorff spaces -/

section Extension

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K] {f : X → K}

theorem exists_unique_point (hf : Continuous f) :
    ∃! k : K, ∀ F ∈ u.sets, k ∈ closure (f '' F) := by
  refine existsUnique_of_exists_of_unique ?_ ?_
  · have := isCompact_univ.inter_iInter_nonempty (fun F : u.sets => closure (f '' (F : Set X)))
      (fun _ => isClosed_closure) (fun p => by
        classical
        have hG := u.sInter_mem (p.image Subtype.val) (by
          intro A hA
          obtain ⟨B, -, rfl⟩ := Finset.mem_image.1 hA
          exact B.2)
        obtain ⟨y, hy⟩ : (⋂₀ (↑(p.image Subtype.val) : Set (Set X))).Nonempty := by
          by_contra h
          rw [not_nonempty_iff_eq_empty] at h
          exact u.empty_not_mem (h ▸ hG)
        refine ⟨f y, mem_univ _, ?_⟩
        simp only [mem_iInter]
        intro F hF
        exact subset_closure ⟨y, hy F (by simp [hF]), rfl⟩)
    obtain ⟨k, -, hk⟩ := this
    exact ⟨k, fun F hF => mem_iInter.1 hk ⟨F, hF⟩⟩
  · intro k₁ k₂ h₁ h₂
    by_contra hne
    obtain ⟨V₁, V₂, hV₁, hV₂, hk₁, hk₂, hd⟩ := t2_separation hne
    have hA₁ : IsClosed (f ⁻¹' V₁ᶜ) := hV₁.isClosed_compl.preimage hf
    have hA₂ : IsClosed (f ⁻¹' V₂ᶜ) := hV₂.isClosed_compl.preimage hf
    have hU : f ⁻¹' V₁ᶜ ∪ f ⁻¹' V₂ᶜ = univ := by
      refine eq_univ_of_forall fun x => ?_
      by_contra hx
      simp only [mem_union, mem_preimage, mem_compl_iff, not_or, not_not] at hx
      exact Set.disjoint_left.1 hd hx.1 hx.2
    have hmem := (u.union_mem_iff hA₁ hA₂).1 (hU ▸ u.univ_mem)
    rcases hmem with h | h
    · have := closure_minimal (image_subset_iff.2 subset_rfl) hV₁.isClosed_compl (h₁ _ h)
      exact this hk₁
    · have := closure_minimal (image_subset_iff.2 subset_rfl) hV₂.isClosed_compl (h₂ _ h)
      exact this hk₂

/-- The extension of `f : X → K` to the Wallman space: the unique point of `K` lying in the
closure of `f '' F` for every member `F` of the ultrafilter. -/
noncomputable def extension (f : X → K) (hf : Continuous f) (u : Wallman X) : K :=
  Classical.choose (exists_unique_point u hf).exists

theorem extension_mem (hf : Continuous f) (F : Set X) (hF : F ∈ u.sets) :
    extension f hf u ∈ closure (f '' F) :=
  Classical.choose_spec (exists_unique_point u hf).exists F hF

theorem extension_pt [T1Space X] (hf : Continuous f) (x : X) : extension f hf (pt x) = f x :=
  ((exists_unique_point (pt x) hf).unique (extension_mem (pt x) hf) fun _ hF =>
    subset_closure ⟨x, hF.2, rfl⟩)

theorem continuous_extension (hf : Continuous f) : Continuous (extension f hf) := by
  refine continuous_iff_continuousAt.2 fun u => ?_
  refine Filter.tendsto_def.2 fun s hs => ?_
  obtain ⟨t, ht, htc, hts⟩ := exists_mem_nhds_isClosed_subset hs
  have hgu : extension f hf u ∈ interior t := mem_interior_iff_mem_nhds.2 ht
  have hO : IsOpen (f ⁻¹' interior t) := isOpen_interior.preimage hf
  have h1 : u ∈ star (f ⁻¹' interior t) := by
    rw [mem_star, ← u.compl_not_mem_iff hO]
    intro hc
    have := closure_minimal (s := f '' (f ⁻¹' interior t)ᶜ) (t := (interior t)ᶜ)
      (by rintro _ ⟨x, hx, rfl⟩; exact hx) isOpen_interior.isClosed_compl (extension_mem u hf _ hc)
    exact this hgu
  refine Filter.mem_of_superset ((isOpen_star hO).mem_nhds h1) fun v hv => ?_
  obtain ⟨F, hF, hFO⟩ := hv
  have := closure_minimal (s := f '' F) (t := t)
    (fun y ⟨x, hx, hxy⟩ => interior_subset (hxy ▸ hFO hx)) htc |> fun h => h (extension_mem v hf F hF)
  exact hts this

end Extension

/-- Morris, Topology Without Tears, Theorem A6.4.6 (TP-698). The Wallman space of a T1 space is a
compact T1 space containing `X` as a dense subspace, and every continuous map from `X` to a compact
Hausdorff space extends continuously to it. -/
@[kb "morris2024" "Theorem A6.4.6, p. 667"]
theorem wallman_compactification (X : Type*) [TopologicalSpace X] [T1Space X] :
    CompactSpace (Wallman X) ∧ T1Space (Wallman X) ∧ Topology.IsEmbedding (pt : X → Wallman X) ∧
      DenseRange (pt : X → Wallman X) ∧
      ∀ (K : Type _) [TopologicalSpace K] [CompactSpace K] [T2Space K] (f : X → K),
        Continuous f → ∃ g : Wallman X → K, Continuous g ∧ ∀ x, g (pt x) = f x :=
  ⟨inferInstance, inferInstance, isEmbedding_pt, denseRange_pt,
    fun _ _ _ _ _ hf => ⟨extension _ hf, continuous_extension hf, extension_pt hf⟩⟩

/-- Morris, Topology Without Tears, Corollary A6.4.8 (TP-700), the "if" half. For a normal T1 space
the Wallman space is the Stone-Cech compactification: there is a homeomorphism commuting with the
maps from `X`. -/
@[kb "morris2024" "Corollary A6.4.8, p. 670"]
theorem exists_homeomorph_stoneCech [T1Space X] [NormalSpace X] :
    ∃ e : Wallman X ≃ₜ StoneCech X, ∀ x, e (pt x) = stoneCechUnit x := by
  have : T2Space (Wallman X) := t2Space_iff_normalSpace.2 ‹_›
  let φ : Wallman X → StoneCech X := extension stoneCechUnit continuous_stoneCechUnit
  have hφ : Continuous φ := continuous_extension _
  have hφpt : ∀ x, φ (pt x) = stoneCechUnit x := extension_pt _
  let ψ : StoneCech X → Wallman X := stoneCechExtend (continuous_pt (X := X))
  have hψ : Continuous ψ := continuous_stoneCechExtend _
  have hψu : ∀ x, ψ (stoneCechUnit x) = pt x := stoneCechExtend_stoneCechUnit _
  have h1 : φ ∘ ψ = id := stoneCech_hom_ext (hφ.comp hψ) continuous_id (by
    ext x; simp [hψu, hφpt])
  have h2 : ψ ∘ φ = id := denseRange_pt.equalizer (hψ.comp hφ) continuous_id (by
    ext x; simp [hψu, hφpt])
  let e : Wallman X ≃ₜ StoneCech X :=
    { toFun := φ
      invFun := ψ
      left_inv := fun w => congrFun h2 w
      right_inv := fun w => congrFun h1 w
      continuous_toFun := hφ
      continuous_invFun := hψ }
  exact ⟨e, hφpt⟩

/-- Morris, Topology Without Tears, Corollary A6.4.8 (TP-700). For a T1 space `X`, the Wallman
space is the Stone-Cech compactification (via a homeomorphism commuting with the maps from `X`) iff
`X` is normal (hence normal Hausdorff). -/
@[kb "morris2024" "Corollary A6.4.8, p. 670"]
theorem normalSpace_iff_exists_homeomorph_stoneCech [T1Space X] :
    NormalSpace X ↔ ∃ e : Wallman X ≃ₜ StoneCech X, ∀ x, e (pt x) = stoneCechUnit x := by
  constructor
  · intro h
    exact exists_homeomorph_stoneCech
  · rintro ⟨e, -⟩
    have : T2Space (Wallman X) := e.isEmbedding.t2Space
    exact t2Space_iff_normalSpace.1 this

section Discrete

universe u

variable {Y : Type u} [TopologicalSpace Y] [DiscreteTopology Y]

/-- On a discrete space, closed-set ultrafilters are exactly ultrafilters (all sets are closed). -/
def equivUltrafilter : Wallman Y ≃ Ultrafilter Y where
  toFun u := Ultrafilter.ofComplNotMemIff
    { sets := u.sets
      univ_sets := u.univ_mem
      sets_of_superset := fun hA hAB => u.mem_of_subset hA hAB (isClosed_discrete _)
      inter_sets := fun hA hB => u.inter_mem hA hB } (fun A => by
        change Aᶜ ∉ u.sets ↔ A ∈ u.sets
        rw [u.compl_not_mem_iff (isOpen_discrete A)]
        exact ⟨fun ⟨F, hF, hFA⟩ => u.mem_of_subset hF hFA (isClosed_discrete _),
          fun h => ⟨A, h, subset_rfl⟩⟩)
  invFun v :=
    { sets := {A | A ∈ v}
      isClosed := fun A _ => isClosed_discrete A
      fip := fun s hs => by
        have : ⋂₀ (↑s : Set (Set Y)) ∈ (v : Filter Y) :=
          (Filter.sInter_mem s.finite_toSet).2 hs
        exact Filter.nonempty_of_mem this
      maximal := fun B _ hf hvB A hA => by
        by_contra hAv
        have h1 : Aᶜ ∈ v := Ultrafilter.compl_mem_iff_notMem.2 hAv
        classical
        obtain ⟨y, hy⟩ := hf {A, Aᶜ} (by
          intro C hC
          simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff,
            mem_singleton_iff] at hC
          rcases hC with rfl | rfl
          · exact hA
          · exact hvB h1)
        have h2 : y ∈ A := hy A (by simp)
        have h3 : y ∈ Aᶜ := hy Aᶜ (by simp)
        exact h3 h2 }
  left_inv u := Wallman.ext (by ext A; rfl)
  right_inv v := Ultrafilter.coe_injective (Filter.ext fun A => Iff.rfl)

/-- Morris, Topology Without Tears, Corollary A6.4.10 (TP-702). The Wallman space of an infinite
discrete space of cardinality `m` has cardinality `2 ^ (2 ^ m)`. -/
@[kb "morris2024" "Corollary A6.4.10, p. 670"]
theorem mk_wallman_of_discrete [Infinite Y] :
    Cardinal.mk (Wallman Y) = 2 ^ (2 ^ Cardinal.mk Y : Cardinal) := by
  rw [Cardinal.mk_congr equivUltrafilter]
  exact Cardinal.mk_ultrafilter_of_infinite

end Discrete

/-! ### Unbounded subsets of normed spaces -/

/-- An unbounded metric space contains a sequence of distinct points all of whose subsets are
closed (a closed discrete copy of `ℕ`). -/
theorem exists_closed_discrete_seq {Y : Type*} [MetricSpace Y]
    (hY : ¬ Bornology.IsBounded (univ : Set Y)) :
    ∃ x : ℕ → Y, Function.Injective x ∧ ∀ T ⊆ range x, IsClosed T := by
  obtain ⟨y0⟩ : Nonempty Y := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hY (by simp [Set.univ_eq_empty_iff.2 h])
  have hfar : ∀ r : ℝ, ∃ y : Y, r < dist y y0 := by
    intro r
    by_contra h
    push Not at h
    exact hY ((Metric.isBounded_closedBall (x := y0) (r := r)).subset fun y _ => by
      simpa using h y)
  choose f hf using hfar
  let x : ℕ → Y := fun n => Nat.rec (f 0) (fun _ y => f (dist y y0 + 1)) n
  have hx0 : x 0 = f 0 := rfl
  have hxs : ∀ n, x (n + 1) = f (dist (x n) y0 + 1) := fun n => rfl
  have hstep : ∀ n, dist (x n) y0 + 1 < dist (x (n + 1)) y0 := fun n => by
    rw [hxs]; exact hf _
  have hge : ∀ n : ℕ, (n : ℝ) ≤ dist (x n) y0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => push_cast; linarith [hstep n]
  have hmono : StrictMono fun n => dist (x n) y0 :=
    strictMono_nat_of_lt_succ fun n => by linarith [hstep n]
  refine ⟨x, fun m n h => hmono.injective (by simp only [h]), fun T hT => ?_⟩
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro y hy
  let N : Set ℕ := {n | dist (x n) y0 ≤ dist y y0 + 1}
  have hN : N.Finite := (Set.finite_Iic ⌈dist y y0 + 1⌉₊).subset fun n hn => by
    have h1 : (n : ℝ) ≤ dist y y0 + 1 := (hge n).trans hn
    exact Nat.cast_le.1 (h1.trans (Nat.le_ceil _))
  let F : Set Y := T ∩ x '' N
  have hF : F.Finite := (hN.image x).subset inter_subset_right
  have hyF : y ∉ F := fun h => hy h.1
  refine Filter.mem_of_superset (Filter.inter_mem (Metric.ball_mem_nhds y one_pos)
    (hF.isClosed.isOpen_compl.mem_nhds hyF)) ?_
  rintro z ⟨hz1, hz2⟩ hzT
  obtain ⟨n, rfl⟩ := hT hzT
  refine hz2 ⟨hzT, n, ?_, rfl⟩
  have := dist_triangle (x n) y y0
  rw [Metric.mem_ball] at hz1
  show dist (x n) y0 ≤ dist y y0 + 1
  linarith [dist_comm y (x n)]

/-- If `ℕ` embeds as a sequence all of whose subsets are closed, then every ultrafilter on `ℕ`
yields a closed-set ultrafilter, injectively. -/
theorem card_ultrafilter_nat_le {Y : Type} [TopologicalSpace Y] {x : ℕ → Y}
    (hinj : Function.Injective x) (hcl : ∀ T ⊆ range x, IsClosed T) :
    Cardinal.mk (Ultrafilter ℕ) ≤ Cardinal.mk (Wallman Y) := by
  have hex : ∀ p : Ultrafilter ℕ, ∃ u : Wallman Y, ∀ S ∈ p, x '' S ∈ u.sets := by
    intro p
    obtain ⟨u, hu⟩ := exists_of_fip (F := {A | ∃ S ∈ p, A = x '' S})
      (by rintro _ ⟨S, -, rfl⟩; exact hcl _ (image_subset_range _ _)) (by
        classical
        intro s hs
        have hT : ⋂₀ ((fun A => x ⁻¹' A) '' (↑s : Set (Set Y))) ∈ (p : Filter ℕ) :=
          (Filter.sInter_mem (s.finite_toSet.image _)).2 (by
            rintro _ ⟨A, hA, rfl⟩
            obtain ⟨S, hS, rfl⟩ := hs hA
            show x ⁻¹' (x '' S) ∈ (p : Filter ℕ)
            rw [hinj.preimage_image]
            exact hS)
        obtain ⟨n, hn⟩ := Filter.nonempty_of_mem hT
        exact ⟨x n, fun A hA => hn _ ⟨A, hA, rfl⟩⟩)
    exact ⟨u, fun S hS => hu ⟨S, hS, rfl⟩⟩
  choose g hg using hex
  refine Cardinal.mk_le_of_injective (f := g) fun p q hpq => ?_
  refine Ultrafilter.eq_of_le (Filter.le_def.2 fun S hS => ?_)
  by_contra hSq
  have hSc : Sᶜ ∈ p := Ultrafilter.compl_mem_iff_notMem.2 hSq
  have h1 := hg q S hS
  have h2 : x '' Sᶜ ∈ (g q).sets := hpq ▸ hg p Sᶜ hSc
  have := (g q).inter_mem h1 h2
  rw [← image_inter hinj, inter_compl_self, image_empty] at this
  exact (g q).empty_not_mem this

/-- Morris, Topology Without Tears, Corollary A6.4.9 (TP-701). An unbounded subset `X` of a normed
space has at least `2 ^ 𝔠` closed-set ultrafilters, i.e. the Wallman space `ωX` has cardinality
at least `2 ^ 𝔠`. -/
@[kb "morris2024" "Corollary A6.4.9, p. 670"]
theorem two_pow_continuum_le_card_wallman {E : Type} [NormedAddCommGroup E] {X : Set E}
    (hX : ¬ Bornology.IsBounded X) : 2 ^ Cardinal.continuum ≤ Cardinal.mk (Wallman X) := by
  have hY : ¬ Bornology.IsBounded (univ : Set X) := by
    intro h
    apply hX
    obtain ⟨C, hC⟩ := Metric.isBounded_iff.1 h
    exact Metric.isBounded_iff.2 ⟨C, fun a ha b hb => hC (mem_univ ⟨a, ha⟩) (mem_univ ⟨b, hb⟩)⟩
  obtain ⟨x, hinj, hcl⟩ := exists_closed_discrete_seq hY
  have h1 : Cardinal.mk (Ultrafilter ℕ) = 2 ^ (2 ^ Cardinal.mk ℕ : Cardinal) :=
    Cardinal.mk_ultrafilter_of_infinite
  rw [Cardinal.mk_nat, Cardinal.two_power_aleph0] at h1
  exact h1 ▸ card_ultrafilter_nat_le hinj hcl

/-- Morris, Topology Without Tears, Corollary A6.4.9 (TP-701). The Stone-Cech compactification of an
unbounded subset of a normed space has cardinality at least `2 ^ 𝔠` (it is the Wallman space). -/
@[kb "morris2024" "Corollary A6.4.9, p. 670"]
theorem two_pow_continuum_le_card_stoneCech {E : Type} [NormedAddCommGroup E] {X : Set E}
    (hX : ¬ Bornology.IsBounded X) : 2 ^ Cardinal.continuum ≤ Cardinal.mk (StoneCech X) := by
  obtain ⟨e, -⟩ := exists_homeomorph_stoneCech (X := X)
  rw [← Cardinal.mk_congr e.toEquiv]
  exact two_pow_continuum_le_card_wallman hX

end Wallman

end UndergradKB.Topology
