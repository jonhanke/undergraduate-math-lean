import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Separation.Basic
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.QuotientGroup
import UndergradKB.Common.Attr

/-!
# Wave 2: monothetic groups and compact elements (Morris, Appendix 5)

Weil's lemma (a monothetic locally compact Hausdorff abelian group is compact or `ℤ`), and the
subgroup of compact elements.
-/

open Set Filter
open scoped Topology

namespace UndergradKB.Topology

section Monothetic

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]

/-- In a non-discrete Hausdorff group with a dense cyclic subgroup `⟨x⟩`, every neighbourhood of `0`
contains infinitely many multiples of `x` (as a set of indices). -/
theorem monothetic_infinite_indices (x : G) (hx : Dense (AddSubgroup.zmultiples x : Set G))
    (hnd : ¬ DiscreteTopology G) {W : Set G} (hW : W ∈ 𝓝 (0 : G)) :
    {n : ℤ | n • x ∈ W}.Infinite := by
  intro hfin
  apply hnd
  set F : Set G := ((fun n : ℤ => n • x) '' {n : ℤ | n • x ∈ W}) \ {0} with hF
  have hFfin : F.Finite := (hfin.image _).sdiff
  set W' : Set G := interior W ∩ Fᶜ with hW'
  have hW'open : IsOpen W' := isOpen_interior.inter hFfin.isClosed.isOpen_compl
  have h0 : (0 : G) ∈ W' := ⟨mem_interior_iff_mem_nhds.2 hW, by simp [hF]⟩
  have key : W' = {0} := by
    refine Set.Subset.antisymm ?_ (by simpa using h0)
    intro y hy
    by_contra hy0
    have hopen : IsOpen (W' \ {0}) := hW'open.sdiff isClosed_singleton
    obtain ⟨z, hz, hzU⟩ := hx.exists_mem_open hopen ⟨y, hy, hy0⟩
    obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hz
    exact hzU.1.2 ⟨⟨n, (interior_subset (s := W) hzU.1.1 : n • x ∈ W), rfl⟩, hzU.2⟩
  exact discreteTopology_of_isOpen_singleton_zero (key ▸ hW'open)

/-- In a non-discrete Hausdorff group with a dense cyclic subgroup `⟨x⟩`, for every neighbourhood `W`
of `0` and every integer `k` there is an integer `j < k` with `j • x ∈ W`. -/
theorem monothetic_exists_lt (x : G) (hx : Dense (AddSubgroup.zmultiples x : Set G))
    (hnd : ¬ DiscreteTopology G) {W : Set G} (hW : W ∈ 𝓝 (0 : G)) (k : ℤ) :
    ∃ j : ℤ, j < k ∧ j • x ∈ W := by
  have hW2 : W ∩ -W ∈ 𝓝 (0 : G) := inter_mem hW (neg_mem_nhds_zero G hW)
  have hinf := monothetic_infinite_indices x hx hnd hW2
  by_contra hcon
  push Not at hcon
  apply hinf
  refine (Set.finite_Icc k (-k)).subset ?_
  intro n hn
  have hn' : n • x ∈ W ∩ -W := hn
  have h1 : k ≤ n := by
    by_contra h
    exact hcon n (not_le.1 h) hn'.1
  have h2 : k ≤ -n := by
    by_contra h
    refine hcon (-n) (not_le.1 h) ?_
    have := hn'.2
    simpa using this
  exact ⟨h1, by omega⟩

/-- Cover step of Weil's lemma: if `V` is open and contains `0`, every `g` lies in `i • x + V` for some
positive `i`. -/
theorem monothetic_exists_pos (x : G) (hx : Dense (AddSubgroup.zmultiples x : Set G))
    (hnd : ¬ DiscreteTopology G) {V : Set G} (hV : IsOpen V) (h0 : (0 : G) ∈ V) (g : G) :
    ∃ i : ℕ, 0 < i ∧ g - i • x ∈ V := by
  have hU : IsOpen {y : G | g - y ∈ V} := hV.preimage (continuous_const.sub continuous_id)
  obtain ⟨z, hz, hzU⟩ := hx.exists_mem_open hU ⟨g, by simpa using h0⟩
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hz
  have hWn : {w : G | (g - k • x) + w ∈ V} ∈ 𝓝 (0 : G) := by
    refine (hV.preimage (continuous_const.add continuous_id)).mem_nhds ?_
    simpa using hzU
  obtain ⟨j, hjk, hj⟩ := monothetic_exists_lt x hx hnd hWn k
  refine ⟨(k - j).toNat, by omega, ?_⟩
  have : ((k - j).toNat : ℤ) = k - j := Int.toNat_of_nonneg (by omega)
  have e : ((k - j).toNat) • x = (k - j) • x := by
    rw [← natCast_zsmul, this]
  have e2 : g - (k - j) • x = (g - k • x) + j • x := by
    rw [sub_smul]; abel
  rw [e, e2]
  exact hj

/-- A non-discrete monothetic locally compact Hausdorff abelian group is compact. -/
theorem compactSpace_of_monothetic_not_discrete [LocallyCompactSpace G] (x : G)
    (hx : Dense (AddSubgroup.zmultiples x : Set G)) (hnd : ¬ DiscreteTopology G) :
    CompactSpace G := by
  obtain ⟨K, hKc, hK⟩ := exists_compact_mem_nhds (0 : G)
  set V : Set G := interior K ∩ -interior K with hVdef
  have hVopen : IsOpen V := isOpen_interior.inter isOpen_interior.neg
  have hV0 : (0 : G) ∈ V := ⟨mem_interior_iff_mem_nhds.2 hK, by
    simpa using mem_interior_iff_mem_nhds.2 hK⟩
  have hVsymm : ∀ v ∈ V, -v ∈ V := by
    intro v hv
    exact ⟨by simpa using hv.2, by simpa using hv.1⟩
  have hVK : V ⊆ K := fun v hv => interior_subset hv.1
  have hclK : closure V ⊆ K := closure_minimal hVK hKc.isClosed
  have hclc : IsCompact (closure V) := hKc.of_isClosed_subset isClosed_closure hclK
  -- the sets `{g | g - (i+1) • x ∈ V}` cover `G`
  have hopen : ∀ i : ℕ, IsOpen {g : G | g - (i + 1) • x ∈ V} := fun i =>
    hVopen.preimage (continuous_id.sub continuous_const)
  have hcov : closure V ⊆ ⋃ i : ℕ, {g : G | g - (i + 1) • x ∈ V} := by
    intro g _
    obtain ⟨i, hi, hg⟩ := monothetic_exists_pos x hx hnd hVopen hV0 g
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
    exact mem_iUnion.2 ⟨n, by simpa using hg⟩
  obtain ⟨t, ht⟩ := hclc.elim_finite_subcover _ hopen hcov
  set N : ℕ := t.sup id with hN
  have hstep : ∀ n : ℕ, ∀ g : G, g - (n + 1) • x ∈ V → ∃ m ≤ N, g - (m + 1) • x ∈ V := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro g hg
      have h1 : (n + 1) • x - g ∈ closure V := subset_closure (by
        simpa using hVsymm _ hg)
      obtain ⟨i, hit, hi⟩ := mem_iUnion₂.1 (ht h1)
      have hiN : i ≤ N := Finset.le_sup (f := id) hit
      by_cases hlt : i < n
      · obtain ⟨n', hn'⟩ : ∃ n', n = n' + i + 1 := ⟨n - i - 1, by omega⟩
        have : g - (n' + 1) • x ∈ V := by
          have := hVsymm _ hi
          convert this using 1
          rw [hn']
          simp only [add_smul, one_smul, neg_sub]
          abel
        obtain ⟨m, hm, hmV⟩ := ih n' (by omega) g this
        exact ⟨m, hm, hmV⟩
      · exact ⟨n, by omega, hg⟩
  have hunivsub : (Set.univ : Set G) ⊆
      ⋃ m ∈ Finset.range (N + 1), (fun y : G => y + (m + 1) • x) '' closure V := by
    intro g _
    obtain ⟨i, hi, hg⟩ := monothetic_exists_pos x hx hnd hVopen hV0 g
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
    obtain ⟨m, hm, hmV⟩ := hstep n g (by simpa using hg)
    refine mem_iUnion₂.2 ⟨m, Finset.mem_range.2 (by omega), g - (m + 1) • x, subset_closure hmV, ?_⟩
    simp
  have hcomp : IsCompact (⋃ m ∈ Finset.range (N + 1), (fun y : G => y + (m + 1) • x) '' closure V) :=
    Finset.isCompact_biUnion _ fun m _ => hclc.image (continuous_id.add continuous_const)
  exact ⟨hcomp.of_isClosed_subset isClosed_univ hunivsub⟩

/-- Morris, Topology Without Tears, Theorem A5.12.3 (TP-596). A monothetic locally compact Hausdorff
abelian group (one with an element generating a dense subgroup) is either compact or topologically
isomorphic to the discrete group `ℤ`. -/
@[kb "morris2024" "Theorem A5.12.3, p. 582"]
theorem compactSpace_or_continuousAddEquiv_int [LocallyCompactSpace G]
    (h : ∃ x : G, Dense (AddSubgroup.zmultiples x : Set G)) :
    CompactSpace G ∨ Nonempty (G ≃ₜ+ ℤ) := by
  obtain ⟨x, hx⟩ := h
  by_cases hd : DiscreteTopology G
  · have hz : (AddSubgroup.zmultiples x : Set G) = Set.univ := dense_discrete.1 hx
    have hsurj : Function.Surjective (fun n : ℤ => n • x) := by
      intro g
      have : g ∈ (AddSubgroup.zmultiples x : Set G) := by rw [hz]; trivial
      obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 this
      exact ⟨n, hn⟩
    by_cases hf : IsOfFinAddOrder x
    · left
      have : Finite (AddSubgroup.zmultiples x) := hf.finite_zmultiples
      have : Finite G := Finite.of_surjective (fun n : AddSubgroup.zmultiples x => (n : G)) (by
        intro g
        have : g ∈ (AddSubgroup.zmultiples x : Set G) := by rw [hz]; trivial
        exact ⟨⟨g, this⟩, rfl⟩)
      infer_instance
    · right
      have hinj : Function.Injective (fun n : ℤ => n • x) :=
        injective_zsmul_iff_not_isOfFinAddOrder.2 hf
      let e : ℤ ≃+ G := AddEquiv.ofBijective (zmultiplesHom G x) ⟨hinj, hsurj⟩
      exact ⟨{ toAddEquiv := e.symm
               continuous_toFun := continuous_of_discreteTopology
               continuous_invFun := continuous_of_discreteTopology }⟩
  · exact Or.inl (compactSpace_of_monothetic_not_discrete x hx hd)

end Monothetic

/-! ### Compact elements (TP-629) -/

section CompactElements

open Pointwise

variable (G : Type*) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]

/-- Bridging definition for Morris, Definition A5.15.4 (TP-629). The set of compact elements of a
topological abelian group: those `g` for which the smallest closed subgroup containing `g`, namely the
closure of `⟨g⟩`, is compact. It is a subgroup (Proposition A5.15.6); whether it is closed is the missing
part, see the docstring of `mem_compactElements_iff`. -/
def compactElements : AddSubgroup G where
  carrier := {g | IsCompact (closure (AddSubgroup.zmultiples g : Set G))}
  zero_mem' := by
    have : (AddSubgroup.zmultiples (0 : G) : Set G) = {0} := by
      ext y; simp
    show IsCompact (closure (AddSubgroup.zmultiples (0 : G) : Set G))
    rw [this, closure_singleton]
    exact isCompact_singleton
  add_mem' := by
    intro g h hg hh
    have hg' : IsCompact (closure (AddSubgroup.zmultiples g : Set G)) := hg
    have hh' : IsCompact (closure (AddSubgroup.zmultiples h : Set G)) := hh
    show IsCompact (closure (AddSubgroup.zmultiples (g + h) : Set G))
    have hsum := hg'.add hh'
    refine hsum.of_isClosed_subset isClosed_closure ?_
    refine closure_minimal ?_ hsum.isClosed
    intro y hy
    obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hy
    rw [smul_add]
    exact Set.add_mem_add (subset_closure (AddSubgroup.mem_zmultiples_iff.2 ⟨n, rfl⟩))
      (subset_closure (AddSubgroup.mem_zmultiples_iff.2 ⟨n, rfl⟩))
  neg_mem' := by
    intro g hg
    have hg' : IsCompact (closure (AddSubgroup.zmultiples g : Set G)) := hg
    show IsCompact (closure (AddSubgroup.zmultiples (-g) : Set G))
    rwa [AddSubgroup.zmultiples_neg]

variable {G}

/-- Membership in `compactElements G`: the closure of the cyclic subgroup generated by `g` is compact.
(Morris's `gp {g}` is the closure of `⟨g⟩`, and `(AddSubgroup.zmultiples g).topologicalClosure` is that
closed subgroup.) -/
theorem mem_compactElements_iff {g : G} :
    g ∈ compactElements G ↔
      IsCompact ((AddSubgroup.zmultiples g).topologicalClosure : Set G) :=
  Iff.rfl

/-- Morris, Topology Without Tears, Proposition A5.15.6 (TP-629), the subgroup part. In a Hausdorff
abelian topological group the compact elements form a subgroup (closedness of this subgroup, which Morris
derives from the structure theorem for compactly generated LCA groups, is not proved here). -/
@[kb "morris2024" "Proposition A5.15.6, p. 610"]
theorem compactElements_isSubgroup (g h : G) (hg : g ∈ compactElements G) (hh : h ∈ compactElements G) :
    g - h ∈ compactElements G :=
  sub_mem hg hh

/-- Every element of a compact group is a compact element. -/
theorem compactElements_eq_top [CompactSpace G] : compactElements G = ⊤ := by
  refine top_unique fun g _ => ?_
  exact isClosed_closure.isCompact

end CompactElements

end UndergradKB.Topology
