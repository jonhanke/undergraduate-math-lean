import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Int.Basic
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Algebra.Module.Injective
import Mathlib.GroupTheory.Divisible
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Basic
import UndergradKB.Common.Attr

/-!
# Wave 2: subgroups of free abelian groups are free (Morris, Appendix 5, Remark A5.5.15 (iii))

Mathlib has this only for finitely generated modules over a PID. Here: for a well-ordered index set,
every `ℤ`-submodule of `ι →₀ ℤ` is free (leading-coefficient argument), then for any free `ℤ`-module.
-/

namespace UndergradKB.Topology

section Core

variable {ι : Type*} [LinearOrder ι] [WellFoundedLT ι] (N : Submodule ℤ (ι →₀ ℤ))

/-- The leading coefficients at `i` of the elements of `N` supported on indices `≤ i`. -/
def leadIdeal (i : ι) : Ideal ℤ where
  carrier := {c | ∃ x ∈ N, (∀ j, i < j → x j = 0) ∧ x i = c}
  zero_mem' := ⟨0, N.zero_mem, fun _ _ => rfl, rfl⟩
  add_mem' := by
    rintro _ _ ⟨x, hx, hxs, rfl⟩ ⟨y, hy, hys, rfl⟩
    exact ⟨x + y, N.add_mem hx hy, fun j hj => by simp [hxs j hj, hys j hj], rfl⟩
  smul_mem' := by
    rintro c _ ⟨x, hx, hxs, rfl⟩
    exact ⟨c • x, N.smul_mem c hx, fun j hj => by simp [hxs j hj], by simp⟩

theorem exists_lead (i : ι) : ∃ n ∈ N, (∀ j, i < j → n j = 0) ∧
    n i = Submodule.IsPrincipal.generator (leadIdeal N i) :=
  Submodule.IsPrincipal.generator_mem (leadIdeal N i)

theorem submodule_finsupp_free : Module.Free ℤ N := by
  classical
  choose n hnN hnsup hnlead using exists_lead N
  let gen : ι → ℤ := fun i => Submodule.IsPrincipal.generator (leadIdeal N i)
  let T : Type _ := {i : ι // gen i ≠ 0}
  let v : T → N := fun i => ⟨n i.1, hnN i.1⟩
  -- linear independence
  have hli : LinearIndependent ℤ v := by
    rw [linearIndependent_iff']
    intro s g hsum
    by_contra hcon
    push Not at hcon
    obtain ⟨i0, hi0s, hi0⟩ := hcon
    let s' : Finset T := s.filter (fun i => g i ≠ 0)
    have hne : s'.Nonempty := ⟨i0, Finset.mem_filter.2 ⟨hi0s, hi0⟩⟩
    let m : T := s'.max' hne
    have hm : m ∈ s' := Finset.max'_mem _ _
    have hmg : g m ≠ 0 := (Finset.mem_filter.1 hm).2
    have hmem : m ∈ s := (Finset.mem_filter.1 hm).1
    have h1 : (∑ i ∈ s, g i • n i.1) = 0 := by
      have := congrArg Subtype.val hsum
      simpa [v] using this
    have h2 := congrArg (Finsupp.lapply (R := ℤ) m.1) h1
    rw [map_sum, map_zero] at h2
    simp only [map_smul, Finsupp.lapply_apply, smul_eq_mul] at h2
    rw [Finset.sum_eq_single_of_mem m hmem] at h2
    · rw [hnlead] at h2
      exact mul_ne_zero hmg m.2 h2
    · intro i hi him
      by_cases hgi : g i = 0
      · simp [hgi]
      · have hi' : i ∈ s' := Finset.mem_filter.2 ⟨hi, hgi⟩
        have hle : i ≤ m := Finset.le_max' _ _ hi'
        have hlt : i.1 < m.1 := lt_of_le_of_ne hle (fun h => him (Subtype.ext h))
        rw [hnsup i.1 m.1 hlt]
        simp
  -- spanning
  let M : Submodule ℤ (ι →₀ ℤ) := Submodule.span ℤ (Set.range fun i : T => n i.1)
  have hspan : ∀ x ∈ N, x ∈ M := by
    have key : ∀ i : ι, ∀ x ∈ N, (∀ j, i < j → x j = 0) → x ∈ M := by
      intro i
      induction i using WellFoundedLT.induction with
      | _ i ih =>
        have hlow : ∀ y ∈ N, (∀ j, i ≤ j → y j = 0) → y ∈ M := by
          intro y hy hyz
          by_cases hy0 : y = 0
          · rw [hy0]; exact M.zero_mem
          · have hsne : y.support.Nonempty := Finsupp.support_nonempty_iff.2 hy0
            let m := y.support.max' hsne
            have hmm : m ∈ y.support := Finset.max'_mem _ _
            have hmi : m < i := by
              by_contra hh
              exact (Finsupp.mem_support_iff.1 hmm) (hyz m (not_lt.1 hh))
            refine ih m hmi y hy fun j hj => ?_
            by_contra hjy
            exact absurd (Finset.le_max' _ j (Finsupp.mem_support_iff.2 hjy)) (not_le.2 hj)
        intro x hx hxs
        obtain ⟨k, hk⟩ := (Submodule.IsPrincipal.mem_iff_eq_smul_generator (S := leadIdeal N i)).1
          (show x i ∈ leadIdeal N i from ⟨x, hx, hxs, rfl⟩)
        by_cases hg : gen i = 0
        · refine hlow x hx fun j hj => ?_
          rcases hj.eq_or_lt with rfl | hj'
          · rw [hk]; simp [gen] at hg; simp [hg]
          · exact hxs j hj'
        · have hnM : n i ∈ M := Submodule.subset_span ⟨⟨i, hg⟩, rfl⟩
          have hy : x - k • n i ∈ M := by
            refine hlow _ (N.sub_mem hx (N.smul_mem k (hnN i))) fun j hj => ?_
            rcases hj.eq_or_lt with rfl | hj'
            · simp only [Finsupp.coe_sub, Finsupp.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
              rw [hnlead, hk]; simp [gen]
            · simp [hxs j hj', hnsup i j hj']
          have := M.add_mem hy (M.smul_mem k hnM)
          simpa using this
    intro x hx
    by_cases hx0 : x = 0
    · rw [hx0]; exact M.zero_mem
    · have hsne : x.support.Nonempty := Finsupp.support_nonempty_iff.2 hx0
      refine key (x.support.max' hsne) x hx fun j hj => ?_
      by_contra hjx
      exact absurd (Finset.le_max' _ j (Finsupp.mem_support_iff.2 hjx)) (not_le.2 hj)
  have hspanN : ⊤ ≤ Submodule.span ℤ (Set.range v) := by
    rintro ⟨x, hx⟩ -
    have hxM := hspan x hx
    have : Submodule.map N.subtype (Submodule.span ℤ (Set.range v)) = M := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [← this] at hxM
    obtain ⟨y, hy, hyx⟩ := hxM
    have : y = ⟨x, hx⟩ := Subtype.ext hyx
    rwa [← this]
  exact Module.Free.of_basis (Module.Basis.mk hli hspanN)

end Core

/-- Morris, Topology Without Tears, Remark A5.5.15 (iii) (TP-548). Every subgroup (`ℤ`-submodule) of a
free abelian group, of any rank, is free. -/
@[kb "morris2024" "Remark A5.5.15, p. 545"]
theorem submodule_free_of_free {F : Type*} [AddCommGroup F] [Module.Free ℤ F] (N : Submodule ℤ F) :
    Module.Free ℤ N := by
  classical
  let ι := Module.Free.ChooseBasisIndex ℤ F
  let _ : LinearOrder ι := linearOrderOfSTO WellOrderingRel
  have _ : WellFoundedLT ι := ⟨fun a => WellOrderingRel.isWellOrder.wf.apply a⟩
  let e : F ≃ₗ[ℤ] (ι →₀ ℤ) := (Module.Free.chooseBasis ℤ F).repr
  have := submodule_finsupp_free (N.map e.toLinearMap)
  exact Module.Free.of_equiv (e.submoduleMap N).symm

/-- Subgroups of a free abelian group are free (additive-subgroup form). -/
theorem addSubgroup_free_of_free {F : Type*} [AddCommGroup F] [Module.Free ℤ F] (H : AddSubgroup F) :
    Module.Free ℤ H.toIntSubmodule :=
  submodule_free_of_free H.toIntSubmodule

/-! ### Theorem A5.5.16 for a free group of any rank (TP-548) -/

section Splitting

open Set Filter Module

variable {V F : Type*} [AddCommGroup V] [AddCommGroup F]

/-- A divisible abelian group (every element has an `n`-th root for every positive `n`) is `ℤ`-divisible
in Mathlib's sense. -/
theorem exists_int_smul_eq_of_divisible (hdiv : ∀ n : ℕ, 0 < n → ∀ v : V, ∃ w, n • w = v)
    (n : ℤ) (hn : n ≠ 0) (a : V) : ∃ w : V, n • w = a := by
  rcases lt_or_gt_of_ne hn with h | h
  · obtain ⟨w, hw⟩ := hdiv (-n).toNat (by omega) (-a)
    refine ⟨w, ?_⟩
    have : ((-n).toNat : ℤ) = -n := Int.toNat_of_nonneg (by omega)
    have h2 : (-n) • w = -a := by rw [← this, natCast_zsmul]; exact hw
    rw [neg_smul] at h2
    simpa using congrArg Neg.neg h2
  · obtain ⟨w, hw⟩ := hdiv n.toNat (by omega) a
    refine ⟨w, ?_⟩
    have : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (by omega)
    rw [← this, natCast_zsmul]; exact hw

/-- Algebraic core of Theorem A5.5.16: for `V` divisible and `F` free abelian, every
subgroup `G` of `V × F` contains `(θ f, f)` for each `f` in the projection of `G` to `F`, for some
homomorphism `θ : F →+ V`. -/
theorem exists_section_hom [Module.Free ℤ F]
    (hdiv : ∀ n : ℕ, 0 < n → ∀ v : V, ∃ w, n • w = v) (G : AddSubgroup (V × F)) :
    ∃ θ : F →+ V, ∀ g ∈ G, (θ g.2, g.2) ∈ G := by
  classical
  let _ : DivisibleBy V ℤ :=
    { div := fun a n => if h : n = 0 then 0 else Classical.choose (exists_int_smul_eq_of_divisible hdiv n h a)
      div_zero := fun a => by simp
      div_cancel := fun {n} a hn => by
        simp only [dif_neg hn]
        exact Classical.choose_spec (exists_int_smul_eq_of_divisible hdiv n hn a) }
  have hBaer : Module.Baer ℤ V := Module.Baer.of_divisible V
  let GM : Submodule ℤ (V × F) := AddSubgroup.toIntSubmodule G
  let π : GM →ₗ[ℤ] F := (LinearMap.snd ℤ V F) ∘ₗ GM.subtype
  let N : Submodule ℤ F := LinearMap.range π
  haveI hNfree : Module.Free ℤ N := submodule_free_of_free N
  let g1 : GM →ₗ[ℤ] N := π.rangeRestrict
  have hg1 : Function.Surjective g1 := LinearMap.surjective_rangeRestrict π
  obtain ⟨s, hs⟩ := Module.projective_lifting_property g1 LinearMap.id hg1
  let θ0 : N →ₗ[ℤ] V := (LinearMap.fst ℤ V F) ∘ₗ GM.subtype ∘ₗ s
  obtain ⟨θ, hθ⟩ := hBaer.extension_property N.subtype Subtype.val_injective θ0
  refine ⟨θ.toAddMonoidHom, fun g hg => ?_⟩
  have hn : g.2 ∈ N := ⟨⟨g, hg⟩, rfl⟩
  have key : ((s ⟨g.2, hn⟩ : GM) : V × F) = (θ g.2, g.2) := by
    have h1 : g1 (s ⟨g.2, hn⟩) = ⟨g.2, hn⟩ := by
      have := LinearMap.congr_fun hs ⟨g.2, hn⟩
      simpa using this
    have h2 : (((s ⟨g.2, hn⟩ : GM) : V × F)).2 = g.2 := congrArg Subtype.val h1
    have h3 : (((s ⟨g.2, hn⟩ : GM) : V × F)).1 = θ g.2 := by
      have := LinearMap.congr_fun hθ ⟨g.2, hn⟩
      exact this.symm
    exact Prod.ext h3 h2
  show (θ g.2, g.2) ∈ G
  rw [← key]
  exact (s ⟨g.2, hn⟩).2

variable [TopologicalSpace V] [IsTopologicalAddGroup V] [TopologicalSpace F] [DiscreteTopology F]

/-- Morris, Topology Without Tears, Theorem A5.5.16 (TP-548), for a free abelian group `F` of any rank.
Let `H = V × F` with `V` a divisible abelian topological group and `F` a discrete free abelian group, and
`G` a closed subgroup of `H`. Then there is a discrete subgroup `F'` of `H` isomorphic to `F` such that
`V × F' → H`, `(v, f') ↦ (v, 0) + f'` is a topological isomorphism (`H = V × F'`), and it maps
`(G ∩ V) × (G ∩ F')` onto `G`. -/
@[kb "morris2024" "Theorem A5.5.16, p. 546"]
theorem closedSubgroup_prod_divisible_free [Module.Free ℤ F]
    (hdiv : ∀ n : ℕ, 0 < n → ∀ v : V, ∃ w, n • w = v)
    (G : AddSubgroup (V × F)) (_hG : IsClosed (G : Set (V × F))) :
    ∃ F' : AddSubgroup (V × F), Nonempty (F ≃+ F') ∧ DiscreteTopology F' ∧
      ∃ e : (V × F') ≃ₜ+ (V × F), (∀ v (f : F'), e (v, f) = ((v, 0) : V × F) + (f : V × F)) ∧
        e '' {p | ((p.1, 0) : V × F) ∈ G ∧ (p.2 : V × F) ∈ G} = (G : Set (V × F)) := by
  obtain ⟨θ, hθ⟩ := exists_section_hom hdiv G
  let φ : F →+ V × F := AddMonoidHom.prod θ (AddMonoidHom.id F)
  have hinj : Function.Injective φ := fun a b h => congrArg Prod.snd h
  have hθc : Continuous θ := continuous_of_discreteTopology
  have hmem : ∀ x : φ.range, (x : V × F) = (θ (x : V × F).2, (x : V × F).2) := by
    rintro ⟨_, a, rfl⟩
    rfl
  refine ⟨φ.range, ⟨AddMonoidHom.ofInjective hinj⟩, ?_, ?_⟩
  · refine DiscreteTopology.of_continuous_injective (β := F) (f := fun x : φ.range => (x : V × F).2)
      (continuous_snd.comp continuous_subtype_val) ?_
    intro x y hxy
    refine Subtype.ext ?_
    rw [hmem x, hmem y]
    simp only at hxy
    rw [hxy]
  · let toFun : V × φ.range → V × F := fun p => ((p.1, 0) : V × F) + (p.2 : V × F)
    let invFun : V × F → V × φ.range := fun h =>
      (h.1 - θ h.2, ⟨(θ h.2, h.2), ⟨h.2, rfl⟩⟩)
    have hleft : ∀ p, invFun (toFun p) = p := by
      rintro ⟨v, x⟩
      have hx := hmem x
      refine Prod.ext ?_ (Subtype.ext ?_)
      · show v + (x : V × F).1 - θ (0 + (x : V × F).2) = v
        rw [zero_add, hx]; simp
      · show ((θ (0 + (x : V × F).2), 0 + (x : V × F).2) : V × F) = x
        rw [zero_add]
        exact (hmem x).symm
    have hright : ∀ h, toFun (invFun h) = h := by
      intro h
      refine Prod.ext ?_ ?_ <;> simp [toFun, invFun]
    let e : (V × φ.range) ≃ₜ+ (V × F) :=
      { toFun := toFun
        invFun := invFun
        left_inv := hleft
        right_inv := hright
        map_add' := fun p q => by
          refine Prod.ext ?_ ?_ <;> simp [toFun] <;> abel
        continuous_toFun :=
          (continuous_fst.prodMk continuous_const).add (continuous_subtype_val.comp continuous_snd)
        continuous_invFun := by
          refine (continuous_fst.sub (hθc.comp continuous_snd)).prodMk ?_
          exact Continuous.subtype_mk (((hθc.comp continuous_snd).prodMk continuous_snd)) _ }
    refine ⟨e, fun v f => rfl, ?_⟩
    ext g
    constructor
    · rintro ⟨⟨v, x⟩, ⟨hv, hx⟩, rfl⟩
      exact add_mem hv hx
    · intro hg
      have hc : (θ g.2, g.2) ∈ G := hθ g hg
      refine ⟨(g.1 - θ g.2, ⟨(θ g.2, g.2), ⟨g.2, rfl⟩⟩), ⟨?_, hc⟩, ?_⟩
      · have : ((g.1 - θ g.2, 0) : V × F) = g - (θ g.2, g.2) := by
          refine Prod.ext ?_ ?_ <;> simp
        show ((g.1 - θ g.2, 0) : V × F) ∈ G
        rw [this]
        exact sub_mem hg hc
      · exact hright g

end Splitting

end UndergradKB.Topology
