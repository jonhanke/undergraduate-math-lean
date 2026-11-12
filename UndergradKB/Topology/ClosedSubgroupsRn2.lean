import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Homeomorph.Defs
import UndergradKB.Topology.ClosedSubgroupsRn
import UndergradKB.Common.Attr

/-!
# Closed subgroups of tori (Morris, Topology Without Tears, Appendix 5.5)
-/

namespace UndergradKB.Topology

open Set ClosedSubgroupsRn

namespace ClosedSubgroupsRn2

/-- A group in which every element is divisible by every nonzero integer is `DivisibleBy ℤ`. -/
noncomputable def divisibleByOfExists {A : Type*} [AddCommGroup A]
    (h : ∀ (a : A) (k : ℤ), k ≠ 0 → ∃ b : A, k • b = a) : DivisibleBy A ℤ where
  div a k := if hk : k = 0 then 0 else Classical.choose (h a k hk)
  div_zero a := by simp
  div_cancel {k} a hk := by
    simp only [hk, dite_false]
    exact Classical.choose_spec (h a k hk)

/-- A compact Hausdorff abelian topological group with a closed divisible subgroup of finite index
splits topologically: `X ≃ₜ+ A × F` with `F` a finite subgroup (injectivity of divisible groups). -/
theorem splitting_of_divisible {X : Type*} [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [T2Space X] [CompactSpace X] (A : AddSubgroup X)
    (hA : IsClosed (A : Set X)) [DivisibleBy A ℤ] [Finite (X ⧸ A)] :
    ∃ F : AddSubgroup X, Finite F ∧ Nonempty (X ≃ₜ+ (A × F)) := by
  haveI : Module.Baer ℤ A := Module.Baer.of_divisible A
  obtain ⟨r, hr⟩ := Module.Baer.extension_property_addMonoidHom (Q := A) this A.subtype
    Subtype.val_injective (AddMonoidHom.id A)
  have hrA : ∀ a : A, r (a : X) = a := fun a => by
    have := DFunLike.congr_fun hr a
    simpa using this
  let F : AddSubgroup X := r.ker
  have hFA : ∀ x : X, x ∈ A → x ∈ F → x = 0 := by
    intro x hxA hxF
    have h1 := hrA ⟨x, hxA⟩
    rw [AddMonoidHom.mem_ker.1 hxF] at h1
    exact (congrArg Subtype.val h1.symm).trans rfl
  have hfin : Finite F := by
    refine Finite.of_injective (fun f : F => (QuotientAddGroup.mk (f : X) : X ⧸ A)) ?_
    intro f f' h
    have h2 : -(f : X) + f' ∈ A := QuotientAddGroup.eq.1 h
    have h3 : -(f : X) + f' ∈ F := F.add_mem (F.neg_mem f.2) f'.2
    have := hFA _ h2 h3
    exact Subtype.ext (neg_add_eq_zero.1 this)
  have hcomp : CompactSpace (A × F) := by
    haveI : CompactSpace A := isCompact_iff_compactSpace.1 hA.isCompact
    infer_instance
  let e : X ≃+ (A × F) :=
    { toFun := fun x => (r x, ⟨x - r x, by
        rw [AddMonoidHom.mem_ker, map_sub, hrA]; simp⟩)
      invFun := fun p => (p.1 : X) + p.2
      left_inv := fun x => by simp
      right_inv := fun p => by
        have h1 : r ((p.1 : X) + p.2) = p.1 := by
          rw [map_add, hrA, AddMonoidHom.mem_ker.1 p.2.2, add_zero]
        refine Prod.ext (by simpa using h1) (Subtype.ext ?_)
        simp [h1]
      map_add' := fun x y => by
        refine Prod.ext (by simp) (Subtype.ext ?_)
        simp only [map_add, AddSubgroup.coe_add, Prod.snd_add]
        abel }
  have hcont : Continuous e.symm := by
    show Continuous fun p : A × F => (p.1 : X) + p.2
    fun_prop
  let h : (A × F) ≃ₜ X := hcont.homeoOfEquivCompactToT2 (f := e.symm.toEquiv)
  exact ⟨F, hfin, ⟨mkCAE e (h.symm.continuous) hcont⟩⟩

section OpenSubspace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- For a closed subgroup `G` of a finite-dimensional real normed space, the largest subspace
inside `G` is an open subset of `G`: it is the trace on `G` of an open set of `E`. -/
theorem exists_open_subspace (G : AddSubgroup E) (hG : IsClosed (G : Set E)) :
    ∃ V : Submodule ℝ E, (∀ v ∈ V, v ∈ G) ∧
      ∃ O : Set E, IsOpen O ∧ ∀ g ∈ G, (g ∈ O ↔ g ∈ V) := by
  obtain ⟨C, hc⟩ := Submodule.exists_isCompl (maxSubspace G)
  set V := maxSubspace G with hV
  let L : AddSubgroup E := G ⊓ C.toAddSubgroup
  have hCcl : IsClosed (C : Set E) := Submodule.closed_of_finiteDimensional C
  have hLcl : IsClosed (L : Set E) := hG.inter hCcl
  have hdisc : DiscreteTopology L := by
    by_contra hnd
    obtain ⟨a, ha, hline⟩ := exists_line_of_closed_not_discrete L hLcl hnd
    have haV : a ∈ V := fun t => (hline t).1
    have haC : a ∈ C := by simpa using (hline 1).2
    exact ha (by simpa using hc.disjoint.le_bot ⟨haV, haC⟩)
  let e : (V × C) ≃L[ℝ] E := (Submodule.prodEquivOfIsCompl V C hc).toContinuousLinearEquiv
  have he : ∀ x : V × C, e x = (x.1 : E) + x.2 := fun x =>
    Submodule.coe_prodEquivOfIsCompl' V C hc x
  have key : ∀ g : E, ((e.symm g).1 : E) + ((e.symm g).2 : E) = g := fun g => by
    rw [← he]; exact e.apply_symm_apply g
  have hmemL : ∀ g ∈ G, ((e.symm g).2 : E) ∈ L := by
    intro g hg
    refine ⟨?_, (e.symm g).2.2⟩
    have : ((e.symm g).2 : E) = g - (e.symm g).1 := eq_sub_of_add_eq' (key g)
    rw [this]
    exact G.sub_mem hg (maxSubspace_le G (e.symm g).1.2)
  obtain ⟨W, hW, hWeq⟩ := isOpen_induced_iff.1 (isOpen_discrete ({0} : Set L))
  refine ⟨V, fun v hv => maxSubspace_le G hv,
    {x | ((e.symm x).2 : E) ∈ W}, ?_, ?_⟩
  · exact hW.preimage (continuous_subtype_val.comp (continuous_snd.comp e.symm.continuous))
  · intro g hg
    constructor
    · intro hgO
      have h1 : (⟨(e.symm g).2, hmemL g hg⟩ : L) ∈ Subtype.val ⁻¹' W := hgO
      rw [hWeq] at h1
      have h2 : ((e.symm g).2 : E) = 0 := congrArg Subtype.val (mem_singleton_iff.1 h1)
      have h3 := key g
      rw [h2, add_zero] at h3
      rw [← h3]
      exact (e.symm g).1.2
    · intro hgV
      have h1 : e.symm g = (⟨g, hgV⟩, 0) := by
        rw [ContinuousLinearEquiv.symm_apply_eq, he]; simp
      have h0 : (0 : E) ∈ W := by
        have : (0 : L) ∈ Subtype.val ⁻¹' W := by rw [hWeq]; exact mem_singleton _
        exact this
      show ((e.symm g).2 : E) ∈ W
      rw [h1]
      exact h0

end OpenSubspace

section Torus

/-- The coordinatewise quotient map `ℝⁿ → (ℝ/ℤ)ⁿ`. -/
noncomputable def expMap (n : ℕ) : (Fin n → ℝ) →+ (Fin n → AddCircle (1 : ℝ)) where
  toFun x i := ((x i : ℝ) : AddCircle (1 : ℝ))
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

theorem continuous_expMap (n : ℕ) : Continuous (expMap n) :=
  continuous_pi fun i => continuous_quotient_mk'.comp (continuous_apply i)

theorem isOpenMap_expMap (n : ℕ) : IsOpenMap (expMap n) :=
  show IsOpenMap (Pi.map fun _ : Fin n => ((↑) : ℝ → AddCircle (1 : ℝ))) from
    IsOpenMap.piMap (fun _ => QuotientAddGroup.isOpenMap_coe)
      (Filter.Eventually.of_forall fun _ => QuotientAddGroup.mk_surjective)

/-- Morris, Topology Without Tears, Corollary A5.5.20 (TP-550). A closed subgroup `H` of the torus
`Tⁿ = (ℝ/ℤ)ⁿ` is topologically isomorphic to `Tᵃ × F` with `F` a finite subgroup of `H`. -/
@[kb "morris2024" "Corollary A5.5.20, p. 548"]
theorem closed_subgroup_torus_equiv {n : ℕ} (H : AddSubgroup (Fin n → AddCircle (1 : ℝ)))
    (hH : IsClosed (H : Set (Fin n → AddCircle (1 : ℝ)))) :
    ∃ (a : ℕ) (F : AddSubgroup H), Finite F ∧
      Nonempty (H ≃ₜ+ ((Fin a → AddCircle (1 : ℝ)) × F)) := by
  classical
  let π := expMap n
  let G' : AddSubgroup (Fin n → ℝ) := H.comap π
  have hG' : IsClosed (G' : Set (Fin n → ℝ)) := hH.preimage (continuous_expMap n)
  obtain ⟨V, hVG, O, hO, hOV⟩ := exists_open_subspace G' hG'
  let A : AddSubgroup (Fin n → AddCircle (1 : ℝ)) := V.toAddSubgroup.map π
  have hAH : ∀ y ∈ A, y ∈ H := by
    rintro _ ⟨v, hv, rfl⟩; exact hVG v hv
  have hAeq : ∀ y, y ∈ A ↔ y ∈ H ∧ y ∈ π '' O := by
    intro y
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨hVG v hv, v, (hOV v (hVG v hv)).2 hv, rfl⟩
    · rintro ⟨hyH, o, ho, rfl⟩
      exact ⟨o, (hOV o hyH).1 ho, rfl⟩
  have : CompactSpace H := isCompact_iff_compactSpace.1 hH.isCompact
  let AH : AddSubgroup H := A.addSubgroupOf H
  have hAHopen : IsOpen (AH : Set H) := by
    have : (AH : Set H) = Subtype.val ⁻¹' (π '' O) := by
      ext h
      show h.1 ∈ A ↔ h.1 ∈ π '' O
      rw [hAeq]
      exact ⟨fun h' => h'.2, fun h' => ⟨h.2, h'⟩⟩
    rw [this]
    exact ((isOpenMap_expMap n) O hO).preimage continuous_subtype_val
  have hAHclosed : IsClosed (AH : Set H) := AddSubgroup.isClosed_of_isOpen AH hAHopen
  have : Finite (H ⧸ AH) := AddSubgroup.quotient_finite_of_isOpen AH hAHopen
  have : DivisibleBy AH ℤ := divisibleByOfExists fun a k hk => by
    have ha : ((a : H) : Fin n → AddCircle (1 : ℝ)) ∈ A := a.2
    obtain ⟨v, hv, hvπ⟩ := ha
    have hw : ((1 / (k : ℝ)) • v) ∈ V := V.smul_mem _ hv
    have hwA : π ((1 / (k : ℝ)) • v) ∈ A := ⟨_, hw, rfl⟩
    refine ⟨⟨⟨π ((1 / (k : ℝ)) • v), hAH _ hwA⟩, hwA⟩, ?_⟩
    refine Subtype.ext (Subtype.ext ?_)
    show k • π ((1 / (k : ℝ)) • v) = ((a : H) : Fin n → AddCircle (1 : ℝ))
    rw [← hvπ, ← map_zsmul, ← Int.cast_smul_eq_zsmul ℝ, smul_smul]
    have : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    simp [this]
  obtain ⟨F, hFfin, ⟨e1⟩⟩ := splitting_of_divisible AH hAHclosed
  -- AH is topologically isomorphic to `A`
  let Aeq : AH ≃ₜ+ A :=
    mkCAE
      { toFun := fun x => ⟨x.1.1, x.2⟩
        invFun := fun a => ⟨⟨a.1, hAH a.1 a.2⟩, a.2⟩
        left_inv := fun x => rfl
        right_inv := fun a => rfl
        map_add' := fun x y => rfl }
      (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _)
      (Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _)
  -- the surjection `V → A`
  let φ : V →+ A :=
    { toFun := fun v => ⟨π v, ⟨v, v.2, rfl⟩⟩
      map_zero' := Subtype.ext (by show π ((0 : V) : Fin n → ℝ) = 0; simp)
      map_add' := fun x y => Subtype.ext (by
        show π (((x + y : V)) : Fin n → ℝ) = π (x : Fin n → ℝ) + π (y : Fin n → ℝ)
        simp) }
  have hφcont : Continuous φ :=
    Continuous.subtype_mk ((continuous_expMap n).comp continuous_subtype_val) _
  have hφsurj : Function.Surjective φ := by
    rintro ⟨a, ⟨v, hv, hvπ⟩⟩
    exact ⟨⟨v, hv⟩, Subtype.ext hvπ⟩
  have hφopen : IsOpenMap φ := by
    intro U hU
    obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.1 hU
    have : φ '' (Subtype.val ⁻¹' W) = Subtype.val ⁻¹' (π '' (O ∩ W)) := by
      ext a
      constructor
      · rintro ⟨v, hvW, rfl⟩
        exact ⟨v, ⟨(hOV v (hVG v v.2)).2 v.2, hvW⟩, rfl⟩
      · rintro ⟨o, ⟨hoO, hoW⟩, hoa⟩
        have hoH : π o ∈ H := hoa ▸ hAH a.1 a.2
        have hoV : o ∈ V := (hOV o hoH).1 hoO
        exact ⟨⟨o, hoV⟩, hoW, Subtype.ext hoa⟩
    rw [this]
    exact ((isOpenMap_expMap n) _ (hO.inter hW)).preimage continuous_subtype_val
  let Λ : AddSubgroup V := φ.ker
  have hΛ : IsClosed (Λ : Set V) := by
    have : (Λ : Set V) = φ ⁻¹' {0} := by
      ext x; simp [Λ, AddMonoidHom.mem_ker]
    rw [this]
    exact isClosed_singleton.preimage hφcont
  obtain ⟨Q⟩ := quotient_equiv Λ φ hφcont hφopen hφsurj (fun x => AddMonoidHom.mem_ker)
  obtain ⟨c, d, ⟨R⟩⟩ := quotient_closed_subgroup_equiv Λ hΛ
  let S : A ≃ₜ+ ((Fin c → ℝ) × (Fin d → AddCircle (1 : ℝ))) := Q.symm.trans R
  have : CompactSpace AH := isCompact_iff_compactSpace.1 hAHclosed.isCompact
  have : CompactSpace A := Function.Surjective.compactSpace Aeq.continuous Aeq.surjective
  have : CompactSpace ((Fin c → ℝ) × (Fin d → AddCircle (1 : ℝ))) :=
    Function.Surjective.compactSpace S.continuous S.surjective
  have : CompactSpace (Fin c → ℝ) :=
    Function.Surjective.compactSpace (continuous_fst (X := Fin c → ℝ) (Y := Fin d → AddCircle (1 : ℝ)))
      (fun x => ⟨(x, 0), rfl⟩)
  have hc : c = 0 := by
    by_contra hne
    have i : Fin c := ⟨0, Nat.pos_of_ne_zero hne⟩
    have : CompactSpace ℝ := Function.Surjective.compactSpace (continuous_apply i)
      (fun r => ⟨fun _ => r, rfl⟩)
    exact (NoncompactSpace.noncompact_univ (X := ℝ)) isCompact_univ
  subst hc
  let drop : ((Fin 0 → ℝ) × (Fin d → AddCircle (1 : ℝ))) ≃ₜ+ (Fin d → AddCircle (1 : ℝ)) :=
    mkCAE
      { toFun := fun p => p.2
        invFun := fun y => (0, y)
        left_inv := fun p => Prod.ext (Subsingleton.elim _ _) rfl
        right_inv := fun y => rfl
        map_add' := fun _ _ => rfl }
      continuous_snd (continuous_const.prodMk continuous_id)
  exact ⟨d, F, hFfin, ⟨e1.trans (prodCAE (Aeq.trans (S.trans drop)) (ContinuousAddEquiv.refl _))⟩⟩

end Torus

end ClosedSubgroupsRn2

end UndergradKB.Topology
