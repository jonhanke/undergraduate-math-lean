import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Projection
import UndergradKB.Topology.GroupsExtra
import UndergradKB.Common.Attr

/-!
# Closed subgroups of `ℝⁿ` (Morris, Topology Without Tears, Appendix 5.5)
-/

namespace UndergradKB.Topology

open Set

namespace ClosedSubgroupsRn

/-- Build a continuous additive isomorphism from an additive isomorphism continuous both ways. -/
def mkCAE {A B : Type*} [AddCommGroup A] [AddCommGroup B] [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃+ B) (h₁ : Continuous e) (h₂ : Continuous e.symm) : A ≃ₜ+ B :=
  { e with continuous_toFun := h₁, continuous_invFun := h₂ }

/-- Product of continuous additive isomorphisms. -/
def prodCAE {A A' B B' : Type*} [AddCommGroup A] [AddCommGroup A'] [AddCommGroup B]
    [AddCommGroup B'] [TopologicalSpace A] [TopologicalSpace A'] [TopologicalSpace B]
    [TopologicalSpace B'] (e₁ : A ≃ₜ+ A') (e₂ : B ≃ₜ+ B') : (A × B) ≃ₜ+ (A' × B') :=
  mkCAE (AddEquiv.prodCongr e₁.toAddEquiv e₂.toAddEquiv)
    (by
      change Continuous fun x : A × B => (e₁ x.1, e₂ x.2)
      exact (e₁.continuous.comp continuous_fst).prodMk (e₂.continuous.comp continuous_snd))
    (by
      change Continuous fun x : A' × B' => (e₁.symm x.1, e₂.symm x.2)
      exact (e₁.symm.continuous.comp continuous_fst).prodMk (e₂.symm.continuous.comp continuous_snd))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The largest real subspace contained in an additive subgroup `G` of a real vector space: the
vectors whose whole line lies in `G` (the union of all lines through `0` contained in `G`). -/
def maxSubspace (G : AddSubgroup E) : Submodule ℝ E where
  carrier := {v | ∀ t : ℝ, t • v ∈ G}
  zero_mem' := fun t => by simpa using G.zero_mem
  add_mem' := fun {a b} ha hb t => by simpa [smul_add] using G.add_mem (ha t) (hb t)
  smul_mem' := fun c v hv t => by simpa [smul_smul] using hv (t * c)

theorem maxSubspace_le (G : AddSubgroup E) {v : E} (hv : v ∈ maxSubspace G) : v ∈ G := by
  simpa using hv 1

/-- A closed subgroup `G` of a finite-dimensional real normed space splits as
`G = V ⊕ L`, with `V` the largest subspace inside `G` and `L = G ∩ C` a discrete subgroup of a
complement `C` of `V`; topologically `G ≃ V × L`. -/
theorem exists_splitting (G : AddSubgroup E) (hG : IsClosed (G : Set E)) :
    ∃ (V : Submodule ℝ E) (L : AddSubgroup E), DiscreteTopology L ∧
      (∀ g, g ∈ G ↔ ∃ v ∈ V, ∃ l ∈ L, g = v + l) ∧ Disjoint V (Submodule.span ℝ (L : Set E)) ∧
      Nonempty (G ≃ₜ+ (V × L)) := by
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
  have he : ∀ x : V × C, e x = (x.1 : E) + x.2 := fun x => by
    exact Submodule.coe_prodEquivOfIsCompl' V C hc x
  have key : ∀ g : E, ((e.symm g).1 : E) + ((e.symm g).2 : E) = g := fun g => by
    rw [← he]; exact e.apply_symm_apply g
  have hmemL : ∀ g : G, ((e.symm g).2 : E) ∈ L := by
    intro g
    refine ⟨?_, (e.symm g).2.2⟩
    have : ((e.symm g).2 : E) = (g : E) - (e.symm g).1 := eq_sub_of_add_eq' (key g)
    rw [this]
    exact G.sub_mem g.2 (maxSubspace_le G (e.symm g).1.2)
  have hmemG : ∀ (v : V) (l : L), (v : E) + l ∈ G := fun v l =>
    G.add_mem (maxSubspace_le G v.2) l.2.1
  have hdec : ∀ g, g ∈ G ↔ ∃ v ∈ V, ∃ l ∈ L, g = v + l := by
    intro g
    constructor
    · intro hg
      exact ⟨(e.symm g).1, (e.symm g).1.2, (e.symm g).2, hmemL ⟨g, hg⟩, (key g).symm⟩
    · rintro ⟨v, hv, l, hl, rfl⟩
      exact G.add_mem (maxSubspace_le G hv) hl.1
  have hind : Disjoint V (Submodule.span ℝ (L : Set E)) :=
    hc.disjoint.mono_right (Submodule.span_le.2 fun x hx => hx.2)
  refine ⟨V, L, hdisc, hdec, hind, ⟨?_⟩⟩
  refine mkCAE
    { toFun := fun g => ((e.symm g).1, ⟨(e.symm g).2, hmemL g⟩)
      invFun := fun p => ⟨(p.1 : E) + p.2, hmemG p.1 p.2⟩
      left_inv := fun g => Subtype.ext (key g)
      right_inv := fun p => by
        have h1 : e.symm ((p.1 : E) + p.2) = (p.1, ⟨p.2, p.2.2.2⟩) := by
          rw [ContinuousLinearEquiv.symm_apply_eq, he]
        refine Prod.ext ?_ (Subtype.ext ?_)
        · simp [h1]
        · simp [h1]
      map_add' := fun g h => by
        refine Prod.ext ?_ (Subtype.ext ?_)
        · simp
        · simp }
    ?_ ?_
  · show Continuous fun g : G => ((e.symm g).1, (⟨((e.symm g).2 : E), hmemL g⟩ : L))
    refine Continuous.prodMk (by fun_prop) (Continuous.subtype_mk ?_ _)
    exact continuous_subtype_val.comp (continuous_snd.comp
      (e.symm.continuous.comp continuous_subtype_val))
  · show Continuous fun p : V × L => (⟨(p.1 : E) + p.2, hmemG p.1 p.2⟩ : G)
    exact Continuous.subtype_mk (by fun_prop) _

/-- A finite-dimensional real vector space is topologically isomorphic, as a group, to `ℝ^p`. -/
noncomputable def subspaceCAE (V : Submodule ℝ E) :
    V ≃ₜ+ (Fin (Module.finrank ℝ V) → ℝ) :=
  mkCAE (Module.finBasis ℝ V).equivFun.toAddEquiv
    (LinearMap.continuous_of_finiteDimensional (Module.finBasis ℝ V).equivFun.toLinearMap)
    (LinearMap.continuous_of_finiteDimensional (Module.finBasis ℝ V).equivFun.symm.toLinearMap)

/-- A discrete subgroup of a finite-dimensional real normed space is topologically isomorphic to
`ℤ^q` (it is free abelian of finite rank). -/
theorem exists_discrete_subgroup_equiv (L : AddSubgroup E) [DiscreteTopology L] :
    ∃ q : ℕ, Nonempty (L ≃ₜ+ (Fin q → ℤ)) := by
  let L' : Submodule ℤ E := AddSubgroup.toIntSubmodule L
  have : DiscreteTopology L' := inferInstanceAs (DiscreteTopology L)
  let b := Module.Free.chooseBasis ℤ L'
  let n := Fintype.card (Module.Free.ChooseBasisIndex ℤ L')
  let e : L' ≃ₗ[ℤ] (Fin n → ℤ) :=
    b.equivFun.trans (LinearEquiv.funCongrLeft ℤ ℤ (Fintype.equivFin _).symm)
  let f : L ≃+ (Fin n → ℤ) :=
    { toFun := fun x => e ⟨x.1, x.2⟩
      invFun := fun y => ⟨(e.symm y).1, (e.symm y).2⟩
      left_inv := fun x => by simp
      right_inv := fun y => e.apply_symm_apply y
      map_add' := fun x y => by
        have := e.map_add ⟨x.1, x.2⟩ ⟨y.1, y.2⟩
        exact this }
  exact ⟨n, ⟨mkCAE f continuous_of_discreteTopology continuous_of_discreteTopology⟩⟩

/-- Morris, Topology Without Tears, Theorem A5.5.12 / A5.5.13 (TP-547), first half. A closed subgroup
`G` of a finite-dimensional real normed space (in particular of `ℝⁿ`) is topologically isomorphic
to `ℝ^p × ℤ^q`. -/
@[kb "morris2024" "Theorem A5.5.13, p. 544"]
theorem closed_subgroup_equiv_real_pi_prod_int_pi (G : AddSubgroup E) (hG : IsClosed (G : Set E)) :
    ∃ p q : ℕ, Nonempty (G ≃ₜ+ ((Fin p → ℝ) × (Fin q → ℤ))) := by
  obtain ⟨V, L, hL, -, -, ⟨e⟩⟩ := exists_splitting G hG
  obtain ⟨q, ⟨f⟩⟩ := exists_discrete_subgroup_equiv L
  exact ⟨_, q, ⟨e.trans (prodCAE (subspaceCAE V) f)⟩⟩

/-- A discrete subgroup `L` of a finite-dimensional real normed space has a `ℤ`-basis `b`, which is
linearly independent over `ℝ`: `L = {∑ nⱼ bⱼ | n : Fin q → ℤ}`. -/
theorem exists_lattice_basis (L : AddSubgroup E) [DiscreteTopology L] :
    ∃ (q : ℕ) (b : Fin q → E), LinearIndependent ℝ b ∧
      ∀ x, x ∈ L ↔ ∃ n : Fin q → ℤ, x = ∑ j, n j • b j := by
  let L' : Submodule ℤ E := AddSubgroup.toIntSubmodule L
  have : DiscreteTopology L' := inferInstanceAs (DiscreteTopology L)
  let bb := Module.Free.chooseBasis ℤ L'
  let q := Fintype.card (Module.Free.ChooseBasisIndex ℤ L')
  let bq : Module.Basis (Fin q) ℤ L' := bb.reindex (Fintype.equivFin _)
  let b : Fin q → E := fun j => (bq j : E)
  have hmem : ∀ x, x ∈ L ↔ ∃ n : Fin q → ℤ, x = ∑ j, n j • b j := by
    intro x
    constructor
    · intro hx
      refine ⟨fun j => bq.repr ⟨x, hx⟩ j, ?_⟩
      have h2 : x = ((∑ j, bq.repr ⟨x, hx⟩ j • bq j : L') : E) := by rw [bq.sum_repr]
      refine h2.trans ?_
      simp only [Submodule.coe_sum, Submodule.coe_smul, b]
    · rintro ⟨n, rfl⟩
      exact L.sum_mem fun j _ => L.zsmul_mem (bq j).2 _
  refine ⟨q, b, ?_, hmem⟩
  have hspan : Submodule.span ℤ (Set.range b) = L' := by
    apply le_antisymm
    · exact Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact (bq j).2)
    · intro x hx
      obtain ⟨n, rfl⟩ := (hmem x).1 hx
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hdisc : DiscreteTopology (Submodule.span ℤ (Set.range b)) := by
    rw [hspan]; exact this
  have h1 := Real.finrank_eq_int_finrank_of_discrete hdisc
  rw [linearIndependent_iff_card_eq_finrank_span]
  have h2 : Set.finrank ℤ (Set.range b) = q := by
    unfold Set.finrank
    rw [hspan]
    exact (Module.finrank_eq_card_basis bq).trans (Fintype.card_fin q)
  rw [Fintype.card_fin]
  exact (h2.symm.trans h1.symm)

section Model

/-- The model map `ℝ^((A ⊕ B) ⊕ S) → ℝ^S × (ℝ/ℤ)^B`: forget the `A`-coordinates, reduce the
`B`-coordinates modulo `1`, keep the `S`-coordinates. -/
noncomputable def modelMap (A B S : Type*) [Fintype A] [Fintype B] [Fintype S] :
    (((A ⊕ B) ⊕ S) → ℝ) →+ (S → ℝ) × (B → AddCircle (1 : ℝ)) where
  toFun y := (fun s => y (Sum.inr s), fun j => ((y (Sum.inl (Sum.inr j)) : ℝ) : AddCircle (1 : ℝ)))
  map_zero' := by ext <;> simp
  map_add' x y := by
    ext
    · simp
    · simp

variable (A B S : Type*) [Fintype A] [Fintype B] [Fintype S]

theorem continuous_modelMap : Continuous (modelMap A B S) := by
  refine Continuous.prodMk (by fun_prop) (continuous_pi fun j => ?_)
  exact (continuous_quotient_mk'.comp (continuous_apply _))

theorem surjective_modelMap : Function.Surjective (modelMap A B S) := by
  rintro ⟨s, t⟩
  have h : ∀ j, ∃ r : ℝ, ((r : ℝ) : AddCircle (1 : ℝ)) = t j := fun j =>
    QuotientAddGroup.mk_surjective (t j)
  choose u hu using h
  refine ⟨Sum.elim (Sum.elim (fun _ => 0) u) s, ?_⟩
  ext
  · simp [modelMap]
  · simp [modelMap, hu]

theorem isOpenMap_modelMap : IsOpenMap (modelMap A B S) := by
  let π : (((A ⊕ B) ⊕ S) → ℝ) →ₗ[ℝ] (B → ℝ) × (S → ℝ) :=
    LinearMap.prod (LinearMap.funLeft ℝ ℝ (fun j : B => Sum.inl (Sum.inr j)))
      (LinearMap.funLeft ℝ ℝ (fun s : S => Sum.inr s))
  have hπ : Function.Surjective π := by
    rintro ⟨u, w⟩
    exact ⟨Sum.elim (Sum.elim (fun _ => 0) u) w, by ext <;> simp [π]⟩
  have h1 : IsOpenMap π := LinearMap.isOpenMap_of_finiteDimensional π hπ
  have h2 : IsOpenMap (fun p : (B → ℝ) × (S → ℝ) => (p.2, Pi.map (fun _ => ((↑) : ℝ → AddCircle (1 : ℝ))) p.1)) := by
    have h3 : IsOpenMap (Prod.map (Pi.map fun _ : B => ((↑) : ℝ → AddCircle (1 : ℝ))) (id : (S → ℝ) → (S → ℝ))) :=
      (IsOpenMap.piMap (fun _ => QuotientAddGroup.isOpenMap_coe)
        (Filter.Eventually.of_forall fun _ => QuotientAddGroup.mk_surjective)).prodMap IsOpenMap.id
    exact (Homeomorph.prodComm _ _).isOpenMap.comp h3
  exact h2.comp h1

theorem modelMap_eq_zero_iff (y : ((A ⊕ B) ⊕ S) → ℝ) :
    modelMap A B S y = 0 ↔ (∀ s, y (Sum.inr s) = 0) ∧ ∀ j, ∃ n : ℤ, y (Sum.inl (Sum.inr j)) = n := by
  constructor
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    refine ⟨fun s => congrFun h1 s, fun j => ?_⟩
    have := congrFun h2 j
    simp only [modelMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply] at this
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).1 this
    exact ⟨n, by simpa using hn.symm⟩
  · rintro ⟨h1, h2⟩
    ext
    · exact h1 _
    · obtain ⟨n, hn⟩ := h2 ‹_›
      simp only [modelMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply]
      exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).2 ⟨n, by simpa using hn.symm⟩

end Model

/-- If `φ : E → T` is a continuous open surjective homomorphism of abelian topological groups with
kernel `G`, then `E ⧸ G` is topologically isomorphic to `T`. -/
theorem quotient_equiv {E T : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [AddCommGroup T] [TopologicalSpace T] (G : AddSubgroup E) (φ : E →+ T) (hc : Continuous φ)
    (ho : IsOpenMap φ) (hs : Function.Surjective φ) (hker : ∀ x, x ∈ G ↔ φ x = 0) :
    Nonempty ((E ⧸ G) ≃ₜ+ T) := by
  let Q : (E ⧸ G) →+ T := QuotientAddGroup.lift G φ (fun x hx => (hker x).1 hx)
  have hQ : ∀ x, Q (QuotientAddGroup.mk x) = φ x := fun x => QuotientAddGroup.lift_mk G _ x
  have hinj : Function.Injective Q := by
    rw [injective_iff_map_eq_zero]
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      intro h
      rw [hQ] at h
      exact (QuotientAddGroup.eq_zero_iff x).2 ((hker x).2 h)
  have hsurj : Function.Surjective Q := by
    intro t
    obtain ⟨x, rfl⟩ := hs t
    exact ⟨QuotientAddGroup.mk x, hQ x⟩
  have hcont : Continuous Q := by
    rw [(QuotientAddGroup.isQuotientMap_mk G).continuous_iff]
    have : (Q ∘ (QuotientAddGroup.mk : E → E ⧸ G)) = φ := funext hQ
    rw [this]; exact hc
  have hopen : IsOpenMap Q := by
    intro U hU
    have : Q '' U = φ '' ((QuotientAddGroup.mk : E → E ⧸ G) ⁻¹' U) := by
      ext t
      constructor
      · rintro ⟨q, hq, rfl⟩
        obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
        exact ⟨x, hq, (hQ x).symm⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨QuotientAddGroup.mk x, hx, hQ x⟩
    rw [this]
    exact ho _ (hU.preimage QuotientAddGroup.continuous_mk)
  let f : (E ⧸ G) ≃+ T := AddEquiv.ofBijective Q ⟨hinj, hsurj⟩
  let e : (E ⧸ G) ≃ₜ T := Equiv.toHomeomorphOfContinuousOpen f.toEquiv hcont hopen
  exact ⟨mkCAE f hcont e.symm.continuous⟩

/-- Morris, Topology Without Tears, Theorem A5.5.13 (TP-547), second half. For a closed subgroup `G`
of a finite-dimensional real normed space `E` (in particular `ℝⁿ`), the quotient group `E ⧸ G` is
topologically isomorphic to `ℝ^c × T^d`. -/
@[kb "morris2024" "Theorem A5.5.13, p. 544"]
theorem quotient_closed_subgroup_equiv (G : AddSubgroup E) (hG : IsClosed (G : Set E)) :
    ∃ c d : ℕ, Nonempty ((E ⧸ G) ≃ₜ+ ((Fin c → ℝ) × (Fin d → AddCircle (1 : ℝ)))) := by
  classical
  obtain ⟨V, L, hL, hdec, hind, -⟩ := exists_splitting G hG
  obtain ⟨q, b, hb, hLmem⟩ := exists_lattice_basis L
  let bV := Module.finBasis ℝ V
  let p := Module.finrank ℝ V
  have hbL : ∀ j, b j ∈ L := fun j =>
    (hLmem (b j)).2 ⟨Pi.single j 1, by simp [Pi.single_apply]⟩
  let f : Fin p ⊕ Fin q → E := Sum.elim (fun i => (bV i : E)) b
  have hf : LinearIndependent ℝ f := by
    refine LinearIndependent.sum_type ?_ hb ?_
    · exact bV.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
    · refine hind.mono ?_ ?_
      · exact Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact (bV i).2)
      · exact Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact hbL j)
  let B := Module.Basis.sumExtend hf
  have hB : ∀ k, B (Sum.inl k) = f k := fun k => by
    simp only [B, Module.Basis.sumExtend, Module.Basis.reindex_apply, Equiv.symm_symm,
      Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.Set.sumDiffSubset_apply_inl,
      Equiv.ofInjective_apply, Module.Basis.coe_extend]
    rfl
  have hB1 : ∀ i, B (Sum.inl (Sum.inl i)) = (bV i : E) := fun i => hB (Sum.inl i)
  have hB2 : ∀ j, B (Sum.inl (Sum.inr j)) = b j := fun j => hB (Sum.inr j)
  have hfin : Finite ((Fin p ⊕ Fin q) ⊕ Module.Basis.sumExtendIndex hf) :=
    Module.Finite.finite_basis B
  have hfinS : Finite (Module.Basis.sumExtendIndex hf) :=
    Finite.of_injective (Sum.inr : _ → (Fin p ⊕ Fin q) ⊕ Module.Basis.sumExtendIndex hf)
      Sum.inr_injective
  let _ := Fintype.ofFinite (Module.Basis.sumExtendIndex hf)
  let φ : E →+ (Module.Basis.sumExtendIndex hf → ℝ) × (Fin q → AddCircle (1 : ℝ)) :=
    (modelMap (Fin p) (Fin q) (Module.Basis.sumExtendIndex hf)).comp
      B.equivFun.toLinearMap.toAddMonoidHom
  have hrep : ∀ m k, B.repr (B m) k = if m = k then 1 else 0 := by
    intro m k
    simp [Module.Basis.repr_self, Finsupp.single_apply]
  have hker : ∀ x, x ∈ G ↔ φ x = 0 := by
    intro x
    change x ∈ G ↔ modelMap (Fin p) (Fin q) _ (B.equivFun x) = 0
    rw [modelMap_eq_zero_iff]
    simp only [Module.Basis.equivFun_apply]
    constructor
    · intro hx
      obtain ⟨v, hv, l, hl, rfl⟩ := (hdec x).1 hx
      obtain ⟨n, hn⟩ := (hLmem l).1 hl
      have hvs : v = ∑ i, bV.repr ⟨v, hv⟩ i • B (Sum.inl (Sum.inl i)) := by
        have := congrArg (fun y : V => (y : E)) (bV.sum_repr ⟨v, hv⟩)
        simp only [Submodule.coe_sum, Submodule.coe_smul] at this
        simp only [hB1]
        exact this.symm
      have hls : l = ∑ j, n j • B (Sum.inl (Sum.inr j)) := by simp only [hB2]; exact hn
      refine ⟨fun s => ?_, fun j => ⟨n j, ?_⟩⟩
      · rw [map_add, hvs, hls]
        simp [map_sum, hrep]
      · rw [map_add, hvs, hls]
        simp [map_sum, Finsupp.single_apply]
    · rintro ⟨h1, h2⟩
      choose n hn using h2
      have hx := B.sum_repr x
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at hx
      have h3 : ∑ s, B.repr x (Sum.inr s) • B (Sum.inr s) = 0 := by simp [h1]
      rw [h3, add_zero] at hx
      rw [hdec]
      refine ⟨∑ i, B.repr x (Sum.inl (Sum.inl i)) • B (Sum.inl (Sum.inl i)), ?_,
        ∑ j, B.repr x (Sum.inl (Sum.inr j)) • B (Sum.inl (Sum.inr j)), ?_, hx.symm⟩
      · exact V.sum_mem fun i _ => V.smul_mem _ (by rw [hB1]; exact (bV i).2)
      · rw [hLmem]
        refine ⟨n, ?_⟩
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hn j, Int.cast_smul_eq_zsmul, hB2]
  have hcont : Continuous φ :=
    (continuous_modelMap _ _ _).comp (LinearMap.continuous_of_finiteDimensional _)
  have hopen : IsOpenMap φ :=
    (isOpenMap_modelMap _ _ _).comp (LinearMap.isOpenMap_of_finiteDimensional _ B.equivFun.surjective)
  have hsurj : Function.Surjective φ := (surjective_modelMap _ _ _).comp B.equivFun.surjective
  obtain ⟨Φ⟩ := quotient_equiv G φ hcont hopen hsurj hker
  let c := Fintype.card (Module.Basis.sumExtendIndex hf)
  let eS : (Module.Basis.sumExtendIndex hf → ℝ) ≃ₗ[ℝ] (Fin c → ℝ) :=
    LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin (Module.Basis.sumExtendIndex hf)).symm
  let Ψ : (Module.Basis.sumExtendIndex hf → ℝ) ≃ₜ+ (Fin c → ℝ) :=
    mkCAE eS.toAddEquiv (LinearMap.continuous_of_finiteDimensional eS.toLinearMap)
      (LinearMap.continuous_of_finiteDimensional eS.symm.toLinearMap)
  exact ⟨c, q, ⟨Φ.trans (prodCAE Ψ (ContinuousAddEquiv.refl _))⟩⟩

end ClosedSubgroupsRn

end UndergradKB.Topology
