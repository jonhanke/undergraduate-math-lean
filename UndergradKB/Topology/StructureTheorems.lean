import UndergradKB.Topology.DualityTheorem
import UndergradKB.Topology.StructureWave2c
import UndergradKB.Topology.DualityPlumbing
import UndergradKB.Topology.DualityDiscrete3
import UndergradKB.Topology.ClassicalDuals
import UndergradKB.Topology.GroupsExtra
import UndergradKB.Topology.GroupsWave2
import UndergradKB.Common.Attr

/-!
# Structure of compactly generated LCA groups (Morris, Theorem A5.13.7)

Following the book: Proposition A5.12.10 gives a compact subgroup `K₀` with
`G / K₀ ≅ ℝᵃ × Tᶜ × ℤᵇ × F`; by Proposition A5.13.2 the dual of `G / K₀` is an open subgroup of `G^`,
which therefore has an open divisible subgroup `ℝᵃ × Tᵇ`; this splits off (Proposition A5.3.8), so
`G^ ≅ ℝᵃ × Tᵇ × D` with `D` discrete, and duality gives `G ≅ ℝᵃ × ℤᵇ × D^`.
-/

open Set Topology

set_option linter.unusedSectionVars false

universe u

namespace UndergradKB.Topology

section Helpers

/-- Reorder `((A × B) × C) × D` to `(A × C) × (B × D)`. -/
def reorder4 (A B C D : Type*) [CommGroup A] [CommGroup B] [CommGroup C] [CommGroup D]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D] :
    (((A × B) × C) × D) ≃ₜ* ((A × C) × (B × D)) where
  toFun p := ((p.1.1.1, p.1.2), (p.1.1.2, p.2))
  invFun q := (((q.1.1, q.2.1), q.1.2), q.2.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- `x ↦ (x, 1)` into a product with a discrete factor is an open embedding. -/
theorem isOpenEmbedding_mk_one {X D : Type*} [TopologicalSpace X] [TopologicalSpace D]
    [DiscreteTopology D] [One D] : IsOpenEmbedding (fun x : X => (x, (1 : D))) := by
  refine ⟨isEmbedding_prodMkLeft (1 : D), ?_⟩
  have : range (fun x : X => (x, (1 : D))) = (univ : Set X) ×ˢ ({1} : Set D) := by
    ext p
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨trivial, rfl⟩
    · rintro ⟨-, h⟩
      exact ⟨p.1, Prod.ext rfl h.symm⟩
  rw [this]
  exact isOpen_univ.prod (isOpen_discrete _)

/-- Roots in `ℝᵃ × Tᵇ`. -/
theorem isDivisible_real_circle (a b : ℕ) :
    ∀ n : ℕ, 0 < n → ∀ y : (Fin a → Multiplicative ℝ) × (Fin b → Circle), ∃ x, x ^ n = y := by
  intro n hn y
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hr : ∀ r : Multiplicative ℝ, ∃ x : Multiplicative ℝ, x ^ n = r := fun r =>
    ⟨Multiplicative.ofAdd (Multiplicative.toAdd r / n), by
      rw [← ofAdd_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ hn']; rfl⟩
  have hc : ∀ z : Circle, ∃ x : Circle, x ^ n = z := fun z => by
    obtain ⟨x, hx⟩ := isDivisibleGroup_additive_circle n hn (Additive.ofMul z)
    refine ⟨Additive.toMul x, ?_⟩
    have := congrArg Additive.toMul hx
    rw [toMul_nsmul] at this
    exact this
  choose f hf using fun i => hr (y.1 i)
  choose g hg using fun i => hc (y.2 i)
  exact ⟨(f, g), Prod.ext (funext fun i => hf i) (funext fun i => hg i)⟩

end Helpers

section Main

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G]

/-- Morris, Topology Without Tears, Theorem A5.13.7 (TP-608). A compactly generated locally compact
Hausdorff abelian group (here `G = V · ⟨g₁, …, g_m⟩` with `V` compact) is topologically isomorphic to
`ℝᵃ × ℤᵇ × K` with `K` a compact Hausdorff abelian group. -/
@[kb "morris2024" "Theorem A5.13.7, p. 597"]
theorem exists_equiv_real_int_compact_of_generated
    (V : Set G) (hV : IsCompact V) {m : ℕ} (g : Fin m → G)
    (hgen : ∀ y : G, ∃ v ∈ V, ∃ w ∈ Subgroup.closure (Set.range g), y = v * w) :
    ∃ (a b : ℕ) (K : Type u) (_ : CommGroup K) (_ : TopologicalSpace K),
      IsTopologicalGroup K ∧ CompactSpace K ∧ T2Space K ∧
        Nonempty (G ≃ₜ* ((Fin a → Multiplicative ℝ) × (Fin b → Multiplicative ℤ)) × K) := by
  classical
  obtain ⟨K0, hK0, a, b, c, F, iF1, iF2, hFf, hFd, ⟨e⟩⟩ :=
    exists_compact_subgroup_quotient_real_circle_int_finite V hV g hgen
  haveI : Finite F := hFf
  haveI : DiscreteTopology F := hFd
  haveI : IsTopologicalGroup F := ⟨⟩
  haveI : CompactSpace F := Finite.compactSpace
  haveI : DiscreteTopology (PontryaginDual F) := inferInstance
  -- the dual of the model
  let eM : PontryaginDual ((((Fin a → Multiplicative ℝ) × (Fin c → Circle)) ×
        (Fin b → Multiplicative ℤ)) × F) ≃ₜ*
      (((Fin a → Multiplicative ℝ) × (Fin c → Multiplicative ℤ)) × (Fin b → Circle)) ×
        PontryaginDual F :=
    (pontryaginDualProdEquiv _ _).trans
      (prodCongr ((pontryaginDualProdEquiv _ _).trans
        (prodCongr ((pontryaginDualProdEquiv _ _).trans
          (prodCongr (selfDualRealPow a) (dualCirclePowEquiv c))) (dualIntPowEquiv b)))
        (ContinuousMulEquiv.refl _))
  let rM : ((((Fin a → Multiplicative ℝ) × (Fin c → Multiplicative ℤ)) × (Fin b → Circle)) ×
        PontryaginDual F) ≃ₜ*
      ((Fin a → Multiplicative ℝ) × (Fin b → Circle)) ×
        ((Fin c → Multiplicative ℤ) × PontryaginDual F) := reorder4 _ _ _ _
  -- the dual of the quotient map
  obtain ⟨-, -, -, -, hemb⟩ := dual_sequence_compact_subgroup K0 hK0
  let ι : ((Fin a → Multiplicative ℝ) × (Fin b → Circle)) →* PontryaginDual G :=
    (PontryaginDual.map (quotHom K0)).toMonoidHom.comp
      ((dualCongr e).symm.toMulEquiv.toMonoidHom.comp
        (eM.symm.toMulEquiv.toMonoidHom.comp
          (rM.symm.toMulEquiv.toMonoidHom.comp
            (MonoidHom.inl _ ((Fin c → Multiplicative ℤ) × PontryaginDual F)))))
  haveI : DiscreteTopology ((Fin c → Multiplicative ℤ) × PontryaginDual F) := inferInstance
  have hι : IsOpenEmbedding ι := by
    have h1 : IsOpenEmbedding (fun x : (Fin a → Multiplicative ℝ) × (Fin b → Circle) =>
        (x, (1 : (Fin c → Multiplicative ℤ) × PontryaginDual F))) := isOpenEmbedding_mk_one
    exact hemb.comp (((dualCongr e).symm.toHomeomorph.isOpenEmbedding).comp
      (eM.symm.toHomeomorph.isOpenEmbedding.comp
        (rM.symm.toHomeomorph.isOpenEmbedding.comp h1)))
  -- the open divisible subgroup `H`
  let H : Subgroup (PontryaginDual G) := ι.range
  have hHo : IsOpen (H : Set (PontryaginDual G)) := by
    have := hι.isOpen_range
    rwa [← MonoidHom.coe_range] at this
  let hh : ((Fin a → Multiplicative ℝ) × (Fin b → Circle)) ≃ₜ H := hι.toIsEmbedding.toHomeomorph
  let hH' : ((Fin a → Multiplicative ℝ) × (Fin b → Circle)) ≃ₜ* H :=
    { toFun := hh
      invFun := hh.symm
      left_inv := hh.left_inv
      right_inv := hh.right_inv
      map_mul' := fun x y => Subtype.ext (map_mul ι x y)
      continuous_toFun := hh.continuous
      continuous_invFun := hh.symm.continuous }
  have hdiv : ∀ n : ℕ, 0 < n → ∀ h : H, ∃ x : H, x ^ n = h := by
    intro n hn h
    obtain ⟨y, hy⟩ := hH'.surjective h
    obtain ⟨x, hx⟩ := isDivisible_real_circle a b n hn y
    exact ⟨hH' x, by rw [← map_pow, hx, hy]⟩
  obtain ⟨e3, -⟩ := exists_continuousMulEquiv_prod_quotient H hHo hdiv
  haveI : DiscreteTopology (PontryaginDual G ⧸ H) := QuotientGroup.discreteTopology hHo
  haveI : IsTopologicalGroup (PontryaginDual G ⧸ H) := inferInstance
  let E1 : PontryaginDual G ≃ₜ*
      ((Fin a → Multiplicative ℝ) × (Fin b → Circle)) × (PontryaginDual G ⧸ H) :=
    e3.trans (prodCongr hH'.symm (ContinuousMulEquiv.refl _))
  obtain ⟨d, -⟩ := LCA.dualityHolds_of_LCA (G := G)
  refine ⟨a, b, PontryaginDual (PontryaginDual G ⧸ H), inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ⟨?_⟩⟩
  exact d.trans ((dualCongr E1).trans ((pontryaginDualProdEquiv _ _).trans
    (prodCongr ((pontryaginDualProdEquiv _ _).trans
      (prodCongr (selfDualRealPow a) (dualCirclePowEquiv b))) (ContinuousMulEquiv.refl _))))

/-- The range of an embedding homomorphism is topologically isomorphic to the source. -/
noncomputable def contMulEquivRange {A B : Type*} [Group A] [Group B] [TopologicalSpace A] [TopologicalSpace B]
    (ι : A →* B) (hι : IsEmbedding ι) : A ≃ₜ* ι.range :=
  let hh : A ≃ₜ ι.range := hι.toHomeomorph
  { toFun := hh
    invFun := hh.symm
    left_inv := hh.left_inv
    right_inv := hh.right_inv
    map_mul' := fun x y => Subtype.ext (map_mul ι x y)
    continuous_toFun := hh.continuous
    continuous_invFun := hh.symm.continuous }

/-- Morris, Topology Without Tears, Theorem A5.13.8 (TP-609), Principal Structure Theorem. Every locally
compact Hausdorff abelian group has an open subgroup topologically isomorphic to `ℝᵃ × K` with `K`
compact. -/
@[kb "morris2024" "Theorem A5.13.8, p. 597"]
theorem exists_open_subgroup_equiv_real_compact :
    ∃ S : Subgroup G, IsOpen (S : Set G) ∧
      ∃ (a : ℕ) (K : Type u) (_ : CommGroup K) (_ : TopologicalSpace K),
        IsTopologicalGroup K ∧ CompactSpace K ∧ T2Space K ∧
          Nonempty (S ≃ₜ* (Fin a → Multiplicative ℝ) × K) := by
  classical
  obtain ⟨H, hHo, V, hVc, m, g, hgen⟩ := LCA.exists_open_generated_subgroup (G := G)
  haveI : LocallyCompactSpace H := hHo.isOpenEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨a, b, K, iK1, iK2, hK1, hK2, hK3, ⟨e⟩⟩ :=
    exists_equiv_real_int_compact_of_generated V hVc g hgen
  haveI : DiscreteTopology (Fin b → Multiplicative ℤ) := inferInstance
  let sw := swapLastTwo (Fin a → Multiplicative ℝ) (Fin b → Multiplicative ℤ) K
  let ι : ((Fin a → Multiplicative ℝ) × K) →* G :=
    H.subtype.comp (e.symm.toMulEquiv.toMonoidHom.comp
      (sw.symm.toMulEquiv.toMonoidHom.comp (MonoidHom.inl _ (Fin b → Multiplicative ℤ))))
  have hι : IsOpenEmbedding ι :=
    hHo.isOpenEmbedding_subtypeVal.comp (e.symm.toHomeomorph.isOpenEmbedding.comp
      (sw.symm.toHomeomorph.isOpenEmbedding.comp isOpenEmbedding_mk_one))
  refine ⟨ι.range, ?_, a, K, iK1, iK2, hK1, hK2, hK3, ⟨(contMulEquivRange ι hι.toIsEmbedding).symm⟩⟩
  have := hι.isOpen_range
  rwa [← MonoidHom.coe_range] at this

/-- Morris, Topology Without Tears, Theorem A5.13.9 (TP-610) and Theorem A5.0.20 (TP-493). A connected
locally compact Hausdorff abelian group is topologically isomorphic to `ℝᵃ × K` with `K` a compact
connected Hausdorff abelian group. -/
@[kb "morris2024" "Theorem A5.13.9, p. 597"]
theorem exists_equiv_real_compact_of_connectedSpace [ConnectedSpace G] :
    ∃ (a : ℕ) (K : Type u) (_ : CommGroup K) (_ : TopologicalSpace K),
      IsTopologicalGroup K ∧ CompactSpace K ∧ T2Space K ∧ ConnectedSpace K ∧
        Nonempty (G ≃ₜ* (Fin a → Multiplicative ℝ) × K) := by
  obtain ⟨S, hSo, a, K, iK1, iK2, hK1, hK2, hK3, ⟨e⟩⟩ := exists_open_subgroup_equiv_real_compact (G := G)
  have hSc : IsClosed (S : Set G) := Subgroup.isClosed_of_isOpen S hSo
  have huniv : (S : Set G) = Set.univ := IsClopen.eq_univ ⟨hSc, hSo⟩ ⟨1, S.one_mem⟩
  have hmem : ∀ x : G, x ∈ S := fun x => by
    have : x ∈ (S : Set G) := by rw [huniv]; trivial
    exact this
  let eG : G ≃ₜ* S :=
    { toFun := fun x => ⟨x, hmem x⟩
      invFun := Subtype.val
      left_inv := fun x => rfl
      right_inv := fun x => rfl
      map_mul' := fun x y => rfl
      continuous_toFun := Continuous.subtype_mk continuous_id _
      continuous_invFun := continuous_subtype_val }
  let E : G ≃ₜ* (Fin a → Multiplicative ℝ) × K := eG.trans e
  have hconn : ConnectedSpace K := by
    refine Function.Surjective.connectedSpace (f := fun x : G => (E x).2) ?_
      (continuous_snd.comp E.continuous)
    intro k
    exact ⟨E.symm (1, k), by simp⟩
  exact ⟨a, K, iK1, iK2, hK1, hK2, hK3, hconn, ⟨E⟩⟩

/-- Morris, Topology Without Tears, Corollary A5.15.16 (TP-636). Every connected locally compact
Hausdorff abelian group is divisible. -/
@[kb "morris2024" "Corollary A5.15.16, p. 613"]
theorem isDivisibleMulGroup_of_connectedSpace_LCA [ConnectedSpace G] : IsDivisibleMulGroup G := by
  obtain ⟨a, K, iK1, iK2, hK1, hK2, hK3, hKc, ⟨E⟩⟩ :=
    exists_equiv_real_compact_of_connectedSpace (G := G)
  have hKdiv : IsDivisibleMulGroup K := isDivisibleMulGroup_of_connectedSpace_of_compact
  intro n hn x
  obtain ⟨r, k⟩ := E x
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨k', hk'⟩ := hKdiv n hn (E x).2
  have hr : ∀ i, ∃ y : Multiplicative ℝ, y ^ n = (E x).1 i := fun i =>
    ⟨Multiplicative.ofAdd (Multiplicative.toAdd ((E x).1 i) / n), by
      rw [← ofAdd_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ hn']; rfl⟩
  choose r' hr' using hr
  refine ⟨E.symm (r', k'), E.injective ?_⟩
  rw [map_pow]
  simp only [ContinuousMulEquiv.apply_symm_apply]
  exact Prod.ext (funext fun i => hr' i) hk'

/-! ### Compact elements (TP-629) -/

section CompactElements

open Pointwise

/-- A compact element (Morris, Definition A5.15.4): the smallest closed subgroup containing it,
the closure of the cyclic subgroup, is compact. -/
def IsCompactElem (g : G) : Prop := IsCompact (closure (Subgroup.zpowers g : Set G))

theorem isCompactElem_one : IsCompactElem (1 : G) := by
  have : (Subgroup.zpowers (1 : G) : Set G) = {1} := by
    ext y; simp [Subgroup.mem_zpowers_iff, eq_comm]
  unfold IsCompactElem
  rw [this, closure_singleton]
  exact isCompact_singleton

theorem isCompactElem_inv {g : G} (h : IsCompactElem g) : IsCompactElem g⁻¹ := by
  unfold IsCompactElem at *
  rwa [Subgroup.zpowers_inv]

theorem isCompactElem_mul {g h : G} (hg : IsCompactElem g) (hh : IsCompactElem h) :
    IsCompactElem (g * h) := by
  have hsum := hg.mul hh
  unfold IsCompactElem
  refine hsum.of_isClosed_subset isClosed_closure ?_
  refine closure_minimal ?_ hsum.isClosed
  intro y hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  rw [mul_zpow]
  exact Set.mul_mem_mul (subset_closure (Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩))
    (subset_closure (Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩))

/-- A continuous real-valued function that is additive along the powers of `w` and bounded on a compact
set containing all powers of `w` vanishes at `w`. -/
theorem zero_of_pow_mem_compact {M : Type*} [Group M] [TopologicalSpace M] (ψ : M → ℝ)
    (hψ : Continuous ψ) (w : M) (hmul : ∀ n : ℕ, ψ (w ^ n) = n * ψ w) {C : Set M}
    (hC : IsCompact C) (hsub : ∀ n : ℕ, w ^ n ∈ C) : ψ w = 0 := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 (hC.image hψ).isBounded
  by_contra hne
  have hpos : 0 < |ψ w| := abs_pos.2 hne
  obtain ⟨n, hn⟩ := exists_nat_gt (r / |ψ w|)
  have h1 : ψ (w ^ n) ∈ Metric.closedBall (0 : ℝ) r := hr ⟨w ^ n, hsub n, rfl⟩
  rw [mem_closedBall_zero_iff, hmul, norm_mul, Real.norm_natCast, Real.norm_eq_abs] at h1
  rw [div_lt_iff₀ hpos] at hn
  linarith

/-- In `ℝᵃ × ℤᵇ` an element all of whose powers lie in a compact set is trivial. -/
theorem eq_one_of_pow_mem_compact {a b : ℕ}
    (w : (Fin a → Multiplicative ℝ) × (Fin b → Multiplicative ℤ))
    {C : Set ((Fin a → Multiplicative ℝ) × (Fin b → Multiplicative ℤ))} (hC : IsCompact C)
    (hsub : ∀ n : ℕ, w ^ n ∈ C) : w = 1 := by
  refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
  · have hc : Continuous (fun x : (Fin a → Multiplicative ℝ) × (Fin b → Multiplicative ℤ) =>
        Multiplicative.toAdd (x.1 i)) :=
      continuous_toAdd.comp ((continuous_apply i).comp continuous_fst)
    have := zero_of_pow_mem_compact _ hc w (fun n => by simp [toAdd_pow]) hC hsub
    exact toAdd_eq_zero.1 this
  · have hd : Continuous (fun y : Multiplicative ℤ => ((Multiplicative.toAdd y : ℤ) : ℝ)) :=
      continuous_of_discreteTopology
    have hc : Continuous (fun x : (Fin a → Multiplicative ℝ) × (Fin b → Multiplicative ℤ) =>
        ((Multiplicative.toAdd (x.2 j) : ℤ) : ℝ)) :=
      hd.comp ((continuous_apply j).comp continuous_snd)
    have := zero_of_pow_mem_compact _ hc w (fun n => by simp [toAdd_pow]) hC hsub
    exact toAdd_eq_zero.1 (by exact_mod_cast this)

/-- Morris, Topology Without Tears, Proposition A5.15.6 (TP-629). In a locally compact Hausdorff abelian
group the set of compact elements is closed (it is a subgroup by `isCompactElem_mul`, `isCompactElem_inv`
and `isCompactElem_one`). Proved through the structure theorem A5.13.7 for an open compactly generated
subgroup. -/
@[kb "morris2024" "Proposition A5.15.6, p. 610"]
theorem isClosed_setOf_isCompactElement : IsClosed {g : G | IsCompactElem g} := by
  classical
  obtain ⟨H, hHo, V, hVc, m, g, hgen⟩ := LCA.exists_open_generated_subgroup (G := G)
  haveI : LocallyCompactSpace H := hHo.isOpenEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨a, b, K, iK1, iK2, hK1, hK2, hK3, ⟨e⟩⟩ :=
    exists_equiv_real_int_compact_of_generated V hVc g hgen
  have hHc : IsClosed (H : Set G) := Subgroup.isClosed_of_isOpen H hHo
  let f0 : K → G := fun k => ((e.symm (1, k) : H) : G)
  have hf0 : Continuous f0 := continuous_subtype_val.comp
    (e.symm.continuous.comp (continuous_const.prodMk continuous_id))
  let C0 : Set G := range f0
  have hC0 : IsCompact C0 := isCompact_range hf0
  -- compact elements of `G` lying in `H` are exactly `C0`
  have hsub : {x : G | IsCompactElem x} ∩ (H : Set G) = C0 := by
    ext x
    constructor
    · rintro ⟨hx, hxH⟩
      let x' : H := ⟨x, hxH⟩
      have hZ : closure (Subgroup.zpowers x : Set G) ⊆ (H : Set G) :=
        closure_minimal (by
          rintro _ ⟨k, rfl⟩
          exact H.zpow_mem hxH k) hHc
      have hZH : IsCompact ((Subtype.val : H → G) ⁻¹' closure (Subgroup.zpowers x : Set G)) := by
        rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
        have : (Subtype.val : H → G) '' ((Subtype.val : H → G) ⁻¹'
            closure (Subgroup.zpowers x : Set G)) = closure (Subgroup.zpowers x : Set G) := by
          ext y
          constructor
          · rintro ⟨z, hz, rfl⟩; exact hz
          · intro hy; exact ⟨⟨y, hZ hy⟩, hy, rfl⟩
        rw [this]; exact hx
      have hpow : ∀ n : ℕ, (e x') ^ n ∈ e '' ((Subtype.val : H → G) ⁻¹'
          closure (Subgroup.zpowers x : Set G)) := fun n =>
        ⟨x' ^ n, subset_closure ⟨(n : ℤ), by simp [x']⟩, by rw [map_pow]⟩
      have hw : (e x').1 = 1 := eq_one_of_pow_mem_compact (e x').1
        ((hZH.image e.continuous).image continuous_fst) (fun n => by
          obtain ⟨y, hy, hyn⟩ := hpow n
          exact ⟨(e x' ^ n), ⟨y, hy, hyn⟩, rfl⟩)
      refine ⟨(e x').2, ?_⟩
      have : e x' = (1, (e x').2) := Prod.ext hw rfl
      show ((e.symm (1, (e x').2) : H) : G) = x
      rw [← this]
      simp [x']
    · rintro ⟨k, rfl⟩
      refine ⟨?_, (e.symm (1, k)).2⟩
      have hCl : IsClosed C0 := hC0.isClosed
      unfold IsCompactElem
      refine hC0.of_isClosed_subset isClosed_closure (closure_minimal ?_ hCl)
      rintro _ ⟨n, rfl⟩
      refine ⟨k ^ n, ?_⟩
      show ((e.symm (1, k ^ n) : H) : G) = ((e.symm (1, k) : H) : G) ^ n
      rw [← Subgroup.coe_zpow, ← map_zpow]
      simp
  have hSH : IsClosed ({x : G | IsCompactElem x} ∩ (H : Set G)) := by rw [hsub]; exact hC0.isClosed
  refine isClosed_of_closure_subset fun x hx => ?_
  have hU : IsOpen ((fun s : G => s⁻¹ * x) ⁻¹' (H : Set G)) :=
    hHo.preimage (continuous_inv.mul continuous_const)
  have hxU : x ∈ (fun s : G => s⁻¹ * x) ⁻¹' (H : Set G) := by
    show x⁻¹ * x ∈ (H : Set G)
    rw [inv_mul_cancel]; exact H.one_mem
  obtain ⟨s, hsU, hsS⟩ := mem_closure_iff.1 hx _ hU hxU
  have hsS' : IsCompactElem s := hsS
  have ht : s⁻¹ * x ∈ closure {g : G | IsCompactElem g} :=
    map_mem_closure (f := fun y : G => s⁻¹ * y) (continuous_const.mul continuous_id) hx
      (fun y hy => isCompactElem_mul (isCompactElem_inv hsS') hy)
  have htH : s⁻¹ * x ∈ (H : Set G) := hsU
  have ht2 : s⁻¹ * x ∈ closure ((H : Set G) ∩ {g : G | IsCompactElem g}) :=
    hHo.inter_closure ⟨htH, ht⟩
  rw [Set.inter_comm, hSH.closure_eq] at ht2
  have hts : IsCompactElem (s⁻¹ * x) := ht2.1
  have : x = s * (s⁻¹ * x) := by simp
  show IsCompactElem x
  rw [this]
  exact isCompactElem_mul hsS' hts

end CompactElements

end Main

section AdditiveCompactElements

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [T2Space A]
  [LocallyCompactSpace A]

/-- Morris, Topology Without Tears, Proposition A5.15.6 (TP-629), additive form. In a locally compact
Hausdorff abelian group the subgroup of compact elements (`compactElements`) is closed. -/
@[kb "morris2024" "Proposition A5.15.6, p. 610"]
theorem isClosed_compactElements : IsClosed ((compactElements A : AddSubgroup A) : Set A) := by
  haveI : LocallyCompactSpace (Multiplicative A) := inferInstanceAs (LocallyCompactSpace A)
  haveI : T2Space (Multiplicative A) := inferInstanceAs (T2Space A)
  exact isClosed_setOf_isCompactElement (G := Multiplicative A)

end AdditiveCompactElements

end UndergradKB.Topology
