import UndergradKB.Topology.StructureWave2
import UndergradKB.Topology.StructureWave2b
import UndergradKB.Topology.GroupsWave2h
import UndergradKB.Topology.DualityLCA2
import UndergradKB.Common.Attr

/-!
# Proposition A5.12.10 (Morris, Topology Without Tears)

A compactly generated locally compact Hausdorff abelian group `G` has a compact subgroup `K` such that
`G / K` is topologically isomorphic to `ℝᵃ × Tᶜ × ℤᵇ × F` with `F` finite and discrete.
-/

open Topology Set Filter

set_option linter.unusedSectionVars false

universe u

namespace UndergradKB.Topology

noncomputable section

/-! ### Conversions between additive and multiplicative models -/

/-- A topological isomorphism of additive groups gives one of their multiplicative copies. -/
def addToMulCongr {A B : Type*} [AddCommGroup A] [AddCommGroup B] [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃ₜ+ B) : Multiplicative A ≃ₜ* Multiplicative B where
  toMulEquiv := AddEquiv.toMultiplicative e.toAddEquiv
  continuous_toFun := e.continuous
  continuous_invFun := e.symm.continuous

/-- `Multiplicative (A × B) ≃ₜ* Multiplicative A × Multiplicative B`. -/
def mulProdEquiv (A B : Type*) [AddCommGroup A] [AddCommGroup B] [TopologicalSpace A]
    [TopologicalSpace B] : Multiplicative (A × B) ≃ₜ* Multiplicative A × Multiplicative B where
  toMulEquiv := MulEquiv.prodMultiplicative A B
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

/-- `Multiplicative (ι → A) ≃ₜ* (ι → Multiplicative A)`. -/
def mulPiEquiv (ι : Type*) (A : Type*) [AddCommGroup A] [TopologicalSpace A] :
    Multiplicative (ι → A) ≃ₜ* (ι → Multiplicative A) where
  toFun x i := Multiplicative.ofAdd (Multiplicative.toAdd x i)
  invFun f := Multiplicative.ofAdd (fun i => Multiplicative.toAdd (f i))
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_pi fun i => continuous_apply i
  continuous_invFun := continuous_pi fun i => continuous_apply i

/-- `Multiplicative (AddCircle 1) ≃ₜ* Circle`. -/
def mulAddCircleEquiv : Multiplicative (AddCircle (1 : ℝ)) ≃ₜ* Circle where
  toFun x := AddCircle.toCircle (Multiplicative.toAdd x)
  invFun z := Multiplicative.ofAdd ((AddCircle.homeomorphCircle one_ne_zero).symm z)
  left_inv x := by
    have h := (AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).symm_apply_apply
      (Multiplicative.toAdd x)
    rw [AddCircle.homeomorphCircle_apply] at h
    exact congrArg Multiplicative.ofAdd h
  right_inv z := by
    have h := (AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).apply_symm_apply z
    rwa [AddCircle.homeomorphCircle_apply] at h
  map_mul' x y := AddCircle.toCircle_add _ _
  continuous_toFun := AddCircle.continuous_toCircle
  continuous_invFun := (AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).symm.continuous

/-- `Multiplicative (Fin c → AddCircle 1) ≃ₜ* (Fin c → Circle)`. -/
def mulAddCirclePiEquiv (c : ℕ) :
    Multiplicative (Fin c → AddCircle (1 : ℝ)) ≃ₜ* (Fin c → Circle) :=
  (mulPiEquiv (Fin c) (AddCircle (1 : ℝ))).trans
    { toFun := fun f i => mulAddCircleEquiv (f i)
      invFun := fun f i => mulAddCircleEquiv.symm (f i)
      left_inv := fun f => by funext i; simp
      right_inv := fun f => by funext i; simp
      map_mul' := fun f g => by funext i; simp
      continuous_toFun := continuous_pi fun i =>
        mulAddCircleEquiv.continuous.comp (continuous_apply i)
      continuous_invFun := continuous_pi fun i =>
        mulAddCircleEquiv.symm.continuous.comp (continuous_apply i) }

/-- Associativity of products. -/
def prodAssocEquiv (A B C : Type*) [CommGroup A] [CommGroup B] [CommGroup C] [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace C] : A × (B × C) ≃ₜ* (A × B) × C where
  toFun p := ((p.1, p.2.1), p.2.2)
  invFun p := (p.1.1, (p.1.2, p.2))
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-! ### The theorem -/

section Main

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G]

/-- Morris, Topology Without Tears, Proposition A5.12.10 (TP-602). If `G` is a compactly generated
locally compact Hausdorff abelian group (here `G = V · ⟨g₁, …, g_m⟩` with `V` compact), then `G` has a
compact subgroup `K` such that `G / K` is topologically isomorphic to `ℝᵃ × Tᶜ × ℤᵇ × F`, where `F` is a
finite discrete abelian group. -/
@[kb "morris2024" "Proposition A5.12.10, p. 587"]
theorem exists_compact_subgroup_quotient_real_circle_int_finite
    (V : Set G) (hV : IsCompact V) {m : ℕ} (g : Fin m → G)
    (hgen : ∀ y : G, ∃ v ∈ V, ∃ w ∈ Subgroup.closure (Set.range g), y = v * w) :
    ∃ K : Subgroup G, IsCompact (K : Set G) ∧
      ∃ (a b c : ℕ) (F : Type) (_ : CommGroup F) (_ : TopologicalSpace F),
        Finite F ∧ DiscreteTopology F ∧
          Nonempty ((G ⧸ K) ≃ₜ*
            (((Fin a → Multiplicative ℝ) × (Fin c → Circle)) × (Fin b → Multiplicative ℤ)) × F) := by
  classical
  obtain ⟨K, D, hKc, hDd, hKD, hD'd, n, E, i1, i2, hE, hEd, ⟨T⟩⟩ :=
    exists_compact_subgroup_discrete_quotient_torus_prod_finite V hV g hgen
  refine ⟨K, hKc, ?_⟩
  haveI : IsClosed (K : Set G) := hKc.isClosed
  let Q := G ⧸ K
  let D' : Subgroup Q := D.map (QuotientGroup.mk' K)
  haveI : DiscreteTopology D' := hD'd
  haveI : Finite E := hE
  haveI : DiscreteTopology E := hEd
  -- local isomorphism with `ℝⁿ`
  have hloc : LocallyIsomorphic (Multiplicative (Fin n → ℝ)) Q :=
    locallyIsomorphic_real_pow_of_discrete_quotient_torus n D' T
  have hadd : AddLocallyIsomorphic (Fin n → ℝ) (Additive Q) :=
    (addLocallyIsomorphic_iff (Fin n → ℝ) (Additive Q)).1 hloc
  haveI : T2Space (Additive Q) := inferInstanceAs (T2Space Q)
  obtain ⟨a, c, S, iS1, iS2, hSd, -, ⟨e⟩⟩ :=
    exists_equiv_real_circle_discrete_of_addLocallyIsomorphic hadd
  -- the multiplicative model
  let e1 : Q ≃ₜ* ((Fin a → Multiplicative ℝ) × (Fin c → Circle)) × Multiplicative S :=
    (addToMulCongr e).trans ((mulProdEquiv _ _).trans
      (prodCongr ((mulProdEquiv _ _).trans
        (prodCongr (mulPiEquiv (Fin a) ℝ) (mulAddCirclePiEquiv c)))
        (ContinuousMulEquiv.refl _)))
  haveI : DiscreteTopology (Multiplicative S) := hSd
  haveI : IsTopologicalAddGroup S := ⟨⟩
  -- `S` is finitely generated
  let pr : Q →* Multiplicative S := (MonoidHom.snd _ _).comp e1.toMulEquiv.toMonoidHom
  have hpr : Function.Surjective pr := fun s => by
    obtain ⟨q, hq⟩ := e1.surjective (1, s)
    refine ⟨q, ?_⟩
    show (e1 q).2 = s
    rw [hq]
  have hprc : Continuous pr := continuous_snd.comp e1.continuous
  let π : G →* Multiplicative S := pr.comp (QuotientGroup.mk' K)
  have hπc : Continuous π := hprc.comp QuotientGroup.continuous_mk
  have hfin : Group.FG (Multiplicative S) := by
    rw [Group.fg_iff]
    have hPfin : (π '' V).Finite := (hV.image hπc).finite_of_discrete
    refine ⟨(π '' V) ∪ Set.range (fun i => π (g i)), ?_, hPfin.union (Set.finite_range _)⟩
    rw [eq_top_iff]
    intro s _
    obtain ⟨q, rfl⟩ := hpr s
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨v, hv, w, hw, rfl⟩ := hgen y
    have h1 : π v ∈ Subgroup.closure ((π '' V) ∪ Set.range (fun i => π (g i))) :=
      Subgroup.subset_closure (Or.inl ⟨v, hv, rfl⟩)
    have h2 : π w ∈ Subgroup.closure ((π '' V) ∪ Set.range (fun i => π (g i))) := by
      have : π w ∈ (Subgroup.closure (Set.range g)).map π := Subgroup.mem_map_of_mem _ hw
      rw [MonoidHom.map_closure, ← Set.range_comp] at this
      exact Subgroup.closure_mono Set.subset_union_right this
    have : pr (QuotientGroup.mk (v * w)) = π v * π w := by
      show π (v * w) = _
      exact map_mul π v w
    rw [this]
    exact Subgroup.mul_mem _ h1 h2
  -- structure of the finitely generated discrete group
  obtain ⟨ι, j, _, _, p, hp, ex, ⟨φ⟩⟩ := CommGroup.equiv_free_prod_prod_multiplicative_zmod
    (Multiplicative S)
  haveI : ∀ i, NeZero (p i ^ ex i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  let ψ : Multiplicative S ≃ₜ*
      ((j → Multiplicative ℤ) × ((i : ι) → Multiplicative (ZMod (p i ^ ex i)))) :=
    { toMulEquiv := φ
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  refine ⟨a, Fintype.card j, c, (i : ι) → Multiplicative (ZMod (p i ^ ex i)), inferInstance,
    inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩
  let e2 : Multiplicative S ≃ₜ* (Fin (Fintype.card j) → Multiplicative ℤ) ×
      ((i : ι) → Multiplicative (ZMod (p i ^ ex i))) :=
    ψ.trans (prodCongr (reindexPi (Fintype.equivFin j) (Multiplicative ℤ))
      (ContinuousMulEquiv.refl _))
  let e3 : Q ≃ₜ* ((Fin a → Multiplicative ℝ) × (Fin c → Circle)) ×
      ((Fin (Fintype.card j) → Multiplicative ℤ) ×
        ((i : ι) → Multiplicative (ZMod (p i ^ ex i)))) :=
    e1.trans (prodCongr (ContinuousMulEquiv.refl _) e2)
  exact e3.trans (prodAssocEquiv _ _ _)

end Main

end

end UndergradKB.Topology
