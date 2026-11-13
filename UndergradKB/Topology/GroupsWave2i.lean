import UndergradKB.Topology.ClosedSubgroupsRn
import UndergradKB.Topology.GroupsWave2e
import Mathlib.Logic.Equiv.Fin.Basic
import UndergradKB.Common.Attr

/-!
# Wave 2: closed subgroups of `ℝⁿ × ℤᵐ` (Morris, Appendix 5.5, Corollary A5.5.17)

From the splitting theorem A5.5.16 (`closedSubgroup_prod_divisible_free`) and the structure of closed
subgroups of `ℝⁿ`, with the dimension bounds.
-/

open Set

universe u

namespace UndergradKB.Topology

open ClosedSubgroupsRn

section Bounds

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A closed subgroup of a finite-dimensional real normed space `E` is topologically isomorphic to
`ℝ^p × ℤ^q` with `p + q ≤ dim E`. -/
theorem closed_subgroup_equiv_bounds (G : AddSubgroup E) (hG : IsClosed (G : Set E)) :
    ∃ p q : ℕ, p + q ≤ Module.finrank ℝ E ∧
      Nonempty (G ≃ₜ+ ((Fin p → ℝ) × (Fin q → ℤ))) := by
  classical
  obtain ⟨V, L, hL, hdec, hind, ⟨e⟩⟩ := exists_splitting G hG
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
  have hle := hf.fintype_card_le_finrank
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at hle
  let Ψ : (Fin q → ℤ) →+ L :=
    { toFun := fun n => ⟨∑ j, n j • b j, (hLmem _).2 ⟨n, rfl⟩⟩
      map_zero' := by ext; simp
      map_add' := fun n m => by
        ext
        simp [add_smul, Finset.sum_add_distrib] }
  have hinj : Function.Injective Ψ := by
    intro n m hnm
    have h1 : ∑ j, n j • b j = ∑ j, m j • b j := congrArg Subtype.val hnm
    have h2 : ∑ j, ((n j : ℝ) - (m j : ℝ)) • b j = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, Int.cast_smul_eq_zsmul ℝ]
      rw [h1]; exact sub_self _
    funext j
    have := Fintype.linearIndependent_iff.1 hb _ h2 j
    have h3 : (n j : ℝ) = m j := sub_eq_zero.1 this
    exact_mod_cast h3
  have hsurj : Function.Surjective Ψ := by
    rintro ⟨x, hx⟩
    obtain ⟨n, hn⟩ := (hLmem x).1 hx
    exact ⟨n, Subtype.ext hn.symm⟩
  let eL : (Fin q → ℤ) ≃+ L := AddEquiv.ofBijective Ψ ⟨hinj, hsurj⟩
  let eL' : L ≃ₜ+ (Fin q → ℤ) :=
    mkCAE eL.symm continuous_of_discreteTopology continuous_of_discreteTopology
  exact ⟨p, q, hle, ⟨e.trans (prodCAE (subspaceCAE V) eL')⟩⟩

end Bounds

section IntPow

/-- A subgroup of `ℤ^m` is isomorphic to `ℤ^s` with `s ≤ m`. -/
theorem subgroup_int_pow_equiv {m : ℕ} (K : AddSubgroup (Fin m → ℤ)) :
    ∃ s : ℕ, s ≤ m ∧ Nonempty (K ≃+ (Fin s → ℤ)) := by
  classical
  let K' : Submodule ℤ (Fin m → ℤ) := AddSubgroup.toIntSubmodule K
  haveI : Module.Free ℤ K' := submodule_free_of_free K'
  let b := Module.Free.chooseBasis ℤ K'
  let s := Fintype.card (Module.Free.ChooseBasisIndex ℤ K')
  let e : K' ≃ₗ[ℤ] (Fin s → ℤ) :=
    b.equivFun.trans (LinearEquiv.funCongrLeft ℤ ℤ (Fintype.equivFin _).symm)
  have hs : s ≤ m := by
    have h1 := Submodule.finrank_le K'
    rw [Module.finrank_eq_card_chooseBasisIndex, Module.finrank_fin_fun] at h1
    exact h1
  refine ⟨s, hs, ⟨?_⟩⟩
  exact
    { toFun := fun x => e ⟨x.1, x.2⟩
      invFun := fun y => ⟨(e.symm y).1, (e.symm y).2⟩
      left_inv := fun x => by simp
      right_inv := fun y => e.apply_symm_apply y
      map_add' := fun x y => e.map_add ⟨x.1, x.2⟩ ⟨y.1, y.2⟩ }

end IntPow

section Splitting

variable {n m : ℕ}

/-- Morris, Topology Without Tears, Corollary A5.5.17 (TP-549), first half. A closed subgroup `G` of
`ℝⁿ × ℤᵐ` is topologically isomorphic to `ℝ^a × ℤ^b` with `a ≤ n` and `a + b ≤ n + m`. -/
@[kb "morris2024" "Corollary A5.5.17, p. 547"]
theorem closedSubgroup_real_pow_prod_int_pow (G : AddSubgroup ((Fin n → ℝ) × (Fin m → ℤ)))
    (hG : IsClosed (G : Set ((Fin n → ℝ) × (Fin m → ℤ)))) :
    ∃ a b : ℕ, a ≤ n ∧ a + b ≤ n + m ∧ Nonempty (G ≃ₜ+ ((Fin a → ℝ) × (Fin b → ℤ))) := by
  classical
  have hdiv : ∀ k : ℕ, 0 < k → ∀ v : Fin n → ℝ, ∃ w, k • w = v := fun k hk v =>
    ⟨(k : ℝ)⁻¹ • v, by
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hk.ne'), one_smul]⟩
  obtain ⟨F', ⟨iso⟩, hFd, e, he1, he2⟩ := closedSubgroup_prod_divisible_free hdiv G hG
  -- the two pieces
  let Gv : AddSubgroup (Fin n → ℝ) := G.comap (AddMonoidHom.inl _ _)
  let Gf : AddSubgroup F' := G.comap F'.subtype
  have hGv : IsClosed (Gv : Set (Fin n → ℝ)) :=
    hG.preimage (continuous_id.prodMk continuous_const)
  let P : AddSubgroup ((Fin n → ℝ) × F') := Gv.prod Gf
  have hP : e '' (P : Set _) = (G : Set _) := by
    rw [← he2]
    rfl
  -- G ≃ P
  let eGP : G ≃ₜ+ P :=
    { toFun := fun g => ⟨e.symm g, by
        obtain ⟨p, hp, hpg⟩ := (hP ▸ g.2 : (g : (Fin n → ℝ) × (Fin m → ℤ)) ∈ e '' (P : Set _))
        have : e.symm g = p := by rw [← hpg]; exact e.symm_apply_apply p
        rw [this]; exact hp⟩
      invFun := fun p => ⟨e p, by
        rw [← SetLike.mem_coe, ← hP]; exact ⟨p, p.2, rfl⟩⟩
      left_inv := fun g => Subtype.ext (e.apply_symm_apply g)
      right_inv := fun p => Subtype.ext (e.symm_apply_apply p)
      map_add' := fun g g' =>
        Subtype.ext (map_add e.symm (g : (Fin n → ℝ) × (Fin m → ℤ)) (g' : (Fin n → ℝ) × (Fin m → ℤ)))
      continuous_toFun :=
        continuous_induced_rng.2 (e.symm.continuous.comp continuous_subtype_val)
      continuous_invFun :=
        continuous_induced_rng.2 (e.continuous.comp continuous_subtype_val) }
  -- P ≃ Gv × Gf
  let ePG : P ≃ₜ+ (Gv × Gf) :=
    { toFun := fun p => (⟨p.1.1, (AddSubgroup.mem_prod.1 p.2).1⟩, ⟨p.1.2, (AddSubgroup.mem_prod.1 p.2).2⟩)
      invFun := fun q => ⟨((q.1 : Fin n → ℝ), (q.2 : F')), AddSubgroup.mem_prod.2 ⟨q.1.2, q.2.2⟩⟩
      left_inv := fun p => rfl
      right_inv := fun q => rfl
      map_add' := fun p p' => rfl
      continuous_toFun := by
        refine Continuous.prodMk (Continuous.subtype_mk ?_ _) (Continuous.subtype_mk ?_ _)
        · exact continuous_fst.comp continuous_subtype_val
        · exact continuous_snd.comp continuous_subtype_val
      continuous_invFun := by
        refine Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _
        · exact continuous_subtype_val.comp continuous_fst
        · exact continuous_subtype_val.comp continuous_snd }
  -- Gv
  obtain ⟨a, b1, hab1, ⟨eV⟩⟩ := closed_subgroup_equiv_bounds Gv hGv
  rw [Module.finrank_fin_fun] at hab1
  -- Gf
  let ι : F' ≃+ (Fin m → ℤ) := iso.symm
  let K : AddSubgroup (Fin m → ℤ) := Gf.map ι.toAddMonoidHom
  obtain ⟨s, hs, ⟨eK⟩⟩ := subgroup_int_pow_equiv K
  let eGf : Gf ≃ₜ+ (Fin s → ℤ) :=
    mkCAE ((AddEquiv.addSubgroupMap ι Gf).trans eK) continuous_of_discreteTopology
      continuous_of_discreteTopology
  -- merge the two integer factors
  let eInt : ((Fin b1 → ℤ) × (Fin s → ℤ)) ≃ₜ+ (Fin (b1 + s) → ℤ) :=
    mkCAE
      { toEquiv := Fin.appendEquiv b1 s
        map_add' := fun x y => by
          ext i
          refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [Fin.appendEquiv] }
      continuous_of_discreteTopology continuous_of_discreteTopology
  have e3 : (((Fin a → ℝ) × (Fin b1 → ℤ)) × (Fin s → ℤ)) ≃ₜ+
      ((Fin a → ℝ) × (Fin (b1 + s) → ℤ)) :=
    mkCAE
      { toEquiv := (Equiv.prodAssoc _ _ _).trans
          (Equiv.prodCongr (Equiv.refl _) (Fin.appendEquiv b1 s))
        map_add' := fun x y => by
          refine Prod.ext rfl ?_
          ext i
          refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [Fin.appendEquiv] }
      (by
        have hcA : Continuous (Fin.appendEquiv (α := ℤ) b1 s) := continuous_of_discreteTopology
        show Continuous fun x : ((Fin a → ℝ) × (Fin b1 → ℤ)) × (Fin s → ℤ) =>
          (x.1.1, Fin.appendEquiv b1 s (x.1.2, x.2))
        exact (continuous_fst.comp continuous_fst).prodMk
          (hcA.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)))
      (by
        have hcB : Continuous (Fin.appendEquiv (α := ℤ) b1 s).symm := continuous_of_discreteTopology
        show Continuous fun x : (Fin a → ℝ) × (Fin (b1 + s) → ℤ) =>
          ((x.1, ((Fin.appendEquiv b1 s).symm x.2).1), ((Fin.appendEquiv b1 s).symm x.2).2)
        exact (continuous_fst.prodMk
          (continuous_fst.comp (hcB.comp continuous_snd))).prodMk
          (continuous_snd.comp (hcB.comp continuous_snd)))
  exact ⟨a, b1 + s, by omega, by omega,
    ⟨eGP.trans (ePG.trans ((prodCAE eV eGf).trans e3))⟩⟩

end Splitting

end UndergradKB.Topology
