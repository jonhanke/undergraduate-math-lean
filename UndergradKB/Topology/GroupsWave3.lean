import UndergradKB.Topology.GroupsWave2k
import UndergradKB.Topology.ClosedSubgroupsRn2
import UndergradKB.Topology.GroupsMore2
import Mathlib.Topology.LocalAtTarget
import UndergradKB.Common.Attr

/-!
# Closed subgroups of `ℝⁿ × Tᵐ × D` and their quotients (Morris, Corollary A5.5.18; TP-549)

Morris, *Topology Without Tears*, Corollary A5.5.18: if `G` is a closed subgroup of `ℝⁿ × Tᵐ × D`
with `D` a discrete abelian group, then `G` is topologically isomorphic to `ℝᵃ × Tᵇ × D'` and the
quotient by `G` to `ℝᶜ × Tᵈ × D''` with `D'`, `D''` discrete and `a + b ≤ n + m`, `c + d ≤ n + m`.

The book derives this from a free resolution of `D` and Theorems A5.5.13 and A5.5.16. We argue
directly with `ρ : ℝⁿ × ℝᵐ → ℝⁿ × Tᵐ × D`, `ρ (u, w) = ((u, w mod ℤᵐ), 0)`, a continuous open
homomorphism:

* (`range_equiv_of_isOpenMap`) the range of a continuous open homomorphism `φ` from a
  finite-dimensional real vector space `E` with closed kernel is an open divisible subgroup
  topologically isomorphic to `E / ker φ ≅ ℝᶜ × Tᵈ`, `c + d ≤ dim E` (Theorem A5.5.13);
* for `G`: `P = ρ⁻¹(G)` contains a vector subspace `V` open in `P`; `ρ` restricted to `V` is a
  continuous open homomorphism into `G`, so its range is an open divisible subgroup `ℝᵃ × Tᵇ` of `G`,
  `a + b ≤ dim V ≤ n + m`, which splits off with a discrete complement (Proposition A5.3.8);
* for the quotient: the same with `ℝⁿ⁺ᵐ → (ℝⁿ × Tᵐ × D) / G`, whose kernel `ρ⁻¹(G)` is closed.
-/

open Set Topology

set_option linter.unusedSectionVars false

namespace UndergradKB.Topology

open ClosedSubgroupsRn ClosedSubgroupsRn2

section Range

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Y : Type*} [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]

/-- The range of a continuous open homomorphism `φ` from a finite-dimensional real vector space `E`
with closed kernel is an open divisible subgroup, topologically isomorphic to `ℝᶜ × Tᵈ` with
`c + d ≤ dim E`. -/
theorem range_equiv_of_isOpenMap (φ : E →+ Y) (hc : Continuous φ) (ho : IsOpenMap φ)
    (hk : IsClosed (φ.ker : Set E)) :
    ∃ c d : ℕ, c + d ≤ Module.finrank ℝ E ∧ IsOpen (φ.range : Set Y) ∧
      IsDivisibleGroup φ.range ∧
      Nonempty (φ.range ≃ₜ+ ((Fin c → ℝ) × (Fin d → AddCircle (1 : ℝ)))) := by
  obtain ⟨c, d, hcd, ⟨e⟩⟩ := quotient_closed_subgroup_equiv φ.ker hk
  have hro : IsOpen (φ.range : Set Y) := by
    rw [AddMonoidHom.coe_range]
    exact ho.isOpen_range
  let ψ : E →+ φ.range := φ.rangeRestrict
  have hψc : Continuous ψ := hc.subtype_mk _
  have hψo : IsOpenMap ψ := by
    intro U hU
    have : (ψ '' U) = ((↑) : φ.range → Y) ⁻¹' (φ '' U) := by
      ext ⟨y, hy⟩
      constructor
      · rintro ⟨x, hx, hxy⟩
        refine ⟨x, hx, ?_⟩
        have := congrArg Subtype.val hxy
        exact this
      · rintro ⟨x, hx, hxy⟩
        exact ⟨x, hx, Subtype.ext hxy⟩
    rw [this]
    exact (ho U hU).preimage continuous_subtype_val
  have hψs : Function.Surjective ψ := φ.rangeRestrict_surjective
  obtain ⟨e2⟩ := quotient_equiv φ.ker ψ hψc hψo hψs fun x => by
    rw [AddMonoidHom.mem_ker]
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      exact congrArg Subtype.val h
  refine ⟨c, d, hcd, hro, ?_, ⟨e2.symm.trans e⟩⟩
  rintro k hk0 ⟨y, x, rfl⟩
  refine ⟨⟨φ ((k : ℝ)⁻¹ • x), (k : ℝ)⁻¹ • x, rfl⟩, Subtype.ext ?_⟩
  show k • φ ((k : ℝ)⁻¹ • x) = φ x
  rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    mul_inv_cancel₀ (by exact_mod_cast hk0.ne'), one_smul]

end Range

section Main

variable {n m : ℕ} {D : Type} [AddCommGroup D] [TopologicalSpace D] [DiscreteTopology D]

/-- The map `ρ : ℝⁿ × ℝᵐ → (ℝⁿ × Tᵐ) × D`, `(u, w) ↦ ((u, w mod ℤᵐ), 0)`. -/
noncomputable def rhoMap (n m : ℕ) (D : Type) [AddCommGroup D] :
    ((Fin n → ℝ) × (Fin m → ℝ)) →+ ((Fin n → ℝ) × (Fin m → AddCircle (1 : ℝ))) × D :=
  (AddMonoidHom.inl _ _).comp ((AddMonoidHom.id _).prodMap (expMap m))

theorem continuous_rhoMap : Continuous (rhoMap n m D) := by
  have h1 : Continuous ((AddMonoidHom.id (Fin n → ℝ)).prodMap (expMap m)) :=
    continuous_id.prodMap (continuous_expMap m)
  exact h1.prodMk continuous_const

theorem isOpenMap_rhoMap : IsOpenMap (rhoMap n m D) := by
  have h1 : IsOpenMap ((AddMonoidHom.id (Fin n → ℝ)).prodMap (expMap m)) :=
    IsOpenMap.id.prodMap (isOpenMap_expMap m)
  have h2 : IsOpenMap fun a : (Fin n → ℝ) × (Fin m → AddCircle (1 : ℝ)) => (a, (0 : D)) := by
    intro U hU
    have : (fun a => (a, (0 : D))) '' U = U ×ˢ {0} := by
      ext ⟨a, d⟩
      simp only [mem_image, Prod.mk.injEq, mem_prod, mem_singleton_iff]
      constructor
      · rintro ⟨x, hx, rfl, rfl⟩
        exact ⟨hx, rfl⟩
      · rintro ⟨ha, rfl⟩
        exact ⟨a, ha, rfl, rfl⟩
    rw [this]
    exact hU.prod (isOpen_discrete _)
  exact h2.comp h1

/-- Morris, Topology Without Tears, Corollary A5.5.18 (TP-549), first part. A closed subgroup `G` of
`ℝⁿ × Tᵐ × D`, `D` a discrete abelian group, is topologically isomorphic to `ℝᵃ × Tᵇ × D'` with `D'`
a discrete abelian group and `a + b ≤ n + m`. -/
@[kb "morris2024" "Corollary A5.5.18, p. 547"]
theorem closedSubgroup_real_circle_discrete
    (G : AddSubgroup (((Fin n → ℝ) × (Fin m → AddCircle (1 : ℝ))) × D))
    (hG : IsClosed (G : Set (((Fin n → ℝ) × (Fin m → AddCircle (1 : ℝ))) × D))) :
    ∃ (a b : ℕ) (D' : Type) (_ : AddCommGroup D') (_ : TopologicalSpace D'),
      DiscreteTopology D' ∧ a + b ≤ n + m ∧
        Nonempty (G ≃ₜ+ (((Fin a → ℝ) × (Fin b → AddCircle (1 : ℝ))) × D')) := by
  classical
  set ρ := rhoMap n m D
  let P : AddSubgroup ((Fin n → ℝ) × (Fin m → ℝ)) := G.comap ρ
  have hP : IsClosed (P : Set ((Fin n → ℝ) × (Fin m → ℝ))) := hG.preimage continuous_rhoMap
  obtain ⟨V, hVP, Ω, hΩ, hΩV⟩ := exists_open_subspace P hP
  -- `ρ` restricted to `V`, as a map into `G`
  let φ : V →+ G :=
    { toFun := fun v => ⟨ρ (v : (Fin n → ℝ) × (Fin m → ℝ)), hVP v v.2⟩
      map_zero' := Subtype.ext (map_zero ρ)
      map_add' := fun v w => Subtype.ext (map_add ρ (v : (Fin n → ℝ) × (Fin m → ℝ)) w) }
  have hφc : Continuous φ :=
    (continuous_rhoMap.comp continuous_subtype_val).subtype_mk _
  have hφo : IsOpenMap φ := by
    -- `ρ` restricted to `P = ρ⁻¹(G)` is open onto `G`, and `V` is open in `P`
    intro U hU
    obtain ⟨U', hU'o, rfl⟩ := isOpen_induced_iff.1 hU
    have : φ '' (((↑) : V → (Fin n → ℝ) × (Fin m → ℝ)) ⁻¹' U') =
        ((↑) : G → _) ⁻¹' (ρ '' (U' ∩ Ω)) := by
      ext ⟨x, hx⟩
      constructor
      · rintro ⟨v, hv, hvx⟩
        have hxv : ρ v = x := congrArg Subtype.val hvx
        exact ⟨v, ⟨hv, (hΩV v (hVP v v.2)).2 v.2⟩, hxv⟩
      · rintro ⟨y, ⟨hyU, hyΩ⟩, hyx⟩
        have hyP : y ∈ P := by
          show ρ y ∈ G
          rw [hyx]
          exact hx
        exact ⟨⟨y, (hΩV y hyP).1 hyΩ⟩, hyU, Subtype.ext hyx⟩
    rw [this]
    exact (isOpenMap_rhoMap _ (hU'o.inter hΩ)).preimage continuous_subtype_val
  have hφk : IsClosed (φ.ker : Set V) := by
    have : (φ.ker : Set V) = φ ⁻¹' {0} := rfl
    rw [this]
    exact isClosed_singleton.preimage hφc
  obtain ⟨a, b, hab, hro, hdiv, ⟨e⟩⟩ := range_equiv_of_isOpenMap φ hφc hφo hφk
  obtain ⟨s, hs⟩ := exists_continuousAddEquiv_prod_quotient φ.range hro hdiv
  have hdim : Module.finrank ℝ V ≤ n + m := by
    calc Module.finrank ℝ V ≤ Module.finrank ℝ ((Fin n → ℝ) × (Fin m → ℝ)) :=
          Submodule.finrank_le V
      _ = n + m := by simp
  have : DiscreteTopology (G ⧸ φ.range) := QuotientAddGroup.discreteTopology hro
  exact ⟨a, b, G ⧸ φ.range, inferInstance, inferInstance, inferInstance, hab.trans hdim,
    ⟨s.trans (prodCAE e (ContinuousAddEquiv.refl _))⟩⟩

/-- Morris, Topology Without Tears, Corollary A5.5.18 (TP-549), second part. For a closed subgroup
`G` of `ℝⁿ × Tᵐ × D`, `D` a discrete abelian group, the quotient group `(ℝⁿ × Tᵐ × D) / G` is
topologically isomorphic to `ℝᶜ × Tᵈ × D''` with `D''` a discrete abelian group and `c + d ≤ n + m`. -/
@[kb "morris2024" "Corollary A5.5.18, p. 547"]
theorem quotient_closedSubgroup_real_circle_discrete
    (G : AddSubgroup (((Fin n → ℝ) × (Fin m → AddCircle (1 : ℝ))) × D))
    (hG : IsClosed (G : Set (((Fin n → ℝ) × (Fin m → AddCircle (1 : ℝ))) × D))) :
    ∃ (c d : ℕ) (D'' : Type) (_ : AddCommGroup D'') (_ : TopologicalSpace D''),
      DiscreteTopology D'' ∧ c + d ≤ n + m ∧
        Nonempty (((((Fin n → ℝ) × (Fin m → AddCircle (1 : ℝ))) × D) ⧸ G) ≃ₜ+
          (((Fin c → ℝ) × (Fin d → AddCircle (1 : ℝ))) × D'')) := by
  classical
  set ρ := rhoMap n m D
  let φ := (QuotientAddGroup.mk' G).comp ρ
  have hφc : Continuous φ := QuotientAddGroup.continuous_mk.comp continuous_rhoMap
  have hφo : IsOpenMap φ := QuotientAddGroup.isOpenMap_coe.comp isOpenMap_rhoMap
  have hφk : IsClosed (φ.ker : Set ((Fin n → ℝ) × (Fin m → ℝ))) := by
    have : (φ.ker : Set ((Fin n → ℝ) × (Fin m → ℝ))) = ρ ⁻¹' G := by
      ext x
      simp [φ, QuotientAddGroup.eq_zero_iff]
    rw [this]
    exact hG.preimage continuous_rhoMap
  obtain ⟨c, d, hcd, hro, hdiv, ⟨e⟩⟩ := range_equiv_of_isOpenMap φ hφc hφo hφk
  obtain ⟨s, hs⟩ := exists_continuousAddEquiv_prod_quotient φ.range hro hdiv
  have hdim : Module.finrank ℝ ((Fin n → ℝ) × (Fin m → ℝ)) = n + m := by simp
  have : DiscreteTopology (((((Fin n → ℝ) × (Fin m → AddCircle (1 : ℝ))) × D) ⧸ G) ⧸ φ.range) :=
    QuotientAddGroup.discreteTopology hro
  exact ⟨c, d, _, inferInstance, inferInstance, inferInstance, hdim ▸ hcd,
    ⟨s.trans (prodCAE e (ContinuousAddEquiv.refl _))⟩⟩

end Main

end UndergradKB.Topology
