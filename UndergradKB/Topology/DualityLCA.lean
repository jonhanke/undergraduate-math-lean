import UndergradKB.Topology.LCASeparation
import UndergradKB.Topology.DualityCompact
import UndergradKB.Topology.GroupsMore
import UndergradKB.Topology.Characters
import UndergradKB.Common.Attr

/-!
# Multiples and torsion in LCA groups, and small neighbourhoods in compact groups

Morris, Topology Without Tears, Appendix 5: Proposition A5.15.13 (TP-634), Theorem A5.15.14 (TP-635),
Corollary A5.15.16 (TP-636, the part not needing the structure theorem) and Corollary A5.10.4 (TP-583).
-/

open Topology Set Filter Real

set_option linter.unusedSectionVars false

universe u

namespace UndergradKB.Topology

/-! ### TP-634 and TP-635 -/

section Multiples

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G]

theorem mem_nTorsion_iff {Γ : Type*} [CommGroup Γ] (n : ℕ) (γ : Γ) :
    γ ∈ nTorsion Γ n ↔ γ ^ n = 1 := Iff.rfl

/-- Morris, Topology Without Tears, Proposition A5.15.13 (ii) (TP-634), the form
`closure G⁽ⁿ⁾ = Λ(G, Γ₍ₙ₎)`. For a locally compact Hausdorff abelian group `G`, the closure of the
subgroup of `n`-th multiples is exactly the set of elements on which all characters of order dividing
`n` are trivial (the annihilator in `G` of the `n`-torsion of the dual). -/
@[kb "morris2024" "Proposition A5.15.13, p. 612"]
theorem closure_nthPowers_eq_coannihilator_nTorsion (n : ℕ) :
    ((nthPowers G n).topologicalClosure : Set G) =
      {x | ∀ χ ∈ nTorsion (PontryaginDual G) n, χ x = 1} := by
  ext x
  constructor
  · intro hx χ hχ
    have : χ ∈ characterAnnihilator G (nthPowers G n).topologicalClosure := by
      rw [characterAnnihilator_closure_nthPowers]
      exact hχ
    exact this x hx
  · intro hx
    by_contra hxn
    obtain ⟨χ, hχ1, hχ2⟩ := LCA.exists_char_trivial_on_ne_of_LCA
      (nthPowers G n).topologicalClosure (Subgroup.isClosed_topologicalClosure _) hxn
    have : χ ∈ nTorsion (PontryaginDual G) n := by
      rw [← characterAnnihilator_closure_nthPowers]
      exact hχ1
    exact hχ2 (hx χ this)

/-- Morris, Topology Without Tears, Theorem A5.15.14 (TP-635), second part. If the dual group of a
locally compact Hausdorff abelian group `G` is torsion free, then `G⁽ⁿ⁾` is dense in `G` for every
`n ≥ 1`. -/
@[kb "morris2024" "Theorem A5.15.14, p. 613"]
theorem dense_nthPowers_of_dual_torsionFree
    (htf : ∀ (χ : PontryaginDual G) (n : ℕ), 0 < n → χ ^ n = 1 → χ = 1) {n : ℕ} (hn : 0 < n) :
    Dense ((nthPowers G n : Subgroup G) : Set G) := by
  rw [dense_iff_closure_eq]
  have h := closure_nthPowers_eq_coannihilator_nTorsion (G := G) n
  rw [Subgroup.topologicalClosure_coe] at h
  rw [h]
  ext x
  simp only [mem_ofPred_eq, mem_univ, iff_true]
  intro χ hχ
  have : χ = 1 := htf χ n hn hχ
  rw [this]
  rfl

theorem divisible_of_dual_torsionFree_of_isClosed_nthPowers
    (htf : ∀ (χ : PontryaginDual G) (n : ℕ), 0 < n → χ ^ n = 1 → χ = 1)
    (hcl : ∀ n : ℕ, 0 < n → IsClosed ((nthPowers G n : Subgroup G) : Set G)) :
    IsDivisibleMulGroup G := by
  intro n hn x
  have hd := dense_nthPowers_of_dual_torsionFree htf hn
  have : x ∈ ((nthPowers G n : Subgroup G) : Set G) := by
    rw [← (hcl n hn).closure_eq, hd.closure_eq]
    trivial
  obtain ⟨y, hy⟩ := this
  exact ⟨y, hy⟩

/-- Morris, Topology Without Tears, Theorem A5.15.14 (TP-635), the equivalence for compact groups. A
compact Hausdorff abelian group is divisible iff its dual group is torsion free. -/
@[kb "morris2024" "Theorem A5.15.14, p. 613"]
theorem isDivisibleMulGroup_iff_dual_torsionFree_of_compact [CompactSpace G] :
    IsDivisibleMulGroup G ↔
      ∀ (χ : PontryaginDual G) (n : ℕ), 0 < n → χ ^ n = 1 → χ = 1 := by
  constructor
  · intro hG χ n hn h
    exact dual_torsionFree_of_divisible hG n hn χ h
  · intro htf
    refine divisible_of_dual_torsionFree_of_isClosed_nthPowers htf fun n _ => ?_
    have : ((nthPowers G n : Subgroup G) : Set G) = Set.range (fun x : G => x ^ n) := by
      ext y
      exact Iff.rfl
    rw [this]
    exact (isCompact_range (continuous_pow n)).isClosed

/-- Morris, Topology Without Tears, Theorem A5.15.14 (TP-635), the equivalence for discrete groups. A
discrete abelian group is divisible iff its dual group is torsion free. -/
@[kb "morris2024" "Theorem A5.15.14, p. 613"]
theorem isDivisibleMulGroup_iff_dual_torsionFree_of_discrete [DiscreteTopology G] :
    IsDivisibleMulGroup G ↔
      ∀ (χ : PontryaginDual G) (n : ℕ), 0 < n → χ ^ n = 1 → χ = 1 := by
  constructor
  · intro hG χ n hn h
    exact dual_torsionFree_of_divisible hG n hn χ h
  · intro htf
    exact divisible_of_dual_torsionFree_of_isClosed_nthPowers htf fun n _ => isClosed_discrete _

/-! ### TP-636 -/

/-- In a connected topological group every character of finite order is trivial, so the dual
group is torsion free. -/
theorem dual_torsionFree_of_connectedSpace [ConnectedSpace G] (χ : PontryaginDual G) (n : ℕ)
    (hn : 0 < n) (h : χ ^ n = 1) : χ = 1 := by
  let T : Set Circle := {z | z ^ n = 1}
  have hfin : T.Finite := by
    have hsub : T ⊆ (fun z : Circle => (z : ℂ)) ⁻¹'
        (Polynomial.nthRootsFinset n (1 : ℂ) : Set ℂ) := by
      intro z hz
      have hz' : z ^ n = 1 := hz
      show (z : ℂ) ∈ (Polynomial.nthRootsFinset n (1 : ℂ) : Set ℂ)
      rw [Finset.mem_coe, Polynomial.mem_nthRootsFinset hn, ← Circle.coe_pow, hz']
      rfl
    exact (Set.Finite.preimage (fun a _ b _ h => Subtype.ext h) (Finset.finite_toSet _)).subset hsub
  haveI : Finite T := hfin.to_subtype
  have hmaps : MapsTo (χ : G → Circle) univ T := by
    intro y _
    show (χ y) ^ n = 1
    have e : (χ ^ n) y = 1 := congrArg (fun ψ : PontryaginDual G => ψ y) h
    exact (dual_pow_apply G χ n y).symm.trans e
  refine PontryaginDual.ext fun x => ?_
  have := isPreconnected_univ.constant_of_mapsTo
    (isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology T))
    (f := (χ : G → Circle)) χ.continuous.continuousOn hmaps (mem_univ x) (mem_univ 1)
  rw [this]
  exact map_one χ

/-- Morris, Topology Without Tears, Corollary A5.15.16 (TP-636), the part not needing the structure
theorem. For a connected locally compact Hausdorff abelian group `G`, the subgroup `G⁽ⁿ⁾` of `n`-th
multiples is dense for every `n ≥ 1`. -/
@[kb "morris2024" "Corollary A5.15.16, p. 613"]
theorem dense_nthPowers_of_connectedSpace [ConnectedSpace G] {n : ℕ} (hn : 0 < n) :
    Dense ((nthPowers G n : Subgroup G) : Set G) :=
  dense_nthPowers_of_dual_torsionFree (fun χ n hn h => dual_torsionFree_of_connectedSpace χ n hn h) hn

/-- Morris, Topology Without Tears, Corollary A5.15.16 (TP-636) for compact groups: a connected
compact Hausdorff abelian group is divisible. -/
@[kb "morris2024" "Corollary A5.15.16, p. 613"]
theorem isDivisibleMulGroup_of_connectedSpace_of_compact [CompactSpace G] [ConnectedSpace G] :
    IsDivisibleMulGroup G :=
  isDivisibleMulGroup_iff_dual_torsionFree_of_compact.2
    fun χ n hn h => dual_torsionFree_of_connectedSpace χ n hn h

end Multiples

/-! ### TP-583: small closed subgroups with quotient in a torus -/

section SmallSubgroups

variable {K : Type u} [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [T2Space K]

/-- Finitely many characters whose common kernel lies in a given neighbourhood of `1`. -/
theorem exists_finite_chars_kernel_subset {U : Set K} (hU : U ∈ 𝓝 (1 : K)) :
    ∃ (n : ℕ) (χ : Fin n → PontryaginDual K), ∀ y, (∀ i, χ i y = 1) → y ∈ U := by
  classical
  have h1W : (1 : K) ∈ interior U := mem_interior_iff_mem_nhds.2 hU
  have hC : IsCompact (interior U)ᶜ := isOpen_interior.isClosed_compl.isCompact
  have hne : ∀ x : ((interior U)ᶜ : Set K), (x : K) ≠ 1 := fun x h => x.2 (h ▸ h1W)
  choose χ hχ using fun x : ((interior U)ᶜ : Set K) => exists_char_ne_one_of_compact (hne x)
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun x : ((interior U)ᶜ : Set K) => {y : K | χ x y ≠ 1})
    (fun x => (isClosed_singleton.preimage (χ x).continuous).isOpen_compl)
    (fun y hy => mem_iUnion.2 ⟨⟨y, hy⟩, hχ ⟨y, hy⟩⟩)
  refine ⟨t.card, fun i => χ (t.equivFin.symm i).1, fun y hy => ?_⟩
  apply interior_subset
  by_contra hyW
  have := ht hyW
  simp only [mem_iUnion, mem_ofPred_eq] at this
  obtain ⟨x, hx, hxy⟩ := this
  apply hxy
  have := hy (t.equivFin ⟨x, hx⟩)
  simpa using this

/-- Morris, Topology Without Tears, Corollary A5.10.4 (TP-583), first part. Every neighbourhood `U`
of the identity in a compact Hausdorff abelian group `K` contains a closed subgroup `H` such that
`K / H` is topologically isomorphic to a closed subgroup of the torus `Tⁿ` (the map `K / H → Tⁿ` is a
continuous injective homomorphism and a closed embedding); `H` is the common kernel of finitely many
characters. -/
@[kb "morris2024" "Corollary A5.10.4, p. 573"]
theorem exists_closedSubgroup_sub_nhds_quotient_closedEmbedding {U : Set K} (hU : U ∈ 𝓝 (1 : K)) :
    ∃ (H : Subgroup K) (n : ℕ) (e : K ⧸ H →ₜ* (Fin n → Circle)),
      IsClosed (H : Set K) ∧ (H : Set K) ⊆ U ∧ Function.Injective e ∧ IsClosedEmbedding e := by
  obtain ⟨n, χ, hχ⟩ := exists_finite_chars_kernel_subset hU
  let f : K →* (Fin n → Circle) := MonoidHom.pi fun i => (χ i : K →* Circle)
  have hcont : Continuous f := continuous_pi fun i => (χ i).continuous
  let e0 : K ⧸ f.ker →* (Fin n → Circle) := QuotientGroup.kerLift f
  have he0c : Continuous e0 := by
    have hq : IsQuotientMap (QuotientGroup.mk' f.ker) := QuotientGroup.isQuotientMap_mk f.ker
    exact hq.continuous_iff.2 hcont
  have hinj : Function.Injective e0 := QuotientGroup.kerLift_injective f
  refine ⟨f.ker, n, ⟨e0, he0c⟩, ?_, ?_, hinj, he0c.isClosedEmbedding hinj⟩
  · exact (isClosed_singleton.preimage hcont : IsClosed (f ⁻¹' {1}))
  · intro x hx
    apply hχ
    intro i
    exact congrFun (MonoidHom.mem_ker.1 hx) i

end SmallSubgroups

end UndergradKB.Topology
