import UndergradKB.Topology.DualityExtension2
import UndergradKB.Topology.DualityDiscrete2
import UndergradKB.Topology.ClassicalDuals
import UndergradKB.Topology.GroupsWave2g
import UndergradKB.Topology.TopGroups
import UndergradKB.Common.Attr

/-!
# Plumbing for the duality theorem for LCA groups (Morris, Appendix 5.13)

* duality is invariant under topological isomorphism, and holds for `ℝᵃ × ℤᵇ × Tᶜ × F` with `F` discrete;
* Proposition A5.13.2 (TP-604): the dual sequence of `K → G → G/K` for a compact subgroup `K`;
* a multiplicative Proposition A5.3.8 (an open divisible subgroup splits off);
* the five-lemma Proposition A5.13.4 (TP-606).
-/

open Set Filter
open scoped Topology

universe u

namespace UndergradKB.Topology

/-! ### Duality is invariant under isomorphism and holds for the elementary groups -/

section Invariance

variable {G H : Type*} [CommGroup G] [CommGroup H] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]

/-- Duality transfers along a topological isomorphism. -/
theorem DualityHolds.of_continuousMulEquiv (e : G ≃ₜ* H) (h : DualityHolds H) : DualityHolds G := by
  obtain ⟨d, hd⟩ := h
  refine ⟨(e.trans d).trans (dualCongr (dualCongr e)).symm, fun g χ => ?_⟩
  show ((dualCongr (dualCongr e)).symm (d (e g))) χ = χ g
  rw [dualCongr_symm_apply]
  show (d (e g)) ((dualCongr e) χ) = χ g
  rw [hd]
  show χ (e.symm (e g)) = χ g
  rw [e.symm_apply_apply]

end Invariance

section Reorder

variable (A B C : Type*) [CommGroup A] [CommGroup B] [CommGroup C] [TopologicalSpace A]
  [TopologicalSpace B] [TopologicalSpace C]

/-- Swap the last two factors of `(A × B) × C`. -/
def swapLastTwo : ((A × B) × C) ≃ₜ* ((A × C) × B) where
  toFun p := ((p.1.1, p.2), p.1.2)
  invFun p := ((p.1.1, p.2), p.1.2)
  left_inv p := rfl
  right_inv p := rfl
  map_mul' p q := rfl
  continuous_toFun :=
    ((continuous_fst.comp continuous_fst).prodMk continuous_snd).prodMk
      (continuous_snd.comp continuous_fst)
  continuous_invFun :=
    ((continuous_fst.comp continuous_fst).prodMk continuous_snd).prodMk
      (continuous_snd.comp continuous_fst)

end Reorder

/-- Morris, Topology Without Tears, Corollary A5.9.4 (TP-575), in the order used in the structure theory:
`((ℝᵃ × ℤᵇ) × Tᶜ) × F` with `F` a discrete (for instance finite) abelian group satisfies the duality
property. -/
theorem dualityHolds_real_int_circle_discrete (a b c : ℕ) (F : Type*) [CommGroup F]
    [TopologicalSpace F] [DiscreteTopology F] :
    DualityHolds ((((Fin a → Multiplicative ℝ) × (Fin b → Multiplicative ℤ)) × (Fin c → Circle)) × F) := by
  haveI : IsTopologicalGroup F := ⟨⟩
  let e : ((((Fin a → Multiplicative ℝ) × (Fin b → Multiplicative ℤ)) × (Fin c → Circle)) × F) ≃ₜ*
      ((((Fin a → Multiplicative ℝ) × (Fin c → Circle)) × (Fin b → Multiplicative ℤ)) × F) :=
    prodCongr (swapLastTwo _ _ _) (ContinuousMulEquiv.refl F)
  exact DualityHolds.of_continuousMulEquiv e (dualityHolds_real_circle_int_pow_discrete F a c b)

/-! ### The dual sequence of a compact subgroup (TP-604) -/

section CompactSubgroup

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G]

/-- The quotient map `G → G ⧸ K` as a continuous homomorphism. -/
def quotHom (K : Subgroup G) : G →ₜ* G ⧸ K := ⟨QuotientGroup.mk' K, QuotientGroup.continuous_mk⟩

/-- Precomposition with the quotient map is an embedding for the compact-open topologies: a compact
subset of `G ⧸ K` lifts to a compact subset of `G`. -/
theorem isInducing_precomp_quotient (K : Subgroup G) (hK : IsCompact (K : Set G)) :
    Topology.IsInducing
      (fun ψ : C(G ⧸ K, Circle) => ψ.comp (⟨QuotientGroup.mk' K, QuotientGroup.continuous_mk⟩ :
        C(G, G ⧸ K))) := by
  haveI : IsClosed (K : Set G) := hK.isClosed
  refine ⟨le_antisymm ?_ ?_⟩
  · exact continuous_iff_le_induced.1 (ContinuousMap.continuous_precomp _)
  · rw [ContinuousMap.compactOpen_eq]
    apply le_generateFrom
    rintro _ ⟨C', hC', U, hU, rfl⟩
    obtain ⟨C, hC, hC'C⟩ := LCA.exists_isCompact_lift K hC'
    have hS : IsCompact (C ∩ (QuotientGroup.mk : G → G ⧸ K) ⁻¹' C') :=
      hC.inter_right (hC'.isClosed.preimage QuotientGroup.continuous_mk)
    have himg : (QuotientGroup.mk : G → G ⧸ K) '' (C ∩ (QuotientGroup.mk : G → G ⧸ K) ⁻¹' C') = C' := by
      ext y
      constructor
      · rintro ⟨s, ⟨-, hs⟩, rfl⟩
        exact hs
      · intro hy
        obtain ⟨c, hc, rfl⟩ := hC'C hy
        exact ⟨c, ⟨hc, hy⟩, rfl⟩
    rw [isOpen_induced_iff]
    refine ⟨{φ : C(G, Circle) | Set.MapsTo φ (C ∩ (QuotientGroup.mk : G → G ⧸ K) ⁻¹' C') U},
      ContinuousMap.isOpen_setOfPred_mapsTo hS hU, ?_⟩
    ext ψ
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    constructor
    · intro h y hy
      rw [← himg] at hy
      obtain ⟨s, hs, rfl⟩ := hy
      exact h hs
    · intro h s hs
      exact h (himg ▸ ⟨s, hs, rfl⟩)

/-- Morris, Topology Without Tears, Proposition A5.13.2 (TP-604). Let `K` be a compact subgroup of a
locally compact Hausdorff abelian group `G`. For the dual sequence `0 ← K^ ← G^ ← (G/K)^ ← 0`:
restriction `G^ → K^` is onto and open (`K^` is discrete); `(G/K)^ → G^` is injective with image the
annihilator of `K`, which is the kernel of the restriction, and it is a topological embedding onto that
open subgroup (so an open map). -/
@[kb "morris2024" "Proposition A5.13.2, p. 592"]
theorem dual_sequence_compact_subgroup (K : Subgroup G) (hK : IsCompact (K : Set G)) :
    (Function.Surjective (PontryaginDual.map (LCA.inclHom K)) ∧
        IsOpenMap (PontryaginDual.map (LCA.inclHom K))) ∧
      Function.Injective (PontryaginDual.map (quotHom K)) ∧
      Set.range (PontryaginDual.map (quotHom K)) = (LCA.annih K : Set (PontryaginDual G)) ∧
      (LCA.annih K : Set (PontryaginDual G)) = PontryaginDual.map (LCA.inclHom K) ⁻¹' {1} ∧
      Topology.IsOpenEmbedding (PontryaginDual.map (quotHom K)) := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : IsClosed (K : Set G) := hK.isClosed
  have hsurj : Function.Surjective (PontryaginDual.map (LCA.inclHom K)) := by
    intro ψ
    obtain ⟨χ, hχ⟩ := exists_extend_char_of_compact_subgroup_LCA K hK ψ
    exact ⟨χ, PontryaginDual.ext fun k => hχ k⟩
  have hopenmap : IsOpenMap (PontryaginDual.map (LCA.inclHom K)) := fun s _ => isOpen_discrete _
  have hinj : Function.Injective (PontryaginDual.map (quotHom K)) :=
    PontryaginDual_map_injective_of_surjective (quotHom K) (QuotientGroup.mk'_surjective K)
  have hrange : Set.range (PontryaginDual.map (quotHom K)) = (LCA.annih K : Set (PontryaginDual G)) := by
    ext χ
    constructor
    · rintro ⟨ψ, rfl⟩ k hk
      show ψ (QuotientGroup.mk k) = 1
      rw [(QuotientGroup.eq_one_iff k).2 hk]
      exact map_one ψ
    · intro hχ
      obtain ⟨ψ, hψ⟩ := LCA.exists_char_quotient_of_trivial K χ hχ
      exact ⟨ψ, PontryaginDual.ext fun y => hψ y⟩
  have hker : (LCA.annih K : Set (PontryaginDual G)) =
      PontryaginDual.map (LCA.inclHom K) ⁻¹' {1} := by
    ext χ
    constructor
    · intro hχ
      exact PontryaginDual.ext fun k => hχ k k.2
    · intro hχ k hk
      exact DFunLike.congr_fun (Set.mem_singleton_iff.1 hχ) ⟨k, hk⟩
  have hopen : IsOpen (Set.range (PontryaginDual.map (quotHom K))) := by
    rw [hrange, hker]
    exact (isOpen_discrete _).preimage (PontryaginDual.map (LCA.inclHom K)).continuous
  -- the embedding
  have hind : Topology.IsInducing (PontryaginDual.map (quotHom K)) := by
    have h1 := ContinuousMonoidHom.isInducing_toContinuousMap G Circle
    have h2 := ContinuousMonoidHom.isInducing_toContinuousMap (G ⧸ K) Circle
    have h3 := (isInducing_precomp_quotient K hK).comp h2
    refine Topology.IsInducing.of_comp (PontryaginDual.map (quotHom K)).continuous h1.continuous ?_
    exact h3
  exact ⟨⟨hsurj, hopenmap⟩, hinj, hrange, hker,
    { toIsEmbedding := ⟨hind, hinj⟩, isOpen_range := hopen }⟩

end CompactSubgroup

/-! ### Open divisible subgroups split off (multiplicative form of TP-530) -/

section Split

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Morris, Topology Without Tears, Proposition A5.3.8 (TP-530), multiplicative form. If `H` is an open
divisible subgroup of an abelian topological group `G` (every element of `H` has an `n`-th root in `H`),
then `G` is topologically isomorphic to `H × G ⧸ H` (the second factor is discrete), the second
coordinate being the quotient map. -/
@[kb "morris2024" "Proposition A5.3.8, p. 532"]
theorem exists_continuousMulEquiv_prod_quotient (H : Subgroup G) (hH : IsOpen (H : Set G))
    (hdiv : ∀ n : ℕ, 0 < n → ∀ h : H, ∃ x : H, x ^ n = h) :
    ∃ e : G ≃ₜ* (H × (G ⧸ H)), ∀ g : G, (e g).2 = QuotientGroup.mk g := by
  have hdivA : IsDivisibleGroup (Additive H) := fun n hn d => by
    obtain ⟨x, hx⟩ := hdiv n hn (Additive.toMul d)
    refine ⟨Additive.ofMul x, ?_⟩
    have := congrArg Additive.ofMul hx
    rw [ofMul_pow] at this
    exact this
  let Hs : AddSubgroup (Additive G) := Subgroup.toAddSubgroup H
  let φ : Hs →+ Additive H :=
    { toFun := fun x => Additive.ofMul ⟨Additive.toMul x.1, x.2⟩
      map_zero' := rfl
      map_add' := fun x y => rfl }
  obtain ⟨r, hr⟩ := exists_addMonoidHom_extension hdivA Hs φ
  let r' : G →* H :=
    { toFun := fun g => Additive.toMul (r (Additive.ofMul g))
      map_one' := by
        show Additive.toMul (r 0) = 1
        rw [map_zero]; rfl
      map_mul' := fun a b => by
        show Additive.toMul (r (Additive.ofMul (a * b))) = _
        rw [ofMul_mul, map_add]; rfl }
  have hr' : ∀ h : H, r' h = h := fun h =>
    congrArg Additive.toMul (hr ⟨Additive.ofMul (h : G), h.2⟩)
  have rcont : Continuous r' := by
    refine continuous_of_continuousAt_one r' ?_
    have hc : ContinuousOn r' (H : Set G) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have : (H : Set G).domRestrict r' = id := by
        funext h; exact hr' ⟨h.1, h.2⟩
      rw [this]; exact continuous_id
    exact hc.continuousAt (hH.mem_nhds H.one_mem)
  have : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hH
  let φ2 : G →* G := MonoidHom.id G / H.subtype.comp r'
  have hφ2 : ∀ x ∈ H, φ2 x = 1 := by
    intro x hx
    have := hr' ⟨x, hx⟩
    simp [φ2, this]
  let s : G ⧸ H →* G := QuotientGroup.lift H φ2 hφ2
  have hs : ∀ g : G, s (QuotientGroup.mk g) = g / r' g := fun g => rfl
  let e : G ≃* (H × (G ⧸ H)) :=
    { toFun := fun g => (r' g, QuotientGroup.mk g)
      invFun := fun p => (p.1 : G) * s p.2
      left_inv := fun g => by
        show ((r' g : H) : G) * s (QuotientGroup.mk g) = g
        rw [hs]; simp
      right_inv := by
        rintro ⟨h, q⟩
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
        refine Prod.ext ?_ ?_
        · show r' ((h : G) * s (QuotientGroup.mk g)) = h
          rw [hs, map_mul, map_div, hr' h, hr' (r' g)]
          simp
        · show QuotientGroup.mk ((h : G) * s (QuotientGroup.mk g)) = QuotientGroup.mk g
          rw [QuotientGroup.eq, hs]
          have : ((h : G) * (g / (r' g : G)))⁻¹ * g = (h : G)⁻¹ * (r' g : G) := by
            simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
            rw [mul_comm (r' g : G), mul_assoc, mul_assoc, mul_comm (g⁻¹), mul_assoc, mul_inv_cancel_right]
            rw [mul_comm]
          rw [this]
          exact H.mul_mem (H.inv_mem h.2) (r' g).2
      map_mul' := fun a b => by
        ext <;> simp }
  refine ⟨{ toMulEquiv := e, continuous_toFun := ?_, continuous_invFun := ?_ }, fun g => rfl⟩
  · exact rcont.prodMk QuotientGroup.continuous_mk
  · show Continuous (fun p : H × (G ⧸ H) => (p.1 : G) * s p.2)
    exact (continuous_subtype_val.comp continuous_fst).mul
      ((continuous_of_discreteTopology (f := s)).comp continuous_snd)

end Split

/-! ### Five lemma (TP-606) -/

section FiveLemma

variable {A B C D E F : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
  [AddCommGroup E] [AddCommGroup F]

/-- Morris, Topology Without Tears, Proposition A5.13.4 (TP-606). In a commutative diagram with exact
rows `0 → A → B → C → 0` and `0 → D → E → F → 0`, if the outer maps `f₅` and `f₇` are algebraic
isomorphisms then so is the middle map `f₆`. (The statement is purely algebraic, so it holds in
particular for abelian topological groups and continuous homomorphisms.) -/
@[kb "morris2024" "Proposition A5.13.4, p. 594"]
theorem five_lemma_bijective (f₁ : A →+ B) (f₂ : B →+ C) (f₃ : D →+ E) (f₄ : E →+ F)
    (f₅ : A →+ D) (f₆ : B →+ E) (f₇ : C →+ F)
    (h₁ : Function.Injective f₁) (h₂ : Function.Surjective f₂) (h₃ : f₂.ker = f₁.range)
    (h₁' : Function.Injective f₃) (h₂' : Function.Surjective f₄) (h₃' : f₄.ker = f₃.range)
    (c₁ : ∀ a, f₃ (f₅ a) = f₆ (f₁ a)) (c₂ : ∀ b, f₄ (f₆ b) = f₇ (f₂ b))
    (h₅ : Function.Bijective f₅) (h₇ : Function.Bijective f₇) : Function.Bijective f₆ := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro b hb
    have h0 : f₂ b = 0 := by
      apply h₇.1
      rw [← c₂, hb, map_zero, map_zero]
    have hb' : b ∈ f₁.range := by rw [← h₃]; exact h0
    obtain ⟨a, rfl⟩ := hb'
    have : f₃ (f₅ a) = 0 := by rw [c₁, hb]
    have h5 : f₅ a = 0 := by
      apply h₁'
      rw [this, map_zero]
    have : a = 0 := by
      apply h₅.1
      rw [h5, map_zero]
    rw [this, map_zero]
  · intro e
    obtain ⟨c, hc⟩ := h₇.2 (f₄ e)
    obtain ⟨b, rfl⟩ := h₂ c
    have hker : e - f₆ b ∈ f₄.ker := by
      rw [AddMonoidHom.mem_ker, map_sub, c₂, hc, sub_self]
    rw [h₃'] at hker
    obtain ⟨d, hd⟩ := hker
    obtain ⟨a, rfl⟩ := h₅.2 d
    refine ⟨b + f₁ a, ?_⟩
    rw [map_add, ← c₁, hd]
    abel

end FiveLemma

end UndergradKB.Topology
