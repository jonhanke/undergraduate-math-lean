import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.GroupTheory.QuotientGroup.Basic
import UndergradKB.Common.Attr

/-! # Judson–Beezer, chapters 9-11: direct products, factor groups, homomorphisms

Internal direct products (9.2), the order of `ℤ ⧸ nℤ` (10.1), kernels of power maps, the exponential
map onto the circle, cyclic groups up to isomorphism, and the correspondence theorem (11).
-/

open scoped Function

namespace UndergradKB.AbstractAlgebra

/-! ## Section 9.2: internal direct products -/

section InternalDirectProduct

variable {G : Type*} [Group G]

/-- A group `G` is the internal direct product of two subgroups `H` and `K`: `G = H K`,
`H ∩ K = 1`, and every element of `H` commutes with every element of `K`. (Bridging definition
for the book's unnumbered definition.) -/
@[kb "judson2026" "Definition (internal direct product), p. 137"]
structure IsInternalDirectProduct₂ (H K : Subgroup G) : Prop where
  sup_eq_top : H ⊔ K = ⊤
  disjoint : Disjoint H K
  commute : ∀ h ∈ H, ∀ k ∈ K, Commute h k

/-- AA-139 (n factors). `G` is the internal direct product of the family `H i`: elements of
different factors commute, each factor meets the join of the others trivially (`iSupIndep`),
and the join of all factors is `G`. -/
@[kb "judson2026" "Definition (internal direct product), p. 138"]
structure IsInternalDirectProduct {ι : Type*} (H : ι → Subgroup G) : Prop where
  commute : Pairwise fun i j => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y
  iSupIndep : iSupIndep H
  iSup_eq_top : ⨆ i, H i = ⊤

/-- AA-140. If `G` is the internal direct product of `H` and `K`, then `G ≅ H × K`. -/
@[kb "judson2026" "Theorem 9.2.15, p. 137"]
noncomputable def internalDirectProductEquiv₂ {H K : Subgroup G}
    (h : IsInternalDirectProduct₂ H K) : H × K ≃* G :=
  have hc : ∀ (m : H) (n : K), Commute (H.subtype m) (K.subtype n) :=
    fun a b => h.commute a a.2 b b.2
  MulEquiv.ofBijective
    (MonoidHom.noncommCoprod H.subtype K.subtype hc)
    ⟨by
      rw [MonoidHom.noncommCoprod_injective]
      refine ⟨H.subtype_injective, K.subtype_injective, ?_⟩
      simpa using h.disjoint,
     by
      rw [← MonoidHom.range_eq_top, MonoidHom.noncommCoprod_range]
      simpa using h.sup_eq_top⟩

/-- AA-140 (n factors). If `G` is the internal direct product of finitely many subgroups `H i`,
then `∏ H i ≅ G`. -/
@[kb "judson2026" "Theorem 9.2.17, p. 138"]
noncomputable def internalDirectProductEquiv {ι : Type*} [Fintype ι] {H : ι → Subgroup G}
    (h : IsInternalDirectProduct H) : (∀ i, H i) ≃* G :=
  MulEquiv.ofBijective (Subgroup.noncommPiCoprod h.commute)
    ⟨Subgroup.injective_noncommPiCoprod_of_iSupIndep h.iSupIndep,
     by
      rw [← MonoidHom.range_eq_top, Subgroup.noncommPiCoprod_range]
      exact h.iSup_eq_top⟩

/-- Two normal subgroups with trivial intersection and product `G` form an internal direct
product (the usual way the hypotheses of the definition are verified). -/
theorem isInternalDirectProduct₂_of_normal {H K : Subgroup G} [H.Normal] [K.Normal]
    (hd : Disjoint H K) (hs : H ⊔ K = ⊤) : IsInternalDirectProduct₂ H K :=
  ⟨hs, hd, fun h hh k hk => Subgroup.commute_of_normal_of_disjoint H K ‹_› ‹_› hd h k hh hk⟩

/-- AA-140 for normal subgroups: if `H`, `K` are normal, `H ∩ K = 1` and `H K = G`, then
`G ≅ H × K`. -/
@[kb "judson2026" "Theorem 9.2.15, p. 137"]
noncomputable def mulEquivProdOfNormal {H K : Subgroup G} [H.Normal] [K.Normal]
    (hd : Disjoint H K) (hs : H ⊔ K = ⊤) : H × K ≃* G :=
  internalDirectProductEquiv₂ (isInternalDirectProduct₂_of_normal hd hs)

end InternalDirectProduct

/-! ## Corollaries 9.2.10 and 9.2.11: products of `ℤ/nᵢℤ` -/

/-- AA-138. `ZMod (m n) ≃+ ZMod m × ZMod n` exactly when `m` and `n` are coprime. -/
@[kb "judson2026" "Corollary 9.2.10, p. 136"]
theorem zmod_mul_equiv_iff_coprime (m n : ℕ) :
    Nonempty (ZMod (m * n) ≃+ ZMod m × ZMod n) ↔ Nat.Coprime m n := by
  constructor
  · rintro ⟨e⟩
    have : IsAddCyclic (ZMod m × ZMod n) :=
      isAddCyclic_of_surjective e.toAddMonoidHom e.surjective
    have h := (AddGroup.isAddCyclic_prod_iff.1 this).2.2
    simpa [Nat.card_zmod] using h
  · intro h
    exact ⟨(ZMod.chineseRemainder h).toAddEquiv⟩

/-- AA-138 (k factors). `ZMod (∏ aᵢ) ≃+ ∏ ZMod aᵢ` exactly when the `aᵢ` are pairwise coprime. -/
@[kb "judson2026" "Corollary 9.2.10, p. 136"]
theorem zmod_prod_equiv_iff_coprime {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℕ) :
    Nonempty (ZMod (∏ i, a i) ≃+ Π i, ZMod (a i)) ↔ Pairwise (Nat.Coprime on a) := by
  constructor
  · rintro ⟨e⟩ i j hij
    let f : (Π k, ZMod (a k)) →+ ZMod (a i) × ZMod (a j) :=
      AddMonoidHom.prod (Pi.evalAddMonoidHom _ i) (Pi.evalAddMonoidHom _ j)
    have hf : Function.Surjective f := by
      rintro ⟨x, y⟩
      refine ⟨Pi.single i x + Pi.single j y, ?_⟩
      simp [f, hij, hij.symm]
    have : IsAddCyclic (ZMod (a i) × ZMod (a j)) :=
      isAddCyclic_of_surjective (f.comp e.toAddMonoidHom) (hf.comp e.surjective)
    have h := (AddGroup.isAddCyclic_prod_iff.1 this).2.2
    simpa [Nat.card_zmod] using h
  · intro h
    exact ⟨(ZMod.prodEquivPi a h).toAddEquiv⟩

/-- AA-138 (prime-power decomposition). For `m ≠ 0`, `ZMod m` is isomorphic to the product of the
groups `ZMod (p ^ e)` over the prime-power factorization `m = ∏ p ^ e`. -/
@[kb "judson2026" "Corollary 9.2.11, p. 137"]
theorem zmod_equiv_pi_primePow (m : ℕ) (hm : m ≠ 0) :
    Nonempty (ZMod m ≃+ Π p : m.primeFactors, ZMod (p ^ (m.factorization p))) :=
  ⟨(ZMod.equivPi m hm).toAddEquiv⟩

/-! ## Chapter 10 and 11 -/

/-- AA-145. The factor group `ℤ ⧸ nℤ` has `n` elements. -/
@[kb "judson2026" "Example 10.1.6, p. 145"]
theorem card_int_quotient_zmultiples (n : ℕ) :
    Nat.card (ℤ ⧸ AddSubgroup.zmultiples (n : ℤ)) = n := by
  rw [Nat.card_congr (Int.quotientZMultiplesNatEquivZMod n).toEquiv, Nat.card_zmod]

/-- AA-145. `ℤ ⧸ nℤ ≅ ℤ/nℤ` as additive groups. -/
@[kb "judson2026" "Example 10.1.6, p. 145"]
noncomputable def intQuotientZMultiplesEquivZMod (n : ℕ) :
    ℤ ⧸ AddSubgroup.zmultiples (n : ℤ) ≃+ ZMod n :=
  Int.quotientZMultiplesNatEquivZMod n

/-- AA-155. The kernel of `n ↦ n • a` is `ℤ` times the additive order of `a` (so `{0}` when `a` has
infinite order, where `addOrderOf a = 0`). -/
@[kb "judson2026" "Example 11.1.9, p. 153"]
theorem ker_zmultiplesHom {A : Type*} [AddGroup A] (a : A) :
    (zmultiplesHom A a).ker = AddSubgroup.zmultiples (addOrderOf a : ℤ) := by
  ext n
  rw [AddMonoidHom.mem_ker, Int.mem_zmultiples_iff, addOrderOf_dvd_iff_zsmul_eq_zero]
  simp

/-- AA-155, case of infinite order: the kernel is trivial. -/
@[kb "judson2026" "Example 11.1.9, p. 153"]
theorem ker_zmultiplesHom_of_addOrderOf_eq_zero {A : Type*} [AddGroup A] {a : A}
    (h : addOrderOf a = 0) : (zmultiplesHom A a).ker = ⊥ := by
  rw [ker_zmultiplesHom, h]
  simp

/-- AA-155, multiplicative form: `g ^ n = 1` iff `n` lies in `ℤ · orderOf g`
(infinite order is `orderOf g = 0`). -/
@[kb "judson2026" "Example 11.1.9, p. 153"]
theorem zpow_eq_one_iff_mem_zmultiples {G : Type*} [Group G] (g : G) (n : ℤ) :
    g ^ n = 1 ↔ n ∈ AddSubgroup.zmultiples (orderOf g : ℤ) := by
  rw [Int.mem_zmultiples_iff, orderOf_dvd_iff_zpow_eq_one]

/-- AA-155, multiplicative form as a statement about `zpowersHom`. -/
@[kb "judson2026" "Example 11.1.9, p. 153"]
theorem mem_ker_zpowersHom_iff {G : Type*} [Group G] (g : G) (n : Multiplicative ℤ) :
    n ∈ (zpowersHom G g).ker ↔ n.toAdd ∈ AddSubgroup.zmultiples (orderOf g : ℤ) := by
  rw [MonoidHom.mem_ker, ← zpow_eq_one_iff_mem_zmultiples]
  rfl

/-- AA-157. The kernel of `θ ↦ exp(iθ)` from `(ℝ, +)` to the circle group is `2π ℤ`. -/
@[kb "judson2026" "Example 11.1.7, p. 153"]
theorem circle_exp_ker : Circle.expHom.ker = AddSubgroup.zmultiples (2 * Real.pi) := by
  ext x
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_zmultiples_iff]
  have : Circle.expHom x = 0 ↔ Circle.exp x = 1 := Iff.rfl
  rw [this, Circle.exp_eq_one]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [hn, zsmul_eq_mul, mul_comm]⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [← hn, zsmul_eq_mul, mul_comm]⟩

/-- AA-157. `θ ↦ cos θ + i sin θ` is a homomorphism from `(ℝ, +)` onto the circle group. -/
@[kb "judson2026" "Example 11.1.3, p. 152"]
theorem circle_exp_surjective : Function.Surjective Circle.expHom :=
  fun z => ⟨z.val.arg, Circle.exp_arg z⟩

/-- AA-162. An infinite cyclic group is isomorphic to `ℤ`. -/
@[kb "judson2026" "Example 11.2.2, p. 154"]
noncomputable def infiniteCyclicMulEquiv (G : Type*) [Group G] [IsCyclic G] [Infinite G] :
    Multiplicative ℤ ≃* G := by
  have hex := IsCyclic.exists_generator (α := G)
  let g := hex.choose
  have hg : ∀ x : G, x ∈ Subgroup.zpowers g := hex.choose_spec
  have h0 : orderOf g = 0 := by
    by_contra h
    have hfin : IsOfFinOrder g := orderOf_pos_iff.1 (Nat.pos_of_ne_zero h)
    have : Finite (Subgroup.zpowers g) := hfin.finite_zpowers
    have : Finite G := Finite.of_surjective (fun x : Subgroup.zpowers g => (x : G))
      (fun x => ⟨⟨x, hg x⟩, rfl⟩)
    exact not_finite G
  refine MulEquiv.ofBijective (zpowersHom G g) ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro n hn
    have h1 : g ^ n.toAdd = 1 := hn
    rw [zpow_eq_one_iff_mem_zmultiples, h0] at h1
    simpa using h1
  · intro x
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg x)
    exact ⟨Multiplicative.ofAdd k, hk⟩

/-- AA-162. A finite cyclic group of order `n` is isomorphic to `ℤ/nℤ` (written multiplicatively). -/
@[kb "judson2026" "Example 11.2.2, p. 154"]
noncomputable def finiteCyclicMulEquiv (G : Type*) [Group G] [IsCyclic G] :
    G ≃* Multiplicative (ZMod (Nat.card G)) :=
  (zmodCyclicMulEquiv inferInstance).symm

/-- AA-164, **correspondence theorem**. For `N` normal in `G`, `QuotientGroup.comapMk'OrderIso N`
is an order isomorphism between the subgroups of `G ⧸ N` and the subgroups of `G` containing `N`
(`H' ↦ π⁻¹ H'`, inverse `H ↦ π H`), and normal subgroups correspond to normal subgroups. -/
@[kb "judson2026" "Theorem 11.2.4, p. 155"]
theorem correspondence_normal {G : Type*} [Group G] (N : Subgroup G) [N.Normal] :
    (∀ H' : Subgroup (G ⧸ N), ((QuotientGroup.comapMk'OrderIso N H').1).Normal ↔ H'.Normal) ∧
    (∀ H : Subgroup G, N ≤ H → (H.Normal ↔ (H.map (QuotientGroup.mk' N)).Normal)) := by
  constructor
  · intro H'
    constructor
    · intro h
      have := h.map (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
      have e : ((QuotientGroup.comapMk'OrderIso N H').1 : Subgroup G)
          = H'.comap (QuotientGroup.mk' N) := rfl
      rw [e, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N)] at this
      exact this
    · intro h
      exact h.comap _
  · intro H hH
    constructor
    · intro h
      exact h.map _ (QuotientGroup.mk'_surjective N)
    · intro h
      have := h.comap (QuotientGroup.mk' N)
      rwa [Subgroup.comap_map_eq_self (by rwa [QuotientGroup.ker_mk'])] at this

end UndergradKB.AbstractAlgebra
