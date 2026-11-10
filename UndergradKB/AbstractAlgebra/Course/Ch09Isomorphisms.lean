import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.RingTheory.Coprime.Lemmas
import UndergradKB.Common.Attr
import UndergradKB.AbstractAlgebra.DirectProducts

/-! # Judson–Beezer, chapter 9: isomorphisms (course layer)

Thin wrappers in the book's terms around Mathlib for the results of chapter 9 that Mathlib has:
properties preserved by isomorphisms, cyclic groups up to isomorphism, Cayley's theorem, orders in
direct products and `ℤ_m × ℤ_n ≅ ℤ_{mn}`. -/

open scoped Function

namespace UndergradKB.AbstractAlgebra.Course

/-- AA-129. An isomorphism has an isomorphism as inverse and preserves the order of the group,
commutativity, cyclicity, orders of elements and the existence of subgroups of each order. -/
@[kb "judson2026" "Theorem 9.1.6, p. 132"]
theorem judson_9_1_6 {G H : Type*} [Group G] [Group H] (φ : G ≃* H) :
    (∀ x, φ.symm (φ x) = x) ∧ Nat.card G = Nat.card H ∧
    ((∀ a b : G, a * b = b * a) ↔ ∀ a b : H, a * b = b * a) ∧
    (IsCyclic G ↔ IsCyclic H) ∧ (∀ g : G, orderOf (φ g) = orderOf g) ∧
    (∀ n : ℕ, (∃ K : Subgroup G, Nat.card K = n) ↔ ∃ K : Subgroup H, Nat.card K = n) := by
  refine ⟨φ.symm_apply_apply, Nat.card_congr φ.toEquiv, ?_, φ.isCyclic, φ.orderOf_eq, ?_⟩
  · constructor
    · intro h a b
      apply φ.symm.injective
      simp [h]
    · intro h a b
      apply φ.injective
      simp [h]
  · intro n
    constructor
    · rintro ⟨K, hK⟩
      exact ⟨K.map φ.toMonoidHom, by rw [Subgroup.card_map_of_injective φ.injective, hK]⟩
    · rintro ⟨K, hK⟩
      exact ⟨K.map φ.symm.toMonoidHom,
        by rw [Subgroup.card_map_of_injective φ.symm.injective, hK]⟩

/-- AA-130. Isomorphism of groups is an equivalence relation (on groups in a fixed universe). -/
@[kb "judson2026" "Theorem 9.1.10, p. 133"]
theorem judson_9_1_10 :
    (∀ (G : Type*) [Group G], Nonempty (G ≃* G)) ∧
    (∀ (G H : Type*) [Group G] [Group H], Nonempty (G ≃* H) → Nonempty (H ≃* G)) ∧
    (∀ (G H K : Type*) [Group G] [Group H] [Group K],
      Nonempty (G ≃* H) → Nonempty (H ≃* K) → Nonempty (G ≃* K)) :=
  ⟨fun _ _ => ⟨MulEquiv.refl _⟩, fun _ _ _ _ h => h.elim fun e => ⟨e.symm⟩,
    fun _ _ _ _ _ _ h h' => h.elim fun e => h'.elim fun f => ⟨e.trans f⟩⟩

/-- AA-132. Every infinite cyclic group is isomorphic to `ℤ` (written multiplicatively). -/
@[kb "judson2026" "Theorem 9.1.7, p. 133"]
theorem judson_9_1_7 {G : Type*} [Group G] [IsCyclic G] [Infinite G] :
    Nonempty (Multiplicative ℤ ≃* G) := by
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp ‹IsCyclic G›
  exact ⟨intEquivOfZPowersEqTop g hg⟩

/-- AA-133. A cyclic group of order `n` is isomorphic to `ℤ_n`. -/
@[kb "judson2026" "Theorem 9.1.8, p. 133"]
theorem judson_9_1_8 {G : Type*} [Group G] [IsCyclic G] {n : ℕ} (h : Nat.card G = n) :
    Nonempty (Multiplicative (ZMod n) ≃* G) := by
  subst h
  exact ⟨zmodCyclicMulEquiv ‹IsCyclic G›⟩

/-- AA-133. A group of prime order `p` is isomorphic to `ℤ_p`. -/
@[kb "judson2026" "Corollary 9.1.9, p. 133"]
theorem judson_9_1_9 {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) (h : Nat.card G = p) :
    Nonempty (Multiplicative (ZMod p) ≃* G) := by
  have : Fact p.Prime := ⟨hp⟩
  have := isCyclic_of_prime_card h
  exact judson_9_1_8 h

/-- AA-134. Cayley: every group is isomorphic to a group of permutations (of its own elements). -/
@[kb "judson2026" "Theorem 9.1.12, p. 134"]
theorem judson_9_1_12 (G : Type*) [Group G] :
    ∃ S : Subgroup (Equiv.Perm G), Nonempty (G ≃* S) :=
  ⟨(MulAction.toPermHom G G).range,
    ⟨MonoidHom.ofInjective (MulAction.toPerm_injective (α := G) (β := G))⟩⟩

/-- AA-136. The order of `(g, h)` in `G × H` is the lcm of the orders of `g` and `h`. -/
@[kb "judson2026" "Theorem 9.2.5, p. 136"]
theorem judson_9_2_5 {G H : Type*} [Group G] [Group H] (g : G) (h : H) :
    orderOf (g, h) = Nat.lcm (orderOf g) (orderOf h) :=
  Prod.orderOf_mk

/-- AA-136. The order of `(g₁, …, gₙ)` in a finite product is the lcm of the orders of the
entries. -/
@[kb "judson2026" "Corollary 9.2.6, p. 136"]
theorem judson_9_2_6 {ι : Type*} [Fintype ι] {G : ι → Type*} [∀ i, Group (G i)]
    (g : ∀ i, G i) : orderOf g = Finset.univ.lcm (fun i => orderOf (g i)) :=
  Pi.orderOf g

/-- AA-137. `ℤ_m × ℤ_n ≅ ℤ_{mn}` if and only if `gcd(m, n) = 1`. -/
@[kb "judson2026" "Theorem 9.2.9, p. 136"]
theorem judson_9_2_9 (m n : ℕ) [NeZero m] [NeZero n] :
    Nonempty (ZMod m × ZMod n ≃+ ZMod (m * n)) ↔ Nat.Coprime m n := by
  constructor
  · rintro ⟨e⟩
    have h : IsAddCyclic (ZMod m × ZMod n) := e.isAddCyclic.mpr inferInstance
    have := (AddGroup.isAddCyclic_prod_iff.mp h).2.2
    simpa [Nat.card_zmod] using this
  · intro h
    exact ⟨(ZMod.chineseRemainder h).symm.toAddEquiv⟩

/-- AA-135. Proposition 9.2.1: the Cartesian product `G × H` of two groups is a group under the
componentwise operation (identity `(1, 1)`, inverse `(g⁻¹, h⁻¹)`); it is abelian if `G` and `H` are. -/
@[kb "judson2026" "Proposition 9.2.1, p. 135"]
theorem judson_9_2_1 {G H : Type*} [Group G] [Group H] :
    (∀ a b : G × H, (a * b).1 = a.1 * b.1 ∧ (a * b).2 = a.2 * b.2) ∧
    (1 : G × H) = (1, 1) ∧ (∀ a : G × H, a⁻¹ = (a.1⁻¹, a.2⁻¹)) ∧
    ((∀ a b : G, a * b = b * a) → (∀ a b : H, a * b = b * a) → ∀ a b : G × H, a * b = b * a) :=
  ⟨fun _ _ => ⟨rfl, rfl⟩, rfl, fun _ => rfl, fun hG hH a b =>
    Prod.ext (hG a.1 b.1) (hH a.2 b.2)⟩

/-- AA-135. Example 9.2.4 (and the finite-product case of Proposition 9.2.1): a product
`G₁ × ⋯ × Gₙ` of groups is a group under componentwise operations, and `ℤ₂ⁿ`, the group of binary
`n`-tuples, has `2ⁿ` elements, each of order at most 2 (`x + x = 0`). -/
@[kb "judson2026" "Example 9.2.4, p. 136"]
theorem judson_9_2_4 {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)] (n : ℕ) :
    (∀ (a b : ∀ i, G i) (i : ι), (a * b) i = a i * b i) ∧
    (∀ (a : ∀ i, G i) (i : ι), a⁻¹ i = (a i)⁻¹) ∧
    Nat.card (Fin n → ZMod 2) = 2 ^ n ∧ ∀ x : Fin n → ZMod 2, x + x = 0 := by
  refine ⟨fun _ _ _ => rfl, fun _ _ => rfl, ?_, fun x => ?_⟩
  · simp [Nat.card_eq_fintype_card]
  · ext i
    simp only [Pi.add_apply, Pi.zero_apply]
    revert i
    intro i
    generalize x i = a
    revert a
    decide

/-- AA-138. Corollary 9.2.10: `ℤ_{n₁} × ⋯ × ℤ_{n_k} ≅ ℤ_{n₁⋯n_k}` if and only if the `nᵢ` are
pairwise relatively prime. -/
@[kb "judson2026" "Corollary 9.2.10, p. 136"]
theorem judson_9_2_10 {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℕ) :
    Nonempty (ZMod (∏ i, a i) ≃+ Π i, ZMod (a i)) ↔ Pairwise (Nat.Coprime on a) :=
  UndergradKB.AbstractAlgebra.zmod_prod_equiv_iff_coprime a

/-- AA-138. Corollary 9.2.11: for `m ≠ 0`, `ℤ_m` is isomorphic to the product of the groups
`ℤ_{p^e}` over the prime-power factorization `m = ∏ p^e`. -/
@[kb "judson2026" "Corollary 9.2.11, p. 137"]
theorem judson_9_2_11 (m : ℕ) (hm : m ≠ 0) :
    Nonempty (ZMod m ≃+ Π p : m.primeFactors, ZMod (p ^ (m.factorization p))) :=
  UndergradKB.AbstractAlgebra.zmod_equiv_pi_primePow m hm

/-- AA-140. Theorem 9.2.15: if `G` is the internal direct product of subgroups `H` and `K`
(`G = H K`, `H ∩ K = 1`, elements of `H` and `K` commute), then `G ≅ H × K`. -/
@[kb "judson2026" "Theorem 9.2.15, p. 137"]
theorem judson_9_2_15 {G : Type*} [Group G] {H K : Subgroup G}
    (h : UndergradKB.AbstractAlgebra.IsInternalDirectProduct₂ H K) :
    Nonempty (G ≃* H × K) :=
  ⟨(UndergradKB.AbstractAlgebra.internalDirectProductEquiv₂ h).symm⟩

/-- AA-140. Theorem 9.2.17: if `G` is the internal direct product of finitely many subgroups
`Hᵢ`, then `G ≅ ∏ Hᵢ`. -/
@[kb "judson2026" "Theorem 9.2.17, p. 138"]
theorem judson_9_2_17 {G : Type*} [Group G] {ι : Type*} [Fintype ι] {H : ι → Subgroup G}
    (h : UndergradKB.AbstractAlgebra.IsInternalDirectProduct H) :
    Nonempty (G ≃* ∀ i, H i) :=
  ⟨(UndergradKB.AbstractAlgebra.internalDirectProductEquiv h).symm⟩

end UndergradKB.AbstractAlgebra.Course
