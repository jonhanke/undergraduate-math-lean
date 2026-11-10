import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.FermatPsp
import UndergradKB.Common.Attr
import UndergradKB.AbstractAlgebra.Permutations

/-! # Judson–Beezer, chapter 6: cosets and Lagrange's theorem (course layer)

Thin wrappers around Mathlib for cosets, index, Lagrange's theorem and its consequences, and the
theorems of Euler and Fermat. -/

open scoped Pointwise
open MulOpposite

namespace UndergradKB.AbstractAlgebra.Course

section Cosets

variable {G : Type*} [Group G] (H : Subgroup G)

/-- AA-079. Lemma on cosets: `g₁H = g₂H` iff `Hg₁⁻¹ = Hg₂⁻¹` iff `g₁H ⊆ g₂H` iff `g₂ ∈ g₁H` iff
`g₁⁻¹ g₂ ∈ H`. -/
@[kb "judson2026" "Lemma 6.1.3, p. 90"]
theorem judson_6_1_3 (g₁ g₂ : G) :
    List.TFAE [g₁ • (H : Set G) = g₂ • (H : Set G),
      op g₁⁻¹ • (H : Set G) = op g₂⁻¹ • (H : Set G),
      g₁ • (H : Set G) ⊆ g₂ • (H : Set G),
      g₂ ∈ g₁ • (H : Set G),
      g₁⁻¹ * g₂ ∈ H] := by
  tfae_have 1 ↔ 5 := leftCoset_eq_iff H
  tfae_have 2 ↔ 5 := by
    rw [rightCoset_eq_iff, inv_inv, ← H.inv_mem_iff, mul_inv_rev, inv_inv]
  tfae_have 4 ↔ 5 := mem_leftCoset_iff g₁
  tfae_have 1 → 3 := fun h => h.subset
  tfae_have 3 → 4 := by
    intro h
    have h1 : g₁ ∈ g₁ • (H : Set G) := (mem_leftCoset_iff g₁).mpr (by simp)
    have h2 := h h1
    rw [mem_leftCoset_iff] at h2
    have h3 : g₂⁻¹ * g₁ ∈ H := h2
    have h4 := H.inv_mem h3
    rw [mem_leftCoset_iff]
    simpa using h4
  tfae_finish

/-- AA-080. The left cosets of a subgroup cover the group and any two are equal or disjoint. -/
@[kb "judson2026" "Theorem 6.1.4, p. 90"]
theorem judson_6_1_4 :
    (⋃ g : G, g • (H : Set G)) = Set.univ ∧
    ∀ g₁ g₂ : G, g₁ • (H : Set G) = g₂ • (H : Set G) ∨
      Disjoint (g₁ • (H : Set G)) (g₂ • (H : Set G)) := by
  refine ⟨?_, fun g₁ g₂ => ?_⟩
  · apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨x, (mem_leftCoset_iff x).mpr (by simp)⟩
  · by_cases h : Disjoint (g₁ • (H : Set G)) (g₂ • (H : Set G))
    · exact Or.inr h
    · left
      obtain ⟨a, ha1, ha2⟩ := Set.not_disjoint_iff.mp h
      rw [mem_leftCoset_iff] at ha1 ha2
      rw [leftCoset_eq_iff]
      have := H.mul_mem ha1 (H.inv_mem ha2)
      simpa [mul_assoc] using this

/-- AA-080. The right cosets of a subgroup cover the group and any two are equal or disjoint. -/
@[kb "judson2026" "Remark 6.1.5, p. 90"]
theorem judson_6_1_5 :
    (⋃ g : G, op g • (H : Set G)) = Set.univ ∧
    ∀ g₁ g₂ : G, op g₁ • (H : Set G) = op g₂ • (H : Set G) ∨
      Disjoint (op g₁ • (H : Set G)) (op g₂ • (H : Set G)) := by
  refine ⟨?_, fun g₁ g₂ => ?_⟩
  · apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨x, (mem_rightCoset_iff x).mpr (by simp)⟩
  · by_cases h : Disjoint (op g₁ • (H : Set G)) (op g₂ • (H : Set G))
    · exact Or.inr h
    · left
      obtain ⟨a, ha1, ha2⟩ := Set.not_disjoint_iff.mp h
      rw [mem_rightCoset_iff] at ha1 ha2
      rw [rightCoset_eq_iff]
      have := H.mul_mem (H.inv_mem ha2) ha1
      simpa [mul_assoc] using this

/-- AA-082. The number of left cosets of `H` equals the number of right cosets. -/
@[kb "judson2026" "Theorem 6.1.8, p. 91"]
theorem judson_6_1_8 :
    Nat.card (G ⧸ H) = Nat.card (Quotient (QuotientGroup.rightRel H)) :=
  (Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel H)).symm

/-- AA-083. For `g ∈ G`, the map `h ↦ g h` is a bijection from `H` onto the coset `gH`, so
`|H| = |gH|`. -/
@[kb "judson2026" "Proposition 6.2.1, p. 91"]
theorem judson_6_2_1 (g : G) :
    ∃ φ : H → ↥(g • (H : Set G)), (∀ h : H, (φ h : G) = g * h) ∧ Function.Bijective φ := by
  refine ⟨fun h => ⟨g * h, Set.mem_smul_set.mpr ⟨h, h.2, rfl⟩⟩, fun h => rfl, ?_, ?_⟩
  · intro h₁ h₂ h
    have := congrArg Subtype.val h
    exact Subtype.ext (mul_left_cancel this)
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hx
    exact ⟨⟨y, hy⟩, rfl⟩

/-- AA-084. Lagrange's theorem: for a subgroup `H` of a finite group `G`, `|G| = [G : H] |H|`; so
`|G| / |H| = [G : H]` and `|H|` divides `|G|`. -/
@[kb "judson2026" "Theorem 6.2.2, p. 91"]
theorem judson_6_2_2 [Finite G] :
    Nat.card G = H.index * Nat.card H ∧ Nat.card G / Nat.card H = H.index ∧
    Nat.card H ∣ Nat.card G := by
  have h1 : Nat.card H * H.index = Nat.card G := H.card_mul_index
  have hpos : 0 < Nat.card H := Nat.card_pos
  refine ⟨by rw [← h1, mul_comm], ?_, ⟨H.index, h1.symm⟩⟩
  rw [← h1, Nat.mul_div_cancel_left _ hpos]

end Cosets

section Consequences

variable {G : Type*} [Group G]

/-- AA-085. In a finite group the order of an element divides the order of the group. -/
@[kb "judson2026" "Corollary 6.2.3, p. 91"]
theorem judson_6_2_3 [Finite G] (g : G) : orderOf g ∣ Nat.card G :=
  orderOf_dvd_natCard g

/-- AA-086. A group of prime order `p` is cyclic, and every non-identity element generates it. -/
@[kb "judson2026" "Corollary 6.2.4, p. 91"]
theorem judson_6_2_4 {p : ℕ} (hp : p.Prime) (h : Nat.card G = p) :
    IsCyclic G ∧ ∀ g : G, g ≠ 1 → Subgroup.zpowers g = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Finite G := Nat.finite_of_card_ne_zero (h ▸ hp.ne_zero)
  refine ⟨isCyclic_of_prime_card h, fun g hg => ?_⟩
  have hd : orderOf g ∣ p := h ▸ orderOf_dvd_natCard g
  have hne : orderOf g ≠ 1 := fun h1 => hg (orderOf_eq_one_iff.mp h1)
  have hord : orderOf g = p := ((Nat.dvd_prime hp).mp hd).resolve_left hne
  apply Subgroup.eq_top_of_card_eq
  rw [Nat.card_zpowers, hord, h]

/-- AA-087. For subgroups `K ≤ H` of a finite group `G`, `[G : K] = [G : H] [H : K]`. -/
@[kb "judson2026" "Corollary 6.2.5, p. 91"]
theorem judson_6_2_5 [Finite G] (H K : Subgroup G) (hKH : K ≤ H) :
    K.index = H.index * K.relIndex H := by
  rw [mul_comm]
  exact (Subgroup.relIndex_mul_index hKH).symm

/-- AA-089. Two cycles in `S_n` have the same length iff they are conjugate, `μ = σ τ σ⁻¹`. -/
@[kb "judson2026" "Theorem 6.2.8, p. 92"]
theorem judson_6_2_8 (n : ℕ) (τ μ : Equiv.Perm (Fin n)) (hτ : τ.IsCycle) (hμ : μ.IsCycle) :
    τ.support.card = μ.support.card ↔ ∃ σ : Equiv.Perm (Fin n), μ = σ * τ * σ⁻¹ := by
  rw [← hτ.isConj_iff hμ, isConj_iff]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩

end Consequences

/-- AA-091. The group `U(n)` of units of `ℤ_n` has `φ(n)` elements. -/
@[kb "judson2026" "Theorem 6.3.1, p. 93"]
theorem judson_6_3_1 (n : ℕ) [NeZero n] : Nat.card (ZMod n)ˣ = Nat.totient n := by
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

/-- AA-092. Euler's theorem: `a^φ(n) ≡ 1 (mod n)` when `gcd(a, n) = 1`. -/
@[kb "judson2026" "Theorem 6.3.2, p. 93"]
theorem judson_6_3_2 (a n : ℕ) (h : Nat.gcd a n = 1) : a ^ Nat.totient n ≡ 1 [MOD n] :=
  Nat.ModEq.pow_totient h

/-- AA-093. Fermat's little theorem: `a^(p-1) ≡ 1 (mod p)` if `p ∤ a`, and `b^p ≡ b (mod p)` for
every `b`. -/
@[kb "judson2026" "Theorem 6.3.3, p. 93"]
theorem judson_6_3_3 {p : ℕ} (hp : p.Prime) :
    (∀ a : ℕ, ¬ p ∣ a → a ^ (p - 1) ≡ 1 [MOD p]) ∧ ∀ b : ℕ, b ^ p ≡ b [MOD p] := by
  refine ⟨fun a ha => Nat.ModEq.pow_card_sub_one_eq_one hp
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr ha).symm, fun b => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  have h := ZMod.pow_card (b : ZMod p)
  rw [← Nat.cast_pow] at h
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h

/-- AA-088. Proposition 6.2.7: `A₄` has order 12 but no subgroup of order 6 (the converse of
Lagrange's theorem fails). -/
@[kb "judson2026" "Proposition 6.2.7, p. 92"]
theorem judson_6_2_7 :
    Nat.card (alternatingGroup (Fin 4)) = 12 ∧
      ∀ H : Subgroup (alternatingGroup (Fin 4)), Nat.card H ≠ 6 := by
  refine ⟨?_, UndergradKB.AbstractAlgebra.alternatingGroup_four_no_subgroup_order_six⟩
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]; decide

end UndergradKB.AbstractAlgebra.Course
