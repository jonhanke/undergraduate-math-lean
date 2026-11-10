import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IntermediateField.Algebraic
import UndergradKB.Common.Attr

/-! # Judson–Beezer, chapter 22: finite fields

The subfields of a finite field `E` with `p ^ n` elements. -/

open Polynomial

namespace UndergradKB.AbstractAlgebra

namespace FiniteFieldSubfields

variable (p : ℕ) [Fact p.Prime] {E : Type*} [Field E] [Finite E] [Algebra (ZMod p) E]

private theorem natCard_intermediateField_eq (K : IntermediateField (ZMod p) E) :
    Nat.card K = p ^ Module.finrank (ZMod p) K :=
  (FiniteField.pow_finrank_eq_natCard p K).symm

/-- Two subfields of the same size `p ^ m` of a finite field coincide. -/
private theorem eq_of_natCard_eq {m : ℕ} {K₁ K₂ : IntermediateField (ZMod p) E}
    (h₁ : Nat.card K₁ = p ^ m) (h₂ : Nat.card K₂ = p ^ m) : K₁ = K₂ := by
  classical
  have hm : m ≠ 0 := by
    rintro rfl
    have : Nat.card K₁ = 1 := by simpa using h₁
    have := Finite.one_lt_card (α := K₁)
    omega
  have hp : 1 < p ^ m := Nat.one_lt_pow hm (Fact.out : p.Prime).one_lt
  set S : Set E := {x | x ^ (p ^ m) = x} with hS
  have hsub : ∀ (K : IntermediateField (ZMod p) E), Nat.card K = p ^ m → (K : Set E) ⊆ S := by
    intro K hK x hx
    have := Fintype.ofFinite K
    have h := FiniteField.pow_card (⟨x, hx⟩ : K)
    rw [← Nat.card_eq_fintype_card, hK] at h
    exact congrArg Subtype.val h
  have hSfin : S.Finite := Set.toFinite S
  have hSle : S.ncard ≤ p ^ m := by
    have hg : (X ^ (p ^ m) - X : E[X]).natDegree = p ^ m := natDegree_X_pow_sub_X hp
    have hsub' : S ⊆ ↑((X ^ (p ^ m) - X : E[X]).roots.toFinset) := by
      intro x hx
      have hg0 : (X ^ (p ^ m) - X : E[X]) ≠ 0 := ne_zero_of_natDegree_gt (n := 0) (by omega)
      simp only [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hg0, IsRoot, eval_sub, eval_pow,
        eval_X]
      exact sub_eq_zero.2 hx
    calc S.ncard ≤ (↑((X ^ (p ^ m) - X : E[X]).roots.toFinset) : Set E).ncard :=
          Set.ncard_le_ncard hsub' (Finset.finite_toSet _)
      _ = (X ^ (p ^ m) - X : E[X]).roots.toFinset.card := Set.ncard_coe_finset _
      _ ≤ Multiset.card (X ^ (p ^ m) - X : E[X]).roots := Multiset.toFinset_card_le _
      _ ≤ p ^ m := (card_roots' _).trans_eq hg
  have key : ∀ (K : IntermediateField (ZMod p) E), Nat.card K = p ^ m → (K : Set E) = S := by
    intro K hK
    refine Set.eq_of_subset_of_ncard_le (hsub K hK) ?_ hSfin
    calc S.ncard ≤ p ^ m := hSle
      _ = Nat.card K := hK.symm
      _ = (K : Set E).ncard := (Nat.card_coe_set_eq _).symm
  exact SetLike.coe_injective ((key K₁ h₁).trans (key K₂ h₂).symm)

end FiniteFieldSubfields

open FiniteFieldSubfields

variable (p : ℕ) [Fact p.Prime] {E : Type*} [Field E] [Finite E] [Algebra (ZMod p) E]

/-- AA-408 (first half). If `E` has `p ^ n` elements, every subfield of `E` (containing the prime
field) has `p ^ m` elements for some `m` dividing `n`. -/
@[kb "judson2026" "Theorem 22.1.7, p. 305"]
theorem finiteField_subfield_card_dvd {n : ℕ} (hn : Nat.card E = p ^ n)
    (K : IntermediateField (ZMod p) E) : ∃ m : ℕ, Nat.card K = p ^ m ∧ m ∣ n := by
  refine ⟨Module.finrank (ZMod p) K, natCard_intermediateField_eq p K, ?_⟩
  have h1 : p ^ Module.finrank (ZMod p) E = p ^ n := by
    rw [FiniteField.pow_finrank_eq_natCard, hn]
  have h2 : Module.finrank (ZMod p) E = n :=
    Nat.pow_right_injective (Fact.out : p.Prime).two_le h1
  rw [← h2, ← Module.finrank_mul_finrank (ZMod p) K E]
  exact Dvd.intro _ rfl

/-- AA-408 (second half). If `E` has `p ^ n` elements, then for every `m ∣ n` there is exactly one
subfield of `E` with `p ^ m` elements. -/
theorem finiteField_exists_unique_subfield {n : ℕ} (hn : Nat.card E = p ^ n) {m : ℕ}
    (hm : m ∣ n) : ∃! K : IntermediateField (ZMod p) E, Nat.card K = p ^ m := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    have := Finite.one_lt_card (α := E)
    simp at hn
    omega
  have hm0 : m ≠ 0 := fun h => hn0 (by simpa [h] using hm)
  have h2 : Module.finrank (ZMod p) E = n :=
    Nat.pow_right_injective (Fact.out : p.Prime).two_le
      (by beta_reduce; rw [FiniteField.pow_finrank_eq_natCard, hn])
  have hdvd : Module.finrank (ZMod p) (GaloisField p m) ∣ Module.finrank (ZMod p) E := by
    rw [h2]
    have h3 : p ^ Module.finrank (ZMod p) (GaloisField p m) = p ^ m := by
      rw [FiniteField.pow_finrank_eq_natCard, GaloisField.card p m hm0]
    rwa [Nat.pow_right_injective (Fact.out : p.Prime).two_le h3]
  obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod p) (K := GaloisField p m)
    (L := E) hdvd
  refine ⟨φ.fieldRange, ?_, fun K hK => eq_of_natCard_eq p hK ?_⟩
  · rw [← GaloisField.card p m hm0]
    exact (Nat.card_congr (AlgEquiv.ofInjectiveField φ).toEquiv).symm
  · rw [← GaloisField.card p m hm0]
    exact (Nat.card_congr (AlgEquiv.ofInjectiveField φ).toEquiv).symm

end UndergradKB.AbstractAlgebra
