import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.Algebra.MvPolynomial.Monad
import UndergradKB.Common.Attr

/-!
# Identities among symmetric functions are decided in `m` variables (A = B, Section 1.7)

An identity among the elementary symmetric functions `e_1..e_m` and the power sums `p_1..p_m`
holds in `n` variables for every `n` iff it holds for `n = m`.
-/

open MvPolynomial Finset

namespace UndergradKB.Combinatorics.AeqB

variable (K : Type*) [CommRing K]

/-- Evaluation of a polynomial in formal letters `inl i` (for `e_{i+1}`) and `inr i`
(for `p_{i+1}`) at the elementary symmetric polynomials and power sums in `n` variables. -/
noncomputable def symmEval (m n : ℕ) :
    MvPolynomial (Fin m ⊕ Fin m) K →ₐ[K] MvPolynomial (Fin n) K :=
  aeval (Sum.elim (fun i : Fin m => esymm (Fin n) K (i + 1))
    (fun i : Fin m => psum (Fin n) K (i + 1)))

/-- Every power sum `p_k` (`1 ≤ k ≤ m`) is a fixed polynomial in `e_1..e_m`, uniformly in the
number of variables (Newton's identities). -/
theorem psum_eq_aeval_esymm (m : ℕ) (k : ℕ) (hk0 : 0 < k) (hkm : k ≤ m) :
    ∃ Q : MvPolynomial (Fin m) K, ∀ n : ℕ,
      aeval (fun i : Fin m => esymm (Fin n) K (i + 1)) Q = psum (Fin n) K k := by
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    have IH' : ∀ j : ℕ, 0 < j → j < k → ∃ Q : MvPolynomial (Fin m) K, ∀ n : ℕ,
        aeval (fun i : Fin m => esymm (Fin n) K (i + 1)) Q = psum (Fin n) K j :=
      fun j h1 h2 => IH j h2 h1 (by omega)
    choose! Qf hQ using IH'
    let E : ℕ → MvPolynomial (Fin m) K := fun j =>
      if j = 0 then 1 else if h : j - 1 < m then X ⟨j - 1, h⟩ else 0
    have hE : ∀ j n, j ≤ m →
        aeval (fun i : Fin m => esymm (Fin n) K (i + 1)) (E j) = esymm (Fin n) K j := by
      intro j n hj
      by_cases h0 : j = 0
      · subst h0; simp [E]
      · have h : j - 1 < m := by omega
        simp [E, h0, h, Nat.sub_add_cancel (Nat.pos_of_ne_zero h0)]
    refine ⟨(-1) ^ (k + 1) * (k : MvPolynomial (Fin m) K) * E k -
      ∑ a ∈ antidiagonal k with a.1 ∈ Set.Ioo 0 k, (-1) ^ a.1 * E a.1 * Qf a.2, fun n => ?_⟩
    rw [psum_eq_mul_esymm_sub_sum (Fin n) K k hk0]
    simp only [map_sub, map_mul, map_pow, map_neg, map_one, map_natCast, map_sum]
    rw [hE k n hkm]
    congr 1
    refine Finset.sum_congr rfl fun a ha => ?_
    simp only [mem_filter, mem_antidiagonal, Set.mem_Ioo] at ha
    rw [hE a.1 n (by omega), hQ a.2 (by omega) (by omega) n]

/-- CO-350. Identities among the elementary symmetric functions `e_1..e_m` and power sums
`p_1..p_m` hold in every number of variables iff they hold in exactly `m` variables
(here over any commutative ring; in particular over a field of characteristic 0).
The polynomial `P` uses letters `inl i` for `e_{i+1}` and `inr i` for `p_{i+1}`. -/
@[kb "petkovsekwilfzeilberger1996" "text (identities among symmetric functions), p. 24"]
theorem symm_identity_iff (m : ℕ) (P : MvPolynomial (Fin m ⊕ Fin m) K) :
    (∀ n, symmEval K m n P = 0) ↔ symmEval K m m P = 0 := by
  refine ⟨fun h => h m, fun h n => ?_⟩
  have hex : ∀ i : Fin m, ∃ Q : MvPolynomial (Fin m) K, ∀ n : ℕ,
      aeval (fun i : Fin m => esymm (Fin n) K (i + 1)) Q = psum (Fin n) K (i + 1) :=
    fun i => psum_eq_aeval_esymm K m (i + 1) (by omega) (by omega)
  choose Qf hQ using hex
  set R : MvPolynomial (Fin m) K := bind₁ (Sum.elim X Qf) P with hR
  have key : ∀ n, symmEval K m n P =
      aeval (fun i : Fin m => esymm (Fin n) K (i + 1)) R := by
    intro n
    rw [hR, aeval_bind₁, symmEval]
    have : (Sum.elim (fun i : Fin m => esymm (Fin n) K (i + 1))
        (fun i : Fin m => psum (Fin n) K (i + 1))) =
        fun s => (aeval fun i : Fin m => esymm (Fin n) K (i + 1)) (Sum.elim X Qf s) := by
      funext s
      rcases s with i | i
      · simp
      · simpa using (hQ i n).symm
    rw [this]
  have hR0 : R = 0 := by
    have hinj := esymmAlgHom_fin_injective K (le_refl m)
    apply hinj
    apply Subtype.ext
    rw [esymmAlgHom_apply, ← key m, h]
    rfl
  rw [key n, hR0, map_zero]

end UndergradKB.Combinatorics.AeqB
