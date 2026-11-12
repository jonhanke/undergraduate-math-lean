import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.ComputeDegree
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.AeqB.Hyper
import UndergradKB.Combinatorics.AeqB.HyperAlgorithm
import UndergradKB.Combinatorics.AeqB.Companions

/-!
# The Apéry recurrence has no hypergeometric solution (A = B, Example 8.4.2)
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace UndergradKB.Combinatorics.AeqB
open Polynomial Filter

section
variable {K : Type*} [Field K] [CharZero K]

lemma cubic_mul_coeff (q0 q1 q2 q3 : K) (w : K[X]) (n : ℕ) :
    ((C q3 * X ^ 3 + C q2 * X ^ 2 + C q1 * X + C q0) * w).coeff (n + 3)
      = q3 * w.coeff n + q2 * w.coeff (n + 1) + q1 * w.coeff (n + 2) + q0 * w.coeff (n + 3) := by
  have e1 : n + 3 - 2 = n + 1 := by omega
  have e2 : n + 3 - 1 = n + 2 := by omega
  rw [add_mul, add_mul, add_mul]
  simp only [coeff_add, mul_assoc, coeff_C_mul, coeff_X_pow_mul', coeff_X_mul]
  simp [e1]

lemma shift_coeff (c : K[X]) (M : ℕ) (hc : c.natDegree ≤ M + 1) (s : K) :
    (c.comp (X + C s)).coeff (M + 1) = c.coeff (M + 1) ∧
      (c.comp (X + C s)).coeff M = c.coeff M + (M + 1) * s * c.coeff (M + 1) := by
  rw [comp, eval₂_eq_sum_range' C (show c.natDegree < M + 2 by omega)]
  simp only [coeff_add, finsetSum_coeff, Finset.sum_range_succ, coeff_C_mul, coeff_X_add_C_pow]
  have h1 : ∑ x ∈ Finset.range M, c.coeff x * (s ^ (x - (M + 1)) * (x.choose (M + 1) : K)) = 0 :=
    Finset.sum_eq_zero fun x hx => by
      have : x < M := by simpa using hx
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
  have h2 : ∑ x ∈ Finset.range M, c.coeff x * (s ^ (x - M) * (x.choose M : K)) = 0 :=
    Finset.sum_eq_zero fun x hx => by
      rw [Nat.choose_eq_zero_of_lt (by simpa using hx)]
      simp
  rw [h1, h2]
  constructor
  · simp
  · simp
    ring

lemma term_coeffs (u q0 q1 q2 q3 s : K) (c : K[X]) (M : ℕ) (hc : c.natDegree = M + 1) :
    (C u * (C q3 * X ^ 3 + C q2 * X ^ 2 + C q1 * X + C q0) * c.comp (X + C s)).coeff (M + 1 + 3)
        = u * q3 * c.coeff (M + 1) ∧
    (C u * (C q3 * X ^ 3 + C q2 * X ^ 2 + C q1 * X + C q0) * c.comp (X + C s)).coeff (M + 3)
        = u * (q3 * (c.coeff M + (M + 1) * s * c.coeff (M + 1)) + q2 * c.coeff (M + 1)) := by
  have hw : (c.comp (X + C s)).natDegree ≤ M + 1 := by
    rw [natDegree_comp, natDegree_X_add_C, hc, mul_one]
  have z1 : (c.comp (X + C s)).coeff (M + 2) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have z2 : (c.comp (X + C s)).coeff (M + 3) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have z3 : (c.comp (X + C s)).coeff (M + 1 + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have z4 : (c.comp (X + C s)).coeff (M + 1 + 2) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have z5 : (c.comp (X + C s)).coeff (M + 1 + 3) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  obtain ⟨h1, h2⟩ := shift_coeff c M hc.le s
  rw [mul_assoc, coeff_C_mul, coeff_C_mul]
  constructor
  · rw [cubic_mul_coeff, z3, z4, z5, h1]
    ring
  · rw [cubic_mul_coeff, z1, z2, h1, h2]
    ring

/-- The reduced auxiliary recurrence of the Apéry recurrence has no nonzero polynomial solution. -/
lemma reduced_aux_false (z : K) (c : K[X]) (hc : c ≠ 0)
    (h : C 1 * (C 1 * X ^ 3 + C 3 * X ^ 2 + C 3 * X + C 1) * c.comp (X + C 0)
      + C z * (C (-34) * X ^ 3 + C (-153) * X ^ 2 + C (-231) * X + C (-117)) * c.comp (X + C 1)
      + C (z ^ 2) * (C 1 * X ^ 3 + C 6 * X ^ 2 + C 12 * X + C 8) * c.comp (X + C 2) = 0) :
    False := by
  rcases Nat.eq_zero_or_pos c.natDegree with hD | hD
  · have hc' : c = C (c.coeff 0) := eq_C_of_natDegree_eq_zero hD
    have hγ : c.coeff 0 ≠ 0 := by
      intro h0; apply hc; rw [hc', h0, C_0]
    rw [hc'] at h
    simp only [C_comp] at h
    have e1 := congrArg (fun q => q.eval (-1 : K)) h
    have e2 := congrArg (fun q => q.eval (-2 : K)) h
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_zero] at e1 e2
    have E1 : z ^ 2 - 5 * z = 0 := by
      have := mul_eq_zero.1 (show c.coeff 0 * (z ^ 2 - 5 * z) = 0 by linear_combination e1)
      exact this.resolve_left hγ
    have E2 : 5 * z - 1 = 0 := by
      have := mul_eq_zero.1 (show c.coeff 0 * (5 * z - 1) = 0 by linear_combination e2)
      exact this.resolve_left hγ
    have : (24 : K) = 0 := by linear_combination (5 * z + 1 - 25) * E2 - 25 * E1
    norm_num at this
  · obtain ⟨M, hM⟩ : ∃ M, c.natDegree = M + 1 := ⟨c.natDegree - 1, by omega⟩
    have hγ : c.coeff (M + 1) ≠ 0 := by
      have := leadingCoeff_ne_zero.2 hc
      rwa [leadingCoeff, hM] at this
    have e4 := congrArg (fun q => q.coeff (M + 1 + 3)) h
    have e3 := congrArg (fun q => q.coeff (M + 3)) h
    simp only [coeff_add, coeff_zero] at e3 e4
    rw [(term_coeffs 1 1 3 3 1 0 c M hM).1, (term_coeffs z (-117) (-231) (-153) (-34) 1 c M hM).1,
      (term_coeffs (z ^ 2) 8 12 6 1 2 c M hM).1] at e4
    rw [(term_coeffs 1 1 3 3 1 0 c M hM).2, (term_coeffs z (-117) (-231) (-153) (-34) 1 c M hM).2,
      (term_coeffs (z ^ 2) 8 12 6 1 2 c M hM).2] at e3
    have E3 : z ^ 2 - 34 * z + 1 = 0 := by
      have := mul_eq_zero.1 (show c.coeff (M + 1) * (z ^ 2 - 34 * z + 1) = 0 by
        linear_combination e4)
      exact this.resolve_left hγ
    have E4 : (2 * (M : K) + 5) * (17 * z - 1) = 0 := by
      have := mul_eq_zero.1 (show c.coeff (M + 1) * ((2 * (M : K) + 5) * (17 * z - 1)) = 0 by
        linear_combination e3 - (c.coeff M + c.coeff (M + 1) * (2 * M + 8)) * E3)
      exact this.resolve_left hγ
    have hM5 : (2 * (M : K) + 5) ≠ 0 := by
      have := Nat.cast_ne_zero (R := K) |>.2 (show 2 * M + 5 ≠ 0 by omega)
      push_cast at this
      exact this
    have E5 : 17 * z - 1 = 0 := (mul_eq_zero.1 E4).resolve_left hM5
    have : (288 : K) = 0 := by linear_combination (-289) * E3 + (17 * z - 577) * E5
    norm_num at this

/-! ### The Apéry recurrence as a recurrence operator -/

/-- The coefficients `p_0, p_1, p_2` of the recurrence (8.4.12), expanded:
`(n+1)^3`, `-(2n+3)(17n^2+51n+39)`, `(n+2)^3`. -/
def aperyP : ℕ → K[X]
  | 0 => C 1 * X ^ 3 + C 3 * X ^ 2 + C 3 * X + C 1
  | 1 => C (-34) * X ^ 3 + C (-153) * X ^ 2 + C (-231) * X + C (-117)
  | _ => C 1 * X ^ 3 + C 6 * X ^ 2 + C 12 * X + C 8

lemma aperyP_zero : (aperyP 0 : K[X]) = (X + C 1) ^ 3 := by
  simp only [aperyP, map_one, map_ofNat]; ring

lemma aperyP_two : (aperyP 2 : K[X]) = (X + C 2) ^ 3 := by
  simp only [aperyP, map_one, map_ofNat]; ring

lemma aperyP_one_natDegree : (aperyP 1 : K[X]).natDegree ≤ 3 := by
  simp only [aperyP]; compute_degree

lemma shift_pow (i : ℕ) (s : K) : ((X + C 1 : K[X]) ^ i).comp (X + C s) = (X + C (s + 1)) ^ i := by
  simp only [pow_comp, add_comp, X_comp, C_comp, C_add]; ring

lemma aux_expand (p : ℕ → K[X]) (a b c : K[X]) (z : K) :
    AuxRecurrence p a b c z 2 ↔
      C 1 * (p 0 * (b * b.comp (X + C 1))) * c.comp (X + C 0)
        + C z * (p 1 * a * b.comp (X + C 1)) * c.comp (X + C 1)
        + C (z ^ 2) * (p 2 * (a * a.comp (X + C 1))) * c.comp (X + C 2) = 0 := by
  unfold AuxRecurrence hyperP
  simp [Finset.sum_range_succ, Finset.prod_range_succ, map_ofNat]

lemma monic_dvd_pow (a : K[X]) (ha : a.Monic) (n : ℕ) (h : a ∣ (X + C 1) ^ n) :
    ∃ i, a = (X + C 1) ^ i := by
  have hp : Prime (X + C (1 : K)) := by
    have := prime_X_sub_C (-1 : K)
    simpa [sub_eq_add_neg] using this
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow hp n).1 h
  exact ⟨i, eq_of_monic_of_associated ha ((monic_X_add_C (1 : K)).pow i) hi⟩

lemma monic_lin_prod (e f : ℕ) :
    ((X + C 1 : K[X]) ^ e * (X + C 2) ^ f).Monic ∧
      ((X + C 1 : K[X]) ^ e * (X + C 2) ^ f).natDegree = e + f := by
  have h1 : ((X + C 1 : K[X]) ^ e).Monic := (monic_X_add_C 1).pow e
  have h2 : ((X + C 2 : K[X]) ^ f).Monic := (monic_X_add_C 2).pow f
  refine ⟨h1.mul h2, ?_⟩
  rw [h1.natDegree_mul h2, natDegree_pow, natDegree_pow, natDegree_X_add_C, natDegree_X_add_C]
  simp

lemma term_top (u : K) (Q c : K[X]) (s : K) (m : ℕ) (hQ : Q.natDegree ≤ m) :
    (C u * Q * c.comp (X + C s)).coeff (m + c.natDegree) = u * Q.coeff m * c.leadingCoeff := by
  have hw : (c.comp (X + C s)).natDegree ≤ c.natDegree := by
    rw [natDegree_comp, natDegree_X_add_C, mul_one]
  have hl : (c.comp (X + C s)).coeff c.natDegree = c.leadingCoeff := by
    have h1 : (c.comp (X + C s)).natDegree = c.natDegree := by
      rw [natDegree_comp, natDegree_X_add_C, mul_one]
    have := leadingCoeff_comp (p := c) (q := X + C s) (by rw [natDegree_X_add_C]; exact one_ne_zero)
    rw [leadingCoeff, h1] at this
    rw [this, leadingCoeff_X_add_C, one_pow, mul_one]
  rw [mul_assoc, coeff_C_mul, coeff_mul_add_eq_of_natDegree_le hQ hw, hl]
  ring

lemma term_zero (u : K) (Q c : K[X]) (s : K) (m : ℕ) (hQ : Q.natDegree < m) :
    (C u * Q * c.comp (X + C s)).coeff (m + c.natDegree) = 0 := by
  have hw : (c.comp (X + C s)).natDegree ≤ c.natDegree := by
    rw [natDegree_comp, natDegree_X_add_C, mul_one]
  rw [mul_assoc, coeff_C_mul, coeff_eq_zero_of_natDegree_lt, mul_zero]
  have := natDegree_mul_le (p := Q) (q := c.comp (X + C s))
  omega

lemma nd_bound (i j : ℕ) :
    (aperyP 1 * (X + C 1 : K[X]) ^ i * (X + C 2) ^ j).natDegree ≤ 3 + i + j := by
  have h1 : ((X + C 1 : K[X]) ^ i).natDegree = i := by
    rw [natDegree_pow, natDegree_X_add_C, mul_one]
  have h2 : ((X + C 2 : K[X]) ^ j).natDegree = j := by
    rw [natDegree_pow, natDegree_X_add_C, mul_one]
  have h3 := natDegree_mul_le (p := (aperyP 1 : K[X])) (q := (X + C 1 : K[X]) ^ i)
  have h4 := natDegree_mul_le (p := (aperyP 1 : K[X]) * (X + C 1 : K[X]) ^ i)
    (q := (X + C 2 : K[X]) ^ j)
  have h5 := aperyP_one_natDegree (K := K)
  omega

/-- Core argument: the recurrence (8.4.12) has no candidate for Algorithm Hyper. -/
lemma no_apery_candidate (a b : K[X]) (z : K) (c : K[X]) (hz : z ≠ 0) (hc : c ≠ 0)
    (ha : a.Monic) (hb : b.Monic) (hadvd : a ∣ (X + C 1) ^ 3) (hbdvd : b ∣ (X + C 1) ^ 3)
    (hrec : AuxRecurrence aperyP a b c z 2) : False := by
  obtain ⟨i, rfl⟩ := monic_dvd_pow a ha 3 hadvd
  obtain ⟨j, rfl⟩ := monic_dvd_pow b hb 3 hbdvd
  rw [aux_expand, shift_pow, shift_pow, one_add_one_eq_two] at hrec
  have hγ : c.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hc
  have e0 : (aperyP 0 : K[X]) = (X + C 1) ^ 3 := aperyP_zero
  have e2 : (aperyP 2 : K[X]) = (X + C 2) ^ 3 := aperyP_two
  rcases lt_trichotomy i j with hij | hij | hij
  · -- the first term dominates
    rw [e0, e2] at hrec
    have hm : ((X + C 1 : K[X]) ^ 3 * ((X + C 1) ^ j * (X + C 2) ^ j)) =
        (X + C 1) ^ (3 + j) * (X + C 2) ^ j := by ring
    have hm2 : ((X + C 2 : K[X]) ^ 3 * ((X + C 1) ^ i * (X + C 2) ^ i)) =
        (X + C 1) ^ i * (X + C 2) ^ (3 + i) := by ring
    rw [hm, hm2] at hrec
    obtain ⟨m0, n0⟩ := monic_lin_prod (K := K) (3 + j) j
    obtain ⟨m2, n2⟩ := monic_lin_prod (K := K) i (3 + i)
    have e := congrArg (fun q => q.coeff ((3 + j + j) + c.natDegree)) hrec
    simp only [coeff_add, coeff_zero] at e
    rw [term_top 1 _ c 0 _ n0.le, term_zero z _ c 1 _ (by have := nd_bound (K := K) i j; omega),
      term_zero (z ^ 2) _ c 2 _ (by omega)] at e
    rw [← n0, m0.coeff_natDegree] at e
    exact hγ (by simpa using e)
  · subst hij
    apply reduced_aux_false z c hc
    have w0 : ((X + C 1 : K[X]) ^ i * (X + C 2) ^ i) ≠ 0 := (monic_lin_prod i i).1.ne_zero
    refine (mul_eq_zero.1 ?_).resolve_left w0
    have f0 : (aperyP 0 : K[X]) = C 1 * X ^ 3 + C 3 * X ^ 2 + C 3 * X + C 1 := rfl
    have f1 : (aperyP 1 : K[X]) = C (-34) * X ^ 3 + C (-153) * X ^ 2 + C (-231) * X + C (-117) :=
      rfl
    have f2 : (aperyP 2 : K[X]) = C 1 * X ^ 3 + C 6 * X ^ 2 + C 12 * X + C 8 := rfl
    rw [f0, f1, f2] at hrec
    rw [← hrec]
    ring
  · rw [e0, e2] at hrec
    have hm : ((X + C 1 : K[X]) ^ 3 * ((X + C 1) ^ j * (X + C 2) ^ j)) =
        (X + C 1) ^ (3 + j) * (X + C 2) ^ j := by ring
    have hm2 : ((X + C 2 : K[X]) ^ 3 * ((X + C 1) ^ i * (X + C 2) ^ i)) =
        (X + C 1) ^ i * (X + C 2) ^ (3 + i) := by ring
    rw [hm, hm2] at hrec
    obtain ⟨m0, n0⟩ := monic_lin_prod (K := K) (3 + j) j
    obtain ⟨m2, n2⟩ := monic_lin_prod (K := K) i (3 + i)
    have e := congrArg (fun q => q.coeff ((i + (3 + i)) + c.natDegree)) hrec
    simp only [coeff_add, coeff_zero] at e
    rw [term_zero 1 _ c 0 _ (by omega), term_zero z _ c 1 _ (by have := nd_bound (K := K) i j; omega),
      term_top (z ^ 2) _ c 2 _ n2.le] at e
    rw [← n2, m2.coeff_natDegree] at e
    have : z ^ 2 * c.leadingCoeff = 0 := by simpa using e
    exact hγ ((mul_eq_zero.1 this).resolve_left (pow_ne_zero 2 hz))

/-- CO-493. The recurrence (8.4.12), `(n+2)^3 y(n+2) - (2n+3)(17n^2+51n+39) y(n+1) + (n+1)^3 y(n) = 0`,
has no hypergeometric solution: no hypergeometric sequence `y` over a field of characteristic
zero satisfies it for all large `n`. -/
@[kb "petkovsekwilfzeilberger1996" "Example 8.4.2, p. 164"]
theorem apery_rec_no_hypergeometric (y : ℕ → K) (hy : IsHypergeometric y) :
    ¬ ∀ᶠ n : ℕ in atTop, ((n : K) + 2) ^ 3 * y (n + 2)
      - (2 * n + 3) * (17 * (n : K) ^ 2 + 51 * n + 39) * y (n + 1) + ((n : K) + 1) ^ 3 * y n = 0 := by
  intro hL
  have hp0 : (aperyP 0 : K[X]) ≠ 0 := by
    rw [aperyP_zero]; exact pow_ne_zero _ (X_add_C_ne_zero 1)
  have hp2 : (aperyP 2 : K[X]) ≠ 0 := by
    rw [aperyP_two]; exact pow_ne_zero _ (X_add_C_ne_zero 2)
  have hL' : ∀ᶠ n : ℕ in atTop, ∑ i ∈ Finset.range (2 + 1),
      (aperyP i : K[X]).eval (n : K) * y (n + i) = 0 := by
    filter_upwards [hL] with n hn
    have f0 : (aperyP 0 : K[X]) = C 1 * X ^ 3 + C 3 * X ^ 2 + C 3 * X + C 1 := rfl
    have f1 : (aperyP 1 : K[X]) = C (-34) * X ^ 3 + C (-153) * X ^ 2 + C (-231) * X + C (-117) :=
      rfl
    have f2 : (aperyP 2 : K[X]) = C 1 * X ^ 3 + C 6 * X ^ 2 + C 12 * X + C 8 := rfl
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, f0, f1, f2, eval_add, eval_mul,
      eval_C, eval_pow, eval_X, zero_add, add_zero]
    linear_combination hn
  obtain ⟨a, b, z, c, ⟨ha, hadvd, hb, hbdvd, hz, -, hc, hrec⟩, -⟩ :=
    hyper_candidate_complete aperyP 2 (by norm_num) hp0 hp2 y hy hL'
  have hbdvd' : b ∣ (X + C 1 : K[X]) ^ 3 := by
    refine hbdvd.trans (dvd_of_eq ?_)
    rw [aperyP_two]
    simp only [pow_comp, add_comp, X_comp, C_comp]
    have : (X + C (1 - ((2 : ℕ) : K)) + C 2 : K[X]) = X + C 1 := by
      rw [add_assoc, ← C_add]; congr 2; norm_num
    rw [this]
  rw [aperyP_zero] at hadvd
  exact no_apery_candidate a b z c hz hc ha hb hadvd hbdvd' hrec

end

end UndergradKB.Combinatorics.AeqB

namespace UndergradKB.Combinatorics.AeqB.Companions
open Filter

/-- CO-493. The Apéry numbers `∑_k C(n,k)^2 C(n+k,k)^2` are not a hypergeometric term: they satisfy
the recurrence (8.4.12) (`aperySum_rec`), which has no hypergeometric solution. -/
@[kb "petkovsekwilfzeilberger1996" "Example 8.4.2, p. 164"]
theorem aperySum_not_hypergeometric (K : Type*) [Field K] [CharZero K] :
    ¬ IsHypergeometric (fun n : ℕ => (aperySum n : K)) := by
  intro hy
  refine apery_rec_no_hypergeometric _ hy (Filter.Eventually.of_forall fun n => ?_)
  have h := aperySum_rec n
  have h' : ((n : K) + 2) ^ 3 * (aperySum (n + 2) : K) + ((n : K) + 1) ^ 3 * (aperySum n : K)
      = (2 * (n : K) + 3) * (17 * (n : K) ^ 2 + 51 * n + 39) * (aperySum (n + 1) : K) := by
    exact_mod_cast h
  linear_combination h'

end UndergradKB.Combinatorics.AeqB.Companions

end
