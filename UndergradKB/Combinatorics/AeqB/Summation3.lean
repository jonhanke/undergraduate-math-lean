import Mathlib.RingTheory.PowerSeries.Derivative
import UndergradKB.Combinatorics.AeqB.EulerTransform
import UndergradKB.Common.Attr

/-!
# Kummer's `2F1(-1)` summation, terminating case (CO-362)

For `a - b + c = 1` and `b = -n` a negative integer, Kummer's identity evaluates
`2F1(a, -n; 1-a-n; -1)`.  We prove it in rising factorial form: the sum is `0` for odd `n` and
`(2m)! (a)_m / (m! (a)_{2m})` for `n = 2m`.  The proof writes the sum as the coefficient of `z^n`
in `(1-z)^(-a) (1+z)^(-a) = (1-z^2)^(-a)`, using the differential equation `(1-z^2) G' = 2 a z G`.
-/

set_option linter.unusedSectionVars false

namespace UndergradKB.Combinatorics.AeqB
open Finset PowerSeries
open scoped Nat

variable {K : Type*} [Field K] [CharZero K]

lemma rescale_C' (c r : K) : rescale c (C r) = C r := by
  ext n
  rw [coeff_rescale, coeff_C]
  split_ifs with h
  · subst h; simp
  · simp

lemma deriv_rescale_neg (f : K⟦X⟧) :
    d⁄dX (rescale (-1 : K) f) = - rescale (-1 : K) (d⁄dX f) := by
  ext n
  rw [coeff_derivative, coeff_rescale, map_neg, coeff_rescale, coeff_derivative]
  ring

/-- `(1+z)^(-a)`, the image of `1F0[a;;z]` under `z ↦ -z`. -/
noncomputable def kN (a : K) : K⟦X⟧ := rescale (-1 : K) (oneFZero a)

lemma kN_ode (a : K) : (1 + X) * d⁄dX (kN a) = - (C a * kN a) := by
  have h := congrArg (rescale (-1 : K)) (oneSub_deriv a)
  rw [map_mul, map_sub, map_one, rescale_neg_one_X, map_mul, rescale_C'] at h
  unfold kN
  rw [deriv_rescale_neg]
  linear_combination (-1 : K⟦X⟧) * h

lemma kG_ode (a : K) :
    (1 - X ^ 2) * d⁄dX (oneFZero a * kN a) = C (2 * a) * X * (oneFZero a * kN a) := by
  have hP := oneSub_deriv a
  have hN := kN_ode a
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_mul]
  have h2 : (C (2 : K) : K⟦X⟧) = 2 := map_ofNat C 2
  rw [h2]
  linear_combination (1 + X) * kN a * hP + (1 - X) * oneFZero a * hN

/-- The recurrence `(n+2) g_{n+2} = (n + 2a) g_n` for the coefficients of `(1-z)^(-a)(1+z)^(-a)`. -/
lemma kG_rec (a : K) (n : ℕ) :
    ((n : K) + 2) * coeff (n + 2) (oneFZero a * kN a) =
      ((n : K) + 2 * a) * coeff n (oneFZero a * kN a) := by
  have h := congrArg (coeff (n + 1)) (kG_ode a)
  set G := oneFZero a * kN a
  have e1 : (1 - X ^ 2 : K⟦X⟧) * d⁄dX G = d⁄dX G - X * (X * d⁄dX G) := by ring
  have e2 : (C (2 * a) * X * G : K⟦X⟧) = C (2 * a) * (X * G) := by ring
  rw [e1, e2, map_sub, coeff_C_mul, coeff_succ_X_mul, coeff_succ_X_mul, coeff_derivative] at h
  rcases n with _ | n
  · simp only [coeff_zero_X_mul] at h
    push_cast at h ⊢
    linear_combination h
  · rw [coeff_succ_X_mul, coeff_derivative] at h
    push_cast at h ⊢
    linear_combination h

lemma coeff_one_kG (a : K) : coeff 1 (oneFZero a * kN a) = 0 := by
  have h := congrArg (coeff 0) (kG_ode a)
  set G := oneFZero a * kN a
  have e1 : (1 - X ^ 2 : K⟦X⟧) * d⁄dX G = d⁄dX G - X * (X * d⁄dX G) := by ring
  have e2 : (C (2 * a) * X * G : K⟦X⟧) = C (2 * a) * (X * G) := by ring
  rw [e1, e2, map_sub, coeff_C_mul, coeff_zero_X_mul, coeff_zero_X_mul, coeff_derivative] at h
  simpa using h

lemma coeff_zero_kG (a : K) : coeff 0 (oneFZero a * kN a) = 1 := by
  have h1 : constantCoeff (oneFZero a) = 1 := constantCoeff_oneFZero a
  have h2 : constantCoeff (kN a) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    unfold kN
    rw [coeff_rescale, pow_zero, one_mul, coeff_zero_eq_constantCoeff_apply, h1]
  rw [coeff_zero_eq_constantCoeff_apply, map_mul, h1, h2, one_mul]

lemma coeff_oneFZero (a : K) (k : ℕ) :
    coeff k (oneFZero a) = (ascPochhammer K k).eval a / (k ! : K) := by
  simp [oneFZero, pFqTerm_one_zero]

lemma u_succ (a : K) (k : ℕ) :
    coeff (k + 1) (oneFZero a) * ((k : K) + 1) = coeff k (oneFZero a) * (a + k) := by
  rw [coeff_oneFZero, coeff_oneFZero, ascPochhammer_succ_eval, Nat.factorial_succ]
  have h1 : (k ! : K) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have h2 : ((k : K) + 1) ≠ 0 := by exact_mod_cast k.succ_ne_zero
  push_cast
  field_simp

lemma kG_coeffs (a : K) (m : ℕ) :
    coeff (2 * m) (oneFZero a * kN a) = coeff m (oneFZero a) ∧
      coeff (2 * m + 1) (oneFZero a * kN a) = 0 := by
  induction m with
  | zero => exact ⟨by simpa [coeff_oneFZero] using coeff_zero_kG a, by simpa using coeff_one_kG a⟩
  | succ m ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have r1 := kG_rec a (2 * m)
    have r2 := kG_rec a (2 * m + 1)
    have u := u_succ a m
    have hne : (((2 * m : ℕ) : K) + 2) ≠ 0 := by exact_mod_cast (by omega : 2 * m + 2 ≠ 0)
    have hne2 : (((2 * m + 1 : ℕ) : K) + 2) ≠ 0 := by
      exact_mod_cast (by omega : 2 * m + 1 + 2 ≠ 0)
    have hm : ((m : K) + 1) ≠ 0 := by exact_mod_cast m.succ_ne_zero
    refine ⟨?_, ?_⟩
    · rw [show 2 * (m + 1) = 2 * m + 2 by ring]
      push_cast at r1 hne
      rw [ih1] at r1
      apply mul_left_cancel₀ hne
      rw [r1]
      linear_combination (-2 : K) * u
    · rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by ring]
      rw [ih2, mul_zero] at r2
      exact (mul_eq_zero.1 r2).resolve_left hne2

/-- The coefficient of `z^n` in `(1+z)^(-a) (1-z)^(-a)` is `∑_k (-1)^k (a)_k (a)_{n-k} / (k! (n-k)!)`. -/
lemma coeff_kG (a : K) (n : ℕ) :
    coeff n (oneFZero a * kN a) = ∑ k ∈ range (n + 1), (-1 : K) ^ k *
      ((ascPochhammer K k).eval a / (k ! : K) * ((ascPochhammer K (n - k)).eval a / ((n - k)! : K))) := by
  rw [mul_comm, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine sum_congr rfl fun k _ => ?_
  simp only [kN, coeff_rescale, coeff_oneFZero]
  ring

/-- CO-362 (Kummer, terminating case). For `a - b + c = 1` and `b = -n`, i.e. `c = 1 - a - n`, with
`(a)_n ≠ 0` (so that the series is defined), the sum `2F1(a, -n; 1-a-n; -1)` vanishes for odd `n`
and equals `(2m)! (a)_m / (m! (a)_{2m})` for `n = 2m`.  (The book's gamma form
`Γ(b/2+1)Γ(b-a+1) / (Γ(b+1)Γ(b/2-a+1))` degenerates at negative integers `b`; its cosine form
is the same statement.) -/
@[kb "petkovsekwilfzeilberger1996" "text (II) Kummer 2F1, p. 53"]
theorem kummer_terminating (a : K) (n : ℕ) (hn : rise a n ≠ 0) :
    ∑ k ∈ range (n + 1), pFqTerm ![a, -(n : K)] ![1 - a - n] (-1) k * rise a n =
      (n ! : K) * coeff n (oneFZero a * kN a) := by
  rw [coeff_kG, mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := by simpa [Nat.lt_succ_iff] using hk
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkn
  have hr := rise_reflect a k m
  have hnk := rise_neg_nat_ne_zero (K := K) (k + m) k (Nat.le_add_right _ _)
  have hf : ∀ j : ℕ, (j ! : K) ≠ 0 := fun j => by exact_mod_cast j.factorial_ne_zero
  have hrhs : rise a (k + m) * rise (-((k + m : ℕ) : K)) k * (m ! : K) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hn hnk) (hf m)
  have hm : rise a m ≠ 0 := by
    intro h0; rw [h0] at hr; simp only [zero_mul] at hr; exact hrhs hr.symm
  have hek : rise (1 - a - ((k + m : ℕ) : K)) k ≠ 0 := by
    intro h0; rw [h0] at hr; simp only [zero_mul, mul_zero] at hr; exact hrhs hr.symm
  have e : (ascPochhammer K k).eval (1 - a - ((k + m : ℕ) : K)) =
      rise a (k + m) * rise (-((k + m : ℕ) : K)) k * (m ! : K) / (rise a m * ((k + m)! : K)) := by
    have := hf (k + m)
    field_simp
    linear_combination hr
  simp only [pFqTerm, Fin.prod_univ_two, Fin.prod_univ_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, Nat.add_sub_cancel_left]
  have := hf k
  have := hf m
  have := hf (k + m)
  rw [e]
  field_simp

/-- CO-362 (Kummer, terminating, odd `n = |b|`): the sum vanishes. -/
@[kb "petkovsekwilfzeilberger1996" "text (II) Kummer 2F1, p. 53"]
theorem kummer_terminating_odd (a : K) (m : ℕ) (hn : rise a (2 * m + 1) ≠ 0) :
    ∑ k ∈ range (2 * m + 1 + 1),
      pFqTerm ![a, -((2 * m + 1 : ℕ) : K)] ![1 - a - ((2 * m + 1 : ℕ) : K)] (-1) k = 0 := by
  have h := kummer_terminating a (2 * m + 1) hn
  rw [← sum_mul, (kG_coeffs a m).2, mul_zero] at h
  exact (mul_eq_zero.1 h).resolve_right hn

/-- CO-362 (Kummer, terminating, even `n = |b| = 2m`):
`2F1(a, -2m; 1-a-2m; -1) = (2m)! (a)_m / (m! (a)_{2m})`. -/
@[kb "petkovsekwilfzeilberger1996" "text (II) Kummer 2F1, p. 53"]
theorem kummer_terminating_even (a : K) (m : ℕ) (hn : rise a (2 * m) ≠ 0) :
    ∑ k ∈ range (2 * m + 1),
      pFqTerm ![a, -((2 * m : ℕ) : K)] ![1 - a - ((2 * m : ℕ) : K)] (-1) k =
      ((2 * m) ! : K) * rise a m / ((m ! : K) * rise a (2 * m)) := by
  have h := kummer_terminating a (2 * m) hn
  rw [← sum_mul, (kG_coeffs a m).1, coeff_oneFZero] at h
  have hm : (m ! : K) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  rw [eq_div_iff (mul_ne_zero hm hn)]
  rw [mul_left_comm, h]
  field_simp

end UndergradKB.Combinatorics.AeqB
