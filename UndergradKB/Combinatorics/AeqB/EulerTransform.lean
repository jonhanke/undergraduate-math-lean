import Mathlib.RingTheory.PowerSeries.Derivative
import UndergradKB.Combinatorics.AeqB.Summation1
import UndergradKB.Common.Attr

/-!
# Euler's transformation of `2F1` as an identity of formal power series (CO-373)

`2F1(a,b;c;z) = (1-z)^(c-a-b) 2F1(c-a,c-b;c;z)` over a field of characteristic zero, `c` not a
nonpositive integer.  The proof compares both sides as the unique formal solution
with constant term `1` of the hypergeometric differential equation
`z(1-z)y'' + (c-(a+b+1)z)y' - ab y = 0`.  The power `(1-z)^s` is the series `1F0[-s; ; z]`.
-/

set_option linter.unusedSectionVars false

namespace UndergradKB.Combinatorics.AeqB
open Finset PowerSeries
open scoped Nat

variable {K : Type*} [Field K] [CharZero K]

/-- The formal series `2F1(a,b;c;z) = ∑ (a)_k (b)_k z^k / ((c)_k k!)`. -/
noncomputable def hyp21 (a b c : K) : K⟦X⟧ :=
  PowerSeries.mk fun k => pFqTerm ![a, b] ![c] 1 k

/-- The hypergeometric differential operator `z(1-z)y'' + (c-(a+b+1)z)y' - ab y`. -/
noncomputable def hypOde (a b c : K) (y : K⟦X⟧) : K⟦X⟧ :=
  X * (1 - X) * d⁄dX (d⁄dX y) + (C c - (C a + C b + 1) * X) * d⁄dX y - C a * C b * y

lemma coeff_hypOde_aux (c p r : K) (y : K⟦X⟧) (n : ℕ) :
    coeff n (X * d⁄dX (d⁄dX y) - X * (X * d⁄dX (d⁄dX y)) + C c * d⁄dX y
      - C p * (X * d⁄dX y) - C r * y) =
      ((n : K) + 1) * ((n : K) + c) * coeff (n + 1) y
        - (n * (n - 1) + p * n + r) * coeff n y := by
  rcases n with _ | n
  · simp only [map_sub, map_add, coeff_C_mul, coeff_zero_X_mul, coeff_derivative]
    push_cast
    ring
  · rcases n with _ | n
    · simp only [map_sub, map_add, coeff_C_mul, coeff_zero_X_mul, coeff_succ_X_mul,
        coeff_derivative]
      push_cast
      ring
    · simp only [map_sub, map_add, coeff_C_mul, coeff_succ_X_mul, coeff_derivative]
      push_cast
      ring

lemma coeff_hypOde (a b c : K) (y : K⟦X⟧) (n : ℕ) :
    coeff n (hypOde a b c y) =
      ((n : K) + 1) * ((n : K) + c) * coeff (n + 1) y - ((n : K) + a) * ((n : K) + b) * coeff n y := by
  have e : hypOde a b c y = X * d⁄dX (d⁄dX y) - X * (X * d⁄dX (d⁄dX y)) + C c * d⁄dX y
      - C (a + b + 1) * (X * d⁄dX y) - C (a * b) * y := by
    unfold hypOde
    simp only [map_add, map_mul, map_one]
    ring
  rw [e, coeff_hypOde_aux]
  ring

lemma coeff_hyp21_succ (a b c : K) (hc : LowerOK ![c]) (n : ℕ) :
    ((n : K) + 1) * ((n : K) + c) * coeff (n + 1) (hyp21 a b c) =
      ((n : K) + a) * ((n : K) + b) * coeff n (hyp21 a b c) := by
  have h := pFqTerm_succ_mul ![a, b] hc 1 n
  simp only [hyp21, coeff_mk]
  simp only [Fin.prod_univ_two, Fin.prod_univ_one, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h
  linear_combination h

lemma hypOde_hyp21 (a b c : K) (hc : LowerOK ![c]) : hypOde a b c (hyp21 a b c) = 0 := by
  ext n
  rw [coeff_hypOde, coeff_hyp21_succ a b c hc]
  simp

/-- A formal solution of the hypergeometric equation with constant term `1` is `2F1`. -/
lemma eq_hyp21_of_ode (a b c : K) (hc : LowerOK ![c]) (y : K⟦X⟧) (h0 : constantCoeff y = 1)
    (hy : hypOde a b c y = 0) : y = hyp21 a b c := by
  have hrec : ∀ n : ℕ, coeff (n + 1) y * (((n : K) + 1) * ((n : K) + c)) =
      coeff n y * ((((n : K) + a) * ((n : K) + b)) * 1) := by
    intro n
    have := congrArg (coeff n) hy
    rw [coeff_hypOde] at this
    simp only [map_zero] at this
    linear_combination this
  have key := eq_pFqTerm_of_term_ratio (p := 2) (q := 1) ![a, b] (b := ![c]) hc 1
    (fun k => coeff k y) (by simpa using h0) (by
      intro k
      simp only [Fin.prod_univ_two, Fin.prod_univ_one, Matrix.cons_val_zero, Matrix.cons_val_one]
      have := hrec k
      linear_combination this)
  ext n
  simp only [hyp21, coeff_mk]
  exact key n

/-! ### Powers `(1-z)^s` as `1F0[-s; ; z]` -/

/-- The formal power `(1 - z)^s := 1F0[-s; ; z] = ∑ (-s)_k z^k / k!`. -/
noncomputable def powOneSub (s : K) : K⟦X⟧ := oneFZero (-s)

lemma oneSub_deriv (a : K) : (1 - X) * d⁄dX (oneFZero a) = C a * oneFZero a := by
  ext n
  have h3 : (n ! : K) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have h4 : ((n : K) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  rw [sub_mul, one_mul, map_sub, coeff_derivative, coeff_C_mul]
  rcases n with _ | n
  · simp [oneFZero, pFqTerm_one_zero, asc_succ_left_eval]
  · have h3' : (n ! : K) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have h4' : ((n : K) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    have h5 : ((n : K) + 1 + 1) ≠ 0 := by exact_mod_cast (n + 1).succ_ne_zero
    rw [coeff_succ_X_mul, coeff_derivative]
    simp only [oneFZero, coeff_mk, pFqTerm_one_zero, one_pow, mul_one]
    rw [ascPochhammer_succ_eval (n + 1), Nat.factorial_succ (n + 1)]
    push_cast
    field_simp
    ring

lemma hypOde_mul (a b c : K) (P W : K⟦X⟧)
    (hP : (1 - X) * d⁄dX P = (C a + C b - C c) * P)
    (hW : hypOde (c - a) (c - b) c W = 0) : hypOde a b c (P * W) = 0 := by
  have h2 := congrArg (d⁄dX) hP
  simp only [Derivation.leibniz, map_sub, map_add, derivative_X, derivative_one, derivative_C,
    smul_eq_mul, mul_zero, zero_add, add_zero, sub_zero, one_mul] at h2
  unfold hypOde at hW ⊢
  simp only [map_sub] at hW
  simp only [Derivation.leibniz, smul_eq_mul, map_add]
  linear_combination P * hW + (X * W) * h2 + (2 * X * d⁄dX W + C c * W) * hP

lemma powOneSub_deriv (a b c : K) :
    (1 - X) * d⁄dX (powOneSub (c - a - b)) =
      (C a + C b - C c) * powOneSub (c - a - b) := by
  unfold powOneSub
  rw [oneSub_deriv]
  simp only [map_sub, map_neg]
  ring

lemma constantCoeff_oneFZero (a : K) : constantCoeff (oneFZero a) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp [oneFZero, pFqTerm_zero]

lemma constantCoeff_hyp21 (a b c : K) : constantCoeff (hyp21 a b c) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp [hyp21, pFqTerm_zero]

/-- CO-373. Euler's transformation as an identity of formal power series over a field of
characteristic zero: `2F1(a,b;c;z) = (1-z)^(c-a-b) 2F1(c-a,c-b;c;z)`, for `c` not a nonpositive
integer (so that the series are defined). -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 60"]
theorem euler_transformation (a b c : K) (hc : LowerOK ![c]) :
    hyp21 a b c = powOneSub (c - a - b) * hyp21 (c - a) (c - b) c := by
  symm
  apply eq_hyp21_of_ode a b c hc
  · rw [map_mul, constantCoeff_hyp21]
    simp [powOneSub, constantCoeff_oneFZero]
  · exact hypOde_mul a b c _ _ (powOneSub_deriv a b c) (hypOde_hyp21 _ _ c hc)

/-! ### Saalschütz's identity from Euler's transformation (CO-363) -/

/-- Rising factorial `(x)_n`. -/
noncomputable abbrev rise (x : K) (n : ℕ) : K := (ascPochhammer K n).eval x

lemma rise_succ (x : K) (n : ℕ) : rise x (n + 1) = rise x n * (x + n) :=
  ascPochhammer_succ_eval n x

lemma rise_reflect (σ : K) (k m : ℕ) :
    rise σ m * rise (1 - σ - ((k + m : ℕ) : K)) k * ((k + m)! : K) =
      rise σ (k + m) * rise (-((k + m : ℕ) : K)) k * (m ! : K) := by
  induction k generalizing m with
  | zero => simp [rise]
  | succ k ih =>
    have h := ih (m + 1)
    rw [show k + (m + 1) = k + 1 + m by omega] at h
    rw [rise_succ σ m, Nat.factorial_succ m] at h
    rw [rise_succ _ k, rise_succ _ k]
    push_cast at h ⊢
    linear_combination (-1 : K) * h

lemma rise_neg_nat_ne_zero (n k : ℕ) (h : k ≤ n) : rise (-(n : K)) k ≠ 0 := by
  unfold rise
  rw [asc_eval_eq_prod]
  refine prod_ne_zero_iff.2 fun j hj => ?_
  have hj' : j < k := mem_range.1 hj
  intro h0
  have : (j : K) = n := by linear_combination h0
  have := Nat.cast_injective this
  omega

/-- CO-363. Pfaff-Saalschütz summation of the terminating `3F2` in rising factorial form:
if `d + e = a + b + c + 1` and `c = -n` is a negative integer (here `n ≥ 0`), then
`3F2(a,b,c; d,e; 1) = (d-a)_n (d-b)_n / ((d)_n (d-a-b)_n)`.  Hypotheses: `d` is not a
nonpositive integer and `(d-a-b)_n ≠ 0` (then `(e)_k ≠ 0` for `k ≤ n` is automatic).
Derived from Euler's transformation (CO-373) by comparing the coefficients of `z^n`. -/
@[kb "petkovsekwilfzeilberger1996" "text (III) Saalschuetz, p. 54"]
theorem saalschutz_three_f_two (a b d e : K) (n : ℕ)
    (hde : d + e = a + b + (-(n : K)) + 1) (hd : LowerOK ![d])
    (hden : rise (d - a - b) n ≠ 0) :
    ∑ k ∈ range (n + 1), pFqTerm ![a, b, -(n : K)] ![d, e] 1 k =
      rise (d - a) n * rise (d - b) n / (rise d n * rise (d - a - b) n) := by
  have hd' : ∀ k : ℕ, rise d k ≠ 0 := fun k =>
    eval_ascPochhammer_ne_zero (fun m => by simpa using hd 0 m) k
  have he : e = 1 - (d - a - b) - (n : K) := by linear_combination hde
  -- Euler's transformation, coefficient of `z^n`
  have h := congrArg (coeff n) (euler_transformation (d - a) (d - b) d hd)
  have hs : -(d - (d - a) - (d - b)) = d - a - b := by ring
  simp only [powOneSub] at h
  rw [hs] at h
  simp only [sub_sub_cancel, hyp21, oneFZero, coeff_mk] at h
  rw [mul_comm, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i (PowerSeries.mk fun k => pFqTerm ![a, b] ![d] 1 k) *
      coeff j (PowerSeries.mk fun k => pFqTerm ![d - a - b] (![] : Fin 0 → K) 1 k))] at h
  simp only [coeff_mk] at h
  have hterm : ∀ k ∈ range (n + 1),
      pFqTerm ![a, b] ![d] 1 k * pFqTerm ![d - a - b] (![] : Fin 0 → K) 1 (n - k) =
        rise (d - a - b) n / (n ! : K) * pFqTerm ![a, b, -(n : K)] ![d, e] 1 k := by
    intro k hk
    have hkn : k ≤ n := by simpa [Nat.lt_succ_iff] using hk
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkn
    have hr := rise_reflect (d - a - b) k m
    rw [← he] at hr
    have hnk := rise_neg_nat_ne_zero (K := K) (k + m) k (Nat.le_add_right _ _)
    have hek : rise e k ≠ 0 := by
      intro h0
      rw [h0] at hr
      simp only [mul_zero, zero_mul] at hr
      have := hr.symm
      simp only [mul_eq_zero] at this
      rcases this with (this | this) | this
      · exact hden this
      · exact hnk this
      · exact (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)) this
    have hf : ∀ j : ℕ, (j ! : K) ≠ 0 := fun j => by exact_mod_cast j.factorial_ne_zero
    simp only [pFqTerm, Fin.prod_univ_two, Fin.prod_univ_three, Fin.prod_univ_one,
      Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, one_pow, mul_one, Nat.add_sub_cancel_left]
    have := hd' k
    have := hf k
    have := hf m
    have := hf (k + m)
    field_simp
    linear_combination (rise a k * rise b k) * hr
  rw [sum_congr rfl hterm, ← mul_sum] at h
  have hL : pFqTerm ![d - a, d - b] ![d] 1 n =
      rise (d - a) n * rise (d - b) n / (rise d n * (n ! : K)) := by
    simp only [pFqTerm, Fin.prod_univ_two, Fin.prod_univ_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, one_pow, mul_one]
  rw [hL] at h
  have hf : (n ! : K) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hdn := hd' n
  rw [eq_div_iff (mul_ne_zero hdn hden)]
  generalize ∑ k ∈ range (n + 1), pFqTerm ![a, b, -(n : K)] ![d, e] 1 k = S at h ⊢
  field_simp at h
  linear_combination (-1 : K) * h

end UndergradKB.Combinatorics.AeqB
