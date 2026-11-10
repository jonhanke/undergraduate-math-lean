import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Factorial.Basic
import UndergradKB.Common.Attr

/-!
# Counting strings with exponential generating functions

Source: Keller--Trotter, *Applied Combinatorics* (2017), Section 8.6 (Examples 8.18--8.20).

For a finite alphabet `ι` and a predicate `p i : ℕ → Prop` on the number of occurrences of each
letter `i`, the number of strings of length `n` meeting all the constraints is `n!` times the
coefficient of `x^n` in the product of the series `∑_{m, p i m} x^m / m!`.  We prove this in general
(by induction on `n`, differentiating the product), and then derive the three examples.
-/

namespace UndergradKB.Combinatorics

open PowerSeries Finset Nat

noncomputable section

open scoped Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The exponential generating factor of a letter whose number of occurrences must satisfy `p`:
`∑_{m with p m} x^m / m!`. -/
def egfFactor (p : ℕ → Prop) : ℚ⟦X⟧ := PowerSeries.mk fun m => if p m then (1 : ℚ) / (m ! : ℚ) else 0

/-- The number of occurrences of the letter `i` in the string `w`. -/
def letterCount {n : ℕ} (w : Fin n → ι) (i : ι) : ℕ := (univ.filter fun j => w j = i).card

/-- The number of strings of length `n` over `ι` in which, for every letter `i`, the number of
occurrences of `i` satisfies `p i`. -/
def stringCount (n : ℕ) (p : ι → ℕ → Prop) : ℕ :=
  (univ.filter fun w : Fin n → ι => ∀ i, p i (letterCount w i)).card

theorem coeff_egfFactor (p : ℕ → Prop) (m : ℕ) :
    coeff m (egfFactor p) = if p m then (1 : ℚ) / (m ! : ℚ) else 0 := by
  simp [egfFactor]

theorem derivative_egfFactor (p : ℕ → Prop) :
    d⁄dX (egfFactor p) = egfFactor (fun m => p (m + 1)) := by
  ext n
  rw [coeff_derivative, coeff_egfFactor, coeff_egfFactor]
  by_cases h : p (n + 1)
  · simp only [h, ite_true, factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have : (n ! : ℚ) ≠ 0 := by positivity
    field_simp
  · simp [h]

/-- Leibniz rule for a finite product of power series. -/
theorem derivative_prod_finset {κ : Type*} [DecidableEq κ] (s : Finset κ) (f : κ → ℚ⟦X⟧) :
    d⁄dX (∏ i ∈ s, f i) = ∑ a ∈ s, d⁄dX (f a) * ∏ i ∈ s.erase a, f i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih =>
    have h2 : ∑ a ∈ s, d⁄dX (f a) * ∏ i ∈ (insert b s).erase a, f i =
        ∑ a ∈ s, f b * (d⁄dX (f a) * ∏ i ∈ s.erase a, f i) := by
      refine sum_congr rfl fun a ha => ?_
      rw [erase_insert_of_ne (show b ≠ a from fun h => hb (h ▸ ha)),
        prod_insert (fun h => hb (mem_of_mem_erase h))]
      ring
    rw [prod_insert hb, Derivation.leibniz, ih, sum_insert hb, erase_insert hb, smul_eq_mul,
      smul_eq_mul, h2, ← mul_sum]
    ring

/-- Shift the constraint of the letter `a` by one (as after removing one occurrence of `a`). -/
def shiftAt (p : ι → ℕ → Prop) (a : ι) : ι → ℕ → Prop :=
  Function.update p a (fun m => p a (m + 1))

theorem letterCount_cons {n : ℕ} (a : ι) (w : Fin n → ι) (i : ι) :
    letterCount (Fin.cons a w : Fin (n + 1) → ι) i = (if a = i then 1 else 0) + letterCount w i := by
  simp only [letterCount, Finset.card_filter, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem stringCount_succ (n : ℕ) (p : ι → ℕ → Prop) :
    stringCount (n + 1) p = ∑ a, stringCount n (shiftAt p a) := by
  unfold stringCount
  simp only [Finset.card_filter]
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => ι))
    (fun x => if ∀ i, p i (letterCount (Fin.consEquiv (fun _ : Fin (n + 1) => ι) x) i) then 1 else 0)
    (fun w => if ∀ i, p i (letterCount w i) then 1 else 0) (fun x => rfl)]
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun a _ => sum_congr rfl fun w _ => ?_
  have key : (∀ i, p i (letterCount (Fin.consEquiv (fun _ : Fin (n + 1) => ι) (a, w)) i)) ↔
      ∀ i, shiftAt p a i (letterCount w i) := by
    have hc : Fin.consEquiv (fun _ : Fin (n + 1) => ι) (a, w) = Fin.cons a w := rfl
    rw [hc]
    refine forall_congr' fun i => ?_
    rw [letterCount_cons]
    by_cases h : a = i
    · subst h
      simp [shiftAt, add_comm]
    · simp [shiftAt, h, Function.update_of_ne (Ne.symm h)]
  simp only [key]

theorem prod_egfFactor_shiftAt (p : ι → ℕ → Prop) (a : ι) :
    ∏ i, egfFactor (shiftAt p a i) = d⁄dX (egfFactor (p a)) * ∏ i ∈ univ.erase a, egfFactor (p i) := by
  rw [← Finset.mul_prod_erase univ _ (mem_univ a)]
  simp only [shiftAt, Function.update_self, derivative_egfFactor]
  congr 1
  refine prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (ne_of_mem_erase hi)]

/-- CO-206. **General exponential-generating-function counting.** The number of strings of length `n` in
which each letter `i` occurs a number of times satisfying `p i` equals `n!` times the coefficient
of `x^n` in `∏ᵢ ∑_{m, p i m} x^m / m!`. -/
@[kb "kellertrotter2017" "Examples 8.18-8.20, p. 195"]
theorem stringCount_eq (n : ℕ) (p : ι → ℕ → Prop) :
    (stringCount n p : ℚ) = (n ! : ℚ) * coeff n (∏ i, egfFactor (p i)) := by
  induction n generalizing p with
  | zero =>
    have hw : ∀ (w : Fin 0 → ι) i, letterCount w i = 0 := fun w i => by simp [letterCount]
    have hconst : ∀ i, constantCoeff (egfFactor (p i)) = if p i 0 then 1 else 0 := fun i => by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_egfFactor]
      simp
    simp only [stringCount, hw, Finset.card_filter, Finset.univ_unique, sum_singleton,
      factorial_zero, Nat.cast_one, one_mul, coeff_zero_eq_constantCoeff_apply, map_prod, hconst]
    by_cases h : ∀ i, p i 0
    · simp [h]
    · push Not at h
      obtain ⟨i, hi⟩ := h
      rw [Finset.prod_eq_zero (mem_univ i) (by simp [hi])]
      simpa using ⟨i, hi⟩
  | succ n ih =>
    rw [stringCount_succ]
    push_cast
    simp only [ih]
    have h : ∑ x, ∏ i, egfFactor (shiftAt p x i) = d⁄dX (∏ i, egfFactor (p i)) := by
      rw [derivative_prod_finset]
      exact sum_congr rfl fun a _ => prod_egfFactor_shiftAt p a
    rw [← mul_sum, ← map_sum, h, coeff_derivative, factorial_succ]
    push_cast
    ring

/-! ### The three examples -/

/-- The series `e^{a x}`. -/
def expRate (a : ℚ) : ℚ⟦X⟧ := rescale a (exp ℚ)

theorem coeff_expRate (a : ℚ) (n : ℕ) : coeff n (expRate a) = a ^ n / (n ! : ℚ) := by
  simp [expRate, coeff_rescale, coeff_exp, div_eq_mul_inv]

theorem expRate_mul (a b : ℚ) : expRate a * expRate b = expRate (a + b) :=
  exp_mul_exp_eq_exp_add a b

theorem egfFactor_true : egfFactor (fun _ => True) = expRate 1 := by
  ext m
  simp [coeff_egfFactor, coeff_expRate]

/-- The factor for "an even number of occurrences" is `cosh x = (e^x + e^{-x}) / 2`. -/
theorem egfFactor_even :
    egfFactor (fun m => Even m) = C (1 / 2 : ℚ) * (expRate 1 + expRate (-1)) := by
  ext m
  rw [coeff_egfFactor, coeff_C_mul, map_add, coeff_expRate, coeff_expRate]
  rcases Nat.even_or_odd m with h | h
  · simp [h, h.neg_one_pow]
    ring
  · simp [h.neg_one_pow, Nat.not_even_iff_odd.2 h]
    ring

/-- The factor for "at least one occurrence" is `e^x - 1`. -/
theorem egfFactor_pos : egfFactor (fun m => 0 < m) = expRate 1 - 1 := by
  ext m
  rw [coeff_egfFactor, map_sub, coeff_expRate, coeff_one]
  rcases Nat.eq_zero_or_pos m with rfl | h
  · simp
  · simp [h, Nat.pos_iff_ne_zero.1 h]

/-- The factor for "at most three occurrences" is the polynomial `1 + x + x²/2 + x³/6`. -/
theorem coeff_egfFactor_le_three (m : ℕ) :
    coeff m (egfFactor fun k => k ≤ 3) = if m ≤ 3 then (1 : ℚ) / (m ! : ℚ) else 0 := by
  rw [coeff_egfFactor]
  by_cases h : m ≤ 3 <;> simp [h]

/-- Example 8.18, exponential generating function: for ternary strings with an even number of
`0`s the product of the letter factors is `(e^{3x} + e^x) / 2`. -/
theorem egf_ternary_even_zeros :
    ∏ i : Fin 3, egfFactor (if i = 0 then (fun m => Even m) else fun _ => True) =
      C (1 / 2 : ℚ) * (expRate 3 + expRate 1) := by
  have e1 : ∀ i : Fin 3, egfFactor (if i = 0 then (fun m => Even m) else fun _ => True) =
      if i = 0 then C (1 / 2 : ℚ) * (expRate 1 + expRate (-1)) else expRate 1 := by
    intro i
    by_cases h : i = 0
    · simp [h, egfFactor_even]
    · simp [h, egfFactor_true]
  simp only [e1, Fin.prod_univ_three]
  simp only [Fin.reduceEq, ite_false, ite_true]
  have h2 : expRate 1 * expRate 1 = expRate 2 := by rw [expRate_mul]; norm_num
  calc C (1 / 2 : ℚ) * (expRate 1 + expRate (-1)) * expRate 1 * expRate 1
      = C (1 / 2 : ℚ) * (expRate 1 * (expRate 1 * expRate 1) + expRate (-1) * (expRate 1 * expRate 1)) := by ring
    _ = _ := by
      rw [h2, expRate_mul, expRate_mul]
      norm_num

/-- CO-206, Example 8.18. The number of ternary strings of length `n` with an even number of `0`s
is `(3^n + 1) / 2`. -/
@[kb "kellertrotter2017" "Example 8.18, p. 195"]
theorem ternary_even_zeros (n : ℕ) :
    2 * stringCount n (fun i : Fin 3 => if i = 0 then (fun m => Even m) else fun _ => True) =
      3 ^ n + 1 := by
  have h := stringCount_eq n (fun i : Fin 3 => if i = 0 then (fun m => Even m) else fun _ => True)
  rw [egf_ternary_even_zeros, coeff_C_mul, map_add, coeff_expRate, coeff_expRate] at h
  have hf : (n ! : ℚ) ≠ 0 := by positivity
  have : (2 * stringCount n (fun i : Fin 3 => if i = 0 then (fun m => Even m) else fun _ => True) :
      ℚ) = 3 ^ n + 1 := by
    rw [mul_comm, h]
    field_simp
    ring
  exact_mod_cast this

/-- Example 8.19, exponential generating function `(e^x - 1)(e^x - 1)e^x = e^{3x} - 2e^{2x} + e^x`. -/
theorem egf_ternary_zero_and_one :
    ∏ i : Fin 3, egfFactor (if i = 2 then (fun _ => True) else (fun m => 0 < m)) =
      expRate 3 - C (2 : ℚ) * expRate 2 + expRate 1 := by
  have e1 : ∀ i : Fin 3, egfFactor (if i = 2 then (fun _ => True) else (fun m => 0 < m)) =
      if i = 2 then expRate 1 else expRate 1 - 1 := by
    intro i
    by_cases h : i = 2
    · simp [h, egfFactor_true]
    · simp [h, egfFactor_pos]
  simp only [e1, Fin.prod_univ_three]
  simp only [Fin.reduceEq, ite_false, ite_true]
  have h2 : expRate 1 * expRate 1 = expRate 2 := by rw [expRate_mul]; norm_num
  have h3 : expRate 2 * expRate 1 = expRate 3 := by rw [expRate_mul]; norm_num
  rw [show (C (2 : ℚ) : ℚ⟦X⟧) = 2 from map_ofNat C 2]
  calc (expRate 1 - 1) * (expRate 1 - 1) * expRate 1
      = expRate 1 * expRate 1 * expRate 1 - 2 * (expRate 1 * expRate 1) + expRate 1 := by ring
    _ = _ := by rw [h2, h3]

/-- CO-206, Example 8.19. The number of ternary strings of length `n` containing at least one `0`
and at least one `1` is `3^n - 2 * 2^n + 1` (stated without subtraction). -/
@[kb "kellertrotter2017" "Example 8.19, p. 196"]
theorem ternary_zero_and_one (n : ℕ) :
    stringCount n (fun i : Fin 3 => if i = 2 then (fun _ => True) else (fun m => 0 < m)) +
      2 * 2 ^ n = 3 ^ n + 1 := by
  have h := stringCount_eq n (fun i : Fin 3 => if i = 2 then (fun _ => True) else (fun m => 0 < m))
  rw [egf_ternary_zero_and_one, map_add, map_sub, coeff_C_mul, coeff_expRate, coeff_expRate,
    coeff_expRate] at h
  have hf : (n ! : ℚ) ≠ 0 := by positivity
  have : (stringCount n (fun i : Fin 3 => if i = 2 then (fun _ => True) else (fun m => 0 < m)) :
      ℚ) + 2 * 2 ^ n = 3 ^ n + 1 := by
    rw [h]
    field_simp
    ring
  exact_mod_cast this

/-- Example 8.20: the constraint on the number of occurrences of the digit `d`: the digit `0`
occurs an even number of times, `1` at least once, `2` at most three times, others freely. -/
def passcodeConstraintNat (d : ℕ) : ℕ → Prop :=
  if d = 0 then (fun m => Even m) else if d = 1 then (fun m => 0 < m)
  else if d = 2 then (fun m => m ≤ 3) else fun _ => True

/-- The same, for the alphabet of the ten digits `Fin 10`. -/
def passcodeConstraint (d : Fin 10) : ℕ → Prop := passcodeConstraintNat d.val

theorem egf_passcode :
    ∏ i : Fin 10, egfFactor (passcodeConstraint i) =
      egfFactor (fun m => Even m) * egfFactor (fun m => 0 < m) * egfFactor (fun m => m ≤ 3) *
        expRate 1 ^ 7 := by
  show ∏ i : Fin 10, egfFactor (passcodeConstraintNat i.val) = _
  rw [Fin.prod_univ_eq_prod_range (fun k => egfFactor (passcodeConstraintNat k)) 10]
  simp [prod_range_succ, passcodeConstraintNat, egfFactor_true]
  ring

theorem expRate_pow (a : ℚ) (k : ℕ) : expRate a ^ k = expRate (k * a) := by
  induction k with
  | zero =>
    ext m
    simp [expRate, coeff_one]
  | succ k ih =>
    rw [pow_succ, ih, expRate_mul]
    congr 1
    push_cast
    ring

/-- The exponential generating function of Example 8.20, simplified. -/
theorem egf_passcode_simplified :
    ∏ i : Fin 10, egfFactor (passcodeConstraint i) =
      C (1 / 2 : ℚ) * (expRate 9 + expRate 7 - expRate 8 - expRate 6) *
        egfFactor (fun m => m ≤ 3) := by
  rw [egf_passcode, egfFactor_even, egfFactor_pos, expRate_pow]
  have h8 : expRate 1 * expRate 7 = expRate 8 := by rw [expRate_mul]; norm_num
  have h6 : expRate (-1) * expRate 7 = expRate 6 := by rw [expRate_mul]; norm_num
  have h9 : expRate 8 * expRate 1 = expRate 9 := by rw [expRate_mul]; norm_num
  have h7 : expRate 6 * expRate 1 = expRate 7 := by rw [expRate_mul]; norm_num
  have h : ((7 : ℕ) : ℚ) * 1 = 7 := by norm_num
  rw [h]
  calc C (1 / 2 : ℚ) * (expRate 1 + expRate (-1)) * (expRate 1 - 1) * egfFactor (fun m => m ≤ 3) *
        expRate 7
      = C (1 / 2 : ℚ) * (((expRate 1 * expRate 7) * expRate 1 + (expRate (-1) * expRate 7) * expRate 1)
          - (expRate 1 * expRate 7 + expRate (-1) * expRate 7)) * egfFactor (fun m => m ≤ 3) := by
        ring
    _ = C (1 / 2 : ℚ) * ((expRate 8 * expRate 1 + expRate 6 * expRate 1)
          - (expRate 8 + expRate 6)) * egfFactor (fun m => m ≤ 3) := by rw [h8, h6]
    _ = _ := by rw [h9, h7]; ring

/-- CO-206, Example 8.20. The number of eight-digit passcodes (digits `0`-`9`) with an even number
of `0`s, at least one `1`, and at most three `2`s is `33847837`. -/
@[kb "kellertrotter2017" "Example 8.20, p. 196"]
theorem passcode_count : stringCount 8 passcodeConstraint = 33847837 := by
  have h := stringCount_eq 8 passcodeConstraint
  rw [egf_passcode_simplified, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simp only [coeff_C_mul, map_add, map_sub, coeff_expRate, coeff_egfFactor_le_three] at h
  simp [Finset.sum_range_succ, Nat.factorial] at h
  norm_num at h
  exact_mod_cast h

end

end UndergradKB.Combinatorics
