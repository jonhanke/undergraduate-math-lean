import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.AeqB.ClosedForm
import UndergradKB.Combinatorics.AeqB.AperyNotHyper
import UndergradKB.Combinatorics.AeqB.NotClosedForm
import UndergradKB.Combinatorics.AeqB.FirstThird

/-!
# Hypergeometric solutions of the first-third recurrence

The sums `S(n) = ∑_{k ≤ n} C(3n, k)` satisfy a recurrence of order two whose operator factors as
`(A(n) N - B(n)) (N - 8)`.  This file proves that every hypergeometric solution of that recurrence
(over a field of characteristic zero) satisfies `y(n+1) = 8 y(n)` for large `n`.

The proof shows that a hypergeometric solution with `y(n+1) ≠ 8 y(n)` would give a rational function
`P/Q` solving the inhomogeneous first-order equation
`b₁ P(n+1) Q(n) - 8 a₁ P(n) Q(n+1) = a₁ q₀ Q(n) Q(n+1)`; shift divisibility forces `Q` to be constant,
and then a polynomial solution would have to have degree two, where a direct computation shows there
is none.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace UndergradKB.Combinatorics.AeqB
open Polynomial Filter

section
variable {K : Type*} [Field K] [CharZero K]

/-- `a₁ = 2(X+2)(2X+3) = 4X² + 14X + 12`. -/
def ftA1 : K[X] := C 4 * X ^ 2 + C 14 * X + C 12

/-- `b₁ = 3(3X+1)(3X+2) = 27X² + 27X + 6`. -/
def ftB1 : K[X] := C 27 * X ^ 2 + C 27 * X + C 6

/-- `q₀ = 5X² + 11X + 4`. -/
def ftQ0 : K[X] := C 5 * X ^ 2 + C 11 * X + C 4

/-! ### No polynomial solutions -/

lemma ft_poly_noSol (P : K[X]) (c : K)
    (h : ftB1 * P.comp (X + C 1) - C 8 * ftA1 * P = ftA1 * ftQ0 * C c) : c = 0 := by
  have hdeg : P.natDegree ≤ 2 := by
    by_contra hlt
    push Not at hlt
    obtain ⟨M, hM⟩ : ∃ M, P.natDegree = M + 1 := ⟨P.natDegree - 1, by omega⟩
    have hγ : P.coeff (M + 1) ≠ 0 := by
      have := leadingCoeff_ne_zero.2 (show P ≠ 0 by
        intro h0; rw [h0] at hM; simp at hM)
      rwa [leadingCoeff, hM] at this
    have e0 : P.comp (X + C 0) = P := by simp
    have h' : C 1 * (C 27 * X ^ 2 + C 27 * X + C 6) * P.comp (X + C 1)
        + C (-8) * (C 4 * X ^ 2 + C 14 * X + C 12) * P.comp (X + C 0)
        = ftA1 * ftQ0 * C c := by
      have hC1 : ∀ r : K[X], C (1 : K) * r = r := fun r => by rw [C_1, one_mul]
      rw [e0, C_neg, hC1]
      simp only [ftB1, ftA1, ftQ0] at h ⊢
      linear_combination h
    have e := congrArg (fun q => q.coeff (M + 1 + 2)) h'
    simp only [coeff_add] at e
    rw [(nc_quad 1 6 27 27 1 P M hM).1, (nc_quad (-8) 12 14 4 0 P M hM).1] at e
    have hz : (ftA1 * ftQ0 * C c : K[X]).coeff (M + 1 + 2) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have : (ftA1 * ftQ0 * C c : K[X]).natDegree ≤ 4 := by
        unfold ftA1 ftQ0
        compute_degree
      omega
    rw [hz] at e
    exact hγ (by
      have : P.coeff (M + 1) * (-5) = 0 := by linear_combination e
      exact (mul_eq_zero.1 this).resolve_right (by norm_num))
  have hP : ∀ x : K, P.eval x = P.coeff 2 * x ^ 2 + P.coeff 1 * x + P.coeff 0 := by
    intro x
    rw [eval_eq_sum_range' (show P.natDegree < 3 by omega)]
    simp [Finset.sum_range_succ]
    ring
  have e0 := congrArg (Polynomial.eval (0 : K)) h
  have e1 := congrArg (Polynomial.eval (1 : K)) h
  have e2 := congrArg (Polynomial.eval (2 : K)) h
  have e3 := congrArg (Polynomial.eval (3 : K)) h
  simp only [eval_sub, eval_mul, eval_comp, eval_add, eval_X, eval_C, eval_pow, ftB1, ftA1, ftQ0,
    hP] at e0 e1 e2 e3
  linear_combination (25 / 492 : K) * e0 - (1093 / 14760 : K) * e1 + (631 / 13776 : K) * e2
    - (77 / 7380 : K) * e3

/-! ### The denominator is constant -/

/-- The two quadratic factors in the shift-divisibility argument, as predicates on a point. -/
def ftPm (M : ℕ) (m0 : K) (x : ℚ) : Prop :=
  (4 : K) * (x : K) ^ 2 + (4 * ((M : K) + 1) + 14) * (x : K) + m0 = 0

def ftPn (M : ℕ) (n0 : K) (x : ℚ) : Prop :=
  (27 : K) * (x : K) ^ 2 + (-27 * (M : K)) * (x : K) + n0 = 0

lemma ft_two_roots (a b c : K) (x y : ℚ) (hxy : x ≠ y) (hx : a * (x : K) ^ 2 + b * x + c = 0)
    (hy : a * (y : K) ^ 2 + b * y + c = 0) : a * ((x : K) + y) + b = 0 := by
  have h : ((x : K) - y) * (a * ((x : K) + y) + b) = 0 := by linear_combination hx - hy
  exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 (by exact_mod_cast hxy))

lemma ftPm_pair (M : ℕ) (m0 : K) (x y : ℚ) (hxy : x ≠ y) (hs : -7 / 2 ≤ x + y)
    (hx : ftPm M m0 x) (hy : ftPm M m0 y) : False := by
  have h := ft_two_roots _ _ _ x y hxy hx hy
  have h2 : (4 * (x + y) + (4 * ((M : ℚ) + 1) + 14) : ℚ) = 0 := by
    apply Rat.cast_injective (α := K)
    push_cast
    linear_combination h
  have : (0 : ℚ) ≤ M := Nat.cast_nonneg M
  linarith

lemma ftPn_pair (M : ℕ) (n0 : K) (x y : ℚ) (hxy : x ≠ y) (hs : x + y < 0)
    (hx : ftPn M n0 x) (hy : ftPn M n0 y) : False := by
  have h := ft_two_roots _ _ _ x y hxy hx hy
  have h2 : (27 * (x + y) + (-27 * (M : ℚ)) : ℚ) = 0 := by
    apply Rat.cast_injective (α := K)
    push_cast
    linear_combination h
  have : (0 : ℚ) ≤ M := Nat.cast_nonneg M
  linarith

lemma ft_AB_root (q : ℚ) (h : (4 * q ^ 2 + 14 * q + 12) * (27 * q ^ 2 + 27 * q + 6) = 0) :
    (ftA1 * ftB1 : K[X]).eval (q : K) = 0 := by
  simp only [ftA1, ftB1, eval_mul, eval_add, eval_C, eval_pow, eval_X]
  exact_mod_cast h

lemma ft_quad_form (m : K[X]) (h : m.natDegree ≤ 2) :
    m = C (m.coeff 2) * X ^ 2 + C (m.coeff 1) * X + C (m.coeff 0) := by
  conv_lhs => rw [as_sum_range' m 3 (by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, ← C_mul_X_pow_eq_monomial]
  ring

lemma ft_Q_const (Q : K[X]) (hQ : Q ≠ 0) (h1 : Q ∣ ftA1 * Q.comp (X + C 1))
    (h2 : Q.comp (X + C 1) ∣ ftB1 * Q) : Q.natDegree = 0 := by
  by_contra hd
  obtain ⟨M, hM⟩ : ∃ M, Q.natDegree = M + 1 := ⟨Q.natDegree - 1, by omega⟩
  have hγ : Q.coeff (M + 1) ≠ 0 := by
    have := leadingCoeff_ne_zero.2 hQ
    rwa [leadingCoeff, hM] at this
  have hQ1 : Q.comp (X + C 1) ≠ 0 := comp_X_add_C_ne_zero' hQ 1
  have hdA : (ftA1 : K[X]).natDegree = 2 := natDegree_quadratic (by norm_num)
  have hdB : (ftB1 : K[X]).natDegree = 2 := natDegree_quadratic (by norm_num)
  have hA0 : (ftA1 : K[X]) ≠ 0 := fun h0 => by rw [h0] at hdA; simp at hdA
  have hB0 : (ftB1 : K[X]) ≠ 0 := fun h0 => by rw [h0] at hdB; simp at hdB
  obtain ⟨m, hm⟩ := h1
  obtain ⟨m', hm'⟩ := h2
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    exact mul_ne_zero hA0 hQ1 hm
  have hn0 : m' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm'
    exact mul_ne_zero hB0 hQ hm'
  have hdm : m.natDegree = 2 := by
    have := congrArg natDegree hm
    rw [natDegree_mul hA0 hQ1, natDegree_mul hQ hm0, natDegree_comp_shift, hdA, hM] at this
    omega
  have hdn : m'.natDegree = 2 := by
    have := congrArg natDegree hm'
    rw [natDegree_mul hB0 hQ, natDegree_mul hQ1 hn0, natDegree_comp_shift, hdB, hM] at this
    omega
  have hprod : m * m' = ftA1 * ftB1 := by
    refine mul_left_cancel₀ (mul_ne_zero hQ hQ1) ?_
    linear_combination (-(Q.comp (X + C 1) * m')) * hm + (-(ftA1 * Q.comp (X + C 1))) * hm'
  have fm := ft_quad_form m hdm.le
  have fn := ft_quad_form m' hdn.le
  generalize m.coeff 2 = m2 at fm
  generalize m.coeff 1 = m1 at fm
  generalize m.coeff 0 = m0 at fm
  generalize m'.coeff 2 = n2 at fn
  generalize m'.coeff 1 = n1 at fn
  generalize m'.coeff 0 = n0 at fn
  have e0 : Q.comp (X + C 0) = Q := by simp
  have hC1 : ∀ r : K[X], C (1 : K) * r = r := fun r => by rw [C_1, one_mul]
  -- coefficients of `ftA1 * Q⁺ = Q * m`
  have eA : C 1 * (C 4 * X ^ 2 + C 14 * X + C 12) * Q.comp (X + C 1)
      = C 1 * (C m2 * X ^ 2 + C m1 * X + C m0) * Q.comp (X + C 0) := by
    rw [e0, hC1, hC1]
    have := hm
    rw [fm] at this
    simp only [ftA1] at this
    linear_combination this
  have eB : C 1 * (C 27 * X ^ 2 + C 27 * X + C 6) * Q.comp (X + C 0)
      = C 1 * (C n2 * X ^ 2 + C n1 * X + C n0) * Q.comp (X + C 1) := by
    rw [e0, hC1, hC1]
    have := hm'
    rw [fn] at this
    simp only [ftB1] at this
    linear_combination this
  have a4 := congrArg (fun q => q.coeff (M + 1 + 2)) eA
  have a3 := congrArg (fun q => q.coeff (M + 2)) eA
  have b4 := congrArg (fun q => q.coeff (M + 1 + 2)) eB
  have b3 := congrArg (fun q => q.coeff (M + 2)) eB
  rw [(nc_quad 1 12 14 4 1 Q M hM).1, (nc_quad 1 m0 m1 m2 0 Q M hM).1] at a4
  rw [(nc_quad 1 12 14 4 1 Q M hM).2, (nc_quad 1 m0 m1 m2 0 Q M hM).2] at a3
  rw [(nc_quad 1 6 27 27 0 Q M hM).1, (nc_quad 1 n0 n1 n2 1 Q M hM).1] at b4
  rw [(nc_quad 1 6 27 27 0 Q M hM).2, (nc_quad 1 n0 n1 n2 1 Q M hM).2] at b3
  have hm2 : m2 = 4 := by
    have : Q.coeff (M + 1) * (m2 - 4) = 0 := by linear_combination -a4
    have := (mul_eq_zero.1 this).resolve_left hγ
    linear_combination this
  have hn2 : n2 = 27 := by
    have : Q.coeff (M + 1) * (n2 - 27) = 0 := by linear_combination -b4
    have := (mul_eq_zero.1 this).resolve_left hγ
    linear_combination this
  subst hm2 hn2
  have hm1 : m1 = 4 * ((M : K) + 1) + 14 := by
    have : Q.coeff (M + 1) * (m1 - (4 * ((M : K) + 1) + 14)) = 0 := by linear_combination -a3
    have := (mul_eq_zero.1 this).resolve_left hγ
    linear_combination this
  have hn1 : n1 = -27 * (M : K) := by
    have : Q.coeff (M + 1) * (n1 - (-27 * (M : K))) = 0 := by linear_combination -b3
    have := (mul_eq_zero.1 this).resolve_left hγ
    linear_combination this
  subst hm1 hn1
  have hroot : ∀ q : ℚ, (4 * q ^ 2 + 14 * q + 12) * (27 * q ^ 2 + 27 * q + 6) = 0 →
      ftPm M m0 q ∨ ftPn M n0 q := by
    intro q hq
    have := congrArg (Polynomial.eval (q : K)) hprod
    rw [eval_mul, ft_AB_root q hq] at this
    rw [fm, fn] at this
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X] at this
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr h
  have r1 := hroot (-2) (by norm_num)
  have r2 := hroot (-3 / 2) (by norm_num)
  have r3 := hroot (-1 / 3) (by norm_num)
  have r4 := hroot (-2 / 3) (by norm_num)
  have pm : ∀ x y : ℚ, x ≠ y → -7 / 2 ≤ x + y → ftPm M m0 x → ftPm M m0 y → False :=
    fun x y h1 h2 h3 h4 => ftPm_pair M m0 x y h1 h2 h3 h4
  have pn : ∀ x y : ℚ, x ≠ y → x + y < 0 → ftPn M n0 x → ftPn M n0 y → False :=
    fun x y h1 h2 h3 h4 => ftPn_pair M n0 x y h1 h2 h3 h4
  rcases r1 with s1 | s1 <;> rcases r2 with s2 | s2 <;> rcases r3 with s3 | s3 <;>
    rcases r4 with s4 | s4 <;>
    first
    | exact pm _ _ (by norm_num) (by norm_num) s1 s2
    | exact pm _ _ (by norm_num) (by norm_num) s1 s3
    | exact pm _ _ (by norm_num) (by norm_num) s1 s4
    | exact pm _ _ (by norm_num) (by norm_num) s2 s3
    | exact pm _ _ (by norm_num) (by norm_num) s2 s4
    | exact pm _ _ (by norm_num) (by norm_num) s3 s4
    | exact pn _ _ (by norm_num) (by norm_num) s1 s2
    | exact pn _ _ (by norm_num) (by norm_num) s1 s3
    | exact pn _ _ (by norm_num) (by norm_num) s2 s3

/-! ### No rational solution -/

lemma ft_no_ratsol (P Q : K[X]) (hQ : Q ≠ 0)
    (h : ftB1 * P.comp (X + C 1) * Q - C 8 * ftA1 * P * Q.comp (X + C 1)
      - ftA1 * ftQ0 * Q * Q.comp (X + C 1) = 0) : False := by
  classical
  have hG0 : GCDMonoid.gcd P Q ≠ 0 := fun h0 =>
    hQ (zero_dvd_iff.1 (h0 ▸ GCDMonoid.gcd_dvd_right P Q))
  have hc := isCoprime_div_gcd_div_gcd (p := P) hQ
  obtain ⟨P', hP'⟩ := GCDMonoid.gcd_dvd_left P Q
  obtain ⟨Q', hQ'⟩ := GCDMonoid.gcd_dvd_right P Q
  generalize GCDMonoid.gcd P Q = G at hc hP' hQ' hG0
  have eP : P / G = P' := by rw [hP']; exact mul_div_cancel_left₀ P' hG0
  have eQ : Q / G = Q' := by rw [hQ']; exact mul_div_cancel_left₀ Q' hG0
  rw [eP, eQ] at hc
  subst hP' hQ'
  have hQ'0 : Q' ≠ 0 := right_ne_zero_of_mul hQ
  have hG1 : G.comp (X + C 1) ≠ 0 := comp_X_add_C_ne_zero' hG0 1
  have E : ftB1 * P'.comp (X + C 1) * Q' - C 8 * ftA1 * P' * Q'.comp (X + C 1)
      - ftA1 * ftQ0 * Q' * Q'.comp (X + C 1) = 0 := by
    refine (mul_eq_zero.1 (show (G * G.comp (X + C 1)) * (ftB1 * P'.comp (X + C 1) * Q'
        - C 8 * ftA1 * P' * Q'.comp (X + C 1) - ftA1 * ftQ0 * Q' * Q'.comp (X + C 1)) = 0 by
      rw [mul_comp, mul_comp] at h
      linear_combination h)).resolve_left (mul_ne_zero hG0 hG1)
  have h8 : IsUnit (C (8 : K) : K[X]) := isUnit_C.2 (by norm_num)
  have d1 : Q' ∣ ftA1 * Q'.comp (X + C 1) := by
    have : Q' ∣ P' * (C 8 * (ftA1 * Q'.comp (X + C 1))) :=
      ⟨ftB1 * P'.comp (X + C 1) - ftA1 * ftQ0 * Q'.comp (X + C 1), by
        linear_combination (-1 : K[X]) * E⟩
    exact (h8.dvd_mul_left).1 (hc.symm.dvd_of_dvd_mul_left this)
  have d2 : Q'.comp (X + C 1) ∣ ftB1 * Q' := by
    have : Q'.comp (X + C 1) ∣ P'.comp (X + C 1) * (ftB1 * Q') :=
      ⟨C 8 * ftA1 * P' + ftA1 * ftQ0 * Q', by linear_combination E⟩
    exact (isCoprime_comp_shift hc.symm 1).dvd_of_dvd_mul_left this
  have hdeg := ft_Q_const Q' hQ'0 d1 d2
  have hQc : Q' = C (Q'.coeff 0) := eq_C_of_natDegree_eq_zero hdeg
  have hγ : Q'.coeff 0 ≠ 0 := fun h0 => hQ'0 (by rw [hQc, h0, C_0])
  generalize Q'.coeff 0 = c at hQc hγ
  subst hQc
  simp only [C_comp] at E
  have E2 : C c * (ftB1 * P'.comp (X + C 1) - C 8 * ftA1 * P' - ftA1 * ftQ0 * C c) = 0 := by
    linear_combination E
  have E3 := (mul_eq_zero.1 E2).resolve_left (C_ne_zero.2 hγ)
  exact hγ (ft_poly_noSol P' c (by linear_combination E3))

/-! ### Hypergeometric solutions have ratio `8` -/

/-- `A(n) = 2(n+2)(2n+3)(5n²+11n+4)`, the leading coefficient of the recurrence. -/
def ftAp : K[X] := ftA1 * ftQ0

/-- `B(n) = 3(3n+1)(3n+2)(5n²+21n+20)`. -/
def ftBp : K[X] := ftB1 * ftQ0.comp (X + C 1)

lemma ftAp_eval_ne (n : ℕ) : (ftAp : K[X]).eval (n : K) ≠ 0 := by
  have : (ftAp : K[X]).eval (n : K) = (((4 * n ^ 2 + 14 * n + 12) * (5 * n ^ 2 + 11 * n + 4) : ℕ) : K) := by
    simp only [ftAp, ftA1, ftQ0, eval_mul, eval_add, eval_C, eval_pow, eval_X]
    push_cast
    ring
  rw [this]
  exact Nat.cast_ne_zero.2 (by positivity)

lemma ftBp_eval_ne (n : ℕ) : (ftBp : K[X]).eval (n : K) ≠ 0 := by
  have : (ftBp : K[X]).eval (n : K)
      = (((27 * n ^ 2 + 27 * n + 6) * (5 * (n + 1) ^ 2 + 11 * (n + 1) + 4) : ℕ) : K) := by
    simp only [ftBp, ftB1, ftQ0, eval_mul, eval_add, eval_C, eval_pow, eval_X, eval_comp]
    push_cast
    ring
  rw [this]
  exact Nat.cast_ne_zero.2 (by positivity)

theorem ft_hyper_ratio8 (y : ℕ → K) (hy : IsHypergeometric y)
    (hL : ∀ᶠ n : ℕ in atTop, (C 8 * ftBp : K[X]).eval (n : K) * y n
      + (-(C 8 * ftAp + ftBp) : K[X]).eval (n : K) * y (n + 1)
      + (ftAp : K[X]).eval (n : K) * y (n + 2) = 0) :
    ∀ᶠ n : ℕ in atTop, y (n + 1) = 8 * y n := by
  have key : ∀ᶠ n : ℕ in atTop, (ftAp : K[X]).eval (n : K) * (y (n + 2) - 8 * y (n + 1))
      = (ftBp : K[X]).eval (n : K) * (y (n + 1) - 8 * y n) := by
    filter_upwards [hL] with n hn
    simp only [eval_add, eval_neg, eval_mul, eval_C] at hn
    linear_combination hn
  by_cases hz : ∀ᶠ n : ℕ in atTop, y (n + 1) - 8 * y n = 0
  · exact hz.mono fun n hn => by linear_combination hn
  exfalso
  have hnz : ∀ᶠ n : ℕ in atTop, y (n + 1) - 8 * y n ≠ 0 := by
    obtain ⟨N, hN⟩ := eventually_atTop.1 key
    obtain ⟨n0, hn0N, hn0⟩ := Filter.frequently_atTop.1 (Filter.not_eventually.1 hz) N
    refine eventually_atTop.2 ⟨n0, fun n hn => ?_⟩
    induction n, hn using Nat.le_induction with
    | base => exact hn0
    | succ n hn ih =>
      intro h0
      have h0' : y (n + 2) - 8 * y (n + 1) = 0 := h0
      have := hN n (hn0N.trans hn)
      rw [h0', mul_zero] at this
      exact mul_ne_zero (ftBp_eval_ne n) ih this.symm
  obtain ⟨-, p, q, hp, hq, hpq⟩ := hy
  have hQ0 : (C 8 * p + q : K[X]) ≠ 0 := by
    intro h0
    apply hp
    apply eq_zero_of_eventually_eval_eq_zero
    filter_upwards [hpq, hnz] with n hn hw
    have e := congrArg (Polynomial.eval (n : K)) h0
    simp only [eval_add, eval_mul, eval_C, eval_zero] at e
    have : p.eval (n : K) * (y (n + 1) - 8 * y n) = 0 := by linear_combination hn - y n * e
    exact (mul_eq_zero.1 this).resolve_right hw
  have h1 : ∀ᶠ n : ℕ in atTop, p.eval ((n + 1 : ℕ) : K) * y (n + 1 + 1)
      + q.eval ((n + 1 : ℕ) : K) * y (n + 1) = 0 := (tendsto_add_atTop_nat 1).eventually hpq
  have hstar : ftAp * (C 8 * p + q).comp (X + C 1) * q
      + ftBp * p.comp (X + C 1) * (C 8 * p + q) = 0 := by
    apply eq_zero_of_eventually_eval_eq_zero
    filter_upwards [hpq, h1, key, hnz] with n h0 h1 hk hw
    have h1' : p.eval ((n : K) + 1) * y (n + 2) + q.eval ((n : K) + 1) * y (n + 1) = 0 := by
      have := h1
      push_cast at this
      exact this
    simp only [eval_add, eval_mul, eval_comp, eval_C, eval_X]
    refine mul_left_cancel₀ hw ?_
    rw [mul_zero]
    linear_combination (-8 * (ftAp : K[X]).eval (n : K) * (8 * p.eval ((n : K) + 1)
        + q.eval ((n : K) + 1))) * h0
      + ((ftAp : K[X]).eval (n : K) * (8 * p.eval (n : K) + q.eval (n : K))) * h1'
      - (p.eval ((n : K) + 1) * (8 * p.eval (n : K) + q.eval (n : K))) * hk
  refine ft_no_ratsol (-(p * ftQ0)) (C 8 * p + q) hQ0 ?_
  simp only [neg_comp, mul_comp]
  simp only [ftAp, ftBp] at hstar
  linear_combination (-1 : K[X]) * hstar

/-! ### The headline theorem -/

/-- CO-502. The sum of the first third of the binomial coefficients, `S(n) = ∑_{k ≤ n} C(3n, k)`, is
not of closed form: it is not, for large `n`, a linear combination of a fixed number of
hypergeometric terms (over any field of characteristic zero).  Proof: `S` satisfies the order-two
recurrence `ftS_rec_K` (built from Pascal's rule and the exact first-order relation
`(n+1)(2n+1)(S(n+1) - 8 S(n)) = -(5n²+11n+4) C(3n,n)`).  That recurrence does have the hypergeometric
solution `8^n`, but Algorithm Hyper's candidate analysis (here replaced by a direct argument,
`ft_hyper_ratio8`) shows that every hypergeometric solution has ratio `8` eventually; so a closed form
would satisfy `S(n+1) = 8 S(n)` for large `n`, contradicting the relation above. -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 8.8.1, p. 160"]
theorem firstThird_not_closedForm (K : Type*) [Field K] [CharZero K] :
    ¬ IsClosedForm (fun n : ℕ => ∑ k ∈ Finset.range (n + 1), (((3 * n).choose k : ℕ) : K)) := by
  intro hf
  have hS : (fun n : ℕ => ∑ k ∈ Finset.range (n + 1), (((3 * n).choose k : ℕ) : K))
      = fun n : ℕ => (ftS n : K) := by
    funext n
    simp [ftS]
  rw [hS] at hf
  have hL : ∀ n : ℕ, (C 8 * ftBp : K[X]).eval (n : K) * (ftS n : K)
      + (-(C 8 * ftAp + ftBp) : K[X]).eval (n : K) * (ftS (n + 1) : K)
      + (ftAp : K[X]).eval (n : K) * (ftS (n + 2) : K) = 0 := by
    intro n
    have h := ftS_rec_K (K := K) n
    simp only [ftAp, ftBp, ftA1, ftB1, ftQ0, eval_add, eval_neg, eval_mul, eval_C, eval_pow,
      eval_X, eval_comp]
    linear_combination h
  obtain ⟨r, J, u, h1, h3, h4⟩ := nc_closed_parts (C 8 * ftBp) (-(C 8 * ftAp + ftBp)) ftAp
    (fun n => (ftS n : K)) hf hL
  have hall : ∀ᶠ n : ℕ in atTop, ∀ j ∈ J, u j (n + 1) = 8 * u j n :=
    (Filter.eventually_all_finset J).2 fun j hj => ft_hyper_ratio8 (u j) (h1 j hj) (h4 j hj)
  have h3' : ∀ᶠ n : ℕ in atTop, (ftS (n + 1) : K) = ∑ j ∈ J, u j (n + 1) :=
    (tendsto_add_atTop_nat 1).eventually h3
  obtain ⟨n, hn1, hn2, hn3⟩ := (hall.and (h3.and h3')).exists
  have hsum : (ftS (n + 1) : K) = 8 * (ftS n : K) := by
    rw [hn3, hn2, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j hj => hn1 j hj
  have hd := ftS_diff_K (K := K) n
  rw [hsum] at hd
  have h0 : (5 * (n : K) ^ 2 + 11 * n + 4) * ((3 * n).choose n : K) = 0 := by
    linear_combination hd
  have hne : (5 * (n : K) ^ 2 + 11 * n + 4) * ((3 * n).choose n : K) ≠ 0 := by
    have : ((((5 * n ^ 2 + 11 * n + 4) * (3 * n).choose n : ℕ)) : K) ≠ 0 :=
      Nat.cast_ne_zero.2 (Nat.pos_iff_ne_zero.1 (Nat.mul_pos (by positivity)
        (Nat.choose_pos (by omega))))
    push_cast at this
    exact this
  exact hne h0

end

end UndergradKB.Combinatorics.AeqB

end
