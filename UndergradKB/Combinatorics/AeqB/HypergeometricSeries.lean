import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import UndergradKB.Common.Attr

/-!
# Hypergeometric series (Petkovsek-Wilf-Zeilberger, "A = B", Chapter 3)

The term sequence of `pFq[a; b; x]`, its term ratio, well-definedness and termination, the
2F1 form of the generalized falling factorial binomial theorem, the terminating Gauss
(Chu-Vandermonde) summation and the series `1F0[a; ; z] = (1 - z)^(-a)`.
-/

set_option linter.unusedSectionVars false

namespace UndergradKB.Combinatorics.AeqB
open Finset Polynomial Nat

variable {K : Type*} [Field K] [CharZero K]

/-! ### Terms of a hypergeometric series -/

/-- CO-353 (series form, p. 45). A sequence `t` is the term sequence of a hypergeometric series:
`t 0 = 1` and `t (k+1) / t k = P(k) / Q(k)` for polynomials `P`, `Q` in `k`, `Q` never vanishing
at a natural number (stated multiplicatively so that vanishing terms are allowed). -/
@[kb "petkovsekwilfzeilberger1996" "Definition (unnumbered) hypergeometric series, p. 45"]
def IsHypergeometricSeries (t : ℕ → K) : Prop :=
  t 0 = 1 ∧ ∃ P Q : K[X], ∀ k : ℕ, Q.eval (k : K) ≠ 0 ∧
    Q.eval (k : K) * t (k + 1) = P.eval (k : K) * t k

/-- CO-354. The `k`-th term `(a₁)_k ⋯ (a_p)_k x^k / ((b₁)_k ⋯ (b_q)_k k!)` of the series
`pFq[a₁..a_p; b₁..b_q; x]` (eq. 3.2.1); rising factorials are `ascPochhammer`. -/
@[kb "petkovsekwilfzeilberger1996" "Equation (3.2.1), p. 46"]
noncomputable def pFqTerm {p q : ℕ} (a : Fin p → K) (b : Fin q → K) (x : K) (k : ℕ) : K :=
  (∏ i, (ascPochhammer K k).eval (a i)) * x ^ k /
    ((∏ j, (ascPochhammer K k).eval (b j)) * (k ! : K))

/-- CO-359. No lower parameter is a nonpositive integer (the series is then well defined). -/
def LowerOK {q : ℕ} (b : Fin q → K) : Prop := ∀ (j : Fin q) (n : ℕ), b j ≠ -(n : K)

theorem pFqTerm_zero {p q : ℕ} (a : Fin p → K) (b : Fin q → K) (x : K) :
    pFqTerm a b x 0 = 1 := by
  simp [pFqTerm]

theorem eval_ascPochhammer_ne_zero {y : K} (hy : ∀ n : ℕ, y ≠ -(n : K)) (k : ℕ) :
    (ascPochhammer K k).eval y ≠ 0 := by
  rw [Ne, ascPochhammer_eval_eq_zero_iff]
  rintro ⟨n, -, hn⟩
  exact hy n (by linear_combination hn)

theorem LowerOK.prod_ne_zero {q : ℕ} {b : Fin q → K} (hb : LowerOK b) (k : ℕ) :
    (∏ j, (ascPochhammer K k).eval (b j)) ≠ 0 :=
  prod_ne_zero_iff.2 fun j _ => eval_ascPochhammer_ne_zero (hb j) k

theorem LowerOK.prod_add_ne_zero {q : ℕ} {b : Fin q → K} (hb : LowerOK b) (k : ℕ) :
    (∏ j, ((k : K) + b j)) ≠ 0 :=
  prod_ne_zero_iff.2 fun j _ h => hb j k (by linear_combination h)

/-- CO-354. The term ratio of `pFq`: `t_{k+1} (k+b₁)⋯(k+b_q)(k+1) = t_k (k+a₁)⋯(k+a_p) x`
(eq. 3.2.1), provided no lower parameter is a nonpositive integer. -/
@[kb "petkovsekwilfzeilberger1996" "Equation (3.2.1), p. 46"]
theorem pFqTerm_succ_mul {p q : ℕ} (a : Fin p → K) {b : Fin q → K} (hb : LowerOK b) (x : K)
    (k : ℕ) :
    pFqTerm a b x (k + 1) * ((∏ j, ((k : K) + b j)) * ((k : K) + 1)) =
      pFqTerm a b x k * ((∏ i, ((k : K) + a i)) * x) := by
  have h1 := hb.prod_ne_zero k
  have h2 := hb.prod_add_ne_zero k
  have h3 : (k ! : K) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have h4 : ((k : K) + 1) ≠ 0 := by exact_mod_cast k.succ_ne_zero
  simp only [pFqTerm, ascPochhammer_succ_eval, prod_mul_distrib, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_succ, pow_succ]
  have e1 : ∀ (c : Fin q → K), ∏ j, (c j + (k : K)) = ∏ j, ((k : K) + c j) := fun c =>
    prod_congr rfl fun j _ => add_comm _ _
  have e2 : ∀ (c : Fin p → K), ∏ j, (c j + (k : K)) = ∏ j, ((k : K) + c j) := fun c =>
    prod_congr rfl fun j _ => add_comm _ _
  rw [e1, e2]
  field_simp

/-- CO-353 / CO-354. The term sequence of `pFq` is a hypergeometric series (`t_0 = 1`, rational
term ratio), with ratio `(k+a₁)⋯(k+a_p) x / ((k+b₁)⋯(k+b_q)(k+1))`. -/
@[kb "petkovsekwilfzeilberger1996" "Definition (unnumbered) hypergeometric series, p. 45"]
theorem isHypergeometricSeries_pFqTerm {p q : ℕ} (a : Fin p → K) {b : Fin q → K}
    (hb : LowerOK b) (x : K) : IsHypergeometricSeries (pFqTerm a b x) := by
  refine ⟨pFqTerm_zero a b x, C x * ∏ i, (X + C (a i)), (∏ j, (X + C (b j))) * (X + 1), ?_⟩
  intro k
  have := pFqTerm_succ_mul a hb x k
  simp only [eval_mul, eval_prod, eval_add, eval_X, eval_C, eval_one]
  refine ⟨mul_ne_zero (hb.prod_add_ne_zero k) (by exact_mod_cast k.succ_ne_zero), ?_⟩
  linear_combination this

/-- CO-354: `0F0[; ; x] = e^x`, i.e. the terms are `x^k / k!`. -/
theorem pFqTerm_zero_zero (x : K) (k : ℕ) :
    pFqTerm (p := 0) (q := 0) ![] ![] x k = x ^ k / k ! := by
  simp [pFqTerm]

/-! ### Relation to Mathlib's `ordinaryHypergeometric` -/

/-- CO-354. For `p = 2`, `q = 1` the terms of `pFq` are the terms of Mathlib's `₂F₁`. -/
theorem pFqTerm_two_one (a b c x : K) (k : ℕ) :
    pFqTerm ![a, b] ![c] x k = ordinaryHypergeometricCoefficient a b c k * x ^ k := by
  simp only [pFqTerm, Fin.prod_univ_two, Fin.prod_univ_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, ordinaryHypergeometricCoefficient]
  field_simp

theorem ordinaryHypergeometric_eq_tsum_pFqTerm [TopologicalSpace K] [IsTopologicalRing K]
    (a b c x : K) : ordinaryHypergeometric a b c x = ∑' k, pFqTerm ![a, b] ![c] x k := by
  rw [ordinaryHypergeometric_eq_tsum]
  refine tsum_congr fun k => ?_
  rw [pFqTerm_two_one, smul_eq_mul]

/-! ### Termination -/

/-- CO-359. If an upper parameter is `-n`, the terms vanish from index `n+1` on. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 50"]
theorem pFqTerm_eq_zero_of_neg_nat {p q : ℕ} {a : Fin p → K} (b : Fin q → K) (x : K)
    (i : Fin p) {n : ℕ} (hi : a i = -(n : K)) {k : ℕ} (hk : n < k) :
    pFqTerm a b x k = 0 := by
  have : (ascPochhammer K k).eval (a i) = 0 := by
    rw [hi]; exact ascPochhammer_eval_neg_natCast_of_lt hk
  have hp : (∏ i, (ascPochhammer K k).eval (a i)) = 0 := prod_eq_zero (Finset.mem_univ i) this
  simp [pFqTerm, hp]

/-- CO-359. The (terminating) sum of `pFq` when an upper parameter is `-n`. -/
theorem tsum_pFqTerm_eq_sum_of_neg_nat [TopologicalSpace K] {p q : ℕ} {a : Fin p → K}
    (b : Fin q → K) (x : K) (i : Fin p) {n : ℕ} (hi : a i = -(n : K)) :
    ∑' k, pFqTerm a b x k = ∑ k ∈ range (n + 1), pFqTerm a b x k := by
  refine tsum_eq_sum fun k hk => ?_
  exact pFqTerm_eq_zero_of_neg_nat b x i hi (by simpa using hk)

/-! ### Generalized falling factorials -/

section Falling

variable {R : Type*} [CommRing R]

/-- CO-356. The generalized falling factorial `[x, d]_n = x (x - d) (x - 2d) ⋯ (x - (n-1)d)`. -/
@[kb "petkovsekwilfzeilberger1996" "Definition (unnumbered) [x,d]_n, p. 48"]
def gff (x d : R) (n : ℕ) : R := ∏ j ∈ range n, (x - (j : R) * d)

theorem gff_zero (x d : R) : gff x d 0 = 1 := by simp [gff]

theorem gff_succ (x d : R) (n : ℕ) : gff x d (n + 1) = gff x d n * (x - (n : R) * d) := by
  simp [gff, prod_range_succ]

/-- CO-356. The binomial theorem for generalized falling factorials:
`∑_k C(n,k) [x,d]_k [y,d]_{n-k} = [x+y,d]_n`. -/
@[kb "petkovsekwilfzeilberger1996" "Example 3.3.3, p. 48"]
theorem gff_add (x y d : R) (n : ℕ) :
    ∑ ij ∈ antidiagonal n, ((n.choose ij.1 : ℕ) : R) * (gff x d ij.1 * gff y d ij.2) =
      gff (x + y) d n := by
  induction n with
  | zero => simp [gff]
  | succ n ih =>
    rw [sum_antidiagonal_choose_succ_mul (fun i j => gff x d i * gff y d j) n, gff_succ,
      ← ih, sum_mul, ← sum_add_distrib]
    refine sum_congr rfl fun ij hij => ?_
    have hij' : ij.1 + ij.2 = n := mem_antidiagonal.1 hij
    have hc : n.choose ij.2 = n.choose ij.1 := (Nat.choose_symm_of_eq_add hij'.symm).symm
    have hn : (n : R) = ij.1 + ij.2 := by rw [← hij']; push_cast; ring
    rw [hc, gff_succ, gff_succ, hn]
    ring

/-- The same, written as a sum over `range (n+1)`. -/
theorem gff_add_range (x y d : R) (n : ℕ) :
    ∑ k ∈ range (n + 1), (n.choose k : R) * (gff x d k * gff y d (n - k)) =
      gff (x + y) d n := by
  rw [← gff_add, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

end Falling

theorem asc_eval_eq_prod (a : K) (n : ℕ) :
    (ascPochhammer K n).eval a = ∏ j ∈ range n, (a + (j : K)) := by
  induction n with
  | zero => simp
  | succ n ih => rw [ascPochhammer_succ_eval, ih, prod_range_succ]

theorem gff_eq_asc (x : K) {d : K} (hd : d ≠ 0) (k : ℕ) :
    gff x d k = (-d) ^ k * (ascPochhammer K k).eval (-x / d) := by
  induction k with
  | zero => simp [gff_zero]
  | succ k ih =>
    rw [gff_succ, ih, ascPochhammer_succ_eval, pow_succ]
    field_simp
    ring

/-- The product of the last `k` factors of `[y,d]_n`. -/
theorem gff_eq_mul_asc (y : K) {d : K} (hd : d ≠ 0) {n k : ℕ} (hk : k ≤ n) :
    gff y d n = gff y d (n - k) * (d ^ k * (ascPochhammer K k).eval (y / d - n + 1)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [Nat.add_sub_cancel_right]
  unfold gff
  have key : ∏ x ∈ range k, (y - ((m + x : ℕ) : K) * d) =
      d ^ k * ∏ j ∈ range k, (y / d - ((m + k : ℕ) : K) + 1 + j) := by
    rw [← prod_range_reflect (fun j : ℕ => y / d - ((m + k : ℕ) : K) + 1 + j) k]
    have hdk : d ^ k = ∏ _j ∈ range k, d := by simp
    rw [hdk, ← prod_mul_distrib]
    refine prod_congr rfl fun j hj => ?_
    have hj' : j < k := mem_range.1 hj
    have : ((k - 1 - j : ℕ) : K) = (k : K) - 1 - j := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    rw [this]
    push_cast
    field_simp
    ring
  rw [prod_range_add, asc_eval_eq_prod, key]

theorem choose_eq_asc (n k : ℕ) :
    (n.choose k : K) = (-1) ^ k * (ascPochhammer K k).eval (-(n : K)) / k ! := by
  have h3 : (k ! : K) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  rw [ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose]
  have : ((-1 : K) ^ k) * ((-1) ^ k) = 1 := by rw [← mul_pow]; simp
  rw [eq_div_iff h3]
  push_cast
  rw [← mul_assoc ((-1 : K) ^ k), this]
  ring

/-- CO-356. The falling factorial binomial theorem as a terminating `2F1`:
`∑_k C(n,k) [x,d]_k [y,d]_{n-k} = [y,d]_n · 2F1(-n, -x/d; y/d - n + 1; 1)`
(here `a' = -x/d`, `c = y/d - n + 1`, `c` not a nonpositive integer, `d ≠ 0`). -/
@[kb "petkovsekwilfzeilberger1996" "Example 3.3.3, p. 48"]
theorem gff_binomial_eq_pFq (x y d a' c : K) (hd : d ≠ 0) (n : ℕ) (ha : a' = -x / d)
    (hc : c = y / d - n + 1) (hcok : LowerOK ![c]) :
    ∑ k ∈ range (n + 1), (n.choose k : K) * (gff x d k * gff y d (n - k)) =
      gff y d n * ∑ k ∈ range (n + 1), pFqTerm ![-(n : K), a'] ![c] 1 k := by
  rw [mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := by simpa [Nat.lt_succ_iff] using hk
  have hP : (ascPochhammer K k).eval c ≠ 0 :=
    eval_ascPochhammer_ne_zero (fun m => by simpa using hcok 0 m) k
  have h3 : (k ! : K) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hsq : ((-1 : K) ^ k) * ((-1) ^ k) = 1 := by rw [← mul_pow]; simp
  rw [gff_eq_mul_asc y hd hkn, ← hc, gff_eq_asc x hd, ← ha, choose_eq_asc]
  simp only [pFqTerm, Fin.prod_univ_two, Fin.prod_univ_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, one_pow, mul_one, neg_pow d k]
  field_simp
  have hsq' : ((-1 : K) ^ k) ^ 2 = 1 := by rw [sq]; exact hsq
  rw [hsq', one_mul]

theorem gff_one_eq_asc (z : K) (n : ℕ) :
    gff (z + n - 1) 1 n = (ascPochhammer K n).eval z := by
  rw [asc_eval_eq_prod, ← prod_range_reflect (fun j : ℕ => z + (j : K)) n]
  unfold gff
  refine prod_congr rfl fun j hj => ?_
  have hj' : j < n := mem_range.1 hj
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

/-- CO-361. Gauss's summation `2F1(a, b; c; 1) = (c-a)_n / (c)_n` for `b = -n` a nonpositive
integer (terminating Chu-Vandermonde form), `c` not a nonpositive integer. This is the case
`b = -n` of the book's `Γ(c-a-b)Γ(c) / (Γ(c-a)Γ(c-b))`, since `Γ(c-a+n)/Γ(c-a) = (c-a)_n` and
`Γ(c+n)/Γ(c) = (c)_n`. -/
@[kb "petkovsekwilfzeilberger1996" "text (I) Gauss 2F1, p. 53"]
theorem gauss_two_one_neg_nat (a c : K) (n : ℕ) (hc : LowerOK ![c]) :
    ∑ k ∈ range (n + 1), pFqTerm ![-(n : K), a] ![c] 1 k =
      (ascPochhammer K n).eval (c - a) / (ascPochhammer K n).eval c := by
  have hP : (ascPochhammer K n).eval c ≠ 0 :=
    eval_ascPochhammer_ne_zero (fun m => by simpa using hc 0 m) n
  have h := gff_binomial_eq_pFq (-a) (c + n - 1) 1 a c one_ne_zero n (by simp) (by ring) hc
  rw [gff_add_range, show -a + (c + n - 1) = (c - a) + n - 1 by ring, gff_one_eq_asc,
    gff_one_eq_asc] at h
  rw [eq_div_iff hP, h]
  ring

/-! ### The series `1F0[a; ; z] = (1 - z)^(-a)` -/

theorem pFqTerm_one_zero (a z : K) (k : ℕ) :
    pFqTerm ![a] (![] : Fin 0 → K) z k = (ascPochhammer K k).eval a * z ^ k / k ! := by
  simp [pFqTerm]

theorem asc_succ_left_eval (a : K) (k : ℕ) :
    (ascPochhammer K (k + 1)).eval a = a * (ascPochhammer K k).eval (a + 1) := by
  rw [asc_eval_eq_prod, asc_eval_eq_prod, prod_range_succ']
  simp only [Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one]
  rw [mul_comm]
  congr 1
  refine prod_congr rfl fun j _ => ?_
  ring

open PowerSeries in
/-- The formal power series `1F0[a; ; z] = ∑ (a)_k z^k / k!`. -/
noncomputable def oneFZero (a : K) : K⟦X⟧ :=
  PowerSeries.mk fun k => pFqTerm ![a] (![] : Fin 0 → K) 1 k

open PowerSeries in
theorem one_sub_X_mul_oneFZero_succ (a : K) :
    (1 - PowerSeries.X) * oneFZero (a + 1) = oneFZero a := by
  ext k
  rw [sub_mul, one_mul, map_sub]
  cases k with
  | zero => simp [oneFZero, pFqTerm_one_zero]
  | succ k =>
    rw [coeff_succ_X_mul]
    simp only [oneFZero, coeff_mk, pFqTerm_one_zero, one_pow, mul_one]
    have h3 : (k ! : K) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    have h4 : ((k : K) + 1) ≠ 0 := by exact_mod_cast k.succ_ne_zero
    rw [ascPochhammer_succ_eval (k := a + 1), asc_succ_left_eval a k, Nat.factorial_succ]
    push_cast
    field_simp
    ring

theorem oneFZero_zero : oneFZero (0 : K) = 1 := by
  ext k
  cases k with
  | zero => simp [oneFZero, pFqTerm_one_zero]
  | succ k => simp [oneFZero, pFqTerm_one_zero, asc_succ_left_eval]

open PowerSeries in
theorem one_sub_X_pow_mul_oneFZero (a : K) (n : ℕ) :
    (1 - PowerSeries.X) ^ n * oneFZero (a + n) = oneFZero a := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [_root_.pow_succ', mul_assoc, show a + ((n + 1 : ℕ) : K) = (a + 1) + n by push_cast; ring,
      ih (a + 1), one_sub_X_mul_oneFZero_succ]

open PowerSeries in
/-- CO-367 (formal version, positive integer `a = n`). The series `1F0[n; ; z]` is the formal
inverse of `(1 - z)^n`, i.e. `1F0[n;;z] = (1 - z)^(-n)`. -/
@[kb "petkovsekwilfzeilberger1996" "text 1F0, p. 55"]
theorem oneFZero_nat_mul_one_sub_X_pow (n : ℕ) :
    oneFZero (n : K) * (1 - PowerSeries.X) ^ n = 1 := by
  have := one_sub_X_pow_mul_oneFZero (0 : K) n
  rwa [zero_add, oneFZero_zero, mul_comm] at this

/-- Bridge to Mathlib's binomial coefficients: the term of `1F0[a; ; z]` over `ℂ` is
`Ring.choose (a + k - 1) k * z^k`. -/
theorem pFqTerm_one_zero_eq_choose (a z : ℂ) (k : ℕ) :
    pFqTerm ![a] (![] : Fin 0 → ℂ) z k = Ring.choose (a + k - 1) k * z ^ k := by
  rw [pFqTerm_one_zero, Ring.choose_eq_smul, descPochhammer_smeval_eq_ascPochhammer,
    ascPochhammer_smeval_eq_eval, show a + k - 1 - k + 1 = a by ring, smul_eq_mul, div_eq_inv_mul]
  ring

/-- CO-367 (analytic version). For complex `a` and `|z| < 1`,
`∑ (a)_k z^k / k! = 1 / (1 - z)^a`, i.e. `1F0[a; ; z] = (1 - z)^(-a)`. -/
@[kb "petkovsekwilfzeilberger1996" "text 1F0, p. 55"]
theorem hasSum_pFqTerm_one_zero (a z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun k => pFqTerm ![a] (![] : Fin 0 → ℂ) z k) (1 / (1 - z) ^ a) := by
  have h := (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero a).hasSum
    (y := z) (by simpa [enorm_eq_nnnorm, ← NNReal.coe_lt_coe] using hz)
  simp only [zero_add] at h
  convert h using 1
  ext k
  rw [pFqTerm_one_zero_eq_choose]
  simp [mul_comm]

end UndergradKB.Combinatorics.AeqB
