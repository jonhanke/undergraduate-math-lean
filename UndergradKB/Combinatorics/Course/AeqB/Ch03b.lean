import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.Polynomial.Pochhammer
import UndergradKB.Combinatorics.AeqB.HypergeometricSeries
import UndergradKB.Combinatorics.AeqB.Summation1
import UndergradKB.Combinatorics.AeqB.Summation3
import UndergradKB.Combinatorics.AeqB.EulerTransform
import UndergradKB.Combinatorics.AeqB.Identities
import UndergradKB.Combinatorics.AeqB.Identities3b
import UndergradKB.Combinatorics.AeqB.Database
import UndergradKB.Common.Attr

/-!
# A=B, Chapter 3: course wrappers of results proved in this library (wave 3)
-/

open Finset Polynomial
open scoped Nat
open UndergradKB.Combinatorics.AeqB

namespace UndergradKB.Combinatorics.Course.AeqB.Ch03b

/-- CO-353. The terms `pFq(a; b; x)` form a hypergeometric series: `t₀ = 1` and
`t_{k+1}/t_k` is a rational function of `k`. -/
@[kb "petkovsekwilfzeilberger1996" "Definition (unnumbered) hypergeometric series, p. 45"]
theorem def_p45_hypergeometric_series {K : Type*} [Field K] [CharZero K] {p q : ℕ}
    (a : Fin p → K) {b : Fin q → K} (hb : LowerOK b) (x : K) :
    IsHypergeometricSeries (pFqTerm a b x) :=
  isHypergeometricSeries_pFqTerm a hb x

/-- CO-354. The term ratio of `pFq[a; b; x]` is
`(k+a₁)⋯(k+a_p) x / ((k+b₁)⋯(k+b_q)(k+1))`; `e^x` is `0F0` and the `p = 2, q = 1` terms are
those of Mathlib's `₂F₁`. -/
@[kb "petkovsekwilfzeilberger1996" "Equation (3.2.1), p. 46"]
theorem eq_3_2_1_pFq_term_ratio {K : Type*} [Field K] [CharZero K] :
    (∀ {p q : ℕ} (a : Fin p → K) {b : Fin q → K}, LowerOK b → ∀ (x : K) (k : ℕ),
      pFqTerm a b x (k + 1) * ((∏ j, ((k : K) + b j)) * ((k : K) + 1)) =
        pFqTerm a b x k * ((∏ i, ((k : K) + a i)) * x)) ∧
    (∀ (x : K) (k : ℕ), pFqTerm (p := 0) (q := 0) ![] ![] x k = x ^ k / k !) ∧
    (∀ (a b c x : K) (k : ℕ),
      pFqTerm ![a, b] ![c] x k = ordinaryHypergeometricCoefficient a b c k * x ^ k) :=
  ⟨fun a _ hb x k => pFqTerm_succ_mul a hb x k, pFqTerm_zero_zero, pFqTerm_two_one⟩

/-- CO-355. The lookup algorithm: a sequence with `t 0 = 1` and the term ratio of `pFq` is that
`pFq` term sequence; a sequence with ratio recurrence from index `m` on, shifted by `m` and
normalized to start at `1`, again has a ratio recurrence. -/
@[kb "petkovsekwilfzeilberger1996" "text lookup algorithm, p. 47"]
theorem text_p47_lookup_algorithm {K : Type*} [Field K] [CharZero K] :
    (∀ {p q : ℕ} (a : Fin p → K) {b : Fin q → K}, LowerOK b → ∀ (x : K) (t : ℕ → K),
      t 0 = 1 →
      (∀ k : ℕ, t (k + 1) * ((∏ j, ((k : K) + b j)) * ((k : K) + 1)) =
        t k * ((∏ i, ((k : K) + a i)) * x)) →
      ∀ k, t k = pFqTerm a b x k) ∧
    (∀ (t : ℕ → K) (m : ℕ), t m ≠ 0 → ∀ (P Q : ℕ → K),
      (∀ k, m ≤ k → Q k * t (k + 1) = P k * t k) →
      (fun k => t (m + k) / t m) 0 = 1 ∧
        ∀ k, Q (m + k) * (t (m + (k + 1)) / t m) = P (m + k) * (t (m + k) / t m)) :=
  ⟨fun a _ hb x t h0 h => eq_pFqTerm_of_term_ratio a hb x t h0 h,
    fun t m hm P Q h => lookup_shift_normalize t m hm P Q h⟩

/-- CO-356. The generalized falling factorial `[x,d]_n` satisfies the binomial convolution
`∑ C(n,k) [x,d]_k [y,d]_{n-k} = [x+y,d]_n`, and the same sum is a terminating `2F1(-n,-x/d; y/d-n+1; 1)`
times `[y,d]_n`. -/
@[kb "petkovsekwilfzeilberger1996" "Example 3.3.3, p. 48"]
theorem ex_3_3_3_gff_binomial :
    (∀ {R : Type*} [CommRing R] (x y d : R) (n : ℕ),
      ∑ ij ∈ antidiagonal n, ((n.choose ij.1 : ℕ) : R) * (gff x d ij.1 * gff y d ij.2) =
        gff (x + y) d n) ∧
    (∀ {K : Type*} [Field K] [CharZero K] (x y d a' c : K), d ≠ 0 → ∀ n : ℕ, a' = -x / d →
      c = y / d - n + 1 → LowerOK ![c] →
      ∑ k ∈ range (n + 1), (n.choose k : K) * (gff x d k * gff y d (n - k)) =
        gff y d n * ∑ k ∈ range (n + 1), pFqTerm ![-(n : K), a'] ![c] 1 k) :=
  ⟨fun x y d n => gff_add x y d n,
    fun x y d a' c hd n ha hc hcok => gff_binomial_eq_pFq x y d a' c hd n ha hc hcok⟩

/-- CO-359. `pFq` terms vanish beyond `n` when an upper parameter is `-n`, so the series
terminates and its sum is the finite sum. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 50"]
theorem text_p50_pFq_terminates {K : Type*} [Field K] [CharZero K] [TopologicalSpace K]
    {p q : ℕ} {a : Fin p → K} (b : Fin q → K) (x : K) (i : Fin p) {n : ℕ}
    (hi : a i = -(n : K)) :
    (∀ k : ℕ, n < k → pFqTerm a b x k = 0) ∧
      ∑' k, pFqTerm a b x k = ∑ k ∈ range (n + 1), pFqTerm a b x k :=
  ⟨fun _ hk => pFqTerm_eq_zero_of_neg_nat b x i hi hk, tsum_pFqTerm_eq_sum_of_neg_nat b x i hi⟩

/-- CO-361. (partial) Gauss's `2F1` summation `2F1(-n, a; c; 1) = (c-a)_n / (c)_n` for a negative
integer upper parameter (the case with `Re(c-a-b) > 0` is not formalized). -/
@[kb "petkovsekwilfzeilberger1996" "text (I) Gauss 2F1, p. 53"]
theorem text_p53_gauss_two_one {K : Type*} [Field K] [CharZero K] (a c : K) (n : ℕ)
    (hc : LowerOK ![c]) :
    ∑ k ∈ range (n + 1), pFqTerm ![-(n : K), a] ![c] 1 k =
      (ascPochhammer K n).eval (c - a) / (ascPochhammer K n).eval c :=
  gauss_two_one_neg_nat a c n hc

/-- CO-362. (partial) Kummer's `2F1(a,-n; 1-a-n; -1)` summation for terminating series: zero for
odd `n`, and `(2m)! (a)_m / (m! (a)_{2m})` for `n = 2m` (the general Gamma form is not
formalized). -/
@[kb "petkovsekwilfzeilberger1996" "text (II) Kummer 2F1, p. 53"]
theorem text_p53_kummer_two_one {K : Type*} [Field K] [CharZero K] (a : K) (m : ℕ) :
    (rise a (2 * m + 1) ≠ 0 →
      ∑ k ∈ range (2 * m + 1 + 1),
        pFqTerm ![a, -((2 * m + 1 : ℕ) : K)] ![1 - a - ((2 * m + 1 : ℕ) : K)] (-1) k = 0) ∧
    (rise a (2 * m) ≠ 0 →
      ∑ k ∈ range (2 * m + 1),
        pFqTerm ![a, -((2 * m : ℕ) : K)] ![1 - a - ((2 * m : ℕ) : K)] (-1) k =
        ((2 * m) ! : K) * rise a m / ((m ! : K) * rise a (2 * m))) :=
  ⟨fun hn => kummer_terminating_odd a m hn, fun hn => kummer_terminating_even a m hn⟩

/-- CO-363. Saalschütz: if `d + e = a + b + c + 1` and `c = -n`, then
`3F2(a,b,-n; d,e; 1) = (d-a)_n (d-b)_n / ((d)_n (d-a-b)_n)`. -/
@[kb "petkovsekwilfzeilberger1996" "text (III) Saalschuetz, p. 54"]
theorem text_p54_saalschutz {K : Type*} [Field K] [CharZero K] (a b d e : K) (n : ℕ)
    (hde : d + e = a + b + (-(n : K)) + 1) (hd : LowerOK ![d])
    (hden : rise (d - a - b) n ≠ 0) :
    ∑ k ∈ range (n + 1), pFqTerm ![a, b, -(n : K)] ![d, e] 1 k =
      rise (d - a) n * rise (d - b) n / (rise d n * rise (d - a - b) n) :=
  saalschutz_three_f_two a b d e n hde hd hden

/-- CO-364. Dixon's identity:
`∑_k (-1)^k C(a+b,a+k) C(a+c,c+k) C(b+c,b+k) = (a+b+c)!/(a! b! c!)`. -/
@[kb "petkovsekwilfzeilberger1996" "text (IV) Dixon, p. 54"]
theorem text_p54_dixon (a b c : ℕ) :
    ∑ᶠ k : ℤ, (-1 : ℚ) ^ k * (zchoose (a + b) (a + k) : ℚ) * (zchoose (a + c) (c + k) : ℚ)
      * (zchoose (b + c) (b + k) : ℚ) = ((a + b + c) ! : ℚ) / (a ! * b ! * c !) :=
  dixon a b c

/-- CO-367. `1F0[a; -; z] = (1-z)^{-a}`: for natural `a = n` as power series, and for complex `a`
as a convergent series when `|z| < 1`. -/
@[kb "petkovsekwilfzeilberger1996" "text 1F0, p. 55"]
theorem text_p55_one_F_zero :
    (∀ {K : Type*} [Field K] [CharZero K] (n : ℕ),
      oneFZero (n : K) * (1 - PowerSeries.X) ^ n = 1) ∧
    (∀ (a z : ℂ), ‖z‖ < 1 →
      HasSum (fun k => pFqTerm ![a] (![] : Fin 0 → ℂ) z k) (1 / (1 - z) ^ a)) :=
  ⟨fun n => oneFZero_nat_mul_one_sub_X_pow n, fun a z hz => hasSum_pFqTerm_one_zero a z hz⟩

/-- CO-370. `3F2(a,b,-n; 1+a-b, 1+a+n; 1) = (1+a)_n (1+a/2-b)_n / ((1+a/2)_n (1+a-b)_n)`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 55 (3F2 (a,b,-n))"]
theorem text_p55_three_F_two_a_b_neg_n {K : Type*} [Field K] [CharZero K] (a b : K) (n : ℕ)
    (ha : ∀ j : ℕ, (1 + a + j : K) ≠ 0) (hab : ∀ j : ℕ, (1 + a - b + j : K) ≠ 0)
    (ha2 : ∀ j : ℕ, (1 + a / 2 + j : K) ≠ 0) :
    ∑ k ∈ range (n + 1), pFqTerm ![a, b, -(n : K)] ![1 + a - b, 1 + a + n] 1 k
      = Identities3b.asc (1 + a) n * Identities3b.asc (1 + a / 2 - b) n /
          (Identities3b.asc (1 + a / 2) n * Identities3b.asc (1 + a - b) n) :=
  Identities3b.threeFTwo_a_b_neg_n a b n ha hab ha2

/-- CO-045. `∑_k (-1)^k C(2n,k)^2 = (-1)^n C(2n,n)`, found as `2F1(-2n,-2n;1;-1)` via Kummer. -/
@[kb "petkovsekwilfzeilberger1996" "Example 3.6.1, p. 55"]
theorem ex_3_6_1_alt_sum_choose_sq (n : ℕ) :
    ∑ k ∈ range (2 * n + 1), (-1 : ℤ) ^ k * ((2 * n).choose k : ℤ) ^ 2
      = (-1) ^ n * ((2 * n).choose n : ℤ) :=
  alt_sum_choose_sq n

/-- CO-373. Euler's transformation `2F1(a,b;c;z) = (1-z)^{c-a-b} 2F1(c-a,c-b;c;z)` as power
series. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 60"]
theorem text_p60_euler_transformation {K : Type*} [Field K] [CharZero K] (a b c : K)
    (hc : LowerOK ![c]) :
    hyp21 a b c = powOneSub (c - a - b) * hyp21 (c - a) (c - b) c :=
  euler_transformation a b c hc

end UndergradKB.Combinatorics.Course.AeqB.Ch03b
