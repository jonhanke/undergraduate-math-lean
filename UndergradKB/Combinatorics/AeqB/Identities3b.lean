import UndergradKB.Combinatorics.AeqB.HypergeometricSeries
import UndergradKB.Common.Attr

namespace UndergradKB.Combinatorics.AeqB.Identities3b
open Finset Polynomial
open scoped Nat
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {K : Type*} [Field K] [CharZero K]

/-- Rising factorial `(x)_k = x (x+1) ⋯ (x+k-1)`. -/
noncomputable def asc (x : K) (k : ℕ) : K := (ascPochhammer K k).eval x

lemma asc_zero (x : K) : asc x 0 = 1 := by simp [asc]

lemma asc_succ (x : K) (k : ℕ) : asc x (k + 1) = asc x k * (x + k) :=
  ascPochhammer_succ_eval k x

lemma asc_succ_left (x : K) (k : ℕ) : asc x (k + 1) = x * asc (x + 1) k := by
  unfold asc; rw [ascPochhammer_succ_left]; simp

lemma asc_ne_zero {x : K} (hx : ∀ j : ℕ, x + j ≠ 0) (k : ℕ) : asc x k ≠ 0 := by
  induction k with
  | zero => simp [asc_zero]
  | succ k ih => rw [asc_succ]; exact mul_ne_zero ih (hx k)

lemma asc_neg_succ (n j : ℕ) : asc (-((n + 1 : ℕ) : K)) (j + 1) = -((n : K) + 1) * asc (-(n : K)) j := by
  rw [asc_succ_left]
  push_cast
  rw [show -((n : K) + 1) + 1 = -(n : K) by ring]

lemma asc_shift (x : K) (hx : x ≠ 0) (j : ℕ) :
    asc (x + 1) (j + 1) = asc x j * (x + j) * (x + j + 1) / x := by
  have h := asc_succ_left x (j + 1)
  rw [asc_succ, asc_succ] at h
  push_cast at h
  field_simp
  linear_combination -h

/-! ### CO-370: `3F2(a,b,-n; 1+a-b, 1+a+n; 1)` -/

/-- Summand `(a)_k (b)_k (-n)_k / ((1+a-b)_k (1+a+n)_k k!)`. -/
noncomputable def wF (a b : K) (n k : ℕ) : K :=
  asc a k * asc b k * asc (-(n : K)) k / (asc (1 + a - b) k * asc (1 + a + n) k * (k ! : K))

/-- Numerator polynomial of the Zeilberger certificate. -/
def wW (a b n k : K) : K :=
  -k / 2 - k ^ 2 / 2 - n * k - n * k ^ 2 / 2 - n ^ 2 * k / 2 + b / 2 + b * k / 2 + b * n
    + b * n * k / 2 + b * n ^ 2 / 2 - a / 2 - 3 * a * k / 2 - a * k ^ 2 / 2 - a * n
    - 3 * a * n * k / 2 - a * n ^ 2 / 2 + a * b + a * b * k / 2 + a * b * n - a ^ 2
    - a ^ 2 * k - a ^ 2 * n + a ^ 2 * b / 2 - a ^ 3 / 2

/-- The telescoping potential `G(n,k) = R(n,k) F(n,k)`, written without the pole of `R`. -/
noncomputable def wG (a b : K) (n : ℕ) : ℕ → K
  | 0 => 0
  | j + 1 => -(((j : K) + 1) * wW a b n ((j : K) + 1) * asc a (j + 1) * asc b (j + 1)
      * asc (-(n : K)) j / (asc (1 + a - b) (j + 1) * asc (1 + a + n) (j + 1)
        * (1 + a + n + ((j : K) + 1)) * ((j + 1)! : K)
        * ((1 + a / 2 + n) * (1 + a - b + n))))

/-- The ratio of consecutive answers. -/
noncomputable def wRho (a b : K) (n : ℕ) : K :=
  (1 + a + n) * (1 + a / 2 - b + n) / ((1 + a / 2 + n) * (1 + a - b + n))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
lemma wAlg (a b n j : K) (h1 : (1 + a + n + j + 1 : K) ≠ 0) (h2 : (1 + a - b + j + 1 : K) ≠ 0)
    (h3 : (1 + a + n + j + 2 : K) ≠ 0) (h4 : (j + 2 : K) ≠ 0) (h5 : (j + 1 : K) ≠ 0)
    (hD1 : (1 + a / 2 + n : K) ≠ 0) (hD2 : (1 + a - b + n : K) ≠ 0)
    (hD3 : (2 + a + n * 2 : K) ≠ 0) :
    -((n + 1) * (1 + a + n) / (1 + a + n + j + 1))
        - (1 + a + n) * (1 + a / 2 - b + n) / ((1 + a / 2 + n) * (1 + a - b + n)) * (j - n)
      = -((j + 2) * wW a b n (j + 2) * (a + j + 1) * (b + j + 1) * (j - n)
          / ((1 + a - b + j + 1) * (1 + a + n + j + 1) * (1 + a + n + j + 2) * (j + 2)
            * ((1 + a / 2 + n) * (1 + a - b + n))))
        + ((j + 1) * wW a b n (j + 1) / ((1 + a + n + j + 1) * ((1 + a / 2 + n) * (1 + a - b + n)))) := by
  unfold wW
  field_simp
  ring

section step
variable (a b : K) (ha : ∀ j : ℕ, (1 + a + j : K) ≠ 0) (hab : ∀ j : ℕ, (1 + a - b + j : K) ≠ 0)
  (ha2 : ∀ j : ℕ, (1 + a / 2 + j : K) ≠ 0)

include ha hab ha2 in
lemma wF_step (n k : ℕ) :
    wF a b (n + 1) k - wRho a b n * wF a b n k = wG a b n (k + 1) - wG a b n k := by
  have hn1 : (1 + a + n : K) ≠ 0 := by simpa using ha n
  have hn2 : (1 + a / 2 + n : K) ≠ 0 := by simpa using ha2 n
  have hn3 : (1 + a - b + n : K) ≠ 0 := by simpa using hab n
  have hM : ∀ j : ℕ, (1 + a + n : K) + j ≠ 0 := fun j => by
    have := ha (n + j); push_cast at this; rwa [← add_assoc] at this
  have hL : ∀ j : ℕ, (1 + a - b : K) + j ≠ 0 := hab
  have hn4 : (1 + a + n + 1 : K) ≠ 0 := by
    have := ha (n + 1); push_cast at this; intro h; apply this; linear_combination h
  have h0 : (1 + a - b : K) ≠ 0 := by simpa using hab 0
  have hn5 : (2 + a + n * 2 : K) ≠ 0 := by intro h; apply hn2; linear_combination h / 2
  rcases k with _ | j
  · unfold wF wG wRho wW
    simp only [asc_zero, zero_add, Nat.factorial_zero, Nat.cast_one, mul_one, asc_succ,
      Nat.cast_zero, add_zero, Nat.factorial_one, one_mul, Nat.cast_ofNat, div_one, mul_zero,
      sub_zero, one_div]
    field_simp
    ring
  · have hj1 : ((j : K) + 1) ≠ 0 := by exact_mod_cast j.succ_ne_zero
    have hj2 : ((j : K) + 2) ≠ 0 := by
      have : ((j : K) + 1 + 1) ≠ 0 := by exact_mod_cast (j + 1).succ_ne_zero
      intro h; apply this; linear_combination h
    have hLj := asc_ne_zero hL (j + 1)
    have hMj := asc_ne_zero hM (j + 1)
    have hf : (((j + 1)! : ℕ) : K) ≠ 0 := by exact_mod_cast (j + 1).factorial_ne_zero
    have hM1 : (1 + a + n + j + 1 : K) ≠ 0 := by
      have := hM (j + 1); push_cast at this; intro h; apply this; linear_combination h
    have hM2 : (1 + a + n + j + 2 : K) ≠ 0 := by
      have := hM (j + 2); push_cast at this; intro h; apply this; linear_combination h
    have hL1 : (1 + a - b + j + 1 : K) ≠ 0 := by
      have := hL (j + 1); push_cast at this; intro h; apply this; linear_combination h
    set T : K := asc a (j + 1) * asc b (j + 1) * asc (-(n : K)) j
      / (asc (1 + a - b) (j + 1) * asc (1 + a + n) (j + 1) * (((j + 1)! : ℕ) : K)) with hT
    have eM' : asc (1 + a + ((n + 1 : ℕ) : K)) (j + 1)
        = asc (1 + a + n) (j + 1) * (1 + a + n + j + 1) / (1 + a + n) := by
      rw [show (1 + a + ((n + 1 : ℕ) : K)) = (1 + a + n) + 1 by push_cast; ring,
        asc_shift _ hn1 j, asc_succ (1 + a + n) j]
    have L1 : wF a b (n + 1) (j + 1)
        = T * (-((n : K) + 1)) * (1 + a + n) / (1 + a + n + j + 1) := by
      unfold wF
      rw [asc_neg_succ n j, eM', hT]
      field_simp
    have L2 : wF a b n (j + 1) = T * ((j : K) - n) := by
      unfold wF
      rw [asc_succ (-(n : K)) j, hT]
      field_simp
      ring
    have L3 : wG a b n (j + 1) = -(T * (((j : K) + 1) * wW a b n ((j : K) + 1)
        / ((1 + a + n + j + 1) * ((1 + a / 2 + n) * (1 + a - b + n))))) := by
      simp only [wG]
      rw [show (1 : K) + a + n + ((j : K) + 1) = 1 + a + n + j + 1 by ring, hT]
      field_simp
    have L4 : wG a b n (j + 1 + 1) = -(T * (((j : K) + 2) * wW a b n ((j : K) + 2)
        * (a + j + 1) * (b + j + 1) * ((j : K) - n)
        / ((1 + a - b + j + 1) * (1 + a + n + j + 1) * (1 + a + n + j + 2) * ((j : K) + 2)
          * ((1 + a / 2 + n) * (1 + a - b + n))))) := by
      simp only [wG]
      rw [asc_succ a (j + 1), asc_succ b (j + 1), asc_succ (1 + a - b) (j + 1),
        asc_succ (1 + a + n) (j + 1), asc_succ (-(n : K)) j, Nat.factorial_succ (j + 1), hT]
      push_cast
      rw [show (j : K) + 1 + 1 = j + 2 by ring,
        show (1 : K) + a + n + ((j : K) + 2) = 1 + a + n + j + 2 by ring]
      simp only [← add_assoc]
      have hD : ((1 + a / 2 + n) * (1 + a - b + n) : K) ≠ 0 := mul_ne_zero hn2 hn3
      generalize ((1 + a / 2 + n) * (1 + a - b + n) : K) = D at hD ⊢
      generalize wW a b n ((j : K) + 2) = W
      field_simp
      ring
    have alg := wAlg a b n j hM1 hL1 hM2 hj2 hj1 hn2 hn3 hn5
    rw [L1, L2, L3, L4]
    unfold wRho
    linear_combination T * alg

end step

lemma asc_neg_nat_eq_zero (n k : ℕ) (h : n < k) : asc (-(n : K)) k = 0 := by
  unfold asc
  exact ascPochhammer_eval_neg_natCast_of_lt h

lemma wF_eq_zero (a b : K) (n k : ℕ) (h : n < k) : wF a b n k = 0 := by
  unfold wF; rw [asc_neg_nat_eq_zero n k h]; simp

/-- The answer `(1+a)_n (1+a/2-b)_n / ((1+a/2)_n (1+a-b)_n)`. -/
noncomputable def wAns (a b : K) (n : ℕ) : K :=
  asc (1 + a) n * asc (1 + a / 2 - b) n / (asc (1 + a / 2) n * asc (1 + a - b) n)

section sum
variable (a b : K) (ha : ∀ j : ℕ, (1 + a + j : K) ≠ 0) (hab : ∀ j : ℕ, (1 + a - b + j : K) ≠ 0)
  (ha2 : ∀ j : ℕ, (1 + a / 2 + j : K) ≠ 0)

include ha hab ha2 in
lemma wSum_succ (n : ℕ) :
    ∑ k ∈ range (n + 2), wF a b (n + 1) k = wRho a b n * ∑ k ∈ range (n + 1), wF a b n k := by
  have h := sum_range_sub (fun k => wG a b n k) (n + 3)
  have h1 : wG a b n (n + 3) = 0 := by
    show wG a b n (n + 2 + 1) = 0
    simp only [wG]
    rw [asc_neg_nat_eq_zero n (n + 2) (by omega)]
    simp
  have h2 : wG a b n 0 = 0 := rfl
  have h3 : ∑ k ∈ range (n + 3), (wF a b (n + 1) k - wRho a b n * wF a b n k) = 0 := by
    rw [sum_congr rfl fun k _ => wF_step a b ha hab ha2 n k, h]
    rw [h1, h2]; simp
  rw [sum_sub_distrib, ← mul_sum] at h3
  have e1 : ∑ k ∈ range (n + 3), wF a b (n + 1) k = ∑ k ∈ range (n + 2), wF a b (n + 1) k := by
    rw [sum_range_succ, wF_eq_zero a b (n + 1) (n + 2) (by omega), add_zero]
  have e2 : ∑ k ∈ range (n + 3), wF a b n k = ∑ k ∈ range (n + 1), wF a b n k := by
    rw [sum_range_succ, sum_range_succ, wF_eq_zero a b n (n + 2) (by omega),
      wF_eq_zero a b n (n + 1) (by omega), add_zero, add_zero]
  rw [e1, e2] at h3
  exact sub_eq_zero.1 h3

include ha hab ha2 in
lemma wAns_succ (n : ℕ) : wAns a b (n + 1) = wRho a b n * wAns a b n := by
  have hn2 : (1 + a / 2 + n : K) ≠ 0 := by simpa using ha2 n
  have hn3 : (1 + a - b + n : K) ≠ 0 := by simpa using hab n
  have h1 := asc_ne_zero (x := 1 + a / 2) (fun j => by simpa using ha2 j) n
  have h2 := asc_ne_zero (x := 1 + a - b) hab n
  unfold wAns wRho
  rw [asc_succ (1 + a) n, asc_succ (1 + a / 2 - b) n, asc_succ (1 + a / 2) n,
    asc_succ (1 + a - b) n]
  field_simp

include ha hab ha2 in
lemma wSum_eq (n : ℕ) : ∑ k ∈ range (n + 1), wF a b n k = wAns a b n := by
  induction n with
  | zero => simp [wF, wAns, asc_zero]
  | succ n ih => rw [wSum_succ a b ha hab ha2 n, ih, wAns_succ a b ha hab ha2 n]

end sum

lemma pFqTerm_eq_wF (a b : K) (n k : ℕ) :
    pFqTerm ![a, b, -(n : K)] ![1 + a - b, 1 + a + n] 1 k = wF a b n k := by
  simp [pFqTerm, wF, asc, Fin.prod_univ_three, Fin.prod_univ_two]

/-- CO-370. The well-poised `3F2` summation
`3F2(a, b, -n; 1+a-b, 1+a+n; 1) = (1+a)_n (1+a/2-b)_n / ((1+a/2)_n (1+a-b)_n)`, for any field of
characteristic zero in which no denominator vanishes (`1+a+j`, `1+a-b+j`, `1+a/2+j` nonzero for all
`j ∈ ℕ`).  Proved by induction on `n` with the Zeilberger certificate
`R(n,k) = k W(n,k) / ((n+1-k)(1+a+n+k)(1+a/2+n)(1+a-b+n))`, `W` the cubic `wW`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 55 (3F2 (a,b,-n))"]
theorem threeFTwo_a_b_neg_n (a b : K) (n : ℕ) (ha : ∀ j : ℕ, (1 + a + j : K) ≠ 0)
    (hab : ∀ j : ℕ, (1 + a - b + j : K) ≠ 0) (ha2 : ∀ j : ℕ, (1 + a / 2 + j : K) ≠ 0) :
    ∑ k ∈ range (n + 1), pFqTerm ![a, b, -(n : K)] ![1 + a - b, 1 + a + n] 1 k
      = asc (1 + a) n * asc (1 + a / 2 - b) n / (asc (1 + a / 2) n * asc (1 + a - b) n) := by
  simp_rw [pFqTerm_eq_wF]
  exact wSum_eq a b ha hab ha2 n

end UndergradKB.Combinatorics.AeqB.Identities3b
