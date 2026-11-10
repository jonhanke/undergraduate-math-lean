import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Cast
import UndergradKB.Combinatorics.AeqB.Companions
import UndergradKB.Common.Attr

namespace UndergradKB.Combinatorics.AeqB.Identities2
open Finset Function
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

/-! ### CO-430: Paule's symmetrization -/

/-- CO-430. Paule's symmetrization: for a finitely supported `f : ℤ → K` (`K` a field of
characteristic zero) the unrestricted sum of `f k` equals the sum of `(f k + f (-k)) / 2`,
because the odd part sums to zero. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 126"]
theorem finsum_symmetrize {K : Type*} [Field K] [CharZero K] (f : ℤ → K)
    (hf : (Function.support f).Finite) :
    ∑ᶠ k : ℤ, f k = ∑ᶠ k : ℤ, (f k + f (-k)) / 2 := by
  have hneg : (Function.support fun k => f (-k)).Finite := by
    have : (Function.support fun k => f (-k)) = (fun k : ℤ => -k) ⁻¹' Function.support f := rfl
    rw [this]
    exact hf.preimage (neg_injective.injOn)
  have h1 : ∑ᶠ k : ℤ, f (-k) = ∑ᶠ k : ℤ, f k := finsum_comp_equiv (Equiv.neg ℤ) (f := f)
  simp_rw [div_eq_mul_inv]
  rw [← finsum_mul, finsum_add_distrib hf hneg, h1]
  ring

/-- CO-430 (Petkovšek's variant). Symmetrizing a sum over `0 ≤ k ≤ n` about `k = n/2`:
`∑_k f k = ∑_k (f k + f (n-k)) / 2`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 126"]
theorem sum_range_symmetrize {K : Type*} [Field K] [CharZero K] (f : ℕ → K) (n : ℕ) :
    ∑ k ∈ range (n + 1), f k = ∑ k ∈ range (n + 1), (f k + f (n - k)) / 2 := by
  have h := sum_range_reflect f (n + 1)
  simp only [Nat.add_sub_cancel] at h
  simp_rw [div_eq_mul_inv]
  rw [← sum_mul, sum_add_distrib, h]
  ring

/-! ### CO-461: dual identities -/

lemma neg_one_pow_add_eq_sub (n k : ℕ) (hk : k ≤ n) :
    (-1 : ℤ) ^ (n + k) = (-1) ^ (n - k) := by
  have : n + k = (n - k) + 2 * k := by omega
  rw [this, pow_add, pow_mul]; simp

/-- CO-461. The dual of `∑_k C(n,k) = 2^n`: `∑_k (-1)^(n+k) C(n,k) 2^k = 1`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 143"]
theorem dual_sum_choose (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1 : ℤ) ^ (n + k) * (n.choose k : ℤ) * 2 ^ k = 1 := by
  have h := (add_pow (2 : ℤ) (-1) n)
  norm_num at h
  refine Eq.trans ?_ h.symm
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hk)
  rw [neg_one_pow_add_eq_sub n k hk']
  ring

/-- CO-461. The dual of Vandermonde's identity (a special case of Gauss's `₂F₁` identity):
`∑_k (-1)^(n+k) C(n,k) C(k+b,k) = C(b,n)`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 143"]
theorem dual_vandermonde (n b : ℕ) :
    ∑ k ∈ range (n + 1), (-1 : ℤ) ^ (n + k) * (n.choose k : ℤ) * ((k + b).choose k : ℤ)
      = (b.choose n : ℤ) := by
  set g : ℕ → ℤ := fun y => (y.choose b : ℤ) with hg
  have h1 := fwdDiff_iter_eq_sum_shift (h := (1 : ℕ)) (fun x : ℕ => g (x + b)) n 0
  have h2 : (fwdDiff (1 : ℕ))^[n] (fun x : ℕ => g (x + b)) 0
      = ((fwdDiff (1 : ℕ))^[n] g) (0 + b) :=
    fwdDiff_iter_comp_add (h := (1 : ℕ)) g b n 0
  have h3 : ((fwdDiff (1 : ℕ))^[n] g) (0 + b) = (b.choose n : ℤ) := by
    rcases le_or_gt n b with hnb | hnb
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hnb
      have h4 := fwdDiff_iter_choose (R := ℤ) j n
      have h5 : (fwdDiff (1 : ℕ))^[n] g = fun x => (x.choose j : ℤ) := h4
      rw [h5]
      simp only [zero_add]
      exact_mod_cast (Nat.choose_symm_add (a := n) (b := j)).symm
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hnb
      have h4 := fwdDiff_iter_choose (R := ℤ) 0 b
      have h5 : (fwdDiff (1 : ℕ))^[b] g = fun _ => (1 : ℤ) := by
        rw [show (fwdDiff (1 : ℕ))^[b] g = (fwdDiff (1 : ℕ))^[b] (fun x => (x.choose (b + 0) : ℤ)) from rfl, h4]
        funext x; simp
      have h6 : (fwdDiff (1 : ℕ))^[b + m + 1] g = fun _ => (0 : ℤ) := by
        rw [show b + m + 1 = (m + 1) + b by ring, iterate_add_apply, h5, iterate_succ_apply]
        have h7 : fwdDiff (1 : ℕ) (fun _ : ℕ => (1 : ℤ)) = fun _ => 0 := fwdDiff_const _ _
        have h8 : fwdDiff (1 : ℕ) (fun _ : ℕ => (0 : ℤ)) = fun _ => 0 := fwdDiff_const _ _
        rw [h7]
        exact Function.iterate_fixed h8 m
      rw [h6, Nat.choose_eq_zero_of_lt (by omega)]
      simp
  rw [h3] at h2
  rw [h2] at h1
  refine Eq.trans ?_ h1.symm
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hk)
  rw [neg_one_pow_add_eq_sub n k hk', smul_eq_mul]
  simp only [hg, smul_eq_mul, zero_add, mul_one]
  rw [Nat.choose_symm_add (a := k) (b := b)]

/-! ### CO-053: Abel-type identity -/

open Polynomial

section Abel
variable {K : Type*} [Field K] [CharZero K]

/-- The coefficient `(k+r)^(k-1)` of Abel's identity, with the `k = 0` value `r⁻¹`. -/
noncomputable def abelC (r : K) (k : ℕ) : K := if k = 0 then r⁻¹ else ((k : K) + r) ^ (k - 1)

lemma abelC_eq_zpow (r : K) (k : ℕ) : abelC r k = ((k : K) + r) ^ ((k : ℤ) - 1) := by
  unfold abelC
  by_cases hk : k = 0
  · subst hk; simp
  · rw [if_neg hk, show (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ) by omega, zpow_natCast]

lemma abelC_mul_pow (r : K) (hr : r ≠ 0) (m k : ℕ) (hm : 1 ≤ m) (hk : k ≤ m) :
    abelC r k * ((k : K) + r) ^ (m - k) = ((k : K) + r) ^ (m - 1) := by
  unfold abelC
  by_cases h0 : k = 0
  · subst h0
    simp only [if_true, Nat.cast_zero, zero_add, Nat.sub_zero]
    obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [add_comm 1 m', pow_succ]
    simp [hr]
    field_simp
  · rw [if_neg h0, ← pow_add]
    congr 1; omega

/-- The polynomial in `s` on the left of Abel's identity. -/
noncomputable def abelPoly (r : K) (n : ℕ) : K[X] :=
  ∑ k ∈ range (n + 1), C ((n.choose k : K) * abelC r k) * (X - C (k : K)) ^ (n - k)

lemma abelPoly_derivative (r : K) (n : ℕ) :
    derivative (abelPoly r (n + 1)) = C ((n : K) + 1) * abelPoly r n := by
  unfold abelPoly
  rw [derivative_sum, sum_range_succ, mul_sum]
  have hlast : derivative (C (((n + 1).choose (n + 1) : K) * abelC r (n + 1))
      * (X - C ((n + 1 : ℕ) : K)) ^ (n + 1 - (n + 1))) = 0 := by
    simp
  rw [hlast, add_zero]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hk)
  rw [derivative_C_mul, derivative_X_sub_C_pow]
  have h1 := congrArg (fun x : ℕ => (x : K)) (Nat.choose_mul_succ_eq n k)
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h1
  rw [Nat.cast_sub (by omega : k ≤ n + 1)] at h1
  push_cast at h1
  have e : n + 1 - k - 1 = n - k := by omega
  rw [e, ← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul]
  congr 2
  push_cast [Nat.cast_sub (by omega : k ≤ n + 1)]
  linear_combination (abelC r k) * (-h1)

lemma abelPoly_eval_neg (r : K) (hr : r ≠ 0) (m : ℕ) (hm : 1 ≤ m) :
    (abelPoly r m).eval (-r) = 0 := by
  set P : K[X] := (X + C r) ^ (m - 1) with hP
  have hdeg : P.natDegree < m := by
    have : P.natDegree ≤ m - 1 := by
      rw [hP]; exact (natDegree_pow_le).trans (by simp)
    omega
  have h0 := congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hdeg) 0
  rw [fwdDiff_iter_eq_sum_shift] at h0
  simp only [Pi.zero_apply] at h0
  unfold abelPoly
  rw [eval_finsetSum]
  rw [← h0]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ m := Nat.lt_succ_iff.1 (mem_range.1 hk)
  simp only [eval_mul, eval_C, eval_pow, eval_sub, eval_X, hP, eval_add, zsmul_eq_mul, nsmul_eq_mul,
    Nat.cast_one, mul_one, zero_add]
  have e : (-r - (k : K)) ^ (m - k) = (-1) ^ (m - k) * ((k : K) + r) ^ (m - k) := by
    rw [← mul_pow]; congr 1; ring
  have := abelC_mul_pow r hr m k hm hk'
  rw [e]
  push_cast
  linear_combination ((-1 : K) ^ (m - k) * (m.choose k : K)) * this

/-- Abel's identity as a polynomial identity in `s`. -/
lemma abelPoly_eq (r : K) (hr : r ≠ 0) (n : ℕ) :
    abelPoly r n = C r⁻¹ * (X + C r) ^ n := by
  induction n with
  | zero =>
    simp [abelPoly, abelC, hr]
  | succ n ih =>
    have hd : derivative (abelPoly r (n + 1) - C r⁻¹ * (X + C r) ^ (n + 1)) = 0 := by
      rw [derivative_sub, abelPoly_derivative, ih, derivative_C_mul, derivative_pow]
      simp only [derivative_add, derivative_X, derivative_C, add_zero, mul_one, Nat.add_sub_cancel]
      push_cast
      ring
    have hc := eq_C_of_derivative_eq_zero hd
    have hev : (abelPoly r (n + 1) - C r⁻¹ * (X + C r) ^ (n + 1)).eval (-r) = 0 := by
      rw [eval_sub, abelPoly_eval_neg r hr (n + 1) (by omega)]
      simp
    rw [hc] at hev
    simp only [eval_C] at hev
    rw [hev, C_0] at hc
    exact sub_eq_zero.1 hc

/-- CO-053. Abel-type identity (Eq. 9.11.2): for `r ≠ 0`,
`∑_{k=0}^n C(n,k) (k+r)^(k-1) (s-k)^(n-k) = (r+s)^n / r`. -/
@[kb "petkovsekwilfzeilberger1996" "Equation (9.11.2), p. 200"]
theorem abel_identity (r s : K) (hr : r ≠ 0) (n : ℕ) :
    ∑ k ∈ range (n + 1), (n.choose k : K) * ((k : K) + r) ^ ((k : ℤ) - 1) * (s - k) ^ (n - k)
      = (r + s) ^ n / r := by
  have h := congrArg (Polynomial.eval s) (abelPoly_eq r hr n)
  unfold abelPoly at h
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_sub, eval_X, eval_add] at h
  rw [div_eq_inv_mul, add_comm r s, ← h]
  refine sum_congr rfl fun k _ => ?_
  rw [abelC_eq_zpow]

end Abel

/-- CO-053 (special case, Eq. 9.11.1): `∑_k C(n,k) (k+1)^(k-1) (n-k+1)^(n-k) = (n+2)^n`. -/
@[kb "petkovsekwilfzeilberger1996" "Equation (9.11.1), p. 200"]
theorem abel_special (n : ℕ) :
    ∑ k ∈ range (n + 1), n.choose k * (k + 1) ^ (k - 1) * (n - k + 1) ^ (n - k) = (n + 2) ^ n := by
  have h := abel_identity (K := ℚ) 1 ((n : ℚ) + 1) one_ne_zero n
  have h2 : ((∑ k ∈ range (n + 1), n.choose k * (k + 1) ^ (k - 1) * (n - k + 1) ^ (n - k) : ℕ) : ℚ)
      = (((n + 2) ^ n : ℕ) : ℚ) := by
    push_cast
    rw [show ((n : ℚ) + 2) = 1 + ((n : ℚ) + 1) by ring, ← div_one ((1 + ((n : ℚ) + 1)) ^ n), ← h]
    refine sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hk)
    rw [Nat.cast_sub hk']
    by_cases h0 : k = 0
    · subst h0; simp
    · rw [show ((k : ℤ) - 1) = ((k - 1 : ℕ) : ℤ) by omega, zpow_natCast]
      ring_nf
  exact_mod_cast h2

/-! ### CO-470: companion series of Example 7.5.2 -/

section CompanionGauss
open Filter Topology UndergradKB.Combinatorics.AeqB.Companions

/-- Summand `C(N,j) / (N * C(N+x,x))` (zero at `N = 0`). -/
noncomputable def omg (x j N : ℕ) : ℝ := (N.choose j : ℝ) / ((N : ℝ) * ((N + x).choose x : ℝ))

/-- Telescoping potential. -/
noncomputable def gpot (x j N : ℕ) : ℝ :=
  (x.factorial : ℝ) * (N.choose (j + 1) : ℝ) / (N.ascFactorial x : ℝ)

lemma omg_nonneg (x j N : ℕ) : 0 ≤ omg x j N := by unfold omg; positivity

lemma gpot_nonneg (x j N : ℕ) : 0 ≤ gpot x j N := by unfold gpot; positivity

lemma omg_alg (x j : ℕ) (f N q q1 c0 c1 : ℝ) (hN : 0 < N) (hq : 0 < q) (hq1 : 0 < q1)
    (hx : 0 < N + x) (hrel : N * q1 = (N + x) * q) (hc : c1 * (j + 1) = c0 * (N - j)) :
    ((x : ℝ) - j - 1) * (f * c1 / ((N + x) * q)) - j * (f * c0 / ((N + x) * q))
      = f * c1 / q - f * (c0 + c1) / q1 := by
  have hq1' : q1 = (N + x) * q / N := by field_simp; linarith
  have h : ((x : ℝ) - j - 1) * (f * c1 / ((N + x) * q)) - j * (f * c0 / ((N + x) * q))
      - (f * c1 / q - f * (c0 + c1) / q1)
      = -(f * (c1 * (j + 1) - c0 * (N - j))) / ((N + x) * q) := by
    rw [hq1']
    field_simp
    ring
  rw [hc, sub_self, mul_zero, neg_zero, zero_div] at h
  linarith

lemma omg_tele (x j N : ℕ) (hj : 1 ≤ j) :
    ((x : ℝ) - j - 1) * omg x (j + 1) N - j * omg x j N = gpot x j N - gpot x j (N + 1) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h1 : (Nat.choose 0 j) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h2 : (Nat.choose 0 (j + 1)) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h3 : (Nat.choose 1 (j + 1)) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [omg, gpot, h1, h2, h3]
  · obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
    have hq : 0 < ((M + 1).ascFactorial x : ℝ) := by
      have := Nat.ascFactorial_pos M x
      exact_mod_cast this
    have hq1 : 0 < ((M + 1 + 1).ascFactorial x : ℝ) := by
      have := Nat.ascFactorial_pos (M + 1) x
      exact_mod_cast this
    have hrel0 := Nat.succ_ascFactorial (M + 1) x
    have hrel : ((M + 1 : ℕ) : ℝ) * (((M + 1 + 1).ascFactorial x : ℕ) : ℝ)
        = (((M + 1 : ℕ) : ℝ) + x) * (((M + 1).ascFactorial x : ℕ) : ℝ) := by
      exact_mod_cast hrel0
    have hbin := Nat.ascFactorial_eq_factorial_mul_choose (M + 1) x
    have hbinR : (((M + 1 + 1).ascFactorial x : ℕ) : ℝ)
        = (x.factorial : ℝ) * (((M + 1 + x).choose x : ℕ) : ℝ) := by exact_mod_cast hbin
    have hpos : (0 : ℝ) < (((M + 1 : ℕ) : ℝ)) := by positivity
    have hcx : (0 : ℝ) < (((M + 1 + x).choose x : ℕ) : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega)
    have hf : (0 : ℝ) < (x.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos x
    have e1 := choose_rel (M + 1) j
    have e2 : ((M + 1 + 1).choose (j + 1) : ℝ)
        = ((M + 1).choose j : ℝ) + ((M + 1).choose (j + 1) : ℝ) := by
      rw [Nat.choose_succ_succ]; push_cast; ring
    have key := omg_alg x j (x.factorial : ℝ) ((M + 1 : ℕ) : ℝ)
      (((M + 1).ascFactorial x : ℕ) : ℝ) (((M + 1 + 1).ascFactorial x : ℕ) : ℝ)
      (((M + 1).choose j : ℕ) : ℝ) (((M + 1).choose (j + 1) : ℕ) : ℝ) hpos hq hq1
      (by positivity) hrel (by simpa using e1)
    have eO : ∀ j' : ℕ, omg x j' (M + 1)
        = (x.factorial : ℝ) * ((M + 1).choose j' : ℝ)
          / ((((M + 1 : ℕ) : ℝ) + x) * (((M + 1).ascFactorial x : ℕ) : ℝ)) := by
      intro j'
      unfold omg
      have h5 : ((M + 1 : ℕ) : ℝ) * (((M + 1 + x).choose x : ℕ) : ℝ)
          = (((M + 1 : ℕ) : ℝ) + x) * (((M + 1).ascFactorial x : ℕ) : ℝ) / (x.factorial : ℝ) := by
        have : (((M + 1 + x).choose x : ℕ) : ℝ) = (((M + 1 + 1).ascFactorial x : ℕ) : ℝ)
            / (x.factorial : ℝ) := by rw [hbinR]; field_simp
        rw [this, ← mul_div_assoc, hrel]
      rw [h5]
      field_simp
    rw [eO, eO]
    unfold gpot
    rw [e2]
    push_cast at key ⊢
    exact key

lemma gpot_tendsto (x j : ℕ) (h : j + 1 < x) : Tendsto (gpot x j) atTop (𝓝 0) := by
  set d := x - (j + 1) with hd
  have hd0 : d ≠ 0 := by omega
  have hlim : Tendsto (fun N : ℕ => (x.factorial : ℝ) * (1 / (N : ℝ)) ^ d) atTop (𝓝 0) := by
    have := ((tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).pow d).const_mul (x.factorial : ℝ)
    simpa [zero_pow hd0] using this
  refine squeeze_zero' (Eventually.of_forall fun N => gpot_nonneg x j N) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with N hN
  unfold gpot
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have h1 : (N.choose (j + 1) : ℝ) ≤ (N : ℝ) ^ (j + 1) := by exact_mod_cast Nat.choose_le_pow N (j + 1)
  have h2 : (N : ℝ) ^ x ≤ (N.ascFactorial x : ℝ) := by exact_mod_cast Nat.pow_succ_le_ascFactorial N x
  have hNx : (0 : ℝ) < (N : ℝ) ^ x := by positivity
  have hf : (0 : ℝ) < (x.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos x
  have h3 : (1 / (N : ℝ)) ^ d * (N : ℝ) ^ x = (N : ℝ) ^ (j + 1) := by
    rw [one_div, inv_pow, ← div_eq_inv_mul, show x = d + (j + 1) by omega, pow_add]
    field_simp
  rw [div_le_iff₀ (lt_of_lt_of_le hNx h2)]
  calc (x.factorial : ℝ) * (N.choose (j + 1) : ℝ)
      ≤ (x.factorial : ℝ) * (N : ℝ) ^ (j + 1) := by gcongr
    _ = (x.factorial : ℝ) * ((1 / (N : ℝ)) ^ d * (N : ℝ) ^ x) := by rw [h3]
    _ ≤ (x.factorial : ℝ) * ((1 / (N : ℝ)) ^ d * (N.ascFactorial x : ℝ)) := by gcongr
    _ = _ := by ring

lemma omg_step (x j : ℕ) (hj : 1 ≤ j) (hx : j + 1 < x) (s : ℝ) (hs : HasSum (omg x j) s) :
    HasSum (omg x (j + 1)) ((j : ℝ) / ((x : ℝ) - j - 1) * s) := by
  have hpos : (0 : ℝ) < (x : ℝ) - j - 1 := by
    have : (j : ℝ) + 1 < x := by exact_mod_cast hx
    linarith
  rw [hasSum_iff_tendsto_nat_of_nonneg (omg_nonneg x (j + 1))]
  have hps := hs.tendsto_sum_nat
  have key : ∀ M, ∑ i ∈ range M, omg x (j + 1) i
      = ((j : ℝ) / ((x : ℝ) - j - 1)) * ∑ i ∈ range M, omg x j i
        + (gpot x j 0 - gpot x j M) / ((x : ℝ) - j - 1) := by
    intro M
    have h1 : ∑ i ∈ range M, (((x : ℝ) - j - 1) * omg x (j + 1) i - j * omg x j i)
        = gpot x j 0 - gpot x j M := by
      rw [sum_congr rfl fun i _ => omg_tele x j i hj]
      exact Finset.sum_range_sub' (fun i => gpot x j i) M
    rw [sum_sub_distrib, ← mul_sum, ← mul_sum] at h1
    field_simp
    linarith
  simp_rw [key]
  have hg0 : gpot x j 0 = 0 := by simp [gpot]
  have := (hps.const_mul ((j : ℝ) / ((x : ℝ) - j - 1))).add
    (((gpot_tendsto x j hx).const_sub (gpot x j 0)).div_const ((x : ℝ) - j - 1))
  simpa [hg0] using this

lemma omg_base (x : ℕ) (hx : 2 ≤ x) : HasSum (omg x 1) (1 / ((x : ℝ) - 1)) := by
  have h := vandermonde_companion (x - 1) 0 (by omega)
  have h' := h.sub (hasSum_ite_eq 0 ((Nat.choose 0 0 : ℝ) / (((0 + (x - 1) + 1).choose 0 : ℕ) : ℝ)))
  have hxr : ((x - 1 : ℕ) : ℝ) = (x : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  convert h' using 1
  · funext n
    by_cases hn : n = 0
    · subst hn; simp [omg]
    · simp only [hn, if_false, sub_zero]
      unfold omg
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      have hc : (n.choose 1 : ℝ) = n := by simp
      have hsymm : ((n + (x - 1) + 1).choose n : ℝ) = ((n + x).choose x : ℝ) := by
        rw [show n + (x - 1) + 1 = n + x by omega]
        rw [Nat.choose_symm_add]
      rw [hc, hsymm]
      simp only [Nat.choose_zero_right, Nat.cast_one]
      field_simp
  · have hx1 : (0 : ℝ) < (x : ℝ) - 1 := by
      have : (2 : ℝ) ≤ x := by exact_mod_cast hx
      linarith
    simp only [Nat.choose_zero_right, Nat.cast_one, Nat.cast_zero, zero_add, Nat.choose_one_right]
    rw [hxr]
    field_simp
    ring

lemma omg_closed (x j : ℕ) (hj : 1 ≤ j) (hx : j + 1 < x) :
    HasSum (omg x j) ((x : ℝ) / (((j : ℝ) + 1) * j * (x.choose (j + 1) : ℝ))) := by
  induction j, hj using Nat.le_induction with
  | base =>
    have h := omg_base x (by omega)
    have e := choose_rel x 1
    have hx1 : (0 : ℝ) < (x : ℝ) - 1 := by
      have : (2 : ℝ) ≤ x := by exact_mod_cast (by omega : 2 ≤ x)
      linarith
    have hxx : (0 : ℝ) < x := by linarith
    have hc : (0 : ℝ) < (x.choose 2 : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
    convert h using 1
    simp only [Nat.cast_one, Nat.choose_one_right] at e ⊢
    field_simp
    nlinarith [e]
  | succ j hj ih =>
    have h1 := omg_step x j hj (by omega) _ (ih (by omega))
    convert h1 using 1
    have e := choose_rel x (j + 1)
    have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have hxj : (0 : ℝ) < (x : ℝ) - j - 1 := by
      have : (j : ℝ) + 1 < x := by exact_mod_cast (by omega : j + 1 < x)
      linarith
    have hc1 : (0 : ℝ) < (x.choose (j + 1) : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
    have hc2 : (0 : ℝ) < (x.choose (j + 1 + 1) : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
    push_cast at e ⊢
    field_simp
    nlinarith [e]

lemma omg_zero (x j : ℕ) (hj : 1 ≤ j) : omg x j 0 = 0 := by
  have : Nat.choose 0 j = 0 := Nat.choose_eq_zero_of_lt (by omega)
  simp [omg, this]

lemma omg_lt (x j l : ℕ) (hl : l < j) : omg x j l = 0 := by
  have : Nat.choose l j = 0 := Nat.choose_eq_zero_of_lt hl
  simp [omg, this]

/-- CO-470 (companion of Example 7.5.2), binomial form. For `2 ≤ k < x`:
`∑_{n ≥ 0} C(n+1,k-1) / ((n+1) C(x+n+1,x)) = x / (k (k-1) C(x,k))`. This is the identity obtained
from the WZ pair of `∑_k k C(n+1,k) C(x,k) / ((n+1) C(n+x,n+1)) = 1` before tidying. -/
@[kb "petkovsekwilfzeilberger1996" "Example 7.5.2, p. 148"]
theorem companion_binomial (x k : ℕ) (hk : 2 ≤ k) (hkx : k < x) :
    HasSum (fun n : ℕ => ((n + 1).choose (k - 1) : ℝ) / (((n : ℝ) + 1) * ((x + n + 1).choose x : ℝ)))
      ((x : ℝ) / ((k : ℝ) * ((k : ℝ) - 1) * (x.choose k : ℝ))) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hj : 1 ≤ j := by omega
  have h := (hasSum_nat_add_iff' 1).mpr (omg_closed x j hj (by omega))
  rw [sum_range_one, omg_zero x j hj, sub_zero] at h
  convert h using 1
  · funext n
    unfold omg
    rw [Nat.add_sub_cancel, show x + n + 1 = n + 1 + x by ring]
    push_cast
    rfl
  · push_cast
    rw [show ((j : ℝ) + 1 - 1) = j by ring]

lemma omg_term (x i m : ℕ) :
    ((i + 1).factorial : ℝ) / (x.factorial : ℝ) * omg x (i + 1) (m + (i + 1))
      = ((m + i).factorial : ℝ) * ((m + i + 1).factorial : ℝ)
        / ((m.factorial : ℝ) * ((x + m + i + 1).factorial : ℝ)) := by
  unfold omg
  have c1 := Nat.cast_choose ℝ (show i + 1 ≤ m + (i + 1) by omega)
  have c2 := Nat.cast_choose ℝ (show x ≤ m + (i + 1) + x by omega)
  rw [Nat.add_sub_cancel_right] at c1
  rw [Nat.add_sub_cancel] at c2
  have e : m + (i + 1) + x = x + m + i + 1 := by ring
  rw [c1, c2, e]
  have f1 : (m + (i + 1)).factorial = (m + i + 1) * (m + i).factorial := by
    rw [show m + (i + 1) = (m + i) + 1 by ring, Nat.factorial_succ]
  have p1 := Nat.factorial_pos m
  have p2 := Nat.factorial_pos (i + 1)
  have p3 := Nat.factorial_pos x
  have p4 := Nat.factorial_pos (m + i)
  have p5 := Nat.factorial_pos (x + m + i + 1)
  rw [show m + (i + 1) = (m + i) + 1 by ring] at f1 ⊢
  rw [f1]
  push_cast
  have : ((m : ℝ) + i + 1) ≠ 0 := by positivity
  field_simp

/-- CO-470 (companion of Example 7.5.2), factorial form. For `2 ≤ k < x`, writing `k = i + 2`,
`∑_{m ≥ 0} (m+i)! (m+i+1)! / (m! (x+m+i+1)!) = i! / (k C(x,k) (x-1)!)`
(the sum over `n ≥ 0` of `n!(n+1)!/((n-k+2)!(x+n+1)!)` in the book, with `n = m + k - 2` and the
terms with `n < k - 2` omitted since `1/(negative)!` is zero). The book's right-hand side is
missing the factor `1/k` (check `x = 3`, `k = 2`: the sum is `1/12`). -/
@[kb "petkovsekwilfzeilberger1996" "Example 7.5.2, p. 148"]
theorem companion_factorial (x i : ℕ) (hx : i + 2 < x) :
    HasSum (fun m : ℕ => ((m + i).factorial : ℝ) * ((m + i + 1).factorial : ℝ)
        / ((m.factorial : ℝ) * ((x + m + i + 1).factorial : ℝ)))
      ((i.factorial : ℝ) / (((i : ℝ) + 2) * (x.choose (i + 2) : ℝ) * ((x - 1).factorial : ℝ))) := by
  have h := (hasSum_nat_add_iff' (i + 1)).mpr (omg_closed x (i + 1) (by omega) (by omega))
  have hz : ∑ l ∈ range (i + 1), omg x (i + 1) l = 0 :=
    sum_eq_zero fun l hl => omg_lt x (i + 1) l (by simpa using hl)
  rw [hz, sub_zero] at h
  have h2 := h.mul_left (((i + 1).factorial : ℝ) / (x.factorial : ℝ))
  convert h2 using 1
  · funext m
    exact (omg_term x i m).symm
  · have hx1 : x = (x - 1) + 1 := by omega
    have hfx : (x.factorial : ℝ) = (x : ℝ) * ((x - 1).factorial : ℝ) := by
      conv_lhs => rw [hx1, Nat.factorial_succ]
      push_cast [Nat.cast_sub (by omega : 1 ≤ x)]
      ring
    have hf1 : ((i + 1).factorial : ℝ) = ((i : ℝ) + 1) * (i.factorial : ℝ) := by
      push_cast [Nat.factorial_succ]; ring
    have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
    have hc : (0 : ℝ) < (x.choose (i + 1 + 1) : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega)
    have hfp : (0 : ℝ) < ((x - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    rw [hfx, hf1]
    push_cast
    field_simp
    ring

end CompanionGauss

end UndergradKB.Combinatorics.AeqB.Identities2
