import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import UndergradKB.Common.Attr

namespace UndergradKB.Combinatorics.AeqB.Companions
open Finset Filter Topology

/-- CO-052. Chu–Vandermonde in the symmetric form `∑_k C(n,k) C(b,k) = C(n+b,b)`. -/
@[kb "petkovsekwilfzeilberger1996" "text (Chu-Vandermonde), p. 190"]
theorem sum_choose_mul_choose (n b : ℕ) :
    ∑ k ∈ range (n + 1), n.choose k * b.choose k = (n + b).choose b := by
  have h := Nat.add_choose_eq b n n
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  rw [add_comm n b, Nat.choose_symm_add, h]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hk)
  simp only
  rw [Nat.choose_symm hk', mul_comm]

/-- Rising factorial `(n+1)(n+2)...(n+a)` as a real number. -/
noncomputable def risingR (a n : ℕ) : ℝ := ((n + 1).ascFactorial a : ℝ)

lemma risingR_pos (a n : ℕ) : 0 < risingR a n := by
  unfold risingR
  exact_mod_cast Nat.ascFactorial_pos _ _

lemma risingR_succ (a n : ℕ) :
    ((n : ℝ) + 1) * risingR a (n + 1) = ((n : ℝ) + a + 1) * risingR a n := by
  unfold risingR
  have := Nat.succ_ascFactorial (n + 1) a
  have h : ((n + 1 : ℕ) : ℝ) * (((n + 1 + 1).ascFactorial a : ℕ) : ℝ)
      = ((n + 1 + a : ℕ) : ℝ) * (((n + 1).ascFactorial a : ℕ) : ℝ) := by exact_mod_cast this
  push_cast at h
  linarith

/-- The summand `C(n,k) / C(n+a+1, n)` of the companion series. -/
noncomputable def compT (a k n : ℕ) : ℝ := (n.choose k : ℝ) / ((n + a + 1).choose n : ℝ)

lemma compT_eq (a k n : ℕ) :
    compT a k n = ((a + 1).factorial : ℝ) * (n.choose k : ℝ) / (((n : ℝ) + a + 1) * risingR a n) := by
  unfold compT
  have h1 := Nat.ascFactorial_eq_factorial_mul_choose n (a + 1)
  rw [Nat.ascFactorial_succ] at h1
  have h2 : (n + (a + 1)).choose (a + 1) = (n + a + 1).choose n := by
    rw [show n + (a + 1) = (a + 1) + n by ring, Nat.choose_symm_add]
    congr 1
    omega
  rw [h2] at h1
  have h3 : (((n + 1 + a : ℕ) : ℝ)) * risingR a n
      = ((a + 1).factorial : ℝ) * ((n + a + 1).choose n : ℝ) := by
    unfold risingR; exact_mod_cast h1
  push_cast at h3
  have hc : (0 : ℝ) < ((n + a + 1).choose n : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hf : (0 : ℝ) < ((a + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have h4 : ((n : ℝ) + a + 1) * risingR a n
      = ((a + 1).factorial : ℝ) * ((n + a + 1).choose n : ℝ) := by
    linarith
  rw [h4]; field_simp

lemma compT_nonneg (a k n : ℕ) : 0 ≤ compT a k n := by
  unfold compT; positivity

/-- The telescoping potential. -/
noncomputable def compG (a k n : ℕ) : ℝ :=
  ((a + 1).factorial : ℝ) * (n.choose k : ℝ) / risingR a n

lemma compG_tele (a k n : ℕ) :
    ((a : ℝ) - k - 1) * compT a (k + 1) n - (k + 1) * compT a k n
      = compG a (k + 1) n - compG a (k + 1) (n + 1) := by
  rw [compT_eq, compT_eq]
  unfold compG
  have hu := risingR_pos a n
  have hw := risingR_pos a (n + 1)
  have hr := risingR_succ a n
  have hx : (0:ℝ) < (n:ℝ) + a + 1 := by positivity
  by_cases hkn : k ≤ n
  · have e1 := Nat.choose_succ_right_eq n k
    have e1' : (n.choose (k+1) : ℝ) * (k + 1) = (n.choose k : ℝ) * ((n : ℝ) - k) := by
      have := congrArg (fun x : ℕ => (x : ℝ)) e1
      simpa [Nat.cast_sub hkn] using this
    have e2 : ((n + 1).choose (k + 1) : ℝ) = (n.choose k : ℝ) + (n.choose (k+1) : ℝ) := by
      rw [Nat.choose_succ_succ]; push_cast; ring
    rw [e2]
    have hw' : risingR a (n + 1) = ((n : ℝ) + a + 1) * risingR a n / ((n : ℝ) + 1) := by
      field_simp; linarith
    rw [hw']
    field_simp
    linear_combination (-1 : ℝ) * e1'
  · have h0 : n.choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h1 : n.choose (k+1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h2 : (n + 1).choose (k + 1) = n.choose k + n.choose (k + 1) := Nat.choose_succ_succ _ _
    simp [h0, h1, h2]

lemma compG_nonneg (a k n : ℕ) : 0 ≤ compG a k n := by
  have := risingR_pos a n
  unfold compG; positivity

lemma compG_tendsto (a k : ℕ) (h : k < a) : Tendsto (compG a k) atTop (𝓝 0) := by
  set d := a - k with hd
  have hd0 : d ≠ 0 := by omega
  have hlim : Tendsto (fun n : ℕ => ((a + 1).factorial : ℝ) * (1 / ((n : ℝ) + 1)) ^ d)
      atTop (𝓝 0) := by
    have := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow d).const_mul
      ((a + 1).factorial : ℝ)
    simpa [zero_pow hd0] using this
  refine squeeze_zero (fun n => compG_nonneg a k n) (fun n => ?_) hlim
  unfold compG risingR
  have hpos : (0:ℝ) < (((n + 1).ascFactorial a : ℕ) : ℝ) := by
    exact_mod_cast Nat.ascFactorial_pos _ _
  rw [div_le_iff₀ hpos]
  have h1 : (n.choose k : ℝ) ≤ ((n : ℝ) + 1) ^ k := by
    have : n.choose k ≤ (n+1) ^ k :=
      (Nat.choose_le_pow n k).trans (Nat.pow_le_pow_left (by omega) _)
    exact_mod_cast this
  have h2 : ((n : ℝ) + 1) ^ a ≤ (((n + 1).ascFactorial a : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_succ_le_ascFactorial (n + 1) a
  have hn : (0:ℝ) < (n:ℝ) + 1 := by positivity
  have h3 : (1 / ((n : ℝ) + 1)) ^ d * ((n : ℝ) + 1) ^ a = ((n : ℝ) + 1) ^ k := by
    rw [one_div, inv_pow, ← div_eq_inv_mul, show a = d + k by omega, pow_add]
    field_simp
  have hf : (0:ℝ) < ((a + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  calc ((a + 1).factorial : ℝ) * (n.choose k : ℝ)
      ≤ ((a + 1).factorial : ℝ) * ((n : ℝ) + 1) ^ k := by gcongr
    _ = ((a + 1).factorial : ℝ) * ((1 / ((n : ℝ) + 1)) ^ d * ((n : ℝ) + 1) ^ a) := by rw [h3]
    _ ≤ ((a + 1).factorial : ℝ) * ((1 / ((n : ℝ) + 1)) ^ d
          * (((n + 1).ascFactorial a : ℕ) : ℝ)) := by gcongr
    _ = _ := by ring

/-- General telescoping: partial sums of a nonnegative series that differs from a multiple
of a convergent one by a telescoping term. -/
lemma compT_step (a k : ℕ) (hk : k + 1 < a) (s : ℝ) (hs : HasSum (compT a k) s) :
    HasSum (compT a (k + 1)) (((k : ℝ) + 1) / ((a : ℝ) - k - 1) * s) := by
  have hpos : (0:ℝ) < (a:ℝ) - k - 1 := by
    have : (k : ℝ) + 1 < a := by exact_mod_cast hk
    linarith
  rw [hasSum_iff_tendsto_nat_of_nonneg (compT_nonneg a (k + 1))]
  have hps := hs.tendsto_sum_nat
  have key : ∀ N, ∑ i ∈ range N, compT a (k + 1) i
      = (((k : ℝ) + 1) / ((a : ℝ) - k - 1)) * ∑ i ∈ range N, compT a k i
        + (compG a (k + 1) 0 - compG a (k + 1) N) / ((a : ℝ) - k - 1) := by
    intro N
    have h1 : ∑ i ∈ range N, (((a : ℝ) - k - 1) * compT a (k + 1) i - (k + 1) * compT a k i)
        = compG a (k + 1) 0 - compG a (k + 1) N := by
      rw [sum_congr rfl fun i _ => compG_tele a k i]
      exact Finset.sum_range_sub' (fun i => compG a (k + 1) i) N
    rw [sum_sub_distrib, ← mul_sum, ← mul_sum] at h1
    field_simp
    linarith
  simp_rw [key]
  have hg0 : compG a (k + 1) 0 = 0 := by simp [compG]
  have := (hps.const_mul (((k : ℝ) + 1) / ((a : ℝ) - k - 1))).add
    (((compG_tendsto a (k + 1) hk).const_sub (compG a (k + 1) 0)).div_const
      ((a : ℝ) - k - 1))
  simpa [hg0] using this

lemma compT_base (a : ℕ) (ha : 0 < a) : HasSum (compT a 0) (((a : ℝ) + 1) / a) := by
  have hapos : (0:ℝ) < a := by exact_mod_cast ha
  rw [hasSum_iff_tendsto_nat_of_nonneg (compT_nonneg a 0)]
  have htele : ∀ n, (a : ℝ) * compT a 0 n = compG a 0 n - compG a 0 (n + 1) := by
    intro n
    rw [compT_eq]
    unfold compG
    have hu := risingR_pos a n
    have hr := risingR_succ a n
    have hx : (0:ℝ) < (n:ℝ) + a + 1 := by positivity
    have hw' : risingR a (n + 1) = ((n : ℝ) + a + 1) * risingR a n / ((n : ℝ) + 1) := by
      have : (0:ℝ) < (n:ℝ) + 1 := by positivity
      field_simp; linarith
    rw [hw']
    simp only [Nat.choose_zero_right, Nat.cast_one]
    field_simp
    ring
  have key : ∀ N, ∑ i ∈ range N, compT a 0 i = (compG a 0 0 - compG a 0 N) / a := by
    intro N
    have h1 : ∑ i ∈ range N, (a : ℝ) * compT a 0 i = compG a 0 0 - compG a 0 N := by
      rw [sum_congr rfl fun i _ => htele i]
      exact Finset.sum_range_sub' (fun i => compG a 0 i) N
    rw [← mul_sum] at h1
    field_simp
    linarith
  simp_rw [key]
  have hg0 : compG a 0 0 = ((a : ℝ) + 1) * (a.factorial : ℝ) / (a.factorial : ℝ) := by
    simp [compG, risingR, Nat.factorial_succ]
  have hf : (a.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos a).ne'
  have hg : compG a 0 0 = (a : ℝ) + 1 := by rw [hg0]; field_simp
  have := (((compG_tendsto a 0 ha).const_sub (compG a 0 0)).div_const (a : ℝ))
  simpa [hg] using this

/-- CO-050 (companion identity). For integers `a > k ≥ 0`:
`∑_{n ≥ 0} C(n,k) / C(n+a+1, n) = (a+1) / ((k+1) C(a,k+1))`. -/
@[kb "petkovsekwilfzeilberger1996" "Example 7.3.4, p. 140"]
theorem vandermonde_companion (a k : ℕ) (hk : k < a) :
    HasSum (fun n : ℕ => (n.choose k : ℝ) / ((n + a + 1).choose n : ℝ))
      (((a : ℝ) + 1) / (((k : ℝ) + 1) * (a.choose (k + 1) : ℝ))) := by
  induction k with
  | zero =>
    have := compT_base a (by omega)
    have h' : HasSum (fun n : ℕ => (n.choose 0 : ℝ) / ((n + a + 1).choose n : ℝ))
        (((a : ℝ) + 1) / a) := this
    convert h' using 1
    simp
  | succ k ih =>
    have h0 := compT_step a k hk _ (ih (by omega))
    have h : HasSum (fun n : ℕ => (n.choose (k + 1) : ℝ) / ((n + a + 1).choose n : ℝ)) _ := h0
    convert h using 1
    have hpos : (0:ℝ) < (a:ℝ) - k - 1 := by
      have : (k : ℝ) + 1 < a := by exact_mod_cast hk
      linarith
    have e := Nat.choose_succ_right_eq a (k + 1)
    have e' : (a.choose (k + 2) : ℝ) * ((k : ℝ) + 2) = (a.choose (k + 1) : ℝ) * ((a : ℝ) - k - 1) := by
      have := congrArg (fun x : ℕ => (x : ℝ)) e
      have hh : k + 1 ≤ a := by omega
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hh] at this
      push_cast at this
      linear_combination this
    have hc1 : (0:ℝ) < (a.choose (k + 1) : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
    have hc2 : (0:ℝ) < (a.choose (k + 2) : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
    push_cast
    field_simp
    nlinarith [e']

/-! ### CO-455: companion of `∑_k C(n,k)^2 = C(2n,n)` -/

/-- `F(n,k) = C(n,k)^2 / C(2n,n)`, the WZ summand of `∑_k C(n,k)^2 = C(2n,n)`. -/
noncomputable def wzF (n k : ℕ) : ℝ := (n.choose k : ℝ) ^ 2 / ((2 * n).choose n : ℝ)

/-- The companion summand `(3n-2k+1)/(2n+1) * F(n,k)`. -/
noncomputable def wzT (k n : ℕ) : ℝ := (3 * (n : ℝ) - 2 * k + 1) / (2 * n + 1) * wzF n k

lemma central_pos (n : ℕ) : (0 : ℝ) < ((2 * n).choose n : ℝ) := by
  exact_mod_cast Nat.choose_pos (by omega)

lemma central_succ (n : ℕ) :
    ((2 * (n + 1)).choose (n + 1) : ℝ) * (n + 1) = 2 * (2 * n + 1) * ((2 * n).choose n : ℝ) := by
  have h := Nat.succ_mul_centralBinom_succ n
  rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at h
  have h' : (((2 * (n + 1)).choose (n + 1) * (n + 1) : ℕ) : ℝ)
      = ((2 * (2 * n + 1) * (2 * n).choose n : ℕ) : ℝ) := by
    rw [mul_comm]; exact_mod_cast h
  push_cast at h'
  exact h'

lemma choose_rel (n k : ℕ) :
    (n.choose (k + 1) : ℝ) * (k + 1) = (n.choose k : ℝ) * ((n : ℝ) - k) := by
  by_cases hkn : k ≤ n
  · have := congrArg (fun x : ℕ => (x : ℝ)) (Nat.choose_succ_right_eq n k)
    simpa [Nat.cast_sub hkn] using this
  · have h0 : n.choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h1 : n.choose (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [h0, h1]

lemma wzT_step (k n : ℕ) :
    wzT (k + 1) n - wzT k n = 2 * (wzF n (k + 1) - wzF (n + 1) (k + 1)) := by
  have hc := central_pos n
  have hc' := central_succ n
  have e := choose_rel n k
  have e2 : ((n + 1).choose (k + 1) : ℝ) = (n.choose k : ℝ) + (n.choose (k + 1) : ℝ) := by
    rw [Nat.choose_succ_succ]; push_cast; ring
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcc : ((2 * (n + 1)).choose (n + 1) : ℝ) = 2 * (2 * n + 1) * ((2 * n).choose n : ℝ) / (n + 1) := by
    field_simp; linarith
  unfold wzT wzF
  rw [e2, hcc]
  push_cast
  set c := ((2 * n).choose n : ℝ)
  set y0 := (n.choose k : ℝ)
  set y1 := (n.choose (k + 1) : ℝ)
  have hnum : (3 * (n : ℝ) - 2 * k - 1) * y1 ^ 2 - (3 * n - 2 * k + 1) * y0 ^ 2
      - 2 * (2 * n + 1) * y1 ^ 2 + (n + 1) * (y0 + y1) ^ 2 = 0 := by
    linear_combination (2 * y0 - 2 * y1) * e
  have hd : (0 : ℝ) < 2 * n + 1 := by positivity
  have h : (3 * (n : ℝ) - 2 * ((k : ℝ) + 1) + 1) / (2 * n + 1) * (y1 ^ 2 / c)
      - (3 * n - 2 * k + 1) / (2 * n + 1) * (y0 ^ 2 / c)
      - 2 * (y1 ^ 2 / c - (y0 + y1) ^ 2 / (2 * (2 * n + 1) * c / (n + 1)))
      = ((3 * (n : ℝ) - 2 * k - 1) * y1 ^ 2 - (3 * n - 2 * k + 1) * y0 ^ 2
      - 2 * (2 * n + 1) * y1 ^ 2 + (n + 1) * (y0 + y1) ^ 2) / ((2 * n + 1) * c) := by
    field_simp
    ring
  rw [hnum, zero_div] at h
  linarith

lemma wzT_zero (n : ℕ) : wzT 0 n = 2 * (wzF n 0 - wzF (n + 1) 0) := by
  have hc := central_pos n
  have hc' := central_succ n
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcc : ((2 * (n + 1)).choose (n + 1) : ℝ) = 2 * (2 * n + 1) * ((2 * n).choose n : ℝ) / (n + 1) := by
    field_simp; linarith
  unfold wzT wzF
  rw [hcc]
  simp only [Nat.choose_zero_right, Nat.cast_one, Nat.cast_zero]
  field_simp
  ring

lemma wzT_partial (k N : ℕ) :
    ∑ i ∈ range N, wzT k i = 2 - 2 * ∑ j ∈ range (k + 1), wzF N j := by
  induction k with
  | zero =>
    rw [sum_congr rfl fun i _ => wzT_zero i, ← mul_sum,
      Finset.sum_range_sub' (fun i => wzF i 0) N]
    simp [wzF]
    ring
  | succ k ih =>
    have h1 : ∑ i ∈ range N, wzT (k + 1) i
        = ∑ i ∈ range N, wzT k i + ∑ i ∈ range N, 2 * (wzF i (k + 1) - wzF (i + 1) (k + 1)) := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun i _ => by linarith [wzT_step k i]
    rw [h1, ih, ← mul_sum, Finset.sum_range_sub' (fun i => wzF i (k + 1)) N,
      sum_range_succ _ (k + 1)]
    have : wzF 0 (k + 1) = 0 := by simp [wzF]
    rw [this]
    ring

lemma wzF_tendsto (j : ℕ) : Tendsto (fun N => wzF N j) atTop (𝓝 0) := by
  have hlim : Tendsto (fun N : ℕ => 3 * ((N : ℝ) ^ (2 * j + 1) / 4 ^ N)) atTop (𝓝 0) := by
    have := (tendsto_pow_const_div_const_pow_of_one_lt (2 * j + 1) (r := 4) (by norm_num)).const_mul 3
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun N => ?_) ?_ hlim
  · unfold wzF; have := central_pos N; positivity
  · filter_upwards [eventually_ge_atTop 1] with N hN
    unfold wzF
    have hc := central_pos N
    have h4 : (4 : ℝ) ^ N ≤ (2 * N + 1) * ((2 * N).choose N : ℝ) := by
      have := Nat.four_pow_le_two_mul_add_one_mul_centralBinom N
      rw [Nat.centralBinom_eq_two_mul_choose] at this
      exact_mod_cast this
    have h1 : (N.choose j : ℝ) ^ 2 ≤ (N : ℝ) ^ (2 * j) := by
      have : N.choose j ≤ N ^ j := Nat.choose_le_pow N j
      have h' : (N.choose j : ℝ) ≤ (N : ℝ) ^ j := by exact_mod_cast this
      calc (N.choose j : ℝ) ^ 2 ≤ ((N : ℝ) ^ j) ^ 2 := by gcongr
        _ = _ := by rw [← pow_mul, mul_comm]
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have h4p : (0 : ℝ) < 4 ^ N := by positivity
    rw [div_le_iff₀ hc]
    have h5 : (N : ℝ) ^ (2 * j + 1) = (N : ℝ) ^ (2 * j) * N := pow_succ _ _
    have h6 : (N : ℝ) ^ (2 * j) * (2 * N + 1) ≤ 3 * (N : ℝ) ^ (2 * j + 1) := by
      rw [h5]
      have : (0 : ℝ) ≤ (N : ℝ) ^ (2 * j) := by positivity
      nlinarith
    calc (N.choose j : ℝ) ^ 2 ≤ (N : ℝ) ^ (2 * j) := h1
      _ = (N : ℝ) ^ (2 * j) * 4 ^ N / 4 ^ N := by field_simp
      _ ≤ (N : ℝ) ^ (2 * j) * ((2 * N + 1) * ((2 * N).choose N : ℝ)) / 4 ^ N := by gcongr
      _ = ((N : ℝ) ^ (2 * j) * (2 * N + 1)) * ((2 * N).choose N : ℝ) / 4 ^ N := by ring
      _ ≤ (3 * (N : ℝ) ^ (2 * j + 1)) * ((2 * N).choose N : ℝ) / 4 ^ N := by gcongr
      _ = 3 * ((N : ℝ) ^ (2 * j + 1) / 4 ^ N) * ((2 * N).choose N : ℝ) := by ring

lemma wzT_nonneg (k n : ℕ) : 0 ≤ wzT k n := by
  unfold wzT wzF
  have hc := central_pos n
  by_cases hkn : k ≤ n
  · have : (k : ℝ) ≤ n := by exact_mod_cast hkn
    have : (0 : ℝ) ≤ 3 * (n : ℝ) - 2 * k + 1 := by linarith
    positivity
  · have h0 : n.choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [h0]

/-- CO-455. Companion of `∑_k C(n,k)^2 = C(2n,n)`: for every `k ≥ 0`,
`∑_{n ≥ 0} (3n-2k+1)/(2n+1) * C(n,k)^2 / C(2n,n) = 2`. Proof: the WZ equation gives
`T_{k+1}(n) - T_k(n) = 2 (F(n,k+1) - F(n+1,k+1))`, so the partial sums are explicit. -/
@[kb "petkovsekwilfzeilberger1996" "Example 7.3.1, p. 138"]
theorem companion_sum_choose_sq (k : ℕ) :
    HasSum (fun n : ℕ => (3 * (n : ℝ) - 2 * k + 1) / (2 * n + 1) * (n.choose k : ℝ) ^ 2
      / ((2 * n).choose n : ℝ)) 2 := by
  have h : HasSum (wzT k) 2 := by
    rw [hasSum_iff_tendsto_nat_of_nonneg (wzT_nonneg k)]
    simp_rw [wzT_partial]
    have hs : Tendsto (fun N => ∑ j ∈ range (k + 1), wzF N j) atTop (𝓝 0) := by
      have := tendsto_finsetSum (range (k + 1)) (fun j _ => wzF_tendsto j)
      simpa using this
    simpa using (hs.const_mul 2).const_sub 2
  convert h using 2 with n
  unfold wzT wzF
  ring

/-! ### CO-493: the sum `∑_k C(n,k) C(n+k,k)` -/

lemma choose_mul_succ_real (p q : ℕ) :
    (p.choose q : ℝ) * ((p : ℝ) + 1) = ((p + 1).choose q : ℝ) * ((p : ℝ) + 1 - q) := by
  by_cases h : q ≤ p + 1
  · have := congrArg (fun x : ℕ => (x : ℝ)) (Nat.choose_mul_succ_eq p q)
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at this
    rw [Nat.cast_sub h] at this
    push_cast at this
    exact this
  · have h0 : (p + 1).choose q = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h1 : p.choose q = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [h0, h1]

/-- Algebraic core of the Zeilberger certificate `R(n,k) = -2 k^2 (2n+3) / ((n+1-k)(n+2-k))`
for `F(n,k) = C(n,k) C(n+k,k)`, written without the poles of `R`. -/
lemma delannoy_alg (n k u2 u1 u v2 v1 v w z : ℝ) (hn : 0 ≤ n) (hk : 0 ≤ k)
    (hA : u1 * (n + 2) = u2 * (n + 2 - k)) (hB : u * (n + 1) = u1 * (n + 1 - k))
    (hC : v1 * (n + k + 2) = v2 * (n + 2)) (hD : v * (n + k + 1) = v1 * (n + 1))
    (hE : w * (k + 1) = u2 * (n + 2 - k)) (hF : z * (k + 1) = v1 * (n + 1)) :
    (n + 2) * (u2 * v2) - 3 * (2 * n + 3) * (u1 * v1) + (n + 1) * (u * v)
      = -2 * (2 * n + 3) * (k + 1) ^ 2 * (w * z) / ((n + 1) * (n + 2))
        - (-2 * (2 * n + 3) * k ^ 2 * (u2 * v) / ((n + 1) * (n + 2))) := by
  have h1 : 0 < n + 1 := by linarith
  have h2 : 0 < n + 2 := by linarith
  have h3 : 0 < n + k + 1 := by linarith
  have h4 : 0 < n + k + 2 := by linarith
  have h5 : 0 < k + 1 := by linarith
  have eu1 : u1 = u2 * (n + 2 - k) / (n + 2) := by field_simp; linarith
  have eu : u = u1 * (n + 1 - k) / (n + 1) := by field_simp; linarith
  have ev1 : v1 = v2 * (n + 2) / (n + k + 2) := by field_simp; linarith
  have ev : v = v1 * (n + 1) / (n + k + 1) := by field_simp; linarith
  have ew : w = u2 * (n + 2 - k) / (k + 1) := by field_simp; linarith
  have ez : z = v1 * (n + 1) / (k + 1) := by field_simp; linarith
  rw [ew, ez, eu, ev, eu1, ev1]
  field_simp
  ring

/-- Summand `C(n,k) C(n+k,k)` (real-valued). -/
noncomputable def dF (n k : ℕ) : ℝ := (n.choose k : ℝ) * ((n + k).choose k : ℝ)

/-- Telescoping term of the certificate. -/
noncomputable def dG (n k : ℕ) : ℝ :=
  -2 * (2 * (n : ℝ) + 3) * (k : ℝ) ^ 2 * ((n + 2).choose k : ℝ) * ((n + k).choose k : ℝ)
    / (((n : ℝ) + 1) * ((n : ℝ) + 2))

lemma dF_step (n k : ℕ) :
    ((n : ℝ) + 2) * dF (n + 2) k - 3 * (2 * n + 3) * dF (n + 1) k + ((n : ℝ) + 1) * dF n k
      = dG n (k + 1) - dG n k := by
  have hA := choose_mul_succ_real (n + 1) k
  have hB := choose_mul_succ_real n k
  have hC := choose_mul_succ_real (n + 1 + k) k
  have hD := choose_mul_succ_real (n + k) k
  have hE := choose_rel (n + 2) k
  have hF := choose_rel (n + 1 + k) k
  have e1 : n + 1 + k + 1 = n + 2 + k := by ring
  have e2 : n + k + 1 = n + 1 + k := by ring
  rw [e1] at hC
  rw [e2] at hD
  push_cast at hA hB hC hD hE hF
  have key := delannoy_alg n k ((n + 2).choose k) ((n + 1).choose k) (n.choose k)
    ((n + 2 + k).choose k) ((n + 1 + k).choose k) ((n + k).choose k)
    ((n + 2).choose (k + 1)) ((n + 1 + k).choose (k + 1)) (by positivity) (by positivity)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  unfold dF dG
  have e3 : n + (k + 1) = n + 1 + k := by ring
  rw [e3]
  push_cast
  linear_combination key

/-- The sum `∑_k C(n,k) C(n+k,k)` (central Delannoy numbers). -/
def delannoySum (n : ℕ) : ℕ := ∑ k ∈ range (n + 1), n.choose k * (n + k).choose k

lemma delannoySum_real (n M : ℕ) (hM : n + 1 ≤ M) :
    (delannoySum n : ℝ) = ∑ k ∈ range M, dF n k := by
  unfold delannoySum dF
  push_cast
  refine sum_subset (Finset.range_mono hM) ?_
  intro k _ hk
  have : n.choose k = 0 := Nat.choose_eq_zero_of_lt (by simpa using hk)
  simp [this]

/-- CO-493 (recurrence part). The sums `D(n) = ∑_k C(n,k) C(n+k,k)` satisfy the second-order
recurrence `(n+2) D(n+2) = 3 (2n+3) D(n+1) - (n+1) D(n)` (written without subtraction). The
recurrence printed in the book (p. 164,`(n+2)^3 y(n+2) - (2n+3)(17n^2+51n+39) y(n+1) +
(n+1)^3 y(n) = 0`) is the corresponding statement for the Apéry sum with squared binomials;
that one is not proved here. -/
@[kb "petkovsekwilfzeilberger1996" "Example 8.4.2, p. 164"]
theorem delannoySum_rec (n : ℕ) :
    (n + 2) * delannoySum (n + 2) + (n + 1) * delannoySum n
      = 3 * (2 * n + 3) * delannoySum (n + 1) := by
  have hR : ((n : ℝ) + 2) * (delannoySum (n + 2) : ℝ) + ((n : ℝ) + 1) * (delannoySum n : ℝ)
      = 3 * (2 * (n : ℝ) + 3) * (delannoySum (n + 1) : ℝ) := by
    rw [delannoySum_real (n + 2) (n + 3) (by omega), delannoySum_real n (n + 3) (by omega),
      delannoySum_real (n + 1) (n + 3) (by omega)]
    have hsum : ∑ k ∈ range (n + 3), (((n : ℝ) + 2) * dF (n + 2) k - 3 * (2 * n + 3) * dF (n + 1) k
        + ((n : ℝ) + 1) * dF n k) = dG n (n + 3) - dG n 0 := by
      rw [sum_congr rfl fun k _ => dF_step n k]
      exact Finset.sum_range_sub (fun k => dG n k) (n + 3)
    have h1 : dG n (n + 3) = 0 := by
      unfold dG; rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
    have h2 : dG n 0 = 0 := by unfold dG; simp
    rw [h1, h2, sub_zero, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, ← mul_sum] at hsum
    linarith
  exact_mod_cast hR

/-! ### CO-493 as printed in the book: the Apéry sum `∑_k C(n,k)^2 C(n+k,k)^2` -/

/-- Numerator of the Zeilberger certificate of the Apéry sum. -/
def aP (n k : ℝ) : ℝ :=
  -96 - 36 * k + 24 * k ^ 2 - 208 * n - 24 * n * k + 16 * n * k ^ 2 - 144 * n ^ 2 - 32 * n ^ 3

lemma apery_alg (n k u2 u1 u v2 v1 v w z : ℝ) (hn : 0 ≤ n) (hk : 0 ≤ k)
    (hA : u1 * (n + 2) = u2 * (n + 2 - k)) (hB : u * (n + 1) = u1 * (n + 1 - k))
    (hC : v1 * (n + k + 2) = v2 * (n + 2)) (hD : v * (n + k + 1) = v1 * (n + 1))
    (hE : w * (k + 1) = u2 * (n + 2 - k)) (hF : z * (k + 1) = v1 * (n + 1)) :
    (n + 2) ^ 3 * (u2 * v2) ^ 2 - (2 * n + 3) * (17 * n ^ 2 + 51 * n + 39) * (u1 * v1) ^ 2
        + (n + 1) ^ 3 * (u * v) ^ 2
      = (k + 1) ^ 4 * aP n (k + 1) * (w * z) ^ 2 / ((n + 1) ^ 2 * (n + 2) ^ 2)
        - k ^ 4 * aP n k * (u2 * v) ^ 2 / ((n + 1) ^ 2 * (n + 2) ^ 2) := by
  have h1 : 0 < n + 1 := by linarith
  have h2 : 0 < n + 2 := by linarith
  have h3 : 0 < n + k + 1 := by linarith
  have h4 : 0 < n + k + 2 := by linarith
  have h5 : 0 < k + 1 := by linarith
  have eu1 : u1 = u2 * (n + 2 - k) / (n + 2) := by field_simp; linarith
  have eu : u = u1 * (n + 1 - k) / (n + 1) := by field_simp; linarith
  have ev1 : v1 = v2 * (n + 2) / (n + k + 2) := by field_simp; linarith
  have ev : v = v1 * (n + 1) / (n + k + 1) := by field_simp; linarith
  have ew : w = u2 * (n + 2 - k) / (k + 1) := by field_simp; linarith
  have ez : z = v1 * (n + 1) / (k + 1) := by field_simp; linarith
  rw [ew, ez, eu, ev, eu1, ev1]
  unfold aP
  field_simp
  ring

/-- Summand `(C(n,k) C(n+k,k))^2` (real-valued). -/
noncomputable def aF (n k : ℕ) : ℝ := ((n.choose k : ℝ) * ((n + k).choose k : ℝ)) ^ 2

/-- Telescoping term of the certificate. -/
noncomputable def aG (n k : ℕ) : ℝ :=
  (k : ℝ) ^ 4 * aP n k * (((n + 2).choose k : ℝ) * ((n + k).choose k : ℝ)) ^ 2
    / (((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2) ^ 2)

lemma aF_step (n k : ℕ) :
    ((n : ℝ) + 2) ^ 3 * aF (n + 2) k - (2 * n + 3) * (17 * n ^ 2 + 51 * n + 39) * aF (n + 1) k
        + ((n : ℝ) + 1) ^ 3 * aF n k = aG n (k + 1) - aG n k := by
  have hA := choose_mul_succ_real (n + 1) k
  have hB := choose_mul_succ_real n k
  have hC := choose_mul_succ_real (n + 1 + k) k
  have hD := choose_mul_succ_real (n + k) k
  have hE := choose_rel (n + 2) k
  have hF := choose_rel (n + 1 + k) k
  have e1 : n + 1 + k + 1 = n + 2 + k := by ring
  have e2 : n + k + 1 = n + 1 + k := by ring
  rw [e1] at hC
  rw [e2] at hD
  push_cast at hA hB hC hD hE hF
  have key := apery_alg n k ((n + 2).choose k) ((n + 1).choose k) (n.choose k)
    ((n + 2 + k).choose k) ((n + 1 + k).choose k) ((n + k).choose k)
    ((n + 2).choose (k + 1)) ((n + 1 + k).choose (k + 1)) (by positivity) (by positivity)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  unfold aF aG
  have e3 : n + (k + 1) = n + 1 + k := by ring
  rw [e3]
  push_cast
  linear_combination key

/-- The Apéry sum `∑_k C(n,k)^2 C(n+k,k)^2`. -/
def aperySum (n : ℕ) : ℕ := ∑ k ∈ range (n + 1), (n.choose k * (n + k).choose k) ^ 2

lemma aperySum_real (n M : ℕ) (hM : n + 1 ≤ M) :
    (aperySum n : ℝ) = ∑ k ∈ range M, aF n k := by
  unfold aperySum aF
  push_cast
  refine sum_subset (Finset.range_mono hM) ?_
  intro k _ hk
  have : n.choose k = 0 := Nat.choose_eq_zero_of_lt (by simpa using hk)
  simp [this]

/-- CO-493 (recurrence part, as printed in the book). The Apéry numbers
`y(n) = ∑_k C(n,k)^2 C(n+k,k)^2` satisfy
`(n+2)^3 y(n+2) - (2n+3)(17n^2+51n+39) y(n+1) + (n+1)^3 y(n) = 0` (stated without subtraction).
The book's printed formula for `y(n)` lost its exponents in the available text; the recurrence
only holds for the squared version, and this is the one proved. The claim that the recurrence
has no hypergeometric solution is not formalized. -/
@[kb "petkovsekwilfzeilberger1996" "Example 8.4.2, p. 164"]
theorem aperySum_rec (n : ℕ) :
    (n + 2) ^ 3 * aperySum (n + 2) + (n + 1) ^ 3 * aperySum n
      = (2 * n + 3) * (17 * n ^ 2 + 51 * n + 39) * aperySum (n + 1) := by
  have hR : ((n : ℝ) + 2) ^ 3 * (aperySum (n + 2) : ℝ) + ((n : ℝ) + 1) ^ 3 * (aperySum n : ℝ)
      = (2 * (n : ℝ) + 3) * (17 * (n : ℝ) ^ 2 + 51 * n + 39) * (aperySum (n + 1) : ℝ) := by
    rw [aperySum_real (n + 2) (n + 3) (by omega), aperySum_real n (n + 3) (by omega),
      aperySum_real (n + 1) (n + 3) (by omega)]
    have hsum : ∑ k ∈ range (n + 3), (((n : ℝ) + 2) ^ 3 * aF (n + 2) k
        - (2 * n + 3) * (17 * n ^ 2 + 51 * n + 39) * aF (n + 1) k
        + ((n : ℝ) + 1) ^ 3 * aF n k) = aG n (n + 3) - aG n 0 := by
      rw [sum_congr rfl fun k _ => aF_step n k]
      exact Finset.sum_range_sub (fun k => aG n k) (n + 3)
    have h1 : aG n (n + 3) = 0 := by
      unfold aG; rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
    have h2 : aG n 0 = 0 := by unfold aG; simp
    rw [h1, h2, sub_zero, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, ← mul_sum]
      at hsum
    linarith
  exact_mod_cast hR

end UndergradKB.Combinatorics.AeqB.Companions
