import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.PSeries
import UndergradKB.Combinatorics.AeqB.GaussSum
import UndergradKB.Common.Attr

/-!
# The companion of the full Saalschütz identity (Example 7.3.3)

We work with the WZ pair of Saalschütz's identity for real parameters, normalised so that
`F(n, k) = q_n * t_k * D(n, k)` where `t_k = gaussTerm a b c k` is the `k`-th term of
`2F1(a, b; c; 1)`, `q_n = 2F1(a, b; c + n; 1) -> 1` and `D(n, k) = ∏_{i<k} (n-i)/(n+s-1-i)`,
`s = c - a - b`.  Summing the WZ equation over `n ≥ 0` (the companion argument) gives the identity.
-/

set_option linter.unusedSectionVars false

namespace UndergradKB.Combinatorics.AeqB
open Finset Filter Topology

/-- `q_n = 2F1(a, b; c + n; 1)`. -/
noncomputable def sQ (a b c : ℝ) (n : ℕ) : ℝ := gaussSum a b (c + n)

/-- `D(n, j) = ∏_{i<j} (n - i) / (n + s - 1 - i)`. -/
noncomputable def sD (s : ℝ) (n j : ℕ) : ℝ :=
  (∏ i ∈ range j, ((n : ℝ) - i)) / ∏ i ∈ range j, ((n : ℝ) + s - 1 - i)

/-- The normalised Saalschütz summand `F(n, k) = q_n t_k D(n, k)`. -/
noncomputable def sF (a b c : ℝ) (n k : ℕ) : ℝ :=
  sQ a b c n * gaussTerm a b c k * sD (c - a - b) n k

/-- The WZ mate `G(n, k)`, with the pole of the certificate cancelled. -/
noncomputable def sG (a b c : ℝ) (n : ℕ) : ℕ → ℝ
  | 0 => 0
  | j + 1 => -((a + j) * (b + j)) * gaussTerm a b c j * sQ a b c n * sD (c - a - b) n j /
      ((c + n - b) * (c - a + n))

theorem sD_zero (s : ℝ) (n : ℕ) : sD s n 0 = 1 := by simp [sD]

theorem sD_succ (s : ℝ) (n j : ℕ) :
    sD s n (j + 1) = sD s n j * (((n : ℝ) - j) / ((n : ℝ) + s - 1 - j)) := by
  unfold sD
  rw [prod_range_succ, prod_range_succ, div_mul_div_comm]

theorem sD_shift (s : ℝ) (n j : ℕ) :
    sD s (n + 1) (j + 1) = sD s n j * (((n : ℝ) + 1) / ((n : ℝ) + s)) := by
  unfold sD
  rw [prod_range_succ', prod_range_succ', div_mul_div_comm]
  have h1 : ∏ i ∈ range j, (((n + 1 : ℕ) : ℝ) - ((i + 1 : ℕ) : ℝ)) = ∏ i ∈ range j, ((n : ℝ) - i) :=
    prod_congr rfl fun i _ => by push_cast; ring
  have h2 : ∏ i ∈ range j, (((n + 1 : ℕ) : ℝ) + s - 1 - ((i + 1 : ℕ) : ℝ))
      = ∏ i ∈ range j, ((n : ℝ) + s - 1 - i) :=
    prod_congr rfl fun i _ => by push_cast; ring
  rw [h1, h2]
  push_cast
  congr 2 <;> ring

theorem sD_lt (s : ℝ) {n j : ℕ} (h : n < j) : sD s n j = 0 := by
  unfold sD
  rw [prod_eq_zero (i := n) (mem_range.2 h) (sub_self _), zero_div]

theorem sD_ratio (s : ℝ) (hs : 0 < s) (j m : ℕ) :
    sD s (j + m + 1) j * (((m : ℝ) + 1) * (s + j + m)) =
      sD s (j + m) j * (((j : ℝ) + m + 1) * (s + m)) := by
  induction j generalizing m with
  | zero => simp [sD_zero]
  | succ j ih =>
    have h1 := ih m
    have e1 : sD s (j + 1 + m + 1) (j + 1) = sD s (j + m + 1) j *
        ((((j + m + 1 : ℕ) : ℝ) + 1) / (((j + m + 1 : ℕ) : ℝ) + s)) := by
      rw [show j + 1 + m + 1 = (j + m + 1) + 1 by ring]; exact sD_shift s _ _
    have e2 : sD s (j + 1 + m) (j + 1) = sD s (j + m) j *
        ((((j + m : ℕ) : ℝ) + 1) / (((j + m : ℕ) : ℝ) + s)) := by
      rw [show j + 1 + m = (j + m) + 1 by ring]; exact sD_shift s _ _
    rw [e1, e2]
    push_cast at *
    have p1 : (j : ℝ) + m + 1 + s ≠ 0 := by positivity
    have p2 : (j : ℝ) + m + s ≠ 0 := by positivity
    field_simp
    linear_combination ((j : ℝ) + m + 2) * ((j : ℝ) + m + 1 + s) * h1


theorem sQ_succ (a b c : ℝ) (hs : 0 < c - a - b) (hc : ∀ k : ℕ, c + k ≠ 0) (n : ℕ) :
    sQ a b c (n + 1) * (((n : ℝ) + c - a) * ((n : ℝ) + c - b)) =
      sQ a b c n * (((n : ℝ) + (c - a - b)) * ((n : ℝ) + c)) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hc' : ∀ k : ℕ, (c + n) + k ≠ 0 := fun k => by
    have := hc (n + k); push_cast at this; rwa [← add_assoc] at this
  have h := gaussSum_contiguous a b (c + n) (by linarith) hc'
  have e : gaussSum a b (c + ((n + 1 : ℕ) : ℝ)) = gaussSum a b (c + n + 1) := by
    congr 1; push_cast; ring
  unfold sQ
  rw [e]
  linear_combination (-1 : ℝ) * h

theorem sWZ_zero (a b c : ℝ) (hs : 0 < c - a - b) (hc : ∀ k : ℕ, c + k ≠ 0)
    (hca : ∀ k : ℕ, (c - a) + k ≠ 0) (hcb : ∀ k : ℕ, (c - b) + k ≠ 0) (n : ℕ) :
    sF a b c (n + 1) 0 - sF a b c n 0 = sG a b c n 1 := by
  have h1 : (c + n - b) ≠ 0 := by
    intro h; apply hcb n; linarith
  have h2 : (c - a + n) ≠ 0 := by
    intro h; apply hca n; linarith
  have h3 : ((n : ℝ) + c - a) ≠ 0 := by intro h; apply h2; linarith
  have h4 : ((n : ℝ) + c - b) ≠ 0 := by intro h; apply h1; linarith
  have hQ := sQ_succ a b c hs hc n
  have hQ' : sQ a b c (n + 1) = sQ a b c n * (((n : ℝ) + (c - a - b)) * ((n : ℝ) + c)) /
      (((n : ℝ) + c - a) * ((n : ℝ) + c - b)) := by
    rw [eq_div_iff (mul_ne_zero h3 h4)]; exact hQ
  simp only [sF, sG, sD_zero, gaussTerm, hQ']
  push_cast
  field_simp
  ring

set_option maxRecDepth 100000 in
theorem sWZ_succ (a b c : ℝ) (hs : 0 < c - a - b) (hc : ∀ k : ℕ, c + k ≠ 0)
    (hca : ∀ k : ℕ, (c - a) + k ≠ 0) (hcb : ∀ k : ℕ, (c - b) + k ≠ 0) (j n : ℕ) :
    sF a b c (n + 1) (j + 1) - sF a b c n (j + 1) =
      sG a b c n ((j + 1) + 1) - sG a b c n (j + 1) := by
  have h1 : (c + n - b) ≠ 0 := by
    intro h; apply hcb n; linarith
  have h2 : (c - a + n) ≠ 0 := by
    intro h; apply hca n; linarith
  have h3 : ((n : ℝ) + c - a) ≠ 0 := by intro h; apply h2; linarith
  have h4 : ((n : ℝ) + c - b) ≠ 0 := by intro h; apply h1; linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h5 : ((n : ℝ) + (c - a - b)) ≠ 0 := by intro h; linarith
  have h6 : c + (j : ℝ) ≠ 0 := hc j
  have h8 : (n : ℝ) + c ≠ 0 := by rw [add_comm]; exact hc n
  have h9 : (j : ℝ) + c ≠ 0 := by rw [add_comm]; exact hc j
  have h7 : (j : ℝ) + 1 ≠ 0 := by positivity
  have hQ := sQ_succ a b c hs hc n
  have hQ' : sQ a b c (n + 1) = sQ a b c n * (((n : ℝ) + (c - a - b)) * ((n : ℝ) + c)) /
      (((n : ℝ) + c - a) * ((n : ℝ) + c - b)) := by
    rw [eq_div_iff (mul_ne_zero h3 h4)]; exact hQ
  simp only [sF, sG]
  rw [sD_shift]
  simp only [gaussTerm_succ a b c j, sD_succ, hQ']
  by_cases hnj : n < j
  · have hD := sD_lt (c - a - b) hnj
    simp [hD]
  · push Not at hnj
    by_cases h0 : (n : ℝ) + (c - a - b) - 1 - j = 0
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hnj
      have hm : m = 0 := by
        have : (m : ℝ) < 1 := by push_cast at h0; linarith
        exact Nat.lt_one_iff.mp (by exact_mod_cast this)
      subst hm
      simp only [add_zero] at *
      rw [h0]
      simp only [div_zero, mul_zero]
      field_simp
      ring
    · push_cast
      field_simp
      ring


/-- Both WZ equations in one statement. -/
theorem sWZ (a b c : ℝ) (hs : 0 < c - a - b) (hc : ∀ k : ℕ, c + k ≠ 0)
    (hca : ∀ k : ℕ, (c - a) + k ≠ 0) (hcb : ∀ k : ℕ, (c - b) + k ≠ 0) (k n : ℕ) :
    sF a b c (n + 1) k - sF a b c n k = sG a b c n (k + 1) - sG a b c n k := by
  cases k with
  | zero => simpa only [sG, sub_zero] using sWZ_zero a b c hs hc hca hcb n
  | succ j => exact sWZ_succ a b c hs hc hca hcb j n

/-! ### Limits -/

theorem sD_tendsto_one (s : ℝ) (j : ℕ) : Tendsto (fun N : ℕ => sD s N j) atTop (𝓝 1) := by
  induction j with
  | zero => simp [sD_zero]
  | succ j ih =>
    have hr : Tendsto (fun N : ℕ => ((N : ℝ) - j) / ((N : ℝ) + s - 1 - j)) atTop (𝓝 1) := by
      rw [← tendsto_add_atTop_iff_nat j]
      have := tendsto_natCast_div_add_atTop (s - 1)
      refine this.congr fun N => ?_
      push_cast
      congr 1 <;> ring
    simpa [sD_succ] using ih.mul hr

theorem sF_tendsto (a b c : ℝ) (hs : 0 < c - a - b) (k : ℕ) :
    Tendsto (fun N : ℕ => sF a b c N k) atTop (𝓝 (gaussTerm a b c k)) := by
  have h1 : Tendsto (fun N : ℕ => sQ a b c N) atTop (𝓝 1) := gaussSum_tendsto_one a b c hs
  have := (h1.mul_const (gaussTerm a b c k)).mul (sD_tendsto_one (c - a - b) k)
  simpa [sF] using this

theorem sF_zero_left (a b c : ℝ) (k : ℕ) :
    sF a b c 0 k = if k = 0 then gaussSum a b c else 0 := by
  cases k with
  | zero => simp [sF, sQ, sD_zero, gaussTerm]
  | succ k => simp [sF, sD_lt (c - a - b) (Nat.succ_pos k)]

theorem sG_summable (a b c : ℝ) (hs : 0 < c - a - b) (k : ℕ) :
    Summable (fun n : ℕ => sG a b c n k) := by
  cases k with
  | zero => simp [sG]
  | succ j =>
    set K : ℝ := -((a + j) * (b + j)) * gaussTerm a b c j with hK
    have hlim : Tendsto (fun n : ℕ => sQ a b c n * sD (c - a - b) n j) atTop (𝓝 1) := by
      have h : Tendsto (fun n : ℕ => sQ a b c n) atTop (𝓝 1) := gaussSum_tendsto_one a b c hs
      simpa using h.mul (sD_tendsto_one (c - a - b) j)
    have hev1 : ∀ᶠ n : ℕ in atTop, |sQ a b c n * sD (c - a - b) n j| < 2 := by
      have := hlim.abs
      simp only [abs_one] at this
      exact this.eventually (gt_mem_nhds (by norm_num))
    have hev2 := eventually_ge_atTop (⌈2 * (|c - b| + |c - a|)⌉₊ + 1)
    refine Summable.of_norm_bounded_eventually_nat
      (g := fun n : ℕ => (8 * |K|) * (1 / (n : ℝ) ^ 2))
      ((Real.summable_one_div_nat_pow.2 (by norm_num)).mul_left _) ?_
    filter_upwards [hev1, hev2] with n h1 h2
    have hn : (2 * (|c - b| + |c - a|) : ℝ) + 1 ≤ n := by
      have := Nat.le_ceil (2 * (|c - b| + |c - a|))
      have h3 : ((⌈2 * (|c - b| + |c - a|)⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast h2
      push_cast at h3
      linarith
    have hb1 : (n : ℝ) / 2 ≤ c + n - b := by
      have := neg_abs_le (c - b); have := abs_nonneg (c - a); linarith
    have hb2 : (n : ℝ) / 2 ≤ c - a + n := by
      have := neg_abs_le (c - a); have := abs_nonneg (c - b); linarith
    have hnpos : (0 : ℝ) < n := by
      have := abs_nonneg (c - b); have := abs_nonneg (c - a); linarith
    have hden : (n : ℝ) ^ 2 / 4 ≤ (c + n - b) * (c - a + n) := by nlinarith
    have hdpos : 0 < (c + n - b) * (c - a + n) := lt_of_lt_of_le (by positivity) hden
    have e : sG a b c n (j + 1) = K * (sQ a b c n * sD (c - a - b) n j) /
        ((c + n - b) * (c - a + n)) := by
      simp only [sG, hK]; ring
    rw [e, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hdpos, div_le_iff₀ hdpos]
    have hM : |K| * |sQ a b c n * sD (c - a - b) n j| ≤ |K| * 2 :=
      mul_le_mul_of_nonneg_left h1.le (abs_nonneg _)
    have h8 : 8 * |K| * (1 / (n : ℝ) ^ 2) * ((c + n - b) * (c - a + n)) ≥
        8 * |K| * (1 / (n : ℝ) ^ 2) * ((n : ℝ) ^ 2 / 4) :=
      mul_le_mul_of_nonneg_left hden (by positivity)
    have h9 : 8 * |K| * (1 / (n : ℝ) ^ 2) * ((n : ℝ) ^ 2 / 4) = 2 * |K| := by
      field_simp; ring
    linarith


/-! ### The companion argument: sum the WZ equation over `n` -/

/-- `S_k = ∑_{n ≥ 0} G(n, k)`. -/
noncomputable def sS (a b c : ℝ) (k : ℕ) : ℝ := ∑' n : ℕ, sG a b c n k

theorem sS_zero (a b c : ℝ) : sS a b c 0 = 0 := by simp [sS, sG]

theorem sS_succ (a b c : ℝ) (hs : 0 < c - a - b) (hc : ∀ k : ℕ, c + k ≠ 0)
    (hca : ∀ k : ℕ, (c - a) + k ≠ 0) (hcb : ∀ k : ℕ, (c - b) + k ≠ 0) (k : ℕ) :
    sS a b c (k + 1) - sS a b c k = gaussTerm a b c k - (if k = 0 then gaussSum a b c else 0) := by
  have hS : HasSum (fun n : ℕ => sG a b c n (k + 1) - sG a b c n k)
      (sS a b c (k + 1) - sS a b c k) :=
    (sG_summable a b c hs (k + 1)).hasSum.sub (sG_summable a b c hs k).hasSum
  have t1 := hS.tendsto_sum_nat
  have e : ∀ N : ℕ, ∑ n ∈ range N, (sG a b c n (k + 1) - sG a b c n k)
      = sF a b c N k - sF a b c 0 k := by
    intro N
    rw [← Finset.sum_range_sub (fun i : ℕ => sF a b c i k) N]
    exact sum_congr rfl fun i _ => (sWZ a b c hs hc hca hcb k i).symm
  simp_rw [e, sF_zero_left] at t1
  exact tendsto_nhds_unique t1 ((sF_tendsto a b c hs k).sub tendsto_const_nhds)

theorem sS_eq (a b c : ℝ) (hs : 0 < c - a - b) (hc : ∀ k : ℕ, c + k ≠ 0)
    (hca : ∀ k : ℕ, (c - a) + k ≠ 0) (hcb : ∀ k : ℕ, (c - b) + k ≠ 0) (k : ℕ) (hk : 1 ≤ k) :
    sS a b c k = ∑ i ∈ range k, gaussTerm a b c i - gaussSum a b c := by
  induction k, hk using Nat.le_induction with
  | base =>
    have := sS_succ a b c hs hc hca hcb 0
    rw [sS_zero] at this
    simp [gaussTerm] at this ⊢
    linarith
  | succ k hk ih =>
    have := sS_succ a b c hs hc hca hcb k
    simp only [show k ≠ 0 by omega, ite_false, sub_zero] at this
    rw [sum_range_succ]
    linarith


/-! ### Identification of `∑_n G(n, k)` with the `3F2` -/

/-- The term ratio of `n ↦ G(n, j+1)` for `n ≥ j`. -/
theorem sG_ratio (a b c : ℝ) (hs : 0 < c - a - b) (hc : ∀ k : ℕ, c + k ≠ 0)
    (hca : ∀ k : ℕ, (c - a) + k ≠ 0) (hcb : ∀ k : ℕ, (c - b) + k ≠ 0) (j m : ℕ) :
    sG a b c (j + m + 1) (j + 1) = sG a b c (j + m) (j + 1) *
      ((((j : ℝ) + 1 + m) * ((c - a - b) + m) * (c + j + m)) /
        ((c - b + ((j : ℝ) + 1) + m) * (c - a + ((j : ℝ) + 1) + m) * ((m : ℝ) + 1))) := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have h1 : (c + ((j + m : ℕ) : ℝ) - b) ≠ 0 := by
    intro h; apply hcb (j + m); push_cast at h ⊢; linarith
  have h2 : (c - a + ((j + m : ℕ) : ℝ)) ≠ 0 := by
    intro h; apply hca (j + m); push_cast at h ⊢; linarith
  have h1' : (c + ((j + m + 1 : ℕ) : ℝ) - b) ≠ 0 := by
    intro h; apply hcb (j + m + 1); push_cast; push_cast at h; linarith
  have h2' : (c - a + ((j + m + 1 : ℕ) : ℝ)) ≠ 0 := by
    intro h; apply hca (j + m + 1); push_cast; push_cast at h; linarith
  have h3 : (((j + m : ℕ) : ℝ) + c - a) ≠ 0 := by intro h; apply h2; linarith
  have h4 : (((j + m : ℕ) : ℝ) + c - b) ≠ 0 := by intro h; apply h1; linarith
  have h5 : (((j + m : ℕ) : ℝ) + (c - a - b)) ≠ 0 := by push_cast; intro h; linarith
  have h6 : (c - b + ((j : ℝ) + 1) + m) ≠ 0 := by
    intro h; apply hcb (j + 1 + m); push_cast; linarith
  have h7 : (c - a + ((j : ℝ) + 1) + m) ≠ 0 := by
    intro h; apply hca (j + 1 + m); push_cast; linarith
  have h8 : (c - a - b) + (m : ℝ) ≠ 0 := by intro h; linarith
  have h9 : (m : ℝ) + 1 ≠ 0 := by positivity
  have h10 : (c - a - b) + (j : ℝ) + m ≠ 0 := by intro h; linarith
  have hQ := sQ_succ a b c hs hc (j + m)
  have hQ' : sQ a b c (j + m + 1) = sQ a b c (j + m) *
      ((((j + m : ℕ) : ℝ) + (c - a - b)) * (((j + m : ℕ) : ℝ) + c)) /
      ((((j + m : ℕ) : ℝ) + c - a) * (((j + m : ℕ) : ℝ) + c - b)) := by
    rw [eq_div_iff (mul_ne_zero h3 h4)]; exact hQ
  have hD := sD_ratio (c - a - b) hs j m
  have hD' : sD (c - a - b) (j + m + 1) j = sD (c - a - b) (j + m) j *
      (((j : ℝ) + m + 1) * ((c - a - b) + m)) / (((m : ℝ) + 1) * ((c - a - b) + j + m)) := by
    rw [eq_div_iff (mul_ne_zero h9 (by intro h; apply h10; linarith))]
    linear_combination hD
  simp only [sG, hQ', hD']
  push_cast
  push_cast at h1 h2 h3 h4 h5 h1' h2'
  field_simp
  ring

theorem sG_pFq (a b c : ℝ) (hs : 0 < c - a - b) (hc : ∀ k : ℕ, c + k ≠ 0)
    (hca : ∀ k : ℕ, (c - a) + k ≠ 0) (hcb : ∀ k : ℕ, (c - b) + k ≠ 0) (j m : ℕ) :
    sG a b c (j + m) (j + 1) = sG a b c j (j + 1) *
      pFqTerm ![((j + 1 : ℕ) : ℝ), c - a - b, c + ((j + 1 : ℕ) : ℝ) - 1]
        ![c - b + ((j + 1 : ℕ) : ℝ), c - a + ((j + 1 : ℕ) : ℝ)] (1 : ℝ) m := by
  have hlow : LowerOK (![c - b + ((j + 1 : ℕ) : ℝ), c - a + ((j + 1 : ℕ) : ℝ)] : Fin 2 → ℝ) := by
    intro i n
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]
      intro h; apply hcb (j + 1 + n); push_cast; push_cast at h; linarith
    · simp only [Fin.mk_one, Matrix.cons_val_one]
      intro h; apply hca (j + 1 + n); push_cast; push_cast at h; linarith
  induction m with
  | zero => simp [pFqTerm_zero]
  | succ m ih =>
    have hp := pFqTerm_succ_mul ![((j + 1 : ℕ) : ℝ), c - a - b, c + ((j + 1 : ℕ) : ℝ) - 1] hlow
      (1 : ℝ) m
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, mul_one] at hp
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have d1 : (m : ℝ) + (c - b + ((j + 1 : ℕ) : ℝ)) ≠ 0 := by
      intro h; apply hcb (j + 1 + m); push_cast; push_cast at h; linarith
    have d2 : (m : ℝ) + (c - a + ((j + 1 : ℕ) : ℝ)) ≠ 0 := by
      intro h; apply hca (j + 1 + m); push_cast; push_cast at h; linarith
    have d3 : (m : ℝ) + 1 ≠ 0 := by positivity
    have hu := eq_div_of_mul_eq (mul_ne_zero (mul_ne_zero d1 d2) d3) hp
    have hr := sG_ratio a b c hs hc hca hcb j m
    rw [show j + (m + 1) = j + m + 1 by ring, hr, ih, hu]
    push_cast
    field_simp
    ring


/-! ### The diagonal value `G(j, j+1)` -/

/-- `P_k = (c-b)_k (c-a)_k / ((a)_k (b)_k)` as a product of ratios. -/
noncomputable def sP (a b c : ℝ) (k : ℕ) : ℝ :=
  ∏ i ∈ range k, ((c - b + i) * (c - a + i) / ((a + i) * (b + i)))

theorem sG_diag_succ (a b c : ℝ) (hs : 0 < c - a - b) (hc : ∀ k : ℕ, c + k ≠ 0)
    (hca : ∀ k : ℕ, (c - a) + k ≠ 0) (hcb : ∀ k : ℕ, (c - b) + k ≠ 0) (j : ℕ) :
    sG a b c (j + 1) (j + 1 + 1) = sG a b c j (j + 1) *
      (((a + ((j : ℝ) + 1)) * (b + ((j : ℝ) + 1))) /
        ((c + ((j : ℝ) + 1) - b) * (c - a + ((j : ℝ) + 1)))) := by
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have h1 : (c + (j : ℝ) - b) ≠ 0 := by intro h; apply hcb j; linarith
  have h2 : (c - a + (j : ℝ)) ≠ 0 := by intro h; apply hca j; linarith
  have h1' : (c + ((j : ℝ) + 1) - b) ≠ 0 := by
    intro h; apply hcb (j + 1); push_cast; linarith
  have h2' : (c - a + ((j : ℝ) + 1)) ≠ 0 := by
    intro h; apply hca (j + 1); push_cast; linarith
  have h3 : ((j : ℝ) + c - a) ≠ 0 := by intro h; apply h2; linarith
  have h4 : ((j : ℝ) + c - b) ≠ 0 := by intro h; apply h1; linarith
  have h5 : ((j : ℝ) + (c - a - b)) ≠ 0 := by intro h; linarith
  have h6 : (j : ℝ) + c ≠ 0 := by rw [add_comm]; exact hc j
  have h7 : (j : ℝ) + 1 ≠ 0 := by positivity
  have hQ := sQ_succ a b c hs hc j
  have hQ' : sQ a b c (j + 1) = sQ a b c j * (((j : ℝ) + (c - a - b)) * ((j : ℝ) + c)) /
      (((j : ℝ) + c - a) * ((j : ℝ) + c - b)) := by
    rw [eq_div_iff (mul_ne_zero h3 h4)]; exact hQ
  have h8 : (c + j ≠ 0) := hc j
  simp only [sG, gaussTerm_succ a b c j, sD_shift, hQ']
  push_cast
  field_simp
  ring

theorem sG_diag (a b c : ℝ) (hs : 0 < c - a - b) (ha : ∀ k : ℕ, a + k ≠ 0) (hb : ∀ k : ℕ, b + k ≠ 0)
    (hc : ∀ k : ℕ, c + k ≠ 0)
    (hca : ∀ k : ℕ, (c - a) + k ≠ 0) (hcb : ∀ k : ℕ, (c - b) + k ≠ 0) (j : ℕ) :
    sG a b c j (j + 1) * sP a b c (j + 1) = -gaussSum a b c := by
  induction j with
  | zero =>
    have h1 : c - b ≠ 0 := by simpa using hcb 0
    have h2 : c - a ≠ 0 := by simpa using hca 0
    have h3 : a ≠ 0 := by simpa using ha 0
    have h4 : b ≠ 0 := by simpa using hb 0
    simp only [sG, sP, sQ, sD_zero, gaussTerm]
    rw [prod_range_one]
    simp only [Nat.cast_zero, add_zero]
    field_simp
  | succ j ih =>
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have h1 : (c + ((j : ℝ) + 1) - b) ≠ 0 := by
      intro h; apply hcb (j + 1); push_cast; linarith
    have h2 : (c - a + ((j : ℝ) + 1)) ≠ 0 := by
      intro h; apply hca (j + 1); push_cast; linarith
    have h3 : a + ((j : ℝ) + 1) ≠ 0 := by simpa using ha (j + 1)
    have h4 : b + ((j : ℝ) + 1) ≠ 0 := by simpa using hb (j + 1)
    rw [sG_diag_succ a b c hs hc hca hcb j]
    have : sP a b c (j + 1 + 1) = sP a b c (j + 1) *
        ((c - b + ((j : ℝ) + 1)) * (c - a + ((j : ℝ) + 1)) / ((a + ((j : ℝ) + 1)) * (b + ((j : ℝ) + 1)))) := by
      rw [sP, prod_range_succ]; push_cast; rfl
    rw [this]
    calc _ = (sG a b c j (j + 1) * sP a b c (j + 1)) * ((a + ((j : ℝ) + 1)) * (b + ((j : ℝ) + 1)) /
          ((c + ((j : ℝ) + 1) - b) * (c - a + ((j : ℝ) + 1))) *
          ((c - b + ((j : ℝ) + 1)) * (c - a + ((j : ℝ) + 1)) /
            ((a + ((j : ℝ) + 1)) * (b + ((j : ℝ) + 1))))) := by ring
      _ = _ := by
        rw [ih]
        have : c + ((j : ℝ) + 1) - b = c - b + ((j : ℝ) + 1) := by ring
        rw [this] at h1 ⊢
        field_simp

theorem sP_eq_asc (a b c : ℝ) (k : ℕ) :
    sP a b c k = (ascPochhammer ℝ k).eval (c - b) * (ascPochhammer ℝ k).eval (c - a) /
      ((ascPochhammer ℝ k).eval a * (ascPochhammer ℝ k).eval b) := by
  simp only [sP, asc_eval_eq_prod]
  rw [prod_div_distrib, prod_mul_distrib, prod_mul_distrib]

/-- CO-457. The companion of the full Saalschütz identity (Example 7.3.3, stated as
Exercise 7.3.3): for real `a b c` with `c > a + b` (and no pole: none of `a, b, c, c-a, c-b` is a
nonpositive integer) and every integer `k > 0`, the nonterminating series
`3F2(k, c-a-b, c+k-1; c-b+k, c-a+k; 1)` converges and equals
`(c-b)_k (c-a)_k / ((a)_k (b)_k) * (1 - Γ(c-a) Γ(c-b) / (Γ(c) Γ(c-a-b)) * ∑_{j<k} (a)_j (b)_j / (j! (c)_j))`.
(The book writes the constant as the quotient of rising factorials `(c-a-b)_a / (c-a)_a`, which
is the same quotient of Gamma values.)  The sum on the right is a partial sum of Gauss's
`2F1(a, b; c; 1)` series. -/
@[kb "petkovsekwilfzeilberger1996" "Exercise 7.3.3, p. 140"]
theorem saalschutz_companion (a b c : ℝ) (hs : 0 < c - a - b)
    (ha : ∀ n : ℕ, a ≠ -(n : ℝ)) (hb : ∀ n : ℕ, b ≠ -(n : ℝ)) (hc : ∀ n : ℕ, c ≠ -(n : ℝ))
    (hca : ∀ n : ℕ, c - a ≠ -(n : ℝ)) (hcb : ∀ n : ℕ, c - b ≠ -(n : ℝ)) (k : ℕ) (hk : 0 < k) :
    Summable (fun m : ℕ => pFqTerm ![(k : ℝ), c - a - b, c + (k : ℝ) - 1]
        ![c - b + (k : ℝ), c - a + (k : ℝ)] (1 : ℝ) m) ∧
    ∑' m : ℕ, pFqTerm ![(k : ℝ), c - a - b, c + (k : ℝ) - 1]
        ![c - b + (k : ℝ), c - a + (k : ℝ)] (1 : ℝ) m =
      ((ascPochhammer ℝ k).eval (c - b) * (ascPochhammer ℝ k).eval (c - a) /
          ((ascPochhammer ℝ k).eval a * (ascPochhammer ℝ k).eval b)) *
        (1 - Real.Gamma (c - a) * Real.Gamma (c - b) / (Real.Gamma c * Real.Gamma (c - a - b)) *
          ∑ i ∈ range k, pFqTerm ![a, b] ![c] (1 : ℝ) i) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have ha' : ∀ n : ℕ, a + n ≠ 0 := fun n h => ha n (by linarith)
  have hb' : ∀ n : ℕ, b + n ≠ 0 := fun n h => hb n (by linarith)
  have hc' : ∀ n : ℕ, c + n ≠ 0 := fun n h => hc n (by linarith)
  have hca' : ∀ n : ℕ, (c - a) + n ≠ 0 := fun n h => hca n (by linarith)
  have hcb' : ∀ n : ℕ, (c - b) + n ≠ 0 := fun n h => hcb n (by linarith)
  have hsn : ∀ n : ℕ, c - a - b ≠ -(n : ℝ) := fun n h => by
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hG0 := gaussSum_eq_gamma a b c hs hc
  have hG0ne : gaussSum a b c ≠ 0 := by
    rw [hG0]
    exact div_ne_zero (mul_ne_zero (Real.Gamma_ne_zero hc) (Real.Gamma_ne_zero hsn))
      (mul_ne_zero (Real.Gamma_ne_zero hca) (Real.Gamma_ne_zero hcb))
  have hdiag := sG_diag a b c hs ha' hb' hc' hca' hcb' j
  set g := sG a b c j (j + 1) with hgdef
  have hg : g ≠ 0 := by
    intro h; rw [h, zero_mul] at hdiag; exact hG0ne (by linarith)
  have hsumG := sG_summable a b c hs (j + 1)
  have hshift : (∑ i ∈ range j, sG a b c i (j + 1)) + ∑' i : ℕ, sG a b c (i + j) (j + 1)
      = sS a b c (j + 1) := hsumG.sum_add_tsum_nat_add j
  have hzero : ∑ i ∈ range j, sG a b c i (j + 1) = 0 :=
    sum_eq_zero fun i hi => by simp [sG, sD_lt (c - a - b) (mem_range.1 hi)]
  rw [hzero, zero_add] at hshift
  have hu : ∀ m : ℕ, sG a b c (m + j) (j + 1) = g *
      pFqTerm ![((j + 1 : ℕ) : ℝ), c - a - b, c + ((j + 1 : ℕ) : ℝ) - 1]
        ![c - b + ((j + 1 : ℕ) : ℝ), c - a + ((j + 1 : ℕ) : ℝ)] (1 : ℝ) m := fun m => by
    rw [add_comm]; exact sG_pFq a b c hs hc' hca' hcb' j m
  have hsum1 : Summable (fun m : ℕ => sG a b c (m + j) (j + 1)) :=
    (summable_nat_add_iff j).2 hsumG
  have hsumU : Summable (fun m : ℕ => pFqTerm ![((j + 1 : ℕ) : ℝ), c - a - b,
      c + ((j + 1 : ℕ) : ℝ) - 1] ![c - b + ((j + 1 : ℕ) : ℝ), c - a + ((j + 1 : ℕ) : ℝ)]
      (1 : ℝ) m) := by
    refine (hsum1.mul_left g⁻¹).congr fun m => ?_
    rw [hu m, ← mul_assoc, inv_mul_cancel₀ hg, one_mul]
  refine ⟨hsumU, ?_⟩
  have hL : g * ∑' m : ℕ, pFqTerm ![((j + 1 : ℕ) : ℝ), c - a - b, c + ((j + 1 : ℕ) : ℝ) - 1]
      ![c - b + ((j + 1 : ℕ) : ℝ), c - a + ((j + 1 : ℕ) : ℝ)] (1 : ℝ) m
      = sS a b c (j + 1) := by
    rw [← tsum_mul_left, ← hshift]
    exact tsum_congr fun m => (hu m).symm
  rw [sS_eq a b c hs hc' hca' hcb' (j + 1) (by omega)] at hL
  have hE : ∑ i ∈ range (j + 1), pFqTerm ![a, b] ![c] (1 : ℝ) i
      = ∑ i ∈ range (j + 1), gaussTerm a b c i :=
    sum_congr rfl fun i _ => (gaussTerm_eq_pFqTerm a b c hc' i).symm
  rw [hE, ← sP_eq_asc]
  have hR : Real.Gamma (c - a) * Real.Gamma (c - b) / (Real.Gamma c * Real.Gamma (c - a - b))
      = (gaussSum a b c)⁻¹ := by
    rw [hG0, inv_div]
  rw [hR]
  apply mul_left_cancel₀ hg
  have e : g * (sP a b c (j + 1) * (1 - (gaussSum a b c)⁻¹ *
      ∑ i ∈ range (j + 1), gaussTerm a b c i)) =
      (g * sP a b c (j + 1)) * (1 - (gaussSum a b c)⁻¹ * ∑ i ∈ range (j + 1), gaussTerm a b c i) := by
    ring
  rw [e, hdiag, hL]
  field_simp
  ring

end UndergradKB.Combinatorics.AeqB
