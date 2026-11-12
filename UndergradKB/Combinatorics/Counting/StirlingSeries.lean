import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Exponential
import UndergradKB.Combinatorics.Counting.StirlingCorrection
import UndergradKB.Common.Attr

/-!
# Stirling's series through the third correction term (Keller–Trotter, Section 11.3)

We prove that the ratio `n!/(√(2πn)(n/e)^n)` equals
`1 + 1/(12n) + 1/(288 n²) - 139/(51840 n³)` up to an error of size `O(1/n⁴)`, with an explicit
(non-sharp) constant.

The proof compares the stepwise difference of the logarithm of the ratio with the stepwise difference
of `1/(12n) - 1/(360 n³)`; the two agree up to `O(1/n⁶)`.  Telescoping gives
`log ratio = 1/(12n) - 1/(360 n³) + O(1/n⁵)`, and a Taylor expansion of the exponential finishes.
-/

namespace UndergradKB.Combinatorics

open Real Nat

namespace Stirling

/-- The comparison function `1/(12x) - 1/(360 x³)`. -/
noncomputable def gcmp (x : ℝ) : ℝ := 1 / (12 * x) - 1 / (360 * x ^ 3)

/-- Rational-function identity behind the comparison of one step. -/
lemma E_eq (M : ℝ) (hM : 0 < M) :
    1 / (3 * (2 * M + 1) ^ 2) + 1 / (5 * (2 * M + 1) ^ 4) - (gcmp M - gcmp (M + 1)) =
      (1 + 11 * M + 21 * M ^ 2 + 20 * M ^ 3 + 10 * M ^ 4) /
        (360 * M ^ 3 * (M + 1) ^ 3 * (2 * M + 1) ^ 4) := by
  unfold gcmp
  have h1 : M + 1 ≠ 0 := by positivity
  have h2 : 2 * M + 1 ≠ 0 := by positivity
  field_simp
  ring

lemma E_bounds (M : ℝ) (hM : 1 ≤ M) :
    0 ≤ 1 / (3 * (2 * M + 1) ^ 2) + 1 / (5 * (2 * M + 1) ^ 4) - (gcmp M - gcmp (M + 1)) ∧
    1 / (3 * (2 * M + 1) ^ 2) + 1 / (5 * (2 * M + 1) ^ 4) - (gcmp M - gcmp (M + 1)) ≤
      1 / (40 * M ^ 6) := by
  have h0 : 0 < M := by linarith
  rw [E_eq M h0]
  constructor
  · positivity
  · have hN : 1 + 11 * M + 21 * M ^ 2 + 20 * M ^ 3 + 10 * M ^ 4 ≤ 63 * M ^ 4 := by
      have h2 : M ^ 2 ≤ M ^ 4 := pow_le_pow_right₀ hM (by norm_num)
      have h3 : M ^ 3 ≤ M ^ 4 := pow_le_pow_right₀ hM (by norm_num)
      have h1 : M ≤ M ^ 4 := by simpa using pow_le_pow_right₀ hM (show 1 ≤ 4 by norm_num)
      have h4 : 1 ≤ M ^ 4 := one_le_pow₀ hM
      linarith
    have hD : 5760 * M ^ 10 ≤ 360 * M ^ 3 * (M + 1) ^ 3 * (2 * M + 1) ^ 4 := by
      have a1 : M ^ 3 ≤ (M + 1) ^ 3 := pow_le_pow_left₀ h0.le (by linarith) 3
      have a2 : (2 * M) ^ 4 ≤ (2 * M + 1) ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
      have a3 : 0 < M ^ 3 := by positivity
      calc 5760 * M ^ 10 = 360 * M ^ 3 * M ^ 3 * (2 * M) ^ 4 := by ring
        _ ≤ 360 * M ^ 3 * (M + 1) ^ 3 * (2 * M + 1) ^ 4 := by
          gcongr
    calc _ ≤ 63 * M ^ 4 / (5760 * M ^ 10) := by
          apply div_le_div₀ (by positivity) hN (by positivity) hD
      _ ≤ 1 / (40 * M ^ 6) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have : 0 < M ^ 10 := by positivity
          nlinarith [pow_pos h0 10, pow_pos h0 6, pow_pos h0 4]

/-- One step: the stepwise difference of `log (stirlingSeq)` compared with that of `gcmp`. -/
lemma step_bounds (m : ℕ) :
    0 ≤ (Real.log (_root_.Stirling.stirlingSeq (m + 1)) - Real.log (_root_.Stirling.stirlingSeq (m + 2))) -
        (gcmp ((m + 1 : ℕ) : ℝ) - gcmp (((m + 1 : ℕ) : ℝ) + 1)) ∧
    (Real.log (_root_.Stirling.stirlingSeq (m + 1)) - Real.log (_root_.Stirling.stirlingSeq (m + 2))) -
        (gcmp ((m + 1 : ℕ) : ℝ) - gcmp (((m + 1 : ℕ) : ℝ) + 1)) ≤ 1 / (10 * ((m + 1 : ℕ) : ℝ) ^ 6) := by
  set M : ℝ := ((m + 1 : ℕ) : ℝ) with hMdef
  have hM : 1 ≤ M := by rw [hMdef]; exact_mod_cast Nat.succ_pos m
  have h0 : 0 < M := by linarith
  obtain ⟨hE0, hE1⟩ := E_bounds M hM
  have hs := _root_.Stirling.log_stirlingSeq_sdiff_hasSum m
  rw [← hMdef] at hs
  set y : ℝ := (1 / (2 * M + 1)) ^ 2 with hy
  have hy0 : 0 < y := by positivity
  have hy9 : y ≤ 1 / 9 := by
    rw [hy, div_pow, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hy3 : y ^ 3 ≤ 1 / (64 * M ^ 6) := by
    rw [hy, ← pow_mul, div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (2 * M) ^ 6 ≤ (2 * M + 1) ^ 6 := pow_le_pow_left₀ (by linarith) (by linarith) 6
    have e : (2 * M) ^ 6 = 64 * M ^ 6 := by ring
    have h6 : (2 * M + 1) ^ (2 * 3) = (2 * M + 1) ^ 6 := rfl
    rw [h6]
    linarith
  have hya : y / 3 = 1 / (3 * (2 * M + 1) ^ 2) := by rw [hy]; field_simp
  have hyb : y ^ 2 / 5 = 1 / (5 * (2 * M + 1) ^ 4) := by rw [hy]; field_simp
  constructor
  · have hge := sum_le_hasSum (Finset.range 2) (fun k _ => by positivity) hs
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hge
    have e1 : (1 : ℝ) / (2 * ((0 + 1 : ℕ) : ℝ) + 1) * y ^ ((0 + 1 : ℕ)) = y / 3 := by
      norm_num; ring
    have e2 : (1 : ℝ) / (2 * ((1 + 1 : ℕ) : ℝ) + 1) * y ^ ((1 + 1 : ℕ)) = y ^ 2 / 5 := by
      norm_num; ring
    linarith
  · -- the tail starting at index 2 is bounded by a geometric series
    have hs2 := (hasSum_nat_add_iff' 2).2 hs
    have hg : HasSum (fun k : ℕ => y ^ 3 * y ^ k) (y ^ 3 * (1 - y)⁻¹) :=
      (hasSum_geometric_of_lt_one hy0.le (by linarith)).mul_left _
    have hle := hasSum_le (fun k => ?_) hs2 hg
    · have hsum : ∑ i ∈ Finset.range 2, (1 : ℝ) / (2 * ((i + 1 : ℕ) : ℝ) + 1) * y ^ (i + 1) =
          y / 3 + y ^ 2 / 5 := by
        simp only [Finset.sum_range_succ, Finset.sum_range_zero]
        norm_num
        ring
      rw [hsum] at hle
      have hgeo : y ^ 3 * (1 - y)⁻¹ ≤ 9 / 8 * y ^ 3 := by
        have : (1 - y)⁻¹ ≤ 9 / 8 := by
          rw [inv_le_comm₀ (by linarith) (by norm_num)]
          linarith
        have h3 : 0 < y ^ 3 := by positivity
        nlinarith
      have h64 : 9 / 8 * y ^ 3 ≤ 9 / 8 * (1 / (64 * M ^ 6)) := by linarith
      have hfin : 1 / (3 * (2 * M + 1) ^ 2) + 1 / (5 * (2 * M + 1) ^ 4) - (gcmp M - gcmp (M + 1)) ≤
          1 / (40 * M ^ 6) := hE1
      have hM6 : 0 < M ^ 6 := by positivity
      have hsm : 9 / 8 * (1 / (64 * M ^ 6)) + 1 / (40 * M ^ 6) ≤ 1 / (10 * M ^ 6) := by
        rw [show (9 : ℝ) / 8 * (1 / (64 * M ^ 6)) + 1 / (40 * M ^ 6) =
          (9 / 512 + 1 / 40) * (1 / M ^ 6) by ring, show 1 / (10 * M ^ 6) = (1 / 10) * (1 / M ^ 6)
          by ring]
        have : 0 < 1 / M ^ 6 := by positivity
        nlinarith
      linarith
    · have hk : (1 : ℝ) / (2 * ((k + 2 + 1 : ℕ) : ℝ) + 1) * y ^ (k + 2 + 1) ≤ y ^ 3 * y ^ k := by
        have : (1 : ℝ) / (2 * ((k + 2 + 1 : ℕ) : ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]
          push_cast
          have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          linarith
        calc _ ≤ 1 * y ^ (k + 2 + 1) := by gcongr
          _ = y ^ 3 * y ^ k := by ring
      exact hk

lemma tendsto_inv_pow (c : ℝ) (hc : 0 < c) (j : ℕ) (hj : 0 < j) :
    Filter.Tendsto (fun k : ℕ => 1 / (c * ((k + 1 : ℕ) : ℝ) ^ j)) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun k : ℕ => c * ((k + 1 : ℕ) : ℝ) ^ j) Filter.atTop Filter.atTop :=
    ((Filter.tendsto_pow_atTop hj.ne').comp
      (tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1))).const_mul_atTop hc
  exact h1.inv_tendsto_atTop.congr fun k => (one_div _).symm

lemma tendsto_gcmp :
    Filter.Tendsto (fun k : ℕ => gcmp ((k + 1 : ℕ) : ℝ)) Filter.atTop (nhds 0) := by
  have h := (tendsto_inv_pow 12 (by norm_num) 1 (by norm_num)).sub
    (tendsto_inv_pow 360 (by norm_num) 3 (by norm_num))
  simp only [sub_zero, pow_one] at h
  exact h

lemma phi_ineq (M : ℝ) (hM : 1 ≤ M) :
    1 / (10 * M ^ 6) ≤ 3 / 4 * (1 / M ^ 5 - 1 / (M + 1) ^ 5) := by
  have h0 : 0 < M := by linarith
  have h1 : 0 < (M + 1) ^ 5 := by positivity
  have a : (M + 1) ^ 5 ≤ 32 * M ^ 5 := by
    have : (M + 1) ^ 5 ≤ (2 * M) ^ 5 := pow_le_pow_left₀ (by linarith) (by linarith) 5
    calc _ ≤ _ := this
      _ = _ := by ring
  have b : 5 * M ^ 4 ≤ (M + 1) ^ 5 - M ^ 5 := by
    nlinarith [pow_pos h0 2, pow_pos h0 3, pow_pos h0 4, pow_pos h0 5]
  rw [div_sub_div _ _ (by positivity) (by positivity), ← mul_div_assoc,
    div_le_div_iff₀ (by positivity) (by positivity)]
  have c1 : M ^ 5 * (M + 1) ^ 5 ≤ 32 * M ^ 10 := by
    calc M ^ 5 * (M + 1) ^ 5 ≤ M ^ 5 * (32 * M ^ 5) :=
          mul_le_mul_of_nonneg_left a (by positivity)
      _ = 32 * M ^ 10 := by ring
  have c2 : 5 * M ^ 4 * (10 * M ^ 6) ≤ ((M + 1) ^ 5 - M ^ 5) * (10 * M ^ 6) :=
    mul_le_mul_of_nonneg_right b (by positivity)
  nlinarith [pow_pos h0 10]

/-- The remainder of the comparison: `0 ≤ log (stirlingSeq n) - log √π - gcmp n ≤ (3/4)/n⁵`. -/
lemma rem_bounds {n : ℕ} (hn : n ≠ 0) :
    0 ≤ Real.log (_root_.Stirling.stirlingSeq n) - Real.log √π - gcmp (n : ℝ) ∧
    Real.log (_root_.Stirling.stirlingSeq n) - Real.log √π - gcmp (n : ℝ) ≤
      3 / 4 * (1 / (n : ℝ) ^ 5) := by
  have hsq : 0 < √π := by positivity
  set hs : ℕ → ℝ := fun k =>
    Real.log (_root_.Stirling.stirlingSeq (k + 1)) - Real.log √π - gcmp ((k + 1 : ℕ) : ℝ) with hhs
  set ph : ℕ → ℝ := fun k => 3 / 4 * (1 / ((k + 1 : ℕ) : ℝ) ^ 5) with hph
  have hstep : ∀ k, hs k - hs (k + 1) =
      (Real.log (_root_.Stirling.stirlingSeq (k + 1)) - Real.log (_root_.Stirling.stirlingSeq (k + 2))) -
        (gcmp ((k + 1 : ℕ) : ℝ) - gcmp (((k + 1 : ℕ) : ℝ) + 1)) := by
    intro k
    simp only [hhs]
    push_cast
    ring_nf
  have hlim : Filter.Tendsto hs Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun k : ℕ => Real.log (_root_.Stirling.stirlingSeq (k + 1)))
        Filter.atTop (nhds (Real.log √π)) :=
      (_root_.Stirling.tendsto_stirlingSeq_sqrt_pi.comp
        (Filter.tendsto_add_atTop_nat 1)).log (by positivity)
    have := (h1.sub_const (Real.log √π)).sub tendsto_gcmp
    simpa only [sub_self, sub_zero] using this
  have hlimph : Filter.Tendsto ph Filter.atTop (nhds 0) := by
    have := (tendsto_inv_pow 1 (by norm_num) 5 (by norm_num)).const_mul (3 / 4 : ℝ)
    simpa [hph] using this
  have hanti : Antitone hs := antitone_nat_of_succ_le fun k => by
    have := (step_bounds k).1
    rw [← hstep] at this
    linarith
  have hmono : Monotone (fun k => hs k - ph k) := monotone_nat_of_le_succ fun k => by
    have h1 := (step_bounds k).2
    rw [← hstep] at h1
    have h2 := phi_ineq ((k + 1 : ℕ) : ℝ) (by exact_mod_cast Nat.succ_pos k)
    have e : ph k - ph (k + 1) = 3 / 4 * (1 / ((k + 1 : ℕ) : ℝ) ^ 5 - 1 / (((k + 1 : ℕ) : ℝ) + 1) ^ 5) := by
      simp only [hph]
      push_cast
      ring
    show hs k - ph k ≤ hs (k + 1) - ph (k + 1)
    linarith
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have a1 := hanti.le_of_tendsto hlim k
  have a2 := hmono.ge_of_tendsto (hlim.sub hlimph) k
  simp only [sub_zero] at a1 a2
  constructor
  · simpa [hhs] using a1
  · have : hs k ≤ ph k := by simpa using a2
    simpa [hhs, hph] using this

/-- CO-526. Stirling's series through the third correction term: the ratio
`n!/(√(2πn)(n/e)^n)` equals `1 + 1/(12n) + 1/(288 n²) - 139/(51840 n³)` up to an error of size
`O(1/n⁴)` (here with the explicit constant `4`; the statement only asserts existence of a constant). -/
@[kb "kellertrotter2017" "text p.255"]
theorem stirling_series :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      |(n ! : ℝ) / (√(2 * π * n) * (n / exp 1) ^ n) -
          (1 + 1 / (12 * n) + 1 / (288 * n ^ 2) - 139 / (51840 * n ^ 3))| ≤ C / (n : ℝ) ^ 4 := by
  refine ⟨4, fun n hn1 => ?_⟩
  have hn : n ≠ 0 := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  obtain ⟨hh0, hh1⟩ := rem_bounds hn
  have hsq : 0 < √π := by positivity
  have hS := _root_.Stirling.stirlingSeq'_pos (n - 1)
  rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hn)] at hS
  set t : ℝ := 1 / n with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hn']; exact hn1'
  set h : ℝ := Real.log (_root_.Stirling.stirlingSeq n) - Real.log √π - gcmp (n : ℝ) with hh
  have hgc : gcmp (n : ℝ) = t / 12 - t ^ 3 / 360 := by
    unfold gcmp
    simp only [ht]
    field_simp
  have hh1' : h ≤ 3 / 4 * t ^ 5 := by
    have : t ^ 5 = 1 / (n : ℝ) ^ 5 := by rw [ht, one_div_pow]
    rw [this]; exact hh1
  have hT : 1 + 1 / (12 * (n : ℝ)) + 1 / (288 * (n : ℝ) ^ 2) - 139 / (51840 * (n : ℝ) ^ 3) =
      1 + t / 12 + t ^ 2 / 288 - 139 / 51840 * t ^ 3 := by
    simp only [ht]; field_simp
  have hC : 4 / (n : ℝ) ^ 4 = 4 * t ^ 4 := by
    simp only [ht]; field_simp
  set g : ℝ := t / 12 - t ^ 3 / 360 with hg
  set r : ℝ := g + h with hr
  have hρ : (n ! : ℝ) / (√(2 * π * n) * (n / exp 1) ^ n) = exp r := by
    rw [ratio_eq hn]
    have : r = Real.log (_root_.Stirling.stirlingSeq n) - Real.log √π := by
      rw [hr, hh, hgc]; ring
    rw [this, exp_sub, exp_log hS, exp_log hsq]
  rw [hρ, hT, hC]
  have p2 : t ^ 2 ≤ t := by nlinarith
  have p3 : t ^ 3 ≤ t ^ 2 := pow_le_pow_of_le_one ht0.le ht1 (by norm_num)
  have p4 : t ^ 4 ≤ t ^ 3 := pow_le_pow_of_le_one ht0.le ht1 (by norm_num)
  have p5 : t ^ 5 ≤ t ^ 4 := pow_le_pow_of_le_one ht0.le ht1 (by norm_num)
  have p6 : t ^ 6 ≤ t ^ 4 := pow_le_pow_of_le_one ht0.le ht1 (by norm_num)
  have p7 : t ^ 7 ≤ t ^ 4 := pow_le_pow_of_le_one ht0.le ht1 (by norm_num)
  have p9 : t ^ 9 ≤ t ^ 4 := pow_le_pow_of_le_one ht0.le ht1 (by norm_num)
  have t4 : 0 < t ^ 4 := by positivity
  have hg0 : 0 ≤ g := by rw [hg]; nlinarith
  have hg1 : g ≤ t / 12 := by rw [hg]; nlinarith [pow_pos ht0 3]
  have hh0' : 0 ≤ h := hh0
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  have hr1 : r ≤ t := by rw [hr]; linarith
  have hr1' : r ≤ 1 := by linarith
  clear_value r g h
  -- Taylor expansion of the exponential
  have hexp := Real.exp_bound (x := r) (by rw [abs_of_nonneg hr0]; exact hr1') (n := 4) (by norm_num)
  have hs4 : ∑ i ∈ Finset.range 4, r ^ i / (i ! : ℝ) = 1 + r + r ^ 2 / 2 + r ^ 3 / 6 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hs4, abs_of_nonneg hr0] at hexp
  have hexp' : |exp r - (1 + r + r ^ 2 / 2 + r ^ 3 / 6)| ≤ 5 / 96 * t ^ 4 := by
    refine hexp.trans ?_
    have : r ^ 4 ≤ t ^ 4 := pow_le_pow_left₀ hr0 hr1 4
    norm_num [Nat.factorial]
    linarith
  -- the polynomial part
  have hq : |1 + g + g ^ 2 / 2 + g ^ 3 / 6 - (1 + t / 12 + t ^ 2 / 288 - 139 / 51840 * t ^ 3)| ≤
      t ^ 4 := by
    have e : 1 + g + g ^ 2 / 2 + g ^ 3 / 6 - (1 + t / 12 + t ^ 2 / 288 - 139 / 51840 * t ^ 3) =
        -(1 / 4320) * t ^ 4 - 1 / 103680 * t ^ 5 + 1 / 259200 * t ^ 6 + 1 / 3110400 * t ^ 7
          - 1 / 279936000 * t ^ 9 := by
      rw [hg]; ring
    rw [e, abs_le]
    have q5 := pow_pos ht0 5
    have q6 := pow_pos ht0 6
    have q7 := pow_pos ht0 7
    have q9 := pow_pos ht0 9
    constructor <;> linarith
  have hW : |h * (1 + (r + g) / 2 + (r ^ 2 + r * g + g ^ 2) / 6)| ≤ 3 * (3 / 4 * t ^ 5) := by
    have hWn : 0 ≤ 1 + (r + g) / 2 + (r ^ 2 + r * g + g ^ 2) / 6 := by positivity
    have hWl : 1 + (r + g) / 2 + (r ^ 2 + r * g + g ^ 2) / 6 ≤ 3 := by
      have a1 : r ^ 2 ≤ 1 := pow_le_one₀ hr0 hr1'
      have a2 : r * g ≤ 1 := mul_le_one₀ hr1' hg0 (by linarith)
      have a3 : g ^ 2 ≤ 1 := pow_le_one₀ hg0 (by linarith)
      linarith
    rw [abs_of_nonneg (by positivity)]
    calc _ ≤ h * 3 := by gcongr
      _ ≤ 3 * (3 / 4 * t ^ 5) := by linarith
  have hsplit : (1 + r + r ^ 2 / 2 + r ^ 3 / 6) -
      (1 + t / 12 + t ^ 2 / 288 - 139 / 51840 * t ^ 3) =
      (1 + g + g ^ 2 / 2 + g ^ 3 / 6 - (1 + t / 12 + t ^ 2 / 288 - 139 / 51840 * t ^ 3)) +
        h * (1 + (r + g) / 2 + (r ^ 2 + r * g + g ^ 2) / 6) := by
    have : r = g + h := hr
    rw [this]; ring
  have hfin := abs_sub_le (exp r) (1 + r + r ^ 2 / 2 + r ^ 3 / 6)
    (1 + t / 12 + t ^ 2 / 288 - 139 / 51840 * t ^ 3)
  have h2 := abs_add_le (1 + g + g ^ 2 / 2 + g ^ 3 / 6 - (1 + t / 12 + t ^ 2 / 288 - 139 / 51840 * t ^ 3))
    (h * (1 + (r + g) / 2 + (r ^ 2 + r * g + g ^ 2) / 6))
  rw [← hsplit] at h2
  linarith

end Stirling

end UndergradKB.Combinatorics
