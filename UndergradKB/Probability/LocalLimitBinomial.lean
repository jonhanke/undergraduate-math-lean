import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-!
# Probability: the local limit theorem for the binomial distribution (Grinstead–Snell, Theorem 9.1)

For fixed `0 < p < 1`, `q = 1 - p` and fixed `x`, if `k_n` are integers with `k_n - n p - x √(n p q)`
bounded, then `√(n p q) · C(n, k_n) p^{k_n} q^{n - k_n} → e^{-x²/2} / √(2π)`.

The proof follows the book: Stirling's formula turns the binomial probability into
`√(n² p q / (2 k m)) · (n p / k)^k (n q / m)^m` up to factors tending to `1`, and a second order
expansion of the logarithm shows `(n p / k)^k (n q / m)^m → e^{-x²/2}`.
-/

open Filter Finset Real
open scoped Topology

namespace UndergradKB.Probability

namespace LocalBinomial

/-- Second order expansion of `log (1 - y)` with remainder bound. -/
theorem log_one_sub_bound {y : ℝ} (hy : |y| ≤ 1 / 2) :
    |log (1 - y) - (-y - y ^ 2 / 2)| ≤ 2 * |y| ^ 3 := by
  have h := Real.abs_log_sub_add_sum_range_le (lt_of_le_of_lt hy (by norm_num)) 2
  simp only [sum_range_succ, sum_range_zero] at h
  have e : log (1 - y) - (-y - y ^ 2 / 2) = (0 + y ^ (0 + 1) / (↑(0 : ℕ) + 1) + y ^ (1 + 1) / (↑(1 : ℕ) + 1)) + log (1 - y) := by
    push_cast; ring
  rw [e]
  refine h.trans ?_
  have h1 : 0 < 1 - |y| := by linarith
  rw [div_le_iff₀ h1]
  have : 0 ≤ |y| ^ 3 := by positivity
  have h2 : |y| ^ (2 + 1) = |y| ^ 3 := rfl
  rw [h2]
  nlinarith [mul_nonneg this (by linarith : (0 : ℝ) ≤ 1 - 2 * |y|)]

/-- Pointwise estimate for the exponent: with `k = s² p + d s`, `m = s² q - d s`. -/
theorem key_bound {p q d s : ℝ} (hp : 0 < p) (hq : 0 < q) (hpq : p + q = 1) (hs : 0 < s)
    (hu : |d / (p * s)| ≤ 1 / 2) (hv : |d / (q * s)| ≤ 1 / 2) :
    |(s ^ 2 * p + d * s) * log ((s ^ 2 * p + d * s) / (s ^ 2 * p)) +
        (s ^ 2 * q - d * s) * log ((s ^ 2 * q - d * s) / (s ^ 2 * q)) -
      (d ^ 2 / (2 * p * q) + d ^ 3 / s * (1 / (2 * q ^ 2) - 1 / (2 * p ^ 2)))| ≤
    2 * (s ^ 2 * p + |d| * s) * |d / (p * s)| ^ 3 +
      2 * (s ^ 2 * q + |d| * s) * |d / (q * s)| ^ 3 := by
  have hp0 : p ≠ 0 := hp.ne'
  have hq0 : q ≠ 0 := hq.ne'
  have hs0 : s ≠ 0 := hs.ne'
  set u := d / (p * s) with hu_def
  set v := d / (q * s) with hv_def
  have e1 : (s ^ 2 * p + d * s) / (s ^ 2 * p) = 1 - (-u) := by
    rw [hu_def]; field_simp; ring
  have e2 : (s ^ 2 * q - d * s) / (s ^ 2 * q) = 1 - v := by
    rw [hv_def]; field_simp
  rw [e1, e2]
  have L1 := log_one_sub_bound (y := -u) (by rwa [abs_neg])
  have L2 := log_one_sub_bound (y := v) hv
  set R1 := log (1 - -u) - (-(-u) - (-u) ^ 2 / 2) with hR1
  set R2 := log (1 - v) - (-v - v ^ 2 / 2) with hR2
  have hq' : q = 1 - p := by linarith
  have hE : (s ^ 2 * p + d * s) * log (1 - -u) + (s ^ 2 * q - d * s) * log (1 - v) -
      (d ^ 2 / (2 * p * q) + d ^ 3 / s * (1 / (2 * q ^ 2) - 1 / (2 * p ^ 2))) =
      (s ^ 2 * p + d * s) * R1 + (s ^ 2 * q - d * s) * R2 := by
    rw [hR1, hR2, hu_def, hv_def]
    subst hq'
    have : 1 - p ≠ 0 := hq0
    field_simp
    ring
  rw [hE]
  have hk : |s ^ 2 * p + d * s| ≤ s ^ 2 * p + |d| * s := by
    calc _ ≤ |s ^ 2 * p| + |d * s| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_of_pos hs, abs_of_pos hp, abs_pow, abs_of_pos hs]
  have hm : |s ^ 2 * q - d * s| ≤ s ^ 2 * q + |d| * s := by
    calc _ ≤ |s ^ 2 * q| + |d * s| := abs_sub _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_of_pos hs, abs_of_pos hq, abs_pow, abs_of_pos hs]
  rw [abs_neg] at L1
  calc _ ≤ |(s ^ 2 * p + d * s) * R1| + |(s ^ 2 * q - d * s) * R2| := abs_add_le _ _
    _ = |s ^ 2 * p + d * s| * |R1| + |s ^ 2 * q - d * s| * |R2| := by rw [abs_mul, abs_mul]
    _ ≤ (s ^ 2 * p + |d| * s) * (2 * |u| ^ 3) + (s ^ 2 * q + |d| * s) * (2 * |v| ^ 3) := by
      gcongr
    _ = _ := by ring

/-- The exponent `k log (k / (n p)) + m log (m / (n q))`, with `n = s²`, `k = n p + d s`, tends to
`d₀² / (2 p q)` when `d → d₀` and `s → ∞`. -/
theorem exponent_tendsto {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hpq : p + q = 1)
    {s d : ℕ → ℝ} {d0 : ℝ} (hs : Tendsto s atTop atTop) (hd : Tendsto d atTop (𝓝 d0)) :
    Tendsto (fun n => (s n ^ 2 * p + d n * s n) * log ((s n ^ 2 * p + d n * s n) / (s n ^ 2 * p)) +
        (s n ^ 2 * q - d n * s n) * log ((s n ^ 2 * q - d n * s n) / (s n ^ 2 * q)))
      atTop (𝓝 (d0 ^ 2 / (2 * p * q))) := by
  have hinv : Tendsto (fun n => (s n)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hs
  have hpos : ∀ᶠ n in atTop, 0 < s n := hs.eventually_gt_atTop 0
  set F : ℕ → ℝ := fun n => d n ^ 2 / (2 * p * q) + d n ^ 3 / s n * (1 / (2 * q ^ 2) - 1 / (2 * p ^ 2))
    with hF
  have hFlim : Tendsto F atTop (𝓝 (d0 ^ 2 / (2 * p * q))) := by
    have h1 : Tendsto (fun n => d n ^ 3 / s n) atTop (𝓝 (d0 ^ 3 * 0)) := by
      simpa only [div_eq_mul_inv] using (hd.pow 3).mul hinv
    have h2 := ((hd.pow 2).div_const (2 * p * q)).add (h1.mul_const (1 / (2 * q ^ 2) - 1 / (2 * p ^ 2)))
    simp only [mul_zero, zero_mul, add_zero] at h2
    exact h2
  have hu : Tendsto (fun n => d n / (p * s n)) atTop (𝓝 0) := by
    have := (hd.div_const p).mul hinv
    simp only [mul_zero] at this
    refine this.congr fun n => ?_
    ring
  have hv : Tendsto (fun n => d n / (q * s n)) atTop (𝓝 0) := by
    have := (hd.div_const q).mul hinv
    simp only [mul_zero] at this
    refine this.congr fun n => ?_
    ring
  have hu' : ∀ᶠ n in atTop, |d n / (p * s n)| ≤ 1 / 2 := by
    filter_upwards [Metric.tendsto_nhds.1 hu (1 / 2) (by norm_num)] with n hn
    rw [Real.dist_eq, sub_zero] at hn
    exact hn.le
  have hv' : ∀ᶠ n in atTop, |d n / (q * s n)| ≤ 1 / 2 := by
    filter_upwards [Metric.tendsto_nhds.1 hv (1 / 2) (by norm_num)] with n hn
    rw [Real.dist_eq, sub_zero] at hn
    exact hn.le
  -- the bound tends to zero
  set B : ℕ → ℝ := fun n => 2 * (s n ^ 2 * p + |d n| * s n) * |d n / (p * s n)| ^ 3 +
      2 * (s n ^ 2 * q + |d n| * s n) * |d n / (q * s n)| ^ 3 with hB
  have hdabs : Tendsto (fun n => |d n|) atTop (𝓝 |d0|) := hd.abs
  have hB' : Tendsto (fun n => 2 * |d n| ^ 3 / p ^ 2 * (s n)⁻¹ + 2 * |d n| ^ 4 / p ^ 3 * ((s n)⁻¹) ^ 2 +
      (2 * |d n| ^ 3 / q ^ 2 * (s n)⁻¹ + 2 * |d n| ^ 4 / q ^ 3 * ((s n)⁻¹) ^ 2)) atTop (𝓝 0) := by
    have a1 := (((hdabs.pow 3).const_mul 2).div_const (p ^ 2)).mul hinv
    have a2 := (((hdabs.pow 4).const_mul 2).div_const (p ^ 3)).mul (hinv.pow 2)
    have a3 := (((hdabs.pow 3).const_mul 2).div_const (q ^ 2)).mul hinv
    have a4 := (((hdabs.pow 4).const_mul 2).div_const (q ^ 3)).mul (hinv.pow 2)
    simpa using (a1.add a2).add (a3.add a4)
  have hBlim : Tendsto B atTop (𝓝 0) := by
    refine hB'.congr' ?_
    filter_upwards [hpos] with n hn
    simp only [hB]
    rw [abs_div, abs_div, abs_mul, abs_mul, abs_of_pos hp, abs_of_pos hq, abs_of_pos hn]
    have hp0 : p ≠ 0 := hp.ne'
    have hq0 : q ≠ 0 := hq.ne'
    have hn0 : s n ≠ 0 := hn.ne'
    field_simp
  have hdiff : Tendsto (fun n => (s n ^ 2 * p + d n * s n) * log ((s n ^ 2 * p + d n * s n) / (s n ^ 2 * p)) +
        (s n ^ 2 * q - d n * s n) * log ((s n ^ 2 * q - d n * s n) / (s n ^ 2 * q)) - F n) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hBlim
    filter_upwards [hpos, hu', hv'] with n h1 h2 h3
    rw [Real.norm_eq_abs]
    exact key_bound hp hq hpq h1 h2 h3
  have := hFlim.add hdiff
  simpa using this

/-- `(n/e)^n p^k q^m / ((k/e)^k (m/e)^m) = exp (-(k log (k/(n p)) + m log (m/(n q))))` for `n = k + m`. -/
theorem power_ratio_eq {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {K m : ℕ} (hK : 0 < K) (hm : 0 < m) :
    (((K + m : ℕ) : ℝ) / exp 1) ^ (K + m) * p ^ K * q ^ m /
        (((K : ℝ) / exp 1) ^ K * ((m : ℝ) / exp 1) ^ m) =
      exp (-((K : ℝ) * log (K / (((K + m : ℕ) : ℝ) * p)) + (m : ℝ) * log (m / (((K + m : ℕ) : ℝ) * q)))) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hn : (0 : ℝ) < ((K + m : ℕ) : ℝ) := by positivity
  have h1 : exp (-((K : ℝ) * log (K / (((K + m : ℕ) : ℝ) * p)))) =
      (((K + m : ℕ) : ℝ) * p / K) ^ K := by
    have : -((K : ℝ) * log (K / (((K + m : ℕ) : ℝ) * p))) =
        (K : ℝ) * log (((K + m : ℕ) : ℝ) * p / K) := by
      rw [← inv_div, Real.log_inv]; ring
    rw [this, Real.exp_nat_mul, Real.exp_log (by positivity)]
  have h2 : exp (-((m : ℝ) * log (m / (((K + m : ℕ) : ℝ) * q)))) =
      (((K + m : ℕ) : ℝ) * q / m) ^ m := by
    have : -((m : ℝ) * log (m / (((K + m : ℕ) : ℝ) * q))) =
        (m : ℝ) * log (((K + m : ℕ) : ℝ) * q / m) := by
      rw [← inv_div, Real.log_inv]; ring
    rw [this, Real.exp_nat_mul, Real.exp_log (by positivity)]
  rw [neg_add, Real.exp_add, h1, h2]
  have he : exp 1 ≠ 0 := (exp_pos 1).ne'
  rw [div_pow, div_pow, div_pow, div_pow, div_pow, mul_pow, mul_pow, pow_add, pow_add]
  have : (((K + m : ℕ) : ℝ)) ^ K ≠ 0 := by positivity
  field_simp

theorem stirlingSeq_ne_zero {k : ℕ} (hk : 0 < k) : Stirling.stirlingSeq k ≠ 0 := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  unfold Stirling.stirlingSeq
  have : 0 < √(2 * (k : ℝ)) := Real.sqrt_pos.2 (by positivity)
  have : (0 : ℝ) < (k : ℝ) / exp 1 := by positivity
  have : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  positivity

theorem factorial_eq {k : ℕ} (hk : 0 < k) :
    (k.factorial : ℝ) = Stirling.stirlingSeq k * (√(2 * (k : ℝ)) * ((k : ℝ) / exp 1) ^ k) := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 : 0 < √(2 * (k : ℝ)) := Real.sqrt_pos.2 (by positivity)
  have h2 : (0 : ℝ) < (k : ℝ) / exp 1 := by positivity
  unfold Stirling.stirlingSeq
  field_simp

/-- Stirling's formula applied to `C(K+m, K) p^K q^m`. -/
theorem binom_identity {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {K m : ℕ} (hK : 0 < K) (hm : 0 < m) :
    √(((K + m : ℕ) : ℝ) * p * q) * ((((K + m).choose K : ℕ) : ℝ) * p ^ K * q ^ m) =
      (Stirling.stirlingSeq (K + m) / (Stirling.stirlingSeq K * Stirling.stirlingSeq m)) *
        (√(((K + m : ℕ) : ℝ) * p * q) * √(2 * ((K + m : ℕ) : ℝ)) /
          (√(2 * (K : ℝ)) * √(2 * (m : ℝ)))) *
        ((((K + m : ℕ) : ℝ) / exp 1) ^ (K + m) * p ^ K * q ^ m /
          (((K : ℝ) / exp 1) ^ K * ((m : ℝ) / exp 1) ^ m)) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hn : 0 < K + m := by omega
  have hc : (((K + m).choose K : ℕ) : ℝ) =
      ((K + m).factorial : ℝ) / ((K.factorial : ℝ) * (m.factorial : ℝ)) := by
    rw [Nat.cast_choose ℝ (show K ≤ K + m by omega)]
    simp
  rw [hc, factorial_eq hn, factorial_eq hK, factorial_eq hm]
  have s1 := stirlingSeq_ne_zero hK
  have s2 := stirlingSeq_ne_zero hm
  have r1 : √(2 * (K : ℝ)) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  have r2 : √(2 * (m : ℝ)) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  have p1 : ((K : ℝ) / exp 1) ^ K ≠ 0 := by positivity
  have p2 : ((m : ℝ) / exp 1) ^ m ≠ 0 := by positivity
  field_simp

theorem sqrt_ratio_eq {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {n K M : ℕ} (hK : 0 < K) (hM : 0 < M) :
    √((n : ℝ) * p * q) * √(2 * (n : ℝ)) / (√(2 * (K : ℝ)) * √(2 * (M : ℝ))) =
      √((n : ℝ) / K * ((n : ℝ) / M) * p * q / 2) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity),
    ← Real.sqrt_div (by positivity)]
  congr 1
  field_simp

/-- Auxiliary: the rescaled deviation `d n = (K n - n p) / √n` converges, and `K n / n → p`. -/
theorem deviation_tendsto {p q : ℝ} (hp0 : 0 < p) (hq : 0 < q) (x : ℝ) {K : ℕ → ℕ} {C : ℝ}
    (hK : ∀ᶠ n : ℕ in atTop, |(K n : ℝ) - n * p - x * √(n * p * q)| ≤ C) :
    Tendsto (fun n : ℕ => ((K n : ℝ) - n * p) / √(n : ℝ)) atTop (𝓝 (x * √(p * q))) := by
  have hsn : Tendsto (fun n : ℕ => √(n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hsn
  have hnpos : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  have hb : Tendsto (fun n : ℕ => C * (√(n : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa using hinv.const_mul C
  have h0 : Tendsto (fun n : ℕ => ((K n : ℝ) - n * p) / √(n : ℝ) - x * √(p * q)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [hK, hnpos] with n hn hn0
    have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn0)
    have e : √((n : ℝ) * p * q) = √(n : ℝ) * √(p * q) := by
      rw [mul_assoc, Real.sqrt_mul (Nat.cast_nonneg n)]
    have : ((K n : ℝ) - n * p) / √(n : ℝ) - x * √(p * q) =
        ((K n : ℝ) - n * p - x * √(n * p * q)) / √(n : ℝ) := by
      rw [e]; field_simp
    rw [Real.norm_eq_abs, this, abs_div, abs_of_pos hs, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hn (inv_nonneg.2 hs.le)
  simpa using h0.add_const (x * √(p * q))

/-- Local limit theorem, general form (see `local_limit_binomial`). -/
theorem local_limit_aux {p q : ℝ} (hp0 : 0 < p) (hq : 0 < q) (hpq : p + q = 1) (x : ℝ)
    {K : ℕ → ℕ} {C : ℝ}
    (hK : ∀ᶠ n : ℕ in atTop, |(K n : ℝ) - n * p - x * √(n * p * q)| ≤ C) :
    Tendsto (fun n : ℕ => √(n * p * q) *
        ((n.choose (K n) : ℝ) * p ^ K n * q ^ (n - K n))) atTop
      (𝓝 (exp (-x ^ 2 / 2) / √(2 * π))) := by
  have hpq0 : 0 < p * q := mul_pos hp0 hq
  have hp1 : p < 1 := by linarith
  have hsn : Tendsto (fun n : ℕ => √(n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hsn
  have hnpos : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  set d : ℕ → ℝ := fun n => ((K n : ℝ) - n * p) / √(n : ℝ) with hd_def
  have hd : Tendsto d atTop (𝓝 (x * √(p * q))) := deviation_tendsto hp0 hq x hK
  -- the exponent
  have hE := exponent_tendsto hp0 hq hpq hsn hd
  have hlim1 : (x * √(p * q)) ^ 2 / (2 * p * q) = x ^ 2 / 2 := by
    rw [mul_pow, Real.sq_sqrt hpq0.le]; field_simp
  rw [hlim1] at hE
  -- K n / n → p
  have hKn : Tendsto (fun n : ℕ => (K n : ℝ) / n) atTop (𝓝 p) := by
    have h1 : Tendsto (fun n : ℕ => p + d n * (√(n : ℝ))⁻¹) atTop (𝓝 (p + x * √(p * q) * 0)) :=
      tendsto_const_nhds.add (hd.mul hinv)
    simp only [mul_zero, add_zero] at h1
    refine h1.congr' ?_
    filter_upwards [hnpos] with n hn0
    have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn0)
    have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
    have hss : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
    have e : d n * (√(n : ℝ))⁻¹ = ((K n : ℝ) - n * p) / n := by
      have h2 : ((K n : ℝ) - n * p) / √(n : ℝ) * (√(n : ℝ))⁻¹ =
          ((K n : ℝ) - n * p) / (√(n : ℝ) * √(n : ℝ)) := by
        field_simp
      rw [hss] at h2
      exact h2
    rw [e]; field_simp; ring
  have hmn : Tendsto (fun n : ℕ => ((n : ℝ) - K n) / n) atTop (𝓝 q) := by
    have h1 : Tendsto (fun n : ℕ => 1 - (K n : ℝ) / n) atTop (𝓝 (1 - p)) :=
      tendsto_const_nhds.sub hKn
    have hq1 : 1 - p = q := by linarith
    rw [hq1] at h1
    refine h1.congr' ?_
    filter_upwards [hnpos] with n hn0
    have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
    field_simp
  -- K n → ∞ and n - K n → ∞
  have hKlow : ∀ᶠ n : ℕ in atTop, p / 2 * n ≤ (K n : ℝ) := by
    filter_upwards [(tendsto_order.1 hKn).1 (p / 2) (by linarith), hnpos] with n h1 h2
    have : (0 : ℝ) < n := by exact_mod_cast h2
    rw [lt_div_iff₀ this] at h1
    linarith
  have hMlow : ∀ᶠ n : ℕ in atTop, q / 2 * n ≤ (n : ℝ) - K n := by
    filter_upwards [(tendsto_order.1 hmn).1 (q / 2) (by linarith), hnpos] with n h1 h2
    have : (0 : ℝ) < n := by exact_mod_cast h2
    rw [lt_div_iff₀ this] at h1
    linarith
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hKtop : Tendsto K atTop atTop := by
    rw [← tendsto_natCast_atTop_iff (R := ℝ)]
    exact tendsto_atTop_mono' _ hKlow (hnat.const_mul_atTop (by positivity))
  have hKle : ∀ᶠ n : ℕ in atTop, K n ≤ n := by
    filter_upwards [hMlow, hnpos] with n h1 h2
    have : (0 : ℝ) < n := by exact_mod_cast h2
    have : (K n : ℝ) ≤ n := by nlinarith
    exact_mod_cast this
  have hMcast : ∀ᶠ n : ℕ in atTop, (((n - K n : ℕ)) : ℝ) = (n : ℝ) - K n := by
    filter_upwards [hKle] with n h1
    rw [Nat.cast_sub h1]
  have hMtop : Tendsto (fun n : ℕ => n - K n) atTop atTop := by
    rw [← tendsto_natCast_atTop_iff (R := ℝ)]
    refine tendsto_atTop_mono' _ ?_ (hnat.const_mul_atTop (show 0 < q / 2 by positivity))
    filter_upwards [hMlow, hMcast] with n h1 h2
    rw [h2]; exact h1
  -- Stirling factor
  have hst := Stirling.tendsto_stirlingSeq_sqrt_pi
  have hsqpi : √π ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hS : Tendsto (fun n : ℕ => Stirling.stirlingSeq n /
      (Stirling.stirlingSeq (K n) * Stirling.stirlingSeq (n - K n))) atTop
      (𝓝 (√π / (√π * √π))) :=
    hst.div ((hst.comp hKtop).mul (hst.comp hMtop)) (mul_ne_zero hsqpi hsqpi)
  -- ratio factor
  have hrat : Tendsto (fun n : ℕ => √((n : ℝ) / K n * ((n : ℝ) / (n - K n : ℕ)) * p * q / 2))
      atTop (𝓝 (√(1 / 2))) := by
    have a1 : Tendsto (fun n : ℕ => ((K n : ℝ) / n)⁻¹) atTop (𝓝 p⁻¹) := hKn.inv₀ hp0.ne'
    have a2 : Tendsto (fun n : ℕ => (((n : ℝ) - K n) / n)⁻¹) atTop (𝓝 q⁻¹) := hmn.inv₀ hq.ne'
    have a3 := ((a1.mul a2).mul_const p).mul_const q |>.div_const 2
    have a4 : p⁻¹ * q⁻¹ * p * q / 2 = 1 / 2 := by field_simp
    rw [a4] at a3
    refine (a3.sqrt).congr' ?_
    filter_upwards [hMcast] with n h1
    rw [h1, inv_div, inv_div]
  have hKpos : ∀ᶠ n : ℕ in atTop, 0 < K n := hKtop.eventually_gt_atTop 0
  have hMpos : ∀ᶠ n : ℕ in atTop, 0 < n - K n := hMtop.eventually_gt_atTop 0
  have hrho : Tendsto (fun n : ℕ => √((n : ℝ) * p * q) * √(2 * (n : ℝ)) /
      (√(2 * (K n : ℝ)) * √(2 * ((n - K n : ℕ) : ℝ)))) atTop (𝓝 (√(1 / 2))) := by
    refine hrat.congr' ?_
    filter_upwards [hKpos, hMpos] with n h1 h2
    exact (sqrt_ratio_eq hp0 hq h1 h2).symm
  -- exponent in the natural form
  have hE' : Tendsto (fun n : ℕ => (K n : ℝ) * log ((K n : ℝ) / (n * p)) +
      ((n - K n : ℕ) : ℝ) * log (((n - K n : ℕ) : ℝ) / (n * q))) atTop (𝓝 (x ^ 2 / 2)) := by
    refine hE.congr' ?_
    filter_upwards [hnpos, hMcast] with n hn0 hM
    beta_reduce
    have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn0)
    have hsq : √(n : ℝ) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
    have hds : d n * √(n : ℝ) = K n - n * p := by rw [hd_def]; simp only; field_simp
    have e1 : √(n : ℝ) ^ 2 * p + d n * √(n : ℝ) = K n := by rw [hsq, hds]; ring
    have e2 : √(n : ℝ) ^ 2 * q - d n * √(n : ℝ) = ((n - K n : ℕ) : ℝ) := by
      rw [hM, hsq, hds]; linear_combination (n : ℝ) * hpq
    rw [e1, e2, hsq]
  have hexp : Tendsto (fun n : ℕ => exp (-((K n : ℝ) * log ((K n : ℝ) / (n * p)) +
      ((n - K n : ℕ) : ℝ) * log (((n - K n : ℕ) : ℝ) / (n * q))))) atTop
      (𝓝 (exp (-(x ^ 2 / 2)))) :=
    (Real.continuous_exp.tendsto _).comp hE'.neg
  have hfin := (hS.mul hrho).mul hexp
  have hlimeq : √π / (√π * √π) * √(1 / 2) * exp (-(x ^ 2 / 2)) = exp (-x ^ 2 / 2) / √(2 * π) := by
    have h2pi : √(2 * π) = √2 * √π := Real.sqrt_mul (by norm_num) π
    have h2 : √(1 / 2 : ℝ) = (√2)⁻¹ := by rw [one_div, Real.sqrt_inv]
    have h3 : √(2 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.2 (by norm_num)
    rw [h2pi, h2, neg_div]
    field_simp
  rw [hlimeq] at hfin
  refine hfin.congr' ?_
  filter_upwards [hKpos, hMpos, hKle] with n h1 h2 h3
  have i1 := binom_identity hp0 hq h1 h2
  have i2 := power_ratio_eq hp0 hq h1 h2
  have hKM : K n + (n - K n) = n := by omega
  rw [hKM] at i1 i2
  rw [i2] at i1
  exact i1.symm

end LocalBinomial

open LocalBinomial in
/-- Grinstead–Snell Theorem 9.1 (PR-097). For fixed `0 < p < 1`, `q = 1 - p` and fixed `x`, if the integers
`k_n` stay within a bounded distance `C` of `n p + x √(n p q)`, then the binomial probability
`b(n, p, k_n) = C(n, k_n) p^{k_n} q^{n - k_n}`, rescaled by `√(n p q)`, converges to the standard normal
density `φ(x) = e^{-x²/2} / √(2π)`. -/
@[kb "grinsteadsnell2006" "Theorem 9.1, p. 336"]
theorem local_limit_binomial {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (x : ℝ) {K : ℕ → ℕ} {C : ℝ}
    (hK : ∀ᶠ n : ℕ in atTop, |(K n : ℝ) - n * p - x * √(n * p * (1 - p))| ≤ C) :
    Tendsto (fun n : ℕ => √(n * p * (1 - p)) *
        ((n.choose (K n) : ℝ) * p ^ K n * (1 - p) ^ (n - K n))) atTop
      (𝓝 (exp (-x ^ 2 / 2) / √(2 * π))) :=
  local_limit_aux hp0 (by linarith) (by ring) x hK

open LocalBinomial in
/-- Grinstead–Snell Theorem 9.1 (PR-097), the book's form: with `k_n` the integer nearest to
`n p + x √(n p q)`, `√(n p q) · b(n, p, k_n) → φ(x)`. -/
@[kb "grinsteadsnell2006" "Theorem 9.1, p. 336"]
theorem local_limit_binomial_nearest {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (x : ℝ) :
    Tendsto (fun n : ℕ => √(n * p * (1 - p)) *
        ((n.choose ⌊n * p + x * √(n * p * (1 - p)) + 1 / 2⌋₊ : ℝ) * p ^ ⌊n * p + x * √(n * p * (1 - p)) + 1 / 2⌋₊ *
          (1 - p) ^ (n - ⌊n * p + x * √(n * p * (1 - p)) + 1 / 2⌋₊))) atTop
      (𝓝 (exp (-x ^ 2 / 2) / √(2 * π))) := by
  have hpq0 : 0 < p * (1 - p) := mul_pos hp0 (by linarith)
  have hsn : Tendsto (fun n : ℕ => √(n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun n : ℕ => √(n : ℝ) * p + x * √(p * (1 - p))) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (hsn.atTop_mul_const hp0)
  refine local_limit_binomial hp0 hp1 x (C := 1 / 2) ?_
  filter_upwards [h1.eventually_ge_atTop 0] with n hn
  have e : (n : ℝ) * p + x * √(n * p * (1 - p)) = √(n : ℝ) * (√(n : ℝ) * p + x * √(p * (1 - p))) := by
    have : √((n : ℝ) * p * (1 - p)) = √(n : ℝ) * √(p * (1 - p)) := by
      rw [mul_assoc, Real.sqrt_mul (Nat.cast_nonneg n)]
    rw [this]
    have hss : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
    calc (n : ℝ) * p + x * (√(n : ℝ) * √(p * (1 - p)))
        = (√(n : ℝ) * √(n : ℝ)) * p + x * (√(n : ℝ) * √(p * (1 - p))) := by rw [hss]
      _ = _ := by ring
  have hy : 0 ≤ (n : ℝ) * p + x * √(n * p * (1 - p)) := by
    rw [e]; exact mul_nonneg (Real.sqrt_nonneg _) hn
  have hf1 := Nat.floor_le (show 0 ≤ (n : ℝ) * p + x * √(n * p * (1 - p)) + 1 / 2 by linarith)
  have hf2 := Nat.lt_floor_add_one ((n : ℝ) * p + x * √(n * p * (1 - p)) + 1 / 2)
  rw [abs_le]
  constructor <;> linarith

end UndergradKB.Probability
