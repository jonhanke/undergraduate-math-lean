import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Exponential
import UndergradKB.Combinatorics.Counting.Stirling
import UndergradKB.Common.Attr

/-!
# The first correction term in Stirling's series (Keller–Trotter, Section 11.3)

The book quotes `n! ≈ √(2πn)(n/e)^n (1 + 1/(12n) + 1/(288 n²) - ...)`.  We prove the first correction
term in asymptotic form: `n!/(√(2πn)(n/e)^n) = 1 + 1/(12n) + O(1/n²)`, with the explicit constant `1`.
The upper bound is `stirling_bounds`; the lower bound `exp(1/(12n) - 1/n²) ≤ ratio` comes from the
first term of the series for the stepwise difference of `log (stirlingSeq n)` (a weaker form of
Robbins' lower bound `exp (1/(12n+1))`, which is not in Mathlib).
-/

namespace UndergradKB.Combinatorics

open Real Nat

namespace Stirling

/-- Elementary inequality behind the telescoping lower bound. -/
lemma aux_ineq (M : ℝ) (hM : 1 ≤ M) :
    1 / (12 * M * (M + 1)) - 1 / (3 * (2 * M + 1) ^ 2) ≤ 1 / M ^ 2 - 1 / (M + 1) ^ 2 := by
  have h0 : 0 < M := by linarith
  rw [div_sub_div _ _ (by positivity) (by positivity), div_sub_div _ _ (by positivity) (by positivity),
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos h0 h0, pow_pos h0 3, pow_pos h0 4, pow_pos h0 5, pow_pos h0 6, pow_pos h0 7,
    pow_pos h0 8]

/-- Step lower bound for the Stirling sequence. -/
lemma sdiff_ge (m : ℕ) :
    1 / (3 * (2 * ((m + 1 : ℕ) : ℝ) + 1) ^ 2) ≤
      Real.log (_root_.Stirling.stirlingSeq (m + 1)) - Real.log (_root_.Stirling.stirlingSeq (m + 2)) := by
  have hs := _root_.Stirling.log_stirlingSeq_sdiff_hasSum m
  have h := sum_le_hasSum (Finset.range 1) (fun k _ => by positivity) hs
  simp only [Finset.sum_range_one] at h
  convert h using 1
  push_cast
  field_simp
  norm_num

/-- Lower bound: `log (stirlingSeq n) ≥ log √π + 1/(12 n) - 1/n²`. -/
lemma log_stirlingSeq_ge {n : ℕ} (hn : n ≠ 0) :
    Real.log √π + 1 / (12 * (n : ℝ)) - 1 / (n : ℝ) ^ 2 ≤ Real.log (_root_.Stirling.stirlingSeq n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  set u : ℕ → ℝ := fun k =>
    Real.log (_root_.Stirling.stirlingSeq (k + 1)) - 1 / (12 * ((k + 1 : ℕ) : ℝ)) +
      1 / ((k + 1 : ℕ) : ℝ) ^ 2 with hu
  have hanti : Antitone u := by
    refine antitone_nat_of_succ_le fun k => ?_
    have h1 := sdiff_ge k
    have h2 := aux_ineq ((k + 1 : ℕ) : ℝ) (by exact_mod_cast Nat.succ_pos k)
    have e : (1 : ℝ) / (12 * ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1)) =
        1 / (12 * ((k + 1 : ℕ) : ℝ)) - 1 / (12 * ((k + 1 + 1 : ℕ) : ℝ)) := by
      push_cast
      field_simp
      ring
    rw [e] at h2
    simp only [hu]
    have h1' : 1 / (3 * (2 * ((k + 1 : ℕ) : ℝ) + 1) ^ 2) ≤ Real.log (_root_.Stirling.stirlingSeq (k + 1)) -
        Real.log (_root_.Stirling.stirlingSeq (k + 1 + 1)) := h1
    push_cast at h1' h2 ⊢
    linarith
  have hlim : Filter.Tendsto u Filter.atTop (nhds (Real.log √π - 0 + 0)) := by
    refine Filter.Tendsto.add (Filter.Tendsto.sub ?_ ?_) ?_
    · exact ((_root_.Stirling.tendsto_stirlingSeq_sqrt_pi.comp
        (Filter.tendsto_add_atTop_nat 1)).log (by positivity))
    · have h1 : Filter.Tendsto (fun k : ℕ => (12 : ℝ) * ((k + 1 : ℕ) : ℝ)) Filter.atTop Filter.atTop :=
        tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1) |>.const_mul_atTop
          (by norm_num)
      exact h1.inv_tendsto_atTop.congr fun k => (one_div _).symm
    · have h1 : Filter.Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ 2) Filter.atTop Filter.atTop :=
        (Filter.tendsto_pow_atTop (by norm_num)).comp
          (tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1))
      exact h1.inv_tendsto_atTop.congr fun k => (one_div _).symm
  have := hanti.le_of_tendsto hlim m
  simp only [hu] at this
  linarith

/-- The ratio `n!/(√(2πn)(n/e)^n)` is the Stirling sequence over `√π`. -/
lemma ratio_eq {n : ℕ} (hn : n ≠ 0) :
    (n ! : ℝ) / (√(2 * π * n) * (n / exp 1) ^ n) = _root_.Stirling.stirlingSeq n / √π := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have e2 : √(2 * π * n) * (n / exp 1) ^ n = √π * (√(2 * (n : ℝ)) * (n / exp 1) ^ n) := by
    rw [show 2 * π * (n : ℝ) = π * (2 * n) by ring, sqrt_mul (by positivity)]
    ring
  have hden : 0 < √(2 * (n : ℝ)) * (n / exp 1) ^ n := by positivity
  have e1 : (n ! : ℝ) = _root_.Stirling.stirlingSeq n * (√(2 * (n : ℝ)) * (n / exp 1) ^ n) := by
    unfold _root_.Stirling.stirlingSeq
    field_simp
  rw [e2, e1]
  field_simp

/-- CO-526 (first correction term). With `ρₙ = n!/(√(2πn)(n/e)^n)` one has
`ρₙ = 1 + 1/(12n) + O(1/n²)`: for every `n ≥ 1`, `|ρₙ - 1 - 1/(12n)| ≤ 1/n²`. -/
@[kb "kellertrotter2017" "text, p. 255"]
theorem stirling_first_correction {n : ℕ} (hn : n ≠ 0) :
    |(n ! : ℝ) / (√(2 * π * n) * (n / exp 1) ^ n) - 1 - 1 / (12 * n)| ≤ 1 / (n : ℝ) ^ 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
  set ρ := (n ! : ℝ) / (√(2 * π * n) * (n / exp 1) ^ n) with hρ
  set y : ℝ := 1 / (12 * n) with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y ≤ 1 / 12 := by
    rw [hy, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hyn : y * n = 1 / 12 := by rw [hy]; field_simp
  have hsq : 0 < √π := by positivity
  have hS := _root_.Stirling.stirlingSeq'_pos (n - 1)
  rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hn)] at hS
  -- upper bound
  have hup : ρ ≤ exp y := by
    have := (stirling_bounds hn).2
    have hd : 0 < √(2 * π * n) * (n / exp 1) ^ n := by positivity
    rw [hρ, div_le_iff₀ hd]
    rw [mul_comm]; exact this
  -- lower bound
  have hlow : exp (y - 1 / (n : ℝ) ^ 2) ≤ ρ := by
    have := log_stirlingSeq_ge hn
    rw [hρ, ratio_eq hn, le_div_iff₀ hsq]
    calc exp (y - 1 / (n : ℝ) ^ 2) * √π = exp (Real.log √π + y - 1 / (n : ℝ) ^ 2) := by
          rw [show Real.log √π + y - 1 / (n : ℝ) ^ 2 = (y - 1 / (n : ℝ) ^ 2) + Real.log √π by ring,
            exp_add, exp_log hsq]
      _ ≤ exp (Real.log (_root_.Stirling.stirlingSeq n)) := exp_le_exp.2 this
      _ = _ := exp_log hS
  have hlow' : 1 + (y - 1 / (n : ℝ) ^ 2) ≤ ρ :=
    le_trans (by linarith [Real.add_one_le_exp (y - 1 / (n : ℝ) ^ 2)]) hlow
  have hexp : exp y < 1 / (1 - y) := Real.exp_bound_div_one_sub_of_interval' hy0 (by linarith)
  have hgeo : 1 / (1 - y) ≤ 1 + y + 2 * y ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_pos hy0 hy0, pow_pos hy0 3]
  have hy2 : 2 * y ^ 2 ≤ 1 / (n : ℝ) ^ 2 := by
    have : y ^ 2 * (n : ℝ) ^ 2 = 1 / 144 := by rw [← mul_pow, hyn]; norm_num
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  rw [abs_le]
  constructor <;> linarith

end Stirling

end UndergradKB.Combinatorics
