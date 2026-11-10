import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Real.Pi.Leibniz
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import UndergradKB.Common.Attr

namespace UndergradKB.Calculus

open Filter Finset Topology

/-- OpenStax Calculus 2:Theorem 5.14 (CA-352). Remainder estimate for alternating series: if `b` is decreasing
with limit `0` and the partial sums `S_N = ∑_{i<N} (-1)^i b i` tend to `S`, then `|S - S_N| ≤ b N` (the first
omitted term). Only the convergence of the partial sums is assumed (not summability of `b`). -/
@[kb "openstaxcalculus2016" "2:Theorem 5.14, p. 448"]
theorem alternating_series_remainder {b : ℕ → ℝ} (hb : Antitone b) (h0 : Tendsto b atTop (𝓝 0)) {S : ℝ}
    (hS : Tendsto (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i * b i) atTop (𝓝 S)) (N : ℕ) :
    |S - ∑ i ∈ range N, (-1 : ℝ) ^ i * b i| ≤ b N := by
  have hb0 : ∀ n, 0 ≤ b n := fun n => hb.le_of_tendsto h0 n
  rcases Nat.even_or_odd' N with ⟨k, rfl | rfl⟩
  · have h1 := hb.alternating_series_le_tendsto hS k
    have h2 := hb.tendsto_le_alternating_series hS k
    rw [Finset.sum_range_succ] at h2
    rw [abs_le]
    constructor
    · simp at h2 ⊢
      linarith
    · simp at h2 ⊢
      linarith
  · have h1 := hb.alternating_series_le_tendsto hS (k + 1)
    have h2 := hb.tendsto_le_alternating_series hS k
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Finset.sum_range_succ] at h1
    rw [Odd.neg_one_pow (by simp)] at h1
    rw [abs_le]
    have := hb0 (2 * k + 1)
    constructor <;> linarith

/-- OpenStax Calculus 2:Example 5.21 (CA-355). The alternating harmonic series `∑ (-1)^n / (n+1)` converges
(its partial sums have a limit) but not absolutely. -/
@[kb "openstaxcalculus2016" "2:Example 5.21, p. 449"]
theorem alternating_harmonic_series :
    (∃ S : ℝ, Tendsto (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i / ((i : ℝ) + 1)) atTop (𝓝 S)) ∧
    ¬ Summable (fun n : ℕ => |(-1 : ℝ) ^ n / ((n : ℝ) + 1)|) := by
  constructor
  · obtain ⟨l, hl⟩ := Antitone.tendsto_alternating_series_of_tendsto_zero
      (f := fun i : ℕ => 1 / ((i : ℝ) + 1))
      (antitone_nat_of_succ_le fun n => by
        simp only [Nat.cast_add, Nat.cast_one]
        gcongr; linarith)
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact ⟨l, Tendsto.congr (fun n => Finset.sum_congr rfl fun i _ => by ring) hl⟩
  · intro h
    have h1 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
      refine h.congr fun n => ?_
      rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_nonneg (by positivity)]
    exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp (by simpa using h1))

/-- Abel's theorem applied to the alternating harmonic series: `x * ∑ (-1)^n x^n/(n+1) = log (1+x)` for `|x|<1`. -/
theorem log_one_add_eq_mul_tsum {x : ℝ} (hx : |x| < 1) :
    Real.log (1 + x) = x * ∑' n : ℕ, (-1 : ℝ) ^ n / ((n : ℝ) + 1) * x ^ n := by
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one (x := -x) (by simpa using hx)
  have hs2 := hs.mul_left (-1)
  have : (fun n : ℕ => -1 * ((-x) ^ (n + 1) / ((n : ℝ) + 1))) =
      fun n : ℕ => x * ((-1 : ℝ) ^ n / ((n : ℝ) + 1) * x ^ n) := by
    funext n
    rw [pow_succ, neg_pow x n]
    ring
  rw [this] at hs2
  have h3 := hs2.tsum_eq
  rw [tsum_mul_left] at h3
  rw [h3, sub_neg_eq_add]
  ring

/-- OpenStax Calculus 2:Example 6.10 (CA-369, CA-355). The alternating harmonic series has sum `ln 2`:
the partial sums of `∑ (-1)^n / (n+1)` tend to `Real.log 2`. -/
@[kb "openstaxcalculus2016" "2:Example 6.10 (part a), p. 499"]
theorem alternating_harmonic_sum_eq_log_two :
    Tendsto (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i / ((i : ℝ) + 1)) atTop (𝓝 (Real.log 2)) := by
  obtain ⟨l, hl⟩ := alternating_harmonic_series.1
  have abel := Real.tendsto_tsum_powerSeries_nhdsWithin_lt
    (f := fun i : ℕ => (-1 : ℝ) ^ i / ((i : ℝ) + 1)) hl
  have h2 : Tendsto (fun x : ℝ => x * ∑' n : ℕ, (-1 : ℝ) ^ n / ((n : ℝ) + 1) * x ^ n)
      (𝓝[<] 1) (𝓝 (1 * l)) :=
    (tendsto_nhdsWithin_of_tendsto_nhds (f := fun x : ℝ => x) tendsto_id).mul abel
  have h3 : Tendsto (fun x : ℝ => Real.log (1 + x)) (𝓝[<] 1) (𝓝 (Real.log 2)) := by
    have : Tendsto (fun x : ℝ => Real.log (1 + x)) (𝓝 1) (𝓝 (Real.log (1 + 1))) :=
      (tendsto_const_nhds.add tendsto_id).log (by norm_num)
    rw [show (1 : ℝ) + 1 = 2 by norm_num] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h4 : ∀ᶠ x : ℝ in 𝓝[<] 1,
      Real.log (1 + x) = x * ∑' n : ℕ, (-1 : ℝ) ^ n / ((n : ℝ) + 1) * x ^ n := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with x hx
    exact log_one_add_eq_mul_tsum (abs_lt.mpr ⟨by linarith [hx.1], hx.2⟩)
  have h5 := h3.congr' h4
  have := tendsto_nhds_unique h5 h2
  rw [this, one_mul]
  exact hl

/-- OpenStax Calculus 2:Example 6.10 (CA-369). The series for `ln (1+x)`: for `-1 < x ≤ 1` the partial sums of
`∑ (-1)^n x^(n+1)/(n+1)` tend to `Real.log (1 + x)`; at `x = -1` the series diverges (its partial sums tend to
`-∞`), so the interval of convergence is `(-1, 1]`. -/
@[kb "openstaxcalculus2016" "2:Example 6.10 (part a), p. 499"]
theorem log_one_add_series {x : ℝ} (hx1 : -1 < x) (hx2 : x ≤ 1) :
    Tendsto (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i * x ^ (i + 1) / ((i : ℝ) + 1)) atTop
      (𝓝 (Real.log (1 + x))) := by
  rcases hx2.lt_or_eq with hlt | rfl
  · have hs := Real.hasSum_pow_div_log_of_abs_lt_one (x := -x) (by rw [abs_lt]; constructor <;> linarith)
    have hs2 := hs.neg.tendsto_sum_nat
    rw [sub_neg_eq_add, neg_neg] at hs2
    refine hs2.congr fun n => Finset.sum_congr rfl fun i _ => ?_
    rw [pow_succ, neg_pow x i]
    ring
  · have := alternating_harmonic_sum_eq_log_two
    rw [show (1 : ℝ) + 1 = 2 by norm_num]
    refine this.congr fun n => Finset.sum_congr rfl fun i _ => ?_
    simp

/-- OpenStax Calculus 2:Example 6.10 (CA-369). At `x = -1` the series for `ln (1+x)` diverges: its partial sums
tend to `-∞`, so they have no finite limit. -/
@[kb "openstaxcalculus2016" "2:Example 6.10 (part a), p. 499"]
theorem log_one_add_series_diverges_at_neg_one :
    Tendsto (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i * (-1) ^ (i + 1) / ((i : ℝ) + 1)) atTop atBot ∧
    ∀ S : ℝ, ¬ Tendsto (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i * (-1) ^ (i + 1) / ((i : ℝ) + 1)) atTop (𝓝 S) := by
  have h : Tendsto (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i * (-1) ^ (i + 1) / ((i : ℝ) + 1)) atTop atBot := by
    refine (tendsto_neg_atTop_atBot.comp Real.tendsto_sum_range_one_div_nat_succ_atTop).congr
      fun n => ?_
    simp only [Function.comp, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← pow_add, show i + (i + 1) = 2 * i + 1 by ring, Odd.neg_one_pow (by simp)]
    ring
  exact ⟨h, fun S hS => not_tendsto_nhds_of_tendsto_atBot h S hS⟩

end UndergradKB.Calculus
