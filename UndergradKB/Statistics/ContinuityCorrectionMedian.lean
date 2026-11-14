import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real
import UndergradKB.Common.Attr
import UndergradKB.Statistics.NormalCdf

/-!
# The continuity correction can be exact where the plain normal value is off by order `1/√n`

OpenStax *Introductory Statistics 2e*, §7.3 (row ST-069, a recorded loose end): "to get the best approximation,
add 0.5 to x or subtract 0.5 from x". The general claim (the corrected error is of smaller order than the plain
one) needs an Edgeworth expansion, which is not available. Here is a family of cases where the comparison is
exact: a fair coin tossed an odd number `n = 2r + 1` of times, at its median `r`. By symmetry
`P(X ≤ r) = 1/2` exactly; the continuity-corrected normal value `Φ((r + 1/2 - n/2)/σ) = Φ(0)` is exactly `1/2`,
while the plain normal value `Φ((r - n/2)/σ) = Φ(-1/√n)` is too small by at least `1/(6√n)`.
-/

namespace UndergradKB.Statistics

open MeasureTheory ProbabilityTheory Real Set

local notation "Φ" => cdf (gaussianReal 0 1)

/-- The standard normal density is at least `1/6` on `[-1, 1]`. -/
lemma gaussianPDFReal_ge_sixth {x : ℝ} (hx : x ^ 2 ≤ 1) : 1 / 6 ≤ gaussianPDFReal 0 1 x := by
  rw [gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  have hpi : √(2 * π) ≤ 3 := by
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith [Real.pi_lt_d2]
  have hpos : 0 < √(2 * π) := Real.sqrt_pos.2 (by positivity)
  have he : 1 / 2 ≤ Real.exp (-x ^ 2 / 2) := by
    have := Real.add_one_le_exp (-x ^ 2 / 2)
    linarith
  have hinv : 1 / 3 ≤ (√(2 * π))⁻¹ := by
    rw [one_div]
    exact inv_anti₀ hpos hpi
  calc (1 : ℝ) / 6 = 1 / 3 * (1 / 2) := by norm_num
    _ ≤ (√(2 * π))⁻¹ * Real.exp (-x ^ 2 / 2) :=
        mul_le_mul hinv he (by norm_num) (inv_nonneg.2 hpos.le)

/-- The standard normal mass of `(-t, 0]` is at least `t/6` for `0 ≤ t ≤ 1`. -/
lemma stdNormalCdf_zero_sub_neg_ge {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : t / 6 ≤ Φ 0 - Φ (-t) := by
  have hab : -t ≤ 0 := by linarith
  have h1 : Φ 0 - Φ (-t) = (gaussianReal 0 1 (Ioc (-t) 0)).toReal := by
    have := (cdf (gaussianReal 0 1)).measure_Ioc (-t) 0
    rw [measure_cdf] at this
    rw [this, ENNReal.toReal_ofReal (sub_nonneg.2 ((cdf (gaussianReal 0 1)).mono hab))]
  rw [h1, gaussianReal_apply_eq_integral 0 one_ne_zero,
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioc
      fun x _ => gaussianPDFReal_nonneg 0 1 x)]
  have hmono : ∫ _ in Ioc (-t) 0, (1 / 6 : ℝ) ≤ ∫ x in Ioc (-t) 0, gaussianPDFReal 0 1 x := by
    refine setIntegral_mono_on (integrableOn_const (by simp [Real.volume_Ioc]))
      (integrable_gaussianPDFReal 0 1).integrableOn measurableSet_Ioc fun x hx ↦ ?_
    apply gaussianPDFReal_ge_sixth
    nlinarith [hx.1, hx.2]
  refine le_trans (le_of_eq ?_) hmono
  simp [Measure.real, Real.volume_Ioc, ht0]
  ring

/-- `Φ(0) = 1/2`. -/
lemma stdNormalCdf_zero : Φ 0 = 1 / 2 := by
  have h := stdNormalCdf_neg 0
  rw [neg_zero] at h
  linarith

/-- **The continuity correction at the median of a fair coin (§7.3, ST-069).** Toss a fair coin
`n = 2r + 1` times and let `X` be the number of heads (`X ~ B(n, 1/2)`, mean `n/2`, standard deviation
`σ = √(n · 1/2 · 1/2)`). Then
* `P(X ≤ r) = ∑_{j ≤ r} C(n, j) (1/2)ʲ (1/2)ⁿ⁻ʲ = 1/2` exactly;
* the continuity-corrected normal value `Φ((r + 0.5 - n/2)/σ)` is exactly `1/2`;
* the plain normal value `Φ((r - n/2)/σ)` falls short of `P(X ≤ r)` by at least `1/(6√n)`.
So adding 0.5 turns an error of order `1/√n` into no error at all. -/
@[kb "openstaxintrostats2e" "§7.3, p. 384"]
theorem binomial_half_median_continuity_correction (r : ℕ) :
    (∑ j ∈ Finset.range (r + 1),
        ((2 * r + 1).choose j : ℝ) * (1 / 2) ^ j * (1 / 2) ^ (2 * r + 1 - j)) = 1 / 2 ∧
    Φ ((r + 1 / 2 - (2 * r + 1 : ℝ) / 2) / √((2 * r + 1 : ℝ) * (1 / 2) * (1 / 2))) = 1 / 2 ∧
    1 / (6 * √(2 * r + 1 : ℝ)) ≤
      (∑ j ∈ Finset.range (r + 1),
          ((2 * r + 1).choose j : ℝ) * (1 / 2) ^ j * (1 / 2) ^ (2 * r + 1 - j)) -
        Φ ((r - (2 * r + 1 : ℝ) / 2) / √((2 * r + 1 : ℝ) * (1 / 2) * (1 / 2))) := by
  have hsum : (∑ j ∈ Finset.range (r + 1),
      ((2 * r + 1).choose j : ℝ) * (1 / 2) ^ j * (1 / 2) ^ (2 * r + 1 - j)) = 1 / 2 := by
    have e : ∀ j ∈ Finset.range (r + 1), ((2 * r + 1).choose j : ℝ) * (1 / 2) ^ j *
        (1 / 2) ^ (2 * r + 1 - j) = ((2 * r + 1).choose j : ℝ) * (1 / 2) ^ (2 * r + 1) := by
      intro j hj
      have hj' : j ≤ 2 * r + 1 := by have := Finset.mem_range.1 hj; omega
      rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hj']
    rw [Finset.sum_congr rfl e, ← Finset.sum_mul]
    have h4 : (∑ j ∈ Finset.range (r + 1), ((2 * r + 1).choose j : ℝ)) = 4 ^ r := by
      exact_mod_cast Nat.sum_range_choose_halfway r
    rw [h4, pow_succ, pow_mul, ← mul_assoc, ← mul_pow]
    norm_num
  refine ⟨hsum, ?_, ?_⟩
  · rw [show (r : ℝ) + 1 / 2 - (2 * r + 1 : ℝ) / 2 = 0 by ring, zero_div, stdNormalCdf_zero]
  · have hn : (0 : ℝ) < 2 * r + 1 := by positivity
    have hsq : √((2 * r + 1 : ℝ) * (1 / 2) * (1 / 2)) = √(2 * r + 1 : ℝ) / 2 := by
      rw [mul_assoc, Real.sqrt_mul hn.le, show (1 / 2 : ℝ) * (1 / 2) = (1 / 2) ^ 2 by ring,
        Real.sqrt_sq (by norm_num)]
      ring
    have hs : 0 < √(2 * r + 1 : ℝ) := Real.sqrt_pos.2 hn
    have hs1 : 1 ≤ √(2 * r + 1 : ℝ) := by
      rw [Real.one_le_sqrt]
      have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      linarith
    have harg : ((r : ℝ) - (2 * r + 1 : ℝ) / 2) / √((2 * r + 1 : ℝ) * (1 / 2) * (1 / 2)) =
        -(1 / √(2 * r + 1 : ℝ)) := by
      rw [hsq]
      field_simp
      ring
    rw [hsum, harg, ← stdNormalCdf_zero]
    have h := stdNormalCdf_zero_sub_neg_ge (t := 1 / √(2 * r + 1 : ℝ)) (by positivity)
      (by rw [div_le_one hs]; exact hs1)
    calc 1 / (6 * √(2 * r + 1 : ℝ)) = 1 / √(2 * r + 1 : ℝ) / 6 := by field_simp
      _ ≤ _ := h

end UndergradKB.Statistics
