import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF
import UndergradKB.Common.Attr
import UndergradKB.Statistics.EmpiricalRule
import UndergradKB.Statistics.NormalCdf

/-!
# Critical values for confidence intervals (OpenStax *Introductory Statistics 2e*, §8.1)

The two-sided 90%, 95%, 99% confidence levels use the standard normal critical values
`1.645`, `1.96`, `2.576`.  We prove explicit enclosures of the central mass
`P(-z < Z < z)` using the alternating Taylor bounds of `EmpiricalRule`, and deduce the
one-sided values `Φ z` and the statements for a general normal variable.
-/

namespace UndergradKB.Statistics

open MeasureTheory ProbabilityTheory Real Set

local notation "Φ" => cdf (gaussianReal 0 1)

/-- Reduction of an enclosure of the central mass to rational Taylor sums. -/
lemma Ioo_enclosure {k a b : ℝ} (hk : 0 ≤ k) (m : ℕ) (ha : 0 < a)
    (hl : a * 2.5067 < 2 * empR (2 * m) k) (hu : 2 * empR (2 * m + 1) k < b * 2.5066) :
    a < (gaussianReal 0 1).real (Ioo (-k) k) ∧ (gaussianReal 0 1).real (Ioo (-k) k) < b := by
  rw [gaussianReal_real_Ioo_eq hk]
  have hl' := le_integral_gauss m hk
  have hu' := integral_gauss_le m hk
  have s1 := sqrt_two_pi_gt
  have s2 := sqrt_two_pi_lt
  have hp : 0 < √(2 * π) := by linarith
  have hb : 0 < b := by
    have h0 : 0 < a * 2.5067 := by positivity
    have : 0 < b * 2.5066 := by linarith
    by_contra hb
    replace hb := not_lt.mp hb
    nlinarith
  constructor
  · rw [lt_div_iff₀ hp]; nlinarith
  · rw [div_lt_iff₀ hp]; nlinarith

lemma crit_90 : (0.8999 : ℝ) < (gaussianReal 0 1).real (Ioo (-1.645) 1.645) ∧
    (gaussianReal 0 1).real (Ioo (-1.645) 1.645) < 0.9001 :=
  Ioo_enclosure (k := 1.645) (a := 0.8999) (b := 0.9001) (by norm_num) 10 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma crit_95 : (0.9499 : ℝ) < (gaussianReal 0 1).real (Ioo (-1.96) 1.96) ∧
    (gaussianReal 0 1).real (Ioo (-1.96) 1.96) < 0.9501 :=
  Ioo_enclosure (k := 1.96) (a := 0.9499) (b := 0.9501) (by norm_num) 10 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma crit_99 : (0.9899 : ℝ) < (gaussianReal 0 1).real (Ioo (-2.576) 2.576) ∧
    (gaussianReal 0 1).real (Ioo (-2.576) 2.576) < 0.9901 :=
  Ioo_enclosure (k := 2.576) (a := 0.9899) (b := 0.9901) (by norm_num) 14 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

/-- `Φ z = 1/2 + P(-z < Z < z)/2`. -/
lemma stdNormalCdf_eq_Ioo {z : ℝ} (hz : 0 ≤ z) :
    Φ z = 1 / 2 + (gaussianReal 0 1).real (Ioo (-z) z) / 2 := by
  have h1 : Φ z = Φ (-z) + (gaussianReal 0 1).real (Ioc (-z) z) := by
    rw [cdf_eq_real, cdf_eq_real, ← measureReal_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc,
      Iic_union_Ioc_eq_Iic (by linarith : -z ≤ z)]
  have h2 : (gaussianReal 0 1).real (Ioo (-z) z) = (gaussianReal 0 1).real (Ioc (-z) z) :=
    measureReal_congr Ioo_ae_eq_Ioc
  have h3 := stdNormalCdf_neg z
  linarith

/-- OpenStax Introductory Statistics 2e §8.1, the critical values for 90%, 95%, 99% confidence:
the standard normal mass within `1.645`, `1.96`, `2.576` of zero lies in `(0.8999, 0.9001)`,
`(0.9499, 0.9501)`, `(0.9899, 0.9901)` respectively (true values about `0.90003`, `0.950004`,
`0.990002`). -/
@[kb "openstaxintrostats2e" "§8.1, p. 418"]
theorem critical_values_standard_normal :
    ((0.8999 : ℝ) < (gaussianReal 0 1).real (Ioo (-1.645) 1.645) ∧
      (gaussianReal 0 1).real (Ioo (-1.645) 1.645) < 0.9001) ∧
    ((0.9499 : ℝ) < (gaussianReal 0 1).real (Ioo (-1.96) 1.96) ∧
      (gaussianReal 0 1).real (Ioo (-1.96) 1.96) < 0.9501) ∧
    ((0.9899 : ℝ) < (gaussianReal 0 1).real (Ioo (-2.576) 2.576) ∧
      (gaussianReal 0 1).real (Ioo (-2.576) 2.576) < 0.9901) :=
  ⟨crit_90, crit_95, crit_99⟩

/-- OpenStax Introductory Statistics 2e §8.1, one-sided form of the critical values: the standard
normal distribution function satisfies `Φ(1.645) ∈ (0.9499, 0.9501)`,
`Φ(1.96) ∈ (0.9749, 0.9751)`, `Φ(2.576) ∈ (0.9949, 0.9951)`. -/
@[kb "openstaxintrostats2e" "§8.1, p. 418"]
theorem critical_values_stdNormalCdf :
    ((0.9499 : ℝ) < Φ 1.645 ∧ Φ 1.645 < 0.9501) ∧
    ((0.9749 : ℝ) < Φ 1.96 ∧ Φ 1.96 < 0.9751) ∧
    ((0.9949 : ℝ) < Φ 2.576 ∧ Φ 2.576 < 0.9951) := by
  rw [stdNormalCdf_eq_Ioo (by norm_num), stdNormalCdf_eq_Ioo (by norm_num),
    stdNormalCdf_eq_Ioo (by norm_num)]
  obtain ⟨a1, a2⟩ := crit_90
  obtain ⟨b1, b2⟩ := crit_95
  obtain ⟨c1, c2⟩ := crit_99
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith

/-- OpenStax Introductory Statistics 2e §8.1, critical values for a general normal variable
`X ~ N(μ, σ²)`, `σ > 0`: the probability that `X` is within `1.645σ`, `1.96σ`, `2.576σ` of the
mean lies in `(0.8999, 0.9001)`, `(0.9499, 0.9501)`, `(0.9899, 0.9901)`. -/
@[kb "openstaxintrostats2e" "§8.1, p. 418"]
theorem critical_values_normal {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {μ σ : ℝ} (hσ : 0 < σ) (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) :
    ((0.8999 : ℝ) < P.real {ω | |X ω - μ| < 1.645 * σ} ∧
      P.real {ω | |X ω - μ| < 1.645 * σ} < 0.9001) ∧
    ((0.9499 : ℝ) < P.real {ω | |X ω - μ| < 1.96 * σ} ∧
      P.real {ω | |X ω - μ| < 1.96 * σ} < 0.9501) ∧
    ((0.9899 : ℝ) < P.real {ω | |X ω - μ| < 2.576 * σ} ∧
      P.real {ω | |X ω - μ| < 2.576 * σ} < 0.9901) := by
  rw [real_abs_sub_lt_eq hσ hX, real_abs_sub_lt_eq hσ hX, real_abs_sub_lt_eq hσ hX]
  exact critical_values_standard_normal

end UndergradKB.Statistics
