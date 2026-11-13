import Mathlib.Probability.Moments.Variance
import UndergradKB.Common.Attr
import UndergradKB.Statistics.EmpiricalRule
import UndergradKB.Statistics.Remarks
import UndergradKB.Statistics.SampleMoments

/-!
# Course layer, chapter 2 (OpenStax *Introductory Statistics 2e*)
-/

namespace UndergradKB.Statistics.Course.C2

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- OpenStax Introductory Statistics 2e §2.7 (ST-015). Chebyshev's inequality: for a random
variable with finite variance `σ² > 0` and `k > 0`, the probability of being at least `k`
standard deviations from the mean is at most `1 / k²`. -/
@[kb "openstaxintrostats2e" "§2.7, p. 118"]
theorem chebyshev_inequality {X : Ω → ℝ} (hX : MemLp X 2 P) (hv : 0 < Var[X; P]) {k : ℝ}
    (hk : 0 < k) :
    P {ω | k * Real.sqrt Var[X; P] ≤ |X ω - ∫ x, X x ∂P|} ≤ ENNReal.ofReal (1 / k ^ 2) := by
  have hs : 0 < Real.sqrt Var[X; P] := Real.sqrt_pos.2 hv
  have h := meas_ge_le_variance_div_sq hX (mul_pos hk hs)
  have e : Var[X; P] / (k * Real.sqrt Var[X; P]) ^ 2 = 1 / k ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hv.le]
    field_simp
  rwa [e] at h

omit [IsProbabilityMeasure P] in
/-- OpenStax Introductory Statistics 2e §2.7 (ST-016). Empirical rule: for bell-shaped data (a
normal population with mean `μ` and standard deviation `σ > 0`), about 68%, 95% and 99.7% of the
values lie within one, two and three standard deviations of the mean (the exact probabilities lie
in `(0.68, 0.69)`, `(0.95, 0.96)` and `(0.997, 0.998)`). -/
@[kb "openstaxintrostats2e" "§2.7, p. 118"]
theorem empirical_rule_bell_shaped_data {X : Ω → ℝ} {μ σ : ℝ} (hσ : 0 < σ)
    (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) :
    ((0.68 : ℝ) < P.real {ω | X ω ∈ Set.Ioo (μ - σ) (μ + σ)} ∧
      P.real {ω | X ω ∈ Set.Ioo (μ - σ) (μ + σ)} < 0.69) ∧
    ((0.95 : ℝ) < P.real {ω | X ω ∈ Set.Ioo (μ - 2 * σ) (μ + 2 * σ)} ∧
      P.real {ω | X ω ∈ Set.Ioo (μ - 2 * σ) (μ + 2 * σ)} < 0.96) ∧
    ((0.997 : ℝ) < P.real {ω | X ω ∈ Set.Ioo (μ - 3 * σ) (μ + 3 * σ)} ∧
      P.real {ω | X ω ∈ Set.Ioo (μ - 3 * σ) (μ + 3 * σ)} < 0.998) :=
  UndergradKB.Statistics.empirical_rule_normal_population hσ hX

/-- OpenStax Introductory Statistics 2e §2.5 (ST-008). Grouped data: if every datum `x i` lies within
`h` of the midpoint `m i` of its class, the mean of the data differs from the mean of the midpoints
by at most `h`. -/
@[kb "openstaxintrostats2e" "§2.5, p. 109"]
theorem grouped_mean_error_bound {n : ℕ} (x m : Fin n → ℝ) (h : ℝ) (hn : 1 ≤ n)
    (hxm : ∀ i, |x i - m i| ≤ h) :
    |UndergradKB.Statistics.mean x - UndergradKB.Statistics.mean m| ≤ h :=
  UndergradKB.Statistics.abs_mean_sub_mean_midpoints_le x m h hn hxm

/-- OpenStax Introductory Statistics 2e §2.5 (ST-008). Grouped data: replacing each datum by the
midpoint of its class (`cls i` is the class of datum `i`, `mid c` the midpoint of class `c`), the
mean of the midpoints is the frequency-weighted midpoint `∑ f_c · mid_c / ∑ f_c`, where `f_c` is
the number of data in class `c`. -/
@[kb "openstaxintrostats2e" "§2.5, p. 109"]
theorem grouped_mean_is_frequency_weighted_midpoint {n : ℕ} {κ : Type*} [Fintype κ]
    [DecidableEq κ] (cls : Fin n → κ) (mid : κ → ℝ) :
    UndergradKB.Statistics.mean (fun i => mid (cls i)) =
      (∑ c, ((Finset.univ.filter fun i => cls i = c).card : ℝ) * mid c) /
        ∑ c, ((Finset.univ.filter fun i => cls i = c).card : ℝ) :=
  UndergradKB.Statistics.mean_midpoints_eq_weighted cls mid

/-- OpenStax Introductory Statistics 2e §2.7 (ST-012). The sample variance (divisor `n - 1`) is an
unbiased estimator of `σ²`: for `n ≥ 2` pairwise independent square-integrable observations with
common mean `μ` and common variance `σ²`, the expected value of `s²` is `σ²`. -/
@[kb "openstaxintrostats2e" "§2.7, p. 118"]
theorem sample_variance_is_unbiased {n : ℕ} (hn : 2 ≤ n) {X : Fin n → Ω → ℝ} {μ σ : ℝ}
    (hL : ∀ i, MemLp (X i) 2 P) (hμ : ∀ i, P[X i] = μ) (hσ : ∀ i, Var[X i; P] = σ ^ 2)
    (hind : Pairwise fun i j ↦ IndepFun (X i) (X j) P) :
    ∫ ω, UndergradKB.Statistics.sampleVariance (fun i ↦ X i ω) ∂P = σ ^ 2 :=
  UndergradKB.Statistics.integral_sampleVariance hn hL hμ hσ hind

/-- OpenStax Introductory Statistics 2e §2.7 (ST-012). Dividing by `n` instead of `n - 1` gives a
biased estimator: under the same hypotheses the expected value of the divisor-`n` variance of the
data is `(n - 1)/n · σ²`. -/
@[kb "openstaxintrostats2e" "§2.7, p. 118"]
theorem divisor_n_variance_is_biased {n : ℕ} (hn : 2 ≤ n) {X : Fin n → Ω → ℝ} {μ σ : ℝ}
    (hL : ∀ i, MemLp (X i) 2 P) (hμ : ∀ i, P[X i] = μ) (hσ : ∀ i, Var[X i; P] = σ ^ 2)
    (hind : Pairwise fun i j ↦ IndepFun (X i) (X j) P) :
    ∫ ω, UndergradKB.Statistics.populationVariance (fun i ↦ X i ω) ∂P =
      ((n : ℝ) - 1) / n * σ ^ 2 :=
  UndergradKB.Statistics.integral_populationVariance hn hL hμ hσ hind

end UndergradKB.Statistics.Course.C2
