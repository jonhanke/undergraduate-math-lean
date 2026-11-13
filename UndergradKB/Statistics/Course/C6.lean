import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import UndergradKB.Common.Attr
import UndergradKB.Statistics.EmpiricalRule

/-!
# Course layer, chapter 6 (OpenStax *Introductory Statistics 2e*): the normal distribution
-/

namespace UndergradKB.Statistics.Course.C6

open MeasureTheory ProbabilityTheory

/-- OpenStax Introductory Statistics 2e §6.1 (ST-058). The normal law with mean `μ` and variance
`v` (standard deviation `√v`) has mean `μ` and variance `v`. -/
@[kb "openstaxintrostats2e" "§6.1, p. 347"]
theorem normal_mean_variance (μ : ℝ) (v : NNReal) :
    ∫ x, x ∂gaussianReal μ v = μ ∧ Var[id; gaussianReal μ v] = v :=
  ⟨integral_id_gaussianReal, variance_id_gaussianReal⟩

/-- OpenStax Introductory Statistics 2e §6.1 (ST-058). The normal density is symmetric about
its mean: shifting the argument by `y` moves the mean by `y`. -/
@[kb "openstaxintrostats2e" "§6.1, p. 347"]
theorem normal_density_shift (μ : ℝ) (v : NNReal) (x y : ℝ) :
    gaussianPDFReal μ v (x - y) = gaussianPDFReal (μ + y) v x :=
  gaussianPDFReal_sub x y

/-- OpenStax Introductory Statistics 2e §6.1 (ST-059). Standardization: if `X ~ N(μ, σ²)` with
`σ² = v ≠ 0` then `Z = (X - μ) / σ` is standard normal. -/
@[kb "openstaxintrostats2e" "§6.1, p. 347"]
theorem standardization {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}
    {μ : ℝ} {v : NNReal} (hX : HasLaw X (gaussianReal μ v) P) (hv : v ≠ 0) :
    HasLaw (fun ω => (X ω - μ) / Real.sqrt v) (gaussianReal 0 1) P := by
  have h := gaussianReal_div_const (gaussianReal_sub_const hX μ) (Real.sqrt v)
  have e : (gaussianReal 0 1) = gaussianReal ((μ - μ) / Real.sqrt v)
      (v / NNReal.mk (Real.sqrt v ^ 2) (sq_nonneg _)) := by
    congr 1
    · simp
    · apply NNReal.eq
      have : (0 : ℝ) < v := by exact_mod_cast pos_iff_ne_zero.2 hv
      simp [Real.sq_sqrt this.le, this.ne']
  rw [e]
  exact h

/-- OpenStax Introductory Statistics 2e §6.1 (ST-059). Conversely, if `Z` is standard normal then
`X = μ + σ Z` is `N(μ, σ²)`. -/
@[kb "openstaxintrostats2e" "§6.1, p. 347"]
theorem normal_of_standard {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {Z : Ω → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) P) (μ : ℝ) (v : NNReal) :
    HasLaw (fun ω => Real.sqrt v * Z ω + μ) (gaussianReal μ v) P := by
  have h := gaussianReal_add_const (gaussianReal_const_mul hZ (Real.sqrt v)) μ
  have e : gaussianReal μ v = gaussianReal (Real.sqrt v * 0 + μ)
      (NNReal.mk (Real.sqrt v ^ 2) (sq_nonneg _) * 1) := by
    congr 1
    · simp
    · apply NNReal.eq
      simp [Real.sq_sqrt v.2]
  rw [e]
  exact h

/-- OpenStax Introductory Statistics 2e §6.2 (ST-062). Linear transformation of a random variable
with finite variance: the mean of `aX + b` is `a μ + b` and its variance is `a² σ²`
(so the standard deviation is `|a| σ`). -/
@[kb "openstaxintrostats2e" "§6.2, p. 351"]
theorem linear_transformation_mean_variance {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : MemLp X 2 P) (a b : ℝ) :
    ∫ ω, (a * X ω + b) ∂P = a * ∫ ω, X ω ∂P + b ∧
      Var[fun ω => a * X ω + b; P] = a ^ 2 * Var[X; P] := by
  have hi : Integrable X P := hX.integrable one_le_two
  refine ⟨?_, ?_⟩
  · rw [integral_add (hi.const_mul a) (integrable_const b), integral_const_mul]
    simp
  · have h1 : Var[fun ω => (a • X) ω + b; P] = Var[a • X; P] :=
      variance_add_const (hX.const_smul a).aestronglyMeasurable b
    have h2 : (fun ω => a * X ω + b) = fun ω => (a • X) ω + b := by
      funext ω; simp
    rw [h2, h1, variance_smul]

/-- OpenStax Introductory Statistics 2e §6.1 (ST-060). Empirical rule for the normal distribution:
if `X ~ N(μ, σ²)` with `σ > 0`, the probability of lying within one, two, three standard
deviations of the mean is about 0.68, 0.95, 0.997 (exactly in `(0.68, 0.69)`, `(0.95, 0.96)`,
`(0.997, 0.998)`). -/
@[kb "openstaxintrostats2e" "§6.1, p. 347"]
theorem empirical_rule_normal_distribution {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : Ω → ℝ} {μ σ : ℝ} (hσ : 0 < σ) (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) :
    ((0.68 : ℝ) < P.real {ω | |X ω - μ| < 1 * σ} ∧ P.real {ω | |X ω - μ| < 1 * σ} < 0.69) ∧
    ((0.95 : ℝ) < P.real {ω | |X ω - μ| < 2 * σ} ∧ P.real {ω | |X ω - μ| < 2 * σ} < 0.96) ∧
    ((0.997 : ℝ) < P.real {ω | |X ω - μ| < 3 * σ} ∧ P.real {ω | |X ω - μ| < 3 * σ} < 0.998) :=
  UndergradKB.Statistics.empirical_rule_normal hσ hX

end UndergradKB.Statistics.Course.C6
