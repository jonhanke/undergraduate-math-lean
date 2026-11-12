import Mathlib.Probability.Moments.Variance
import UndergradKB.Common.Attr

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

end UndergradKB.Statistics.Course.C2
