import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import UndergradKB.Common.Attr

/-! Course layer, OpenStax Calculus Volume 2, Chapter 1 (integration). -/

namespace UndergradKB.Calculus.Course.V2C1

open Set MeasureTheory
open scoped Interval

/-- OpenStax Calculus 2:Theorem 1.6 (CA-200). Net change: the final value of a quantity is its
initial value plus the integral of its (continuous) rate of change. -/
@[kb "openstaxcalculus2016" "2:Theorem 1.6, p. 65"]
theorem net_change_theorem {Q Q' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hQ : ∀ x ∈ Icc a b, HasDerivAt Q (Q' x) x) (hQ' : ContinuousOn Q' (Icc a b)) :
    Q b = Q a + ∫ t in a..b, Q' t := by
  have h : ∫ t in a..b, Q' t = Q b - Q a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hQ x (by rwa [uIcc_of_le hab] at hx))
      (hQ'.intervalIntegrable_of_Icc hab)
  rw [h]
  ring

/-- OpenStax Calculus 2:§1.4 Basic Integration Formulas, power rule (CA-201). For a natural
exponent `n`, `∫ a..b x^n dx = (b^(n+1) - a^(n+1))/(n+1)`. -/
@[kb "openstaxcalculus2016" "2:§1.4 Basic Integration Formulas (power rule), p. 64"]
theorem integral_pow_rule (n : ℕ) (a b : ℝ) :
    ∫ x in a..b, x ^ n = (b ^ (n + 1) - a ^ (n + 1)) / (n + 1) :=
  integral_pow n

/-- OpenStax Calculus 2:§1.4 Basic Integration Formulas, power rule (CA-201). For a real
exponent `r ≠ -1`, `∫ a..b x^r dx = (b^(r+1) - a^(r+1))/(r+1)`, provided the integrand is
defined on the interval (`r > -1`, or `0` outside the interval). -/
@[kb "openstaxcalculus2016" "2:§1.4 Basic Integration Formulas (power rule), p. 64"]
theorem integral_rpow_rule {r : ℝ} {a b : ℝ} (h : -1 < r ∨ r ≠ -1 ∧ (0 : ℝ) ∉ [[a, b]]) :
    ∫ x in a..b, x ^ r = (b ^ (r + 1) - a ^ (r + 1)) / (r + 1) :=
  integral_rpow h

end UndergradKB.Calculus.Course.V2C1
