import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 6 (Stitz-Zeager): exponential and logarithmic functions -/

namespace UndergradKB.Precalculus.Course

open Real

/-- Definition 6.1: for a base `b > 0`, the exponential function `x ↦ bˣ` equals `exp (x ln b)` (PC-092). -/
@[kb "stitzzeager2013" "Definition 6.1, p. 430"]
theorem def_6_1_exponential_function (b : ℝ) (hb : 0 < b) (x : ℝ) : b ^ x = Real.exp (Real.log b * x) :=
  rpow_def_of_pos hb x

/-- Definition 6.2: for `b > 0`, `b ≠ 1`, the base-`b` logarithm is the inverse of `x ↦ bˣ`, that is
`log_b (bˣ) = x` for every real `x` and `b ^ (log_b y) = y` for `y > 0` (PC-094). -/
@[kb "stitzzeager2013" "Definition 6.2, p. 434"]
theorem def_6_2_logarithm_inverse (b : ℝ) (hb : 0 < b) (hb1 : b ≠ 1) :
    (∀ x : ℝ, Real.logb b (b ^ x) = x) ∧ (∀ y : ℝ, 0 < y → b ^ (Real.logb b y) = y) :=
  ⟨fun _ => logb_rpow hb hb1, fun _ hy => rpow_logb hb hb1 hy⟩

/-- Definition 6.3: the common logarithm is the base-`10` logarithm and the natural logarithm is the base-`e`
logarithm, `ln x = log_e x` (PC-095). -/
@[kb "stitzzeager2013" "Definition 6.3, p. 434"]
theorem def_6_3_common_and_natural_log (x : ℝ) :
    Real.logb 10 x = Real.log x / Real.log 10 ∧ Real.logb (Real.exp 1) x = Real.log x := by
  refine ⟨rfl, ?_⟩
  rw [Real.logb, Real.log_exp, div_one]

/-- Theorem 6.3 (inverse properties): for `b > 0`, `b ≠ 1`, `y > 0`: `bᵃ = y` iff `log_b y = a`; also
`log_b (bˣ) = x` for all `x`, and `b ^ (log_b x) = x` for `x > 0` (PC-097). -/
@[kb "stitzzeager2013" "Theorem 6.3, p. 449"]
theorem thm_6_3_log_exp_inverse_properties (b : ℝ) (hb : 0 < b) (hb1 : b ≠ 1) :
    (∀ a y : ℝ, 0 < y → (b ^ a = y ↔ Real.logb b y = a)) ∧
    (∀ x : ℝ, Real.logb b (b ^ x) = x) ∧ (∀ x : ℝ, 0 < x → b ^ (Real.logb b x) = x) := by
  refine ⟨fun a y hy => ?_, fun x => logb_rpow hb hb1, fun x hx => rpow_logb hb hb1 hx⟩
  rw [eq_comm, logb_eq_iff_rpow_eq hb hb1 hy]
  exact eq_comm

/-- Theorem 6.5 (exponent laws): for `b > 0`, `b^(u+w) = bᵘ bʷ`, `b^(u-w) = bᵘ / bʷ`, `(bᵘ)ʷ = b^(uw)` (PC-099). -/
@[kb "stitzzeager2013" "Theorem 6.5, p. 449"]
theorem thm_6_5_exponent_laws (b : ℝ) (hb : 0 < b) (u w : ℝ) :
    b ^ (u + w) = b ^ u * b ^ w ∧ b ^ (u - w) = b ^ u / b ^ w ∧ (b ^ u) ^ w = b ^ (u * w) :=
  ⟨rpow_add hb u w, rpow_sub hb u w, (rpow_mul hb.le u w).symm⟩

/-- Theorem 6.6 (log laws): for `u, w > 0`, `b > 0`, `b ≠ 1` (the base hypotheses are not needed in Mathlib):
`log_b (uw) = log_b u + log_b w`, `log_b (u/w) = log_b u - log_b w`, `log_b (uʷ) = w log_b u` (PC-100). -/
@[kb "stitzzeager2013" "Theorem 6.6, p. 450"]
theorem thm_6_6_log_laws (b u w : ℝ) (hu : 0 < u) (hw : 0 < w) :
    Real.logb b (u * w) = Real.logb b u + Real.logb b w ∧
    Real.logb b (u / w) = Real.logb b u - Real.logb b w ∧
    Real.logb b (u ^ w) = w * Real.logb b u :=
  ⟨logb_mul hu.ne' hw.ne', logb_div hu.ne' hw.ne', logb_rpow_eq_mul_logb_of_pos hu⟩

end UndergradKB.Precalculus.Course
