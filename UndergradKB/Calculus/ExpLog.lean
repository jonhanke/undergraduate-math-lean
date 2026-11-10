import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import UndergradKB.Common.Attr

/-! # Calculus: exponentials and logarithms to a general base

The number `e`, the natural exponential and logarithm, change of base, derivatives and integrals of `b ^ x` and
`log_b x`, the integrals of `ln`, the limit `x ^ x → 1`, and the linearization of `(1 + x) ^ n`.
Mathlib's `Real.logb b x = Real.log x / Real.log b` is the base-`b` logarithm. -/

namespace UndergradKB.Calculus

open Real Filter Topology Set intervalIntegral

/-! ## The number e and the natural exponential (CA-033, CA-034) -/

/-- OpenStax Calculus 1:§1.5 The number e (CA-033): `e = lim (1 + 1/m)^m`, where `e = exp 1`. -/
@[kb "openstaxcalculus2016" "1:§1.5 The number e, natural exponential function, p. 91"]
theorem tendsto_one_add_inv_pow_exp :
    Tendsto (fun m : ℕ => (1 + 1 / (m : ℝ)) ^ m) atTop (𝓝 (exp 1)) := by
  simpa using Real.tendsto_one_add_div_pow_exp 1

/-- OpenStax Calculus 1:§1.5 (CA-033): `e ^ x = exp x` (the real power of `e = exp 1`). -/
@[kb "openstaxcalculus2016" "1:§1.5 The number e, natural exponential function, p. 91"]
theorem exp_one_rpow_eq (x : ℝ) : (exp 1) ^ x = exp x := Real.exp_one_rpow x

/-- OpenStax Calculus 1:§3.9 Definition (natural exponential function) (CA-034): the tangent of `exp` at `0`
has slope `1`. -/
@[kb "openstaxcalculus2016" "1:§3.9 Definition (natural exponential function), p. 284"]
theorem hasDerivAt_exp_zero_slope_one : HasDerivAt exp 1 0 := by
  simpa using Real.hasDerivAt_exp 0

/-- OpenStax Calculus 1:§3.9 Definition (natural exponential function) (CA-034): among the exponentials `b ^ x`
(`b > 0`), the slope at `0` equals `1` exactly when `b = e`. -/
@[kb "openstaxcalculus2016" "1:§3.9 Definition (natural exponential function), p. 284"]
theorem hasDerivAt_rpow_zero_eq_one_iff {b : ℝ} (hb : 0 < b) :
    HasDerivAt (fun x : ℝ => b ^ x) 1 0 ↔ b = exp 1 := by
  have h : HasDerivAt (fun x : ℝ => b ^ x) (log b) 0 := by
    simpa using (Real.hasStrictDerivAt_const_rpow hb 0).hasDerivAt
  constructor
  · intro h1
    have : log b = 1 := h.unique h1
    rw [← this, exp_log hb]
  · intro hbe
    have : log b = 1 := by rw [hbe, log_exp]
    rwa [this] at h

/-- OpenStax Calculus 1:§3.9 Definition (natural logarithmic function) (CA-034): `ln` is the inverse of `exp`
(both composites). -/
@[kb "openstaxcalculus2016" "1:§3.9 Definition (natural logarithmic function), p. 284"]
theorem log_inverse_of_exp : (∀ x : ℝ, log (exp x) = x) ∧ ∀ x : ℝ, 0 < x → exp (log x) = x :=
  ⟨Real.log_exp, fun _ hx => Real.exp_log hx⟩

/-! ## Change of base (CA-041) -/

/-- OpenStax Calculus 1:§1.5 Rule: Change-of-Base Formulas (CA-041): `log_b x = ln x / ln b`. -/
@[kb "openstaxcalculus2016" "1:§1.5 Rule: Change-of-Base Formulas, p. 95"]
theorem logb_eq_log_div_log' (b x : ℝ) : logb b x = log x / log b := rfl

/-- OpenStax Calculus 1:§1.5 Rule: Change-of-Base Formulas (CA-041): `log_a x = log_b x / log_b a`
for a base `b > 0`, `b ≠ 1`. -/
@[kb "openstaxcalculus2016" "1:§1.5 Rule: Change-of-Base Formulas, p. 95"]
theorem logb_change_base {b : ℝ} (hb0 : 0 < b) (hb1 : b ≠ 1) (a x : ℝ) :
    logb a x = logb b x / logb b a := by
  have hb : log b ≠ 0 := by
    intro h
    rcases Real.log_eq_zero.mp h with h | h | h <;> [exact hb0.ne' h; exact hb1 h; linarith]
  unfold logb
  rw [div_div_div_cancel_right₀ hb]

/-- OpenStax Calculus 1:§1.5 Rule: Change-of-Base Formulas (CA-041): `b ^ x = e ^ (x ln b)` for `b > 0`. -/
@[kb "openstaxcalculus2016" "1:§1.5 Rule: Change-of-Base Formulas, p. 95"]
theorem rpow_eq_exp_mul_log {b : ℝ} (hb : 0 < b) (x : ℝ) : b ^ x = exp (x * log b) := by
  rw [Real.rpow_def_of_pos hb, mul_comm]

/-! ## Derivatives of `b ^ g` and `log_b g` (CA-126, CA-127, CA-291, CA-293) -/

/-- OpenStax Calculus 1:Theorem 3.16 (CA-126): `d/dx b ^ g(x) = b ^ g(x) · ln b · g'(x)` for `b > 0`. -/
@[kb "openstaxcalculus2016" "1:Theorem 3.16, p. 289"]
theorem hasDerivAt_rpow_comp {b : ℝ} (hb : 0 < b) {g : ℝ → ℝ} {g' x : ℝ} (hg : HasDerivAt g g' x) :
    HasDerivAt (fun y => b ^ g y) (b ^ g x * log b * g') x := by
  have h := (Real.hasStrictDerivAt_const_rpow hb (g x)).hasDerivAt.comp x hg
  exact h

/-- OpenStax Calculus 1:Theorem 6.20 (CA-291): `d/dx b ^ x = b ^ x ln b` for `b > 0`. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.20, p. 641"]
theorem hasDerivAt_rpow_self {b : ℝ} (hb : 0 < b) (x : ℝ) :
    HasDerivAt (fun y : ℝ => b ^ y) (b ^ x * log b) x := by
  simpa using hasDerivAt_rpow_comp hb (hasDerivAt_id x)

/-- OpenStax Calculus 1:Theorem 6.20 (CA-291): `b ^ x / ln b` is an antiderivative of `b ^ x`, for `b > 0`, `b ≠ 1`. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.20, p. 641"]
theorem hasDerivAt_rpow_div_log {b : ℝ} (hb : 0 < b) (hb1 : b ≠ 1) (x : ℝ) :
    HasDerivAt (fun y : ℝ => b ^ y / log b) (b ^ x) x := by
  have hl : log b ≠ 0 := by
    intro h
    rcases Real.log_eq_zero.mp h with h | h | h <;> [exact hb.ne' h; exact hb1 h; linarith]
  have := (hasDerivAt_rpow_self hb x).div_const (log b)
  rwa [mul_div_assoc, div_self hl, mul_one] at this

/-- OpenStax Calculus 1:Theorem 6.20 (CA-291): `∫ₐᵇ c ^ x dx = (c ^ b - c ^ a) / ln c`, `c > 0`, `c ≠ 1`. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.20, p. 641"]
theorem integral_rpow_base {c : ℝ} (hc : 0 < c) (hc1 : c ≠ 1) (a b : ℝ) :
    ∫ x in a..b, c ^ x = (c ^ b - c ^ a) / log c := by
  rw [integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_rpow_div_log hc hc1 x)
    (by apply Continuous.intervalIntegrable; exact Real.continuous_const_rpow hc.ne'),
    sub_div]

/-- OpenStax Calculus 1:Theorem 3.16 (CA-127): `d/dx log_b g(x) = g'(x) / (g(x) ln b)` where `g(x) ≠ 0`.
(Holds for every `b`, as `log_b = ln / ln b`; the book assumes `b > 0`, `b ≠ 1`.) -/
@[kb "openstaxcalculus2016" "1:Theorem 3.16, p. 289"]
theorem hasDerivAt_logb_comp (b : ℝ) {g : ℝ → ℝ} {g' x : ℝ} (hg : HasDerivAt g g' x) (hx : g x ≠ 0) :
    HasDerivAt (fun y => logb b (g y)) (g' / (g x * log b)) x := by
  have := (hg.log hx).div_const (log b)
  refine this.congr_deriv ?_
  rw [div_div]

/-- OpenStax Calculus 1:Theorem 6.21 (CA-293): `d/dx log_b x = 1 / (x ln b)` for `x ≠ 0`. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.21, p. 642"]
theorem hasDerivAt_logb_self (b : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (logb b) (1 / (x * log b)) x := by
  simpa using hasDerivAt_logb_comp b (hasDerivAt_id x) hx

/-! ## Integrals (CA-205, CA-207) -/

/-- OpenStax Calculus 1:§5.6 Rule (integrals of exponential functions) (CA-205): `∫ₐᵇ e ^ u du = e ^ b - e ^ a`. -/
@[kb "openstaxcalculus2016" "1:§5.6 Rule (integrals of exponential functions), p. 524"]
theorem integral_exp_eq (a b : ℝ) : ∫ u in a..b, exp u = exp b - exp a := integral_exp

/-- OpenStax Calculus 1:§5.6 Rule (integrals of exponential functions) (CA-205): `e ^ u` is an antiderivative
of `e ^ u`. -/
@[kb "openstaxcalculus2016" "1:§5.6 Rule (integrals of exponential functions), p. 524"]
theorem hasDerivAt_exp_antiderivative (u : ℝ) : HasDerivAt exp (exp u) u := Real.hasDerivAt_exp u

/-- OpenStax Calculus 1:§5.6 Rule (integrals of exponential functions) (CA-205): `a ^ u / ln a` is an
antiderivative of `a ^ u`, `a > 0`, `a ≠ 1`. -/
@[kb "openstaxcalculus2016" "1:§5.6 Rule (integrals of exponential functions), p. 524"]
theorem hasDerivAt_rpow_antiderivative {a : ℝ} (ha : 0 < a) (ha1 : a ≠ 1) (u : ℝ) :
    HasDerivAt (fun y : ℝ => a ^ y / log a) (a ^ u) u := hasDerivAt_rpow_div_log ha ha1 u

/-- OpenStax Calculus 1:§5.6 Rule (integrals of exponential functions) (CA-205): `∫ₐᵇ c ^ u du = (c^b - c^a)/ln c`. -/
@[kb "openstaxcalculus2016" "1:§5.6 Rule (integrals of exponential functions), p. 524"]
theorem integral_rpow_eq {c : ℝ} (hc : 0 < c) (hc1 : c ≠ 1) (a b : ℝ) :
    ∫ u in a..b, c ^ u = (c ^ b - c ^ a) / log c := integral_rpow_base hc hc1 a b

/-- OpenStax Calculus 1:§5.6 Rule (integration formulas involving logarithmic functions) (CA-207):
`u ln u - u` is an antiderivative of `ln u` (`u ≠ 0`). -/
@[kb "openstaxcalculus2016" "1:§5.6 Rule (integration formulas involving logarithmic functions), p. 529"]
theorem hasDerivAt_mul_log_sub {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (fun y : ℝ => y * log y - y) (log u) u := by
  have := ((hasDerivAt_id u).mul (Real.hasDerivAt_log hu)).sub (hasDerivAt_id u)
  refine this.congr_deriv ?_
  simp [hu]

/-- OpenStax Calculus 1:§5.6 (CA-207): `∫ₐᵇ ln u du = b ln b - a ln a - b + a`. -/
@[kb "openstaxcalculus2016" "1:§5.6 Rule (integration formulas involving logarithmic functions), p. 529"]
theorem integral_log_eq (a b : ℝ) : ∫ u in a..b, log u = b * log b - a * log a - b + a := integral_log

/-- OpenStax Calculus 1:§5.6 (CA-207): `(u ln u - u) / ln a` is an antiderivative of `log_a u` (`u ≠ 0`). -/
@[kb "openstaxcalculus2016" "1:§5.6 Rule (integration formulas involving logarithmic functions), p. 529"]
theorem hasDerivAt_logb_antiderivative (a : ℝ) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (fun y : ℝ => (y * log y - y) / log a) (logb a u) u :=
  (hasDerivAt_mul_log_sub hu).div_const (log a)

/-- OpenStax Calculus 1:§5.6 (CA-207): `∫ₐᵇ log_c u du = (b ln b - a ln a - b + a) / ln c`. -/
@[kb "openstaxcalculus2016" "1:§5.6 Rule (integration formulas involving logarithmic functions), p. 529"]
theorem integral_logb_eq (c a b : ℝ) :
    ∫ u in a..b, logb c u = (b * log b - a * log a - b + a) / log c := by
  show ∫ u in a..b, log u / log c = _
  rw [intervalIntegral.integral_div, integral_log]

/-! ## Limits and linearization (CA-168, CA-134) -/

/-- OpenStax Calculus 1:Example 4.44 (CA-168): `x ^ x → 1` as `x → 0+`. -/
@[kb "openstaxcalculus2016" "1:Example 4.44, p. 411"]
theorem tendsto_rpow_self_zero_right : Tendsto (fun x : ℝ => x ^ x) (𝓝[>] 0) (𝓝 1) := by
  have h : Tendsto (fun x : ℝ => x * log x) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuous_mul_log.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  have h2 := (Real.continuous_exp.tendsto 0).comp h
  rw [exp_zero] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp [Real.rpow_def_of_pos (show (0:ℝ) < x from hx), mul_comm]

/-- OpenStax Calculus 1:Example 4.7 (CA-134): the derivative of `(1 + x) ^ n` at `0` is `n`. -/
@[kb "openstaxcalculus2016" "1:Example 4.7, p. 319"]
theorem hasDerivAt_one_add_rpow (n : ℝ) : HasDerivAt (fun x : ℝ => (1 + x) ^ n) n 0 := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ n) (n * (1 + (0:ℝ)) ^ (n - 1)) (1 + 0) :=
    Real.hasDerivAt_rpow_const (Or.inl (by norm_num))
  have h2 : HasDerivAt (fun x : ℝ => 1 + x) 1 0 := (hasDerivAt_id (0:ℝ)).const_add 1
  have h := h1.comp 0 h2
  simpa [Function.comp_def] using h

/-- OpenStax Calculus 1:Example 4.7 (CA-134): `(1 + x) ^ n = 1 + n x + o(x)` as `x → 0`. -/
@[kb "openstaxcalculus2016" "1:Example 4.7, p. 319"]
theorem one_add_rpow_isLittleO (n : ℝ) :
    (fun x : ℝ => (1 + x) ^ n - (1 + n * x)) =o[𝓝 0] fun x => x := by
  have h := (hasDerivAt_iff_isLittleO_nhds_zero.mp (hasDerivAt_one_add_rpow n))
  refine h.congr_left fun x => ?_
  simp [mul_comm]; ring

end UndergradKB.Calculus
