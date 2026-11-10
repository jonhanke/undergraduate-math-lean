import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import UndergradKB.Common.Attr
import UndergradKB.Calculus.Defs
import UndergradKB.Calculus.Trig
import UndergradKB.Calculus.TrigCalculus

/-! # Calculus: integrals involving trigonometric and inverse trigonometric functions

Antiderivatives (as `HasDerivAt` statements) and definite integrals of the inverse-trigonometric rules, of `tan`, `sec`
and their powers (reduction formulas), the product-to-sum rules, and the identities behind the trigonometric
substitutions. -/

namespace UndergradKB.Calculus

open Real Set

/-! ## Integrals giving inverse trigonometric functions -/

/-- `u ↦ u / a` has derivative `1 / a`. -/
private theorem hasDerivAt_div_const' (a u : ℝ) : HasDerivAt (fun u : ℝ => u / a) (1 / a) u :=
  (hasDerivAt_id' u).div_const a

/-- OpenStax Calculus 1:§5.7 Rule, formula 1 (CA-208). For `a > 0` and `|u| < a`, the function
`u ↦ arcsin (u / a)` has derivative `1 / √(a² - u²)`. -/
@[kb "openstaxcalculus2016" "1:§5.7 Rule (inverse trigonometric integrals, formula 1), p. 534"]
theorem hasDerivAt_arcsin_div {a u : ℝ} (ha : 0 < a) (hu : |u| < a) :
    HasDerivAt (fun u => Real.arcsin (u / a)) (1 / √(a ^ 2 - u ^ 2)) u := by
  obtain ⟨hu1, hu2⟩ := abs_lt.mp hu
  have h1 : u / a ≠ -1 := by
    intro h; rw [div_eq_iff ha.ne'] at h; linarith
  have h2 : u / a ≠ 1 := by
    intro h; rw [div_eq_iff ha.ne'] at h; linarith
  refine ((Real.hasDerivAt_arcsin h1 h2).comp u (hasDerivAt_div_const' a u)).congr_deriv ?_
  have hpos : 0 < a ^ 2 - u ^ 2 := by nlinarith
  have e : 1 - (u / a) ^ 2 = (a ^ 2 - u ^ 2) / a ^ 2 := by field_simp
  rw [e, Real.sqrt_div hpos.le, Real.sqrt_sq ha.le]
  have hs : 0 < √(a ^ 2 - u ^ 2) := Real.sqrt_pos.2 hpos
  field_simp

/-- OpenStax Calculus 1:§5.7 Rule, formula 1 (CA-208). For `a > 0`, `|b| < a`, `|c| < a`:
`∫_b^c dx / √(a² - x²) = arcsin (c/a) - arcsin (b/a)`. -/
@[kb "openstaxcalculus2016" "1:§5.7 Rule (inverse trigonometric integrals, formula 1), p. 534"]
theorem integral_inv_sqrt_sq_sub {a b c : ℝ} (ha : 0 < a) (hb : |b| < a) (hc : |c| < a) :
    ∫ x in b..c, 1 / √(a ^ 2 - x ^ 2) = Real.arcsin (c / a) - Real.arcsin (b / a) := by
  have hmem : ∀ x ∈ Set.uIcc b c, |x| < a := by
    intro x hx
    obtain ⟨hb1, hb2⟩ := abs_lt.mp hb
    obtain ⟨hc1, hc2⟩ := abs_lt.mp hc
    rw [abs_lt]
    rcases Set.mem_uIcc.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun u => Real.arcsin (u / a)) (fun x hx => hasDerivAt_arcsin_div ha (hmem x hx)) ?_
  apply ContinuousOn.intervalIntegrable
  refine continuousOn_const.div (Continuous.continuousOn (by fun_prop)) (fun x hx => ?_)
  obtain ⟨h1, h2⟩ := abs_lt.mp (hmem x hx)
  exact (Real.sqrt_pos.2 (by nlinarith)).ne'

/-- OpenStax Calculus 1:§5.7 Rule, formula 2 (CA-209). For `a ≠ 0`, `u ↦ (1/a) arctan (u/a)` has
derivative `1 / (a² + u²)`. -/
@[kb "openstaxcalculus2016" "1:§5.7 Rule (inverse trigonometric integrals, formula 2), p. 534"]
theorem hasDerivAt_arctan_div {a : ℝ} (ha : a ≠ 0) (u : ℝ) :
    HasDerivAt (fun u => (1 / a) * Real.arctan (u / a)) (1 / (a ^ 2 + u ^ 2)) u := by
  have h := ((Real.hasDerivAt_arctan (u / a)).comp u (hasDerivAt_div_const' a u)).const_mul (1 / a)
  refine h.congr_deriv ?_
  have : 0 < a ^ 2 := by positivity
  have : 0 < a ^ 2 + u ^ 2 := by positivity
  field_simp

/-- OpenStax Calculus 1:§5.7 Rule, formula 2 (CA-209). For `a ≠ 0`:
`∫_b^c dx / (a² + x²) = (1/a) arctan (c/a) - (1/a) arctan (b/a)`. -/
@[kb "openstaxcalculus2016" "1:§5.7 Rule (inverse trigonometric integrals, formula 2), p. 534"]
theorem integral_inv_sq_add_sq' {a : ℝ} (ha : a ≠ 0) (b c : ℝ) :
    ∫ x in b..c, 1 / (a ^ 2 + x ^ 2) =
      (1 / a) * Real.arctan (c / a) - (1 / a) * Real.arctan (b / a) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun u => (1 / a) * Real.arctan (u / a)) (fun x _ => hasDerivAt_arctan_div ha x) ?_
  apply Continuous.intervalIntegrable
  have : 0 < a ^ 2 := by positivity
  have hc : Continuous fun x : ℝ => a ^ 2 + x ^ 2 := by fun_prop
  exact continuous_const.div hc (fun x => by show a ^ 2 + x ^ 2 ≠ 0; positivity)

/-- `√((w/a)² - 1) = √(w² - a²) / a` for `a > 0`, `a² ≤ w²`. -/
theorem sqrt_div_sq_sub_one {w a : ℝ} (ha : 0 < a) (h : a ^ 2 ≤ w ^ 2) :
    √((w / a) ^ 2 - 1) = √(w ^ 2 - a ^ 2) / a := by
  have e : (w / a) ^ 2 - 1 = (w ^ 2 - a ^ 2) / a ^ 2 := by field_simp
  rw [e, Real.sqrt_div (by linarith), Real.sqrt_sq ha.le]

/-- OpenStax Calculus 1:§5.7 Rule, formula 3 (CA-210). For `a > 0` and `|u| > a`, the function
`u ↦ (1/a) arcsec (|u|/a)` has derivative `1 / (u √(u² - a²))`. -/
@[kb "openstaxcalculus2016" "1:§5.7 Rule (inverse trigonometric integrals, formula 3), p. 534"]
theorem hasDerivAt_arcsec_div {a u : ℝ} (ha : 0 < a) (hu : a < |u|) :
    HasDerivAt (fun u => (1 / a) * arcsec (|u| / a)) (1 / (u * √(u ^ 2 - a ^ 2))) u := by
  have hu2 : a ^ 2 < u ^ 2 := by nlinarith [sq_abs u, abs_nonneg u]
  have hs : 0 < √(u ^ 2 - a ^ 2) := Real.sqrt_pos.2 (by linarith)
  rcases lt_or_gt_of_ne (show u ≠ 0 by rintro rfl; simp at hu; linarith) with hneg | hpos
  · -- u < 0
    have hy : 1 < |-u / a| := by
      rw [abs_of_pos (by have := neg_pos.2 hneg; positivity), lt_div_iff₀ ha]
      rw [abs_of_neg hneg] at hu; linarith
    have hd : HasDerivAt (fun u : ℝ => -u / a) (-1 / a) u := (hasDerivAt_neg u).div_const a
    have h := ((hasDerivAt_arcsec hy).comp u hd).const_mul (1 / a)
    have e : (fun u : ℝ => (1 / a) * arcsec (|u| / a)) =ᶠ[nhds u]
        (fun u => (1 / a) * (arcsec ∘ fun u : ℝ => -u / a) u) := by
      filter_upwards [Iio_mem_nhds hneg] with y hy
      simp only [Function.comp, abs_of_neg (show y < 0 from hy), neg_div]
    refine (h.congr_of_eventuallyEq e).congr_deriv ?_
    have hpos' : 0 < -u / a := by have := neg_pos.2 hneg; positivity
    rw [abs_of_pos hpos', neg_div, neg_sq]
    rw [show (u / a) ^ 2 - 1 = (u ^ 2 - a ^ 2) / a ^ 2 by field_simp,
      Real.sqrt_div (by linarith), Real.sqrt_sq ha.le]
    field_simp
  · -- u > 0
    have hy : 1 < |u / a| := by
      rw [abs_of_pos (by positivity), lt_div_iff₀ ha]
      rw [abs_of_pos hpos] at hu; linarith
    have h := ((hasDerivAt_arcsec hy).comp u (hasDerivAt_div_const' a u)).const_mul (1 / a)
    have e : (fun u : ℝ => (1 / a) * arcsec (|u| / a)) =ᶠ[nhds u]
        (fun u => (1 / a) * (arcsec ∘ fun u : ℝ => u / a) u) := by
      filter_upwards [Ioi_mem_nhds hpos] with y hy
      simp only [Function.comp, abs_of_pos (show 0 < y from hy)]
    refine (h.congr_of_eventuallyEq e).congr_deriv ?_
    have hpos' : 0 < u / a := by positivity
    rw [abs_of_pos hpos']
    rw [show (u / a) ^ 2 - 1 = (u ^ 2 - a ^ 2) / a ^ 2 by field_simp,
      Real.sqrt_div (by linarith), Real.sqrt_sq ha.le]
    field_simp

/-- OpenStax Calculus 1:§5.7 Rule, formula 3 (CA-210). For `a > 0` and an interval `[b, c]` on which
`|x| > a`: `∫_b^c dx / (x √(x² - a²)) = (1/a) arcsec (|c|/a) - (1/a) arcsec (|b|/a)`. -/
@[kb "openstaxcalculus2016" "1:§5.7 Rule (inverse trigonometric integrals, formula 3), p. 534"]
theorem integral_inv_mul_sqrt_sq_sub {a b c : ℝ} (ha : 0 < a) (hI : ∀ x ∈ Set.uIcc b c, a < |x|) :
    ∫ x in b..c, 1 / (x * √(x ^ 2 - a ^ 2)) =
      (1 / a) * arcsec (|c| / a) - (1 / a) * arcsec (|b| / a) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun u => (1 / a) * arcsec (|u| / a)) (fun x hx => hasDerivAt_arcsec_div ha (hI x hx)) ?_
  apply ContinuousOn.intervalIntegrable
  have hc : Continuous fun x : ℝ => x * √(x ^ 2 - a ^ 2) := by fun_prop
  refine continuousOn_const.div hc.continuousOn (fun x hx => ?_)
  have hx2 : a ^ 2 < x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x, hI x hx]
  have hx0 : x ≠ 0 := by
    rintro rfl; have := hI 0 (by simpa using hx); simp at this; linarith
  exact mul_ne_zero hx0 (Real.sqrt_pos.2 (by linarith)).ne'

/-! ## Antiderivatives of tan and sec -/

/-- OpenStax Calculus 2:§3.2 recalled integrals (CA-218). `(ln |sec x|)' = tan x` where `cos x ≠ 0`. -/
@[kb "openstaxcalculus2016" "2:§3.2 Recalled integrals of tan and sec, p. 253"]
theorem hasDerivAt_log_abs_sec {x : ℝ} (h : Real.cos x ≠ 0) :
    HasDerivAt (fun x => Real.log |sec x|) (Real.tan x) x := by
  have e : (fun x => Real.log |sec x|) = fun x => Real.log (sec x) := funext fun y => Real.log_abs _
  rw [e]
  have hs : sec x ≠ 0 := one_div_ne_zero h
  exact ((hasDerivAt_sec h).log hs).congr_deriv (mul_div_cancel_left₀ _ hs)

/-- `sec x + tan x ≠ 0` where `cos x ≠ 0`. -/
theorem sec_add_tan_ne_zero {x : ℝ} (h : Real.cos x ≠ 0) : sec x + Real.tan x ≠ 0 := by
  have h1 : 1 + Real.sin x ≠ 0 := by
    intro h0
    have hs : Real.sin x = -1 := by linarith
    have := Real.sin_sq_add_cos_sq x
    rw [hs] at this
    exact h (by nlinarith)
  unfold sec
  rw [Real.tan_eq_sin_div_cos, ← add_div]
  exact div_ne_zero h1 h

/-- OpenStax Calculus 2:§3.2 recalled integrals (CA-218). `(ln |sec x + tan x|)' = sec x` where
`cos x ≠ 0`. -/
@[kb "openstaxcalculus2016" "2:§3.2 Recalled integrals of tan and sec, p. 253"]
theorem hasDerivAt_log_abs_sec_add_tan {x : ℝ} (h : Real.cos x ≠ 0) :
    HasDerivAt (fun x => Real.log |sec x + Real.tan x|) (sec x) x := by
  have e : (fun x => Real.log |sec x + Real.tan x|) = fun x => Real.log (sec x + Real.tan x) :=
    funext fun y => Real.log_abs _
  rw [e]
  have hne := sec_add_tan_ne_zero h
  refine (((hasDerivAt_sec h).add (hasDerivAt_tan_sec_sq h)).log hne).congr_deriv ?_
  show (sec x * Real.tan x + sec x ^ 2) / (sec x + Real.tan x) = sec x
  rw [div_eq_iff hne]
  ring

/-- OpenStax Calculus 2:§3.2 recalled integrals (CA-218). `∫_b^c tan x dx = ln|sec c| - ln|sec b|`
when `cos ≠ 0` on `[b, c]`. -/
@[kb "openstaxcalculus2016" "2:§3.2 Recalled integrals of tan and sec, p. 253"]
theorem integral_tan {b c : ℝ} (hI : ∀ x ∈ Set.uIcc b c, Real.cos x ≠ 0) :
    ∫ x in b..c, Real.tan x = Real.log |sec c| - Real.log |sec b| := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => Real.log |sec x|)
    (fun x hx => hasDerivAt_log_abs_sec (hI x hx)) ?_
  exact (continuousOn_tan'.mono fun x hx => hI x hx).intervalIntegrable

/-- OpenStax Calculus 2:§3.2 recalled integrals (CA-218). `∫_b^c sec x dx =
ln|sec c + tan c| - ln|sec b + tan b|` when `cos ≠ 0` on `[b, c]`. -/
@[kb "openstaxcalculus2016" "2:§3.2 Recalled integrals of tan and sec, p. 253"]
theorem integral_sec {b c : ℝ} (hI : ∀ x ∈ Set.uIcc b c, Real.cos x ≠ 0) :
    ∫ x in b..c, sec x =
      Real.log |sec c + Real.tan c| - Real.log |sec b + Real.tan b| := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x => Real.log |sec x + Real.tan x|)
    (fun x hx => hasDerivAt_log_abs_sec_add_tan (hI x hx)) ?_
  exact (continuousOn_sec.mono fun x hx => hI x hx).intervalIntegrable

/-- OpenStax Calculus 2:§3.2 recalled integrals (CA-218). `∫_b^c sec² x dx = tan c - tan b`
when `cos ≠ 0` on `[b, c]`. -/
@[kb "openstaxcalculus2016" "2:§3.2 Recalled integrals of tan and sec, p. 253"]
theorem integral_sec_sq {b c : ℝ} (hI : ∀ x ∈ Set.uIcc b c, Real.cos x ≠ 0) :
    ∫ x in b..c, sec x ^ 2 = Real.tan c - Real.tan b := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := Real.tan)
    (fun x hx => hasDerivAt_tan_sec_sq (hI x hx)) ?_
  exact ((continuousOn_sec.mono fun x hx => hI x hx).pow 2).intervalIntegrable

/-- OpenStax Calculus 2:§3.2 recalled integrals (CA-218). `∫_b^c sec x tan x dx = sec c - sec b`
when `cos ≠ 0` on `[b, c]`. -/
@[kb "openstaxcalculus2016" "2:§3.2 Recalled integrals of tan and sec, p. 253"]
theorem integral_sec_mul_tan {b c : ℝ} (hI : ∀ x ∈ Set.uIcc b c, Real.cos x ≠ 0) :
    ∫ x in b..c, sec x * Real.tan x = sec c - sec b := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := sec)
    (fun x hx => hasDerivAt_sec (hI x hx)) ?_
  exact ((continuousOn_sec.mono fun x hx => hI x hx).mul
    (continuousOn_tan'.mono fun x hx => hI x hx)).intervalIntegrable

/-! ## Powers of secant and tangent -/

/-- OpenStax Calculus 2:Example 3.18 (CA-220). The antiderivative of `sec³`:
`((sec x tan x + ln|sec x + tan x|) / 2)' = sec³ x` where `cos x ≠ 0`. -/
@[kb "openstaxcalculus2016" "2:Example 3.18, p. 255"]
theorem hasDerivAt_sec_cube {x : ℝ} (h : Real.cos x ≠ 0) :
    HasDerivAt (fun x => (sec x * Real.tan x + Real.log |sec x + Real.tan x|) / 2)
      (sec x ^ 3) x := by
  have h1 := (((hasDerivAt_sec h).mul (hasDerivAt_tan_sec_sq h)).add
    (hasDerivAt_log_abs_sec_add_tan h)).div_const 2
  refine h1.congr_deriv ?_
  linear_combination (sec x / 2) * one_add_tan_sq h

/-- OpenStax Calculus 2:Example 3.18 (CA-220). `∫_b^c sec³ x dx =
(sec c tan c + ln|sec c + tan c| - sec b tan b - ln|sec b + tan b|) / 2` when `cos ≠ 0` on `[b, c]`. -/
@[kb "openstaxcalculus2016" "2:Example 3.18, p. 255"]
theorem integral_sec_cube {b c : ℝ} (hI : ∀ x ∈ Set.uIcc b c, Real.cos x ≠ 0) :
    ∫ x in b..c, sec x ^ 3 =
      (sec c * Real.tan c + Real.log |sec c + Real.tan c|) / 2 -
        (sec b * Real.tan b + Real.log |sec b + Real.tan b|) / 2 := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x => (sec x * Real.tan x + Real.log |sec x + Real.tan x|) / 2)
    (fun x hx => hasDerivAt_sec_cube (hI x hx)) ?_
  exact ((continuousOn_sec.mono fun x hx => hI x hx).pow 3).intervalIntegrable

/-- Derivative of `sec^m tan`: `(m+1) sec^(m+2) - m sec^m` where `cos x ≠ 0`. -/
theorem hasDerivAt_sec_pow_mul_tan (m : ℕ) {x : ℝ} (h : Real.cos x ≠ 0) :
    HasDerivAt (fun x => sec x ^ m * Real.tan x)
      ((m + 1) * sec x ^ (m + 2) - m * sec x ^ m) x := by
  cases m with
  | zero =>
    simpa using hasDerivAt_tan_sec_sq h
  | succ k =>
    refine (((hasDerivAt_sec h).pow (k + 1)).mul (hasDerivAt_tan_sec_sq h)).congr_deriv ?_
    simp only [Nat.add_sub_cancel, Pi.pow_apply]
    push_cast
    linear_combination (((k : ℝ) + 1) * sec x ^ (k + 1)) * one_add_tan_sq h

/-- OpenStax Calculus 2:Eq. 3.6 (CA-221). Reduction formula for `sec`, for `cos ≠ 0` on `[b, c]` and
`m ∈ ℕ` (the book's `n = m + 2`):
`(m+1) ∫ sec^(m+2) = [sec^m tan]_b^c + m ∫ sec^m`. -/
@[kb "openstaxcalculus2016" "2:§3.2 Rule (reduction formula for sec^n, Eq. 3.6), p. 256"]
theorem integral_sec_pow_reduction (m : ℕ) {b c : ℝ} (hI : ∀ x ∈ Set.uIcc b c, Real.cos x ≠ 0) :
    ((m : ℝ) + 1) * ∫ x in b..c, sec x ^ (m + 2) =
      (sec c ^ m * Real.tan c - sec b ^ m * Real.tan b) + m * ∫ x in b..c, sec x ^ m := by
  have hsec : ContinuousOn sec (Set.uIcc b c) := continuousOn_sec.mono fun x hx => hI x hx
  have i1 : IntervalIntegrable (fun x => sec x ^ (m + 2)) MeasureTheory.volume b c :=
    (hsec.pow _).intervalIntegrable
  have i2 : IntervalIntegrable (fun x => sec x ^ m) MeasureTheory.volume b c :=
    (hsec.pow _).intervalIntegrable
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x => sec x ^ m * Real.tan x)
    (f' := fun x => ((m : ℝ) + 1) * sec x ^ (m + 2) - m * sec x ^ m)
    (fun x hx => hasDerivAt_sec_pow_mul_tan m (hI x hx))
    ((i1.const_mul _).sub (i2.const_mul _))
  rw [intervalIntegral.integral_sub (i1.const_mul _) (i2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hF
  linarith

/-- OpenStax Calculus 2:Eq. 3.6 (CA-221), solved form for `n ≥ 2` (`m = n - 2`):
`∫ sec^(m+2) = ([sec^m tan]_b^c + m ∫ sec^m) / (m+1)`. -/
@[kb "openstaxcalculus2016" "2:§3.2 Rule (reduction formula for sec^n, Eq. 3.6), p. 256"]
theorem integral_sec_pow_reduction' (m : ℕ) {b c : ℝ} (hI : ∀ x ∈ Set.uIcc b c, Real.cos x ≠ 0) :
    ∫ x in b..c, sec x ^ (m + 2) =
      ((sec c ^ m * Real.tan c - sec b ^ m * Real.tan b) + m * ∫ x in b..c, sec x ^ m) / (m + 1) := by
  rw [eq_div_iff (by positivity), mul_comm]
  exact integral_sec_pow_reduction m hI

/-- Derivative of `tan^(m+1)`: `(m+1)(tan^m + tan^(m+2))` where `cos x ≠ 0`. -/
theorem hasDerivAt_tan_pow_succ (m : ℕ) {x : ℝ} (h : Real.cos x ≠ 0) :
    HasDerivAt (fun x => Real.tan x ^ (m + 1))
      (((m : ℝ) + 1) * (Real.tan x ^ m + Real.tan x ^ (m + 2))) x := by
  refine ((hasDerivAt_tan_sec_sq h).pow (m + 1)).congr_deriv ?_
  rw [← one_add_tan_sq h]
  simp only [Nat.add_sub_cancel]
  push_cast
  ring

/-- OpenStax Calculus 2:Eq. 3.7 (CA-222). Reduction formula for `tan`, for `cos ≠ 0` on `[b, c]`
(book's `n = m + 2`): `∫ tan^(m+2) = [tan^(m+1)/(m+1)]_b^c - ∫ tan^m`. -/
@[kb "openstaxcalculus2016" "2:§3.2 Rule (reduction formula for tan^n, Eq. 3.7), p. 256"]
theorem integral_tan_pow_reduction (m : ℕ) {b c : ℝ} (hI : ∀ x ∈ Set.uIcc b c, Real.cos x ≠ 0) :
    ∫ x in b..c, Real.tan x ^ (m + 2) =
      (Real.tan c ^ (m + 1) / (m + 1) - Real.tan b ^ (m + 1) / (m + 1)) -
        ∫ x in b..c, Real.tan x ^ m := by
  have ht : ContinuousOn Real.tan (Set.uIcc b c) := continuousOn_tan'.mono fun x hx => hI x hx
  have i1 : IntervalIntegrable (fun x => Real.tan x ^ (m + 2)) MeasureTheory.volume b c :=
    (ht.pow _).intervalIntegrable
  have i2 : IntervalIntegrable (fun x => Real.tan x ^ m) MeasureTheory.volume b c :=
    (ht.pow _).intervalIntegrable
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x => Real.tan x ^ (m + 1))
    (f' := fun x => ((m : ℝ) + 1) * (Real.tan x ^ m + Real.tan x ^ (m + 2)))
    (fun x hx => hasDerivAt_tan_pow_succ m (hI x hx))
    (((i2.add i1)).const_mul _)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add i2 i1] at hF
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  linarith

/-! ## Strategies: the identities behind them -/

/-- OpenStax Calculus 2:§3.2 Strategy, odd power of sine (CA-216):
`sin^(2m+1) x = (1 - cos² x)^m sin x`. -/
@[kb "openstaxcalculus2016" "2:§3.2 Strategy (powers of sin and cos), p. 251"]
theorem sin_pow_odd (m : ℕ) (x : ℝ) :
    Real.sin x ^ (2 * m + 1) = (1 - Real.cos x ^ 2) ^ m * Real.sin x := by
  rw [pow_succ, pow_mul, Real.sin_sq]

/-- OpenStax Calculus 2:§3.2 Strategy, odd power of cosine (CA-216):
`cos^(2m+1) x = (1 - sin² x)^m cos x`. -/
@[kb "openstaxcalculus2016" "2:§3.2 Strategy (powers of sin and cos), p. 251"]
theorem cos_pow_odd (m : ℕ) (x : ℝ) :
    Real.cos x ^ (2 * m + 1) = (1 - Real.sin x ^ 2) ^ m * Real.cos x := by
  rw [pow_succ, pow_mul, Real.cos_sq']

/-- OpenStax Calculus 2:§3.2 Strategy, even powers (CA-216): power-reducing identity
`sin² x = 1/2 - cos(2x)/2`. -/
@[kb "openstaxcalculus2016" "2:§3.2 Strategy (powers of sin and cos), p. 251"]
theorem sin_sq_power_reduce (x : ℝ) : Real.sin x ^ 2 = 1 / 2 - Real.cos (2 * x) / 2 := by
  rw [Real.sin_sq, Real.cos_sq]; ring

/-- OpenStax Calculus 2:§3.2 Strategy, even powers (CA-216): power-reducing identity
`cos² x = 1/2 + cos(2x)/2`. -/
@[kb "openstaxcalculus2016" "2:§3.2 Strategy (powers of sin and cos), p. 251"]
theorem cos_sq_power_reduce (x : ℝ) : Real.cos x ^ 2 = 1 / 2 + Real.cos (2 * x) / 2 := Real.cos_sq x

/-- OpenStax Calculus 2:§3.2 Strategy (CA-216): `sin x cos x = sin(2x)/2`. -/
@[kb "openstaxcalculus2016" "2:§3.2 Strategy (powers of sin and cos), p. 251"]
theorem sin_mul_cos_double (x : ℝ) : Real.sin x * Real.cos x = Real.sin (2 * x) / 2 := by
  rw [Real.sin_two_mul]; ring

/-- OpenStax Calculus 2:§3.2 Eq. 3.3 (CA-217). `sin a sin b = (cos(a-b) - cos(a+b))/2`. -/
@[kb "openstaxcalculus2016" "2:§3.2 Rule (products of sines and cosines of different angles, Eq. 3.3-3.5), p. 252"]
theorem sin_mul_sin_eq (a b : ℝ) :
    Real.sin a * Real.sin b = (Real.cos (a - b) - Real.cos (a + b)) / 2 := by
  rw [Real.cos_sub, Real.cos_add]; ring

/-- OpenStax Calculus 2:§3.2 Eq. 3.4 (CA-217). `sin a cos b = (sin(a-b) + sin(a+b))/2`. -/
@[kb "openstaxcalculus2016" "2:§3.2 Rule (products of sines and cosines of different angles, Eq. 3.3-3.5), p. 252"]
theorem sin_mul_cos_eq (a b : ℝ) :
    Real.sin a * Real.cos b = (Real.sin (a - b) + Real.sin (a + b)) / 2 := by
  rw [Real.sin_sub, Real.sin_add]; ring

/-- OpenStax Calculus 2:§3.2 Eq. 3.5 (CA-217). `cos a cos b = (cos(a-b) + cos(a+b))/2`. -/
@[kb "openstaxcalculus2016" "2:§3.2 Rule (products of sines and cosines of different angles, Eq. 3.3-3.5), p. 252"]
theorem cos_mul_cos_eq (a b : ℝ) :
    Real.cos a * Real.cos b = (Real.cos (a - b) + Real.cos (a + b)) / 2 := by
  rw [Real.cos_sub, Real.cos_add]; ring

private theorem hasDerivAt_sin_mul_div {c : ℝ} (hc : c ≠ 0) (x : ℝ) :
    HasDerivAt (fun x => Real.sin (c * x) / c) (Real.cos (c * x)) x := by
  refine (((hasDerivAt_id' x).const_mul c).sin.div_const c).congr_deriv ?_
  field_simp

private theorem hasDerivAt_cos_mul_div {c : ℝ} (hc : c ≠ 0) (x : ℝ) :
    HasDerivAt (fun x => Real.cos (c * x) / c) (-Real.sin (c * x)) x := by
  refine (((hasDerivAt_id' x).const_mul c).cos.div_const c).congr_deriv ?_
  field_simp

/-- OpenStax Calculus 2:Eq. 3.3 (CA-217). For `a ≠ ±b`, an antiderivative of `sin(ax) sin(bx)` is
`(sin((a-b)x)/(a-b) - sin((a+b)x)/(a+b))/2`. -/
@[kb "openstaxcalculus2016" "2:§3.2 Rule (products of sines and cosines of different angles, Eq. 3.3-3.5), p. 252"]
theorem hasDerivAt_sin_mul_sin {a b : ℝ} (h1 : a - b ≠ 0) (h2 : a + b ≠ 0) (x : ℝ) :
    HasDerivAt (fun x => (Real.sin ((a - b) * x) / (a - b) - Real.sin ((a + b) * x) / (a + b)) / 2)
      (Real.sin (a * x) * Real.sin (b * x)) x := by
  refine (((hasDerivAt_sin_mul_div h1 x).sub (hasDerivAt_sin_mul_div h2 x)).div_const 2).congr_deriv ?_
  rw [sin_mul_sin_eq, ← sub_mul, ← add_mul]

/-- OpenStax Calculus 2:Eq. 3.4 (CA-217). For `a ≠ ±b`, an antiderivative of `sin(ax) cos(bx)` is
`-(cos((a-b)x)/(a-b) + cos((a+b)x)/(a+b))/2`. -/
@[kb "openstaxcalculus2016" "2:§3.2 Rule (products of sines and cosines of different angles, Eq. 3.3-3.5), p. 252"]
theorem hasDerivAt_sin_mul_cos {a b : ℝ} (h1 : a - b ≠ 0) (h2 : a + b ≠ 0) (x : ℝ) :
    HasDerivAt (fun x => -(Real.cos ((a - b) * x) / (a - b) + Real.cos ((a + b) * x) / (a + b)) / 2)
      (Real.sin (a * x) * Real.cos (b * x)) x := by
  refine ((((hasDerivAt_cos_mul_div h1 x).add (hasDerivAt_cos_mul_div h2 x)).neg).div_const 2).congr_deriv ?_
  rw [sin_mul_cos_eq, ← sub_mul, ← add_mul]; ring

/-- OpenStax Calculus 2:Eq. 3.5 (CA-217). For `a ≠ ±b`, an antiderivative of `cos(ax) cos(bx)` is
`(sin((a-b)x)/(a-b) + sin((a+b)x)/(a+b))/2`. -/
@[kb "openstaxcalculus2016" "2:§3.2 Rule (products of sines and cosines of different angles, Eq. 3.3-3.5), p. 252"]
theorem hasDerivAt_cos_mul_cos {a b : ℝ} (h1 : a - b ≠ 0) (h2 : a + b ≠ 0) (x : ℝ) :
    HasDerivAt (fun x => (Real.sin ((a - b) * x) / (a - b) + Real.sin ((a + b) * x) / (a + b)) / 2)
      (Real.cos (a * x) * Real.cos (b * x)) x := by
  refine (((hasDerivAt_sin_mul_div h1 x).add (hasDerivAt_sin_mul_div h2 x)).div_const 2).congr_deriv ?_
  rw [cos_mul_cos_eq, ← sub_mul, ← add_mul]

/-- OpenStax Calculus 2:§3.2 Strategy, even power of secant (CA-219): `sec^(2m+2) x = (1 + tan² x)^m sec² x`
where `cos x ≠ 0` (substitute `u = tan x`). -/
@[kb "openstaxcalculus2016" "2:§3.2 Strategy (powers of tan and sec), p. 253"]
theorem sec_pow_even {x : ℝ} (m : ℕ) (h : Real.cos x ≠ 0) :
    sec x ^ (2 * m + 2) = (1 + Real.tan x ^ 2) ^ m * sec x ^ 2 := by
  rw [pow_add, pow_mul, ← one_add_tan_sq h]

/-- OpenStax Calculus 2:§3.2 Strategy, odd power of tangent (CA-219):
`tan^(2m+1) x sec^(k+1) x = (sec² x - 1)^m sec^k x (sec x tan x)` where `cos x ≠ 0` (substitute `u = sec x`). -/
@[kb "openstaxcalculus2016" "2:§3.2 Strategy (powers of tan and sec), p. 253"]
theorem tan_pow_odd_mul_sec_pow {x : ℝ} (m k : ℕ) (h : Real.cos x ≠ 0) :
    Real.tan x ^ (2 * m + 1) * sec x ^ (k + 1) =
      (sec x ^ 2 - 1) ^ m * sec x ^ k * (sec x * Real.tan x) := by
  have e : sec x ^ 2 - 1 = Real.tan x ^ 2 := by linear_combination -(one_add_tan_sq h)
  rw [e, pow_succ, pow_succ, pow_mul]; ring

/-! ## Trigonometric substitutions -/

/-- OpenStax Calculus 2:§3.3 Strategy, `x = a sin θ` (CA-223). For `a ≥ 0`, `θ ∈ [-π/2, π/2]`:
`√(a² - (a sin θ)²) = a cos θ`. -/
@[kb "openstaxcalculus2016" "2:§3.3 Strategy (sqrt(a^2 - x^2)), p. 260"]
theorem sqrt_sq_sub_mul_sin {a θ : ℝ} (ha : 0 ≤ a) (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) :
    √(a ^ 2 - (a * Real.sin θ) ^ 2) = a * Real.cos θ := by
  have hc : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc hθ
  have : a ^ 2 - (a * Real.sin θ) ^ 2 = (a * Real.cos θ) ^ 2 := by
    have := Real.sin_sq_add_cos_sq θ
    linear_combination (-(a ^ 2)) * this
  rw [this, Real.sqrt_sq (mul_nonneg ha hc)]

/-- OpenStax Calculus 2:§3.3 Strategy, `x = a sin θ` (CA-223): `d(a sin θ)/dθ = a cos θ`. -/
@[kb "openstaxcalculus2016" "2:§3.3 Strategy (sqrt(a^2 - x^2)), p. 260"]
theorem hasDerivAt_mul_sin (a θ : ℝ) : HasDerivAt (fun θ => a * Real.sin θ) (a * Real.cos θ) θ :=
  (Real.hasDerivAt_sin θ).const_mul a

/-- OpenStax Calculus 2:§3.3 Strategy, `x = a tan θ` (CA-224). For `a ≥ 0`, `θ ∈ (-π/2, π/2)`:
`√(a² + (a tan θ)²) = a sec θ`. -/
@[kb "openstaxcalculus2016" "2:§3.3 Strategy (sqrt(a^2 + x^2)), p. 263"]
theorem sqrt_sq_add_mul_tan {a θ : ℝ} (ha : 0 ≤ a) (hθ : θ ∈ Ioo (-(π / 2)) (π / 2)) :
    √(a ^ 2 + (a * Real.tan θ) ^ 2) = a * sec θ := by
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo hθ
  have hs : 0 ≤ sec θ := by unfold sec; positivity
  have : a ^ 2 + (a * Real.tan θ) ^ 2 = (a * sec θ) ^ 2 := by
    linear_combination (a ^ 2) * one_add_tan_sq hc.ne'
  rw [this, Real.sqrt_sq (mul_nonneg ha hs)]

/-- OpenStax Calculus 2:§3.3 Strategy, `x = a tan θ` (CA-224): `d(a tan θ)/dθ = a sec² θ`
where `cos θ ≠ 0`. -/
@[kb "openstaxcalculus2016" "2:§3.3 Strategy (sqrt(a^2 + x^2)), p. 263"]
theorem hasDerivAt_mul_tan (a : ℝ) {θ : ℝ} (h : Real.cos θ ≠ 0) :
    HasDerivAt (fun θ => a * Real.tan θ) (a * sec θ ^ 2) θ :=
  (hasDerivAt_tan_sec_sq h).const_mul a

/-- OpenStax Calculus 2:§3.3 Strategy, `x = a sec θ` (CA-225). For `a ≥ 0` and `cos θ ≠ 0`:
`√((a sec θ)² - a²) = a |tan θ|`. -/
@[kb "openstaxcalculus2016" "2:§3.3 Strategy (sqrt(x^2 - a^2)), p. 266"]
theorem sqrt_sq_sub_mul_sec {a θ : ℝ} (ha : 0 ≤ a) (h : Real.cos θ ≠ 0) :
    √((a * sec θ) ^ 2 - a ^ 2) = a * |Real.tan θ| := by
  have : (a * sec θ) ^ 2 - a ^ 2 = (a * Real.tan θ) ^ 2 := by
    linear_combination (-(a ^ 2)) * one_add_tan_sq h
  rw [this, Real.sqrt_sq_eq_abs, abs_mul, abs_of_nonneg ha]

/-- OpenStax Calculus 2:§3.3 Strategy, `x = a sec θ`, case `x ≥ a` (CA-225). For `a ≥ 0`,
`θ ∈ [0, π/2)`: `√((a sec θ)² - a²) = a tan θ`. -/
@[kb "openstaxcalculus2016" "2:§3.3 Strategy (sqrt(x^2 - a^2)), p. 266"]
theorem sqrt_sq_sub_mul_sec_of_first {a θ : ℝ} (ha : 0 ≤ a) (h0 : 0 ≤ θ) (h1 : θ < π / 2) :
    √((a * sec θ) ^ 2 - a ^ 2) = a * Real.tan θ := by
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩
  rw [sqrt_sq_sub_mul_sec ha hc.ne',
    abs_of_nonneg (Real.tan_nonneg_of_nonneg_of_le_pi_div_two h0 h1.le)]

/-- OpenStax Calculus 2:§3.3 Strategy, `x = a sec θ`, case `x ≤ -a` (CA-225). For `a ≥ 0`,
`θ ∈ (π/2, π]`: `√((a sec θ)² - a²) = -a tan θ`. -/
@[kb "openstaxcalculus2016" "2:§3.3 Strategy (sqrt(x^2 - a^2)), p. 266"]
theorem sqrt_sq_sub_mul_sec_of_second {a θ : ℝ} (ha : 0 ≤ a) (h0 : π / 2 < θ) (h1 : θ ≤ π) :
    √((a * sec θ) ^ 2 - a ^ 2) = -(a * Real.tan θ) := by
  have hc : Real.cos θ < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt h0 (by linarith [Real.pi_pos])
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [Real.pi_pos]) h1
  have ht : Real.tan θ ≤ 0 := by
    rw [Real.tan_eq_sin_div_cos]; exact div_nonpos_of_nonneg_of_nonpos hs hc.le
  rw [sqrt_sq_sub_mul_sec ha hc.ne, abs_of_nonpos ht]
  ring

/-- OpenStax Calculus 2:§3.3 Strategy, `x = a sec θ` (CA-225): `d(a sec θ)/dθ = a sec θ tan θ`
where `cos θ ≠ 0`. -/
@[kb "openstaxcalculus2016" "2:§3.3 Strategy (sqrt(x^2 - a^2)), p. 266"]
theorem hasDerivAt_mul_sec (a : ℝ) {θ : ℝ} (h : Real.cos θ ≠ 0) :
    HasDerivAt (fun θ => a * sec θ) (a * (sec θ * Real.tan θ)) θ :=
  (hasDerivAt_sec h).const_mul a

end UndergradKB.Calculus
