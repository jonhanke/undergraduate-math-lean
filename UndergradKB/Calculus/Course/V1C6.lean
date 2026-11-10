import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import UndergradKB.Common.Attr
import UndergradKB.Calculus.AreasBetween
import UndergradKB.Calculus.Volumes
import UndergradKB.Calculus.ArcLength
import UndergradKB.Calculus.MassCentroid
import UndergradKB.Calculus.ExpLog
import UndergradKB.Calculus.FirstOrderODE
import UndergradKB.Calculus.Hyperbolic

/-! Course layer, OpenStax Calculus Volume 1, Chapter 6 (applications of integration, and the
logarithm/exponential of section 6.7). -/

namespace UndergradKB.Calculus.Course.V1C6

open Set MeasureTheory
open scoped Interval

/-- OpenStax Calculus 1:Theorem 6.1 (CA-249). For continuous `f ≥ g` on `[a,b]`, the area of the
region between the graphs is `∫ a..b (f - g)`, with area taken as Lebesgue measure on the plane. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.1, p. 549"]
theorem area_between_curves {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hfg : ∀ x ∈ Icc a b, g x ≤ f x) :
    volume (regionBetween g f (Icc a b)) = ENNReal.ofReal (∫ x in a..b, (f x - g x)) := by
  rw [Measure.volume_eq_prod, volume_regionBetween_eq_integral
    (hg.integrableOn_Icc) (hf.integrableOn_Icc) measurableSet_Icc hfg,
    intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
  rfl

/-- OpenStax Calculus 1:§6.2 Definition (cylinder) and volume formula (CA-252). A cylinder with
planar base `s` and height `h` has volume equal to base area times height. -/
@[kb "openstaxcalculus2016" "1:§6.2 Definition (cylinder) and volume formula A*h, p. 559"]
theorem cylinder_volume (s : Set (ℝ × ℝ)) (h : ℝ) :
    volume (s ×ˢ Icc (0 : ℝ) h) = volume s * ENNReal.ofReal h := by
  rw [Measure.volume_eq_prod (α := ℝ × ℝ) (β := ℝ), Measure.prod_prod, Real.volume_Icc]
  simp

/-- OpenStax Calculus 1:§6.7 Definition (natural logarithm) (CA-281). For `x > 0`,
`ln x = ∫ 1..x dt/t`. -/
@[kb "openstaxcalculus2016" "1:§6.7 Definition (natural logarithm) (6.24), p. 635"]
theorem log_eq_integral_inv {x : ℝ} (hx : 0 < x) : Real.log x = ∫ t in (1 : ℝ)..x, t⁻¹ := by
  rw [integral_inv_of_pos one_pos hx, div_one]

/-- OpenStax Calculus 1:Theorem 6.15 (CA-282). For `x > 0`, `d/dx ln x = 1/x`. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.15, p. 635"]
theorem hasDerivAt_log_pos {x : ℝ} (hx : 0 < x) : HasDerivAt Real.log x⁻¹ x :=
  Real.hasDerivAt_log hx.ne'

/-- OpenStax Calculus 1:Theorem 6.16 (CA-283). `ln` is differentiable on `(0, ∞)`. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.16, p. 635"]
theorem log_differentiableOn : DifferentiableOn ℝ Real.log (Ioi 0) :=
  fun _ hx => (Real.differentiableAt_log (ne_of_gt hx)).differentiableWithinAt

/-- OpenStax Calculus 1:Theorem 6.16 (CA-283). `ln` is continuous on `(0, ∞)`. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.16, p. 635"]
theorem log_continuousOn : ContinuousOn Real.log (Ioi 0) :=
  log_differentiableOn.continuousOn

/-- OpenStax Calculus 1:Theorem 6.17 (CA-284). `ln |u|` is an antiderivative of `1/u` for `u ≠ 0`. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.17, p. 636"]
theorem hasDerivAt_log_abs {u : ℝ} (hu : u ≠ 0) : HasDerivAt (fun t => Real.log |t|) u⁻¹ u := by
  have : (fun t : ℝ => Real.log |t|) = Real.log := funext Real.log_abs
  rw [this]
  exact Real.hasDerivAt_log hu

/-- OpenStax Calculus 1:Theorem 6.17 (CA-284), definite form. If `0` is not between `a` and `b`,
`∫ a..b du/u = ln (b/a)`. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.17, p. 636"]
theorem integral_inv_log_div {a b : ℝ} (h : (0 : ℝ) ∉ [[a, b]]) :
    ∫ u in a..b, u⁻¹ = Real.log (b / a) :=
  integral_inv h

/-- OpenStax Calculus 1:Theorem 6.18 (CA-285). `ln 1 = 0`. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.18, p. 637"]
theorem log_one_eq_zero : Real.log 1 = 0 :=
  Real.log_one

/-- OpenStax Calculus 1:Theorem 6.18 (CA-285). `ln (ab) = ln a + ln b` for `a, b > 0`. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.18, p. 637"]
theorem log_mul_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.log (a * b) = Real.log a + Real.log b :=
  Real.log_mul ha.ne' hb.ne'

/-- OpenStax Calculus 1:Theorem 6.18 (CA-285). `ln (a/b) = ln a - ln b` for `a, b > 0`. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.18, p. 637"]
theorem log_div_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.log (a / b) = Real.log a - Real.log b :=
  Real.log_div ha.ne' hb.ne'

/-- OpenStax Calculus 1:Theorem 6.18 (CA-285). `ln (a^r) = r ln a` for `a > 0` and rational `r`. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.18, p. 637"]
theorem log_rpow_rat {a : ℝ} (ha : 0 < a) (r : ℚ) :
    Real.log (a ^ (r : ℝ)) = r * Real.log a :=
  Real.log_rpow ha r

/-- OpenStax Calculus 1:§6.7 Definition (the number e) (CA-286). The number `e = exp 1` is the
unique positive real whose logarithm is `1`. -/
@[kb "openstaxcalculus2016" "1:§6.7 Definition (the number e), p. 638"]
theorem exp_one_unique : Real.log (Real.exp 1) = 1 ∧ ∀ x : ℝ, 0 < x → Real.log x = 1 → x = Real.exp 1 := by
  refine ⟨Real.log_exp 1, fun x hx h => ?_⟩
  rw [← h, Real.exp_log hx]

/-- OpenStax Calculus 1:§6.7 Definition (exponential function) (CA-287). For `y > 0`,
`y = exp x` iff `ln y = x`. -/
@[kb "openstaxcalculus2016" "1:§6.7 Definition (exponential function) (6.25-6.26), p. 639"]
theorem eq_exp_iff_log_eq {x y : ℝ} (hy : 0 < y) : y = Real.exp x ↔ Real.log y = x := by
  constructor
  · rintro rfl
    exact Real.log_exp x
  · rintro rfl
    exact (Real.exp_log hy).symm

/-- OpenStax Calculus 1:§6.7 Definition (exponential function) (CA-287). `exp x = e^x`. -/
@[kb "openstaxcalculus2016" "1:§6.7 Definition (exponential function) (6.25-6.26), p. 639"]
theorem exp_eq_e_rpow (x : ℝ) : Real.exp x = Real.exp 1 ^ x :=
  (Real.exp_one_rpow x).symm

/-- OpenStax Calculus 1:Theorem 6.19 (CA-288). `e^(x+y) = e^x e^y`. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.19, p. 639"]
theorem exp_add_eq (x y : ℝ) : Real.exp (x + y) = Real.exp x * Real.exp y :=
  Real.exp_add x y

/-- OpenStax Calculus 1:Theorem 6.19 (CA-288). `e^(x-y) = e^x / e^y`. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.19, p. 639"]
theorem exp_sub_eq (x y : ℝ) : Real.exp (x - y) = Real.exp x / Real.exp y :=
  Real.exp_sub x y

/-- OpenStax Calculus 1:Theorem 6.19 (CA-288). `(e^x)^r = e^(rx)`. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.19, p. 639"]
theorem exp_rpow_eq (x r : ℝ) : Real.exp x ^ r = Real.exp (r * x) := by
  rw [← Real.exp_mul, mul_comm]

/-- OpenStax Calculus 1:§6.7 derivative and integral of e^x (CA-289). `d/dx e^x = e^x`. -/
@[kb "openstaxcalculus2016" "1:§6.7 derivative and integral of e^x, p. 640"]
theorem hasDerivAt_exp_self (x : ℝ) : HasDerivAt Real.exp (Real.exp x) x :=
  Real.hasDerivAt_exp x

/-- OpenStax Calculus 1:§6.7 derivative and integral of e^x (CA-289). `∫ a..b e^x dx = e^b - e^a`. -/
@[kb "openstaxcalculus2016" "1:§6.7 derivative and integral of e^x, p. 640"]
theorem integral_exp_eq (a b : ℝ) : ∫ x in a..b, Real.exp x = Real.exp b - Real.exp a :=
  integral_exp

/-- OpenStax Calculus 1:§6.7 Definition (general exponential) (CA-290). For `b > 0`,
`b^x = e^(x ln b)`. -/
@[kb "openstaxcalculus2016" "1:§6.7 Definition (general exponential), p. 641"]
theorem rpow_eq_exp_mul_log {b : ℝ} (hb : 0 < b) (x : ℝ) : b ^ x = Real.exp (x * Real.log b) := by
  rw [Real.rpow_def_of_pos hb, mul_comm]

/-- OpenStax Calculus 1:§6.7 change of base for general logarithm (CA-292). `log_b x = ln x / ln b`. -/
@[kb "openstaxcalculus2016" "1:§6.7 change of base for general logarithm, p. 641"]
theorem logb_eq_log_div_log (b x : ℝ) : Real.logb b x = Real.log x / Real.log b :=
  rfl

/-! ## Results proved in undergrad-kb -/

/-- OpenStax Calculus 1:Theorem 6.2 (CA-250). For continuous `f, g` on `[a, b]` whose graphs may
cross, the area between them is `∫ a..b |f - g|`. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.2, p. 551"]
theorem area_between_crossing_curves {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {a b : ℝ} (hab : a ≤ b) :
    volume {p : ℝ × ℝ | p.1 ∈ Icc a b ∧
      ((f p.1 < p.2 ∧ p.2 < g p.1) ∨ (g p.1 < p.2 ∧ p.2 < f p.1))} =
    ENNReal.ofReal (∫ x in a..b, |f x - g x|) :=
  UndergradKB.Calculus.area_between_crossing hf hg hab

/-- OpenStax Calculus 1:Theorem 6.3 (CA-251). For continuous `u, v` with `v ≤ u`, the area of the
region between the curves `x = v(y)` and `x = u(y)` for `y ∈ [c, d]` is `∫ c..d (u - v)`. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.3, p. 554"]
theorem area_between_curves_in_y_book {u v : ℝ → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hle : ∀ y, v y ≤ u y) {c d : ℝ} (hcd : c ≤ d) :
    volume {p : ℝ × ℝ | p.2 ∈ Icc c d ∧ v p.2 < p.1 ∧ p.1 < u p.2} =
    ENNReal.ofReal (∫ y in c..d, (u y - v y)) :=
  UndergradKB.Calculus.area_between_curves_in_y hu hv hle hcd

/-- OpenStax Calculus 1:§6.2 slicing method (CA-253). The volume of a solid is the integral of its
cross-sectional areas: for a measurable solid, `volume S = ∫⁻ x, volume (slice at x)`; and for a
solid over `[a, b]` with continuous slice area `A(x)` it is `∫ a..b A`. -/
@[kb "openstaxcalculus2016" "1:§6.2 slicing method, p. 561"]
theorem slicing_method :
    (∀ {S : Set (ℝ × ℝ × ℝ)}, MeasurableSet S →
      volume S = ∫⁻ x, volume (Prod.mk x ⁻¹' S)) ∧
    (∀ {a b : ℝ}, a ≤ b → ∀ (T : ℝ → Set (ℝ × ℝ)) (A : ℝ → ℝ),
      MeasurableSet {p : ℝ × ℝ × ℝ | p.1 ∈ Icc a b ∧ p.2 ∈ T p.1} →
      ContinuousOn A (Icc a b) → (∀ x ∈ Icc a b, 0 ≤ A x) →
      (∀ x ∈ Icc a b, volume (T x) = ENNReal.ofReal (A x)) →
      volume {p : ℝ × ℝ × ℝ | p.1 ∈ Icc a b ∧ p.2 ∈ T p.1} =
        ENNReal.ofReal (∫ x in a..b, A x)) :=
  ⟨fun hS => UndergradKB.Calculus.volume_eq_lintegral_slices hS,
    fun hab T A hS hA hA0 hT => UndergradKB.Calculus.volume_solid_of_slices hab T A hS hA hA0 hT⟩

/-- OpenStax Calculus 1:§6.2 Rule: The Disk Method (6.3) (CA-256). Revolving the region under a
continuous `y = f(x)` over `[a, b]` about the `x`-axis gives volume `π ∫ a..b f(x)² dx`. -/
@[kb "openstaxcalculus2016" "1:§6.2 Rule: The Disk Method (6.3), p. 566"]
theorem disk_method {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ} (hf : Continuous f) :
    volume {p : ℝ × ℝ × ℝ | p.1 ∈ Icc a b ∧ p.2.1 ^ 2 + p.2.2 ^ 2 ≤ f p.1 ^ 2} =
      ENNReal.ofReal (Real.pi * ∫ x in a..b, f x ^ 2) :=
  UndergradKB.Calculus.volume_disk_method hab hf

/-- OpenStax Calculus 1:§6.2 Rule: Disk Method around the y-axis (6.4) (CA-257). Revolving the
region between `x = g(y)` and the `y`-axis over `[c, d]` about the `y`-axis gives volume
`π ∫ c..d g(y)² dy`. -/
@[kb "openstaxcalculus2016" "1:§6.2 Rule: Disk Method around the y-axis (6.4), p. 568"]
theorem disk_method_y_axis {c d : ℝ} (hcd : c ≤ d) {g : ℝ → ℝ} (hg : Continuous g) :
    volume {p : ℝ × ℝ × ℝ | p.2.1 ∈ Icc c d ∧ p.1 ^ 2 + p.2.2 ^ 2 ≤ g p.2.1 ^ 2} =
      ENNReal.ofReal (Real.pi * ∫ y in c..d, g y ^ 2) :=
  UndergradKB.Calculus.volume_disk_method_y hcd hg

/-- OpenStax Calculus 1:§6.2 Rule: The Washer Method (6.5) (CA-258). The region between `0 ≤ g ≤ f`
over `[a, b]`, revolved about the `x`-axis, has volume `π ∫ a..b (f² - g²)`. -/
@[kb "openstaxcalculus2016" "1:§6.2 Rule: The Washer Method (6.5), p. 570"]
theorem washer_method {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ} (hf : Continuous f)
    (hg : Continuous g) (hg0 : ∀ x ∈ Icc a b, 0 ≤ g x) (hgf : ∀ x ∈ Icc a b, g x ≤ f x) :
    volume {p : ℝ × ℝ × ℝ | p.1 ∈ Icc a b ∧ g p.1 ^ 2 ≤ p.2.1 ^ 2 + p.2.2 ^ 2 ∧
      p.2.1 ^ 2 + p.2.2 ^ 2 ≤ f p.1 ^ 2} =
      ENNReal.ofReal (Real.pi * ∫ x in a..b, (f x ^ 2 - g x ^ 2)) :=
  UndergradKB.Calculus.volume_washer_method hab hf hg hg0 hgf

/-- OpenStax Calculus 1:§6.2 Rule: Washer Method around the y-axis (CA-259). The region between
`0 ≤ u ≤ v` (as functions of `y`) over `[c, d]`, revolved about the `y`-axis, has volume
`π ∫ c..d (v² - u²) dy`. -/
@[kb "openstaxcalculus2016" "1:§6.2 Rule: Washer Method around the y-axis, p. 571"]
theorem washer_method_y_axis {c d : ℝ} (hcd : c ≤ d) {u v : ℝ → ℝ} (hu : Continuous u)
    (hv : Continuous v) (hu0 : ∀ y ∈ Icc c d, 0 ≤ u y) (huv : ∀ y ∈ Icc c d, u y ≤ v y) :
    volume {p : ℝ × ℝ × ℝ | p.2.1 ∈ Icc c d ∧ u p.2.1 ^ 2 ≤ p.1 ^ 2 + p.2.2 ^ 2 ∧
      p.1 ^ 2 + p.2.2 ^ 2 ≤ v p.2.1 ^ 2} =
      ENNReal.ofReal (Real.pi * ∫ y in c..d, (v y ^ 2 - u y ^ 2)) :=
  UndergradKB.Calculus.volume_washer_method_y hcd hu hv hu0 huv

/-- OpenStax Calculus 1:§6.3 Rule: The Method of Cylindrical Shells (6.6) (CA-260). The region
under `y = f(x) ≥ 0` over `[a, b]` (`0 ≤ a`), revolved about the `y`-axis, has volume
`2π ∫ a..b x f(x) dx`. -/
@[kb "openstaxcalculus2016" "1:§6.3 Rule: The Method of Cylindrical Shells (6.6), p. 580"]
theorem cylindrical_shells {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : Continuous f) (hf0 : ∀ x ∈ Icc a b, 0 ≤ f x) :
    volume {p : ℝ × ℝ × ℝ | a ≤ √(p.1 ^ 2 + p.2.2 ^ 2) ∧ √(p.1 ^ 2 + p.2.2 ^ 2) ≤ b ∧
      0 ≤ p.2.1 ∧ p.2.1 ≤ f (√(p.1 ^ 2 + p.2.2 ^ 2))} =
      ENNReal.ofReal (2 * Real.pi * ∫ x in a..b, x * f x) :=
  UndergradKB.Calculus.volume_shell_method ha hab hf hf0

/-- OpenStax Calculus 1:§6.3 Rule: Method of Cylindrical Shells around the x-axis (CA-261). The
region between `x = 0` and `x = g(y)` over `[c, d]` (`0 ≤ c`), revolved about the `x`-axis, has
volume `2π ∫ c..d y g(y) dy`. -/
@[kb "openstaxcalculus2016" "1:§6.3 Rule: Method of Cylindrical Shells around the x-axis, p. 582"]
theorem cylindrical_shells_x_axis {c d : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d) {g : ℝ → ℝ}
    (hg : Continuous g) (hg0 : ∀ y ∈ Icc c d, 0 ≤ g y) :
    volume {p : ℝ × ℝ × ℝ | c ≤ √(p.2.1 ^ 2 + p.2.2 ^ 2) ∧ √(p.2.1 ^ 2 + p.2.2 ^ 2) ≤ d ∧
      0 ≤ p.1 ∧ p.1 ≤ g (√(p.2.1 ^ 2 + p.2.2 ^ 2))} =
      ENNReal.ofReal (2 * Real.pi * ∫ y in c..d, y * g y) :=
  UndergradKB.Calculus.volume_shell_method_x hc hcd hg hg0

/-- OpenStax Calculus 1:§6.3 shell formula for axis x=-k (CA-262). Revolving about the vertical
line `x = -k` replaces the shell radius `x` by `x + k`, giving volume `2π ∫ a..b (x + k) f(x) dx`. -/
@[kb "openstaxcalculus2016" "1:§6.3 shell formula for axis x=-k, p. 583"]
theorem cylindrical_shells_shifted_axis {a b k : ℝ} (ha : 0 ≤ a + k) (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : Continuous f) (hf0 : ∀ x ∈ Icc a b, 0 ≤ f x) :
    volume {p : ℝ × ℝ × ℝ | a + k ≤ √((p.1 + k) ^ 2 + p.2.2 ^ 2) ∧
      √((p.1 + k) ^ 2 + p.2.2 ^ 2) ≤ b + k ∧
      0 ≤ p.2.1 ∧ p.2.1 ≤ f (√((p.1 + k) ^ 2 + p.2.2 ^ 2) - k)} =
      ENNReal.ofReal (2 * Real.pi * ∫ x in a..b, (x + k) * f x) :=
  UndergradKB.Calculus.volume_shell_method_shifted ha hab hf hf0

/-- OpenStax Calculus 1:Theorem 6.4 (CA-263). For `f` with continuous derivative on `[a, b]`, the
arc length `∫ a..b √(1 + f'(x)²) dx` is the least upper bound (supremum) of the lengths of inscribed
polygonal paths. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.4, p. 591"]
theorem arc_length_formula {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {a b : ℝ} (hab : a < b) :
    IsLUB (UndergradKB.Calculus.polygonLengths f a b) (∫ x in a..b, √(1 + deriv f x ^ 2)) ∧
    (∫ x in a..b, √(1 + deriv f x ^ 2)) = sSup (UndergradKB.Calculus.polygonLengths f a b) :=
  ⟨UndergradKB.Calculus.arcLength_isLUB hf hab, UndergradKB.Calculus.arcLength_eq_sSup hf hab⟩

/-- OpenStax Calculus 1:Theorem 6.5 (CA-264). The arc length of the graph `x = g(y)` over
`[f a, f b]`, for `g` the inverse of an increasing `f` (both with continuous derivative), is
`∫ √(1 + g'(y)²) dy`, and it equals the arc length of `y = f(x)` over `[a, b]`. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.5, p. 593"]
theorem arc_length_in_y {f g : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) {a b : ℝ}
    (hpos : ∀ x ∈ uIcc a b, 0 < deriv f x) (hgf : ∀ x, g (f x) = x) :
    (∫ y in f a..f b, √(1 + deriv g y ^ 2)) = ∫ x in a..b, √(1 + deriv f x ^ 2) :=
  UndergradKB.Calculus.arcLength_inverse hf hg hpos hgf

/-- OpenStax Calculus 1:§6.4 lateral area of frustum (CA-266). If the frustum is cut from a cone by
similar triangles (`r₁ (s₁ + s) = r₂ s₁`), its lateral area (difference of two cone lateral areas
`π r s`) is `π (r₁ + r₂) s`. -/
@[kb "openstaxcalculus2016" "1:§6.4 lateral area of frustum, p. 596"]
theorem frustum_lateral_area {r₁ r₂ s₁ s : ℝ} (hsim : r₁ * (s₁ + s) = r₂ * s₁) :
    Real.pi * r₂ * (s₁ + s) - Real.pi * r₁ * s₁ = Real.pi * (r₁ + r₂) * s :=
  UndergradKB.Calculus.frustum_lateralArea hsim

/-- OpenStax Calculus 1:Theorem 6.6 (CA-267). The surface of revolution of `y = f(x)` about the
`x`-axis has area `2π ∫ a..b f(x) √(1 + f'(x)²) dx`; for the cone `y = r x / h` this gives the lateral
area `π r √(h² + r²)`. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.6, p. 597"]
theorem surface_area_of_revolution :
    (∀ (f : ℝ → ℝ) (a b : ℝ), UndergradKB.Calculus.surfaceArea f a b =
      2 * Real.pi * ∫ x in a..b, f x * √(1 + deriv f x ^ 2)) ∧
    (∀ {r h : ℝ}, 0 < h → UndergradKB.Calculus.surfaceArea (fun x => r * x / h) 0 h =
      Real.pi * r * √(h ^ 2 + r ^ 2)) :=
  ⟨fun _ _ _ => rfl, fun hh => UndergradKB.Calculus.surfaceArea_cone hh⟩

/-- OpenStax Calculus 1:Theorem 6.7 (CA-268). A thin rod over `[a, b]` with continuous nonnegative
linear density `ρ` has mass `∫ a..b ρ`, the total mass of the measure with density `ρ`. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.7, p. 603"]
theorem mass_of_rod {a b : ℝ} (hab : a ≤ b) {ρ : ℝ → ℝ} (hρ : ContinuousOn ρ (Icc a b))
    (hρ0 : ∀ x ∈ Icc a b, 0 ≤ ρ x) :
    (volume.withDensity fun x => ENNReal.ofReal (ρ x)) (Icc a b) =
      ENNReal.ofReal (∫ x in a..b, ρ x) :=
  UndergradKB.Calculus.rodMass_eq_withDensity hab hρ hρ0

/-- OpenStax Calculus 1:Theorem 6.8 (CA-269). A disk of radius `r` with continuous nonnegative
radial density `ρ` has mass `2π ∫ 0..r x ρ(x) dx`. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.8, p. 605"]
theorem mass_of_disk_radial_density {r : ℝ} (hr : 0 ≤ r) {ρ : ℝ → ℝ} (hρ : Continuous ρ)
    (hρ0 : ∀ x ∈ Icc 0 r, 0 ≤ ρ x) :
    ∫⁻ q in {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 ≤ r ^ 2}, ENNReal.ofReal (ρ (√(q.1 ^ 2 + q.2 ^ 2))) =
      ENNReal.ofReal (2 * Real.pi * ∫ x in (0 : ℝ)..r, x * ρ x) :=
  UndergradKB.Calculus.lintegral_disk_radial hr hρ hρ0

/-- OpenStax Calculus 1:§6.5 Definition (work) (6.12) (CA-270). The work of a variable force `F`
moving an object from `a` to `b` is `∫ a..b F`, which is `F (b - a)` for a constant force. -/
@[kb "openstaxcalculus2016" "1:§6.5 Definition (work) (6.12), p. 606"]
theorem work_as_integral :
    (∀ (F : ℝ → ℝ) (a b : ℝ), UndergradKB.Calculus.work F a b = ∫ x in a..b, F x) ∧
    (∀ F a b : ℝ, UndergradKB.Calculus.work (fun _ => F) a b = F * (b - a)) :=
  ⟨fun _ _ _ => rfl, UndergradKB.Calculus.work_const⟩

/-- OpenStax Calculus 1:§6.5 Equation 6.13 (hydrostatic force) (CA-273). The force on a vertical
plate with depth `d(x)` and width `w(x)` over `[a, b]` in a liquid of weight-density `γ` is
`γ ∫ a..b d(x) w(x) dx`; for constant depth and width this is `γ s w₀ (b - a)`. -/
@[kb "openstaxcalculus2016" "1:§6.5 Equation 6.13 (hydrostatic force), p. 613"]
theorem hydrostatic_force :
    (∀ (γ : ℝ) (d w : ℝ → ℝ) (a b : ℝ), UndergradKB.Calculus.hydrostaticForce γ d w a b =
      γ * ∫ x in a..b, d x * w x) ∧
    (∀ γ s w₀ a b : ℝ, UndergradKB.Calculus.hydrostaticForce γ (fun _ => s) (fun _ => w₀) a b =
      γ * s * (w₀ * (b - a))) :=
  ⟨fun _ _ _ _ _ => rfl, UndergradKB.Calculus.hydrostaticForce_const⟩

/-- OpenStax Calculus 1:Theorem 6.9 (CA-274). Point masses `m i` at positions `x i` on a line have
center of mass the mass-weighted mean of the positions, and translating the positions by `c`
translates the center of mass by `c` (for nonzero total mass). -/
@[kb "openstaxcalculus2016" "1:Theorem 6.9, p. 620"]
theorem center_of_mass_on_line :
    (∀ {ι : Type*} (s : Finset ι) (m x : ι → ℝ),
      UndergradKB.Calculus.centerOfMass s m x = s.centerMass m x) ∧
    (∀ {ι : Type*} (s : Finset ι) (m x : ι → ℝ) (c : ℝ), ∑ i ∈ s, m i ≠ 0 →
      UndergradKB.Calculus.centerOfMass s m (fun i => x i + c) =
        UndergradKB.Calculus.centerOfMass s m x + c) :=
  ⟨fun s m x => UndergradKB.Calculus.centerOfMass_eq_centerMass s m x,
    fun s m x c hm => UndergradKB.Calculus.centerOfMass_add_const s m x c hm⟩

/-- OpenStax Calculus 1:Theorem 6.10 (CA-275). Point masses `m i` at points `p i` of the plane have
center of mass the mass-weighted mean of the points (moments `M_x`, `M_y` over total mass). -/
@[kb "openstaxcalculus2016" "1:Theorem 6.10, p. 621"]
theorem center_of_mass_in_plane {ι : Type*} (s : Finset ι) (m : ι → ℝ) (p : ι → ℝ × ℝ) :
    UndergradKB.Calculus.centerOfMass2 s m p = s.centerMass m p :=
  UndergradKB.Calculus.centerOfMass2_eq_centerMass s m p

/-- OpenStax Calculus 1:Theorem 6.11 (CA-277). Symmetry principle: if a lamina is symmetric about
the vertical line `x = c`, its first moment about that line vanishes, i.e. its centroid lies on it. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.11, p. 622"]
theorem centroid_on_symmetry_line {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {c h : ℝ} (hh : 0 ≤ h) (hgf : ∀ x ∈ Icc (c - h) (c + h), g x ≤ f x)
    (hfs : ∀ t, f (c - t) = f (c + t)) (hgs : ∀ t, g (c - t) = g (c + t)) (ρ : ℝ) :
    UndergradKB.Calculus.laminaMy ρ (UndergradKB.Calculus.lamina f g (c - h) (c + h)) =
      c * UndergradKB.Calculus.laminaMass ρ (UndergradKB.Calculus.lamina f g (c - h) (c + h)) :=
  UndergradKB.Calculus.lamina_symmetric_centroid_x hf hg hh hgf hfs hgs ρ

/-- OpenStax Calculus 1:Theorem 6.12 (CA-278). A lamina of constant density `ρ` under `y = f(x)`
over `[a, b]` has mass `ρ ∫ f`, moments `M_x = ρ ∫ f²/2` and `M_y = ρ ∫ x f`. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.12, p. 624"]
theorem lamina_under_curve {f : ℝ → ℝ} {a b : ℝ} (hf : Continuous f) (hab : a ≤ b)
    (hf0 : ∀ x ∈ Icc a b, 0 ≤ f x) (ρ : ℝ) :
    UndergradKB.Calculus.laminaMass ρ (UndergradKB.Calculus.lamina f (fun _ => 0) a b) =
      ρ * ∫ x in a..b, f x ∧
    UndergradKB.Calculus.laminaMx ρ (UndergradKB.Calculus.lamina f (fun _ => 0) a b) =
      ρ * ∫ x in a..b, f x ^ 2 / 2 ∧
    UndergradKB.Calculus.laminaMy ρ (UndergradKB.Calculus.lamina f (fun _ => 0) a b) =
      ρ * ∫ x in a..b, x * f x :=
  UndergradKB.Calculus.lamina_under_graph hf hab hf0 ρ

/-- OpenStax Calculus 1:Theorem 6.13 (CA-279). A lamina of constant density `ρ` between the graphs
`g ≤ f` over `[a, b]` has mass `ρ ∫ (f - g)`, `M_x = ρ ∫ (f² - g²)/2` and `M_y = ρ ∫ x (f - g)`. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.13, p. 626"]
theorem lamina_between_curves {f g : ℝ → ℝ} {a b : ℝ} (hf : Continuous f) (hg : Continuous g)
    (hab : a ≤ b) (hgf : ∀ x ∈ Icc a b, g x ≤ f x) (ρ : ℝ) :
    UndergradKB.Calculus.laminaMass ρ (UndergradKB.Calculus.lamina f g a b) =
      ρ * ∫ x in a..b, (f x - g x) ∧
    UndergradKB.Calculus.laminaMx ρ (UndergradKB.Calculus.lamina f g a b) =
      ρ * ∫ x in a..b, (f x ^ 2 - g x ^ 2) / 2 ∧
    UndergradKB.Calculus.laminaMy ρ (UndergradKB.Calculus.lamina f g a b) =
      ρ * ∫ x in a..b, x * (f x - g x) :=
  UndergradKB.Calculus.lamina_mass_moments hf hg hab hgf ρ

/-- OpenStax Calculus 1:Theorem 6.14 (CA-280). Theorem of Pappus: revolving the region between
`0 ≤ g ≤ f` about the `x`-axis gives volume `2π · ȳ · A`, the distance travelled by the centroid
times the area. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.14, p. 631"]
theorem pappus_theorem {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ} (hf : Continuous f)
    (hg : Continuous g) (hg0 : ∀ x ∈ Icc a b, 0 ≤ g x) (hgf : ∀ x ∈ Icc a b, g x ≤ f x)
    (hA : 0 < volume.real (UndergradKB.Calculus.lamina f g a b)) :
    volume {p : ℝ × ℝ × ℝ | p.1 ∈ Icc a b ∧ g p.1 ^ 2 ≤ p.2.1 ^ 2 + p.2.2 ^ 2 ∧
      p.2.1 ^ 2 + p.2.2 ^ 2 ≤ f p.1 ^ 2} =
      ENNReal.ofReal (2 * Real.pi *
        (UndergradKB.Calculus.laminaCenter 1 (UndergradKB.Calculus.lamina f g a b)).2 *
        volume.real (UndergradKB.Calculus.lamina f g a b)) :=
  UndergradKB.Calculus.pappus_x_axis hab hf hg hg0 hgf hA

/-- OpenStax Calculus 1:Theorem 6.20 (CA-291). For `b > 0`, `d/dx b^x = b^x ln b`; for `b ≠ 1`,
`b^x / ln b` is an antiderivative of `b^x` and `∫ b^x dx = (b^β - b^α)/ln b`. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.20, p. 641"]
theorem deriv_and_integral_general_exponential {b : ℝ} (hb : 0 < b) :
    (∀ x : ℝ, HasDerivAt (fun y : ℝ => b ^ y) (b ^ x * Real.log b) x) ∧
    (b ≠ 1 → ∀ x : ℝ, HasDerivAt (fun y : ℝ => b ^ y / Real.log b) (b ^ x) x) ∧
    (b ≠ 1 → ∀ α β : ℝ, ∫ x in α..β, b ^ x = (b ^ β - b ^ α) / Real.log b) :=
  ⟨UndergradKB.Calculus.hasDerivAt_rpow_self hb,
    fun hb1 x => UndergradKB.Calculus.hasDerivAt_rpow_div_log hb hb1 x,
    fun hb1 α β => UndergradKB.Calculus.integral_rpow_base hb hb1 α β⟩

/-- OpenStax Calculus 1:Theorem 6.21 (CA-293). For `b ≠ 1`, `d/dx log_b x = 1/(x ln b)` where
`x ≠ 0`. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.21, p. 642"]
theorem deriv_logb_self (b : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (Real.logb b) (1 / (x * Real.log b)) x :=
  UndergradKB.Calculus.hasDerivAt_logb_self b hx

/-- OpenStax Calculus 1:§6.8 Rule: Exponential Growth Model (6.27) (CA-294). For `k > 0`, a function
satisfies the differential equation `y' = k y` exactly when `y = y(0) e^(k t)`; with `y(0) = y₀` this
is `y = y₀ e^(k t)`. -/
@[kb "openstaxcalculus2016" "1:§6.8 Rule: Exponential Growth Model (6.27), p. 645"]
theorem exponential_growth_model {k : ℝ} (hk : 0 < k) :
    (∀ {y : ℝ → ℝ}, (∀ t, HasDerivAt y (k * y t) t) ↔ ∀ t, y t = y 0 * Real.exp (k * t)) ∧
    (∀ {y : ℝ → ℝ} {y0 : ℝ}, y 0 = y0 →
      ((∀ t, HasDerivAt y (k * y t) t) ↔ ∀ t, y t = y0 * Real.exp (k * t))) :=
  ⟨UndergradKB.Calculus.exp_growth_iff hk, fun h0 => UndergradKB.Calculus.exp_growth_ivp hk h0⟩

/-- OpenStax Calculus 1:§6.8 Rule: Exponential Decay Model (CA-297). For `k > 0`, a function
satisfies `y' = -k y` exactly when `y = y(0) e^(-k t)`; with `y(0) = y₀` this is
`y = y₀ e^(-k t)`. -/
@[kb "openstaxcalculus2016" "1:§6.8 Rule: Exponential Decay Model, p. 648"]
theorem exponential_decay_model {k : ℝ} (hk : 0 < k) :
    (∀ {y : ℝ → ℝ}, (∀ t, HasDerivAt y (-k * y t) t) ↔ ∀ t, y t = y 0 * Real.exp (-k * t)) ∧
    (∀ {y : ℝ → ℝ} {y0 : ℝ}, y 0 = y0 →
      ((∀ t, HasDerivAt y (-k * y t) t) ↔ ∀ t, y t = y0 * Real.exp (-k * t))) :=
  ⟨UndergradKB.Calculus.exp_decay_iff hk, fun h0 => UndergradKB.Calculus.exp_decay_ivp hk h0⟩

/-- OpenStax Calculus 1:§6.9 Table 6.2 (CA-300). Derivatives of the hyperbolic functions
(`sinh' = cosh`, `cosh' = sinh`, `tanh' = sech²`, `coth' = -csch²`, `sech' = -sech tanh`,
`csch' = -csch coth`; `coth` and `csch` away from `0`). -/
@[kb "openstaxcalculus2016" "1:§6.9 Table 6.2, p. 655"]
theorem derivatives_of_hyperbolic_functions :
    (∀ x : ℝ, HasDerivAt Real.sinh (Real.cosh x) x) ∧
    (∀ x : ℝ, HasDerivAt Real.cosh (Real.sinh x) x) ∧
    (∀ x : ℝ, HasDerivAt Real.tanh (UndergradKB.Calculus.sech x ^ 2) x) ∧
    (∀ {x : ℝ}, x ≠ 0 → HasDerivAt UndergradKB.Calculus.coth (-(UndergradKB.Calculus.csch x ^ 2)) x) ∧
    (∀ x : ℝ, HasDerivAt UndergradKB.Calculus.sech
      (-(UndergradKB.Calculus.sech x * Real.tanh x)) x) ∧
    (∀ {x : ℝ}, x ≠ 0 → HasDerivAt UndergradKB.Calculus.csch
      (-(UndergradKB.Calculus.csch x * UndergradKB.Calculus.coth x)) x) :=
  ⟨Real.hasDerivAt_sinh, Real.hasDerivAt_cosh, UndergradKB.Calculus.hasDerivAt_tanh,
    @UndergradKB.Calculus.hasDerivAt_coth, UndergradKB.Calculus.hasDerivAt_sech,
    @UndergradKB.Calculus.hasDerivAt_csch⟩

/-- OpenStax Calculus 1:§6.9 hyperbolic integral formulas (CA-301). Reading the derivative table
backwards: `-sech`, `-csch` and `-coth` are antiderivatives of `sech tanh`, `csch coth` and `csch²`,
and `∫ a..b sinh = cosh b - cosh a`, `∫ a..b cosh = sinh b - sinh a`. -/
@[kb "openstaxcalculus2016" "1:§6.9 hyperbolic integral formulas, p. 656"]
theorem integrals_of_hyperbolic_functions :
    (∀ x : ℝ, HasDerivAt (fun y => -UndergradKB.Calculus.sech y)
      (UndergradKB.Calculus.sech x * Real.tanh x) x) ∧
    (∀ {x : ℝ}, x ≠ 0 → HasDerivAt (fun y => -UndergradKB.Calculus.csch y)
      (UndergradKB.Calculus.csch x * UndergradKB.Calculus.coth x) x) ∧
    (∀ {x : ℝ}, x ≠ 0 → HasDerivAt (fun y => -UndergradKB.Calculus.coth y)
      (UndergradKB.Calculus.csch x ^ 2) x) ∧
    (∀ a b : ℝ, ∫ x in a..b, Real.sinh x = Real.cosh b - Real.cosh a) ∧
    (∀ a b : ℝ, ∫ x in a..b, Real.cosh x = Real.sinh b - Real.sinh a) :=
  ⟨UndergradKB.Calculus.hasDerivAt_neg_sech, @UndergradKB.Calculus.hasDerivAt_neg_csch,
    @UndergradKB.Calculus.hasDerivAt_neg_coth, UndergradKB.Calculus.integral_sinh,
    UndergradKB.Calculus.integral_cosh⟩

/-- OpenStax Calculus 1:§6.9 Table 6.4 and derivation (CA-302). Derivatives of the inverse
hyperbolic functions: `arsinh' = 1/√(x²+1)`, `arcosh' = 1/√(x²-1)` for `x > 1`, and
`artanh' = 1/(1-x²)` for `|x| < 1`. -/
@[kb "openstaxcalculus2016" "1:§6.9 Table 6.4 and derivation, p. 658"]
theorem derivatives_of_inverse_hyperbolic_functions :
    (∀ x : ℝ, HasDerivAt Real.arsinh (1 / √(x ^ 2 + 1)) x) ∧
    (∀ {x : ℝ}, 1 < x → HasDerivAt Real.arcosh (1 / √(x ^ 2 - 1)) x) ∧
    (∀ {x : ℝ}, |x| < 1 → HasDerivAt Real.artanh (1 / (1 - x ^ 2)) x) :=
  ⟨UndergradKB.Calculus.hasDerivAt_arsinh', @UndergradKB.Calculus.hasDerivAt_arcosh',
    @UndergradKB.Calculus.hasDerivAt_artanh⟩

/-- OpenStax Calculus 1:§6.9 inverse hyperbolic integral formulas (CA-303). Antiderivatives giving
inverse hyperbolic functions, for `a > 0`: `arsinh (u/a)` for `1/√(a²+u²)`, `arcosh (u/a)` for
`1/√(u²-a²)` (`u > a`), and `(1/a) artanh (u/a)` for `1/(a²-u²)` (`|u| < a`). -/
@[kb "openstaxcalculus2016" "1:§6.9 inverse hyperbolic integral formulas, p. 659"]
theorem integrals_giving_inverse_hyperbolic_functions {a : ℝ} (ha : 0 < a) :
    (∀ u : ℝ, HasDerivAt (fun y => Real.arsinh (y / a)) (1 / √(a ^ 2 + u ^ 2)) u) ∧
    (∀ {u : ℝ}, a < u →
      HasDerivAt (fun y => Real.arcosh (y / a)) (1 / √(u ^ 2 - a ^ 2)) u) ∧
    (∀ {u : ℝ}, |u| < a →
      HasDerivAt (fun y => (1 / a) * Real.artanh (y / a))
        (1 / (a ^ 2 - u ^ 2)) u) :=
  ⟨UndergradKB.Calculus.hasDerivAt_arsinh_div ha, fun hu => UndergradKB.Calculus.hasDerivAt_arcosh_div ha hu,
    fun hu => UndergradKB.Calculus.hasDerivAt_artanh_div ha hu⟩

/-! ## Wave 3: further results -/

/-- OpenStax Calculus 1:Example 6.6 (CA-254). A pyramid of height `h` with a square base of side `a`,
sliced by squares of side `a (h - x)/h`, has volume `a^2 h / 3`. -/
@[kb "openstaxcalculus2016" "1:Example 6.6, p. 561"]
theorem pyramid_volume {a h : ℝ} (ha : 0 ≤ a) (hh : 0 < h) :
    volume {p : ℝ × ℝ × ℝ | p.1 ∈ Icc 0 h ∧ |p.2.1| ≤ a * (h - p.1) / (2 * h) ∧
        |p.2.2| ≤ a * (h - p.1) / (2 * h)} = ENNReal.ofReal (a ^ 2 * h / 3) :=
  UndergradKB.Calculus.volume_pyramid ha hh

/-- OpenStax Calculus 1:§6.8 continuous compound interest (CA-295). Compounding `n` times a year at
rate `r` for `t` years gives `P (1 + r/n)^(n t)`, which tends to `P e^(r t)` as `n` grows. -/
@[kb "openstaxcalculus2016" "1:§6.8 continuous compound interest, p. 647"]
theorem continuous_compound_interest (P r t : ℝ) :
    Filter.Tendsto (fun n : ℕ => P * (1 + r / n) ^ ((n : ℝ) * t)) Filter.atTop
      (nhds (P * Real.exp (r * t))) :=
  UndergradKB.Calculus.compound_interest_tendsto P r t

/-- OpenStax Calculus 1:§6.8 Definition (doubling time) (CA-296). For `y = y₀ e^(k t)` the quantity
doubles over a time span `s` exactly when `s = ln 2 / k`, and for `k > 0` this span is positive. -/
@[kb "openstaxcalculus2016" "1:§6.8 Definition (doubling time), p. 648"]
theorem doubling_time_formula {y : ℝ → ℝ} {y₀ k : ℝ} (hy₀ : y₀ ≠ 0) (hk : k ≠ 0)
    (hy : ∀ t, y t = y₀ * Real.exp (k * t)) :
    (∀ t s : ℝ, y (t + s) = 2 * y t ↔ s = Real.log 2 / k) ∧
    (0 < k → ∀ t : ℝ, 0 < Real.log 2 / k ∧
      y₀ * Real.exp (k * (t + Real.log 2 / k)) = 2 * (y₀ * Real.exp (k * t))) :=
  ⟨UndergradKB.Calculus.doubling_time_iff hy₀ hk hy,
    fun h t => UndergradKB.Calculus.doubling_time h t⟩

/-- OpenStax Calculus 1:§6.8 Newton's law of cooling solution (CA-298). A temperature obeying
`T' = -k (T - Tₐ)` at every time is `Tₐ + (T 0 - Tₐ) e^(-k t)`, and conversely. -/
@[kb "openstaxcalculus2016" "1:§6.8 Newton's law of cooling solution, p. 649"]
theorem newtons_law_of_cooling_solution {T : ℝ → ℝ} {k Tₐ : ℝ} :
    (∀ t : ℝ, HasDerivAt T (-k * (T t - Tₐ)) t) ↔
      ∀ t : ℝ, T t = Tₐ + (T 0 - Tₐ) * Real.exp (-k * t) :=
  UndergradKB.Calculus.newton_cooling_iff

/-- OpenStax Calculus 1:§6.8 Definition (half-life) (CA-299). For `y = y₀ e^(-k t)` the quantity
halves over a time span `s` exactly when `s = ln 2 / k`, and for `k > 0` this span is positive. -/
@[kb "openstaxcalculus2016" "1:§6.8 Definition (half-life), p. 650"]
theorem half_life_formula {y : ℝ → ℝ} {y₀ k : ℝ} (hy₀ : y₀ ≠ 0) (hk : k ≠ 0)
    (hy : ∀ t, y t = y₀ * Real.exp (-k * t)) :
    (∀ t s : ℝ, y (t + s) = y t / 2 ↔ s = Real.log 2 / k) ∧
    (0 < k → ∀ t : ℝ, 0 < Real.log 2 / k ∧
      y₀ * Real.exp (-k * (t + Real.log 2 / k)) = y₀ * Real.exp (-k * t) / 2) :=
  ⟨UndergradKB.Calculus.half_life_iff hy₀ hk hy, fun h t => UndergradKB.Calculus.half_life h t⟩

end UndergradKB.Calculus.Course.V1C6
