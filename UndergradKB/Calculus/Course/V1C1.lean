import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.LinearAlgebra.AffineSpace.Slope
import Mathlib.Logic.Function.Basic
import UndergradKB.Common.Attr
import UndergradKB.Calculus.Functions
import UndergradKB.Calculus.Trig
import UndergradKB.Calculus.Hyperbolic
import UndergradKB.Calculus.ExpLog
import UndergradKB.Calculus.EndBehavior

/-!
# OpenStax Calculus Volume 1, Chapter 1 (functions and graphs): course layer

Thin wrappers around Mathlib stating the central results of the chapter in the book's terms.
-/

namespace UndergradKB.Calculus.Course.V1C1

open Real

/-- OpenStax Calculus 1:§1.1 Combining Functions Using Mathematical Operations (CA-005).
Sum, difference, product and quotient of functions are computed pointwise. -/
@[kb "openstaxcalculus2016" "1:§1.1 Combining Functions Using Mathematical Operations, p. 26"]
theorem pointwise_operations (f g : ℝ → ℝ) (x : ℝ) :
    (f + g) x = f x + g x ∧ (f - g) x = f x - g x ∧ (f * g) x = f x * g x ∧
      (f / g) x = f x / g x :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- OpenStax Calculus 1:§1.1 Definition (composite function) (CA-006).
The composite applies `g` first and then `f`. -/
@[kb "openstaxcalculus2016" "1:§1.1 Definition (composite function), p. 27"]
theorem comp_apply_eq (f g : ℝ → ℝ) (x : ℝ) : (f ∘ g) x = f (g x) := rfl

/-- OpenStax Calculus 1:§1.1 Definition (even and odd functions) (CA-007).
Even means `f (-x) = f x` for all `x`, odd means `f (-x) = -f x` for all `x`. -/
@[kb "openstaxcalculus2016" "1:§1.1 Definition (even and odd functions), p. 30"]
theorem even_odd_iff (f : ℝ → ℝ) :
    (Function.Even f ↔ ∀ x, f (-x) = f x) ∧ (Function.Odd f ↔ ∀ x, f (-x) = -f x) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- OpenStax Calculus 1:§1.1 Absolute value function (CA-008).
`|x| = x` for `x ≥ 0` and `|x| = -x` for `x < 0`. -/
@[kb "openstaxcalculus2016" "1:§1.1 Absolute value function, p. 31"]
theorem abs_piecewise (x : ℝ) : (0 ≤ x → |x| = x) ∧ (x < 0 → |x| = -x) :=
  ⟨abs_of_nonneg, abs_of_neg⟩

/-- OpenStax Calculus 1:§1.2 Definition (slope) (CA-009).
The slope through `(x₁, f x₁)` and `(x₂, f x₂)` is the ratio of the change in `y` to the change in
`x`, and the linear function `m x + b` has slope `m`. -/
@[kb "openstaxcalculus2016" "1:§1.2 Definition (slope), p. 39"]
theorem slope_ratio_and_linear (f : ℝ → ℝ) (x₁ x₂ m b : ℝ) (h : x₁ ≠ x₂) :
    slope f x₁ x₂ = (f x₂ - f x₁) / (x₂ - x₁) ∧ slope (fun x => m * x + b) x₁ x₂ = m := by
  refine ⟨slope_def_field f x₁ x₂, ?_⟩
  rw [slope_def_field]
  have : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  field_simp
  ring

/-- OpenStax Calculus 1:§1.2 Polynomial function (definition in text) (CA-011).
A polynomial function is the finite sum of coefficient times power of `x`, up to its degree. -/
@[kb "openstaxcalculus2016" "1:§1.2 Polynomial function (definition in text), p. 42"]
theorem polynomial_eval_as_sum (p : Polynomial ℝ) (x : ℝ) :
    p.eval x = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * x ^ i :=
  Polynomial.eval_eq_sum_range x

/-- OpenStax Calculus 1:§1.2 Rule: The Quadratic Formula (CA-013).
For `a ≠ 0` and nonnegative discriminant, `a x² + b x + c = 0` iff `x = (-b ± √(b²-4ac))/(2a)`. -/
@[kb "openstaxcalculus2016" "1:§1.2 Rule: The Quadratic Formula, p. 44"]
theorem quadratic_formula (a b c x : ℝ) (ha : a ≠ 0) (hd : 0 ≤ b ^ 2 - 4 * a * c) :
    a * x ^ 2 + b * x + c = 0 ↔
      x = (-b + √(b ^ 2 - 4 * a * c)) / (2 * a) ∨ x = (-b - √(b ^ 2 - 4 * a * c)) / (2 * a) := by
  have h := quadratic_eq_zero_iff (a := a) (b := b) (c := c) (K := ℝ) ha
    (s := √(b ^ 2 - 4 * a * c)) (by
      rw [discrim, ← sq, sq_sqrt hd]) x
  rw [← h]
  constructor <;> intro h <;> linarith [h]

/-- OpenStax Calculus 1:§1.3 Trigonometric functions properties (CA-018).
Sine and cosine have period `2π`, tangent has period `π`; sine is odd, cosine is even. -/
@[kb "openstaxcalculus2016" "1:§1.3 Trigonometric functions properties, p. 64"]
theorem trig_periodicity_parity :
    Function.Periodic Real.sin (2 * π) ∧ Function.Periodic Real.cos (2 * π) ∧
      Function.Periodic Real.tan π ∧ (∀ x, Real.sin (-x) = -Real.sin x) ∧
      (∀ x, Real.cos (-x) = Real.cos x) :=
  ⟨Real.sin_periodic, Real.cos_periodic, Real.tan_periodic, Real.sin_neg, Real.cos_neg⟩

/-- OpenStax Calculus 1:§1.3 Rule: Trigonometric Identities (addition and subtraction) (CA-020).
The sine and cosine of a sum or difference of angles. -/
@[kb "openstaxcalculus2016" "1:§1.3 Rule: Trigonometric Identities (addition and subtraction), p. 66"]
theorem trig_addition_subtraction (α β : ℝ) :
    Real.sin (α + β) = Real.sin α * Real.cos β + Real.cos α * Real.sin β ∧
    Real.sin (α - β) = Real.sin α * Real.cos β - Real.cos α * Real.sin β ∧
    Real.cos (α + β) = Real.cos α * Real.cos β - Real.sin α * Real.sin β ∧
    Real.cos (α - β) = Real.cos α * Real.cos β + Real.sin α * Real.sin β :=
  ⟨Real.sin_add α β, Real.sin_sub α β, Real.cos_add α β, Real.cos_sub α β⟩

/-- OpenStax Calculus 1:§1.3 Rule: Trigonometric Identities (double-angle) (CA-021).
`sin 2θ = 2 sin θ cos θ` and the three forms of `cos 2θ`. -/
@[kb "openstaxcalculus2016" "1:§1.3 Rule: Trigonometric Identities (double-angle), p. 66"]
theorem trig_double_angle (θ : ℝ) :
    Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ ∧
    Real.cos (2 * θ) = Real.cos θ ^ 2 - Real.sin θ ^ 2 ∧
    Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 ∧
    Real.cos (2 * θ) = 1 - 2 * Real.sin θ ^ 2 := by
  refine ⟨Real.sin_two_mul θ, ?_, Real.cos_two_mul θ, ?_⟩
  · rw [Real.cos_two_mul]; nlinarith [Real.sin_sq_add_cos_sq θ]
  · rw [Real.cos_two_mul]; nlinarith [Real.sin_sq_add_cos_sq θ]

/-- OpenStax Calculus 1:§1.4 Definition (inverse function) (CA-023).
A function has an inverse `g` (`g (f x) = x` and `f (g y) = y`) exactly when it is bijective. -/
@[kb "openstaxcalculus2016" "1:§1.4 Definition (inverse function), p. 74"]
theorem inverse_function_iff_bijective (f : ℝ → ℝ) :
    Function.Bijective f ↔ ∃ g : ℝ → ℝ, (∀ x, g (f x) = x) ∧ ∀ y, f (g y) = y :=
  Function.bijective_iff_has_inverse

/-- OpenStax Calculus 1:§1.4 Definition (one-to-one) (CA-024).
`f` is one-to-one iff distinct inputs give distinct outputs. -/
@[kb "openstaxcalculus2016" "1:§1.4 Definition (one-to-one), p. 74"]
theorem injective_iff_distinct_outputs (f : ℝ → ℝ) :
    Function.Injective f ↔ ∀ x y, x ≠ y → f x ≠ f y := by
  constructor
  · intro h x y hxy hf
    exact hxy (h hf)
  · intro h x y hf
    by_contra hxy
    exact h x y hxy hf

/-- OpenStax Calculus 1:§1.4 Existence of an inverse function (CA-025).
A one-to-one function has a left inverse that is also a right inverse on its range. -/
@[kb "openstaxcalculus2016" "1:§1.4 Existence of an inverse function, p. 73"]
theorem injective_has_inverse_on_range (f : ℝ → ℝ) (hf : Function.Injective f) :
    ∃ g : ℝ → ℝ, (∀ x, g (f x) = x) ∧ ∀ y ∈ Set.range f, f (g y) = y := by
  refine ⟨Function.invFun f, Function.leftInverse_invFun hf, ?_⟩
  rintro _ ⟨x, rfl⟩
  rw [Function.leftInverse_invFun hf]

/-- OpenStax Calculus 1:§1.5 Exponential functions (CA-031).
For `b > 1`, `b ^ x` is increasing, and for `0 < b < 1` it is decreasing. -/
@[kb "openstaxcalculus2016" "1:§1.5 Exponential functions, p. 88"]
theorem exponential_monotone (b : ℝ) :
    (1 < b → StrictMono fun x : ℝ => b ^ x) ∧ (0 < b → b < 1 → StrictAnti fun x : ℝ => b ^ x) :=
  ⟨Real.strictMono_rpow_of_base_gt_one, fun h0 h1 => Real.strictAnti_rpow_of_base_lt_one h0 h1⟩

/-- OpenStax Calculus 1:§1.5 Rule: Laws of Exponents (CA-032).
Product, quotient, power, product-base and quotient-base laws for real exponents. -/
@[kb "openstaxcalculus2016" "1:§1.5 Rule: Laws of Exponents, p. 90"]
theorem laws_of_exponents (a b x y : ℝ) (ha : 0 < a) (hb : 0 < b) :
    b ^ x * b ^ y = b ^ (x + y) ∧ b ^ x / b ^ y = b ^ (x - y) ∧ (b ^ x) ^ y = b ^ (x * y) ∧
    (a * b) ^ x = a ^ x * b ^ x ∧ (a / b) ^ x = a ^ x / b ^ x :=
  ⟨(Real.rpow_add hb x y).symm, (Real.rpow_sub hb x y).symm,
    (Real.rpow_mul hb.le x y).symm, Real.mul_rpow ha.le hb.le, Real.div_rpow ha.le hb.le x⟩

/-- OpenStax Calculus 1:§1.5 Logarithmic functions (CA-036).
`log_b` inverts `b ^ x` for `b > 0`, `b ≠ 1`, and `y = ln x` exactly when `e ^ y = x`. -/
@[kb "openstaxcalculus2016" "1:§1.5 Logarithmic functions, p. 92"]
theorem logarithm_inverse (b : ℝ) (hb : 0 < b) (hb1 : b ≠ 1) :
    (∀ x : ℝ, Real.logb b (b ^ x) = x) ∧ (∀ y : ℝ, 0 < y → b ^ Real.logb b y = y) ∧
    (∀ x y : ℝ, 0 < x → (y = Real.log x ↔ Real.exp y = x)) := by
  refine ⟨fun x => Real.logb_rpow hb hb1, fun y hy => Real.rpow_logb hb hb1 hy, ?_⟩
  intro x y hx
  constructor
  · rintro rfl; exact Real.exp_log hx
  · rintro rfl; exact (Real.log_exp y).symm

/-- OpenStax Calculus 1:§1.5 Rule: Properties of Logarithms (CA-040).
Logarithm of a product, quotient and power. -/
@[kb "openstaxcalculus2016" "1:§1.5 Rule: Properties of Logarithms, p. 94"]
theorem logarithm_properties (b x y r : ℝ) (hx : 0 < x) (hy : 0 < y) :
    Real.logb b (x * y) = Real.logb b x + Real.logb b y ∧
    Real.logb b (x / y) = Real.logb b x - Real.logb b y ∧
    Real.logb b (x ^ r) = r * Real.logb b x := by
  refine ⟨Real.logb_mul hx.ne' hy.ne', Real.logb_div hx.ne' hy.ne', ?_⟩
  rw [Real.logb, Real.logb, Real.log_rpow hx]
  ring

/-! ## Results proved in undergrad-kb -/

/-- OpenStax Calculus 1:§1.1 Rule: Vertical Line Test (CA-003). A set in the plane is the graph of a
function on its projection exactly when each vertical line meets it in at most one point. -/
@[kb "openstaxcalculus2016" "1:§1.1 Rule: Vertical Line Test, p. 22"]
theorem vertical_line_test_book (S : Set (ℝ × ℝ)) :
    (∃ f : ℝ → ℝ, S = {p | p.1 ∈ Prod.fst '' S ∧ p.2 = f p.1}) ↔
      ∀ x : ℝ, {y | (x, y) ∈ S}.Subsingleton :=
  UndergradKB.Calculus.vertical_line_test S

/-- OpenStax Calculus 1:§1.2 Definition (equations of a line) (CA-010). Point-slope, slope-intercept
and standard forms describe the same line (including the vertical case `a x = c`). -/
@[kb "openstaxcalculus2016" "1:§1.2 Definition (equations of a line), p. 40"]
theorem line_equation_forms :
    (∀ {m b x₀ y₀ : ℝ}, y₀ = m * x₀ + b → ∀ x y : ℝ,
      (y - y₀ = m * (x - x₀) ↔ y = m * x + b)) ∧
    (∀ {a b c : ℝ}, b ≠ 0 → ∀ x y : ℝ, (a * x + b * y = c ↔ y = (-a / b) * x + c / b)) ∧
    (∀ {a c : ℝ}, a ≠ 0 → ∀ x y : ℝ, (a * x + 0 * y = c ↔ x = c / a)) :=
  ⟨@UndergradKB.Calculus.pointSlope_iff_slopeIntercept,
    @UndergradKB.Calculus.standardForm_iff_slopeIntercept,
    @UndergradKB.Calculus.standardForm_vertical⟩

/-- OpenStax Calculus 1:§1.3 Definition (trigonometric functions) (CA-017). Tangent, cotangent,
secant and cosecant are quotients and reciprocals of sine and cosine. -/
@[kb "openstaxcalculus2016" "1:§1.3 Definition (trigonometric functions), p. 63"]
theorem trig_reciprocal_identities :
    (∀ x : ℝ, Real.tan x = Real.sin x / Real.cos x ∧ Real.cot x = 1 / Real.tan x ∧
      UndergradKB.Calculus.sec x = 1 / Real.cos x ∧ UndergradKB.Calculus.csc x = 1 / Real.sin x ∧
      Real.cot x = Real.cos x / Real.sin x) ∧
    (∀ {x : ℝ}, Real.cos x ≠ 0 → UndergradKB.Calculus.sec x * Real.cos x = 1) ∧
    (∀ {x : ℝ}, Real.sin x ≠ 0 → UndergradKB.Calculus.csc x * Real.sin x = 1) :=
  ⟨UndergradKB.Calculus.reciprocal_identities, @UndergradKB.Calculus.sec_mul_cos,
    @UndergradKB.Calculus.csc_mul_sin⟩

/-- OpenStax Calculus 1:§1.3 Rule: Trigonometric Identities (Pythagorean) (CA-019). The three
Pythagorean identities. -/
@[kb "openstaxcalculus2016" "1:§1.3 Rule: Trigonometric Identities (Pythagorean), p. 66"]
theorem pythagorean_identities :
    (∀ x : ℝ, Real.sin x ^ 2 + Real.cos x ^ 2 = 1) ∧
    (∀ {x : ℝ}, Real.cos x ≠ 0 → 1 + Real.tan x ^ 2 = UndergradKB.Calculus.sec x ^ 2) ∧
    (∀ {x : ℝ}, Real.sin x ≠ 0 → 1 + Real.cot x ^ 2 = UndergradKB.Calculus.csc x ^ 2) :=
  ⟨UndergradKB.Calculus.sin_sq_add_cos_sq', @UndergradKB.Calculus.one_add_tan_sq,
    @UndergradKB.Calculus.one_add_cot_sq⟩

/-- OpenStax Calculus 1:§1.3 Key Equations (generalized sine function) (CA-022). The function
`A sin (B (x - α)) + d` with `B ≠ 0` has period `2π/|B|` and range `[d - |A|, d + |A|]`. -/
@[kb "openstaxcalculus2016" "1:§1.3 Key Equations (generalized sine function), p. 108"]
theorem generalized_sine_amplitude_period (A B α d : ℝ) (hB : B ≠ 0) :
    Function.Periodic (fun x => A * Real.sin (B * (x - α)) + d) (2 * π / |B|) ∧
    Set.range (fun x => A * Real.sin (B * (x - α)) + d) = Set.Icc (d - |A|) (d + |A|) :=
  ⟨UndergradKB.Calculus.generalized_sin_periodic A B α d hB,
    UndergradKB.Calculus.generalized_sin_range A B α d hB⟩

/-- OpenStax Calculus 1:§1.4 Rule: Horizontal Line Test (CA-026). A function is one-to-one exactly
when each horizontal line meets its graph in at most one point. -/
@[kb "openstaxcalculus2016" "1:§1.4 Rule: Horizontal Line Test, p. 74"]
theorem horizontal_line_test_book (f : ℝ → ℝ) :
    Function.Injective f ↔
      ∀ y : ℝ, {x | (x, y) ∈ UndergradKB.Calculus.fnGraph f}.Subsingleton :=
  UndergradKB.Calculus.horizontal_line_test f

/-- OpenStax Calculus 1:§1.5 Rule: Change-of-Base Formulas (CA-041). `log_b x = ln x / ln b`,
`log_a x = log_b x / log_b a` (for `b > 0`, `b ≠ 1`) and `b^x = e^(x ln b)` (for `b > 0`). -/
@[kb "openstaxcalculus2016" "1:§1.5 Rule: Change-of-Base Formulas, p. 95"]
theorem change_of_base_formulas :
    (∀ b x : ℝ, Real.logb b x = Real.log x / Real.log b) ∧
    (∀ {b : ℝ}, 0 < b → b ≠ 1 → ∀ a x : ℝ, Real.logb a x = Real.logb b x / Real.logb b a) ∧
    (∀ {b : ℝ}, 0 < b → ∀ x : ℝ, b ^ x = Real.exp (x * Real.log b)) :=
  ⟨UndergradKB.Calculus.logb_eq_log_div_log', @UndergradKB.Calculus.logb_change_base,
    @UndergradKB.Calculus.rpow_eq_exp_mul_log⟩

/-- OpenStax Calculus 1:§1.5 Rule: Identities Involving Hyperbolic Functions (CA-043). The basic
hyperbolic identities, with the addition and double-angle formulas. -/
@[kb "openstaxcalculus2016" "1:§1.5 Rule: Identities Involving Hyperbolic Functions, p. 100"]
theorem hyperbolic_identities :
    (∀ x : ℝ, Real.cosh x + Real.sinh x = Real.exp x) ∧
    (∀ x : ℝ, Real.cosh x - Real.sinh x = Real.exp (-x)) ∧
    (∀ x : ℝ, Real.cosh x ^ 2 - Real.sinh x ^ 2 = 1) ∧
    (∀ x : ℝ, 1 - Real.tanh x ^ 2 = UndergradKB.Calculus.sech x ^ 2) ∧
    (∀ {x : ℝ}, x ≠ 0 → UndergradKB.Calculus.coth x ^ 2 - 1 = UndergradKB.Calculus.csch x ^ 2) ∧
    (∀ x y : ℝ, Real.sinh (x + y) = Real.sinh x * Real.cosh y + Real.cosh x * Real.sinh y) ∧
    (∀ x y : ℝ, Real.cosh (x + y) = Real.cosh x * Real.cosh y + Real.sinh x * Real.sinh y) ∧
    (∀ x : ℝ, Real.sinh (2 * x) = 2 * Real.sinh x * Real.cosh x) ∧
    (∀ x : ℝ, Real.cosh (2 * x) = Real.cosh x ^ 2 + Real.sinh x ^ 2) :=
  ⟨UndergradKB.Calculus.cosh_add_sinh, UndergradKB.Calculus.cosh_sub_sinh_eq,
    UndergradKB.Calculus.cosh_sq_sub_sinh_sq_eq, UndergradKB.Calculus.one_sub_tanh_sq,
    @UndergradKB.Calculus.coth_sq_sub_one, UndergradKB.Calculus.sinh_add_eq,
    UndergradKB.Calculus.cosh_add_eq, UndergradKB.Calculus.sinh_double,
    UndergradKB.Calculus.cosh_double⟩

/-! ## Wave 3: further results -/

/-- OpenStax Calculus 1:§1.1 Definition (increasing/decreasing) (CA-004). Increasing, strictly
increasing, decreasing and strictly decreasing on a set are conditions comparing `f x₁` and `f x₂`
for `x₁ < x₂`. -/
@[kb "openstaxcalculus2016" "1:§1.1 Definition (increasing/decreasing), p. 25"]
theorem increasing_decreasing_defs (f : ℝ → ℝ) (s : Set ℝ) :
    (MonotoneOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, x₁ < x₂ → f x₁ ≤ f x₂) ∧
    (StrictMonoOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, x₁ < x₂ → f x₁ < f x₂) ∧
    (AntitoneOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, x₁ < x₂ → f x₂ ≤ f x₁) ∧
    (StrictAntiOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, x₁ < x₂ → f x₂ < f x₁) :=
  ⟨monotoneOn_iff_forall_lt, Iff.rfl, antitoneOn_iff_forall_lt, Iff.rfl⟩

/-- OpenStax Calculus 1:§1.2 end behavior of polynomial (CA-012). A polynomial of positive degree
tends to `+∞` or `-∞` at `±∞` according to the sign of its leading coefficient and the parity of
its degree. -/
@[kb "openstaxcalculus2016" "1:§1.2 end behavior of polynomial, p. 43"]
theorem polynomial_end_behavior (P : Polynomial ℝ) (hP : 0 < P.degree) :
    (0 ≤ P.leadingCoeff →
      Filter.Tendsto (fun x => Polynomial.eval x P) Filter.atTop Filter.atTop) ∧
    (P.leadingCoeff ≤ 0 →
      Filter.Tendsto (fun x => Polynomial.eval x P) Filter.atTop Filter.atBot) ∧
    (Even P.natDegree ∧ 0 < P.leadingCoeff ∨ Odd P.natDegree ∧ P.leadingCoeff < 0 →
      Filter.Tendsto (fun x => Polynomial.eval x P) Filter.atBot Filter.atTop) ∧
    (Odd P.natDegree ∧ 0 < P.leadingCoeff ∨ Even P.natDegree ∧ P.leadingCoeff < 0 →
      Filter.Tendsto (fun x => Polynomial.eval x P) Filter.atBot Filter.atBot) :=
  ⟨Polynomial.tendsto_atTop_of_leadingCoeff_nonneg P hP,
    Polynomial.tendsto_atBot_of_leadingCoeff_nonpos P hP,
    UndergradKB.Calculus.polynomial_tendsto_atBot_atTop P hP,
    UndergradKB.Calculus.polynomial_tendsto_atBot_atBot P hP⟩

/-- OpenStax Calculus 1:§1.2 Transformations of Functions (CA-015). Adding a constant, shifting the
argument, scaling the output or the argument, and negating the output or the argument move the
graph by translation, stretching, compression or reflection. -/
@[kb "openstaxcalculus2016" "1:§1.2 Transformations of Functions, p. 53"]
theorem graph_transformations (f : ℝ → ℝ) (c a b : ℝ) (hb : b ≠ 0) :
    (UndergradKB.Calculus.fnGraph fun x => f x + c) =
      (fun p : ℝ × ℝ => (p.1, p.2 + c)) '' UndergradKB.Calculus.fnGraph f ∧
    (UndergradKB.Calculus.fnGraph fun x => f (x + c)) =
      (fun p : ℝ × ℝ => (p.1 - c, p.2)) '' UndergradKB.Calculus.fnGraph f ∧
    (UndergradKB.Calculus.fnGraph fun x => a * f x) =
      (fun p : ℝ × ℝ => (p.1, a * p.2)) '' UndergradKB.Calculus.fnGraph f ∧
    (UndergradKB.Calculus.fnGraph fun x => f (b * x)) =
      (fun p : ℝ × ℝ => (p.1 / b, p.2)) '' UndergradKB.Calculus.fnGraph f ∧
    (UndergradKB.Calculus.fnGraph fun x => -f x) =
      (fun p : ℝ × ℝ => (p.1, -p.2)) '' UndergradKB.Calculus.fnGraph f ∧
    (UndergradKB.Calculus.fnGraph fun x => f (-x)) =
      (fun p : ℝ × ℝ => (-p.1, p.2)) '' UndergradKB.Calculus.fnGraph f :=
  ⟨UndergradKB.Calculus.fnGraph_add_const f c, UndergradKB.Calculus.fnGraph_comp_add_const f c,
    UndergradKB.Calculus.fnGraph_const_mul f a, UndergradKB.Calculus.fnGraph_comp_const_mul f hb,
    UndergradKB.Calculus.fnGraph_neg f, UndergradKB.Calculus.fnGraph_comp_neg f⟩

/-- OpenStax Calculus 1:§1.3 Radian measure (CA-016). The arc cut on a circle of radius `r` by an
angle of `θ` radians has length `r θ`, and `180` degrees correspond to `π` radians. -/
@[kb "openstaxcalculus2016" "1:§1.3 Radian measure, p. 61"]
theorem radian_measure :
    (∀ r θ : ℝ, UndergradKB.Calculus.circleArcLength r θ = r * θ) ∧
    UndergradKB.Calculus.radiansOfDegrees 180 = π :=
  ⟨fun _ _ => rfl, UndergradKB.Calculus.radiansOfDegrees_180⟩

/-- OpenStax Calculus 1:§1.4 Graphing Inverse Functions (CA-027). The graph of the inverse of an
injective function is the reflection of its graph in the line `y = x`. -/
@[kb "openstaxcalculus2016" "1:§1.4 Graphing Inverse Functions, p. 77"]
theorem graph_of_inverse_is_reflection {f : ℝ → ℝ} {s : Set ℝ} (h : Set.InjOn f s) :
    {p : ℝ × ℝ | p.1 ∈ f '' s ∧ p.2 = Function.invFunOn f s p.1} =
      Prod.swap '' {p : ℝ × ℝ | p.1 ∈ s ∧ p.2 = f p.1} :=
  UndergradKB.Calculus.graph_inverse_eq_swap h

/-- OpenStax Calculus 1:§1.4 Definition (inverse trigonometric functions) (CA-029). The principal
ranges of the six inverse trigonometric functions. -/
@[kb "openstaxcalculus2016" "1:§1.4 Definition (inverse trigonometric functions), p. 81"]
theorem inverse_trig_principal_ranges :
    (∀ x : ℝ, Real.arcsin x ∈ Set.Icc (-(π / 2)) (π / 2)) ∧
    (∀ x : ℝ, Real.arccos x ∈ Set.Icc 0 π) ∧
    (∀ x : ℝ, -(π / 2) < Real.arctan x ∧ Real.arctan x < π / 2) ∧
    (∀ x : ℝ, UndergradKB.Calculus.arccot x ∈ Set.Ioo 0 π) ∧
    (∀ {x : ℝ}, 1 ≤ |x| → UndergradKB.Calculus.arcsec x ∈ Set.Icc 0 π ∧
      UndergradKB.Calculus.arcsec x ≠ π / 2) ∧
    (∀ {x : ℝ}, 1 ≤ |x| → UndergradKB.Calculus.arccsc x ∈ Set.Icc (-(π / 2)) (π / 2) ∧
      UndergradKB.Calculus.arccsc x ≠ 0) :=
  ⟨Real.arcsin_mem_Icc, fun x => ⟨Real.arccos_nonneg x, Real.arccos_le_pi x⟩,
    fun x => ⟨Real.neg_pi_div_two_lt_arctan x, Real.arctan_lt_pi_div_two x⟩,
    UndergradKB.Calculus.arccot_mem_Ioo, @UndergradKB.Calculus.arcsec_mem,
    @UndergradKB.Calculus.arccsc_mem⟩

/-- OpenStax Calculus 1:§1.4 Inverse trigonometric functions (CA-030). Each trigonometric function
and its inverse cancel on the principal domain, in both orders. -/
@[kb "openstaxcalculus2016" "1:§1.4 Inverse trigonometric functions, p. 82"]
theorem inverse_trig_cancellation :
    (∀ {x : ℝ}, -1 ≤ x → x ≤ 1 → Real.sin (Real.arcsin x) = x) ∧
    (∀ {x : ℝ}, -(π / 2) ≤ x → x ≤ π / 2 → Real.arcsin (Real.sin x) = x) ∧
    (∀ {x : ℝ}, -1 ≤ x → x ≤ 1 → Real.cos (Real.arccos x) = x) ∧
    (∀ {x : ℝ}, 0 ≤ x → x ≤ π → Real.arccos (Real.cos x) = x) ∧
    (∀ x : ℝ, Real.tan (Real.arctan x) = x) ∧
    (∀ {x : ℝ}, -(π / 2) < x → x < π / 2 → Real.arctan (Real.tan x) = x) ∧
    (∀ x : ℝ, Real.cot (UndergradKB.Calculus.arccot x) = x) ∧
    (∀ {x : ℝ}, 0 < x → x < π → UndergradKB.Calculus.arccot (Real.cot x) = x) ∧
    (∀ {x : ℝ}, 1 ≤ |x| → UndergradKB.Calculus.sec (UndergradKB.Calculus.arcsec x) = x) ∧
    (∀ {x : ℝ}, 0 ≤ x → x ≤ π → x ≠ π / 2 →
      UndergradKB.Calculus.arcsec (UndergradKB.Calculus.sec x) = x) ∧
    (∀ {x : ℝ}, 1 ≤ |x| → UndergradKB.Calculus.csc (UndergradKB.Calculus.arccsc x) = x) ∧
    (∀ {x : ℝ}, -(π / 2) ≤ x → x ≤ π / 2 → x ≠ 0 →
      UndergradKB.Calculus.arccsc (UndergradKB.Calculus.csc x) = x) :=
  ⟨@UndergradKB.Calculus.sin_arcsin', @UndergradKB.Calculus.arcsin_sin',
    @UndergradKB.Calculus.cos_arccos', @UndergradKB.Calculus.arccos_cos',
    UndergradKB.Calculus.tan_arctan', @UndergradKB.Calculus.arctan_tan',
    UndergradKB.Calculus.cot_arccot, @UndergradKB.Calculus.arccot_cot,
    @UndergradKB.Calculus.sec_arcsec, @UndergradKB.Calculus.arcsec_sec,
    @UndergradKB.Calculus.csc_arccsc, @UndergradKB.Calculus.arccsc_csc⟩

/-- OpenStax Calculus 1:§1.5 The number e, natural exponential function (CA-033). The number `e` is
the limit of `(1 + 1/m)^m`, and the natural exponential function is the power `e^x`. -/
@[kb "openstaxcalculus2016" "1:§1.5 The number e, natural exponential function, p. 91"]
theorem number_e_and_natural_exponential :
    Filter.Tendsto (fun m : ℕ => (1 + 1 / (m : ℝ)) ^ m) Filter.atTop (nhds (Real.exp 1)) ∧
    (∀ x : ℝ, Real.exp 1 ^ x = Real.exp x) :=
  ⟨UndergradKB.Calculus.tendsto_one_add_inv_pow_exp, UndergradKB.Calculus.exp_one_rpow_eq⟩

/-- OpenStax Calculus 1:§1.5 Definition (hyperbolic functions) (CA-042). The six hyperbolic
functions written with exponentials. -/
@[kb "openstaxcalculus2016" "1:§1.5 Definition (hyperbolic functions), p. 98"]
theorem hyperbolic_functions_def (x : ℝ) :
    Real.sinh x = (Real.exp x - Real.exp (-x)) / 2 ∧
    Real.cosh x = (Real.exp x + Real.exp (-x)) / 2 ∧
    Real.tanh x = (Real.exp x - Real.exp (-x)) / (Real.exp x + Real.exp (-x)) ∧
    UndergradKB.Calculus.sech x = 2 / (Real.exp x + Real.exp (-x)) ∧
    UndergradKB.Calculus.csch x = 2 / (Real.exp x - Real.exp (-x)) ∧
    UndergradKB.Calculus.coth x =
      (Real.exp x + Real.exp (-x)) / (Real.exp x - Real.exp (-x)) :=
  ⟨UndergradKB.Calculus.sinh_eq_exp x, UndergradKB.Calculus.cosh_eq_exp x,
    UndergradKB.Calculus.tanh_eq_exp x, UndergradKB.Calculus.sech_eq_exp x,
    UndergradKB.Calculus.csch_eq_exp x, UndergradKB.Calculus.coth_eq_exp x⟩

/-- OpenStax Calculus 1:§1.5 Definition (inverse hyperbolic functions) (CA-044). Logarithmic
formulas for the inverse hyperbolic functions, and the inverse relations for `sinh`, `cosh`, `tanh`. -/
@[kb "openstaxcalculus2016" "1:§1.5 Definition (inverse hyperbolic functions), p. 101"]
theorem inverse_hyperbolic_functions_def :
    (∀ x : ℝ, Real.arsinh x = Real.log (x + √(x ^ 2 + 1))) ∧
    (∀ x : ℝ, Real.arcosh x = Real.log (x + √(x ^ 2 - 1))) ∧
    (∀ {x : ℝ}, |x| < 1 → Real.artanh x = 1 / 2 * Real.log ((1 + x) / (1 - x))) ∧
    (∀ {x : ℝ}, 1 < |x| → UndergradKB.Calculus.arcoth x = 1 / 2 * Real.log ((x + 1) / (x - 1))) ∧
    (∀ {x : ℝ}, 0 < x → x ≤ 1 →
      UndergradKB.Calculus.arsech x = Real.log ((1 + √(1 - x ^ 2)) / x)) ∧
    (∀ {x : ℝ}, x ≠ 0 →
      UndergradKB.Calculus.arcsch x = Real.log (1 / x + √(1 + x ^ 2) / |x|)) ∧
    (∀ x : ℝ, Real.sinh (Real.arsinh x) = x) ∧
    (∀ x : ℝ, Real.arsinh (Real.sinh x) = x) ∧
    (∀ {x : ℝ}, 1 ≤ x → Real.cosh (Real.arcosh x) = x) ∧
    (∀ {x : ℝ}, 0 ≤ x → Real.arcosh (Real.cosh x) = x) ∧
    (∀ {x : ℝ}, x ∈ Set.Ioo (-1 : ℝ) 1 → Real.tanh (Real.artanh x) = x) ∧
    (∀ x : ℝ, Real.artanh (Real.tanh x) = x) :=
  ⟨UndergradKB.Calculus.arsinh_eq_log, UndergradKB.Calculus.arcosh_eq_log,
    @UndergradKB.Calculus.artanh_eq_log, @UndergradKB.Calculus.arcoth_eq_log,
    @UndergradKB.Calculus.arsech_eq_log, @UndergradKB.Calculus.arcsch_eq_log,
    Real.sinh_arsinh, Real.arsinh_sinh, @Real.cosh_arcosh, @Real.arcosh_cosh,
    @Real.tanh_artanh, Real.artanh_tanh⟩

end UndergradKB.Calculus.Course.V1C1
