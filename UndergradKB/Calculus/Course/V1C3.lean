import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import UndergradKB.Common.Attr
import UndergradKB.Calculus.TrigCalculus
import UndergradKB.Calculus.TangentsAntiderivatives
import UndergradKB.Calculus.ExpLog

/-!
# OpenStax Calculus Volume 1, Chapter 3 (derivatives): course layer

Thin wrappers around Mathlib stating the differentiation rules of the chapter for real functions.
-/

namespace UndergradKB.Calculus.Course.V1C3

open Filter Topology Real

/-- OpenStax Calculus 1:§3.1 Definition (difference quotient, with increment) (CA-084).
The secant slope through `(a, f a)` and `(a + h, f (a + h))` is `(f (a + h) - f a) / h`. -/
@[kb "openstaxcalculus2016" "1:§3.1 Definition (difference quotient, with increment), p. 197"]
theorem difference_quotient_increment (f : ℝ → ℝ) (a h : ℝ) :
    slope f a (a + h) = (f (a + h) - f a) / h := by
  rw [slope_def_field]
  simp

/-- OpenStax Calculus 1:§3.1 Definition (derivative at a point) (CA-086).
`f' a = L` iff the difference quotient tends to `L` as `h → 0`. -/
@[kb "openstaxcalculus2016" "1:§3.1 Definition (derivative at a point), p. 201"]
theorem derivative_as_limit_of_difference_quotient (f : ℝ → ℝ) (a L : ℝ) :
    HasDerivAt f L a ↔ Tendsto (fun h => (f (a + h) - f a) / h) (𝓝[≠] 0) (𝓝 L) := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simp only [smul_eq_mul, div_eq_inv_mul]

/-- OpenStax Calculus 1:§3.2 Definition (derivative function, differentiable) (CA-089).
Where `f` is differentiable, `deriv f x` is the limit of the difference quotients. -/
@[kb "openstaxcalculus2016" "1:§3.2 Definition (derivative function, differentiable), p. 211"]
theorem derivative_function_limit (f : ℝ → ℝ) (x : ℝ) :
    (DifferentiableAt ℝ f x ↔ ∃ L, Tendsto (fun h => (f (x + h) - f x) / h) (𝓝[≠] 0) (𝓝 L)) ∧
      (DifferentiableAt ℝ f x →
        Tendsto (fun h => (f (x + h) - f x) / h) (𝓝[≠] 0) (𝓝 (deriv f x))) := by
  refine ⟨⟨fun h => ⟨deriv f x, (derivative_as_limit_of_difference_quotient f x _).1 h.hasDerivAt⟩,
    fun ⟨L, hL⟩ => ((derivative_as_limit_of_difference_quotient f x L).2 hL).differentiableAt⟩,
    fun h => (derivative_as_limit_of_difference_quotient f x _).1 h.hasDerivAt⟩

/-- OpenStax Calculus 1:Example 3.11 (CA-090). For `x > 0`, `d/dx √x = 1/(2√x)`. -/
@[kb "openstaxcalculus2016" "1:Example 3.11, p. 211"]
theorem deriv_sqrt (x : ℝ) (hx : 0 < x) : HasDerivAt Real.sqrt (1 / (2 * √x)) x :=
  Real.hasDerivAt_sqrt hx.ne'

/-- OpenStax Calculus 1:§3.2 Definition (second and higher-order derivatives) (CA-091).
The `(n+1)`-st derivative is the derivative of the `n`-th, and the second derivative is the
derivative of the derivative. -/
@[kb "openstaxcalculus2016" "1:§3.2 Definition (second and higher-order derivatives), p. 218"]
theorem higher_order_derivative (f : ℝ → ℝ) (n : ℕ) :
    iteratedDeriv (n + 1) f = deriv (iteratedDeriv n f) ∧ iteratedDeriv 2 f = deriv (deriv f) := by
  refine ⟨iteratedDeriv_succ, ?_⟩
  rw [iteratedDeriv_succ, iteratedDeriv_one]

/-- OpenStax Calculus 1:Theorem 3.1 (CA-092). A function differentiable at `a` is continuous at `a`. -/
@[kb "openstaxcalculus2016" "1:Theorem 3.1, p. 215"]
theorem differentiable_implies_continuous (f : ℝ → ℝ) (a : ℝ) (h : DifferentiableAt ℝ f a) :
    ContinuousAt f a :=
  h.continuousAt

/-- OpenStax Calculus 1:§3.2 Discussion (continuous but not differentiable: |x| at 0) (CA-093).
`|x|` is continuous but not differentiable at `0`. -/
@[kb "openstaxcalculus2016" "1:§3.2 Discussion (continuous but not differentiable: |x| at 0), p. 216"]
theorem abs_continuous_not_differentiable_at_zero :
    Continuous (abs : ℝ → ℝ) ∧ ¬ DifferentiableAt ℝ (abs : ℝ → ℝ) 0 :=
  ⟨continuous_abs, not_differentiableAt_abs_zero⟩

/-- OpenStax Calculus 1:Theorem 3.2 (CA-094). The derivative of a constant is `0`. -/
@[kb "openstaxcalculus2016" "1:Theorem 3.2, p. 225"]
theorem deriv_constant (c x : ℝ) : HasDerivAt (fun _ : ℝ => c) 0 x :=
  hasDerivAt_const x c

/-- OpenStax Calculus 1:Theorem 3.3 (CA-095). Power rule: `d/dx xⁿ = n xⁿ⁻¹`. -/
@[kb "openstaxcalculus2016" "1:Theorem 3.3, p. 226"]
theorem power_rule (n : ℕ) (x : ℝ) : HasDerivAt (fun y : ℝ => y ^ n) (n * x ^ (n - 1)) x :=
  hasDerivAt_pow n x

section Rules

variable {f g : ℝ → ℝ} {x : ℝ}

/-- OpenStax Calculus 1:Theorem 3.4 (CA-096). Sum rule: `(f + g)' = f' + g'`. -/
@[kb "openstaxcalculus2016" "1:Theorem 3.4, p. 227"]
theorem sum_rule (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (fun y => f y + g y) x = deriv f x + deriv g x :=
  deriv_add hf hg

/-- OpenStax Calculus 1:Theorem 3.4 (CA-097). Difference rule: `(f - g)' = f' - g'`. -/
@[kb "openstaxcalculus2016" "1:Theorem 3.4, p. 227"]
theorem difference_rule (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (fun y => f y - g y) x = deriv f x - deriv g x :=
  deriv_sub hf hg

/-- OpenStax Calculus 1:Theorem 3.4 (CA-098). Constant multiple rule: `(k f)' = k f'`. -/
@[kb "openstaxcalculus2016" "1:Theorem 3.4, p. 227"]
theorem constant_multiple_rule (k : ℝ) (hf : DifferentiableAt ℝ f x) :
    deriv (fun y => k * f y) x = k * deriv f x :=
  deriv_const_mul k hf

/-- OpenStax Calculus 1:Theorem 3.5 (CA-099). Product rule: `(f g)' = f' g + f g'`. -/
@[kb "openstaxcalculus2016" "1:Theorem 3.5, p. 229"]
theorem product_rule (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (fun y => f y * g y) x = deriv f x * g x + f x * deriv g x :=
  deriv_mul hf hg

/-- OpenStax Calculus 1:Theorem 3.6 (CA-100). Quotient rule: `(f/g)' = (f' g - f g')/g²`, `g x ≠ 0`. -/
@[kb "openstaxcalculus2016" "1:Theorem 3.6, p. 231"]
theorem quotient_rule (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hx : g x ≠ 0) :
    deriv (fun y => f y / g y) x = (deriv f x * g x - f x * deriv g x) / g x ^ 2 :=
  deriv_div hf hg hx

/-- OpenStax Calculus 1:Example 3.29 (CA-102). Product rule for three factors. -/
@[kb "openstaxcalculus2016" "1:Example 3.29, p. 233"]
theorem triple_product_rule {h : ℝ → ℝ} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h x) :
    deriv (fun y => f y * g y * h y) x =
      deriv f x * g x * h x + f x * deriv g x * h x + f x * g x * deriv h x := by
  change deriv (f * g * h) x = _
  rw [((hf.hasDerivAt.mul hg.hasDerivAt).mul hh.hasDerivAt).deriv]
  simp only [Pi.mul_apply]
  ring

end Rules

/-- OpenStax Calculus 1:Theorem 3.7 (CA-101).
`d/dx xⁿ = n xⁿ⁻¹` for an integer `n` (for `x ≠ 0`, or `n ≥ 0`); in particular negative `n`. -/
@[kb "openstaxcalculus2016" "1:Theorem 3.7, p. 231"]
theorem power_rule_integer (n : ℤ) (x : ℝ) (h : x ≠ 0 ∨ 0 ≤ n) :
    HasDerivAt (fun y : ℝ => y ^ n) (n * x ^ (n - 1)) x :=
  hasDerivAt_zpow n x h

/-- OpenStax Calculus 1:Theorem 3.8 (CA-105). `d/dx sin x = cos x`. -/
@[kb "openstaxcalculus2016" "1:Theorem 3.8, p. 250"]
theorem deriv_sin_eq (x : ℝ) : HasDerivAt Real.sin (Real.cos x) x :=
  Real.hasDerivAt_sin x

/-- OpenStax Calculus 1:Theorem 3.8 (CA-106). `d/dx cos x = -sin x`. -/
@[kb "openstaxcalculus2016" "1:Theorem 3.8, p. 250"]
theorem deriv_cos_eq (x : ℝ) : HasDerivAt Real.cos (-Real.sin x) x :=
  Real.hasDerivAt_cos x

/-- OpenStax Calculus 1:Theorem 3.9 (CA-107). `d/dx tan x = sec² x` where `cos x ≠ 0`. -/
@[kb "openstaxcalculus2016" "1:Theorem 3.9, p. 254"]
theorem deriv_tan_eq (x : ℝ) (hx : Real.cos x ≠ 0) :
    HasDerivAt Real.tan (1 / Real.cos x ^ 2) x :=
  Real.hasDerivAt_tan hx

/-- OpenStax Calculus 1:§3.6 Rule: The Chain Rule (CA-112).
`(f ∘ g)' (x) = f' (g x) g' (x)`. -/
@[kb "openstaxcalculus2016" "1:§3.6 Rule: The Chain Rule, p. 259"]
theorem chain_rule (f g : ℝ → ℝ) (x : ℝ) (hg : DifferentiableAt ℝ g x)
    (hf : DifferentiableAt ℝ f (g x)) :
    deriv (fun y => f (g y)) x = deriv f (g x) * deriv g x :=
  deriv_comp x hf hg

/-- OpenStax Calculus 1:§3.6 Rule: Power Rule for Composition of Functions (CA-113).
`d/dx (g x)ⁿ = n (g x)ⁿ⁻¹ g' x` for an integer `n` (where `g x ≠ 0` if `n < 0`). -/
@[kb "openstaxcalculus2016" "1:§3.6 Rule: Power Rule for Composition of Functions, p. 259"]
theorem power_rule_composition (g : ℝ → ℝ) (g' x : ℝ) (n : ℤ) (hg : HasDerivAt g g' x)
    (h : g x ≠ 0 ∨ 0 ≤ n) :
    HasDerivAt (fun y => g y ^ n) (n * g x ^ (n - 1) * g') x :=
  (hasDerivAt_zpow n (g x) h).comp x hg

/-- OpenStax Calculus 1:§3.6 Rule: Chain Rule for a Composition of Three Functions (CA-115).
`(f ∘ g ∘ k)' (x) = f' (g (k x)) g' (k x) k' (x)`. -/
@[kb "openstaxcalculus2016" "1:§3.6 Rule: Chain Rule for a Composition of Three Functions, p. 262"]
theorem chain_rule_three (f g k : ℝ → ℝ) (f' g' k' x : ℝ) (hk : HasDerivAt k k' x)
    (hg : HasDerivAt g g' (k x)) (hf : HasDerivAt f f' (g (k x))) :
    HasDerivAt (fun y => f (g (k y))) (f' * g' * k') x := by
  exact (hf.comp x (hg.comp x hk)).congr_deriv (by ring)

/-- OpenStax Calculus 1:Theorem 3.11 (CA-116).
If `f` has inverse `g` near `a`, `g` is continuous at `a` and `f' (g a) ≠ 0`, then
`g' a = 1 / f' (g a)`. -/
@[kb "openstaxcalculus2016" "1:Theorem 3.11, p. 268"]
theorem inverse_function_derivative (f g : ℝ → ℝ) (f' a : ℝ) (hg : ContinuousAt g a)
    (hf : HasDerivAt f f' (g a)) (hf' : f' ≠ 0) (hfg : ∀ᶠ y in 𝓝 a, f (g y) = y) :
    HasDerivAt g (1 / f') a := by
  simpa using HasDerivAt.of_local_left_inverse hg hf hf' hfg

/-- OpenStax Calculus 1:Theorem 3.12 (CA-117).
For `x > 0`: `d/dx x^(1/n) = (1/n) x^(1/n - 1)` and `d/dx x^(m/n) = (m/n) x^(m/n - 1)`. -/
@[kb "openstaxcalculus2016" "1:Theorem 3.12, p. 269"]
theorem rational_power_rule (n : ℕ) (m : ℤ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => y ^ ((1 : ℝ) / n)) ((1 / n) * x ^ ((1 : ℝ) / n - 1)) x ∧
      HasDerivAt (fun y : ℝ => y ^ ((m : ℝ) / n)) ((m / n) * x ^ ((m : ℝ) / n - 1)) x :=
  ⟨Real.hasDerivAt_rpow_const (Or.inl hx.ne'), Real.hasDerivAt_rpow_const (Or.inl hx.ne')⟩

/-- OpenStax Calculus 1:Theorem 3.13 (CA-118). `d/dx arcsin x = 1/√(1 - x²)` for `|x| < 1`. -/
@[kb "openstaxcalculus2016" "1:Theorem 3.13, p. 272"]
theorem deriv_arcsin_eq (x : ℝ) (hx : |x| < 1) :
    HasDerivAt Real.arcsin (1 / √(1 - x ^ 2)) x := by
  obtain ⟨h1, h2⟩ := abs_lt.1 hx
  exact Real.hasDerivAt_arcsin h1.ne' h2.ne

/-- OpenStax Calculus 1:Theorem 3.13 (CA-119). `d/dx arccos x = -1/√(1 - x²)` for `|x| < 1`. -/
@[kb "openstaxcalculus2016" "1:Theorem 3.13, p. 272"]
theorem deriv_arccos_eq (x : ℝ) (hx : |x| < 1) :
    HasDerivAt Real.arccos (-(1 / √(1 - x ^ 2))) x := by
  obtain ⟨h1, h2⟩ := abs_lt.1 hx
  exact Real.hasDerivAt_arccos h1.ne' h2.ne

/-- OpenStax Calculus 1:Theorem 3.13 (CA-120). `d/dx arctan x = 1/(1 + x²)`. -/
@[kb "openstaxcalculus2016" "1:Theorem 3.13, p. 272"]
theorem deriv_arctan_eq (x : ℝ) : HasDerivAt Real.arctan (1 / (1 + x ^ 2)) x :=
  Real.hasDerivAt_arctan x

/-- OpenStax Calculus 1:§3.9 Fact (limit defining e) (CA-123).
`(e^h - 1)/h → 1` as `h → 0`. -/
@[kb "openstaxcalculus2016" "1:§3.9 Fact (limit defining e), p. 286"]
theorem limit_exp_minus_one_over_h :
    Tendsto (fun h : ℝ => (Real.exp h - 1) / h) (𝓝[≠] 0) (𝓝 1) := by
  have := (derivative_as_limit_of_difference_quotient Real.exp 0 1).1
    (by simpa using Real.hasDerivAt_exp 0)
  simpa using this

/-- OpenStax Calculus 1:Theorem 3.14 (CA-124).
`d/dx eˣ = eˣ`, `d/dx e^(g x) = e^(g x) g' x`, and `∫ₐᵇ eˣ dx = eᵇ - eᵃ`. -/
@[kb "openstaxcalculus2016" "1:Theorem 3.14, p. 286"]
theorem deriv_and_integral_exp :
    (∀ x : ℝ, HasDerivAt Real.exp (Real.exp x) x) ∧
    (∀ (g : ℝ → ℝ) (g' x : ℝ), HasDerivAt g g' x →
      HasDerivAt (fun y => Real.exp (g y)) (Real.exp (g x) * g') x) ∧
    (∀ a b : ℝ, ∫ x in a..b, Real.exp x = Real.exp b - Real.exp a) :=
  ⟨Real.hasDerivAt_exp, fun _ _ _ hg => hg.exp, fun _ _ => integral_exp⟩

/-- OpenStax Calculus 1:Theorem 3.15 (CA-125).
`d/dx ln x = 1/x` for `x > 0`, and `d/dx ln (g x) = g' x / g x` where `g x > 0`. -/
@[kb "openstaxcalculus2016" "1:Theorem 3.15, p. 287"]
theorem deriv_log_eq :
    (∀ x : ℝ, 0 < x → HasDerivAt Real.log (1 / x) x) ∧
    (∀ (g : ℝ → ℝ) (g' x : ℝ), HasDerivAt g g' x → 0 < g x →
      HasDerivAt (fun y => Real.log (g y)) (g' / g x) x) :=
  ⟨fun x hx => by simpa using Real.hasDerivAt_log hx.ne', fun _ _ _ hg hx => hg.log hx.ne'⟩

/-- OpenStax Calculus 1:§3.9 Problem-Solving Strategy: Logarithmic Differentiation (CA-128).
For `f x > 0`, `(f^g)' = f^g (g' ln f + g f'/f)`. -/
@[kb "openstaxcalculus2016" "1:§3.9 Problem-Solving Strategy: Logarithmic Differentiation, p. 290"]
theorem logarithmic_differentiation (f g : ℝ → ℝ) (f' g' x : ℝ) (hf : HasDerivAt f f' x)
    (hg : HasDerivAt g g' x) (h : 0 < f x) :
    HasDerivAt (fun y => f y ^ g y)
      (f x ^ g x * (g' * Real.log (f x) + g x * f' / f x)) x := by
  have := hf.rpow hg h
  convert this using 1
  rw [Real.rpow_sub_one h.ne']
  field_simp
  ring

/-- OpenStax Calculus 1:Example 3.83 (CA-129). For `x > 0` and real `r`, `d/dx x^r = r x^(r-1)`. -/
@[kb "openstaxcalculus2016" "1:Example 3.83, p. 291"]
theorem power_rule_real (r x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => y ^ r) (r * x ^ (r - 1)) x :=
  Real.hasDerivAt_rpow_const (Or.inl hx.ne')

/-! ## Results proved in this library -/

/-- OpenStax Calculus 1:Theorem 3.9 (CA-108). `d/dx cot x = -csc² x` where `sin x ≠ 0`. -/
@[kb "openstaxcalculus2016" "1:Theorem 3.9, p. 254"]
theorem deriv_cot {x : ℝ} (h : Real.sin x ≠ 0) :
    HasDerivAt Real.cot (-(UndergradKB.Calculus.csc x ^ 2)) x :=
  UndergradKB.Calculus.hasDerivAt_cot h

/-- OpenStax Calculus 1:Theorem 3.9 (CA-109). `d/dx sec x = sec x tan x` where `cos x ≠ 0`. -/
@[kb "openstaxcalculus2016" "1:Theorem 3.9, p. 254"]
theorem deriv_sec {x : ℝ} (h : Real.cos x ≠ 0) :
    HasDerivAt UndergradKB.Calculus.sec (UndergradKB.Calculus.sec x * Real.tan x) x :=
  UndergradKB.Calculus.hasDerivAt_sec h

/-- OpenStax Calculus 1:Theorem 3.9 (CA-110). `d/dx csc x = -csc x cot x` where `sin x ≠ 0`. -/
@[kb "openstaxcalculus2016" "1:Theorem 3.9, p. 254"]
theorem deriv_csc {x : ℝ} (h : Real.sin x ≠ 0) :
    HasDerivAt UndergradKB.Calculus.csc (-(UndergradKB.Calculus.csc x * Real.cot x)) x :=
  UndergradKB.Calculus.hasDerivAt_csc h

/-- OpenStax Calculus 1:Theorem 3.10 (CA-114). Chain rule for the trigonometric functions: for
`g` differentiable at `x`, the six composite derivatives (with the nonvanishing conditions that
`tan, cot, sec, csc` need). -/
@[kb "openstaxcalculus2016" "1:Theorem 3.10, p. 262"]
theorem trig_chain_rule {g : ℝ → ℝ} {g' x : ℝ} (hg : HasDerivAt g g' x) :
    HasDerivAt (fun y => Real.sin (g y)) (g' * Real.cos (g x)) x ∧
    HasDerivAt (fun y => Real.cos (g y)) (-(g' * Real.sin (g x))) x ∧
    (Real.cos (g x) ≠ 0 →
      HasDerivAt (fun y => Real.tan (g y)) (g' * UndergradKB.Calculus.sec (g x) ^ 2) x) ∧
    (Real.sin (g x) ≠ 0 →
      HasDerivAt (fun y => Real.cot (g y)) (-(g' * UndergradKB.Calculus.csc (g x) ^ 2)) x) ∧
    (Real.cos (g x) ≠ 0 →
      HasDerivAt (fun y => UndergradKB.Calculus.sec (g y))
        (g' * (UndergradKB.Calculus.sec (g x) * Real.tan (g x))) x) ∧
    (Real.sin (g x) ≠ 0 →
      HasDerivAt (fun y => UndergradKB.Calculus.csc (g y))
        (-(g' * (UndergradKB.Calculus.csc (g x) * Real.cot (g x)))) x) :=
  ⟨UndergradKB.Calculus.hasDerivAt_sin_comp hg, UndergradKB.Calculus.hasDerivAt_cos_comp hg,
    fun h => UndergradKB.Calculus.hasDerivAt_tan_comp hg h,
    fun h => UndergradKB.Calculus.hasDerivAt_cot_comp hg h,
    fun h => UndergradKB.Calculus.hasDerivAt_sec_comp hg h,
    fun h => UndergradKB.Calculus.hasDerivAt_csc_comp hg h⟩

/-- OpenStax Calculus 1:Theorem 3.13 (CA-121). Derivatives of the inverse cotangent, secant and
cosecant (the latter two for `|x| > 1`). -/
@[kb "openstaxcalculus2016" "1:Theorem 3.13, p. 272"]
theorem deriv_arccot_arcsec_arccsc :
    (∀ x : ℝ, HasDerivAt UndergradKB.Calculus.arccot (-(1 / (1 + x ^ 2))) x) ∧
    (∀ {x : ℝ}, 1 < |x| →
      HasDerivAt UndergradKB.Calculus.arcsec (1 / (|x| * √(x ^ 2 - 1))) x) ∧
    (∀ {x : ℝ}, 1 < |x| →
      HasDerivAt UndergradKB.Calculus.arccsc (-(1 / (|x| * √(x ^ 2 - 1)))) x) :=
  ⟨UndergradKB.Calculus.hasDerivAt_arccot, @UndergradKB.Calculus.hasDerivAt_arcsec,
    @UndergradKB.Calculus.hasDerivAt_arccsc⟩

/-- OpenStax Calculus 1:§3.8 Problem-Solving Strategy: Implicit Differentiation (CA-122). If
`F(t, y(t)) = c` near `x`, `y` is differentiable at `x` and `F` has partial derivatives `Fx, Fy` at
`(x, y x)`, then `Fx + Fy y' = 0`, hence `y' = -Fx/Fy` when `Fy ≠ 0`. -/
@[kb "openstaxcalculus2016" "1:§3.8 Problem-Solving Strategy: Implicit Differentiation, p. 277"]
theorem implicit_differentiation_strategy {F : ℝ → ℝ → ℝ} {y : ℝ → ℝ} {x y' Fx Fy c : ℝ}
    (hF : HasFDerivAt (fun p : ℝ × ℝ => F p.1 p.2)
      (Fx • ContinuousLinearMap.fst ℝ ℝ ℝ + Fy • ContinuousLinearMap.snd ℝ ℝ ℝ) (x, y x))
    (hy : HasDerivAt y y' x) (hloc : ∀ᶠ t in 𝓝 x, F t (y t) = c) :
    Fx + Fy * y' = 0 ∧ (Fy ≠ 0 → y' = -Fx / Fy) :=
  ⟨UndergradKB.Calculus.implicit_differentiation hF hy hloc,
    fun hFy => UndergradKB.Calculus.implicit_differentiation_eq hF hy hloc hFy⟩

/-- OpenStax Calculus 1:Theorem 3.16 (CA-126). For `b > 0`, `d/dx b^g(x) = b^g(x) ln b g'(x)`;
for `b ≠ 1`, `b^x / ln b` is an antiderivative of `b^x`, and `∫ b^x dx = (b^β - b^α)/ln b`. -/
@[kb "openstaxcalculus2016" "1:Theorem 3.16, p. 289"]
theorem deriv_and_integral_rpow_base {b : ℝ} (hb : 0 < b) :
    (∀ {g : ℝ → ℝ} {g' x : ℝ}, HasDerivAt g g' x →
      HasDerivAt (fun y => b ^ g y) (b ^ g x * Real.log b * g') x) ∧
    (b ≠ 1 → ∀ x : ℝ, HasDerivAt (fun y : ℝ => b ^ y / Real.log b) (b ^ x) x) ∧
    (b ≠ 1 → ∀ α β : ℝ, ∫ x in α..β, b ^ x = (b ^ β - b ^ α) / Real.log b) :=
  ⟨fun hg => UndergradKB.Calculus.hasDerivAt_rpow_comp hb hg,
    fun hb1 x => UndergradKB.Calculus.hasDerivAt_rpow_div_log hb hb1 x,
    fun hb1 α β => UndergradKB.Calculus.integral_rpow_base hb hb1 α β⟩

/-- OpenStax Calculus 1:Theorem 3.16 (CA-127). For `b ≠ 1`, `d/dx log_b g(x) = g'(x)/(g(x) ln b)`
where `g(x) ≠ 0`. -/
@[kb "openstaxcalculus2016" "1:Theorem 3.16, p. 289"]
theorem deriv_logb_comp (b : ℝ) {g : ℝ → ℝ} {g' x : ℝ} (hg : HasDerivAt g g' x) (hx : g x ≠ 0) :
    HasDerivAt (fun y => Real.logb b (g y)) (g' / (g x * Real.log b)) x :=
  UndergradKB.Calculus.hasDerivAt_logb_comp b hg hx

/-! ## Wave 3: further results -/

/-- OpenStax Calculus 1:§3.9 Definition (natural exponential function) (CA-034). The slope of the
tangent to `e^x` at `0` is `1`, the base `b > 0` with this property is `e`, and the natural logarithm
is the inverse of the natural exponential. -/
@[kb "openstaxcalculus2016" "1:§3.9 Definition (natural exponential function), p. 284"]
theorem natural_exponential_def :
    HasDerivAt Real.exp 1 0 ∧
    (∀ {b : ℝ}, 0 < b → (HasDerivAt (fun x : ℝ => b ^ x) 1 0 ↔ b = Real.exp 1)) ∧
    ((∀ x : ℝ, Real.log (Real.exp x) = x) ∧ ∀ x : ℝ, 0 < x → Real.exp (Real.log x) = x) :=
  ⟨UndergradKB.Calculus.hasDerivAt_exp_zero_slope_one,
    @UndergradKB.Calculus.hasDerivAt_rpow_zero_eq_one_iff,
    UndergradKB.Calculus.log_inverse_of_exp⟩

/-- OpenStax Calculus 1:§3.1 Definition (tangent line) (CA-085). The tangent line at `a` is
`y = f a + f'(a) (x - a)`; it is the only line through `(a, f a)` approximating `f` to first order,
and its slope is the limit of the difference quotients. -/
@[kb "openstaxcalculus2016" "1:§3.1 Definition (tangent line), p. 199"]
theorem tangent_line_def (f : ℝ → ℝ) (a : ℝ) :
    (∀ x : ℝ, UndergradKB.Calculus.tangentLine f a x = f a + deriv f a * (x - a)) ∧
    (∀ m : ℝ, ((fun x => f x - (f a + m * (x - a))) =o[𝓝 a] fun x => x - a) ↔
      HasDerivAt f m a) ∧
    (∀ {m : ℝ}, ((fun x => f x - (f a + m * (x - a))) =o[𝓝 a] fun x => x - a) →
      DifferentiableAt ℝ f a ∧ m = deriv f a) ∧
    (∀ m : ℝ, HasDerivAt f m a ↔ Tendsto (slope f a) (𝓝[≠] a) (𝓝 m)) :=
  ⟨fun _ => rfl, UndergradKB.Calculus.isLittleO_line_iff_hasDerivAt f a,
    @UndergradKB.Calculus.tangentLine_unique f a, fun _ => hasDerivAt_iff_tendsto_slope⟩

/-- OpenStax Calculus 1:Example 3.45 (CA-111). The derivatives of sine and cosine repeat with period
four: the `n`th one is determined by `n` modulo `4`. -/
@[kb "openstaxcalculus2016" "1:Example 3.45, p. 255"]
theorem iterated_derivatives_sin_cos (n : ℕ) :
    iteratedDeriv n Real.sin =
      (if n % 4 = 0 then Real.sin else if n % 4 = 1 then Real.cos
        else if n % 4 = 2 then -Real.sin else -Real.cos) ∧
    iteratedDeriv n Real.cos =
      (if n % 4 = 0 then Real.cos else if n % 4 = 1 then -Real.sin
        else if n % 4 = 2 then -Real.cos else Real.sin) ∧
    iteratedDeriv (n + 4) Real.sin = iteratedDeriv n Real.sin ∧
    iteratedDeriv (n + 4) Real.cos = iteratedDeriv n Real.cos :=
  ⟨UndergradKB.Calculus.iteratedDeriv_sin n, UndergradKB.Calculus.iteratedDeriv_cos n,
    UndergradKB.Calculus.iteratedDeriv_sin_add_four n,
    UndergradKB.Calculus.iteratedDeriv_cos_add_four n⟩

end UndergradKB.Calculus.Course.V1C3
