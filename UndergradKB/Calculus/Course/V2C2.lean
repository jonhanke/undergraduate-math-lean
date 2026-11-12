import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import UndergradKB.Common.Attr
import UndergradKB.Calculus.Hyperbolic
import UndergradKB.Calculus.FirstOrderODE
import UndergradKB.Calculus.MassCentroid

/-! Course layer, OpenStax Calculus Volume 2, Chapter 2 (applications of integration; the
logarithm and exponential of section 2.7 and compound interest of section 2.8). -/

namespace UndergradKB.Calculus.Course.V2C2

open Set Filter Topology
open scoped Interval

/-- OpenStax Calculus 2:§2.7 Definition (the number e) (CA-035). The area under `1/t` from `1`
to `e = exp 1` equals `1`. -/
@[kb "openstaxcalculus2016" "2:§2.7 Definition (the number e), p. 205"]
theorem integral_inv_one_to_e : ∫ t in (1 : ℝ)..Real.exp 1, t⁻¹ = 1 := by
  rw [integral_inv_of_pos one_pos (Real.exp_pos 1), div_one, Real.log_exp]

/-- OpenStax Calculus 2:§2.7 Definition (the number e) (CA-035). `e` is the unique `x > 0` with
`∫ 1..x dt/t = 1`. -/
@[kb "openstaxcalculus2016" "2:§2.7 Definition (the number e), p. 205"]
theorem e_unique_by_integral {x : ℝ} (hx : 0 < x) (h : ∫ t in (1 : ℝ)..x, t⁻¹ = 1) :
    x = Real.exp 1 := by
  rw [integral_inv_of_pos one_pos hx, div_one] at h
  rw [← h, Real.exp_log hx]

/-- OpenStax Calculus 2:§2.7 Definition (natural logarithm) (CA-037). For `x > 0`,
`ln x = ∫ 1..x dt/t`. -/
@[kb "openstaxcalculus2016" "2:§2.7 Definition (natural logarithm), p. 202"]
theorem log_eq_integral_inv {x : ℝ} (hx : 0 < x) : Real.log x = ∫ t in (1 : ℝ)..x, t⁻¹ := by
  rw [integral_inv_of_pos one_pos hx, div_one]

/-- OpenStax Calculus 2:§2.7 Definition (exponential function) (CA-038). `exp (ln x) = x` for
`x > 0`. -/
@[kb "openstaxcalculus2016" "2:§2.7 Definition (exponential function), p. 206"]
theorem exp_log_eq {x : ℝ} (hx : 0 < x) : Real.exp (Real.log x) = x :=
  Real.exp_log hx

/-- OpenStax Calculus 2:§2.7 Definition (exponential function) (CA-038). `ln (exp x) = x`. -/
@[kb "openstaxcalculus2016" "2:§2.7 Definition (exponential function), p. 206"]
theorem log_exp_eq (x : ℝ) : Real.log (Real.exp x) = x :=
  Real.log_exp x

/-- OpenStax Calculus 2:§2.7 Definition (b^x) (CA-039). For `b > 0`, `b^x = e^(x ln b)`. -/
@[kb "openstaxcalculus2016" "2:§2.7 Definition (b^x), p. 208"]
theorem rpow_eq_exp_mul_log {b : ℝ} (hb : 0 < b) (x : ℝ) : b ^ x = Real.exp (x * Real.log b) := by
  rw [Real.rpow_def_of_pos hb, mul_comm]

/-- OpenStax Calculus 2:§2.8 Derivation of continuous compounding (CA-075). `(1 + r/n)^(n t)`
tends to `e^(r t)` as `n → ∞`, so continuous compounding of `P` yields `P e^(r t)`. -/
@[kb "openstaxcalculus2016" "2:§2.8 Derivation of continuous compounding, p. 214"]
theorem compound_interest_limit (r t : ℝ) :
    Tendsto (fun n : ℕ => (1 + r / n) ^ ((n : ℝ) * t)) atTop (𝓝 (Real.exp (r * t))) := by
  have h1 := Real.tendsto_one_add_div_pow_exp r
  have h2 := h1.rpow_const (p := t) (Or.inl (Real.exp_pos r).ne')
  rw [← Real.exp_mul] at h2
  refine h2.congr' ?_
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < 1 + r / n := by
    have := (tendsto_const_div_atTop_nhds_zero_nat r).const_add 1
    rw [add_zero] at this
    exact this.eventually (lt_mem_nhds (one_pos : (0 : ℝ) < 1))
  filter_upwards [hpos] with n hn
  rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]

/-- OpenStax Calculus 2:Theorem 2.16 (CA-083). `ln` is differentiable, hence continuous, on its
domain (here on the nonzero reals, where `ln x = ln |x|`). -/
@[kb "openstaxcalculus2016" "2:Theorem 2.16, p. 202"]
theorem log_differentiable_continuous :
    DifferentiableOn ℝ Real.log {0}ᶜ ∧ ContinuousOn Real.log {0}ᶜ :=
  ⟨Real.differentiableOn_log, Real.continuousOn_log⟩

/-! ## Results proved in this library -/

open UndergradKB.Calculus

/-- OpenStax Calculus 2:§2.9 Table 2.3 (CA-045). Domains and ranges of the inverse hyperbolic
functions: each is a bijection from its domain onto its range. -/
@[kb "openstaxcalculus2016" "2:§2.9 Table 2.3 (inverse hyperbolic function domains and ranges), p. 224"]
theorem inverse_hyperbolic_domains_ranges :
    Function.Bijective Real.arsinh ∧
    BijOn Real.arcosh (Ici 1) (Ici 0) ∧
    BijOn Real.artanh (Ioo (-1) 1) univ ∧
    BijOn arcoth {x : ℝ | 1 < |x|} {y : ℝ | y ≠ 0} ∧
    BijOn arsech (Ioc 0 1) (Ici 0) ∧
    BijOn arcsch {x : ℝ | x ≠ 0} {y : ℝ | y ≠ 0} :=
  ⟨UndergradKB.Calculus.arsinh_bijective, UndergradKB.Calculus.arcosh_bijOn',
    UndergradKB.Calculus.artanh_bijOn', UndergradKB.Calculus.arcoth_bijOn,
    UndergradKB.Calculus.arsech_bijOn, UndergradKB.Calculus.arcsch_bijOn⟩

/-- OpenStax Calculus 2:§2.9 Table 2.2 (CA-130). The derivatives of the six hyperbolic functions
(`tanh' = sech²`, `coth' = -csch²`, `sech' = -sech tanh`, `csch' = -csch coth`). -/
@[kb "openstaxcalculus2016" "2:§2.9 Table 2.2 (derivatives of the hyperbolic functions), p. 222"]
theorem hyperbolic_derivatives :
    (∀ x : ℝ, HasDerivAt Real.sinh (Real.cosh x) x) ∧
    (∀ x : ℝ, HasDerivAt Real.cosh (Real.sinh x) x) ∧
    (∀ x : ℝ, HasDerivAt Real.tanh (sech x ^ 2) x) ∧
    (∀ x : ℝ, x ≠ 0 → HasDerivAt coth (-(csch x ^ 2)) x) ∧
    (∀ x : ℝ, HasDerivAt sech (-(sech x * Real.tanh x)) x) ∧
    (∀ x : ℝ, x ≠ 0 → HasDerivAt csch (-(csch x * coth x)) x) :=
  ⟨UndergradKB.Calculus.hasDerivAt_sinh', UndergradKB.Calculus.hasDerivAt_cosh',
    UndergradKB.Calculus.hasDerivAt_tanh, fun _ hx => UndergradKB.Calculus.hasDerivAt_coth hx,
    UndergradKB.Calculus.hasDerivAt_sech, fun _ hx => UndergradKB.Calculus.hasDerivAt_csch hx⟩

/-- OpenStax Calculus 2:§2.9 Table 2.4 (CA-131). The derivatives of the six inverse hyperbolic
functions, each on its natural domain. -/
@[kb "openstaxcalculus2016" "2:§2.9 Table 2.4 (derivatives of inverse hyperbolic functions), p. 225"]
theorem inverse_hyperbolic_derivatives :
    (∀ x : ℝ, HasDerivAt Real.arsinh (1 / √(x ^ 2 + 1)) x) ∧
    (∀ x : ℝ, 1 < x → HasDerivAt Real.arcosh (1 / √(x ^ 2 - 1)) x) ∧
    (∀ x : ℝ, |x| < 1 → HasDerivAt Real.artanh (1 / (1 - x ^ 2)) x) ∧
    (∀ x : ℝ, 1 < |x| → HasDerivAt arcoth (1 / (1 - x ^ 2)) x) ∧
    (∀ x : ℝ, 0 < x → x < 1 → HasDerivAt arsech (-1 / (x * √(1 - x ^ 2))) x) ∧
    (∀ x : ℝ, x ≠ 0 → HasDerivAt arcsch (-1 / (|x| * √(1 + x ^ 2))) x) :=
  ⟨UndergradKB.Calculus.hasDerivAt_arsinh', fun _ hx => UndergradKB.Calculus.hasDerivAt_arcosh' hx,
    fun _ hx => UndergradKB.Calculus.hasDerivAt_artanh hx,
    fun _ hx => UndergradKB.Calculus.hasDerivAt_arcoth hx,
    fun _ hx hx1 => UndergradKB.Calculus.hasDerivAt_arsech hx hx1,
    fun _ hx => UndergradKB.Calculus.hasDerivAt_arcsch hx⟩

/-- OpenStax Calculus 2:§2.9 Integration formulas for hyperbolic functions (CA-211). Definite
integrals of `sinh`, `cosh`, `sech²`, `sech tanh` and, when `0` is not between the limits,
`csch²` and `csch coth`. -/
@[kb "openstaxcalculus2016" "2:§2.9 Integration formulas for hyperbolic functions, p. 223"]
theorem hyperbolic_integration_formulas (a b : ℝ) :
    (∫ x in a..b, Real.sinh x = Real.cosh b - Real.cosh a) ∧
    (∫ x in a..b, Real.cosh x = Real.sinh b - Real.sinh a) ∧
    (∫ x in a..b, sech x ^ 2 = Real.tanh b - Real.tanh a) ∧
    (∫ x in a..b, sech x * Real.tanh x = sech a - sech b) ∧
    (0 ∉ uIcc a b → ∫ x in a..b, csch x ^ 2 = coth a - coth b) ∧
    (0 ∉ uIcc a b → ∫ x in a..b, csch x * coth x = csch a - csch b) :=
  ⟨UndergradKB.Calculus.integral_sinh a b, UndergradKB.Calculus.integral_cosh a b,
    UndergradKB.Calculus.integral_sech_sq a b, UndergradKB.Calculus.integral_sech_mul_tanh a b,
    fun h => UndergradKB.Calculus.integral_csch_sq h,
    fun h => UndergradKB.Calculus.integral_csch_mul_coth h⟩

/-- OpenStax Calculus 2:§2.9 Integration formulas with inverse hyperbolic functions (CA-212).
Antiderivative formulas for `1/√(a²+u²)`, `1/√(u²-a²)`, `1/(a²-u²)` (two ranges),
`1/(u√(a²-u²))` and `1/(u√(a²+u²))`, in terms of inverse hyperbolic functions of `u/a`. -/
@[kb "openstaxcalculus2016" "2:§2.9 Integration formulas with inverse hyperbolic functions, p. 226"]
theorem inverse_hyperbolic_integration_formulas {a : ℝ} (ha : 0 < a) :
    (∀ u : ℝ, HasDerivAt (fun y => Real.arsinh (y / a)) (1 / √(a ^ 2 + u ^ 2)) u) ∧
    (∀ u : ℝ, a < u →
      HasDerivAt (fun y => Real.arcosh (y / a)) (1 / √(u ^ 2 - a ^ 2)) u) ∧
    (∀ u : ℝ, |u| < a →
      HasDerivAt (fun y => (1 / a) * Real.artanh (y / a)) (1 / (a ^ 2 - u ^ 2)) u) ∧
    (∀ u : ℝ, a < |u| →
      HasDerivAt (fun y => (1 / a) * arcoth (y / a)) (1 / (a ^ 2 - u ^ 2)) u) ∧
    (∀ u : ℝ, 0 < u → u < a →
      HasDerivAt (fun y => -(1 / a) * arsech (y / a)) (1 / (u * √(a ^ 2 - u ^ 2))) u) ∧
    (∀ u : ℝ, 0 < u →
      HasDerivAt (fun y => -(1 / a) * arcsch (y / a)) (1 / (u * √(a ^ 2 + u ^ 2))) u) :=
  ⟨fun u => UndergradKB.Calculus.hasDerivAt_arsinh_div ha u,
    fun _ hu => UndergradKB.Calculus.hasDerivAt_arcosh_div ha hu,
    fun _ hu => UndergradKB.Calculus.hasDerivAt_artanh_div ha hu,
    fun _ hu => UndergradKB.Calculus.hasDerivAt_arcoth_div ha hu,
    fun _ hu hua => UndergradKB.Calculus.hasDerivAt_arsech_div ha hu hua,
    fun _ hu => UndergradKB.Calculus.hasDerivAt_arcsch_div ha hu⟩

/-- OpenStax Calculus 2:§2.8 Rule: Exponential Growth Model (CA-305). For `k > 0`, a function with
`y' = k y` and `y 0 = y0` is exactly `y t = y0 e^(k t)`. -/
@[kb "openstaxcalculus2016" "2:§2.8 Rule: Exponential Growth Model, p. 212"]
theorem exponential_growth_model {y : ℝ → ℝ} {k y0 : ℝ} (hk : 0 < k) (h0 : y 0 = y0) :
    (∀ t, HasDerivAt y (k * y t) t) ↔ ∀ t, y t = y0 * Real.exp (k * t) :=
  UndergradKB.Calculus.exp_growth_ivp hk h0

/-- OpenStax Calculus 2:§2.8 Rule: Exponential Decay Model (CA-307). For `k > 0`, a function with
`y' = -k y` and `y 0 = y0` is exactly `y t = y0 e^(-k t)`. -/
@[kb "openstaxcalculus2016" "2:§2.8 Rule: Exponential Decay Model, p. 215"]
theorem exponential_decay_model {y : ℝ → ℝ} {k y0 : ℝ} (hk : 0 < k) (h0 : y 0 = y0) :
    (∀ t, HasDerivAt y (-k * y t) t) ↔ ∀ t, y t = y0 * Real.exp (-k * t) :=
  UndergradKB.Calculus.exp_decay_ivp hk h0

/-! ## Wave 3: further results -/

open MeasureTheory in
/-- OpenStax Calculus 2:§2.6 Definition (centroid) (CA-276). The centroid of a plane region `R`
(a lamina of constant density `ρ`) is the pair of its moments about the axes divided by its mass,
where the mass is `ρ` times the area. -/
@[kb "openstaxcalculus2016" "2:§2.6 Definition (centroid), p. 189"]
theorem centroid_definition (ρ : ℝ) (R : Set (ℝ × ℝ)) :
    UndergradKB.Calculus.laminaCenter ρ R =
      (ρ * (∫ q in R, q.1) / (ρ * volume.real R), ρ * (∫ q in R, q.2) / (ρ * volume.real R)) :=
  rfl

/-- OpenStax Calculus 2:§2.8 Definition (doubling time) (CA-306). With `k > 0`, the quantity
`y0 e^(k t)` is multiplied by `2` over a time span of `ln 2 / k`, starting at any time `t`. -/
@[kb "openstaxcalculus2016" "2:§2.8 Definition (doubling time), p. 215"]
theorem doubling_time_formula {y0 k : ℝ} (hk : 0 < k) (t : ℝ) :
    0 < Real.log 2 / k ∧
      y0 * Real.exp (k * (t + Real.log 2 / k)) = 2 * (y0 * Real.exp (k * t)) :=
  UndergradKB.Calculus.doubling_time hk t

/-- OpenStax Calculus 2:§2.8 Newton's law of cooling (CA-308). The temperature satisfies
`T' = -k (T - Ta)` at every time exactly when `T t = Ta + (T 0 - Ta) e^(-k t)`. -/
@[kb "openstaxcalculus2016" "2:§2.8 Newton's law of cooling, p. 216"]
theorem newtons_cooling_law_solution {T : ℝ → ℝ} {k Ta : ℝ} :
    (∀ t, HasDerivAt T (-k * (T t - Ta)) t) ↔ ∀ t, T t = Ta + (T 0 - Ta) * Real.exp (-k * t) :=
  UndergradKB.Calculus.newton_cooling_iff

/-- OpenStax Calculus 2:§2.8 Definition (half-life) (CA-309). With `k > 0`, the quantity
`y0 e^(-k t)` is halved over a time span of `ln 2 / k`, starting at any time `t`. -/
@[kb "openstaxcalculus2016" "2:§2.8 Definition (half-life), p. 217"]
theorem half_life_formula {y0 k : ℝ} (hk : 0 < k) (t : ℝ) :
    0 < Real.log 2 / k ∧
      y0 * Real.exp (-k * (t + Real.log 2 / k)) = y0 * Real.exp (-k * t) / 2 :=
  UndergradKB.Calculus.half_life hk t

end UndergradKB.Calculus.Course.V2C2
