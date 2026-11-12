import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import UndergradKB.Calculus.Bessel
import UndergradKB.Calculus.ODEExtras
import UndergradKB.Calculus.SecondOrderODE
import UndergradKB.Common.Attr

/-! Course layer, OpenStax Calculus Volume 3, Chapter 7 (second-order differential equations),
including the background items it recalls (Euler's formula, uniqueness of power series, Cramer's
rule). -/

namespace UndergradKB.Calculus.Course.V3C7

open Filter Topology

/-- OpenStax Calculus 3:§7.1 Euler's formula (CA-387). For real `x`, `e^(ix) = cos x + i sin x`. -/
@[kb "openstaxcalculus2016" "3:§7.1 Euler's formula (recalled from earlier chapter), p. 758"]
theorem euler_formula (x : ℝ) :
    Complex.exp (x * Complex.I) = Real.cos x + Real.sin x * Complex.I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- OpenStax Calculus 3:§7.4 uniqueness of power series (CA-388). If two real power series
`∑ aₙ xⁿ` and `∑ bₙ xⁿ` both represent the same function near `0`, their coefficients agree. -/
@[kb "openstaxcalculus2016" "3:§7.4 (uniqueness of power series, used in Example 7.25), p. 793"]
theorem power_series_coefficients_unique {f : ℝ → ℝ} {a b : ℕ → ℝ}
    (ha : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℝ a) 0)
    (hb : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℝ b) 0) : a = b := by
  have h := ha.eq_formalMultilinearSeries hb
  funext n
  have := congrArg (fun p : FormalMultilinearSeries ℝ ℝ ℝ => p n (fun _ => (1 : ℝ))) h
  simpa [FormalMultilinearSeries.ofScalars_apply_eq] using this

/-- OpenStax Calculus 3:§7.4 uniqueness of power series (CA-388). If a power series represents the
zero function near `0`, every coefficient vanishes (so in a power-series solution each
coefficient of `xⁿ` must vanish separately). -/
@[kb "openstaxcalculus2016" "3:§7.4 (uniqueness of power series, used in Example 7.25), p. 793"]
theorem power_series_zero_coefficients {a : ℕ → ℝ}
    (ha : HasFPowerSeriesAt (fun _ : ℝ => (0 : ℝ)) (FormalMultilinearSeries.ofScalars ℝ a) 0) :
    a = 0 := by
  have h := ha.eq_zero
  funext n
  have := congrArg (fun p : FormalMultilinearSeries ℝ ℝ ℝ => p n (fun _ => (1 : ℝ))) h
  simpa [FormalMultilinearSeries.ofScalars_apply_eq] using this

/-- OpenStax Calculus 3:§7.2 Rule: Cramer's Rule (CA-680). If `a₁x + b₁y = c₁`,
`a₂x + b₂y = c₂` and `D = a₁b₂ - a₂b₁ ≠ 0`, then `x = (c₁b₂ - c₂b₁)/D` and
`y = (a₁c₂ - a₂c₁)/D`. -/
@[kb "openstaxcalculus2016" "3:§7.2 Rule: Cramer's Rule, p. 771"]
theorem cramers_rule_two_by_two {a₁ b₁ c₁ a₂ b₂ c₂ x y : ℝ} (h₁ : a₁ * x + b₁ * y = c₁)
    (h₂ : a₂ * x + b₂ * y = c₂) (hD : a₁ * b₂ - a₂ * b₁ ≠ 0) :
    x = (c₁ * b₂ - c₂ * b₁) / (a₁ * b₂ - a₂ * b₁) ∧
    y = (a₁ * c₂ - a₂ * c₁) / (a₁ * b₂ - a₂ * b₁) := by
  constructor
  · rw [eq_div_iff hD]
    linear_combination b₂ * h₁ - b₁ * h₂
  · rw [eq_div_iff hD]
    linear_combination a₁ * h₂ - a₂ * h₁

/-- OpenStax Calculus 3:§7.2 Rule: Cramer's Rule (CA-680). The same in matrix form, for any
`n × n` system over a commutative ring: `A (cramer A b) = det A • b`, where the `i`-th entry of
`cramer A b` is the determinant of `A` with column `i` replaced by `b`. -/
@[kb "openstaxcalculus2016" "3:§7.2 Rule: Cramer's Rule, p. 771"]
theorem cramers_rule_matrix {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) (b : n → ℝ) :
    A.mulVec (Matrix.cramer A b) = A.det • b ∧
      ∀ i, Matrix.cramer A b i = (A.updateCol i b).det :=
  ⟨Matrix.mulVec_cramer A b, fun i => Matrix.cramer_apply A b i⟩

/-! ## Results proved in this library -/

section ProvedInKB

open UndergradKB.Calculus (LinSol ConstSol LinDepOn)
open UndergradKB.Calculus.ODEExtras (ForcedSpring EntireCoeff psum)

/-- OpenStax Calculus 3:Theorem 7.1 (CA-667).
Any linear combination of two solutions of a linear homogeneous equation is a solution. -/
@[kb "openstaxcalculus2016" "3:Theorem 7.1, p. 754"]
theorem superposition_principle {p q y1 y2 : ℝ → ℝ} (h1 : LinSol p q (fun _ => 0) y1)
    (h2 : LinSol p q (fun _ => 0) y2) (c1 c2 : ℝ) :
    LinSol p q (fun _ => 0) (fun x => c1 * y1 x + c2 * y2 x) :=
  UndergradKB.Calculus.superposition h1 h2 c1 c2

/-- OpenStax Calculus 3:Theorem 7.2 (CA-669).
Two functions are linearly dependent on a set exactly when one is a constant multiple of the other
there. -/
@[kb "openstaxcalculus2016" "3:Theorem 7.2, p. 755"]
theorem linearly_dependent_iff_constant_multiple (s : Set ℝ) (f g : ℝ → ℝ) :
    LinDepOn s f g ↔ (∃ k : ℝ, ∀ x ∈ s, f x = k * g x) ∨ (∃ k : ℝ, ∀ x ∈ s, g x = k * f x) :=
  UndergradKB.Calculus.linDepOn_iff s f g

/-- OpenStax Calculus 3:Theorem 7.3 (CA-670).
If `y₁, y₂` are linearly independent solutions of a homogeneous second-order linear equation with
continuous coefficients, every solution is `c₁ y₁ + c₂ y₂`. -/
@[kb "openstaxcalculus2016" "3:Theorem 7.3, p. 756"]
theorem general_solution_linearly_independent {p q y1 y2 : ℝ → ℝ} (hp : Continuous p)
    (hq : Continuous q) (h1 : LinSol p q (fun _ => 0) y1) (h2 : LinSol p q (fun _ => 0) y2)
    (hind : ¬ LinDepOn Set.univ y1 y2) {y : ℝ → ℝ} (hy : LinSol p q (fun _ => 0) y) :
    ∃ c1 c2 : ℝ, ∀ x, y x = c1 * y1 x + c2 * y2 x :=
  UndergradKB.Calculus.general_solution_of_independent hp hq h1 h2 hind hy

/-- OpenStax Calculus 3:§7.1 Distinct Real Roots (CA-672).
For `a y'' + b y' + c y = 0` with distinct real characteristic roots `r₁, r₂`, the solutions are
exactly `c₁ e^(r₁ x) + c₂ e^(r₂ x)`. -/
@[kb "openstaxcalculus2016" "3:§7.1 Distinct Real Roots (unnumbered), p. 757"]
theorem solution_distinct_real_roots {a b c r1 r2 : ℝ} (ha : a ≠ 0)
    (hr1 : a * r1 ^ 2 + b * r1 + c = 0) (hr2 : a * r2 ^ 2 + b * r2 + c = 0) (hne : r1 ≠ r2)
    (y : ℝ → ℝ) :
    ConstSol a b c (fun _ => 0) y ↔
      ∃ c1 c2 : ℝ, ∀ x, y x = c1 * Real.exp (r1 * x) + c2 * Real.exp (r2 * x) :=
  UndergradKB.Calculus.general_solution_distinct_real_roots ha hr1 hr2 hne y

/-- OpenStax Calculus 3:§7.1 Single Repeated Real Root (CA-673).
With a repeated root `r = -b / (2a)` the solutions are exactly `c₁ e^(r x) + c₂ x e^(r x)`. -/
@[kb "openstaxcalculus2016" "3:§7.1 Single Repeated Real Root (unnumbered), p. 757"]
theorem solution_repeated_real_root {a b c : ℝ} (ha : a ≠ 0) (hd : b ^ 2 = 4 * a * c)
    (y : ℝ → ℝ) :
    ConstSol a b c (fun _ => 0) y ↔
      ∃ c1 c2 : ℝ, ∀ x, y x =
        c1 * Real.exp (-b / (2 * a) * x) + c2 * x * Real.exp (-b / (2 * a) * x) :=
  UndergradKB.Calculus.general_solution_repeated_root ha hd y

/-- OpenStax Calculus 3:§7.1 Complex Conjugate Roots (CA-674).
With roots `α ± β i` (`α = -b / (2a)`, `β = √(4ac - b²) / (2a)`) the real solutions are exactly
`e^(α x) (c₁ cos β x + c₂ sin β x)`. -/
@[kb "openstaxcalculus2016" "3:§7.1 Complex Conjugate Roots (unnumbered), p. 758"]
theorem solution_complex_conjugate_roots {a b c : ℝ} (ha : a ≠ 0) (hd : b ^ 2 < 4 * a * c)
    (y : ℝ → ℝ) :
    ConstSol a b c (fun _ => 0) y ↔
      ∃ c1 c2 : ℝ, ∀ x, y x = Real.exp (-b / (2 * a) * x) *
        (c1 * Real.cos (√(4 * a * c - b ^ 2) / (2 * a) * x) +
          c2 * Real.sin (√(4 * a * c - b ^ 2) / (2 * a) * x)) :=
  UndergradKB.Calculus.general_solution_complex_roots ha hd y

/-- OpenStax Calculus 3:Theorem 7.4 (CA-678).
A function solves the nonhomogeneous equation exactly when it is a particular solution plus a
solution of the complementary (homogeneous) equation. -/
@[kb "openstaxcalculus2016" "3:Theorem 7.4, p. 765"]
theorem general_solution_particular_plus_complementary {p q f yp : ℝ → ℝ} (hp : LinSol p q f yp)
    (y : ℝ → ℝ) :
    LinSol p q f y ↔ ∃ yc, LinSol p q (fun _ => 0) yc ∧ ∀ x, y x = yp x + yc x :=
  UndergradKB.Calculus.general_eq_particular_add_complementary hp y

/-- OpenStax Calculus 3:Table 7.2 (CA-679).
Undetermined coefficients for `a y'' + b y' + c y`: the guesses `A e^(r x)` (or `A x e^(r x)` when
`r` is a characteristic root), a combination of `cos` and `sin`, and a polynomial of no larger
degree reproduce the forcing terms `k e^(r x)`, `k cos ω x + l sin ω x`, and a polynomial. -/
@[kb "openstaxcalculus2016" "3:Table 7.2, p. 767"]
theorem undetermined_coefficients_guesses (a b c : ℝ) :
    (∀ k r : ℝ, a * r ^ 2 + b * r + c ≠ 0 → ∀ (y : ℝ → ℝ),
      y = (fun x => k / (a * r ^ 2 + b * r + c) * Real.exp (r * x)) →
      ∀ x, a * deriv (deriv y) x + b * deriv y x + c * y x = k * Real.exp (r * x)) ∧
    (∀ k r : ℝ, a * r ^ 2 + b * r + c = 0 → 2 * a * r + b ≠ 0 → ∀ (y : ℝ → ℝ),
      y = (fun x => k / (2 * a * r + b) * (x * Real.exp (r * x))) →
      ∀ x, a * deriv (deriv y) x + b * deriv y x + c * y x = k * Real.exp (r * x)) ∧
    (∀ k l ω : ℝ, (c - a * ω ^ 2) ^ 2 + (b * ω) ^ 2 ≠ 0 → ∀ (y : ℝ → ℝ),
      y = (fun x =>
        ((c - a * ω ^ 2) * k - b * ω * l) / ((c - a * ω ^ 2) ^ 2 + (b * ω) ^ 2) * Real.cos (ω * x)
        + ((c - a * ω ^ 2) * l + b * ω * k) / ((c - a * ω ^ 2) ^ 2 + (b * ω) ^ 2) *
          Real.sin (ω * x)) →
      ∀ x, a * deriv (deriv y) x + b * deriv y x + c * y x = k * Real.cos (ω * x) + l * Real.sin (ω * x)) ∧
    (c ≠ 0 → ∀ p : Polynomial ℝ, ∃ q : Polynomial ℝ, q.natDegree ≤ p.natDegree ∧
      ∀ x : ℝ, a * deriv (deriv (fun x : ℝ => q.eval x)) x + b * deriv (fun x : ℝ => q.eval x) x
        + c * q.eval x = p.eval x) :=
  ⟨fun k r hP y hy x => by
      subst hy
      exact UndergradKB.Calculus.ODEExtras.undetermined_exp a b c k r hP x,
    fun k r hP hP' y hy x => by
      subst hy
      exact UndergradKB.Calculus.ODEExtras.undetermined_exp_resonant a b c k r hP hP' x,
    fun k l ω hΔ y hy x => by
      subst hy
      exact UndergradKB.Calculus.ODEExtras.undetermined_trig a b c k l ω hΔ x,
    fun hc p => UndergradKB.Calculus.ODEExtras.undetermined_polynomial a b c hc p⟩

/-- OpenStax Calculus 3:§7.2 Strategy: Variation of Parameters (CA-681).
If `u₁' y₁ + u₂' y₂ = 0` and `u₁' y₁' + u₂' y₂' = f`, then `u₁ y₁ + u₂ y₂` is a particular
solution; the derivatives `u₁', u₂'` are given by Cramer's rule. -/
@[kb "openstaxcalculus2016" "3:§7.2 Strategy: Variation of Parameters, p. 772"]
theorem variation_of_parameters_method :
    (∀ {p q f y1 y2 u1 u2 : ℝ → ℝ}, LinSol p q (fun _ => 0) y1 → LinSol p q (fun _ => 0) y2 →
      Differentiable ℝ u1 → Differentiable ℝ u2 →
      (∀ x, deriv u1 x * y1 x + deriv u2 x * y2 x = 0) →
      (∀ x, deriv u1 x * deriv y1 x + deriv u2 x * deriv y2 x = f x) →
      LinSol p q f (fun x => u1 x * y1 x + u2 x * y2 x)) ∧
    (∀ {y1 y2 y1' y2' u1' u2' f : ℝ}, y1 * y2' - y1' * y2 ≠ 0 →
      u1' * y1 + u2' * y2 = 0 → u1' * y1' + u2' * y2' = f →
      u1' = -y2 * f / (y1 * y2' - y1' * y2) ∧ u2' = y1 * f / (y1 * y2' - y1' * y2)) :=
  ⟨fun {_ _ _ _ _ _ _} h1 h2 hu1 hu2 c1 c2 =>
      UndergradKB.Calculus.variation_of_parameters h1 h2 hu1 hu2 c1 c2,
    fun {_ _ _ _ _ _ _} hW c1 c2 => UndergradKB.Calculus.variation_of_parameters_cramer hW c1 c2⟩

/-- OpenStax Calculus 3:§7.3 Equations 7.5-7.6 (simple harmonic motion) (CA-682).
The undamped spring `m x'' + k x = 0` has exactly the solutions
`c₁ cos(ω t) + c₂ sin(ω t)` with `ω = √(k / m)`. -/
@[kb "openstaxcalculus2016" "3:§7.3 Equations 7.5-7.6 (simple harmonic motion), p. 776"]
theorem simple_harmonic_motion_solutions {m k : ℝ} (hm : 0 < m) (hk : 0 < k) (x : ℝ → ℝ) :
    ConstSol m 0 k (fun _ => 0) x ↔
      ∃ c1 c2 : ℝ, ∀ t, x t = c1 * Real.cos (√(k / m) * t) + c2 * Real.sin (√(k / m) * t) :=
  UndergradKB.Calculus.simple_harmonic_motion hm hk x

/-- OpenStax Calculus 3:Theorem 7.5 (CA-683).
`c₁ cos ω t + c₂ sin ω t = A sin(ω t + φ)` with amplitude `A = √(c₁² + c₂²)` and phase `φ`
satisfying `tan φ = c₁ / c₂` (when `c₂ ≠ 0`). -/
@[kb "openstaxcalculus2016" "3:Theorem 7.5, p. 778"]
theorem amplitude_phase_form (c1 c2 ω : ℝ) (h : c1 ≠ 0 ∨ c2 ≠ 0) :
    ∃ A φ : ℝ, 0 < A ∧ A = √(c1 ^ 2 + c2 ^ 2) ∧ A * Real.sin φ = c1 ∧ A * Real.cos φ = c2 ∧
      (c2 ≠ 0 → Real.tan φ = c1 / c2) ∧
      ∀ t, c1 * Real.cos (ω * t) + c2 * Real.sin (ω * t) = A * Real.sin (ω * t + φ) :=
  UndergradKB.Calculus.amplitude_phase c1 c2 ω h

/-- OpenStax Calculus 3:§7.3 Case 1 overdamped (CA-684).
For `b² > 4mk` the solutions are combinations of two distinct decaying exponentials. -/
@[kb "openstaxcalculus2016" "3:§7.3 Case 1 overdamped, p. 780"]
theorem overdamped_spring {m b k : ℝ} (hm : 0 < m) (hb : 0 < b) (hk : 0 < k)
    (hd : 4 * m * k < b ^ 2) :
    ∃ r1 r2 : ℝ, r1 < 0 ∧ r2 < 0 ∧ r1 ≠ r2 ∧ ∀ x : ℝ → ℝ,
      ConstSol m b k (fun _ => 0) x ↔
        ∃ c1 c2 : ℝ, ∀ t, x t = c1 * Real.exp (r1 * t) + c2 * Real.exp (r2 * t) :=
  UndergradKB.Calculus.overdamped hm hb hk hd

/-- OpenStax Calculus 3:§7.3 Case 2 critically damped (CA-685).
For `b² = 4mk` the solutions are `e^(r t)(c₁ + c₂ t)` with `r < 0`. -/
@[kb "openstaxcalculus2016" "3:§7.3 Case 2 critically damped, p. 782"]
theorem critically_damped_spring {m b k : ℝ} (hm : 0 < m) (hb : 0 < b) (hd : b ^ 2 = 4 * m * k) :
    ∃ r : ℝ, r < 0 ∧ ∀ x : ℝ → ℝ,
      ConstSol m b k (fun _ => 0) x ↔
        ∃ c1 c2 : ℝ, ∀ t, x t = Real.exp (r * t) * (c1 + c2 * t) :=
  UndergradKB.Calculus.critically_damped hm hb hd

/-- OpenStax Calculus 3:§7.3 Case 3 underdamped (CA-686).
For `b² < 4mk` the solutions are `e^(α t)(c₁ cos β t + c₂ sin β t)` with `α < 0 < β`, and every
solution tends to `0`. -/
@[kb "openstaxcalculus2016" "3:§7.3 Case 3 underdamped, p. 782"]
theorem underdamped_spring {m b k : ℝ} (hm : 0 < m) (hb : 0 < b) (hk : 0 < k)
    (hd : b ^ 2 < 4 * m * k) :
    (∃ α β : ℝ, α < 0 ∧ 0 < β ∧ ∀ x : ℝ → ℝ,
      ConstSol m b k (fun _ => 0) x ↔
        ∃ c1 c2 : ℝ, ∀ t, x t = Real.exp (α * t) * (c1 * Real.cos (β * t) + c2 * Real.sin (β * t))) ∧
    (∀ {x : ℝ → ℝ}, ConstSol m b k (fun _ => 0) x → Tendsto x atTop (𝓝 0)) :=
  ⟨UndergradKB.Calculus.underdamped hm hb hd,
    fun {_} h => UndergradKB.Calculus.spring_solution_tendsto_zero hm hb hk h⟩

/-- OpenStax Calculus 3:§7.3 Equation 7.9 (RLC series circuit) (CA-688).
The charge in a series RLC circuit satisfies `L q'' + R q' + q / C = E(t)`, which is the forced
spring equation with spring constant `1 / C`; any two solutions differ by a transient tending
to `0`. -/
@[kb "openstaxcalculus2016" "3:§7.3 Equation 7.9 (RLC series circuit), p. 789"]
theorem rlc_series_circuit (L R C : ℝ) (E q : ℝ → ℝ) :
    (∀ t, L * deriv (deriv q) t + R * deriv q t + q t / C = E t) ↔ ForcedSpring L R (1 / C) E q :=
  UndergradKB.Calculus.ODEExtras.rlc_iff_forcedSpring L R C E q

/-- OpenStax Calculus 3:§7.4 Strategy: Finding Power Series Solutions (CA-689).
If the coefficients of an everywhere convergent series satisfy the recursion obtained by
substituting `y = ∑ cₙ xⁿ` into `y'' + β y' + γ y = 0`, the series is a solution. -/
@[kb "openstaxcalculus2016" "3:§7.4 Strategy: Finding Power Series Solutions, p. 793"]
theorem power_series_solution_method {c : ℕ → ℝ} (hc : EntireCoeff c) (β γ : ℝ)
    (hrec : ∀ n : ℕ, ((n : ℝ) + 2) * ((n : ℝ) + 1) * c (n + 2) + β * (((n : ℝ) + 1) * c (n + 1))
      + γ * c n = 0) (x : ℝ) :
    deriv (deriv (psum c)) x + β * deriv (psum c) x + γ * psum c x = 0 :=
  UndergradKB.Calculus.ODEExtras.power_series_method hc β γ hrec x

end ProvedInKB

/-! ## Wave 3: further results -/

/-- OpenStax Calculus 3:§7.1 Definition (linear, homogeneous, nonhomogeneous second-order equation) (CA-666).
A solution of `y'' + p(x) y' + q(x) y = f(x)` is a twice differentiable function satisfying it for all `x`;
the equation is homogeneous when `f = 0`. The constant coefficient case `a y'' + b y' + c y = f` is the same
with `p`, `q` constant. -/
@[kb "openstaxcalculus2016" "3:§7.1 Definition (linear, homogeneous, nonhomogeneous second-order equation), p. 752"]
theorem linear_second_order_equation_definition :
    (∀ (p q f y : ℝ → ℝ), LinSol p q f y ↔ Differentiable ℝ y ∧ Differentiable ℝ (deriv y) ∧
      ∀ x, deriv (deriv y) x + p x * deriv y x + q x * y x = f x) ∧
    (∀ (a b c : ℝ) (f y : ℝ → ℝ), ConstSol a b c f y ↔ Differentiable ℝ y ∧
      Differentiable ℝ (deriv y) ∧ ∀ x, a * deriv (deriv y) x + b * deriv y x + c * y x = f x) :=
  ⟨fun _ _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl⟩

/-- OpenStax Calculus 3:§7.1 Definition (linear dependence of functions) (CA-668).
Two functions are linearly dependent on a set `s` when a combination with coefficients not both zero vanishes
on all of `s`; otherwise they are linearly independent on `s`. -/
@[kb "openstaxcalculus2016" "3:§7.1 Definition (linear dependence of functions), p. 755"]
theorem linear_dependence_of_functions (s : Set ℝ) (f g : ℝ → ℝ) :
    LinDepOn s f g ↔ ∃ c1 c2 : ℝ, (c1 ≠ 0 ∨ c2 ≠ 0) ∧ ∀ x ∈ s, c1 * f x + c2 * g x = 0 :=
  Iff.rfl

/-- OpenStax Calculus 3:§7.1 Definition (characteristic equation) (CA-671).
Trying `y = e^(r x)` in `a y'' + b y' + c y = 0` gives a solution exactly when `a r² + b r + c = 0`. -/
@[kb "openstaxcalculus2016" "3:§7.1 Definition (characteristic equation), p. 757"]
theorem characteristic_equation (a b c r : ℝ) :
    ConstSol a b c (fun _ => 0) (fun x => Real.exp (r * x)) ↔ a * r ^ 2 + b * r + c = 0 :=
  UndergradKB.Calculus.exp_solves_iff_characteristic a b c r

/-- OpenStax Calculus 3:§7.1 boundary conditions / boundary-value problem (unnumbered) (CA-675).
A boundary-value problem prescribes values of the solution at two different points. For `y'' = -y` with
`y(0) = 0 = y(π)` there are infinitely many solutions, while with `y(0) = 0`, `y(π/2) = 1` the only solution is
`sin`. -/
@[kb "openstaxcalculus2016" "3:§7.1 boundary conditions / boundary-value problem (unnumbered), p. 760"]
theorem boundary_value_problem_examples :
    (∀ (F : ℝ → ℝ → ℝ → ℝ) (x₀ x₁ α β : ℝ) (y : ℝ → ℝ),
      UndergradKB.Calculus.ODEExtras.IsBVPSolution F x₀ x₁ α β y ↔
        Differentiable ℝ y ∧ Differentiable ℝ (deriv y) ∧
          (∀ x, deriv (deriv y) x = F x (y x) (deriv y x)) ∧ y x₀ = α ∧ y x₁ = β) ∧
    {y : ℝ → ℝ | UndergradKB.Calculus.ODEExtras.IsBVPSolution (fun _ y _ => -y) 0 Real.pi 0 0 y}.Infinite ∧
    {y : ℝ → ℝ | UndergradKB.Calculus.ODEExtras.IsBVPSolution (fun _ y _ => -y) 0 (Real.pi / 2) 0 1 y} =
      {Real.sin} :=
  ⟨fun _ _ _ _ _ _ => Iff.rfl, UndergradKB.Calculus.ODEExtras.bvp_sin_infinitely_many,
    UndergradKB.Calculus.ODEExtras.bvp_sin_unique⟩

/-- OpenStax Calculus 3:§7.3 Forced vibrations (Eq. 7.8, transient and steady-state solutions) (CA-687).
For a damped spring with `m, b, k > 0` and forcing `f`, any solution differs from a steady-state (particular)
solution by a transient term that tends to `0` as `t → ∞`. -/
@[kb "openstaxcalculus2016" "3:§7.3 Forced vibrations (Eq. 7.8, transient and steady-state solutions), p. 787"]
theorem forced_vibration_transient_steady_state {m b k : ℝ} (hm : 0 < m) (hb : 0 < b) (hk : 0 < k)
    {f x xp : ℝ → ℝ} (hx : ConstSol m b k f x) (hxp : ConstSol m b k f xp) :
    Tendsto (fun t => x t - xp t) atTop (𝓝 0) :=
  UndergradKB.Calculus.forced_vibration_transient hm hb hk hx hxp

/-- OpenStax Calculus 3:Example 7.26 (CA-690).
The power series `J0(x) = ∑ (-1)^n x^(2n) / (4^n (n!)²)` is twice differentiable on all of `ℝ` and solves the
Bessel equation of order 0, `x² y'' + x y' + x² y = 0`. -/
@[kb "openstaxcalculus2016" "3:Example 7.26, p. 797"]
theorem bessel_equation_order_zero_series_solution :
    Differentiable ℝ UndergradKB.Calculus.J0 ∧ Differentiable ℝ (deriv UndergradKB.Calculus.J0) ∧
      ∀ x, x ^ 2 * deriv (deriv UndergradKB.Calculus.J0) x + x * deriv UndergradKB.Calculus.J0 x +
        x ^ 2 * UndergradKB.Calculus.J0 x = 0 :=
  UndergradKB.Calculus.J0_bessel_equation

end UndergradKB.Calculus.Course.V3C7
