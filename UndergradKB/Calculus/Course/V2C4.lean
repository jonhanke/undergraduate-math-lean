import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import UndergradKB.Common.Attr
import UndergradKB.Calculus.FirstOrderODE

/-! Course layer, OpenStax Calculus Volume 2, Chapter 4 (differential equations: Euler's method,
separable equations, exponential and cooling models, the logistic equation, first-order linear
equations). -/

namespace UndergradKB.Calculus.Course.V2C4

open Set Filter Topology

/-! ## Results proved in undergrad-kb -/

/-- OpenStax Calculus 2:Theorem 4.1 (CA-315). Error bound for Euler's method (iterates
`UndergradKB.Calculus.eulerIter`): for step `h > 0`, the error after `n` steps is at most
`(M h / (2 L)) (e^(L n h) - 1)`, so it is first order in `h`. -/
@[kb "openstaxcalculus2016" "2:Theorem 4.1, p. 333"]
theorem euler_method_error_bound {f : ℝ → ℝ → ℝ} {y w : ℝ → ℝ} {L M x0 y0 h : ℝ}
    (hL : 0 < L) (hh : 0 < h)
    (hlip : ∀ x u v, |f x u - f x v| ≤ L * |u - v|)
    (hy : ∀ x, HasDerivAt y (f x (y x)) x)
    (hz : ∀ x, HasDerivAt (fun x => f x (y x)) (w x) x) (hw : ∀ x, |w x| ≤ M)
    (hy0 : y x0 = y0) (n : ℕ) :
    |y (x0 + n * h) - UndergradKB.Calculus.eulerIter f x0 y0 h n| ≤
      M * h / (2 * L) * (Real.exp (L * (n * h)) - 1) :=
  UndergradKB.Calculus.euler_error_bound hL hh hlip hy hz hw hy0 n

/-- OpenStax Calculus 2:§4.3 Problem-Solving Strategy, separation of variables (CA-317). For
`y' = g(x) h(y)`: a constant `c` with `h c = 0` is a solution, and otherwise (with `h (y x) ≠ 0`,
`H' = 1/h`, `G' = g`) the equation holds exactly when `H(y) = G(x) + C`. -/
@[kb "openstaxcalculus2016" "2:§4.3 Problem-Solving Strategy (separation of variables), p. 342"]
theorem separation_of_variables :
    (∀ {g h : ℝ → ℝ} {c : ℝ}, h c = 0 → ∀ x, HasDerivAt (fun _ : ℝ => c) (g x * h c) x) ∧
    (∀ {a b : ℝ} {g h G H y : ℝ → ℝ},
      (∀ x ∈ Ioo a b, DifferentiableAt ℝ y x) → (∀ x ∈ Ioo a b, h (y x) ≠ 0) →
      (∀ x ∈ Ioo a b, HasDerivAt H (1 / h (y x)) (y x)) →
      (∀ x ∈ Ioo a b, HasDerivAt G (g x) x) →
      ((∀ x ∈ Ioo a b, HasDerivAt y (g x * h (y x)) x) ↔
        ∃ C : ℝ, ∀ x ∈ Ioo a b, H (y x) = G x + C)) :=
  ⟨fun hc => UndergradKB.Calculus.separable_const_solution hc,
    fun hy hh hH hG => UndergradKB.Calculus.separable_iff hy hh hH hG⟩

/-- OpenStax Calculus 2:§4.3 Equation, exponential growth and decay (CA-318). `y' = k y` with
`y 0 = y0` holds exactly when `y t = y0 e^(k t)` (growth for `k > 0`, decay for `k < 0`). -/
@[kb "openstaxcalculus2016" "2:§4.3 Equation (exponential growth/decay), p. 352"]
theorem exponential_growth_decay_equation {y : ℝ → ℝ} {k y0 : ℝ} (h0 : y 0 = y0) :
    (∀ t, HasDerivAt y (k * y t) t) ↔ ∀ t, y t = y0 * Real.exp (k * t) :=
  UndergradKB.Calculus.exp_model_ivp h0

/-- OpenStax Calculus 2:§4.3 Key Equation, Newton's law of cooling (CA-319). `T' = k (T - Ta)`
holds exactly when `T t = Ta + (T 0 - Ta) e^(k t)`. -/
@[kb "openstaxcalculus2016" "2:§4.3 Key Equation (Newton's law of cooling), p. 377"]
theorem newtons_law_of_cooling {T : ℝ → ℝ} {k Ta : ℝ} :
    (∀ t, HasDerivAt T (k * (T t - Ta)) t) ↔
      ∀ t, T t = Ta + (T 0 - Ta) * Real.exp (k * t) :=
  UndergradKB.Calculus.newton_cooling_pos_iff

/-- OpenStax Calculus 2:Theorem 4.2 (CA-322). The logistic initial-value problem
`P' = r P (1 - P/K)`, `P 0 = P0`: the formula `P0 K e^(r t) / (K + P0 (e^(r t) - 1))` solves it
wherever the denominator is nonzero, and every positive solution on `ℝ` equals it. -/
@[kb "openstaxcalculus2016" "2:Theorem 4.2, p. 359"]
theorem logistic_initial_value_problem {K r P0 : ℝ} (hK : K ≠ 0) :
    (∀ t : ℝ, K + P0 * (Real.exp (r * t) - 1) ≠ 0 →
      HasDerivAt (fun t => P0 * K * Real.exp (r * t) / (K + P0 * (Real.exp (r * t) - 1)))
        (r * (P0 * K * Real.exp (r * t) / (K + P0 * (Real.exp (r * t) - 1))) *
          (1 - (P0 * K * Real.exp (r * t) / (K + P0 * (Real.exp (r * t) - 1))) / K)) t) ∧
    (0 < P0 → ∀ {Q : ℝ → ℝ}, (∀ t, HasDerivAt Q (r * Q t * (1 - Q t / K)) t) → Q 0 = P0 →
      (∀ t, 0 < Q t) →
      ∀ t, Q t = P0 * K * Real.exp (r * t) / (K + P0 * (Real.exp (r * t) - 1))) :=
  ⟨fun t hD => UndergradKB.Calculus.logisticSol_hasDerivAt hK t hD,
    fun hP0 _ hQ hQ0 hpos => UndergradKB.Calculus.logistic_unique hK hP0 hQ hQ0 hpos⟩

/-- OpenStax Calculus 2:§4.5 Integrating factor and Problem-Solving Strategy (CA-326). For
`y' + p y = q` with `P' = p`, `q` continuous and integrating factor `μ = e^P`, the solutions are
exactly `y x = (1/μ x) (∫ μ q + C)`. -/
@[kb "openstaxcalculus2016" "2:§4.5 Integrating factor, p. 367"]
theorem linear_first_order_integrating_factor {p q P y : ℝ → ℝ} (hq : Continuous q)
    (hP : ∀ x, HasDerivAt P (p x) x) (x0 : ℝ) :
    (∀ x, HasDerivAt y (q x - p x * y x) x) ↔
      ∃ C : ℝ, ∀ x, y x = Real.exp (-P x) * ((∫ t in x0..x, Real.exp (P t) * q t) + C) :=
  UndergradKB.Calculus.linear_first_order_iff hq hP x0

/-! ## Wave 3: further results -/

/-- OpenStax Calculus 2:§4.2 Definition (equilibrium solution) (CA-313). For the autonomous
equation `y' = f(y)`, the constant function `y = c` is a solution exactly when `f c = 0`. -/
@[kb "openstaxcalculus2016" "2:§4.2 Definition (equilibrium solution), p. 329"]
theorem equilibrium_solution_iff {f : ℝ → ℝ} (c : ℝ) :
    (∀ x, HasDerivAt (fun _ : ℝ => c) (f c) x) ↔ f c = 0 :=
  UndergradKB.Calculus.equilibrium_iff c

/-- OpenStax Calculus 2:§4.2 Definition (asymptotically stable / unstable / semi-stable solution)
(CA-314). If `f c = 0` and `f'(c) < 0`, then the equilibrium `c` of `y' = f(y)` is
asymptotically stable. -/
@[kb "openstaxcalculus2016" "2:§4.2 Definition (asymptotically stable / unstable / semi-stable solution), p. 329"]
theorem equilibrium_asymptotically_stable {f : ℝ → ℝ} {c d : ℝ} (hfc : f c = 0)
    (hd : HasDerivAt f d c) (hneg : d < 0) : UndergradKB.Calculus.AsympStable f c :=
  UndergradKB.Calculus.asympStable_of_deriv_neg hfc hd hneg

/-- OpenStax Calculus 2:§4.4 text on point of inflection (CA-323). For the logistic solution `P`
with `r > 0` and `0 < P0 < K`, the second derivative is `r² P (1 - P/K)(1 - 2P/K)`; it vanishes
exactly where `P = K/2`, which happens only at `t = ln((K-P0)/P0) / r`, and it is positive before
and negative after that time. -/
@[kb "openstaxcalculus2016" "2:§4.4 text on point of inflection, p. 359"]
theorem logistic_point_of_inflection {K r P0 : ℝ} (hr : 0 < r) (hP0 : 0 < P0) (hPK : P0 < K) :
    let P := UndergradKB.Calculus.logisticSol K r P0
    let ts := Real.log ((K - P0) / P0) / r
    (∀ t, deriv (deriv P) t = r ^ 2 * P t * (1 - P t / K) * (1 - 2 * P t / K)) ∧
    (∀ t, deriv (deriv P) t = 0 ↔ P t = K / 2) ∧
    (∀ t, P t = K / 2 ↔ t = ts) ∧
    (∀ t, t < ts → 0 < deriv (deriv P) t) ∧
    (∀ t, ts < t → deriv (deriv P) t < 0) ∧
    (0 < ts ↔ P0 < K / 2) :=
  UndergradKB.Calculus.logistic_inflection hr hP0 hPK

end UndergradKB.Calculus.Course.V2C4
