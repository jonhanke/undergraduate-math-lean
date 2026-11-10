import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.FieldTheory.RatFunc.Basic
import UndergradKB.Common.Attr
import UndergradKB.Calculus.Defs
import UndergradKB.Calculus.IntegralsFTC
import UndergradKB.Calculus.TrigIntegrals
import UndergradKB.Calculus.PolynomialDivision
import UndergradKB.Calculus.RiemannSums
import UndergradKB.Calculus.Simpson
import UndergradKB.Calculus.ImproperIntegrals
import UndergradKB.Calculus.Laplace

/-! Course layer, OpenStax Calculus Volume 2, Chapter 3 (techniques of integration). -/

namespace UndergradKB.Calculus.Course.V2C3

open Set Filter Topology MeasureTheory Polynomial
open scoped Interval

/-- OpenStax Calculus 2:Theorem 3.2 (CA-214). Integration by parts on `[a,b]`:
`∫ u v' = u(b) v(b) - u(a) v(a) - ∫ u' v` for continuously differentiable `u, v`. -/
@[kb "openstaxcalculus2016" "2:Theorem 3.2, p. 245"]
theorem integration_by_parts_definite {u v u' v' : ℝ → ℝ} {a b : ℝ}
    (hu : ∀ x ∈ [[a, b]], HasDerivAt u (u' x) x) (hv : ∀ x ∈ [[a, b]], HasDerivAt v (v' x) x)
    (hu' : ContinuousOn u' [[a, b]]) (hv' : ContinuousOn v' [[a, b]]) :
    ∫ x in a..b, u x * v' x = u b * v b - u a * v a - ∫ x in a..b, u' x * v x :=
  intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu'.intervalIntegrable
    hv'.intervalIntegrable

/-- OpenStax Calculus 2:§3.2 Identities (power-reducing) (CA-215). `sin² x = (1 - cos 2x)/2`. -/
@[kb "openstaxcalculus2016" "2:§3.2 Identities (power-reducing), p. 250"]
theorem sin_sq_power_reducing (x : ℝ) : Real.sin x ^ 2 = (1 - Real.cos (2 * x)) / 2 := by
  rw [Real.sin_sq_eq_half_sub]
  ring

/-- OpenStax Calculus 2:§3.2 Identities (power-reducing) (CA-215). `cos² x = (1 + cos 2x)/2`. -/
@[kb "openstaxcalculus2016" "2:§3.2 Identities (power-reducing), p. 250"]
theorem cos_sq_power_reducing (x : ℝ) : Real.cos x ^ 2 = (1 + Real.cos (2 * x)) / 2 := by
  rw [Real.cos_sq x]
  ring

/-- OpenStax Calculus 2:Example 3.24 (CA-226). The antiderivative of `1/√(1+x²)` is
`ln (x + √(1+x²))` (that is, `arsinh x`). -/
@[kb "openstaxcalculus2016" "2:Example 3.24, p. 264"]
theorem hasDerivAt_log_x_add_sqrt (x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.log (t + √(1 + t ^ 2))) (1 / √(1 + x ^ 2)) x := by
  rw [one_div]
  exact Real.hasDerivAt_arsinh x

/-- A polynomial of degree below `1` is a constant (helper for the partial-fraction wrappers). -/
private theorem eq_C_of_degree_lt_one' {p : ℝ[X]} (h : p.degree < 1) : p = C (p.coeff 0) :=
  eq_C_of_degree_le_zero (Nat.WithBot.lt_one_iff_le_zero.mp h)

/-- A polynomial of degree below `2` is linear (helper for the partial-fraction wrappers). -/
private theorem eq_linear_of_degree_lt_two {p : ℝ[X]} (h : p.degree < 2) :
    p = C (p.coeff 1) * X + C (p.coeff 0) := by
  refine eq_X_add_C_of_degree_le_one ?_
  by_contra hc
  have h1 := Nat.WithBot.add_one_le_of_lt (not_le.mp hc)
  rw [one_add_one_eq_two] at h1
  exact absurd h (not_lt.2 h1)

/-- OpenStax Calculus 2:§3.4 Nonrepeated linear factors (CA-229). In the field of rational
functions, `P / ∏ (X - a_i)` (distinct `a_i`) equals a polynomial `q` plus a sum of constants
over the linear factors; `q = 0` when `deg P < deg Q` (not proved here). -/
@[kb "openstaxcalculus2016" "2:§3.4 Nonrepeated linear factors, p. 271"]
theorem partial_fractions_distinct_linear {ι : Type*} (P : ℝ[X]) (s : Finset ι) (a : ι → ℝ)
    (ha : Function.Injective a) :
    ∃ (q : ℝ[X]) (A : ι → ℝ),
      algebraMap ℝ[X] (RatFunc ℝ) P / ∏ i ∈ s, algebraMap ℝ[X] (RatFunc ℝ) (X - C (a i)) =
        algebraMap ℝ[X] (RatFunc ℝ) q +
          ∑ i ∈ s, algebraMap ℝ[X] (RatFunc ℝ) (C (A i)) /
            algebraMap ℝ[X] (RatFunc ℝ) (X - C (a i)) := by
  obtain ⟨q, r, hr, h⟩ := Polynomial.div_prod_eq_quo_add_sum_rem_div (RatFunc ℝ) P
    (g := fun i => X - C (a i)) (s := s) (fun i _ => monic_X_sub_C _)
    (fun i _ j _ hij => pairwise_coprime_X_sub_C ha hij)
  refine ⟨q, fun i => (r i).coeff 0, ?_⟩
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hri : r i = C ((r i).coeff 0) := by
    refine eq_C_of_degree_lt_one' ?_
    simpa [degree_X_sub_C] using hr i hi
  rw [← hri]

/-- OpenStax Calculus 2:§3.4 Repeated linear factors (CA-230). A polynomial `P` can be written
as `q (X-a)^n + ∑_{i<n} A_i (X-a)^i`; dividing by `(X-a)^n` gives the terms
`A_i/(X-a)^(n-i)` of the book. -/
@[kb "openstaxcalculus2016" "2:§3.4 Repeated linear factors, p. 274"]
theorem partial_fractions_repeated_linear (P : ℝ[X]) (a : ℝ) (n : ℕ) :
    ∃ (q : ℝ[X]) (A : Fin n → ℝ),
      P = q * (X - C a) ^ n + ∑ i : Fin n, C (A i) * (X - C a) ^ i.1 := by
  obtain ⟨q, r, hr, h⟩ := Polynomial.eq_quo_mul_pow_add_sum_rem_mul_pow P
    (monic_X_sub_C a) n
  refine ⟨q, fun i => (r i).coeff 0, ?_⟩
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hri : r i = C ((r i).coeff 0) := by
    refine eq_C_of_degree_lt_one' ?_
    simpa [degree_X_sub_C] using hr i
  rw [← hri]

/-- OpenStax Calculus 2:§3.4 Strategy step 3c (CA-231). With pairwise coprime monic quadratic
factors `g_i`, `P / ∏ g_i` equals a polynomial `q` plus `(A_i X + B_i)/g_i`. Irreducibility is not
needed for the existence of the decomposition. -/
@[kb "openstaxcalculus2016" "2:§3.4 Strategy step 3c, p. 275"]
theorem partial_fractions_quadratic_factors {ι : Type*} (P : ℝ[X]) (s : Finset ι) (g : ι → ℝ[X])
    (hg : ∀ i ∈ s, (g i).Monic) (hdeg : ∀ i ∈ s, (g i).degree = 2)
    (hcop : Set.Pairwise (↑s : Set ι) fun i j => IsCoprime (g i) (g j)) :
    ∃ (q : ℝ[X]) (A B : ι → ℝ),
      algebraMap ℝ[X] (RatFunc ℝ) P / ∏ i ∈ s, algebraMap ℝ[X] (RatFunc ℝ) (g i) =
        algebraMap ℝ[X] (RatFunc ℝ) q +
          ∑ i ∈ s, algebraMap ℝ[X] (RatFunc ℝ) (C (A i) * X + C (B i)) /
            algebraMap ℝ[X] (RatFunc ℝ) (g i) := by
  obtain ⟨q, r, hr, h⟩ := Polynomial.div_prod_eq_quo_add_sum_rem_div (RatFunc ℝ) P hg hcop
  refine ⟨q, fun i => (r i).coeff 1, fun i => (r i).coeff 0, ?_⟩
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hri : r i = C ((r i).coeff 1) * X + C ((r i).coeff 0) := by
    refine eq_linear_of_degree_lt_two ?_
    simpa [hdeg i hi] using hr i hi
  rw [← hri]

/-- OpenStax Calculus 2:§3.4 Strategy step 3d (CA-232). For a monic quadratic `g` and `n ≥ 0`,
`P = q g^n + ∑_{i<n} (A_i X + B_i) g^i`; dividing by `g^n` gives the terms
`(A X + B)/g^k` of the book. -/
@[kb "openstaxcalculus2016" "2:§3.4 Strategy step 3d, p. 275"]
theorem partial_fractions_repeated_quadratic (P g : ℝ[X]) (hg : g.Monic) (hdeg : g.degree = 2)
    (n : ℕ) :
    ∃ (q : ℝ[X]) (A B : Fin n → ℝ),
      P = q * g ^ n + ∑ i : Fin n, (C (A i) * X + C (B i)) * g ^ i.1 := by
  obtain ⟨q, r, hr, h⟩ := Polynomial.eq_quo_mul_pow_add_sum_rem_mul_pow P hg n
  refine ⟨q, fun i => (r i).coeff 1, fun i => (r i).coeff 0, ?_⟩
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hri : r i = C ((r i).coeff 1) * X + C ((r i).coeff 0) := by
    refine eq_linear_of_degree_lt_two ?_
    simpa [hdeg] using hr i
  rw [← hri]

/-- OpenStax Calculus 2:§3.4 Rule (Method of Equating Coefficients) (CA-233). Two real polynomials
are equal iff all their coefficients agree. -/
@[kb "openstaxcalculus2016" "2:§3.4 Rule (Method of Equating Coefficients), p. 272"]
theorem equating_coefficients {p q : ℝ[X]} : p = q ↔ ∀ n, p.coeff n = q.coeff n :=
  Polynomial.ext_iff

/-- OpenStax Calculus 2:§3.4 Rule (Method of Strategic Substitution) (CA-233). Two real polynomials
that agree at every real number are equal, so substituting chosen values is legitimate. -/
@[kb "openstaxcalculus2016" "2:§3.4 Rule (Method of Strategic Substitution), p. 272"]
theorem strategic_substitution {p q : ℝ[X]} (h : ∀ x : ℝ, p.eval x = q.eval x) : p = q :=
  Polynomial.funext h

/-- OpenStax Calculus 2:Example 3.47 (CA-243). For `p ≤ 1`, `x^(-p)` is not integrable on
`[1, ∞)`: the improper integral diverges. -/
@[kb "openstaxcalculus2016" "2:Example 3.47, p. 297"]
theorem not_integrable_rpow_neg_of_le_one {p : ℝ} (hp : p ≤ 1) :
    ¬ IntegrableOn (fun x : ℝ => x ^ (-p)) (Ioi 1) :=
  not_integrableOn_Ioi_rpow_of_neg_one_le (by linarith)

/-- OpenStax Calculus 2:Example 3.47 (CA-243), case `p = 1`. The area under `1/x` over `[1, N]`
tends to infinity as `N → ∞`. -/
@[kb "openstaxcalculus2016" "2:Example 3.47, p. 297"]
theorem integral_inv_tendsto_atTop :
    Tendsto (fun N : ℝ => ∫ x in (1 : ℝ)..N, x⁻¹) atTop atTop := by
  have h : (fun N : ℝ => ∫ x in (1 : ℝ)..N, x⁻¹) =ᶠ[atTop] Real.log := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
    rw [integral_inv_of_pos one_pos hN, div_one]
  exact Real.tendsto_log_atTop.congr' h.symm

/-- OpenStax Calculus 2:Theorem 3.7 (CA-245). Comparison test: if `0 ≤ f ≤ g` on `[a, ∞)`, both
continuous, and `∫_a^∞ g` converges, then `∫_a^∞ f` converges. -/
@[kb "openstaxcalculus2016" "2:Theorem 3.7, p. 305"]
theorem improper_comparison_converges {f g : ℝ → ℝ} {a : ℝ} (hf : ContinuousOn f (Ici a))
    (h0 : ∀ x ∈ Ici a, 0 ≤ f x) (hfg : ∀ x ∈ Ici a, f x ≤ g x)
    (hg : IntegrableOn g (Ici a)) : IntegrableOn f (Ici a) := by
  refine Integrable.mono' hg (hf.aestronglyMeasurable measurableSet_Ici) ?_
  refine (ae_restrict_iff' measurableSet_Ici).2 (Eventually.of_forall fun x hx => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (h0 x hx)]
  exact hfg x hx

/-- OpenStax Calculus 2:Theorem 3.7 (CA-245). Contrapositive: if `∫_a^∞ f` diverges (is not
integrable) then so does `∫_a^∞ g`. -/
@[kb "openstaxcalculus2016" "2:Theorem 3.7, p. 305"]
theorem improper_comparison_diverges {f g : ℝ → ℝ} {a : ℝ} (hf : ContinuousOn f (Ici a))
    (h0 : ∀ x ∈ Ici a, 0 ≤ f x) (hfg : ∀ x ∈ Ici a, f x ≤ g x)
    (hdiv : ¬ IntegrableOn f (Ici a)) : ¬ IntegrableOn g (Ici a) :=
  fun hg => hdiv (improper_comparison_converges hf h0 hfg hg)

/-! ## Results proved in undergrad-kb -/

/-- OpenStax Calculus 2:Theorem 3.1 (CA-213). Integration by parts: if `H' = v u'` then
`u v - H` is an antiderivative of `u v'` (that is, `∫ u dv = u v - ∫ v du`), and the definite
form for continuously differentiable `u`, `v`. -/
@[kb "openstaxcalculus2016" "2:Theorem 3.1, p. 240"]
theorem integration_by_parts_formula :
    (∀ {u v u' v' H : ℝ → ℝ}, (∀ x, HasDerivAt u (u' x) x) → (∀ x, HasDerivAt v (v' x) x) →
      (∀ x, HasDerivAt H (v x * u' x) x) →
      ∀ x, HasDerivAt (fun x => u x * v x - H x) (u x * v' x) x) ∧
    (∀ {u v u' v' : ℝ → ℝ}, (∀ x, HasDerivAt u (u' x) x) → (∀ x, HasDerivAt v (v' x) x) →
      Continuous u' → Continuous v' → ∀ a b : ℝ,
      ∫ x in a..b, u x * v' x = u b * v b - u a * v a - ∫ x in a..b, u' x * v x) :=
  ⟨fun hu hv hH => UndergradKB.Calculus.hasDerivAt_parts_antiderivative hu hv hH,
    fun hu hv hu' hv' a b => UndergradKB.Calculus.integral_parts hu hv hu' hv' a b⟩

/-- OpenStax Calculus 2:§3.2 Strategy for powers of sine and cosine (CA-216). An odd power splits
off one factor and uses `sin² + cos² = 1`; even powers use the power-reducing identities; and
`sin x cos x = sin (2x) / 2`. -/
@[kb "openstaxcalculus2016" "2:§3.2 Strategy (powers of sin and cos), p. 251"]
theorem sine_cosine_powers_strategy :
    (∀ (m : ℕ) (x : ℝ), Real.sin x ^ (2 * m + 1) = (1 - Real.cos x ^ 2) ^ m * Real.sin x) ∧
    (∀ (m : ℕ) (x : ℝ), Real.cos x ^ (2 * m + 1) = (1 - Real.sin x ^ 2) ^ m * Real.cos x) ∧
    (∀ x : ℝ, Real.sin x ^ 2 = 1 / 2 - Real.cos (2 * x) / 2) ∧
    (∀ x : ℝ, Real.cos x ^ 2 = 1 / 2 + Real.cos (2 * x) / 2) ∧
    (∀ x : ℝ, Real.sin x * Real.cos x = Real.sin (2 * x) / 2) :=
  ⟨UndergradKB.Calculus.sin_pow_odd, UndergradKB.Calculus.cos_pow_odd,
    UndergradKB.Calculus.sin_sq_power_reduce, UndergradKB.Calculus.cos_sq_power_reduce,
    UndergradKB.Calculus.sin_mul_cos_double⟩

/-- OpenStax Calculus 2:§3.2 Rule, products of sines and cosines of different angles
(Eq. 3.3-3.5) (CA-217). The product-to-sum identities, and the resulting antiderivatives of
`sin(ax) sin(bx)`, `sin(ax) cos(bx)`, `cos(ax) cos(bx)` for `a ≠ ±b`. -/
@[kb "openstaxcalculus2016" "2:§3.2 Rule (products of sines and cosines of different angles, Eq. 3.3-3.5), p. 252"]
theorem product_to_sum_integrals :
    (∀ a b : ℝ, Real.sin a * Real.sin b = (Real.cos (a - b) - Real.cos (a + b)) / 2) ∧
    (∀ a b : ℝ, Real.sin a * Real.cos b = (Real.sin (a - b) + Real.sin (a + b)) / 2) ∧
    (∀ a b : ℝ, Real.cos a * Real.cos b = (Real.cos (a - b) + Real.cos (a + b)) / 2) ∧
    (∀ {a b : ℝ}, a - b ≠ 0 → a + b ≠ 0 → ∀ x : ℝ,
      HasDerivAt
        (fun x => (Real.sin ((a - b) * x) / (a - b) - Real.sin ((a + b) * x) / (a + b)) / 2)
        (Real.sin (a * x) * Real.sin (b * x)) x) ∧
    (∀ {a b : ℝ}, a - b ≠ 0 → a + b ≠ 0 → ∀ x : ℝ,
      HasDerivAt
        (fun x => -(Real.cos ((a - b) * x) / (a - b) + Real.cos ((a + b) * x) / (a + b)) / 2)
        (Real.sin (a * x) * Real.cos (b * x)) x) ∧
    (∀ {a b : ℝ}, a - b ≠ 0 → a + b ≠ 0 → ∀ x : ℝ,
      HasDerivAt
        (fun x => (Real.sin ((a - b) * x) / (a - b) + Real.sin ((a + b) * x) / (a + b)) / 2)
        (Real.cos (a * x) * Real.cos (b * x)) x) :=
  ⟨UndergradKB.Calculus.sin_mul_sin_eq, UndergradKB.Calculus.sin_mul_cos_eq,
    UndergradKB.Calculus.cos_mul_cos_eq,
    fun h1 h2 x => UndergradKB.Calculus.hasDerivAt_sin_mul_sin h1 h2 x,
    fun h1 h2 x => UndergradKB.Calculus.hasDerivAt_sin_mul_cos h1 h2 x,
    fun h1 h2 x => UndergradKB.Calculus.hasDerivAt_cos_mul_cos h1 h2 x⟩

/-- OpenStax Calculus 2:§3.2 Strategy for powers of tangent and secant (CA-219). With
`cos x ≠ 0`: an even power of `sec` is `(1 + tan²)^m sec²` (substitute `u = tan x`), and
`tan^(2m+1) sec^(k+1) = (sec² - 1)^m sec^k (sec tan)` (substitute `u = sec x`). -/
@[kb "openstaxcalculus2016" "2:§3.2 Strategy (powers of tan and sec), p. 253"]
theorem tangent_secant_powers_strategy :
    (∀ {x : ℝ} (m : ℕ), Real.cos x ≠ 0 →
      sec x ^ (2 * m + 2) = (1 + Real.tan x ^ 2) ^ m * sec x ^ 2) ∧
    (∀ {x : ℝ} (m k : ℕ), Real.cos x ≠ 0 →
      Real.tan x ^ (2 * m + 1) * sec x ^ (k + 1) =
        (sec x ^ 2 - 1) ^ m * sec x ^ k * (sec x * Real.tan x)) :=
  ⟨fun m h => UndergradKB.Calculus.sec_pow_even m h,
    fun m k h => UndergradKB.Calculus.tan_pow_odd_mul_sec_pow m k h⟩

/-- OpenStax Calculus 2:§3.2 Rule, reduction formula for `sec^n` (Eq. 3.6) (CA-221). The
derivative of `sec^m tan`, and `(m+1) ∫ sec^(m+2) = [sec^m tan] + m ∫ sec^m` (also solved for
`∫ sec^(m+2)`), where `cos ≠ 0` on the interval. -/
@[kb "openstaxcalculus2016" "2:§3.2 Rule (reduction formula for sec^n, Eq. 3.6), p. 256"]
theorem secant_power_reduction :
    (∀ (m : ℕ) {x : ℝ}, Real.cos x ≠ 0 →
      HasDerivAt (fun x => sec x ^ m * Real.tan x)
        ((m + 1) * sec x ^ (m + 2) - m * sec x ^ m) x) ∧
    (∀ (m : ℕ) {b c : ℝ}, (∀ x ∈ uIcc b c, Real.cos x ≠ 0) →
      ((m : ℝ) + 1) * ∫ x in b..c, sec x ^ (m + 2) =
        (sec c ^ m * Real.tan c - sec b ^ m * Real.tan b) + m * ∫ x in b..c, sec x ^ m) ∧
    (∀ (m : ℕ) {b c : ℝ}, (∀ x ∈ uIcc b c, Real.cos x ≠ 0) →
      ∫ x in b..c, sec x ^ (m + 2) =
        ((sec c ^ m * Real.tan c - sec b ^ m * Real.tan b) + m * ∫ x in b..c, sec x ^ m) /
          (m + 1)) :=
  ⟨fun m _ h => UndergradKB.Calculus.hasDerivAt_sec_pow_mul_tan m h,
    fun m _ _ hI => UndergradKB.Calculus.integral_sec_pow_reduction m hI,
    fun m _ _ hI => UndergradKB.Calculus.integral_sec_pow_reduction' m hI⟩

/-- OpenStax Calculus 2:§3.2 Rule, reduction formula for `tan^n` (Eq. 3.7) (CA-222). The
derivative of `tan^(m+1)`, and `∫ tan^(m+2) = [tan^(m+1)/(m+1)] - ∫ tan^m`, where `cos ≠ 0` on
the interval. -/
@[kb "openstaxcalculus2016" "2:§3.2 Rule (reduction formula for tan^n, Eq. 3.7), p. 256"]
theorem tangent_power_reduction :
    (∀ (m : ℕ) {x : ℝ}, Real.cos x ≠ 0 →
      HasDerivAt (fun x => Real.tan x ^ (m + 1))
        (((m : ℝ) + 1) * (Real.tan x ^ m + Real.tan x ^ (m + 2))) x) ∧
    (∀ (m : ℕ) {b c : ℝ}, (∀ x ∈ uIcc b c, Real.cos x ≠ 0) →
      ∫ x in b..c, Real.tan x ^ (m + 2) =
        (Real.tan c ^ (m + 1) / (m + 1) - Real.tan b ^ (m + 1) / (m + 1)) -
          ∫ x in b..c, Real.tan x ^ m) :=
  ⟨fun m _ h => UndergradKB.Calculus.hasDerivAt_tan_pow_succ m h,
    fun m _ _ hI => UndergradKB.Calculus.integral_tan_pow_reduction m hI⟩

/-- OpenStax Calculus 2:§3.3 Strategy for `√(a² - x²)` (CA-223). With `x = a sin θ`,
`θ ∈ [-π/2, π/2]`, the root becomes `a cos θ`, and `dx = a cos θ dθ`. -/
@[kb "openstaxcalculus2016" "2:§3.3 Strategy (sqrt(a^2 - x^2)), p. 260"]
theorem trig_substitution_sine :
    (∀ {a θ : ℝ}, 0 ≤ a → θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) →
      √(a ^ 2 - (a * Real.sin θ) ^ 2) = a * Real.cos θ) ∧
    (∀ a θ : ℝ, HasDerivAt (fun θ => a * Real.sin θ) (a * Real.cos θ) θ) :=
  ⟨fun ha hθ => UndergradKB.Calculus.sqrt_sq_sub_mul_sin ha hθ,
    UndergradKB.Calculus.hasDerivAt_mul_sin⟩

/-- OpenStax Calculus 2:§3.3 Strategy for `√(a² + x²)` (CA-224). With `x = a tan θ`,
`θ ∈ (-π/2, π/2)`, the root becomes `a sec θ`, and `dx = a sec² θ dθ`. -/
@[kb "openstaxcalculus2016" "2:§3.3 Strategy (sqrt(a^2 + x^2)), p. 263"]
theorem trig_substitution_tangent :
    (∀ {a θ : ℝ}, 0 ≤ a → θ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) →
      √(a ^ 2 + (a * Real.tan θ) ^ 2) = a * sec θ) ∧
    (∀ (a : ℝ) {θ : ℝ}, Real.cos θ ≠ 0 →
      HasDerivAt (fun θ => a * Real.tan θ) (a * sec θ ^ 2) θ) :=
  ⟨fun ha hθ => UndergradKB.Calculus.sqrt_sq_add_mul_tan ha hθ,
    fun a _ h => UndergradKB.Calculus.hasDerivAt_mul_tan a h⟩

/-- OpenStax Calculus 2:§3.3 Strategy for `√(x² - a²)` (CA-225). With `x = a sec θ` the root is
`a |tan θ|`: it equals `a tan θ` for `θ ∈ [0, π/2)` (`x ≥ a`) and `-a tan θ` for
`θ ∈ (π/2, π]` (`x ≤ -a`); and `dx = a sec θ tan θ dθ`. -/
@[kb "openstaxcalculus2016" "2:§3.3 Strategy (sqrt(x^2 - a^2)), p. 266"]
theorem trig_substitution_secant :
    (∀ {a θ : ℝ}, 0 ≤ a → Real.cos θ ≠ 0 → √((a * sec θ) ^ 2 - a ^ 2) = a * |Real.tan θ|) ∧
    (∀ {a θ : ℝ}, 0 ≤ a → 0 ≤ θ → θ < Real.pi / 2 →
      √((a * sec θ) ^ 2 - a ^ 2) = a * Real.tan θ) ∧
    (∀ {a θ : ℝ}, 0 ≤ a → Real.pi / 2 < θ → θ ≤ Real.pi →
      √((a * sec θ) ^ 2 - a ^ 2) = -(a * Real.tan θ)) ∧
    (∀ (a : ℝ) {θ : ℝ}, Real.cos θ ≠ 0 →
      HasDerivAt (fun θ => a * sec θ) (a * (sec θ * Real.tan θ)) θ) :=
  ⟨fun ha h => UndergradKB.Calculus.sqrt_sq_sub_mul_sec ha h,
    fun ha h0 h1 => UndergradKB.Calculus.sqrt_sq_sub_mul_sec_of_first ha h0 h1,
    fun ha h0 h1 => UndergradKB.Calculus.sqrt_sq_sub_mul_sec_of_second ha h0 h1,
    fun a _ h => UndergradKB.Calculus.hasDerivAt_mul_sec a h⟩

/-- OpenStax Calculus 2:§3.4 Problem-Solving Strategy, partial fraction decomposition, step 2
(CA-228). A nonzero real polynomial is its leading coefficient times a product of monic linear
factors `x - r` and monic irreducible quadratics `x² + b x + c` (with `b² - 4c < 0`). -/
@[kb "openstaxcalculus2016" "2:§3.4 Problem-Solving Strategy (Partial Fraction Decomposition), p. 275"]
theorem real_polynomial_linear_quadratic_factors (p : ℝ[X]) (hp : p ≠ 0) :
    ∃ l : Multiset ℝ[X],
      (∀ q ∈ l, (∃ r : ℝ, q = X - C r) ∨
        (∃ b c : ℝ, b ^ 2 - 4 * c < 0 ∧ q = X ^ 2 + C b * X + C c)) ∧
      p = C p.leadingCoeff * l.prod :=
  UndergradKB.Calculus.real_polynomial_factorization p hp

/-- OpenStax Calculus 2:Theorem 3.3 (CA-234). For `f` continuous on `[a, b]`, the midpoint
sums `M_n` (`UndergradKB.Calculus.midSum`) converge to the integral. -/
@[kb "openstaxcalculus2016" "2:Theorem 3.3, p. 285"]
theorem midpoint_sum_converges {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) :
    Tendsto (fun n => UndergradKB.Calculus.midSum f a b n) atTop (𝓝 (∫ x in a..b, f x)) :=
  UndergradKB.Calculus.tendsto_midSum hab hf

/-- OpenStax Calculus 2:Theorem 3.4 (CA-235). The trapezoidal sum `T_n` is the average of the
left and right endpoint sums, and for `f` continuous on `[a, b]` it converges to the integral. -/
@[kb "openstaxcalculus2016" "2:Theorem 3.4, p. 287"]
theorem trapezoidal_sum_converges :
    (∀ (f : ℝ → ℝ) (a b : ℝ) {n : ℕ}, 0 < n →
      trapezoidal_integral f n a b =
        (UndergradKB.Calculus.leftSum f a b n + UndergradKB.Calculus.rightSum f a b n) / 2) ∧
    (∀ {f : ℝ → ℝ} {a b : ℝ}, a ≤ b → ContinuousOn f (Icc a b) →
      Tendsto (fun n => trapezoidal_integral f n a b) atTop (𝓝 (∫ x in a..b, f x))) :=
  ⟨fun f a b _ hn => UndergradKB.Calculus.trapezoidal_integral_eq_avg f a b hn,
    fun hab hf => UndergradKB.Calculus.tendsto_trapezoid hab hf⟩

/-- OpenStax Calculus 2:Theorem 3.5 (CA-237). If `|f''| ≤ M` on `[a, b]`, the midpoint error is
at most `M (b-a)³ / (24 n²)` and the trapezoidal error is at most `M (b-a)³ / (12 n²)`. -/
@[kb "openstaxcalculus2016" "2:Theorem 3.5, p. 289"]
theorem midpoint_trapezoid_error_bounds {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {a b M : ℝ}
    (hab : a ≤ b) {n : ℕ} (hn : 0 < n) (hM : ∀ x ∈ Icc a b, |iteratedDeriv 2 f x| ≤ M) :
    |UndergradKB.Calculus.midSum f a b n - ∫ x in a..b, f x| ≤ M * (b - a) ^ 3 / (24 * n ^ 2) ∧
    |trapezoidal_integral f n a b - ∫ x in a..b, f x| ≤ M * (b - a) ^ 3 / (12 * n ^ 2) :=
  ⟨UndergradKB.Calculus.midpoint_error_le hf hab hn hM,
    UndergradKB.Calculus.trapezoid_error_le hf hab hn hM⟩

/-- OpenStax Calculus 2:Theorem 3.6 (CA-238). Simpson's rule `S_n` (`UndergradKB.Calculus.simpson`,
`n` even) has the weights `1, 4, 2, 4, ..., 4, 1` times `Δx/3`, and converges to the integral of
a continuous function (along `n = 2k`). -/
@[kb "openstaxcalculus2016" "2:Theorem 3.6, p. 291"]
theorem simpsons_rule :
    (∀ (f : ℝ → ℝ) (a b : ℝ) (k : ℕ),
      UndergradKB.Calculus.simpson f a b (2 * (k + 1)) =
        ((b - a) / (2 * (k + 1) : ℕ) / 3) *
          (f a + f b +
            4 * ∑ j ∈ Finset.range (k + 1), f (a + (2 * j + 1) * ((b - a) / (2 * (k + 1) : ℕ)))
            + 2 * ∑ j ∈ Finset.range k, f (a + (2 * j + 2) * ((b - a) / (2 * (k + 1) : ℕ))))) ∧
    (∀ {f : ℝ → ℝ} {a b : ℝ}, a ≤ b → ContinuousOn f (Icc a b) →
      Tendsto (fun n => UndergradKB.Calculus.simpson f a b (2 * n)) atTop
        (𝓝 (∫ x in a..b, f x))) :=
  ⟨UndergradKB.Calculus.simpson_weights, fun hab hf => UndergradKB.Calculus.tendsto_simpson hab hf⟩

/-- OpenStax Calculus 2:§3.6 Rule, error bound for Simpson's rule (CA-240). If `|f''''| ≤ M` on
`[a, b]` and `n > 0` is even, then `|S_n - ∫ f| ≤ M (b-a)⁵ / (180 n⁴)`. -/
@[kb "openstaxcalculus2016" "2:§3.6 Rule (Error Bound for Simpson's Rule), p. 292"]
theorem simpson_error_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 4 f) {a b M : ℝ} (hab : a ≤ b) {n : ℕ}
    (hn : Even n) (hpos : 0 < n) (hM : ∀ x ∈ Icc a b, |iteratedDeriv 4 f x| ≤ M) :
    |UndergradKB.Calculus.simpson f a b n - ∫ x in a..b, f x| ≤
      M * (b - a) ^ 5 / (180 * n ^ 4) :=
  UndergradKB.Calculus.simpson_error_le hf hab hn hpos hM

/-! ## Wave 3: further results -/

/-- OpenStax Calculus 2:§3.2 Recalled integrals of tan and sec (CA-218). On an interval where
`cos` does not vanish: `∫ tan = ln|sec|`, `∫ sec = ln|sec + tan|`, `∫ sec² = tan` and
`∫ sec tan = sec`, with the derivative facts behind the first two. -/
@[kb "openstaxcalculus2016" "2:§3.2 Recalled integrals of tan and sec, p. 253"]
theorem recalled_integrals_tan_sec :
    (∀ {x : ℝ}, Real.cos x ≠ 0 →
      HasDerivAt (fun x => Real.log |UndergradKB.Calculus.sec x|) (Real.tan x) x) ∧
    (∀ {x : ℝ}, Real.cos x ≠ 0 →
      HasDerivAt (fun x => Real.log |UndergradKB.Calculus.sec x + Real.tan x|)
        (UndergradKB.Calculus.sec x) x) ∧
    (∀ {b c : ℝ}, (∀ x ∈ uIcc b c, Real.cos x ≠ 0) →
      ∫ x in b..c, Real.tan x =
        Real.log |UndergradKB.Calculus.sec c| - Real.log |UndergradKB.Calculus.sec b|) ∧
    (∀ {b c : ℝ}, (∀ x ∈ uIcc b c, Real.cos x ≠ 0) →
      ∫ x in b..c, UndergradKB.Calculus.sec x =
        Real.log |UndergradKB.Calculus.sec c + Real.tan c| -
          Real.log |UndergradKB.Calculus.sec b + Real.tan b|) ∧
    (∀ {b c : ℝ}, (∀ x ∈ uIcc b c, Real.cos x ≠ 0) →
      ∫ x in b..c, UndergradKB.Calculus.sec x ^ 2 = Real.tan c - Real.tan b) ∧
    (∀ {b c : ℝ}, (∀ x ∈ uIcc b c, Real.cos x ≠ 0) →
      ∫ x in b..c, UndergradKB.Calculus.sec x * Real.tan x =
        UndergradKB.Calculus.sec c - UndergradKB.Calculus.sec b) :=
  ⟨fun h => UndergradKB.Calculus.hasDerivAt_log_abs_sec h,
    fun h => UndergradKB.Calculus.hasDerivAt_log_abs_sec_add_tan h,
    fun hI => UndergradKB.Calculus.integral_tan hI,
    fun hI => UndergradKB.Calculus.integral_sec hI,
    fun hI => UndergradKB.Calculus.integral_sec_sq hI,
    fun hI => UndergradKB.Calculus.integral_sec_mul_tan hI⟩

/-- OpenStax Calculus 2:Example 3.18 (CA-220). An antiderivative of `sec³` is
`(sec x tan x + ln|sec x + tan x|) / 2`, so the definite integral is the difference of its values. -/
@[kb "openstaxcalculus2016" "2:Example 3.18, p. 255"]
theorem integral_sec_cubed_example :
    (∀ {x : ℝ}, Real.cos x ≠ 0 →
      HasDerivAt (fun x => (UndergradKB.Calculus.sec x * Real.tan x +
        Real.log |UndergradKB.Calculus.sec x + Real.tan x|) / 2)
        (UndergradKB.Calculus.sec x ^ 3) x) ∧
    (∀ {b c : ℝ}, (∀ x ∈ uIcc b c, Real.cos x ≠ 0) →
      ∫ x in b..c, UndergradKB.Calculus.sec x ^ 3 =
        (UndergradKB.Calculus.sec c * Real.tan c +
            Real.log |UndergradKB.Calculus.sec c + Real.tan c|) / 2 -
          (UndergradKB.Calculus.sec b * Real.tan b +
            Real.log |UndergradKB.Calculus.sec b + Real.tan b|) / 2) :=
  ⟨fun h => UndergradKB.Calculus.hasDerivAt_sec_cube h,
    fun hI => UndergradKB.Calculus.integral_sec_cube hI⟩

/-- OpenStax Calculus 2:§3.4 Requirement: degree of numerator less than denominator (CA-227).
Dividing a real polynomial `P` by a nonzero `D` gives `P = Q D + R` with `deg R < deg D`, so the
rational function `P / D` is a polynomial plus a proper fraction. -/
@[kb "openstaxcalculus2016" "2:§3.4 Requirement: degree of numerator less than denominator, p. 271"]
theorem proper_fraction_by_long_division (P D : ℝ[X]) (hD : D ≠ 0) :
    ∃ Q R : ℝ[X], P = Q * D + R ∧ R.degree < D.degree :=
  UndergradKB.Calculus.polynomial_long_division P D hD

/-- OpenStax Calculus 2:§3.6 Remark (Simpson as weighted average) (CA-239). Simpson's sum with
`2n` subintervals is `(2 M_n + T_n) / 3`, a weighted average of the midpoint and trapezoidal
sums with `n` subintervals. -/
@[kb "openstaxcalculus2016" "2:§3.6 Remark (Simpson as weighted average), p. 292"]
theorem simpson_weighted_average (f : ℝ → ℝ) (a b : ℝ) {n : ℕ} (hn : 0 < n) :
    UndergradKB.Calculus.simpson f a b (2 * n) =
      (2 * UndergradKB.Calculus.midSum f a b n +
        trapezoidal_integral f n a b) / 3 :=
  UndergradKB.Calculus.simpson_two_mul f a b hn

/-- OpenStax Calculus 2:§3.7 Definition (infinite intervals, Eq. 3.16-3.18) (CA-241). The
improper integral over `[a, ∞)` is the limit of `∫_a^t f` as `t → ∞`: it equals the Lebesgue
integral for integrable `f`, for a nonnegative continuous `f` it exists exactly when `f` is
integrable, and `∫_1^∞ x^(-p)` converges exactly when `p > 1`. -/
@[kb "openstaxcalculus2016" "2:§3.7 Definition (infinite intervals, Eq. 3.16-3.18), p. 296"]
theorem improper_integral_infinite_interval :
    (∀ {f : ℝ → ℝ} {a : ℝ}, IntegrableOn f (Ioi a) →
      Tendsto (fun t => ∫ x in a..t, f x) atTop (𝓝 (∫ x in Ioi a, f x))) ∧
    (∀ {f : ℝ → ℝ} {a : ℝ}, ContinuousOn f (Ici a) → (∀ x, a ≤ x → 0 ≤ f x) →
      ((∃ L, Tendsto (fun t => ∫ x in a..t, f x) atTop (𝓝 L)) ↔ IntegrableOn f (Ioi a))) ∧
    (∀ p : ℝ, (∃ L, Tendsto (fun t => ∫ x in (1 : ℝ)..t, x ^ (-p)) atTop (𝓝 L)) ↔ 1 < p) :=
  ⟨fun hf => UndergradKB.Calculus.tendsto_intervalIntegral_of_integrableOn_Ioi hf,
    fun hc hnn => UndergradKB.Calculus.converges_Ioi_iff_integrableOn hc hnn,
    fun p => UndergradKB.Calculus.converges_Ioi_one_rpow_iff p⟩

/-- OpenStax Calculus 2:§3.7 Definition (infinite discontinuity, Eq. 3.19-3.21) (CA-242). For an
integrand integrable on `(a, b]`, the integral over `[t, b]` tends to the full integral as
`t → a⁺`; for nonnegative continuous integrands existence of the limit is integrability, and
`∫_0^1 x^(-p)` converges exactly when `p < 1`. -/
@[kb "openstaxcalculus2016" "2:§3.7 Definition (infinite discontinuity, Eq. 3.19-3.21), p. 302"]
theorem improper_integral_infinite_discontinuity :
    (∀ {f : ℝ → ℝ} {a b : ℝ}, a < b → IntegrableOn f (Ioc a b) →
      Tendsto (fun t => ∫ x in t..b, f x) (𝓝[>] a) (𝓝 (∫ x in Ioc a b, f x))) ∧
    (∀ {f : ℝ → ℝ} {a b : ℝ}, a < b → ContinuousOn f (Ioc a b) → (∀ x ∈ Ioc a b, 0 ≤ f x) →
      ((∃ L, Tendsto (fun t => ∫ x in t..b, f x) (𝓝[>] a) (𝓝 L)) ↔ IntegrableOn f (Ioc a b))) ∧
    (∀ p : ℝ, (∃ L, Tendsto (fun t => ∫ x in t..(1 : ℝ), x ^ (-p)) (𝓝[>] 0) (𝓝 L)) ↔ p < 1) :=
  ⟨fun hab hf => UndergradKB.Calculus.tendsto_intervalIntegral_left_endpoint hab hf,
    fun hab hc hnn => UndergradKB.Calculus.converges_Ioc_iff_integrableOn hab hc hnn,
    fun p => UndergradKB.Calculus.converges_Ioc_zero_one_rpow_iff p⟩

/-- OpenStax Calculus 2:Example 3.48 (CA-244). Gabriel's horn: revolving `y = 1/x` on `[1, ∞)`
about the `x`-axis gives volume integrals `∫_1^t π (1/x)² dx` tending to `π`, while the area
integrals `∫_1^t 1/x dx` have no limit. -/
@[kb "openstaxcalculus2016" "2:Example 3.48, p. 298"]
theorem gabriels_horn :
    Tendsto (fun t => ∫ x in (1 : ℝ)..t, Real.pi * (1 / x) ^ 2) atTop (𝓝 Real.pi) ∧
    ¬ ∃ L, Tendsto (fun t => ∫ x in (1 : ℝ)..t, 1 / x) atTop (𝓝 L) :=
  ⟨UndergradKB.Calculus.gabriel_volume, UndergradKB.Calculus.gabriel_area_diverges⟩

/-- OpenStax Calculus 2:§3.7 Student Project (Laplace transform definition) (CA-246). The Laplace
transform of `f` at `s` is the improper integral `∫_0^∞ e^(-s t) f(t) dt`. -/
@[kb "openstaxcalculus2016" "2:§3.7 Student Project (Laplace transform definition), p. 306"]
theorem laplace_transform_definition (f : ℝ → ℝ) (s : ℝ) :
    UndergradKB.Calculus.laplace f s = ∫ t in Ioi (0 : ℝ), Real.exp (-s * t) * f t :=
  rfl

/-- OpenStax Calculus 2:§3.7 Student Project (transform of a derivative) (CA-247). If `f` is
differentiable on `[0, ∞)` with continuous derivative `f'`, both of exponential order `a`, then
for `s > a` the transform of `f'` is `s` times the transform of `f` minus `f 0`. -/
@[kb "openstaxcalculus2016" "2:§3.7 Student Project (transform of a derivative), p. 307"]
theorem laplace_transform_of_derivative {f f' : ℝ → ℝ} {M M' a s : ℝ}
    (hf : ∀ t, 0 ≤ t → HasDerivAt f (f' t) t) (hf'c : ContinuousOn f' (Ici 0))
    (hb : ∀ t, 0 ≤ t → |f t| ≤ M * Real.exp (a * t))
    (hb' : ∀ t, 0 ≤ t → |f' t| ≤ M' * Real.exp (a * t)) (has : a < s) :
    UndergradKB.Calculus.laplace f' s = s * UndergradKB.Calculus.laplace f s - f 0 :=
  UndergradKB.Calculus.laplace_deriv hf hf'c hb hb' has

/-- OpenStax Calculus 2:§3.7 Student Project (transform of an integral) (CA-248). For a continuous
`f` of exponential order `a` and `s > 0` with `s > a`, the transform of `t ↦ ∫_0^t f` is the
transform of `f` divided by `s`. -/
@[kb "openstaxcalculus2016" "2:§3.7 Student Project (transform of an integral), p. 307"]
theorem laplace_transform_of_integral {f : ℝ → ℝ} {M a s : ℝ} (hc : Continuous f)
    (hb : ∀ t, 0 ≤ t → |f t| ≤ M * Real.exp (a * t)) (hs : 0 < s) (has : a < s) :
    UndergradKB.Calculus.laplace (fun t => ∫ u in (0 : ℝ)..t, f u) s =
      UndergradKB.Calculus.laplace f s / s :=
  UndergradKB.Calculus.laplace_integral hc hb hs has

end UndergradKB.Calculus.Course.V2C3
