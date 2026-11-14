import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import UndergradKB.Common.Attr
import UndergradKB.Probability.ExamplesLead
import UndergradKB.Probability.ExamplesLeadWalk
import UndergradKB.Probability.ExamplesLimits
import UndergradKB.Probability.ExamplesBranching
import UndergradKB.Probability.GeneratingFunctions
import UndergradKB.Probability.Branching
import UndergradKB.Probability.MgfSeries
import UndergradKB.Probability.Moments
import UndergradKB.Probability.Sums
import UndergradKB.Probability.ExamplesKeyfitz
import UndergradKB.Probability.ExamplesLeadFair

/-!
# Course layer, Chapter 10 (Grinstead–Snell, Generating Functions)

Thin wrappers stating the book's results of Chapter 10 as direct instances of Mathlib.
-/

namespace UndergradKB.Probability.Course

open MeasureTheory ProbabilityTheory

/-- Grinstead–Snell §10.1 moment generating function (PR-102). The moment generating function is
`g(t) = E(e^(tX))`, and when it is finite near `0` its `n`-th derivative at `0` is the moment
`E(X^n)`. -/
@[kb "grinsteadsnell2006" "§10.1 moment generating function, p. 374"]
theorem gs_section_10_1_moment_generating_function {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (t : ℝ)
    (h : 0 ∈ interior (integrableExpSet X P)) (n : ℕ) :
    mgf X P t = ∫ ω, Real.exp (t * X ω) ∂P ∧ iteratedDeriv n (mgf X P) 0 = moment X n P :=
  ⟨rfl, iteratedDeriv_mgf_zero h n⟩

/-- Grinstead–Snell §10.2 generating function of a sum (PR-104). The moment generating function
of a sum of independent random variables is the product of their moment generating functions. -/
@[kb "grinsteadsnell2006" "§10.2 generating function of a sum, p. 378"]
theorem gs_section_10_2_generating_function_of_a_sum {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ) (hX : Measurable X)
    (hY : Measurable Y) (hXY : IndepFun X Y P) (Z : ι → Ω → ℝ) (hZ : iIndepFun Z P)
    (hZm : ∀ i, Measurable (Z i)) (s : Finset ι) (t : ℝ) :
    mgf (X + Y) P t = mgf X P t * mgf Y P t ∧
      mgf (∑ i ∈ s, Z i) P t = ∏ i ∈ s, mgf (Z i) P t :=
  ⟨hXY.mgf_add' hX.aestronglyMeasurable hY.aestronglyMeasurable, hZ.mgf_sum hZm s⟩

/-- Grinstead–Snell §10.3 characteristic function (PR-109). The characteristic function of a
random variable `X` with law `μ` is `τ ↦ E(e^(i τ X))`. -/
@[kb "grinsteadsnell2006" "§10.3 characteristic function, p. 405"]
theorem gs_section_10_3_characteristic_function {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (μ : Measure ℝ) (hX : HasLaw X μ P) (τ : ℝ) :
    charFun μ τ = ∫ ω, Complex.exp (τ * X ω * Complex.I) ∂P := by
  rw [charFun_apply_real, ← hX.map_eq, integral_map hX.aemeasurable (by fun_prop)]

/-- Grinstead–Snell Theorem 10.1 (PR-103). The generating function determines the distribution. -/
@[kb "grinsteadsnell2006" "Theorem 10.1, p. 376"]
theorem gs_theorem_10_1 : type_of% @UndergradKB.Probability.eq_of_genFun_eq :=
  @UndergradKB.Probability.eq_of_genFun_eq

/-- Grinstead–Snell Theorem 10.2 (PR-106). The extinction probability of a branching process is the
smallest root of `z = h(z)`. -/
@[kb "grinsteadsnell2006" "Theorem 10.2, p. 388"]
theorem gs_theorem_10_2 : type_of% @UndergradKB.Probability.extinction_smallest_root :=
  @UndergradKB.Probability.extinction_smallest_root

/-- Grinstead–Snell Theorem 10.2 (PR-106), mean offspring at most `1`: extinction is certain. -/
@[kb "grinsteadsnell2006" "Theorem 10.2, p. 388"]
theorem gs_theorem_10_2_eq_one : type_of% @UndergradKB.Probability.extinction_prob_eq_one :=
  @UndergradKB.Probability.extinction_prob_eq_one

/-- Grinstead–Snell Theorem 10.2 (PR-106), mean offspring above `1`: extinction probability below `1`. -/
@[kb "grinsteadsnell2006" "Theorem 10.2, p. 388"]
theorem gs_theorem_10_2_lt_one : type_of% @UndergradKB.Probability.extinction_prob_lt_one :=
  @UndergradKB.Probability.extinction_prob_lt_one

/-- Grinstead–Snell Theorem 10.3 (PR-107). For a bounded variable `∑ μ_k t^k/k!` converges to `g(t)`. -/
@[kb "grinsteadsnell2006" "Theorem 10.3, p. 404"]
theorem gs_theorem_10_3 : type_of% @UndergradKB.Probability.hasSum_moments_mgf :=
  @UndergradKB.Probability.hasSum_moments_mgf

/-- Grinstead–Snell Theorem 10.4 (PR-108). For a bounded variable the moment generating function
determines the distribution. -/
@[kb "grinsteadsnell2006" "Theorem 10.4, p. 405"]
theorem gs_theorem_10_4 : type_of% @UndergradKB.Probability.map_eq_of_mgf_eq_of_bounded :=
  @UndergradKB.Probability.map_eq_of_mgf_eq_of_bounded

/-- Grinstead–Snell Example 10.8 (PR-158). Tree measure of the branching process with `p₀ = 1/2, p₁ = p₂ = 1/4`. -/
@[kb "grinsteadsnell2006" "Example 10.8, p. 386"]
theorem gs_example_10_8 : type_of% @UndergradKB.Probability.exampleOffspring_two_two :=
  @UndergradKB.Probability.exampleOffspring_two_two

/-- Grinstead–Snell Example 10.8 (PR-158). The probability of dying out by a given generation. -/
@[kb "grinsteadsnell2006" "Example 10.8, p. 386"]
theorem gs_example_10_8_b : type_of% @UndergradKB.Probability.exampleOffspring_extinctProb :=
  @UndergradKB.Probability.exampleOffspring_extinctProb

/-- Grinstead–Snell Example 10.10 (PR-158). The generating function iterates by composition. -/
@[kb "grinsteadsnell2006" "Example 10.10, p. 392"]
theorem gs_example_10_10 : type_of% @UndergradKB.Probability.exampleOffspring_gf_comp :=
  @UndergradKB.Probability.exampleOffspring_gf_comp

/-- Grinstead–Snell Example 10.10 (PR-158). The mean number of offspring and the extinction probability. -/
@[kb "grinsteadsnell2006" "Example 10.10, p. 392"]
theorem gs_example_10_10_b : type_of% @UndergradKB.Probability.exampleOffspring_extinction :=
  @UndergradKB.Probability.exampleOffspring_extinction

/-- Grinstead–Snell Example 10.11 (PR-142). The generating function and mean of the geometric offspring law. -/
@[kb "grinsteadsnell2006" "Example 10.11, p. 392"]
theorem gs_example_10_11 : type_of% @UndergradKB.Probability.geomOffspring_gf_mean :=
  @UndergradKB.Probability.geomOffspring_gf_mean

/-- Grinstead–Snell Example 10.11 (PR-142). The extinction probability for the geometric offspring law. -/
@[kb "grinsteadsnell2006" "Example 10.11, p. 392"]
theorem gs_example_10_11_b : type_of% @UndergradKB.Probability.geomOffspring_extinction :=
  @UndergradKB.Probability.geomOffspring_extinction

/-- Grinstead–Snell Example 10.11 (PR-142). For the geometric offspring law, `d < 1` exactly when `m > 1`. -/
@[kb "grinsteadsnell2006" "Example 10.11, p. 392"]
theorem gs_example_10_11_c : type_of% @UndergradKB.Probability.geomOffspring_d_lt_one_iff :=
  @UndergradKB.Probability.geomOffspring_d_lt_one_iff

/-! ## Worked examples (wave 4) -/

/-- Grinstead–Snell Example 10.7 (PR-179). Closed form: the book's recursion for the first time in the lead is solved by `r_{2k+1} = C_k p^{k+1} q^k`, `r_{2k} = 0` (`C_k` the Catalan numbers), and... -/
@[kb "grinsteadsnell2006" "Example 10.7, p. 380"]
theorem gs_example_10_7 : type_of% @UndergradKB.Probability.lead_closed_form :=
  @UndergradKB.Probability.lead_closed_form

/-- Grinstead–Snell Example 10.7 (PR-179). Generating function: for `4pqz² ≤ 1` (in particular `|z| ≤ 1`) the series `h(z) = ∑ r_n z^n` converges, satisfies `h = pz + qz h²`, and for `z ≠ 0` equals... -/
@[kb "grinsteadsnell2006" "Example 10.7, p. 380"]
theorem gs_example_10_7_b : type_of% @UndergradKB.Probability.lead_generating_function :=
  @UndergradKB.Probability.lead_generating_function

/-- Grinstead–Snell Example 10.7 (PR-179). Probability of ever leading: with `p + q = 1`, `∑ r_n = (1 - |p - q|) / (2q)`, which is `p/q` if `p < q` and `1` if `p ≥ q`. -/
@[kb "grinsteadsnell2006" "Example 10.7, p. 380"]
theorem gs_example_10_7_c : type_of% @UndergradKB.Probability.lead_total_probability :=
  @UndergradKB.Probability.lead_total_probability

/-- Grinstead–Snell Example 10.7 (PR-179). The walk itself: the probability that Peter is first in the lead at time
`n` satisfies the book's recursion, equals `C_k p^{k+1} q^k` at `n = 2k+1`, and sums to `min(1, p/q)`. -/
@[kb "grinsteadsnell2006" "Example 10.7, p. 380"]
theorem gs_example_10_7_e : type_of% @UndergradKB.Probability.leadProb_isLeadSeq :=
  @UndergradKB.Probability.leadProb_isLeadSeq

/-- Grinstead–Snell Example 10.7 (PR-179). Expected waiting time: if `p > q` (with `p + q = 1`), `E(T) = ∑ n r_n = 1/(p - q)`. -/
@[kb "grinsteadsnell2006" "Example 10.7, p. 380"]
theorem gs_example_10_7_d : type_of% @UndergradKB.Probability.lead_expected_time :=
  @UndergradKB.Probability.lead_expected_time

/-- Grinstead–Snell Example 10.14 (PR-180). The one-buyer chain letter is unfavourable: the expected winnings are negative for every p < 1. -/
@[kb "grinsteadsnell2006" "Example 10.14, p. 396"]
theorem gs_example_10_14 : type_of% @UndergradKB.Probability.chain_letter_unfavorable :=
  @UndergradKB.Probability.chain_letter_unfavorable

/-- Grinstead–Snell Example 10.14 (PR-180). Branching version: with mean offspring `m ≥ 0` the expected winnings `50 m + 50 m^12 - 100` are positive iff `m > 1`, and for `p₀ = 0.2, p₁ = 0.5, p₂ = 0.3`... -/
@[kb "grinsteadsnell2006" "Example 10.14, p. 396"]
theorem gs_example_10_14_b : type_of% @UndergradKB.Probability.chain_letter_branching :=
  @UndergradKB.Probability.chain_letter_branching


/-! ## Wave 5 course layer (this library) -/

/-- Grinstead–Snell Example 10.15 (PR-105). The uniform law on `[0,1]` has moment generating function `(e^t - 1)/t` for `t ≠ 0`. -/
@[kb "grinsteadsnell2006" "Example 10.15, p. 402"]
theorem gs_example_10_15 : type_of% @UndergradKB.Probability.mgf_uniform_unit :=
  @UndergradKB.Probability.mgf_uniform_unit

/-- Grinstead–Snell Example 10.16 (PR-105). The exponential law of rate `r` has moment generating function `r/(r - t)` for `t < r`. -/
@[kb "grinsteadsnell2006" "Example 10.16, p. 403"]
theorem gs_example_10_16 : type_of% @UndergradKB.Probability.mgf_exponential :=
  @UndergradKB.Probability.mgf_exponential

/-- Grinstead–Snell Example 10.17 (PR-105). A normal variable with mean `μ` and variance `v` has moment generating function `exp (μ t + v t² / 2)`. -/
@[kb "grinsteadsnell2006" "Example 10.17, p. 403"]
theorem gs_example_10_17 : type_of% @UndergradKB.Probability.mgf_normal :=
  @UndergradKB.Probability.mgf_normal

/-- Grinstead–Snell Example 10.1 (PR-105). If `X` is uniform on `{1, …, n}` (`n ≥ 1`), its moment generating function is `(e^t + e^{2t} + ... + e^{nt}) / n`. -/
@[kb "grinsteadsnell2006" "Example 10.1, p. 375"]
theorem gs_example_10_1 : type_of% @UndergradKB.Probability.mgf_uniform_discrete :=
  @UndergradKB.Probability.mgf_uniform_discrete

/-- Grinstead–Snell Example 10.2 (PR-105). The binomial law with `n` trials and success probability `p` has moment generating function `(p e^t + q)^n`, where `q = 1 - p`. -/
@[kb "grinsteadsnell2006" "Example 10.2, p. 375"]
theorem gs_example_10_2 : type_of% @UndergradKB.Probability.mgf_binomial :=
  @UndergradKB.Probability.mgf_binomial

/-- Grinstead–Snell Example 10.3 (PR-105). For the geometric law with `P(X = j) = q^{j-1} p` (`j ≥ 1`, `q = 1 - p`), realized as Mathlib's geometric law on `ℕ` shifted by one, the moment generating function is `p e^t / (1 - q e^t)` whenever `q e^t < 1`. -/
@[kb "grinsteadsnell2006" "Example 10.3, p. 375"]
theorem gs_example_10_3 : type_of% @UndergradKB.Probability.mgf_geometric :=
  @UndergradKB.Probability.mgf_geometric

/-- Grinstead–Snell Example 10.4 (PR-105). The Poisson law with mean `λ` has moment generating function `e^{λ(e^t - 1)}`. -/
@[kb "grinsteadsnell2006" "Example 10.4, p. 376"]
theorem gs_example_10_4 : type_of% @UndergradKB.Probability.mgf_poisson :=
  @UndergradKB.Probability.mgf_poisson

/-- Grinstead–Snell Examples 10.5, 10.6 (PR-093), convolution of masses (Vandermonde). -/
@[kb "grinsteadsnell2006" "Example 10.5, p. 379"]
theorem gs_example_10_5 : type_of% @UndergradKB.Probability.binomial_mass_convolution :=
  @UndergradKB.Probability.binomial_mass_convolution

/-- Grinstead–Snell Examples 10.5, 10.6 (PR-093), law statement. The sum of independent `binomial m p` and `binomial n p` variables is `binomial (m + n) p`. -/
@[kb "grinsteadsnell2006" "Example 10.5, p. 379"]
theorem gs_example_10_5_b : type_of% @UndergradKB.Probability.hasLaw_add_binomial :=
  @UndergradKB.Probability.hasLaw_add_binomial

/-- Grinstead–Snell Example 10.9 (PR-210). Table 10.2 (Keyfitz's offspring law of Japanese women, ages 45-49 in 1960). Erratum: the printed probabilities `.2092, .2584, .2360, .1593, .0828, .0357, .0133, .0042, .0011, .0002, .0000` sum to `1.0002`, not `1`; we use the table divided by its sum as the offspring law. -/
@[kb "grinsteadsnell2006" "Example 10.9, p. 390"]
theorem gs_example_10_9 : type_of% @UndergradKB.Probability.keyfitz_extinction :=
  @UndergradKB.Probability.keyfitz_extinction

/-- Grinstead–Snell Example 10.12 (PR-211), solving for the parameters. For the geometric offspring law `p_k = b c^(k-1)` with mean `m = b/(1-c)^2 > 1` and extinction probability `d = (1-b-c)/(c(1-c))` (Example 10.11), `c = (m-1)/(m-d)` and `b = m ((1-d)/(m-d))^2`. -/
@[kb "grinsteadsnell2006" "Example 10.12, p. 393"]
theorem gs_example_10_12 : type_of% @UndergradKB.Probability.geom_fit_parameters :=
  @UndergradKB.Probability.geom_fit_parameters

/-- Grinstead–Snell Example 10.12 (PR-211), the numbers. With the Keyfitz values `m = 1.837`, `d = .324`, the parameters `c = (m-1)/(m-d)` and `b = m((1-d)/(m-d))^2` satisfy `.5532 < c < .5533` and `.3667 < b < .3668` (the book prints `b = .3666`, which is a rounding slip: `b = .36671...`; with the book's rounded `c = .5533` one gets `b`-values consistent with Table 10.3), and `(1-c)^2 < b < 1-c`, as... -/
@[kb "grinsteadsnell2006" "Example 10.12, p. 393"]
theorem gs_example_10_12_b : type_of% @UndergradKB.Probability.geom_fit_keyfitz :=
  @UndergradKB.Probability.geom_fit_keyfitz

/-- Grinstead–Snell Example 10.12 (PR-211), Table 10.3. With the book's rounded parameters `b = .3666`, `c = .5533`, the geometric column of Table 10.3 for `p_1, ..., p_10` is reproduced to four places (`.3666, .2028, .1122, .0621, .0344, .0190, .0105, .0058, .0032, .0018`), while `p_0 = 1 - b/(1-c)` is `.1793` (the book prints `.1816`, an erratum: with it the table would sum to `1` before the positiv... -/
@[kb "grinsteadsnell2006" "Example 10.12, p. 393"]
theorem gs_example_10_12_c : type_of% @UndergradKB.Probability.geom_fit_table :=
  @UndergradKB.Probability.geom_fit_table

/-- Grinstead–Snell Example 10.13 (PR-212), the law of `Z_n`. Erratum: the book writes "`m < 1`", but the formulas need `m > 1` (for `m ≤ 1` one has `d = 1` and `m^n → 0` or `= 1`, and the extinction formulas degenerate). For the geometric offspring law `p_k = b c^(k-1)` with `m = b/(1-c)^2 > 1` and `d = (1-b-c)/(c(1-c))`, put `M = m^n`. -/
@[kb "grinsteadsnell2006" "Example 10.13, p. 395"]
theorem gs_example_10_13 : type_of% @UndergradKB.Probability.geom_generation_law :=
  @UndergradKB.Probability.geom_generation_law

/-- Grinstead–Snell Example 10.13 (PR-212), `P(Z_n = 0) → d`. In the setting of `geom_generation_law`, `P(Z_n = 0) = d (m^n-1)/(m^n-d)` converges to the extinction probability `d = (1-b-c)/(c(1-c))`. -/
@[kb "grinsteadsnell2006" "Example 10.13, p. 395"]
theorem gs_example_10_13_b : type_of% @UndergradKB.Probability.geom_generation_zero_tendsto :=
  @UndergradKB.Probability.geom_generation_zero_tendsto

/-- Grinstead–Snell Example 10.13 (PR-212), the local limit. In the setting of `geom_generation_law` (`m > 1`; the book's "`m < 1`" is an erratum), for every `t > 0` and `j_n = ⌊t m^n⌋`, `m^n P(Z_n = j_n) → (1-d)^2 e^{-t(1-d)}`, where `P(Z_n = j)` is the book's law `lawN d (m^n) j` (identified with the law of `Z_n` by `geom_generation_law`). -/
@[kb "grinsteadsnell2006" "Example 10.13, p. 395"]
theorem gs_example_10_13_c : type_of% @UndergradKB.Probability.geom_generation_local_limit :=
  @UndergradKB.Probability.geom_generation_local_limit

/-! ## Wave 6 course layer (this library) -/

/-- Grinstead–Snell Example 10.7 (PR-179), the fair coin: if `p = q = 1/2`, the expected time `E(T) = ∑ n r_n` until Peter first leads is infinite (the series diverges), although `∑ r_n = 1`. -/
@[kb "grinsteadsnell2006" "Example 10.7, p. 380"]
theorem gs_example_10_7_f : type_of% @UndergradKB.Probability.lead_expected_time_fair :=
  @UndergradKB.Probability.lead_expected_time_fair

end UndergradKB.Probability.Course
