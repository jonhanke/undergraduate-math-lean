import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import UndergradKB.Common.Attr

/-!
# Keller–Trotter, Chapter 10 (probability): thin wrappers over Mathlib
-/

namespace UndergradKB.Combinatorics.Course.KellerTrotter
open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- CO-238. In `n` independent trials with success probability `p`, the number of successes equals
`i` with probability `C(n,i) p^i (1-p)^(n-i)`. -/
@[kb "kellertrotter2017" "text (binomial distribution), p. 242"]
theorem text_p242_binomial (n i : ℕ) (p : I) :
    (binomial n p).real {i} = (n.choose i) * (p : ℝ) ^ i * (1 - (p : ℝ)) ^ (n - i) :=
  binomial_real_singleton n i p

/-- CO-242. Markov's inequality: `P(|X| ≥ k) ≤ E|X| / k` for `k > 0`. -/
@[kb "kellertrotter2017" "Theorem 10.20, p. 245"]
theorem thm_10_20 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Integrable X μ) {k : ℝ} (hk : 0 < k) :
    μ.real {ω | k ≤ |X ω|} ≤ (∫ ω, |X ω| ∂μ) / k := by
  rw [le_div_iff₀ hk, mul_comm]
  exact mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
    hX.abs k

/-- CO-244. For pairwise independent square-integrable random variables the variance of the sum is
the sum of the variances. -/
@[kb "kellertrotter2017" "text (Exercise 10.22), p. 246"]
theorem ex_10_22_variance_sum {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ι → Ω → ℝ} {s : Finset ι}
    (hs : ∀ i ∈ s, MemLp (X i) 2 μ) (h : Set.Pairwise ↑s fun i j => X i ⟂ᵢ[μ] X j) :
    variance (∑ i ∈ s, X i) μ = ∑ i ∈ s, variance (X i) μ :=
  IndepFun.variance_sum hs h

/-- CO-246. `var(X) = E(X²) - E(X)²`. -/
@[kb "kellertrotter2017" "Proposition 10.23, p. 247"]
theorem prop_10_23 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    variance X μ = μ[X ^ 2] - μ[X] ^ 2 :=
  variance_eq_sub hX

/-- CO-247. Chebyshev's inequality: with `σ = √var X > 0`, `P(|X - μ| ≤ kσ) ≥ 1 - 1/k²`. -/
@[kb "kellertrotter2017" "Theorem 10.24, p. 247"]
theorem thm_10_24 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : MemLp X 2 μ) (hσ : 0 < variance X μ) {k : ℝ} (hk : 0 < k) :
    1 - 1 / k ^ 2 ≤ μ.real {ω | |X ω - μ[X]| ≤ k * Real.sqrt (variance X μ)} := by
  have hc : 0 < k * Real.sqrt (variance X μ) := mul_pos hk (Real.sqrt_pos.2 hσ)
  have h := meas_ge_le_variance_div_sq hX hc
  have h2 : μ.real {ω | k * Real.sqrt (variance X μ) ≤ |X ω - μ[X]|} ≤
      variance X μ / (k * Real.sqrt (variance X μ)) ^ 2 := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) h
  have h3 : variance X μ / (k * Real.sqrt (variance X μ)) ^ 2 = 1 / k ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hσ.le]
    field_simp
  have hu := measureReal_union_le (μ := μ)
    {ω | |X ω - μ[X]| ≤ k * Real.sqrt (variance X μ)}
    {ω | k * Real.sqrt (variance X μ) ≤ |X ω - μ[X]|}
  have hall : ({ω | |X ω - μ[X]| ≤ k * Real.sqrt (variance X μ)} ∪
      {ω | k * Real.sqrt (variance X μ) ≤ |X ω - μ[X]|}) = Set.univ := by
    ext ω
    simpa using le_total _ _
  rw [hall] at hu
  simp only [probReal_univ] at hu
  linarith


/-! ### Definitions of Chapter 10 in the book's terms -/

section Definitions

variable {S : Type*} [MeasurableSpace S] (μ : Measure S)

/-- CO-235. A probability space: `P(∅) = 0`, `P(S) = 1`, and `P` is additive on disjoint events. -/
@[kb "kellertrotter2017" "Definition (unnumbered) probability space, p. 238"]
theorem def_p238_probability_space [IsProbabilityMeasure μ] :
    μ ∅ = 0 ∧ μ Set.univ = 1 ∧
      ∀ A B : Set S, MeasurableSet A → MeasurableSet B → Disjoint A B →
        μ (A ∪ B) = μ A + μ B :=
  ⟨measure_empty, measure_univ, fun _ _ _ hB hd => measure_union hd hB⟩

/-- CO-236. Conditional probability: `P(A | B) = P(A ∩ B) / P(B)`, written as
`P(B)⁻¹ · P(B ∩ A)`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) conditional probability, p. 240"]
theorem def_p240_conditional {A B : Set S} (hB : MeasurableSet B) :
    μ[A | B] = (μ B)⁻¹ * μ (B ∩ A) :=
  cond_apply hB μ A

/-- CO-237. Events are independent when `P(A ∩ B) = P(A) P(B)`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) independent events, p. 241"]
theorem def_p241_independent [IsProbabilityMeasure μ] {A B : Set S} (hA : MeasurableSet A)
    (hB : MeasurableSet B) : IndepSet A B μ ↔ μ (A ∩ B) = μ A * μ B :=
  indepSet_iff_measure_inter_eq_mul hA hB μ

/-- CO-239. On a finite outcome set the expectation of a random variable `X` is the weighted
sum `∑ X(x) P(x)`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) random variable and expectation, p. 242"]
theorem def_p242_expectation [Fintype S] [MeasurableSingletonClass S] [IsFiniteMeasure μ]
    (X : S → ℝ) : ∫ x, X x ∂μ = ∑ x, X x * μ.real {x} := by
  rw [integral_fintype (Integrable.of_finite)]
  simp [smul_eq_mul, mul_comm]

/-- CO-243. The variance is `E((X - E X)^2)`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) variance, p. 246"]
theorem def_p246_variance {X : S → ℝ} (hX : AEMeasurable X μ) :
    Var[X; μ] = ∫ ω, (X ω - μ[X]) ^ 2 ∂μ :=
  variance_eq_integral hX

end Definitions

end UndergradKB.Combinatorics.Course.KellerTrotter
