import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Moments.Variance
import UndergradKB.Common.Attr
import UndergradKB.Probability.Branching
import UndergradKB.Probability.ExamplesExpectation
import UndergradKB.Probability.LimitTheorems

/-! # Probability: worked examples on limit theorems, branching and beta priors

Examples 8.2, 8.3 (Chebyshev bounds for averages), 10.8, 10.10 (a branching process with
`p₀ = 1/2, p₁ = p₂ = 1/4`), and 4.23 (beta prior with Bernoulli data). -/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal unitInterval

namespace UndergradKB.Probability

/-! ## Examples 8.2 and 8.3 (PR-157) -/

section Chebyshev

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Chebyshev bound for averages of an independent trials process with mean `m` and variance `v`:
`P(|S_n/n - m| ≥ ε) ≤ v / (n ε²)`. -/
theorem average_chebyshev {X : ℕ → Ω → ℝ} (hL : ∀ i, MemLp (X i) 2 P) (hind : iIndepFun X P)
    {m v : ℝ} (hm : ∀ i, P[X i] = m) (hv : ∀ i, Var[X i; P] = v) {n : ℕ} (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | ε ≤ |(∑ k ∈ range n, X k ω) / n - m|} ≤ v / (n * ε ^ 2) :=
  weak_law_chebyshev_bound hL (fun _ _ hij => hind.indepFun hij) hm hv hn hε

/-- Grinstead–Snell Example 8.2 (PR-157). For `n ≥ 1` independent rolls `X_j` of a fair die with sum
`S_n`, `P(|S_n/n - 7/2| ≥ ε) ≤ 35 / (12 n ε²)`. -/
@[kb "grinsteadsnell2006" "Example 8.2, p. 316"]
theorem die_chebyshev {X : ℕ → Ω → ℝ} (hind : iIndepFun X P)
    (hX : ∀ i, HasLaw (X i) dieLaw P) {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | ε ≤ |(∑ k ∈ range n, X k ω) / n - 7 / 2|} ≤ 35 / (12 * n * ε ^ 2) := by
  have h := average_chebyshev (m := 7 / 2) (v := 35 / 12)
    (fun i => (hX i).memLp dieLaw_memLp) hind
    (fun i => (die_law_mean_variance (hX i)).1) (fun i => (die_law_mean_variance (hX i)).2) hn hε
  convert h using 1
  have : (n : ℝ) ≠ 0 := by positivity
  field_simp

lemma bernoulliLaw_memLp_id (p : I) : MemLp id 2 Ber((1 : ℝ), (0 : ℝ), p) := by
  rw [bernoulliMeasure_def]
  exact MemLp.add_measure (MemLp.smul_measure_nnreal (memLp_dirac (by simp)))
    (MemLp.smul_measure_nnreal (memLp_dirac (by simp)))

/-- Grinstead–Snell Example 8.3 (PR-157). For a Bernoulli trials process with success probability
`.3` and `A_n = S_n/n`, `P(|A_n - .3| ≥ .1) ≤ 21/n` (here `ε = 1/10`, variance `.21`). -/
@[kb "grinsteadsnell2006" "Example 8.3, p. 318"]
theorem bernoulli_chebyshev {X : ℕ → Ω → ℝ} (hind : iIndepFun X P)
    (hX : ∀ i, HasLaw (X i) Ber(1, 0, (⟨3 / 10, by norm_num, by norm_num⟩ : I)) P)
    {n : ℕ} (hn : 0 < n) :
    P.real {ω | (1 / 10 : ℝ) ≤ |(∑ k ∈ range n, X k ω) / n - 3 / 10|} ≤ 21 / n := by
  have hmean : ∀ i, P[X i] = 3 / 10 := by
    intro i
    rw [(hX i).integral_eq, integral_bernoulliMeasure]
    norm_num
  have hvar : ∀ i, Var[X i; P] = 21 / 100 := by
    intro i
    rw [(hX i).variance_eq, variance_eq_sub (bernoulliLaw_memLp_id _)]
    simp only [Pi.pow_apply, id_eq]
    rw [integral_bernoulliMeasure, integral_bernoulliMeasure]
    norm_num
  have h := average_chebyshev (m := 3 / 10) (v := 21 / 100)
    (fun i => (hX i).memLp (bernoulliLaw_memLp_id _)) hind hmean hvar hn (ε := 1 / 10) (by norm_num)
  convert h using 1
  have : (n : ℝ) ≠ 0 := by positivity
  field_simp
  norm_num

end Chebyshev

/-! ## Examples 10.8 and 10.10 (PR-158) -/

/-- The offspring law of Example 10.8: `p₀ = 1/2`, `p₁ = p₂ = 1/4`, and `p_k = 0` for `k ≥ 3`. -/
noncomputable def exampleOffspring (k : ℕ) : ℝ :=
  if k = 0 then 1 / 2 else if k = 1 then 1 / 4 else if k = 2 then 1 / 4 else 0

lemma exampleOffspring_hasSum_aux (f : ℕ → ℝ) (a b c : ℝ)
    (hf : ∀ k, f k = if k = 0 then a else if k = 1 then b else if k = 2 then c else 0) :
    HasSum f (a + b + c) := by
  have h : ∀ k ∉ range 3, f k = 0 := by
    intro k hk
    have : 3 ≤ k := by simpa using hk
    simp only [hf, show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega, ite_false]
  have : HasSum f (∑ b ∈ range 3, f b) := hasSum_sum_of_ne_finset_zero h
  convert this using 1
  simp [Finset.sum_range_succ, hf]

lemma exampleOffspring_isOffspring : IsOffspring exampleOffspring where
  nonneg k := by unfold exampleOffspring; split_ifs <;> norm_num
  hasSum := by
    have := exampleOffspring_hasSum_aux exampleOffspring (1 / 2) (1 / 4) (1 / 4) (fun k => rfl)
    convert this using 1; norm_num

lemma exampleOffspring_gf (z : ℝ) :
    offspringGF exampleOffspring z = 1 / 2 + z / 4 + z ^ 2 / 4 := by
  have := exampleOffspring_hasSum_aux (fun k => exampleOffspring k * z ^ k) (1 / 2) (z / 4)
    (z ^ 2 / 4) (by
      intro k
      unfold exampleOffspring
      split_ifs with h0 h1 h2 <;> subst_vars <;> simp_all <;> ring)
  exact this.tsum_eq

lemma exampleOffspring_mean : HasSum (fun k : ℕ => (k : ℝ) * exampleOffspring k) (3 / 4) := by
  have := exampleOffspring_hasSum_aux (fun k => (k : ℝ) * exampleOffspring k) 0 (1 / 4) (1 / 2) (by
    intro k
    unfold exampleOffspring
    split_ifs with h0 h1 h2 <;> subst_vars <;> simp_all; norm_num)
  convert this using 1; norm_num

/-- Grinstead–Snell Example 10.8 (PR-158), tree measure. With `p₀ = 1/2, p₁ = p₂ = 1/4`, given two
offspring in the first generation, the probability of two in the second generation is
`p₀p₂ + p₁p₁ + p₂p₀ = 5/16`. -/
@[kb "grinsteadsnell2006" "Example 10.8, p. 386"]
theorem exampleOffspring_two_two :
    exampleOffspring 0 * exampleOffspring 2 + exampleOffspring 1 * exampleOffspring 1 +
      exampleOffspring 2 * exampleOffspring 0 = 5 / 16 := by
  simp [exampleOffspring]; norm_num

/-- Grinstead–Snell Example 10.8 (PR-158), dying out. The probability of dying out by generation
`m` is `d₀ = 0`, `d₁ = 1/2`, `d₂ = 11/16`. -/
@[kb "grinsteadsnell2006" "Example 10.8, p. 386"]
theorem exampleOffspring_extinctProb :
    extinctProb exampleOffspring 0 = 0 ∧ extinctProb exampleOffspring 1 = 1 / 2 ∧
      extinctProb exampleOffspring 2 = 11 / 16 := by
  refine ⟨rfl, ?_, ?_⟩
  · rw [extinctProb_succ, extinctProb_zero, exampleOffspring_gf]; norm_num
  · rw [extinctProb_succ, extinctProb_succ, extinctProb_zero, exampleOffspring_gf,
      exampleOffspring_gf]; norm_num

/-- Grinstead–Snell Example 10.10 (PR-158). For `p₀ = 1/2, p₁ = p₂ = 1/4` the generating function is
`h(z) = 1/2 + z/4 + z²/4` and `h(h(z)) = 11/16 + z/8 + 9z²/64 + z³/32 + z⁴/64`. -/
@[kb "grinsteadsnell2006" "Example 10.10, p. 392"]
theorem exampleOffspring_gf_comp (z : ℝ) :
    offspringGF exampleOffspring z = 1 / 2 + z / 4 + z ^ 2 / 4 ∧
    offspringGF exampleOffspring (offspringGF exampleOffspring z) =
      11 / 16 + z / 8 + 9 * z ^ 2 / 64 + z ^ 3 / 32 + z ^ 4 / 64 := by
  refine ⟨exampleOffspring_gf z, ?_⟩
  rw [exampleOffspring_gf, exampleOffspring_gf]
  ring

/-- Grinstead–Snell Example 10.10 (PR-158), mean and extinction. The mean number of offspring is
`3/4 ≤ 1`, so the process dies out with probability `1`. -/
@[kb "grinsteadsnell2006" "Example 10.10, p. 392"]
theorem exampleOffspring_extinction :
    IsOffspring exampleOffspring ∧
    HasSum (fun k : ℕ => (k : ℝ) * exampleOffspring k) (3 / 4) ∧
    extinctionProb exampleOffspring = 1 := by
  refine ⟨exampleOffspring_isOffspring, exampleOffspring_mean, ?_⟩
  refine extinction_prob_eq_one exampleOffspring_isOffspring (by simp [exampleOffspring]; norm_num)
    exampleOffspring_mean.summable ?_
  rw [exampleOffspring_mean.tsum_eq]; norm_num

/-! ## Example 4.23 (PR-159) -/

section Beta

/-- On `(0,1)` the beta density times `x^i (1-x)^j` is a constant multiple of the shifted beta density
(and both vanish outside `(0,1)`). -/
lemma betaPDFReal_mul_pow {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (i j : ℕ) (x : ℝ) :
    betaPDFReal α β x * (x ^ i * (1 - x) ^ j) =
      (beta (α + i) (β + j) / beta α β) * betaPDFReal (α + i) (β + j) x := by
  unfold betaPDFReal
  split_ifs with h
  · obtain ⟨h0, h1⟩ := h
    have e1 : x ^ (α + i - 1) = x ^ (α - 1) * x ^ i := by
      rw [show α + i - 1 = (α - 1) + i by ring, Real.rpow_add_natCast h0.ne']
    have e2 : (1 - x) ^ (β + j - 1) = (1 - x) ^ (β - 1) * (1 - x) ^ j := by
      rw [show β + j - 1 = (β - 1) + j by ring, Real.rpow_add_natCast (by linarith)]
    rw [e1, e2]
    have h1 := (beta_pos (by positivity : 0 < α + i) (by positivity : 0 < β + j)).ne'
    have h2 := (beta_pos hα hβ).ne'
    field_simp
  · simp

lemma integral_betaPDFReal {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∫ x, betaPDFReal α β x = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae]
  · have : (fun x => ENNReal.ofReal (betaPDFReal α β x)) = betaPDF α β := rfl
    rw [this, lintegral_betaPDF_eq_one hα hβ]; simp
  · refine Filter.Eventually.of_forall fun x => ?_
    unfold betaPDFReal; split_ifs with h
    · have := betaPDFReal_pos h.1 h.2 hα hβ
      unfold betaPDFReal at this; rw [ite_eq_left h] at this; exact this.le
    · exact le_rfl
  · exact (measurable_betaPDFReal α β).aestronglyMeasurable

/-- Grinstead–Snell Example 4.23 (PR-159). With a beta`(α,β)` prior density for the success
probability `x` and `i` successes and `j` failures in `n = i + j` trials (likelihood
`C(n,i) x^i (1-x)^j`), the posterior density `f(x,i)/m(i)` is the beta`(α+i, β+j)` density:
the denominator is `∫ f(y,i) dy`, the marginal `m(i)`. -/
@[kb "grinsteadsnell2006" "Example 4.23, p. 176"]
theorem beta_posterior {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (i j : ℕ) (x : ℝ) :
    ((i + j).choose i * (x ^ i * (1 - x) ^ j) * betaPDFReal α β x) /
        ∫ y, ((i + j).choose i * (y ^ i * (1 - y) ^ j) * betaPDFReal α β y)
      = betaPDFReal (α + i) (β + j) x := by
  have hαi : 0 < α + i := by positivity
  have hβj : 0 < β + j := by positivity
  have hc : (0 : ℝ) < (i + j).choose i := by exact_mod_cast Nat.choose_pos (by omega)
  have hK : 0 < beta (α + i) (β + j) / beta α β :=
    div_pos (beta_pos hαi hβj) (beta_pos hα hβ)
  have key : ∀ y, ((i + j).choose i : ℝ) * (y ^ i * (1 - y) ^ j) * betaPDFReal α β y =
      (((i + j).choose i : ℝ) * (beta (α + i) (β + j) / beta α β)) *
        betaPDFReal (α + i) (β + j) y := by
    intro y
    have := betaPDFReal_mul_pow hα hβ i j y
    calc _ = ((i + j).choose i : ℝ) * (betaPDFReal α β y * (y ^ i * (1 - y) ^ j)) := by ring
      _ = _ := by rw [this]; ring
  simp_rw [key]
  rw [integral_const_mul, integral_betaPDFReal hαi hβj]
  have : (((i + j).choose i : ℝ) * (beta (α + i) (β + j) / beta α β)) ≠ 0 := by positivity
  have h1 := (beta_pos hαi hβj).ne'
  have h2 := (beta_pos hα hβ).ne'
  field_simp

end Beta

end UndergradKB.Probability
