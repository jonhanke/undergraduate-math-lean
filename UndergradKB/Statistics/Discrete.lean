import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Vandermonde
import UndergradKB.Common.Attr

/-!
# Discrete distributions: binomial, geometric, Poisson, hypergeometric

OpenStax *Introductory Statistics 2e*, chapter 4. Mathlib supplies the laws
`ProbabilityTheory.binomial`, `geometricMeasure` (counting failures before the first success) and
`poissonMeasure`; here we prove their variances (and the geometric and Poisson means), and add the
missing hypergeometric mass function with its normalisation and mean.
-/

namespace UndergradKB.Statistics

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal unitInterval

section Binomial

private lemma choose_mul_aux (n k : ℕ) :
    ((n + 2).choose (k + 2) : ℝ) * (k + 2) * (k + 1) = (n + 2) * (n + 1) * (n.choose k : ℝ) := by
  have h1 := Nat.add_one_mul_choose_eq (n + 1) (k + 1)
  have h2 := Nat.add_one_mul_choose_eq n k
  have h1' : ((n : ℝ) + 2) * ((n + 1).choose (k + 1) : ℝ) =
      ((n + 2).choose (k + 2) : ℝ) * ((k : ℝ) + 2) := by
    have := congrArg (Nat.cast : ℕ → ℝ) h1
    push_cast at this
    linarith
  have h2' : ((n : ℝ) + 1) * (n.choose k : ℝ) = ((n + 1).choose (k + 1) : ℝ) * ((k : ℝ) + 1) := by
    exact_mod_cast h2
  linear_combination (-((k : ℝ) + 1)) * h1' - ((n : ℝ) + 2) * h2'

private lemma binom_second_factorial (x y : ℝ) (hxy : x + y = 1) (n : ℕ) :
    ∑ k ∈ range (n + 1), ((n.choose k : ℝ) * x ^ k * y ^ (n - k)) * ((k : ℝ) * ((k : ℝ) - 1)) =
      n * (n - 1) * x ^ 2 := by
  rcases n with _ | _ | n
  · simp
  · simp [sum_range_succ]
  · rw [sum_range_succ', sum_range_succ']
    have key : ∀ k : ℕ, ((n + 2).choose (k + 1 + 1) : ℝ) * x ^ (k + 1 + 1) * y ^ (n + 2 - (k + 1 + 1)) *
        (((k + 1 + 1 : ℕ) : ℝ) * (((k + 1 + 1 : ℕ) : ℝ) - 1)) =
        ((n : ℝ) + 2) * ((n : ℝ) + 1) * x ^ 2 * ((n.choose k : ℝ) * x ^ k * y ^ (n - k)) := by
      intro k
      have h := choose_mul_aux n k
      rw [show n + 2 - (k + 1 + 1) = n - k by omega]
      push_cast
      linear_combination (x ^ (k + 1 + 1) * y ^ (n - k)) * h
    have hs : ∑ k ∈ range (n + 1), (n.choose k : ℝ) * x ^ k * y ^ (n - k) = 1 := by
      calc _ = ∑ k ∈ range (n + 1), x ^ k * y ^ (n - k) * (n.choose k : ℝ) :=
            sum_congr rfl fun k _ => by ring
        _ = (x + y) ^ n := (add_pow x y n).symm
        _ = 1 := by rw [hxy, one_pow]
    simp only [key, ← mul_sum, hs]
    push_cast
    ring

/-- **Variance of the binomial law (ST-040).** For `X ~ B(n, p)` the variance is `n p (1 - p)`
(so the standard deviation is `√(n p q)`); the law is Mathlib's `Bin(ℝ, n, p)`, whose mean is
`n p`. -/
@[kb "openstaxintrostats2e" "§4.3, p. 248"]
theorem variance_binomial (n : ℕ) (p : I) :
    variance (id : ℝ → ℝ) Bin(ℝ, n, p) = n * p * (1 - p) := by
  have hint : ∀ f : ℝ → ℝ, ∫ x, f x ∂Bin(ℝ, n, p) =
      ∑ k ∈ range (n + 1), ((n.choose k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k)) * f k := by
    intro f
    rw [integral_map_cast_binomial, ← n.range_succ_eq_Iic]
    simp only [smul_eq_mul]
  have hp1 : ∫ x, x ∂Bin(ℝ, n, p) = p * n :=
    integral_of_hasLaw_binomial (X := id) (P := Bin(ℝ, n, p)) HasLaw.id
  have hL : MemLp id 2 Bin(ℝ, n, p) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2 (integrable_map_cast_binomial _)
  rw [variance_eq_sub hL]
  have h2 : ∫ x, (id ^ 2 : ℝ → ℝ) x ∂Bin(ℝ, n, p) = n * (n - 1) * (p : ℝ) ^ 2 + p * n := by
    simp only [Pi.pow_apply, id]
    rw [hint (fun x => x ^ 2)]
    have hf := binom_second_factorial (p : ℝ) (1 - p) (by ring) n
    have hm : ∑ k ∈ range (n + 1),
        ((n.choose k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k)) * (k : ℝ) = p * n :=
      (hint (fun x => x)).symm.trans hp1
    calc _ = ∑ k ∈ range (n + 1),
          (((n.choose k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k)) * ((k : ℝ) * ((k : ℝ) - 1)) +
          ((n.choose k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k)) * (k : ℝ)) :=
          sum_congr rfl fun k _ => by ring
      _ = _ := by rw [sum_add_distrib, hf, hm]
  have h1 : ∫ x, (id : ℝ → ℝ) x ∂Bin(ℝ, n, p) = p * n := hp1
  rw [h2, h1]
  ring

/-- Random-variable form of ST-040: if `X` has the binomial law `B(n, p)` then
`Var X = n p (1 - p)`. -/
@[kb "openstaxintrostats2e" "§4.3, p. 248"]
theorem variance_of_hasLaw_binomial {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : Ω → ℝ} {n : ℕ} {p : I} (hX : HasLaw X Bin(ℝ, n, p) P) :
    variance X P = n * p * (1 - p) := by
  rw [hX.variance_eq, variance_binomial]

end Binomial

section Poisson

open Real

private lemma poisson_hasSum0 (r : ℝ) :
    HasSum (fun n : ℕ => r ^ n / (n.factorial : ℝ)) (exp r) := by
  simpa [← exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp r

private lemma poisson_hasSum1 (r : ℝ) :
    HasSum (fun n : ℕ => (n : ℝ) * (r ^ n / (n.factorial : ℝ))) (r * exp r) := by
  have h := (poisson_hasSum0 r).mul_left r
  refine (hasSum_nat_add_iff' 1).1 ?_
  simp only [sum_range_one, Nat.cast_zero, zero_mul, sub_zero]
  convert h using 1
  funext n
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

private lemma poisson_hasSum2 (r : ℝ) :
    HasSum (fun n : ℕ => (n : ℝ) * ((n : ℝ) - 1) * (r ^ n / (n.factorial : ℝ)))
      (r ^ 2 * exp r) := by
  have h := (poisson_hasSum0 r).mul_left (r ^ 2)
  refine (hasSum_nat_add_iff' 2).1 ?_
  simp only [sum_range_succ, sum_range_zero, Nat.cast_zero, Nat.cast_one, zero_mul, sub_zero,
    zero_add, mul_zero, add_zero]
  convert h using 1
  · funext n
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    field_simp
    ring
  · norm_num

private lemma poisson_weighted (r : ℝ≥0) {f : ℕ → ℝ} {a : ℝ}
    (h : HasSum (fun n : ℕ => f n * ((r : ℝ) ^ n / (n.factorial : ℝ))) (a * exp r)) :
    HasSum (fun n : ℕ => (exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ)) • f n) a := by
  convert h.mul_left (exp (-(r : ℝ))) using 1
  · funext n
    simp only [smul_eq_mul]
    ring
  · rw [← mul_assoc, mul_comm (exp (-(r : ℝ))) a, mul_assoc, ← exp_add]
    simp

private lemma poisson_sum1 (r : ℝ≥0) :
    HasSum (fun n : ℕ => (exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ)) • (n : ℝ)) r :=
  poisson_weighted r (poisson_hasSum1 r)

private lemma poisson_sum2 (r : ℝ≥0) :
    HasSum (fun n : ℕ => (exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ)) • ((n : ℝ) ^ 2))
      ((r : ℝ) ^ 2 + r) := by
  have h := (poisson_weighted r (poisson_hasSum2 r)).add (poisson_sum1 r)
  convert h using 1
  funext n
  simp only [smul_eq_mul]
  ring

/-- **Mean of the Poisson law (ST-045).** If `X ~ P(μ)` then `E[X] = μ`. -/
@[kb "openstaxintrostats2e" "§4.6, p. 261"]
theorem integral_poissonMeasure_id (r : ℝ≥0) : ∫ n, (n : ℝ) ∂poissonMeasure r = r := by
  rw [integral_poissonMeasure, (poisson_sum1 r).tsum_eq]

/-- **Variance of the Poisson law (ST-045).** If `X ~ P(μ)` then `Var X = μ`
(so the standard deviation is `√μ`). -/
@[kb "openstaxintrostats2e" "§4.6, p. 261"]
theorem variance_poissonMeasure (r : ℝ≥0) :
    variance (fun n : ℕ => (n : ℝ)) (poissonMeasure r) = r := by
  have hL : MemLp (fun n : ℕ => (n : ℝ)) 2 (poissonMeasure r) := by
    refine (memLp_two_iff_integrable_sq Measurable.of_discrete.aestronglyMeasurable).2 ?_
    rw [integrable_poissonMeasure_iff]
    refine (poisson_sum2 r).summable.congr fun n => ?_
    simp only [smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (n : ℝ))]
  rw [variance_eq_sub hL]
  have h2 : ∫ n, ((fun n : ℕ => (n : ℝ)) ^ 2) n ∂poissonMeasure r = (r : ℝ) ^ 2 + r := by
    simp only [Pi.pow_apply]
    rw [integral_poissonMeasure, (poisson_sum2 r).tsum_eq]
  have h1 : ∫ n, (fun n : ℕ => (n : ℝ)) n ∂poissonMeasure r = r := integral_poissonMeasure_id r
  rw [h2, h1]
  ring

/-- Random-variable form of ST-045 (mean). -/
@[kb "openstaxintrostats2e" "§4.6, p. 261"]
theorem expectation_of_hasLaw_poisson {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : Ω → ℕ} {r : ℝ≥0} (hX : HasLaw X (poissonMeasure r) P) :
    ∫ ω, (X ω : ℝ) ∂P = (r : ℝ) := by
  have : ∫ ω, (X ω : ℝ) ∂P = ∫ n, (n : ℝ) ∂poissonMeasure r :=
    hX.integral_comp (f := fun n : ℕ => (n : ℝ)) Measurable.of_discrete.aestronglyMeasurable
  rw [this, integral_poissonMeasure_id]

/-- Random-variable form of ST-045 (variance); `X` is measurable. -/
@[kb "openstaxintrostats2e" "§4.6, p. 261"]
theorem variance_of_hasLaw_poisson {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : Ω → ℕ} {r : ℝ≥0} (hX : HasLaw X (poissonMeasure r) P) (hXm : Measurable X) :
    variance (fun ω => (X ω : ℝ)) P = r := by
  rw [(hX.measurePreserving hXm).variance_fun_comp (f := fun n : ℕ => (n : ℝ))
    Measurable.of_discrete.aemeasurable, variance_poissonMeasure]

end Poisson

section Geometric

open Real

variable {p : I}

private lemma geom_bounds (hp : p ≠ 0) : 0 < (p : ℝ) := by
  have : (p : ℝ) ≠ 0 := fun h => hp (Subtype.ext (by simpa using h))
  exact lt_of_le_of_ne p.2.1 this.symm

private lemma geom_q_norm (hp : p ≠ 0) : ‖(1 - (p : ℝ))‖ < 1 := by
  have h0 := geom_bounds hp
  have h1 := p.2.2
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  linarith

private lemma geom_hasSum1 (hp : p ≠ 0) :
    HasSum (fun n : ℕ => ((1 - (p : ℝ)) ^ n * p) • (n : ℝ)) ((1 - p) / p) := by
  have h0 := geom_bounds hp
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one (geom_q_norm hp)).mul_right (p : ℝ)
  convert h using 1
  · funext n
    simp only [smul_eq_mul]
    ring
  · have : (1 - (1 - (p : ℝ))) = p := by ring
    rw [this]
    field_simp

private lemma geom_hasSum2 (hp : p ≠ 0) :
    HasSum (fun n : ℕ => ((1 - (p : ℝ)) ^ n * p) • ((n : ℝ) ^ 2))
      ((1 - p) * (2 - p) / (p : ℝ) ^ 2) := by
  have h0 := geom_bounds hp
  set q : ℝ := 1 - p with hq
  have hn := geom_q_norm hp
  have hq0 : 0 ≤ q := by have := p.2.2; rw [hq]; linarith
  have hq1 : q < 1 := by rw [hq]; linarith
  have hb : Summable (fun n : ℕ => (n : ℝ) ^ 2 * q ^ n) := summable_pow_mul_geometric_of_norm_lt_one 2 hn
  set B := ∑' n : ℕ, (n : ℝ) ^ 2 * q ^ n with hB
  have ha := hasSum_coe_mul_geometric_of_norm_lt_one hn
  have hg := hasSum_geometric_of_lt_one hq0 hq1
  have hshift : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 2 * q ^ (n + 1)) B := by
    have := (hasSum_nat_add_iff' 1).2 hb.hasSum
    simpa using this
  have hsum : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 2 * q ^ (n + 1))
      (q * (B + 2 * (q / (1 - q) ^ 2) + (1 - q)⁻¹)) := by
    have := ((hb.hasSum.add (ha.mul_left 2)).add hg).mul_left q
    convert this using 1
    funext n
    push_cast
    ring
  have heq : B = q * (B + 2 * (q / (1 - q) ^ 2) + (1 - q)⁻¹) := hshift.unique hsum
  have h1q : 1 - q ≠ 0 := by linarith
  have hBv : B = q * (1 + q) / (1 - q) ^ 3 := by
    rw [eq_div_iff (pow_ne_zero 3 h1q)]
    field_simp at heq
    nlinarith [heq]
  have h := hb.hasSum.mul_right (p : ℝ)
  rw [← hB] at h
  convert h using 1
  · funext n
    simp only [smul_eq_mul]
    ring
  · have hp' : (1 - q) = p := by rw [hq]; ring
    rw [hBv, hp', hq]
    field_simp
    ring

private lemma geom_hasSum0 (hp : p ≠ 0) :
    HasSum (fun n : ℕ => ((1 - (p : ℝ)) ^ n * p) • (1 : ℝ)) 1 := by
  have h0 := geom_bounds hp
  have h := (hasSum_geometric_of_lt_one (r := 1 - (p : ℝ)) (by linarith [p.2.2])
    (by linarith)).mul_right (p : ℝ)
  convert h using 1
  · funext n
    simp
  · have : (1 - (1 - (p : ℝ))) = p := by ring
    rw [this]
    field_simp

/-- **Mean of the geometric law, failures version (ST-042).** The number `X` of failures before the
first success, with success probability `p`, has `E[X] = (1 - p)/p`. -/
@[kb "openstaxintrostats2e" "§4.4, p. 253"]
theorem integral_geometricMeasure_id (hp : p ≠ 0) :
    ∫ n, (n : ℝ) ∂geometricMeasure p = (1 - p) / p := by
  rw [integral_geometricMeasure hp]
  exact (geom_hasSum1 hp).tsum_eq

/-- **Mean of the geometric law, trials version (ST-042).** The number of trials up to and including
the first success, with success probability `p`, has mean `1/p`. -/
@[kb "openstaxintrostats2e" "§4.4, p. 253"]
theorem integral_geometricMeasure_trials (hp : p ≠ 0) :
    ∫ n, ((n : ℝ) + 1) ∂geometricMeasure p = 1 / p := by
  have h0 := geom_bounds hp
  rw [integral_geometricMeasure hp]
  have h := (geom_hasSum1 hp).add (geom_hasSum0 hp)
  convert h.tsum_eq using 1
  · congr 1
    funext n
    simp only [smul_eq_mul]
    ring
  · field_simp
    ring

/-- **Variance of the geometric law (ST-042).** The number of failures before the first success has
variance `(1 - p)/p²` (the number of trials differs by the constant `1`, so has the same variance). -/
@[kb "openstaxintrostats2e" "§4.4, p. 253"]
theorem variance_geometricMeasure (hp : p ≠ 0) :
    variance (fun n : ℕ => (n : ℝ)) (geometricMeasure p) = (1 - p) / (p : ℝ) ^ 2 := by
  have h0 := geom_bounds hp
  have hL : MemLp (fun n : ℕ => (n : ℝ)) 2 (geometricMeasure p) := by
    refine (memLp_two_iff_integrable_sq Measurable.of_discrete.aestronglyMeasurable).2 ?_
    rw [integrable_geometricMeasure_iff hp]
    refine (geom_hasSum2 hp).summable.congr fun n => ?_
    simp only [smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (n : ℝ))]
  rw [variance_eq_sub hL]
  have h2 : ∫ n, ((fun n : ℕ => (n : ℝ)) ^ 2) n ∂geometricMeasure p =
      (1 - p) * (2 - p) / (p : ℝ) ^ 2 := by
    simp only [Pi.pow_apply]
    rw [integral_geometricMeasure hp]
    exact (geom_hasSum2 hp).tsum_eq
  have h1 : ∫ n, (fun n : ℕ => (n : ℝ)) n ∂geometricMeasure p = (1 - p) / p :=
    integral_geometricMeasure_id hp
  rw [h2, h1]
  field_simp
  ring

/-- Variance of the geometric law, trials version (ST-042): `(1 - p)/p²`. -/
@[kb "openstaxintrostats2e" "§4.4, p. 253"]
theorem variance_geometricMeasure_trials (hp : p ≠ 0) :
    variance (fun n : ℕ => (n : ℝ) + 1) (geometricMeasure p) = (1 - p) / (p : ℝ) ^ 2 := by
  rw [variance_add_const Measurable.of_discrete.aestronglyMeasurable, variance_geometricMeasure hp]

end Geometric

section Hypergeometric

/-- The hypergeometric mass function `h(x) = C(A, x) C(B, n - x) / C(A + B, n)`: the chance that a
sample of `n` drawn without replacement from `A` successes and `B` failures contains exactly `x`
successes. (Mathlib has no hypergeometric law.) -/
noncomputable def hypergeometricPMF (A B n x : ℕ) : ℝ :=
  (A.choose x : ℝ) * (B.choose (n - x) : ℝ) / ((A + B).choose n : ℝ)

theorem hypergeometricPMF_nonneg (A B n x : ℕ) : 0 ≤ hypergeometricPMF A B n x := by
  unfold hypergeometricPMF
  positivity

private lemma vandermonde_real (A B n : ℕ) :
    ∑ x ∈ range (n + 1), (A.choose x : ℝ) * (B.choose (n - x) : ℝ) = ((A + B).choose n : ℝ) := by
  have hv : (A + B).choose n = ∑ x ∈ range (n + 1), A.choose x * B.choose (n - x) := by
    rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => A.choose i * B.choose j) n]
  rw [hv]
  push_cast
  rfl

/-- **The hypergeometric probabilities sum to one (ST-043).** For a sample of size `n ≤ A + B` the
masses `h(0), …, h(n)` add to `1` (Vandermonde's identity). -/
@[kb "openstaxintrostats2e" "§4.5, p. 258"]
theorem sum_hypergeometricPMF (A B n : ℕ) (h : n ≤ A + B) :
    ∑ x ∈ range (n + 1), hypergeometricPMF A B n x = 1 := by
  have hpos : (0 : ℝ) < ((A + B).choose n : ℝ) := by exact_mod_cast Nat.choose_pos h
  unfold hypergeometricPMF
  rw [← sum_div, vandermonde_real, div_self hpos.ne']

/-- **Mean of the hypergeometric law (ST-044).** Drawing `n ≤ A + B` items without replacement from
`A` successes and `B` failures, the expected number of successes is `n A / (A + B)`. -/
@[kb "openstaxintrostats2e" "§4.5, p. 258"]
theorem sum_mul_hypergeometricPMF (A B n : ℕ) (h : n ≤ A + B) :
    ∑ x ∈ range (n + 1), (x : ℝ) * hypergeometricPMF A B n x = n * A / (A + B) := by
  rcases n with _ | n
  · simp [hypergeometricPMF]
  rcases A with _ | a
  · rw [sum_eq_zero]
    · simp
    · intro x _
      rcases x with _ | x <;> simp [hypergeometricPMF]
  have e : a + 1 + B = (a + B) + 1 := by omega
  have hD : (0 : ℝ) < ((a + 1 + B).choose (n + 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos h
  have hnum : ∑ x ∈ range (n + 1 + 1), (x : ℝ) *
      ((a + 1).choose x * B.choose (n + 1 - x)) = (a + 1) * ((a + B).choose n : ℝ) := by
    rw [sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, add_zero]
    have hx : ∀ x ∈ range (n + 1), ((x + 1 : ℕ) : ℝ) *
        (((a + 1).choose (x + 1) : ℝ) * (B.choose (n + 1 - (x + 1)) : ℝ)) =
        ((a : ℝ) + 1) * ((a.choose x : ℝ) * (B.choose (n - x) : ℝ)) := by
      intro x _
      have h2 := congrArg (Nat.cast : ℕ → ℝ) (Nat.add_one_mul_choose_eq a x)
      push_cast at h2
      rw [show n + 1 - (x + 1) = n - x by omega]
      push_cast
      linear_combination (-(B.choose (n - x) : ℝ)) * h2
    rw [sum_congr rfl hx, ← mul_sum, vandermonde_real]
  have hmain := congrArg (Nat.cast : ℕ → ℝ) (Nat.add_one_mul_choose_eq (a + B) n)
  push_cast at hmain
  have hmain' : ((a : ℝ) + B + 1) * ((a + B).choose n : ℝ) =
      ((a + B + 1).choose (n + 1) : ℝ) * ((n : ℝ) + 1) := hmain
  simp only [hypergeometricPMF]
  have : ∀ x : ℕ, (x : ℝ) * (((a + 1).choose x : ℝ) * (B.choose (n + 1 - x) : ℝ) /
      ((a + 1 + B).choose (n + 1) : ℝ)) = (x : ℝ) * (((a + 1).choose x : ℝ) *
      (B.choose (n + 1 - x) : ℝ)) / ((a + 1 + B).choose (n + 1) : ℝ) := fun x => by ring
  simp only [this]
  rw [← sum_div, hnum, e]
  rw [e] at hD
  push_cast
  rw [div_eq_div_iff hD.ne' (by positivity)]
  linear_combination ((a : ℝ) + 1) * hmain'

end Hypergeometric

end UndergradKB.Statistics
