import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import UndergradKB.Common.Attr

/-!
# Continuous distributions (Grinstead–Snell, chapters 2, 4, 5, 6, 9)

Moments of the exponential and uniform laws, memorylessness of the exponential law, the Cauchy law has
no mean, standardized random variables, affine images of the standard normal, and the cdf of a law with
density.
-/

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal

namespace UndergradKB.Probability

section Exponential

variable {r : ℝ}

lemma exponentialPDF_toReal (hr : 0 < r) (x : ℝ) :
    (exponentialPDF r x).toReal = (Ici (0 : ℝ)).indicator (fun x => r * exp (-(r * x))) x := by
  rw [exponentialPDF_eq, ENNReal.toReal_ofReal]
  · by_cases hx : 0 ≤ x <;> simp [hx]
  · by_cases hx : 0 ≤ x <;> simp [hx]; positivity

lemma measurable_exponentialPDF' (r : ℝ) : Measurable (exponentialPDF r) :=
  ENNReal.measurable_ofReal.comp (measurable_exponentialPDFReal r)

lemma integral_expMeasure_eq (hr : 0 < r) (g : ℝ → ℝ) :
    ∫ x, g x ∂(expMeasure r) = ∫ x in Ioi 0, r * exp (-(r * x)) * g x := by
  unfold expMeasure gammaMeasure
  have h1 : gammaPDF 1 r = exponentialPDF r := rfl
  rw [h1, integral_withDensity_eq_integral_toReal_smul (measurable_exponentialPDF' r)
    (ae_of_all _ (fun x => by rw [exponentialPDF_eq]; exact ENNReal.ofReal_lt_top))]
  have : (fun x => (exponentialPDF r x).toReal • g x)
      = (Ici (0 : ℝ)).indicator (fun x => r * exp (-(r * x)) * g x) := by
    ext x
    rw [exponentialPDF_toReal hr]
    by_cases hx : 0 ≤ x <;> simp [hx]
  rw [this, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]

lemma integrable_expMeasure_iff (hr : 0 < r) (g : ℝ → ℝ) :
    Integrable g (expMeasure r) ↔ IntegrableOn (fun x => r * exp (-(r * x)) * g x) (Ioi 0) := by
  unfold expMeasure gammaMeasure
  have h1 : gammaPDF 1 r = exponentialPDF r := rfl
  rw [h1, integrable_withDensity_iff_integrable_smul' (measurable_exponentialPDF' r)
    (ae_of_all _ (fun x => by rw [exponentialPDF_eq]; exact ENNReal.ofReal_lt_top))]
  have : (fun x => (exponentialPDF r x).toReal • g x)
      = (Ici (0 : ℝ)).indicator (fun x => r * exp (-(r * x)) * g x) := by
    ext x
    rw [exponentialPDF_toReal hr]
    by_cases hx : 0 ≤ x <;> simp [hx]
  rw [this, integrable_indicator_iff measurableSet_Ici, IntegrableOn,
    Measure.restrict_congr_set Ioi_ae_eq_Ici.symm]
  rfl

lemma integrableOn_pow_exp (hr : 0 < r) (k : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ k * exp (-(r * x))) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (k : ℝ)) (b := r)
    (by have : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith) one_pos hr
  refine this.congr_fun (fun x hx => ?_) measurableSet_Ioi
  simp [rpow_natCast, neg_mul]

lemma integral_pow_exp (hr : 0 < r) (k : ℕ) :
    ∫ x in Ioi (0 : ℝ), x ^ k * exp (-(r * x)) = k.factorial / r ^ (k + 1) := by
  have h := integral_rpow_mul_exp_neg_mul_Ioi (a := (k : ℝ) + 1) (r := r) (by positivity) hr
  have e : ∀ x : ℝ, x ^ ((k : ℝ) + 1 - 1) = x ^ k := fun x => by
    rw [add_sub_cancel_right, rpow_natCast]
  simp_rw [e] at h
  rw [h, Real.Gamma_nat_eq_factorial, one_div]
  rw [show (k:ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by push_cast; ring, rpow_natCast, inv_pow]
  field_simp

lemma integral_expMeasure_pow (hr : 0 < r) (k : ℕ) :
    ∫ x, x ^ k ∂(expMeasure r) = k.factorial / r ^ k := by
  rw [integral_expMeasure_eq hr]
  have : ∀ x : ℝ, r * exp (-(r * x)) * x ^ k = r * (x ^ k * exp (-(r * x))) := fun x => by ring
  simp_rw [this]
  rw [integral_const_mul, integral_pow_exp hr]
  field_simp
  ring

lemma integrable_expMeasure_pow (hr : 0 < r) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (expMeasure r) := by
  rw [integrable_expMeasure_iff hr]
  have : ∀ x : ℝ, r * exp (-(r * x)) * x ^ k = r * (x ^ k * exp (-(r * x))) := fun x => by ring
  simp_rw [this]
  exact (integrableOn_pow_exp hr k).const_mul r

/-- Grinstead–Snell Example 6.26 (PR-081). An exponential law with rate `r > 0` has mean `1/r`. -/
@[kb "grinsteadsnell2006" "Example 6.26, p. 281"]
theorem integral_expMeasure (hr : 0 < r) : ∫ x, x ∂(expMeasure r) = 1 / r := by
  simpa using integral_expMeasure_pow hr 1

/-- Grinstead–Snell Example 6.26 (PR-081). An exponential law with rate `r > 0` has variance `1/r^2`. -/
@[kb "grinsteadsnell2006" "Example 6.26, p. 281"]
theorem variance_expMeasure (hr : 0 < r) : variance id (expMeasure r) = 1 / r ^ 2 := by
  have := isProbabilityMeasure_expMeasure hr
  have hL : MemLp id 2 (expMeasure r) := by
    rw [memLp_two_iff_integrable_sq (by fun_prop)]
    exact integrable_expMeasure_pow hr 2
  rw [variance_eq_sub hL]
  have h2 := integral_expMeasure_pow hr 2
  have h1 := integral_expMeasure hr
  simp only [Pi.pow_apply, id] at *
  rw [h2, h1]
  simp [Nat.factorial]
  field_simp
  ring

end Exponential

section Memoryless

variable {r : ℝ}

/-- Tail of the exponential law: `P(T > x) = exp(-r x)` for `x ≥ 0`. -/
lemma expMeasure_Ioi (hr : 0 < r) {x : ℝ} (hx : 0 ≤ x) :
    expMeasure r (Ioi x) = ENNReal.ofReal (exp (-(r * x))) := by
  have := isProbabilityMeasure_expMeasure hr
  have hc : expMeasure r (Iic x) = ENNReal.ofReal (1 - exp (-(r * x))) := by
    have h := cdf_expMeasure_eq hr x
    rw [cdf_eq_real, measureReal_def] at h
    simp only [hx, ↓reduceIte] at h
    rw [← h, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hle : exp (-(r * x)) ≤ 1 := by
    rw [exp_le_one_iff]; nlinarith
  rw [← compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, hc,
    ENNReal.ofReal_sub _ (exp_pos _).le, ENNReal.ofReal_one,
    ENNReal.sub_sub_cancel ENNReal.one_ne_top (by simpa using ENNReal.ofReal_le_ofReal hle)]

/-- Grinstead–Snell Example 4.20 (PR-018). The exponential waiting time is memoryless:
`P(T > r + s | T > r) = P(T > s)` for the exponential law of rate `lam > 0`. -/
@[kb "grinsteadsnell2006" "Example 4.20, p. 171"]
theorem expMeasure_memoryless {lam : ℝ} (hlam : 0 < lam) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (expMeasure lam)[Ioi (r + s) | Ioi r] = expMeasure lam (Ioi s) := by
  rw [cond_apply measurableSet_Ioi, expMeasure_Ioi hlam hr, expMeasure_Ioi hlam hs]
  have : Ioi r ∩ Ioi (r + s) = Ioi (r + s) := inter_eq_right.2 (Ioi_subset_Ioi (by linarith))
  rw [this, expMeasure_Ioi hlam (by linarith), ← ENNReal.ofReal_inv_of_pos (exp_pos _),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [mul_add, neg_add, exp_add]
  have := exp_pos (-(lam * r))
  rw [← exp_neg]
  field_simp
  rw [← exp_add]
  simp

end Memoryless

section Uniform

lemma volume_Icc_zero_one : (volume : Measure ℝ) (Icc (0 : ℝ) 1) = 1 := by simp

instance : IsProbabilityMeasure ((volume : Measure ℝ).restrict (Icc (0 : ℝ) 1)) :=
  ⟨by simp⟩

lemma cond_Icc_zero_one : (volume : Measure ℝ)[|Icc (0 : ℝ) 1] = volume.restrict (Icc 0 1) := by
  simp [ProbabilityTheory.cond]

/-- Grinstead–Snell Example 6.20 (PR-080). The uniform law on `[0,1]` has mean `1/2`. -/
@[kb "grinsteadsnell2006" "Example 6.20, p. 277"]
theorem integral_uniform_Icc : ∫ x, x ∂((volume : Measure ℝ).restrict (Icc (0 : ℝ) 1)) = 1 / 2 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  simp [integral_id]

/-- Grinstead–Snell Example 6.25 (PR-080). The uniform law on `[0,1]` has variance `1/12`. -/
@[kb "grinsteadsnell2006" "Example 6.25, p. 280"]
theorem variance_uniform_Icc :
    variance id ((volume : Measure ℝ).restrict (Icc (0 : ℝ) 1)) = 1 / 12 := by
  rw [variance_eq_integral aemeasurable_id]
  have h := integral_uniform_Icc
  simp only [id] at h ⊢
  rw [h, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  rw [intervalIntegral.integral_comp_sub_right (fun x : ℝ => x ^ 2)]
  simp [integral_pow]
  norm_num

/-- Grinstead–Snell Examples 6.20 and 6.25 (PR-080), random-variable form: a random variable uniform on
`[0,1]` has mean `1/2`. -/
@[kb "grinsteadsnell2006" "Example 6.20, p. 277"]
theorem integral_of_isUniform_Icc {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    (hX : pdf.IsUniform X (Icc (0 : ℝ) 1) P) : ∫ ω, X ω ∂P = 1 / 2 := by
  have hm : P.map X = volume.restrict (Icc 0 1) := by rw [hX.map_eq, cond_Icc_zero_one]
  have := integral_map (μ := P) hX.aemeasurable (f := id) aestronglyMeasurable_id
  rw [hm] at this
  simp only [id] at this
  rw [← this]
  exact integral_uniform_Icc

/-- Grinstead–Snell Examples 6.20 and 6.25 (PR-080), random-variable form: a random variable uniform on
`[0,1]` has variance `1/12`. -/
@[kb "grinsteadsnell2006" "Example 6.25, p. 280"]
theorem variance_of_isUniform_Icc {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    (hX : pdf.IsUniform X (Icc (0 : ℝ) 1) P) : variance X P = 1 / 12 := by
  have hm : P.map X = volume.restrict (Icc 0 1) := by rw [hX.map_eq, cond_Icc_zero_one]
  rw [← variance_id_map hX.aemeasurable, hm]
  exact variance_uniform_Icc

end Uniform

section Cauchy

/-- Grinstead–Snell Example 6.28 (PR-083). The standard Cauchy law has no expected value:
`id` is not integrable, i.e. `∫ |x| / (π (1 + x^2))` diverges. -/
@[kb "grinsteadsnell2006" "Example 6.28, p. 282"]
theorem not_integrable_cauchyMeasure : ¬ Integrable id (cauchyMeasure 0 1) := by
  intro h
  rw [cauchyMeasure_of_scale_ne_zero 0 one_ne_zero] at h
  have hm : Measurable (cauchyPDF 0 1) := measurable_cauchyPDF 0 1
  rw [integrable_withDensity_iff_integrable_smul' hm
    (ae_of_all _ (fun x => by rw [cauchyPDF_def]; exact ENNReal.ofReal_lt_top))] at h
  have h1 : IntegrableOn (fun x : ℝ => (cauchyPDF 0 1 x).toReal * x) (Ioi 1) := h.integrableOn
  have h2 : IntegrableOn (fun x : ℝ => x ^ (-1 : ℝ)) (Ioi 1) := by
    refine Integrable.mono' (h1.const_mul (2 * π)) ?_ ?_
    · exact (measurable_id.pow_const _).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ (fun x hx => ?_))
      have hx1 : (1 : ℝ) < x := hx
      have hx0 : 0 < x := by linarith
      rw [cauchyPDF_def, ENNReal.toReal_ofReal (cauchyPDF_pos 0 one_ne_zero x).le, cauchyPDFReal_def]
      rw [Real.rpow_neg_one, norm_inv, Real.norm_eq_abs, abs_of_pos hx0]
      have hpi := Real.pi_pos
      simp only [NNReal.coe_one, sub_zero, one_pow, mul_one]
      have e : 2 * π * (π⁻¹ * (x ^ 2 + 1)⁻¹ * x) = 2 * x / (x ^ 2 + 1) := by
        field_simp
      rw [e, inv_eq_one_div, div_le_div_iff₀ hx0 (by positivity)]
      nlinarith
  rw [integrableOn_Ioi_rpow_iff zero_lt_one] at h2
  norm_num at h2

end Cauchy

section Standardized

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}

/-- Grinstead–Snell §6.2, standardized random variable (PR-077). If `X` has finite variance `σ²`
with `σ > 0` and mean `μ`, then `X* = (X - μ) / σ` has mean `0`. -/
@[kb "grinsteadsnell2006" "§6.2 standardized random variable, p. 272"]
theorem integral_standardize {μ σ : ℝ} (hX : MemLp X 2 P) (hμ : ∫ ω, X ω ∂P = μ) :
    ∫ ω, (X ω - μ) / σ ∂P = 0 := by
  rw [integral_div, integral_sub (hX.integrable one_le_two) (integrable_const _), hμ]
  simp

/-- Grinstead–Snell §6.2, standardized random variable (PR-077). If `X` has finite variance `σ²`
with `σ > 0`, then `X* = (X - μ) / σ` has variance `1`. -/
@[kb "grinsteadsnell2006" "§6.2 standardized random variable, p. 272"]
theorem variance_standardize {μ σ : ℝ} (hX : MemLp X 2 P) (hσ : 0 < σ)
    (hv : variance X P = σ ^ 2) :
    variance (fun ω => (X ω - μ) / σ) P = 1 := by
  have : (fun ω => (X ω - μ) / σ) = fun ω => σ⁻¹ * (X ω - μ) := by
    ext ω; rw [div_eq_inv_mul]
  rw [this, variance_const_mul, variance_sub_const hX.aestronglyMeasurable, hv]
  field_simp

/-- Grinstead–Snell Definition 9.1 (PR-096). If `S` has mean `n p` and variance `n p q` with `n p q > 0`,
then `(S - n p) / sqrt (n p q)` has mean `0`. -/
@[kb "grinsteadsnell2006" "Definition 9.1, p. 334"]
theorem integral_standardize_sum {n p q : ℝ} {S : Ω → ℝ} (hS : MemLp S 2 P)
    (hm : ∫ ω, S ω ∂P = n * p) :
    ∫ ω, (S ω - n * p) / sqrt (n * p * q) ∂P = 0 :=
  integral_standardize hS hm

/-- Grinstead–Snell Definition 9.1 (PR-096). If `S` has mean `n p` and variance `n p q` with `n p q > 0`,
then `(S - n p) / sqrt (n p q)` has variance `1`. -/
@[kb "grinsteadsnell2006" "Definition 9.1, p. 334"]
theorem variance_standardize_sum {n p q : ℝ} {S : Ω → ℝ} (hS : MemLp S 2 P)
    (hpos : 0 < n * p * q) (hv : variance S P = n * p * q) :
    variance (fun ω => (S ω - n * p) / sqrt (n * p * q)) P = 1 :=
  variance_standardize hS (sqrt_pos.2 hpos) (by rw [sq_sqrt hpos.le, hv])

end Standardized

section Normal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → ℝ}

/-- Grinstead–Snell §5.2 (PR-058). If `Z` is standard normal then `σ Z + μ` is normal with
parameters `μ` and `σ²`. -/
@[kb "grinsteadsnell2006" "§5.2 standardized normal, p. 221"]
theorem hasLaw_gaussian_affine (hZ : HasLaw Z (gaussianReal 0 1) P) (μ : ℝ) (σ : ℝ≥0) :
    HasLaw (fun ω => σ * Z ω + μ) (gaussianReal μ (σ ^ 2)) P := by
  have h := gaussianReal_add_const (gaussianReal_const_mul hZ (σ : ℝ)) μ
  convert h using 2
  · simp
  · ext; simp

/-- Grinstead–Snell §5.2 (PR-058). If `X` is normal with parameters `μ` and `σ²` (`σ ≠ 0`) then the
standardized version `(X - μ) / σ` is standard normal. -/
@[kb "grinsteadsnell2006" "§5.2 standardized version, p. 222"]
theorem hasLaw_gaussian_standardize {X : Ω → ℝ} {μ : ℝ} {σ : ℝ≥0} (hσ : σ ≠ 0)
    (hX : HasLaw X (gaussianReal μ (σ ^ 2)) P) :
    HasLaw (fun ω => (X ω - μ) / σ) (gaussianReal 0 1) P := by
  have h := gaussianReal_div_const (gaussianReal_sub_const hX μ) (σ : ℝ)
  convert h using 2
  · simp
  · have : (σ : ℝ) ≠ 0 := by exact_mod_cast hσ
    ext; simp [this]

end Normal

section Density

/-- Grinstead–Snell Theorem 2.1 (PR-013). If a probability law on `ℝ` has density `f`, its cdf at `x`
is the integral of `f` over `(-∞, x]`. -/
@[kb "grinsteadsnell2006" "Theorem 2.1, p. 69"]
theorem cdf_withDensity_eq_integral {f : ℝ → ℝ} (hf : Integrable f) (hnn : ∀ x, 0 ≤ f x)
    [IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (f x)))] (x : ℝ) :
    cdf (volume.withDensity (fun x => ENNReal.ofReal (f x))) x = ∫ t in Iic x, f t := by
  rw [cdf_eq_real, measureReal_def, withDensity_apply _ measurableSet_Iic,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hnn) hf.aestronglyMeasurable.restrict]

/-- Grinstead–Snell Theorem 2.1 (PR-013). At a point `x` where the density `f` is continuous, the cdf
has derivative `f x`. -/
@[kb "grinsteadsnell2006" "Theorem 2.1, p. 69"]
theorem hasDerivAt_cdf_withDensity {f : ℝ → ℝ} (hf : Integrable f) (hnn : ∀ x, 0 ≤ f x)
    [IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (f x)))] {x : ℝ}
    (hx : ContinuousAt f x) :
    HasDerivAt (cdf (volume.withDensity (fun x => ENNReal.ofReal (f x)))) (f x) x := by
  have hint : ∀ a b : ℝ, IntervalIntegrable f volume a b := fun a b => hf.intervalIntegrable
  have key : cdf (volume.withDensity (fun x => ENNReal.ofReal (f x))) =
      fun y => (∫ t in Iic 0, f t) + ∫ t in (0:ℝ)..y, f t := by
    ext y
    rw [cdf_withDensity_eq_integral hf hnn, ← intervalIntegral.integral_Iic_sub_Iic
      hf.integrableOn hf.integrableOn]
    ring
  rw [key]
  exact (intervalIntegral.integral_hasDerivAt_right (hint 0 x)
    (hf.aestronglyMeasurable.stronglyMeasurableAtFilter) hx).const_add _

end Density

end UndergradKB.Probability
