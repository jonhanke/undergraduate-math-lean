import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic
import UndergradKB.Common.Attr
import UndergradKB.Statistics.ChiSquared
import UndergradKB.Statistics.NormalSample
import UndergradKB.Statistics.Inference

/-!
# The Welch (Satterthwaite) two-sample t statistic (OpenStax *Introductory Statistics 2e* §10.1)

With two independent samples of sizes `n₁, n₂` and unknown standard deviations, the book uses
`t = ((x̄₁ - x̄₂) - (μ₁ - μ₂)) / √(s₁²/n₁ + s₂²/n₂)` and says it is *approximately* Student `t` with the
Welch degrees of freedom `welchDF`. The approximation is not an exact theorem; this file proves the facts
that justify it:

* `welchDF` is the bridging definition of the degrees-of-freedom formula;
* `welch_mean_variance`: for independent normal samples, `V = s₁²/n₁ + s₂²/n₂` has mean
  `σ₁²/n₁ + σ₂²/n₂` and variance `2(σ₁²/n₁)²/(n₁ - 1) + 2(σ₂²/n₂)²/(n₂ - 1)`;
* `welch_moment_matching`: `welchDF σ₁² σ₂² n₁ n₂` is the only `ν > 0` for which a multiple of a `χ²_ν`
  variable with the mean of `V` also has the variance of `V` (Satterthwaite's idea);
* `welchDF_bounds`: `min(n₁, n₂) - 1 ≤ welchDF ≤ n₁ + n₂ - 2`;
* `hasLaw_welchStatistic_knownSD`: with the standard deviations known, the statistic is exactly `N(0, 1)`.
-/

namespace UndergradKB.Statistics

open MeasureTheory ProbabilityTheory Real Set

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-! ### The degrees of freedom -/

/-- The Welch-Satterthwaite degrees of freedom, with `v₁, v₂` standing for the two sample variances
`s₁², s₂²`:
`(v₁/n₁ + v₂/n₂)² / ((v₁/n₁)²/(n₁ - 1) + (v₂/n₂)²/(n₂ - 1))`. -/
noncomputable def welchDF (v₁ v₂ : ℝ) (n₁ n₂ : ℕ) : ℝ :=
  (v₁ / n₁ + v₂ / n₂) ^ 2 /
    ((v₁ / n₁) ^ 2 / ((n₁ : ℝ) - 1) + (v₂ / n₂) ^ 2 / ((n₂ : ℝ) - 1))

/-! ### Bounds -/

section Bounds

private lemma welchDF_aux {a b p q : ℝ} (ha : 0 < a) (hb : 0 < b) (hp : 0 < p) (hq : 0 < q) :
    0 < a ^ 2 / p + b ^ 2 / q := by positivity

/-- `welchDF ≤ n₁ + n₂ - 2` (Cauchy-Schwarz). -/
private lemma welchDF_le {v₁ v₂ : ℝ} {n₁ n₂ : ℕ} (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂)
    (h₁ : 0 < v₁) (h₂ : 0 < v₂) :
    welchDF v₁ v₂ n₁ n₂ ≤ (n₁ : ℝ) + n₂ - 2 := by
  have e1 : (2 : ℝ) ≤ n₁ := by exact_mod_cast hn₁
  have e2 : (2 : ℝ) ≤ n₂ := by exact_mod_cast hn₂
  have hp : 0 < (n₁ : ℝ) - 1 := by linarith
  have hq : 0 < (n₂ : ℝ) - 1 := by linarith
  have ha : 0 < v₁ / n₁ := div_pos h₁ (by linarith)
  have hb : 0 < v₂ / n₂ := div_pos h₂ (by linarith)
  unfold welchDF
  generalize v₁ / n₁ = a at *
  generalize v₂ / n₂ = b at *
  generalize hpd : (n₁ : ℝ) - 1 = p at *
  generalize hqd : (n₂ : ℝ) - 1 = q at *
  have hsum : (n₁ : ℝ) + n₂ - 2 = p + q := by linarith
  rw [hsum, div_le_iff₀ (welchDF_aux ha hb hp hq)]
  have key : (p + q) * (a ^ 2 / p + b ^ 2 / q) - (a + b) ^ 2 = (a * q - b * p) ^ 2 / (p * q) := by
    field_simp
    ring
  have : 0 ≤ (a * q - b * p) ^ 2 / (p * q) := by positivity
  linarith

/-- `min(n₁, n₂) - 1 ≤ welchDF`. -/
private lemma le_welchDF {v₁ v₂ : ℝ} {n₁ n₂ : ℕ} (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂)
    (h₁ : 0 < v₁) (h₂ : 0 < v₂) :
    ((min n₁ n₂ : ℕ) : ℝ) - 1 ≤ welchDF v₁ v₂ n₁ n₂ := by
  have e1 : (2 : ℝ) ≤ n₁ := by exact_mod_cast hn₁
  have e2 : (2 : ℝ) ≤ n₂ := by exact_mod_cast hn₂
  have hp : 0 < (n₁ : ℝ) - 1 := by linarith
  have hq : 0 < (n₂ : ℝ) - 1 := by linarith
  have ha : 0 < v₁ / n₁ := div_pos h₁ (by linarith)
  have hb : 0 < v₂ / n₂ := div_pos h₂ (by linarith)
  have hm : ((min n₁ n₂ : ℕ) : ℝ) - 1 = min ((n₁ : ℝ) - 1) ((n₂ : ℝ) - 1) := by
    rw [Nat.cast_min]
    rcases le_total (n₁ : ℝ) n₂ with h | h
    · rw [min_eq_left h, min_eq_left (by linarith)]
    · rw [min_eq_right h, min_eq_right (by linarith)]
  rw [hm]
  unfold welchDF
  generalize v₁ / n₁ = a at *
  generalize v₂ / n₂ = b at *
  generalize (n₁ : ℝ) - 1 = p at *
  generalize (n₂ : ℝ) - 1 = q at *
  set m := min p q with hmdef
  have hm0 : 0 < m := lt_min hp hq
  have hmp : m ≤ p := min_le_left _ _
  have hmq : m ≤ q := min_le_right _ _
  rw [le_div_iff₀ (welchDF_aux ha hb hp hq)]
  have t1 : a ^ 2 / p ≤ a ^ 2 / m := div_le_div_of_nonneg_left (by positivity) hm0 hmp
  have t2 : b ^ 2 / q ≤ b ^ 2 / m := div_le_div_of_nonneg_left (by positivity) hm0 hmq
  have t3 : m * (a ^ 2 / m + b ^ 2 / m) = a ^ 2 + b ^ 2 := by field_simp
  have t4 : m * (a ^ 2 / p + b ^ 2 / q) ≤ m * (a ^ 2 / m + b ^ 2 / m) :=
    mul_le_mul_of_nonneg_left (add_le_add t1 t2) hm0.le
  nlinarith [mul_pos ha hb]

/-- **Bounds on the Welch degrees of freedom** (ST-090). For positive variances and sample sizes at least `2`,
`min(n₁, n₂) - 1 ≤ df ≤ n₁ + n₂ - 2`: the Welch test sits between the pooled-variance test (the upper bound,
`n₁ + n₂ - 2`) and the conservative rule that uses the smaller sample (the lower bound). -/
@[kb "openstaxintrostats2e" "§10.1, p. 523"]
theorem welchDF_bounds {v₁ v₂ : ℝ} {n₁ n₂ : ℕ} (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂)
    (h₁ : 0 < v₁) (h₂ : 0 < v₂) :
    ((min n₁ n₂ : ℕ) : ℝ) - 1 ≤ welchDF v₁ v₂ n₁ n₂ ∧
      welchDF v₁ v₂ n₁ n₂ ≤ (n₁ : ℝ) + n₂ - 2 :=
  ⟨le_welchDF hn₁ hn₂ h₁ h₂, welchDF_le hn₁ hn₂ h₁ h₂⟩

end Bounds

/-! ### Moments of the sample variance -/

section Moments

private lemma memLp_two_id_chiSquared {k : ℝ} (hk : 0 < k) : MemLp id 2 (chiSquared k) := by
  have := isProbabilityMeasure_chiSquared' hk
  have h2 := integral_pow_gammaMeasure (a := k / 2) (r := 1 / 2) (by positivity) (by norm_num) 2
  exact (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2 h2.1

/-- For a normal sample of size `n ≥ 2`, `s²/n` is square integrable with mean `σ²/n` and variance
`2(σ²/n)²/(n - 1)`. (From `(n - 1) s²/σ² ~ χ²_{n-1}`.) -/
lemma sampleVariance_div_moments {n : ℕ} [IsProbabilityMeasure P] {X : Fin n → Ω → ℝ} {μ σ : ℝ}
    (hn : 2 ≤ n) (hσ : 0 < σ) (hX : IsNormalSample X μ σ P) :
    MemLp (fun ω ↦ sampleVariance (fun i ↦ X i ω) / n) 2 P ∧
      ∫ ω, sampleVariance (fun i ↦ X i ω) / n ∂P = σ ^ 2 / n ∧
      variance (fun ω ↦ sampleVariance (fun i ↦ X i ω) / n) P = 2 * (σ ^ 2 / n) ^ 2 / ((n : ℝ) - 1) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hk : 0 < (n : ℝ) - 1 := by linarith
  have hU := hasLaw_sampleVariance_chiSquared hn hσ hX
  have e : (fun ω ↦ sampleVariance (fun i ↦ X i ω) / n) =
      fun ω ↦ (σ ^ 2 / (n * ((n : ℝ) - 1))) *
        (((n : ℝ) - 1) * sampleVariance (fun i ↦ X i ω) / σ ^ 2) := by
    funext ω
    field_simp
  rw [e]
  refine ⟨(hU.memLp (memLp_two_id_chiSquared hk)).const_mul _, ?_, ?_⟩
  · rw [integral_const_mul]
    have h1 : ∫ ω, ((n : ℝ) - 1) * sampleVariance (fun i ↦ X i ω) / σ ^ 2 ∂P = (n : ℝ) - 1 :=
      hU.integral_eq.trans (integral_id_chiSquared hk)
    rw [h1]
    field_simp
  · rw [variance_const_mul, hU.variance_eq, variance_id_chiSquared hk]
    field_simp

end Moments

/-! ### Moment matching -/

section Matching

variable [IsProbabilityMeasure P] {n₁ n₂ : ℕ} {X : Fin n₁ → Ω → ℝ} {Y : Fin n₂ → Ω → ℝ}
  {μ₁ μ₂ σ₁ σ₂ : ℝ}

/-- **Mean and variance of the Welch variance estimate** (ST-090). For independent normal samples of sizes
`n₁, n₂ ≥ 2`, the estimate `V = s₁²/n₁ + s₂²/n₂` of the variance of `x̄₁ - x̄₂` is unbiased,
`E V = σ₁²/n₁ + σ₂²/n₂`, and has variance
`Var V = 2(σ₁²/n₁)²/(n₁ - 1) + 2(σ₂²/n₂)²/(n₂ - 1)`. -/
@[kb "openstaxintrostats2e" "§10.1, p. 523"]
theorem welch_mean_variance (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂) (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂)
    (hX : IsNormalSample X μ₁ σ₁ P) (hY : IsNormalSample Y μ₂ σ₂ P)
    (hind : IndepFun (fun ω i ↦ X i ω) (fun ω j ↦ Y j ω) P) :
    ∫ ω, (sampleVariance (fun i ↦ X i ω) / n₁ + sampleVariance (fun j ↦ Y j ω) / n₂) ∂P =
        σ₁ ^ 2 / n₁ + σ₂ ^ 2 / n₂ ∧
      variance (fun ω ↦ sampleVariance (fun i ↦ X i ω) / n₁ + sampleVariance (fun j ↦ Y j ω) / n₂) P =
        2 * (σ₁ ^ 2 / n₁) ^ 2 / ((n₁ : ℝ) - 1) + 2 * (σ₂ ^ 2 / n₂) ^ 2 / ((n₂ : ℝ) - 1) := by
  obtain ⟨m₁, i₁, v₁⟩ := sampleVariance_div_moments hn₁ hσ₁ hX
  obtain ⟨m₂, i₂, v₂⟩ := sampleVariance_div_moments hn₂ hσ₂ hY
  have hind' : IndepFun (fun ω ↦ sampleVariance (fun i ↦ X i ω) / n₁)
      (fun ω ↦ sampleVariance (fun j ↦ Y j ω) / n₂) P :=
    hind.comp (measurable_sampleVariance'.div_const _) (measurable_sampleVariance'.div_const _)
  refine ⟨?_, ?_⟩
  · rw [integral_add (m₁.integrable one_le_two) (m₂.integrable one_le_two), i₁, i₂]
  · rw [hind'.variance_fun_add m₁ m₂, v₁, v₂]

/-- Pure algebra behind Satterthwaite's formula: for `ν > 0`, `2 (a + b)² / ν = 2a²/p + 2b²/q` holds
exactly when `ν = (a + b)² / (a²/p + b²/q)`. -/
private lemma match_iff {a b p q ν : ℝ} (ha : 0 < a) (hb : 0 < b) (hp : 0 < p) (hq : 0 < q)
    (hν : 0 < ν) :
    2 * (a + b) ^ 2 / ν = 2 * a ^ 2 / p + 2 * b ^ 2 / q ↔
      ν = (a + b) ^ 2 / (a ^ 2 / p + b ^ 2 / q) := by
  have hd : 0 < a ^ 2 / p + b ^ 2 / q := welchDF_aux ha hb hp hq
  have e : 2 * a ^ 2 / p + 2 * b ^ 2 / q = 2 * (a ^ 2 / p + b ^ 2 / q) := by ring
  rw [e, div_eq_iff hν.ne', eq_div_iff hd.ne']
  constructor <;> intro h <;> linarith

/-- **Satterthwaite moment matching** (ST-090). The variable `c · χ²_ν` has mean `c ν` and variance `2 c² ν`;
choosing `c ν = E V` makes the variance `2 (E V)² / ν`. This equals `Var V` exactly when `ν` is the Welch
degrees of freedom `welchDF σ₁² σ₂² n₁ n₂`, so that value is the unique choice of `ν > 0` for which a scaled
chi-square variable has the same mean and variance as `V`. This is the exact content behind the book's
"approximately Student t with Welch degrees of freedom". -/
@[kb "openstaxintrostats2e" "§10.1, p. 523"]
theorem welch_moment_matching (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂) (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂)
    (hX : IsNormalSample X μ₁ σ₁ P) (hY : IsNormalSample Y μ₂ σ₂ P)
    (hind : IndepFun (fun ω i ↦ X i ω) (fun ω j ↦ Y j ω) P) {ν : ℝ} (hν : 0 < ν) :
    2 * (∫ ω, (sampleVariance (fun i ↦ X i ω) / n₁ + sampleVariance (fun j ↦ Y j ω) / n₂) ∂P) ^ 2 / ν =
        variance (fun ω ↦ sampleVariance (fun i ↦ X i ω) / n₁ + sampleVariance (fun j ↦ Y j ω) / n₂) P ↔
      ν = welchDF (σ₁ ^ 2) (σ₂ ^ 2) n₁ n₂ := by
  obtain ⟨hm, hv⟩ := welch_mean_variance hn₁ hn₂ hσ₁ hσ₂ hX hY hind
  have e1 : (2 : ℝ) ≤ n₁ := by exact_mod_cast hn₁
  have e2 : (2 : ℝ) ≤ n₂ := by exact_mod_cast hn₂
  rw [hm, hv, welchDF]
  exact match_iff (div_pos (by positivity) (by linarith)) (div_pos (by positivity) (by linarith))
    (by linarith) (by linarith) hν

/-- Existence half of `welch_moment_matching`: the Welch degrees of freedom `welchDF σ₁² σ₂² n₁ n₂` is
positive. -/
theorem welchDF_pos {v₁ v₂ : ℝ} {n₁ n₂ : ℕ} (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂)
    (h₁ : 0 < v₁) (h₂ : 0 < v₂) : 0 < welchDF v₁ v₂ n₁ n₂ := by
  have := (welchDF_bounds hn₁ hn₂ h₁ h₂).1
  have : 2 ≤ min n₁ n₂ := le_min hn₁ hn₂
  have : (2 : ℝ) ≤ ((min n₁ n₂ : ℕ) : ℝ) := by exact_mod_cast this
  linarith

/-! ### Known standard deviations -/

/-- **The Welch statistic with known standard deviations is exactly standard normal** (ST-090). If the sample
standard deviations in `t = ((x̄₁ - x̄₂) - (μ₁ - μ₂)) / √(s₁²/n₁ + s₂²/n₂)` are replaced by the true `σ₁, σ₂`,
the statistic is exactly `N(0, 1)`; the Student-t approximation with `welchDF` accounts for the extra
randomness of `s₁², s₂²` (no exact `t` law holds in general). -/
@[kb "openstaxintrostats2e" "§10.1, p. 523"]
theorem hasLaw_welchStatistic_knownSD (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂) (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂)
    (hX : IsNormalSample X μ₁ σ₁ P) (hY : IsNormalSample Y μ₂ σ₂ P)
    (hind : IndepFun (fun ω i ↦ X i ω) (fun ω j ↦ Y j ω) P) :
    HasLaw (fun ω ↦ ((mean (fun i ↦ X i ω) - mean (fun j ↦ Y j ω)) - (μ₁ - μ₂)) /
      √(σ₁ ^ 2 / n₁ + σ₂ ^ 2 / n₂)) (gaussianReal 0 1) P :=
  hasLaw_twoSampleZ hn₁ hn₂ hσ₁ hσ₂ hX hY hind

end Matching

end UndergradKB.Statistics
