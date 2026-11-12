import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Inference

/-!
# p-values and power of the z test (OpenStax *Introductory Statistics 2e*, §9.2 and §9.4)

`Φ` below is the standard normal distribution function `cdf (gaussianReal 0 1)`.
-/

namespace UndergradKB.Statistics

open MeasureTheory ProbabilityTheory Real Set

/-! ### Facts about the standard normal distribution function -/

/-- The standard normal distribution function is strictly increasing (the law has full support). -/
lemma cdf_gaussianReal_strictMono : StrictMono (cdf (gaussianReal 0 1)) := by
  intro a b hab
  have h1 := (cdf (gaussianReal 0 1)).measure_Ioc a b
  rw [measure_cdf] at h1
  by_contra hle
  push_neg at hle
  have h0 : ENNReal.ofReal (cdf (gaussianReal 0 1) b - cdf (gaussianReal 0 1) a) = 0 :=
    ENNReal.ofReal_eq_zero.2 (by linarith)
  rw [h0] at h1
  have := gaussianReal_absolutelyContinuous' 0 one_ne_zero h1
  rw [Real.volume_Ioc] at this
  simp at this
  linarith

lemma gaussianReal_real_Ioi (t : ℝ) :
    (gaussianReal 0 1).real (Ioi t) = 1 - cdf (gaussianReal 0 1) t := by
  rw [cdf_eq_real, ← compl_Iic, measureReal_compl measurableSet_Iic]
  simp

lemma gaussianReal_Ioi (t : ℝ) :
    gaussianReal 0 1 (Ioi t) = ENNReal.ofReal (1 - cdf (gaussianReal 0 1) t) := by
  rw [← gaussianReal_real_Ioi, ofReal_measureReal]

lemma gaussianReal_real_Iio_neg (c : ℝ) :
    (gaussianReal 0 1).real (Iio (-c)) = (gaussianReal 0 1).real (Ioi c) := by
  have h := congrArg (fun m : Measure ℝ ↦ m (Iio (-c)))
    (gaussianReal_map_neg (μ := 0) (v := 1))
  simp only [neg_zero] at h
  rw [Measure.map_apply measurable_neg measurableSet_Iio] at h
  have e : (fun x : ℝ ↦ -x) ⁻¹' Iio (-c) = Ioi c := by
    ext x; simp
  rw [e] at h
  unfold Measure.real
  rw [h]

/-- The central mass: `Φ`-form of `P(-c ≤ Z ≤ c) = 1 - 2 (1 - Φ(c))` for `c ≥ 0`. -/
lemma gaussianReal_real_Icc (c : ℝ) (hc : 0 ≤ c) :
    (gaussianReal 0 1).real (Icc (-c) c) = 1 - 2 * (1 - cdf (gaussianReal 0 1) c) := by
  have h1 := measureReal_compl (μ := gaussianReal 0 1) (measurableSet_Icc (a := -c) (b := c))
  have e : (Icc (-c) c)ᶜ = Iio (-c) ∪ Ioi c := by
    ext x
    simp only [mem_compl_iff, mem_Icc, mem_union, mem_Iio, mem_Ioi]
    constructor
    · intro h
      by_cases h' : -c ≤ x
      · exact Or.inr (lt_of_not_ge fun hx ↦ h ⟨h', hx⟩)
      · exact Or.inl (lt_of_not_ge h')
    · rintro (h | h) ⟨h1, h2⟩ <;> linarith
  have hd : Disjoint (Iio (-c)) (Ioi c) :=
    Set.disjoint_left.2 (fun x h1 h2 ↦ by simp at h1 h2; linarith)
  rw [e, measureReal_union hd measurableSet_Ioi, gaussianReal_real_Iio_neg,
    gaussianReal_real_Ioi] at h1
  have hu : (gaussianReal 0 1).real univ = 1 := by simp
  rw [hu] at h1
  linarith

/-- If the central mass of `[-c, c]` is `1 - α` with `0 < α < 1`, then `c ≥ 0` and
`2 (1 - Φ(c)) = α`. -/
lemma critical_value_eq {c α : ℝ} (h0 : 0 < α) (h1 : α < 1)
    (hz : gaussianReal 0 1 (Icc (-c) c) = ENNReal.ofReal (1 - α)) :
    0 ≤ c ∧ 2 * (1 - cdf (gaussianReal 0 1) c) = α := by
  have hc : 0 ≤ c := by
    by_contra hneg
    push_neg at hneg
    have : Icc (-c) c = ∅ := Set.Icc_eq_empty (by linarith)
    rw [this, measure_empty] at hz
    have := ENNReal.ofReal_pos.2 (by linarith : 0 < 1 - α)
    rw [← hz] at this
    exact lt_irrefl _ this
  refine ⟨hc, ?_⟩
  have h2 := gaussianReal_real_Icc c hc
  have h3 : (gaussianReal 0 1).real (Icc (-c) c) = 1 - α := by
    unfold Measure.real
    rw [hz, ENNReal.toReal_ofReal (by linarith)]
  linarith

/-! ### The p-value -/

/-- The two-sided p-value of an observed standard normal test statistic `z`:
`2 (1 - Φ(|z|))`, the probability under `H₀` of a statistic at least as extreme as `z`. -/
noncomputable def zPValue (z : ℝ) : ℝ := 2 * (1 - cdf (gaussianReal 0 1) |z|)

/-- The p-value is twice the upper tail probability of the standard normal law beyond `|z|`. -/
theorem zPValue_eq_two_mul_tail (z : ℝ) :
    zPValue z = 2 * (gaussianReal 0 1).real (Ioi |z|) := by
  unfold zPValue
  rw [gaussianReal_real_Ioi]

/-- OpenStax Introductory Statistics 2e §9.4 (ST-087). For the two-sided z test, rejecting when
the p-value is below `α` is the same as rejecting when `|z|` exceeds the critical value `c`
(where the standard normal mass of `[-c, c]` is `1 - α`). -/
@[kb "openstaxintrostats2e" "§9.4, p. 478"]
theorem zPValue_lt_iff {c α : ℝ} (h0 : 0 < α) (h1 : α < 1)
    (hz : gaussianReal 0 1 (Icc (-c) c) = ENNReal.ofReal (1 - α)) (z : ℝ) :
    zPValue z < α ↔ c < |z| := by
  obtain ⟨hc, he⟩ := critical_value_eq h0 h1 hz
  unfold zPValue
  rw [← he]
  constructor
  · intro h
    have : cdf (gaussianReal 0 1) c < cdf (gaussianReal 0 1) |z| := by linarith
    exact cdf_gaussianReal_strictMono.lt_iff_lt.1 this
  · intro h
    have := cdf_gaussianReal_strictMono h
    linarith

/-- OpenStax Introductory Statistics 2e §9.4 (ST-087). Under `H₀` the p-value is uniform in the
sense that `P(p-value < α) = α`: for a normal sample with known `σ` and true mean `μ₀`. -/
@[kb "openstaxintrostats2e" "§9.4, p. 478"]
theorem zPValue_prob_lt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} {X : Fin n → Ω → ℝ} {μ₀ σ : ℝ} (hn : 1 ≤ n) (hσ : 0 < σ)
    (hX : IsNormalSample X μ₀ σ P) {c α : ℝ} (h0 : 0 < α) (h1 : α < 1)
    (hz : gaussianReal 0 1 (Icc (-c) c) = ENNReal.ofReal (1 - α)) :
    P {ω | zPValue ((mean (fun i ↦ X i ω) - μ₀) / (σ / √(n : ℝ))) < α} = ENNReal.ofReal α := by
  rw [← zTest_typeI_error hn hσ hX h1.le hz]
  congr 1
  ext ω
  exact zPValue_lt_iff h0 h1 hz _

/-! ### Power of the right-tailed z test -/

/-- The power at `μ₁` of the right-tailed z test (critical value `c`, known `σ`, sample size `n`)
of `H₀ : μ = μ₀`: `1 - Φ(c - (μ₁ - μ₀) √n / σ)`. -/
noncomputable def zTestPower (μ₀ μ₁ σ : ℝ) (n : ℕ) (c : ℝ) : ℝ :=
  1 - cdf (gaussianReal 0 1) (c - (μ₁ - μ₀) * √(n : ℝ) / σ)

/-- The probability of a Type II error, `β = 1 - power`. -/
noncomputable def zTestTypeII (μ₀ μ₁ σ : ℝ) (n : ℕ) (c : ℝ) : ℝ :=
  cdf (gaussianReal 0 1) (c - (μ₁ - μ₀) * √(n : ℝ) / σ)

/-- OpenStax Introductory Statistics 2e §9.2 (ST-083). If the true mean is `μ₁`, the right-tailed
z test (reject when `z > c`) rejects with probability `1 - Φ(c - (μ₁ - μ₀) √n / σ)`. -/
@[kb "openstaxintrostats2e" "§9.2, p. 475"]
theorem zTest_power_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} {X : Fin n → Ω → ℝ} {μ₁ σ : ℝ} (hn : 1 ≤ n) (hσ : 0 < σ)
    (hX : IsNormalSample X μ₁ σ P) (μ₀ c : ℝ) :
    P {ω | c < (mean (fun i ↦ X i ω) - μ₀) / (σ / √(n : ℝ))} =
      ENNReal.ofReal (zTestPower μ₀ μ₁ σ n c) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < √(n : ℝ) := sqrt_pos.2 hn'
  have h := prob_mem_of_hasLaw (hasLaw_zStatistic hn hσ hX)
    (measurableSet_Ioi (a := c - (μ₁ - μ₀) * √(n : ℝ) / σ))
  rw [gaussianReal_Ioi] at h
  unfold zTestPower
  rw [← h]
  congr 1
  ext ω
  have e : (mean (fun i ↦ X i ω) - μ₀) / (σ / √(n : ℝ)) =
      (mean (fun i ↦ X i ω) - μ₁) / (σ / √(n : ℝ)) + (μ₁ - μ₀) * √(n : ℝ) / σ := by
    field_simp
    ring
  simp only [mem_setOf_eq, mem_Ioi]
  rw [e]
  constructor <;> intro h <;> linarith

/-- OpenStax Introductory Statistics 2e §9.2 (ST-083). A larger critical value (smaller `α`)
gives smaller power (strictly) and larger `β`. -/
@[kb "openstaxintrostats2e" "§9.2, p. 475"]
theorem zTestPower_strictAnti_critical (μ₀ μ₁ σ : ℝ) (n : ℕ) {c c' : ℝ} (h : c < c') :
    zTestPower μ₀ μ₁ σ n c' < zTestPower μ₀ μ₁ σ n c ∧
      zTestTypeII μ₀ μ₁ σ n c < zTestTypeII μ₀ μ₁ σ n c' := by
  have := cdf_gaussianReal_strictMono
    (show c - (μ₁ - μ₀) * √(n : ℝ) / σ < c' - (μ₁ - μ₀) * √(n : ℝ) / σ by linarith)
  unfold zTestPower zTestTypeII
  exact ⟨by linarith, this⟩

/-- OpenStax Introductory Statistics 2e §9.2 (ST-083). In terms of the level: if the right-tailed
critical values `c`, `c'` have `1 - Φ(c) = α` and `1 - Φ(c') = α'` with `α' < α`, the test of level
`α'` has strictly smaller power (larger `β`). -/
@[kb "openstaxintrostats2e" "§9.2, p. 475"]
theorem zTestPower_lt_of_smaller_level (μ₀ μ₁ σ : ℝ) (n : ℕ) {c c' α α' : ℝ}
    (hc : 1 - cdf (gaussianReal 0 1) c = α) (hc' : 1 - cdf (gaussianReal 0 1) c' = α')
    (h : α' < α) :
    zTestPower μ₀ μ₁ σ n c' < zTestPower μ₀ μ₁ σ n c := by
  have : c < c' := cdf_gaussianReal_strictMono.lt_iff_lt.1 (by linarith)
  exact (zTestPower_strictAnti_critical μ₀ μ₁ σ n this).1

/-- OpenStax Introductory Statistics 2e §9.2 (ST-083). For `μ₁ > μ₀`, the power increases
(strictly) with the sample size, and `β` decreases. -/
@[kb "openstaxintrostats2e" "§9.2, p. 475"]
theorem zTestPower_strictMono_sampleSize {μ₀ μ₁ σ : ℝ} (hμ : μ₀ < μ₁) (hσ : 0 < σ) (c : ℝ)
    {n n' : ℕ} (h : n < n') :
    zTestPower μ₀ μ₁ σ n c < zTestPower μ₀ μ₁ σ n' c ∧
      zTestTypeII μ₀ μ₁ σ n' c < zTestTypeII μ₀ μ₁ σ n c := by
  have hs : √(n : ℝ) < √(n' : ℝ) := Real.sqrt_lt_sqrt (Nat.cast_nonneg n) (Nat.cast_lt.2 h)
  have h1 : (μ₁ - μ₀) * √(n : ℝ) < (μ₁ - μ₀) * √(n' : ℝ) :=
    mul_lt_mul_of_pos_left hs (by linarith)
  have h2 : (μ₁ - μ₀) * √(n : ℝ) / σ < (μ₁ - μ₀) * √(n' : ℝ) / σ :=
    div_lt_div_of_pos_right h1 hσ
  have := cdf_gaussianReal_strictMono
    (show c - (μ₁ - μ₀) * √(n' : ℝ) / σ < c - (μ₁ - μ₀) * √(n : ℝ) / σ by linarith)
  unfold zTestPower zTestTypeII
  exact ⟨by linarith, this⟩

end UndergradKB.Statistics
