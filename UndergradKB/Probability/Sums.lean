import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Density
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Analysis.LConvolution
import Mathlib.MeasureTheory.Group.Convolution
import UndergradKB.Common.Attr

/-! # Probability: sums of independent random variables (Grinstead–Snell, Chapter 7)

Convolution of discrete and continuous distributions, the triangular and gamma densities, the
binomial family, and mean and variance of sums of independent variables. -/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace UndergradKB.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-! ## Discrete convolution (PR-087) -/

/-- Grinstead–Snell Definition 7.1, §7.1 (PR-087). For independent integer-valued variables,
`P(X+Y=j)` is the convolution sum of the two mass functions (a `tsum` over `ℤ`). -/
@[kb "grinsteadsnell2006" "Definition 7.1, p. 294"]
theorem measure_add_eq_tsum_int {X Y : Ω → ℤ} (hX : Measurable X) (hY : Measurable Y)
    (h : IndepFun X Y P) (j : ℤ) :
    P {ω | X ω + Y ω = j} = ∑' k : ℤ, P {ω | X ω = k} * P {ω | Y ω = j - k} := by
  have hset : {ω | X ω + Y ω = j} = ⋃ k : ℤ, (X ⁻¹' {k} ∩ Y ⁻¹' {j - k}) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff]
    constructor
    · intro hω
      exact ⟨X ω, rfl, by omega⟩
    · rintro ⟨k, h1, h2⟩
      omega
  rw [hset, measure_iUnion]
  · refine tsum_congr fun k => ?_
    exact h.measure_inter_preimage_eq_mul _ _ (measurableSet_singleton _)
      (measurableSet_singleton _)
  · intro a b hab
    refine Set.disjoint_left.2 fun ω hω hω' => hab ?_
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff] at hω hω'
    omega
  · intro k
    exact (hX (measurableSet_singleton _)).inter (hY (measurableSet_singleton _))

/-- Real-valued form of `measure_add_eq_tsum_int` for a probability measure. -/
@[kb "grinsteadsnell2006" "Definition 7.1, p. 294"]
theorem real_add_eq_tsum_int [IsProbabilityMeasure P] {X Y : Ω → ℤ} (hX : Measurable X)
    (hY : Measurable Y) (h : IndepFun X Y P) (j : ℤ) :
    P.real {ω | X ω + Y ω = j} = ∑' k : ℤ, P.real {ω | X ω = k} * P.real {ω | Y ω = j - k} := by
  simp only [measureReal_def]
  rw [measure_add_eq_tsum_int hX hY h j, ENNReal.tsum_toReal_eq]
  · simp [ENNReal.toReal_mul]
  · intro k
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)

/-- Finite form of the convolution formula for `ℕ`-valued variables: `P(X+Y=j)` is the sum over
the pairs `(i, j - i)` of `P(X=i) P(Y=j-i)`. -/
@[kb "grinsteadsnell2006" "Definition 7.1, p. 294"]
theorem measure_add_eq_sum_antidiagonal {X Y : Ω → ℕ} (hX : Measurable X) (hY : Measurable Y)
    (h : IndepFun X Y P) (j : ℕ) :
    P {ω | X ω + Y ω = j} =
      ∑ ij ∈ antidiagonal j, P {ω | X ω = ij.1} * P {ω | Y ω = ij.2} := by
  have hset : {ω | X ω + Y ω = j} =
      ⋃ ij ∈ antidiagonal j, (X ⁻¹' {ij.1} ∩ Y ⁻¹' {ij.2}) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, Finset.mem_antidiagonal, exists_prop]
    constructor
    · intro hω
      exact ⟨(X ω, Y ω), hω, rfl, rfl⟩
    · rintro ⟨ij, h0, h1, h2⟩
      omega
  rw [hset, measure_biUnion_finset]
  · refine Finset.sum_congr rfl fun ij _ => ?_
    exact h.measure_inter_preimage_eq_mul _ _ (measurableSet_singleton _)
      (measurableSet_singleton _)
  · intro a ha b hb hab
    refine Set.disjoint_left.2 fun ω hω hω' => hab ?_
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff] at hω hω'
    apply Prod.ext <;> omega
  · intro ij _
    exact (hX (measurableSet_singleton _)).inter (hY (measurableSet_singleton _))

/-! ## Convolution of densities (PR-088) -/

/-- Grinstead–Snell Theorem 7.1 (PR-088). If `X` and `Y` are independent with densities `f` and
`g`, then `X + Y` has density `z ↦ ∫ f (z - y) g y dy`. -/
@[kb "grinsteadsnell2006" "Theorem 7.1, p. 299"]
theorem map_add_eq_withDensity_convolution [IsProbabilityMeasure P] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y) (h : IndepFun X Y P) {f g : ℝ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (hXf : P.map X = volume.withDensity f) (hYg : P.map Y = volume.withDensity g) :
    P.map (X + Y) = volume.withDensity (fun z => ∫⁻ y, f (z - y) * g y) := by
  rw [h.map_add_eq_map_conv_map hX hY, hXf, hYg, conv_withDensity_eq_lconvolution hf hg]
  congr 1
  funext z
  rw [lconvolution_comm]
  refine lintegral_congr fun y => ?_
  rw [mul_comm]
  simp only [neg_add_eq_sub]

/-! ## Sum of two exponentials (PR-090) -/

lemma measurable_gammaPDF' (a r : ℝ) : Measurable (gammaPDF a r) :=
  (measurable_gammaPDFReal a r).ennreal_ofReal

/-- Grinstead–Snell Example 7.4 (PR-090), density identity. The convolution of two exponential
densities of rate `r` is the gamma density with shape `2`: `∫ f (z - y) f y dy = r² z e^{-r z}`
for `z ≥ 0` and `0` otherwise. -/
@[kb "grinsteadsnell2006" "Example 7.4, p. 300"]
theorem lintegral_gammaPDF_one_conv {r : ℝ} (hr : 0 < r) (z : ℝ) :
    ∫⁻ y, gammaPDF 1 r (z - y) * gammaPDF 1 r y = gammaPDF 2 r z := by
  have key : (fun y => gammaPDF 1 r (z - y) * gammaPDF 1 r y) =
      (Set.Icc 0 z).indicator (fun _ => ENNReal.ofReal (r ^ 2 * Real.exp (-(r * z)))) := by
    funext y
    by_cases hy : y ∈ Set.Icc 0 z
    · rw [Set.indicator_of_mem hy, gammaPDF_of_nonneg (sub_nonneg.2 hy.2),
        gammaPDF_of_nonneg hy.1]
      have hexp : Real.exp (-(r * (z - y))) * Real.exp (-(r * y)) = Real.exp (-(r * z)) := by
        rw [← Real.exp_add]; congr 1; ring
      simp only [Real.rpow_one, Real.Gamma_one, sub_self, Real.rpow_zero, div_one, mul_one]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [← hexp]; ring
    · rw [Set.indicator_of_notMem hy]
      by_cases h0 : 0 ≤ y
      · have : z < y := by
          by_contra h
          exact hy ⟨h0, not_lt.1 h⟩
        rw [gammaPDF_of_neg (by linarith : z - y < 0), zero_mul]
      · rw [gammaPDF_of_neg (not_le.1 h0), mul_zero]
  rw [key, lintegral_indicator measurableSet_Icc, setLIntegral_const, Real.volume_Icc]
  by_cases hz : 0 ≤ z
  · have hG : Real.Gamma 2 = 1 := by simp
    rw [gammaPDF_of_nonneg hz, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    norm_num [hG, Real.rpow_two]
    ring
  · rw [gammaPDF_of_neg (not_le.1 hz), ENNReal.ofReal_of_nonpos (show z - 0 ≤ 0 by linarith),
      mul_zero]

/-- Grinstead–Snell Example 7.4 (PR-090), law statement. The sum of two independent exponential
variables of rate `r` has the gamma law with shape `2` and rate `r`. -/
@[kb "grinsteadsnell2006" "Example 7.4, p. 300"]
theorem map_add_expMeasure [IsProbabilityMeasure P] {X Y : Ω → ℝ} (hX : Measurable X)
    (hY : Measurable Y) (h : IndepFun X Y P) {r : ℝ} (hr : 0 < r)
    (hXr : P.map X = expMeasure r) (hYr : P.map Y = expMeasure r) :
    P.map (X + Y) = gammaMeasure 2 r := by
  rw [map_add_eq_withDensity_convolution hX hY h (measurable_gammaPDF' 1 r)
    (measurable_gammaPDF' 1 r) hXr hYr]
  unfold gammaMeasure
  congr 1
  funext z
  exact lintegral_gammaPDF_one_conv hr z

/-! ## Sum of two uniform variables (PR-089) -/

/-- The density of the uniform law on `[0,1]`. -/
noncomputable def unitDensity : ℝ → ℝ≥0∞ := (Set.Icc (0 : ℝ) 1).indicator 1

/-- The triangular density on `[0,2]`: `z` on `[0,1]`, `2 - z` on `[1,2]`, and `0` elsewhere. -/
noncomputable def triangularPDF (z : ℝ) : ℝ≥0∞ :=
  if z ≤ 1 then ENNReal.ofReal z else ENNReal.ofReal (2 - z)

lemma measurable_unitDensity : Measurable unitDensity :=
  measurable_one.indicator measurableSet_Icc

/-- Grinstead–Snell Examples 2.4, 2.14, 7.3, 7.9 (PR-089), density identity. The convolution of
the indicator of `[0,1]` with itself is the triangular density. -/
@[kb "grinsteadsnell2006" "Example 7.3, p. 300"]
theorem lintegral_unitDensity_conv (z : ℝ) :
    ∫⁻ y, unitDensity (z - y) * unitDensity y = triangularPDF z := by
  have key : (fun y => unitDensity (z - y) * unitDensity y) =
      (Set.Icc (max 0 (z - 1)) (min 1 z)).indicator 1 := by
    funext y
    have hiff : y ∈ Set.Icc (max 0 (z - 1)) (min 1 z) ↔
        (z - y ∈ Set.Icc (0 : ℝ) 1 ∧ y ∈ Set.Icc (0 : ℝ) 1) := by
      simp only [Set.mem_Icc, max_le_iff, le_min_iff]
      constructor
      · rintro ⟨⟨a, b⟩, c, d⟩
        exact ⟨⟨by linarith, by linarith⟩, a, c⟩
      · rintro ⟨⟨a, b⟩, c, d⟩
        exact ⟨⟨c, by linarith⟩, d, by linarith⟩
    by_cases hc : z - y ∈ Set.Icc (0 : ℝ) 1 ∧ y ∈ Set.Icc (0 : ℝ) 1
    · rw [Set.indicator_of_mem (hiff.2 hc)]
      simp [unitDensity, Set.indicator_of_mem hc.1, Set.indicator_of_mem hc.2]
    · rw [Set.indicator_of_notMem (fun h => hc (hiff.1 h))]
      rcases not_and_or.1 hc with h | h
      · simp [unitDensity, Set.indicator_of_notMem h]
      · simp [unitDensity, Set.indicator_of_notMem h]
  rw [key, lintegral_indicator_one measurableSet_Icc, Real.volume_Icc]
  unfold triangularPDF
  split_ifs with h
  · rw [min_eq_right h, max_eq_left (by linarith)]
    simp
  · rw [min_eq_left (by linarith), max_eq_right (by linarith)]
    congr 1
    ring

lemma ofReal_indicator_one (y : ℝ) :
    ENNReal.ofReal ((Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y) = unitDensity y := by
  by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
  · simp [unitDensity, Set.indicator_of_mem hy]
  · simp [unitDensity, Set.indicator_of_notMem hy]

/-- Grinstead–Snell Examples 2.4, 2.14, 7.3, 7.9 (PR-089), as a real integral. For every `z`,
`∫ 1_{[0,1]}(z - y) 1_{[0,1]}(y) dy` is the triangular density at `z`. -/
@[kb "grinsteadsnell2006" "Example 7.3, p. 300"]
theorem integral_indicator_Icc_conv (z : ℝ) :
    ∫ y, (Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) (z - y) *
      (Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y = (triangularPDF z).toReal := by
  have hnn : ∀ w : ℝ, 0 ≤ (Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) w :=
    fun w => Set.indicator_nonneg (fun _ _ => zero_le_one) w
  have hm : Measurable ((Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ))) :=
    measurable_const.indicator measurableSet_Icc
  have hmeas : Measurable fun y : ℝ => (Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) (z - y) *
      (Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y :=
    (hm.comp (measurable_const.sub measurable_id)).mul hm
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun y => mul_nonneg (hnn (z - y)) (hnn y))
    hmeas.aestronglyMeasurable]
  congr 1
  rw [← lintegral_unitDensity_conv z]
  refine lintegral_congr fun y => ?_
  rw [ENNReal.ofReal_mul (hnn _), ofReal_indicator_one, ofReal_indicator_one]

/-- Grinstead–Snell Examples 2.4, 2.14, 7.3, 7.9 (PR-089), law statement. The sum of two
independent uniform `[0,1]` variables has the triangular density. -/
@[kb "grinsteadsnell2006" "Example 7.3, p. 300"]
theorem map_add_uniform [IsProbabilityMeasure P] {X Y : Ω → ℝ} (hX : Measurable X)
    (hY : Measurable Y) (h : IndepFun X Y P)
    (hXu : P.map X = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hYu : P.map Y = volume.restrict (Set.Icc (0 : ℝ) 1)) :
    P.map (X + Y) = volume.withDensity triangularPDF := by
  have hu : volume.withDensity unitDensity = volume.restrict (Set.Icc (0 : ℝ) 1) :=
    withDensity_indicator_one measurableSet_Icc
  rw [map_add_eq_withDensity_convolution hX hY h measurable_unitDensity measurable_unitDensity
    (hXu.trans hu.symm) (hYu.trans hu.symm)]
  congr 1
  funext z
  exact lintegral_unitDensity_conv z

/-! ## Binomial sums (PR-093) -/

/-- Grinstead–Snell Examples 10.5, 10.6 (PR-093), convolution of masses (Vandermonde). -/
@[kb "grinsteadsnell2006" "Example 10.5, p. 379"]
theorem binomial_mass_convolution (m n : ℕ) (p q : ℝ) (j : ℕ) :
    ∑ ij ∈ antidiagonal j, ((m.choose ij.1 : ℝ) * p ^ ij.1 * q ^ (m - ij.1)) *
        ((n.choose ij.2 : ℝ) * p ^ ij.2 * q ^ (n - ij.2)) =
      ((m + n).choose j : ℝ) * p ^ j * q ^ (m + n - j) := by
  rw [Nat.add_choose_eq, Nat.cast_sum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ij hij => ?_
  rw [Finset.mem_antidiagonal] at hij
  by_cases h : ij.1 ≤ m ∧ ij.2 ≤ n
  · have e1 : p ^ j = p ^ ij.1 * p ^ ij.2 := by rw [← pow_add, hij]
    have e2 : q ^ (m + n - j) = q ^ (m - ij.1) * q ^ (n - ij.2) := by
      rw [← pow_add]; congr 1; omega
    rw [e1, e2]; push_cast; ring
  · rcases not_and_or.1 h with h | h <;> simp [Nat.choose_eq_zero_of_lt (not_le.1 h)]

/-- Grinstead–Snell Examples 10.5, 10.6 (PR-093), law statement. The sum of independent
`binomial m p` and `binomial n p` variables is `binomial (m + n) p`. -/
@[kb "grinsteadsnell2006" "Example 10.5, p. 379"]
theorem hasLaw_add_binomial [IsProbabilityMeasure P] {X Y : Ω → ℕ} (hX : Measurable X)
    (hY : Measurable Y) (h : IndepFun X Y P) {m n : ℕ} {p : unitInterval}
    (hXl : HasLaw X (binomial m p) P) (hYl : HasLaw Y (binomial n p) P) :
    HasLaw (X + Y) (binomial (m + n) p) P := by
  refine ⟨(hX.add hY).aemeasurable, ?_⟩
  apply Measure.ext_of_singleton
  intro j
  have hmass : ∀ (Z : Ω → ℕ) (N : ℕ), Measurable Z → HasLaw Z (binomial N p) P → ∀ i,
      P {ω | Z ω = i} = ENNReal.ofReal ((N.choose i) * (p : ℝ) ^ i * (1 - (p : ℝ)) ^ (N - i)) := by
    intro Z N hZ hl i
    rw [← binomial_singleton, ← hl.map_eq, Measure.map_apply hZ (measurableSet_singleton i)]
    rfl
  rw [Measure.map_apply (hX.add hY) (measurableSet_singleton j)]
  have hpre : (X + Y) ⁻¹' {j} = {ω | X ω + Y ω = j} := rfl
  rw [hpre, measure_add_eq_sum_antidiagonal hX hY h j, binomial_singleton]
  simp_rw [hmass X m hX hXl, hmass Y n hY hYl]
  simp_rw [← ENNReal.ofReal_mul binomial_nonneg]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun ij _ => mul_nonneg binomial_nonneg binomial_nonneg)]
  congr 1
  exact binomial_mass_convolution m n (p : ℝ) (1 - (p : ℝ)) j

end UndergradKB.Probability
