import Mathlib.Probability.StrongLaw
import UndergradKB.Common.Attr
import UndergradKB.Probability.ContinuousDistributions
import UndergradKB.Probability.LittleLaw
import UndergradKB.Probability.QueueUniformization

/-! # Probability: Little's law almost surely, arrival side (Grinstead–Snell Example 6.29)

Wave 8, a recorded loose end (3).  Wave 7 proved Little's law `L = λW` along one sample path
(`little_law_sample_path`), given that the arrival rate `λ = lim n / a_n` and the mean time in the system
`W = lim (w_0 + ⋯ + w_{n-1})/n` exist.  For the queue of the book the interarrival times are independent
exponential variables with rate `λ`; here the strong law of large numbers (Mathlib `strong_law_ae_real`) shows
that almost surely the arrival times `a_n = X_0 + ⋯ + X_n` are nondecreasing, nonnegative and satisfy
`n / a_n → λ`.  So Little's law holds almost surely for any sojourn times whose mean converges
(`little_law_ae`); that this mean converges almost surely for the queue (a renewal-reward argument over busy
cycles) is not proved here. -/

open MeasureTheory ProbabilityTheory Set Filter Topology Finset

namespace UndergradKB.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Almost surely the arrival times `a_n = X_0 + ⋯ + X_n` of independent exponential(`λ`) interarrival times
are nondecreasing and nonnegative, and the arrival rate `n / a_n` tends to `λ` (strong law of large numbers). -/
theorem arrival_times_ae {X : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (X i)) (hind : iIndepFun X P) {lam : ℝ}
    (hl : 0 < lam) (hX : ∀ i, P.map (X i) = expMeasure lam) :
    ∀ᵐ ω ∂P, Monotone (fun n => ∑ i ∈ range (n + 1), X i ω) ∧ 0 ≤ X 0 ω ∧
      Tendsto (fun n : ℕ => (n : ℝ) / ∑ i ∈ range (n + 1), X i ω) atTop (𝓝 lam) := by
  -- the gaps are almost surely nonnegative
  have hnn : ∀ᵐ ω ∂P, ∀ i, 0 ≤ X i ω := by
    rw [ae_all_iff]
    intro i
    have h0 : P {ω | X i ω < 0} = 0 := by
      have e : {ω | X i ω < 0} = X i ⁻¹' Iio 0 := rfl
      rw [e, ← Measure.map_apply (hmeas i) measurableSet_Iio, hX i, expMeasure, gammaMeasure,
        withDensity_apply _ measurableSet_Iio]
      exact lintegral_gammaPDF_of_nonpos le_rfl
    refine measure_mono_null (fun ω hω => ?_) h0
    simpa [not_le] using hω
  -- strong law: `S_m / m → 1/λ`
  have hint : Integrable (X 0) P := by
    have h := integrable_expMeasure_pow hl 1
    simp only [pow_one] at h
    rw [← hX 0] at h
    exact (integrable_map_measure aestronglyMeasurable_id (hmeas 0).aemeasurable).1 h
  have hmean : P[X 0] = 1 / lam := by
    rw [← integral_expMeasure hl, ← hX 0]
    exact (integral_map (hmeas 0).aemeasurable aestronglyMeasurable_id).symm
  have hslln := strong_law_ae_real X hint (fun i j hij => hind.indepFun hij)
    (fun i => ⟨(hmeas i).aemeasurable, (hmeas 0).aemeasurable, by rw [hX i, hX 0]⟩)
  rw [hmean] at hslln
  filter_upwards [hnn, hslln] with ω hω hs
  refine ⟨monotone_nat_of_le_succ fun n => ?_, hω 0, ?_⟩
  · rw [sum_range_succ _ (n + 1)]
    linarith [hω (n + 1)]
  · have h1 : Tendsto (fun n : ℕ => (∑ i ∈ range (n + 1), X i ω) / ((n + 1 : ℕ) : ℝ)) atTop
        (𝓝 (1 / lam)) := hs.comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun n : ℕ => (n : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
      have := tendsto_natCast_div_add_atTop (1 : ℝ)
      refine this.congr fun n => ?_
      push_cast; rfl
    have h3 := h2.div h1 (by positivity)
    rw [one_div_one_div] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    simp only [Pi.div_apply]
    rw [div_div_div_cancel_right₀ hn']

/-- Grinstead–Snell Example 6.29 (PR-209), Little's law almost surely.  Let the interarrival times
`X_0, X_1, …` be independent exponential variables with rate `λ > 0` (customer `n` arrives at
`a_n = X_0 + ⋯ + X_n`), and let customer `i` stay `w_i ≥ 0` in the system.  On almost every sample path where
the mean time in the system `(w_0 + ⋯ + w_{n-1})/n` converges to `W`, the mean number in the system
`(1/T) ∫_0^T N(t) dt` converges to `λ W`. -/
@[kb "grinsteadsnell2006" "Example 6.29, p. 283"]
theorem little_law_ae {X : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (X i)) (hind : iIndepFun X P) {lam : ℝ}
    (hl : 0 < lam) (hX : ∀ i, P.map (X i) = expMeasure lam) (w : ℕ → Ω → ℝ) (hw : ∀ i ω, 0 ≤ w i ω)
    (W : Ω → ℝ) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (∑ i ∈ range n, w i ω) / n) atTop (𝓝 (W ω)) →
      Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T,
        queueNumber (fun n => ∑ i ∈ range (n + 1), X i ω) (fun i => w i ω) t) / T) atTop
        (𝓝 (lam * W ω)) := by
  filter_upwards [arrival_times_ae hmeas hind hl hX] with ω ⟨hmono, h0, hrate⟩ hW
  exact little_law_sample_path _ _ hmono (by simpa using h0) (fun i => hw i ω) hl hrate hW

end UndergradKB.Probability
