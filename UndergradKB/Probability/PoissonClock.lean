import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import UndergradKB.Common.Attr
import UndergradKB.Probability.NormalFamilies

/-! # Probability: exponential gaps give a Poisson count (Grinstead–Snell §5.2)

Wave 8, a recorded loose end (1).  The book (§5.2, after the exponential density) lets `X_1, X_2, …` be
independent exponential variables with parameter `λ` (the times between emissions of a radioactive source),
`S_n = X_1 + ⋯ + X_n`, and `Y` the number of emissions in a time interval of length `t`, so that
`P(Y = n) = P(S_n ≤ t < S_{n+1}) = P(S_n ≤ t) - P(S_{n+1} ≤ t)`.  It states (proof deferred to Chapter 7) that
`S_n` has the gamma density `λ (λx)^{n-1} e^{-λx}/(n-1)!`, that its distribution function is
`G_n(x) = 1 - e^{-λx}(1 + λx + ⋯ + (λx)^{n-1}/(n-1)!)` for `x > 0` ("easy by induction"), and concludes
`P(Y = n) = e^{-λt} (λt)^n / n!`, the Poisson law with parameter `λt`.

* `hasLaw_sum_exponential_gamma`: `S_n` has the gamma law with shape `n` and rate `λ` (`n ≥ 1`);
* `measureReal_sum_exponential_le`: `P(S_n ≤ t) = 1 - ∑_{k<n} e^{-λt}(λt)^k/k!` for `t ≥ 0` (all `n`);
* `exponential_gaps_poisson_count`: `P(S_n ≤ t < S_{n+1}) = e^{-λt}(λt)^n/n!`.

Indices start at `0` here: `S n = X 0 + ⋯ + X (n-1)`. -/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace UndergradKB.Probability

section

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Grinstead–Snell §5.2 (PR-215), gamma density of `S_n` (proved in the book's Chapter 7).  If `X_0, X_1, …` are
independent exponential variables with rate `λ > 0`, then for `n ≥ 1` the sum `S_n = X_0 + ⋯ + X_{n-1}` has the
gamma law with shape `n` and rate `λ` (density `λ (λx)^{n-1} e^{-λx}/(n-1)!` for `x > 0`). -/
@[kb "grinsteadsnell2006" "§5.2 gamma density, p. 213"]
theorem hasLaw_sum_exponential_gamma {X : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) {r : ℝ} (hr : 0 < r) (hX : ∀ i, P.map (X i) = expMeasure r) :
    ∀ n, 1 ≤ n → P.map (fun ω => ∑ i ∈ Finset.range n, X i ω) = gammaMeasure n r := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simpa [expMeasure] using hX 0
  | succ n hn ih =>
    have hsum_eq : (∑ i ∈ Finset.range n, X i) = fun ω => ∑ i ∈ Finset.range n, X i ω := by
      funext ω; simp [Finset.sum_apply]
    have hind2 : IndepFun (∑ i ∈ Finset.range n, X i) (X n) P :=
      hind.indepFun_finsetSum_of_notMem hmeas (by simp)
    rw [hsum_eq] at hind2
    have hms : Measurable fun ω => ∑ i ∈ Finset.range n, X i ω :=
      Finset.measurable_sum _ fun i _ => hmeas i
    have h := map_add_gammaMeasure hms (hmeas n) hind2 (by exact_mod_cast hn) one_pos hr ih
      (by simpa [expMeasure] using hX n)
    have hfun : (fun ω => ∑ i ∈ Finset.range (n + 1), X i ω) =
        (fun ω => ∑ i ∈ Finset.range n, X i ω) + X n := by
      funext ω; simp [Finset.sum_range_succ]
    rw [hfun, h]
    push_cast
    rfl

end

/-- The partial sums `∑_{k<n} e^{-λx}(λx)^k/k!` of the Poisson weights. -/
noncomputable def poissonPartial (r x : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, Real.exp (-(r * x)) * ((r * x) ^ k / k.factorial)

theorem poissonPartial_hasDerivAt (r x : ℝ) (n : ℕ) :
    HasDerivAt (fun y => poissonPartial r y (n + 1))
      (-(r * (Real.exp (-(r * x)) * ((r * x) ^ n / n.factorial)))) x := by
  have he : HasDerivAt (fun y => Real.exp (-(r * y))) (Real.exp (-(r * x)) * -r) x := by
    have := ((hasDerivAt_id x).const_mul r).neg.exp
    simpa using this
  induction n with
  | zero =>
    unfold poissonPartial
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero,
      Nat.cast_one, div_one, mul_one]
    convert he using 1
    ring
  | succ n ih =>
    have e : (fun y => poissonPartial r y (n + 1 + 1)) = fun y =>
        poissonPartial r y (n + 1) + Real.exp (-(r * y)) * ((r * y) ^ (n + 1) / (n + 1).factorial) := by
      funext y; unfold poissonPartial; rw [Finset.sum_range_succ]
    rw [e]
    have hp : HasDerivAt (fun y => (r * y) ^ (n + 1) / ((n + 1).factorial : ℝ))
        (((n + 1 : ℕ) : ℝ) * (r * x) ^ n * r / ((n + 1).factorial : ℝ)) x := by
      have h0 := (hasDerivAt_pow (n + 1) (r * x)).comp x ((hasDerivAt_id' x).const_mul r)
      have h1 : HasDerivAt (fun y => (r * y) ^ (n + 1)) (((n + 1 : ℕ) : ℝ) * (r * x) ^ n * r) x := by
        convert h0 using 1
        · rfl
        · rw [Nat.add_sub_cancel, mul_one]
      exact h1.div_const _
    convert ih.add (he.mul hp) using 1
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring

theorem poissonPartial_zero (r : ℝ) (n : ℕ) : poissonPartial r 0 (n + 1) = 1 := by
  unfold poissonPartial
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk; simp [zero_pow hk]
  · simp

/-- The integral of the gamma density with integer shape `n + 1` over `[0, x]`. -/
theorem integral_gammaPDFReal_nat {r : ℝ} (hr : 0 < r) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ∫ y in (0 : ℝ)..x, gammaPDFReal (n + 1) r y = 1 - poissonPartial r x (n + 1) := by
  have hcongr : ∀ y ∈ uIcc (0 : ℝ) x, gammaPDFReal (n + 1) r y =
      r * (Real.exp (-(r * y)) * ((r * y) ^ n / n.factorial)) := by
    intro y hy
    rw [uIcc_of_le hx] at hy
    unfold gammaPDFReal
    rw [ite_eq_left hy.1, show ((n : ℝ) + 1 - 1) = (n : ℕ) by ring, Real.rpow_natCast,
      show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
      show Real.Gamma ((n + 1 : ℕ) : ℝ) = n.factorial by rw [Nat.cast_succ, Real.Gamma_nat_eq_factorial]]
    rw [mul_pow, pow_succ]
    field_simp
  rw [intervalIntegral.integral_congr hcongr]
  have hderiv : ∀ y ∈ uIcc (0 : ℝ) x, HasDerivAt (fun y => 1 - poissonPartial r y (n + 1))
      (r * (Real.exp (-(r * y)) * ((r * y) ^ n / n.factorial))) y := by
    intro y _
    convert (poissonPartial_hasDerivAt r y n).const_sub 1 using 1
    ring
  have hint : IntervalIntegrable (fun y => r * (Real.exp (-(r * y)) * ((r * y) ^ n / n.factorial)))
      volume 0 x := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, poissonPartial_zero]
  ring

/-- Grinstead–Snell §5.2 (PR-215), distribution function of `S_n`.  For the gamma law with integer shape `n ≥ 1` and
rate `λ > 0`: `G_n(x) = 1 - e^{-λx}(1 + λx + ⋯ + (λx)^{n-1}/(n-1)!)` for `x ≥ 0`, and `G_n(x) = 0` for `x < 0`. -/
@[kb "grinsteadsnell2006" "§5.2 gamma density, p. 213"]
theorem cdf_gammaMeasure_nat {r : ℝ} (hr : 0 < r) (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    cdf (gammaMeasure n r) x = if 0 ≤ x then 1 - poissonPartial r x n else 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  rw [cdf_gammaMeasure_eq_integral hpos hr]
  have hneg : ∀ y, y < 0 → gammaPDFReal ((m + 1 : ℕ) : ℝ) r y = 0 := fun y hy => by
    unfold gammaPDFReal; rw [ite_eq_right (not_le.2 hy)]
  have hIio0 : ∫ y in Iio 0, gammaPDFReal ((m + 1 : ℕ) : ℝ) r y = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun y hy => hneg y hy
  have hint : Integrable (gammaPDFReal ((m + 1 : ℕ) : ℝ) r) := by
    have h := lintegral_gammaPDF_eq_one hpos hr
    refine ⟨(measurable_gammaPDFReal _ r).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (gammaPDFReal_nonneg hpos hr))]
    unfold gammaPDF at h
    rw [h]; exact ENNReal.one_lt_top
  split_ifs with hx
  · rw [← Iic_union_Ioc_eq_Iic hx, setIntegral_union (Set.disjoint_left.2 fun y h1 h2 => by
        exact absurd h1 (not_le.2 h2.1)) measurableSet_Ioc hint.integrableOn hint.integrableOn,
      integral_Iic_eq_integral_Iio, hIio0, zero_add, ← intervalIntegral.integral_of_le hx]
    push_cast
    exact integral_gammaPDFReal_nat hr m hx
  · rw [integral_Iic_eq_integral_Iio]
    exact setIntegral_eq_zero_of_forall_eq_zero fun y hy => hneg y (lt_trans hy (not_le.1 hx))

section

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- `P(S_n ≤ t) = 1 - ∑_{k<n} e^{-λt}(λt)^k/k!` for `t ≥ 0` and every `n` (for `n = 0`, `S_0 = 0`). -/
theorem measureReal_sum_exponential_le {X : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) {r : ℝ} (hr : 0 < r) (hX : ∀ i, P.map (X i) = expMeasure r) (n : ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | ∑ i ∈ Finset.range n, X i ω ≤ t} = 1 - poissonPartial r t n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [poissonPartial, ht]
  have hms : Measurable fun ω => ∑ i ∈ Finset.range n, X i ω := Finset.measurable_sum _ fun i _ => hmeas i
  have hlaw := hasLaw_sum_exponential_gamma hmeas hind hr hX n hn
  have : IsProbabilityMeasure (gammaMeasure n r) :=
    isProbabilityMeasure_gammaMeasure (by exact_mod_cast hn) hr
  have e : {ω | ∑ i ∈ Finset.range n, X i ω ≤ t} = (fun ω => ∑ i ∈ Finset.range n, X i ω) ⁻¹' Iic t := rfl
  rw [e, ← map_measureReal_apply hms measurableSet_Iic, hlaw, ← cdf_eq_real,
    cdf_gammaMeasure_nat hr n hn t, ite_eq_left ht]

/-- Grinstead–Snell §5.2 (PR-215), the exponential density and the Poisson distribution.  Let `X_0, X_1, …` be
independent exponential variables with parameter `λ > 0` (times between emissions), `S_n = X_0 + ⋯ + X_{n-1}`,
and `t ≥ 0`.  The probability that exactly `n` emissions occur by time `t`, `P(S_n ≤ t < S_{n+1})`, is the
Poisson probability `e^{-λt}(λt)^n/n!`. -/
@[kb "grinsteadsnell2006" "§5.2 exponential and Poisson, p. 213"]
theorem exponential_gaps_poisson_count {X : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) {r : ℝ} (hr : 0 < r) (hX : ∀ i, P.map (X i) = expMeasure r) (n : ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | ∑ i ∈ Finset.range n, X i ω ≤ t ∧ t < ∑ i ∈ Finset.range (n + 1), X i ω} =
      Real.exp (-(r * t)) * ((r * t) ^ n / n.factorial) := by
  set A := {ω | ∑ i ∈ Finset.range n, X i ω ≤ t} with hA
  set B := {ω | ∑ i ∈ Finset.range (n + 1), X i ω ≤ t} with hB
  have hBm : MeasurableSet B :=
    measurableSet_le (Finset.measurable_sum _ fun i _ => hmeas i) measurable_const
  -- `B ⊆ A` outside the null set `{X n < 0}`
  have hnull : P {ω | X n ω < 0} = 0 := by
    have e : {ω | X n ω < 0} = X n ⁻¹' Iio 0 := rfl
    rw [e, ← Measure.map_apply (hmeas n) measurableSet_Iio, hX n, expMeasure, gammaMeasure,
      withDensity_apply _ measurableSet_Iio]
    exact lintegral_gammaPDF_of_nonpos le_rfl
  have hsub : B ⊆ A ∪ {ω | X n ω < 0} := by
    intro ω hω
    simp only [hB, mem_ofPred_eq, Finset.sum_range_succ] at hω
    by_cases h : X n ω < 0
    · exact Or.inr h
    · exact Or.inl (show _ ≤ t by linarith [not_lt.1 h])
  have hAB : P.real (A ∩ B) = P.real B := by
    have h1 : P (A ∩ B) ≤ P B := measure_mono inter_subset_right
    have h2 : P B ≤ P (A ∩ B) := by
      calc P B ≤ P ((A ∩ B) ∪ {ω | X n ω < 0}) := measure_mono fun ω hω => by
              rcases hsub hω with h | h
              · exact Or.inl ⟨h, hω⟩
              · exact Or.inr h
        _ ≤ P (A ∩ B) + P {ω | X n ω < 0} := measure_union_le _ _
        _ = P (A ∩ B) := by rw [hnull, add_zero]
    unfold Measure.real
    rw [le_antisymm h1 h2]
  have hset : {ω | ∑ i ∈ Finset.range n, X i ω ≤ t ∧ t < ∑ i ∈ Finset.range (n + 1), X i ω} = A \ B := by
    ext ω; simp [hA, hB, not_le]
  have hdiff := measureReal_sdiff_add_inter (μ := P) (s := A) hBm
  rw [hset]
  rw [hAB] at hdiff
  have hAv := measureReal_sum_exponential_le hmeas hind hr hX n ht
  have hBv := measureReal_sum_exponential_le hmeas hind hr hX (n + 1) ht
  rw [← hA] at hAv
  rw [← hB] at hBv
  have : P.real (A \ B) = P.real A - P.real B := by linarith
  rw [this, hAv, hBv]
  unfold poissonPartial
  rw [Finset.sum_range_succ]
  ring

end

end UndergradKB.Probability
