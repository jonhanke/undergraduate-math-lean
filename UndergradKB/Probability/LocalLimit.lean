import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.Moments.Variance
import UndergradKB.Common.Attr

/-!
# Central limit theorem in interval form (Grinstead–Snell, chapter 9)

The central limit theorem of Mathlib is a statement of convergence in distribution. Here it is turned,
by the portmanteau theorem (the standard normal law has no atoms), into the interval form of the book:
`P(a ≤ S_n* ≤ b)` tends to the integral of the standard normal density over `[a, b]`, for sums of
independent identically distributed variables (Theorem 9.4 shape, used for Theorem 9.5's iid case) and
for Bernoulli trials (Theorem 9.2).
-/

open MeasureTheory ProbabilityTheory Filter unitInterval
open scoped Topology NNReal ENNReal

namespace UndergradKB.Probability

section Interval

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'}

/-- The boundary of a closed interval is null for the standard normal law. -/
theorem gaussianReal_frontier_Icc_null {a b : ℝ} (hab : a ≤ b) :
    gaussianReal 0 1 (frontier (Set.Icc a b)) = 0 := by
  rw [frontier_Icc hab]
  have : (volume : Measure ℝ) {a, b} = 0 := (Set.toFinite _).measure_zero _
  exact gaussianReal_absolutelyContinuous 0 one_ne_zero this

/-- Portmanteau for intervals: if `X n` converges in distribution to a standard normal variable,
then `P(X n ∈ [a, b])` converges to the standard normal integral over `[a, b]`. -/
theorem tendsto_real_Icc_of_tendstoInDistribution [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {X : ℕ → Ω → ℝ} {Y : Ω' → ℝ} (hY : HasLaw Y (gaussianReal 0 1) P')
    (hT : TendstoInDistribution X atTop Y (fun _ => P) P') {a b : ℝ} (hab : a ≤ b) :
    Tendsto (fun n => P.real {ω | a ≤ X n ω ∧ X n ω ≤ b}) atTop
      (𝓝 (∫ x in a..b, gaussianPDFReal 0 1 x)) := by
  have hnull : (P'.map Y) (frontier (Set.Icc a b)) = 0 := by
    rw [hY.map_eq]; exact gaussianReal_frontier_Icc_null hab
  have hP : ∀ n, IsProbabilityMeasure (P.map (X n)) := fun n => inferInstance
  have hP' : IsProbabilityMeasure (P'.map Y) := inferInstance
  have key := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    (μs := fun n => (⟨P.map (X n), hP n⟩ : ProbabilityMeasure ℝ))
    (μ := (⟨P'.map Y, hP'⟩ : ProbabilityMeasure ℝ))
    hT.tendsto (E := Set.Icc a b) hnull
  have key2 := (ENNReal.tendsto_toReal (measure_ne_top (P'.map Y) (Set.Icc a b))).comp key
  have hlim : ((P'.map Y) (Set.Icc a b)).toReal = ∫ x in a..b, gaussianPDFReal 0 1 x := by
    rw [hY.map_eq, gaussianReal_apply_eq_integral 0 one_ne_zero,
      ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Icc
        fun x _ => gaussianPDFReal_nonneg 0 1 x),
      intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
  rw [← hlim]
  refine key2.congr fun n => ?_
  change ((P.map (X n)) (Set.Icc a b)).toReal = _
  rw [Measure.map_apply_of_aemeasurable (hT.forall_aemeasurable n) measurableSet_Icc,
    measureReal_def]
  rfl

end Interval

section IID

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- Grinstead–Snell Theorem 9.4 (PR-100). Interval form of the central limit theorem: for independent
identically distributed variables with finite nonzero variance `σ²` and mean `μ`, the chance that the
standardized sum `(S_n - nμ)/(σ √n)` lies in `[a, b]` tends to the standard normal integral over `[a, b]`. -/
@[kb "grinsteadsnell2006" "Theorem 9.4, p. 351"]
theorem clt_iid_interval {X : ℕ → Ω → ℝ} (hX : MemLp (X 0) 2 P) (hv : Var[X 0; P] ≠ 0)
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {a b : ℝ} (hab : a ≤ b) :
    Tendsto (fun n : ℕ => P.real {ω | a ≤ (∑ k ∈ Finset.range n, X k ω - n * P[X 0]) /
        (√Var[X 0; P] * √n) ∧ (∑ k ∈ Finset.range n, X k ω - n * P[X 0]) /
        (√Var[X 0; P] * √n) ≤ b}) atTop (𝓝 (∫ x in a..b, gaussianPDFReal 0 1 x)) := by
  set v := Var[X 0; P] with hvdef
  have hvpos : 0 < v := lt_of_le_of_ne (variance_nonneg _ _) (Ne.symm hv)
  have hsq : 0 < √v := Real.sqrt_pos.2 hvpos
  let P' : Measure ℝ := gaussianReal 0 v.toNNReal
  have hY : HasLaw (id : ℝ → ℝ) (gaussianReal 0 v.toNNReal) P' :=
    ⟨aemeasurable_id, by simp [P']⟩
  have h1 := tendstoInDistribution_inv_sqrt_mul_sum_sub (P := P) (X := X) hY hX hindep hident
  have hne : v.toNNReal ≠ 0 := by simpa using hvpos
  have hY1 : HasLaw (fun y : ℝ => y / √v) (gaussianReal 0 1) P' := by
    have := gaussianReal_div_const hY √v
    convert this using 2
    all_goals first
      | simp
      | (apply NNReal.coe_injective; simp [Real.sq_sqrt hvpos.le, hvpos.le, hvpos.ne', v])
  have h2 := h1.continuous_comp (g := fun y : ℝ => y / √v) (by fun_prop)
  have h3 := tendsto_real_Icc_of_tendstoInDistribution hY1 h2 hab
  have key : ∀ (n : ℕ) (ω : Ω), (√n)⁻¹ * (∑ k ∈ Finset.range n, X k ω - n * P[X 0]) / √v =
      (∑ k ∈ Finset.range n, X k ω - n * P[X 0]) / (√v * √n) := by
    intro n ω; ring
  refine h3.congr fun n => ?_
  congr 1
  ext ω
  simp only [Set.mem_setOf_eq, Function.comp_apply, key]

end IID

section Bernoulli

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- A Bernoulli variable takes only the values `1` and `0` almost surely. -/
theorem bernoulli_ae_mem {Z : Ω → ℝ} {p : I} (hZ : HasLaw Z Ber(1, 0, p) P) :
    ∀ᵐ ω ∂P, Z ω ∈ ({1, 0} : Set ℝ) := by
  have hs : MeasurableSet ({1, 0} : Set ℝ)ᶜ := (Set.toFinite _).measurableSet.compl
  have h0 : Ber((1 : ℝ), 0, p) ({1, 0} : Set ℝ)ᶜ = 0 :=
    bernoulliMeasure_apply_of_notMem_of_notMem p hs (by simp) (by simp)
  rw [← hZ.map_eq, Measure.map_apply_of_aemeasurable hZ.aemeasurable hs] at h0
  rw [ae_iff]
  exact h0

/-- A Bernoulli variable is in `L²`. -/
theorem bernoulli_memLp {Z : Ω → ℝ} {p : I} (hZ : HasLaw Z Ber(1, 0, p) P) : MemLp Z 2 P := by
  refine MemLp.of_bound hZ.aemeasurable.aestronglyMeasurable 1 ?_
  filter_upwards [bernoulli_ae_mem hZ] with ω hω
  rcases hω with h | h <;> simp [Set.mem_singleton_iff.1 h]

/-- A Bernoulli(`p`) variable has mean `p` and variance `p (1 - p)`. -/
theorem bernoulli_mean_variance {Z : Ω → ℝ} {p : I} (hZ : HasLaw Z Ber(1, 0, p) P) :
    P[Z] = (p : ℝ) ∧ Var[Z; P] = (p : ℝ) * (1 - p) := by
  have hmean : P[Z] = (p : ℝ) := by
    have : P[Z] = ∫ x, x ∂(P.map Z) := (integral_map hZ.aemeasurable aestronglyMeasurable_id).symm
    rw [this, hZ.map_eq, integral_bernoulliMeasure]
    simp
  refine ⟨hmean, ?_⟩
  have hsq : P[Z ^ 2] = (p : ℝ) := by
    rw [← hmean]
    refine integral_congr_ae ?_
    filter_upwards [bernoulli_ae_mem hZ] with ω hω
    rcases hω with h | h <;> simp [Set.mem_singleton_iff.1 h]
  rw [variance_eq_sub (bernoulli_memLp hZ), hsq, hmean]
  ring

/-- Grinstead–Snell Theorem 9.2 (PR-098). Central limit theorem for Bernoulli trials in interval
form: for independent trials with success probability `p` (`0 < p < 1`), the chance that the
standardized number of successes `(S_n - n p)/√(n p q)` lies in `[a, b]` tends to the integral of the
standard normal density over `[a, b]`. -/
@[kb "grinsteadsnell2006" "Theorem 9.2, p. 338"]
theorem clt_bernoulli_interval {X : ℕ → Ω → ℝ} {p : I} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hlaw : ∀ i, HasLaw (X i) Ber(1, 0, p) P) (hindep : iIndepFun X P) {a b : ℝ} (hab : a ≤ b) :
    Tendsto (fun n : ℕ => P.real {ω | a ≤ (∑ k ∈ Finset.range n, X k ω - n * p) /
        √(n * p * (1 - p)) ∧ (∑ k ∈ Finset.range n, X k ω - n * p) / √(n * p * (1 - p)) ≤ b})
      atTop (𝓝 (∫ x in a..b, gaussianPDFReal 0 1 x)) := by
  obtain ⟨hm, hv⟩ := bernoulli_mean_variance (hlaw 0)
  have hident : ∀ i, IdentDistrib (X i) (X 0) P P := fun i =>
    ⟨(hlaw i).aemeasurable, (hlaw 0).aemeasurable, by rw [(hlaw i).map_eq, (hlaw 0).map_eq]⟩
  have hmem : MemLp (X 0) 2 P := bernoulli_memLp (hlaw 0)
  have hpq : 0 < (p : ℝ) * (1 - p) := mul_pos hp0 (by linarith)
  have := clt_iid_interval hmem (by rw [hv]; exact hpq.ne') hindep hident hab
  rw [hm, hv] at this
  refine this.congr fun n => ?_
  congr 1
  ext ω
  have h : √((p : ℝ) * (1 - p)) * √n = √(n * p * (1 - p)) := by
    rw [← Real.sqrt_mul hpq.le]; congr 1; ring
  simp only [Set.mem_setOf_eq, h]

end Bernoulli

end UndergradKB.Probability
