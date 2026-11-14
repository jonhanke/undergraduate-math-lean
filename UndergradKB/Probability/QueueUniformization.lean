import Mathlib.Probability.Independence.Basic
import UndergradKB.Common.Attr
import UndergradKB.Probability.PoissonClock
import UndergradKB.Probability.QueueStartTime

/-! # Probability: the queue in continuous time from a Poisson clock (Grinstead–Snell Example 6.29)

Wave 8, a recorded loose end (1).  The continuous-time queue of the book is realized by uniformization: a clock
whose gaps `X_0, X_1, …` are independent exponential variables with rate `ν = λ + μ` rings at the times
`S_1 < S_2 < ⋯`, and at each ring the queue makes one step of its jump chain `Y_0, Y_1, …` (`queueJump`),
independent of the clock.  The queue length at time `t` is `Y_n` on the event `S_n ≤ t < S_{n+1}` (exactly `n`
rings by time `t`).

`queue_uniformization_law`: if the clock gaps are independent exponential(`λ + μ`), the chain started with `j`
customers has the laws `queueLawFrom j` of the jump chain, and the clock is independent of the chain, then
`P(queue length at time t = k) = ∑_n P(S_n ≤ t < S_{n+1}) P(Y_n = k)`, which is the uniformization law
`queueLawTimeFrom j t k` (so, by `queue_forward_determines_law`, the unique bounded solution of the forward
equations).  This uses the Poisson count of `exponential_gaps_poisson_count` (§5.2). -/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace UndergradKB.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The event that exactly `n` rings of the clock with gaps `X` happen by time `t`. -/
def clockCount (X : ℕ → Ω → ℝ) (t : ℝ) (n : ℕ) : Set Ω :=
  {ω | ∑ i ∈ Finset.range n, X i ω ≤ t ∧ t < ∑ i ∈ Finset.range (n + 1), X i ω}

omit [MeasurableSpace Ω] in
/-- The clock events `S_n ≤ t < S_{n+1}` are disjoint outside the event that some gap is negative. -/
theorem clockCount_inter_subset (X : ℕ → Ω → ℝ) (t : ℝ) {n m : ℕ} (hnm : n < m) :
    clockCount X t n ∩ clockCount X t m ⊆ ⋃ i, {ω | X i ω < 0} := by
  intro ω ⟨h1, h2⟩
  by_contra hω
  simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_lt] at hω
  have hmono : ∑ i ∈ Finset.range (n + 1), X i ω ≤ ∑ i ∈ Finset.range m, X i ω :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega)) fun i _ _ => hω i
  exact absurd (h1.2.trans_le (hmono.trans h2.1)) (lt_irrefl t)

theorem measurableSet_clockCount {X : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (X i)) (t : ℝ) (n : ℕ) :
    MeasurableSet (clockCount X t n) :=
  show MeasurableSet ({ω | ∑ i ∈ Finset.range n, X i ω ≤ t} ∩ {ω | t < ∑ i ∈ Finset.range (n + 1), X i ω}) from
  (measurableSet_le (Finset.measurable_sum _ fun i _ => hmeas i) measurable_const).inter
    (measurableSet_lt measurable_const (Finset.measurable_sum _ fun i _ => hmeas i))

/-- Grinstead–Snell Example 6.29 (PR-209), the queue in continuous time by uniformization.  Let `λ, μ > 0`.  Let
the clock gaps `X_0, X_1, …` be independent exponential variables with rate `λ + μ`, let `Y_0, Y_1, …` be the
queue lengths of the jump chain started with `j` customers (`P(Y_n = k) = queueLawFrom j n k`, the laws of
`queueJump` by `queueLawFrom_step`), and let the clock be independent of the chain.  Then for `t ≥ 0` the queue
length at time `t` (equal to `Y_n` when exactly `n` rings happen by time `t`) has the uniformization law:
`P(∃ n, S_n ≤ t < S_{n+1} and Y_n = k) = queueLawTimeFrom j t k`. -/
@[kb "grinsteadsnell2006" "Example 6.29, p. 283"]
theorem queue_uniformization_law {lam mu : ℝ} (hl : 0 < lam) (hm : 0 < mu) (j : ℕ)
    {X : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hX : ∀ i, P.map (X i) = expMeasure (lam + mu))
    {Y : ℕ → Ω → ℕ} (hYm : ∀ n, Measurable (Y n))
    (hY : ∀ n k, P.real {ω | Y n ω = k} = queueLawFrom lam mu j n k)
    (hXY : IndepFun (fun ω i => X i ω) (fun ω n => Y n ω) P) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    P.real {ω | ∃ n, ω ∈ clockCount X t n ∧ Y n ω = k} = queueLawTimeFrom lam mu j t k := by
  have hν : 0 < lam + mu := by linarith
  set E : ℕ → Set Ω := fun n => clockCount X t n ∩ {ω | Y n ω = k} with hE
  have hEm : ∀ n, MeasurableSet (E n) := fun n =>
    (measurableSet_clockCount hmeas t n).inter (measurableSet_eq_fun (hYm n) measurable_const)
  -- the probability of each piece factors
  have hpiece : ∀ n, P.real (E n) = poissonWeight (lam + mu) t n * queueLawFrom lam mu j n k := by
    intro n
    have hXv : Measurable fun ω (i : ℕ) => X i ω := measurable_pi_iff.2 hmeas
    have hYv : Measurable fun ω (n : ℕ) => Y n ω := measurable_pi_iff.2 hYm
    set s : Set (ℕ → ℝ) := {x | ∑ i ∈ Finset.range n, x i ≤ t ∧ t < ∑ i ∈ Finset.range (n + 1), x i}
    set u : Set (ℕ → ℕ) := {y | y n = k}
    have hs : MeasurableSet s :=
      show MeasurableSet ({x : ℕ → ℝ | ∑ i ∈ Finset.range n, x i ≤ t} ∩
        {x : ℕ → ℝ | t < ∑ i ∈ Finset.range (n + 1), x i}) from
      (measurableSet_le (Finset.measurable_sum _ fun i _ => measurable_pi_apply i) measurable_const).inter
        (measurableSet_lt measurable_const (Finset.measurable_sum _ fun i _ => measurable_pi_apply i))
    have hu : MeasurableSet u := measurableSet_eq_fun (measurable_pi_apply n) measurable_const
    have h := hXY.measure_inter_preimage_eq_mul s u hs hu
    have e1 : (fun ω (i : ℕ) => X i ω) ⁻¹' s = clockCount X t n := rfl
    have e2 : (fun ω (n : ℕ) => Y n ω) ⁻¹' u = {ω | Y n ω = k} := rfl
    rw [e1, e2] at h
    have hc := exponential_gaps_poisson_count hmeas hind hν hX n ht
    rw [show {ω | ∑ i ∈ Finset.range n, X i ω ≤ t ∧ t < ∑ i ∈ Finset.range (n + 1), X i ω} =
      clockCount X t n from rfl] at hc
    simp only [hE, Measure.real, h, ENNReal.toReal_mul]
    rw [← Measure.real, ← Measure.real, hc, hY]
    rfl
  -- the pieces are almost disjoint
  have hnull : P (⋃ i, {ω | X i ω < 0}) = 0 := by
    refine measure_iUnion_null fun i => ?_
    have e : {ω | X i ω < 0} = X i ⁻¹' Iio 0 := rfl
    rw [e, ← Measure.map_apply (hmeas i) measurableSet_Iio, hX i, expMeasure, gammaMeasure,
      withDensity_apply _ measurableSet_Iio]
    exact lintegral_gammaPDF_of_nonpos le_rfl
  have hdisj : Pairwise (Function.onFun (AEDisjoint P) E) := by
    intro n m hnm
    show P (E n ∩ E m) = 0
    refine measure_mono_null ?_ hnull
    rcases lt_or_gt_of_ne hnm with h | h
    · exact fun ω hω => clockCount_inter_subset X t h ⟨hω.1.1, hω.2.1⟩
    · exact fun ω hω => clockCount_inter_subset X t h ⟨hω.2.1, hω.1.1⟩
  have hset : {ω | ∃ n, ω ∈ clockCount X t n ∧ Y n ω = k} = ⋃ n, E n := by
    ext ω; simp [hE]
  have hU := measure_iUnion₀ hdisj fun n => (hEm n).nullMeasurableSet
  rw [hset, Measure.real, hU, ENNReal.tsum_toReal_eq fun n => measure_ne_top P (E n)]
  unfold queueLawTimeFrom poissonMix
  exact tsum_congr fun n => hpiece n

end UndergradKB.Probability
