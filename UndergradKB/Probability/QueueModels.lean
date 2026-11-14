import Mathlib.Probability.HasLawExists
import UndergradKB.Common.Attr
import UndergradKB.Probability.PoissonClock
import UndergradKB.Probability.QueueArrivals

/-! # Probability: the clock and the coin-driven queue exist (Grinstead–Snell §5.2, Example 6.29)

Wave 8.  The hypotheses of `exponential_gaps_poisson_count` (independent exponential gaps) and of
`queue_arrivals_see_equilibrium_limit` (independent initial length and coins) can be met: Mathlib's
`exists_hasLaw_indepFun` builds independent variables with any given laws on an infinite product space. -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace UndergradKB.Probability

/-- Independent exponential gaps with rate `λ > 0` exist. -/
theorem exists_exponential_gaps {r : ℝ} (hr : 0 < r) :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω, ∃ X : ℕ → Ω → ℝ,
      IsProbabilityMeasure P ∧ (∀ i, Measurable (X i)) ∧ iIndepFun X P ∧ ∀ i, P.map (X i) = expMeasure r := by
  have := isProbabilityMeasure_expMeasure hr
  obtain ⟨Ω, mΩ, P, X, hm, hlaw, hind, hP⟩ := exists_iid ℕ (expMeasure r)
  exact ⟨Ω, mΩ, P, X, hP, hm, hind, fun i => (hlaw i).map_eq⟩

/-- The law of a coin on `ℕ`: `1` with probability `a`, `0` with probability `1 - a`. -/
noncomputable def coinLaw (a : ℝ) : Measure ℕ :=
  ENNReal.ofReal a • Measure.dirac 1 + ENNReal.ofReal (1 - a) • Measure.dirac 0

theorem coinLaw_prob {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) : IsProbabilityMeasure (coinLaw a) := by
  constructor
  simp only [coinLaw, add_apply, smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add h0 (by linarith)]
  simp

theorem coinLaw_one {a : ℝ} (h0 : 0 ≤ a) : (coinLaw a).real {1} = a := by
  simp [coinLaw, Measure.real, h0]

/-- For `λ, μ > 0` and any `j`, there are independent variables `Z 0 = j` and coins `Z (n+1)` that are
arrivals (value `1`) with probability `λ/(λ+μ)`: the hypotheses of `queue_arrivals_see_equilibrium_limit`. -/
theorem exists_queue_coins {lam mu : ℝ} (hl : 0 < lam) (hm : 0 < mu) (j : ℕ) :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω, ∃ Z : ℕ → Ω → ℕ,
      IsProbabilityMeasure P ∧ (∀ i, Measurable (Z i)) ∧ iIndepFun Z P ∧
      (∀ n, P.real {ω | Z (n + 1) ω = 1} = lam / (lam + mu)) ∧ P.real {ω | Z 0 ω = j} = 1 := by
  set a := lam / (lam + mu) with ha
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 := by rw [ha, div_le_one (by linarith)]; linarith
  set μs : ℕ → Measure ℕ := fun i => if i = 0 then Measure.dirac j else coinLaw a with hμs
  have hμ : ∀ i, IsProbabilityMeasure (μs i) := fun i => by
    by_cases hi : i = 0
    · simp only [hμs, hi, ite_true]; infer_instance
    · simp only [hμs, hi, ite_false]; exact coinLaw_prob ha0 ha1
  obtain ⟨Ω, mΩ, P, Z, hmZ, hlaw, hind, hP⟩ := exists_hasLaw_indepFun (fun _ : ℕ => ℕ) μs
  refine ⟨Ω, mΩ, P, Z, hP, hmZ, hind, fun n => ?_, ?_⟩
  · have e : {ω | Z (n + 1) ω = 1} = Z (n + 1) ⁻¹' {1} := rfl
    rw [e, ← map_measureReal_apply (hmZ (n + 1)) (MeasurableSet.of_discrete), (hlaw (n + 1)).map_eq]
    simp only [hμs, Nat.add_one_ne_zero, ite_false]
    exact coinLaw_one ha0
  · have e : {ω | Z 0 ω = j} = Z 0 ⁻¹' {j} := rfl
    rw [e, ← map_measureReal_apply (hmZ 0) (MeasurableSet.of_discrete), (hlaw 0).map_eq]
    simp [hμs]

end UndergradKB.Probability
