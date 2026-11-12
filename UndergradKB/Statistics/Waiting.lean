import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.HasLaw
import UndergradKB.Common.Attr

/-!
# Poisson counts and exponential waiting times

OpenStax *Introductory Statistics 2e*, §5.3: if events occur at rate `m` per unit time and `N t` counts the events
in `[0, t]`, with `N t` Poisson with mean `m t`, then the waiting time `T` to the first event is exponential with
decay rate `m`, because `T > t` exactly when `N t = 0`.
-/

namespace UndergradKB.Statistics

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal

/-- **Poisson counts give an exponential waiting time (ST-056).** Let `T` be a random time and `N t` the
(random) number of events up to time `t`. Suppose that for every `t ≥ 0` the event `T > t` is exactly the event
`N t = 0`, and that `N t` has the Poisson law with mean `m t`. Then `T` has the exponential law with decay rate
`m` (and mean `1/m`). -/
@[kb "openstaxintrostats2e" "§5.3, p. 313"]
theorem hasLaw_expMeasure_of_poisson_counts {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {T : Ω → ℝ} {N : ℝ → Ω → ℕ} {m : ℝ} (hm : 0 < m)
    (hT : AEMeasurable T P)
    (hev : ∀ t, 0 ≤ t → {ω | t < T ω} = {ω | N t ω = 0})
    (hN : ∀ t, 0 ≤ t → HasLaw (N t) (poissonMeasure (m * t).toNNReal) P) :
    HasLaw T (expMeasure m) P := by
  have := isProbabilityMeasure_expMeasure hm
  refine ⟨hT, ?_⟩
  -- the survival function
  have hsurv : ∀ t, 0 ≤ t → P.real {ω | t < T ω} = exp (-(m * t)) := by
    intro t ht
    rw [hev t ht]
    have h : P.real {ω | N t ω = 0} = (poissonMeasure (m * t).toNNReal).real {x : ℕ | x = 0} :=
      (hN t ht).measureReal_eq (p := fun k ↦ k = 0) MeasurableSet.of_discrete
    rw [h, show {x : ℕ | x = 0} = {0} from rfl, poissonMeasure_real_singleton,
      Real.coe_toNNReal _ (by positivity)]
    simp
  have hnull : ∀ t, 0 ≤ t → NullMeasurableSet {ω | t < T ω} P := by
    intro t ht
    rw [hev t ht]
    exact ((hN t ht).aemeasurable.nullMeasurable (MeasurableSet.of_discrete (s := {0})))
  have hcdf : ∀ a, 0 ≤ a → (P.map T).real (Iic a) = 1 - exp (-(m * a)) := by
    intro a ha
    rw [measureReal_def, Measure.map_apply_of_aemeasurable hT measurableSet_Iic, ← measureReal_def]
    have : T ⁻¹' Iic a = {ω | a < T ω}ᶜ := by
      ext ω
      simp
    rw [this, probReal_compl_eq_one_sub₀ (hnull a ha), hsurv a ha]
  have hex : ∀ a, 0 ≤ a → (expMeasure m).real (Iic a) = 1 - exp (-(m * a)) := by
    intro a ha
    rw [← cdf_eq_real, cdf_expMeasure_eq hm, if_pos ha]
  have hzero : (P.map T).real (Iic 0) = 0 := by
    rw [hcdf 0 le_rfl]
    simp
  refine Measure.ext_of_Iic (P.map T) (expMeasure m) fun a ↦ ?_
  rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)]
  show (P.map T).real (Iic a) = (expMeasure m).real (Iic a)
  by_cases ha : 0 ≤ a
  · rw [hcdf a ha, hex a ha]
  · push_neg at ha
    have h1 : (P.map T).real (Iic a) = 0 :=
      le_antisymm (hzero ▸ measureReal_mono (Iic_subset_Iic.2 ha.le)) measureReal_nonneg
    rw [h1, ← cdf_eq_real, cdf_expMeasure_eq hm, if_neg (not_le.2 ha)]

end UndergradKB.Statistics
