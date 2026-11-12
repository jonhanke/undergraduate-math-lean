import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Probability.CDF
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import UndergradKB.Statistics.Data

/-!
# Median, percentiles and symmetry

OpenStax *Introductory Statistics 2e*, §2.3, §2.5, §2.6.

* the median of a data list (`median`), with the fact that at least half of the data lie on each side;
* percentiles of a law through `ProbabilityTheory.cdf`;
* the mean of a law symmetric about `m` is `m`.
-/

namespace UndergradKB.Statistics

open MeasureTheory ProbabilityTheory Finset Set Filter Topology

section Median

variable {n : ℕ}

/-- The data list `x` rearranged into non-decreasing order. -/
noncomputable def sortedData (x : Fin n → ℝ) : Fin n → ℝ := x ∘ Tuple.sort x

lemma monotone_sortedData (x : Fin n → ℝ) : Monotone (sortedData x) := Tuple.monotone_sort x

/-- The median of a data list: the middle value of the sorted list when `n` is odd, the mean of the two middle
values when `n` is even (and `0` for the empty list). -/
noncomputable def median (x : Fin n → ℝ) : ℝ :=
  if h : 0 < n then (sortedData x ⟨(n - 1) / 2, by omega⟩ + sortedData x ⟨n / 2, by omega⟩) / 2
  else 0

private lemma card_filter_sorted (x : Fin n → ℝ) (P : ℝ → Prop) [DecidablePred P] :
    (univ.filter fun j ↦ P (sortedData x j)).card = (univ.filter fun i ↦ P (x i)).card := by
  refine Finset.card_bij (fun j _ ↦ Tuple.sort x j) (fun j hj ↦ ?_) (fun a _ b _ h ↦
    (Tuple.sort x).injective h) fun i hi ↦ ⟨(Tuple.sort x).symm i, ?_, by simp⟩
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hj).2⟩
  · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    have := (Finset.mem_filter.1 hi).2
    simpa [sortedData] using this

/-- **At least half of the data are at most the median (ST-007).** -/
@[kb "openstaxintrostats2e" "§2.5, p. 109"]
theorem half_le_card_le_median (x : Fin n → ℝ) (hn : 0 < n) :
    n ≤ 2 * (univ.filter fun i ↦ x i ≤ median x).card := by
  set a : Fin n := ⟨(n - 1) / 2, by omega⟩ with ha
  set b : Fin n := ⟨n / 2, by omega⟩ with hb
  have hab : a ≤ b := by simp only [ha, hb, Fin.mk_le_mk]; omega
  have hmed : median x = (sortedData x a + sortedData x b) / 2 := by simp [median, hn, ha, hb]
  have hle : sortedData x a ≤ median x := by
    rw [hmed]; linarith [monotone_sortedData x hab]
  have hsub : Finset.Iic a ⊆ univ.filter fun j ↦ sortedData x j ≤ median x := by
    intro j hj
    rw [Finset.mem_Iic] at hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (monotone_sortedData x hj).trans hle
  have := Finset.card_le_card hsub
  rw [Fin.card_Iic, card_filter_sorted x (fun v ↦ v ≤ median x)] at this
  simp only [ha] at this
  omega

/-- **At least half of the data are at least the median (ST-007).** -/
@[kb "openstaxintrostats2e" "§2.5, p. 109"]
theorem half_le_card_ge_median (x : Fin n → ℝ) (hn : 0 < n) :
    n ≤ 2 * (univ.filter fun i ↦ median x ≤ x i).card := by
  set a : Fin n := ⟨(n - 1) / 2, by omega⟩ with ha
  set b : Fin n := ⟨n / 2, by omega⟩ with hb
  have hab : a ≤ b := by simp only [ha, hb, Fin.mk_le_mk]; omega
  have hmed : median x = (sortedData x a + sortedData x b) / 2 := by simp [median, hn, ha, hb]
  have hle : median x ≤ sortedData x b := by
    rw [hmed]; linarith [monotone_sortedData x hab]
  have hsub : Finset.Ici b ⊆ univ.filter fun j ↦ median x ≤ sortedData x j := by
    intro j hj
    rw [Finset.mem_Ici] at hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hle.trans (monotone_sortedData x hj)
  have := Finset.card_le_card hsub
  rw [Fin.card_Ici, card_filter_sorted x (fun v ↦ median x ≤ v)] at this
  simp only [hb] at this
  omega

end Median

section Percentile

/-- **Percentiles of a continuous law (ST-009).** If the distribution function of a probability law `μ` on `ℝ`
is continuous, then for every `0 < p < 1` there is a point `q` with `P(X ≤ q) = p` (a `100p`-th percentile);
`q` is unique when the distribution function is strictly increasing. -/
@[kb "openstaxintrostats2e" "§2.3, p. 97"]
theorem exists_percentile (μ : Measure ℝ) [IsProbabilityMeasure μ] (hc : Continuous (cdf μ))
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : ∃ q, μ.real (Iic q) = p := by
  obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot μ).eventually (gt_mem_nhds hp0)).exists
  obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop μ).eventually (lt_mem_nhds hp1)).exists
  obtain ⟨q, hq⟩ := mem_range_of_exists_le_of_exists_ge (c := p) hc ⟨a, ha.le⟩ ⟨b, hb.le⟩
  exact ⟨q, by rw [← cdf_eq_real]; exact hq⟩

/-- Uniqueness of the percentile for a strictly increasing distribution function (ST-009). -/
@[kb "openstaxintrostats2e" "§2.3, p. 97"]
theorem existsUnique_percentile (μ : Measure ℝ) [IsProbabilityMeasure μ] (hc : Continuous (cdf μ))
    (hs : StrictMono (cdf μ)) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∃! q, μ.real (Iic q) = p := by
  obtain ⟨q, hq⟩ := exists_percentile μ hc hp0 hp1
  refine ⟨q, hq, fun r hr ↦ hs.injective ?_⟩
  rw [cdf_eq_real] at *
  rw [cdf_eq_real, hr, hq]

end Percentile

section Symmetry

/-- **The mean of a symmetric law is its centre (ST-011).** If `μ` is a probability law on `ℝ` with integrable
identity that is unchanged by the reflection `x ↦ 2m - x` about `m`, its mean is `m`. -/
@[kb "openstaxintrostats2e" "§2.6, p. 115"]
theorem integral_eq_of_map_reflect (μ : Measure ℝ) [IsProbabilityMeasure μ] (m : ℝ)
    (hsymm : μ.map (fun x ↦ 2 * m - x) = μ) (hint : Integrable (fun x : ℝ ↦ x) μ) :
    ∫ x, x ∂μ = m := by
  have h1 : ∫ x, x ∂μ = ∫ x, (2 * m - x) ∂μ := by
    conv_lhs => rw [← hsymm]
    rw [integral_map (by fun_prop) (by fun_prop)]
  rw [integral_sub (integrable_const _) hint] at h1
  simp only [integral_const, probReal_univ, one_smul] at h1
  linarith

end Symmetry

end UndergradKB.Statistics
