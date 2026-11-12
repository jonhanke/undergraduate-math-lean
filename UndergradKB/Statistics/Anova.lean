import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Data

/-!
# One-way analysis of variance (OpenStax *Introductory Statistics 2e*, §13.2)

The data are a list `x : Fin n → ℝ` with a group label `g : Fin n → Fin k` for each observation.
-/

namespace UndergradKB.Statistics

open Finset

variable {n k : ℕ}

/-- The size `nⱼ` of group `j`. -/
def groupSize (g : Fin n → Fin k) (j : Fin k) : ℕ := (univ.filter fun i => g i = j).card

/-- The mean `x̄ⱼ` of group `j`. -/
noncomputable def groupMean (x : Fin n → ℝ) (g : Fin n → Fin k) (j : Fin k) : ℝ :=
  (∑ i ∈ univ.filter (fun i => g i = j), x i) / groupSize g j

/-- Between-group sum of squares `∑ⱼ nⱼ (x̄ⱼ - x̄)²`. -/
noncomputable def ssBetween (x : Fin n → ℝ) (g : Fin n → Fin k) : ℝ :=
  ∑ j, (groupSize g j : ℝ) * (groupMean x g j - mean x) ^ 2

/-- Within-group sum of squares `∑ᵢ (xᵢ - x̄_{g i})²`. -/
noncomputable def ssWithin (x : Fin n → ℝ) (g : Fin n → Fin k) : ℝ :=
  ∑ i, (x i - groupMean x g (g i)) ^ 2

/-- Mean square between groups, `SS_between / (k - 1)`. -/
noncomputable def msBetween (x : Fin n → ℝ) (g : Fin n → Fin k) : ℝ :=
  ssBetween x g / ((k : ℝ) - 1)

/-- Mean square within groups, `SS_within / (n - k)`. -/
noncomputable def msWithin (x : Fin n → ℝ) (g : Fin n → Fin k) : ℝ :=
  ssWithin x g / ((n : ℝ) - k)

/-- The `F` statistic `MS_between / MS_within`. -/
noncomputable def fStatistic (x : Fin n → ℝ) (g : Fin n → Fin k) : ℝ :=
  msBetween x g / msWithin x g

lemma sum_fiber_sub_groupMean (x : Fin n → ℝ) (g : Fin n → Fin k) (j : Fin k) :
    ∑ i ∈ univ.filter (fun i => g i = j), (x i - groupMean x g j) = 0 := by
  rcases Nat.eq_zero_or_pos (groupSize g j) with h0 | hpos
  · have : univ.filter (fun i => g i = j) = ∅ := Finset.card_eq_zero.1 h0
    rw [this]; simp
  · have hne : (groupSize g j : ℝ) ≠ 0 := by positivity
    rw [sum_sub_distrib, sum_const]
    unfold groupMean
    rw [nsmul_eq_mul]
    change _ - (groupSize g j : ℝ) * _ = _
    field_simp
    ring

lemma sum_cross_eq_zero (x : Fin n → ℝ) (g : Fin n → Fin k) (c : Fin k → ℝ) :
    ∑ i, (x i - groupMean x g (g i)) * c (g i) = 0 := by
  rw [← Finset.sum_fiberwise univ g]
  apply sum_eq_zero
  intro j _
  have : ∀ i ∈ univ.filter (fun i => g i = j),
      (x i - groupMean x g (g i)) * c (g i) = (x i - groupMean x g j) * c j := by
    intro i hi
    rw [(mem_filter.1 hi).2]
  rw [sum_congr rfl this, ← sum_mul, sum_fiber_sub_groupMean]
  simp

lemma sum_groupMean_sq (x : Fin n → ℝ) (g : Fin n → Fin k) :
    ∑ i, (groupMean x g (g i) - mean x) ^ 2 = ssBetween x g := by
  rw [← Finset.sum_fiberwise univ g]
  unfold ssBetween
  apply sum_congr rfl
  intro j _
  have : ∀ i ∈ univ.filter (fun i => g i = j),
      (groupMean x g (g i) - mean x) ^ 2 = (groupMean x g j - mean x) ^ 2 := by
    intro i hi
    rw [(mem_filter.1 hi).2]
  rw [sum_congr rfl this, sum_const, nsmul_eq_mul]
  rfl

/-- (ST-114) One-way decomposition of variation: total = between + within. -/
@[kb "openstaxintrostats2e" "§13.2, p. 691"]
theorem sumSqDev_eq_ssBetween_add_ssWithin (x : Fin n → ℝ) (g : Fin n → Fin k) :
    sumSqDev x = ssBetween x g + ssWithin x g := by
  have h : ∀ i, (x i - mean x) ^ 2 = (x i - groupMean x g (g i)) ^ 2
      + 2 * ((x i - groupMean x g (g i)) * (groupMean x g (g i) - mean x))
      + (groupMean x g (g i) - mean x) ^ 2 := by intro i; ring
  unfold sumSqDev
  simp only [h, sum_add_distrib, ← mul_sum]
  rw [sum_cross_eq_zero x g (fun j => groupMean x g j - mean x), sum_groupMean_sq]
  unfold ssWithin
  ring

end UndergradKB.Statistics
