import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.BigOperators
import UndergradKB.Statistics.Data

/-!
# Simple random sampling from a finite population

OpenStax *Introductory Statistics 2e*, §1.2 and §7.1. A simple random sample of size `n` from a population
`x : Fin N → ℝ` is a uniformly chosen `n`-element subset `S` of the `N` members. We model it by Mathlib's
`MeasureTheory.Measure.uniformOfFinset` on `Finset.powersetCard n univ`, and prove that every member is
equally likely to be chosen (probability `n/N`) and that the sample mean is an unbiased estimator of the
population mean.
-/

namespace UndergradKB.Statistics

open MeasureTheory Finset

variable {N n : ℕ}

/-- The law of a simple random sample of size `n` from a population of `N` members (indexed by `Fin N`): the
uniform law on the `n`-element subsets. -/
noncomputable def srsLaw (N n : ℕ) : Measure (Finset (Fin N)) :=
  Measure.uniformOfFinset (powersetCard n (univ : Finset (Fin N)))

/-- Number of `n`-subsets of `Fin N` containing a given member. -/
private lemma card_filter_mem (hn : 1 ≤ n) (i : Fin N) :
    (univ.powersetCard n |>.filter fun S : Finset (Fin N) ↦ i ∈ S).card = (N - 1).choose (n - 1) := by
  have h1 := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin N)).powersetCard n)
    (fun S : Finset (Fin N) ↦ i ∈ S)
  have h2 : (univ.powersetCard n |>.filter fun S : Finset (Fin N) ↦ i ∉ S) =
      ((univ : Finset (Fin N)).erase i).powersetCard n := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    constructor
    · rintro ⟨hc, hi⟩
      exact ⟨fun a ha ↦ Finset.mem_erase.2 ⟨fun h ↦ hi (h ▸ ha), Finset.mem_univ _⟩, hc⟩
    · rintro ⟨hs, hc⟩
      exact ⟨hc, fun hi ↦ by simpa using hs hi⟩
  rw [h2, Finset.card_powersetCard, Finset.card_powersetCard, Finset.card_erase_of_mem (mem_univ _),
    Finset.card_univ, Fintype.card_fin] at h1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rcases N with _ | M
  · exact Fin.elim0 i
  · simp only [Nat.add_sub_cancel] at h1 ⊢
    have hp : (M + 1).choose (m + 1) = M.choose m + M.choose (m + 1) := Nat.choose_succ_succ' M m
    omega

/-- **Every member is equally likely to be sampled (ST-001).** In a simple random sample of size `n` from a
population of `N` members (`1 ≤ n ≤ N`), each member belongs to the sample with probability `n/N`. -/
@[kb "openstaxintrostats2e" "§1.2, p. 21"]
theorem srsLaw_inclusion_prob (hn : 1 ≤ n) (hnN : n ≤ N) (i : Fin N) :
    (srsLaw N n).real {S | i ∈ S} = n / N := by
  classical
  have hN : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le hn hnN
  have hc : (0 : ℝ) < (N.choose n : ℝ) := by exact_mod_cast Nat.choose_pos hnN
  rw [Measure.real, srsLaw, Measure.uniformOfFinset_apply, ENNReal.toReal_div]
  simp only [Set.mem_setOf_eq]
  rw [card_filter_mem hn i, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  simp only [ENNReal.toReal_natCast]
  rw [div_eq_div_iff hc.ne' hN.ne']
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have := congrArg (Nat.cast : ℕ → ℝ) (Nat.add_one_mul_choose_eq M m)
  push_cast at this ⊢
  linarith

/-- The integral against the uniform law on a finset is the average over it. -/
private lemma integral_srsLaw (hnN : n ≤ N) (f : Finset (Fin N) → ℝ) :
    ∫ S, f S ∂srsLaw N n = ∑ S ∈ powersetCard n (univ : Finset (Fin N)),
      ((powersetCard n (univ : Finset (Fin N))).card : ℝ)⁻¹ * f S := by
  rw [srsLaw, Measure.uniformOfFinset, integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun S _ ↦ ?_
    rw [integral_smul_measure, integral_dirac]
    simp
  · intro S _
    exact (integrable_dirac (by simp)).smul_measure
      (by simp [Finset.card_powersetCard, (Nat.choose_pos hnN).ne'])

/-- **Unbiasedness of the sample mean (ST-063).** For a simple random sample `S` of size `n` (`1 ≤ n ≤ N`) from
a population `x`, the expected value of the sample mean `(∑_{i ∈ S} xᵢ)/n` is the population mean. -/
@[kb "openstaxintrostats2e" "§7.1, p. 378"]
theorem integral_srsLaw_sampleMean (hn : 1 ≤ n) (hnN : n ≤ N) (x : Fin N → ℝ) :
    ∫ S, (∑ i ∈ S, x i) / n ∂srsLaw N n = mean x := by
  classical
  have hN : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le hn hnN
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : (0 : ℝ) < (N.choose n : ℝ) := by exact_mod_cast Nat.choose_pos hnN
  rw [integral_srsLaw hnN, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hsum : ∑ S ∈ (univ : Finset (Fin N)).powersetCard n, (∑ i ∈ S, x i) =
      ((N - 1).choose (n - 1) : ℝ) * ∑ i, x i := by
    have : ∀ S : Finset (Fin N), ∑ i ∈ S, x i = ∑ i, if i ∈ S then x i else 0 := by
      intro S
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    simp_rw [this]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.sum_filter, Finset.sum_const, card_filter_mem hn i]
    simp [mul_comm]
  have hkey : (N : ℝ) * ((N - 1).choose (n - 1) : ℝ) = n * (N.choose n : ℝ) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    have := congrArg (Nat.cast : ℕ → ℝ) (Nat.add_one_mul_choose_eq M m)
    push_cast at this ⊢
    linarith
  simp_rw [div_eq_inv_mul, ← Finset.mul_sum, mul_left_comm _ (n : ℝ)⁻¹]
  rw [hsum, mean]
  field_simp
  linear_combination (∑ i, x i) * hkey

end UndergradKB.Statistics
