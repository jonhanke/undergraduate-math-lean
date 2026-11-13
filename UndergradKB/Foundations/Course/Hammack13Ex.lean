import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import UndergradKB.Common

/-!
# Course layer: Hammack, Book of Proof, Chapter 13, worked examples
-/

namespace UndergradKB.Foundations.Course

/-- Hammack Example 13.1: in the epsilon-delta sense, `lim_{x→2} (3x + 4) = 10`. -/
@[kb "hammack2018" "Example 13.1, p. 260"]
theorem hammack_ex_13_1_limit_linear :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, 0 < |x - 2| → |x - 2| < δ →
      |(3 * x + 4) - 10| < ε := by
  intro ε hε
  refine ⟨ε / 3, by positivity, fun x _ hx => ?_⟩
  have : (3 * x + 4) - 10 = 3 * (x - 2) := by ring
  rw [this, abs_mul]
  norm_num
  linarith

/-- Hammack Example 13.2: in the epsilon-delta sense, `lim_{x→2} 5x^2 = 20`. -/
@[kb "hammack2018" "Example 13.2, p. 260"]
theorem hammack_ex_13_2_limit_quadratic :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, 0 < |x - 2| → |x - 2| < δ →
      |5 * x ^ 2 - 20| < ε := by
  intro ε hε
  refine ⟨min 1 (ε / 25), lt_min one_pos (by positivity), fun x _ hx => ?_⟩
  have h1 : |x - 2| < 1 := lt_of_lt_of_le hx (min_le_left _ _)
  have h2 : |x - 2| < ε / 25 := lt_of_lt_of_le hx (min_le_right _ _)
  have h3 : |x + 2| < 5 := by
    have := abs_lt.mp h1
    rw [abs_lt]
    constructor <;> linarith
  have : 5 * x ^ 2 - 20 = 5 * ((x - 2) * (x + 2)) := by ring
  rw [this, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5)]
  have h4 : |x - 2| * |x + 2| ≤ |x - 2| * 5 :=
    mul_le_mul_of_nonneg_left h3.le (abs_nonneg _)
  linarith

/-- Hammack Example 13.6: `lim_{x→1} (1/x - 1)/(1 - x) = 1`. -/
@[kb "hammack2018" "Example 13.6, p. 267"]
theorem hammack_ex_13_6_rational_limit :
    Filter.Tendsto (fun x : ℝ => (1 / x - 1) / (1 - x)) (nhdsWithin 1 {1}ᶜ) (nhds 1) := by
  have hinv : Filter.Tendsto (fun x : ℝ => 1 / x) (nhdsWithin 1 {1}ᶜ) (nhds 1) := by
    have := (tendsto_inv₀ (one_ne_zero : (1 : ℝ) ≠ 0)).mono_left
      (nhdsWithin_le_nhds (s := ({1}ᶜ : Set ℝ)))
    simpa using this
  refine hinv.congr' ?_
  have h0' : ∀ᶠ x : ℝ in nhds 1, x ≠ 0 := isOpen_ne.mem_nhds (one_ne_zero : (1 : ℝ) ≠ 0)
  have h0 : ∀ᶠ x : ℝ in nhdsWithin 1 {1}ᶜ, x ≠ 0 := h0'.filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, h0] with x hx1 hx0
  have hx1' : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  field_simp

/-- Hammack Example 13.8: the sequence `1 - 1/n` converges to 1 (epsilon-N form). -/
@[kb "hammack2018" "Example 13.8, p. 274"]
theorem hammack_ex_13_8_one_minus_inv :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N < n → |(1 - 1 / (n : ℝ)) - 1| < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, fun n hn => ?_⟩
  have hnN : (N : ℝ) < n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_trans (lt_trans (by positivity) hN) hnN
  have : (1 - 1 / (n : ℝ)) - 1 = -(1 / n) := by ring
  rw [this, abs_neg, abs_of_pos (by positivity), div_lt_iff₀ hnpos]
  have h1 : 1 / ε < n := lt_trans hN hnN
  rw [div_lt_iff₀ hε] at h1
  linarith

/-- Hammack Example 13.9: the sequence `(-1)^(n+1) (n+1)/n` has no limit. -/
@[kb "hammack2018" "Example 13.9, p. 275"]
theorem hammack_ex_13_9_alternating_diverges :
    ¬ ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => (-1 : ℝ) ^ (n + 1) * ((n + 1) / n))
      Filter.atTop (nhds L) := by
  rintro ⟨L, hL⟩
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hL.cauchySeq 2 (by norm_num)
  have hm := hN (N + 1) (by omega) (N + 2) (by omega)
  rw [Real.dist_eq] at hm
  set m : ℕ := N + 1 with hmdef
  have hmpos : (0 : ℝ) < m := by positivity
  have hsucc : ((N + 2 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast [hmdef]; ring
  have hpow : (-1 : ℝ) ^ (N + 2 + 1) = -((-1 : ℝ) ^ (m + 1)) := by
    rw [hmdef]; ring
  rw [hpow, hsucc] at hm
  have hu : ((m : ℝ) + 1) / m > 1 := by rw [gt_iff_lt, lt_div_iff₀ hmpos]; linarith
  have hv : ((m : ℝ) + 1 + 1) / ((m : ℝ) + 1) > 1 := by
    rw [gt_iff_lt, lt_div_iff₀ (by positivity)]; linarith
  have habs : |(-1 : ℝ) ^ (m + 1)| = 1 := by simp
  set e : ℝ := (-1 : ℝ) ^ (m + 1)
  have hdiff : e * ((m + 1) / m) - -e * ((m + 1 + 1) / (m + 1)) =
      e * (((m : ℝ) + 1) / m + ((m : ℝ) + 1 + 1) / ((m : ℝ) + 1)) := by ring
  have hm' : |e * (((m : ℝ) + 1) / m + ((m : ℝ) + 1 + 1) / ((m : ℝ) + 1))| < 2 := by
    rw [← hdiff]; exact hm
  rw [abs_mul, habs, one_mul, abs_of_pos (by linarith)] at hm'
  linarith

end UndergradKB.Foundations.Course
