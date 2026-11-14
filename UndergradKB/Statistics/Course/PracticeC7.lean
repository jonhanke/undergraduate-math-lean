import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF
import UndergradKB.Common.Attr
import UndergradKB.Statistics.NormalCdf
import UndergradKB.Statistics.CriticalValues
import UndergradKB.Statistics.EmpiricalRule
import UndergradKB.Statistics.Continuous
import UndergradKB.Statistics.Inference
import UndergradKB.Statistics.Course.ExamplesC7

/-!
# "Practice" exercises, chapter 7 (OpenStax *Introductory Statistics 2e*): the central limit theorem

As in `ExamplesC7.lean` and `TryItC7.lean`, the normal approximation of the book is the hypothesis: the
sample mean (or sample sum) `X` has the normal law with the mean and variance the book computes
(`HasLaw X (gaussianReal μ v.toNNReal) P`).  Standard errors are exact or enclosed between two decimals;
every probability and percentile is enclosed between two bounds around the rounded value.  Values of the
standard normal distribution function `Φ` come from the alternating Taylor enclosures (`Phi_enc` of
`ExamplesC7.lean`); the bounds in each theorem are the ones the enclosures give, rounded outwards.

Skipped (no mathematical statement): Exercises 7.26, 7.27, 7.28 (verbal), and 7.38, 7.40, 7.42, 7.44,
7.46 (drawings of the graphs of Exercises 7.37, 7.39, 7.41, 7.43, 7.45).
-/

namespace UndergradKB.Statistics.Course.PracticeC7

open MeasureTheory ProbabilityTheory Set UndergradKB.Statistics
open UndergradKB.Statistics.Course.ExamplesC7

local notation "Φ" => cdf (gaussianReal 0 1)

macro "pc7_num" : tactic =>
  `(tactic| (simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial]))

/-! ### Values of `Φ` -/

private lemma t_0_2 : (0.57922 : ℝ) < Φ 0.2 ∧ Φ 0.2 < 0.57929 :=
  Phi_enc (by norm_num) 1 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_0_2083 : (0.58247 : ℝ) < Φ 0.2083 ∧ Φ 0.2083 < 0.58254 :=
  Phi_enc (by norm_num) 1 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_0_2084 : (0.58251 : ℝ) < Φ 0.2084 ∧ Φ 0.2084 < 0.58258 :=
  Phi_enc (by norm_num) 1 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_0_4166 : (0.66148 : ℝ) < Φ 0.4166 ∧ Φ 0.4166 < 0.66155 :=
  Phi_enc (by norm_num) 2 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_0_4167 : (0.66152 : ℝ) < Φ 0.4167 ∧ Φ 0.4167 < 0.66159 :=
  Phi_enc (by norm_num) 2 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_0_4274 : (0.66542 : ℝ) < Φ 0.4274 ∧ Φ 0.4274 < 0.66549 :=
  Phi_enc (by norm_num) 2 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_0_4275 : (0.66546 : ℝ) < Φ 0.4275 ∧ Φ 0.4275 < 0.66553 :=
  Phi_enc (by norm_num) 2 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_0_6743 : (0.7499 : ℝ) < Φ 0.6743 ∧ Φ 0.6743 < 0.74997 :=
  Phi_enc (by norm_num) 2 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_0_6744 : (0.74994 : ℝ) < Φ 0.6744 ∧ Φ 0.6744 < 0.75001 :=
  Phi_enc (by norm_num) 2 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_0_6745 : (0.74997 : ℝ) < Φ 0.6745 ∧ Φ 0.6745 < 0.75004 :=
  Phi_enc (by norm_num) 2 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_0_6746 : (0.75 : ℝ) < Φ 0.6746 ∧ Φ 0.6746 < 0.75007 :=
  Phi_enc (by norm_num) 2 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_0_6747 : (0.75003 : ℝ) < Φ 0.6747 ∧ Φ 0.6747 < 0.7501 :=
  Phi_enc (by norm_num) 2 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_0_8 : (0.78811 : ℝ) < Φ 0.8 ∧ Φ 0.8 < 0.78818 :=
  Phi_enc (by norm_num) 2 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_0_8333 : (0.79763 : ℝ) < Φ 0.8333 ∧ Φ 0.8333 < 0.7977 :=
  Phi_enc (by norm_num) 2 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_0_8334 : (0.79766 : ℝ) < Φ 0.8334 ∧ Φ 0.8334 < 0.79773 :=
  Phi_enc (by norm_num) 2 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_0_8414 : (0.7999 : ℝ) < Φ 0.8414 ∧ Φ 0.8414 < 0.79997 :=
  Phi_enc (by norm_num) 2 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_0_8415 : (0.79993 : ℝ) < Φ 0.8415 ∧ Φ 0.8415 < 0.8 :=
  Phi_enc (by norm_num) 2 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_0_8416 : (0.79996 : ℝ) < Φ 0.8416 ∧ Φ 0.8416 < 0.80003 :=
  Phi_enc (by norm_num) 2 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_0_8417 : (0.79999 : ℝ) < Φ 0.8417 ∧ Φ 0.8417 < 0.80006 :=
  Phi_enc (by norm_num) 2 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_0_8418 : (0.80002 : ℝ) < Φ 0.8418 ∧ Φ 0.8418 < 0.80009 :=
  Phi_enc (by norm_num) 3 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_1 : (0.84131 : ℝ) < Φ 1 ∧ Φ 1 < 0.84138 :=
  Phi_enc (by norm_num) 3 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_1_0362 : (0.84991 : ℝ) < Φ 1.0362 ∧ Φ 1.0362 < 0.84998 :=
  Phi_enc (by norm_num) 3 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_1_0363 : (0.84993 : ℝ) < Φ 1.0363 ∧ Φ 1.0363 < 0.85 :=
  Phi_enc (by norm_num) 3 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_1_0364 : (0.84996 : ℝ) < Φ 1.0364 ∧ Φ 1.0364 < 0.85003 :=
  Phi_enc (by norm_num) 3 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_1_0365 : (0.84998 : ℝ) < Φ 1.0365 ∧ Φ 1.0365 < 0.85005 :=
  Phi_enc (by norm_num) 3 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_1_0366 : (0.85 : ℝ) < Φ 1.0366 ∧ Φ 1.0366 < 0.85007 :=
  Phi_enc (by norm_num) 3 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_1_0367 : (0.85003 : ℝ) < Φ 1.0367 ∧ Φ 1.0367 < 0.8501 :=
  Phi_enc (by norm_num) 3 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_1_2813 : (0.89992 : ℝ) < Φ 1.2813 ∧ Φ 1.2813 < 0.89999 :=
  Phi_enc (by norm_num) 3 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_1_2814 : (0.89994 : ℝ) < Φ 1.2814 ∧ Φ 1.2814 < 0.90001 :=
  Phi_enc (by norm_num) 3 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_1_2815 : (0.89996 : ℝ) < Φ 1.2815 ∧ Φ 1.2815 < 0.90003 :=
  Phi_enc (by norm_num) 3 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_1_2816 : (0.89997 : ℝ) < Φ 1.2816 ∧ Φ 1.2816 < 0.90004 :=
  Phi_enc (by norm_num) 3 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_1_2817 : (0.89999 : ℝ) < Φ 1.2817 ∧ Φ 1.2817 < 0.90006 :=
  Phi_enc (by norm_num) 3 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_1_2818 : (0.90001 : ℝ) < Φ 1.2818 ∧ Φ 1.2818 < 0.90008 :=
  Phi_enc (by norm_num) 3 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_1_5 : (0.93316 : ℝ) < Φ 1.5 ∧ Φ 1.5 < 0.93323 :=
  Phi_enc (by norm_num) 4 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_1_5811 : (0.94304 : ℝ) < Φ 1.5811 ∧ Φ 1.5811 < 0.94311 :=
  Phi_enc (by norm_num) 4 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_1_5812 : (0.94305 : ℝ) < Φ 1.5812 ∧ Φ 1.5812 < 0.94312 :=
  Phi_enc (by norm_num) 4 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_1_6444 : (0.94992 : ℝ) < Φ 1.6444 ∧ Φ 1.6444 < 0.94999 :=
  Phi_enc (by norm_num) 4 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_1_6445 : (0.94993 : ℝ) < Φ 1.6445 ∧ Φ 1.6445 < 0.95 :=
  Phi_enc (by norm_num) 4 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_1_6446 : (0.94994 : ℝ) < Φ 1.6446 ∧ Φ 1.6446 < 0.95001 :=
  Phi_enc (by norm_num) 4 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_1_6447 : (0.94995 : ℝ) < Φ 1.6447 ∧ Φ 1.6447 < 0.95002 :=
  Phi_enc (by norm_num) 4 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_1_6448 : (0.94996 : ℝ) < Φ 1.6448 ∧ Φ 1.6448 < 0.95003 :=
  Phi_enc (by norm_num) 4 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_1_6449 : (0.94997 : ℝ) < Φ 1.6449 ∧ Φ 1.6449 < 0.95004 :=
  Phi_enc (by norm_num) 4 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_1_645 : (0.94998 : ℝ) < Φ 1.645 ∧ Φ 1.645 < 0.95005 :=
  Phi_enc (by norm_num) 4 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_1_6451 : (0.94999 : ℝ) < Φ 1.6451 ∧ Φ 1.6451 < 0.95006 :=
  Phi_enc (by norm_num) 4 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_1_6452 : (0.95 : ℝ) < Φ 1.6452 ∧ Φ 1.6452 < 0.95007 :=
  Phi_enc (by norm_num) 4 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_1_6453 : (0.95001 : ℝ) < Φ 1.6453 ∧ Φ 1.6453 < 0.95008 :=
  Phi_enc (by norm_num) 4 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_1_6666 : (0.95217 : ℝ) < Φ 1.6666 ∧ Φ 1.6666 < 0.95224 :=
  Phi_enc (by norm_num) 4 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_1_6667 : (0.95218 : ℝ) < Φ 1.6667 ∧ Φ 1.6667 < 0.95225 :=
  Phi_enc (by norm_num) 4 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_1_7099 : (0.95632 : ℝ) < Φ 1.7099 ∧ Φ 1.7099 < 0.95639 :=
  Phi_enc (by norm_num) 4 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_1_71 : (0.95633 : ℝ) < Φ 1.71 ∧ Φ 1.71 < 0.9564 :=
  Phi_enc (by norm_num) 4 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_1_732 : (0.95833 : ℝ) < Φ 1.732 ∧ Φ 1.732 < 0.9584 :=
  Phi_enc (by norm_num) 5 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_1_7321 : (0.95834 : ℝ) < Φ 1.7321 ∧ Φ 1.7321 < 0.95841 :=
  Phi_enc (by norm_num) 5 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_1_8 : (0.96403 : ℝ) < Φ 1.8 ∧ Φ 1.8 < 0.9641 :=
  Phi_enc (by norm_num) 5 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_2 : (0.97721 : ℝ) < Φ 2 ∧ Φ 2 < 0.97728 :=
  Phi_enc (by norm_num) 5 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_2_3717 : (0.99111 : ℝ) < Φ 2.3717 ∧ Φ 2.3717 < 0.99118 :=
  Phi_enc (by norm_num) 6 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_2_3718 : (0.99111 : ℝ) < Φ 2.3718 ∧ Φ 2.3718 < 0.99118 :=
  Phi_enc (by norm_num) 6 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_2_4 : (0.99177 : ℝ) < Φ 2.4 ∧ Φ 2.4 < 0.99184 :=
  Phi_enc (by norm_num) 7 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_2_4494 : (0.99281 : ℝ) < Φ 2.4494 ∧ Φ 2.4494 < 0.99288 :=
  Phi_enc (by norm_num) 7 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_2_4495 : (0.99281 : ℝ) < Φ 2.4495 ∧ Φ 2.4495 < 0.99288 :=
  Phi_enc (by norm_num) 7 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_3_464 : (0.9997 : ℝ) < Φ 3.464 ∧ Φ 3.464 < 0.99977 :=
  Phi_enc (by norm_num) 11 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_3_4642 : (0.9997 : ℝ) < Φ 3.4642 ∧ Φ 3.4642 < 0.99977 :=
  Phi_enc (by norm_num) 11 (by norm_num) (by pc7_num) (by pc7_num)

private lemma t_3_5 : (0.99973 : ℝ) < Φ 3.5 ∧ Φ 3.5 < 0.9998 :=
  Phi_enc (by norm_num) 11 (by norm_num) (by pc7_num) (by pc7_num)

/-! ### Helpers -/

section Helpers

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}

/-- A normal law with variance `v ≥ 0` has standard deviation `√v`. -/
private lemma law_sqrt {μ v : ℝ} (hv : 0 ≤ v) (hX : HasLaw X (gaussianReal μ v.toNNReal) P) :
    HasLaw X (gaussianReal μ ((Real.sqrt v) ^ 2).toNNReal) P := by
  rwa [Real.sq_sqrt hv]

private lemma sq_exact {n r : ℝ} (hr : 0 ≤ r) (h : r * r = n) : Real.sqrt n = r := by
  rw [← h]; exact Real.sqrt_mul_self hr

/-- `c / σ` lies between `lo` and `hi` when `σ` lies between `s1` and `s2`. -/
private lemma div_enc {c σ s1 s2 lo hi : ℝ} (hs : 0 < s1 ∧ s1 ≤ σ ∧ σ ≤ s2) (hlo0 : 0 ≤ lo)
    (hlo : lo * s2 ≤ c) (hhi : c ≤ hi * s1) : lo ≤ c / σ ∧ c / σ ≤ hi := by
  obtain ⟨h0, h1, h2⟩ := hs
  have hσ : 0 < σ := by linarith
  have hc : 0 ≤ c := le_trans (mul_nonneg hlo0 (by linarith)) hlo
  have hhi0 : 0 ≤ hi := by
    by_contra h
    replace h := not_le.1 h
    nlinarith
  constructor
  · rw [le_div_iff₀ hσ]; nlinarith [mul_nonneg hlo0 (sub_nonneg.2 h2)]
  · rw [div_le_iff₀ hσ]; nlinarith [mul_nonneg hhi0 (sub_nonneg.2 h1)]

private lemma Phi_enc2 {c σ s1 s2 lo hi L U : ℝ} (hs : 0 < s1 ∧ s1 ≤ σ ∧ σ ≤ s2) (hlo0 : 0 ≤ lo)
    (hlo : lo * s2 ≤ c) (hhi : c ≤ hi * s1) (hL : L < Φ lo) (hU : Φ hi < U) :
    L < Φ (c / σ) ∧ Φ (c / σ) < U :=
  Phi_between (div_enc hs hlo0 hlo hhi).1 (div_enc hs hlo0 hlo hhi).2 hL hU

private lemma sd_pos {σ s1 s2 : ℝ} (hs : 0 < s1 ∧ s1 ≤ σ ∧ σ ≤ s2) : 0 < σ := by
  linarith [hs.1, hs.2.1]

/-- Right tail `P(X > x)` with `x` above the mean: `1 - Φ(c/σ)` with `c = x - μ`. -/
private lemma right_tail {μ σ s1 s2 x c lo hi L U : ℝ}
    (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) (hs : 0 < s1 ∧ s1 ≤ σ ∧ σ ≤ s2)
    (hc : x - μ = c) (hlo0 : 0 ≤ lo) (hlo : lo * s2 ≤ c) (hhi : c ≤ hi * s1) (hL : L < Φ lo)
    (hU : Φ hi < U) : 1 - U < P.real {ω | x < X ω} ∧ P.real {ω | x < X ω} < 1 - L := by
  rw [prob_gt (sd_pos hs) hX x, hc]
  have h := Phi_enc2 hs hlo0 hlo hhi hL hU
  constructor <;> linarith [h.1, h.2]

private lemma right_tail_ge {μ σ s1 s2 x c lo hi L U : ℝ}
    (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) (hs : 0 < s1 ∧ s1 ≤ σ ∧ σ ≤ s2)
    (hc : x - μ = c) (hlo0 : 0 ≤ lo) (hlo : lo * s2 ≤ c) (hhi : c ≤ hi * s1) (hL : L < Φ lo)
    (hU : Φ hi < U) : 1 - U < P.real {ω | x ≤ X ω} ∧ P.real {ω | x ≤ X ω} < 1 - L := by
  rw [prob_ge (sd_pos hs) hX x, hc]
  have h := Phi_enc2 hs hlo0 hlo hhi hL hU
  constructor <;> linarith [h.1, h.2]

/-- Left tail `P(X < x)` with `x` below the mean: `1 - Φ(c/σ)` with `c = μ - x`. -/
private lemma left_tail {μ σ s1 s2 x c lo hi L U : ℝ}
    (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) (hs : 0 < s1 ∧ s1 ≤ σ ∧ σ ≤ s2)
    (hc : μ - x = c) (hlo0 : 0 ≤ lo) (hlo : lo * s2 ≤ c) (hhi : c ≤ hi * s1) (hL : L < Φ lo)
    (hU : Φ hi < U) : 1 - U < P.real {ω | X ω < x} ∧ P.real {ω | X ω < x} < 1 - L := by
  rw [prob_lt (sd_pos hs) hX x]
  have e : x - μ = -c := by linarith
  rw [e, neg_div, stdNormalCdf_neg]
  have h := Phi_enc2 hs hlo0 hlo hhi hL hU
  constructor <;> linarith [h.1, h.2]

private lemma left_tail_le {μ σ s1 s2 x c lo hi L U : ℝ}
    (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) (hs : 0 < s1 ∧ s1 ≤ σ ∧ σ ≤ s2)
    (hc : μ - x = c) (hlo0 : 0 ≤ lo) (hlo : lo * s2 ≤ c) (hhi : c ≤ hi * s1) (hL : L < Φ lo)
    (hU : Φ hi < U) : 1 - U < P.real {ω | X ω ≤ x} ∧ P.real {ω | X ω ≤ x} < 1 - L := by
  rw [prob_le_normal (sd_pos hs) hX x]
  have e : x - μ = -c := by linarith
  rw [e, neg_div, stdNormalCdf_neg]
  have h := Phi_enc2 hs hlo0 hlo hhi hL hU
  constructor <;> linarith [h.1, h.2]

/-- Right tail `P(X > x)` with `x` below the mean: `Φ(c/σ)` with `c = μ - x`. -/
private lemma right_tail_b {μ σ s1 s2 x c lo hi L U : ℝ}
    (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) (hs : 0 < s1 ∧ s1 ≤ σ ∧ σ ≤ s2)
    (hc : μ - x = c) (hlo0 : 0 ≤ lo) (hlo : lo * s2 ≤ c) (hhi : c ≤ hi * s1) (hL : L < Φ lo)
    (hU : Φ hi < U) : L < P.real {ω | x < X ω} ∧ P.real {ω | x < X ω} < U := by
  rw [prob_gt (sd_pos hs) hX x]
  have e : x - μ = -c := by linarith
  rw [e, neg_div, stdNormalCdf_neg]
  have h := Phi_enc2 hs hlo0 hlo hhi hL hU
  constructor <;> linarith [h.1, h.2]

/-- Left tail `P(X < x)` with `x` above the mean: `Φ(c/σ)` with `c = x - μ`. -/
private lemma left_tail_b {μ σ s1 s2 x c lo hi L U : ℝ}
    (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) (hs : 0 < s1 ∧ s1 ≤ σ ∧ σ ≤ s2)
    (hc : x - μ = c) (hlo0 : 0 ≤ lo) (hlo : lo * s2 ≤ c) (hhi : c ≤ hi * s1) (hL : L < Φ lo)
    (hU : Φ hi < U) : L < P.real {ω | X ω < x} ∧ P.real {ω | X ω < x} < U := by
  rw [prob_lt (sd_pos hs) hX x, hc]
  exact Phi_enc2 hs hlo0 hlo hhi hL hU

/-- `P(a < X < b)` with `a` below and `b` above the mean. -/
private lemma straddle {μ σ s1 s2 a b c1 c2 lo1 hi1 lo2 hi2 L1 U1 L2 U2 : ℝ}
    (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) (hs : 0 < s1 ∧ s1 ≤ σ ∧ σ ≤ s2)
    (hc1 : μ - a = c1) (hc2 : b - μ = c2) (hlo10 : 0 ≤ lo1) (hlo1 : lo1 * s2 ≤ c1)
    (hhi1 : c1 ≤ hi1 * s1) (hlo20 : 0 ≤ lo2) (hlo2 : lo2 * s2 ≤ c2) (hhi2 : c2 ≤ hi2 * s1)
    (hL1 : L1 < Φ lo1) (hU1 : Φ hi1 < U1) (hL2 : L2 < Φ lo2) (hU2 : Φ hi2 < U2) :
    L1 + L2 - 1 < P.real {ω | a < X ω ∧ X ω < b} ∧
      P.real {ω | a < X ω ∧ X ω < b} < U1 + U2 - 1 := by
  have hs0 := hs.1
  have hn1 : 0 ≤ c1 := le_trans (mul_nonneg hlo10 (by linarith [hs.2.1, hs.2.2])) hlo1
  have hn2 : 0 ≤ c2 := le_trans (mul_nonneg hlo20 (by linarith [hs.2.1, hs.2.2])) hlo2
  rw [prob_Ioo (sd_pos hs) hX (a := a) (b := b) (by linarith)]
  have e : a - μ = -c1 := by linarith
  rw [e, hc2, neg_div, stdNormalCdf_neg]
  have h1 := Phi_enc2 hs hlo10 hlo1 hhi1 hL1 hU1
  have h2 := Phi_enc2 hs hlo20 hlo2 hhi2 hL2 hU2
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- `P(μ - aσ < X < μ + bσ) = Φ(a) + Φ(b) - 1` for a normal variable and `a, b ≥ 0`. -/
private lemma between_z {μ σ a b L1 U1 L2 U2 : ℝ}
    (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) (hσ : 0 < σ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hL1 : L1 < Φ a) (hU1 : Φ a < U1) (hL2 : L2 < Φ b) (hU2 : Φ b < U2) :
    L1 + L2 - 1 < P.real {ω | μ - a * σ < X ω ∧ X ω < μ + b * σ} ∧
      P.real {ω | μ - a * σ < X ω ∧ X ω < μ + b * σ} < U1 + U2 - 1 := by
  rw [prob_Ioo hσ hX (a := μ - a * σ) (b := μ + b * σ) (by nlinarith)]
  have e1 : (μ + b * σ - μ) / σ = b := by field_simp; ring
  have e2 : (μ - a * σ - μ) / σ = -a := by field_simp; ring
  rw [e1, e2, stdNormalCdf_neg]
  constructor <;> linarith

/-- Percentile above the median: `Φ lo < p < Φ hi` pins `k` between `μ + s1 lo` and `μ + s2 hi`. -/
private lemma pct_hi {μ σ s1 s2 p lo hi k : ℝ}
    (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) (hs : 0 < s1 ∧ s1 ≤ σ ∧ σ ≤ s2)
    (hlo0 : 0 ≤ lo) (hp0 : 0 < p) (hp1 : p < 1) (hl : Φ lo < p) (hh : p < Φ hi)
    (hk : P.real {ω | X ω ≤ k} = p) : μ + s1 * lo < k ∧ k < μ + s2 * hi := by
  have hσ := sd_pos hs
  have hlh : lo ≤ hi := by
    by_contra h
    replace h := not_le.1 h
    have := Phi_mono h.le
    linarith
  obtain ⟨k', hk', h1', h2'⟩ := percentile_bd hσ hX hp0 hp1 hl hh
  have e : k = k' := ((normal_percentile hσ hX hp0 hp1).2 k hk).trans
    ((normal_percentile hσ hX hp0 hp1).2 k' hk').symm
  rw [e]
  have hhi0 : 0 ≤ hi := le_trans hlo0 hlh
  constructor
  · nlinarith [mul_nonneg hlo0 (sub_nonneg.2 hs.2.1)]
  · nlinarith [mul_nonneg hhi0 (sub_nonneg.2 hs.2.2)]

/-- Percentile below the median: `Φ lo < 1 - p < Φ hi` pins `k` between `μ - s2 hi` and
`μ - s1 lo`. -/
private lemma pct_lo {μ σ s1 s2 p lo hi k : ℝ}
    (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) (hs : 0 < s1 ∧ s1 ≤ σ ∧ σ ≤ s2)
    (hlo0 : 0 ≤ lo) (hp0 : 0 < p) (hp1 : p < 1) (hl : Φ lo < 1 - p) (hh : 1 - p < Φ hi)
    (hk : P.real {ω | X ω ≤ k} = p) : μ - s2 * hi < k ∧ k < μ - s1 * lo := by
  have hσ := sd_pos hs
  have hlh : lo ≤ hi := by
    by_contra h
    replace h := not_le.1 h
    have := Phi_mono h.le
    linarith
  have hl' : Φ (-hi) < p := by rw [stdNormalCdf_neg]; linarith
  have hh' : p < Φ (-lo) := by rw [stdNormalCdf_neg]; linarith
  obtain ⟨k', hk', h1', h2'⟩ := percentile_bd hσ hX hp0 hp1 hl' hh'
  have e : k = k' := ((normal_percentile hσ hX hp0 hp1).2 k hk).trans
    ((normal_percentile hσ hX hp0 hp1).2 k' hk').symm
  rw [e]
  have hhi0 : 0 ≤ hi := le_trans hlo0 hlh
  constructor
  · nlinarith [mul_nonneg hhi0 (sub_nonneg.2 hs.2.2)]
  · nlinarith [mul_nonneg hlo0 (sub_nonneg.2 hs.2.1)]

end Helpers

section Settings

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}

/-! ### The laws of the exercises' settings -/

private lemma law_y1 (hX : HasLaw X (gaussianReal 4 ((1.2 : ℝ) ^ 2).toNNReal) P) :
    HasLaw X (gaussianReal 4 ((1.2 : ℝ) ^ 2).toNNReal) P := hX

private lemma sdb_y1 : 0 < (1.2 : ℝ) ∧ (1.2 : ℝ) ≤ 1.2 ∧ (1.2 : ℝ) ≤ 1.2 :=
  ⟨by norm_num, le_rfl, le_rfl⟩

private lemma law_y16 (hX : HasLaw X (gaussianReal 4 ((1.2 ^ 2 / 16 : ℝ).toNNReal)) P) :
    HasLaw X (gaussianReal 4 ((1.2 / Real.sqrt 16) ^ 2).toNNReal) P :=
  law_mean (s := 1.2) (n := 16) (by norm_num) hX

private lemma sdv_y16 : (1.2 / Real.sqrt 16 : ℝ) = 0.3 := by
  rw [sq_exact (n := (16 : ℝ)) (r := 4) (by norm_num) (by norm_num)]; norm_num

private lemma sdb_y16 : 0 < (0.3 : ℝ) ∧ (0.3 : ℝ) ≤ 1.2 / Real.sqrt 16 ∧ 1.2 / Real.sqrt 16 ≤ (0.3 : ℝ) := by
  rw [sdv_y16]; norm_num

private lemma law_s95 (hX : HasLaw X (gaussianReal (95 * 80) ((95 * 12 ^ 2 : ℝ).toNNReal)) P) :
    HasLaw X (gaussianReal 7600 ((Real.sqrt 95 * 12) ^ 2).toNNReal) P := by
  have h := law_sum (s := 12) (n := 95) (by norm_num) hX
  rwa [show (95 * 80 : ℝ) = 7600 by norm_num] at h

private lemma sdb_s95 : 0 < (116.961528 : ℝ) ∧ (116.961528 : ℝ) ≤ Real.sqrt 95 * 12 ∧ Real.sqrt 95 * 12 ≤ (116.96154 : ℝ) := by
  have hs := sqrt_bd (n := (95 : ℝ)) (a := 9.746794) (b := 9.746795) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  refine ⟨by norm_num, by linarith [hs.1], by linarith [hs.2]⟩

private lemma law_c40 (hX : HasLaw X (gaussianReal (40 * 180) ((40 * 20 ^ 2 : ℝ).toNNReal)) P) :
    HasLaw X (gaussianReal 7200 ((Real.sqrt 40 * 20) ^ 2).toNNReal) P := by
  have h := law_sum (s := 20) (n := 40) (by norm_num) hX
  rwa [show (40 * 180 : ℝ) = 7200 by norm_num] at h

private lemma sdb_c40 : 0 < (126.4911 : ℝ) ∧ (126.4911 : ℝ) ≤ Real.sqrt 40 * 20 ∧ Real.sqrt 40 * 20 ≤ (126.49112 : ℝ) := by
  have hs := sqrt_bd (n := (40 : ℝ)) (a := 6.324555) (b := 6.324556) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  refine ⟨by norm_num, by linarith [hs.1], by linarith [hs.2]⟩

private lemma law_c100 (hX : HasLaw X (gaussianReal (100 * 39.01) ((100 * 0.5 ^ 2 : ℝ).toNNReal)) P) :
    HasLaw X (gaussianReal 3901 ((Real.sqrt 100 * 0.5) ^ 2).toNNReal) P := by
  have h := law_sum (s := 0.5) (n := 100) (by norm_num) hX
  rwa [show (100 * 39.01 : ℝ) = 3901 by norm_num] at h

private lemma sdv_c100 : (Real.sqrt 100 * 0.5 : ℝ) = 5 := by
  rw [sq_exact (n := (100 : ℝ)) (r := 10) (by norm_num) (by norm_num)]; norm_num

private lemma sdb_c100 : 0 < (5 : ℝ) ∧ (5 : ℝ) ≤ Real.sqrt 100 * 0.5 ∧ Real.sqrt 100 * 0.5 ≤ (5 : ℝ) := by
  rw [sdv_c100]; norm_num

private lemma law_k25 (hX : HasLaw X (gaussianReal (25 * 12) ((25 * 1 ^ 2 : ℝ).toNNReal)) P) :
    HasLaw X (gaussianReal 300 ((Real.sqrt 25 * 1) ^ 2).toNNReal) P := by
  have h := law_sum (s := 1) (n := 25) (by norm_num) hX
  rwa [show (25 * 12 : ℝ) = 300 by norm_num] at h

private lemma sdv_k25 : (Real.sqrt 25 * 1 : ℝ) = 5 := by
  rw [sq_exact (n := (25 : ℝ)) (r := 5) (by norm_num) (by norm_num)]; norm_num

private lemma sdb_k25 : 0 < (5 : ℝ) ∧ (5 : ℝ) ≤ Real.sqrt 25 * 1 ∧ Real.sqrt 25 * 1 ≤ (5 : ℝ) := by
  rw [sdv_k25]; norm_num

private lemma law_m400 (hX : HasLaw X (gaussianReal (400 * 3) ((400 * 0.7 ^ 2 : ℝ).toNNReal)) P) :
    HasLaw X (gaussianReal 1200 ((Real.sqrt 400 * 0.7) ^ 2).toNNReal) P := by
  have h := law_sum (s := 0.7) (n := 400) (by norm_num) hX
  rwa [show (400 * 3 : ℝ) = 1200 by norm_num] at h

private lemma sdv_m400 : (Real.sqrt 400 * 0.7 : ℝ) = 14 := by
  rw [sq_exact (n := (400 : ℝ)) (r := 20) (by norm_num) (by norm_num)]; norm_num

private lemma sdb_m400 : 0 < (14 : ℝ) ∧ (14 : ℝ) ≤ Real.sqrt 400 * 0.7 ∧ Real.sqrt 400 * 0.7 ≤ (14 : ℝ) := by
  rw [sdv_m400]; norm_num

private lemma law_n100 (hX : HasLaw X (gaussianReal (100 * 100) ((100 * 100 ^ 2 : ℝ).toNNReal)) P) :
    HasLaw X (gaussianReal 10000 ((Real.sqrt 100 * 100) ^ 2).toNNReal) P := by
  have h := law_sum (s := 100) (n := 100) (by norm_num) hX
  rwa [show (100 * 100 : ℝ) = 10000 by norm_num] at h

private lemma sdv_n100 : (Real.sqrt 100 * 100 : ℝ) = 1000 := by
  rw [sq_exact (n := (100 : ℝ)) (r := 10) (by norm_num) (by norm_num)]; norm_num

private lemma sdb_n100 : 0 < (1000 : ℝ) ∧ (1000 : ℝ) ≤ Real.sqrt 100 * 100 ∧ Real.sqrt 100 * 100 ≤ (1000 : ℝ) := by
  rw [sdv_n100]; norm_num

private lemma law_w100 (hX : HasLaw X (gaussianReal (25) ((2 ^ 2 / 12 / 100 : ℝ).toNNReal)) P) :
    HasLaw X (gaussianReal 25 ((Real.sqrt (2 ^ 2 / 12 / 100)) ^ 2).toNNReal) P := by
  exact law_sqrt (by norm_num) hX

private lemma sdb_w100 : 0 < (0.057735 : ℝ) ∧ (0.057735 : ℝ) ≤ Real.sqrt (2 ^ 2 / 12 / 100) ∧ Real.sqrt (2 ^ 2 / 12 / 100) ≤ (0.057736 : ℝ) := by
  have hs := sqrt_bd (n := (2 ^ 2 / 12 / 100 : ℝ)) (a := 0.057735) (b := 0.057736) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  exact ⟨by norm_num, hs.1.le, hs.2.le⟩

private lemma law_ws100 (hX : HasLaw X (gaussianReal (100 * 25) ((100 * (2 ^ 2 / 12) : ℝ).toNNReal)) P) :
    HasLaw X (gaussianReal 2500 ((Real.sqrt (100 * (2 ^ 2 / 12))) ^ 2).toNNReal) P := by
  rw [show (100 * 25 : ℝ) = 2500 by norm_num] at hX
  exact law_sqrt (by norm_num) hX

private lemma sdb_ws100 : 0 < (5.773502 : ℝ) ∧ (5.773502 : ℝ) ≤ Real.sqrt (100 * (2 ^ 2 / 12)) ∧ Real.sqrt (100 * (2 ^ 2 / 12)) ≤ (5.773503 : ℝ) := by
  have hs := sqrt_bd (n := (100 * (2 ^ 2 / 12) : ℝ)) (a := 5.773502) (b := 5.773503) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  exact ⟨by norm_num, hs.1.le, hs.2.le⟩

private lemma law_e64m (hX : HasLaw X (gaussianReal 10 ((10 ^ 2 / 64 : ℝ).toNNReal)) P) :
    HasLaw X (gaussianReal 10 ((10 / Real.sqrt 64) ^ 2).toNNReal) P :=
  law_mean (s := 10) (n := 64) (by norm_num) hX

private lemma sdv_e64m : (10 / Real.sqrt 64 : ℝ) = 1.25 := by
  rw [sq_exact (n := (64 : ℝ)) (r := 8) (by norm_num) (by norm_num)]; norm_num

private lemma sdb_e64m : 0 < (1.25 : ℝ) ∧ (1.25 : ℝ) ≤ 10 / Real.sqrt 64 ∧ 10 / Real.sqrt 64 ≤ (1.25 : ℝ) := by
  rw [sdv_e64m]; norm_num

private lemma law_e64s (hX : HasLaw X (gaussianReal (64 * 10) ((64 * 10 ^ 2 : ℝ).toNNReal)) P) :
    HasLaw X (gaussianReal 640 ((Real.sqrt 64 * 10) ^ 2).toNNReal) P := by
  have h := law_sum (s := 10) (n := 64) (by norm_num) hX
  rwa [show (64 * 10 : ℝ) = 640 by norm_num] at h

private lemma sdv_e64s : (Real.sqrt 64 * 10 : ℝ) = 80 := by
  rw [sq_exact (n := (64 : ℝ)) (r := 8) (by norm_num) (by norm_num)]; norm_num

private lemma sdb_e64s : 0 < (80 : ℝ) ∧ (80 : ℝ) ≤ Real.sqrt 64 * 10 ∧ Real.sqrt 64 * 10 ≤ (80 : ℝ) := by
  rw [sdv_e64s]; norm_num

private lemma law_u50 (hX : HasLaw X (gaussianReal (50 * 8) ((50 * ((10 - 6) ^ 2 / 12) : ℝ).toNNReal)) P) :
    HasLaw X (gaussianReal 400 ((Real.sqrt (50 * ((10 - 6) ^ 2 / 12))) ^ 2).toNNReal) P := by
  rw [show (50 * 8 : ℝ) = 400 by norm_num] at hX
  exact law_sqrt (by norm_num) hX

private lemma sdb_u50 : 0 < (8.164965 : ℝ) ∧ (8.164965 : ℝ) ≤ Real.sqrt (50 * ((10 - 6) ^ 2 / 12)) ∧ Real.sqrt (50 * ((10 - 6) ^ 2 / 12)) ≤ (8.164966 : ℝ) := by
  have hs := sqrt_bd (n := (50 * ((10 - 6) ^ 2 / 12) : ℝ)) (a := 8.164965) (b := 8.164966) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  exact ⟨by norm_num, hs.1.le, hs.2.le⟩


/-! ### Exercises -/

/-- OpenStax Introductory Statistics 2e Practice exercise 7.1. Yoonie's reviews take 4 hours on average with population standard deviation 1.2 hours, and a month's sample has 16 reviews; the standard deviation of the mean time is the population one divided by the square root of the sample size, 0.3 hours. -/
@[kb "openstaxintrostats2e" "Exercise 7.1, p. 401"]
theorem ex_7_1_yoonie_standard_error :
    (1.2 : ℝ) / Real.sqrt 16 = 0.3 := by
  rw [sq_exact (n := (16 : ℝ)) (r := 4) (by norm_num) (by norm_num)]; norm_num


/-- OpenStax Introductory Statistics 2e Practice exercise 7.2. A mean time with the normal law of mean 4 and variance `1.2² / 16` has the normal law of mean 4 and standard deviation 0.3, i.e. `N(4, 0.3²)`, which is the distribution of the monthly mean in part (b). -/
@[kb "openstaxintrostats2e" "Exercise 7.2, p. 401"]
theorem ex_7_2_yoonie_distribution_of_mean :
    HasLaw X (gaussianReal 4 ((1.2 ^ 2 / 16 : ℝ).toNNReal)) P ↔
      HasLaw X (gaussianReal 4 (((0.3 : ℝ)) ^ 2).toNNReal) P := by
  rw [show ((1.2 : ℝ) ^ 2 / 16) = 0.3 ^ 2 by norm_num]


/-- OpenStax Introductory Statistics 2e Practice exercise 7.3. A single review time is normal with mean 4 and standard deviation 1.2 hours. The probability that it lies between 3.5 and 4.25 hours is enclosed in (0.243, 0.245). -/
@[kb "openstaxintrostats2e" "Exercise 7.3, p. 401"]
theorem ex_7_3_one_review_between (hX : HasLaw X (gaussianReal 4 ((1.2 : ℝ) ^ 2).toNNReal) P) :
    0.243 < P.real {ω | 3.5 < X ω ∧ X ω < 4.25} ∧ P.real {ω | 3.5 < X ω ∧ X ω < 4.25} < 0.245 := by
  have h := straddle (law_y1 hX) sdb_y1 (a := 3.5) (b := 4.25) (c1 := 0.5) (c2 := 0.25)
    (lo1 := 0.4166) (hi1 := 0.4167) (lo2 := 0.2083) (hi2 := 0.2084)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) t_0_4166.1 t_0_4167.2 t_0_2083.1 t_0_2084.2
  constructor <;> linarith [h.1, h.2]


/-- OpenStax Introductory Statistics 2e Practice exercise 7.4. The mean of the 16 reviews of a month has the normal law with mean 4 and standard deviation `1.2/√16 = 0.3`. The probability that it lies between 3.5 and 4.25 hours is enclosed in (0.749, 0.75). -/
@[kb "openstaxintrostats2e" "Exercise 7.4, p. 401"]
theorem ex_7_4_mean_of_reviews_between (hX : HasLaw X (gaussianReal 4 ((1.2 ^ 2 / 16 : ℝ).toNNReal)) P) :
    0.749 < P.real {ω | 3.5 < X ω ∧ X ω < 4.25} ∧ P.real {ω | 3.5 < X ω ∧ X ω < 4.25} < 0.75 := by
  have h := straddle (law_y16 hX) sdb_y16 (a := 3.5) (b := 4.25) (c1 := 0.5) (c2 := 0.25)
    (lo1 := 1.6666) (hi1 := 1.6667) (lo2 := 0.8333) (hi2 := 0.8334)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) t_1_6666.1 t_1_6667.2 t_0_8333.1 t_0_8334.2
  constructor <;> linarith [h.1, h.2]


/-- OpenStax Introductory Statistics 2e Practice exercise 7.5. The two probabilities of Exercises 7.3 and 7.4 differ because the mean of 16 reviews has a smaller standard deviation than one review: `1.2/√16 = 0.3 < 1.2`. -/
@[kb "openstaxintrostats2e" "Exercise 7.5, p. 401"]
theorem ex_7_5_mean_has_smaller_spread :
    (1.2 : ℝ) / Real.sqrt 16 < 1.2 := by
  rw [sq_exact (n := (16 : ℝ)) (r := 4) (by norm_num) (by norm_num)]; norm_num


/-- OpenStax Introductory Statistics 2e Practice exercise 7.6. The mean of Yoonie's 16 reviews has the normal law with mean 4 and standard deviation 0.3. Any 95th percentile `k` of it lies in (4.493, 4.494) hours (about 4.49). -/
@[kb "openstaxintrostats2e" "Exercise 7.6, p. 401"]
theorem ex_7_6_mean_percentile_95 (hX : HasLaw X (gaussianReal 4 ((1.2 ^ 2 / 16 : ℝ).toNNReal)) P) {k : ℝ}
    (hk : P.real {ω | X ω ≤ k} = 19 / 20) :
    4.493 < k ∧ k < 4.494 := by
  have h := pct_hi (law_y16 hX) sdb_y16 (lo := 1.6444) (hi := 1.6453) (by norm_num) (by norm_num) (by norm_num)
    (lt_of_lt_of_le t_1_6444.2 (by norm_num)) (lt_of_le_of_lt (by norm_num) t_1_6453.1) hk
  constructor <;> linarith [h.1, h.2]


/-- OpenStax Introductory Statistics 2e Practice exercise 7.7. The sum of 95 values from a population with mean 80 and standard deviation 12 has the normal law with mean 7600 and variance `95 · 12²`. The probability that it exceeds 7650 is enclosed in (0.3344, 0.3346). -/
@[kb "openstaxintrostats2e" "Exercise 7.7, p. 402"]
theorem ex_7_7_sum_above_7650 (hX : HasLaw X (gaussianReal (95 * 80) ((95 * 12 ^ 2 : ℝ).toNNReal)) P) :
    0.3344 < P.real {ω | 7650 < X ω} ∧ P.real {ω | 7650 < X ω} < 0.3346 := by
  have h := right_tail (law_s95 hX) sdb_s95 (x := 7650) (c := 50) (lo := 0.4274) (hi := 0.4275)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) t_0_4274.1 t_0_4275.2
  constructor <;> linarith [h.1, h.2]


/-- OpenStax Introductory Statistics 2e Practice exercise 7.8. For the same sum of 95 values (normal law, mean 7600, standard deviation `12 √95`), the probability that it is below 7400 is enclosed in (0.0436, 0.0437). -/
@[kb "openstaxintrostats2e" "Exercise 7.8, p. 402"]
theorem ex_7_8_sum_below_7400 (hX : HasLaw X (gaussianReal (95 * 80) ((95 * 12 ^ 2 : ℝ).toNNReal)) P) :
    0.0436 < P.real {ω | X ω < 7400} ∧ P.real {ω | X ω < 7400} < 0.0437 := by
  have h := left_tail (law_s95 hX) sdb_s95 (x := 7400) (c := 200) (lo := 1.7099) (hi := 1.71)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) t_1_7099.1 t_1_71.2
  constructor <;> linarith [h.1, h.2]


/-- OpenStax Introductory Statistics 2e Practice exercise 7.9. For the sum of 95 values (mean `95 · 80`, standard deviation `12 √95`), the sum two standard deviations above the mean lies in (7833.92, 7833.93). -/
@[kb "openstaxintrostats2e" "Exercise 7.9, p. 402"]
theorem ex_7_9_sum_two_sd_above :
    7833.92 < 95 * 80 + 2 * (Real.sqrt 95 * 12) ∧ 95 * 80 + 2 * (Real.sqrt 95 * 12) < 7833.93 := by
  obtain ⟨h0, h1, h2⟩ := sdb_s95
  constructor <;> linarith


/-- OpenStax Introductory Statistics 2e Practice exercise 7.10. For the same sum of 95 values, the sum one and a half standard deviations below the mean lies in (7424.55, 7424.56). -/
@[kb "openstaxintrostats2e" "Exercise 7.10, p. 402"]
theorem ex_7_10_sum_one_half_sd_below :
    7424.55 < 95 * 80 + (-1.5) * (Real.sqrt 95 * 12) ∧ 95 * 80 + (-1.5) * (Real.sqrt 95 * 12) < 7424.56 := by
  obtain ⟨h0, h1, h2⟩ := sdb_s95
  constructor <;> linarith


/-- OpenStax Introductory Statistics 2e Practice exercise 7.11. The sum of 40 cholesterol readings (mean 180, standard deviation 20) has the normal law with mean 7200 and variance `40 · 20²`. The probability that it exceeds 7500 is enclosed in (0.0088, 0.0089). -/
@[kb "openstaxintrostats2e" "Exercise 7.11, p. 402"]
theorem ex_7_11_cholesterol_sum_above_7500 (hX : HasLaw X (gaussianReal (40 * 180) ((40 * 20 ^ 2 : ℝ).toNNReal)) P) :
    0.0088 < P.real {ω | 7500 < X ω} ∧ P.real {ω | 7500 < X ω} < 0.0089 := by
  have h := right_tail (law_c40 hX) sdb_c40 (x := 7500) (c := 300) (lo := 2.3717) (hi := 2.3718)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) t_2_3717.1 t_2_3718.2
  constructor <;> linarith [h.1, h.2]


/-- OpenStax Introductory Statistics 2e Practice exercise 7.12. For the same sum of 40 readings, the probability that it is below 7000 is enclosed in (0.0568, 0.057). -/
@[kb "openstaxintrostats2e" "Exercise 7.12, p. 402"]
theorem ex_7_12_cholesterol_sum_below_7000 (hX : HasLaw X (gaussianReal (40 * 180) ((40 * 20 ^ 2 : ℝ).toNNReal)) P) :
    0.0568 < P.real {ω | X ω < 7000} ∧ P.real {ω | X ω < 7000} < 0.057 := by
  have h := left_tail (law_c40 hX) sdb_c40 (x := 7000) (c := 200) (lo := 1.5811) (hi := 1.5812)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) t_1_5811.1 t_1_5812.2
  constructor <;> linarith [h.1, h.2]


/-- OpenStax Introductory Statistics 2e Practice exercise 7.13. For the sum of 40 readings (mean `40 · 180`, standard deviation `20 √40`), the sum one standard deviation above the mean lies in (7326.49, 7326.5). -/
@[kb "openstaxintrostats2e" "Exercise 7.13, p. 402"]
theorem ex_7_13_cholesterol_sum_one_sd_above :
    7326.49 < 40 * 180 + 1 * (Real.sqrt 40 * 20) ∧ 40 * 180 + 1 * (Real.sqrt 40 * 20) < 7326.5 := by
  obtain ⟨h0, h1, h2⟩ := sdb_c40
  constructor <;> linarith


/-- OpenStax Introductory Statistics 2e Practice exercise 7.14. For the same sum of 40 readings, the sum one and a half standard deviations below the mean lies in (7010.26, 7010.27). -/
@[kb "openstaxintrostats2e" "Exercise 7.14, p. 402"]
theorem ex_7_14_cholesterol_sum_one_half_sd_below :
    7010.26 < 40 * 180 + (-1.5) * (Real.sqrt 40 * 20) ∧ 40 * 180 + (-1.5) * (Real.sqrt 40 * 20) < 7010.27 := by
  obtain ⟨h0, h1, h2⟩ := sdb_c40
  constructor <;> linarith


/-- OpenStax Introductory Statistics 2e Practice exercise 7.15. For the normal law of the sum of 40 readings, the probability that the sum lies between one and a half standard deviations below the mean and one standard deviation above it is enclosed in (0.774, 0.775), about 77.5 percent. -/
@[kb "openstaxintrostats2e" "Exercise 7.15, p. 402"]
theorem ex_7_15_cholesterol_sum_between_z (hX : HasLaw X (gaussianReal (40 * 180) ((40 * 20 ^ 2 : ℝ).toNNReal)) P) :
    0.774 < P.real {ω | 40 * 180 - 1.5 * (Real.sqrt 40 * 20) < X ω ∧ X ω < 40 * 180 + 1 * (Real.sqrt 40 * 20)} ∧ P.real {ω | 40 * 180 - 1.5 * (Real.sqrt 40 * 20) < X ω ∧ X ω < 40 * 180 + 1 * (Real.sqrt 40 * 20)} < 0.775 := by
  have h := between_z (law_c40 hX) (sd_pos sdb_c40) (a := 1.5) (b := 1)
    (by norm_num) (by norm_num) t_1_5.1 t_1_5.2 t_1.1 t_1.2
  constructor <;> linarith [h.1, h.2]


/-- OpenStax Introductory Statistics 2e Practice exercise 7.16. The sum of the sugar contents of 100 cans (mean 39.01, standard deviation 0.5) has the normal law with mean 3901 and standard deviation 5. The probability that it exceeds 3910 is enclosed in (0.0359, 0.036). -/
@[kb "openstaxintrostats2e" "Exercise 7.16, p. 402"]
theorem ex_7_16_sugar_sum_above_3910 (hX : HasLaw X (gaussianReal (100 * 39.01) ((100 * 0.5 ^ 2 : ℝ).toNNReal)) P) :
    0.0359 < P.real {ω | 3910 < X ω} ∧ P.real {ω | 3910 < X ω} < 0.036 := by
  have h := right_tail (law_c100 hX) sdb_c100 (x := 3910) (c := 9) (lo := 1.8) (hi := 1.8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) t_1_8.1 t_1_8.2
  constructor <;> linarith [h.1, h.2]


/-- OpenStax Introductory Statistics 2e Practice exercise 7.17. For the same sum of 100 cans, the probability that it is below 3900 is enclosed in (0.4207, 0.4208). -/
@[kb "openstaxintrostats2e" "Exercise 7.17, p. 402"]
theorem ex_7_17_sugar_sum_below_3900 (hX : HasLaw X (gaussianReal (100 * 39.01) ((100 * 0.5 ^ 2 : ℝ).toNNReal)) P) :
    0.4207 < P.real {ω | X ω < 3900} ∧ P.real {ω | X ω < 3900} < 0.4208 := by
  have h := left_tail (law_c100 hX) sdb_c100 (x := 3900) (c := 1) (lo := 0.2) (hi := 0.2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) t_0_2.1 t_0_2.2
  constructor <;> linarith [h.1, h.2]


/-- OpenStax Introductory Statistics 2e Practice exercise 7.18. For the same sum of 100 cans, the probability that it lies between 3900 and 3910 (the two numbers of Exercises 7.17 and 7.16) is enclosed in (0.543, 0.544). -/
@[kb "openstaxintrostats2e" "Exercise 7.18, p. 402"]
theorem ex_7_18_sugar_sum_between (hX : HasLaw X (gaussianReal (100 * 39.01) ((100 * 0.5 ^ 2 : ℝ).toNNReal)) P) :
    0.543 < P.real {ω | 3900 < X ω ∧ X ω < 3910} ∧ P.real {ω | 3900 < X ω ∧ X ω < 3910} < 0.544 := by
  have h := straddle (law_c100 hX) sdb_c100 (a := 3900) (b := 3910) (c1 := 1) (c2 := 9)
    (lo1 := 0.2) (hi1 := 0.2) (lo2 := 1.8) (hi2 := 1.8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) t_0_2.1 t_0_2.2 t_1_8.1 t_1_8.2
  constructor <;> linarith [h.1, h.2]


/-- OpenStax Introductory Statistics 2e Practice exercise 7.19. For the sum of 100 cans (mean `100 · 39.01`, standard deviation `√100 · 0.5 = 5`), the sum with z-score -2.5 is exactly 3888.5. -/
@[kb "openstaxintrostats2e" "Exercise 7.19, p. 402"]
theorem ex_7_19_sugar_sum_z_minus_2_5 :
    100 * 39.01 + (-2.5) * (Real.sqrt 100 * 0.5) = 3888.5 := by
  rw [sdv_c100]; norm_num


/-- OpenStax Introductory Statistics 2e Practice exercise 7.20. For the same sum of 100 cans, the sum with z-score 0.5 is exactly 3903.5. -/
@[kb "openstaxintrostats2e" "Exercise 7.20, p. 402"]
theorem ex_7_20_sugar_sum_z_half :
    100 * 39.01 + 0.5 * (Real.sqrt 100 * 0.5) = 3903.5 := by
  rw [sdv_c100]; norm_num


/-- OpenStax Introductory Statistics 2e Practice exercise 7.21. For the normal law of the sum of 100 cans, the probability that the sum has z-score between -2 and 1 is enclosed in (0.818, 0.819), about 81.9 percent. -/
@[kb "openstaxintrostats2e" "Exercise 7.21, p. 402"]
theorem ex_7_21_sugar_sum_between_z (hX : HasLaw X (gaussianReal (100 * 39.01) ((100 * 0.5 ^ 2 : ℝ).toNNReal)) P) :
    0.818 < P.real {ω | 100 * 39.01 - 2 * (Real.sqrt 100 * 0.5) < X ω ∧ X ω < 100 * 39.01 + 1 * (Real.sqrt 100 * 0.5)} ∧ P.real {ω | 100 * 39.01 - 2 * (Real.sqrt 100 * 0.5) < X ω ∧ X ω < 100 * 39.01 + 1 * (Real.sqrt 100 * 0.5)} < 0.819 := by
  have h := between_z (law_c100 hX) (sd_pos sdb_c100) (a := 2) (b := 1)
    (by norm_num) (by norm_num) t_2.1 t_2.2 t_1.1 t_1.2
  constructor <;> linarith [h.1, h.2]


/-- OpenStax Introductory Statistics 2e Practice exercise 7.22. Each value has mean 12 and there are 25 values, so the sum has mean 300. -/
@[kb "openstaxintrostats2e" "Exercise 7.22, p. 402"]
theorem ex_7_22_sum_mean_25_values :
    (25 : ℝ) * 12 = 300 := by
  norm_num


/-- OpenStax Introductory Statistics 2e Practice exercise 7.23. Each value has standard deviation 1 and there are 25 values, so the sum has standard deviation `√25 · 1 = 5`. -/
@[kb "openstaxintrostats2e" "Exercise 7.23, p. 402"]
theorem ex_7_23_sum_sd_25_values :
    Real.sqrt 25 * 1 = 5 := by
  rw [sqrt_25]; norm_num


/-- OpenStax Introductory Statistics 2e Practice exercise 7.24. The sum of 25 values with mean 12 and standard deviation 1 has a continuous (normal) law, so the probability that it equals exactly 290 is 0. -/
@[kb "openstaxintrostats2e" "Exercise 7.24, p. 402"]
theorem ex_7_24_sum_equals_290_has_probability_zero (hX : HasLaw X (gaussianReal (25 * 12) ((25 * 1 ^ 2 : ℝ).toNNReal)) P) :
    P.real {ω | X ω = 290} = 0 := by
  have h := law_k25 hX
  have e : P {ω | X ω = 290} = gaussianReal 300 ((Real.sqrt 25 * 1) ^ 2).toNNReal {290} := by
    have := prob_mem_of_hasLaw h (measurableSet_singleton (290 : ℝ))
    simpa using this
  have h0 : gaussianReal 300 25 {290} = 0 :=
    (gaussianReal_absolutelyContinuous 300 (by norm_num)) (by simp)
  rw [Measure.real, e]
  simp [h0]


/-- OpenStax Introductory Statistics 2e Practice exercise 7.25. The sum of 25 values with mean 12 and standard deviation 1 has the normal law with mean 300 and standard deviation 5. The probability that it exceeds 290 is enclosed in (0.9772, 0.9773). -/
@[kb "openstaxintrostats2e" "Exercise 7.25, p. 402"]
theorem ex_7_25_sum_above_290 (hX : HasLaw X (gaussianReal (25 * 12) ((25 * 1 ^ 2 : ℝ).toNNReal)) P) :
    0.9772 < P.real {ω | 290 < X ω} ∧ P.real {ω | 290 < X ω} < 0.9773 := by
  have h := right_tail_b (law_k25 hX) sdb_k25 (x := 290) (c := 10) (lo := 2) (hi := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) t_2.1 t_2.2
  constructor <;> linarith [h.1, h.2]


/-- OpenStax Introductory Statistics 2e Practice exercise 7.29. If the standard deviation of the sum of `n` values from a population of standard deviation 6 is 42, the sample size is `n = 49`. -/
@[kb "openstaxintrostats2e" "Exercise 7.29, p. 403"]
theorem ex_7_29_sample_size_from_sd_of_sum :
    ∀ n : ℝ, 0 < n → Real.sqrt n * 6 = 42 → n = 49 := by
  intro n hn h
  have h7 : Real.sqrt n = 7 := by linarith
  have := Real.sq_sqrt hn.le
  rw [h7] at this
  linarith


/-- OpenStax Introductory Statistics 2e Practice exercise 7.30. If the mean of the sum of `n` values from a population of mean 19 is 15,200, the sample size is `n = 800`. -/
@[kb "openstaxintrostats2e" "Exercise 7.30, p. 403"]
theorem ex_7_30_sample_size_from_mean_of_sum :
    ∀ n : ℝ, n * 19 = 15200 → n = 800 := by
  intro n h
  linarith


/-- OpenStax Introductory Statistics 2e Practice exercise 7.31. For the sum of 400 purchases (mean 3, standard deviation 0.7 each) the mean of the sum is 1200 and its standard deviation `√400 · 0.7 = 14`; the sum 840 has z-score `-180/7` (about -25.7). -/
@[kb "openstaxintrostats2e" "Exercise 7.31, p. 403"]
theorem ex_7_31_zscore_840 :
    ((840 : ℝ) - 400 * 3) / (Real.sqrt 400 * 0.7) = -180 / 7 := by
  rw [sq_exact (n := (400 : ℝ)) (r := 20) (by norm_num) (by norm_num)]; norm_num


/-- OpenStax Introductory Statistics 2e Practice exercise 7.32. For the same sum of 400 purchases, the sum 1186 has z-score exactly -1. -/
@[kb "openstaxintrostats2e" "Exercise 7.32, p. 403"]
theorem ex_7_32_zscore_1186 :
    ((1186 : ℝ) - 400 * 3) / (Real.sqrt 400 * 0.7) = -1 := by
  rw [sq_exact (n := (400 : ℝ)) (r := 20) (by norm_num) (by norm_num)]; norm_num


/-- OpenStax Introductory Statistics 2e Practice exercise 7.33. The sum of 400 purchases has the normal law with mean 1200 and standard deviation 14. The probability that it is below 1186 (z-score -1) is enclosed in (0.1586, 0.1587). -/
@[kb "openstaxintrostats2e" "Exercise 7.33, p. 403"]
theorem ex_7_33_sum_below_1186 (hX : HasLaw X (gaussianReal (400 * 3) ((400 * 0.7 ^ 2 : ℝ).toNNReal)) P) :
    0.1586 < P.real {ω | X ω < 1186} ∧ P.real {ω | X ω < 1186} < 0.1587 := by
  have h := left_tail (law_m400 hX) sdb_m400 (x := 1186) (c := 14) (lo := 1) (hi := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) t_1.1 t_1.2
  constructor <;> linarith [h.1, h.2]


/-- OpenStax Introductory Statistics 2e Practice exercise 7.34. Each value has mean 100 and there are 100 values, so the sum has mean 10,000. -/
@[kb "openstaxintrostats2e" "Exercise 7.34, p. 403"]
theorem ex_7_34_sum_mean_100_values :
    (100 : ℝ) * 100 = 10000 := by
  norm_num


/-- OpenStax Introductory Statistics 2e Practice exercise 7.35. Each value has standard deviation 100 and there are 100 values, so the sum has standard deviation `√100 · 100 = 1000`. -/
@[kb "openstaxintrostats2e" "Exercise 7.35, p. 403"]
theorem ex_7_35_sum_sd_100_values :
    Real.sqrt 100 * 100 = 1000 := by
  rw [sqrt_100]; norm_num


/-- OpenStax Introductory Statistics 2e Practice exercise 7.36. The sum of 100 values with mean 100 and standard deviation 100 has the normal law with mean 10,000 and standard deviation 1000. The probability that it exceeds 9000 (z-score -1) is enclosed in (0.8413, 0.8414). -/
@[kb "openstaxintrostats2e" "Exercise 7.36, p. 403"]
theorem ex_7_36_sum_above_9000 (hX : HasLaw X (gaussianReal (100 * 100) ((100 * 100 ^ 2 : ℝ).toNNReal)) P) :
    0.8413 < P.real {ω | 9000 < X ω} ∧ P.real {ω | 9000 < X ω} < 0.8414 := by
  have h := right_tail_b (law_n100 hX) sdb_n100 (x := 9000) (c := 1000) (lo := 1) (hi := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) t_1.1 t_1.2
  constructor <;> linarith [h.1, h.2]


/-- OpenStax Introductory Statistics 2e Practice exercise 7.37. A weight uniform on [24, 26] has mean 25 and variance `(26 - 24)²/12 = 1/3`, so its standard deviation `√(1/3)` lies strictly between 0.5773 and 0.5774 (part a). -/
@[kb "openstaxintrostats2e" "Exercise 7.37, p. 403"]
theorem ex_7_37_weight_uniform_mean_variance {X : Ω → ℝ} (hX : pdf.IsUniform X (Set.Icc 24 26) P) :
    P[X] = 25 ∧ variance X P = 1 / 3 ∧ 0.5773 < Real.sqrt (1 / 3) ∧ Real.sqrt (1 / 3) < 0.5774 := by
  have h1 := uniform_mean hX (by norm_num)
  have h2 := uniform_variance hX (by norm_num)
  have hs := sqrt_bd (n := (1 / 3 : ℝ)) (a := 0.5773) (b := 0.5774) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨by rw [h1]; norm_num, by rw [h2]; norm_num, hs.1, hs.2⟩


/-- OpenStax Introductory Statistics 2e Practice exercise 7.37. The mean of 100 such weights has variance `(1/3)/100 = 1/300`, so its standard deviation `√(2²/12/100)` lies strictly between 0.05773 and 0.05774 (part b). -/
@[kb "openstaxintrostats2e" "Exercise 7.37, p. 403"]
theorem ex_7_37_mean_weight_sd :
    (2 : ℝ) ^ 2 / 12 / 100 = 1 / 300 ∧ 0.05773 < Real.sqrt ((2 : ℝ) ^ 2 / 12 / 100) ∧ Real.sqrt ((2 : ℝ) ^ 2 / 12 / 100) < 0.05774 := by
  have hs := sqrt_bd (n := ((2 : ℝ) ^ 2 / 12 / 100)) (a := 0.05773) (b := 0.05774) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨by norm_num, hs.1, hs.2⟩


/-- OpenStax Introductory Statistics 2e Practice exercise 7.37. The mean of 100 weights (uniform on [24, 26]) has the normal law with mean 25 and variance `2²/12/100`. The probability that it is below 24.9 is enclosed in (0.0415, 0.0417) (about 0.042). -/
@[kb "openstaxintrostats2e" "Exercise 7.37, p. 403"]
theorem ex_7_37_mean_weight_below_24_9 (hX : HasLaw X (gaussianReal (25) ((2 ^ 2 / 12 / 100 : ℝ).toNNReal)) P) :
    0.0415 < P.real {ω | X ω < 24.9} ∧ P.real {ω | X ω < 24.9} < 0.0417 := by
  have h := left_tail (law_w100 hX) sdb_w100 (x := 24.9) (c := 0.1) (lo := 1.732) (hi := 1.7321)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) t_1_732.1 t_1_7321.2
  constructor <;> linarith [h.1, h.2]


/-- OpenStax Introductory Statistics 2e Practice exercise 7.39. For the same normal law of the mean of 100 weights, the probability that it exceeds 25.2 is enclosed in (0.00023, 0.0003) (a few hundredths of one percent). -/
@[kb "openstaxintrostats2e" "Exercise 7.39, p. 403"]
theorem ex_7_39_mean_weight_above_25_2 (hX : HasLaw X (gaussianReal (25) ((2 ^ 2 / 12 / 100 : ℝ).toNNReal)) P) :
    0.00023 < P.real {ω | 25.2 < X ω} ∧ P.real {ω | 25.2 < X ω} < 0.0003 := by
  have h := right_tail (law_w100 hX) sdb_w100 (x := 25.2) (c := 0.2) (lo := 3.464) (hi := 3.4642)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) t_3_464.1 t_3_4642.2
  constructor <;> linarith [h.1, h.2]


/-- OpenStax Introductory Statistics 2e Practice exercise 7.41. For the same normal law of the mean of 100 weights, any 90th percentile `k` lies in (25.073, 25.075) pounds (about 25.07). -/
@[kb "openstaxintrostats2e" "Exercise 7.41, p. 403"]
theorem ex_7_41_mean_weight_percentile_90 (hX : HasLaw X (gaussianReal (25) ((2 ^ 2 / 12 / 100 : ℝ).toNNReal)) P) {k : ℝ}
    (hk : P.real {ω | X ω ≤ k} = 9 / 10) :
    25.073 < k ∧ k < 25.075 := by
  have h := pct_hi (law_w100 hX) sdb_w100 (lo := 1.2813) (hi := 1.2818) (by norm_num) (by norm_num) (by norm_num)
    (lt_of_lt_of_le t_1_2813.2 (by norm_num)) (lt_of_le_of_lt (by norm_num) t_1_2818.1) hk
  constructor <;> linarith [h.1, h.2]


/-- OpenStax Introductory Statistics 2e Practice exercise 7.43. The sum of 100 weights (each uniform on [24, 26]) has mean `100 · 25 = 2500` and variance `100 · (2²/12) = 100/3`, so its standard deviation lies strictly between 5.7735 and 5.7736 (part a). -/
@[kb "openstaxintrostats2e" "Exercise 7.43, p. 403"]
theorem ex_7_43_weight_sum_mean_and_sd :
    (100 : ℝ) * 25 = 2500 ∧ (100 : ℝ) * (2 ^ 2 / 12) = 100 / 3 ∧ 5.7735 < Real.sqrt (100 * (2 ^ 2 / 12)) ∧ Real.sqrt (100 * (2 ^ 2 / 12)) < 5.7736 := by
  have hs := sqrt_bd (n := (100 * (2 ^ 2 / 12) : ℝ)) (a := 5.7735) (b := 5.7736) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨by norm_num, by norm_num, hs.1, hs.2⟩


/-- OpenStax Introductory Statistics 2e Practice exercise 7.43. The sum of 100 weights has the normal law with mean 2500 and variance `100 · (2²/12)`. The probability that the sum is below 2450 is enclosed in (0, 0.0003); the true value is astronomically small (about `10⁻¹⁸`), which the book rounds to 0. -/
@[kb "openstaxintrostats2e" "Exercise 7.43, p. 403"]
theorem ex_7_43_weight_sum_below_2450 (hX : HasLaw X (gaussianReal (100 * 25) ((100 * (2 ^ 2 / 12) : ℝ).toNNReal)) P) :
    0 < P.real {ω | X ω < 2450} ∧ P.real {ω | X ω < 2450} < 0.0003 := by
  have h := left_tail (law_ws100 hX) sdb_ws100 (x := 2450) (c := 50) (lo := 3.5) (hi := 8.6603)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) t_3_5.1 (Phi_lt_one _)
  constructor <;> linarith [h.1, h.2]


/-- OpenStax Introductory Statistics 2e Practice exercise 7.45. For the same normal law of the sum of 100 weights, any 90th percentile `k` lies in (2507.3, 2507.5) pounds (about 2507.4). -/
@[kb "openstaxintrostats2e" "Exercise 7.45, p. 403"]
theorem ex_7_45_weight_sum_percentile_90 (hX : HasLaw X (gaussianReal (100 * 25) ((100 * (2 ^ 2 / 12) : ℝ).toNNReal)) P) {k : ℝ}
    (hk : P.real {ω | X ω ≤ k} = 9 / 10) :
    2507.3 < k ∧ k < 2507.5 := by
  have h := pct_hi (law_ws100 hX) sdb_ws100 (lo := 1.2813) (hi := 1.2818) (by norm_num) (by norm_num) (by norm_num)
    (lt_of_lt_of_le t_1_2813.2 (by norm_num)) (lt_of_le_of_lt (by norm_num) t_1_2818.1) hk
  constructor <;> linarith [h.1, h.2]


/-- OpenStax Introductory Statistics 2e Practice exercise 7.47. A battery lifetime that is exponential with mean 10 months has decay parameter `m = 1/10 = 0.1` and standard deviation `1/m = 10` months. -/
@[kb "openstaxintrostats2e" "Exercise 7.47, p. 403"]
theorem ex_7_47_battery_sd_and_decay_parameter :
    (1 : ℝ) / 10 = 0.1 ∧ Real.sqrt (variance id (expMeasure (0.1 : ℝ))) = 10 := by
  refine ⟨by norm_num, ?_⟩
  rw [sqrt_variance_expMeasure (by norm_num)]; norm_num


/-- OpenStax Introductory Statistics 2e Practice exercise 7.48. A battery lifetime with the exponential law of parameter 0.1 has mean 10 months and variance 100 (so standard deviation 10). -/
@[kb "openstaxintrostats2e" "Exercise 7.48, p. 403"]
theorem ex_7_48_battery_lifetime_exponential (hX : HasLaw X (expMeasure (0.1 : ℝ)) P) :
    P[X] = 10 ∧ variance X P = 100 := by
  refine ⟨?_, ?_⟩
  · rw [expectation_of_hasLaw_exp hX (by norm_num)]; norm_num
  · rw [variance_of_hasLaw_exp hX (by norm_num)]; norm_num


/-- OpenStax Introductory Statistics 2e Practice exercise 7.49. The mean lifetime of 64 batteries, with the normal law of mean 10 and variance `10²/64`, has standard deviation `10/√64 = 1.25`: it is the same law as `N(10, 1.25²)`. -/
@[kb "openstaxintrostats2e" "Exercise 7.49, p. 404"]
theorem ex_7_49_battery_mean_distribution :
    HasLaw X (gaussianReal 10 ((10 ^ 2 / 64 : ℝ).toNNReal)) P ↔
      HasLaw X (gaussianReal 10 (((1.25 : ℝ)) ^ 2).toNNReal) P := by
  rw [show ((10 : ℝ) ^ 2 / 64) = 1.25 ^ 2 by norm_num]


/-- OpenStax Introductory Statistics 2e Practice exercise 7.50. The total lifetime of 64 batteries, with the normal law of mean `64 · 10` and variance `64 · 10²`, has mean 640 and standard deviation 80: it is the same law as `N(640, 80²)`. -/
@[kb "openstaxintrostats2e" "Exercise 7.50, p. 404"]
theorem ex_7_50_battery_total_distribution :
    HasLaw X (gaussianReal (64 * 10) ((64 * 10 ^ 2 : ℝ).toNNReal)) P ↔
      HasLaw X (gaussianReal 640 (((80 : ℝ)) ^ 2).toNNReal) P := by
  rw [show (64 * 10 : ℝ) = 640 by norm_num, show (64 * 10 ^ 2 : ℝ) = 80 ^ 2 by norm_num]


/-- OpenStax Introductory Statistics 2e Practice exercise 7.51. The mean lifetime of 64 batteries has the normal law with mean 10 and standard deviation 1.25. The probability that it lies between 7 and 11 months is enclosed in (0.779, 0.781). -/
@[kb "openstaxintrostats2e" "Exercise 7.51, p. 404"]
theorem ex_7_51_battery_mean_between_7_and_11 (hX : HasLaw X (gaussianReal 10 ((10 ^ 2 / 64 : ℝ).toNNReal)) P) :
    0.779 < P.real {ω | 7 < X ω ∧ X ω < 11} ∧ P.real {ω | 7 < X ω ∧ X ω < 11} < 0.781 := by
  have h := straddle (law_e64m hX) sdb_e64m (a := 7) (b := 11) (c1 := 3) (c2 := 1)
    (lo1 := 2.4) (hi1 := 2.4) (lo2 := 0.8) (hi2 := 0.8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) t_2_4.1 t_2_4.2 t_0_8.1 t_0_8.2
  constructor <;> linarith [h.1, h.2]


/-- OpenStax Introductory Statistics 2e Practice exercise 7.52. The total lifetime of 64 batteries has the normal law with mean 640 and standard deviation 80. Any 80th percentile `k` of it lies in (707.3, 707.4) months (about 707.3). -/
@[kb "openstaxintrostats2e" "Exercise 7.52, p. 404"]
theorem ex_7_52_battery_total_percentile_80 (hX : HasLaw X (gaussianReal (64 * 10) ((64 * 10 ^ 2 : ℝ).toNNReal)) P) {k : ℝ}
    (hk : P.real {ω | X ω ≤ k} = 4 / 5) :
    707.3 < k ∧ k < 707.4 := by
  have h := pct_hi (law_e64s hX) sdb_e64s (lo := 0.8414) (hi := 0.8418) (by norm_num) (by norm_num) (by norm_num)
    (lt_of_lt_of_le t_0_8414.2 (by norm_num)) (lt_of_le_of_lt (by norm_num) t_0_8418.1) hk
  constructor <;> linarith [h.1, h.2]


/-- OpenStax Introductory Statistics 2e Practice exercise 7.53. For the mean lifetime of 64 batteries (normal, mean 10, standard deviation 1.25), if `q1` and `q3` are the first and third quartiles, the interquartile range `q3 - q1` lies in (1.68, 1.69) months (about 1.69). -/
@[kb "openstaxintrostats2e" "Exercise 7.53, p. 404"]
theorem ex_7_53_battery_mean_iqr (hX : HasLaw X (gaussianReal 10 ((10 ^ 2 / 64 : ℝ).toNNReal)) P) {q1 q3 : ℝ}
    (h1 : P.real {ω | X ω ≤ q1} = 1 / 4) (h3 : P.real {ω | X ω ≤ q3} = 3 / 4) :
    1.68 < q3 - q1 ∧ q3 - q1 < 1.69 := by
  have a := pct_hi (law_e64m hX) sdb_e64m (lo := 0.6743) (hi := 0.6747) (by norm_num) (by norm_num) (by norm_num)
    (lt_of_lt_of_le t_0_6743.2 (by norm_num)) (lt_of_le_of_lt (by norm_num) t_0_6747.1) h3
  have b := pct_lo (law_e64m hX) sdb_e64m (lo := 0.6743) (hi := 0.6747) (by norm_num) (by norm_num) (by norm_num)
    (lt_of_lt_of_le t_0_6743.2 (by norm_num)) (lt_of_le_of_lt (by norm_num) t_0_6747.1) h1
  constructor <;> linarith [a.1, a.2, b.1, b.2]


/-- OpenStax Introductory Statistics 2e Practice exercise 7.54. For the total lifetime of 64 batteries (normal, mean 640, standard deviation 80), the middle 80 percent lies between the 10th percentile `k10`, in (537.4, 537.5), and the 90th percentile `k90`, in (742.5, 742.6) months. -/
@[kb "openstaxintrostats2e" "Exercise 7.54, p. 404"]
theorem ex_7_54_battery_total_middle_80 (hX : HasLaw X (gaussianReal (64 * 10) ((64 * 10 ^ 2 : ℝ).toNNReal)) P) {k10 k90 : ℝ}
    (h1 : P.real {ω | X ω ≤ k10} = 1 / 10) (h9 : P.real {ω | X ω ≤ k90} = 9 / 10) :
    (537.4 < k10 ∧ k10 < 537.5) ∧ (742.5 < k90 ∧ k90 < 742.6) := by
  have a := pct_hi (law_e64s hX) sdb_e64s (lo := 1.2813) (hi := 1.2818) (by norm_num) (by norm_num) (by norm_num)
    (lt_of_lt_of_le t_1_2813.2 (by norm_num)) (lt_of_le_of_lt (by norm_num) t_1_2818.1) h9
  have b := pct_lo (law_e64s hX) sdb_e64s (lo := 1.2813) (hi := 1.2818) (by norm_num) (by norm_num) (by norm_num)
    (lt_of_lt_of_le t_1_2813.2 (by norm_num)) (lt_of_le_of_lt (by norm_num) t_1_2818.1) h1
  exact ⟨⟨by linarith [b.1], by linarith [b.2]⟩, ⟨by linarith [a.1], by linarith [a.2]⟩⟩


/-- OpenStax Introductory Statistics 2e Practice exercise 7.55. The sum of 50 values uniform on [6, 10] (mean 8, variance 16/12) has the normal law with mean 400 and variance `50 · (4²/12)`. The probability that it exceeds 420 is enclosed in (0.0071, 0.0072). -/
@[kb "openstaxintrostats2e" "Exercise 7.55, p. 404"]
theorem ex_7_55_uniform_sum_above_420 (hX : HasLaw X (gaussianReal (50 * 8) ((50 * ((10 - 6) ^ 2 / 12) : ℝ).toNNReal)) P) :
    0.0071 < P.real {ω | 420 < X ω} ∧ P.real {ω | 420 < X ω} < 0.0072 := by
  have h := right_tail (law_u50 hX) sdb_u50 (x := 420) (c := 20) (lo := 2.4494) (hi := 2.4495)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) t_2_4494.1 t_2_4495.2
  constructor <;> linarith [h.1, h.2]


/-- OpenStax Introductory Statistics 2e Practice exercise 7.56. For the same normal law of the sum of 50 values, any 90th percentile `k` lies in (410.4, 410.5) (about 410.5). -/
@[kb "openstaxintrostats2e" "Exercise 7.56, p. 404"]
theorem ex_7_56_uniform_sum_percentile_90 (hX : HasLaw X (gaussianReal (50 * 8) ((50 * ((10 - 6) ^ 2 / 12) : ℝ).toNNReal)) P) {k : ℝ}
    (hk : P.real {ω | X ω ≤ k} = 9 / 10) :
    410.4 < k ∧ k < 410.5 := by
  have h := pct_hi (law_u50 hX) sdb_u50 (lo := 1.2813) (hi := 1.2818) (by norm_num) (by norm_num) (by norm_num)
    (lt_of_lt_of_le t_1_2813.2 (by norm_num)) (lt_of_le_of_lt (by norm_num) t_1_2818.1) hk
  constructor <;> linarith [h.1, h.2]


/-- OpenStax Introductory Statistics 2e Practice exercise 7.57. For the same normal law of the sum, any 15th percentile `k` lies in (391.5, 391.6) (about 391.5). -/
@[kb "openstaxintrostats2e" "Exercise 7.57, p. 404"]
theorem ex_7_57_uniform_sum_percentile_15 (hX : HasLaw X (gaussianReal (50 * 8) ((50 * ((10 - 6) ^ 2 / 12) : ℝ).toNNReal)) P) {k : ℝ}
    (hk : P.real {ω | X ω ≤ k} = 3 / 20) :
    391.5 < k ∧ k < 391.6 := by
  have h := pct_lo (law_u50 hX) sdb_u50 (lo := 1.0362) (hi := 1.0367) (by norm_num) (by norm_num) (by norm_num)
    (lt_of_lt_of_le t_1_0362.2 (by norm_num)) (lt_of_le_of_lt (by norm_num) t_1_0367.1) hk
  constructor <;> linarith [h.1, h.2]


/-- OpenStax Introductory Statistics 2e Practice exercise 7.58. For the same normal law of the sum, any first quartile `k` lies in (394.4, 394.5) (about 394.5). -/
@[kb "openstaxintrostats2e" "Exercise 7.58, p. 404"]
theorem ex_7_58_uniform_sum_first_quartile (hX : HasLaw X (gaussianReal (50 * 8) ((50 * ((10 - 6) ^ 2 / 12) : ℝ).toNNReal)) P) {k : ℝ}
    (hk : P.real {ω | X ω ≤ k} = 1 / 4) :
    394.4 < k ∧ k < 394.5 := by
  have h := pct_lo (law_u50 hX) sdb_u50 (lo := 0.6743) (hi := 0.6747) (by norm_num) (by norm_num) (by norm_num)
    (lt_of_lt_of_le t_0_6743.2 (by norm_num)) (lt_of_le_of_lt (by norm_num) t_0_6747.1) hk
  constructor <;> linarith [h.1, h.2]


/-- OpenStax Introductory Statistics 2e Practice exercise 7.59. For the same normal law of the sum, any third quartile `k` lies in (405.5, 405.6) (about 405.5). -/
@[kb "openstaxintrostats2e" "Exercise 7.59, p. 404"]
theorem ex_7_59_uniform_sum_third_quartile (hX : HasLaw X (gaussianReal (50 * 8) ((50 * ((10 - 6) ^ 2 / 12) : ℝ).toNNReal)) P) {k : ℝ}
    (hk : P.real {ω | X ω ≤ k} = 3 / 4) :
    405.5 < k ∧ k < 405.6 := by
  have h := pct_hi (law_u50 hX) sdb_u50 (lo := 0.6743) (hi := 0.6747) (by norm_num) (by norm_num) (by norm_num)
    (lt_of_lt_of_le t_0_6743.2 (by norm_num)) (lt_of_le_of_lt (by norm_num) t_0_6747.1) hk
  constructor <;> linarith [h.1, h.2]


/-- OpenStax Introductory Statistics 2e Practice exercise 7.60. For the same normal law of the sum, any 80th percentile `k` lies in (406.8, 406.9) (about 406.9). -/
@[kb "openstaxintrostats2e" "Exercise 7.60, p. 404"]
theorem ex_7_60_uniform_sum_percentile_80 (hX : HasLaw X (gaussianReal (50 * 8) ((50 * ((10 - 6) ^ 2 / 12) : ℝ).toNNReal)) P) {k : ℝ}
    (hk : P.real {ω | X ω ≤ k} = 4 / 5) :
    406.8 < k ∧ k < 406.9 := by
  have h := pct_hi (law_u50 hX) sdb_u50 (lo := 0.8414) (hi := 0.8418) (by norm_num) (by norm_num) (by norm_num)
    (lt_of_lt_of_le t_0_8414.2 (by norm_num)) (lt_of_le_of_lt (by norm_num) t_0_8418.1) hk
  constructor <;> linarith [h.1, h.2]


end Settings

end UndergradKB.Statistics.Course.PracticeC7
