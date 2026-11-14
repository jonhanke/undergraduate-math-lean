import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF
import UndergradKB.Common.Attr
import UndergradKB.Statistics.NormalCdf
import UndergradKB.Statistics.CriticalValues
import UndergradKB.Statistics.EmpiricalRule
import UndergradKB.Statistics.PValue
import UndergradKB.Statistics.Course.ExamplesC7

/-!
# "Practice" exercises, chapter 9 (OpenStax *Introductory Statistics 2e*): hypothesis testing

Most exercises of this chapter are verbal (random variables, hypotheses, errors, which distribution).
Where the exercise has numbers or a statement about a parameter, it gets the honest mathematical
content that the repository has: hypotheses as statements about a parameter (with the kind of test
they give, defined below), the decision rule on the p-value, the power and Type II error, test
statistics with their standard error, and, under the normal approximation to the sampling
distribution (taken as the hypothesis, as in the worked examples), the p-value enclosed between two
bounds. Values of the standard normal distribution function `Φ` come from the alternating Taylor
enclosures (`Phi_enc` of `ExamplesC7.lean`). Where a Student `t` table value would be needed, only the
statistic is proved.

Skipped (verbal, no number or no mathematical content): 9.1, 9.3, 9.5 (random variable in words),
9.11 to 9.16, 9.18, 9.20 (errors and their consequences in words), 9.21 to 9.23, 9.27 to 9.31
(which distribution, assumptions), 9.37 (shaded graph), 9.40 to 9.46 (words, read-off of the data
given), 9.52, 9.53 (drawings), 9.56 (the test type is ambiguous in the text).
-/

namespace UndergradKB.Statistics.Course.PracticeC9

open MeasureTheory ProbabilityTheory Set UndergradKB.Statistics
open UndergradKB.Statistics.Course.ExamplesC7

local notation "Φ" => cdf (gaussianReal 0 1)

macro "pc9_num" : tactic =>
  `(tactic| (simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial]))

/-- The three forms of an alternative hypothesis about a parameter (`<`, `>`, `≠`). -/
inductive Alt where
  | less
  | greater
  | ne

/-- Left-tailed, right-tailed or two-tailed test. -/
inductive Tail where
  | left
  | right
  | two

/-- The tail of the test determined by the alternative hypothesis (`Table 9.5` of the book). -/
def Alt.tail : Alt → Tail
  | Alt.less => Tail.left
  | Alt.greater => Tail.right
  | Alt.ne => Tail.two

/-- The decision rule: reject the null hypothesis when the p-value is below the level `α`. -/
def rejectH0 (α p : ℝ) : Prop := p < α

/-! ### Values of `Φ` -/

private lemma t_0_6078 : (0.7283 : ℝ) < Φ 0.6078 ∧ Φ 0.6078 < 0.72837 :=
  Phi_enc (by norm_num) 2 (by norm_num) (by pc9_num) (by pc9_num)

private lemma t_0_6079 : (0.72834 : ℝ) < Φ 0.6079 ∧ Φ 0.6079 < 0.72841 :=
  Phi_enc (by norm_num) 2 (by norm_num) (by pc9_num) (by pc9_num)

private lemma t_1_6996 : (0.95536 : ℝ) < Φ 1.6996 ∧ Φ 1.6996 < 0.95543 :=
  Phi_enc (by norm_num) 4 (by norm_num) (by pc9_num) (by pc9_num)

private lemma t_1_6997 : (0.95537 : ℝ) < Φ 1.6997 ∧ Φ 1.6997 < 0.95544 :=
  Phi_enc (by norm_num) 4 (by norm_num) (by pc9_num) (by pc9_num)

private lemma t_1_9364 : (0.97356 : ℝ) < Φ 1.9364 ∧ Φ 1.9364 < 0.97363 :=
  Phi_enc (by norm_num) 5 (by norm_num) (by pc9_num) (by pc9_num)

private lemma t_1_9365 : (0.97356 : ℝ) < Φ 1.9365 ∧ Φ 1.9365 < 0.97363 :=
  Phi_enc (by norm_num) 5 (by norm_num) (by pc9_num) (by pc9_num)

private lemma t_2_0784 : (0.98113 : ℝ) < Φ 2.0784 ∧ Φ 2.0784 < 0.9812 :=
  Phi_enc (by norm_num) 6 (by norm_num) (by pc9_num) (by pc9_num)

private lemma t_2_0785 : (0.98113 : ℝ) < Φ 2.0785 ∧ Φ 2.0785 < 0.9812 :=
  Phi_enc (by norm_num) 5 (by norm_num) (by pc9_num) (by pc9_num)

private lemma t_3_5 : (0.99973 : ℝ) < Φ 3.5 ∧ Φ 3.5 < 0.9998 :=
  Phi_enc (by norm_num) 11 (by norm_num) (by pc9_num) (by pc9_num)

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

/-- Strict enclosure of a quotient `c / σ`. -/
private lemma zbd {c σ s1 s2 lo hi : ℝ} (hs : 0 < s1 ∧ s1 ≤ σ ∧ σ ≤ s2) (hlo : lo * s2 < c)
    (hhi : c < hi * s1) (hlo0 : 0 ≤ lo) : lo < c / σ ∧ c / σ < hi := by
  obtain ⟨h0, h1, h2⟩ := hs
  have hσ : 0 < σ := by linarith
  have hc : 0 < c := lt_of_le_of_lt (mul_nonneg hlo0 (by linarith)) hlo
  have hhi0 : 0 ≤ hi := by
    by_contra h
    replace h := not_le.1 h
    nlinarith
  constructor
  · rw [lt_div_iff₀ hσ]; nlinarith [mul_nonneg hlo0 (sub_nonneg.2 h2)]
  · rw [div_lt_iff₀ hσ]; nlinarith [mul_nonneg hhi0 (sub_nonneg.2 h1)]

end Helpers

section Settings

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}

/-! ### The laws of the exercises' settings -/

private lemma law_t24 (hX : HasLaw X (gaussianReal 13 ((2 ^ 2 / 20 : ℝ).toNNReal)) P) :
    HasLaw X (gaussianReal 13 ((2 / Real.sqrt 20) ^ 2).toNNReal) P :=
  law_mean (s := 2) (n := 20) (by norm_num) hX

private lemma sdb_t24 : 0 < (0.447213 : ℝ) ∧ (0.447213 : ℝ) ≤ 2 / Real.sqrt 20 ∧ 2 / Real.sqrt 20 ≤ (0.447214 : ℝ) := by
  have hs := sqrt_bd (n := (20 : ℝ)) (a := 4.472135) (b := 4.472136) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hp : 0 < Real.sqrt (20 : ℝ) := by linarith [hs.1]
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [le_div_iff₀ hp]; nlinarith [hs.2]
  · rw [div_le_iff₀ hp]; nlinarith [hs.1]

private lemma law_m25 (hX : HasLaw X (gaussianReal 25 ((5 ^ 2 / 108 : ℝ).toNNReal)) P) :
    HasLaw X (gaussianReal 25 ((5 / Real.sqrt 108) ^ 2).toNNReal) P :=
  law_mean (s := 5) (n := 108) (by norm_num) hX

private lemma sdb_m25 : 0 < (0.481125 : ℝ) ∧ (0.481125 : ℝ) ≤ 5 / Real.sqrt 108 ∧ 5 / Real.sqrt 108 ≤ (0.481126 : ℝ) := by
  have hs := sqrt_bd (n := (108 : ℝ)) (a := 10.392304) (b := 10.392305) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hp : 0 < Real.sqrt (108 : ℝ) := by linarith [hs.1]
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [le_div_iff₀ hp]; nlinarith [hs.2]
  · rw [div_le_iff₀ hp]; nlinarith [hs.1]

private lemma law_p26 (hX : HasLaw X (gaussianReal (0.42) ((0.42 * (1 - 0.42) / 100 : ℝ).toNNReal)) P) :
    HasLaw X (gaussianReal 0.42 ((Real.sqrt (0.42 * (1 - 0.42) / 100)) ^ 2).toNNReal) P := by
  exact law_sqrt (by norm_num) hX

private lemma sdb_p26 : 0 < (0.049355 : ℝ) ∧ (0.049355 : ℝ) ≤ Real.sqrt (0.42 * (1 - 0.42) / 100) ∧ Real.sqrt (0.42 * (1 - 0.42) / 100) ≤ (0.049356 : ℝ) := by
  have hs := sqrt_bd (n := (0.42 * (1 - 0.42) / 100 : ℝ)) (a := 0.049355) (b := 0.049356) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  exact ⟨by norm_num, hs.1.le, hs.2.le⟩

private lemma law_m35 (hX : HasLaw X (gaussianReal 73 ((1.8 ^ 2 / 40 : ℝ).toNNReal)) P) :
    HasLaw X (gaussianReal 73 ((1.8 / Real.sqrt 40) ^ 2).toNNReal) P :=
  law_mean (s := 1.8) (n := 40) (by norm_num) hX

private lemma sdb_m35 : 0 < (0.284604 : ℝ) ∧ (0.284604 : ℝ) ≤ 1.8 / Real.sqrt 40 ∧ 1.8 / Real.sqrt 40 ≤ (0.284606 : ℝ) := by
  have hs := sqrt_bd (n := (40 : ℝ)) (a := 6.324555) (b := 6.324556) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hp : 0 < Real.sqrt (40 : ℝ) := by linarith [hs.1]
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [le_div_iff₀ hp]; nlinarith [hs.2]
  · rw [div_le_iff₀ hp]; nlinarith [hs.1]

private lemma law_m36 (hX : HasLaw X (gaussianReal 31 ((2 ^ 2 / 15 : ℝ).toNNReal)) P) :
    HasLaw X (gaussianReal 31 ((2 / Real.sqrt 15) ^ 2).toNNReal) P :=
  law_mean (s := 2) (n := 15) (by norm_num) hX

private lemma sdb_m36 : 0 < (0.516397 : ℝ) ∧ (0.516397 : ℝ) ≤ 2 / Real.sqrt 15 ∧ 2 / Real.sqrt 15 ≤ (0.516398 : ℝ) := by
  have hs := sqrt_bd (n := (15 : ℝ)) (a := 3.872983) (b := 3.872984) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hp : 0 < Real.sqrt (15 : ℝ) := by linarith [hs.1]
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [le_div_iff₀ hp]; nlinarith [hs.2]
  · rw [div_le_iff₀ hp]; nlinarith [hs.1]

private lemma law_m47 (hX : HasLaw X (gaussianReal 2.5 ((1.5 ^ 2 / 26 : ℝ).toNNReal)) P) :
    HasLaw X (gaussianReal 2.5 ((1.5 / Real.sqrt 26) ^ 2).toNNReal) P :=
  law_mean (s := 1.5) (n := 26) (by norm_num) hX

private lemma sdb_m47 : 0 < (0.294174 : ℝ) ∧ (0.294174 : ℝ) ≤ 1.5 / Real.sqrt 26 ∧ 1.5 / Real.sqrt 26 ≤ (0.294175 : ℝ) := by
  have hs := sqrt_bd (n := (26 : ℝ)) (a := 5.099019) (b := 5.09902) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hp : 0 < Real.sqrt (26 : ℝ) := by linarith [hs.1]
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [le_div_iff₀ hp]; nlinarith [hs.2]
  · rw [div_le_iff₀ hp]; nlinarith [hs.1]

private lemma law_t48 (hX : HasLaw X (gaussianReal 15 ((6.3 ^ 2 / 75 : ℝ).toNNReal)) P) :
    HasLaw X (gaussianReal 15 ((6.3 / Real.sqrt 75) ^ 2).toNNReal) P :=
  law_mean (s := 6.3) (n := 75) (by norm_num) hX

private lemma sdb_t48 : 0 < (0.727461 : ℝ) ∧ (0.727461 : ℝ) ≤ 6.3 / Real.sqrt 75 ∧ 6.3 / Real.sqrt 75 ≤ (0.727462 : ℝ) := by
  have hs := sqrt_bd (n := (75 : ℝ)) (a := 8.660254) (b := 8.660255) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hp : 0 < Real.sqrt (75 : ℝ) := by linarith [hs.1]
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [le_div_iff₀ hp]; nlinarith [hs.2]
  · rw [div_le_iff₀ hp]; nlinarith [hs.1]


/-! ### Exercises -/

/-- OpenStax Introductory Statistics 2e Practice exercise 9.2. The null hypothesis `μ ≤ 3` and the alternative `μ > 3` (mean speed above three Megabits per second) exclude each other and cover every value of the mean; the alternative with `>` is a right-tailed test. -/
@[kb "openstaxintrostats2e" "Exercise 9.2, p. 500"]
theorem ex_9_2_cable_speed_hypotheses :
    (∀ μ : ℝ, μ ≤ 3 ↔ ¬ 3 < μ) ∧ Alt.tail Alt.greater = Tail.right := by
  exact ⟨fun μ => not_lt.symm, rfl⟩


/-- OpenStax Introductory Statistics 2e Practice exercise 9.4. Null hypothesis `μ = 58000` against the alternative `μ > 58000` for the mean IT salary: the alternative excludes the null value, and it is a right-tailed test. -/
@[kb "openstaxintrostats2e" "Exercise 9.4, p. 500"]
theorem ex_9_4_it_salary_hypotheses :
    (∀ μ : ℝ, 58000 < μ → μ ≠ 58000) ∧ Alt.tail Alt.greater = Tail.right := by
  exact ⟨fun μ h => ne_of_gt h, rfl⟩


/-- OpenStax Introductory Statistics 2e Practice exercise 9.6. Null hypothesis `p = 0.83` against `p ≠ 0.83` for the proportion of visitors: the two hypotheses are exact negations of each other, and the alternative with `≠` is a two-tailed test. -/
@[kb "openstaxintrostats2e" "Exercise 9.6, p. 500"]
theorem ex_9_6_times_square_hypotheses :
    (∀ p : ℝ, p = 0.83 ↔ ¬ p ≠ 0.83) ∧ Alt.tail Alt.ne = Tail.two := by
  exact ⟨fun p => not_not.symm, rfl⟩


/-- OpenStax Introductory Statistics 2e Practice exercise 9.7. Null hypothesis `p = 0.42` against `p < 0.42` for the proportion of female fish: the alternative excludes the null value, and it is a left-tailed test. -/
@[kb "openstaxintrostats2e" "Exercise 9.7, p. 500"]
theorem ex_9_7_fish_hypotheses :
    (∀ p : ℝ, p < 0.42 → p ≠ 0.42) ∧ Alt.tail Alt.less = Tail.left := by
  exact ⟨fun p h => ne_of_lt h, rfl⟩


/-- OpenStax Introductory Statistics 2e Practice exercise 9.8. Null hypothesis `μ = 2.5` against `μ > 2.5` for the mean jail time in years (has it increased?): the alternative excludes the null value, and it is a right-tailed test. -/
@[kb "openstaxintrostats2e" "Exercise 9.8, p. 500"]
theorem ex_9_8_jail_time_hypotheses :
    (∀ μ : ℝ, 2.5 < μ → μ ≠ 2.5) ∧ Alt.tail Alt.greater = Tail.right := by
  exact ⟨fun μ h => ne_of_gt h, rfl⟩


/-- OpenStax Introductory Statistics 2e Practice exercise 9.9. Null hypothesis `μ = 15` against `μ ≠ 15` for the mean repayment time in years: exact negations of each other, and a two-tailed test. -/
@[kb "openstaxintrostats2e" "Exercise 9.9, p. 500"]
theorem ex_9_9_loan_repayment_hypotheses :
    (∀ μ : ℝ, μ = 15 ↔ ¬ μ ≠ 15) ∧ Alt.tail Alt.ne = Tail.two := by
  exact ⟨fun μ => not_not.symm, rfl⟩


/-- OpenStax Introductory Statistics 2e Practice exercise 9.10. Null hypothesis `p = 0.095` against `p < 0.095` for the proportion with depression in the town (a sample of 7 in 100 is the data): the alternative excludes the null value, and it is a left-tailed test. -/
@[kb "openstaxintrostats2e" "Exercise 9.10, p. 501"]
theorem ex_9_10_depression_hypotheses :
    (∀ p : ℝ, p < 0.095 → p ≠ 0.095) ∧ Alt.tail Alt.less = Tail.left := by
  exact ⟨fun p h => ne_of_lt h, rfl⟩


/-- OpenStax Introductory Statistics 2e Practice exercise 9.17. A test with power 0.981 has Type II error probability `1 - 0.981 = 0.019`; stated for the repository's z test, if the power at the alternative `μ₁` is 0.981 then `β = 0.019`. -/
@[kb "openstaxintrostats2e" "Exercise 9.17, p. 501"]
theorem ex_9_17_power_to_type_II :
    ∀ (μ₀ μ₁ σ : ℝ) (n : ℕ) (c : ℝ), zTestPower μ₀ μ₁ σ n c = 0.981 → zTestTypeII μ₀ μ₁ σ n c = 0.019 := by
  intro μ₀ μ₁ σ n c h
  have := zTestTypeII_add_zTestPower μ₀ μ₁ σ n c
  linarith


/-- OpenStax Introductory Statistics 2e Practice exercise 9.19. For the E-coli test the Type I error probability is `α = 0.012` and the Type II error probability is `β = 0.002`; the power is `1 - β = 0.998` (any z test with Type II error probability 0.002 has this power). -/
@[kb "openstaxintrostats2e" "Exercise 9.19, p. 501"]
theorem ex_9_19_e_coli_power :
    (1 : ℝ) - 0.002 = 0.998 ∧ ∀ (μ₀ μ₁ σ : ℝ) (n : ℕ) (c : ℝ), zTestTypeII μ₀ μ₁ σ n c = 0.002 → zTestPower μ₀ μ₁ σ n c = 0.998 := by
  refine ⟨by norm_num, ?_⟩
  intro μ₀ μ₁ σ n c h
  have := zTestTypeII_add_zTestPower μ₀ μ₁ σ n c
  linarith


/-- OpenStax Introductory Statistics 2e Practice exercise 9.24. A normal population with mean 13, sample of 20 with mean 12.8 and standard deviation 2: the population standard deviation is unknown, so the Student `t` distribution is used, with `20 - 1 = 19` degrees of freedom; the test statistic `(12.8 - 13) / (2/√20)` lies in (-0.448, -0.447). -/
@[kb "openstaxintrostats2e" "Exercise 9.24, p. 501"]
theorem ex_9_24_sample_t_statistic :
    -0.448 < (12.8 - 13) / (2 / Real.sqrt 20) ∧ (12.8 - 13) / (2 / Real.sqrt 20) < -0.447 := by
  have e : (12.8 - 13) / (2 / Real.sqrt 20) = -(0.2 / (2 / Real.sqrt 20)) := by rw [← neg_div]; norm_num
  rw [e]
  have h := zbd sdb_t24 (c := 0.2) (lo := 0.4472) (hi := 0.4473) (by norm_num) (by norm_num) (by norm_num)
  constructor <;> linarith [h.1, h.2]


/-- OpenStax Introductory Statistics 2e Practice exercise 9.24. The sample of size 20 gives `20 - 1 = 19` degrees of freedom for the Student `t` distribution of the test. -/
@[kb "openstaxintrostats2e" "Exercise 9.24, p. 501"]
theorem ex_9_24_degrees_of_freedom :
    (20 : ℕ) - 1 = 19 := by
  norm_num


/-- OpenStax Introductory Statistics 2e Practice exercise 9.25. A population with mean 25 and standard deviation 5 (known), sample of 108 with mean 24: the test is a normal one for a mean, with standard error `5/√108`, and the statistic `(24 - 25) / (5/√108)` lies in (-2.079, -2.078). -/
@[kb "openstaxintrostats2e" "Exercise 9.25, p. 501"]
theorem ex_9_25_z_statistic_known_sd :
    -2.079 < (24 - 25) / (5 / Real.sqrt 108) ∧ (24 - 25) / (5 / Real.sqrt 108) < -2.078 := by
  have e : (24 - 25) / (5 / Real.sqrt 108) = -(1 / (5 / Real.sqrt 108)) := by rw [← neg_div]; norm_num
  rw [e]
  have h := zbd sdb_m25 (c := 1) (lo := 2.0784) (hi := 2.0785) (by norm_num) (by norm_num) (by norm_num)
  constructor <;> linarith [h.1, h.2]


/-- OpenStax Introductory Statistics 2e Practice exercise 9.25. Under the null hypothesis the mean of 108 values has the normal law with mean 25 and variance `5²/108`. The probability that it is at most 24 is enclosed in (0.0188, 0.0189). -/
@[kb "openstaxintrostats2e" "Exercise 9.25, p. 501"]
theorem ex_9_25_left_tail_probability (hX : HasLaw X (gaussianReal 25 ((5 ^ 2 / 108 : ℝ).toNNReal)) P) :
    0.0188 < P.real {ω | X ω ≤ 24} ∧ P.real {ω | X ω ≤ 24} < 0.0189 := by
  have h := left_tail_le (law_m25 hX) sdb_m25 (x := 24) (c := 1) (lo := 2.0784) (hi := 2.0785)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) t_2_0784.1 t_2_0785.2
  constructor <;> linarith [h.1, h.2]


/-- OpenStax Introductory Statistics 2e Practice exercise 9.26. In a sample of 100 with null proportion 0.42, both `np = 42` and `nq = 58` are at least 5, so the normal distribution is the one to use for the test of a proportion. -/
@[kb "openstaxintrostats2e" "Exercise 9.26, p. 501"]
theorem ex_9_26_proportion_normal_conditions :
    (5 : ℝ) ≤ 100 * 0.42 ∧ (5 : ℝ) ≤ 100 * (1 - 0.42) := by
  norm_num


/-- OpenStax Introductory Statistics 2e Practice exercise 9.26. With null proportion 0.42, sample size 100 and sample proportion 0.39, the test statistic `(0.39 - 0.42) / √(0.42 · 0.58 / 100)` lies in (-0.608, -0.607). -/
@[kb "openstaxintrostats2e" "Exercise 9.26, p. 501"]
theorem ex_9_26_proportion_z_statistic :
    -0.608 < (0.39 - 0.42) / (Real.sqrt (0.42 * (1 - 0.42) / 100)) ∧ (0.39 - 0.42) / (Real.sqrt (0.42 * (1 - 0.42) / 100)) < -0.607 := by
  have e : (0.39 - 0.42) / (Real.sqrt (0.42 * (1 - 0.42) / 100)) = -(0.03 / (Real.sqrt (0.42 * (1 - 0.42) / 100))) := by rw [← neg_div]; norm_num
  rw [e]
  have h := zbd sdb_p26 (c := 0.03) (lo := 0.6078) (hi := 0.6079) (by norm_num) (by norm_num) (by norm_num)
  constructor <;> linarith [h.1, h.2]


/-- OpenStax Introductory Statistics 2e Practice exercise 9.26. Under the null hypothesis the sample proportion has the normal law with mean 0.42 and variance `0.42 · 0.58 / 100`. The probability that it is at most 0.39 is enclosed in (0.271, 0.272). -/
@[kb "openstaxintrostats2e" "Exercise 9.26, p. 501"]
theorem ex_9_26_proportion_left_tail (hX : HasLaw X (gaussianReal (0.42) ((0.42 * (1 - 0.42) / 100 : ℝ).toNNReal)) P) :
    0.271 < P.real {ω | X ω ≤ 0.39} ∧ P.real {ω | X ω ≤ 0.39} < 0.272 := by
  have h := left_tail_le (law_p26 hX) sdb_p26 (x := 0.39) (c := 0.03) (lo := 0.6078) (hi := 0.6079)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) t_0_6078.1 t_0_6079.2
  constructor <;> linarith [h.1, h.2]


/-- OpenStax Introductory Statistics 2e Practice exercise 9.32. The decision rule of the book: reject the null hypothesis exactly when the p-value is below the significance level. -/
@[kb "openstaxintrostats2e" "Exercise 9.32, p. 502"]
theorem ex_9_32_reject_rule :
    ∀ α p : ℝ, rejectH0 α p ↔ p < α := by
  intro α p; exact Iff.rfl


/-- OpenStax Introductory Statistics 2e Practice exercise 9.33. The grand prize has probability 0.005, which is far below the usual level 0.05 (below even 0.01): winning is very unlikely. -/
@[kb "openstaxintrostats2e" "Exercise 9.33, p. 502"]
theorem ex_9_33_grand_prize_unlikely :
    (0.005 : ℝ) < 0.01 ∧ (0.01 : ℝ) < 0.05 := by
  norm_num


/-- OpenStax Introductory Statistics 2e Practice exercise 9.34. Michele winning the prize of probability 0.005 is a rare event: its probability is below 0.05. -/
@[kb "openstaxintrostats2e" "Exercise 9.34, p. 502"]
theorem ex_9_34_grand_prize_rare_event :
    (0.005 : ℝ) < 0.05 := by
  norm_num


/-- OpenStax Introductory Statistics 2e Practice exercise 9.35. Heights of players: null mean 73 inches against a smaller mean, known standard deviation 1.8, a sample of 40. Under the null hypothesis the sample mean has the normal law with mean 73 and variance `1.8²/40`; the probability that it is at most the observed 71 is positive and below 0.0003, far below the level 0.05, so the null hypothesis is rejected (the p-value is almost zero). -/
@[kb "openstaxintrostats2e" "Exercise 9.35, p. 502"]
theorem ex_9_35_basketball_left_tail (hX : HasLaw X (gaussianReal 73 ((1.8 ^ 2 / 40 : ℝ).toNNReal)) P) :
    0 < P.real {ω | X ω ≤ 71} ∧ P.real {ω | X ω ≤ 71} < 0.0003 := by
  have h := left_tail_le (law_m35 hX) sdb_m35 (x := 71) (c := 2) (lo := 3.5) (hi := 7.0274)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) t_3_5.1 (Phi_lt_one _)
  constructor <;> linarith [h.1, h.2]


/-- OpenStax Introductory Statistics 2e Practice exercise 9.35. For the basketball heights the statistic `(71 - 73) / (1.8/√40)` lies in (-7.028, -7.027). -/
@[kb "openstaxintrostats2e" "Exercise 9.35, p. 502"]
theorem ex_9_35_basketball_z_statistic :
    -7.028 < (71 - 73) / (1.8 / Real.sqrt 40) ∧ (71 - 73) / (1.8 / Real.sqrt 40) < -7.027 := by
  have e : (71 - 73) / (1.8 / Real.sqrt 40) = -(2 / (1.8 / Real.sqrt 40)) := by rw [← neg_div]; norm_num
  rw [e]
  have h := zbd sdb_m35 (c := 2) (lo := 7.0272) (hi := 7.0274) (by norm_num) (by norm_num) (by norm_num)
  constructor <;> linarith [h.1, h.2]


/-- OpenStax Introductory Statistics 2e Practice exercise 9.36. Ages of graduate students: null mean 31 years (at most), known standard deviation 2, a sample of 15 with mean 32. Under the null hypothesis the sample mean has the normal law with mean 31 and variance `2²/15`. The p-value, the probability that it exceeds 32, lies in (0.0263, 0.0265); it is above 0.01, so the result is not significant at the 1 percent level. -/
@[kb "openstaxintrostats2e" "Exercise 9.36, p. 502"]
theorem ex_9_36_graduate_age_right_tail (hX : HasLaw X (gaussianReal 31 ((2 ^ 2 / 15 : ℝ).toNNReal)) P) :
    0.0263 < P.real {ω | 32 < X ω} ∧ P.real {ω | 32 < X ω} < 0.0265 := by
  have h := right_tail (law_m36 hX) sdb_m36 (x := 32) (c := 1) (lo := 1.9364) (hi := 1.9365)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) t_1_9364.1 t_1_9365.2
  constructor <;> linarith [h.1, h.2]


/-- OpenStax Introductory Statistics 2e Practice exercise 9.36. For the graduate student ages the statistic `(32 - 31) / (2/√15)` lies in (1.936, 1.937). -/
@[kb "openstaxintrostats2e" "Exercise 9.36, p. 502"]
theorem ex_9_36_graduate_age_z_statistic :
    1.936 < (32 - 31) / (2 / Real.sqrt 15) ∧ (32 - 31) / (2 / Real.sqrt 15) < 1.937 := by
  have h := zbd sdb_m36 (c := 32 - 31) (lo := 1.9364) (hi := 1.9365) (by norm_num) (by norm_num) (by norm_num)
  constructor <;> linarith [h.1, h.2]


/-- OpenStax Introductory Statistics 2e Practice exercise 9.38. When the level exceeds the p-value, reject the null hypothesis. -/
@[kb "openstaxintrostats2e" "Exercise 9.38, p. 502"]
theorem ex_9_38_reject_when_alpha_exceeds_p :
    ∀ α p : ℝ, p < α → rejectH0 α p := by
  intro α p h; exact h


/-- OpenStax Introductory Statistics 2e Practice exercise 9.39. When the level equals the p-value, the rule of the book (reject only when the p-value is strictly below the level) does not reject. -/
@[kb "openstaxintrostats2e" "Exercise 9.39, p. 502"]
theorem ex_9_39_do_not_reject_when_equal :
    ∀ α p : ℝ, α = p → ¬ rejectH0 α p := by
  intro α p h; rw [h]; exact lt_irrefl p


/-- OpenStax Introductory Statistics 2e Practice exercise 9.47. Jail times: null mean 2.5 years, known population standard deviation 1.5, sample of 26 with mean 3. The sample mean follows the normal law with mean 2.5 and standard deviation `1.5/√26`; the statistic `(3 - 2.5) / (1.5/√26)` lies in (1.699, 1.7). -/
@[kb "openstaxintrostats2e" "Exercise 9.47, p. 503"]
theorem ex_9_47_jail_z_statistic :
    1.699 < (3 - 2.5) / (1.5 / Real.sqrt 26) ∧ (3 - 2.5) / (1.5 / Real.sqrt 26) < 1.7 := by
  have h := zbd sdb_m47 (c := 3 - 2.5) (lo := 1.6996) (hi := 1.6997) (by norm_num) (by norm_num) (by norm_num)
  constructor <;> linarith [h.1, h.2]


/-- OpenStax Introductory Statistics 2e Practice exercise 9.47. Under the null hypothesis the mean of the 26 jail times has the normal law with mean 2.5 and variance `1.5²/26`. The p-value, the probability that it exceeds 3, lies in (0.044, 0.045); it is below 0.05. -/
@[kb "openstaxintrostats2e" "Exercise 9.47, p. 503"]
theorem ex_9_47_jail_right_tail (hX : HasLaw X (gaussianReal 2.5 ((1.5 ^ 2 / 26 : ℝ).toNNReal)) P) :
    0.044 < P.real {ω | 3 < X ω} ∧ P.real {ω | 3 < X ω} < 0.045 := by
  have h := right_tail (law_m47 hX) sdb_m47 (x := 3) (c := 0.5) (lo := 1.6996) (hi := 1.6997)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) t_1_6996.1 t_1_6997.2
  constructor <;> linarith [h.1, h.2]


/-- OpenStax Introductory Statistics 2e Practice exercise 9.48. Student loans: null mean 15 years, sample of 75 with mean 17.4 and standard deviation 6.3 (population standard deviation unknown, so the `t` test with `75 - 1 = 74` degrees of freedom). The statistic `(17.4 - 15) / (6.3/√75)` lies in (3.299, 3.3). -/
@[kb "openstaxintrostats2e" "Exercise 9.48, p. 503"]
theorem ex_9_48_loan_t_statistic :
    3.299 < (17.4 - 15) / (6.3 / Real.sqrt 75) ∧ (17.4 - 15) / (6.3 / Real.sqrt 75) < 3.3 := by
  have h := zbd sdb_t48 (c := 17.4 - 15) (lo := 3.2991) (hi := 3.2992) (by norm_num) (by norm_num) (by norm_num)
  constructor <;> linarith [h.1, h.2]


/-- OpenStax Introductory Statistics 2e Practice exercise 9.48. The statistic of the loan test exceeds 1.993, the book's table value of the two-tailed `t` test at level 0.05 with 74 degrees of freedom (a table constant, not proved), so the null hypothesis `μ = 15` is rejected at level 0.05. -/
@[kb "openstaxintrostats2e" "Exercise 9.48, p. 503"]
theorem ex_9_48_loan_t_exceeds_table :
    1.993 < (17.4 - 15) / (6.3 / Real.sqrt 75) := by
  have h := zbd sdb_t48 (c := 17.4 - 15) (lo := 1.993) (hi := 4) (by norm_num) (by norm_num) (by norm_num)
  exact h.1


/-- OpenStax Introductory Statistics 2e Practice exercise 9.49. Null hypothesis `μ = 9` against `μ < 9`: the alternative excludes the null value, and the test is left-tailed. -/
@[kb "openstaxintrostats2e" "Exercise 9.49, p. 503"]
theorem ex_9_49_left_tailed_mean_9 :
    (∀ μ : ℝ, μ < 9 → μ ≠ 9) ∧ Alt.tail Alt.less = Tail.left := by
  exact ⟨fun μ h => ne_of_lt h, rfl⟩


/-- OpenStax Introductory Statistics 2e Practice exercise 9.50. Null hypothesis `μ ≤ 6` against `μ > 6`: exact negations of each other, and the test is right-tailed. -/
@[kb "openstaxintrostats2e" "Exercise 9.50, p. 503"]
theorem ex_9_50_right_tailed_mean_6 :
    (∀ μ : ℝ, μ ≤ 6 ↔ ¬ 6 < μ) ∧ Alt.tail Alt.greater = Tail.right := by
  exact ⟨fun μ => not_lt.symm, rfl⟩


/-- OpenStax Introductory Statistics 2e Practice exercise 9.51. Null hypothesis `p = 0.25` against `p ≠ 0.25`: exact negations of each other, and the test is two-tailed. -/
@[kb "openstaxintrostats2e" "Exercise 9.51, p. 503"]
theorem ex_9_51_two_tailed_proportion_025 :
    (∀ p : ℝ, p = 0.25 ↔ ¬ p ≠ 0.25) ∧ Alt.tail Alt.ne = Tail.two := by
  exact ⟨fun p => not_not.symm, rfl⟩


/-- OpenStax Introductory Statistics 2e Practice exercise 9.54. A bottle labelled 16 ounces that you believe holds less: the alternative is `μ < 16` against the null value 16, which excludes it, and the test is left-tailed. -/
@[kb "openstaxintrostats2e" "Exercise 9.54, p. 503"]
theorem ex_9_54_water_bottle_test_type :
    (∀ μ : ℝ, μ < 16 → μ ≠ 16) ∧ Alt.tail Alt.less = Tail.left := by
  exact ⟨fun μ h => ne_of_lt h, rfl⟩


/-- OpenStax Introductory Statistics 2e Practice exercise 9.55. A golf score claimed to be 63 that you want to show is higher: the alternative is `μ > 63`, which excludes the null value 63, and the test is right-tailed. -/
@[kb "openstaxintrostats2e" "Exercise 9.55, p. 503"]
theorem ex_9_55_golf_score_test_type :
    (∀ μ : ℝ, 63 < μ → μ ≠ 63) ∧ Alt.tail Alt.greater = Tail.right := by
  exact ⟨fun μ h => ne_of_gt h, rfl⟩


/-- OpenStax Introductory Statistics 2e Practice exercise 9.57. A coin whose probability of heads is claimed to be 0.5 but that you think is smaller: the alternative is `p < 0.5`, which excludes the null value, and the test is left-tailed. -/
@[kb "openstaxintrostats2e" "Exercise 9.57, p. 503"]
theorem ex_9_57_coin_test_type :
    (∀ p : ℝ, p < 0.5 → p ≠ 0.5) ∧ Alt.tail Alt.less = Tail.left := by
  exact ⟨fun p h => ne_of_lt h, rfl⟩


/-- OpenStax Introductory Statistics 2e Practice exercise 9.58. An alternative hypothesis with the symbol `≠` gives a two-tailed test. -/
@[kb "openstaxintrostats2e" "Exercise 9.58, p. 503"]
theorem ex_9_58_not_equal_test_type :
    Alt.tail Alt.ne = Tail.two := by
  rfl


/-- OpenStax Introductory Statistics 2e Practice exercise 9.59. Null hypothesis `μ ≥ 18` (mean at least 18), whose alternative is `μ < 18`: exact negations of each other, and the test is left-tailed. -/
@[kb "openstaxintrostats2e" "Exercise 9.59, p. 503"]
theorem ex_9_59_at_least_18_test_type :
    (∀ μ : ℝ, 18 ≤ μ ↔ ¬ μ < 18) ∧ Alt.tail Alt.less = Tail.left := by
  exact ⟨fun μ => not_lt.symm, rfl⟩


/-- OpenStax Introductory Statistics 2e Practice exercise 9.60. Null hypothesis `μ ≤ 12` (mean at most 12), whose alternative is `μ > 12`: exact negations of each other, and the test is right-tailed. -/
@[kb "openstaxintrostats2e" "Exercise 9.60, p. 503"]
theorem ex_9_60_at_most_12_test_type :
    (∀ μ : ℝ, μ ≤ 12 ↔ ¬ 12 < μ) ∧ Alt.tail Alt.greater = Tail.right := by
  exact ⟨fun μ => not_lt.symm, rfl⟩


/-- OpenStax Introductory Statistics 2e Practice exercise 9.61. Null hypothesis `μ = 88` against `μ ≠ 88`: exact negations of each other, and the test is two-tailed. -/
@[kb "openstaxintrostats2e" "Exercise 9.61, p. 503"]
theorem ex_9_61_equal_88_test_type :
    (∀ μ : ℝ, μ = 88 ↔ ¬ μ ≠ 88) ∧ Alt.tail Alt.ne = Tail.two := by
  exact ⟨fun μ => not_not.symm, rfl⟩


end Settings

end UndergradKB.Statistics.Course.PracticeC9
