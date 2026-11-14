import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF
import UndergradKB.Common.Attr
import UndergradKB.Statistics.NormalCdf
import UndergradKB.Statistics.CriticalValues
import UndergradKB.Statistics.EmpiricalRule
import UndergradKB.Statistics.Continuous

/-!
# Course layer, chapter 7 (OpenStax *Introductory Statistics 2e*): central limit theorem examples

The book applies the normal approximation to a sample mean or a sample sum.  Here the approximation
is taken as the hypothesis: the mean (or sum) `X` has the law `N(μ, σ²)` with the mean and variance
the book computes (`HasLaw X (gaussianReal μ v.toNNReal) P`).  We prove the standard-error
arithmetic exactly and enclose every probability and percentile of the example in a two-sided bound
around the book's rounded value.  The numerical values of the standard normal distribution function
`Φ` come from the alternating Taylor enclosures of `EmpiricalRule.lean`.
-/

namespace UndergradKB.Statistics.Course.ExamplesC7

open MeasureTheory ProbabilityTheory Set UndergradKB.Statistics

local notation "Φ" => cdf (gaussianReal 0 1)

/-! ### General reductions to `Φ` -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}

/-- Enclosure of `Φ z` from the Taylor enclosure of the central mass. -/
lemma Phi_enc {z A B : ℝ} (hz : 0 ≤ z) (m : ℕ) (hA : 1 / 2 < A)
    (hl : (2 * A - 1) * 2.5067 < 2 * empR (2 * m) z)
    (hu : 2 * empR (2 * m + 1) z < (2 * B - 1) * 2.5066) : A < Φ z ∧ Φ z < B := by
  have h := Ioo_enclosure hz m (by linarith) hl hu
  rw [stdNormalCdf_eq_Ioo hz]
  constructor <;> linarith [h.1, h.2]

/-- Enclosure of `Φ` at a point from enclosures at nearby points. -/
lemma Phi_between {z lo hi L U : ℝ} (h1 : lo ≤ z) (h2 : z ≤ hi) (hL : L < Φ lo) (hU : Φ hi < U) :
    L < Φ z ∧ Φ z < U :=
  ⟨lt_of_lt_of_le hL ((cdf (gaussianReal 0 1)).mono h1),
    lt_of_le_of_lt ((cdf (gaussianReal 0 1)).mono h2) hU⟩

lemma Phi_lt_one (z : ℝ) : Φ z < 1 := (stdNormalCdf_properties.2.2.2.2 z).2

lemma Phi_pos (z : ℝ) : 0 < Φ z := (stdNormalCdf_properties.2.2.2.2 z).1

lemma Phi_zero : Φ 0 = 1 / 2 := by
  rw [stdNormalCdf_eq_Ioo le_rfl]
  simp

lemma sqrt_bd {n a b : ℝ} (ha0 : 0 ≤ a) (ha : a ^ 2 < n) (hb : n < b ^ 2) (hb0 : 0 ≤ b) :
    a < Real.sqrt n ∧ Real.sqrt n < b :=
  ⟨(Real.lt_sqrt ha0).2 ha, (Real.sqrt_lt' (lt_of_le_of_lt ha0 (by nlinarith))).2 hb⟩

/-- A sample mean with variance `s²/n` has standard deviation `s/√n`. -/
lemma law_mean {μ s n : ℝ} (hn : 0 < n)
    (hX : HasLaw X (gaussianReal μ ((s ^ 2 / n : ℝ).toNNReal)) P) :
    HasLaw X (gaussianReal μ ((s / Real.sqrt n) ^ 2).toNNReal) P := by
  rwa [div_pow, Real.sq_sqrt hn.le]

/-- A sample sum with variance `n s²` has standard deviation `√n s`. -/
lemma law_sum {μ s n : ℝ} (hn : 0 < n)
    (hX : HasLaw X (gaussianReal μ ((n * s ^ 2 : ℝ).toNNReal)) P) :
    HasLaw X (gaussianReal μ ((Real.sqrt n * s) ^ 2).toNNReal) P := by
  rwa [mul_pow, Real.sq_sqrt hn.le]

lemma prob_std {μ σ : ℝ} (hσ : 0 < σ) (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P)
    {S A : Set ℝ} (hS : MeasurableSet S) (hA : ∀ x, x ∈ A ↔ (x - μ) / σ ∈ S) :
    P.real {ω | X ω ∈ A} = (gaussianReal 0 1).real S := by
  have e : {ω | X ω ∈ A} = (fun ω ↦ (X ω - μ) / σ) ⁻¹' S := by
    ext ω; simp [hA]
  rw [e, real_preimage_of_hasLaw (standardized_hasLaw hσ hX) hS]

lemma prob_lt {μ σ : ℝ} (hσ : 0 < σ) (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) (x : ℝ) :
    P.real {ω | X ω < x} = Φ ((x - μ) / σ) := by
  have h := prob_std hσ hX (S := Iio ((x - μ) / σ)) (A := Iio x) measurableSet_Iio (by
    intro y
    simp only [mem_Iio]
    rw [div_lt_div_iff_of_pos_right hσ]
    constructor <;> intro h <;> linarith)
  simp only [mem_Iio] at h
  rw [h, measureReal_congr Iio_ae_eq_Iic, cdf_eq_real]

lemma prob_gt {μ σ : ℝ} (hσ : 0 < σ) (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) (x : ℝ) :
    P.real {ω | x < X ω} = 1 - Φ ((x - μ) / σ) := by
  have h := prob_std hσ hX (S := Ioi ((x - μ) / σ)) (A := Ioi x) measurableSet_Ioi (by
    intro y
    simp only [mem_Ioi]
    rw [div_lt_div_iff_of_pos_right hσ]
    constructor <;> intro h <;> linarith)
  simp only [mem_Ioi] at h
  rw [h, ← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, cdf_eq_real]

lemma prob_ge {μ σ : ℝ} (hσ : 0 < σ) (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) (x : ℝ) :
    P.real {ω | x ≤ X ω} = 1 - Φ ((x - μ) / σ) := by
  have h := prob_std hσ hX (S := Ici ((x - μ) / σ)) (A := Ici x) measurableSet_Ici (by
    intro y
    simp only [mem_Ici]
    rw [div_le_div_iff_of_pos_right hσ]
    constructor <;> intro h <;> linarith)
  simp only [mem_Ici] at h
  rw [h, ← compl_Iio, probReal_compl_eq_one_sub measurableSet_Iio,
    measureReal_congr Iio_ae_eq_Iic, cdf_eq_real]

lemma prob_Ioo {μ σ : ℝ} (hσ : 0 < σ) (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P)
    {a b : ℝ} (hab : a ≤ b) :
    P.real {ω | a < X ω ∧ X ω < b} = Φ ((b - μ) / σ) - Φ ((a - μ) / σ) := by
  have h := prob_std hσ hX (S := Ioo ((a - μ) / σ) ((b - μ) / σ)) (A := Ioo a b)
    measurableSet_Ioo (by
    intro y
    simp only [mem_Ioo]
    rw [div_lt_div_iff_of_pos_right hσ, div_lt_div_iff_of_pos_right hσ]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith)
  simp only [mem_Ioo] at h
  rw [h, measureReal_congr Ioo_ae_eq_Ioc]
  have hab' : (a - μ) / σ ≤ (b - μ) / σ := by gcongr
  have e2 : Ioc ((a - μ) / σ) ((b - μ) / σ) = Iic ((b - μ) / σ) \ Iic ((a - μ) / σ) := by
    ext x; simp [and_comm]
  rw [e2, measureReal_diff (Iic_subset_Iic.2 hab') measurableSet_Iic,
    ← cdf_eq_real, ← cdf_eq_real]

/-- Percentile of a normal law enclosed by `z`-scores: if `Φ lo < p < Φ hi` then the `p`-th
percentile `k` exists with `μ + σ lo < k < μ + σ hi` and `P(X ≤ k) = p`. -/
lemma percentile_bd {μ σ : ℝ} (hσ : 0 < σ) (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P)
    {p lo hi : ℝ} (h0 : 0 < p) (h1 : p < 1) (hlo : Φ lo < p) (hhi : p < Φ hi) :
    ∃ k, P.real {ω | X ω ≤ k} = p ∧ μ + σ * lo < k ∧ k < μ + σ * hi := by
  have hq := stdNormalCdf_normalQuantile h0 h1
  have hmono := stdNormalCdf_properties.2.1
  refine ⟨μ + σ * normalQuantile p, (normal_percentile hσ hX h0 h1).1, ?_, ?_⟩
  · have : lo < normalQuantile p := by
      by_contra h
      have := hmono.monotone (not_lt.1 h)
      linarith [hq.1]
    nlinarith
  · have : normalQuantile p < hi := by
      by_contra h
      have := hmono.monotone (not_lt.1 h)
      linarith [hq.1]
    nlinarith

/-! ### Values of `Φ` -/

lemma phi_2_8284 : (0.99763 : ℝ) < Φ 2.8284 ∧ Φ 2.8284 < 0.99770 :=
  Phi_enc (by norm_num) 8 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_2_8285 : (0.99763 : ℝ) < Φ 2.8285 ∧ Φ 2.8285 < 0.99770 :=
  Phi_enc (by norm_num) 8 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_3_5 : (0.99973 : ℝ) < Φ 3.5 ∧ Φ 3.5 < 0.99980 :=
  Phi_enc (by norm_num) 11 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_8_3 : (0.99613 : ℝ) < Φ (8/3 : ℝ) ∧ Φ (8/3 : ℝ) < 0.99620 :=
  Phi_enc (by norm_num) 7 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_1_64 : (0.94946 : ℝ) < Φ 1.64 ∧ Φ 1.64 < 0.94953 :=
  Phi_enc (by norm_num) 4 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_1_7 : (0.95540 : ℝ) < Φ 1.7 ∧ Φ 1.7 < 0.95547 :=
  Phi_enc (by norm_num) 4 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_1_25 : (0.89432 : ℝ) < Φ 1.25 ∧ Φ 1.25 < 0.89439 :=
  Phi_enc (by norm_num) 3 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_1_31 : (0.90487 : ℝ) < Φ 1.31 ∧ Φ 1.31 < 0.90494 :=
  Phi_enc (by norm_num) 3 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_1_5491 : (0.93929 : ℝ) < Φ 1.5491 ∧ Φ 1.5491 < 0.93936 :=
  Phi_enc (by norm_num) 4 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_1_5492 : (0.93930 : ℝ) < Φ 1.5492 ∧ Φ 1.5492 < 0.93937 :=
  Phi_enc (by norm_num) 4 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_2_3237 : (0.98989 : ℝ) < Φ 2.3237 ∧ Φ 2.3237 < 0.98996 :=
  Phi_enc (by norm_num) 6 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_2_3238 : (0.98990 : ℝ) < Φ 2.3238 ∧ Φ 2.3238 < 0.98997 :=
  Phi_enc (by norm_num) 6 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_2_236 : (0.98729 : ℝ) < Φ 2.236 ∧ Φ 2.236 < 0.98736 :=
  Phi_enc (by norm_num) 6 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_2_2361 : (0.98729 : ℝ) < Φ 2.2361 ∧ Φ 2.2361 < 0.98736 :=
  Phi_enc (by norm_num) 6 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_0_8395 : (0.79937 : ℝ) < Φ 0.8395 ∧ Φ 0.8395 < 0.79944 :=
  Phi_enc (by norm_num) 2 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_0_848 : (0.80175 : ℝ) < Φ 0.848 ∧ Φ 0.848 < 0.80182 :=
  Phi_enc (by norm_num) 3 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_0_9428 : (0.82707 : ℝ) < Φ 0.9428 ∧ Φ 0.9428 < 0.82714 :=
  Phi_enc (by norm_num) 3 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_0_9429 : (0.82710 : ℝ) < Φ 0.9429 ∧ Φ 0.9429 < 0.82717 :=
  Phi_enc (by norm_num) 3 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_1_8856 : (0.97029 : ℝ) < Φ 1.8856 ∧ Φ 1.8856 < 0.97036 :=
  Phi_enc (by norm_num) 5 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_1_8857 : (0.97030 : ℝ) < Φ 1.8857 ∧ Φ 1.8857 < 0.97037 :=
  Phi_enc (by norm_num) 5 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_3_2 : (0.99928 : ℝ) < Φ 3.2 ∧ Φ 3.2 < 0.99935 :=
  Phi_enc (by norm_num) 10 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_1_275 : (0.89881 : ℝ) < Φ 1.275 ∧ Φ 1.275 < 0.89888 :=
  Phi_enc (by norm_num) 3 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_1_35 : (0.91146 : ℝ) < Φ 1.35 ∧ Φ 1.35 < 0.91153 :=
  Phi_enc (by norm_num) 4 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_2_5 : (0.99376 : ℝ) < Φ 2.5 ∧ Φ 2.5 < 0.99383 :=
  Phi_enc (by norm_num) 7 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_1_27 : (0.89792 : ℝ) < Φ 1.27 ∧ Φ 1.27 < 0.89799 :=
  Phi_enc (by norm_num) 3 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_1_29 : (0.90144 : ℝ) < Φ 1.29 ∧ Φ 1.29 < 0.90151 :=
  Phi_enc (by norm_num) 3 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_0_8131 : (0.79188 : ℝ) < Φ 0.8131 ∧ Φ 0.8131 < 0.79195 :=
  Phi_enc (by norm_num) 2 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_0_8132 : (0.79191 : ℝ) < Φ 0.8132 ∧ Φ 0.8132 < 0.79198 :=
  Phi_enc (by norm_num) 2 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_1_61 : (0.94627 : ℝ) < Φ 1.61 ∧ Φ 1.61 < 0.94634 :=
  Phi_enc (by norm_num) 4 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_1_646 : (0.95008 : ℝ) < Φ 1.646 ∧ Φ 1.646 < 0.95015 :=
  Phi_enc (by norm_num) 4 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_0_67 : (0.74854 : ℝ) < Φ 0.67 ∧ Φ 0.67 < 0.74861 :=
  Phi_enc (by norm_num) 2 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_0_68 : (0.75171 : ℝ) < Φ 0.68 ∧ Φ 0.68 < 0.75178 :=
  Phi_enc (by norm_num) 2 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_3 : (0.99862 : ℝ) < Φ 3 ∧ Φ 3 < 0.99869 :=
  Phi_enc (by norm_num) 9 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_41_18 : (0.98860 : ℝ) < Φ (41/18 : ℝ) ∧ Φ (41/18 : ℝ) < 0.98867 :=
  Phi_enc (by norm_num) 6 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_859_630 : (0.91360 : ℝ) < Φ (859/630 : ℝ) ∧ Φ (859/630 : ℝ) < 0.91367 :=
  Phi_enc (by norm_num) 4 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_809_630 : (0.90042 : ℝ) < Φ (809/630 : ℝ) ∧ Φ (809/630 : ℝ) < 0.90049 :=
  Phi_enc (by norm_num) 3 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_1_65 : (0.95049 : ℝ) < Φ 1.65 ∧ Φ 1.65 < 0.95056 :=
  Phi_enc (by norm_num) 4 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_1_285 : (0.90057 : ℝ) < Φ 1.285 ∧ Φ 1.285 < 0.90064 :=
  Phi_enc (by norm_num) 3 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_1_0989 : (0.86406 : ℝ) < Φ 1.0989 ∧ Φ 1.0989 < 0.86413 :=
  Phi_enc (by norm_num) 3 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_1_099 : (0.86408 : ℝ) < Φ 1.099 ∧ Φ 1.099 < 0.86415 :=
  Phi_enc (by norm_num) 3 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_0_1735 : (0.56884 : ℝ) < Φ 0.1735 ∧ Φ 0.1735 < 0.56891 :=
  Phi_enc (by norm_num) 1 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_0_1736 : (0.56888 : ℝ) < Φ 0.1736 ∧ Φ 0.1736 < 0.56895 :=
  Phi_enc (by norm_num) 1 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_0_4048 : (0.65715 : ℝ) < Φ 0.4048 ∧ Φ 0.4048 < 0.65722 :=
  Phi_enc (by norm_num) 2 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_0_4049 : (0.65719 : ℝ) < Φ 0.4049 ∧ Φ 0.4049 < 0.65726 :=
  Phi_enc (by norm_num) 2 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_1_4459 : (0.92586 : ℝ) < Φ 1.4459 ∧ Φ 1.4459 < 0.92593 :=
  Phi_enc (by norm_num) 4 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_1_446 : (0.92588 : ℝ) < Φ 1.446 ∧ Φ 1.446 < 0.92595 :=
  Phi_enc (by norm_num) 4 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_1_9086 : (0.97181 : ℝ) < Φ 1.9086 ∧ Φ 1.9086 < 0.97188 :=
  Phi_enc (by norm_num) 5 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_1_9088 : (0.97182 : ℝ) < Φ 1.9088 ∧ Φ 1.9088 < 0.97189 :=
  Phi_enc (by norm_num) 5 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_1_793 : (0.96348 : ℝ) < Φ 1.793 ∧ Φ 1.793 < 0.96355 :=
  Phi_enc (by norm_num) 5 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

lemma phi_1_7931 : (0.96349 : ℝ) < Φ 1.7931 ∧ Φ 1.7931 < 0.96356 :=
  Phi_enc (by norm_num) 5 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

/-! ### Auxiliary facts -/

lemma Phi_mono {a b : ℝ} (h : a ≤ b) : Φ a ≤ Φ b := (cdf (gaussianReal 0 1)).mono h

/-- Enclosure of `Φ (c / s)` for a quotient with `s` known to lie between two numbers. -/
lemma Phi_div {c s s1 s2 lo hi L U : ℝ} (h0 : 0 < s1) (h1 : s1 < s) (h2 : s < s2)
    (hlo0 : 0 ≤ lo) (hhi0 : 0 ≤ hi) (hlo : lo * s2 ≤ c) (hhi : c ≤ hi * s1) (hL : L < Φ lo)
    (hU : Φ hi < U) : L < Φ (c / s) ∧ Φ (c / s) < U := by
  have hs : 0 < s := by linarith
  refine Phi_between (lo := lo) (hi := hi) ?_ ?_ hL hU
  · rw [le_div_iff₀ hs]; nlinarith
  · rw [div_le_iff₀ hs]; nlinarith

lemma sqrt_25 : Real.sqrt 25 = 5 := by
  rw [show (25 : ℝ) = 5 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)

lemma sqrt_49 : Real.sqrt 49 = 7 := by
  rw [show (49 : ℝ) = 7 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)

lemma sqrt_100 : Real.sqrt 100 = 10 := by
  rw [show (100 : ℝ) = 10 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)

/-! ### Section 7.1: sample means -/

/-- OpenStax Introductory Statistics 2e Example 7.2. The time (in hours) of an over-40 soccer match
is normal with mean 2 and standard deviation 0.5; for a sample of 50 matches the sample mean has the
normal law with mean 2 and variance `0.5² / 50`. The probability that it lies between 1.8 and 2.3
hours is enclosed in `(0.9973, 0.9978)` (the book's `0.9977`). -/
@[kb "openstaxintrostats2e" "Example 7.2, p. 380"]
theorem example_7_2_soccer_mean_probability [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal 2 ((0.5 ^ 2 / 50 : ℝ).toNNReal)) P) :
    0.9973 < P.real {ω | 1.8 < X ω ∧ X ω < 2.3} ∧
      P.real {ω | 1.8 < X ω ∧ X ω < 2.3} < 0.9978 := by
  have hs := sqrt_bd (n := (50 : ℝ)) (a := 7.0710) (b := 7.0711) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hne : Real.sqrt 50 ≠ 0 := by positivity
  have hpos : 0 < 0.5 / Real.sqrt 50 := by positivity
  have hX' := law_mean (s := 0.5) (n := 50) (by norm_num) hX
  have hP := prob_Ioo hpos hX' (a := 1.8) (b := 2.3) (by norm_num)
  have e1 : (2.3 - 2) / (0.5 / Real.sqrt 50) = 0.6 * Real.sqrt 50 := by
    field_simp; norm_num
  have e2 : (1.8 - 2) / (0.5 / Real.sqrt 50) = -(0.4 * Real.sqrt 50) := by
    field_simp; norm_num
  rw [hP, e1, e2, stdNormalCdf_neg]
  have h3 := Phi_between (z := 0.4 * Real.sqrt 50) (lo := 2.8284) (hi := 2.8285)
    (by linarith [hs.1]) (by linarith [hs.2]) phi_2_8284.1 phi_2_8285.2
  have h4 : (0.99973 : ℝ) < Φ (0.6 * Real.sqrt 50) :=
    lt_of_lt_of_le phi_3_5.1 (Phi_mono (by linarith [hs.1]))
  have h5 := Phi_lt_one (0.6 * Real.sqrt 50)
  constructor <;> linarith [h3.1, h3.2]

/-- OpenStax Introductory Statistics 2e Example 7.3 (standard error). With population standard
deviation 15 and a sample of size 100, the standard deviation of the sample mean is
`15 / √100 = 3/2`. -/
@[kb "openstaxintrostats2e" "Example 7.3, p. 381"]
theorem example_7_3_ipad_standard_error : 15 / Real.sqrt 100 = 3 / 2 := by
  rw [sqrt_100]; norm_num

/-- OpenStax Introductory Statistics 2e Example 7.3 (probability). The mean age of the sample of 100
iPad users has the normal law with mean 34 and variance `15² / 100` (standard deviation `1.5`). The
probability that it exceeds 30 lies in `(0.9961, 0.9963)` (the book's `0.9962`). -/
@[kb "openstaxintrostats2e" "Example 7.3, p. 381"]
theorem example_7_3_ipad_mean_over_30 [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal 34 ((15 ^ 2 / 100 : ℝ).toNNReal)) P) :
    0.9961 < P.real {ω | 30 < X ω} ∧ P.real {ω | 30 < X ω} < 0.9963 := by
  have hX' := law_mean (s := 15) (n := 100) (by norm_num) hX
  rw [sqrt_100] at hX'
  have hP := prob_gt (by norm_num : (0 : ℝ) < 15 / 10) hX' 30
  have e : ((30 : ℝ) - 34) / (15 / 10) = -(8 / 3) := by norm_num
  rw [hP, e, stdNormalCdf_neg]
  constructor <;> linarith [phi_8_3.1, phi_8_3.2]

/-- OpenStax Introductory Statistics 2e Example 7.3 (percentile). For the same normal law of the
sample mean, the 95th percentile `k` (the number with `P(X̄ ≤ k) = 0.95`) exists and lies in
`(36.45, 36.55)`, that is `36.5` to one decimal place as in the book. -/
@[kb "openstaxintrostats2e" "Example 7.3, p. 381"]
theorem example_7_3_ipad_percentile [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal 34 ((15 ^ 2 / 100 : ℝ).toNNReal)) P) :
    ∃ k, P.real {ω | X ω ≤ k} = 0.95 ∧ 36.45 < k ∧ k < 36.55 := by
  have hX' := law_mean (s := 15) (n := 100) (by norm_num) hX
  rw [sqrt_100] at hX'
  obtain ⟨k, hk, h1, h2⟩ := percentile_bd (by norm_num : (0 : ℝ) < 15 / 10) hX' (p := 0.95)
    (lo := 1.64) (hi := 1.7) (by norm_num) (by norm_num) (by linarith [phi_1_64.2])
    (by linarith [phi_1_7.1])
  exact ⟨k, hk, by linarith, by linarith⟩

/-- OpenStax Introductory Statistics 2e Example 7.4 (standard error). With standard deviation 1
minute and a sample of 60 users, the standard deviation of the sample mean (the standard error of the
mean) is `1/√60`, strictly between `0.129` and `0.1292`. -/
@[kb "openstaxintrostats2e" "Example 7.4, p. 382"]
theorem example_7_4_standard_error :
    0.129 < 1 / Real.sqrt 60 ∧ 1 / Real.sqrt 60 < 0.1292 := by
  have hs := sqrt_bd (n := (60 : ℝ)) (a := 7.7459) (b := 7.7460) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hpos : 0 < Real.sqrt 60 := by positivity
  constructor
  · rw [lt_div_iff₀ hpos]; linarith [hs.2]
  · rw [div_lt_iff₀ hpos]; linarith [hs.1]

/-- OpenStax Introductory Statistics 2e Example 7.4 (percentile). The sample mean of 60 app-engagement
times has the normal law with mean `8.2` and variance `1² / 60`. Its 90th percentile `k` exists and lies
in `(8.36, 8.37)` (the book's `8.37`). -/
@[kb "openstaxintrostats2e" "Example 7.4, p. 382"]
theorem example_7_4_percentile [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal 8.2 ((1 ^ 2 / 60 : ℝ).toNNReal)) P) :
    ∃ k, P.real {ω | X ω ≤ k} = 0.9 ∧ 8.36 < k ∧ k < 8.37 := by
  have hs := sqrt_bd (n := (60 : ℝ)) (a := 7.7459) (b := 7.7460) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hpos : 0 < Real.sqrt 60 := by positivity
  have hX' := law_mean (s := 1) (n := 60) (by norm_num) hX
  have hσ : 0 < 1 / Real.sqrt 60 := by positivity
  have hσ1 : 0.129 < 1 / Real.sqrt 60 := by rw [lt_div_iff₀ hpos]; linarith [hs.2]
  have hσ2 : 1 / Real.sqrt 60 < 0.1292 := by rw [div_lt_iff₀ hpos]; linarith [hs.1]
  obtain ⟨k, hk, h1, h2⟩ := percentile_bd hσ hX' (p := 0.9) (lo := 1.25) (hi := 1.31)
    (by norm_num) (by norm_num) (by linarith [phi_1_25.2]) (by linarith [phi_1_31.1])
  exact ⟨k, hk, by linarith, by linarith⟩

/-- OpenStax Introductory Statistics 2e Example 7.4 (probability). For the same normal law of the
sample mean, the probability that it lies between 8 and 8.5 minutes is enclosed in
`(0.9291, 0.9295)` (the book's `0.9293`). -/
@[kb "openstaxintrostats2e" "Example 7.4, p. 382"]
theorem example_7_4_probability [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal 8.2 ((1 ^ 2 / 60 : ℝ).toNNReal)) P) :
    0.9291 < P.real {ω | 8 < X ω ∧ X ω < 8.5} ∧ P.real {ω | 8 < X ω ∧ X ω < 8.5} < 0.9295 := by
  have hs := sqrt_bd (n := (60 : ℝ)) (a := 7.7459) (b := 7.7460) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hne : Real.sqrt 60 ≠ 0 := by positivity
  have hX' := law_mean (s := 1) (n := 60) (by norm_num) hX
  have hσ : 0 < 1 / Real.sqrt 60 := by positivity
  have hP := prob_Ioo hσ hX' (a := 8) (b := 8.5) (by norm_num)
  have e1 : (8.5 - 8.2) / (1 / Real.sqrt 60) = 0.3 * Real.sqrt 60 := by
    field_simp; norm_num
  have e2 : (8 - 8.2) / (1 / Real.sqrt 60) = -(0.2 * Real.sqrt 60) := by
    field_simp; norm_num
  rw [hP, e1, e2, stdNormalCdf_neg]
  have h3 := Phi_between (z := 0.2 * Real.sqrt 60) (lo := 1.5491) (hi := 1.5492)
    (by linarith [hs.1]) (by linarith [hs.2]) phi_1_5491.1 phi_1_5492.2
  have h4 := Phi_between (z := 0.3 * Real.sqrt 60) (lo := 2.3237) (hi := 2.3238)
    (by linarith [hs.1]) (by linarith [hs.2]) phi_2_3237.1 phi_2_3238.2
  constructor <;> linarith [h3.1, h3.2, h4.1, h4.2]

/-! ### Section 7.2: sample sums -/

/-- OpenStax Introductory Statistics 2e Example 7.5 (probability). The sum `S` of 80 values from a
population with mean 90 and standard deviation 15 has the normal law with mean `80 · 90 = 7200` and
variance `80 · 15²`. The probability that it exceeds 7500 lies in `(0.0126, 0.0128)` (the book's
`0.0127`). -/
@[kb "openstaxintrostats2e" "Example 7.5, p. 383"]
theorem example_7_5_sum_probability [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal (80 * 90) ((80 * 15 ^ 2 : ℝ).toNNReal)) P) :
    0.0126 < P.real {ω | 7500 < X ω} ∧ P.real {ω | 7500 < X ω} < 0.0128 := by
  have hs := sqrt_bd (n := (80 : ℝ)) (a := 8.9442) (b := 8.9443) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hX' := law_sum (s := 15) (n := 80) (by norm_num) hX
  rw [show (80 * 90 : ℝ) = 7200 by norm_num] at hX'
  have hσ : 0 < Real.sqrt 80 * 15 := by have := hs.1; positivity
  have hP := prob_gt hσ hX' 7500
  have e : ((7500 : ℝ) - 7200) / (Real.sqrt 80 * 15) = 300 / (Real.sqrt 80 * 15) := by norm_num
  rw [hP, e]
  have h := Phi_div (c := 300) (s := Real.sqrt 80 * 15) (s1 := 134.163) (s2 := 134.1645)
    (lo := 2.236) (hi := 2.2361) (by norm_num) (by linarith [hs.1]) (by linarith [hs.2])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) phi_2_236.1 phi_2_2361.2
  constructor <;> linarith [h.1, h.2]

/-- OpenStax Introductory Statistics 2e Example 7.5 (the sum 1.5 standard deviations above the
mean). The mean of the sums is `80 · 90 = 7200` and the sum `7200 + 1.5 · (√80 · 15)` lies in
`(7401.2, 7401.3)` (the book's `7,401.2`). -/
@[kb "openstaxintrostats2e" "Example 7.5, p. 383"]
theorem example_7_5_sum_above_mean :
    (80 : ℝ) * 90 = 7200 ∧ 7401.2 < 80 * 90 + 1.5 * (Real.sqrt 80 * 15) ∧
      80 * 90 + 1.5 * (Real.sqrt 80 * 15) < 7401.3 := by
  have hs := sqrt_bd (n := (80 : ℝ)) (a := 8.9442) (b := 8.9443) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  refine ⟨by norm_num, by linarith [hs.1], by linarith [hs.2]⟩

/-- OpenStax Introductory Statistics 2e Example 7.6 (mean and standard deviation of the sum). The sum
of 50 ages with mean 34 and standard deviation 15 has mean `50 · 34 = 1700` and standard deviation
`√50 · 15`, strictly between `106.06` and `106.07` (the book's `106.07`). -/
@[kb "openstaxintrostats2e" "Example 7.6, p. 384"]
theorem example_7_6_mean_and_sd_of_sum :
    (50 : ℝ) * 34 = 1700 ∧ 106.06 < Real.sqrt 50 * 15 ∧ Real.sqrt 50 * 15 < 106.07 := by
  have hs := sqrt_bd (n := (50 : ℝ)) (a := 7.0710) (b := 7.0711) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  refine ⟨by norm_num, by linarith [hs.1], by linarith [hs.2]⟩

/-- OpenStax Introductory Statistics 2e Example 7.6 (probability). The sum of the 50 ages has the
normal law with mean `50 · 34` and variance `50 · 15²`. The probability that it lies between 1500
and 1800 is enclosed in `(0.7973, 0.7976)` (the book's `0.7974`). -/
@[kb "openstaxintrostats2e" "Example 7.6, p. 384"]
theorem example_7_6_probability [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal (50 * 34) ((50 * 15 ^ 2 : ℝ).toNNReal)) P) :
    0.7973 < P.real {ω | 1500 < X ω ∧ X ω < 1800} ∧
      P.real {ω | 1500 < X ω ∧ X ω < 1800} < 0.7976 := by
  have hs := sqrt_bd (n := (50 : ℝ)) (a := 7.0710) (b := 7.0711) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hX' := law_sum (s := 15) (n := 50) (by norm_num) hX
  rw [show (50 * 34 : ℝ) = 1700 by norm_num] at hX'
  have hσ : 0 < Real.sqrt 50 * 15 := by have := hs.1; positivity
  have hP := prob_Ioo hσ hX' (a := 1500) (b := 1800) (by norm_num)
  have e1 : ((1800 : ℝ) - 1700) / (Real.sqrt 50 * 15) = 100 / (Real.sqrt 50 * 15) := by norm_num
  have e2 : ((1500 : ℝ) - 1700) / (Real.sqrt 50 * 15) = -(200 / (Real.sqrt 50 * 15)) := by
    rw [← neg_div]; norm_num
  rw [hP, e1, e2, stdNormalCdf_neg]
  have h3 := Phi_div (c := 100) (s := Real.sqrt 50 * 15) (s1 := 106.065) (s2 := 106.0665)
    (lo := 0.9428) (hi := 0.9429) (by norm_num) (by linarith [hs.1]) (by linarith [hs.2])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) phi_0_9428.1 phi_0_9429.2
  have h4 := Phi_div (c := 200) (s := Real.sqrt 50 * 15) (s1 := 106.065) (s2 := 106.0665)
    (lo := 1.8856) (hi := 1.8857) (by norm_num) (by linarith [hs.1]) (by linarith [hs.2])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) phi_1_8856.1 phi_1_8857.2
  constructor <;> linarith [h3.1, h3.2, h4.1, h4.2]

/-- OpenStax Introductory Statistics 2e Example 7.6 (percentile). For the same normal law of the sum,
the 80th percentile `k` exists and lies in `(1789, 1790)` (the book's `1,789.3`). -/
@[kb "openstaxintrostats2e" "Example 7.6, p. 384"]
theorem example_7_6_percentile [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal (50 * 34) ((50 * 15 ^ 2 : ℝ).toNNReal)) P) :
    ∃ k, P.real {ω | X ω ≤ k} = 0.8 ∧ 1789 < k ∧ k < 1790 := by
  have hs := sqrt_bd (n := (50 : ℝ)) (a := 7.0710) (b := 7.0711) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hX' := law_sum (s := 15) (n := 50) (by norm_num) hX
  rw [show (50 * 34 : ℝ) = 1700 by norm_num] at hX'
  have hσ : 0 < Real.sqrt 50 * 15 := by have := hs.1; positivity
  obtain ⟨k, hk, h1, h2⟩ := percentile_bd hσ hX' (p := 0.8) (lo := 0.8395) (hi := 0.848)
    (by norm_num) (by norm_num) (by linarith [phi_0_8395.2]) (by linarith [phi_0_848.1])
  exact ⟨k, hk, by nlinarith [hs.1], by nlinarith [hs.2]⟩

/-! ### Section 7.3: using the central limit theorem -/

/-- OpenStax Introductory Statistics 2e Example 7.8 (moments of the stress score). A stress score that
is uniform on `[1, 5]` has mean `3` and variance `4/3`; for 75 students the sample mean has variance
`(4/3)/75 = (2/15)²` (standard deviation `2/15`) and the sum has variance `75 · 4/3 = 10²`. -/
@[kb "openstaxintrostats2e" "Example 7.8, p. 386"]
theorem example_7_8_uniform_moments [IsProbabilityMeasure P]
    (hX : pdf.IsUniform X (Icc (1 : ℝ) 5) P) :
    P[X] = 3 ∧ variance X P = 4 / 3 ∧ (4 / 3 : ℝ) / 75 = (2 / 15) ^ 2 ∧
      (75 : ℝ) * (4 / 3) = 10 ^ 2 := by
  refine ⟨?_, ?_, by norm_num, by norm_num⟩
  · rw [uniform_mean hX (by norm_num)]; norm_num
  · rw [uniform_variance hX (by norm_num)]; norm_num

/-- OpenStax Introductory Statistics 2e Example 7.8 (a), (b). The mean stress score of 75 students has
the normal law with mean 3 and variance `4² / 12 / 75` (standard deviation `2/15`). The probability
that it is below 2 is under `0.001` (the book: about zero), and its 90th percentile `k` exists and
lies in `(3.17, 3.18)` (the book's `3.2`). -/
@[kb "openstaxintrostats2e" "Example 7.8, p. 386"]
theorem example_7_8_mean [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal 3 ((4 ^ 2 / 12 / 75 : ℝ).toNNReal)) P) :
    P.real {ω | X ω < 2} < 0.001 ∧
      ∃ k, P.real {ω | X ω ≤ k} = 0.9 ∧ 3.17 < k ∧ k < 3.18 := by
  have e : ((2 : ℝ) / 15) ^ 2 = 4 ^ 2 / 12 / 75 := by norm_num
  rw [← e] at hX
  have hσ : (0 : ℝ) < 2 / 15 := by norm_num
  constructor
  · rw [prob_lt hσ hX 2]
    have e1 : ((2 : ℝ) - 3) / (2 / 15) = -(15 / 2) := by norm_num
    rw [e1, stdNormalCdf_neg]
    have h1 : Φ 3.2 ≤ Φ (15 / 2) := Phi_mono (by norm_num)
    linarith [phi_3_2.1]
  · obtain ⟨k, hk, h1, h2⟩ := percentile_bd hσ hX (p := 0.9) (lo := 1.275) (hi := 1.35)
      (by norm_num) (by norm_num) (by linarith [phi_1_275.2]) (by linarith [phi_1_35.1])
    exact ⟨k, hk, by linarith, by linarith⟩

/-- OpenStax Introductory Statistics 2e Example 7.8 (c), (d). The total of 75 stress scores has the
normal law with mean `75 · 3 = 225` and variance `75 · (4² / 12) = 10²`. The probability that the
total is below 200 lies in `(0.0061, 0.0063)` (the book's `0.0062`), and the 90th percentile `k` of the
total exists and lies in `(237.7, 237.9)` (the book's `237.8`). -/
@[kb "openstaxintrostats2e" "Example 7.8, p. 386"]
theorem example_7_8_sum [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal (75 * 3) ((75 * (4 ^ 2 / 12) : ℝ).toNNReal)) P) :
    (0.0061 < P.real {ω | X ω < 200} ∧ P.real {ω | X ω < 200} < 0.0063) ∧
      ∃ k, P.real {ω | X ω ≤ k} = 0.9 ∧ 237.7 < k ∧ k < 237.9 := by
  have e : ((10 : ℝ)) ^ 2 = 75 * (4 ^ 2 / 12) := by norm_num
  rw [← e, show (75 * 3 : ℝ) = 225 by norm_num] at hX
  have hσ : (0 : ℝ) < 10 := by norm_num
  constructor
  · rw [prob_lt hσ hX 200]
    have e1 : ((200 : ℝ) - 225) / 10 = -(5 / 2) := by norm_num
    rw [e1, stdNormalCdf_neg]
    have h : (5 / 2 : ℝ) = 2.5 := by norm_num
    rw [h]
    constructor <;> linarith [phi_2_5.1, phi_2_5.2]
  · obtain ⟨k, hk, h1, h2⟩ := percentile_bd hσ hX (p := 0.9) (lo := 1.27) (hi := 1.29)
      (by norm_num) (by norm_num) (by linarith [phi_1_27.2]) (by linarith [phi_1_29.1])
    exact ⟨k, hk, by linarith, by linarith⟩

/-- OpenStax Introductory Statistics 2e Example 7.9 (moments of the excess time). An exponential
variable with rate `1/22` (mean 22 minutes) has mean 22 and standard deviation 22; the mean of 80 such
times has variance `22² / 80`. -/
@[kb "openstaxintrostats2e" "Example 7.9, p. 388"]
theorem example_7_9_exponential_moments [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hY : HasLaw Y (expMeasure (1 / 22)) P) :
    P[Y] = 22 ∧ variance Y P = 22 ^ 2 := by
  have hm : (0 : ℝ) < 1 / 22 := by norm_num
  refine ⟨?_, ?_⟩
  · rw [expectation_of_hasLaw_exp hY hm]; norm_num
  · rw [variance_of_hasLaw_exp hY hm]; norm_num

/-- OpenStax Introductory Statistics 2e Example 7.9 (a). The mean excess time of 80 customers has the
normal law with mean 22 and variance `22² / 80`. The probability that it exceeds 20 minutes lies in
`(0.7918, 0.7921)` (the book's `0.7919`). -/
@[kb "openstaxintrostats2e" "Example 7.9, p. 388"]
theorem example_7_9_mean_over_20 [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal 22 ((22 ^ 2 / 80 : ℝ).toNNReal)) P) :
    0.7918 < P.real {ω | 20 < X ω} ∧ P.real {ω | 20 < X ω} < 0.7921 := by
  have hs := sqrt_bd (n := (80 : ℝ)) (a := 8.9442) (b := 8.9443) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hne : Real.sqrt 80 ≠ 0 := by positivity
  have hX' := law_mean (s := 22) (n := 80) (by norm_num) hX
  have hσ : 0 < 22 / Real.sqrt 80 := by positivity
  have hP := prob_gt hσ hX' 20
  have e : ((20 : ℝ) - 22) / (22 / Real.sqrt 80) = -(Real.sqrt 80 / 11) := by
    field_simp; norm_num
  rw [hP, e, stdNormalCdf_neg]
  have h := Phi_between (z := Real.sqrt 80 / 11) (lo := 0.8131) (hi := 0.8132)
    (by linarith [hs.1]) (by linarith [hs.2]) phi_0_8131.1 phi_0_8132.2
  constructor <;> linarith [h.1, h.2]

/-- OpenStax Introductory Statistics 2e Example 7.9 (b). A single excess time is exponential with rate
`1/22`, and `P(Y > 20) = e^{-20/22}`, which lies in `(0.4028, 0.4030)` (the book's `0.4029`). -/
@[kb "openstaxintrostats2e" "Example 7.9, p. 388"]
theorem example_7_9_individual_over_20 [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hY : HasLaw Y (expMeasure (1 / 22)) P) :
    0.4028 < P.real {ω | 20 < Y ω} ∧ P.real {ω | 20 < Y ω} < 0.4030 := by
  rw [expMeasure_survival_of_hasLaw hY (by norm_num) (by norm_num)]
  have h := Real.exp_bound (x := -(10 / 11)) (by norm_num [abs_of_neg]) (n := 8) (by norm_num)
  have e : -(1 / 22 * (20 : ℝ)) = -(10 / 11) := by norm_num
  rw [e]
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_neg] at h
  constructor <;> linarith [h.1, h.2]

/-- OpenStax Introductory Statistics 2e Example 7.9 (c). The two probabilities differ because the
sample mean and a single value have different laws: the probability that the mean of 80 customers
exceeds 20 minutes is strictly larger than the probability that a single customer's excess time does. -/
@[kb "openstaxintrostats2e" "Example 7.9, p. 388"]
theorem example_7_9_mean_versus_individual [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hX : HasLaw X (gaussianReal 22 ((22 ^ 2 / 80 : ℝ).toNNReal)) P)
    (hY : HasLaw Y (expMeasure (1 / 22)) P) :
    P.real {ω | 20 < Y ω} < P.real {ω | 20 < X ω} := by
  have h1 := (example_7_9_mean_over_20 hX).1
  have h2 := (example_7_9_individual_over_20 hY).2
  linarith

/-- OpenStax Introductory Statistics 2e Example 7.9 (percentile). The 95th percentile `k` of the mean
excess time of 80 customers exists and lies in `(25.95, 26.05)` (the book's `26.0`). -/
@[kb "openstaxintrostats2e" "Example 7.9, p. 388"]
theorem example_7_9_percentile [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal 22 ((22 ^ 2 / 80 : ℝ).toNNReal)) P) :
    ∃ k, P.real {ω | X ω ≤ k} = 0.95 ∧ 25.95 < k ∧ k < 26.05 := by
  have hs := sqrt_bd (n := (80 : ℝ)) (a := 8.9442) (b := 8.9443) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hpos : 0 < Real.sqrt 80 := by positivity
  have hX' := law_mean (s := 22) (n := 80) (by norm_num) hX
  have hσ : 0 < 22 / Real.sqrt 80 := by positivity
  have hσ1 : 2.459 < 22 / Real.sqrt 80 := by rw [lt_div_iff₀ hpos]; linarith [hs.2]
  have hσ2 : 22 / Real.sqrt 80 < 2.4605 := by rw [div_lt_iff₀ hpos]; linarith [hs.1]
  obtain ⟨k, hk, h1, h2⟩ := percentile_bd hσ hX' (p := 0.95) (lo := 1.61) (hi := 1.646)
    (by norm_num) (by norm_num) (by linarith [phi_1_61.2]) (by linarith [phi_1_646.1])
  exact ⟨k, hk, by linarith, by linarith⟩

/-- OpenStax Introductory Statistics 2e Example 7.10 (standard error and percentiles of the mean). The
mean time of 100 robberies (population mean 2, standard deviation 0.5) has standard error
`0.5/√100 = 0.05`; the normal law of the mean has median `2` and quartiles in `(1.966, 1.9665)` and
`(2.0335, 2.034)` (the book's `1.97` and `2.03`). -/
@[kb "openstaxintrostats2e" "Example 7.10, p. 390"]
theorem example_7_10_mean_quartiles [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal 2 ((0.5 ^ 2 / 100 : ℝ).toNNReal)) P) :
    0.5 / Real.sqrt 100 = 0.05 ∧ P.real {ω | X ω ≤ 2} = 1 / 2 ∧
      (∃ k, P.real {ω | X ω ≤ k} = 0.25 ∧ 1.966 < k ∧ k < 1.9665) ∧
      ∃ k, P.real {ω | X ω ≤ k} = 0.75 ∧ 2.0335 < k ∧ k < 2.034 := by
  have hX' := law_mean (s := 0.5) (n := 100) (by norm_num) hX
  rw [sqrt_100] at hX'
  have hσ : (0 : ℝ) < 0.5 / 10 := by norm_num
  refine ⟨by rw [sqrt_100]; norm_num, ?_, ?_, ?_⟩
  · rw [prob_le_normal hσ hX' 2, sub_self, zero_div, Phi_zero]
  · have h1 : Φ (-0.68) = 1 - Φ 0.68 := stdNormalCdf_neg 0.68
    have h2 : Φ (-0.67) = 1 - Φ 0.67 := stdNormalCdf_neg 0.67
    obtain ⟨k, hk, h3, h4⟩ := percentile_bd hσ hX' (p := 0.25) (lo := -0.68) (hi := -0.67)
      (by norm_num) (by norm_num) (by linarith [phi_0_68.1]) (by linarith [phi_0_67.2])
    exact ⟨k, hk, by linarith, by linarith⟩
  · obtain ⟨k, hk, h3, h4⟩ := percentile_bd hσ hX' (p := 0.75) (lo := 0.67) (hi := 0.68)
      (by norm_num) (by norm_num) (by linarith [phi_0_67.2]) (by linarith [phi_0_68.1])
    exact ⟨k, hk, by linarith, by linarith⟩

/-- OpenStax Introductory Statistics 2e Example 7.10 (percentiles of the sum). The sum of 100 times has
the normal law with mean `100 · 2 = 200` and variance `100 · 0.5²` (standard deviation `5`); its median
is `200`, its quartiles lie in `(196.6, 196.65)` and `(203.35, 203.4)` (the book's `196.63` and
`203.37`), and its interquartile range lies in `(6.7, 6.8)` (the book's `6.74`). -/
@[kb "openstaxintrostats2e" "Example 7.10, p. 390"]
theorem example_7_10_sum_quartiles [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal (100 * 2) ((100 * 0.5 ^ 2 : ℝ).toNNReal)) P) :
    P.real {ω | X ω ≤ 200} = 1 / 2 ∧
      ∃ k₁ k₃, P.real {ω | X ω ≤ k₁} = 0.25 ∧ 196.6 < k₁ ∧ k₁ < 196.65 ∧
        P.real {ω | X ω ≤ k₃} = 0.75 ∧ 203.35 < k₃ ∧ k₃ < 203.4 ∧ 6.7 < k₃ - k₁ ∧
        k₃ - k₁ < 6.8 := by
  have e : ((5 : ℝ)) ^ 2 = 100 * 0.5 ^ 2 := by norm_num
  rw [← e, show (100 * 2 : ℝ) = 200 by norm_num] at hX
  have hσ : (0 : ℝ) < 5 := by norm_num
  refine ⟨?_, ?_⟩
  · rw [prob_le_normal hσ hX 200, sub_self, zero_div, Phi_zero]
  · have h1 : Φ (-0.68) = 1 - Φ 0.68 := stdNormalCdf_neg 0.68
    have h2 : Φ (-0.67) = 1 - Φ 0.67 := stdNormalCdf_neg 0.67
    obtain ⟨k₁, hk₁, h3, h4⟩ := percentile_bd hσ hX (p := 0.25) (lo := -0.68) (hi := -0.67)
      (by norm_num) (by norm_num) (by linarith [phi_0_68.1]) (by linarith [phi_0_67.2])
    obtain ⟨k₃, hk₃, h5, h6⟩ := percentile_bd hσ hX (p := 0.75) (lo := 0.67) (hi := 0.68)
      (by norm_num) (by norm_num) (by linarith [phi_0_67.2]) (by linarith [phi_0_68.1])
    exact ⟨k₁, k₃, hk₁, by linarith, by linarith, hk₃, by linarith, by linarith, by linarith,
      by linarith⟩

/-- OpenStax Introductory Statistics 2e Example 7.10 (c). The mean time of 100 robberies has the
normal law with mean 2 and standard deviation `0.05`. The probability that it lies between 1.75 and
1.85 minutes lies in `(0.001, 0.0014)` (the book's `0.0013`; the true value is about `0.00135`). -/
@[kb "openstaxintrostats2e" "Example 7.10, p. 390"]
theorem example_7_10_probability [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal 2 ((0.5 ^ 2 / 100 : ℝ).toNNReal)) P) :
    0.001 < P.real {ω | 1.75 < X ω ∧ X ω < 1.85} ∧
      P.real {ω | 1.75 < X ω ∧ X ω < 1.85} < 0.0014 := by
  have hX' := law_mean (s := 0.5) (n := 100) (by norm_num) hX
  rw [sqrt_100] at hX'
  have hσ : (0 : ℝ) < 0.5 / 10 := by norm_num
  rw [prob_Ioo hσ hX' (a := 1.75) (b := 1.85) (by norm_num)]
  have e1 : ((1.85 : ℝ) - 2) / (0.5 / 10) = -3 := by norm_num
  have e2 : ((1.75 : ℝ) - 2) / (0.5 / 10) = -5 := by norm_num
  rw [e1, e2, stdNormalCdf_neg, stdNormalCdf_neg]
  have h1 : Φ 3.5 ≤ Φ 5 := Phi_mono (by norm_num)
  have h2 := Phi_lt_one 5
  constructor <;> linarith [phi_3.1, phi_3.2, phi_3_5.1]

/-- OpenStax Introductory Statistics 2e Example 7.10 (d). The value two standard deviations above the
mean of the sample mean is `2 · 0.05 + 2 = 2.1`; its `z`-score is `2`. -/
@[kb "openstaxintrostats2e" "Example 7.10, p. 390"]
theorem example_7_10_two_sd_above :
    2 + 2 * (0.5 / Real.sqrt 100) = 2.1 ∧ (2.1 - 2) / (0.5 / Real.sqrt 100) = 2 := by
  rw [sqrt_100]
  constructor <;> norm_num

/-- OpenStax Introductory Statistics 2e Example 7.11 (a). The mean age of 25 attendees (population
mean `30.9`, standard deviation 9) has the normal law with mean `30.9` and variance `9² / 25` (standard
deviation `1.8`). The probability that it is below 35 lies in `(0.9885, 0.9888)` (the book's
`0.9886`). -/
@[kb "openstaxintrostats2e" "Example 7.11, p. 391"]
theorem example_7_11_mean_below_35 [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal 30.9 ((9 ^ 2 / 25 : ℝ).toNNReal)) P) :
    0.9885 < P.real {ω | X ω < 35} ∧ P.real {ω | X ω < 35} < 0.9888 := by
  have hX' := law_mean (s := 9) (n := 25) (by norm_num) hX
  rw [sqrt_25] at hX'
  have hσ : (0 : ℝ) < 9 / 5 := by norm_num
  rw [prob_lt hσ hX' 35]
  have e : ((35 : ℝ) - 30.9) / (9 / 5) = 41 / 18 := by norm_num
  rw [e]
  constructor <;> linarith [phi_41_18.1, phi_41_18.2]

/-- OpenStax Introductory Statistics 2e Example 7.11 (b). For the same normal law of the mean age of
25 attendees, the probability that it exceeds 50 is under `0.001` (the book: about zero). -/
@[kb "openstaxintrostats2e" "Example 7.11, p. 391"]
theorem example_7_11_mean_above_50 [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal 30.9 ((9 ^ 2 / 25 : ℝ).toNNReal)) P) :
    P.real {ω | 50 < X ω} < 0.001 := by
  have hX' := law_mean (s := 9) (n := 25) (by norm_num) hX
  rw [sqrt_25] at hX'
  have hσ : (0 : ℝ) < 9 / 5 := by norm_num
  rw [prob_gt hσ hX' 50]
  have h1 : Φ 3.2 ≤ Φ (((50 : ℝ) - 30.9) / (9 / 5)) := Phi_mono (by norm_num)
  linarith [phi_3_2.1]

/-- OpenStax Introductory Statistics 2e Example 7.11 (c), (d). The sum of the ages of 49 attendees has
the normal law with mean `49 · 30.9 = 1514.1` and variance `49 · 9²` (standard deviation `63`). The
probability that the sum is at least 1600 lies in `(0.0863, 0.0865)` (the book's `0.0864`), and the
probability that it is at most 1595 lies in `(0.9003, 0.9006)` (the book's `0.9005`). -/
@[kb "openstaxintrostats2e" "Example 7.11, p. 391"]
theorem example_7_11_sum_49 [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal (49 * 30.9) ((49 * 9 ^ 2 : ℝ).toNNReal)) P) :
    (0.0863 < P.real {ω | 1600 ≤ X ω} ∧ P.real {ω | 1600 ≤ X ω} < 0.0865) ∧
      (0.9003 < P.real {ω | X ω ≤ 1595} ∧ P.real {ω | X ω ≤ 1595} < 0.9006) := by
  have e : ((63 : ℝ)) ^ 2 = 49 * 9 ^ 2 := by norm_num
  rw [← e, show (49 * 30.9 : ℝ) = 1514.1 by norm_num] at hX
  have hσ : (0 : ℝ) < 63 := by norm_num
  rw [prob_ge hσ hX 1600, prob_le_normal hσ hX 1595]
  have e1 : ((1600 : ℝ) - 1514.1) / 63 = 859 / 630 := by norm_num
  have e2 : ((1595 : ℝ) - 1514.1) / 63 = 809 / 630 := by norm_num
  rw [e1, e2]
  refine ⟨?_, ?_⟩ <;> constructor <;>
    linarith [phi_859_630.1, phi_859_630.2, phi_809_630.1, phi_809_630.2]

/-- OpenStax Introductory Statistics 2e Example 7.11 (e). The mean age of 65 attendees has the normal
law with mean `30.9` and variance `9² / 65`. Its 95th percentile `k` exists and lies in
`(32.7, 32.75)` (the book's `32.7`). -/
@[kb "openstaxintrostats2e" "Example 7.11, p. 391"]
theorem example_7_11_percentile_mean [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal 30.9 ((9 ^ 2 / 65 : ℝ).toNNReal)) P) :
    ∃ k, P.real {ω | X ω ≤ k} = 0.95 ∧ 32.7 < k ∧ k < 32.75 := by
  have hs := sqrt_bd (n := (65 : ℝ)) (a := 8.06) (b := 8.07) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hpos : 0 < Real.sqrt 65 := by positivity
  have hX' := law_mean (s := 9) (n := 65) (by norm_num) hX
  have hσ : 0 < 9 / Real.sqrt 65 := by positivity
  have hσ1 : 1.11 < 9 / Real.sqrt 65 := by rw [lt_div_iff₀ hpos]; linarith [hs.2]
  have hσ2 : 9 / Real.sqrt 65 < 1.12 := by rw [div_lt_iff₀ hpos]; linarith [hs.1]
  obtain ⟨k, hk, h1, h2⟩ := percentile_bd hσ hX' (p := 0.95) (lo := 1.64) (hi := 1.65)
    (by norm_num) (by norm_num) (by linarith [phi_1_64.2]) (by linarith [phi_1_65.1])
  exact ⟨k, hk, by linarith, by linarith⟩

/-- OpenStax Introductory Statistics 2e Example 7.11 (f). The sum of the ages of 65 attendees has the
normal law with mean `65 · 30.9 = 2008.5` and variance `65 · 9²`. Its 90th percentile `k` exists and
lies in `(2101, 2102)` (the book's `2,101.5`). -/
@[kb "openstaxintrostats2e" "Example 7.11, p. 391"]
theorem example_7_11_percentile_sum [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal (65 * 30.9) ((65 * 9 ^ 2 : ℝ).toNNReal)) P) :
    ∃ k, P.real {ω | X ω ≤ k} = 0.9 ∧ 2101 < k ∧ k < 2102 := by
  have hs := sqrt_bd (n := (65 : ℝ)) (a := 8.0622) (b := 8.0623) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hX' := law_sum (s := 9) (n := 65) (by norm_num) hX
  rw [show (65 * 30.9 : ℝ) = 2008.5 by norm_num] at hX'
  have hσ : 0 < Real.sqrt 65 * 9 := by have := hs.1; positivity
  obtain ⟨k, hk, h1, h2⟩ := percentile_bd hσ hX' (p := 0.9) (lo := 1.275) (hi := 1.285)
    (by norm_num) (by norm_num) (by linarith [phi_1_275.2]) (by linarith [phi_1_285.1])
  exact ⟨k, hk, by nlinarith [hs.1], by nlinarith [hs.2]⟩

/-! ### Section 7.4: normal approximation to the binomial -/

/-- OpenStax Introductory Statistics 2e Example 7.12 (parameters). For the binomial count with
`n = 300`, `p = 0.53` the mean is `np = 159` and the variance is `npq = 74.73`, whose square root
lies in `(8.6446, 8.6447)` (the book's `8.6447`). -/
@[kb "openstaxintrostats2e" "Example 7.12, p. 392"]
theorem example_7_12_mean_and_sd :
    (300 : ℝ) * 0.53 = 159 ∧ (300 : ℝ) * 0.53 * 0.47 = 74.73 ∧
      8.6446 < Real.sqrt 74.73 ∧ Real.sqrt 74.73 < 8.6447 := by
  have hs := sqrt_bd (n := (74.73 : ℝ)) (a := 8.6446) (b := 8.6447) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  exact ⟨by norm_num, by norm_num, hs.1, hs.2⟩

/-- OpenStax Introductory Statistics 2e Example 7.12 (a) and (b). The normal approximation `Y` of the
binomial count has the law with mean `159` and variance `300 · 0.53 · 0.47`. With the continuity
correction, `P(Y ≥ 149.5)` lies in `(0.8640, 0.8643)` (the book's `0.8641`) and `P(Y ≤ 160.5)` lies
in `(0.5688, 0.5690)` (the book's `0.5689`). -/
@[kb "openstaxintrostats2e" "Example 7.12, p. 392"]
theorem example_7_12_at_least_and_at_most [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal (300 * 0.53) ((300 * 0.53 * 0.47 : ℝ).toNNReal)) P) :
    (0.8640 < P.real {ω | 149.5 ≤ X ω} ∧ P.real {ω | 149.5 ≤ X ω} < 0.8643) ∧
      (0.5688 < P.real {ω | X ω ≤ 160.5} ∧ P.real {ω | X ω ≤ 160.5} < 0.5690) := by
  have hs := sqrt_bd (n := (74.73 : ℝ)) (a := 8.6446) (b := 8.6447) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have e : (300 * 0.53 * 0.47 : ℝ) = (Real.sqrt 74.73) ^ 2 := by
    rw [Real.sq_sqrt (by norm_num)]; norm_num
  rw [e, show (300 * 0.53 : ℝ) = 159 by norm_num] at hX
  have hσ : 0 < Real.sqrt 74.73 := by have := hs.1; positivity
  rw [prob_ge hσ hX 149.5, prob_le_normal hσ hX 160.5]
  have e1 : ((149.5 : ℝ) - 159) / Real.sqrt 74.73 = -(9.5 / Real.sqrt 74.73) := by
    rw [← neg_div]; norm_num
  have e2 : ((160.5 : ℝ) - 159) / Real.sqrt 74.73 = 1.5 / Real.sqrt 74.73 := by norm_num
  rw [e1, e2, stdNormalCdf_neg]
  have h1 := Phi_div (c := 9.5) (s := Real.sqrt 74.73) (s1 := 8.6446) (s2 := 8.6447)
    (lo := 1.0989) (hi := 1.099) (by norm_num) hs.1 hs.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) phi_1_0989.1 phi_1_099.2
  have h2 := Phi_div (c := 1.5) (s := Real.sqrt 74.73) (s1 := 8.6446) (s2 := 8.6447)
    (lo := 0.1735) (hi := 0.1736) (by norm_num) hs.1 hs.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) phi_0_1735.1 phi_0_1736.2
  refine ⟨?_, ?_⟩ <;> constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- OpenStax Introductory Statistics 2e Example 7.12 (c) and (d). For the same normal approximation
`Y`, `P(Y > 155.5)` lies in `(0.6571, 0.6573)` (the book's `0.6572`) and `P(Y < 146.5)` lies in
`(0.0740, 0.0742)` (the book's `0.0741`). -/
@[kb "openstaxintrostats2e" "Example 7.12, p. 392"]
theorem example_7_12_more_than_and_fewer_than [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal (300 * 0.53) ((300 * 0.53 * 0.47 : ℝ).toNNReal)) P) :
    (0.6571 < P.real {ω | 155.5 < X ω} ∧ P.real {ω | 155.5 < X ω} < 0.6573) ∧
      (0.0740 < P.real {ω | X ω < 146.5} ∧ P.real {ω | X ω < 146.5} < 0.0742) := by
  have hs := sqrt_bd (n := (74.73 : ℝ)) (a := 8.6446) (b := 8.6447) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have e : (300 * 0.53 * 0.47 : ℝ) = (Real.sqrt 74.73) ^ 2 := by
    rw [Real.sq_sqrt (by norm_num)]; norm_num
  rw [e, show (300 * 0.53 : ℝ) = 159 by norm_num] at hX
  have hσ : 0 < Real.sqrt 74.73 := by have := hs.1; positivity
  rw [prob_gt hσ hX 155.5, prob_lt hσ hX 146.5]
  have e1 : ((155.5 : ℝ) - 159) / Real.sqrt 74.73 = -(3.5 / Real.sqrt 74.73) := by
    rw [← neg_div]; norm_num
  have e2 : ((146.5 : ℝ) - 159) / Real.sqrt 74.73 = -(12.5 / Real.sqrt 74.73) := by
    rw [← neg_div]; norm_num
  rw [e1, e2, stdNormalCdf_neg, stdNormalCdf_neg]
  have h1 := Phi_div (c := 3.5) (s := Real.sqrt 74.73) (s1 := 8.6446) (s2 := 8.6447)
    (lo := 0.4048) (hi := 0.4049) (by norm_num) hs.1 hs.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) phi_0_4048.1 phi_0_4049.2
  have h2 := Phi_div (c := 12.5) (s := Real.sqrt 74.73) (s1 := 8.6446) (s2 := 8.6447)
    (lo := 1.4459) (hi := 1.446) (by norm_num) hs.1 hs.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) phi_1_4459.1 phi_1_446.2
  refine ⟨?_, ?_⟩ <;> constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- OpenStax Introductory Statistics 2e Example 7.12 (e). For the same normal approximation `Y`, the
approximation `P(174.5 < Y < 175.5)` of the chance of exactly 175 successes lies in
`(0.0082, 0.0085)` (the book's `0.0083`). -/
@[kb "openstaxintrostats2e" "Example 7.12, p. 392"]
theorem example_7_12_exactly [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal (300 * 0.53) ((300 * 0.53 * 0.47 : ℝ).toNNReal)) P) :
    0.0082 < P.real {ω | 174.5 < X ω ∧ X ω < 175.5} ∧
      P.real {ω | 174.5 < X ω ∧ X ω < 175.5} < 0.0085 := by
  have hs := sqrt_bd (n := (74.73 : ℝ)) (a := 8.6446) (b := 8.6447) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have e : (300 * 0.53 * 0.47 : ℝ) = (Real.sqrt 74.73) ^ 2 := by
    rw [Real.sq_sqrt (by norm_num)]; norm_num
  rw [e, show (300 * 0.53 : ℝ) = 159 by norm_num] at hX
  have hσ : 0 < Real.sqrt 74.73 := by have := hs.1; positivity
  rw [prob_Ioo hσ hX (a := 174.5) (b := 175.5) (by norm_num)]
  have e1 : ((175.5 : ℝ) - 159) / Real.sqrt 74.73 = 16.5 / Real.sqrt 74.73 := by norm_num
  have e2 : ((174.5 : ℝ) - 159) / Real.sqrt 74.73 = 15.5 / Real.sqrt 74.73 := by norm_num
  rw [e1, e2]
  have h1 := Phi_div (c := 16.5) (s := Real.sqrt 74.73) (s1 := 8.6446) (s2 := 8.6447)
    (lo := 1.9086) (hi := 1.9088) (by norm_num) hs.1 hs.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) phi_1_9086.1 phi_1_9088.2
  have h2 := Phi_div (c := 15.5) (s := Real.sqrt 74.73) (s1 := 8.6446) (s2 := 8.6447)
    (lo := 1.793) (hi := 1.7931) (by norm_num) hs.1 hs.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) phi_1_793.1 phi_1_7931.2
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

end UndergradKB.Statistics.Course.ExamplesC7
