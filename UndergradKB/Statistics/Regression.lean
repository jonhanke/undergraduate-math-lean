import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Chebyshev
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Data

/-!
# Linear regression and correlation (OpenStax *Introductory Statistics 2e*, chapter 12)

The least-squares line, its properties, and the correlation coefficient.
-/

namespace UndergradKB.Statistics

open Finset

variable {n : ℕ}

/-- Slope `b = Sxy / Sxx` of the least-squares line. -/
noncomputable def slope (x y : Fin n → ℝ) : ℝ := sumProdDev x y / sumSqDev x

/-- Intercept `a = ȳ - b x̄` of the least-squares line. -/
noncomputable def intercept (x y : Fin n → ℝ) : ℝ := mean y - slope x y * mean x

/-- Sum of squared errors `∑ (yᵢ - (a + b xᵢ))²` of the line `a + b x`. -/
noncomputable def sse (x y : Fin n → ℝ) (a b : ℝ) : ℝ := ∑ i, (y i - (a + b * x i)) ^ 2

/-- Standard error of the estimate `√(SSE / (n - 2))`. -/
noncomputable def stdErrorEstimate (x y : Fin n → ℝ) : ℝ :=
  Real.sqrt (sse x y (intercept x y) (slope x y) / ((n : ℝ) - 2))

lemma sumSqDev_nonneg (x : Fin n → ℝ) : 0 ≤ sumSqDev x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma pos_of_sumSqDev_pos {x : Fin n → ℝ} (h : 0 < sumSqDev x) : 0 < n := by
  apply Nat.pos_of_ne_zero
  rintro rfl
  simp [sumSqDev] at h

lemma sse_eq (x y : Fin n → ℝ) (a b : ℝ) :
    sse x y a b = sumSqDev y - 2 * b * sumProdDev x y + b ^ 2 * sumSqDev x
      + n * (mean y - a - b * mean x) ^ 2 := by
  unfold sse
  obtain ⟨U, hU⟩ : ∃ U : Fin n → ℝ, ∀ i, U i = (y i - mean y) - b * (x i - mean x) :=
    ⟨_, fun _ => rfl⟩
  have hs : ∑ i, U i = 0 := by
    rw [show ∑ i, U i = ∑ i, (y i - mean y) - b * ∑ i, (x i - mean x) by
      simp only [hU]; rw [sum_sub_distrib, mul_sum]]
    rw [sum_sub_mean, sum_sub_mean]; ring
  have h : ∀ i, (y i - (a + b * x i)) ^ 2 = (y i - mean y) ^ 2
      - 2 * b * ((x i - mean x) * (y i - mean y)) + b ^ 2 * (x i - mean x) ^ 2
      + 2 * (mean y - a - b * mean x) * U i
      + (mean y - a - b * mean x) ^ 2 := by intro i; rw [hU]; ring
  simp only [h, sum_add_distrib, sum_sub_distrib, ← mul_sum, hs, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  unfold sumSqDev sumProdDev
  ring

lemma sse_opt {x : Fin n → ℝ} (y : Fin n → ℝ) (hx : sumSqDev x ≠ 0) :
    sse x y (intercept x y) (slope x y) = sumSqDev y - sumProdDev x y ^ 2 / sumSqDev x := by
  rw [sse_eq]
  unfold intercept slope
  field_simp
  ring

lemma sse_sub_opt {x : Fin n → ℝ} (y : Fin n → ℝ) (hx : sumSqDev x ≠ 0) (a b : ℝ) :
    sse x y a b = sse x y (intercept x y) (slope x y)
      + sumSqDev x * (b - slope x y) ^ 2 + n * (mean y - a - b * mean x) ^ 2 := by
  rw [sse_opt y hx, sse_eq]
  unfold slope
  field_simp
  ring

/-- (ST-103) The least-squares line `ŷ = a + b x` has the smallest sum of squared errors among
all lines, and it is the only one. -/
@[kb "openstaxintrostats2e" "§12.3, p. 634"]
theorem sse_intercept_slope_le (x y : Fin n → ℝ) (hx : sumSqDev x ≠ 0) (a b : ℝ) :
    sse x y (intercept x y) (slope x y) ≤ sse x y a b := by
  rw [sse_sub_opt y hx a b]
  have := sumSqDev_nonneg x
  have h2 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [mul_nonneg this (sq_nonneg (b - slope x y)), mul_nonneg h2 (sq_nonneg (mean y - a - b * mean x))]

/-- (ST-103, uniqueness) A line attaining the minimal sum of squared errors is the least-squares
line. -/
@[kb "openstaxintrostats2e" "§12.3, p. 634"]
theorem eq_intercept_slope_of_sse_eq (x y : Fin n → ℝ) (hx : sumSqDev x ≠ 0) (a b : ℝ)
    (h : sse x y a b = sse x y (intercept x y) (slope x y)) :
    a = intercept x y ∧ b = slope x y := by
  have hpos : 0 < sumSqDev x := lt_of_le_of_ne (sumSqDev_nonneg x) (Ne.symm hx)
  have hn : (0 : ℝ) < n := by exact_mod_cast pos_of_sumSqDev_pos hpos
  have h1 := sse_sub_opt y hx a b
  rw [h] at h1
  have e : sumSqDev x * (b - slope x y) ^ 2 + n * (mean y - a - b * mean x) ^ 2 = 0 := by linarith
  have t1 := mul_nonneg hpos.le (sq_nonneg (b - slope x y))
  have t2 := mul_nonneg hn.le (sq_nonneg (mean y - a - b * mean x))
  have e1 : sumSqDev x * (b - slope x y) ^ 2 = 0 := by linarith
  have e2 : (n : ℝ) * (mean y - a - b * mean x) ^ 2 = 0 := by linarith
  have hb : b = slope x y := by
    rcases mul_eq_zero.1 e1 with h | h
    · exact absurd h hx
    · have := pow_eq_zero_iff (two_ne_zero) |>.1 h
      linarith
  refine ⟨?_, hb⟩
  rcases mul_eq_zero.1 e2 with h | h
  · exact absurd h hn.ne'
  · have := pow_eq_zero_iff (two_ne_zero) |>.1 h
    unfold intercept
    rw [← hb]
    linarith

/-- (ST-104) The least-squares line passes through the point of means `(x̄, ȳ)`. -/
@[kb "openstaxintrostats2e" "§12.3, p. 634"]
theorem intercept_add_slope_mul_mean (x y : Fin n → ℝ) :
    intercept x y + slope x y * mean x = mean y := by
  unfold intercept; ring

lemma residual_eq (x y : Fin n → ℝ) (i : Fin n) :
    y i - (intercept x y + slope x y * x i)
      = (y i - mean y) - slope x y * (x i - mean x) := by
  unfold intercept; ring

/-- (ST-104) The residuals of the least-squares line sum to zero. -/
@[kb "openstaxintrostats2e" "§12.3, p. 634"]
theorem sum_residual_eq_zero (x y : Fin n → ℝ) :
    ∑ i, (y i - (intercept x y + slope x y * x i)) = 0 := by
  simp only [residual_eq]
  rw [sum_sub_distrib, ← mul_sum, sum_sub_mean, sum_sub_mean]
  ring

/-- (ST-104) The residuals of the least-squares line are orthogonal to the `xᵢ`. -/
@[kb "openstaxintrostats2e" "§12.3, p. 634"]
theorem sum_residual_mul_eq_zero (x y : Fin n → ℝ) (hx : sumSqDev x ≠ 0) :
    ∑ i, (y i - (intercept x y + slope x y * x i)) * x i = 0 := by
  have h : ∀ i, (y i - (intercept x y + slope x y * x i)) * x i
      = (y i - (intercept x y + slope x y * x i)) * (x i - mean x)
        + mean x * (y i - (intercept x y + slope x y * x i)) := by intro i; ring
  simp only [h, sum_add_distrib, ← mul_sum, sum_residual_eq_zero]
  have : ∑ i, (y i - (intercept x y + slope x y * x i)) * (x i - mean x)
      = sumProdDev x y - slope x y * sumSqDev x := by
    simp only [residual_eq]
    unfold sumProdDev sumSqDev
    rw [Finset.mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => by ring
  rw [this]
  unfold slope
  field_simp
  ring

/-! ### Correlation -/

lemma sumProdDev_sq_le (x y : Fin n → ℝ) :
    sumProdDev x y ^ 2 ≤ sumSqDev x * sumSqDev y := by
  unfold sumProdDev sumSqDev
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- (ST-106) The correlation coefficient lies between `-1` and `1`. -/
@[kb "openstaxintrostats2e" "§12.3, p. 634"]
theorem correlation_mem_Icc (x y : Fin n → ℝ) :
    -1 ≤ correlation x y ∧ correlation x y ≤ 1 := by
  unfold correlation
  by_cases h : sumSqDev x * sumSqDev y = 0
  · simp [h]
  have hp : 0 < sumSqDev x * sumSqDev y :=
    lt_of_le_of_ne (mul_nonneg (sumSqDev_nonneg x) (sumSqDev_nonneg y)) (Ne.symm h)
  have hs := Real.sqrt_pos.2 hp
  have := Real.abs_le_sqrt (sumProdDev_sq_le x y)
  rw [← abs_le, abs_div, abs_of_pos hs, div_le_one hs]
  exact this

lemma correlation_sq {x y : Fin n → ℝ} (hx : 0 < sumSqDev x) (hy : 0 < sumSqDev y) :
    correlation x y ^ 2 = sumProdDev x y ^ 2 / (sumSqDev x * sumSqDev y) := by
  unfold correlation
  rw [div_pow, Real.sq_sqrt (mul_pos hx hy).le]

lemma sse_opt_eq {x y : Fin n → ℝ} (hx : 0 < sumSqDev x) (hy : 0 < sumSqDev y) :
    sse x y (intercept x y) (slope x y) = (1 - correlation x y ^ 2) * sumSqDev y := by
  rw [sse_opt y hx.ne', correlation_sq hx hy]
  field_simp

/-- (ST-105) The slope equals `r · s_y / s_x`. -/
@[kb "openstaxintrostats2e" "§12.3, p. 634"]
theorem slope_eq_correlation_mul (x y : Fin n → ℝ) (hn : 2 ≤ n)
    (hx : 0 < sumSqDev x) (hy : 0 < sumSqDev y) :
    slope x y = correlation x y * sampleStdDev y / sampleStdDev x := by
  have hn' : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have e : ∀ z : Fin n → ℝ, sampleStdDev z = Real.sqrt (sumSqDev z) / Real.sqrt ((n : ℝ) - 1) := by
    intro z
    unfold sampleStdDev sampleVariance
    exact Real.sqrt_div (sumSqDev_nonneg z) _
  have hsx := Real.sqrt_pos.2 hx
  have hsy := Real.sqrt_pos.2 hy
  have hsn := Real.sqrt_pos.2 hn'
  have hxy : Real.sqrt (sumSqDev x * sumSqDev y) = Real.sqrt (sumSqDev x) * Real.sqrt (sumSqDev y) :=
    Real.sqrt_mul hx.le _
  unfold slope correlation
  rw [e x, e y, hxy]
  have h1 : Real.sqrt (sumSqDev x) ^ 2 = sumSqDev x := Real.sq_sqrt hx.le
  field_simp
  try rw [h1]
  try ring

/-- Points on a line `y = a + b x` with `b ≠ 0` have correlation `b / |b|`. -/
lemma correlation_of_linear {x y : Fin n → ℝ} (hx : 0 < sumSqDev x) (a b : ℝ) (hb : b ≠ 0)
    (h : ∀ i, y i = a + b * x i) : correlation x y = b / |b| := by
  have hn := pos_of_sumSqDev_pos hx
  have hm : mean y = a + b * mean x := by
    have hn' : (n : ℝ) ≠ 0 := by positivity
    unfold mean
    simp only [h, sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  have hd : ∀ i, y i - mean y = b * (x i - mean x) := by intro i; rw [h, hm]; ring
  have hxy : sumProdDev x y = b * sumSqDev x := by
    unfold sumProdDev sumSqDev
    rw [mul_sum]
    exact sum_congr rfl fun i _ => by rw [hd]; ring
  have hyy : sumSqDev y = b ^ 2 * sumSqDev x := by
    unfold sumSqDev
    rw [mul_sum]
    exact sum_congr rfl fun i _ => by rw [hd]; ring
  have hab : 0 < |b| := abs_pos.2 hb
  have hsq : sumSqDev x * sumSqDev y = (|b| * sumSqDev x) ^ 2 := by
    rw [hyy, mul_pow, sq_abs]; ring
  unfold correlation
  rw [hsq, Real.sqrt_sq (mul_pos hab hx).le, hxy]
  field_simp

/-- (ST-107) `r = 1` exactly when the points lie on a line of positive slope. -/
@[kb "openstaxintrostats2e" "§12.3, p. 634"]
theorem correlation_eq_one_iff (x y : Fin n → ℝ) (hx : 0 < sumSqDev x) (hy : 0 < sumSqDev y) :
    correlation x y = 1 ↔ ∃ a b : ℝ, 0 < b ∧ ∀ i, y i = a + b * x i := by
  constructor
  · intro hr
    have hr2 : correlation x y ^ 2 = 1 := by rw [hr]; norm_num
    have h0 : sse x y (intercept x y) (slope x y) = 0 := by
      rw [sse_opt_eq hx hy, hr2]; ring
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).1 h0
    have hxy : 0 < sumProdDev x y := by
      have hs := Real.sqrt_pos.2 (mul_pos hx hy)
      unfold correlation at hr
      rw [div_eq_one_iff_eq hs.ne'] at hr
      rw [hr]; exact hs
    refine ⟨intercept x y, slope x y, div_pos hxy hx, fun i => ?_⟩
    have := hz i (mem_univ i)
    have := pow_eq_zero_iff (two_ne_zero) |>.1 this
    linarith
  · rintro ⟨a, b, hb, h⟩
    rw [correlation_of_linear hx a b hb.ne' h, abs_of_pos hb, div_self hb.ne']

/-- (ST-107) `r = -1` exactly when the points lie on a line of negative slope. -/
@[kb "openstaxintrostats2e" "§12.3, p. 634"]
theorem correlation_eq_neg_one_iff (x y : Fin n → ℝ) (hx : 0 < sumSqDev x)
    (hy : 0 < sumSqDev y) :
    correlation x y = -1 ↔ ∃ a b : ℝ, b < 0 ∧ ∀ i, y i = a + b * x i := by
  constructor
  · intro hr
    have hr2 : correlation x y ^ 2 = 1 := by rw [hr]; norm_num
    have h0 : sse x y (intercept x y) (slope x y) = 0 := by
      rw [sse_opt_eq hx hy, hr2]; ring
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).1 h0
    have hxy : sumProdDev x y < 0 := by
      have hs := Real.sqrt_pos.2 (mul_pos hx hy)
      unfold correlation at hr
      rw [div_eq_iff hs.ne'] at hr
      rw [hr]; linarith
    refine ⟨intercept x y, slope x y, div_neg_of_neg_of_pos hxy hx, fun i => ?_⟩
    have := hz i (mem_univ i)
    have := pow_eq_zero_iff (two_ne_zero) |>.1 this
    linarith
  · rintro ⟨a, b, hb, h⟩
    rw [correlation_of_linear hx a b hb.ne h, abs_of_neg hb, div_neg, div_self hb.ne]

/-- (ST-107) `|r| = 1` exactly when all points lie on a line with nonzero slope. -/
@[kb "openstaxintrostats2e" "§12.3, p. 634"]
theorem abs_correlation_eq_one_iff (x y : Fin n → ℝ) (hx : 0 < sumSqDev x)
    (hy : 0 < sumSqDev y) :
    |correlation x y| = 1 ↔ ∃ a b : ℝ, b ≠ 0 ∧ ∀ i, y i = a + b * x i := by
  rw [abs_eq (by norm_num), correlation_eq_one_iff x y hx hy, correlation_eq_neg_one_iff x y hx hy]
  constructor
  · rintro (⟨a, b, hb, h⟩ | ⟨a, b, hb, h⟩)
    · exact ⟨a, b, hb.ne', h⟩
    · exact ⟨a, b, hb.ne, h⟩
  · rintro ⟨a, b, hb, h⟩
    rcases lt_or_gt_of_ne hb with hb | hb
    · exact Or.inr ⟨a, b, hb, h⟩
    · exact Or.inl ⟨a, b, hb, h⟩

/-! ### Variance decomposition -/

/-- (ST-108) Total variation splits as explained plus unexplained:
`SST = SSR + SSE`. -/
@[kb "openstaxintrostats2e" "§12.3, p. 634"]
theorem sumSqDev_eq_ssr_add_sse (x y : Fin n → ℝ) (hx : sumSqDev x ≠ 0) :
    sumSqDev y = ∑ i, (intercept x y + slope x y * x i - mean y) ^ 2
      + sse x y (intercept x y) (slope x y) := by
  have h : ∀ i, (intercept x y + slope x y * x i - mean y) ^ 2
      = slope x y ^ 2 * (x i - mean x) ^ 2 := by
    intro i; unfold intercept; ring
  simp only [h, ← mul_sum]
  rw [sse_opt y hx]
  have : slope x y ^ 2 * ∑ i, (x i - mean x) ^ 2 = sumProdDev x y ^ 2 / sumSqDev x := by
    change slope x y ^ 2 * sumSqDev x = _
    unfold slope
    field_simp
  rw [this]; ring

/-- (ST-108) The coefficient of determination: `r² = SSR / SST`. -/
@[kb "openstaxintrostats2e" "§12.3, p. 634"]
theorem correlation_sq_eq_ssr_div (x y : Fin n → ℝ) (hx : 0 < sumSqDev x)
    (hy : 0 < sumSqDev y) :
    correlation x y ^ 2
      = (∑ i, (intercept x y + slope x y * x i - mean y) ^ 2) / sumSqDev y := by
  have h := sumSqDev_eq_ssr_add_sse x y hx.ne'
  rw [sse_opt_eq hx hy] at h
  rw [eq_div_iff hy.ne']
  linarith

/-- (ST-108) `r² = 1 - SSE / SST`. -/
@[kb "openstaxintrostats2e" "§12.3, p. 634"]
theorem correlation_sq_eq_one_sub (x y : Fin n → ℝ) (hx : 0 < sumSqDev x)
    (hy : 0 < sumSqDev y) :
    correlation x y ^ 2 = 1 - sse x y (intercept x y) (slope x y) / sumSqDev y := by
  rw [sse_opt_eq hx hy]
  field_simp
  ring

/-- (ST-110) The standard error of the estimate is `√((1 - r²) Syy / (n - 2))`. -/
@[kb "openstaxintrostats2e" "§12.5, p. 646"]
theorem stdErrorEstimate_eq (x y : Fin n → ℝ) (hx : 0 < sumSqDev x) (hy : 0 < sumSqDev y) :
    stdErrorEstimate x y
      = Real.sqrt ((1 - correlation x y ^ 2) * sumSqDev y / ((n : ℝ) - 2)) := by
  unfold stdErrorEstimate
  rw [sse_opt_eq hx hy]

end UndergradKB.Statistics
