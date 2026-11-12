import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.Field
import UndergradKB.Common

/-!
# Foundations: limits that fail to exist, and series via partial sums

Gap rows from Hammack's chapter 13: three classical limit computations, the limit of
`sin x / x` at infinity, and the book's notion of a convergent series (convergence of the
partial sums `s n = a 1 + ... + a n`), which differs from Mathlib's unconditional `HasSum`.
-/

open Filter Topology

namespace UndergradKB.Foundations

/-- FO-264. The function `x/2 + |x-2|/(x-2) + 2` has no limit at `2`: the one-sided values differ. -/
@[kb "hammack2018" "Example 13.3, p. 261"]
theorem hammack_ex_13_3_no_limit :
    ¬ ∃ L : ℝ, Tendsto (fun x : ℝ => x / 2 + |x - 2| / (x - 2) + 2) (𝓝[≠] 2) (𝓝 L) := by
  rintro ⟨L, h⟩
  rw [Metric.tendsto_nhdsWithin_nhds] at h
  obtain ⟨δ, hδ, hd⟩ := h 1 one_pos
  have ha := @hd (2 - δ / 2) (by simp; linarith) (by
    rw [Real.dist_eq]; rw [abs_lt]; constructor <;> linarith)
  have hb := @hd (2 + δ / 2) (by simp; linarith) (by
    rw [Real.dist_eq]; rw [abs_lt]; constructor <;> linarith)
  have e1 : |(2 - δ / 2) - 2| / ((2 - δ / 2) - 2) = -1 := by
    have : (2 - δ / 2) - 2 = -(δ / 2) := by ring
    rw [this, abs_neg, abs_of_pos (by linarith)]
    field_simp
  have e2 : |(2 + δ / 2) - 2| / ((2 + δ / 2) - 2) = 1 := by
    have : (2 + δ / 2) - 2 = δ / 2 := by ring
    rw [this, abs_of_pos (by linarith)]
    field_simp
  rw [e1, Real.dist_eq, abs_lt] at ha
  rw [e2, Real.dist_eq, abs_lt] at hb
  linarith [ha.1, ha.2, hb.1, hb.2]

/-- FO-265. `sin (1/x)` has no limit as `x → 0`. -/
@[kb "hammack2018" "Example 13.4, p. 262"]
theorem hammack_ex_13_4_sin_inv_no_limit :
    ¬ ∃ L : ℝ, Tendsto (fun x : ℝ => Real.sin (1 / x)) (𝓝[≠] 0) (𝓝 L) := by
  rintro ⟨L, h⟩
  have key : ∀ u : ℕ → ℝ, (∀ n, 0 < u n) → Tendsto u atTop (𝓝 0) →
      Tendsto (fun n => Real.sin (1 / u n)) atTop (𝓝 L) := by
    intro u hpos hu
    refine h.comp (tendsto_nhdsWithin_iff.mpr ⟨hu, Eventually.of_forall fun n => ?_⟩)
    exact (hpos n).ne'
  have hu : Tendsto (fun n : ℕ => 1 / (((n : ℝ) + 1) * Real.pi)) atTop (𝓝 0) := by
    simp only [one_div]
    refine tendsto_inv_atTop_zero.comp ?_
    exact (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_mul_const
      Real.pi_pos
  have hv : Tendsto (fun n : ℕ => 1 / (2 * Real.pi * n + Real.pi / 2)) atTop (𝓝 0) := by
    simp only [one_div]
    refine tendsto_inv_atTop_zero.comp ?_
    exact (tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)).atTop_add
      tendsto_const_nhds
  have h1 := key _ (fun n => by positivity) hu
  have h2 := key _ (fun n => by positivity) hv
  have e1 : (fun n : ℕ => Real.sin (1 / (1 / (((n : ℝ) + 1) * Real.pi)))) = fun _ => 0 := by
    funext n
    rw [one_div_one_div]
    have := Real.sin_nat_mul_pi (n + 1)
    simpa using this
  have e2 : (fun n : ℕ => Real.sin (1 / (1 / (2 * Real.pi * n + Real.pi / 2)))) = fun _ => 1 := by
    funext n
    rw [one_div_one_div]
    have : 2 * Real.pi * n + Real.pi / 2 = Real.pi / 2 + n * (2 * Real.pi) := by ring
    rw [this, Real.sin_add_nat_mul_two_pi, Real.sin_pi_div_two]
  rw [e1] at h1
  rw [e2] at h2
  have := tendsto_nhds_unique h1 tendsto_const_nhds
  have := tendsto_nhds_unique h2 tendsto_const_nhds
  linarith

/-- FO-266. `x sin (1/x) → 0` as `x → 0`. -/
@[kb "hammack2018" "Example 13.5, p. 262"]
theorem hammack_ex_13_5_x_sin_inv :
    Tendsto (fun x : ℝ => x * Real.sin (1 / x)) (𝓝[≠] 0) (𝓝 0) := by
  refine squeeze_zero_norm (a := fun x : ℝ => |x|) (fun x => ?_) ?_
  · rw [Real.norm_eq_abs, abs_mul]
    calc |x| * |Real.sin (1 / x)| ≤ |x| * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
      _ = |x| := mul_one _
  · have : Tendsto (fun x : ℝ => |x|) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_abs.tendsto (0 : ℝ))
    exact this.mono_left nhdsWithin_le_nhds

/-- FO-281. `sin x / x → 0` as `x → ∞`. -/
@[kb "hammack2018" "Example 13.7, p. 271"]
theorem hammack_ex_13_7_sin_div_x :
    Tendsto (fun x : ℝ => Real.sin x / x) atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun x : ℝ => x⁻¹) ?_ tendsto_inv_atTop_zero
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hx, div_eq_mul_inv]
  calc |Real.sin x| * x⁻¹ ≤ 1 * x⁻¹ :=
        mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (inv_nonneg.mpr hx.le)
    _ = x⁻¹ := one_mul _

/-- The `n`-th partial sum `a 1 + ... + a n` of a series, as in the book. -/
def partialSum (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 n, a k

/-- FO-285. The series `∑_{k ≥ 1} a k` converges to `S` when its partial sums converge to `S`. -/
@[kb "hammack2018" "Definition 13.7, p. 278"]
def SeriesConvergesTo (a : ℕ → ℝ) (S : ℝ) : Prop :=
  Tendsto (partialSum a) atTop (𝓝 S)

/-- The book's partial sums are the usual `range` sums of the shifted sequence. -/
theorem partialSum_eq_sum_range (a : ℕ → ℝ) (n : ℕ) :
    partialSum a n = ∑ k ∈ Finset.range n, a (k + 1) := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih =>
    unfold partialSum at *
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- FO-285. An unconditionally summable series converges in the book's sense, to the same sum. -/
@[kb "hammack2018" "Definition 13.7, p. 278"]
theorem seriesConvergesTo_of_hasSum {a : ℕ → ℝ} {S : ℝ} (h : HasSum (fun k => a (k + 1)) S) :
    SeriesConvergesTo a S := by
  unfold SeriesConvergesTo
  have := h.tendsto_sum_nat
  simpa [funext (partialSum_eq_sum_range a)] using this

/-- FO-286. The series `∑_{k ≥ 1} 1 / 2^k` converges to `1`. -/
@[kb "hammack2018" "Example 13.10, p. 278"]
theorem hammack_ex_13_10_geometric_half :
    SeriesConvergesTo (fun k => 1 / 2 ^ k) 1 := by
  have hs : ∀ n, partialSum (fun k => 1 / 2 ^ k : ℕ → ℝ) n = 1 - 1 / 2 ^ n := by
    intro n
    induction n with
    | zero => simp [partialSum]
    | succ n ih =>
      unfold partialSum at *
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      field_simp
      ring
  unfold SeriesConvergesTo
  rw [funext hs]
  have : Tendsto (fun n : ℕ => 1 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this

/-- FO-288 (support). If a series converges then its terms tend to `0`. -/
@[kb "hammack2018" "Theorem 13.11, p. 279"]
theorem hammack_thm_13_11_terms_tendsto_zero {a : ℕ → ℝ} {S : ℝ}
    (h : SeriesConvergesTo a S) : Tendsto a atTop (𝓝 0) := by
  have h1 : Tendsto (fun n => partialSum a (n + 1)) atTop (𝓝 S) :=
    h.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n => partialSum a n) atTop (𝓝 S) := h
  have h3 : Tendsto (fun n => partialSum a (n + 1) - partialSum a n) atTop (𝓝 (S - S)) :=
    h1.sub h2
  rw [sub_self] at h3
  have e : ∀ n, partialSum a (n + 1) - partialSum a n = a (n + 1) := by
    intro n
    unfold partialSum
    rw [Finset.sum_Icc_succ_top (by omega)]
    ring
  simp only [e] at h3
  exact (tendsto_add_atTop_iff_nat 1).mp h3

/-- FO-288. Divergence test: if the terms do not tend to `0` (they diverge, or tend to a nonzero
limit), the series does not converge to any real number. -/
@[kb "hammack2018" "Corollary 13.1, p. 279"]
theorem hammack_cor_13_1_divergence_test {a : ℕ → ℝ} (h : ¬ Tendsto a atTop (𝓝 0)) :
    ¬ ∃ S : ℝ, SeriesConvergesTo a S :=
  fun ⟨_, hS⟩ => h (hammack_thm_13_11_terms_tendsto_zero hS)

end UndergradKB.Foundations
