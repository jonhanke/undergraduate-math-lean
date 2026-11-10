import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import UndergradKB.Common.Attr

namespace UndergradKB.Calculus

open Set Filter Topology
open scoped ContDiff

/-- OpenStax Calculus 1:§4.9 Newton's method (CA-172). One step of the iteration
`x ↦ x - f(x)/f'(x)`, with `f'` the derivative given as an argument. -/
@[kb "openstaxcalculus2016" "1:§4.9 Newton's method iteration formula (Equation 4.8), p. 418"]
noncomputable def newtonStep (f f' : ℝ → ℝ) (x : ℝ) : ℝ := x - f x / f' x

/-- OpenStax Calculus 1:§4.9 (CA-172). The Newton iterates `x_0, x_1 = step x_0, ...`: the same function
applied repeatedly. -/
@[kb "openstaxcalculus2016" "1:§4.9 Iterative processes, p. 420"]
noncomputable def newtonSeq (f f' : ℝ → ℝ) (x₀ : ℝ) (n : ℕ) : ℝ := (newtonStep f f')^[n] x₀

/-- OpenStax Calculus 1:§4.9 (CA-172). The Newton step is the `x`-intercept of the tangent line at `x`:
the line `y = f x + f'(x) (t - x)` vanishes at `t = newtonStep f f' x` when `f'(x) ≠ 0`. -/
@[kb "openstaxcalculus2016" "1:§4.9 Newton's method iteration formula (Equation 4.8), p. 418"]
theorem tangent_vanishes_at_newtonStep {f : ℝ → ℝ} {x : ℝ} (h : deriv f x ≠ 0) :
    f x + deriv f x * (newtonStep f (deriv f) x - x) = 0 := by
  unfold newtonStep
  field_simp
  ring

theorem newtonSeq_succ (f f' : ℝ → ℝ) (x₀ : ℝ) (n : ℕ) :
    newtonSeq f f' x₀ (n + 1) = newtonStep f f' (newtonSeq f f' x₀ n) := by
  unfold newtonSeq
  rw [Function.iterate_succ_apply']

/-- One Newton step is quadratically close to the root: if `f r = 0`, `f` is differentiable on
`[r-ρ, r+ρ]` with `|f'(x) - f'(y)| ≤ K |x - y|` and `|f'| ≥ m > 0` there, then
`|newtonStep x - r| ≤ (K/m) |x - r|²` for `x` in that interval. -/
theorem newtonStep_sub_le {f : ℝ → ℝ} {r ρ K m : ℝ} (hr : f r = 0) (hK : 0 ≤ K) (hm : 0 < m)
    (hd : ∀ x ∈ Icc (r - ρ) (r + ρ), DifferentiableAt ℝ f x)
    (hlip : ∀ x ∈ Icc (r - ρ) (r + ρ), ∀ y ∈ Icc (r - ρ) (r + ρ),
      |deriv f x - deriv f y| ≤ K * |x - y|)
    (hder : ∀ x ∈ Icc (r - ρ) (r + ρ), m ≤ |deriv f x|)
    (hrmem : r ∈ Icc (r - ρ) (r + ρ)) {x : ℝ} (hx : x ∈ Icc (r - ρ) (r + ρ)) :
    |newtonStep f (deriv f) x - r| ≤ K / m * |x - r| ^ 2 := by
  have hs : uIcc x r ⊆ Icc (r - ρ) (r + ρ) := ordConnected_Icc.uIcc_subset hx hrmem
  set h : ℝ → ℝ := fun t => f t - deriv f x * t with hh
  have hhd : ∀ t ∈ uIcc x r, HasDerivAt h (deriv f t - deriv f x) t := fun t ht => by
    exact ((hd t (hs ht)).hasDerivAt.fun_sub ((hasDerivAt_id t).const_mul (deriv f x))).congr_deriv
      (by ring)
  have hbound := (convex_uIcc x r).norm_image_sub_le_of_norm_deriv_le
    (fun t ht => (hhd t ht).differentiableAt) (C := K * |r - x|)
    (fun t ht => by
      rw [(hhd t ht).deriv, Real.norm_eq_abs]
      calc |deriv f t - deriv f x| ≤ K * |t - x| := hlip t (hs ht) x hx
        _ ≤ K * |r - x| := mul_le_mul_of_nonneg_left (Set.abs_sub_left_of_mem_uIcc ht) hK)
    (left_mem_uIcc) (right_mem_uIcc)
  have hfx : deriv f x ≠ 0 := fun h0 => by have := hder x hx; rw [h0, abs_zero] at this; linarith
  have key : newtonStep f (deriv f) x - r = (h r - h x) / deriv f x := by
    simp only [hh, newtonStep, hr]
    field_simp
    ring
  rw [key, abs_div]
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hbound
  calc |h r - h x| / |deriv f x| ≤ (K * |r - x| * |r - x|) / m := by
        refine div_le_div₀ (by positivity) ?_ hm (hder x hx)
        have := hbound
        rwa [show h r - h x = h r - h x from rfl] at this
    _ = K / m * |x - r| ^ 2 := by
        rw [abs_sub_comm r x]; field_simp

/-- OpenStax Calculus 1:§4.9 (CA-172), local quadratic convergence (stretch result beyond the book): under
the hypotheses of `newtonStep_sub_le` with `K > 0`, there is `δ > 0` such that for every start `x₀` with
`|x₀ - r| ≤ δ`, each Newton step satisfies `|x_{n+1} - r| ≤ (K/m)|x_n - r|²` and `x_n → r`. -/
@[kb "openstaxcalculus2016" "1:§4.9 Newton's method iteration formula (Equation 4.8), p. 418"]
theorem newton_local_convergence {f : ℝ → ℝ} {r ρ K m : ℝ} (hρ : 0 < ρ) (hr : f r = 0)
    (hK : 0 < K) (hm : 0 < m)
    (hd : ∀ x ∈ Icc (r - ρ) (r + ρ), DifferentiableAt ℝ f x)
    (hlip : ∀ x ∈ Icc (r - ρ) (r + ρ), ∀ y ∈ Icc (r - ρ) (r + ρ),
      |deriv f x - deriv f y| ≤ K * |x - y|)
    (hder : ∀ x ∈ Icc (r - ρ) (r + ρ), m ≤ |deriv f x|) :
    ∃ δ > 0, ∀ x₀, |x₀ - r| ≤ δ →
      (∀ n, |newtonSeq f (deriv f) x₀ (n + 1) - r| ≤ K / m * |newtonSeq f (deriv f) x₀ n - r| ^ 2) ∧
      Tendsto (newtonSeq f (deriv f) x₀) atTop (𝓝 r) := by
  have hrmem : r ∈ Icc (r - ρ) (r + ρ) := ⟨by linarith, by linarith⟩
  have hmem : ∀ x, |x - r| ≤ ρ → x ∈ Icc (r - ρ) (r + ρ) := fun x hx =>
    ⟨by linarith [(abs_le.mp hx).1], by linarith [(abs_le.mp hx).2]⟩
  have hstep := fun x (hx : x ∈ Icc (r - ρ) (r + ρ)) =>
    newtonStep_sub_le hr hK.le hm hd hlip hder hrmem hx
  refine ⟨min ρ (m / (2 * K)), lt_min hρ (by positivity), fun x₀ hx₀ => ?_⟩
  have hδρ : min ρ (m / (2 * K)) ≤ ρ := min_le_left _ _
  have hδm : min ρ (m / (2 * K)) ≤ m / (2 * K) := min_le_right _ _
  -- geometric decay
  have hdecay : ∀ n, |newtonSeq f (deriv f) x₀ n - r| ≤ (1 / 2) ^ n * |x₀ - r| := by
    intro n
    induction n with
    | zero => simp [newtonSeq]
    | succ n ih =>
      have hle : |newtonSeq f (deriv f) x₀ n - r| ≤ |x₀ - r| := by
        refine ih.trans ?_
        exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ (by norm_num) (by norm_num))
      have hxn : |newtonSeq f (deriv f) x₀ n - r| ≤ m / (2 * K) :=
        hle.trans (hx₀.trans hδm)
      have hmemn := hmem _ (hle.trans (hx₀.trans hδρ))
      rw [newtonSeq_succ]
      have h1 := hstep _ hmemn
      have h2 : K / m * |newtonSeq f (deriv f) x₀ n - r| ^ 2 ≤ 1 / 2 * |newtonSeq f (deriv f) x₀ n - r| := by
        have : K / m * |newtonSeq f (deriv f) x₀ n - r| ≤ 1 / 2 := by
          calc K / m * |newtonSeq f (deriv f) x₀ n - r| ≤ K / m * (m / (2 * K)) :=
                mul_le_mul_of_nonneg_left hxn (by positivity)
            _ = 1 / 2 := by field_simp
        calc K / m * |newtonSeq f (deriv f) x₀ n - r| ^ 2
            = (K / m * |newtonSeq f (deriv f) x₀ n - r|) * |newtonSeq f (deriv f) x₀ n - r| := by ring
          _ ≤ 1 / 2 * |newtonSeq f (deriv f) x₀ n - r| :=
              mul_le_mul_of_nonneg_right this (abs_nonneg _)
      calc _ ≤ _ := h1
        _ ≤ 1 / 2 * |newtonSeq f (deriv f) x₀ n - r| := h2
        _ ≤ 1 / 2 * ((1 / 2) ^ n * |x₀ - r|) := by linarith
        _ = (1 / 2) ^ (n + 1) * |x₀ - r| := by ring
  refine ⟨fun n => ?_, ?_⟩
  · rw [newtonSeq_succ]
    have hle : |newtonSeq f (deriv f) x₀ n - r| ≤ |x₀ - r| :=
      (hdecay n).trans (mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ (by norm_num) (by norm_num)))
    exact hstep _ (hmem _ (hle.trans (hx₀.trans hδρ)))
  · rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (g := fun n => (1 / 2 : ℝ) ^ n * |x₀ - r|) (fun n => dist_nonneg) (fun n => ?_) ?_
    · exact (Real.dist_eq _ _ ▸ hdecay n : dist (newtonSeq f (deriv f) x₀ n) r ≤ _)
    · have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).mul_const |x₀ - r|
      simpa using this

/-- OpenStax Calculus 1:§4.9 (CA-172), `C²` form (stretch): if `f` is `C²`, `f r = 0` and `f'(r) ≠ 0`
(a simple root), then there are `δ > 0` and `C` such that Newton's iteration started within `δ` of `r`
converges to `r` and satisfies `|x_{n+1} - r| ≤ C |x_n - r|²`. -/
@[kb "openstaxcalculus2016" "1:§4.9 Newton's method iteration formula (Equation 4.8), p. 418"]
theorem newton_local_convergence_of_contDiff {f : ℝ → ℝ} {r : ℝ} (hf : ContDiff ℝ 2 f) (hr : f r = 0)
    (hr' : deriv f r ≠ 0) :
    ∃ δ > 0, ∃ C : ℝ, ∀ x₀, |x₀ - r| ≤ δ →
      (∀ n, |newtonSeq f (deriv f) x₀ (n + 1) - r| ≤ C * |newtonSeq f (deriv f) x₀ n - r| ^ 2) ∧
      Tendsto (newtonSeq f (deriv f) x₀) atTop (𝓝 r) := by
  have hdf : ContDiff ℝ 1 (deriv f) := by
    have h2 : ContDiff ℝ ((1 : ℕ∞ω) + 1) f := by
      have : ((1 : ℕ∞ω) + 1) = 2 := by norm_num
      rw [this]; exact hf
    exact ((contDiff_succ_iff_deriv (n := 1)).mp h2).2.2
  have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  obtain ⟨K, t, ht, hKt⟩ := hdf.contDiffAt.exists_lipschitzOnWith (x := r)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp ht
  have hcont : Continuous (deriv f) := hdf.continuous
  have hpos : 0 < |deriv f r| := abs_pos.mpr hr'
  have hnear : ∀ᶠ x in 𝓝 r, |deriv f r| / 2 < |deriv f x| := by
    have := (continuous_abs.comp hcont).continuousAt (x := r)
    exact this.eventually (lt_mem_nhds (by linarith : |deriv f r| / 2 < |deriv f r|))
  obtain ⟨ε', hε', hball'⟩ := Metric.mem_nhds_iff.mp hnear
  set ρ := min ε ε' / 2 with hρ
  have hρpos : 0 < ρ := by positivity
  have hρε : ρ < ε := by have := min_le_left ε ε'; simp only [hρ]; linarith
  have hρε' : ρ < ε' := by have := min_le_right ε ε'; simp only [hρ]; linarith
  have hin : ∀ x ∈ Icc (r - ρ) (r + ρ), dist x r < ε ∧ dist x r < ε' := fun x hx => by
    have : |x - r| ≤ ρ := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    rw [Real.dist_eq]
    exact ⟨by linarith, by linarith⟩
  have hK1 : 0 < (K : ℝ) + 1 := by positivity
  obtain ⟨δ, hδ, H⟩ := newton_local_convergence (f := f) (r := r) (ρ := ρ) (K := (K : ℝ) + 1)
    (m := |deriv f r| / 2) hρpos hr hK1 (by positivity)
    (fun x _ => hdiff x)
    (fun x hx y hy => by
      have h := hKt.dist_le_mul x (hball (hin x hx).1) y (hball (hin y hy).1)
      rw [Real.dist_eq, Real.dist_eq] at h
      nlinarith [abs_nonneg (x - y)])
    (fun x hx => le_of_lt (hball' (hin x hx).2))
  exact ⟨δ, hδ, ((K : ℝ) + 1) / (|deriv f r| / 2), H⟩

end UndergradKB.Calculus
