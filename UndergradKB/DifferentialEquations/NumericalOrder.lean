import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import UndergradKB.Common.Attr
import UndergradKB.DifferentialEquations.FirstOrderExtra

/-! # Order of the improved Euler method for general `f` (Lebl, §1.7)

* DE-039: for `f` of class `C²` and `y' = f(x, y)`, one Heun step from the exact value has local truncation
  error `O(h³)`, i.e. the improved Euler method is second order.
* DE-038 (partial): for `y' = g(x)` a Runge-Kutta step is Simpson's rule, with local error `O(h⁵)` for `g ∈ C⁴`.
-/

namespace UndergradKB.DifferentialEquations

open Set Filter Topology Metric

/-- First-order Taylor expansion with quadratic remainder for a function of class `C²` at a point. -/
theorem taylor_quadratic_remainder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (p : E) (hF : ContDiffAt ℝ 2 F p) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ r : ℝ, 0 < r ∧ ∀ v : E, ‖v‖ < r →
      |F (p + v) - F p - fderiv ℝ F p v| ≤ K * ‖v‖ ^ 2 := by
  obtain ⟨K, t, ht, hK⟩ := (hF.fderiv_right (m := 1) (by norm_num)).exists_lipschitzOnWith
  have hev : ∀ᶠ q in 𝓝 p, ContDiffAt ℝ 2 F q := hF.eventually (by simp)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem ht hev)
  refine ⟨K, K.2, r, hr, fun v hv => ?_⟩
  have hsub : closedBall p ‖v‖ ⊆ ball p r := closedBall_subset_ball hv
  have hdiff : ∀ q ∈ closedBall p ‖v‖, HasFDerivAt (fun q => F q - fderiv ℝ F p q)
      (fderiv ℝ F q - fderiv ℝ F p) q := by
    intro q hq
    have hq' : ContDiffAt ℝ 2 F q := (hball (hsub hq)).2
    exact (hq'.differentiableAt (by norm_num)).hasFDerivAt.sub (fderiv ℝ F p).hasFDerivAt
  have hbd : ∀ q ∈ closedBall p ‖v‖, ‖fderiv ℝ F q - fderiv ℝ F p‖ ≤ K * ‖v‖ := by
    intro q hq
    have h1 := hK.dist_le_mul q (hball (hsub hq)).1 p (mem_of_mem_nhds ht)
    rw [dist_eq_norm, dist_eq_norm] at h1
    have h2 : ‖q - p‖ ≤ ‖v‖ := by simpa [dist_eq_norm] using hq
    calc _ ≤ K * ‖q - p‖ := h1
      _ ≤ K * ‖v‖ := by gcongr
  have key := (convex_closedBall p ‖v‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun q hq => (hdiff q hq).hasFDerivWithinAt) hbd (mem_closedBall_self (norm_nonneg v))
    (show p + v ∈ closedBall p ‖v‖ by simp)
  have e : (F (p + v) - fderiv ℝ F p (p + v)) - (F p - fderiv ℝ F p p) =
      F (p + v) - F p - fderiv ℝ F p v := by simp; ring
  simp only [e, add_sub_cancel_left, Real.norm_eq_abs] at key
  calc _ ≤ _ := key
    _ = _ := by ring

section Heun

variable (f : ℝ → ℝ → ℝ) (hf : ContDiff ℝ 2 (fun p : ℝ × ℝ => f p.1 p.2))
  (y : ℝ → ℝ) (x₀ : ℝ) (hy : ∀ᶠ t in 𝓝 x₀, HasDerivAt y (f t (y t)) t)

include hf hy in
/-- A solution of `y' = f(x, y)` with `f` of class `C²` is `C²` at `x₀`. -/
theorem solution_contDiffAt_two : ContDiffAt ℝ 2 y x₀ := by
  have ha : ∀ m : ℕ, m ≤ 2 → ContDiffAt ℝ m y x₀ → ContDiffAt ℝ m (fun t => f t (y t)) x₀ :=
    fun m hm h => ContDiffAt.comp (g := fun p : ℝ × ℝ => f p.1 p.2) x₀
      ((hf.contDiffAt (x := (x₀, y x₀))).of_le (by exact_mod_cast hm))
      (contDiffAt_id.prodMk h)
  have step : ∀ m : ℕ, ContDiffAt ℝ m (fun t => f t (y t)) x₀ → ContDiffAt ℝ (m + 1 : ℕ) y x₀ := by
    intro m h
    rw [Nat.cast_succ, contDiffAt_succ_iff_hasFDerivAt]
    refine ⟨fun t => (1 : ℝ →L[ℝ] ℝ).smulRight (f t (y t)),
      ⟨_, hy, fun t ht => ht.hasFDerivAt⟩, ?_⟩
    have := h.smul (contDiffAt_const (c := (1 : ℝ →L[ℝ] ℝ)))
    convert this using 2 with t
    ext; simp
  have h0 : ContDiffAt ℝ (0 : ℕ) y x₀ := by
    exact contDiffAt_zero.2 ⟨{t | HasDerivAt y (f t (y t)) t}, hy,
      fun t ht => (show HasDerivAt y (f t (y t)) t from ht).continuousAt.continuousWithinAt⟩
  have h1 := step 0 (ha 0 (by norm_num) h0)
  have h2 := step 1 (ha 1 (by norm_num) (by simpa using h1))
  simpa using h2

include hf hy in
/-- Second-order Taylor expansion of a solution with cubic remainder; `b₀ = a'(x₀)` for `a(t) = f(t, y(t))`. -/
theorem solution_taylor :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, |h| < δ →
      |y (x₀ + h) - y x₀ - h * f x₀ (y x₀) - h ^ 2 / 2 * deriv (fun t => f t (y t)) x₀|
        ≤ K * |h| ^ 3 := by
  have hy2 := solution_contDiffAt_two f hf y x₀ hy
  have ha2 : ContDiffAt ℝ 2 (fun t => f t (y t)) x₀ :=
    ContDiffAt.comp (g := fun p : ℝ × ℝ => f p.1 p.2) x₀
      (hf.contDiffAt (x := (x₀, y x₀))) (contDiffAt_id.prodMk hy2)
  obtain ⟨K, hK0, r, hr, hrem⟩ := taylor_quadratic_remainder _ x₀ ha2
  obtain ⟨s, hs, hs'⟩ := Metric.eventually_nhds_iff.1 hy
  refine ⟨K, hK0, min r s, lt_min hr hs, fun h hh => ?_⟩
  have hhr : |h| < r := lt_of_lt_of_le hh (min_le_left _ _)
  have hhs : |h| < s := lt_of_lt_of_le hh (min_le_right _ _)
  set a : ℝ → ℝ := fun t => f t (y t) with ha
  set b₀ := deriv a x₀ with hb₀
  let ψ : ℝ → ℝ := fun u => y (x₀ + u) - y x₀ - u * a x₀ - u ^ 2 / 2 * b₀
  have hψ : ∀ u ∈ closedBall (0 : ℝ) |h|,
      HasDerivWithinAt ψ (a (x₀ + u) - a x₀ - u * b₀) (closedBall (0 : ℝ) |h|) u := by
    intro u hu
    have hu' : |u| ≤ |h| := by simpa [Real.dist_eq] using hu
    have hd : HasDerivAt (fun u => y (x₀ + u)) (a (x₀ + u)) u := by
      apply HasDerivAt.comp_const_add
      exact hs' (by simpa [Real.dist_eq] using lt_of_le_of_lt hu' hhs)
    have := ((hd.sub_const (y x₀)).sub ((hasDerivAt_id u).mul_const (a x₀))).sub
      (((hasDerivAt_pow 2 u).div_const 2).mul_const b₀)
    refine (HasDerivAt.hasDerivWithinAt ?_)
    convert this using 1
    · ext w; simp only [ψ, Pi.sub_apply, id]
    · norm_num
  have hbd : ∀ u ∈ closedBall (0 : ℝ) |h|, ‖a (x₀ + u) - a x₀ - u * b₀‖ ≤ K * |h| ^ 2 := by
    intro u hu
    have hu' : |u| ≤ |h| := by simpa [Real.dist_eq] using hu
    have h1 := hrem u (by simpa using lt_of_le_of_lt hu' hhr)
    have e : fderiv ℝ a x₀ u = u * b₀ := by
      rw [hb₀, ← fderiv_apply_one_eq_deriv]
      conv_lhs => rw [show u = u • (1 : ℝ) by simp]
      rw [map_smul]; simp
    rw [e] at h1
    rw [Real.norm_eq_abs]
    calc _ ≤ K * ‖u‖ ^ 2 := by simpa using h1
      _ ≤ K * |h| ^ 2 := by
        rw [Real.norm_eq_abs]; gcongr
  have key := (convex_closedBall (0 : ℝ) |h|).norm_image_sub_le_of_norm_hasDerivWithin_le hψ hbd
    (mem_closedBall_self (abs_nonneg h)) (show h ∈ closedBall (0 : ℝ) |h| by simp)
  simp only [ψ, Real.norm_eq_abs, sub_zero, zero_mul, add_zero, zero_pow two_ne_zero,
    zero_div] at key
  rw [show y x₀ - y x₀ = 0 by ring, sub_zero] at key
  calc _ ≤ K * |h| ^ 2 * |h| := key
    _ = K * |h| ^ 3 := by ring

include hf hy in
/-- **Improved Euler (Heun) method is second order** (DE-039): for `f` of class `C²` and a solution `y` of
`y' = f(x, y)` near `x₀`, one Heun step started at the exact value `y(x₀)` has local truncation error
`O(h³)`, i.e. the method is second order. (Added hypothesis: `f` is `C²` on all of `ℝ²`.) -/
@[kb "lebldiffyqs2026" "§1.7 improved Euler method, p. 62"]
theorem heunStep_local_error :
    ∃ C : ℝ, ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, |h| < δ →
      |y (x₀ + h) - heunStep f x₀ (y x₀) h| ≤ C * |h| ^ 3 := by
  obtain ⟨K₁, hK₁, δ₁, hδ₁, hT⟩ := solution_taylor f hf y x₀ hy
  have hy2 := solution_contDiffAt_two f hf y x₀ hy
  set a : ℝ → ℝ := fun t => f t (y t) with ha
  set F : ℝ × ℝ → ℝ := fun p => f p.1 p.2 with hF
  set a₀ := f x₀ (y x₀) with ha₀
  obtain ⟨K, hK, r, hr, hrem⟩ := taylor_quadratic_remainder F (x₀, y x₀) (hf.contDiffAt)
  have hyd : HasDerivAt y a₀ x₀ := hy.self_of_nhds
  have hγ : HasDerivAt (fun t => (t, y t)) ((1 : ℝ), a₀) x₀ := (hasDerivAt_id x₀).prodMk hyd
  have hFd : HasFDerivAt F (fderiv ℝ F (x₀, y x₀)) (x₀, y x₀) :=
    (hf.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt
  have hb : deriv a x₀ = fderiv ℝ F (x₀, y x₀) (1, a₀) := by
    have := HasFDerivAt.comp_hasDerivAt (l := F) x₀ hFd hγ
    exact this.deriv
  have hlin : ∀ h : ℝ, fderiv ℝ F (x₀, y x₀) (h, h * a₀) = h * deriv a x₀ := by
    intro h
    rw [hb, show (h, h * a₀) = h • ((1 : ℝ), a₀) by ext <;> simp, map_smul]
    simp
  set M : ℝ := 1 + |a₀| with hM
  have hM1 : 1 ≤ M := by have := abs_nonneg a₀; linarith
  have hMpos : 0 < M := by linarith
  refine ⟨K₁ + K * M ^ 2 / 2, min δ₁ (r / M), lt_min hδ₁ (div_pos hr hMpos), fun h hh => ?_⟩
  have hh1 : |h| < δ₁ := lt_of_lt_of_le hh (min_le_left _ _)
  have hh2 : |h| < r / M := lt_of_lt_of_le hh (min_le_right _ _)
  have hnorm : ‖(h, h * a₀)‖ ≤ M * |h| := by
    rw [Prod.norm_def]
    refine max_le ?_ ?_
    · rw [Real.norm_eq_abs]; nlinarith [abs_nonneg h, abs_nonneg a₀]
    · rw [Real.norm_eq_abs, abs_mul]; nlinarith [abs_nonneg h, abs_nonneg a₀]
  have hnorm' : ‖(h, h * a₀)‖ < r := by
    calc _ ≤ M * |h| := hnorm
      _ < M * (r / M) := by gcongr
      _ = r := by field_simp
  have hR := hrem (h, h * a₀) hnorm'
  rw [hlin] at hR
  have hFv : F ((x₀, y x₀) + (h, h * a₀)) = f (x₀ + h) (y x₀ + h * a₀) := by simp [hF]
  rw [hFv] at hR
  have hFp : F (x₀, y x₀) = a₀ := rfl
  rw [hFp] at hR
  have hT' := hT h hh1
  have hheun : heunStep f x₀ (y x₀) h = y x₀ + h * a₀ + h ^ 2 / 2 * deriv a x₀ +
      h / 2 * (f (x₀ + h) (y x₀ + h * a₀) - a₀ - h * deriv a x₀) := by
    unfold heunStep; rw [← ha₀]; ring
  rw [hheun]
  set R := f (x₀ + h) (y x₀ + h * a₀) - a₀ - h * deriv a x₀ with hRdef
  have hRb : |R| ≤ K * M ^ 2 * |h| ^ 2 := by
    calc |R| ≤ K * ‖(h, h * a₀)‖ ^ 2 := hR
      _ ≤ K * (M * |h|) ^ 2 := by gcongr
      _ = _ := by ring
  have e : y (x₀ + h) - (y x₀ + h * a₀ + h ^ 2 / 2 * deriv a x₀ + h / 2 * R) =
      (y (x₀ + h) - y x₀ - h * a₀ - h ^ 2 / 2 * deriv a x₀) - h / 2 * R := by ring
  rw [e]
  have h3 : |h / 2 * R| ≤ K * M ^ 2 / 2 * |h| ^ 3 := by
    rw [abs_mul, abs_div, abs_two]
    calc |h| / 2 * |R| ≤ |h| / 2 * (K * M ^ 2 * |h| ^ 2) := by gcongr
      _ = _ := by ring
  calc _ ≤ |y (x₀ + h) - y x₀ - h * a₀ - h ^ 2 / 2 * deriv a x₀| + |h / 2 * R| := abs_sub _ _
    _ ≤ K₁ * |h| ^ 3 + K * M ^ 2 / 2 * |h| ^ 3 := add_le_add hT' h3
    _ = _ := by ring

end Heun

/-! ### DE-038: Runge-Kutta for `y' = f(x)` (Simpson's rule) -/

/-- Taylor polynomial of degree 3 of a `C⁴` function at `x₀` with a quartic remainder bound on `[x₀, x₀+1]`. -/
theorem taylor_cubic_bound (g : ℝ → ℝ) (hg : ContDiff ℝ 4 g) (x₀ : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : ℝ, u ∈ Icc (0 : ℝ) 1 →
      |g (x₀ + u) - (iteratedDeriv 0 g x₀ + u * iteratedDeriv 1 g x₀ + u ^ 2 / 2 * iteratedDeriv 2 g x₀ +
        u ^ 3 / 6 * iteratedDeriv 3 g x₀)| ≤ K * u ^ 4 := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := x₀) (b := x₀ + 1)).exists_bound_of_continuousOn
    (hg.continuous_iteratedDeriv 4 (by norm_num)).continuousOn
  refine ⟨max M 0 / 6, by positivity, fun u hu => ?_⟩
  rcases eq_or_lt_of_le hu.1 with h0 | hpos
  · subst h0; simp
  have hlt : x₀ < x₀ + u := by linarith
  have hw : ∀ k : ℕ, k ≤ 4 →
      iteratedDerivWithin k g (Icc x₀ (x₀ + u)) x₀ = iteratedDeriv k g x₀ := fun k hk =>
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hlt)
      (hg.contDiffAt.of_le (by exact_mod_cast hk)) (left_mem_Icc.2 hlt.le)
  have hT := taylor_mean_remainder_bound (f := g) (a := x₀) (b := x₀ + u) (C := max M 0)
    (x := x₀ + u) (n := 3) hlt.le (hg.contDiffOn.of_le (by norm_num)) (right_mem_Icc.2 hlt.le)
    (fun z hz => by
      have hz' : z ∈ Icc x₀ (x₀ + 1) := ⟨hz.1, by linarith [hz.2, hu.2]⟩
      have h1 := hM z hz'
      have h2 : iteratedDerivWithin (3 + 1) g (Icc x₀ (x₀ + u)) z = iteratedDeriv 4 g z :=
        iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hlt)
          (hg.contDiffAt.of_le (by norm_num)) hz
      rw [h2]
      exact h1.trans (le_max_left _ _))
  rw [taylor_within_apply] at hT
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hw 0 (by norm_num), hw 1 (by norm_num),
    hw 2 (by norm_num), hw 3 (by norm_num), Nat.factorial, smul_eq_mul, Real.norm_eq_abs] at hT
  norm_num at hT
  rw [iteratedDeriv_zero, iteratedDeriv_one]
  refine le_trans (le_of_eq (by congr 2; ring)) (hT.trans (le_of_eq ?_))
  ring

/-- On `y' = f(x)` (no `y`-dependence) a Runge-Kutta step is Simpson's rule on `[x, x + h]`. -/
theorem rk4Step_x_only (g : ℝ → ℝ) (x y h : ℝ) :
    rk4Step (fun t _ => g t) x y h = y + h / 6 * (g x + 4 * g (x + h / 2) + g (x + h)) := by
  unfold rk4Step; ring

/-- **Runge-Kutta for `y' = f(x)` reduces to Simpson's rule and has local error `O(h⁵)`** (DE-038, partial: only
right-hand sides depending on `x` alone, not general `f(x, y)`). If `g` is `C⁴` and `y' = g` on `ℝ`, then one
RK4 step from the exact value satisfies `|y(x₀+h) - rk4Step| ≤ C h⁵` for `0 ≤ h ≤ 1`, so the method is fourth
order. (Added hypotheses: `g` is `C⁴` on all of `ℝ`, `y' = g` everywhere, `0 ≤ h ≤ 1`.) -/
@[kb "lebldiffyqs2026" "§1.7 Runge-Kutta method, p. 61"]
theorem rk4Step_x_only_local_error (g : ℝ → ℝ) (hg : ContDiff ℝ 4 g) (y : ℝ → ℝ)
    (hy : ∀ t, HasDerivAt y (g t) t) (x₀ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, h ∈ Icc (0 : ℝ) 1 →
      |y (x₀ + h) - rk4Step (fun t _ => g t) x₀ (y x₀) h| ≤ C * h ^ 5 := by
  obtain ⟨K, hK0, hK⟩ := taylor_cubic_bound g hg x₀
  refine ⟨2 * K, by positivity, fun h hh => ?_⟩
  set c0 := iteratedDeriv 0 g x₀
  set c1 := iteratedDeriv 1 g x₀
  set c2 := iteratedDeriv 2 g x₀
  set c3 := iteratedDeriv 3 g x₀
  let P : ℝ → ℝ := fun u => c0 + u * c1 + u ^ 2 / 2 * c2 + u ^ 3 / 6 * c3
  let ψ : ℝ → ℝ := fun u => y (x₀ + u) - y x₀ -
    (u * c0 + u ^ 2 / 2 * c1 + u ^ 3 / 6 * c2 + u ^ 4 / 24 * c3)
  have hψ : ∀ u ∈ Icc (0 : ℝ) h, HasDerivWithinAt ψ (g (x₀ + u) - P u) (Icc (0 : ℝ) h) u := by
    intro u _
    have hd : HasDerivAt (fun u => y (x₀ + u)) (g (x₀ + u)) u :=
      HasDerivAt.comp_const_add _ _ (hy (x₀ + u))
    have := (hd.sub_const (y x₀)).sub
      ((((((hasDerivAt_id u).mul_const c0).add (((hasDerivAt_pow 2 u).div_const 2).mul_const c1)).add
        (((hasDerivAt_pow 3 u).div_const 6).mul_const c2)).add
        (((hasDerivAt_pow 4 u).div_const 24).mul_const c3)))
    refine HasDerivAt.hasDerivWithinAt ?_
    convert this using 1
    · ext w; simp only [ψ, Pi.sub_apply, Pi.add_apply, id]
    · simp only [P]; norm_num; ring
  have hbd : ∀ u ∈ Icc (0 : ℝ) h, ‖g (x₀ + u) - P u‖ ≤ K * h ^ 4 := by
    intro u hu
    rw [Real.norm_eq_abs]
    refine (hK u ⟨hu.1, hu.2.trans hh.2⟩).trans ?_
    gcongr
    exacts [hu.1, hu.2]
  have key := (convex_Icc (0 : ℝ) h).norm_image_sub_le_of_norm_hasDerivWithin_le hψ hbd
    (left_mem_Icc.2 hh.1) (right_mem_Icc.2 hh.1)
  simp only [ψ, Real.norm_eq_abs, sub_zero, zero_mul, add_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0),
    zero_pow (by norm_num : (3:ℕ) ≠ 0), zero_pow (by norm_num : (4:ℕ) ≠ 0), zero_div,
    abs_of_nonneg hh.1, sub_self, sub_zero] at key
  have r0 : |g x₀ - P 0| ≤ 0 := by
    have := hK 0 ⟨le_rfl, zero_le_one⟩
    simpa [P] using this
  have r1 := hK (h / 2) ⟨by linarith [hh.1], by linarith [hh.2]⟩
  have r2 := hK h hh
  rw [rk4Step_x_only]
  have hP : h / 6 * (P 0 + 4 * P (h / 2) + P h) =
      h * c0 + h ^ 2 / 2 * c1 + h ^ 3 / 6 * c2 + h ^ 4 / 24 * c3 := by simp only [P]; ring
  have e : y (x₀ + h) - (y x₀ + h / 6 * (g x₀ + 4 * g (x₀ + h / 2) + g (x₀ + h))) =
      (y (x₀ + h) - y x₀ - (h * c0 + h ^ 2 / 2 * c1 + h ^ 3 / 6 * c2 + h ^ 4 / 24 * c3)) -
        h / 6 * ((g x₀ - P 0) + 4 * (g (x₀ + h / 2) - P (h / 2)) + (g (x₀ + h) - P h)) := by
    rw [← hP]; ring
  rw [e]
  have hh0 := hh.1
  have s1 : |h / 6 * ((g x₀ - P 0) + 4 * (g (x₀ + h / 2) - P (h / 2)) + (g (x₀ + h) - P h))| ≤
      h / 6 * (0 + 4 * (K * (h / 2) ^ 4) + K * h ^ 4) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ h / 6)]
    gcongr
    calc _ ≤ |g x₀ - P 0| + |4 * (g (x₀ + h / 2) - P (h / 2))| + |g (x₀ + h) - P h| := abs_add_three _ _ _
      _ ≤ _ := by
        rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4)]
        linarith
  calc _ ≤ |y (x₀ + h) - y x₀ - (h * c0 + h ^ 2 / 2 * c1 + h ^ 3 / 6 * c2 + h ^ 4 / 24 * c3)| +
        |h / 6 * ((g x₀ - P 0) + 4 * (g (x₀ + h / 2) - P (h / 2)) + (g (x₀ + h) - P h))| :=
        abs_sub _ _
    _ ≤ K * h ^ 4 * h + h / 6 * (0 + 4 * (K * (h / 2) ^ 4) + K * h ^ 4) := add_le_add key s1
    _ ≤ 2 * K * h ^ 5 := by
        have : 0 ≤ K * h ^ 5 := by positivity
        nlinarith

end UndergradKB.DifferentialEquations
