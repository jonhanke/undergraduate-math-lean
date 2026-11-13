import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import UndergradKB.Common.Attr
import UndergradKB.DifferentialEquations.FourierSeries

/-! # Convergence of Fourier series at jumps and corners (Dirichlet's theorem)

Lebl, *Notes on Diffy Qs*, Theorem 4.3.1: the Fourier series of a `2L`-periodic piecewise smooth function
converges at every point to the average of the one-sided limits (so to `f(t)` where `f` is continuous).

Proof (the classical one): the partial sum is an integral against the Dirichlet kernel,
`S_N f(x) = (1/L) ∫_0^L (f(x+s) + f(x-s)) D_N(s) ds`, `D_N(s) = 1/2 + ∑_{k=1}^N cos(kπs/L)`, with
`2 sin(πs/(2L)) D_N(s) = sin((N + 1/2)πs/L)`.  Subtracting the average of the one-sided limits leaves
`∫_0^L h(s) sin((N + 1/2)πs/L) ds` with `h` integrable (the one-sided difference quotients are bounded), which
tends to `0` by the Riemann-Lebesgue lemma (`Real.tendsto_integral_exp_smul_cocompact` in Mathlib).

The core theorem `fourier_tendsto_of_dini` assumes only integrability on a period and a one-sided Lipschitz
bound at the point; `fourier_series_piecewise_smooth` is the book's statement for piecewise smooth `f`
(`PiecewiseSmoothOn`, from `FourierSeries.lean`).  Then the sine and cosine series (DE-134). -/

namespace UndergradKB.DifferentialEquations

open Real intervalIntegral MeasureTheory Set Filter Topology

/-! ## Riemann-Lebesgue on an interval -/

/-- Riemann-Lebesgue lemma on an interval: `∫_a^b H(s) sin(ω s) ds → 0` as `ω → ∞`. -/
theorem tendsto_integral_mul_sin {H : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hH : IntegrableOn H (Ioc a b)) :
    Tendsto (fun ω : ℝ => ∫ s in a..b, H s * Real.sin (ω * s)) atTop (𝓝 0) := by
  set F : ℝ → ℂ := (Ioc a b).indicator (fun s => (H s : ℂ)) with hFdef
  have hF : Integrable F := (hH.ofReal).integrable_indicator measurableSet_Ioc
  have hRL := Real.tendsto_integral_exp_smul_cocompact F
  have hw : Tendsto (fun ω : ℝ => ω / (2 * π)) atTop (cocompact ℝ) :=
    (tendsto_id.atTop_div_const (by positivity)).mono_right atTop_le_cocompact
  have h1 := (Complex.continuous_im.tendsto 0).comp (hRL.comp hw)
  simp only [Complex.zero_im] at h1
  have key : ∀ ω : ℝ, (∫ v : ℝ, Real.fourierChar (-(v * (ω / (2 * π)))) • F v).im
      = - ∫ s in a..b, H s * Real.sin (ω * s) := by
    intro ω
    have hint : Integrable (fun v : ℝ => Real.fourierChar (-(v * (ω / (2 * π)))) • F v) := by
      refine (hF.norm).mono' ?_ (Eventually.of_forall fun v => ?_)
      · exact (Real.continuous_fourierChar.comp (by fun_prop : Continuous fun v : ℝ =>
          -(v * (ω / (2 * π))))).aestronglyMeasurable.smul hF.aestronglyMeasurable
      · simp [Circle.norm_smul]
    change RCLike.im (∫ v : ℝ, Real.fourierChar (-(v * (ω / (2 * π)))) • F v) = _
    rw [← integral_im hint, intervalIntegral.integral_of_le hab, ← MeasureTheory.integral_neg,
      ← MeasureTheory.integral_indicator measurableSet_Ioc]
    congr 1
    funext v
    by_cases hv : v ∈ Ioc a b
    · simp only [hFdef, indicator_of_mem hv, Real.fourierChar_apply, Circle.smul_def, smul_eq_mul]
      change Complex.im _ = _
      rw [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_add,
        show (↑(2 * π * -(v * (ω / (2 * π)))) * Complex.I) = ((-(ω * v) : ℝ) : ℂ) * Complex.I by
          push_cast; field_simp,
        Complex.exp_ofReal_mul_I_im, Real.sin_neg]
      ring
    · simp [hFdef, indicator_of_notMem hv]
  have h2 : Tendsto (fun ω : ℝ => - ∫ s in a..b, H s * Real.sin (ω * s)) atTop (𝓝 0) :=
    h1.congr (fun ω => key ω)
  simpa using h2.neg

/-! ## The Dirichlet kernel -/

/-- The Dirichlet kernel `D_N(s) = 1/2 + ∑_{k=1}^N cos(kπs/L)`. -/
noncomputable def dirichletKernel (L : ℝ) (N : ℕ) (s : ℝ) : ℝ :=
  1 / 2 + ∑ k ∈ Finset.Icc 1 N, Real.cos (k * π / L * s)

lemma dirichletKernel_mul_sin (L : ℝ) (N : ℕ) (s : ℝ) :
    2 * Real.sin (π / (2 * L) * s) * dirichletKernel L N s = Real.sin ((N + 1 / 2) * π / L * s) := by
  induction N with
  | zero =>
    simp only [dirichletKernel, Nat.zero_lt_one, Finset.Icc_eq_empty_of_lt, Finset.sum_empty, add_zero,
      Nat.cast_zero, zero_add]
    rw [show 1 / 2 * π / L * s = π / (2 * L) * s by ring]
    ring
  | succ N ih =>
    have hsplit : dirichletKernel L (N + 1) s =
        dirichletKernel L N s + Real.cos (((N + 1 : ℕ) : ℝ) * π / L * s) := by
      simp only [dirichletKernel]
      rw [Finset.sum_Icc_succ_top (by omega)]
      ring
    have key : ∀ u v : ℝ, 2 * Real.sin u * Real.cos v = Real.sin (v + u) - Real.sin (v - u) := by
      intro u v; rw [Real.sin_add, Real.sin_sub]; ring
    rw [hsplit, mul_add, ih, key]
    have e1 : (((N + 1 : ℕ) : ℝ)) * π / L * s - π / (2 * L) * s = ((N : ℝ) + 1 / 2) * π / L * s := by
      push_cast; ring
    have e2 : (((N + 1 : ℕ) : ℝ)) * π / L * s + π / (2 * L) * s = (((N + 1 : ℕ) : ℝ) + 1 / 2) * π / L * s := by
      push_cast; ring
    rw [e1, e2]
    ring

lemma dirichletKernel_neg (L : ℝ) (N : ℕ) (s : ℝ) : dirichletKernel L N (-s) = dirichletKernel L N s := by
  simp [dirichletKernel]

lemma dirichletKernel_periodic {L : ℝ} (hL : L ≠ 0) (N : ℕ) : Function.Periodic (dirichletKernel L N) (2 * L) := by
  intro s
  unfold dirichletKernel
  refine congrArg (fun z => 1 / 2 + z) (Finset.sum_congr rfl fun k _ => ?_)
  rw [show (k : ℝ) * π / L * (s + 2 * L) = (k : ℝ) * π / L * s + (k : ℕ) * (2 * π) by field_simp]
  exact Real.cos_add_nat_mul_two_pi _ _

lemma continuous_dirichletKernel (L : ℝ) (N : ℕ) : Continuous (dirichletKernel L N) := by
  unfold dirichletKernel; fun_prop

lemma integral_dirichletKernel {L : ℝ} (hL : 0 < L) (N : ℕ) :
    ∫ s in (0 : ℝ)..L, dirichletKernel L N s = L / 2 := by
  unfold dirichletKernel
  rw [intervalIntegral.integral_add (by simp) (by
    exact (by fun_prop : Continuous fun s : ℝ => ∑ k ∈ Finset.Icc 1 N, Real.cos ((k : ℝ) * π / L * s)).intervalIntegrable _ _),
    intervalIntegral.integral_finsetSum (fun k _ => by
      exact (by fun_prop : Continuous fun s : ℝ => Real.cos ((k : ℝ) * π / L * s)).intervalIntegrable _ _)]
  have hk : ∀ k ∈ Finset.Icc 1 N, ∫ s in (0 : ℝ)..L, Real.cos ((k : ℝ) * π / L * s) = 0 := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    have hc : (k : ℝ) * π / L ≠ 0 := by positivity
    rw [intervalIntegral.integral_comp_mul_left (fun s => Real.cos s) hc, integral_cos]
    rw [show (k : ℝ) * π / L * L = (k : ℕ) * π by field_simp, Real.sin_nat_mul_pi]
    simp
  rw [Finset.sum_eq_zero hk]
  simp
  ring

/-! ## The partial sum as an integral against the kernel -/

lemma ii_sum {ι : Type*} (s : Finset ι) {g : ι → ℝ → ℝ} {a b : ℝ}
    (h : ∀ i ∈ s, IntervalIntegrable (g i) volume a b) :
    IntervalIntegrable (fun t => ∑ i ∈ s, g i t) volume a b := by
  have := IntervalIntegrable.sum s h
  convert this using 1
  funext t
  simp [Finset.sum_apply]

lemma trigPoly_eq_kernel {f : ℝ → ℝ} {L : ℝ} (hint : IntervalIntegrable f volume (-L) L)
    (N : ℕ) (x : ℝ) :
    trigPoly L (fourierA f L) (fourierB f L) N x =
      (1 / L) * ∫ t in (-L)..L, f t * dirichletKernel L N (t - x) := by
  have hc : ∀ c : ℝ, IntervalIntegrable (fun t => f t * Real.cos (c * t)) volume (-L) L :=
    fun c => hint.mul_continuousOn (by fun_prop)
  have hs : ∀ c : ℝ, IntervalIntegrable (fun t => f t * Real.sin (c * t)) volume (-L) L :=
    fun c => hint.mul_continuousOn (by fun_prop)
  have e : ∀ t, f t * dirichletKernel L N (t - x) =
      f t * Real.cos (((0 : ℕ) : ℝ) * π / L * t) / 2 + ∑ k ∈ Finset.Icc 1 N,
        (f t * Real.cos ((k : ℝ) * π / L * t) * Real.cos ((k : ℝ) * π / L * x) +
          f t * Real.sin ((k : ℝ) * π / L * t) * Real.sin ((k : ℝ) * π / L * x)) := by
    intro t
    simp only [dirichletKernel, Nat.cast_zero, zero_mul, zero_div, Real.cos_zero, mul_add, Finset.mul_sum]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [show (k : ℝ) * π / L * (t - x) = (k : ℝ) * π / L * t - (k : ℝ) * π / L * x by ring, Real.cos_sub]
      ring
  rw [intervalIntegral.integral_congr (fun t _ => e t)]
  have hsum : ∀ k ∈ Finset.Icc 1 N, IntervalIntegrable (fun t => f t * Real.cos ((k : ℝ) * π / L * t) *
      Real.cos ((k : ℝ) * π / L * x) + f t * Real.sin ((k : ℝ) * π / L * t) * Real.sin ((k : ℝ) * π / L * x))
      volume (-L) L := fun k _ => ((hc _).mul_const _).add ((hs _).mul_const _)
  rw [intervalIntegral.integral_add ((hc _).div_const 2) (ii_sum _ hsum), intervalIntegral.integral_finsetSum hsum,
    intervalIntegral.integral_div]
  rw [Finset.sum_congr rfl fun k _ => intervalIntegral.integral_add ((hc _).mul_const _) ((hs _).mul_const _)]
  simp only [intervalIntegral.integral_mul_const]
  simp only [trigPoly, fourierA, fourierB, mul_add, Finset.mul_sum]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun k _ => ?_
    ring

lemma integral_kernel_shift {f : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (hper : Function.Periodic f (2 * L))
    (N : ℕ) (x : ℝ) :
    ∫ t in (-L)..L, f t * dirichletKernel L N (t - x) = ∫ s in (-L)..L, f (x + s) * dirichletKernel L N s := by
  have h1 := intervalIntegral.integral_comp_add_left (fun t => f t * dirichletKernel L N (t - x)) x
    (a := -L) (b := L)
  simp only [add_sub_cancel_left] at h1
  rw [h1]
  have hG : Function.Periodic (fun t => f t * dirichletKernel L N (t - x)) (2 * L) := by
    intro t
    simp only
    rw [hper t, show t + 2 * L - x = (t - x) + 2 * L by ring, dirichletKernel_periodic hL.ne' N]
  have h2 := hG.intervalIntegral_add_eq (x + -L) (-L)
  rw [show x + -L + 2 * L = x + L by ring, show -L + 2 * L = L by ring] at h2
  exact h2.symm

lemma integral_fold {F : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L) (hF : IntervalIntegrable F volume (-L) L) :
    ∫ s in (-L)..L, F s = ∫ s in (0 : ℝ)..L, (F s + F (-s)) := by
  have h0 : (0 : ℝ) ∈ uIcc (-L) L := Set.mem_uIcc.2 (Or.inl ⟨by linarith, hL⟩)
  have h1 : IntervalIntegrable F volume (-L) 0 := hF.mono_set (uIcc_subset_uIcc left_mem_uIcc h0)
  have h2 : IntervalIntegrable F volume 0 L := hF.mono_set (uIcc_subset_uIcc h0 right_mem_uIcc)
  have h1' : IntervalIntegrable (fun s => F (-s)) volume 0 L := by
    have := (h1.comp_sub_left 0).symm
    simpa using this
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2, intervalIntegral.integral_add h2 h1']
  have h3 : ∫ s in (0 : ℝ)..L, F (-s) = ∫ s in (-L)..0, F s := by
    rw [intervalIntegral.integral_comp_neg]; simp
  rw [h3]; ring

/-! ## Convergence under a one-sided Lipschitz (Dini) condition -/

lemma sin_half_ge {L s : ℝ} (hL : 0 < L) (hs0 : 0 ≤ s) (hsL : s ≤ L) : s / L ≤ Real.sin (π / (2 * L) * s) := by
  have h1 : 0 ≤ π / (2 * L) * s := by positivity
  have h2 : π / (2 * L) * s ≤ π / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Real.pi_pos]
  have := Real.mul_le_sin h1 h2
  calc s / L = 2 / π * (π / (2 * L) * s) := by field_simp
    _ ≤ _ := this

/-- **Dirichlet's convergence theorem, Dini form.** Let `f` be `2L`-periodic and integrable on a period, and
suppose that at `x` there are numbers `l₁, l₂` with `|f(x+s) - l₁| ≤ C s` and `|f(x-s) - l₂| ≤ C s` for
`0 < s < δ` (this holds at every point of a piecewise smooth function, with `l₁, l₂` the one-sided limits).
Then the partial sums `a₀/2 + ∑_{n=1}^N (aₙ cos(nπx/L) + bₙ sin(nπx/L))` tend to `(l₁ + l₂)/2`. -/
@[kb "lebldiffyqs2026" "Theorem 4.3.1, p. 211"]
theorem fourier_tendsto_of_dini {f : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (hper : Function.Periodic f (2 * L))
    (hint : IntervalIntegrable f volume (-L) L) {x l₁ l₂ C δ : ℝ} (hδ : 0 < δ)
    (h₁ : ∀ s ∈ Ioo 0 δ, |f (x + s) - l₁| ≤ C * s) (h₂ : ∀ s ∈ Ioo 0 δ, |f (x - s) - l₂| ≤ C * s) :
    Tendsto (fun N : ℕ => trigPoly L (fourierA f L) (fourierB f L) N x) atTop (𝓝 ((l₁ + l₂) / 2)) := by
  have hall : ∀ a b, IntervalIntegrable f volume a b :=
    hper.intervalIntegrable (by positivity) (t := -L) (by rwa [show -L + 2 * L = L by ring])
  have hplus : ∀ a b, IntervalIntegrable (fun s => f (x + s)) volume a b := fun a b => by
    simpa using (hall (x + a) (x + b)).comp_add_left x
  have hminus : ∀ a b, IntervalIntegrable (fun s => f (x - s)) volume a b := fun a b => by
    simpa using (hall (x - a) (x - b)).comp_sub_left x
  set G : ℝ → ℝ := fun s => (f (x + s) - l₁) + (f (x - s) - l₂) with hGdef
  have hG : IntervalIntegrable G volume 0 L :=
    ((hplus 0 L).sub intervalIntegrable_const).add ((hminus 0 L).sub intervalIntegrable_const)
  set H : ℝ → ℝ := fun s => G s * (Real.sin (π / (2 * L) * s))⁻¹ with hHdef
  -- the partial sum through the kernel
  have hform : ∀ N : ℕ, trigPoly L (fourierA f L) (fourierB f L) N x =
      (l₁ + l₂) / 2 + (1 / L) * ∫ s in (0 : ℝ)..L, G s * dirichletKernel L N s := by
    intro N
    have hD := continuous_dirichletKernel L N
    rw [trigPoly_eq_kernel hint, integral_kernel_shift hL hper,
      integral_fold hL.le ((hplus (-L) L).mul_continuousOn hD.continuousOn)]
    have e : ∀ s, f (x + s) * dirichletKernel L N s + f (x + -s) * dirichletKernel L N (-s) =
        G s * dirichletKernel L N s + (l₁ + l₂) * dirichletKernel L N s := by
      intro s; rw [dirichletKernel_neg, ← sub_eq_add_neg]; simp only [hGdef]; ring
    simp_rw [e]
    rw [intervalIntegral.integral_add (hG.mul_continuousOn hD.continuousOn)
      ((hD.intervalIntegrable _ _).const_mul _), intervalIntegral.integral_const_mul, integral_dirichletKernel hL]
    field_simp
    ring
  -- the kernel integral as a sine integral
  have hsin : ∀ N : ℕ, ∫ s in (0 : ℝ)..L, G s * dirichletKernel L N s =
      (1 / 2) * ∫ s in (0 : ℝ)..L, H s * Real.sin ((N + 1 / 2) * π / L * s) := by
    intro N
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun s hs => ?_)
    rw [uIoc_of_le hL.le] at hs
    have hpos : 0 < Real.sin (π / (2 * L) * s) :=
      lt_of_lt_of_le (div_pos hs.1 hL) (sin_half_ge hL hs.1.le hs.2)
    have hk := dirichletKernel_mul_sin L N s
    simp only [hHdef]
    rw [← hk]
    generalize Real.sin (π / (2 * L) * s) = A at hpos ⊢
    field_simp
  -- integrability of H
  have hH : IntegrableOn H (Ioc 0 L) := by
    set m := min δ L with hm
    have hm0 : 0 < m := lt_min hδ hL
    have hGi : IntegrableOn G (Ioc 0 L) := (intervalIntegrable_iff_integrableOn_Ioc_of_le hL.le).mp hG
    refine Integrable.mono' (g := fun s => 2 * |C| * L + |G s| * (L / m)) ?_ ?_ ?_
    · exact (integrableOn_const (by simp)).add (hGi.norm.mul_const _)
    · exact hGi.aestronglyMeasurable.mul
        ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).measurable.inv.aestronglyMeasurable)
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs => ?_)
      have hsL : s / L ≤ Real.sin (π / (2 * L) * s) := sin_half_ge hL hs.1.le hs.2
      have hsl0 : 0 < s / L := div_pos hs.1 hL
      have hpos : 0 < Real.sin (π / (2 * L) * s) := lt_of_lt_of_le hsl0 hsL
      simp only [hHdef, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hpos]
      rw [← div_eq_mul_inv, div_le_iff₀ hpos]
      by_cases hsδ : s < δ
      · have hb : |G s| ≤ 2 * C * s := by
          simp only [hGdef]
          have := h₁ s ⟨hs.1, hsδ⟩
          have := h₂ s ⟨hs.1, hsδ⟩
          calc _ ≤ |f (x + s) - l₁| + |f (x - s) - l₂| := abs_add_le _ _
            _ ≤ _ := by linarith
        have hC : 2 * C * s ≤ 2 * |C| * L * (s / L) := by
          rw [show 2 * |C| * L * (s / L) = 2 * |C| * s by field_simp]
          nlinarith [le_abs_self C, hs.1]
        nlinarith [abs_nonneg (G s), mul_le_mul_of_nonneg_left hsL (show 0 ≤ 2 * |C| * L by positivity),
          mul_nonneg (mul_nonneg (abs_nonneg (G s)) (show 0 ≤ L / m by positivity)) hpos.le]
      · have hms : m ≤ s := le_trans (min_le_left _ _) (not_lt.mp hsδ)
        have h1 : 1 ≤ L / m * Real.sin (π / (2 * L) * s) := by
          calc (1 : ℝ) = L / m * (m / L) := by field_simp
            _ ≤ L / m * (s / L) := by gcongr
            _ ≤ _ := by gcongr
        nlinarith [abs_nonneg (G s), mul_le_mul_of_nonneg_left h1 (abs_nonneg (G s)),
          mul_nonneg (show 0 ≤ 2 * |C| * L by positivity) hpos.le]
  -- Riemann-Lebesgue
  have hω : Tendsto (fun N : ℕ => ((N : ℝ) + 1 / 2) * π / L) atTop atTop := by
    refine Tendsto.atTop_div_const hL (Tendsto.atTop_mul_const Real.pi_pos ?_)
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hRL := (tendsto_integral_mul_sin hL.le hH).comp hω
  have hlim : Tendsto (fun N : ℕ => (l₁ + l₂) / 2 + (1 / L) * ((1 / 2) *
      ∫ s in (0 : ℝ)..L, H s * Real.sin ((N + 1 / 2) * π / L * s))) atTop (𝓝 ((l₁ + l₂) / 2)) := by
    have := (hRL.const_mul (1 / 2)).const_mul (1 / L) |>.const_add ((l₁ + l₂) / 2)
    simpa using this
  refine hlim.congr fun N => ?_
  rw [hform N, hsin N]

/-! ## Piecewise continuous and piecewise smooth functions -/

lemma pc_local_bound {f : ℝ → ℝ} {a b : ℝ} {S : Finset ℝ}
    (hc : ∀ x ∈ Icc a b, x ∉ S → ContinuousWithinAt f (Icc a b) x)
    (hl : ∀ x ∈ S, (a < x → ∃ l, Tendsto f (𝓝[<] x) (𝓝 l)) ∧ (x < b → ∃ l, Tendsto f (𝓝[>] x) (𝓝 l)))
    {y : ℝ} (hy : y ∈ Icc a b) : ∃ M, ∀ᶠ z in 𝓝 y, z ∈ Icc a b → |f z| ≤ M := by
  by_cases hyS : y ∈ S
  · have h1 : ∃ M₁, ∀ᶠ z in 𝓝[<] y, z ∈ Icc a b → |f z| ≤ M₁ := by
      by_cases hay : a < y
      · obtain ⟨l, hl'⟩ := (hl y hyS).1 hay
        refine ⟨|l| + 1, (hl'.eventually (Metric.ball_mem_nhds l one_pos)).mono fun z hz _ => ?_⟩
        rw [Real.dist_eq] at hz
        have := abs_sub_abs_le_abs_sub (f z) l
        linarith
      · refine ⟨0, Filter.mem_of_superset (self_mem_nhdsWithin : Iio y ∈ 𝓝[<] y) fun z hz hzI => ?_⟩
        exact absurd (lt_of_le_of_lt hzI.1 (show z < y from hz)) (by linarith [hy.1, not_lt.mp hay])
    have h2 : ∃ M₂, ∀ᶠ z in 𝓝[>] y, z ∈ Icc a b → |f z| ≤ M₂ := by
      by_cases hyb : y < b
      · obtain ⟨l, hl'⟩ := (hl y hyS).2 hyb
        refine ⟨|l| + 1, (hl'.eventually (Metric.ball_mem_nhds l one_pos)).mono fun z hz _ => ?_⟩
        rw [Real.dist_eq] at hz
        have := abs_sub_abs_le_abs_sub (f z) l
        linarith
      · refine ⟨0, Filter.mem_of_superset (self_mem_nhdsWithin : Ioi y ∈ 𝓝[>] y) fun z hz hzI => ?_⟩
        exact absurd (lt_of_lt_of_le (show y < z from hz) hzI.2) (by linarith [hy.2, not_lt.mp hyb])
    obtain ⟨M₁, hM₁⟩ := h1
    obtain ⟨M₂, hM₂⟩ := h2
    refine ⟨max (max M₁ M₂) |f y|, ?_⟩
    rw [← nhdsNE_sup_pure, ← nhdsLT_sup_nhdsGT]
    refine Filter.eventually_sup.2 ⟨Filter.eventually_sup.2 ⟨hM₁.mono fun z hz hzI => ?_,
      hM₂.mono fun z hz hzI => ?_⟩, ?_⟩
    · exact le_trans (hz hzI) (le_trans (le_max_left _ _) (le_max_left _ _))
    · exact le_trans (hz hzI) (le_trans (le_max_right _ _) (le_max_left _ _))
    · exact Filter.eventually_pure.2 fun _ => le_max_right _ _
  · have h := hc y hy hyS
    refine ⟨|f y| + 1, ?_⟩
    have := (h.eventually (Metric.ball_mem_nhds (f y) one_pos))
    rw [eventually_nhdsWithin_iff] at this
    refine this.mono fun z hz hzI => ?_
    have hz' := hz hzI
    rw [Real.dist_eq] at hz'
    have := abs_sub_abs_le_abs_sub (f z) (f y)
    linarith

/-- A piecewise continuous function on `[a, b]` is bounded there. -/
lemma PiecewiseContinuousOn.bounded {f : ℝ → ℝ} {a b : ℝ} (h : PiecewiseContinuousOn f a b) :
    ∃ M, ∀ y ∈ Icc a b, |f y| ≤ M := by
  obtain ⟨S, hc, hl⟩ := h
  refine isCompact_Icc.induction_on (p := fun t => ∃ M, ∀ y ∈ t, |f y| ≤ M) ⟨0, by simp⟩
    (fun s t hst ⟨M, hM⟩ => ⟨M, fun y hy => hM y (hst hy)⟩)
    (fun s t ⟨M, hM⟩ ⟨M', hM'⟩ => ⟨max M M', fun y hy => hy.elim
      (fun h => le_trans (hM y h) (le_max_left _ _)) (fun h => le_trans (hM' y h) (le_max_right _ _))⟩) ?_
  intro y hy
  obtain ⟨M, hM⟩ := pc_local_bound hc hl hy
  refine ⟨{z | z ∈ Icc a b → |f z| ≤ M} ∩ Icc a b, ?_, M, fun z hz => hz.1 hz.2⟩
  exact Filter.inter_mem (mem_nhdsWithin_of_mem_nhds hM) self_mem_nhdsWithin

/-- A piecewise continuous function on `[a, b]` is integrable there. -/
lemma PiecewiseContinuousOn.intervalIntegrable {f : ℝ → ℝ} {a b : ℝ} (h : PiecewiseContinuousOn f a b)
    (hab : a ≤ b) : IntervalIntegrable f volume a b := by
  obtain ⟨M, hM⟩ := h.bounded
  obtain ⟨S, hc, -⟩ := h
  have hmeas : MeasurableSet (Icc a b \ (S : Set ℝ)) :=
    measurableSet_Icc.diff S.finite_toSet.measurableSet
  have hcont : ContinuousOn f (Icc a b \ (S : Set ℝ)) := fun y hy => (hc y hy.1 hy.2).mono sdiff_subset
  have h1 : IntegrableOn f (Icc a b \ (S : Set ℝ)) := by
    refine ⟨hcont.aestronglyMeasurable hmeas, HasFiniteIntegral.restrict_of_bounded (C := M) ?_ ?_⟩
    · refine lt_top_iff_ne_top.2 ?_
      exact ne_top_of_le_ne_top (measure_Icc_lt_top (a := a) (b := b)).ne (measure_mono sdiff_subset)
    · refine (ae_restrict_iff' hmeas).2 (Eventually.of_forall fun y hy => ?_)
      simpa [Real.norm_eq_abs] using hM y hy.1
  have h2 : IntegrableOn f (S : Set ℝ) := by
    have : volume.restrict (S : Set ℝ) = 0 := Measure.restrict_eq_zero.2 (S.finite_toSet.measure_zero _)
    unfold IntegrableOn; rw [this]; exact integrable_zero_measure
  have h3 : IntegrableOn f (Icc a b) := (integrableOn_union.2 ⟨h1, h2⟩).mono_set fun y hy => by
    by_cases hyS : y ∈ (S : Set ℝ)
    · exact Or.inr hyS
    · exact Or.inl ⟨hy, hyS⟩
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 h3

/-- A one-sided Lipschitz bound gives the one-sided limit. -/
lemma tendsto_nhdsGT_of_dini {f : ℝ → ℝ} {x l C δ : ℝ} (hδ : 0 < δ)
    (h : ∀ s ∈ Ioo 0 δ, |f (x + s) - l| ≤ C * s) : Tendsto f (𝓝[>] x) (𝓝 l) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun y => C * (y - x)) (𝓝[>] x) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds
      ((by fun_prop : Continuous fun y : ℝ => C * (y - x)).tendsto' x 0 (by simp))
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [Ioo_mem_nhdsGT (show x < x + δ by linarith)] with y hy
  have := h (y - x) ⟨by linarith [hy.1], by linarith [hy.2]⟩
  simpa [Real.norm_eq_abs] using this

lemma tendsto_nhdsLT_of_dini {f : ℝ → ℝ} {x l C δ : ℝ} (hδ : 0 < δ)
    (h : ∀ s ∈ Ioo 0 δ, |f (x - s) - l| ≤ C * s) : Tendsto f (𝓝[<] x) (𝓝 l) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun y => C * (x - y)) (𝓝[<] x) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds
      ((by fun_prop : Continuous fun y : ℝ => C * (x - y)).tendsto' x 0 (by simp))
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [Ioo_mem_nhdsLT (show x - δ < x by linarith)] with y hy
  have := h (x - y) ⟨by linarith [hy.2], by linarith [hy.1]⟩
  simpa [Real.norm_eq_abs] using this

lemma eventually_nhdsGT_not_mem (T : Finset ℝ) (x : ℝ) : ∀ᶠ y in 𝓝[>] x, y ∉ T := by
  have : ∀ᶠ y in 𝓝[>] x, ∀ t ∈ T, y ≠ t := by
    refine (Filter.eventually_all_finset T).2 fun t _ => ?_
    by_cases htx : t ≤ x
    · exact Filter.mem_of_superset self_mem_nhdsWithin fun y hy => ne_of_gt (lt_of_le_of_lt htx hy)
    · exact mem_nhdsWithin_of_mem_nhds (Filter.mem_of_superset (Iio_mem_nhds (not_le.mp htx)) fun y hy => ne_of_lt hy)
  exact this.mono fun y hy hyT => hy y hyT rfl

lemma eventually_nhdsLT_not_mem (T : Finset ℝ) (x : ℝ) : ∀ᶠ y in 𝓝[<] x, y ∉ T := by
  have : ∀ᶠ y in 𝓝[<] x, ∀ t ∈ T, y ≠ t := by
    refine (Filter.eventually_all_finset T).2 fun t _ => ?_
    by_cases htx : x ≤ t
    · exact Filter.mem_of_superset self_mem_nhdsWithin fun y hy => ne_of_lt (lt_of_lt_of_le hy htx)
    · exact mem_nhdsWithin_of_mem_nhds (Filter.mem_of_superset (Ioi_mem_nhds (not_le.mp htx)) fun y hy => ne_of_gt hy)
  exact this.mono fun y hy hyT => hy y hyT rfl

lemma abs_le_of_ball {u l : ℝ} (h : dist u l < 1) : |u| ≤ |l| + 1 := by
  rw [Real.dist_eq] at h
  have := abs_sub_abs_le_abs_sub u l
  linarith

/-- At a point of `[a, b)` a piecewise smooth function satisfies a right one-sided Lipschitz bound. -/
lemma PiecewiseSmoothOn.dini_right {f : ℝ → ℝ} {a b x : ℝ} (h : PiecewiseSmoothOn f a b)
    (hx : x ∈ Ico a b) : ∃ l C δ : ℝ, 0 < δ ∧ ∀ s ∈ Ioo 0 δ, |f (x + s) - l| ≤ C * s := by
  obtain ⟨⟨S1, hc1, hl1⟩, S2, hd, ⟨S3, hc3, hl3⟩⟩ := h
  have hIcc : Icc a b ∈ 𝓝[>] x :=
    Filter.mem_of_superset (Ioo_mem_nhdsGT hx.2) fun y hy => ⟨hx.1.trans hy.1.le, hy.2.le⟩
  have hD : ∃ l', Tendsto (deriv f) (𝓝[>] x) (𝓝 l') := by
    by_cases hx3 : x ∈ S3
    · exact (hl3 x hx3).2 hx.2
    · exact ⟨_, (hc3 x ⟨hx.1, hx.2.le⟩ hx3).mono_of_mem_nhdsWithin hIcc⟩
  have hF : ∃ l, Tendsto f (𝓝[>] x) (𝓝 l) := by
    by_cases hx1 : x ∈ S1
    · exact (hl1 x hx1).2 hx.2
    · exact ⟨_, (hc1 x ⟨hx.1, hx.2.le⟩ hx1).mono_of_mem_nhdsWithin hIcc⟩
  obtain ⟨l', hl'⟩ := hD
  obtain ⟨l, hl⟩ := hF
  have hev : ∀ᶠ y in 𝓝[>] x, y ∉ S2 ∧ y < b ∧ |deriv f y| ≤ |l'| + 1 :=
    (eventually_nhdsGT_not_mem S2 x).and ((show ∀ᶠ y in 𝓝[>] x, y < b from
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hx.2)).and
      ((hl'.eventually (Metric.ball_mem_nhds l' one_pos)).mono fun y hy => abs_le_of_ball hy))
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hxu : x < u := hu
  refine ⟨l, |l'| + 1, u - x, by linarith, fun s hs => ?_⟩
  have hdiff : ∀ y ∈ Ioo x u, DifferentiableAt ℝ f y := fun y hy =>
    hd y ⟨lt_of_le_of_lt hx.1 hy.1, (hsub hy).2.1⟩ (hsub hy).1
  have hbound : ∀ y ∈ Ioo x u, ‖deriv f y‖ ≤ |l'| + 1 := fun y hy => (hsub hy).2.2
  have key : ∀ s' ∈ Ioo 0 s, |f (x + s) - f (x + s')| ≤ (|l'| + 1) * s := by
    intro s' hs'
    have := (convex_Ioo x u).norm_image_sub_le_of_norm_deriv_le hdiff hbound
      (show x + s' ∈ Ioo x u from ⟨by linarith [hs'.1], by linarith [hs'.2, hs.2]⟩)
      (show x + s ∈ Ioo x u from ⟨by linarith [hs.1], by linarith [hs.2]⟩)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, show x + s - (x + s') = s - s' by ring,
      abs_of_pos (show (0 : ℝ) < s - s' by linarith [hs'.2])] at this
    nlinarith [abs_nonneg l', hs'.1]
  have hshift : Tendsto (fun s' => x + s') (𝓝[>] 0) (𝓝[>] x) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact tendsto_nhdsWithin_of_tendsto_nhds ((continuous_const.add continuous_id).tendsto' 0 x (by simp))
    · filter_upwards [self_mem_nhdsWithin] with s' hs'
      exact show x < x + s' by linarith [show (0 : ℝ) < s' from hs']
  have hlim : Tendsto (fun s' => |f (x + s) - f (x + s')|) (𝓝[>] 0) (𝓝 |f (x + s) - l|) :=
    ((tendsto_const_nhds.sub (hl.comp hshift)).abs)
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT hs.1] with s' hs'
  exact key s' hs'

/-- At a point of `(a, b]` a piecewise smooth function satisfies a left one-sided Lipschitz bound. -/
lemma PiecewiseSmoothOn.dini_left {f : ℝ → ℝ} {a b x : ℝ} (h : PiecewiseSmoothOn f a b)
    (hx : x ∈ Ioc a b) : ∃ l C δ : ℝ, 0 < δ ∧ ∀ s ∈ Ioo 0 δ, |f (x - s) - l| ≤ C * s := by
  obtain ⟨⟨S1, hc1, hl1⟩, S2, hd, ⟨S3, hc3, hl3⟩⟩ := h
  have hIcc : Icc a b ∈ 𝓝[<] x :=
    Filter.mem_of_superset (Ioo_mem_nhdsLT hx.1) fun y hy => ⟨hy.1.le, hy.2.le.trans hx.2⟩
  have hD : ∃ l', Tendsto (deriv f) (𝓝[<] x) (𝓝 l') := by
    by_cases hx3 : x ∈ S3
    · exact (hl3 x hx3).1 hx.1
    · exact ⟨_, (hc3 x ⟨hx.1.le, hx.2⟩ hx3).mono_of_mem_nhdsWithin hIcc⟩
  have hF : ∃ l, Tendsto f (𝓝[<] x) (𝓝 l) := by
    by_cases hx1 : x ∈ S1
    · exact (hl1 x hx1).1 hx.1
    · exact ⟨_, (hc1 x ⟨hx.1.le, hx.2⟩ hx1).mono_of_mem_nhdsWithin hIcc⟩
  obtain ⟨l', hl'⟩ := hD
  obtain ⟨l, hl⟩ := hF
  have hev : ∀ᶠ y in 𝓝[<] x, y ∉ S2 ∧ a < y ∧ |deriv f y| ≤ |l'| + 1 :=
    (eventually_nhdsLT_not_mem S2 x).and ((show ∀ᶠ y in 𝓝[<] x, a < y from
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hx.1)).and
      ((hl'.eventually (Metric.ball_mem_nhds l' one_pos)).mono fun y hy => abs_le_of_ball hy))
  obtain ⟨u, hu, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hev
  have hux : u < x := hu
  refine ⟨l, |l'| + 1, x - u, by linarith, fun s hs => ?_⟩
  have hdiff : ∀ y ∈ Ioo u x, DifferentiableAt ℝ f y := fun y hy =>
    hd y ⟨(hsub hy).2.1, lt_of_lt_of_le hy.2 hx.2⟩ (hsub hy).1
  have hbound : ∀ y ∈ Ioo u x, ‖deriv f y‖ ≤ |l'| + 1 := fun y hy => (hsub hy).2.2
  have key : ∀ s' ∈ Ioo 0 s, |f (x - s) - f (x - s')| ≤ (|l'| + 1) * s := by
    intro s' hs'
    have := (convex_Ioo u x).norm_image_sub_le_of_norm_deriv_le hdiff hbound
      (show x - s' ∈ Ioo u x from ⟨by linarith [hs'.2, hs.2], by linarith [hs'.1]⟩)
      (show x - s ∈ Ioo u x from ⟨by linarith [hs.2], by linarith [hs.1]⟩)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, show x - s - (x - s') = -(s - s') by ring, abs_neg,
      abs_of_pos (show (0 : ℝ) < s - s' by linarith [hs'.2])] at this
    nlinarith [abs_nonneg l', hs'.1]
  have hshift : Tendsto (fun s' => x - s') (𝓝[>] 0) (𝓝[<] x) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact tendsto_nhdsWithin_of_tendsto_nhds ((continuous_const.sub continuous_id).tendsto' 0 x (by simp))
    · filter_upwards [self_mem_nhdsWithin] with s' hs'
      exact show x - s' < x by linarith [show (0 : ℝ) < s' from hs']
  have hlim : Tendsto (fun s' => |f (x - s) - f (x - s')|) (𝓝[>] 0) (𝓝 |f (x - s) - l|) :=
    ((tendsto_const_nhds.sub (hl.comp hshift)).abs)
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT hs.1] with s' hs'
  exact key s' hs'

/-! ## Theorem 4.3.1 for piecewise smooth periodic functions -/

/-- Right one-sided Lipschitz (Dini) condition at `x` (bridging notion for the proofs below). -/
def DiniRight (F : ℝ → ℝ) (x : ℝ) : Prop := ∃ l C δ : ℝ, 0 < δ ∧ ∀ s ∈ Ioo 0 δ, |F (x + s) - l| ≤ C * s

/-- Left one-sided Lipschitz (Dini) condition at `x`. -/
def DiniLeft (F : ℝ → ℝ) (x : ℝ) : Prop := ∃ l C δ : ℝ, 0 < δ ∧ ∀ s ∈ Ioo 0 δ, |F (x - s) - l| ≤ C * s

lemma diniRight_of_eqOn {F f : ℝ → ℝ} {x ε : ℝ} (hε : 0 < ε) (heq : ∀ y ∈ Ioo x (x + ε), F y = f y)
    (h : DiniRight f x) : DiniRight F x := by
  obtain ⟨l, C, δ, hδ, hb⟩ := h
  refine ⟨l, C, min δ ε, lt_min hδ hε, fun s hs => ?_⟩
  rw [heq (x + s) ⟨by linarith [hs.1], by linarith [hs.2, min_le_right δ ε]⟩]
  exact hb s ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_left _ _)⟩

lemma diniLeft_of_eqOn {F f : ℝ → ℝ} {x ε : ℝ} (hε : 0 < ε) (heq : ∀ y ∈ Ioo (x - ε) x, F y = f y)
    (h : DiniLeft f x) : DiniLeft F x := by
  obtain ⟨l, C, δ, hδ, hb⟩ := h
  refine ⟨l, C, min δ ε, lt_min hδ hε, fun s hs => ?_⟩
  rw [heq (x - s) ⟨by linarith [hs.2, min_le_right δ ε], by linarith [hs.1]⟩]
  exact hb s ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_left _ _)⟩

/-- Reduction to one period: the Dini conditions at every point follow from those on `[-L, L)` and `(-L, L]`. -/
lemma dini_everywhere {F : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (hper : Function.Periodic F (2 * L))
    (hR : ∀ x ∈ Ico (-L) L, DiniRight F x) (hLft : ∀ x ∈ Ioc (-L) L, DiniLeft F x) (x : ℝ) :
    DiniRight F x ∧ DiniLeft F x := by
  have hp : 0 < 2 * L := by positivity
  constructor
  · have hm := toIcoMod_mem_Ico hp (-L) x
    rw [show -L + 2 * L = L by ring] at hm
    obtain ⟨l, C, δ, hδ, hb⟩ := hR _ hm
    refine ⟨l, C, δ, hδ, fun s hs => ?_⟩
    have := hb s hs
    rwa [← self_sub_toIcoDiv_zsmul, show x - toIcoDiv hp (-L) x • (2 * L) + s =
      (x + s) - toIcoDiv hp (-L) x • (2 * L) by ring, hper.sub_zsmul_eq] at this
  · have hm := toIocMod_mem_Ioc hp (-L) x
    rw [show -L + 2 * L = L by ring] at hm
    obtain ⟨l, C, δ, hδ, hb⟩ := hLft _ hm
    refine ⟨l, C, δ, hδ, fun s hs => ?_⟩
    have := hb s hs
    rwa [← self_sub_toIocDiv_zsmul, show x - toIocDiv hp (-L) x • (2 * L) - s =
      (x - s) - toIocDiv hp (-L) x • (2 * L) by ring, hper.sub_zsmul_eq] at this

/-- Convergence from Dini conditions at a point, with the one-sided limits. -/
lemma fourier_tendsto_of_diniRL {F : ℝ → ℝ} {L x : ℝ} (hL : 0 < L) (hper : Function.Periodic F (2 * L))
    (hint : IntervalIntegrable F volume (-L) L) (hR : DiniRight F x) (hLf : DiniLeft F x) :
    ∃ l₁ l₂, Tendsto F (𝓝[>] x) (𝓝 l₁) ∧ Tendsto F (𝓝[<] x) (𝓝 l₂) ∧
      Tendsto (fun N : ℕ => trigPoly L (fourierA F L) (fourierB F L) N x) atTop (𝓝 ((l₁ + l₂) / 2)) := by
  obtain ⟨l₁, C₁, δ₁, hδ₁, h₁⟩ := hR
  obtain ⟨l₂, C₂, δ₂, hδ₂, h₂⟩ := hLf
  refine ⟨l₁, l₂, tendsto_nhdsGT_of_dini hδ₁ h₁, tendsto_nhdsLT_of_dini hδ₂ h₂, ?_⟩
  refine fourier_tendsto_of_dini hL hper hint (C := max C₁ C₂) (δ := min δ₁ δ₂) (lt_min hδ₁ hδ₂)
    (fun s hs => ?_) (fun s hs => ?_)
  · exact (h₁ s ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_left _ _)⟩).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hs.1.le)
  · exact (h₂ s ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_right _ _)⟩).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hs.1.le)

/-- **Fourier convergence for piecewise smooth periodic functions (DE-129, Theorem 4.3.1).** Let `f` be
`2L`-periodic and piecewise smooth on `[-L, L]` (one period). At every `t` the one-sided limits `f(t+)`,
`f(t-)` exist and the Fourier series `a₀/2 + ∑ (aₙ cos(nπt/L) + bₙ sin(nπt/L))` converges to
`(f(t+) + f(t-))/2`. -/
@[kb "lebldiffyqs2026" "Theorem 4.3.1, p. 211"]
theorem fourier_series_piecewise_smooth {f : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hper : Function.Periodic f (2 * L)) (hpw : PiecewiseSmoothOn f (-L) L) (t : ℝ) :
    ∃ l₁ l₂, Tendsto f (𝓝[>] t) (𝓝 l₁) ∧ Tendsto f (𝓝[<] t) (𝓝 l₂) ∧
      Tendsto (fun N : ℕ => trigPoly L (fourierA f L) (fourierB f L) N t) atTop (𝓝 ((l₁ + l₂) / 2)) := by
  have hd := dini_everywhere hL hper (fun x hx => hpw.dini_right hx) (fun x hx => hpw.dini_left hx) t
  exact fourier_tendsto_of_diniRL hL hper (hpw.1.intervalIntegrable (by linarith)) hd.1 hd.2

/-- **Theorem 4.3.1 at points of continuity (DE-129).** If moreover `f` is continuous at `t`, the Fourier
series converges to `f(t)`. -/
@[kb "lebldiffyqs2026" "Theorem 4.3.1, p. 211"]
theorem fourier_series_piecewise_smooth_continuousAt {f : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hper : Function.Periodic f (2 * L)) (hpw : PiecewiseSmoothOn f (-L) L) {t : ℝ}
    (hc : ContinuousAt f t) :
    Tendsto (fun N : ℕ => trigPoly L (fourierA f L) (fourierB f L) N t) atTop (𝓝 (f t)) := by
  obtain ⟨l₁, l₂, h₁, h₂, h⟩ := fourier_series_piecewise_smooth hL hper hpw t
  have e₁ : l₁ = f t := tendsto_nhds_unique h₁ (hc.tendsto.mono_left nhdsWithin_le_nhds)
  have e₂ : l₂ = f t := tendsto_nhds_unique h₂ (hc.tendsto.mono_left nhdsWithin_le_nhds)
  rw [e₁, e₂, add_self_div_two] at h
  exact h

/-! ## Sine and cosine series (DE-134, Theorem 4.4.1) -/

/-- Sine series coefficient `bₙ = (2/L) ∫₀ᴸ f(t) sin(nπt/L) dt`. -/
noncomputable def sineCoef (f : ℝ → ℝ) (L : ℝ) (n : ℕ) : ℝ := (2 / L) * ∫ t in (0 : ℝ)..L, f t * sin (n * π / L * t)

/-- Cosine series coefficient `aₙ = (2/L) ∫₀ᴸ f(t) cos(nπt/L) dt`. -/
noncomputable def cosineCoef (f : ℝ → ℝ) (L : ℝ) (n : ℕ) : ℝ := (2 / L) * ∫ t in (0 : ℝ)..L, f t * cos (n * π / L * t)

section Odd

variable {f : ℝ → ℝ} {L : ℝ} (hL : 0 < L)

include hL in
lemma oddPeriodicExt_eq_oddExt {t : ℝ} (ht : t ∈ Ioo (-L) L) : oddPeriodicExt hL f t = oddExt f t := by
  unfold oddPeriodicExt
  exact periodicExt_eq _ _ _ ⟨ht.1.le, by linarith [ht.2]⟩

include hL in
lemma oddPeriodicExt_diniRight (hf : PiecewiseSmoothOn f 0 L) :
    ∀ x ∈ Ico (-L) L, DiniRight (oddPeriodicExt hL f) x := by
  obtain ⟨-, hodd, heq⟩ := oddPeriodicExt_spec hL f
  intro x hx
  by_cases h0 : 0 ≤ x
  · exact diniRight_of_eqOn (ε := L - x) (by linarith [hx.2])
      (fun y hy => heq y ⟨by linarith [hy.1], by linarith [hy.2]⟩) (hf.dini_right ⟨h0, hx.2⟩)
  · rw [not_le] at h0
    obtain ⟨l, C, δ, hδ, hb⟩ := hf.dini_left (x := -x) ⟨by linarith, by linarith [hx.1]⟩
    refine ⟨-l, C, min δ (-x), lt_min hδ (by linarith), fun s hs => ?_⟩
    have hs2 : s < -x := lt_of_lt_of_le hs.2 (min_le_right _ _)
    have hmem : -x - s ∈ Ioo 0 L := ⟨by linarith, by linarith [hx.1, hs.1]⟩
    have e : oddPeriodicExt hL f (x + s) = - f (-x - s) := by
      have := hodd (-x - s) ⟨by linarith [hmem.1, hx.1], hmem.2⟩
      rw [show -(-x - s) = x + s by ring, heq _ hmem] at this
      exact this
    rw [e, show -f (-x - s) - -l = -(f (-x - s) - l) by ring, abs_neg]
    exact hb s ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_left _ _)⟩

include hL in
lemma oddPeriodicExt_diniLeft (hf : PiecewiseSmoothOn f 0 L) :
    ∀ x ∈ Ioc (-L) L, DiniLeft (oddPeriodicExt hL f) x := by
  obtain ⟨-, hodd, heq⟩ := oddPeriodicExt_spec hL f
  intro x hx
  by_cases h0 : 0 < x
  · exact diniLeft_of_eqOn (ε := x) h0
      (fun y hy => heq y ⟨by linarith [hy.1], by linarith [hy.2, hx.2]⟩) (hf.dini_left ⟨h0, hx.2⟩)
  · rw [not_lt] at h0
    obtain ⟨l, C, δ, hδ, hb⟩ := hf.dini_right (x := -x) ⟨by linarith, by linarith [hx.1]⟩
    refine ⟨-l, C, min δ (L + x), lt_min hδ (by linarith [hx.1]), fun s hs => ?_⟩
    have hs2 : s < L + x := lt_of_lt_of_le hs.2 (min_le_right _ _)
    have hmem : -x + s ∈ Ioo 0 L := ⟨by linarith [hs.1], by linarith⟩
    have e : oddPeriodicExt hL f (x - s) = - f (-x + s) := by
      have := hodd (-x + s) ⟨by linarith [hmem.1], hmem.2⟩
      rw [show -(-x + s) = x - s by ring, heq _ hmem] at this
      exact this
    rw [e, show -f (-x + s) - -l = -(f (-x + s) - l) by ring, abs_neg]
    exact hb s ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_left _ _)⟩

include hL in
lemma oddPeriodicExt_intervalIntegrable (hf : PiecewiseSmoothOn f 0 L) :
    IntervalIntegrable (oddPeriodicExt hL f) volume (-L) L := by
  obtain ⟨-, hodd, heq⟩ := oddPeriodicExt_spec hL f
  have hfi : IntervalIntegrable f volume 0 L := hf.1.intervalIntegrable hL.le
  have h2 : IntervalIntegrable (oddPeriodicExt hL f) volume 0 L := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hL.le] at hfi ⊢
    exact hfi.congr_fun (fun y hy => (heq y hy).symm) measurableSet_Ioo
  have hg : IntervalIntegrable (fun t => -f (-t)) volume (-L) 0 := by
    have h := (hfi.comp_sub_left 0).symm
    simp only [zero_sub, sub_zero] at h
    exact h.neg
  have h1 : IntervalIntegrable (oddPeriodicExt hL f) volume (-L) 0 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)] at hg ⊢
    refine hg.congr_fun (fun y hy => ?_) measurableSet_Ioo
    have := hodd (-y) ⟨by linarith [hy.2], by linarith [hy.1]⟩
    rw [neg_neg, heq (-y) ⟨by linarith [hy.2], by linarith [hy.1]⟩] at this
    simp only
    linarith
  exact h1.trans h2

include hL in
lemma trigPoly_oddPeriodicExt (hf : PiecewiseSmoothOn f 0 L) (N : ℕ) (x : ℝ) :
    trigPoly L (fourierA (oddPeriodicExt hL f) L) (fourierB (oddPeriodicExt hL f) L) N x =
      ∑ k ∈ Finset.Icc 1 N, sineCoef f L k * sin (k * π / L * x) := by
  have hfi : IntervalIntegrable f volume 0 L := hf.1.intervalIntegrable hL.le
  have hA : ∀ n : ℕ, fourierA (oddPeriodicExt hL f) L n = 0 := fun n => by
    rw [← fourierA_oddExt f L n]
    unfold fourierA
    congr 1
    exact intervalIntegral.integral_congr_Ioo_of_le (by linarith)
      (fun t ht => by simp only [oddPeriodicExt_eq_oddExt hL ht])
  have hB : ∀ n : ℕ, fourierB (oddPeriodicExt hL f) L n = sineCoef f L n := fun n => by
    rw [sineCoef, ← fourierB_oddExt hL hfi n]
    unfold fourierB
    congr 1
    exact intervalIntegral.integral_congr_Ioo_of_le (by linarith)
      (fun t ht => by simp only [oddPeriodicExt_eq_oddExt hL ht])
  simp [trigPoly, hA, hB]

include hL in
/-- **Sine series (DE-134, Theorem 4.4.1).** Let `f` be piecewise smooth on `[0, L]` and `F` its `2L`-periodic odd
extension. At every `t` the sine series `∑ bₙ sin(nπt/L)`, `bₙ = (2/L)∫₀ᴸ f(s) sin(nπs/L) ds`, converges to the
average `(F(t+) + F(t-))/2` of the one-sided limits of `F` (which exist). -/
@[kb "lebldiffyqs2026" "Theorem 4.4.1, p. 220"]
theorem sine_series_tendsto (hf : PiecewiseSmoothOn f 0 L) (t : ℝ) :
    ∃ l₁ l₂, Tendsto (oddPeriodicExt hL f) (𝓝[>] t) (𝓝 l₁) ∧ Tendsto (oddPeriodicExt hL f) (𝓝[<] t) (𝓝 l₂) ∧
      Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N, sineCoef f L k * sin (k * π / L * t)) atTop
        (𝓝 ((l₁ + l₂) / 2)) := by
  have hper := (oddPeriodicExt_spec hL f).1
  have hd := dini_everywhere hL hper (oddPeriodicExt_diniRight hL hf) (oddPeriodicExt_diniLeft hL hf) t
  obtain ⟨l₁, l₂, h₁, h₂, h⟩ :=
    fourier_tendsto_of_diniRL hL hper (oddPeriodicExt_intervalIntegrable hL hf) hd.1 hd.2
  refine ⟨l₁, l₂, h₁, h₂, h.congr fun N => ?_⟩
  exact trigPoly_oddPeriodicExt hL hf N t

include hL in
/-- **Sine series inside the interval (DE-134).** If `0 < t < L` and `f` is continuous at `t`, the sine series of
`f` converges to `f(t)`. -/
@[kb "lebldiffyqs2026" "Theorem 4.4.1, p. 220"]
theorem sine_series_tendsto_of_continuousAt (hf : PiecewiseSmoothOn f 0 L) {t : ℝ} (ht : t ∈ Ioo 0 L)
    (hc : ContinuousAt f t) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N, sineCoef f L k * sin (k * π / L * t)) atTop (𝓝 (f t)) := by
  obtain ⟨l₁, l₂, h₁, h₂, h⟩ := sine_series_tendsto hL hf t
  have hev : oddPeriodicExt hL f =ᶠ[𝓝 t] f :=
    Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2) fun y hy => (oddPeriodicExt_spec hL f).2.2 y hy
  have hc' : ContinuousAt (oddPeriodicExt hL f) t := hc.congr hev.symm
  have hFt : oddPeriodicExt hL f t = f t := (oddPeriodicExt_spec hL f).2.2 t ht
  have e₁ : l₁ = f t := hFt ▸ tendsto_nhds_unique h₁ (hc'.tendsto.mono_left nhdsWithin_le_nhds)
  have e₂ : l₂ = f t := hFt ▸ tendsto_nhds_unique h₂ (hc'.tendsto.mono_left nhdsWithin_le_nhds)
  rw [e₁, e₂, add_self_div_two] at h
  exact h

end Odd

section Even

variable {f : ℝ → ℝ} {L : ℝ} (hL : 0 < L)

include hL in
lemma evenPeriodicExt_eq_evenExt {t : ℝ} (ht : t ∈ Ioo (-L) L) : evenPeriodicExt hL f t = evenExt f t := by
  unfold evenPeriodicExt
  exact periodicExt_eq _ _ _ ⟨ht.1.le, by linarith [ht.2]⟩

include hL in
lemma evenPeriodicExt_diniRight (hf : PiecewiseSmoothOn f 0 L) :
    ∀ x ∈ Ico (-L) L, DiniRight (evenPeriodicExt hL f) x := by
  obtain ⟨-, heven, heq⟩ := evenPeriodicExt_spec hL f
  intro x hx
  by_cases h0 : 0 ≤ x
  · exact diniRight_of_eqOn (ε := L - x) (by linarith [hx.2])
      (fun y hy => heq y ⟨by linarith [hy.1], by linarith [hy.2]⟩) (hf.dini_right ⟨h0, hx.2⟩)
  · rw [not_le] at h0
    obtain ⟨l, C, δ, hδ, hb⟩ := hf.dini_left (x := -x) ⟨by linarith, by linarith [hx.1]⟩
    refine ⟨l, C, min δ (-x), lt_min hδ (by linarith), fun s hs => ?_⟩
    have hs2 : s < -x := lt_of_lt_of_le hs.2 (min_le_right _ _)
    have hmem : -x - s ∈ Ioo 0 L := ⟨by linarith, by linarith [hx.1, hs.1]⟩
    have e : evenPeriodicExt hL f (x + s) = f (-x - s) := by
      have := heven (-x - s) ⟨by linarith [hmem.1, hx.1], hmem.2⟩
      rw [show -(-x - s) = x + s by ring, heq _ ⟨hmem.1.le, hmem.2⟩] at this
      exact this
    rw [e]
    exact hb s ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_left _ _)⟩

include hL in
lemma evenPeriodicExt_diniLeft (hf : PiecewiseSmoothOn f 0 L) :
    ∀ x ∈ Ioc (-L) L, DiniLeft (evenPeriodicExt hL f) x := by
  obtain ⟨-, heven, heq⟩ := evenPeriodicExt_spec hL f
  intro x hx
  by_cases h0 : 0 < x
  · exact diniLeft_of_eqOn (ε := x) h0
      (fun y hy => heq y ⟨by linarith [hy.1], by linarith [hy.2, hx.2]⟩) (hf.dini_left ⟨h0, hx.2⟩)
  · rw [not_lt] at h0
    obtain ⟨l, C, δ, hδ, hb⟩ := hf.dini_right (x := -x) ⟨by linarith, by linarith [hx.1]⟩
    refine ⟨l, C, min δ (L + x), lt_min hδ (by linarith [hx.1]), fun s hs => ?_⟩
    have hs2 : s < L + x := lt_of_lt_of_le hs.2 (min_le_right _ _)
    have hmem : -x + s ∈ Ioo 0 L := ⟨by linarith [hs.1], by linarith⟩
    have e : evenPeriodicExt hL f (x - s) = f (-x + s) := by
      have := heven (-x + s) ⟨by linarith [hmem.1], hmem.2⟩
      rw [show -(-x + s) = x - s by ring, heq _ ⟨hmem.1.le, hmem.2⟩] at this
      exact this
    rw [e]
    exact hb s ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_left _ _)⟩

include hL in
lemma evenPeriodicExt_intervalIntegrable (hf : PiecewiseSmoothOn f 0 L) :
    IntervalIntegrable (evenPeriodicExt hL f) volume (-L) L := by
  obtain ⟨-, heven, heq⟩ := evenPeriodicExt_spec hL f
  have hfi : IntervalIntegrable f volume 0 L := hf.1.intervalIntegrable hL.le
  have h2 : IntervalIntegrable (evenPeriodicExt hL f) volume 0 L := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hL.le] at hfi ⊢
    exact hfi.congr_fun (fun y hy => (heq y ⟨hy.1.le, hy.2⟩).symm) measurableSet_Ioo
  have hg : IntervalIntegrable (fun t => f (-t)) volume (-L) 0 := by
    have := (hfi.comp_sub_left 0).symm
    simpa using this
  have h1 : IntervalIntegrable (evenPeriodicExt hL f) volume (-L) 0 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)] at hg ⊢
    refine hg.congr_fun (fun y hy => ?_) measurableSet_Ioo
    have := heven (-y) ⟨by linarith [hy.2], by linarith [hy.1]⟩
    rw [neg_neg, heq (-y) ⟨by linarith [hy.2], by linarith [hy.1]⟩] at this
    exact this.symm
  exact h1.trans h2

include hL in
lemma trigPoly_evenPeriodicExt (hf : PiecewiseSmoothOn f 0 L) (N : ℕ) (x : ℝ) :
    trigPoly L (fourierA (evenPeriodicExt hL f) L) (fourierB (evenPeriodicExt hL f) L) N x =
      cosineCoef f L 0 / 2 + ∑ k ∈ Finset.Icc 1 N, cosineCoef f L k * cos (k * π / L * x) := by
  have hfi : IntervalIntegrable f volume 0 L := hf.1.intervalIntegrable hL.le
  have hB : ∀ n : ℕ, fourierB (evenPeriodicExt hL f) L n = 0 := fun n => by
    rw [← fourierB_evenExt f L n]
    unfold fourierB
    congr 1
    exact intervalIntegral.integral_congr_Ioo_of_le (by linarith)
      (fun t ht => by simp only [evenPeriodicExt_eq_evenExt hL ht])
  have hA : ∀ n : ℕ, fourierA (evenPeriodicExt hL f) L n = cosineCoef f L n := fun n => by
    rw [cosineCoef, ← fourierA_evenExt hL hfi n]
    unfold fourierA
    congr 1
    exact intervalIntegral.integral_congr_Ioo_of_le (by linarith)
      (fun t ht => by simp only [evenPeriodicExt_eq_evenExt hL ht])
  simp [trigPoly, hA, hB]

include hL in
/-- **Cosine series (DE-134, Theorem 4.4.1).** Let `f` be piecewise smooth on `[0, L]` and `F` its `2L`-periodic
even extension. At every `t` the cosine series `a₀/2 + ∑ aₙ cos(nπt/L)`, `aₙ = (2/L)∫₀ᴸ f(s) cos(nπs/L) ds`,
converges to `(F(t+) + F(t-))/2`. -/
@[kb "lebldiffyqs2026" "Theorem 4.4.1, p. 220"]
theorem cosine_series_tendsto (hf : PiecewiseSmoothOn f 0 L) (t : ℝ) :
    ∃ l₁ l₂, Tendsto (evenPeriodicExt hL f) (𝓝[>] t) (𝓝 l₁) ∧ Tendsto (evenPeriodicExt hL f) (𝓝[<] t) (𝓝 l₂) ∧
      Tendsto (fun N : ℕ => cosineCoef f L 0 / 2 + ∑ k ∈ Finset.Icc 1 N, cosineCoef f L k * cos (k * π / L * t))
        atTop (𝓝 ((l₁ + l₂) / 2)) := by
  have hper := (evenPeriodicExt_spec hL f).1
  have hd := dini_everywhere hL hper (evenPeriodicExt_diniRight hL hf) (evenPeriodicExt_diniLeft hL hf) t
  obtain ⟨l₁, l₂, h₁, h₂, h⟩ :=
    fourier_tendsto_of_diniRL hL hper (evenPeriodicExt_intervalIntegrable hL hf) hd.1 hd.2
  refine ⟨l₁, l₂, h₁, h₂, h.congr fun N => ?_⟩
  exact trigPoly_evenPeriodicExt hL hf N t

include hL in
/-- **Cosine series inside the interval (DE-134).** If `0 < t < L` and `f` is continuous at `t`, the cosine series
of `f` converges to `f(t)`. -/
@[kb "lebldiffyqs2026" "Theorem 4.4.1, p. 220"]
theorem cosine_series_tendsto_of_continuousAt (hf : PiecewiseSmoothOn f 0 L) {t : ℝ} (ht : t ∈ Ioo 0 L)
    (hc : ContinuousAt f t) :
    Tendsto (fun N : ℕ => cosineCoef f L 0 / 2 + ∑ k ∈ Finset.Icc 1 N, cosineCoef f L k * cos (k * π / L * t))
      atTop (𝓝 (f t)) := by
  obtain ⟨l₁, l₂, h₁, h₂, h⟩ := cosine_series_tendsto hL hf t
  have hev : evenPeriodicExt hL f =ᶠ[𝓝 t] f :=
    Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2) fun y hy =>
      (evenPeriodicExt_spec hL f).2.2 y ⟨hy.1.le, hy.2⟩
  have hc' : ContinuousAt (evenPeriodicExt hL f) t := hc.congr hev.symm
  have hFt : evenPeriodicExt hL f t = f t := (evenPeriodicExt_spec hL f).2.2 t ⟨ht.1.le, ht.2⟩
  have e₁ : l₁ = f t := hFt ▸ tendsto_nhds_unique h₁ (hc'.tendsto.mono_left nhdsWithin_le_nhds)
  have e₂ : l₂ = f t := hFt ▸ tendsto_nhds_unique h₂ (hc'.tendsto.mono_left nhdsWithin_le_nhds)
  rw [e₁, e₂, add_self_div_two] at h
  exact h

end Even

end UndergradKB.DifferentialEquations
