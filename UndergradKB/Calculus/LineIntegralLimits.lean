import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import UndergradKB.Common.Attr

/-! Scalar line integrals along a `C¹` curve: existence of the integral and convergence of the
arc-length Riemann sums (OpenStax Calculus Volume 3, §6.2).

The curve is `r : ℝ → E` into a normed space `E` (for the plane, `E = EuclideanSpace ℝ (Fin 2)`),
`C¹` on all of `ℝ` (it is only used on `[a, b]`), and `f : E → ℝ` is continuous. -/

namespace UndergradKB.Calculus.LineIntegralLimits

open Set Filter Topology MeasureTheory intervalIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- OpenStax Calculus 3:§6.2 (CA-611). For a continuous `f` and a `C¹` curve `r`, the integrand
`t ↦ f(r t) ‖r'(t)‖` of the scalar line integral is interval integrable, so the line integral
`∫ₐᵇ f(r t) ‖r'(t)‖ dt` exists. -/
@[kb "openstaxcalculus2016" "3:§6.2 text after Definition, p. 602"]
theorem lineIntegrand_intervalIntegrable {r : ℝ → E} (hr : ContDiff ℝ 1 r) {f : E → ℝ}
    (hf : Continuous f) (a b : ℝ) :
    IntervalIntegrable (fun t => f (r t) * ‖deriv r t‖) volume a b := by
  have : Continuous fun t => f (r t) * ‖deriv r t‖ :=
    (hf.comp hr.continuous).mul (continuous_norm.comp hr.continuous_deriv_one)
  exact this.intervalIntegrable a b

/-- One piece of the Riemann sum: on `[u, v]` the term `f(r u) ‖r v - r u‖` differs from
`∫ᵤᵛ f(r s) ‖r' s‖ ds` by at most `(ε₂ + M ε₁)(v - u)`. -/
lemma line_piece {r : ℝ → E} (hr : ContDiff ℝ 1 r) {f : E → ℝ} (hf : Continuous f) {u v : ℝ}
    (huv : u ≤ v) {ε₁ ε₂ M : ℝ}
    (h1 : ∀ s ∈ Icc u v, ‖deriv r s - deriv r u‖ ≤ ε₁)
    (h2 : ∀ s ∈ Icc u v,
      |f (r s) * ‖deriv r s‖ - f (r u) * ‖deriv r u‖| ≤ ε₂)
    (hM : |f (r u)| ≤ M) :
    |f (r u) * ‖r v - r u‖ - ∫ s in u..v, f (r s) * ‖deriv r s‖| ≤ (ε₂ + M * ε₁) * (v - u) := by
  have hε₁ : 0 ≤ ε₁ := (norm_nonneg _).trans (h1 u ⟨le_rfl, huv⟩)
  have hε₂ : 0 ≤ ε₂ := (abs_nonneg _).trans (h2 u ⟨le_rfl, huv⟩)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hM
  have hd : ∀ s, HasDerivAt (fun s => r s - s • deriv r u) (deriv r s - deriv r u) s := by
    intro s
    have := ((hr.differentiable one_ne_zero) s).hasDerivAt.sub
      ((hasDerivAt_id s).smul_const (deriv r u))
    exact this.congr_deriv (by simp)
  have hmv : ‖(r v - v • deriv r u) - (r u - u • deriv r u)‖ ≤ ε₁ * ‖v - u‖ := by
    refine Convex.norm_image_sub_le_of_norm_deriv_le (f := fun s => r s - s • deriv r u)
      (s := Icc u v) (fun s _ => (hd s).differentiableAt) (fun s hs => ?_) (convex_Icc u v)
      ⟨le_rfl, huv⟩ ⟨huv, le_rfl⟩
    rw [(hd s).deriv]; exact h1 s hs
  have hA : |‖r v - r u‖ - (v - u) * ‖deriv r u‖| ≤ ε₁ * (v - u) := by
    have e : (r v - v • deriv r u) - (r u - u • deriv r u) = (r v - r u) - (v - u) • deriv r u := by
      rw [sub_smul]; abel
    rw [e, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ v - u)] at hmv
    have := abs_norm_sub_norm_le (r v - r u) ((v - u) • deriv r u)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ v - u)] at this
    linarith
  have hint : IntervalIntegrable (fun s => f (r s) * ‖deriv r s‖) volume u v :=
    lineIntegrand_intervalIntegrable hr hf u v
  have hB : |(∫ s in u..v, f (r s) * ‖deriv r s‖) - (v - u) * (f (r u) * ‖deriv r u‖)| ≤
      ε₂ * (v - u) := by
    have e : (∫ s in u..v, f (r s) * ‖deriv r s‖) - (v - u) * (f (r u) * ‖deriv r u‖)
        = ∫ s in u..v, (f (r s) * ‖deriv r s‖ - f (r u) * ‖deriv r u‖) := by
      rw [intervalIntegral.integral_sub hint intervalIntegrable_const]
      simp
      ring
    rw [e]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := u) (b := v)
      (f := fun s => f (r s) * ‖deriv r s‖ - f (r u) * ‖deriv r u‖) (C := ε₂) (fun s hs => by
        rw [Real.norm_eq_abs]
        rw [Set.uIoc_of_le huv] at hs
        exact h2 s ⟨hs.1.le, hs.2⟩)
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ v - u)] at this
    exact this
  have key : f (r u) * ‖r v - r u‖ - ∫ s in u..v, f (r s) * ‖deriv r s‖
      = f (r u) * (‖r v - r u‖ - (v - u) * ‖deriv r u‖)
        - ((∫ s in u..v, f (r s) * ‖deriv r s‖) - (v - u) * (f (r u) * ‖deriv r u‖)) := by ring
  rw [key]
  calc _ ≤ |f (r u) * (‖r v - r u‖ - (v - u) * ‖deriv r u‖)|
        + |(∫ s in u..v, f (r s) * ‖deriv r s‖) - (v - u) * (f (r u) * ‖deriv r u‖)| :=
          abs_sub _ _
    _ ≤ M * (ε₁ * (v - u)) + ε₂ * (v - u) := by
          rw [abs_mul]
          exact add_le_add (mul_le_mul hM hA (abs_nonneg _) hM0) hB
    _ = (ε₂ + M * ε₁) * (v - u) := by ring

/-- OpenStax Calculus 3:§6.2 Equation 6.5 (CA-610). For a `C¹` curve `r` and continuous `f`, the
arc-length Riemann sums `∑ f(r(tᵢ)) ‖r(tᵢ₊₁) - r(tᵢ)‖` over the regular partition
`tᵢ = a + i (b-a)/n` of `[a, b]` converge, as `n → ∞`, to the line integral
`∫ₐᵇ f(r t) ‖r'(t)‖ dt`. -/
@[kb "openstaxcalculus2016" "3:Equation 6.5, p. 602"]
theorem line_integral_riemann_sums {r : ℝ → E} (hr : ContDiff ℝ 1 r) {f : E → ℝ}
    (hf : Continuous f) {a b : ℝ} (hab : a ≤ b) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n,
        f (r (a + i * (b - a) / n)) * ‖r (a + (i + 1) * (b - a) / n) - r (a + i * (b - a) / n)‖)
      atTop (𝓝 (∫ t in a..b, f (r t) * ‖deriv r t‖)) := by
  have hr' : Continuous (deriv r) := hr.continuous_deriv_one
  have hg : Continuous fun t => f (r t) * ‖deriv r t‖ :=
    (hf.comp hr.continuous).mul (continuous_norm.comp hr')
  have hK : IsCompact (Icc a b) := isCompact_Icc
  obtain ⟨M', hM'⟩ := hK.exists_bound_of_continuousOn (hf.comp hr.continuous).continuousOn
  set M : ℝ := max M' 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hM : ∀ t ∈ Icc a b, |f (r t)| ≤ M := by
    intro t ht
    have := hM' t ht
    simp only [Function.comp, Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  have ucr := hK.uniformContinuousOn_of_continuous hr'.continuousOn
  have ucg := hK.uniformContinuousOn_of_continuous hg.continuousOn
  rw [Metric.uniformContinuousOn_iff] at ucr ucg
  rw [Metric.tendsto_atTop]
  intro ε hε
  set L : ℝ := b - a + 1 with hL
  have hL0 : 0 < L := by linarith
  have hε2 : 0 < ε / (2 * L) := by positivity
  have hε1 : 0 < ε / (2 * L * (M + 1)) := by positivity
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := ucr _ hε1
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := ucg _ hε2
  set δ : ℝ := min δ₁ δ₂ with hδ
  have hδ0 : 0 < δ := lt_min hδ₁ hδ₂
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / δ)
  refine ⟨N + 1, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast (le_trans (Nat.le_add_left 1 N) hn)
    linarith
  set h : ℝ := (b - a) / n with hh
  have hh0 : 0 ≤ h := by positivity
  have hhδ : h < δ := by
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast (le_trans (Nat.le_succ N) hn)
    rw [hh, div_lt_iff₀ hn0]
    rw [div_lt_iff₀ hδ0] at hN
    nlinarith
  set t : ℕ → ℝ := fun i => a + i * (b - a) / n with ht
  have ht' : ∀ i : ℕ, t (i + 1) = t i + h := by
    intro i; simp only [ht, hh]; push_cast; ring
  have ht0 : t 0 = a := by simp [ht]
  have htn : t n = b := by simp only [ht]; field_simp; ring
  have hmono : ∀ i, i ≤ n → t i ∈ Icc a b := by
    intro i hi
    have hi' : (i : ℝ) ≤ n := by exact_mod_cast hi
    have : (i : ℝ) * (b - a) / n ≤ b - a := by
      rw [div_le_iff₀ hn0]; nlinarith
    constructor
    · simp only [ht]; have : 0 ≤ (i : ℝ) * (b - a) / n := by positivity
      linarith
    · simp only [ht]; linarith
  have hsum : ∑ i ∈ Finset.range n, ∫ s in t i..t (i + 1), f (r s) * ‖deriv r s‖
      = ∫ s in a..b, f (r s) * ‖deriv r s‖ := by
    rw [intervalIntegral.sum_integral_adjacent_intervals (a := t) (n := n)
      (fun k _ => lineIntegrand_intervalIntegrable hr hf _ _), ht0, htn]
  have e1 : ∀ i : ℕ, a + ((i : ℝ) + 1) * (b - a) / n = t (i + 1) := by
    intro i; simp only [ht]; push_cast; ring
  have e0 : ∀ i : ℕ, a + (i : ℝ) * (b - a) / n = t i := fun i => rfl
  simp only [e1, e0]
  rw [Real.dist_eq, ← hsum, ← Finset.sum_sub_distrib]
  have hpiece : ∀ i ∈ Finset.range n,
      |f (r (t i)) * ‖r (t (i + 1)) - r (t i)‖ - ∫ s in t i..t (i + 1), f (r s) * ‖deriv r s‖|
        ≤ (ε / (2 * L) + M * (ε / (2 * L * (M + 1)))) * h := by
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    have hti : t i ∈ Icc a b := hmono i hi'.le
    have hti1 : t (i + 1) ∈ Icc a b := hmono (i + 1) hi'
    have hle : t i ≤ t (i + 1) := by rw [ht' i]; linarith
    have := line_piece hr hf hle (ε₁ := ε / (2 * L * (M + 1))) (ε₂ := ε / (2 * L)) (M := M)
      (fun s hs => by
        have hsI : s ∈ Icc a b := ⟨hti.1.trans hs.1, hs.2.trans hti1.2⟩
        have := hδ₁' s hsI (t i) hti (by
          rw [Real.dist_eq, abs_of_nonneg (by linarith [hs.1])]
          have : s - t i ≤ h := by linarith [hs.2, ht' i]
          exact lt_of_le_of_lt this (lt_of_lt_of_le hhδ (min_le_left _ _)))
        rw [dist_eq_norm] at this
        exact this.le)
      (fun s hs => by
        have hsI : s ∈ Icc a b := ⟨hti.1.trans hs.1, hs.2.trans hti1.2⟩
        have := hδ₂' s hsI (t i) hti (by
          rw [Real.dist_eq, abs_of_nonneg (by linarith [hs.1])]
          have : s - t i ≤ h := by linarith [hs.2, ht' i]
          exact lt_of_le_of_lt this (lt_of_lt_of_le hhδ (min_le_right _ _)))
        rw [Real.dist_eq] at this
        exact this.le)
      (hM _ hti)
    have e : t (i + 1) - t i = h := by rw [ht' i]; ring
    rw [e] at this
    exact this
  calc |∑ i ∈ Finset.range n, (f (r (t i)) * ‖r (t (i + 1)) - r (t i)‖ -
          ∫ s in t i..t (i + 1), f (r s) * ‖deriv r s‖)|
      ≤ ∑ i ∈ Finset.range n, |f (r (t i)) * ‖r (t (i + 1)) - r (t i)‖ -
          ∫ s in t i..t (i + 1), f (r s) * ‖deriv r s‖| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range n, (ε / (2 * L) + M * (ε / (2 * L * (M + 1)))) * h :=
        Finset.sum_le_sum hpiece
    _ = (ε / (2 * L) + M * (ε / (2 * L * (M + 1)))) * (b - a) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hh]
        field_simp
    _ < ε := by
        have e1 : M * (ε / (2 * L * (M + 1))) ≤ ε / (2 * L) := by
          rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [mul_pos hε hL0]
        have e2 : (ε / (2 * L) + M * (ε / (2 * L * (M + 1)))) ≤ ε / L := by
          have : ε / (2 * L) + ε / (2 * L) = ε / L := by field_simp; ring
          linarith
        calc _ ≤ ε / L * (b - a) := mul_le_mul_of_nonneg_right e2 (by linarith)
          _ < ε := by
            rw [div_mul_eq_mul_div, div_lt_iff₀ hL0]
            nlinarith

/-- Components version of CA-610: for a plane curve `t ↦ (x t, y t)` with `x, y` of class `C¹`, the
Riemann sums with chord lengths `√((x tᵢ₊₁ - x tᵢ)² + (y tᵢ₊₁ - y tᵢ)²)` tend to
`∫ₐᵇ f(x t, y t) √(x'(t)² + y'(t)²) dt`. -/
@[kb "openstaxcalculus2016" "3:Equation 6.5, p. 602"]
theorem line_integral_riemann_sums_plane {x y : ℝ → ℝ} (hx : ContDiff ℝ 1 x)
    (hy : ContDiff ℝ 1 y) {f : ℝ × ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n,
        f (x (a + i * (b - a) / n), y (a + i * (b - a) / n)) *
          √((x (a + (i + 1) * (b - a) / n) - x (a + i * (b - a) / n)) ^ 2 +
            (y (a + (i + 1) * (b - a) / n) - y (a + i * (b - a) / n)) ^ 2))
      atTop (𝓝 (∫ t in a..b, f (x t, y t) * √(deriv x t ^ 2 + deriv y t ^ 2))) := by
  let e := (EuclideanSpace.equiv (Fin 2) ℝ).symm
  let r : ℝ → EuclideanSpace ℝ (Fin 2) := fun t => e ![x t, y t]
  have hpi : ContDiff ℝ 1 (fun t => ![x t, y t]) := by
    rw [contDiff_pi]
    intro i; fin_cases i <;> simpa
  have hr : ContDiff ℝ 1 r := e.contDiff.comp hpi
  have hnorm : ∀ p q : ℝ, ‖e ![p, q]‖ = √(p ^ 2 + q ^ 2) := by
    intro p q
    simp [e, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have hder : ∀ t, deriv r t = e ![deriv x t, deriv y t] := by
    intro t
    have h1 : HasDerivAt (fun t => ![x t, y t]) ![deriv x t, deriv y t] t := by
      rw [hasDerivAt_pi]
      intro i; fin_cases i
      · exact ((hx.differentiable one_ne_zero) t).hasDerivAt
      · exact ((hy.differentiable one_ne_zero) t).hasDerivAt
    exact (e.hasFDerivAt.comp_hasDerivAt t h1).deriv
  have key1 : ∀ p q p' q' : ℝ,
      ‖e ![p, q] - e ![p', q']‖ = √((p - p') ^ 2 + (q - q') ^ 2) := by
    intro p q p' q'
    rw [← map_sub]
    have : (![p, q] - ![p', q'] : Fin 2 → ℝ) = ![p - p', q - q'] := by
      ext i; fin_cases i <;> simp
    rw [this]; exact hnorm _ _
  have := line_integral_riemann_sums hr (f := fun p => f (p 0, p 1)) (by fun_prop) hab
  convert this using 2
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [r]
    rw [key1]
    simp [e]
  · refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [r, hder, hnorm]
    simp [e]

end UndergradKB.Calculus.LineIntegralLimits
