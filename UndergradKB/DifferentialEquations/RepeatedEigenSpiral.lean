import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import UndergradKB.Common.Attr
import UndergradKB.DifferentialEquations.Nonlinear

/-! # A repeated eigenvalue need not give a node (Lebl, *Notes on Diffy Qs*, Table 8.1)

Table 8.1 lists every almost linear critical point whose Jacobian has two negative real eigenvalues as a sink (stable
node).  For a *repeated* eigenvalue this is not right in general: the almost linear system
`x' = -x - y / ln r`, `y' = -y + x / ln r` (`r = √(x² + y²)`) has Jacobian `-I` at the origin (the extra terms are
`o(r)` because `1 / ln r → 0`), but in polar coordinates `r' = -r`, `θ' = 1 / ln r`, so `θ(t) = -ln(t + c) → -∞`: every
solution starting near the origin spirals into it, crossing every line through the origin at arbitrarily large times.
(Boyce and DiPrima, Table 9.3.1, list "node or spiral point" for equal eigenvalues.)  The stability column of the
table is right (`AlmostLinear.lean`). -/

namespace UndergradKB.DifferentialEquations

open Real Filter Topology

/-- The field of the example. -/
noncomputable def rsF (u v : ℝ) : ℝ := -u - v / log (√(u ^ 2 + v ^ 2))
/-- The field of the example. -/
noncomputable def rsG (u v : ℝ) : ℝ := -v + u / log (√(u ^ 2 + v ^ 2))

/-- The explicit solutions `r = r₀ e^{-t}`, `θ = -ln(t - ln r₀)`. -/
noncomputable def rsX (r₀ t : ℝ) : ℝ := r₀ * exp (-t) * cos (-log (t - log r₀))
/-- The explicit solutions. -/
noncomputable def rsY (r₀ t : ℝ) : ℝ := r₀ * exp (-t) * sin (-log (t - log r₀))

lemma rs_norm {r₀ t : ℝ} (hr : 0 < r₀) : √(rsX r₀ t ^ 2 + rsY r₀ t ^ 2) = r₀ * exp (-t) := by
  have : rsX r₀ t ^ 2 + rsY r₀ t ^ 2 = (r₀ * exp (-t)) ^ 2 := by
    simp only [rsX, rsY]
    have := sin_sq_add_cos_sq (-log (t - log r₀))
    nlinarith [this]
  rw [this, sqrt_sq (by positivity)]

lemma rs_log {r₀ t : ℝ} (hr : 0 < r₀) : log (√(rsX r₀ t ^ 2 + rsY r₀ t ^ 2)) = -(t - log r₀) := by
  rw [rs_norm hr, log_mul hr.ne' (exp_pos _).ne', log_exp]; ring

/-- The explicit curves solve the system for `t ≥ 0` (when `r₀ < 1`). -/
theorem rs_isPlanarSol {r₀ : ℝ} (hr : 0 < r₀) (hr1 : r₀ < 1) : IsPlanarSol rsF rsG (rsX r₀) (rsY r₀) := by
  intro t ht
  have hc : 0 < t - log r₀ := by have := log_neg hr hr1; linarith
  have hc' : t - log r₀ ≠ 0 := hc.ne'
  have hθ : HasDerivAt (fun t => -log (t - log r₀)) (-(1 / (t - log r₀))) t := by
    have h1 : HasDerivAt (fun t => t - log r₀) 1 t := (hasDerivAt_id t).sub_const _
    refine (h1.log hc').neg.congr_deriv ?_
    field_simp
  have hR : HasDerivAt (fun t => r₀ * exp (-t)) (-(r₀ * exp (-t))) t := by
    have := ((hasDerivAt_neg t).exp).const_mul r₀
    convert this using 1; ring
  have hL := rs_log (t := t) hr
  constructor
  · have := hR.mul (hθ.cos)
    refine this.congr_deriv ?_
    simp only [rsF]
    rw [hL]
    simp only [rsX, rsY]
    field_simp
    ring
  · have := hR.mul (hθ.sin)
    refine this.congr_deriv ?_
    simp only [rsG]
    rw [hL]
    simp only [rsX, rsY]
    field_simp

/-- The system is almost linear at the origin with Jacobian `-I` (a repeated eigenvalue `-1`). -/
theorem rs_almost_linear : ∀ ε > 0, ∃ ρ > 0, ∀ u v, u ^ 2 + v ^ 2 < ρ ^ 2 →
    (rsF (0 + u) (0 + v) - (-1 * u + 0 * v)) ^ 2 + (rsG (0 + u) (0 + v) - (0 * u + -1 * v)) ^ 2
      ≤ ε * (u ^ 2 + v ^ 2) := by
  intro ε hε
  refine ⟨exp (-(1 / √ε)), exp_pos _, fun u v huv => ?_⟩
  simp only [zero_add, rsF, rsG]
  set r := √(u ^ 2 + v ^ 2) with hr
  have hsq : r ^ 2 = u ^ 2 + v ^ 2 := sq_sqrt (by positivity)
  have e : (-u - v / log r - (-1 * u + 0 * v)) ^ 2 + (-v + u / log r - (0 * u + -1 * v)) ^ 2 =
      (u ^ 2 + v ^ 2) * (1 / log r) ^ 2 := by
    rcases eq_or_ne (log r) 0 with h0 | h0
    · simp [h0]
    · field_simp; ring
  rw [e]
  rcases eq_or_lt_of_le (sqrt_nonneg (u ^ 2 + v ^ 2)) with h0 | hpos
  · rw [← hr] at h0
    have : u ^ 2 + v ^ 2 = 0 := by rw [← hsq, ← h0]; ring
    rw [this]; simp
  rw [← hr] at hpos
  have hrρ : r < exp (-(1 / √ε)) := by
    rw [hr]
    calc √(u ^ 2 + v ^ 2) < √((exp (-(1 / √ε))) ^ 2) := sqrt_lt_sqrt (by positivity) huv
      _ = _ := sqrt_sq (exp_pos _).le
  have hlog : log r < -(1 / √ε) := by
    rw [← log_exp (-(1 / √ε))]; exact log_lt_log hpos hrρ
  have hse : 0 < √ε := sqrt_pos.2 hε
  have h1 : 1 / √ε < |log r| := by
    rw [abs_of_neg (by linarith [one_div_pos.2 hse])]; linarith
  have h2 : (1 / log r) ^ 2 ≤ ε := by
    have hneg : log r < 0 := by linarith [one_div_pos.2 hse]
    have hpos2 : 0 < log r ^ 2 := by nlinarith
    rw [div_pow, one_pow, div_le_iff₀ hpos2, ← sq_abs (log r)]
    have h3 : (1 / √ε) ^ 2 = 1 / ε := by rw [div_pow, one_pow, sq_sqrt hε.le]
    have h4 : (1 / √ε) ^ 2 < |log r| ^ 2 := by
      exact pow_lt_pow_left₀ h1 (by positivity) (by norm_num)
    rw [h3] at h4
    rw [div_lt_iff₀ hε] at h4
    linarith
  calc (u ^ 2 + v ^ 2) * (1 / log r) ^ 2 ≤ (u ^ 2 + v ^ 2) * ε := by gcongr
    _ = _ := by ring

/-- The solutions tend to the origin and never reach it. -/
theorem rs_tendsto {r₀ : ℝ} (hr : 0 < r₀) :
    Tendsto (rsX r₀) atTop (𝓝 0) ∧ Tendsto (rsY r₀) atTop (𝓝 0) ∧ ∀ t, ¬(rsX r₀ t = 0 ∧ rsY r₀ t = 0) := by
  have hR : Tendsto (fun t => r₀ * exp (-t)) atTop (𝓝 0) := by
    simpa using (tendsto_exp_neg_atTop_nhds_zero.const_mul r₀)
  refine ⟨?_, ?_, fun t ⟨hx, hy⟩ => ?_⟩
  · refine squeeze_zero_norm (fun t => ?_) hR
    rw [rsX, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc _ ≤ r₀ * exp (-t) * 1 := by gcongr; exact abs_cos_le_one _
      _ = _ := by ring
  · refine squeeze_zero_norm (fun t => ?_) hR
    rw [rsY, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc _ ≤ r₀ * exp (-t) * 1 := by gcongr; exact abs_sin_le_one _
      _ = _ := by ring
  · have := rs_norm (t := t) hr
    rw [hx, hy] at this
    simp at this
    have : 0 < r₀ * exp (-t) := by positivity
    linarith

/-- **Lebl, Table 8.1, repeated eigenvalue: the almost linear system may spiral.**  For `x' = -x - y / ln r`,
`y' = -y + x / ln r`, almost linear at the origin with Jacobian `-I` (eigenvalue `-1` twice, so the table's row "real
and both negative: sink / stable node"), every solution `r₀ e^{-t} (cos θ, sin θ)`, `θ = -ln(t - ln r₀)`, `0 < r₀ < 1`,
tends to the origin and crosses every line through the origin at arbitrarily large times: it is a spiral sink, not a
node. -/
@[kb "lebldiffyqs2026" "Table 8.1, p. 358"]
theorem repeated_eigenvalue_spiral {r₀ : ℝ} (hr : 0 < r₀) {w₁ w₂ : ℝ} (hw : w₁ ≠ 0 ∨ w₂ ≠ 0) :
    ∀ T, ∃ t₁, T ≤ t₁ ∧ ∃ t₂, T ≤ t₂ ∧
      0 < w₁ * (rsY r₀ t₁ - 0) - w₂ * (rsX r₀ t₁ - 0) ∧ w₁ * (rsY r₀ t₂ - 0) - w₂ * (rsX r₀ t₂ - 0) < 0 := by
  set E : ℝ → ℝ := fun s => w₁ * sin s - w₂ * cos s with hE
  have hEπ : ∀ s, E (s + π) = -E s := fun s => by simp [hE, sin_add_pi, cos_add_pi]; ring
  have hE2π : ∀ s (k : ℕ), E (s - k * (2 * π)) = E s := fun s k => by
    simp only [hE]
    rw [sin_sub_nat_mul_two_pi, cos_sub_nat_mul_two_pi]
  -- an angle where `E` is positive
  obtain ⟨s₁, hs₁⟩ : ∃ s, 0 < E s := by
    rcases hw with h | h
    · rcases lt_or_gt_of_ne h with h' | h'
      · exact ⟨π / 2 + π, by rw [hEπ]; simp [hE]; linarith⟩
      · exact ⟨π / 2, by simp [hE]; linarith⟩
    · rcases lt_or_gt_of_ne h with h' | h'
      · exact ⟨0, by simp [hE]; linarith⟩
      · exact ⟨π, by simpa [hE] using h'⟩
  have hs₂ : E (s₁ + π) < 0 := by rw [hEπ]; linarith
  -- times at which the angle `-ln(t - ln r₀)` equals a given value `s`
  have hval : ∀ (s : ℝ) (t : ℝ), t = exp (-s) + log r₀ →
      w₁ * (rsY r₀ t - 0) - w₂ * (rsX r₀ t - 0) = r₀ * exp (-t) * E s := by
    intro s t ht
    have : -log (t - log r₀) = s := by rw [ht, add_sub_cancel_right, log_exp, neg_neg]
    simp only [rsX, rsY, this, hE]; ring
  have hlarge : ∀ (s : ℝ) (T : ℝ), ∃ k : ℕ, T ≤ exp (-(s - k * (2 * π))) + log r₀ := by
    intro s T
    obtain ⟨k, hk⟩ := exists_nat_gt ((log (max 1 (T - log r₀)) + s) / (2 * π))
    refine ⟨k, ?_⟩
    have h2π : 0 < 2 * π := by positivity
    have hk' : log (max 1 (T - log r₀)) + s < k * (2 * π) := by rwa [div_lt_iff₀ h2π] at hk
    have : max 1 (T - log r₀) ≤ exp (-(s - k * (2 * π))) := by
      rw [← exp_log (lt_of_lt_of_le one_pos (le_max_left 1 _))]
      exact exp_le_exp.2 (by linarith)
    linarith [le_max_right 1 (T - log r₀)]
  intro T
  obtain ⟨k₁, hk₁⟩ := hlarge s₁ T
  obtain ⟨k₂, hk₂⟩ := hlarge (s₁ + π) T
  refine ⟨_, hk₁, _, hk₂, ?_, ?_⟩
  · rw [hval _ _ rfl, hE2π]; positivity
  · rw [hval _ _ rfl, hE2π]
    have : 0 < r₀ * exp (-(exp (-(s₁ + π - k₂ * (2 * π))) + log r₀)) := by positivity
    nlinarith

end UndergradKB.DifferentialEquations
