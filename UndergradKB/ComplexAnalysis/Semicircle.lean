import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import UndergradKB.ComplexAnalysis.PiecewisePath
import UndergradKB.ComplexAnalysis.Primitive
import UndergradKB.Common.Attr

/-!
# The semicircle contour and `∫ dx / (x² + 1) = π` (Beck Examples 4.4.7 and 5.3.5)

For `R > 1` the integral of `1 / (z² + 1)` over the counterclockwise semicircle `σ_R` (the segment
`[-R, R]` followed by the upper arc of radius `R` from `R` to `-R`) is `π`, computed with explicit
logarithmic primitives on each piece. Then the arc integral is bounded by `π R / (R² - 1)`, which
tends to `0`, so the improper real integral `∫_ℝ dx / (x² + 1)` equals `π`.
-/

open Set Filter Topology MeasureTheory intervalIntegral Complex
open scoped Real

namespace UndergradKB.ComplexAnalysis

/-- The upper semicircular arc of radius `R`, from `R` (at `t = 0`) to `-R` (at `t = 1`). -/
noncomputable def semicircleArc (R : ℝ) (t : ℝ) : ℂ := R * Complex.exp (π * t * Complex.I)

/-- The counterclockwise semicircle `σ_R`: the segment `[-R, R]` followed by the upper arc. -/
noncomputable def semicirclePath (R : ℝ) : ℝ → ℂ :=
  pathConcat (segPath (-R) R) (semicircleArc R)

section Arc

lemma hasDerivAt_semicircleArc (R t : ℝ) :
    HasDerivAt (semicircleArc R)
      (R * Complex.exp (π * t * Complex.I) * (π * Complex.I)) t := by
  have h1 : HasDerivAt (fun t : ℝ => (π : ℂ) * (t : ℂ) * Complex.I) ((π : ℂ) * Complex.I) t := by
    simpa using (((hasDerivAt_id t).ofReal_comp).const_mul (π : ℂ)).mul_const Complex.I
  have h2 := (h1.cexp).const_mul (R : ℂ)
  exact h2.congr_deriv (by ring)

lemma isC1On_semicircleArc (R : ℝ) (x y : ℝ) : IsC1On (semicircleArc R) x y := by
  refine ⟨fun t _ => (hasDerivAt_semicircleArc R t).differentiableAt, ?_⟩
  have hc : Continuous fun t : ℝ =>
      (R : ℂ) * Complex.exp (π * t * Complex.I) * (π * Complex.I) :=
    (continuous_const.mul (Complex.continuous_exp.comp
      ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const))).mul
      continuous_const
  have he : deriv (semicircleArc R) = fun t : ℝ =>
      (R : ℂ) * Complex.exp (π * t * Complex.I) * (π * Complex.I) :=
    funext fun t => (hasDerivAt_semicircleArc R t).deriv
  rw [he]
  exact hc.continuousOn

lemma semicircleArc_eq (R t : ℝ) :
    semicircleArc R t
      = ((R * Real.cos (π * t) : ℝ) : ℂ) + ((R * Real.sin (π * t) : ℝ) : ℂ) * I := by
  have : (π : ℂ) * t * Complex.I = ((π * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [semicircleArc, this, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast
  ring

lemma semicircleArc_re (R t : ℝ) : (semicircleArc R t).re = R * Real.cos (π * t) := by
  rw [semicircleArc_eq]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im]
  ring

lemma semicircleArc_im (R t : ℝ) : (semicircleArc R t).im = R * Real.sin (π * t) := by
  rw [semicircleArc_eq]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re]
  ring

lemma norm_semicircleArc {R : ℝ} (hR : 0 ≤ R) (t : ℝ) : ‖semicircleArc R t‖ = R := by
  have : (π : ℂ) * t * Complex.I = ((π * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [semicircleArc, this, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real,
    Real.norm_of_nonneg hR, mul_one]

lemma norm_deriv_semicircleArc {R : ℝ} (hR : 0 ≤ R) (t : ℝ) :
    ‖deriv (semicircleArc R) t‖ = R * π := by
  have : (π : ℂ) * t * Complex.I = ((π * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [(hasDerivAt_semicircleArc R t).deriv, this, norm_mul, norm_mul,
    Complex.norm_exp_ofReal_mul_I, norm_mul, Complex.norm_real, Complex.norm_I,
    Complex.norm_real, Real.norm_of_nonneg hR, Real.norm_of_nonneg Real.pi_pos.le]
  ring

end Arc

section Primitives

/-- Primitive of `1 / (z² + 1)` on the strip `|Im z| < 1`. -/
noncomputable def primS (z : ℂ) : ℂ := 1 / (2 * I) * (Complex.log (z - I) - Complex.log (z + I))

/-- Primitive of `1 / (z² + 1)` near the upper semicircle. -/
noncomputable def primA (z : ℂ) : ℂ :=
  1 / (2 * I) * (Complex.log (-I * (z - I)) - Complex.log (z + I))

lemma hasDerivAt_primS {z : ℂ} (h1 : z - I ∈ slitPlane) (h2 : z + I ∈ slitPlane) :
    HasDerivAt primS (1 / (z ^ 2 + 1)) z := by
  have a1 := ((hasDerivAt_id z).sub_const I).clog (by simpa using h1)
  have a2 := ((hasDerivAt_id z).add_const I).clog (by simpa using h2)
  have n1 : z - I ≠ 0 := slitPlane_ne_zero h1
  have n2 : z + I ≠ 0 := slitPlane_ne_zero h2
  have h := (a1.sub a2).const_mul (1 / (2 * I))
  refine h.congr_deriv ?_
  have e : z ^ 2 + 1 = (z - I) * (z + I) := by
    linear_combination Complex.I_sq
  simp only [id]
  rw [e]
  field_simp
  ring_nf

lemma hasDerivAt_primA {z : ℂ} (h1 : -I * (z - I) ∈ slitPlane) (h2 : z + I ∈ slitPlane) :
    HasDerivAt primA (1 / (z ^ 2 + 1)) z := by
  have a1 := (((hasDerivAt_id z).sub_const I).const_mul (-I)).clog (by simpa using h1)
  have a2 := ((hasDerivAt_id z).add_const I).clog (by simpa using h2)
  have n1 : -I * (z - I) ≠ 0 := slitPlane_ne_zero h1
  have n2 : z + I ≠ 0 := slitPlane_ne_zero h2
  have n1' : z - I ≠ 0 := fun h => n1 (by simp [h])
  have h := (a1.sub a2).const_mul (1 / (2 * I))
  refine h.congr_deriv ?_
  have e : z ^ 2 + 1 = (z - I) * (z + I) := by
    linear_combination Complex.I_sq
  simp only [id]
  rw [e]
  field_simp
  ring_nf

end Primitives

section Args

lemma arg_sum {R : ℝ} (hR : 0 < R) : arg ((R : ℂ) + I) + arg (1 + R * I) = π / 2 := by
  have h1 : |arg ((R : ℂ) + I)| < π / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl (by simpa using hR))
  have h2 : |arg (1 + (R : ℂ) * I)| < π / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl (by simp))
  have hx : (R : ℂ) + I ≠ 0 := fun h => by simpa using congrArg Complex.im h
  have hy : 1 + (R : ℂ) * I ≠ 0 := fun h => by simpa using congrArg Complex.re h
  have hmem : arg ((R : ℂ) + I) + arg (1 + R * I) ∈ Ioc (-π) π := by
    rw [abs_lt] at h1 h2
    constructor <;> linarith [Real.pi_pos]
  have hmul : ((R : ℂ) + I) * (1 + R * I) = ((R ^ 2 + 1 : ℝ) : ℂ) * I := by
    push_cast
    linear_combination (R : ℂ) * Complex.I_sq
  have := Complex.arg_mul hx hy hmem
  rw [hmul, Complex.arg_real_mul _ (by positivity), Complex.arg_I] at this
  exact this.symm

lemma log_bracket {R : ℝ} (hR : 0 < R) :
    Complex.log ((R : ℂ) - I) - Complex.log (-(R : ℂ) - I) + Complex.log (-1 + R * I)
      - Complex.log (-1 - R * I) = 2 * π * I := by
  set a := arg ((R : ℂ) + I) with ha
  set b := arg (1 + (R : ℂ) * I) with hb
  have hab := arg_sum hR
  have ha' : |a| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl (by simpa using hR))
  have hapi : a ≠ π := by
    rw [abs_lt] at ha'
    intro h
    linarith [Real.pi_pos]
  have hbpi : b ≠ π := by
    have : |b| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl (by simp))
    rw [abs_lt] at this
    intro h
    linarith [Real.pi_pos]
  have e1 : arg ((R : ℂ) - I) = -a := by
    have : (R : ℂ) - I = (starRingEnd ℂ) ((R : ℂ) + I) := by simp; ring
    rw [this, Complex.arg_conj]
    exact ite_eq_right_iff.2 (fun h => absurd h hapi)
  have e2 : arg (-(R : ℂ) - I) = a - π := by
    have : -(R : ℂ) - I = -((R : ℂ) + I) := by ring
    rw [this, Complex.arg_neg_eq_arg_sub_pi_of_im_pos (by simp)]
  have e3 : arg (-1 + (R : ℂ) * I) = π - b := by
    have : -1 + (R : ℂ) * I = -((starRingEnd ℂ) (1 + (R : ℂ) * I)) := by simp; ring
    rw [this, Complex.arg_neg_eq_arg_add_pi_of_im_neg (by simpa using hR), Complex.arg_conj,
      ite_eq_right_iff.2 (fun h => absurd h hbpi)]
    ring
  have e4 : arg (-1 - (R : ℂ) * I) = b - π := by
    have : -1 - (R : ℂ) * I = -(1 + (R : ℂ) * I) := by ring
    rw [this, Complex.arg_neg_eq_arg_sub_pi_of_im_pos (by simpa using hR)]
  have n1 : ‖(R : ℂ) - I‖ = ‖-(R : ℂ) - I‖ := by
    simp [Complex.norm_def, Complex.normSq_apply]
  have n2 : ‖-1 + (R : ℂ) * I‖ = ‖-1 - (R : ℂ) * I‖ := by
    simp [Complex.norm_def, Complex.normSq_apply]
  apply Complex.ext
  · simp [Complex.log_re, n1, n2]
  · simp only [Complex.sub_im, Complex.add_im, Complex.log_im, e1, e2, e3, e4]
    simp
    linarith

end Args

section Pieces

/-- The strip `|Im z| < 1` containing the segment. -/
def stripSet : Set ℂ := {z | |z.im| < 1}

/-- A set containing the upper arc on which `primA` is a primitive. -/
def arcSet : Set ℂ := {z | 0 < (z + I).im ∧ -I * (z - I) ∈ slitPlane}

lemma sq_add_one_ne_zero {z : ℂ} (h1 : z - I ≠ 0) (h2 : z + I ≠ 0) : z ^ 2 + 1 ≠ 0 := by
  have e : z ^ 2 + 1 = (z - I) * (z + I) := by
    linear_combination Complex.I_sq
  rw [e]
  exact mul_ne_zero h1 h2

lemma continuousOn_inv_sq_add_one {U : Set ℂ} (h : ∀ z ∈ U, z ^ 2 + 1 ≠ 0) :
    ContinuousOn (fun z : ℂ => 1 / (z ^ 2 + 1)) U :=
  by
  simp only [one_div]
  exact ContinuousOn.inv₀ (((continuous_pow 2).add continuous_const).continuousOn) h

lemma sub_I_mem_slitPlane {z : ℂ} (hz : z ∈ stripSet) : z - I ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  right
  have hz' : |z.im| < 1 := hz
  have := (abs_lt.1 hz').2
  simp only [Complex.sub_im, Complex.I_im]
  intro h
  linarith

lemma add_I_mem_slitPlane {z : ℂ} (hz : z ∈ stripSet) : z + I ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  right
  have hz' : |z.im| < 1 := hz
  have := (abs_lt.1 hz').1
  simp only [Complex.add_im, Complex.I_im]
  intro h
  linarith

lemma continuousOn_strip : ContinuousOn (fun z : ℂ => 1 / (z ^ 2 + 1)) stripSet :=
  continuousOn_inv_sq_add_one fun _ hz =>
    sq_add_one_ne_zero (slitPlane_ne_zero (sub_I_mem_slitPlane hz))
      (slitPlane_ne_zero (add_I_mem_slitPlane hz))

lemma add_I_mem_slitPlane_arc {z : ℂ} (hz : z ∈ arcSet) : z + I ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  exact Or.inr hz.1.ne'

lemma sub_I_ne_zero_arc {z : ℂ} (hz : z ∈ arcSet) : z - I ≠ 0 := by
  intro h
  have := slitPlane_ne_zero hz.2
  apply this
  simp [h]

lemma continuousOn_arc : ContinuousOn (fun z : ℂ => 1 / (z ^ 2 + 1)) arcSet :=
  continuousOn_inv_sq_add_one fun _ hz =>
    sq_add_one_ne_zero (sub_I_ne_zero_arc hz) (slitPlane_ne_zero (add_I_mem_slitPlane_arc hz))

lemma segPath_mem_strip {R t : ℝ} : segPath (-(R : ℂ)) R t ∈ stripSet := by
  simp [stripSet, segPath]

lemma semicircleArc_mem {R t : ℝ} (hR : 1 < R) (ht : t ∈ Icc (0 : ℝ) 1) :
    semicircleArc R t ∈ arcSet := by
  have hs : 0 ≤ Real.sin (π * t) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos, ht.1])
      (by nlinarith [Real.pi_pos, ht.2])
  have hR0 : 0 < R := by linarith
  have hre := semicircleArc_re R t
  have him := semicircleArc_im R t
  show 0 < (semicircleArc R t + I).im ∧ -I * (semicircleArc R t - I) ∈ slitPlane
  rw [mem_slitPlane_iff]
  refine ⟨?_, ?_⟩
  · simp only [Complex.add_im, Complex.I_im, him]
    nlinarith [mul_nonneg hR0.le hs]
  by_cases hc : Real.cos (π * t) = 0
  · left
    have h1 : Real.sin (π * t) = 1 := by
      nlinarith [Real.sin_sq_add_cos_sq (π * t)]
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
      Complex.sub_re, Complex.sub_im, him, hre, h1, hc]
    linarith
  · right
    simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
      Complex.sub_re, Complex.sub_im, him, hre]
    intro h
    have h0 : R * Real.cos (π * t) = 0 := by linarith
    rcases mul_eq_zero.1 h0 with h0 | h0
    · exact hR0.ne' h0
    · exact hc h0

lemma pathIntegral_segment {R : ℝ} :
    pathIntegral (fun z => 1 / (z ^ 2 + 1)) (segPath (-(R : ℂ)) R) 0 1
      = primS R - primS (-(R : ℂ)) := by
  have h := pathIntegral_eq_sub (f := fun z : ℂ => 1 / (z ^ 2 + 1)) (F := primS)
    (U := stripSet) (isC1On_segPath (-(R : ℂ)) R 0 1) (fun t _ => segPath_mem_strip)
    (fun z hz => hasDerivAt_primS (sub_I_mem_slitPlane hz) (add_I_mem_slitPlane hz))
    continuousOn_strip
  simpa [segPath_zero, segPath_one] using h

lemma pathIntegral_arc {R : ℝ} (hR : 1 < R) :
    pathIntegral (fun z => 1 / (z ^ 2 + 1)) (semicircleArc R) 0 1
      = primA (-(R : ℂ)) - primA R := by
  have h := pathIntegral_eq_sub (f := fun z : ℂ => 1 / (z ^ 2 + 1)) (F := primA)
    (U := arcSet) (isC1On_semicircleArc R 0 1)
    (fun t ht => semicircleArc_mem hR (by rwa [uIcc_of_le zero_le_one] at ht))
    (fun z hz => hasDerivAt_primA hz.2 (add_I_mem_slitPlane_arc hz))
    continuousOn_arc
  have e0 : semicircleArc R 0 = R := by simp [semicircleArc]
  have e1 : semicircleArc R 1 = -(R : ℂ) := by simp [semicircleArc, Complex.exp_pi_mul_I]
  rwa [e0, e1] at h

end Pieces

/-- Beck Example 4.4.7: the integral of `1 / (z² + 1)` over the counterclockwise semicircle of
radius `R > 1` is `π`. -/
@[kb "beck2025" "Example 4.4.7, p. 84"]
theorem pathIntegral_semicircle {R : ℝ} (hR : 1 < R) :
    pathIntegral (fun z => 1 / (z ^ 2 + 1)) (semicirclePath R) 0 1 = π := by
  have hR0 : 0 < R := by linarith
  have hseg := isC1On_segPath (-(R : ℂ)) R 0 1
  have harc := isC1On_semicircleArc R 0 1
  have hf₁ : ContinuousOn (fun z : ℂ => 1 / (z ^ 2 + 1)) (segPath (-(R : ℂ)) R '' Icc 0 1) :=
    continuousOn_strip.mono (by rintro _ ⟨t, -, rfl⟩; exact segPath_mem_strip)
  have hf₂ : ContinuousOn (fun z : ℂ => 1 / (z ^ 2 + 1)) (semicircleArc R '' Icc 0 1) :=
    continuousOn_arc.mono (by rintro _ ⟨t, ht, rfl⟩; exact semicircleArc_mem hR ht)
  have hjoin : segPath (-(R : ℂ)) R 1 = semicircleArc R 0 := by
    simp [segPath, semicircleArc]
  rw [semicirclePath, pathIntegral_pathConcat (hseg.isPiecewiseSmooth zero_le_one)
    (harc.isPiecewiseSmooth zero_le_one) hjoin hf₁ hf₂, pathIntegral_segment,
    pathIntegral_arc hR]
  have h3 : -I * (-(R : ℂ) - I) = -1 + R * I := by linear_combination Complex.I_sq
  have h4 : -I * ((R : ℂ) - I) = -1 - R * I := by linear_combination Complex.I_sq
  have key : primS R - primS (-(R : ℂ)) + (primA (-(R : ℂ)) - primA R)
      = 1 / (2 * I) * (Complex.log ((R : ℂ) - I) - Complex.log (-(R : ℂ) - I)
        + Complex.log (-1 + R * I) - Complex.log (-1 - R * I)) := by
    unfold primS primA
    rw [h3, h4]
    ring
  rw [key, log_bracket hR0]
  field_simp


section Real

lemma pathIntegral_segment_eq {R : ℝ} (hR : 0 < R) :
    pathIntegral (fun z => 1 / (z ^ 2 + 1)) (segPath (-(R : ℂ)) R) 0 1
      = ((∫ x in (-R)..R, 1 / (x ^ 2 + 1) : ℝ) : ℂ) := by
  have h : ∀ t : ℝ, 1 / (segPath (-(R : ℂ)) R t ^ 2 + 1) * deriv (segPath (-(R : ℂ)) R) t
      = ((2 * R * (1 / ((2 * R * t - R) ^ 2 + 1)) : ℝ) : ℂ) := by
    intro t
    rw [deriv_segPath]
    simp only [segPath]
    push_cast
    ring_nf
  unfold pathIntegral
  simp only [h]
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_sub (fun x : ℝ => 1 / (x ^ 2 + 1)) (by positivity) R]
  congr 1
  simp only [smul_eq_mul, mul_zero, zero_sub, mul_one]
  have : 2 * R - R = R := by ring
  rw [this]
  field_simp

lemma norm_pathIntegral_arc_le {R : ℝ} (hR : 1 < R) :
    ‖pathIntegral (fun z => 1 / (z ^ 2 + 1)) (semicircleArc R) 0 1‖ ≤ π * R / (R ^ 2 - 1) := by
  have hR0 : 0 < R := by linarith
  have hpos : 0 < R ^ 2 - 1 := by nlinarith
  unfold pathIntegral
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := π * R / (R ^ 2 - 1))
    ?_).trans (by simp)
  intro t ht
  rw [uIoc_of_le zero_le_one] at ht
  have hz := norm_semicircleArc hR0.le t
  have hlow : R ^ 2 - 1 ≤ ‖semicircleArc R t ^ 2 + 1‖ := by
    have := norm_sub_norm_le (semicircleArc R t ^ 2) (-1)
    rw [norm_pow, hz, norm_neg, norm_one, sub_neg_eq_add] at this
    exact this
  rw [norm_mul, norm_div, norm_one, norm_deriv_semicircleArc hR0.le]
  calc 1 / ‖semicircleArc R t ^ 2 + 1‖ * (R * π) ≤ 1 / (R ^ 2 - 1) * (R * π) := by
        gcongr
    _ = π * R / (R ^ 2 - 1) := by field_simp

/-- Beck Example 5.3.5: `∫_{-∞}^{∞} dx / (x² + 1) = π`, proved by the book's contour argument:
the integral over the segment `[-R, R]` equals `π` minus the arc integral, which is bounded by
`π R / (R² - 1) → 0`. -/
@[kb "beck2025" "Example 5.3.5, p. 97"]
theorem integral_inv_sq_add_one_via_contour : ∫ x : ℝ, 1 / (x ^ 2 + 1) = π := by
  have hlim : Tendsto (fun R : ℝ => ∫ x in (-R)..R, 1 / (x ^ 2 + 1)) atTop (𝓝 π) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      ((tendsto_const_nhds (x := 2 * π)).div_atTop tendsto_id)
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with R hR2
    have hR : 1 < R := by linarith
    have hR0 : 0 < R := by linarith
    have hc := pathIntegral_semicircle hR
    have hsplit : pathIntegral (fun z => 1 / (z ^ 2 + 1)) (semicirclePath R) 0 1
        = pathIntegral (fun z => 1 / (z ^ 2 + 1)) (segPath (-(R : ℂ)) R) 0 1
          + pathIntegral (fun z => 1 / (z ^ 2 + 1)) (semicircleArc R) 0 1 := by
      have hf₁ : ContinuousOn (fun z : ℂ => 1 / (z ^ 2 + 1))
          (segPath (-(R : ℂ)) R '' Icc 0 1) :=
        continuousOn_strip.mono (by rintro _ ⟨t, -, rfl⟩; exact segPath_mem_strip)
      have hf₂ : ContinuousOn (fun z : ℂ => 1 / (z ^ 2 + 1)) (semicircleArc R '' Icc 0 1) :=
        continuousOn_arc.mono (by rintro _ ⟨t, ht, rfl⟩; exact semicircleArc_mem hR ht)
      have hjoin : segPath (-(R : ℂ)) R 1 = semicircleArc R 0 := by
        simp [segPath, semicircleArc]
      exact pathIntegral_pathConcat ((isC1On_segPath _ _ 0 1).isPiecewiseSmooth zero_le_one)
        ((isC1On_semicircleArc R 0 1).isPiecewiseSmooth zero_le_one) hjoin hf₁ hf₂
    rw [hsplit, pathIntegral_segment_eq hR0] at hc
    have hnorm : ‖(∫ x in (-R)..R, 1 / (x ^ 2 + 1)) - π‖
        = ‖pathIntegral (fun z => 1 / (z ^ 2 + 1)) (semicircleArc R) 0 1‖ := by
      rw [← Complex.norm_real, Complex.ofReal_sub, ← norm_neg]
      congr 1
      rw [← eq_sub_iff_add_eq'] at hc
      rw [hc]
      ring
    rw [hnorm]
    refine (norm_pathIntegral_arc_le hR).trans ?_
    rw [id, div_le_div_iff₀ (by nlinarith) hR0]
    nlinarith [mul_nonneg Real.pi_pos.le (show (0 : ℝ) ≤ R ^ 2 - 2 by nlinarith)]
  have hint : Integrable (fun x : ℝ => 1 / (x ^ 2 + 1)) := by
    simpa [add_comm, one_div] using integrable_inv_one_add_sq
  exact tendsto_nhds_unique
    (intervalIntegral_tendsto_integral hint tendsto_neg_atTop_atBot tendsto_id) hlim

end Real

end UndergradKB.ComplexAnalysis
