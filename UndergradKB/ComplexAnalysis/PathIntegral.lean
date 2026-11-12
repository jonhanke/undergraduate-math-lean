import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Shift
import UndergradKB.Common.Attr

/-!
# Contour integrals along C^1 paths (rows CX-056 to CX-059, CX-061 to CX-064)

The integral of a complex function along a parametrised path `γ : ℝ → ℂ` on `[a, b]` is the
interval integral of `f (γ t) * γ' t`. Mathlib only has the special case of circles; here the general
definition is introduced and the basic calculus is proved: agreement with `circleIntegral`,
invariance under reparametrisation, linearity, additivity, reversal, the length estimate, the
fundamental theorem of calculus for contour integrals and the non-existence of a logarithm
antiderivative of `1 / z`.

"Smooth" is encoded by `IsC1On γ a b`: `γ` is differentiable at every point of `[a, b]` and `deriv γ`
is continuous there. Piecewise smooth paths are handled by splitting the interval
(`pathIntegral_add_adjacent`).
-/

open Set intervalIntegral MeasureTheory
open scoped Real

namespace UndergradKB.ComplexAnalysis

/-- Beck Definition 4.1.1 (CX-056). The integral of `f` along the parametrised path `γ` on `[a, b]`. -/
@[kb "beck2025" "Definition 4.1.1, p. 70"]
noncomputable def pathIntegral (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) : ℂ :=
  ∫ t in a..b, f (γ t) * deriv γ t

/-- Beck Definition 4.1.5 (CX-058). The length of the path `γ` on `[a, b]`. -/
@[kb "beck2025" "Definition 4.1.5, p. 72"]
noncomputable def pathLength (γ : ℝ → ℂ) (a b : ℝ) : ℝ :=
  ∫ t in a..b, ‖deriv γ t‖

/-- `γ` is a `C^1` path on the interval with endpoints `a`, `b`. -/
def IsC1On (γ : ℝ → ℂ) (a b : ℝ) : Prop :=
  (∀ t ∈ uIcc a b, DifferentiableAt ℝ γ t) ∧ ContinuousOn (deriv γ) (uIcc a b)

namespace IsC1On

variable {γ : ℝ → ℂ} {a b : ℝ}

lemma hasDerivAt (h : IsC1On γ a b) {t : ℝ} (ht : t ∈ uIcc a b) :
    HasDerivAt γ (deriv γ t) t :=
  (h.1 t ht).hasDerivAt

lemma continuousOn (h : IsC1On γ a b) : ContinuousOn γ (uIcc a b) :=
  fun t ht => (h.1 t ht).continuousAt.continuousWithinAt

lemma mono (h : IsC1On γ a b) {c d : ℝ} (hs : uIcc c d ⊆ uIcc a b) : IsC1On γ c d :=
  ⟨fun t ht => h.1 t (hs ht), h.2.mono hs⟩

end IsC1On

section Basic

variable {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ}

lemma integrand_continuousOn (hγ : IsC1On γ a b) (hf : ContinuousOn f (γ '' uIcc a b)) :
    ContinuousOn (fun t => f (γ t) * deriv γ t) (uIcc a b) :=
  (hf.comp hγ.continuousOn (mapsTo_image γ _)).mul hγ.2

lemma intervalIntegrable_integrand (hγ : IsC1On γ a b)
    (hf : ContinuousOn f (γ '' uIcc a b)) :
    IntervalIntegrable (fun t => f (γ t) * deriv γ t) volume a b :=
  (integrand_continuousOn hγ hf).intervalIntegrable

/-- The circle `circleMap c R` is a `C^1` path. -/
lemma isC1On_circleMap (c : ℂ) (R : ℝ) (a b : ℝ) : IsC1On (circleMap c R) a b := by
  refine ⟨fun t _ => (hasDerivAt_circleMap c R t).differentiableAt, ?_⟩
  have : deriv (circleMap c R) = fun θ => circleMap 0 R θ * Complex.I :=
    funext (deriv_circleMap c R)
  rw [this]
  exact ((continuous_circleMap 0 R).mul continuous_const).continuousOn

/-- Beck Definition 4.1.1 (CX-056): for the circle path the contour integral is Mathlib's
`circleIntegral`. -/
@[kb "beck2025" "Definition 4.1.1, p. 70"]
theorem pathIntegral_circleMap (f : ℂ → ℂ) (c : ℂ) (R : ℝ) :
    pathIntegral f (circleMap c R) 0 (2 * π) = ∮ z in C(c, R), f z := by
  unfold pathIntegral circleIntegral
  refine integral_congr (fun t _ => ?_)
  simp only [smul_eq_mul, mul_comm]

/-! ### Linearity, additivity, reversal, estimate (CX-059) -/

/-- Beck Proposition 4.1.8 (CX-059): additivity in the integrand. -/
@[kb "beck2025" "Proposition 4.1.8, p. 73"]
theorem pathIntegral_add (g : ℂ → ℂ)
    (hf : IntervalIntegrable (fun t => f (γ t) * deriv γ t) volume a b)
    (hg : IntervalIntegrable (fun t => g (γ t) * deriv γ t) volume a b) :
    pathIntegral (fun z => f z + g z) γ a b = pathIntegral f γ a b + pathIntegral g γ a b := by
  unfold pathIntegral
  simp only [add_mul]
  exact integral_add hf hg

/-- Beck Proposition 4.1.8 (CX-059): constant multiples. -/
@[kb "beck2025" "Proposition 4.1.8, p. 73"]
theorem pathIntegral_const_mul (k : ℂ) :
    pathIntegral (fun z => k * f z) γ a b = k * pathIntegral f γ a b := by
  unfold pathIntegral
  simp only [mul_assoc]
  exact integral_const_mul _ _

/-- Beck Proposition 4.1.8 (CX-059): splitting the interval (concatenation of paths). -/
@[kb "beck2025" "Proposition 4.1.8, p. 73"]
theorem pathIntegral_add_adjacent {c : ℝ}
    (hab : IntervalIntegrable (fun t => f (γ t) * deriv γ t) volume a b)
    (hbc : IntervalIntegrable (fun t => f (γ t) * deriv γ t) volume b c) :
    pathIntegral f γ a b + pathIntegral f γ b c = pathIntegral f γ a c :=
  integral_add_adjacent_intervals hab hbc

/-- Additivity for a `C^1` path on `[a, c]` split at `b`. -/
theorem pathIntegral_add_adjacent_of_isC1On {c : ℝ} (hγ : IsC1On γ a c)
    (hf : ContinuousOn f (γ '' uIcc a c)) (hb : b ∈ uIcc a c) :
    pathIntegral f γ a b + pathIntegral f γ b c = pathIntegral f γ a c :=
  pathIntegral_add_adjacent
    (intervalIntegrable_integrand (hγ.mono (uIcc_subset_uIcc_left hb))
      (hf.mono (image_mono (uIcc_subset_uIcc_left hb))))
    (intervalIntegrable_integrand (hγ.mono (uIcc_subset_uIcc_right hb))
      (hf.mono (image_mono (uIcc_subset_uIcc_right hb))))

/-- Beck Proposition 4.1.8 (CX-059): reversing the path changes the sign. -/
@[kb "beck2025" "Proposition 4.1.8, p. 73"]
theorem pathIntegral_reverse :
    pathIntegral f (fun t => γ (a + b - t)) a b = -pathIntegral f γ a b := by
  unfold pathIntegral
  have h : ∀ t, deriv (fun t => γ (a + b - t)) t = -deriv γ (a + b - t) :=
    fun t => deriv_comp_const_sub γ (a + b) t
  simp only [h, mul_neg]
  rw [intervalIntegral.integral_neg, integral_comp_sub_left (fun s => f (γ s) * deriv γ s) (a + b)]
  simp

/-- Beck Proposition 4.1.8 (CX-059): `|∫_γ f| ≤ M · length γ` when `|f| ≤ M` on the path. -/
@[kb "beck2025" "Proposition 4.1.8, p. 73"]
theorem norm_pathIntegral_le {M : ℝ} (hγ : IsC1On γ a b) (hf : ContinuousOn f (γ '' uIcc a b))
    (hab : a ≤ b) (hM : ∀ t ∈ Icc a b, ‖f (γ t)‖ ≤ M) :
    ‖pathIntegral f γ a b‖ ≤ M * pathLength γ a b := by
  unfold pathIntegral pathLength
  have hI := intervalIntegrable_integrand hγ hf
  have hL : IntervalIntegrable (fun t => ‖deriv γ t‖) volume a b :=
    hγ.2.norm.intervalIntegrable
  calc ‖∫ t in a..b, f (γ t) * deriv γ t‖
      ≤ ∫ t in a..b, ‖f (γ t) * deriv γ t‖ := norm_integral_le_integral_norm hab
    _ ≤ ∫ t in a..b, M * ‖deriv γ t‖ := by
        refine integral_mono_on hab hI.norm (hL.const_mul M) (fun t ht => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hM t ht) (norm_nonneg _)
    _ = M * ∫ t in a..b, ‖deriv γ t‖ := integral_const_mul _ _

/-! ### Reparametrisation (CX-057) -/

/-- Beck Proposition 4.1.3 (CX-057): the integral along `γ ∘ σ` equals that along `γ` when `σ` is a
`C^1` increasing change of parameter from `[c, d]` onto `[a, b]` (`σ c = a`, `σ d = b`). -/
@[kb "beck2025" "Proposition 4.1.3, p. 72"]
theorem pathIntegral_comp {c d : ℝ} {σ : ℝ → ℝ} (hγ : IsC1On γ a b)
    (hf : ContinuousOn f (γ '' uIcc a b))
    (hσd : ∀ t ∈ uIcc c d, DifferentiableAt ℝ σ t) (hσc : ContinuousOn (deriv σ) (uIcc c d))
    (hmaps : MapsTo σ (uIcc c d) (uIcc a b)) (hc : σ c = a) (hd : σ d = b) :
    pathIntegral f (γ ∘ σ) c d = pathIntegral f γ a b := by
  have hg : ContinuousOn (fun u => f (γ u) * deriv γ u) (σ '' uIcc c d) :=
    (integrand_continuousOn hγ hf).mono (by rintro _ ⟨t, ht, rfl⟩; exact hmaps ht)
  have key := integral_deriv_smul_comp' (f := σ) (f' := deriv σ)
    (g := fun u => f (γ u) * deriv γ u) (fun t ht => (hσd t ht).hasDerivAt) hσc hg
  rw [hc, hd] at key
  unfold pathIntegral
  refine Eq.trans (integral_congr (fun t ht => ?_)) key
  have hder : deriv (γ ∘ σ) t = deriv σ t • deriv γ (σ t) :=
    ((hγ.hasDerivAt (hmaps ht)).scomp t ((hσd t ht).hasDerivAt)).deriv
  change f (γ (σ t)) * deriv (γ ∘ σ) t = deriv σ t • (f (γ (σ t)) * deriv γ (σ t))
  rw [hder]
  simp only [Complex.real_smul]
  ring

/-! ### Lengths (CX-058) -/

/-- Beck Example 4.1.6 (CX-058): the segment from `z` to `w` has length `|w - z|`. -/
@[kb "beck2025" "Example 4.1.6, p. 72"]
theorem pathLength_segment (z w : ℂ) :
    pathLength (fun t : ℝ => z + (t : ℂ) * (w - z)) 0 1 = ‖w - z‖ := by
  have h : ∀ t : ℝ, HasDerivAt (fun t : ℝ => z + (t : ℂ) * (w - z)) (w - z) t := fun t => by
    simpa using ((hasDerivAt_id t).ofReal_comp.mul_const (w - z)).const_add z
  have hd : ∀ t : ℝ, deriv (fun t : ℝ => z + (t : ℂ) * (w - z)) t = w - z := fun t => (h t).deriv
  simp [pathLength, hd]

/-- Beck Example 4.1.7 (CX-058): the circle of radius `R` has length `2π|R|`. -/
@[kb "beck2025" "Example 4.1.7, p. 73"]
theorem pathLength_circleMap (c : ℂ) (R : ℝ) :
    pathLength (circleMap c R) 0 (2 * π) = 2 * π * |R| := by
  simp [pathLength]

/-! ### Fundamental theorem (CX-061 to CX-064) -/

/-- Beck Theorem 4.2.5 (CX-062): if `F' = f` on a set `U` containing the path, then
`∫_γ f = F (γ b) - F (γ a)`. (`f` is assumed continuous on `U`, as in the book.) -/
@[kb "beck2025" "Theorem 4.2.5, p. 75"]
theorem pathIntegral_eq_sub {F : ℂ → ℂ} {U : Set ℂ} (hγ : IsC1On γ a b)
    (hsub : ∀ t ∈ uIcc a b, γ t ∈ U) (hF : ∀ z ∈ U, HasDerivAt F (f z) z)
    (hf : ContinuousOn f U) :
    pathIntegral f γ a b = F (γ b) - F (γ a) := by
  have hfc : ContinuousOn f (γ '' uIcc a b) :=
    hf.mono (by rintro _ ⟨t, ht, rfl⟩; exact hsub t ht)
  unfold pathIntegral
  refine integral_eq_sub_of_hasDerivAt (f := fun t => F (γ t)) (fun t ht => ?_)
    (intervalIntegrable_integrand hγ hfc)
  have h2 : HasDerivAt (fun t => F (γ t)) (deriv γ t • f (γ t)) t :=
    (hF _ (hsub t ht)).scomp t (hγ.hasDerivAt ht)
  rwa [smul_eq_mul, mul_comm] at h2

/-- Beck Corollary 4.2.7 (CX-063): a function with an antiderivative has zero integral over a
closed path. -/
@[kb "beck2025" "Corollary 4.2.7, p. 75"]
theorem pathIntegral_eq_zero_of_closed {F : ℂ → ℂ} {U : Set ℂ} (hγ : IsC1On γ a b)
    (hsub : ∀ t ∈ uIcc a b, γ t ∈ U) (hF : ∀ z ∈ U, HasDerivAt F (f z) z)
    (hf : ContinuousOn f U) (hclosed : γ a = γ b) :
    pathIntegral f γ a b = 0 := by
  rw [pathIntegral_eq_sub hγ hsub hF hf, hclosed, sub_self]

/-- Beck Example 4.2.8 (CX-064): `1 / z` has no antiderivative on `ℂ \ {0}`, because its integral
over the unit circle is `2πi ≠ 0`. -/
@[kb "beck2025" "Example 4.2.8, p. 75"]
theorem not_exists_antiderivative_inv :
    ¬ ∃ F : ℂ → ℂ, ∀ z : ℂ, z ≠ 0 → HasDerivAt F z⁻¹ z := by
  rintro ⟨F, hF⟩
  have h1 := pathIntegral_circleMap (fun z => z⁻¹) 0 1
  have h2 := circleIntegral.integral_sub_inv_of_mem_ball (c := 0) (w := 0) (R := 1)
    (Metric.mem_ball_self one_pos)
  simp only [sub_zero] at h2
  have h3 : pathIntegral (fun z : ℂ => z⁻¹) (circleMap 0 1) 0 (2 * π) = 0 := by
    refine pathIntegral_eq_zero_of_closed (U := {0}ᶜ) (F := F) (isC1On_circleMap 0 1 0 (2 * π))
      (fun t _ => ?_) (fun z hz => hF z hz) ?_ ?_
    · simp [circleMap]
    · exact continuousOn_inv₀
    · exact ((periodic_circleMap 0 1).eq).symm
  have h4 : (2 * π * Complex.I : ℂ) = 0 := by rw [← h2, ← h1, h3]
  simp [Real.pi_ne_zero, Complex.I_ne_zero] at h4

end Basic

end UndergradKB.ComplexAnalysis
