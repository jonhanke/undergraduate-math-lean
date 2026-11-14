import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import UndergradKB.ComplexAnalysis.GreenRectangle

/-!
# Green's theorem in radial form

For a closed piecewise smooth path `γ` on `[0, 1]` and a point `c` such that every segment from
`c` to a point of `γ` lies in an open set `U` on which `f, g : ℂ → ℝ` are `C¹`, the line integral
`∫_γ f dx + g dy` equals the integral over the parameter square of
`(∂g/∂x - ∂f/∂y)` at `P(s, t) = c + s (γ(t) - c)` times the Jacobian
`s · (Re(γ t - c) Im γ'(t) - Im(γ t - c) Re γ'(t))` of `P` (`green_radial`).

This is the computation behind Green's theorem (Beck Theorem A.0.10) for regions that are
star-shaped about `c`: integrate the exterior derivative of `f dx + g dy` pulled back by `P` over
the square. The `s`-integral of `∂_s (ω(∂_t P))` gives the line integral (the fundamental theorem
in `s`), the `t`-integral of `∂_t (ω(∂_s P))` vanishes because `γ` is closed (the fundamental
theorem in `t`, off the finitely many corners), and Fubini's theorem exchanges the order.
-/

open Set Metric Complex Filter Topology MeasureTheory intervalIntegral
open scoped Real

namespace UndergradKB.ComplexAnalysis

/-- A real-linear functional on `ℂ` in coordinates. -/
lemma clm_apply_eq (L : ℂ →L[ℝ] ℝ) (v : ℂ) : L v = v.re * L 1 + v.im * L I := by
  have hv : v = v.re • (1 : ℂ) + v.im • I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- The point `c + s (γ t - c)` of the segment from `c` to `γ t`. -/
noncomputable def segPt (c : ℂ) (γ : ℝ → ℂ) (s t : ℝ) : ℂ := c + (s : ℂ) * (γ t - c)

lemma segPt_one (c : ℂ) (γ : ℝ → ℂ) (t : ℝ) : segPt c γ 1 t = γ t := by
  simp [segPt]

lemma hasDerivAt_segPt_s (c : ℂ) (γ : ℝ → ℂ) (s t : ℝ) :
    HasDerivAt (fun s => segPt c γ s t) (γ t - c) s := by
  have := ((hasDerivAt_id s).ofReal_comp.mul_const (γ t - c)).const_add c
  simpa [segPt] using this

lemma hasDerivAt_segPt_t (c : ℂ) {γ : ℝ → ℂ} (s : ℝ) {t : ℝ} {D : ℂ} (h : HasDerivAt γ D t) :
    HasDerivAt (fun t => segPt c γ s t) ((s : ℂ) * D) t := by
  have := ((h.sub_const c).const_mul (s : ℂ)).const_add c
  simpa [segPt] using this

lemma hasDerivAt_re_sub {γ : ℝ → ℂ} {t : ℝ} {D : ℂ} (c : ℂ) (h : HasDerivAt γ D t) :
    HasDerivAt (fun t => (γ t - c).re) D.re t := by
  exact reCLM.hasFDerivAt.comp_hasDerivAt t (h.sub_const c)

lemma hasDerivAt_im_sub {γ : ℝ → ℂ} {t : ℝ} {D : ℂ} (c : ℂ) (h : HasDerivAt γ D t) :
    HasDerivAt (fun t => (γ t - c).im) D.im t := by
  exact imCLM.hasFDerivAt.comp_hasDerivAt t (h.sub_const c)

section Radial

variable {γ : ℝ → ℂ} {c : ℂ} {U : Set ℂ} {f g : ℂ → ℝ}

/-- `∂_s` of `ω(∂_t P)` (with `ω = f dx + g dy`), in coordinates. -/
noncomputable def greenA (f g : ℂ → ℝ) (c : ℂ) (γ : ℝ → ℂ) (t s : ℝ) : ℝ :=
  (deriv γ t).re * (f (segPt c γ s t) + s * fderiv ℝ f (segPt c γ s t) (γ t - c)) +
    (deriv γ t).im * (g (segPt c γ s t) + s * fderiv ℝ g (segPt c γ s t) (γ t - c))

/-- The coefficients of `Re γ'` and `Im γ'` in `∂_t` of `ω(∂_s P)`. -/
noncomputable def greenB₁ (f g : ℂ → ℝ) (c : ℂ) (γ : ℝ → ℂ) (t s : ℝ) : ℝ :=
  s * (fderiv ℝ f (segPt c γ s t) 1 * (γ t - c).re + fderiv ℝ g (segPt c γ s t) 1 * (γ t - c).im)
    + f (segPt c γ s t)

noncomputable def greenB₂ (f g : ℂ → ℝ) (c : ℂ) (γ : ℝ → ℂ) (t s : ℝ) : ℝ :=
  s * (fderiv ℝ f (segPt c γ s t) I * (γ t - c).re + fderiv ℝ g (segPt c γ s t) I * (γ t - c).im)
    + g (segPt c γ s t)

/-- `∂_t` of `ω(∂_s P)`, in coordinates. -/
noncomputable def greenB (f g : ℂ → ℝ) (c : ℂ) (γ : ℝ → ℂ) (t s : ℝ) : ℝ :=
  (deriv γ t).re * greenB₁ f g c γ t s + (deriv γ t).im * greenB₂ f g c γ t s

/-- The integrand of the radial Green formula. -/
noncomputable def greenIntegrand (f g : ℂ → ℝ) (c : ℂ) (γ : ℝ → ℂ) (t s : ℝ) : ℝ :=
  s * (fderiv ℝ g (segPt c γ s t) 1 - fderiv ℝ f (segPt c γ s t) I) *
    ((γ t - c).re * (deriv γ t).im - (γ t - c).im * (deriv γ t).re)

lemma greenA_sub_greenB (t s : ℝ) :
    greenA f g c γ t s - greenB f g c γ t s = greenIntegrand f g c γ t s := by
  simp only [greenA, greenB, greenB₁, greenB₂, greenIntegrand]
  rw [clm_apply_eq (fderiv ℝ f _) (γ t - c), clm_apply_eq (fderiv ℝ g _) (γ t - c)]
  ring

lemma continuous_segPt_s (c : ℂ) (γ : ℝ → ℂ) (t : ℝ) : Continuous fun s => segPt c γ s t := by
  unfold segPt
  fun_prop

variable (hγ : IsPiecewiseSmooth γ 0 1) (hU : IsOpen U)
  (hPU : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, segPt c γ s t ∈ U)
  (hf : ContDiffOn ℝ 1 f U) (hg : ContDiffOn ℝ 1 g U)
include hγ hU hPU hf hg

lemma continuousOn_segPt :
    ContinuousOn (fun p : ℝ × ℝ => segPt c γ p.2 p.1) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
  refine continuousOn_const.add (ContinuousOn.mul ?_ ?_)
  · exact continuous_ofReal.comp_continuousOn continuousOn_snd
  · exact (hγ.continuousOn.comp continuousOn_fst
      (fun p (hp : p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) => hp.1)).sub continuousOn_const

lemma mapsTo_segPt :
    MapsTo (fun p : ℝ × ℝ => segPt c γ p.2 p.1) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) U :=
  fun p hp => hPU p.1 hp.1 p.2 hp.2

lemma continuousOn_greenB₁ :
    ContinuousOn (fun p : ℝ × ℝ => greenB₁ f g c γ p.1 p.2) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
  have hP := continuousOn_segPt hγ hU hPU hf hg
  have hM := mapsTo_segPt hγ hU hPU hf hg
  have hu : ContinuousOn (fun p : ℝ × ℝ => γ p.1 - c) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    (hγ.continuousOn.comp continuousOn_fst
      (fun p (hp : p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) => hp.1)).sub continuousOn_const
  have hDf := ((hf.continuousOn_fderiv_of_isOpen hU le_rfl).comp hP hM).clm_apply
    (continuousOn_const (c := (1 : ℂ)))
  have hDg := ((hg.continuousOn_fderiv_of_isOpen hU le_rfl).comp hP hM).clm_apply
    (continuousOn_const (c := (1 : ℂ)))
  refine ContinuousOn.add (continuousOn_snd.mul (ContinuousOn.add (hDf.mul ?_) (hDg.mul ?_)))
    (hf.continuousOn.comp hP hM)
  · exact continuous_re.comp_continuousOn hu
  · exact continuous_im.comp_continuousOn hu

lemma continuousOn_greenB₂ :
    ContinuousOn (fun p : ℝ × ℝ => greenB₂ f g c γ p.1 p.2) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
  have hP := continuousOn_segPt hγ hU hPU hf hg
  have hM := mapsTo_segPt hγ hU hPU hf hg
  have hu : ContinuousOn (fun p : ℝ × ℝ => γ p.1 - c) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    (hγ.continuousOn.comp continuousOn_fst
      (fun p (hp : p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) => hp.1)).sub continuousOn_const
  have hDf := ((hf.continuousOn_fderiv_of_isOpen hU le_rfl).comp hP hM).clm_apply
    (continuousOn_const (c := I))
  have hDg := ((hg.continuousOn_fderiv_of_isOpen hU le_rfl).comp hP hM).clm_apply
    (continuousOn_const (c := I))
  refine ContinuousOn.add (continuousOn_snd.mul (ContinuousOn.add (hDf.mul ?_) (hDg.mul ?_)))
    (hg.continuousOn.comp hP hM)
  · exact continuous_re.comp_continuousOn hu
  · exact continuous_im.comp_continuousOn hu

lemma continuousOn_segPt_t (s : ℝ) : ContinuousOn (fun t => segPt c γ s t) (Icc 0 1) :=
  continuousOn_const.add (continuousOn_const.mul (hγ.continuousOn.sub continuousOn_const))

lemma continuousOn_greenA {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ContinuousOn (fun s => greenA f g c γ t s) (Icc 0 1) := by
  have hM : MapsTo (fun s => segPt c γ s t) (Icc (0 : ℝ) 1) U := fun s hs => hPU t ht s hs
  have hP := (continuous_segPt_s c γ t).continuousOn (s := Icc (0 : ℝ) 1)
  have hc1 := ((hf.continuousOn_fderiv_of_isOpen hU le_rfl).comp hP hM).clm_apply
    (continuousOn_const (c := γ t - c))
  have hc2 := ((hg.continuousOn_fderiv_of_isOpen hU le_rfl).comp hP hM).clm_apply
    (continuousOn_const (c := γ t - c))
  have hc3 := hf.continuousOn.comp hP hM
  have hc4 := hg.continuousOn.comp hP hM
  exact (continuousOn_const.mul (hc3.add (continuousOn_id.mul hc1))).add
    (continuousOn_const.mul (hc4.add (continuousOn_id.mul hc2)))

/-- For fixed `t`, the `s`-integral of `greenA` is the line integrand at `t`. -/
lemma integral_greenA {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∫ s in (0 : ℝ)..1, greenA f g c γ t s =
      f (γ t) * (deriv γ t).re + g (γ t) * (deriv γ t).im := by
  have hP := continuousOn_segPt hγ hU hPU hf hg
  have hM := mapsTo_segPt hγ hU hPU hf hg
  have hpair : ContinuousOn (fun s : ℝ => ((t, s) : ℝ × ℝ)) (Icc (0 : ℝ) 1) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hpairM : MapsTo (fun s : ℝ => ((t, s) : ℝ × ℝ)) (Icc (0 : ℝ) 1)
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := fun s hs => ⟨ht, hs⟩
  have hd : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt
      (fun s => s * (f (segPt c γ s t) * (deriv γ t).re + g (segPt c γ s t) * (deriv γ t).im))
      (greenA f g c γ t s) s := by
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    have hm := hPU t ht s hs
    have hfd := ((hf.differentiableOn one_ne_zero _ hm).differentiableAt (hU.mem_nhds hm)).hasFDerivAt
    have hgd := ((hg.differentiableOn one_ne_zero _ hm).differentiableAt (hU.mem_nhds hm)).hasFDerivAt
    have h1 := hfd.comp_hasDerivAt s (hasDerivAt_segPt_s c γ s t)
    have h2 := hgd.comp_hasDerivAt s (hasDerivAt_segPt_s c γ s t)
    have h3 := (hasDerivAt_id s).mul ((h1.mul_const (deriv γ t).re).add (h2.mul_const (deriv γ t).im))
    refine h3.congr_deriv ?_
    simp only [greenA, id, Function.comp_def, Pi.add_apply]
    ring
  rw [integral_eq_sub_of_hasDerivAt hd]
  · simp only [segPt_one, one_mul, zero_mul, sub_zero]
  · refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact continuousOn_greenA hγ hU hPU hf hg ht

lemma intervalIntegrable_deriv_re :
    IntervalIntegrable (fun t => (deriv γ t).re) volume 0 1 := by
  have h := hγ.intervalIntegrable_deriv zero_le_one
  exact ⟨h.1.re, h.2.re⟩

lemma intervalIntegrable_deriv_im :
    IntervalIntegrable (fun t => (deriv γ t).im) volume 0 1 := by
  have h := hγ.intervalIntegrable_deriv zero_le_one
  exact ⟨h.1.im, h.2.im⟩

/-- For fixed `s`, the `t`-integral of `greenB` vanishes, since `γ` is closed. -/
lemma integral_greenB (hcl : γ 0 = γ 1) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∫ t in (0 : ℝ)..1, greenB f g c γ t s = 0 := by
  have hP := continuousOn_segPt hγ hU hPU hf hg
  have hM := mapsTo_segPt hγ hU hPU hf hg
  have hpair : ContinuousOn (fun t : ℝ => ((t, s) : ℝ × ℝ)) (Icc (0 : ℝ) 1) :=
    (continuous_id.prodMk continuous_const).continuousOn
  have hpairM : MapsTo (fun t : ℝ => ((t, s) : ℝ × ℝ)) (Icc (0 : ℝ) 1)
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := fun t ht => ⟨ht, hs⟩
  obtain ⟨S, hdiff, -, -⟩ := hγ.2
  have hfin := integral_eq_of_hasDerivAt_off_countable_of_le
    (fun t => f (segPt c γ s t) * (γ t - c).re + g (segPt c γ s t) * (γ t - c).im)
    (fun t => greenB f g c γ t s) zero_le_one S.countable_toSet ?_ ?_ ?_
  · rw [hfin]
    simp only [segPt, hcl, sub_self]
  · have hM' : MapsTo (fun t => segPt c γ s t) (Icc (0 : ℝ) 1) U := fun t ht => hPU t ht s hs
    have hc3 := hf.continuousOn.comp (continuousOn_segPt_t hγ hU hPU hf hg s) hM'
    have hc4 := hg.continuousOn.comp (continuousOn_segPt_t hγ hU hPU hf hg s) hM'
    have hu : ContinuousOn (fun t => γ t - c) (Icc (0 : ℝ) 1) :=
      hγ.continuousOn.sub continuousOn_const
    exact (hc3.mul (continuous_re.comp_continuousOn hu)).add
      (hc4.mul (continuous_im.comp_continuousOn hu))
  · intro t ht
    have htI : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht.1
    have hγd := (hdiff t ht.1 ht.2).hasDerivAt
    have hm := hPU t htI s hs
    have hfd := ((hf.differentiableOn one_ne_zero _ hm).differentiableAt (hU.mem_nhds hm)).hasFDerivAt
    have hgd := ((hg.differentiableOn one_ne_zero _ hm).differentiableAt (hU.mem_nhds hm)).hasFDerivAt
    have h1 := hfd.comp_hasDerivAt t (hasDerivAt_segPt_t c s hγd)
    have h2 := hgd.comp_hasDerivAt t (hasDerivAt_segPt_t c s hγd)
    have h3 := (h1.mul (hasDerivAt_re_sub c hγd)).add (h2.mul (hasDerivAt_im_sub c hγd))
    refine h3.congr_deriv ?_
    simp only [greenB, greenB₁, greenB₂, Function.comp_def]
    rw [clm_apply_eq (fderiv ℝ f _) ((s : ℂ) * deriv γ t),
      clm_apply_eq (fderiv ℝ g _) ((s : ℂ) * deriv γ t)]
    simp only [mul_re, mul_im, ofReal_re, ofReal_im, zero_mul, sub_zero, add_zero]
    ring
  · have hB₁ := (continuousOn_greenB₁ hγ hU hPU hf hg).comp hpair hpairM
    have hB₂ := (continuousOn_greenB₂ hγ hU hPU hf hg).comp hpair hpairM
    rw [← uIcc_of_le zero_le_one] at hB₁ hB₂
    exact ((intervalIntegrable_deriv_re hγ hU hPU hf hg).mul_continuousOn hB₁).add
      ((intervalIntegrable_deriv_im hγ hU hPU hf hg).mul_continuousOn hB₂)

/-- `greenB` is integrable on the square (it is bounded and measurable). -/
lemma integrable_greenB :
    Integrable (Function.uncurry fun t s => greenB f g c γ t s)
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  rw [Measure.prod_restrict]
  have hsq : Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 :=
    prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self
  have hms : MeasurableSet (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) :=
    measurableSet_Ioc.prod measurableSet_Ioc
  have hB₁ := continuousOn_greenB₁ hγ hU hPU hf hg
  have hB₂ := continuousOn_greenB₂ hγ hU hPU hf hg
  obtain ⟨M₁, hM₁⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hB₁
  obtain ⟨M₂, hM₂⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hB₂
  obtain ⟨-, -, -, -, MD, hMD⟩ := hγ
  have hfin : (volume.prod volume) (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) < ⊤ := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_lt_top measure_Ioc_lt_top measure_Ioc_lt_top
  refine ⟨?_, HasFiniteIntegral.restrict_of_bounded (C := MD * M₁ + MD * M₂) hfin ?_⟩
  · have hre : Measurable fun p : ℝ × ℝ => (deriv γ p.1).re :=
      Complex.measurable_re.comp ((measurable_deriv γ).comp measurable_fst)
    have him : Measurable fun p : ℝ × ℝ => (deriv γ p.1).im :=
      Complex.measurable_im.comp ((measurable_deriv γ).comp measurable_fst)
    exact (hre.aestronglyMeasurable.mul ((hB₁.mono hsq).aestronglyMeasurable hms)).add
      (him.aestronglyMeasurable.mul ((hB₂.mono hsq).aestronglyMeasurable hms))
  · refine ae_restrict_of_forall_mem hms (fun p hp => ?_)
    have hp' := hsq hp
    have hD := hMD p.1 hp'.1
    have h1 := hM₁ p hp'
    have h2 := hM₂ p hp'
    simp only [Function.uncurry, greenB]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul]
      exact mul_le_mul ((Complex.abs_re_le_norm _).trans hD) h1 (norm_nonneg _)
        ((norm_nonneg _).trans hD)
    · rw [norm_mul]
      exact mul_le_mul ((Complex.abs_im_le_norm _).trans hD) h2 (norm_nonneg _)
        ((norm_nonneg _).trans hD)

lemma intervalIntegrable_greenB_s {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun s => greenB f g c γ t s) volume 0 1 := by
  have hpair : ContinuousOn (fun s : ℝ => ((t, s) : ℝ × ℝ)) (Icc (0 : ℝ) 1) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hpairM : MapsTo (fun s : ℝ => ((t, s) : ℝ × ℝ)) (Icc (0 : ℝ) 1)
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := fun s hs => ⟨ht, hs⟩
  have h1 := (continuousOn_greenB₁ hγ hU hPU hf hg).comp hpair hpairM
  have h2 := (continuousOn_greenB₂ hγ hU hPU hf hg).comp hpair hpairM
  have h3 := (continuousOn_const (c := (deriv γ t).re)).mul h1
  have h4 := (continuousOn_const (c := (deriv γ t).im)).mul h2
  exact (h3.add h4).intervalIntegrable_of_Icc zero_le_one

lemma integral_integral_greenB (hcl : γ 0 = γ 1) :
    ∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1, greenB f g c γ t s = 0 := by
  have hInt := integrable_greenB hγ hU hPU hf hg
  simp only [intervalIntegral.integral_of_le zero_le_one]
  rw [integral_integral_swap hInt]
  refine (setIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)).trans (integral_zero _ _)
  have := integral_greenB hγ hU hPU hf hg hcl (Ioc_subset_Icc_self hs)
  rwa [intervalIntegral.integral_of_le zero_le_one] at this

lemma intervalIntegrable_integral_greenB :
    IntervalIntegrable (fun t => ∫ s in (0 : ℝ)..1, greenB f g c γ t s) volume 0 1 := by
  have hInt := integrable_greenB hγ hU hPU hf hg
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  simp only [intervalIntegral.integral_of_le zero_le_one]
  exact hInt.integral_prod_left

lemma intervalIntegrable_lineIntegrand :
    IntervalIntegrable (fun t => f (γ t) * (deriv γ t).re + g (γ t) * (deriv γ t).im)
      volume 0 1 := by
  have hγU : MapsTo γ (Icc (0 : ℝ) 1) U := fun t ht => by
    simpa [segPt_one] using hPU t ht 1 ⟨zero_le_one, le_rfl⟩
  have hfc : ContinuousOn (fun t => f (γ t)) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    exact hf.continuousOn.comp hγ.continuousOn hγU
  have hgc : ContinuousOn (fun t => g (γ t)) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    exact hg.continuousOn.comp hγ.continuousOn hγU
  exact ((intervalIntegrable_deriv_re hγ hU hPU hf hg).continuousOn_mul hfc).add
    ((intervalIntegrable_deriv_im hγ hU hPU hf hg).continuousOn_mul hgc)

lemma intervalIntegrable_integral_greenA :
    IntervalIntegrable (fun t => ∫ s in (0 : ℝ)..1, greenA f g c γ t s) volume 0 1 := by
  refine (intervalIntegrable_lineIntegrand hγ hU hPU hf hg).congr ?_
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by
    rw [uIoc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] at ht
    exact Ioc_subset_Icc_self ht
  exact (integral_greenA hγ hU hPU hf hg ht').symm

/-- **Green's theorem in radial form.** For a closed piecewise smooth path `γ`, a point `c` and an
open set `U` containing every segment from `c` to the path, and `C¹` functions `f, g` on `U`,
`∫_γ f dx + g dy` is the integral over the square `0 ≤ s, t ≤ 1` of `(∂g/∂x - ∂f/∂y)` at
`c + s (γ t - c)` times the Jacobian `s (Re(γ t - c) Im γ' t - Im(γ t - c) Re γ' t)`. -/
@[kb "beck2025" "Theorem A.0.10, p. 167"]
theorem green_radial (hcl : γ 0 = γ 1) :
    lineIntegral f g γ = ∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1, greenIntegrand f g c γ t s := by
  have e1 : ∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1, greenIntegrand f g c γ t s =
      ∫ t in (0 : ℝ)..1, ((∫ s in (0 : ℝ)..1, greenA f g c γ t s) -
        ∫ s in (0 : ℝ)..1, greenB f g c γ t s) := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [uIcc_of_le zero_le_one] at ht
    have hA : IntervalIntegrable (fun s => greenA f g c γ t s) volume 0 1 :=
      (continuousOn_greenA hγ hU hPU hf hg ht).intervalIntegrable_of_Icc zero_le_one
    have hB := intervalIntegrable_greenB_s hγ hU hPU hf hg ht
    rw [← intervalIntegral.integral_sub hA hB]
    exact intervalIntegral.integral_congr (fun s _ => (greenA_sub_greenB t s).symm)
  rw [e1, intervalIntegral.integral_sub (intervalIntegrable_integral_greenA hγ hU hPU hf hg)
    (intervalIntegrable_integral_greenB hγ hU hPU hf hg),
    integral_integral_greenB hγ hU hPU hf hg hcl, sub_zero, lineIntegral]
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [uIcc_of_le zero_le_one] at ht
  exact (integral_greenA hγ hU hPU hf hg ht).symm

end Radial

end UndergradKB.ComplexAnalysis
