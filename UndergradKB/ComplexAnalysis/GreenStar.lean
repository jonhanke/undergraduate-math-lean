import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.LinearAlgebra.Complex.Module
import UndergradKB.ComplexAnalysis.GreenRadial
import UndergradKB.ComplexAnalysis.StarExamples

/-!
# Green's theorem for convex star-shaped paths

Beck Theorem A.0.10 (Green's theorem) for every piecewise smooth path `γ` that is star-shaped about
`c` (`IsStarPath`) and lies on the boundary of a convex set `K` containing `c`:
`∫_γ f dx + g dy = ∬_{inside γ} (∂g/∂x - ∂f/∂y) dx dy` (`IsStarPath.green`).

The proof starts from the radial form `green_radial` (an integral over the parameter square of the
integrand at `c + s (γ t - c)` times the Jacobian) and changes variables by the map
`Φ(t + i s) = c + s (γ t - c)`, which is injective on the open square (off the finitely many
corners of `γ`), has Jacobian determinant `-s (Re(γ - c) Im γ' - Im(γ - c) Re γ')`, of constant
sign because the angle of `γ` about `c` increases, and maps the square onto the inside of `γ` up to
finitely many segments (of measure zero).
-/

open Set Metric Complex Filter Topology MeasureTheory intervalIntegral
open scoped Real

namespace UndergradKB.ComplexAnalysis

/-- The determinant of a real-linear map of `ℂ`. -/
lemma det_clm_complex (L : ℂ →L[ℝ] ℂ) :
    L.det = (L 1).re * (L I).im - (L 1).im * (L I).re := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr,
    ContinuousLinearMap.coe_coe, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

/-- A line in `ℂ` has measure zero. -/
lemma volume_range_line (c v : ℂ) : volume (Set.range fun s : ℝ => c + s * v) = 0 := by
  by_cases hv : v = 0
  · subst hv
    simp only [mul_zero, add_zero, range_const]
    exact measure_singleton c
  refine measure_mono_null ?_
    (Measure.addHaar_affineSubspace volume (AffineSubspace.mk' c (ℝ ∙ v)) ?_)
  · rintro _ ⟨s, rfl⟩
    rw [SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub, add_sub_cancel_left,
      Submodule.mem_span_singleton]
    exact ⟨s, by rw [Complex.real_smul]⟩
  · intro htop
    have hmem : c + I * v ∈ AffineSubspace.mk' c (ℝ ∙ v) := htop ▸ AffineSubspace.mem_top ℝ ℂ _
    rw [AffineSubspace.mem_mk', vsub_eq_sub, add_sub_cancel_left,
      Submodule.mem_span_singleton] at hmem
    obtain ⟨r, hr⟩ := hmem
    rw [Complex.real_smul] at hr
    have h1 : ((r : ℂ) - I) * v = 0 := by rw [sub_mul, hr, sub_self]
    rcases mul_eq_zero.1 h1 with h2 | h2
    · have := congrArg Complex.im h2
      simp at this
    · exact hv h2

/-- The vertical line `Re z = a` has measure zero. -/
lemma volume_re_eq (a : ℝ) : volume {z : ℂ | z.re = a} = 0 := by
  refine measure_mono_null (t := Set.range fun s : ℝ => (a : ℂ) + s * I)
    (fun z (hz : z.re = a) => ⟨z.im, ?_⟩) (volume_range_line (a : ℂ) I)
  apply Complex.ext <;> simp [hz.symm]

/-- The horizontal line `Im z = a` has measure zero. -/
lemma volume_im_eq (a : ℝ) : volume {z : ℂ | z.im = a} = 0 := by
  refine measure_mono_null (t := Set.range fun s : ℝ => (a : ℂ) * I + s * 1)
    (fun z (hz : z.im = a) => ⟨z.re, ?_⟩) (volume_range_line ((a : ℂ) * I) 1)
  apply Complex.ext <;> simp [hz.symm]

namespace IsStarPath

variable {γ : ℝ → ℂ} {c : ℂ} {φ : ℝ → ℝ}

/-- The Jacobian factor `Re(γ - c) Im γ' - Im(γ - c) Re γ'` is nonnegative: the angle of a
star-shaped path about its centre increases. -/
lemma jacobian_nonneg (h : IsStarPath γ c φ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {D : ℂ}
    (hD : HasDerivAt γ D t) : 0 ≤ (γ t - c).re * D.im - (γ t - c).im * D.re := by
  have htI : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
  set u := γ t - c with hu
  set Λ : ℂ → ℝ := fun z => u.re * z.im - u.im * z.re with hΛ
  have hΛc : Continuous Λ := by fun_prop
  have hlim := (hΛc.tendsto D).comp hD.tendsto_slope_zero_right
  refine ge_of_tendsto hlim ?_
  have hφc : ContinuousAt φ t := h.angle_cont.continuousAt (Icc_mem_nhds ht.1 ht.2)
  have hφt : Tendsto (fun x : ℝ => φ (t + x)) (𝓝[>] 0) (𝓝 (φ t)) := by
    have : Tendsto (fun x : ℝ => t + x) (𝓝[>] 0) (𝓝 t) := by
      have h0 : Tendsto (fun x : ℝ => t + x) (𝓝 0) (𝓝 (t + 0)) := tendsto_const_nhds.add tendsto_id
      rw [add_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    exact hφc.tendsto.comp this
  have hev1 : ∀ᶠ x in 𝓝[>] (0 : ℝ), φ (t + x) - φ t < π := by
    have := hφt.eventually (Iio_mem_nhds (show φ t < φ t + π by linarith [Real.pi_pos]))
    filter_upwards [this] with x hx
    linarith
  have hev2 : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioo (0 : ℝ) (1 - t) :=
    Ioo_mem_nhdsGT (by linarith [ht.2])
  filter_upwards [hev1, hev2] with x hx1 hx2
  have hx0 : 0 < x := hx2.1
  have htx : t + x ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [hx2.2]⟩
  have hmono : φ t ≤ φ (t + x) := h.angle_mono.monotoneOn htI htx (by linarith)
  set w := γ (t + x) - c with hw
  have e1 := h.sub_eq htI
  have e2 := h.sub_eq htx
  set N₁ := ‖γ t - c‖
  set N₂ := ‖γ (t + x) - c‖
  have hslope : x⁻¹ • (γ (t + x) - γ t) = (x⁻¹ : ℝ) • (w - u) := by
    rw [hw, hu]; congr 1; ring
  simp only [Function.comp_apply, hslope, hΛ]
  have hkey : u.re * (w - u).im - u.im * (w - u).re = N₁ * N₂ * Real.sin (φ (t + x) - φ t) := by
    rw [hw, hu, e1, e2]
    simp only [sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im, zero_mul, sub_zero,
      add_zero, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im]
    rw [Real.sin_sub]
    ring
  have hsin : 0 ≤ Real.sin (φ (t + x) - φ t) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) hx1.le
  simp only [Complex.real_smul, mul_im, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
    add_zero]
  have : u.re * (x⁻¹ * (w - u).im) - u.im * (x⁻¹ * (w - u).re) =
      x⁻¹ * (u.re * (w - u).im - u.im * (w - u).re) := by ring
  rw [this, hkey]
  have hN₁ : 0 ≤ N₁ := norm_nonneg _
  have hN₂ : 0 ≤ N₂ := norm_nonneg _
  have hx' : 0 ≤ x⁻¹ := inv_nonneg.2 hx0.le
  positivity

end IsStarPath

/-! ### The change of variables `t + i s ↦ c + s (γ t - c)` -/

/-- The map `t + i s ↦ c + s (γ t - c)` from the parameter square to the plane. -/
noncomputable def starMap (c : ℂ) (γ : ℝ → ℂ) (p : ℂ) : ℂ := segPt c γ p.im p.re

/-- Its derivative at `p`: `v ↦ Re v · s γ'(t) + Im v · (γ t - c)` with `p = t + i s`. -/
noncomputable def starMapDeriv (c : ℂ) (γ : ℝ → ℂ) (p : ℂ) : ℂ →L[ℝ] ℂ :=
  reCLM.smulRight ((p.im : ℂ) * deriv γ p.re) + imCLM.smulRight (γ p.re - c)

lemma hasFDerivAt_starMap {γ : ℝ → ℂ} (c : ℂ) {p : ℂ} (hd : DifferentiableAt ℝ γ p.re) :
    HasFDerivAt (starMap c γ) (starMapDeriv c γ p) p := by
  have h1 : HasFDerivAt (fun q : ℂ => γ q.re) (reCLM.smulRight (deriv γ p.re)) p := by
    have := hd.hasDerivAt.hasFDerivAt.comp p reCLM.hasFDerivAt
    refine this.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    simp
  have h2 : HasFDerivAt (fun q : ℂ => ((q.im : ℝ) : ℂ)) (ofRealCLM.comp imCLM) p :=
    ofRealCLM.hasFDerivAt.comp p imCLM.hasFDerivAt
  have h3 := (h2.mul (h1.sub_const c)).const_add c
  have hfun : starMap c γ = fun q : ℂ => c + ((q.im : ℝ) : ℂ) * (γ q.re - c) := rfl
  rw [hfun]
  refine h3.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp only [starMapDeriv, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, reCLM_apply, imCLM_apply,
    ofRealCLM_apply, Complex.real_smul, smul_eq_mul]
  ring

lemma det_starMapDeriv (c : ℂ) (γ : ℝ → ℂ) (p : ℂ) :
    (starMapDeriv c γ p).det = -(p.im * ((γ p.re - c).re * (deriv γ p.re).im -
      (γ p.re - c).im * (deriv γ p.re).re)) := by
  rw [det_clm_complex]
  simp only [starMapDeriv, add_apply, ContinuousLinearMap.smulRight_apply,
    reCLM_apply, imCLM_apply, one_re, one_im, I_re, I_im, Complex.real_smul, ofReal_one,
    ofReal_zero, one_mul, zero_mul, add_zero, zero_add, mul_re, mul_im, ofReal_re, ofReal_im]
  ring

section Green

variable {γ : ℝ → ℂ} {c : ℂ} {φ : ℝ → ℝ} {K : Set ℂ} {U : Set ℂ} {f g : ℂ → ℝ}

/-- The radial integrand is integrable on the parameter square. -/
lemma integrableOn_greenIntegrand (hγ : IsPiecewiseSmooth γ 0 1) (hU : IsOpen U)
    (hPU : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, segPt c γ s t ∈ U)
    (hf : ContDiffOn ℝ 1 f U) (hg : ContDiffOn ℝ 1 g U) :
    IntegrableOn (fun p : ℝ × ℝ => greenIntegrand f g c γ p.1 p.2) (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1)
      (volume.prod volume) := by
  have hsq : Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 :=
    prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self
  have hms : MeasurableSet (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) :=
    measurableSet_Ioc.prod measurableSet_Ioc
  have hP := continuousOn_segPt hγ hU hPU hf hg
  have hM := mapsTo_segPt hγ hU hPU hf hg
  have hDf := ((hf.continuousOn_fderiv_of_isOpen hU le_rfl).comp hP hM).clm_apply
    (continuousOn_const (c := I))
  have hDg := ((hg.continuousOn_fderiv_of_isOpen hU le_rfl).comp hP hM).clm_apply
    (continuousOn_const (c := (1 : ℂ)))
  have hu : ContinuousOn (fun p : ℝ × ℝ => γ p.1 - c) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    (hγ.continuousOn.comp continuousOn_fst
      (fun p (hp : p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) => hp.1)).sub continuousOn_const
  have hC : ContinuousOn (fun p : ℝ × ℝ => p.2 * (fderiv ℝ g (segPt c γ p.2 p.1) 1 -
      fderiv ℝ f (segPt c γ p.2 p.1) I)) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    continuousOn_snd.mul (hDg.sub hDf)
  have hC₁ := hC.mul (continuous_re.comp_continuousOn hu)
  have hC₂ := hC.mul (continuous_im.comp_continuousOn hu)
  obtain ⟨M₁, hM₁⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hC₁
  obtain ⟨M₂, hM₂⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hC₂
  obtain ⟨-, -, -, -, MD, hMD⟩ := hγ
  have hfin : (volume.prod volume) (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) < ⊤ := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_lt_top measure_Ioc_lt_top measure_Ioc_lt_top
  have heq : (fun p : ℝ × ℝ => greenIntegrand f g c γ p.1 p.2) = fun p =>
      (deriv γ p.1).im * (p.2 * (fderiv ℝ g (segPt c γ p.2 p.1) 1 -
        fderiv ℝ f (segPt c γ p.2 p.1) I) * (γ p.1 - c).re) -
      (deriv γ p.1).re * (p.2 * (fderiv ℝ g (segPt c γ p.2 p.1) 1 -
        fderiv ℝ f (segPt c γ p.2 p.1) I) * (γ p.1 - c).im) := by
    funext p
    simp only [greenIntegrand]
    ring
  rw [heq]
  refine ⟨?_, HasFiniteIntegral.restrict_of_bounded (C := MD * M₁ + MD * M₂) hfin ?_⟩
  · have hre : Measurable fun p : ℝ × ℝ => (deriv γ p.1).re :=
      Complex.measurable_re.comp ((measurable_deriv γ).comp measurable_fst)
    have him : Measurable fun p : ℝ × ℝ => (deriv γ p.1).im :=
      Complex.measurable_im.comp ((measurable_deriv γ).comp measurable_fst)
    exact (him.aestronglyMeasurable.mul ((hC₁.mono hsq).aestronglyMeasurable hms)).sub
      (hre.aestronglyMeasurable.mul ((hC₂.mono hsq).aestronglyMeasurable hms))
  · refine ae_restrict_of_forall_mem hms (fun p hp => ?_)
    have hp' := hsq hp
    have hD := hMD p.1 hp'.1
    refine (norm_sub_le _ _).trans ?_
    refine add_le_add ?_ ?_
    · rw [norm_mul]
      exact mul_le_mul ((Complex.abs_im_le_norm _).trans hD) (hM₁ p hp') (norm_nonneg _)
        ((norm_nonneg _).trans hD)
    · rw [norm_mul]
      exact mul_le_mul ((Complex.abs_re_le_norm _).trans hD) (hM₂ p hp') (norm_nonneg _)
        ((norm_nonneg _).trans hD)

/-- The iterated integral over the parameter square as an integral over the subset
`(0, 1] × (0, 1]` of `ℂ`. -/
lemma iterated_eq_setIntegral (hγ : IsPiecewiseSmooth γ 0 1) (hU : IsOpen U)
    (hPU : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, segPt c γ s t ∈ U)
    (hf : ContDiffOn ℝ 1 f U) (hg : ContDiffOn ℝ 1 g U) :
    ∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1, greenIntegrand f g c γ t s =
      ∫ z in Ioc (0 : ℝ) 1 ×ℂ Ioc (0 : ℝ) 1, greenIntegrand f g c γ z.re z.im := by
  have hm := Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding
    (fun p : ℝ × ℝ => greenIntegrand f g c γ p.1 p.2) (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1)
  have hpre : Complex.measurableEquivRealProd ⁻¹' (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) =
      Ioc (0 : ℝ) 1 ×ℂ Ioc (0 : ℝ) 1 := by
    ext z; simp [mem_reProdIm, Complex.measurableEquivRealProd]
  have hz : (fun z : ℂ => greenIntegrand f g c γ (Complex.measurableEquivRealProd z).1
      (Complex.measurableEquivRealProd z).2) = fun z => greenIntegrand f g c γ z.re z.im := by
    funext z; rfl
  rw [hpre, hz] at hm
  rw [hm, Measure.volume_eq_prod,
    setIntegral_prod _ (integrableOn_greenIntegrand hγ hU hPU hf hg)]
  simp only [intervalIntegral.integral_of_le zero_le_one]

/-- **Green's theorem for convex star-shaped paths** (Beck Theorem A.0.10). Let `γ` be a
piecewise smooth closed path, star-shaped about `c` (`IsStarPath`), on the boundary of a convex set
`K` containing `c`, and let `f, g : ℂ → ℝ` be `C¹` on an open set `U ⊇ K`. Then
`∫_γ f dx + g dy = ∬_{inside γ} (∂g/∂x - ∂f/∂y) dx dy`. -/
@[kb "beck2025" "Theorem A.0.10, p. 167"]
theorem IsStarPath.green (h : IsStarPath γ c φ) (hγ : IsPiecewiseSmooth γ 0 1) (hK : Convex ℝ K)
    (hcK : c ∈ K) (himK : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ K)
    (hint : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∉ interior K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) (hg : ContDiffOn ℝ 1 g U) :
    lineIntegral f g γ = ∫ z in insideOf γ, (fderiv ℝ g z 1 - fderiv ℝ f z I) := by
  have hPU : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, segPt c γ s t ∈ U := fun t ht s hs =>
    hKU (by
      rw [segPt, IsStarPath.combo_eq]
      exact hK hcK (himK t ht) (by linarith [hs.2]) hs.1 (by ring))
  obtain ⟨S, hdiff, -, -⟩ := hγ.2
  set A : Set ℂ := (Ioo (0 : ℝ) 1 \ (S : Set ℝ)) ×ℂ Ioo (0 : ℝ) 1 with hA
  set B : Set ℂ := Ioc (0 : ℝ) 1 ×ℂ Ioc (0 : ℝ) 1 with hB
  have hAm : MeasurableSet A :=
    (Complex.measurable_re (measurableSet_Ioo.diff S.finite_toSet.measurableSet)).inter
      (Complex.measurable_im measurableSet_Ioo)
  -- the square minus `A` is contained in finitely many lines
  set N : Set ℂ := (⋃ τ ∈ ((insert 1 S : Finset ℝ) : Set ℝ), {z : ℂ | z.re = τ}) ∪
    {z : ℂ | z.im = 1} with hN
  have hN0 : volume N = 0 :=
    measure_union_null ((measure_biUnion_null_iff (Finset.countable_toSet _)).2
      (fun τ _ => volume_re_eq τ)) (volume_im_eq 1)
  have hBA : B \ N = A := by
    ext z
    simp only [hA, hB, hN, Set.mem_sdiff, mem_reProdIm, mem_Ioc, mem_Ioo, mem_union, mem_iUnion,
      Set.mem_ofPred_eq, Finset.coe_insert, mem_insert_iff, Finset.mem_coe, exists_prop, not_or,
      not_exists, not_and]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, h6, h7⟩
      refine ⟨⟨⟨h1, lt_of_le_of_ne h2 (fun e => h6 _ (Or.inl rfl) e)⟩,
        fun hS => h6 _ (Or.inr hS) rfl⟩, h3, lt_of_le_of_ne h4 h7⟩
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4, h5⟩
      refine ⟨⟨⟨h1, h2.le⟩, h4, h5.le⟩, fun τ hτ e => ?_, h5.ne⟩
      rcases hτ with rfl | hτ
      · exact absurd e h2.ne
      · exact h3 (e ▸ hτ)
  -- the image of `A` is the inside up to finitely many segments
  set L : Set ℂ := {c} ∪ ⋃ τ ∈ ((insert 0 (insert 1 S) : Finset ℝ) : Set ℝ),
    Set.range fun s : ℝ => c + s * (γ τ - c) with hL
  have hL0 : volume L = 0 :=
    measure_union_null (measure_singleton c) ((measure_biUnion_null_iff
      (Finset.countable_toSet _)).2 (fun τ _ => volume_range_line _ _))
  have hsubI : starMap c γ '' A ⊆ interior K := by
    rintro _ ⟨p, hp, rfl⟩
    exact (h.mem_interior_iff hK hcK himK hint).2 ⟨p.re, Ioo_subset_Icc_self hp.1.1, p.im,
      ⟨hp.2.1.le, hp.2.2⟩, rfl⟩
  have hdiffL : interior K \ starMap c γ '' A ⊆ L := by
    rintro z ⟨hz, hzA⟩
    by_cases hzc : z = c
    · exact Or.inl hzc
    right
    obtain ⟨t, ht, r, hr, rfl⟩ := h.exists_ray hzc
    have ht' := Ico_subset_Icc_self ht
    by_cases hτ : t ∈ ((insert 0 (insert 1 S) : Finset ℝ) : Set ℝ)
    · exact mem_biUnion hτ ⟨r, rfl⟩
    exfalso
    simp only [Finset.coe_insert, mem_insert_iff, Finset.mem_coe, not_or] at hτ
    obtain ⟨t', ht'', s', hs', he⟩ := (h.mem_interior_iff hK hcK himK hint).1 hz
    have hs'0 : 0 < s' := by
      rcases eq_or_lt_of_le hs'.1 with e | e
      · exfalso; apply hzc; rw [he, ← e]; simp
      · exact e
    obtain ⟨-, hrs⟩ := h.eq_of_ray_eq ht' ht'' hr hs'0 he
    refine hzA ⟨⟨t, r⟩, ⟨⟨⟨lt_of_le_of_ne ht.1 (Ne.symm hτ.1), ht.2⟩, hτ.2.2⟩, hr,
      hrs ▸ hs'.2⟩, ?_⟩
    simp [starMap, segPt]
  have hAeq : starMap c γ '' A =ᵐ[volume] interior K := by
    have : starMap c γ '' A = interior K \ (interior K \ starMap c γ '' A) :=
      (sdiff_sdiff_cancel_left hsubI).symm
    rw [this]
    exact sdiff_null_ae_eq_self (measure_mono_null hdiffL hL0)
  -- assemble
  rw [green_radial hγ hU hPU hf hg h.closed, iterated_eq_setIntegral hγ hU hPU hf hg,
    setIntegral_congr_set (sdiff_null_ae_eq_self hN0).symm, hBA,
    h.insideOf_eq_interior hK hcK himK hint, ← setIntegral_congr_set hAeq,
    integral_image_eq_integral_abs_det_fderiv_smul volume hAm
      (fun p hp => (hasFDerivAt_starMap c (hdiff p.re hp.1.1 hp.1.2)).hasFDerivWithinAt) ?_]
  · refine setIntegral_congr_fun hAm (fun p hp => ?_)
    have hJ := h.jacobian_nonneg hp.1.1 (hdiff p.re hp.1.1 hp.1.2).hasDerivAt
    rw [det_starMapDeriv, abs_neg, abs_of_nonneg (mul_nonneg hp.2.1.le hJ), smul_eq_mul]
    simp only [greenIntegrand, starMap]
    ring
  · rintro p hp q hq hpq
    have hpq' : c + (p.im : ℂ) * (γ p.re - c) = c + (q.im : ℂ) * (γ q.re - c) := hpq
    obtain ⟨hγe, him⟩ := h.eq_of_ray_eq (Ioo_subset_Icc_self hp.1.1) (Ioo_subset_Icc_self hq.1.1)
      hp.2.1 hq.2.1 hpq'
    have hre := h.injOn (Ioo_subset_Ico_self hp.1.1) (Ioo_subset_Ico_self hq.1.1) hγe
    exact Complex.ext hre him

end Green

/-! ### Circles and ellipses -/

section Examples

variable {c : ℂ} {U : Set ℂ} {f g : ℂ → ℝ}

/-- **Green's theorem for a circle**: `∫_{C[c, R]} f dx + g dy = ∬_{D(c, R)} (∂g/∂x - ∂f/∂y)`. -/
@[kb "beck2025" "Theorem A.0.10, p. 167"]
theorem green_circlePath {R : ℝ} (hR : 0 < R) (hU : IsOpen U) (hKU : closedBall c R ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) (hg : ContDiffOn ℝ 1 g U) :
    lineIntegral f g (circlePath c R) = ∫ z in ball c R, (fderiv ℝ g z 1 - fderiv ℝ f z I) := by
  have e : circlePath c R = polarPath c (fun _ => R) := rfl
  have hs := isStarPath_polarPath (c := c) (ρ := fun _ => R) continuousOn_const (fun _ _ => hR) rfl
  have hps : IsPiecewiseSmooth (polarPath c (fun _ => R)) 0 1 := e ▸ isPiecewiseSmooth_circlePath c R
  have hnorm : ∀ t : ℝ, ‖polarPath c (fun _ => R) t - c‖ = R := fun t => norm_polarPath_sub hR
  rw [← insideOf_circlePath hR, e]
  refine hs.green hps (convex_closedBall c R) (mem_closedBall_self hR.le)
    (fun t _ => by rw [mem_closedBall, dist_eq_norm, hnorm]) (fun t _ => ?_) hU hKU hf hg
  rw [interior_closedBall c hR.ne', mem_ball, dist_eq_norm, hnorm]
  exact lt_irrefl R

/-- **Green's theorem for an ellipse**: the line integral along `ellipsePath c a b` is the double
integral over the open elliptical disc. -/
@[kb "beck2025" "Theorem A.0.10, p. 167"]
theorem green_ellipsePath {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hU : IsOpen U)
    (hKU : ellipseDisc c a b ⊆ U) (hf : ContDiffOn ℝ 1 f U) (hg : ContDiffOn ℝ 1 g U) :
    lineIntegral f g (ellipsePath c a b) =
      ∫ z in ellipseOpenDisc c a b, (fderiv ℝ g z 1 - fderiv ℝ f z I) := by
  rw [← insideOf_ellipsePath ha hb]
  exact (isStarPath_ellipsePath ha hb).green (isPiecewiseSmooth_ellipsePath ha hb)
    convex_ellipseDisc center_mem_ellipseDisc
    (fun t _ => le_of_eq (ellipsePath_on_ellipse ha hb t))
    (fun t _ => ellipsePath_not_mem_interior ha hb t) hU hKU hf hg

end Examples

end UndergradKB.ComplexAnalysis
