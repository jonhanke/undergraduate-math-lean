import UndergradKB.ComplexAnalysis.GreenStar
import UndergradKB.ComplexAnalysis.StarJordan

/-!
# Green's theorem for star-shaped paths

Beck Theorem A.0.10 (Green's theorem) for every piecewise smooth path `γ` that is star-shaped about
a point `c` (`IsStarPath`), with no convexity hypothesis (wave 4 proved it for convex star-shaped
paths, `IsStarPath.green`): `∫_γ f dx + g dy = ∬_{inside γ} (∂g/∂x - ∂f/∂y) dx dy` whenever `f, g`
are `C¹` on an open set containing the closed inside. The proof is wave 4's (radial form, then the
change of variables `t + i s ↦ c + s (γ t - c)`), with the inside now described by the inner region
of `StarJordan.lean`.
-/

open Set Metric Complex Filter Topology MeasureTheory intervalIntegral
open scoped Real

namespace UndergradKB.ComplexAnalysis

namespace IsStarPath

variable {γ : ℝ → ℂ} {c : ℂ} {φ : ℝ → ℝ} {U : Set ℂ} {f g : ℂ → ℝ}

/-- The inner region is the set of points `c + s (γ t - c)` with `0 ≤ s < 1`. -/
lemma mem_inner_iff (h : IsStarPath γ c φ) {z : ℂ} :
    z ∈ inner γ c ↔ ∃ t ∈ Icc (0 : ℝ) 1, ∃ s ∈ Ico (0 : ℝ) 1, z = c + s * (γ t - c) := by
  constructor
  · intro hz
    by_cases hzc : z = c
    · exact ⟨0, zero_mem, 0, ⟨le_rfl, one_pos⟩, by simp [hzc]⟩
    obtain ⟨t, ht, r, hr, hzr, -, hn⟩ := h.exists_ray_radius hzc
    refine ⟨t, ht, r, ⟨hr.le, ?_⟩, hzr⟩
    have h1 : r * radius γ c z < radius γ c z := hn ▸ hz
    have := h.radius_pos z
    nlinarith
  · rintro ⟨t, ht, s, hs, rfl⟩
    exact h.ray_mem_inner ht hs

/-- **Green's theorem for star-shaped paths** (Beck Theorem A.0.10). Let `γ` be a piecewise smooth
closed path, star-shaped about `c` (`IsStarPath`), and let `f, g : ℂ → ℝ` be `C¹` on an open set
`U` containing the path and its inside. Then
`∫_γ f dx + g dy = ∬_{inside γ} (∂g/∂x - ∂f/∂y) dx dy`. No convexity is needed. -/
@[kb "beck2025" "Theorem A.0.10, p. 167"]
theorem green_star (h : IsStarPath γ c φ) (hγ : IsPiecewiseSmooth γ 0 1) (hU : IsOpen U)
    (hKU : inner γ c ∪ pathImage γ ⊆ U) (hf : ContDiffOn ℝ 1 f U) (hg : ContDiffOn ℝ 1 g U) :
    lineIntegral f g γ = ∫ z in insideOf γ, (fderiv ℝ g z 1 - fderiv ℝ f z I) := by
  have hPU : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, segPt c γ s t ∈ U := fun t ht s hs => by
    refine hKU ?_
    rcases eq_or_lt_of_le hs.2 with hs1 | hs1
    · right
      exact ⟨t, ht, by rw [segPt, hs1]; push_cast; ring⟩
    · left
      exact h.ray_mem_inner ht ⟨hs.1, hs1⟩
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
  have hsubI : starMap c γ '' A ⊆ inner γ c := by
    rintro _ ⟨p, hp, rfl⟩
    exact h.mem_inner_iff.2 ⟨p.re, Ioo_subset_Icc_self hp.1.1, p.im,
      ⟨hp.2.1.le, hp.2.2⟩, rfl⟩
  have hdiffL : inner γ c \ starMap c γ '' A ⊆ L := by
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
    obtain ⟨t', ht'', s', hs', he⟩ := h.mem_inner_iff.1 hz
    have hs'0 : 0 < s' := by
      rcases eq_or_lt_of_le hs'.1 with e | e
      · exfalso; apply hzc; rw [he, ← e]; simp
      · exact e
    obtain ⟨-, hrs⟩ := h.eq_of_ray_eq ht' ht'' hr hs'0 he
    refine hzA ⟨⟨t, r⟩, ⟨⟨⟨lt_of_le_of_ne ht.1 (Ne.symm hτ.1), ht.2⟩, hτ.2.2⟩, hr,
      hrs ▸ hs'.2⟩, ?_⟩
    simp [starMap, segPt]
  have hAeq : starMap c γ '' A =ᵐ[volume] inner γ c := by
    have : starMap c γ '' A = inner γ c \ (inner γ c \ starMap c γ '' A) :=
      (sdiff_sdiff_cancel_left hsubI).symm
    rw [this]
    exact sdiff_null_ae_eq_self (measure_mono_null hdiffL hL0)
  -- assemble
  rw [green_radial hγ hU hPU hf hg h.closed, iterated_eq_setIntegral hγ hU hPU hf hg,
    setIntegral_congr_set (sdiff_null_ae_eq_self hN0).symm, hBA,
    h.insideOf_eq_inner, ← setIntegral_congr_set hAeq,
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

end IsStarPath

/-- **Green's theorem for polar paths** `c + ρ(t) e^{2π i t}` with a positive `C¹` radius of
period `1` (convex or not). -/
@[kb "beck2025" "Theorem A.0.10, p. 167"]
theorem green_polarPath {c : ℂ} {ρ : ℝ → ℝ} {U : Set ℂ} {f g : ℂ → ℝ} (hρ : ContDiff ℝ 1 ρ)
    (hpos : ∀ t, 0 < ρ t) (h01 : ρ 0 = ρ 1) (hU : IsOpen U)
    (hKU : IsStarPath.inner (polarPath c ρ) c ∪ pathImage (polarPath c ρ) ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) (hg : ContDiffOn ℝ 1 g U) :
    lineIntegral f g (polarPath c ρ) =
      ∫ z in insideOf (polarPath c ρ), (fderiv ℝ g z 1 - fderiv ℝ f z I) := by
  have hc : ContDiff ℝ 1 (polarPath c ρ) := by
    unfold polarPath
    have h1 : ContDiff ℝ 1 (fun t => ((ρ t : ℝ) : ℂ)) := ofRealCLM.contDiff.comp hρ
    have h2 : ContDiff ℝ 1 (fun t : ℝ => exp (((2 * π * t : ℝ) : ℂ) * I)) :=
      Complex.contDiff_exp.comp ((ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).mul
        contDiff_const)
    exact contDiff_const.add (h1.mul h2)
  exact (isStarPath_polarPath hρ.continuous.continuousOn (fun t _ => hpos t) h01).green_star
    (IsC1On.isPiecewiseSmooth ⟨fun t _ => (hc.differentiable (by norm_num)).differentiableAt,
      (hc.continuous_deriv le_rfl).continuousOn⟩ zero_le_one) hU hKU hf hg

end UndergradKB.ComplexAnalysis
