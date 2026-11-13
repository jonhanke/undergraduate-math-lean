import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import UndergradKB.ComplexAnalysis.PathIntegral

/-!
# Piecewise smooth paths (rows CX-056, CX-062, CX-067)

Beck et al. integrate along *piecewise smooth* paths: continuous paths made of finitely many `C¹`
pieces. Here such a path on `[a, b]` is encoded by `IsPiecewiseSmooth γ a b`: `γ` is continuous on
`[a, b]`, and off a finite set of corners it is differentiable in `(a, b)` with continuous derivative,
the derivative being bounded on `[a, b]`. Every path made of finitely many `C¹` pieces has this
property, so results proved for it hold for the book's paths. The contour integral is still
`pathIntegral f γ a b` (the corners have measure zero).

Proved here: `C¹` paths are piecewise smooth, the fundamental theorem of calculus for piecewise smooth
paths (Theorem 4.2.5), constant paths, and concatenation `γ₁ + γ₂` of two paths parametrised on
`[0, 1]` with additivity of the integral.
-/

open Set Filter Topology MeasureTheory intervalIntegral

namespace UndergradKB.ComplexAnalysis

/-- A piecewise smooth path on `[a, b]`: continuous on `[a, b]`, differentiable with continuous
derivative on `(a, b)` off a finite set, with bounded derivative on `[a, b]`. -/
def IsPiecewiseSmooth (γ : ℝ → ℂ) (a b : ℝ) : Prop :=
  ContinuousOn γ (Icc a b) ∧ ∃ S : Finset ℝ, (∀ t ∈ Ioo a b, t ∉ S → DifferentiableAt ℝ γ t) ∧
    ContinuousOn (deriv γ) (Ioo a b \ ↑S) ∧ ∃ M : ℝ, ∀ t ∈ Icc a b, ‖deriv γ t‖ ≤ M

namespace IsPiecewiseSmooth

variable {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ}

lemma continuousOn (h : IsPiecewiseSmooth γ a b) : ContinuousOn γ (Icc a b) := h.1

lemma mono (h : IsPiecewiseSmooth γ a b) {u v : ℝ} (hu : a ≤ u) (hv : v ≤ b) :
    IsPiecewiseSmooth γ u v := by
  obtain ⟨hc, S, hd, hdc, M, hM⟩ := h
  have hI : Icc u v ⊆ Icc a b := Icc_subset_Icc hu hv
  have hO : Ioo u v ⊆ Ioo a b := Ioo_subset_Ioo hu hv
  exact ⟨hc.mono hI, S, fun t ht htS => hd t (hO ht) htS, hdc.mono (sdiff_subset_sdiff_left hO), M,
    fun t ht => hM t (hI ht)⟩

lemma intervalIntegrable_deriv (h : IsPiecewiseSmooth γ a b) (hab : a ≤ b) :
    IntervalIntegrable (deriv γ) volume a b := by
  obtain ⟨-, -, -, -, M, hM⟩ := h
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  exact Measure.integrableOn_of_bounded measure_Icc_lt_top.ne
    (measurable_deriv γ).aestronglyMeasurable (ae_restrict_of_forall_mem measurableSet_Icc hM)

lemma intervalIntegrable_integrand (h : IsPiecewiseSmooth γ a b) (hab : a ≤ b)
    (hf : ContinuousOn f (γ '' Icc a b)) :
    IntervalIntegrable (fun t => f (γ t) * deriv γ t) volume a b := by
  refine (h.intervalIntegrable_deriv hab).continuousOn_mul ?_
  rw [uIcc_of_le hab]
  exact hf.comp h.continuousOn (mapsTo_image γ _)

end IsPiecewiseSmooth

variable {f : ℂ → ℂ} {γ γ₁ γ₂ : ℝ → ℂ} {a b : ℝ}

/-- A `C¹` path is piecewise smooth. -/
theorem IsC1On.isPiecewiseSmooth (h : IsC1On γ a b) (hab : a ≤ b) : IsPiecewiseSmooth γ a b := by
  have hI : uIcc a b = Icc a b := uIcc_of_le hab
  obtain ⟨M, hM⟩ := isCompact_uIcc.exists_bound_of_continuousOn h.2
  refine ⟨hI ▸ h.continuousOn, ∅, fun t ht _ => h.1 t (hI ▸ Ioo_subset_Icc_self ht), ?_, M,
    fun t ht => hM t (hI ▸ ht)⟩
  exact h.2.mono (fun t ht => hI ▸ Ioo_subset_Icc_self ht.1)

/-- Beck Theorem 4.2.5 (CX-062) for piecewise smooth paths: if `F' = f` on a set `U` containing the
path and `f` is continuous on `U`, then `∫_γ f = F (γ b) - F (γ a)`. -/
@[kb "beck2025" "Theorem 4.2.5, p. 75"]
theorem pathIntegral_eq_sub_of_isPiecewiseSmooth {F : ℂ → ℂ} {U : Set ℂ}
    (hγ : IsPiecewiseSmooth γ a b) (hab : a ≤ b) (hsub : ∀ t ∈ Icc a b, γ t ∈ U)
    (hF : ∀ z ∈ U, HasDerivAt F (f z) z) (hf : ContinuousOn f U) :
    pathIntegral f γ a b = F (γ b) - F (γ a) := by
  have hFc : ContinuousOn F U := fun z hz => (hF z hz).continuousAt.continuousWithinAt
  have hfc : ContinuousOn f (γ '' Icc a b) := hf.mono (by rintro _ ⟨t, ht, rfl⟩; exact hsub t ht)
  obtain ⟨S, hd, -, -⟩ := hγ.2
  unfold pathIntegral
  refine integral_eq_of_hasDerivAt_off_countable_of_le (fun t => F (γ t)) _ hab
    S.countable_toSet (hFc.comp hγ.continuousOn hsub) (fun t ht => ?_)
    (hγ.intervalIntegrable_integrand hab hfc)
  have h2 : HasDerivAt (fun t => F (γ t)) (deriv γ t • f (γ t)) t :=
    (hF _ (hsub t (Ioo_subset_Icc_self ht.1))).scomp t (hd t ht.1 ht.2).hasDerivAt
  rwa [smul_eq_mul, mul_comm] at h2

/-- Corollary 4.2.7 (CX-063) for piecewise smooth paths: a function with an antiderivative on a set
containing the closed path has integral zero along it. -/
@[kb "beck2025" "Corollary 4.2.7, p. 75"]
theorem pathIntegral_eq_zero_of_closed_of_isPiecewiseSmooth {F : ℂ → ℂ} {U : Set ℂ}
    (hγ : IsPiecewiseSmooth γ a b) (hab : a ≤ b) (hsub : ∀ t ∈ Icc a b, γ t ∈ U)
    (hF : ∀ z ∈ U, HasDerivAt F (f z) z) (hf : ContinuousOn f U) (hclosed : γ a = γ b) :
    pathIntegral f γ a b = 0 := by
  rw [pathIntegral_eq_sub_of_isPiecewiseSmooth hγ hab hsub hF hf, hclosed, sub_self]

/-! ### Constant paths -/

/-- A constant path is piecewise smooth. -/
theorem isPiecewiseSmooth_const (c : ℂ) (a b : ℝ) : IsPiecewiseSmooth (fun _ => c) a b :=
  ⟨continuousOn_const, ∅, fun _ _ _ => differentiableAt_const c,
    by simpa using continuousOn_const, 0, fun t _ => by simp⟩

/-- The integral along a constant path vanishes. -/
@[simp]
theorem pathIntegral_const_path (c : ℂ) (a b : ℝ) : pathIntegral f (fun _ => c) a b = 0 := by
  simp [pathIntegral]

/-! ### Concatenation -/

/-- Beck's sum `γ₁ + γ₂` of two paths parametrised on `[0, 1]`: first `γ₁` at double speed, then
`γ₂`. -/
noncomputable def pathConcat (γ₁ γ₂ : ℝ → ℂ) (t : ℝ) : ℂ :=
  if t ≤ 1 / 2 then γ₁ (2 * t) else γ₂ (2 * t - 1)

lemma pathConcat_of_le {t : ℝ} (ht : t ≤ 1 / 2) : pathConcat γ₁ γ₂ t = γ₁ (2 * t) := if_pos ht

lemma pathConcat_of_lt {t : ℝ} (ht : 1 / 2 < t) : pathConcat γ₁ γ₂ t = γ₂ (2 * t - 1) :=
  if_neg (not_le.2 ht)

@[simp] lemma pathConcat_zero : pathConcat γ₁ γ₂ 0 = γ₁ 0 := by
  rw [pathConcat_of_le (by norm_num), mul_zero]

@[simp] lemma pathConcat_one : pathConcat γ₁ γ₂ 1 = γ₂ 1 := by
  rw [pathConcat_of_lt (by norm_num)]; norm_num

lemma pathConcat_eventuallyEq_left {t : ℝ} (ht : t < 1 / 2) :
    pathConcat γ₁ γ₂ =ᶠ[𝓝 t] fun u => γ₁ (2 * u) := by
  filter_upwards [Iio_mem_nhds ht] with u hu using pathConcat_of_le (le_of_lt hu)

lemma pathConcat_eventuallyEq_right {t : ℝ} (ht : 1 / 2 < t) :
    pathConcat γ₁ γ₂ =ᶠ[𝓝 t] fun u => γ₂ (2 * u - 1) := by
  filter_upwards [Ioi_mem_nhds ht] with u hu using pathConcat_of_lt hu

lemma deriv_comp_two_mul_sub_one (g : ℝ → ℂ) (u : ℝ) :
    deriv (fun u => g (2 * u - 1)) u = 2 * deriv g (2 * u - 1) := by
  have h := deriv_comp_mul_left (f := fun v => g (v - 1)) (c := (2 : ℝ)) (x := u)
  rw [h, deriv_comp_sub_const, Complex.real_smul, Complex.ofReal_ofNat]

lemma deriv_comp_two_mul (g : ℝ → ℂ) (u : ℝ) :
    deriv (fun u => g (2 * u)) u = 2 * deriv g (2 * u) := by
  rw [deriv_comp_mul_left (f := g) (c := (2 : ℝ)), Complex.real_smul, Complex.ofReal_ofNat]

lemma deriv_pathConcat_of_lt {t : ℝ} (ht : t < 1 / 2) :
    deriv (pathConcat γ₁ γ₂) t = 2 * deriv γ₁ (2 * t) := by
  rw [(pathConcat_eventuallyEq_left ht).deriv_eq, deriv_comp_two_mul]

lemma deriv_pathConcat_of_gt {t : ℝ} (ht : 1 / 2 < t) :
    deriv (pathConcat γ₁ γ₂) t = 2 * deriv γ₂ (2 * t - 1) := by
  rw [(pathConcat_eventuallyEq_right ht).deriv_eq, deriv_comp_two_mul_sub_one]

lemma eventuallyEq_deriv_pathConcat_left {t : ℝ} (ht : t < 1 / 2) :
    deriv (pathConcat γ₁ γ₂) =ᶠ[𝓝 t] fun u => 2 * deriv γ₁ (2 * u) := by
  filter_upwards [Iio_mem_nhds ht] with u hu using deriv_pathConcat_of_lt hu

lemma eventuallyEq_deriv_pathConcat_right {t : ℝ} (ht : 1 / 2 < t) :
    deriv (pathConcat γ₁ γ₂) =ᶠ[𝓝 t] fun u => 2 * deriv γ₂ (2 * u - 1) := by
  filter_upwards [Ioi_mem_nhds ht] with u hu using deriv_pathConcat_of_gt hu

/-- The image of `[0, 1]` under `γ₁ + γ₂` lies in the union of the images. -/
lemma pathConcat_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    pathConcat γ₁ γ₂ t ∈ γ₁ '' Icc 0 1 ∪ γ₂ '' Icc 0 1 := by
  by_cases h : t ≤ 1 / 2
  · rw [pathConcat_of_le h]
    exact Or.inl ⟨2 * t, ⟨by linarith [ht.1], by linarith⟩, rfl⟩
  · rw [pathConcat_of_lt (not_le.1 h)]
    exact Or.inr ⟨2 * t - 1, ⟨by linarith, by linarith [ht.2]⟩, rfl⟩

/-- The sum of two piecewise smooth paths on `[0, 1]` (with `γ₁ 1 = γ₂ 0`) is piecewise smooth. -/
theorem IsPiecewiseSmooth.pathConcat (h₁ : IsPiecewiseSmooth γ₁ 0 1)
    (h₂ : IsPiecewiseSmooth γ₂ 0 1) (h : γ₁ 1 = γ₂ 0) :
    IsPiecewiseSmooth (pathConcat γ₁ γ₂) 0 1 := by
  obtain ⟨hc₁, S₁, hd₁, hdc₁, M₁, hM₁⟩ := h₁
  obtain ⟨hc₂, S₂, hd₂, hdc₂, M₂, hM₂⟩ := h₂
  classical
  refine ⟨?_, S₁.image (fun u => u / 2) ∪ S₂.image (fun u => (u + 1) / 2) ∪ {1 / 2}, ?_, ?_, ?_⟩
  · -- continuity, from the two closed halves
    have hL : ContinuousOn (UndergradKB.ComplexAnalysis.pathConcat γ₁ γ₂) (Icc 0 (1 / 2)) := by
      have : ContinuousOn (fun u : ℝ => γ₁ (2 * u)) (Icc 0 (1 / 2)) :=
        hc₁.comp (continuous_const.mul continuous_id).continuousOn
          (fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩)
      exact this.congr (fun u hu => pathConcat_of_le hu.2)
    have hR : ContinuousOn (UndergradKB.ComplexAnalysis.pathConcat γ₁ γ₂) (Icc (1 / 2) 1) := by
      have : ContinuousOn (fun u : ℝ => γ₂ (2 * u - 1)) (Icc (1 / 2) 1) :=
        hc₂.comp ((continuous_const.mul continuous_id).sub continuous_const).continuousOn
          (fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩)
      refine this.congr (fun u hu => ?_)
      rcases eq_or_lt_of_le hu.1 with e | e
      · subst e
        rw [pathConcat_of_le le_rfl]
        norm_num [h]
      · exact pathConcat_of_lt e
    have := hL.union_of_isClosed hR isClosed_Icc isClosed_Icc
    rwa [Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)] at this
  · intro t ht htS
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton, not_or] at htS
    obtain ⟨⟨hS₁, hS₂⟩, h12⟩ := htS
    rcases lt_or_gt_of_ne h12 with hlt | hgt
    · have hm : 2 * t ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith⟩
      have hn : 2 * t ∉ S₁ := fun hm' => hS₁ ⟨2 * t, hm', by ring⟩
      have : DifferentiableAt ℝ (fun u : ℝ => γ₁ (2 * u)) t :=
        (hd₁ _ hm hn).comp t ((differentiableAt_id.const_mul 2))
      exact this.congr_of_eventuallyEq (pathConcat_eventuallyEq_left hlt)
    · have hm : 2 * t - 1 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith [ht.2]⟩
      have hn : 2 * t - 1 ∉ S₂ := fun hm' => hS₂ ⟨2 * t - 1, hm', by ring⟩
      have : DifferentiableAt ℝ (fun u : ℝ => γ₂ (2 * u - 1)) t :=
        (hd₂ _ hm hn).comp t ((differentiableAt_id.const_mul 2).sub_const 1)
      exact this.congr_of_eventuallyEq (pathConcat_eventuallyEq_right hgt)
  · refine fun t ht => ContinuousAt.continuousWithinAt ?_
    obtain ⟨ht, htS⟩ := ht
    simp only [Finset.coe_union, Finset.coe_image, Finset.coe_singleton, mem_union, mem_image,
      Finset.mem_coe, mem_singleton_iff, not_or] at htS
    obtain ⟨⟨hS₁, hS₂⟩, h12⟩ := htS
    have hopen : ∀ S : Finset ℝ, IsOpen (Ioo (0 : ℝ) 1 \ ↑S) := fun S =>
      isOpen_Ioo.sdiff S.finite_toSet.isClosed
    rcases lt_or_gt_of_ne h12 with hlt | hgt
    · have hm : 2 * t ∈ Ioo (0 : ℝ) 1 \ ↑S₁ :=
        ⟨⟨by linarith [ht.1], by linarith⟩, fun hm' => hS₁ ⟨2 * t, hm', by ring⟩⟩
      have hca : ContinuousAt (deriv γ₁) (2 * t) := hdc₁.continuousAt ((hopen S₁).mem_nhds hm)
      have : ContinuousAt (fun u : ℝ => 2 * deriv γ₁ (2 * u)) t :=
        continuousAt_const.mul (ContinuousAt.comp (g := deriv γ₁) (f := fun u : ℝ => 2 * u) hca
          (by fun_prop))
      exact this.congr (eventuallyEq_deriv_pathConcat_left hlt).symm
    · have hm : 2 * t - 1 ∈ Ioo (0 : ℝ) 1 \ ↑S₂ :=
        ⟨⟨by linarith, by linarith [ht.2]⟩, fun hm' => hS₂ ⟨2 * t - 1, hm', by ring⟩⟩
      have hca : ContinuousAt (deriv γ₂) (2 * t - 1) := hdc₂.continuousAt ((hopen S₂).mem_nhds hm)
      have : ContinuousAt (fun u : ℝ => 2 * deriv γ₂ (2 * u - 1)) t :=
        continuousAt_const.mul (ContinuousAt.comp (g := deriv γ₂) (f := fun u : ℝ => 2 * u - 1) hca
          (by fun_prop))
      exact this.congr (eventuallyEq_deriv_pathConcat_right hgt).symm
  · refine ⟨max (max (2 * M₁) (2 * M₂)) ‖deriv (UndergradKB.ComplexAnalysis.pathConcat γ₁ γ₂) (1 / 2)‖,
      fun t ht => ?_⟩
    rcases lt_trichotomy t (1 / 2) with hlt | heq | hgt
    · rw [deriv_pathConcat_of_lt hlt, norm_mul]
      have := hM₁ (2 * t) ⟨by linarith [ht.1], by linarith⟩
      norm_num
      exact Or.inl (Or.inl (by linarith))
    · rw [heq]; exact le_max_right _ _
    · rw [deriv_pathConcat_of_gt hgt, norm_mul]
      have := hM₂ (2 * t - 1) ⟨by linarith, by linarith [ht.2]⟩
      norm_num
      exact Or.inl (Or.inr (by linarith))

lemma ae_ne_half : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 1 / 2 := by
  have : volume ({1 / 2} : Set ℝ) = 0 := measure_singleton _
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 this] with t ht using ht

/-- Beck Proposition 4.1.8 (CX-059) for the sum of two paths: the integral along `γ₁ + γ₂` is the sum
of the integrals (for `f` continuous on both paths). -/
@[kb "beck2025" "Proposition 4.1.8, p. 73"]
theorem pathIntegral_pathConcat (h₁ : IsPiecewiseSmooth γ₁ 0 1) (h₂ : IsPiecewiseSmooth γ₂ 0 1)
    (h : γ₁ 1 = γ₂ 0) (hf₁ : ContinuousOn f (γ₁ '' Icc 0 1)) (hf₂ : ContinuousOn f (γ₂ '' Icc 0 1)) :
    pathIntegral f (pathConcat γ₁ γ₂) 0 1 = pathIntegral f γ₁ 0 1 + pathIntegral f γ₂ 0 1 := by
  have hc := h₁.pathConcat h₂ h
  have hf : ContinuousOn f ((pathConcat γ₁ γ₂) '' Icc 0 1) :=
    (hf₁.union_of_isClosed hf₂ ((isCompact_Icc.image_of_continuousOn h₁.1).isClosed)
      ((isCompact_Icc.image_of_continuousOn h₂.1).isClosed)).mono
      (by rintro _ ⟨t, ht, rfl⟩; exact pathConcat_mem ht)
  have hint := hc.intervalIntegrable_integrand zero_le_one hf
  unfold pathIntegral
  have hs1 : uIcc (0 : ℝ) (1 / 2) ⊆ uIcc 0 1 := by
    rw [uIcc_of_le (by norm_num), uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl (by norm_num)
  have hs2 : uIcc (1 / 2 : ℝ) 1 ⊆ uIcc 0 1 := by
    rw [uIcc_of_le (by norm_num), uIcc_of_le zero_le_one]
    exact Icc_subset_Icc (by norm_num) le_rfl
  rw [← integral_add_adjacent_intervals (b := 1 / 2) (hint.mono_set hs1) (hint.mono_set hs2)]
  congr 1
  · have e : ∫ t in (0 : ℝ)..1 / 2, f (pathConcat γ₁ γ₂ t) * deriv (pathConcat γ₁ γ₂) t
        = ∫ t in (0 : ℝ)..1 / 2, 2 * (f (γ₁ (2 * t)) * deriv γ₁ (2 * t)) := by
      refine integral_congr_ae ?_
      filter_upwards [ae_ne_half] with t ht hmem
      rw [uIoc_of_le (by norm_num)] at hmem
      have hlt : t < 1 / 2 := lt_of_le_of_ne hmem.2 ht
      rw [pathConcat_of_le hmem.2, deriv_pathConcat_of_lt hlt]
      ring
    rw [e, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left (fun u => f (γ₁ u) * deriv γ₁ u) (two_ne_zero)]
    norm_num
    ring
  · have e : ∫ t in (1 / 2 : ℝ)..1, f (pathConcat γ₁ γ₂ t) * deriv (pathConcat γ₁ γ₂) t
        = ∫ t in (1 / 2 : ℝ)..1, 2 * (f (γ₂ (2 * t - 1)) * deriv γ₂ (2 * t - 1)) := by
      refine integral_congr_ae ?_
      filter_upwards [ae_ne_half] with t _ hmem
      rw [uIoc_of_le (by norm_num)] at hmem
      rw [pathConcat_of_lt hmem.1, deriv_pathConcat_of_gt hmem.1]
      ring
    rw [e, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_sub (fun u => f (γ₂ u) * deriv γ₂ u) (two_ne_zero) 1]
    norm_num
    ring

end UndergradKB.ComplexAnalysis
