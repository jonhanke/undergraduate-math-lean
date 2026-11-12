import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import UndergradKB.ComplexAnalysis.PathIntegral
import UndergradKB.Common.Attr

/-! # Cauchy's theorem for homotopic closed paths (rows CX-066, CX-067)

The G-homotopy of Beck's Definition 4.3.1, and Theorem 4.3.4 proved under the hypotheses of the
book's own proof: the homotopy is of class C² (on the whole plane) and the closedness condition
`h 0 s = h 1 s` holds for `s` in `[0,1]`.  Differentiation under the integral sign is replaced by
the fundamental theorem of calculus in each variable together with Fubini, applied to the two
expressions `∂ₛ(f(h) hₜ)` and `∂ₜ(f(h) hₛ)`, which agree by symmetry of the second derivative. -/

open Set MeasureTheory intervalIntegral Filter Topology

namespace UndergradKB.ComplexAnalysis

section C2

variable {H : ℝ × ℝ → ℂ}

lemma hasDerivAt_line_s {φ : ℝ × ℝ → ℂ} {φ' : ℝ × ℝ →L[ℝ] ℂ} {t s : ℝ}
    (h : HasFDerivAt φ φ' (t, s)) : HasDerivAt (fun s' => φ (t, s')) (φ' (0, 1)) s :=
  h.comp_hasDerivAt s ((hasDerivAt_const s t).prodMk (hasDerivAt_id s))

lemma hasDerivAt_line_t {φ : ℝ × ℝ → ℂ} {φ' : ℝ × ℝ →L[ℝ] ℂ} {t s : ℝ}
    (h : HasFDerivAt φ φ' (t, s)) : HasDerivAt (fun t' => φ (t', s)) (φ' (1, 0)) t :=
  h.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t s))

lemma hasFDerivAt_fderiv (hH : ContDiff ℝ 2 H) (p : ℝ × ℝ) :
    HasFDerivAt (fderiv ℝ H) (fderiv ℝ (fderiv ℝ H) p) p :=
  ((hH.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) p).hasFDerivAt

lemma hasFDerivAt_eval (hH : ContDiff ℝ 2 H) (v : ℝ × ℝ) (p : ℝ × ℝ) :
    HasFDerivAt (fun q => fderiv ℝ H q v)
      ((ContinuousLinearMap.apply ℝ ℂ v).comp (fderiv ℝ (fderiv ℝ H) p)) p :=
  (ContinuousLinearMap.apply ℝ ℂ v).hasFDerivAt.comp p (hasFDerivAt_fderiv hH p)

variable {f : ℂ → ℂ}

lemma hasFDerivAt_comp (hH : ContDiff ℝ 2 H) {p : ℝ × ℝ} (hf : DifferentiableAt ℂ f (H p)) :
    HasFDerivAt (fun q => f (H q)) (deriv f (H p) • fderiv ℝ H p) p :=
  hf.hasDerivAt.comp_hasFDerivAt p ((hH.differentiable (by norm_num) p).hasFDerivAt)

lemma hasDerivAt_P_s (hH : ContDiff ℝ 2 H) {t s : ℝ} (hf : DifferentiableAt ℂ f (H (t, s))) :
    HasDerivAt (fun s' => f (H (t, s')) * fderiv ℝ H (t, s') (1, 0))
      ((deriv f (H (t, s)) * fderiv ℝ H (t, s) (0, 1)) * fderiv ℝ H (t, s) (1, 0) +
        f (H (t, s)) * fderiv ℝ (fderiv ℝ H) (t, s) (0, 1) (1, 0)) s := by
  have h1 := hasDerivAt_line_s (hasFDerivAt_comp hH hf)
  have h2 := hasDerivAt_line_s (hasFDerivAt_eval hH (1, 0) (t, s))
  refine HasDerivAt.congr_deriv (h1.mul h2) ?_
  simp

lemma hasDerivAt_Q_t (hH : ContDiff ℝ 2 H) {t s : ℝ} (hf : DifferentiableAt ℂ f (H (t, s))) :
    HasDerivAt (fun t' => f (H (t', s)) * fderiv ℝ H (t', s) (0, 1))
      ((deriv f (H (t, s)) * fderiv ℝ H (t, s) (1, 0)) * fderiv ℝ H (t, s) (0, 1) +
        f (H (t, s)) * fderiv ℝ (fderiv ℝ H) (t, s) (1, 0) (0, 1)) t := by
  have h1 := hasDerivAt_line_t (hasFDerivAt_comp hH hf)
  have h2 := hasDerivAt_line_t (hasFDerivAt_eval hH (0, 1) (t, s))
  refine HasDerivAt.congr_deriv (h1.mul h2) ?_
  simp

lemma deriv_slice_t (hH : ContDiff ℝ 2 H) (t s : ℝ) :
    deriv (fun t' => H (t', s)) t = fderiv ℝ H (t, s) (1, 0) :=
  (hasDerivAt_line_t ((hH.differentiable (by norm_num) (t, s)).hasFDerivAt)).deriv

lemma deriv_slice_s (hH : ContDiff ℝ 2 H) (t s : ℝ) :
    deriv (fun s' => H (t, s')) s = fderiv ℝ H (t, s) (0, 1) :=
  (hasDerivAt_line_s ((hH.differentiable (by norm_num) (t, s)).hasFDerivAt)).deriv

lemma symm_second (hH : ContDiff ℝ 2 H) (p : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ H) p (0, 1) (1, 0) = fderiv ℝ (fderiv ℝ H) p (1, 0) (0, 1) := by
  have := (hH.contDiffAt (x := p)).isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField])
  exact this _ _

lemma integral_swap_of_continuousOn {g : ℝ × ℝ → ℂ}
    (hg : ContinuousOn g (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1)) :
    ∫ t in (0:ℝ)..1, ∫ s in (0:ℝ)..1, g (t, s) = ∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1, g (t, s) := by
  simp only [intervalIntegral.integral_of_le zero_le_one]
  have hint : Integrable (Function.uncurry fun t s => g (t, s))
      ((volume.restrict (Ioc (0:ℝ) 1)).prod (volume.restrict (Ioc (0:ℝ) 1))) := by
    rw [Measure.prod_restrict]
    exact (hg.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  exact integral_integral_swap hint

theorem cauchy_C2_core {f : ℂ → ℂ} {G : Set ℂ} (hG : IsOpen G) (hf : DifferentiableOn ℂ f G)
    (hH : ContDiff ℝ 2 H) (hmem : ∀ t ∈ Icc (0:ℝ) 1, ∀ s ∈ Icc (0:ℝ) 1, H (t, s) ∈ G)
    (hclosed : ∀ s ∈ Icc (0:ℝ) 1, H (0, s) = H (1, s)) :
    ∫ t in (0:ℝ)..1, f (H (t, 0)) * fderiv ℝ H (t, 0) (1, 0) =
      ∫ t in (0:ℝ)..1, f (H (t, 1)) * fderiv ℝ H (t, 1) (1, 0) := by
  set S : Set (ℝ × ℝ) := Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1 with hS
  have hSmem : ∀ p ∈ S, H p ∈ G := fun p hp => hmem p.1 hp.1 p.2 hp.2
  have hdf : ∀ p ∈ S, DifferentiableAt ℂ f (H p) := fun p hp =>
    hf.differentiableAt (hG.mem_nhds (hSmem p hp))
  have hHc : Continuous H := hH.continuous
  have hD : ∀ v, Continuous (fun p => fderiv ℝ H p v) := fun v =>
    (hH.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hE : Continuous (fderiv ℝ (fderiv ℝ H)) :=
    (hH.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have hE' : ∀ v w, Continuous fun p => fderiv ℝ (fderiv ℝ H) p v w := fun v w =>
    (hE.clm_apply continuous_const).clm_apply continuous_const
  have hfH : ContinuousOn (fun p => f (H p)) S :=
    hf.continuousOn.comp hHc.continuousOn (fun p hp => hSmem p hp)
  have hf'H : ContinuousOn (fun p => deriv f (H p)) S :=
    (hf.deriv hG).continuousOn.comp hHc.continuousOn (fun p hp => hSmem p hp)
  set dP : ℝ × ℝ → ℂ := fun p => (deriv f (H p) * fderiv ℝ H p (0, 1)) * fderiv ℝ H p (1, 0) +
    f (H p) * fderiv ℝ (fderiv ℝ H) p (0, 1) (1, 0) with hdP
  set dQ : ℝ × ℝ → ℂ := fun p => (deriv f (H p) * fderiv ℝ H p (1, 0)) * fderiv ℝ H p (0, 1) +
    f (H p) * fderiv ℝ (fderiv ℝ H) p (1, 0) (0, 1) with hdQ
  have hPQ : ∀ p, dP p = dQ p := fun p => by
    simp only [hdP, hdQ, symm_second hH p]; ring
  have hdPc : ContinuousOn dP S :=
    ((hf'H.mul (hD _).continuousOn).mul (hD _).continuousOn).add
      (hfH.mul (hE' _ _).continuousOn)
  have hdQc : ContinuousOn dQ S := by
    have : dQ = dP := funext fun p => (hPQ p).symm
    rw [this]; exact hdPc
  have hline_s : ∀ t ∈ Icc (0:ℝ) 1, ContinuousOn (Prod.mk t) (Icc (0:ℝ) 1) := fun t _ =>
    (continuous_const.prodMk continuous_id).continuousOn
  have hline_t : ∀ s ∈ Icc (0:ℝ) 1, ContinuousOn (fun t : ℝ => (t, s)) (Icc (0:ℝ) 1) := fun s _ =>
    (continuous_id.prodMk continuous_const).continuousOn
  -- FTC in `s`
  have hA : ∀ t ∈ Icc (0:ℝ) 1, ∫ s in (0:ℝ)..1, dP (t, s) =
      f (H (t, 1)) * fderiv ℝ H (t, 1) (1, 0) - f (H (t, 0)) * fderiv ℝ H (t, 0) (1, 0) := by
    intro t ht
    refine integral_eq_sub_of_hasDerivAt (f := fun s => f (H (t, s)) * fderiv ℝ H (t, s) (1, 0))
      (fun s hs => ?_) ?_
    · rw [uIcc_of_le zero_le_one] at hs
      exact hasDerivAt_P_s hH (hdf (t, s) ⟨ht, hs⟩)
    · refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le zero_le_one]
      exact hdPc.comp (hline_s t ht) (fun s hs => ⟨ht, hs⟩)
  -- FTC in `t`
  have hB : ∀ s ∈ Icc (0:ℝ) 1, ∫ t in (0:ℝ)..1, dQ (t, s) =
      f (H (1, s)) * fderiv ℝ H (1, s) (0, 1) - f (H (0, s)) * fderiv ℝ H (0, s) (0, 1) := by
    intro s hs
    refine integral_eq_sub_of_hasDerivAt (f := fun t => f (H (t, s)) * fderiv ℝ H (t, s) (0, 1))
      (fun t ht => ?_) ?_
    · rw [uIcc_of_le zero_le_one] at ht
      exact hasDerivAt_Q_t hH (hdf (t, s) ⟨ht, hs⟩)
    · refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le zero_le_one]
      exact hdQc.comp (hline_t s hs) (fun t ht => ⟨ht, hs⟩)
  -- the boundary term vanishes
  have hD2 : ∀ s ∈ Icc (0:ℝ) 1, fderiv ℝ H (0, s) (0, 1) = fderiv ℝ H (1, s) (0, 1) := by
    have hIoo : ∀ s ∈ Ioo (0:ℝ) 1, fderiv ℝ H (0, s) (0, 1) = fderiv ℝ H (1, s) (0, 1) := by
      intro s hs
      rw [← deriv_slice_s hH, ← deriv_slice_s hH]
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [Ioo_mem_nhds hs.1 hs.2] with s' hs'
      exact hclosed s' (Ioo_subset_Icc_self hs')
    have hc0 : ContinuousOn (fun s => fderiv ℝ H (0, s) (0, 1)) (Icc 0 1) :=
      ((hD _).comp (continuous_const.prodMk continuous_id)).continuousOn
    have hc1 : ContinuousOn (fun s => fderiv ℝ H (1, s) (0, 1)) (Icc 0 1) :=
      ((hD _).comp (continuous_const.prodMk continuous_id)).continuousOn
    exact Set.EqOn.of_subset_closure hIoo hc0 hc1 Ioo_subset_Icc_self
      (by rw [closure_Ioo zero_ne_one])
  have hbd : ∀ s ∈ Icc (0:ℝ) 1, ∫ t in (0:ℝ)..1, dQ (t, s) = 0 := by
    intro s hs
    rw [hB s hs, hclosed s hs, hD2 s hs, sub_self]
  -- assemble
  have hcontP : ∀ s ∈ Icc (0:ℝ) 1, IntervalIntegrable
      (fun t => f (H (t, s)) * fderiv ℝ H (t, s) (1, 0)) volume 0 1 := by
    intro s hs
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact (hfH.mul (hD _).continuousOn).comp (hline_t s hs) (fun t ht => ⟨ht, hs⟩)
  have h1 : ∫ t in (0:ℝ)..1, ∫ s in (0:ℝ)..1, dP (t, s) =
      (∫ t in (0:ℝ)..1, f (H (t, 1)) * fderiv ℝ H (t, 1) (1, 0)) -
        ∫ t in (0:ℝ)..1, f (H (t, 0)) * fderiv ℝ H (t, 0) (1, 0) := by
    rw [← integral_sub (hcontP 1 ⟨zero_le_one, le_rfl⟩) (hcontP 0 ⟨le_rfl, zero_le_one⟩)]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le zero_le_one] at ht
    exact hA t ht
  have h2 : ∫ t in (0:ℝ)..1, ∫ s in (0:ℝ)..1, dP (t, s) = 0 := by
    rw [integral_swap_of_continuousOn hdPc]
    have : ∀ s ∈ uIcc (0:ℝ) 1, ∫ t in (0:ℝ)..1, dP (t, s) = 0 := by
      intro s hs
      rw [uIcc_of_le zero_le_one] at hs
      have := hbd s hs
      rw [← this]; congr 1; ext t; exact hPQ _
    rw [intervalIntegral.integral_congr this]
    simp
  rw [h2] at h1
  exact (sub_eq_zero.1 h1.symm).symm

end C2

/-- Beck Definition 4.3.1 (CX-066). The closed paths `γ₀, γ₁ : ℝ → ℂ` (parametrised on `[0,1]`) are
`G`-homotopic: there is a continuous `h : [0,1]² → G` with `h(t,0) = γ₀ t`, `h(t,1) = γ₁ t` and
`h(0,s) = h(1,s)`. -/
@[kb "beck2025" "Definition 4.3.1, p. 77"]
def IsGHomotopic (G : Set ℂ) (γ₀ γ₁ : ℝ → ℂ) : Prop :=
  ∃ h : ℝ → ℝ → ℂ, ContinuousOn (fun p : ℝ × ℝ => h p.1 p.2) (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) ∧
    (∀ t ∈ Icc (0:ℝ) 1, ∀ s ∈ Icc (0:ℝ) 1, h t s ∈ G) ∧
    (∀ t ∈ Icc (0:ℝ) 1, h t 0 = γ₀ t) ∧ (∀ t ∈ Icc (0:ℝ) 1, h t 1 = γ₁ t) ∧
    (∀ s ∈ Icc (0:ℝ) 1, h 0 s = h 1 s)

/-- The `C²` version of the homotopy of Definition 4.3.1 used in the book's proof of Cauchy's
theorem: `h` is twice continuously differentiable on the plane, and `γᵢ t = h t i`. -/
@[kb "beck2025" "Definition 4.3.1, p. 77"]
def IsC2Homotopic (G : Set ℂ) (γ₀ γ₁ : ℝ → ℂ) : Prop :=
  ∃ h : ℝ → ℝ → ℂ, ContDiff ℝ 2 (fun p : ℝ × ℝ => h p.1 p.2) ∧
    (∀ t ∈ Icc (0:ℝ) 1, ∀ s ∈ Icc (0:ℝ) 1, h t s ∈ G) ∧
    γ₀ = (fun t => h t 0) ∧ γ₁ = (fun t => h t 1) ∧ (∀ s ∈ Icc (0:ℝ) 1, h 0 s = h 1 s)

/-- A `C²` homotopy is a homotopy. -/
theorem IsC2Homotopic.isGHomotopic {G : Set ℂ} {γ₀ γ₁ : ℝ → ℂ} (h : IsC2Homotopic G γ₀ γ₁) :
    IsGHomotopic G γ₀ γ₁ := by
  obtain ⟨h, hc, hG, rfl, rfl, hcl⟩ := h
  exact ⟨h, hc.continuous.continuousOn, hG, fun _ _ => rfl, fun _ _ => rfl, hcl⟩

/-- Beck Theorem 4.3.4 (CX-067), Cauchy's theorem for homotopic closed paths, under the hypotheses
of the book's proof: `f` is holomorphic on the open set `G` and the homotopy `h` is of class `C²` on
the plane (with values in `G` on `[0,1]²` and `h 0 s = h 1 s` for `s ∈ [0,1]`).  Then
`∫_{γ₀} f = ∫_{γ₁} f`, where `γ₀ = h(·,0)` and `γ₁ = h(·,1)`.  (The book also allows a piecewise `C²`
homotopy and a merely piecewise smooth path; those cases are not covered.) -/
@[kb "beck2025" "Theorem 4.3.4, p. 78"]
theorem cauchy_theorem_C2_homotopy {f : ℂ → ℂ} {G : Set ℂ} (hG : IsOpen G)
    (hf : DifferentiableOn ℂ f G) {γ₀ γ₁ : ℝ → ℂ} (hh : IsC2Homotopic G γ₀ γ₁) :
    pathIntegral f γ₀ 0 1 = pathIntegral f γ₁ 0 1 := by
  obtain ⟨h, hc, hmem, rfl, rfl, hcl⟩ := hh
  have key := cauchy_C2_core (H := fun p : ℝ × ℝ => h p.1 p.2) hG hf hc hmem hcl
  unfold pathIntegral
  have e : ∀ s t : ℝ, deriv (fun t => h t s) t = fderiv ℝ (fun p : ℝ × ℝ => h p.1 p.2) (t, s) (1, 0) :=
    fun s t => deriv_slice_t hc t s
  simp only [e]
  exact key

end UndergradKB.ComplexAnalysis
