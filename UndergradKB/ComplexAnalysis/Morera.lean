import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Complex.Harmonic.Poisson
import UndergradKB.ComplexAnalysis.Primitive
import UndergradKB.ComplexAnalysis.Harmonic
import UndergradKB.Common.Attr

/-! # Morera's theorem and strong extrema of `‖f‖` (rows CX-075, CX-088)

Morera's theorem on a region (via the antiderivative theorem of `Primitive.lean` and the fact that
derivatives of holomorphic functions are holomorphic), and the statement that the modulus of a
nowhere-vanishing holomorphic function has no strong relative extremum. -/

open Set Metric Filter Topology

namespace UndergradKB.ComplexAnalysis

/-- Beck Corollary 5.2.1 (CX-075), Morera's theorem. If `f` is continuous on the region `G` (open
and connected) and its integral over every closed polygonal path in `G` (made of horizontal and
vertical segments) vanishes, then `f` is holomorphic on `G`.  This has fewer hypotheses than the
book's version, which asks for all piecewise smooth closed paths. -/
@[kb "beck2025" "Corollary 5.2.1, p. 94"]
theorem differentiableOn_of_closed_integrals_zero {f : ℂ → ℂ} {G : Set ℂ} (hG : IsOpen G)
    (hconn : IsPreconnected G) (hf : ContinuousOn f G)
    (hcl : ∀ a I, HVPathIntegral G f a a I → I = 0) : DifferentiableOn ℂ f G := by
  obtain ⟨F, hF⟩ := exists_antiderivative_of_closed_integrals hG hconn hf hcl
  have hFd : DifferentiableOn ℂ F G := fun z hz => (hF z hz).differentiableAt.differentiableWithinAt
  refine (hFd.deriv hG).congr fun z hz => ?_
  exact (hF z hz).deriv.symm

theorem exists_near_eq {f : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hev : ∀ᶠ y in 𝓝 z₀, f y = f z₀) : ∃ y, y ≠ z₀ ∧ dist y z₀ < r ∧ f y = f z₀ := by
  have : ∀ᶠ y in 𝓝[≠] z₀, f y = f z₀ ∧ dist y z₀ < r ∧ y ≠ z₀ := by
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_eventually_nhds (ball_mem_nhds z₀ hr),
      self_mem_nhdsWithin] with y h1 h2 h3
    exact ⟨h1, mem_ball.1 h2, h3⟩
  obtain ⟨y, h1, h2, h3⟩ := this.exists
  exact ⟨y, h3, h2, h1⟩

/-- Beck Corollary 6.2.4 (CX-088). If `f` is holomorphic and nonzero on the open set `G`, then
`‖f‖` has neither a strong relative maximum nor a strong relative minimum at any point of `G`. -/
@[kb "beck2025" "Corollary 6.2.4, p. 107"]
theorem norm_no_strong_extremum {f : ℂ → ℂ} {G : Set ℂ} (hG : IsOpen G)
    (hf : DifferentiableOn ℂ f G) (hne : ∀ z ∈ G, f z ≠ 0) {z₀ : ℂ} (hz₀ : z₀ ∈ G) :
    ¬ HasStrongRelMax (fun z => ‖f z‖) z₀ ∧ ¬ HasStrongRelMin (fun z => ‖f z‖) z₀ := by
  have hd : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ f z :=
    Filter.eventually_of_mem (hG.mem_nhds hz₀) fun z hz => hf.differentiableAt (hG.mem_nhds hz)
  constructor
  · rintro ⟨r, hr, h⟩
    have hmax : IsLocalMax (norm ∘ f) z₀ := by
      filter_upwards [ball_mem_nhds z₀ hr] with z hz
      by_cases hzz : z = z₀
      · rw [hzz]
      · exact (h z hzz (mem_ball.1 hz)).le
    have hev := Complex.eventually_eq_of_isLocalMax_norm hd hmax
    obtain ⟨y, hy3, hy2, hy1⟩ := exists_near_eq hr hev
    have := h y hy3 hy2
    simp only [hy1] at this
    exact lt_irrefl _ this
  · rintro ⟨r, hr, h⟩
    have hmin : IsLocalMin (norm ∘ f) z₀ := by
      filter_upwards [ball_mem_nhds z₀ hr] with z hz
      by_cases hzz : z = z₀
      · rw [hzz]
      · exact (h z hzz (mem_ball.1 hz)).le
    rcases Complex.eventually_eq_or_eq_zero_of_isLocalMin_norm hd hmin with hev | h0
    · obtain ⟨y, hy3, hy2, hy1⟩ := exists_near_eq hr hev
      have := h y hy3 hy2
      simp only [hy1] at this
      exact lt_irrefl _ this
    · exact hne z₀ hz₀ h0

/-! ## The Dirichlet problem on the unit disc (CX-090) -/

/-- The Poisson integral of boundary data `φ` on the unit circle, extended by `φ` itself to the
points with `‖z‖ ≥ 1` (only its values on the closed unit disc matter). -/
noncomputable def poissonExtension (φ : ℂ → ℝ) (z : ℂ) : ℝ :=
  if ‖z‖ < 1 then Real.circleAverage (poissonKernel 0 z • φ) 0 1 else φ z

theorem circleIntegrable_of_continuousOn_sphere {φ : ℂ → ℝ} (hφ : ContinuousOn φ (sphere 0 1)) :
    CircleIntegrable φ 0 1 :=
  ContinuousOn.circleIntegrable' (by simpa using hφ)

/-- The Poisson integral of continuous boundary data is harmonic in the open unit disc. -/
theorem harmonicOnNhd_poissonExtension {φ : ℂ → ℝ} (hφ : ContinuousOn φ (sphere 0 1)) :
    InnerProductSpace.HarmonicOnNhd (poissonExtension φ) (ball 0 1) := by
  have hint := circleIntegrable_of_continuousOn_sphere hφ
  have hint' : CircleIntegrable (fun ζ => (φ ζ : ℂ)) 0 1 := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at hint ⊢
    exact Complex.ofRealCLM.integrable_comp hint
  have hFa := analyticOnNhd_circleAverage_herglotzRieszKernel_smul (R := 1) hint'
  intro z hz
  have hz1 : ‖z‖ < 1 := by simpa using hz
  have hnot : ∀ w ∈ ball (0:ℂ) 1, w ∉ sphere (0:ℂ) |1| := fun w hw hs => by
    rw [mem_sphere_iff_norm, abs_one, sub_zero] at hs
    rw [mem_ball_zero_iff] at hw
    linarith
  have hev : (fun w => (Real.circleAverage (fun ζ => herglotzRieszKernel 0 w ζ • (φ ζ : ℂ)) 0 1).re)
      =ᶠ[𝓝 z] poissonExtension φ := by
    filter_upwards [ball_mem_nhds z (show (0:ℝ) < 1 - ‖z‖ by linarith)] with w hw
    have hw1 : ‖w‖ < 1 := by
      have := mem_ball_iff_norm.1 hw
      have := norm_sub_norm_le w z
      linarith
    simp only [poissonExtension, hw1, ↓reduceIte]
    rw [re_circleAverage_herglotzRieszKernel_smul hint (hnot w (by simpa using hw1)),
      poissonKernel_eq_re_herglotzRieszKernel]
  have hh := AnalyticAt.harmonicAt_re (hFa z (hnot z hz))
  exact (InnerProductSpace.harmonicAt_congr_nhds hev).1 hh

theorem poisson_mean {g : ℂ → ℝ} (hg : InnerProductSpace.HarmonicOnNhd g (closedBall 0 1))
    {z : ℂ} (hz : ‖z‖ < 1) : Real.circleAverage (poissonKernel 0 z • g) 0 1 = g z :=
  InnerProductSpace.HarmonicOnNhd.circleAverage_poissonKernel_smul hg (mem_ball_zero_iff.2 hz)

theorem poissonKernel_nonneg' {z : ℂ} (hz : ‖z‖ < 1) {ζ : ℂ} (hζ : ζ ∈ sphere (0:ℂ) |1|) :
    0 ≤ poissonKernel 0 z ζ := by
  rw [mem_sphere_iff_norm, abs_one, sub_zero] at hζ
  rw [poissonKernel_def, sub_zero, sub_zero, hζ]
  refine div_nonneg ?_ (sq_nonneg _)
  nlinarith [norm_nonneg z]

theorem poissonKernel_continuousOn' {z : ℂ} (hz : ‖z‖ < 1) :
    ContinuousOn (poissonKernel 0 z) (sphere (0:ℂ) |1|) := by
  have hzs : z ∉ sphere (0:ℂ) |1| := fun hs => by
    rw [mem_sphere_iff_norm, abs_one, sub_zero] at hs
    linarith
  rw [poissonKernel_eq_re_herglotzRieszKernel]
  exact Complex.continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere hzs)

/-- Comparison: if boundary data `φ ≤ ψ` on the circle with `ψ` harmonic on the closed disc, the
Poisson integral of `φ` is `≤ ψ` in the open disc. -/
theorem poissonExtension_le {φ ψ : ℂ → ℝ} (hφ : ContinuousOn φ (sphere 0 1))
    (hψ : InnerProductSpace.HarmonicOnNhd ψ (closedBall 0 1))
    (hle : ∀ ζ ∈ sphere (0:ℂ) 1, φ ζ ≤ ψ ζ) {z : ℂ} (hz : ‖z‖ < 1) :
    poissonExtension φ z ≤ ψ z := by
  have hP := poissonKernel_continuousOn' hz
  have hφi := circleIntegrable_of_continuousOn_sphere hφ
  have hψi : CircleIntegrable ψ 0 1 := circleIntegrable_of_continuousOn_sphere
    (hψ.continuousOn.mono sphere_subset_closedBall)
  rw [← poisson_mean hψ hz]
  simp only [poissonExtension, hz, ↓reduceIte]
  refine Real.circleAverage_mono (hφi.continuousOn_smul hP) (hψi.continuousOn_smul hP) fun x hx => ?_
  simp only [smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (hle x (by simpa using hx)) (poissonKernel_nonneg' hz hx)

theorem le_poissonExtension {φ ψ : ℂ → ℝ} (hφ : ContinuousOn φ (sphere 0 1))
    (hψ : InnerProductSpace.HarmonicOnNhd ψ (closedBall 0 1))
    (hle : ∀ ζ ∈ sphere (0:ℂ) 1, ψ ζ ≤ φ ζ) {z : ℂ} (hz : ‖z‖ < 1) :
    ψ z ≤ poissonExtension φ z := by
  have hP := poissonKernel_continuousOn' hz
  have hφi := circleIntegrable_of_continuousOn_sphere hφ
  have hψi : CircleIntegrable ψ 0 1 := circleIntegrable_of_continuousOn_sphere
    (hψ.continuousOn.mono sphere_subset_closedBall)
  rw [← poisson_mean hψ hz]
  simp only [poissonExtension, hz, ↓reduceIte]
  refine Real.circleAverage_mono (hψi.continuousOn_smul hP) (hφi.continuousOn_smul hP) fun x hx => ?_
  simp only [smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (hle x (by simpa using hx)) (poissonKernel_nonneg' hz hx)

theorem harmonicOnNhd_affine_re (K₁ K₂ : ℝ) (a : ℂ) :
    InnerProductSpace.HarmonicOnNhd (fun ζ : ℂ => K₁ + K₂ * (ζ * (starRingEnd ℂ) a).re)
      (closedBall 0 1) := by
  intro x _
  have hre : InnerProductSpace.HarmonicAt (fun ζ : ℂ => (ζ * (starRingEnd ℂ) a).re) x :=
    AnalyticAt.harmonicAt_re (by fun_prop)
  have := (InnerProductSpace.harmonicAt_const (E := ℂ) K₁).add (hre.const_smul (c := K₂))
  simpa [Pi.add_def, smul_eq_mul] using this

theorem norm_sub_sq_eq {z₀ : ℂ} (hz₀ : ‖z₀‖ = 1) (w : ℂ) :
    ‖w - z₀‖ ^ 2 = ‖w‖ ^ 2 + 1 - 2 * (w * (starRingEnd ℂ) z₀).re := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_norm_sq, hz₀]
  ring

/-- Poisson estimate: if `|φ ζ - φ z₀| ≤ ε + C ‖ζ - z₀‖²` on the circle, then the Poisson integral
at `z` in the disc differs from `φ z₀` by at most `ε + C (‖z - z₀‖² + 1 - ‖z‖²)`. -/
theorem poissonExtension_sub_le {φ : ℂ → ℝ} (hφ : ContinuousOn φ (sphere 0 1)) {z₀ : ℂ}
    (hz₀ : ‖z₀‖ = 1) {ε C : ℝ}
    (hbd : ∀ ζ ∈ sphere (0:ℂ) 1, |φ ζ - φ z₀| ≤ ε + C * ‖ζ - z₀‖ ^ 2) {z : ℂ} (hz : ‖z‖ < 1) :
    |poissonExtension φ z - φ z₀| ≤ ε + C * (‖z - z₀‖ ^ 2 + (1 - ‖z‖ ^ 2)) := by
  have hsph : ∀ ζ ∈ sphere (0:ℂ) 1, ‖ζ - z₀‖ ^ 2 = 2 - 2 * (ζ * (starRingEnd ℂ) z₀).re := by
    intro ζ hζ
    rw [mem_sphere_zero_iff_norm] at hζ
    rw [norm_sub_sq_eq hz₀, hζ]; ring
  have hup := poissonExtension_le hφ (harmonicOnNhd_affine_re (φ z₀ + ε + 2 * C) (-2 * C) z₀)
    (fun ζ hζ => by
      have := (abs_le.1 (hbd ζ hζ)).2
      rw [hsph ζ hζ] at this
      linarith) hz
  have hlo := le_poissonExtension hφ (harmonicOnNhd_affine_re (φ z₀ - ε - 2 * C) (2 * C) z₀)
    (fun ζ hζ => by
      have := (abs_le.1 (hbd ζ hζ)).1
      rw [hsph ζ hζ] at this
      linarith) hz
  have hz2 := norm_sub_sq_eq hz₀ z
  rw [abs_le]
  have hk : ‖z - z₀‖ ^ 2 + (1 - ‖z‖ ^ 2) = 2 - 2 * (z * (starRingEnd ℂ) z₀).re := by linarith
  rw [hk]
  constructor <;> linarith

/-- The Poisson extension of continuous boundary data is continuous on the closed unit disc and
equals `φ` on the circle. -/
theorem poissonExtension_continuousOn {φ : ℂ → ℝ} (hφ : ContinuousOn φ (sphere 0 1)) :
    ContinuousOn (poissonExtension φ) (closedBall 0 1) := by
  intro z₀ hz₀
  by_cases hlt : ‖z₀‖ < 1
  · exact ((harmonicOnNhd_poissonExtension hφ).continuousOn.continuousAt
      (isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hlt))).continuousWithinAt
  have hz₀1 : ‖z₀‖ = 1 := le_antisymm (mem_closedBall_zero_iff.1 hz₀) (not_lt.1 hlt)
  have hz₀s : z₀ ∈ sphere (0:ℂ) 1 := mem_sphere_zero_iff_norm.2 hz₀1
  have hu₀ : poissonExtension φ z₀ = φ z₀ := by simp [poissonExtension, hlt]
  obtain ⟨M, hM⟩ := (isCompact_sphere (0:ℂ) 1).exists_bound_of_continuousOn hφ
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM z₀ hz₀s)
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  set e := ε / 3 with he
  have he0 : 0 < e := by positivity
  obtain ⟨δ₁, hδ₁, hcont⟩ := Metric.continuousWithinAt_iff.1 (hφ z₀ hz₀s) e he0
  set C : ℝ := 2 * M / δ₁ ^ 2 with hC
  have hC0 : 0 ≤ C := by positivity
  have hbd : ∀ ζ ∈ sphere (0:ℂ) 1, |φ ζ - φ z₀| ≤ e + C * ‖ζ - z₀‖ ^ 2 := by
    intro ζ hζ
    by_cases h : ‖ζ - z₀‖ < δ₁
    · have := hcont hζ (by rwa [dist_eq_norm])
      rw [Real.dist_eq] at this
      have : 0 ≤ C * ‖ζ - z₀‖ ^ 2 := by positivity
      linarith
    · rw [not_lt] at h
      have h1 : |φ ζ - φ z₀| ≤ 2 * M := by
        have a := hM ζ hζ
        have b := hM z₀ hz₀s
        rw [Real.norm_eq_abs] at a b
        calc |φ ζ - φ z₀| ≤ |φ ζ| + |φ z₀| := abs_sub _ _
          _ ≤ 2 * M := by linarith
      have h2 : 2 * M ≤ C * ‖ζ - z₀‖ ^ 2 := by
        have : C * δ₁ ^ 2 = 2 * M := by rw [hC]; field_simp
        rw [← this]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ₁.le h 2) hC0
      linarith
  set δ' := e / (3 * C + 1) with hδ'
  have hδ'0 : 0 < δ' := by positivity
  refine ⟨min δ₁ (min 1 δ'), lt_min hδ₁ (lt_min one_pos hδ'0), fun x hx hxd => ?_⟩
  have hd1 : dist x z₀ < δ₁ := lt_of_lt_of_le hxd (min_le_left _ _)
  have hd2 : dist x z₀ < 1 := lt_of_lt_of_le hxd ((min_le_right _ _).trans (min_le_left _ _))
  have hd3 : dist x z₀ < δ' := lt_of_lt_of_le hxd ((min_le_right _ _).trans (min_le_right _ _))
  rw [hu₀, Real.dist_eq]
  by_cases hxl : ‖x‖ < 1
  · have hest := poissonExtension_sub_le hφ hz₀1 hbd hxl
    rw [dist_eq_norm] at hd1 hd2 hd3
    set d := ‖x - z₀‖ with hd
    have hd0 : 0 ≤ d := norm_nonneg _
    have h1x : 1 - ‖x‖ ≤ d := by
      have := norm_sub_norm_le z₀ x
      rw [norm_sub_rev] at this
      linarith [hz₀1, norm_sub_rev z₀ x]
    have hk : d ^ 2 + (1 - ‖x‖ ^ 2) ≤ 3 * d := by
      nlinarith [norm_nonneg x]
    have hlt3 : d * (3 * C + 1) < e := by
      rwa [hδ', lt_div_iff₀ (by positivity)] at hd3
    have : C * (d ^ 2 + (1 - ‖x‖ ^ 2)) ≤ C * (3 * d) := mul_le_mul_of_nonneg_left hk hC0
    have hee : ε = 3 * e := by rw [he]; ring
    nlinarith
  · have hx1 : ‖x‖ = 1 := le_antisymm (mem_closedBall_zero_iff.1 hx) (not_lt.1 hxl)
    have hxs : x ∈ sphere (0:ℂ) 1 := mem_sphere_zero_iff_norm.2 hx1
    have := hcont hxs hd1
    rw [Real.dist_eq] at this
    have hux : poissonExtension φ x = φ x := by simp [poissonExtension, hxl]
    rw [hux]
    linarith

/-- Beck, Dirichlet problem on the unit disc (CX-090): for continuous boundary data `φ` on the unit
circle, the Poisson integral `u` is harmonic in the open disc, continuous on the closed disc,
and equals `φ` on the circle. -/
@[kb "beck2025" "Dirichlet problem, p. 107"]
theorem dirichlet_problem_unit_disc {φ : ℂ → ℝ} (hφ : ContinuousOn φ (sphere 0 1)) :
    InnerProductSpace.HarmonicOnNhd (poissonExtension φ) (ball 0 1) ∧
      ContinuousOn (poissonExtension φ) (closedBall 0 1) ∧
      ∀ z ∈ sphere (0:ℂ) 1, poissonExtension φ z = φ z := by
  refine ⟨harmonicOnNhd_poissonExtension hφ, poissonExtension_continuousOn hφ, fun z hz => ?_⟩
  have : ¬ ‖z‖ < 1 := by rw [mem_sphere_zero_iff_norm.1 hz]; exact lt_irrefl _
  simp [poissonExtension, this]

end UndergradKB.ComplexAnalysis
