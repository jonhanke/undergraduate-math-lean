import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.RingTheory.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import UndergradKB.Common.Attr
import UndergradKB.Geometry.HypTriangles

/-! # Hyperbolic area in the conformal disc model (Petrunin, Sections 9 and 20I)

The h-plane has curvature `-1` (book p. 90, p. 177): the area of an h-triangle is its defect `π - (α + β + γ)`.
Here the area is the Riemannian area of the conformal metric `2|dz|/(1-|z|²)` of the disc model (the conformal
factor of Lemma 13.13, p. 112), i.e. the measure `4/(1-|z|²)² dx dy` on the unit disc.

* `harea`: the hyperbolic area of a set of the plane (the density integral over its part in the unit disc);
* `harea_motion`: the area is invariant under the h-motions `z ↦ u · mobius a z` (change of variables,
  using `|f'(z)| = (1-|f z|²)/(1-|z|²)`);
* `harea_hcircle_zero`: the h-disc of radius `r` has area `4π sinh²(r/2) = 2π (cosh r - 1)`
  (polar coordinates).
-/

namespace UndergradKB.Geometry

open Real Complex ComplexConjugate MeasureTheory Set
open scoped ENNReal

/-- The density of the hyperbolic area with respect to Lebesgue measure on the unit disc. -/
noncomputable def hdensity (z : ℂ) : ℝ≥0∞ := ENNReal.ofReal (4 / (1 - ‖z‖ ^ 2) ^ 2)

/-- The **hyperbolic area** of a set `s` of the plane: the integral of `4/(1-|z|²)²` over `s ∩ (unit disc)`. -/
noncomputable def harea (s : Set ℂ) : ℝ≥0∞ := ∫⁻ z in s ∩ Metric.ball 0 1, hdensity z

section Motion

variable {a u z : ℂ}

theorem hasDerivAt_mobius (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    HasDerivAt (mobius a) (((1 - ‖a‖ ^ 2 : ℝ) : ℂ) / (1 - conj a * z) ^ 2) z := by
  have hD := mobius_den_ne ha hz
  have h1 : HasDerivAt (fun w : ℂ => w - a) 1 z := (hasDerivAt_id z).sub_const a
  have h2 : HasDerivAt (fun w : ℂ => 1 - conj a * w) (-(conj a)) z := by
    have := ((hasDerivAt_id z).const_mul (conj a)).const_sub 1
    simpa using this
  have := h1.div h2 hD
  refine HasDerivAt.congr_deriv this ?_
  rw [ofReal_one_sub_sq]
  have e : (z - a) * conj a = conj a * z - a * conj a := by ring
  field_simp
  ring

theorem normSq_deriv_motion (ha : ‖a‖ < 1) (hu : ‖u‖ = 1) (hz : ‖z‖ < 1) :
    Complex.normSq (u * (((1 - ‖a‖ ^ 2 : ℝ) : ℂ) / (1 - conj a * z) ^ 2)) =
      (1 - ‖a‖ ^ 2) ^ 2 / ‖1 - conj a * z‖ ^ 4 := by
  have hD := norm_den_pos ha hz
  have hp := one_sub_sq_pos ha
  rw [← Complex.sq_norm, norm_mul, norm_div, norm_pow, hu, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hp]
  field_simp

theorem det_smulRight_restrict (c : ℂ) :
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ).det = Complex.normSq c := by
  rw [ContinuousLinearMap.det]
  have : (↑((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ) : ℂ →ₗ[ℝ] ℂ) =
      Algebra.lmul ℝ ℂ c := by
    ext y; simp [mul_comm]
  rw [this, ← Algebra.norm_apply, Algebra.norm_complex_apply]

/-- **The hyperbolic area is invariant under h-motions** `z ↦ u · mobius a z` (`|u| = 1`, `|a| < 1`), for
measurable subsets of the disc. -/
@[kb "petrunin2025" "Section 20I, area of neutral planes, p. 176"]
theorem harea_motion (ha : ‖a‖ < 1) (hu : ‖u‖ = 1) {s : Set ℂ} (hs : MeasurableSet s)
    (hsub : s ⊆ Metric.ball 0 1) : harea ((fun z => u * mobius a z) '' s) = harea s := by
  have himg : (fun z => u * mobius a z) '' s ⊆ Metric.ball 0 1 := by
    rintro _ ⟨z, hz, rfl⟩
    rw [mem_ball_zero_iff, norm_mul, hu, one_mul]
    exact norm_mobius_lt_one ha (mem_ball_zero_iff.mp (hsub hz))
  unfold harea
  rw [inter_eq_left.mpr himg, inter_eq_left.mpr hsub]
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  let f' : ℂ → ℂ →L[ℝ] ℂ := fun z => (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
    (u * (((1 - ‖a‖ ^ 2 : ℝ) : ℂ) / (1 - conj a * z) ^ 2))).restrictScalars ℝ
  have hderiv : ∀ x ∈ s, HasFDerivWithinAt (fun z => u * mobius a z) (f' x) s x := fun x hx =>
    (((hasDerivAt_mobius ha (mem_ball_zero_iff.mp (hsub hx))).const_mul u).hasFDerivAt.restrictScalars
      ℝ).hasFDerivWithinAt
  have hinj : InjOn (fun z => u * mobius a z) s := by
    intro x hx y hy hxy
    have h1 : mobius a x = mobius a y := mul_left_cancel₀ hu0 hxy
    have := congrArg (mobius (-a)) h1
    rwa [mobius_neg_mobius ha (mem_ball_zero_iff.mp (hsub hx)),
      mobius_neg_mobius ha (mem_ball_zero_iff.mp (hsub hy))] at this
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hderiv hinj]
  refine setLIntegral_congr_fun hs fun x hx => ?_
  have hx1 : ‖x‖ < 1 := mem_ball_zero_iff.mp (hsub hx)
  have hD := norm_den_pos ha hx1
  have hp := one_sub_sq_pos ha
  have hq := one_sub_sq_pos hx1
  have hdet : (f' x).det = (1 - ‖a‖ ^ 2) ^ 2 / ‖1 - conj a * x‖ ^ 4 := by
    rw [← normSq_deriv_motion ha hu hx1]
    exact det_smulRight_restrict _
  simp only [hdet, hdensity, norm_mul, hu, one_mul]
  rw [abs_of_nonneg (by positivity), one_sub_norm_mobius_sq ha hx1, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

end Motion

section Radial

/-- The radial integral of the hyperbolic area element: `∫₀^ρ r · 4/(1-r²)² dr = 2/(1-ρ²) - 2`. -/
theorem lintegral_radial {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    ∫⁻ r in Ioc 0 ρ, ENNReal.ofReal (r * (4 / (1 - r ^ 2) ^ 2)) = ENNReal.ofReal (2 / (1 - ρ ^ 2) - 2) := by
  have hpos : ∀ x ∈ uIcc 0 ρ, 0 < 1 - x ^ 2 := by
    intro x hx
    rw [uIcc_of_le h0] at hx
    nlinarith [hx.1, hx.2]
  have hderiv : ∀ x ∈ uIcc 0 ρ, HasDerivAt (fun r : ℝ => 2 / (1 - r ^ 2)) (x * (4 / (1 - x ^ 2) ^ 2)) x := by
    intro x hx
    have hne : 1 - x ^ 2 ≠ 0 := (hpos x hx).ne'
    have h1 : HasDerivAt (fun r : ℝ => 1 - r ^ 2) (-(2 * x)) x := by
      simpa using ((hasDerivAt_id x).pow 2).const_sub 1
    have := (hasDerivAt_const x (2 : ℝ)).div h1 hne
    refine this.congr_deriv ?_
    field_simp
    ring
  have hcont : ContinuousOn (fun r : ℝ => r * (4 / (1 - r ^ 2) ^ 2)) (uIcc 0 ρ) := by
    refine continuousOn_id.mul (continuousOn_const.div ((continuousOn_const.sub (continuousOn_id.pow 2)).pow 2) fun x hx => ?_)
    exact pow_ne_zero 2 (hpos x hx).ne'
  have hint : IntervalIntegrable (fun r : ℝ => r * (4 / (1 - r ^ 2) ^ 2)) volume 0 ρ := hcont.intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_of_le h0] at hftc
  have hI : IntegrableOn (fun r : ℝ => r * (4 / (1 - r ^ 2) ^ 2)) (Ioc 0 ρ) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h0).mp hint
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 ρ)] fun r : ℝ => r * (4 / (1 - r ^ 2) ^ 2) := by
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun r hr => ?_)
    have : 0 < 1 - r ^ 2 := by nlinarith [hr.1, hr.2]
    have : 0 ≤ r := hr.1.le
    positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hI hnn, hftc]
  simp

/-- The part of the plane in polar coordinates `(r, θ)` with `θ ∈ Θ` and `0 < r ≤ R(θ)`. -/
noncomputable def radialSet (Θ : Set ℝ) (R : ℝ → ℝ) : Set ℂ :=
  Complex.polarCoord.symm '' {p : ℝ × ℝ | p.2 ∈ Θ ∧ 0 < p.1 ∧ p.1 ≤ R p.2}

theorem measurableSet_radial {Θ : Set ℝ} (hΘ : MeasurableSet Θ) {R : ℝ → ℝ} (hR : Measurable R) :
    MeasurableSet {p : ℝ × ℝ | p.2 ∈ Θ ∧ 0 < p.1 ∧ p.1 ≤ R p.2} := by
  have h1 : MeasurableSet {p : ℝ × ℝ | p.2 ∈ Θ} := measurable_snd hΘ
  have h2 : MeasurableSet {p : ℝ × ℝ | 0 < p.1} := measurableSet_lt measurable_const measurable_fst
  have h3 : MeasurableSet {p : ℝ × ℝ | p.1 ≤ R p.2} :=
    measurableSet_le measurable_fst (hR.comp measurable_snd)
  exact h1.inter (h2.inter h3)

/-- **Area in polar coordinates**: the hyperbolic area of the region `{r e^{iθ} : θ ∈ Θ, 0 < r ≤ R(θ)}`
(`Θ ⊆ (-π, π)`, `0 ≤ R < 1`) is `∫_Θ (2/(1 - R(θ)²) - 2) dθ`. -/
theorem harea_radialSet {Θ : Set ℝ} (hΘ : MeasurableSet Θ) (hΘπ : Θ ⊆ Ioo (-π) π) {R : ℝ → ℝ}
    (hR : Measurable R) (hR0 : ∀ θ ∈ Θ, 0 ≤ R θ) (hR1 : ∀ θ ∈ Θ, R θ < 1) :
    harea (radialSet Θ R) = ∫⁻ θ in Θ, ENNReal.ofReal (2 / (1 - R θ ^ 2) - 2) := by
  set E : Set (ℝ × ℝ) := {p | p.2 ∈ Θ ∧ 0 < p.1 ∧ p.1 ≤ R p.2} with hEdef
  have hE : MeasurableSet E := measurableSet_radial hΘ hR
  have hEtarget : E ⊆ Complex.polarCoord.target := by
    rintro p ⟨h2, h1, -⟩
    exact ⟨h1, hΘπ h2⟩
  have hnorm : ∀ p ∈ E, ‖Complex.polarCoord.symm p‖ = p.1 := by
    intro p hp
    rw [Complex.norm_polarCoord_symm, abs_of_pos hp.2.1]
  have hS : radialSet Θ R = Complex.polarCoord.symm '' E := rfl
  have hsub : radialSet Θ R ⊆ Metric.ball 0 1 := by
    rintro _ ⟨p, hp, rfl⟩
    rw [mem_ball_zero_iff, hnorm p hp]
    exact lt_of_le_of_lt hp.2.2 (hR1 _ hp.1)
  have hmeas : MeasurableSet (radialSet Θ R) := by
    refine hE.image_of_continuousOn_injOn ?_ ?_
    · exact Complex.polarCoord.continuousOn_symm.mono hEtarget
    · exact Complex.polarCoord.symm.injOn.mono hEtarget
  unfold harea
  rw [inter_eq_left.mpr hsub, ← lintegral_indicator hmeas, ← Complex.lintegral_comp_polarCoord_symm]
  have hpt : ∀ p ∈ _root_.polarCoord.target,
      ENNReal.ofReal p.1 • (radialSet Θ R).indicator hdensity (Complex.polarCoord.symm p) =
        E.indicator (fun q : ℝ × ℝ => ENNReal.ofReal (q.1 * (4 / (1 - q.1 ^ 2) ^ 2))) p := by
    intro p hp
    by_cases hpE : p ∈ E
    · have hmem : Complex.polarCoord.symm p ∈ radialSet Θ R := ⟨p, hpE, rfl⟩
      rw [indicator_of_mem hmem, indicator_of_mem hpE, hdensity, hnorm p hpE, smul_eq_mul,
        ← ENNReal.ofReal_mul hp.1.le]
    · have hmem : Complex.polarCoord.symm p ∉ radialSet Θ R := by
        rintro ⟨q, hq, hqp⟩
        have := Complex.polarCoord.symm.injOn (hEtarget hq) hp hqp
        exact hpE (this ▸ hq)
      rw [indicator_of_notMem hmem, indicator_of_notMem hpE, smul_zero]
  rw [setLIntegral_congr_fun _root_.polarCoord.open_target.measurableSet hpt]
  set g : ℝ × ℝ → ℝ≥0∞ := fun q => ENNReal.ofReal (q.1 * (4 / (1 - q.1 ^ 2) ^ 2)) with hg
  have hgm : Measurable g := by
    simp only [hg]
    fun_prop
  rw [setLIntegral_eq_of_support_subset]
  swap
  · intro p hp
    by_contra hpE
    exact hp (indicator_of_notMem (fun h => hpE (hEtarget h)) _)
  rw [Measure.volume_eq_prod, lintegral_prod_symm' _ (hgm.indicator hE), ← lintegral_indicator hΘ]
  refine lintegral_congr fun θ => ?_
  by_cases hθ : θ ∈ Θ
  · rw [indicator_of_mem hθ]
    have : (fun r : ℝ => E.indicator g (r, θ)) =
        (Ioc 0 (R θ)).indicator (fun r => ENNReal.ofReal (r * (4 / (1 - r ^ 2) ^ 2))) := by
      funext r
      by_cases hr : r ∈ Ioc 0 (R θ)
      · rw [indicator_of_mem hr, indicator_of_mem (show (r, θ) ∈ E from ⟨hθ, hr.1, hr.2⟩)]
      · rw [indicator_of_notMem hr, indicator_of_notMem]
        rintro ⟨-, h1, h2⟩
        exact hr ⟨h1, h2⟩
    rw [this, lintegral_indicator measurableSet_Ioc]
    exact lintegral_radial (hR0 θ hθ) (hR1 θ hθ)
  · rw [indicator_of_notMem hθ]
    have : (fun r : ℝ => E.indicator g (r, θ)) = fun _ => 0 := by
      funext r
      exact indicator_of_notMem (show (r, θ) ∉ E from fun h => hθ h.1) _
    rw [this]
    simp

end Radial

/-- The area of an h-sector with centre `0`, angle `θ₁ - θ₀` and Euclidean radius `ρ` (h-radius `r` with
`ρ = tanh (r/2)`) is `(θ₁ - θ₀)(2/(1-ρ²) - 2)`; for `ρ = tanh (r/2)` this is `(θ₁ - θ₀)(cosh r - 1)`. -/
theorem harea_sector {θ₀ θ₁ ρ : ℝ} (h01 : θ₀ ≤ θ₁) (hπ : Ioc θ₀ θ₁ ⊆ Ioo (-π) π) (h0 : 0 ≤ ρ)
    (h1 : ρ < 1) :
    harea (radialSet (Ioc θ₀ θ₁) (fun _ => ρ)) =
      ENNReal.ofReal ((θ₁ - θ₀) * (2 / (1 - ρ ^ 2) - 2)) := by
  rw [harea_radialSet measurableSet_Ioc hπ measurable_const (fun _ _ => h0) (fun _ _ => h1),
    setLIntegral_const, Real.volume_Ioc, mul_comm, ENNReal.ofReal_mul (by linarith)]

section Geodesic

/-- The radial coordinate of the h-line `hline 1 (K e^{iφ})` in the direction `θ`: the smaller root of
`r² - 2 k r + 1 = 0` with `k = K cos (θ - φ)`. -/
noncomputable def geodR (K φ θ : ℝ) : ℝ :=
  K * Real.cos (θ - φ) - Real.sqrt ((K * Real.cos (θ - φ)) ^ 2 - 1)

theorem geodR_facts {k : ℝ} (hk : 1 < k) :
    0 < k - Real.sqrt (k ^ 2 - 1) ∧ k - Real.sqrt (k ^ 2 - 1) < 1 ∧
    (k - Real.sqrt (k ^ 2 - 1)) ^ 2 + 1 = 2 * (k - Real.sqrt (k ^ 2 - 1)) * k ∧
    2 / (1 - (k - Real.sqrt (k ^ 2 - 1)) ^ 2) - 2 = k / Real.sqrt (k ^ 2 - 1) - 1 ∧
    1 ≤ k / Real.sqrt (k ^ 2 - 1) := by
  have hpos : 0 < k ^ 2 - 1 := by nlinarith
  have hs : 0 < Real.sqrt (k ^ 2 - 1) := Real.sqrt_pos.mpr hpos
  have hs2 : Real.sqrt (k ^ 2 - 1) ^ 2 = k ^ 2 - 1 := Real.sq_sqrt hpos.le
  set s := Real.sqrt (k ^ 2 - 1)
  have hks : s < k := by nlinarith
  have hR : 0 < k - s := by linarith
  have hprod : (k - s) * (k + s) = 1 := by nlinarith
  refine ⟨hR, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · have h1 : 1 - (k - s) ^ 2 = 2 * s * (k - s) := by nlinarith
    rw [h1]
    field_simp
    nlinarith
  · rw [le_div_iff₀ hs]; linarith

/-- The primitive of the polar area integrand along the h-line `hline 1 (K e^{iφ})`. -/
noncomputable def geodG (K φ θ : ℝ) : ℝ :=
  Real.arcsin (K * Real.sin (θ - φ) / Real.sqrt (K ^ 2 - 1)) - θ

theorem geod_aux {K sn cs S s : ℝ} (hK2 : 0 < K ^ 2 - 1) (hS : S ^ 2 = K ^ 2 - 1)
    (hs : s ^ 2 = (K * cs) ^ 2 - 1) (hsc : sn ^ 2 + cs ^ 2 = 1) :
    1 - (K * sn / S) ^ 2 = (s / S) ^ 2 := by
  rw [div_pow, div_pow, hS, hs, eq_div_iff hK2.ne', sub_mul, div_mul_cancel₀ _ hK2.ne']
  linear_combination (-K ^ 2) * hsc

theorem hasDerivAt_geodG {K φ θ : ℝ} (hK : 1 < K) (hk : 1 < K * Real.cos (θ - φ)) :
    HasDerivAt (geodG K φ) (K * Real.cos (θ - φ) / Real.sqrt ((K * Real.cos (θ - φ)) ^ 2 - 1) - 1) θ := by
  have hK2 : 0 < K ^ 2 - 1 := by nlinarith
  have hS : 0 < Real.sqrt (K ^ 2 - 1) := Real.sqrt_pos.mpr hK2
  have hS2 : Real.sqrt (K ^ 2 - 1) ^ 2 = K ^ 2 - 1 := Real.sq_sqrt hK2.le
  have hk2 : 0 < (K * Real.cos (θ - φ)) ^ 2 - 1 := by nlinarith
  have hs : 0 < Real.sqrt ((K * Real.cos (θ - φ)) ^ 2 - 1) := Real.sqrt_pos.mpr hk2
  have hs2 : Real.sqrt ((K * Real.cos (θ - φ)) ^ 2 - 1) ^ 2 = (K * Real.cos (θ - φ)) ^ 2 - 1 :=
    Real.sq_sqrt hk2.le
  have e1 := geod_aux hK2 hS2 hs2 (Real.sin_sq_add_cos_sq (θ - φ))
  unfold geodG
  generalize Real.sqrt (K ^ 2 - 1) = S at *
  generalize Real.sqrt ((K * Real.cos (θ - φ)) ^ 2 - 1) = s at *
  have hX : HasDerivAt (fun t => K * Real.sin (t - φ) / S) (K * Real.cos (θ - φ) / S) θ := by
    have := (((hasDerivAt_id θ).sub_const φ).sin.const_mul K).div_const S
    simpa using this
  have hlt : (K * Real.sin (θ - φ) / S) ^ 2 < 1 := by
    have : 0 < (s / S) ^ 2 := by positivity
    linarith
  have habs : |K * Real.sin (θ - φ) / S| < 1 := by
    rw [← sq_lt_one_iff_abs_lt_one]; exact hlt
  have h1 : K * Real.sin (θ - φ) / S ≠ -1 := by
    intro h; rw [h] at habs; simp at habs
  have h2 : K * Real.sin (θ - φ) / S ≠ 1 := by
    intro h; rw [h] at habs; simp at habs
  have hA : HasDerivAt (fun t => Real.arcsin (K * Real.sin (t - φ) / S))
      (1 / √(1 - (K * Real.sin (θ - φ) / S) ^ 2) * (K * Real.cos (θ - φ) / S)) θ :=
    HasDerivAt.comp θ (Real.hasDerivAt_arcsin h1 h2) hX
  have hB := hA.sub (hasDerivAt_id θ)
  have hder : 1 / √(1 - (K * Real.sin (θ - φ) / S) ^ 2) * (K * Real.cos (θ - φ) / S) - 1 =
      K * Real.cos (θ - φ) / s - 1 := by
    rw [e1, Real.sqrt_sq (by positivity)]
    field_simp
  rw [hder] at hB
  exact hB

theorem lintegral_ofReal_deriv {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hd : ∀ x ∈ uIcc a b, HasDerivAt g (f x) x) (hc : ContinuousOn f (uIcc a b))
    (hnn : ∀ x ∈ Ioc a b, 0 ≤ f x) :
    ∫⁻ x in Ioc a b, ENNReal.ofReal (f x) = ENNReal.ofReal (g b - g a) := by
  have hint : IntervalIntegrable f volume a b := hc.intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  rw [intervalIntegral.integral_of_le hab] at hftc
  have hI : IntegrableOn f (Ioc a b) := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hint
  have hnn' : 0 ≤ᵐ[volume.restrict (Ioc a b)] f :=
    (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall hnn)
  rw [← ofReal_integral_eq_lintegral_ofReal hI hnn', hftc]

/-- **Area of a geodesic sector.** Let `K > 1` and let `L = hline 1 (K e^{iφ})` be the h-line with
`r² + 1 = 2 K r cos (θ - φ)` in polar coordinates. If `θ₀ ≤ θ₁` and `L` meets every ray `θ ∈ [θ₀, θ₁]`
(that is, `K cos (θ - φ) > 1`), then the region between the rays `θ₀`, `θ₁`, the centre and the arc of `L`
(an h-triangle with a vertex at the centre once the arc is cut by the rays) has hyperbolic area
`G(θ₁) - G(θ₀)` with `G(θ) = arcsin (K sin (θ - φ) / √(K² - 1)) - θ`. -/
@[kb "petrunin2025" "Section 20I, area of neutral planes, p. 176"]
theorem harea_geodesic_sector {K φ θ₀ θ₁ : ℝ} (hK : 1 < K) (h01 : θ₀ ≤ θ₁)
    (hπ : Ioc θ₀ θ₁ ⊆ Ioo (-π) π) (hk : ∀ θ ∈ Icc θ₀ θ₁, 1 < K * Real.cos (θ - φ)) :
    harea (radialSet (Ioc θ₀ θ₁) (geodR K φ)) = ENNReal.ofReal (geodG K φ θ₁ - geodG K φ θ₀) := by
  have hc1 : Continuous fun θ : ℝ => K * Real.cos (θ - φ) :=
    continuous_const.mul (Real.continuous_cos.comp (continuous_id.sub continuous_const))
  have hc2 : Continuous fun θ : ℝ => Real.sqrt ((K * Real.cos (θ - φ)) ^ 2 - 1) :=
    Real.continuous_sqrt.comp ((hc1.pow 2).sub continuous_const)
  have hRm : Measurable (geodR K φ) := (hc1.sub hc2).measurable
  have hmemI : ∀ θ ∈ Ioc θ₀ θ₁, θ ∈ Icc θ₀ θ₁ := fun θ hθ => ⟨hθ.1.le, hθ.2⟩
  rw [harea_radialSet measurableSet_Ioc hπ hRm
    (fun θ hθ => (geodR_facts (hk θ (hmemI θ hθ))).1.le)
    (fun θ hθ => (geodR_facts (hk θ (hmemI θ hθ))).2.1)]
  have hcongr : ∫⁻ θ in Ioc θ₀ θ₁, ENNReal.ofReal (2 / (1 - geodR K φ θ ^ 2) - 2) =
      ∫⁻ θ in Ioc θ₀ θ₁, ENNReal.ofReal (K * Real.cos (θ - φ) /
        Real.sqrt ((K * Real.cos (θ - φ)) ^ 2 - 1) - 1) := by
    refine setLIntegral_congr_fun measurableSet_Ioc fun θ hθ => ?_
    have := (geodR_facts (hk θ (hmemI θ hθ))).2.2.2.1
    exact congrArg ENNReal.ofReal this
  rw [hcongr]
  refine lintegral_ofReal_deriv h01 (fun θ hθ => ?_) ?_ (fun θ hθ => ?_)
  · rw [uIcc_of_le h01] at hθ
    exact hasDerivAt_geodG hK (hk θ hθ)
  · refine ContinuousOn.sub (ContinuousOn.div hc1.continuousOn hc2.continuousOn fun θ hθ => ?_)
      continuousOn_const
    rw [uIcc_of_le h01] at hθ
    have hk2 : 0 < (K * Real.cos (θ - φ)) ^ 2 - 1 := by nlinarith [hk θ hθ]
    exact (Real.sqrt_pos.mpr hk2).ne'
  · have := (geodR_facts (hk θ (hmemI θ hθ))).2.2.2.2
    linarith

end Geodesic

end UndergradKB.Geometry
