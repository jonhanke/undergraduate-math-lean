import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.JacobianOneDim
import UndergradKB.DifferentialEquations.Laplace
import UndergradKB.Common.Attr

/-!
# The heat-kernel transform pair and the inversion in Lebl Example 6.5.3 (DE-188)

For `x > 0` and `s > 0`, `L{e^{-x²/(4t)}/√(π t)}(s) = e^{-x√s}/√s`, proved by the Cauchy-Schlömilch
trick (substitute `t = u²`, then `a²u² + b²/u² = (au - b/u)² + 2ab`, and the Gaussian integral through the
substitution `v = au - b/u`).  Consequently the transform of the convolution
`y(x,·) = f * (-kernel)` is the decaying solution `Y(x) = -F(s) e^{-x√s}/√s` of the transformed heat problem.
-/

open Real Set Filter Topology MeasureTheory

namespace UndergradKB.DifferentialEquations

/-! ### The Cauchy-Schlömilch integral -/

/-- The map `u ↦ a u - b / u`. -/
private lemma phi_deriv {a b u : ℝ} (hu : 0 < u) :
    HasDerivWithinAt (fun u : ℝ => a * u - b * u⁻¹) (a + b / u ^ 2) (Ioi 0) u := by
  have h := ((hasDerivAt_id u).const_mul a).sub ((hasDerivAt_inv hu.ne').const_mul b)
  refine (h.congr_deriv ?_).hasDerivWithinAt
  simp only [mul_one]
  field_simp
  ring

private lemma phi_injOn {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    InjOn (fun u : ℝ => a * u - b * u⁻¹) (Ioi 0) := by
  have hm : StrictMonoOn (fun u : ℝ => a * u - b * u⁻¹) (Ioi 0) := by
    intro x hx y hy hxy
    simp only [mem_Ioi] at hx hy
    have : y⁻¹ < x⁻¹ := inv_strictAnti₀ hx hxy
    simp only
    nlinarith
  exact hm.injOn

private lemma phi_image {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (fun u : ℝ => a * u - b * u⁻¹) '' Ioi 0 = univ := by
  refine eq_univ_of_forall fun v => ?_
  set D := Real.sqrt (v ^ 2 + 4 * a * b) with hD
  have hD2 : D ^ 2 = v ^ 2 + 4 * a * b := Real.sq_sqrt (by positivity)
  have hDv : |v| < D :=
    abs_lt_of_sq_lt_sq (by rw [hD2]; nlinarith [mul_pos ha hb]) (Real.sqrt_nonneg _)
  have hDv' := abs_lt.1 hDv
  refine ⟨(v + D) / (2 * a), ?_, ?_⟩
  · simp only [mem_Ioi]; exact div_pos (by linarith) (by positivity)
  · have hne : v + D ≠ 0 := by linarith
    simp only
    field_simp
    nlinarith

private lemma integrableOn_gauss_phi {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun u : ℝ => (a + b / u ^ 2) * Real.exp (-(a * u - b * u⁻¹) ^ 2)) (Ioi 0) := by
  have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul (measurableSet_Ioi (a := (0:ℝ)))
    (fun u hu => phi_deriv (a := a) (b := b) hu) (phi_injOn ha hb)
    (fun v => Real.exp (-v ^ 2))).1
  rw [phi_image ha hb] at h
  have h1 : IntegrableOn (fun v : ℝ => Real.exp (-v ^ 2)) univ := by
    have := (integrable_exp_neg_mul_sq (b := 1) one_pos).integrableOn (s := univ)
    simpa using this
  refine (h h1).congr_fun (fun u hu => ?_) measurableSet_Ioi
  have : 0 < a + b / u ^ 2 := by have : 0 < u := hu; positivity
  simp only [smul_eq_mul, abs_of_pos this]

private lemma integral_gauss_phi {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ u in Ioi 0, (a + b / u ^ 2) * Real.exp (-(a * u - b * u⁻¹) ^ 2) = Real.sqrt π := by
  have h := integral_image_eq_integral_abs_deriv_smul (measurableSet_Ioi (a := (0:ℝ)))
    (fun u hu => phi_deriv (a := a) (b := b) hu) (phi_injOn ha hb)
    (fun v => Real.exp (-v ^ 2))
  rw [phi_image ha hb] at h
  have h1 : ∫ v : ℝ in univ, Real.exp (-v ^ 2) = Real.sqrt π := by
    rw [setIntegral_univ]
    have := integral_gaussian 1
    simpa using this
  rw [h1] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
  have : 0 < a + b / u ^ 2 := by have : 0 < u := hu; positivity
  simp only [smul_eq_mul, abs_of_pos this]

/-- The map `w ↦ b / (a w)` of `(0,∞)` onto itself. -/
private lemma psi_deriv {a b w : ℝ} (hw : 0 < w) :
    HasDerivWithinAt (fun w : ℝ => b / a * w⁻¹) (-(b / a / w ^ 2)) (Ioi 0) w := by
  have h := (hasDerivAt_inv hw.ne').const_mul (b / a)
  refine (h.congr_deriv ?_).hasDerivWithinAt
  field_simp

private lemma psi_injOn {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    InjOn (fun w : ℝ => b / a * w⁻¹) (Ioi 0) := by
  intro x hx y hy hxy
  simp only at hxy
  have hc : b / a ≠ 0 := by positivity
  exact inv_injective (mul_left_cancel₀ hc hxy)

private lemma psi_image {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (fun w : ℝ => b / a * w⁻¹) '' Ioi 0 = Ioi 0 := by
  ext y
  simp only [mem_image, mem_Ioi]
  constructor
  · rintro ⟨w, hw, rfl⟩; positivity
  · intro hy
    refine ⟨b / a * y⁻¹, by positivity, ?_⟩
    simp only [mul_inv_rev, inv_inv]
    field_simp

private lemma gauss_sym {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ u in Ioi 0, Real.exp (-(a * u - b * u⁻¹) ^ 2) =
      ∫ u in Ioi 0, (b / a / u ^ 2) * Real.exp (-(a * u - b * u⁻¹) ^ 2) := by
  have h := integral_image_eq_integral_abs_deriv_smul (measurableSet_Ioi (a := (0:ℝ)))
    (fun u hu => psi_deriv (a := a) (b := b) hu) (psi_injOn ha hb)
    (fun u => Real.exp (-(a * u - b * u⁻¹) ^ 2))
  rw [psi_image ha hb] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun w hw => ?_)
  have hw' : 0 < w := hw
  have : 0 < b / a / w ^ 2 := by positivity
  simp only [smul_eq_mul, abs_neg, abs_of_pos this]
  congr 2
  field_simp
  ring

/-- `∫_0^∞ e^{-(au - b/u)²} du = √π / (2a)`. -/
lemma integral_exp_neg_sq_phi {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ u in Ioi 0, Real.exp (-(a * u - b * u⁻¹) ^ 2) = Real.sqrt π / (2 * a) := by
  have hI := integrableOn_gauss_phi ha hb
  set J := ∫ u in Ioi 0, Real.exp (-(a * u - b * u⁻¹) ^ 2) with hJ
  have hcont : ContinuousOn (fun u : ℝ => Real.exp (-(a * u - b * u⁻¹) ^ 2)) (Ioi 0) := by
    have : ContinuousOn (fun u : ℝ => u⁻¹) (Ioi 0) := continuousOn_inv₀.mono (fun u hu => ne_of_gt hu)
    fun_prop
  have hcont2 : ContinuousOn (fun u : ℝ => b / u ^ 2) (Ioi 0) := by
    refine continuousOn_const.div (continuousOn_pow 2) (fun u hu => ?_)
    have : 0 < u := hu
    exact (pow_pos this 2).ne'
  have hpos : ∀ u : ℝ, 0 < Real.exp (-(a * u - b * u⁻¹) ^ 2) := fun u => Real.exp_pos _
  have hint1 : IntegrableOn (fun u : ℝ => a * Real.exp (-(a * u - b * u⁻¹) ^ 2)) (Ioi 0) := by
    refine hI.mono' ((continuousOn_const.mul hcont).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    have : 0 < u := hu
    have h0 := hpos u
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    have : 0 < b / u ^ 2 := by positivity
    nlinarith
  have hint2 : IntegrableOn (fun u : ℝ => b / u ^ 2 * Real.exp (-(a * u - b * u⁻¹) ^ 2)) (Ioi 0) := by
    refine hI.mono' ((hcont2.mul hcont).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    have : 0 < u := hu
    have h0 := hpos u
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    nlinarith
  have hsplit := integral_gauss_phi ha hb
  have e1 : (fun u : ℝ => (a + b / u ^ 2) * Real.exp (-(a * u - b * u⁻¹) ^ 2)) =
      fun u => a * Real.exp (-(a * u - b * u⁻¹) ^ 2) + b / u ^ 2 * Real.exp (-(a * u - b * u⁻¹) ^ 2) := by
    ext u; ring
  rw [e1, integral_add hint1 hint2, integral_const_mul] at hsplit
  have hs := gauss_sym ha hb
  have e2 : ∫ u in Ioi 0, (b / a / u ^ 2) * Real.exp (-(a * u - b * u⁻¹) ^ 2) =
      (1 / a) * ∫ u in Ioi 0, b / u ^ 2 * Real.exp (-(a * u - b * u⁻¹) ^ 2) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
    field_simp
  rw [e2] at hs
  have : ∫ u in Ioi 0, b / u ^ 2 * Real.exp (-(a * u - b * u⁻¹) ^ 2) = a * J := by
    rw [hJ, hs, ← mul_assoc, mul_one_div_cancel ha.ne', one_mul]
  rw [this] at hsplit
  rw [eq_div_iff (by positivity)]
  linarith

/-! ### The transform pair -/

/-- The heat kernel `e^{-x²/(4t)} / √(π t)` of Example 6.5.3 (a small abbreviation; value `0` at `t = 0`). -/
noncomputable def heatKernel (x t : ℝ) : ℝ := Real.exp (-(x ^ 2 / (4 * t))) / Real.sqrt (π * t)

private lemma sq_injOn : InjOn (fun u : ℝ => u ^ 2) (Ioi 0) := by
  intro x hx y hy hxy
  exact (sq_eq_sq₀ (le_of_lt hx) (le_of_lt hy)).1 hxy

private lemma sq_image : (fun u : ℝ => u ^ 2) '' Ioi 0 = Ioi 0 := by
  ext y
  simp only [mem_image, mem_Ioi]
  constructor
  · rintro ⟨w, hw, rfl⟩; positivity
  · intro hy
    exact ⟨Real.sqrt y, Real.sqrt_pos.2 hy, Real.sq_sqrt hy.le⟩

private lemma heat_pointwise {a x u : ℝ} (hu : 0 < u) :
    |2 * u| • (Real.exp (-(a ^ 2 * u ^ 2)) * heatKernel x (u ^ 2)) =
      (2 / Real.sqrt π * Real.exp (-(x * a))) * Real.exp (-(a * u - (x / 2) * u⁻¹) ^ 2) := by
  have hs : Real.sqrt (π * u ^ 2) = Real.sqrt π * u := by
    rw [Real.sqrt_mul pi_pos.le, Real.sqrt_sq hu.le]
  have hpi : 0 < Real.sqrt π := Real.sqrt_pos.2 pi_pos
  have e : Real.exp (-(a ^ 2 * u ^ 2)) * Real.exp (-(x ^ 2 / (4 * u ^ 2))) =
      Real.exp (-(x * a)) * Real.exp (-(a * u - (x / 2) * u⁻¹) ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp
    ring
  unfold heatKernel
  rw [hs, abs_of_pos (by positivity), smul_eq_mul]
  calc 2 * u * (Real.exp (-(a ^ 2 * u ^ 2)) * (Real.exp (-(x ^ 2 / (4 * u ^ 2))) / (Real.sqrt π * u)))
      = 2 / Real.sqrt π * (Real.exp (-(a ^ 2 * u ^ 2)) * Real.exp (-(x ^ 2 / (4 * u ^ 2)))) := by
        field_simp
    _ = _ := by rw [e]; ring

/-- The transform pair for `x > 0`, in the variable `s = a²`. -/
lemma laplace_heatKernel_sq {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    laplace (heatKernel x) (a ^ 2) = Real.exp (-(x * a)) / a := by
  have hb : 0 < x / 2 := by positivity
  have h := integral_image_eq_integral_abs_deriv_smul (measurableSet_Ioi (a := (0:ℝ)))
    (f := fun u : ℝ => u ^ 2) (f' := fun u => 2 * u)
    (fun u hu => by simpa using (hasDerivAt_pow 2 u).hasDerivWithinAt) sq_injOn
    (fun t => Real.exp (-(a ^ 2 * t)) * heatKernel x t)
  rw [sq_image] at h
  unfold laplace
  rw [h]
  have h2 : ∫ u in Ioi (0:ℝ), |2 * u| • (Real.exp (-(a ^ 2 * u ^ 2)) * heatKernel x (u ^ 2)) =
      ∫ u in Ioi (0:ℝ), (2 / Real.sqrt π * Real.exp (-(x * a))) *
        Real.exp (-(a * u - (x / 2) * u⁻¹) ^ 2) :=
    setIntegral_congr_fun measurableSet_Ioi (fun u hu => heat_pointwise hu)
  rw [h2, integral_const_mul, integral_exp_neg_sq_phi ha hb]
  have hpi : 0 < Real.sqrt π := Real.sqrt_pos.2 pi_pos
  field_simp

/-- **DE-188 (Example 6.5.3, the transform pair).** Lebl Example 6.5.3, p. 324: for `x > 0` and `s > 0`,
`L{e^{-x²/(4t)}/√(π t)}(s) = e^{-x√s}/√s`. (Cauchy-Schlömilch: substitute `t = u²`, split
`a²u² + b²/u² = (au - b/u)² + 2ab`, and use the Gaussian integral through `v = au - b/u`.) -/
@[kb "lebldiffyqs2026" "Example 6.5.3, p. 324"]
theorem laplace_heat_kernel {x s : ℝ} (hx : 0 < x) (hs : 0 < s) :
    laplace (fun t => Real.exp (-(x ^ 2 / (4 * t))) / Real.sqrt (π * t)) s =
      Real.exp (-(x * Real.sqrt s)) / Real.sqrt s := by
  have := laplace_heatKernel_sq hx (Real.sqrt_pos.2 hs)
  rw [Real.sq_sqrt hs.le] at this
  exact this

/-! ### Properties of the kernel -/

lemma heatKernel_zero (x : ℝ) : heatKernel x 0 = 0 := by simp [heatKernel]

lemma heatKernel_nonneg (x t : ℝ) : 0 ≤ heatKernel x t := by
  unfold heatKernel; positivity

/-- Key estimate: `e^{-y} (1 + y) ≤ 1`. -/
private lemma exp_neg_mul_one_add_le {y : ℝ} : Real.exp (-y) * (1 + y) ≤ 1 := by
  have h := Real.add_one_le_exp y
  have e : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
  calc Real.exp (-y) * (1 + y) ≤ Real.exp (-y) * Real.exp y :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
    _ = 1 := e

/-- The kernel is bounded: `0 ≤ k_x(t) ≤ 2/(x √π)` for `t ≥ 0`. -/
lemma heatKernel_le_bound {x : ℝ} (hx : 0 < x) {t : ℝ} (ht : 0 ≤ t) :
    heatKernel x t ≤ 2 / (x * Real.sqrt π) := by
  rcases ht.eq_or_lt with rfl | ht
  · rw [heatKernel_zero]; positivity
  have hpi : 0 < Real.sqrt π := Real.sqrt_pos.2 pi_pos
  set w := Real.sqrt t with hw
  have hw0 : 0 < w := Real.sqrt_pos.2 ht
  have hwt : t = w ^ 2 := (Real.sq_sqrt ht.le).symm
  have hs : Real.sqrt (π * t) = Real.sqrt π * w := by rw [Real.sqrt_mul pi_pos.le]
  have hE := exp_neg_mul_one_add_le (y := x ^ 2 / (4 * t))
  set E := Real.exp (-(x ^ 2 / (4 * t))) with hEdef
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  unfold heatKernel
  rw [hs, div_le_div_iff₀ (by positivity) (by positivity)]
  have hr : 2 * (x / (2 * w)) ≤ 1 + x ^ 2 / (4 * t) := by
    rw [hwt]
    have : x ^ 2 / (4 * w ^ 2) = (x / (2 * w)) ^ 2 := by field_simp; ring
    rw [this]; nlinarith [sq_nonneg (x / (2 * w) - 1)]
  have h2 : E * (2 * (x / (2 * w))) ≤ 1 := le_trans (mul_le_mul_of_nonneg_left hr hE0) hE
  have h3 : E * (2 * (x / (2 * w))) = E * x / w := by field_simp
  rw [h3, div_le_one hw0] at h2
  rw [← hEdef]
  nlinarith [mul_pos hx hpi]

/-- Smallness near `0`: `0 ≤ k_x(t) ≤ 4 √t / (x² √π)` for `t ≥ 0`. -/
lemma heatKernel_le_sqrt {x : ℝ} (hx : 0 < x) {t : ℝ} (ht : 0 ≤ t) :
    heatKernel x t ≤ 4 * Real.sqrt t / (x ^ 2 * Real.sqrt π) := by
  rcases ht.eq_or_lt with rfl | ht
  · rw [heatKernel_zero]; simp
  have hpi : 0 < Real.sqrt π := Real.sqrt_pos.2 pi_pos
  set w := Real.sqrt t with hw
  have hw0 : 0 < w := Real.sqrt_pos.2 ht
  have hwt : t = w ^ 2 := (Real.sq_sqrt ht.le).symm
  have hs : Real.sqrt (π * t) = Real.sqrt π * w := by rw [Real.sqrt_mul pi_pos.le]
  have hE := exp_neg_mul_one_add_le (y := x ^ 2 / (4 * t))
  set E := Real.exp (-(x ^ 2 / (4 * t))) with hEdef
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  unfold heatKernel
  rw [hs, div_le_div_iff₀ (by positivity) (by positivity)]
  have hy : 0 < x ^ 2 / (4 * t) := by positivity
  have h2 : E * (x ^ 2 / (4 * t)) ≤ 1 := by nlinarith
  rw [hwt] at h2
  have h3 : E * (x ^ 2 / (4 * w ^ 2)) = E * x ^ 2 / (4 * w ^ 2) := by ring
  rw [h3, div_le_one (by positivity)] at h2
  rw [← hEdef]
  have : E * x ^ 2 * (Real.sqrt π * w) ≤ 4 * w ^ 2 * (Real.sqrt π * w) :=
    mul_le_mul_of_nonneg_right h2 (by positivity)
  nlinarith

lemma continuousOn_heatKernel {x : ℝ} (hx : 0 < x) : ContinuousOn (heatKernel x) (Ici 0) := by
  have hI : ContinuousOn (heatKernel x) (Ioi 0) := by
    unfold heatKernel
    refine ContinuousOn.div ?_ ?_ (fun t ht => ?_)
    · refine Real.continuous_exp.comp_continuousOn (ContinuousOn.neg ?_)
      refine continuousOn_const.div (continuousOn_const.mul continuousOn_id) (fun t ht => ?_)
      have : 0 < t := ht
      exact (by positivity : (0:ℝ) < 4 * t).ne'
    · exact (Real.continuous_sqrt.comp (continuous_const.mul continuous_id)).continuousOn
    · have : 0 < t := ht
      exact (Real.sqrt_pos.2 (by positivity)).ne'
  intro t ht
  rcases (mem_Ici.1 ht).eq_or_lt with rfl | ht
  · unfold ContinuousWithinAt
    rw [heatKernel_zero]
    have hlim : Tendsto (fun t : ℝ => 4 * Real.sqrt t / (x ^ 2 * Real.sqrt π)) (𝓝[Ici 0] 0) (𝓝 0) := by
      have := ((Real.continuous_sqrt.const_mul 4).div_const (x ^ 2 * Real.sqrt π)).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hlim
    refine eventually_nhdsWithin_of_forall (fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg x t)]
    exact heatKernel_le_sqrt hx ht
  · exact ((hI.continuousAt (Ioi_mem_nhds ht)).continuousWithinAt)

lemma expOrder_heatKernel {x : ℝ} (hx : 0 < x) {c : ℝ} (hc : 0 ≤ c) :
    ExpOrder (fun t => -heatKernel x t) (2 / (x * Real.sqrt π)) c := by
  intro t ht
  rw [abs_neg, abs_of_nonneg (heatKernel_nonneg x t)]
  refine le_trans (heatKernel_le_bound hx ht) ?_
  have : 1 ≤ Real.exp (c * t) := Real.one_le_exp (by positivity)
  have hM : 0 ≤ 2 / (x * Real.sqrt π) := by positivity
  nlinarith

/-- Integrability of the integrand of the transform pair: `e^{-st} e^{-x²/(4t)}/√(π t)` is integrable on
`(0,∞)` for `x > 0`, `s > 0`. -/
lemma heatKernel_integrableOn {x s : ℝ} (hx : 0 < x) (hs : 0 < s) :
    IntegrableOn (fun t => Real.exp (-(s * t)) * heatKernel x t) (Ioi 0) := by
  have := laplace_integrableOn (f := fun t => -heatKernel x t) (c := 0) (s := s)
    (continuousOn_heatKernel hx).neg (expOrder_heatKernel hx le_rfl) hs
  simpa using this.neg

/-! ### The inversion -/

/-- **DE-188 (Example 6.5.3, the inversion).** Lebl Example 6.5.3, p. 324: if `f` is continuous on `[0,∞)` and
of exponential order `c`, then the convolution `y(x,t) = (f * (-e^{-x²/(4t)}/√(π t)))(t)` (the book's inverted
solution of the half-infinite rod problem) has, for `x > 0`, `s > c` and `s > 0`, the
Laplace transform in `t` equal to `-F(s) e^{-x√s}/√s`, which is the decaying solution
`Y(x) = -(F(s)/√s) e^{-√s x}` of `Y'' = sY`, `Y'(0) = F(s)` (see `example_653_ode`). The kernel is set to `0` at
`t = 0` (its limit); no further hypothesis than those of the convolution theorem is added. -/
@[kb "lebldiffyqs2026" "Example 6.5.3, p. 324"]
theorem example_653_inversion {f : ℝ → ℝ} {M c x s : ℝ} (hx : 0 < x) (hs : 0 < s)
    (hfc : ContinuousOn f (Ici 0)) (hf : ExpOrder f M c) (hcs : c < s) :
    laplace (conv0 f (fun t => -heatKernel x t)) s =
      -(laplace f s / Real.sqrt s) * Real.exp (-(Real.sqrt s * x)) := by
  have hM : 0 ≤ M := by simpa using (abs_nonneg _).trans (hf 0 le_rfl)
  have hf' : ExpOrder f M (max c 0) := fun t ht =>
    (hf t ht).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_left _ _) ht)) hM)
  have hcs' : max c 0 < s := max_lt hcs hs
  have hg := expOrder_heatKernel hx (le_max_right c 0)
  rw [laplace_conv0 (g := fun t => -heatKernel x t) hfc (continuousOn_heatKernel hx).neg hf' hg hcs']
  have hneg : laplace (fun t => -heatKernel x t) s = -laplace (heatKernel x) s := by
    have := laplace_const_mul (-1) (heatKernel x) s
    simpa using this
  have hp := laplace_heat_kernel hx hs
  have hp' : laplace (heatKernel x) s = Real.exp (-(x * Real.sqrt s)) / Real.sqrt s := hp
  rw [hneg, hp']
  have : Real.sqrt s * x = x * Real.sqrt s := mul_comm _ _
  rw [this]
  ring

end UndergradKB.DifferentialEquations
