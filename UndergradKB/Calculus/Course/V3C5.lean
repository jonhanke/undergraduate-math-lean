import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Probability.Density
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import UndergradKB.Calculus.MultipleIntegrals
import UndergradKB.Calculus.CoordinateFubini
import UndergradKB.Calculus.MultipleRiemannSums
import UndergradKB.Calculus.Volumes
import UndergradKB.Calculus.MassMoments
import UndergradKB.Common.Attr

/-! Course layer, OpenStax Calculus Volume 3, Chapter 5 (multiple integration). Double integrals
over a region `S ⊆ ℝ × ℝ` are `∫ p in S, f p` (Lebesgue measure on the plane), triple integrals the
same on `ℝ × ℝ × ℝ`. -/

namespace UndergradKB.Calculus.Course.V3C5

open MeasureTheory Set Filter Topology

/-- Set integrals over a closed interval agree with interval integrals (helper). -/
theorem integral_Icc_eq_interval {a b : ℝ} (hab : a ≤ b) (g : ℝ → ℝ) :
    ∫ x in Icc a b, g x = ∫ x in a..b, g x := by
  rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]

/-- OpenStax Calculus 3:§5.1 text on integrability (CA-554). A function continuous on the closed
rectangle `[a,b] × [c,d]` is integrable over it. -/
@[kb "openstaxcalculus2016" "3:§5.1 text on integrability (bounded, continuous off finitely many smooth curves), p. 432"]
theorem integrable_of_continuousOn_rectangle {f : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (hf : ContinuousOn f (Icc a b ×ˢ Icc c d)) :
    IntegrableOn f (Icc a b ×ˢ Icc c d) :=
  hf.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

/-- OpenStax Calculus 3:Theorem 5.1 (i) (CA-555). The double integral of a sum of integrable
functions is the sum of the double integrals. -/
@[kb "openstaxcalculus2016" "3:Theorem 5.1, p. 432"]
theorem double_integral_add {S : Set (ℝ × ℝ)} {f g : ℝ × ℝ → ℝ} (hf : IntegrableOn f S)
    (hg : IntegrableOn g S) :
    ∫ p in S, (f p + g p) = (∫ p in S, f p) + ∫ p in S, g p :=
  MeasureTheory.integral_add hf hg

/-- OpenStax Calculus 3:Theorem 5.1 (ii) (CA-555). Constant multiples come out of the double
integral. -/
@[kb "openstaxcalculus2016" "3:Theorem 5.1, p. 432"]
theorem double_integral_const_mul {S : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℝ} (c : ℝ) :
    ∫ p in S, c * f p = c * ∫ p in S, f p :=
  MeasureTheory.integral_const_mul c f

/-- OpenStax Calculus 3:Theorem 5.1 (iii) / Theorem 5.5 (CA-556). If two regions overlap only in
a set of area zero, the integral over the union is the sum of the integrals. -/
@[kb "openstaxcalculus2016" "3:Theorem 5.5, p. 454"]
theorem double_integral_union {S T : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℝ}
    (hST : volume (S ∩ T) = 0) (hT : MeasurableSet T) (hfS : IntegrableOn f S)
    (hfT : IntegrableOn f T) :
    ∫ p in S ∪ T, f p = (∫ p in S, f p) + ∫ p in T, f p :=
  MeasureTheory.setIntegral_union₀ hST hT.nullMeasurableSet hfS hfT

/-- OpenStax Calculus 3:Theorem 5.1 (iv) (CA-557). If `f ≤ g` on a region then the double
integral of `f` is at most that of `g`. -/
@[kb "openstaxcalculus2016" "3:Theorem 5.1, p. 432"]
theorem double_integral_mono {S : Set (ℝ × ℝ)} {f g : ℝ × ℝ → ℝ} (hf : IntegrableOn f S)
    (hg : IntegrableOn g S) (hS : MeasurableSet S) (h : ∀ p ∈ S, f p ≤ g p) :
    ∫ p in S, f p ≤ ∫ p in S, g p :=
  MeasureTheory.setIntegral_mono_on hf hg hS h

/-- OpenStax Calculus 3:Theorem 5.1 (v) (CA-558). If `m ≤ f ≤ M` on a region of finite area, then
`m * area ≤ ∫∫ f ≤ M * area`. -/
@[kb "openstaxcalculus2016" "3:Theorem 5.1, p. 432"]
theorem double_integral_bounds {S : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℝ} {m M : ℝ}
    (hf : IntegrableOn f S) (hS : MeasurableSet S) (hfin : volume S ≠ ⊤)
    (hm : ∀ p ∈ S, m ≤ f p) (hM : ∀ p ∈ S, f p ≤ M) :
    m * (volume S).toReal ≤ ∫ p in S, f p ∧ ∫ p in S, f p ≤ M * (volume S).toReal := by
  have hc : ∀ c : ℝ, IntegrableOn (fun _ : ℝ × ℝ => c) S := fun c =>
    integrableOn_const hfin
  have h1 := MeasureTheory.setIntegral_mono_on (hc m) hf hS hm
  have h2 := MeasureTheory.setIntegral_mono_on hf (hc M) hS hM
  simp only [MeasureTheory.setIntegral_const, smul_eq_mul, Measure.real] at h1 h2
  constructor
  · linarith [mul_comm m (volume S).toReal]
  · linarith [mul_comm M (volume S).toReal]

/-- OpenStax Calculus 3:Theorem 5.1 (vi) (CA-559). The integral of `g(x) h(y)` over a rectangle is
the product of the two single integrals. -/
@[kb "openstaxcalculus2016" "3:Theorem 5.1, p. 432"]
theorem double_integral_product (g h : ℝ → ℝ) (a b c d : ℝ) :
    ∫ p in Icc a b ×ˢ Icc c d, g p.1 * h p.2 =
      (∫ x in Icc a b, g x) * ∫ y in Icc c d, h y := by
  rw [Measure.volume_eq_prod]
  exact MeasureTheory.setIntegral_prod_mul g h _ _

/-- OpenStax Calculus 3:Theorem 5.2 (CA-561). Fubini's theorem on a rectangle: for `f` continuous
on `[a,b] × [c,d]` the double integral equals the iterated integral `∫ₐᵇ ∫_c^d f dy dx`. -/
@[kb "openstaxcalculus2016" "3:Theorem 5.2, p. 433"]
theorem fubini_rectangle_dy_dx {f : ℝ × ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hf : ContinuousOn f (Icc a b ×ˢ Icc c d)) :
    ∫ p in Icc a b ×ˢ Icc c d, f p = ∫ x in a..b, ∫ y in c..d, f (x, y) := by
  have hint : IntegrableOn f (Icc a b ×ˢ Icc c d) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact integrable_of_continuousOn_rectangle hf
  rw [Measure.volume_eq_prod, MeasureTheory.setIntegral_prod f hint,
    integral_Icc_eq_interval hab]
  refine intervalIntegral.integral_congr fun x _ => ?_
  exact integral_Icc_eq_interval hcd (fun y => f (x, y))

/-- OpenStax Calculus 3:Theorem 5.2 (CA-561). Fubini's theorem on a rectangle, other order:
`∫_c^d ∫ₐᵇ f dx dy`. -/
@[kb "openstaxcalculus2016" "3:Theorem 5.2, p. 433"]
theorem fubini_rectangle_dx_dy {f : ℝ × ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hf : ContinuousOn f (Icc a b ×ˢ Icc c d)) :
    ∫ p in Icc a b ×ˢ Icc c d, f p = ∫ y in c..d, ∫ x in a..b, f (x, y) := by
  have hint : Integrable f ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact integrable_of_continuousOn_rectangle hf
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, MeasureTheory.integral_prod_symm f hint,
    integral_Icc_eq_interval hcd]
  refine intervalIntegral.integral_congr fun y _ => ?_
  exact integral_Icc_eq_interval hab (fun x => f (x, y))

/-- OpenStax Calculus 3:Definition (area of a plane-bounded region) (CA-562). The area of a region
is the double integral of the constant `1` over it. -/
@[kb "openstaxcalculus2016" "3:Definition (area of a plane-bounded region), p. 459"]
theorem area_eq_double_integral_one (S : Set (ℝ × ℝ)) :
    ∫ _ in S, (1 : ℝ) = (volume S).toReal := by
  simp [Measure.real]

/-- OpenStax Calculus 3:§5.1 text, volume as double integral (CA-563). For `f ≥ 0` integrable over
a measurable region `S` of the plane, the solid between the plane and the graph over `S` has volume
`∫∫_S f` (the region is `regionBetween 0 f S ⊆ (ℝ × ℝ) × ℝ`, open at the top and bottom). -/
@[kb "openstaxcalculus2016" "3:§5.1 text, volume V as double integral, p. 430"]
theorem volume_under_graph {S : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℝ} (hf : IntegrableOn f S)
    (hS : MeasurableSet S) (h0 : ∀ p ∈ S, 0 ≤ f p) :
    (volume : Measure ((ℝ × ℝ) × ℝ)) (regionBetween (fun _ => 0) f S) =
      ENNReal.ofReal (∫ p in S, f p) := by
  rw [Measure.volume_eq_prod (α := ℝ × ℝ) (β := ℝ)]
  rw [volume_regionBetween_eq_integral integrableOn_zero hf hS h0]
  simp

/-- OpenStax Calculus 3:Definition (average value over a plane region) (CA-564). The average of `f`
over a region of positive area is the double integral divided by the area. -/
@[kb "openstaxcalculus2016" "3:Definition (average value over a plane region), p. 459"]
theorem average_value_plane (S : Set (ℝ × ℝ)) (f : ℝ × ℝ → ℝ) :
    ⨍ p in S, f p = (∫ p in S, f p) / (volume S).toReal := by
  rw [setAverage_eq]
  simp [Measure.real, div_eq_inv_mul]

/-- OpenStax Calculus 3:Theorem 5.3 (CA-566). Integrating over a region `D` inside a rectangle `R`
equals integrating over `R` the function extended by zero outside `D`. -/
@[kb "openstaxcalculus2016" "3:Theorem 5.3, p. 451"]
theorem integral_over_region_via_zero_extension {D R : Set (ℝ × ℝ)} (hD : MeasurableSet D)
    (hDR : D ⊆ R) (f : ℝ × ℝ → ℝ) :
    ∫ p in R, D.indicator f p = ∫ p in D, f p := by
  rw [MeasureTheory.setIntegral_indicator hD, inter_eq_right.mpr hDR]

/-- OpenStax Calculus 3:Theorem 5.6 (CA-568). Fubini-Tonelli for nonnegative (extended-real)
functions on a product region `S × T`: the double integral equals the iterated integral in
either order. -/
@[kb "openstaxcalculus2016" "3:Theorem 5.6, p. 461"]
theorem tonelli_nonneg {S T : Set ℝ} {f : ℝ × ℝ → ENNReal} (hf : Measurable f) :
    ∫⁻ p in S ×ˢ T, f p = ∫⁻ x in S, ∫⁻ y in T, f (x, y) ∧
    ∫⁻ p in S ×ˢ T, f p = ∫⁻ y in T, ∫⁻ x in S, f (x, y) := by
  rw [Measure.volume_eq_prod]
  exact ⟨MeasureTheory.setLIntegral_prod f hf.aemeasurable,
    MeasureTheory.setLIntegral_prod_symm f hf.aemeasurable⟩

/-- OpenStax Calculus 3:Definition (expected values E(X), E(Y)) (CA-572). For a random vector
`(X, Y)` with joint density `f`, `E(X) = ∬ x f(x,y)` and `E(Y) = ∬ y f(x,y)`. -/
@[kb "openstaxcalculus2016" "3:Definition (expected values E(X), E(Y)), p. 464"]
theorem expected_values_from_joint_density {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    [IsFiniteMeasure ℙ] {Z : Ω → ℝ × ℝ} [HasPDF Z ℙ volume] :
    (∫ p : ℝ × ℝ, p.1 * (pdf Z ℙ volume p).toReal = ∫ ω, (Z ω).1 ∂ℙ) ∧
    (∫ p : ℝ × ℝ, p.2 * (pdf Z ℙ volume p).toReal = ∫ ω, (Z ω).2 ∂ℙ) := by
  constructor
  · have := MeasureTheory.pdf.integral_pdf_smul (ℙ := ℙ) (X := Z) (μ := volume)
      (f := fun p : ℝ × ℝ => p.1) measurable_fst.aestronglyMeasurable
    simp only [smul_eq_mul] at this
    rw [← this]
    simp_rw [mul_comm]
  · have := MeasureTheory.pdf.integral_pdf_smul (ℙ := ℙ) (X := Z) (μ := volume)
      (f := fun p : ℝ × ℝ => p.2) measurable_snd.aestronglyMeasurable
    simp only [smul_eq_mul] at this
    rw [← this]
    simp_rw [mul_comm]

/-- OpenStax Calculus 3:Section 5.3 exercise on the Gaussian integral (CA-575). The integral of
`exp(-(x²+y²))` over the plane is `π`. -/
@[kb "openstaxcalculus2016" "3:Example 5.35, p. 483"]
theorem gaussian_integral_plane : ∫ p : ℝ × ℝ, Real.exp (-(p.1 ^ 2 + p.2 ^ 2)) = Real.pi := by
  have h1 : ∀ p : ℝ × ℝ, Real.exp (-(p.1 ^ 2 + p.2 ^ 2)) =
      Real.exp (-1 * p.1 ^ 2) * Real.exp (-1 * p.2 ^ 2) := by
    intro p
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [h1]
  rw [Measure.volume_eq_prod,
    MeasureTheory.integral_prod_mul (fun x : ℝ => Real.exp (-1 * x ^ 2))
      (fun y : ℝ => Real.exp (-1 * y ^ 2)),
    integral_gaussian, div_one, Real.mul_self_sqrt Real.pi_pos.le]

/-- OpenStax Calculus 3:Section 5.3 exercise on the Gaussian integral (CA-575). Consequently
`∫ exp(-x²) dx = √π`. -/
@[kb "openstaxcalculus2016" "3:Example 5.35, p. 483"]
theorem gaussian_integral_line : ∫ x : ℝ, Real.exp (-x ^ 2) = Real.sqrt Real.pi := by
  have := integral_gaussian 1
  simpa using this

/-- OpenStax Calculus 3:§5.4 text on integrability (CA-578). A function continuous on a box in
`ℝ³` is integrable over it. -/
@[kb "openstaxcalculus2016" "3:§5.4 text on integrability (continuity sufficient), p. 494"]
theorem integrable_of_continuousOn_box {f : ℝ × ℝ × ℝ → ℝ} {a₁ b₁ a₂ b₂ a₃ b₃ : ℝ}
    (hf : ContinuousOn f (Icc a₁ b₁ ×ˢ (Icc a₂ b₂ ×ˢ Icc a₃ b₃))) :
    IntegrableOn f (Icc a₁ b₁ ×ˢ (Icc a₂ b₂ ×ˢ Icc a₃ b₃)) :=
  hf.integrableOn_compact (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))

/-- OpenStax Calculus 3:Theorem 5.9 (CA-579). Fubini for triple integrals: for `f` continuous on a
box, the triple integral equals `∫ dx ∫ dy ∫ dz f(x,y,z)`. -/
@[kb "openstaxcalculus2016" "3:Theorem 5.9, p. 494"]
theorem fubini_box_dz_dy_dx {f : ℝ × ℝ × ℝ → ℝ} {a₁ b₁ a₂ b₂ a₃ b₃ : ℝ} (h₁ : a₁ ≤ b₁)
    (h₂ : a₂ ≤ b₂) (h₃ : a₃ ≤ b₃) (hf : ContinuousOn f (Icc a₁ b₁ ×ˢ (Icc a₂ b₂ ×ˢ Icc a₃ b₃))) :
    ∫ p in Icc a₁ b₁ ×ˢ (Icc a₂ b₂ ×ˢ Icc a₃ b₃), f p =
      ∫ x in a₁..b₁, ∫ y in a₂..b₂, ∫ z in a₃..b₃, f (x, y, z) := by
  have hint : IntegrableOn f (Icc a₁ b₁ ×ˢ (Icc a₂ b₂ ×ˢ Icc a₃ b₃))
      ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))) := integrable_of_continuousOn_box hf
  rw [Measure.volume_eq_prod, MeasureTheory.setIntegral_prod f hint, integral_Icc_eq_interval h₁]
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [uIcc_of_le h₁] at hx
  have hs : ContinuousOn (fun q : ℝ × ℝ => f (x, q)) (Icc a₂ b₂ ×ˢ Icc a₃ b₃) :=
    hf.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun q hq => ⟨hx, hq⟩)
  exact fubini_rectangle_dy_dx h₂ h₃ hs

/-- OpenStax Calculus 3:Theorem 5.9 (CA-579). Another order: `∫ dx ∫ dz ∫ dy f(x,y,z)`. -/
@[kb "openstaxcalculus2016" "3:Theorem 5.9, p. 494"]
theorem fubini_box_dy_dz_dx {f : ℝ × ℝ × ℝ → ℝ} {a₁ b₁ a₂ b₂ a₃ b₃ : ℝ} (h₁ : a₁ ≤ b₁)
    (h₂ : a₂ ≤ b₂) (h₃ : a₃ ≤ b₃) (hf : ContinuousOn f (Icc a₁ b₁ ×ˢ (Icc a₂ b₂ ×ˢ Icc a₃ b₃))) :
    ∫ p in Icc a₁ b₁ ×ˢ (Icc a₂ b₂ ×ˢ Icc a₃ b₃), f p =
      ∫ x in a₁..b₁, ∫ z in a₃..b₃, ∫ y in a₂..b₂, f (x, y, z) := by
  rw [fubini_box_dz_dy_dx h₁ h₂ h₃ hf]
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [uIcc_of_le h₁] at hx
  have hs : ContinuousOn (fun q : ℝ × ℝ => f (x, q)) (Icc a₂ b₂ ×ˢ Icc a₃ b₃) :=
    hf.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun q hq => ⟨hx, hq⟩)
  rw [← fubini_rectangle_dy_dx h₂ h₃ hs, fubini_rectangle_dx_dy h₂ h₃ hs]

/-- OpenStax Calculus 3:§5.4 text, volume as triple integral of 1 (CA-581). The volume of a solid
is the triple integral of the constant `1` over it. -/
@[kb "openstaxcalculus2016" "3:§5.4 text, volume as triple integral of 1, p. 499"]
theorem volume_eq_triple_integral_one (S : Set (ℝ × ℝ × ℝ)) :
    ∫ _ in S, (1 : ℝ) = (volume S).toReal := by
  simp [Measure.real]

/-- OpenStax Calculus 3:Theorem 5.11 (CA-582). The average of `f` over a solid of positive volume
is the triple integral divided by the volume. -/
@[kb "openstaxcalculus2016" "3:Theorem 5.11, p. 503"]
theorem average_value_solid (S : Set (ℝ × ℝ × ℝ)) (f : ℝ × ℝ × ℝ → ℝ) :
    ⨍ p in S, f p = (∫ p in S, f p) / (volume S).toReal := by
  rw [setAverage_eq]
  simp [Measure.real, div_eq_inv_mul]

/-- OpenStax Calculus 3:Example 5.52 (CA-587). The volume of a ball of radius `r ≥ 0` in space is
`(4/3) π r³`. -/
@[kb "openstaxcalculus2016" "3:Example 5.52, p. 524"]
theorem volume_ball_space (x : EuclideanSpace ℝ (Fin 3)) {r : ℝ} (hr : 0 ≤ r) :
    (volume (Metric.ball x r)).toReal = 4 / 3 * Real.pi * r ^ 3 := by
  rw [EuclideanSpace.volume_ball_fin_three, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr, ENNReal.toReal_ofReal (by positivity)]
  ring

/-- OpenStax Calculus 3:Definition (Jacobian of a C^1 transformation, two variables) (CA-600).
The determinant of the derivative of a plane map is `x_u y_v - x_v y_u`, where the partials of
`(x,y)` are the images of the basis vectors. -/
@[kb "openstaxcalculus2016" "3:Definition (Jacobian of a C^1 transformation, two variables), p. 557"]
theorem jacobian_two_variables (T' : ℝ × ℝ →L[ℝ] ℝ × ℝ) :
    T'.det = (T' (1, 0)).1 * (T' (0, 1)).2 - (T' (0, 1)).1 * (T' (1, 0)).2 := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply]

/-- OpenStax Calculus 3:Definition (Jacobian in three variables) (CA-603). The determinant of the
derivative of a map `ℝ³ → ℝ³` is the determinant of the matrix of partial derivatives. -/
@[kb "openstaxcalculus2016" "3:Definition (Jacobian in three variables), p. 563"]
theorem jacobian_three_variables (T' : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) :
    T'.det = Matrix.det (Matrix.of fun i j => T' (Pi.single j 1) i) := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix' (T' : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ))]
  rfl

/-- OpenStax Calculus 3:Theorem 5.14 (CA-602). Change of variables for double integrals: for a
one-to-one `C¹` map `T` taking `S` onto `R`, `∬_R f = ∬_S f(T(u,v)) |x_u y_v - x_v y_u|`. -/
@[kb "openstaxcalculus2016" "3:Theorem 5.14, p. 559"]
theorem change_of_variables_double {S R : Set (ℝ × ℝ)} {T : ℝ × ℝ → ℝ × ℝ}
    {T' : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ × ℝ} (hS : MeasurableSet S) (hR : T '' S = R)
    (hT : ∀ p ∈ S, HasFDerivWithinAt T (T' p) S p) (hinj : InjOn T S) (f : ℝ × ℝ → ℝ) :
    ∫ q in R, f q = ∫ p in S,
      |(T' p (1, 0)).1 * (T' p (0, 1)).2 - (T' p (0, 1)).1 * (T' p (1, 0)).2| * f (T p) := by
  subst hR
  rw [MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul volume hS hT hinj f]
  simp only [jacobian_two_variables, smul_eq_mul]

/-- OpenStax Calculus 3:Theorem 5.15 (CA-604). Change of variables for triple integrals: for a
one-to-one `C¹` map `T : ℝ³ → ℝ³` taking `S` onto `R`, `∭_R f = ∭_S f(T(u)) |det (∂xᵢ/∂uⱼ)|`. -/
@[kb "openstaxcalculus2016" "3:Theorem 5.15, p. 564"]
theorem change_of_variables_triple {S R : Set (Fin 3 → ℝ)} {T : (Fin 3 → ℝ) → (Fin 3 → ℝ)}
    {T' : (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)} (hS : MeasurableSet S) (hR : T '' S = R)
    (hT : ∀ p ∈ S, HasFDerivWithinAt T (T' p) S p) (hinj : InjOn T S) (f : (Fin 3 → ℝ) → ℝ) :
    ∫ q in R, f q = ∫ p in S,
      |Matrix.det (Matrix.of fun i j => T' p (Pi.single j 1) i)| * f (T p) := by
  subst hR
  rw [MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul volume hS hT hinj f]
  simp only [jacobian_three_variables, smul_eq_mul]

/-! ## Results proved in undergrad-kb -/

section ProvedInKB

open UndergradKB.Calculus (typeIRegion typeIIRegion polarRegionBetween regionBetweenClosed)

/-- OpenStax Calculus 3:Theorem 5.4 (CA-567).
For `f` continuous on a Type I region the double integral is the iterated integral with `y` from
`g₁(x)` to `g₂(x)` inside and `x` from `a` to `b` outside; a Type II region reverses the order. -/
@[kb "openstaxcalculus2016" "3:Theorem 5.4, p. 451"]
theorem double_integral_type_I_and_II :
    (∀ {a b : ℝ}, a ≤ b → ∀ {g1 g2 : ℝ → ℝ}, Continuous g1 → Continuous g2 →
      (∀ x ∈ Icc a b, g1 x ≤ g2 x) → ∀ {f : ℝ × ℝ → ℝ},
      ContinuousOn f (typeIRegion a b g1 g2) →
      ∫ p in typeIRegion a b g1 g2, f p = ∫ x in a..b, ∫ y in g1 x..g2 x, f (x, y)) ∧
    (∀ {c d : ℝ}, c ≤ d → ∀ {h1 h2 : ℝ → ℝ}, Continuous h1 → Continuous h2 →
      (∀ y ∈ Icc c d, h1 y ≤ h2 y) → ∀ {f : ℝ × ℝ → ℝ},
      ContinuousOn f (typeIIRegion c d h1 h2) →
      ∫ p in typeIIRegion c d h1 h2, f p = ∫ y in c..d, ∫ x in h1 y..h2 y, f (x, y)) :=
  ⟨fun {_ _} hab {_ _} h1 h2 hle {_} hf => UndergradKB.Calculus.setIntegral_typeI hab h1 h2 hle hf,
    fun {_ _} hcd {_ _} h1 h2 hle {_} hf => UndergradKB.Calculus.setIntegral_typeII hcd h1 h2 hle hf⟩

/-- OpenStax Calculus 3:Theorem 5.7 (CA-569).
For `f` integrable on `[a, ∞) × [c, ∞)`, the integrals over `[a, b] × [c, d]` tend to the improper
double integral as `b, d → ∞`, also when computed as iterated integrals. -/
@[kb "openstaxcalculus2016" "3:Theorem 5.7, p. 462"]
theorem improper_double_integral_limit {a c : ℝ} {f : ℝ × ℝ → ℝ}
    (hf : IntegrableOn f (Ici a ×ˢ Ici c)) :
    Tendsto (fun p : ℝ × ℝ => ∫ x in Icc a p.1 ×ˢ Icc c p.2, f x) atTop
      (𝓝 (∫ x in Ici a ×ˢ Ici c, f x)) ∧
    Tendsto (fun p : ℝ × ℝ => ∫ x in a..p.1, ∫ y in c..p.2, f (x, y)) atTop
      (𝓝 (∫ x in Ici a ×ˢ Ici c, f x)) :=
  ⟨UndergradKB.Calculus.tendsto_setIntegral_Icc_prod_Ici hf,
    UndergradKB.Calculus.tendsto_intervalIntegral_prod_Ici hf⟩

/-- OpenStax Calculus 3:Theorem 5.8 (CA-574).
Over the polar region `α ≤ θ ≤ β`, `h₁(θ) ≤ r ≤ h₂(θ)`, the double integral of a continuous `f` is
`∫∫ f(r cos θ, r sin θ) r dr dθ` with `dr` inside. -/
@[kb "openstaxcalculus2016" "3:Theorem 5.8, p. 477"]
theorem double_integral_polar_region {a b : ℝ} (hab : a ≤ b) (ha : -Real.pi < a)
    (hb : b < Real.pi) {h1 h2 : ℝ → ℝ} (hc1 : Continuous h1) (hc2 : Continuous h2)
    (h0 : ∀ θ, 0 ≤ h1 θ) (hle : ∀ θ, h1 θ ≤ h2 θ) {f : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (polarRegionBetween a b h1 h2)) :
    ∫ p in polarRegionBetween a b h1 h2, f p =
      ∫ θ in a..b, ∫ r in h1 θ..h2 θ, r * f (r * Real.cos θ, r * Real.sin θ) :=
  UndergradKB.Calculus.setIntegral_polarRegionBetween hab ha hb hc1 hc2 h0 hle hf

/-- OpenStax Calculus 3:Theorem 5.10 (CA-580).
The triple integral over a solid between `z = u₁(x, y)` and `z = u₂(x, y)` above a region `D` is
the double integral over `D` of the integral in `z`; for a Type I shadow it is a triple iterated
integral. -/
@[kb "openstaxcalculus2016" "3:Theorem 5.10, p. 496"]
theorem triple_integral_over_solid {D : Set (ℝ × ℝ)} (hD : IsCompact D) {u1 u2 : ℝ × ℝ → ℝ}
    (h1 : Continuous u1) (h2 : Continuous u2) (hle : ∀ x ∈ D, u1 x ≤ u2 x)
    {f : (ℝ × ℝ) × ℝ → ℝ} (hf : ContinuousOn f (regionBetweenClosed u1 u2 D)) :
    ∫ p in regionBetweenClosed u1 u2 D, f p = ∫ x in D, (∫ z in u1 x..u2 x, f (x, z)) :=
  UndergradKB.Calculus.setIntegral_solid hD h1 h2 hle hf

end ProvedInKB

/-! ## Wave 2: Fubini in cylindrical and spherical coordinates -/

/-- OpenStax Calculus 3:Theorem 5.12 (CA-584). Fubini in cylindrical coordinates: for `f` continuous on a cylindrical
box, the triple integral equals the iterated integral of `r f(r cos θ, r sin θ, z)` in any of the six orders. -/
@[kb "openstaxcalculus2016" "3:Theorem 5.12, p. 513"]
theorem fubini_cylindrical_coordinates {a b α β c d : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hα : -Real.pi ≤ α)
    (hαβ : α ≤ β) (hβ : β ≤ Real.pi) (hcd : c ≤ d) {f : (ℝ × ℝ) × ℝ → ℝ}
    (hf : ContinuousOn f (UndergradKB.Calculus.cylindricalCoord '' ((Icc a b ×ˢ Icc α β) ×ˢ Icc c d))) :
    (∫ p in UndergradKB.Calculus.cylindricalCoord '' ((Icc a b ×ˢ Icc α β) ×ˢ Icc c d), f p =
        ∫ r in a..b, ∫ θ in α..β, ∫ z in c..d, r * f ((r * Real.cos θ, r * Real.sin θ), z)) ∧
    (∫ p in UndergradKB.Calculus.cylindricalCoord '' ((Icc a b ×ˢ Icc α β) ×ˢ Icc c d), f p =
        ∫ r in a..b, ∫ z in c..d, ∫ θ in α..β, r * f ((r * Real.cos θ, r * Real.sin θ), z)) ∧
    (∫ p in UndergradKB.Calculus.cylindricalCoord '' ((Icc a b ×ˢ Icc α β) ×ˢ Icc c d), f p =
        ∫ θ in α..β, ∫ r in a..b, ∫ z in c..d, r * f ((r * Real.cos θ, r * Real.sin θ), z)) ∧
    (∫ p in UndergradKB.Calculus.cylindricalCoord '' ((Icc a b ×ˢ Icc α β) ×ˢ Icc c d), f p =
        ∫ θ in α..β, ∫ z in c..d, ∫ r in a..b, r * f ((r * Real.cos θ, r * Real.sin θ), z)) ∧
    (∫ p in UndergradKB.Calculus.cylindricalCoord '' ((Icc a b ×ˢ Icc α β) ×ˢ Icc c d), f p =
        ∫ z in c..d, ∫ r in a..b, ∫ θ in α..β, r * f ((r * Real.cos θ, r * Real.sin θ), z)) ∧
    (∫ p in UndergradKB.Calculus.cylindricalCoord '' ((Icc a b ×ˢ Icc α β) ×ˢ Icc c d), f p =
        ∫ z in c..d, ∫ θ in α..β, ∫ r in a..b, r * f ((r * Real.cos θ, r * Real.sin θ), z)) :=
  UndergradKB.Calculus.fubini_cylindrical ha hab hα hαβ hβ hcd hf

/-- OpenStax Calculus 3:Theorem 5.13 (CA-586). Fubini in spherical coordinates: for `f` continuous on a spherical
box, the triple integral equals the iterated integral of `ρ² sin φ f(ρ sin φ cos θ, ρ sin φ sin θ, ρ cos φ)` in any
of the six orders. -/
@[kb "openstaxcalculus2016" "3:Theorem 5.13, p. 520"]
theorem fubini_spherical_coordinates {a b φ1 φ2 α β : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hφ1 : 0 ≤ φ1)
    (hφ : φ1 ≤ φ2) (hφ2 : φ2 ≤ Real.pi) (hα : -Real.pi ≤ α) (hαβ : α ≤ β) (hβ : β ≤ Real.pi)
    {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContinuousOn f (UndergradKB.Calculus.sphericalCoord ''
      {v : Fin 3 → ℝ | v 0 ∈ Icc a b ∧ v 1 ∈ Icc φ1 φ2 ∧ v 2 ∈ Icc α β})) :
    (∫ p in UndergradKB.Calculus.sphericalCoord '' {v : Fin 3 → ℝ | v 0 ∈ Icc a b ∧ v 1 ∈ Icc φ1 φ2 ∧ v 2 ∈ Icc α β},
        f p = ∫ ρ in a..b, ∫ φ in φ1..φ2, ∫ θ in α..β,
          ρ ^ 2 * Real.sin φ * f (UndergradKB.Calculus.sphericalCoord ![ρ, φ, θ])) ∧
    (∫ p in UndergradKB.Calculus.sphericalCoord '' {v : Fin 3 → ℝ | v 0 ∈ Icc a b ∧ v 1 ∈ Icc φ1 φ2 ∧ v 2 ∈ Icc α β},
        f p = ∫ ρ in a..b, ∫ θ in α..β, ∫ φ in φ1..φ2,
          ρ ^ 2 * Real.sin φ * f (UndergradKB.Calculus.sphericalCoord ![ρ, φ, θ])) ∧
    (∫ p in UndergradKB.Calculus.sphericalCoord '' {v : Fin 3 → ℝ | v 0 ∈ Icc a b ∧ v 1 ∈ Icc φ1 φ2 ∧ v 2 ∈ Icc α β},
        f p = ∫ φ in φ1..φ2, ∫ ρ in a..b, ∫ θ in α..β,
          ρ ^ 2 * Real.sin φ * f (UndergradKB.Calculus.sphericalCoord ![ρ, φ, θ])) ∧
    (∫ p in UndergradKB.Calculus.sphericalCoord '' {v : Fin 3 → ℝ | v 0 ∈ Icc a b ∧ v 1 ∈ Icc φ1 φ2 ∧ v 2 ∈ Icc α β},
        f p = ∫ φ in φ1..φ2, ∫ θ in α..β, ∫ ρ in a..b,
          ρ ^ 2 * Real.sin φ * f (UndergradKB.Calculus.sphericalCoord ![ρ, φ, θ])) ∧
    (∫ p in UndergradKB.Calculus.sphericalCoord '' {v : Fin 3 → ℝ | v 0 ∈ Icc a b ∧ v 1 ∈ Icc φ1 φ2 ∧ v 2 ∈ Icc α β},
        f p = ∫ θ in α..β, ∫ ρ in a..b, ∫ φ in φ1..φ2,
          ρ ^ 2 * Real.sin φ * f (UndergradKB.Calculus.sphericalCoord ![ρ, φ, θ])) ∧
    (∫ p in UndergradKB.Calculus.sphericalCoord '' {v : Fin 3 → ℝ | v 0 ∈ Icc a b ∧ v 1 ∈ Icc φ1 φ2 ∧ v 2 ∈ Icc α β},
        f p = ∫ θ in α..β, ∫ φ in φ1..φ2, ∫ ρ in a..b,
          ρ ^ 2 * Real.sin φ * f (UndergradKB.Calculus.sphericalCoord ![ρ, φ, θ])) :=
  UndergradKB.Calculus.fubini_spherical ha hab hφ1 hφ hφ2 hα hαβ hβ hf

/-! ## Wave 3: further results -/

/-- OpenStax Calculus 3:Definition (double integral over a rectangle) (CA-553).
For `f` continuous on `[a,b] × [c,d]`, the double Riemann sums over the `m × n` grid with arbitrary sample
points in the cells tend to the double integral as both `m` and `n` grow. -/
@[kb "openstaxcalculus2016" "3:Definition (double integral over a rectangle), p. 430"]
theorem double_integral_rectangle_riemann_sums {f : ℝ × ℝ → ℝ} {a b c d : ℝ} (hab : a < b)
    (hcd : c < d) (hf : ContinuousOn f (Icc a b ×ˢ Icc c d))
    (t : ℕ → ℕ → ℕ → ℕ → ℝ × ℝ)
    (ht : ∀ m n, ∀ i < m, ∀ j < n, t m n i j ∈
      Icc (UndergradKB.Calculus.gridPoint a b m i) (UndergradKB.Calculus.gridPoint a b m (i + 1)) ×ˢ
      Icc (UndergradKB.Calculus.gridPoint c d n j) (UndergradKB.Calculus.gridPoint c d n (j + 1))) :
    Tendsto (fun q : ℕ × ℕ => ∑ i ∈ Finset.range q.1, ∑ j ∈ Finset.range q.2,
        f (t q.1 q.2 i j) * (((b - a) / q.1) * ((d - c) / q.2)))
      (atTop ×ˢ atTop) (𝓝 (∫ p in Icc a b ×ˢ Icc c d, f p)) :=
  UndergradKB.Calculus.tendsto_doubleSum hab hcd hf t ht

/-- OpenStax Calculus 3:Definition (Type I and Type II regions) (CA-565).
A region between two vertical lines and two continuous graphs over them (Type I), or between two horizontal
lines and two continuous graphs over them (Type II), is compact. -/
@[kb "openstaxcalculus2016" "3:Definition (Type I and Type II regions), p. 449"]
theorem type_I_and_II_regions_compact (a b c d : ℝ) {g1 g2 h1 h2 : ℝ → ℝ} (hg1 : Continuous g1)
    (hg2 : Continuous g2) (hh1 : Continuous h1) (hh2 : Continuous h2) :
    IsCompact (UndergradKB.Calculus.typeIRegion a b g1 g2) ∧
      IsCompact (UndergradKB.Calculus.typeIIRegion c d h1 h2) :=
  ⟨UndergradKB.Calculus.isCompact_typeIRegion a b hg1 hg2,
    UndergradKB.Calculus.isCompact_typeIIRegion c d hh1 hh2⟩

/-- OpenStax Calculus 3:Definition (joint density function) (CA-570).
If `f` is a joint density of `(X, Y)`, the probability of `(X, Y) ∈ D` is the double integral of `f` over `D`,
and the total integral of `f` is `1`. -/
@[kb "openstaxcalculus2016" "3:Definition (joint density function), p. 463"]
theorem joint_density_function {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X Y : Ω → ℝ} {f : ℝ × ℝ → ENNReal} (hX : Measurable X)
    (hY : Measurable Y) (hf : UndergradKB.Calculus.IsJointDensity P X Y f) :
    (∀ D : Set (ℝ × ℝ), MeasurableSet D → P {ω | (X ω, Y ω) ∈ D} = ∫⁻ p in D, f p) ∧
      ∫⁻ p, f p = 1 :=
  ⟨fun _ hD => UndergradKB.Calculus.IsJointDensity.measure_preimage hX hY hf hD,
    UndergradKB.Calculus.IsJointDensity.lintegral_eq_one hX hY hf⟩

/-- OpenStax Calculus 3:Definition (independent random variables) (CA-571).
Random variables with densities `f₁` and `f₂` are independent exactly when `f₁(x) f₂(y)` is their joint
density. -/
@[kb "openstaxcalculus2016" "3:Definition (independent random variables), p. 463"]
theorem independent_iff_joint_density_product {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    {f₁ f₂ : ℝ → ENNReal} (hf₁ : Measurable f₁) (hf₂ : Measurable f₂)
    (h₁ : P.map X = volume.withDensity f₁) (h₂ : P.map Y = volume.withDensity f₂) :
    ProbabilityTheory.IndepFun X Y P ↔
      UndergradKB.Calculus.IsJointDensity P X Y (fun p => f₁ p.1 * f₂ p.2) :=
  UndergradKB.Calculus.indepFun_iff_jointDensity_mul hX hY hf₁ hf₂ h₁ h₂

/-- OpenStax Calculus 3:Definition (double integral over a polar rectangle, eq. 5.8) (CA-573).
Over a polar rectangle the double integral is the iterated integral of `f(r cos θ, r sin θ) r`, and over the
whole plane the same change of variables holds on `r > 0`, `-π < θ < π`. -/
@[kb "openstaxcalculus2016" "3:Definition (double integral over a polar rectangle, eq. 5.8), p. 474"]
theorem double_integral_polar_rectangle {a b c d : ℝ} (hab : a ≤ b) (ha : -Real.pi < a)
    (hb : b < Real.pi) (hc : 0 ≤ c) (hcd : c ≤ d) {f : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (polarRegionBetween a b (fun _ => c) (fun _ => d))) :
    (∫ p in polarRegionBetween a b (fun _ => c) (fun _ => d), f p =
      ∫ θ in a..b, ∫ r in c..d, r * f (r * Real.cos θ, r * Real.sin θ)) ∧
    (∫ p, f p = ∫ q in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
      q.1 * f (q.1 * Real.cos q.2, q.1 * Real.sin q.2)) :=
  ⟨UndergradKB.Calculus.setIntegral_polarRectangle hab ha hb hc hcd hf,
    UndergradKB.Calculus.integral_plane_polar f⟩

/-- OpenStax Calculus 3:Example 5.32 Analysis (CA-576).
A right circular cone of radius `R` and height `h` has volume `π R² h / 3`. -/
@[kb "openstaxcalculus2016" "3:Example 5.32 Analysis, p. 480"]
theorem volume_right_circular_cone {R h : ℝ} (hh : 0 < h) :
    volume {p : ℝ × ℝ × ℝ | p.1 ∈ Icc 0 h ∧ p.2.1 ^ 2 + p.2.2 ^ 2 ≤ (R * p.1 / h) ^ 2} =
      ENNReal.ofReal (Real.pi * R ^ 2 * h / 3) :=
  UndergradKB.Calculus.volume_cone hh

/-- OpenStax Calculus 3:Definition (triple integral over a box, eq. 5.10) (CA-577).
For `f` continuous on a box, triple Riemann sums over finer and finer subdivisions with arbitrary sample points
tend to the triple integral. -/
@[kb "openstaxcalculus2016" "3:Definition (triple integral over a box, eq. 5.10), p. 494"]
theorem triple_integral_box_riemann_sums {f : ℝ × ℝ × ℝ → ℝ} {a b c d e g : ℝ} (hab : a < b)
    (hcd : c < d) (heg : e < g) (hf : ContinuousOn f (Icc a b ×ˢ (Icc c d ×ˢ Icc e g)))
    (t : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℝ × ℝ × ℝ)
    (ht : ∀ m n l, ∀ i < m, ∀ j < n, ∀ k < l, t m n l i j k ∈
      Icc (UndergradKB.Calculus.gridPoint a b m i) (UndergradKB.Calculus.gridPoint a b m (i + 1)) ×ˢ
      (Icc (UndergradKB.Calculus.gridPoint c d n j) (UndergradKB.Calculus.gridPoint c d n (j + 1)) ×ˢ
        Icc (UndergradKB.Calculus.gridPoint e g l k) (UndergradKB.Calculus.gridPoint e g l (k + 1)))) :
    Tendsto (fun q : ℕ × ℕ × ℕ => ∑ i ∈ Finset.range q.1, ∑ j ∈ Finset.range q.2.1,
        ∑ k ∈ Finset.range q.2.2,
        f (t q.1 q.2.1 q.2.2 i j k) * (((b - a) / q.1) * (((d - c) / q.2.1) * ((g - e) / q.2.2))))
      (atTop ×ˢ (atTop ×ˢ atTop)) (𝓝 (∫ p in Icc a b ×ˢ (Icc c d ×ˢ Icc e g), f p)) :=
  UndergradKB.Calculus.tendsto_tripleSum hab hcd heg hf t ht

/-- OpenStax Calculus 3:Definition (triple integral in cylindrical coordinates, eq. 5.11) (CA-583).
Over a measurable set `R` of `((r, θ), z)` with `r > 0` and `-π < θ < π`, the integral over the image is the
integral over `R` with the volume element `r dz dr dθ`. -/
@[kb "openstaxcalculus2016" "3:Definition (triple integral in cylindrical coordinates, eq. 5.11), p. 513"]
theorem triple_integral_cylindrical_coordinates {R : Set ((ℝ × ℝ) × ℝ)} (hR : MeasurableSet R)
    (hRt : R ⊆ polarCoord.target ×ˢ univ) (f : (ℝ × ℝ) × ℝ → ℝ) :
    ∫ p in UndergradKB.Calculus.cylindricalCoord '' R, f p =
      ∫ q in R, q.1.1 * f (UndergradKB.Calculus.cylindricalCoord q) :=
  UndergradKB.Calculus.setIntegral_cylindricalCoord_image hR hRt f

/-- OpenStax Calculus 3:Definition (triple integral in spherical coordinates) (CA-585).
The Jacobian of the spherical coordinate map is `ρ² sin φ`, and a triple integral over the image of a set `R`
in the spherical domain is the integral over `R` with volume element `ρ² sin φ dρ dφ dθ`. -/
@[kb "openstaxcalculus2016" "3:Definition (triple integral in spherical coordinates), p. 519"]
theorem triple_integral_spherical_coordinates {R : Set (Fin 3 → ℝ)} (hR : MeasurableSet R)
    (hRd : R ⊆ UndergradKB.Calculus.sphericalDomain) (f : (Fin 3 → ℝ) → ℝ) :
    (∀ v : Fin 3 → ℝ,
      (UndergradKB.Calculus.sphericalJacobianMatrix v).det = v 0 ^ 2 * Real.sin (v 1)) ∧
    (∀ v : Fin 3 → ℝ, (UndergradKB.Calculus.sphericalFDeriv v).det = v 0 ^ 2 * Real.sin (v 1)) ∧
    ∫ p in UndergradKB.Calculus.sphericalCoord '' R, f p =
      ∫ v in R, v 0 ^ 2 * Real.sin (v 1) * f (UndergradKB.Calculus.sphericalCoord v) :=
  ⟨UndergradKB.Calculus.det_sphericalJacobianMatrix, UndergradKB.Calculus.det_sphericalFDeriv,
    UndergradKB.Calculus.setIntegral_sphericalCoord_image hR hRd f⟩

/-- OpenStax Calculus 3:Example 5.53 (CA-588).
The solid ellipsoid `x²/a² + y²/b² + z²/c² ≤ 1` has volume `4π a b c / 3`. -/
@[kb "openstaxcalculus2016" "3:Example 5.53, p. 525"]
theorem ellipsoid_volume_formula (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume {p : EuclideanSpace ℝ (Fin 3) | (p 0 / a) ^ 2 + (p 1 / b) ^ 2 + (p 2 / c) ^ 2 ≤ 1} =
      ENNReal.ofReal (4 / 3 * Real.pi * a * b * c) :=
  UndergradKB.Calculus.ellipsoid_volume a b c ha hb hc

/-- OpenStax Calculus 3:§5.6 mass of a lamina (eq. 5.13) (CA-589).
The mass of a lamina is the double integral of its density over the region; for constant density `c` it is `c`
times the area. -/
@[kb "openstaxcalculus2016" "3:§5.6 mass of a lamina (eq. 5.13), p. 537"]
theorem lamina_mass (D : Set (ℝ × ℝ)) (ρ : ℝ × ℝ → ℝ) (c : ℝ) :
    UndergradKB.Calculus.MassMoments.laminaMass D ρ = (∫ p in D, ρ p) ∧
      UndergradKB.Calculus.MassMoments.laminaMass D (fun _ => c) = (volume D).toReal * c :=
  ⟨rfl, UndergradKB.Calculus.MassMoments.laminaMass_const D c⟩

/-- OpenStax Calculus 3:§5.6 moments M_x, M_y of a lamina (CA-590).
The moment about the `x`-axis is the double integral of `y ρ`, the moment about the `y`-axis that of `x ρ`;
the latter vanishes for a region symmetric about the `y`-axis with a density even in `x`. -/
@[kb "openstaxcalculus2016" "3:§5.6 moments M_x, M_y of a lamina, p. 538"]
theorem lamina_moments (D : Set (ℝ × ℝ)) (ρ : ℝ × ℝ → ℝ) :
    UndergradKB.Calculus.MassMoments.laminaMomentX D ρ = (∫ p in D, p.2 * ρ p) ∧
      UndergradKB.Calculus.MassMoments.laminaMomentY D ρ = (∫ p in D, p.1 * ρ p) ∧
      ((fun p : ℝ × ℝ => (-p.1, p.2)) ⁻¹' D = D → (∀ p : ℝ × ℝ, ρ (-p.1, p.2) = ρ p) →
        UndergradKB.Calculus.MassMoments.laminaMomentY D ρ = 0) :=
  ⟨rfl, rfl, fun hD hρ => UndergradKB.Calculus.MassMoments.laminaMomentY_eq_zero_of_symm hD hρ⟩

/-- OpenStax Calculus 3:§5.6 definition of center of mass and centroid (CA-591).
The center of mass of a lamina is `(M_y / m, M_x / m)`; for constant nonzero density it is the centroid, and
for a symmetric lamina its first coordinate is `0`. -/
@[kb "openstaxcalculus2016" "3:§5.6 definition of center of mass and centroid, p. 536"]
theorem lamina_center_of_mass (D : Set (ℝ × ℝ)) (ρ : ℝ × ℝ → ℝ) :
    UndergradKB.Calculus.MassMoments.laminaCenterOfMass D ρ =
      (UndergradKB.Calculus.MassMoments.laminaMomentY D ρ /
          UndergradKB.Calculus.MassMoments.laminaMass D ρ,
        UndergradKB.Calculus.MassMoments.laminaMomentX D ρ /
          UndergradKB.Calculus.MassMoments.laminaMass D ρ) ∧
    (∀ c : ℝ, c ≠ 0 → UndergradKB.Calculus.MassMoments.laminaCenterOfMass D (fun _ => c) =
      ((∫ p in D, p.1) / (volume D).toReal, (∫ p in D, p.2) / (volume D).toReal)) ∧
    ((fun p : ℝ × ℝ => (-p.1, p.2)) ⁻¹' D = D → (∀ p : ℝ × ℝ, ρ (-p.1, p.2) = ρ p) →
      (UndergradKB.Calculus.MassMoments.laminaCenterOfMass D ρ).1 = 0) :=
  ⟨rfl, fun _ hc => UndergradKB.Calculus.MassMoments.laminaCenterOfMass_const D hc,
    fun hD hρ => UndergradKB.Calculus.MassMoments.laminaCenterOfMass_fst_eq_zero_of_symm hD hρ⟩

/-- OpenStax Calculus 3:§5.6 moments of inertia I_x, I_y, I_0 (CA-592).
The moments of inertia about the `x`-axis, `y`-axis and origin are the double integrals of `y² ρ`, `x² ρ` and
`(x² + y²) ρ`, and the polar moment is the sum of the other two. -/
@[kb "openstaxcalculus2016" "3:§5.6 moments of inertia I_x, I_y, I_0, p. 543"]
theorem lamina_moments_of_inertia {D : Set (ℝ × ℝ)} {ρ : ℝ × ℝ → ℝ}
    (hx : IntegrableOn (fun p => p.2 ^ 2 * ρ p) D) (hy : IntegrableOn (fun p => p.1 ^ 2 * ρ p) D) :
    UndergradKB.Calculus.MassMoments.laminaInertiaX D ρ = (∫ p in D, p.2 ^ 2 * ρ p) ∧
      UndergradKB.Calculus.MassMoments.laminaInertiaY D ρ = (∫ p in D, p.1 ^ 2 * ρ p) ∧
      UndergradKB.Calculus.MassMoments.laminaInertiaO D ρ = (∫ p in D, (p.1 ^ 2 + p.2 ^ 2) * ρ p) ∧
      UndergradKB.Calculus.MassMoments.laminaInertiaO D ρ =
        UndergradKB.Calculus.MassMoments.laminaInertiaX D ρ +
          UndergradKB.Calculus.MassMoments.laminaInertiaY D ρ :=
  ⟨rfl, rfl, rfl, UndergradKB.Calculus.MassMoments.laminaInertiaO_eq hx hy⟩

/-- OpenStax Calculus 3:§5.6 radii of gyration (CA-593).
For a nonnegative density with positive mass, the squared radii of gyration about the `x`-axis, `y`-axis and
origin times the mass are the corresponding moments of inertia. -/
@[kb "openstaxcalculus2016" "3:§5.6 radii of gyration, p. 543"]
theorem lamina_radii_of_gyration {D : Set (ℝ × ℝ)} {ρ : ℝ × ℝ → ℝ} (hD : MeasurableSet D)
    (hρ : ∀ p ∈ D, 0 ≤ ρ p) (hm : 0 < UndergradKB.Calculus.MassMoments.laminaMass D ρ) :
    UndergradKB.Calculus.MassMoments.laminaRadiusGyrationX D ρ ^ 2 *
        UndergradKB.Calculus.MassMoments.laminaMass D ρ =
        UndergradKB.Calculus.MassMoments.laminaInertiaX D ρ ∧
      UndergradKB.Calculus.MassMoments.laminaRadiusGyrationY D ρ ^ 2 *
        UndergradKB.Calculus.MassMoments.laminaMass D ρ =
        UndergradKB.Calculus.MassMoments.laminaInertiaY D ρ ∧
      UndergradKB.Calculus.MassMoments.laminaRadiusGyrationO D ρ ^ 2 *
        UndergradKB.Calculus.MassMoments.laminaMass D ρ =
        UndergradKB.Calculus.MassMoments.laminaInertiaO D ρ :=
  ⟨UndergradKB.Calculus.MassMoments.laminaRadiusGyrationX_sq hD hρ hm,
    UndergradKB.Calculus.MassMoments.laminaRadiusGyrationY_sq hD hρ hm,
    UndergradKB.Calculus.MassMoments.laminaRadiusGyrationO_sq hD hρ hm⟩

/-- OpenStax Calculus 3:§5.6 definition (mass of a solid, 3D) (CA-594).
The mass of a solid is the triple integral of its density; for constant density `c` it is `c` times the
volume. -/
@[kb "openstaxcalculus2016" "3:§5.6 definition (mass of a solid, 3D), p. 545"]
theorem solid_mass (E : Set (ℝ × ℝ × ℝ)) (ρ : ℝ × ℝ × ℝ → ℝ) (c : ℝ) :
    UndergradKB.Calculus.MassMoments.solidMass E ρ = (∫ p in E, ρ p) ∧
      UndergradKB.Calculus.MassMoments.solidMass E (fun _ => c) = (volume E).toReal * c :=
  ⟨rfl, UndergradKB.Calculus.MassMoments.solidMass_const E c⟩

/-- OpenStax Calculus 3:§5.6 definition (moments of a solid) (CA-595).
The moments of a solid about the `yz`-, `xz`- and `xy`-planes are the triple integrals of `x ρ`, `y ρ` and
`z ρ`. -/
@[kb "openstaxcalculus2016" "3:§5.6 definition (moments of a solid), p. 545"]
theorem solid_moments (E : Set (ℝ × ℝ × ℝ)) (ρ : ℝ × ℝ × ℝ → ℝ) :
    UndergradKB.Calculus.MassMoments.solidMomentYZ E ρ = (∫ p in E, p.1 * ρ p) ∧
      UndergradKB.Calculus.MassMoments.solidMomentXZ E ρ = (∫ p in E, p.2.1 * ρ p) ∧
      UndergradKB.Calculus.MassMoments.solidMomentXY E ρ = ∫ p in E, p.2.2 * ρ p :=
  ⟨rfl, rfl, rfl⟩

/-- OpenStax Calculus 3:§5.6 definition (center of mass of a solid) (CA-596).
The center of mass of a solid is the vector of the three moments divided by the mass; for constant nonzero
density it is the centroid. -/
@[kb "openstaxcalculus2016" "3:§5.6 definition (center of mass of a solid), p. 545"]
theorem solid_center_of_mass (E : Set (ℝ × ℝ × ℝ)) (ρ : ℝ × ℝ × ℝ → ℝ) :
    UndergradKB.Calculus.MassMoments.solidCenterOfMass E ρ =
      (UndergradKB.Calculus.MassMoments.solidMomentYZ E ρ /
          UndergradKB.Calculus.MassMoments.solidMass E ρ,
        UndergradKB.Calculus.MassMoments.solidMomentXZ E ρ /
          UndergradKB.Calculus.MassMoments.solidMass E ρ,
        UndergradKB.Calculus.MassMoments.solidMomentXY E ρ /
          UndergradKB.Calculus.MassMoments.solidMass E ρ) ∧
    (∀ c : ℝ, c ≠ 0 → UndergradKB.Calculus.MassMoments.solidCenterOfMass E (fun _ => c) =
      ((∫ p in E, p.1) / (volume E).toReal, (∫ p in E, p.2.1) / (volume E).toReal,
        (∫ p in E, p.2.2) / (volume E).toReal)) :=
  ⟨rfl, fun _ hc => UndergradKB.Calculus.MassMoments.solidCenterOfMass_const E hc⟩

/-- OpenStax Calculus 3:§5.6 definition (moments of inertia of a solid) (CA-597).
The moments of inertia of a solid about the coordinate axes are the triple integrals of
`(y² + z²) ρ`, `(x² + z²) ρ`, `(x² + y²) ρ`; together they add up to twice the integral of
`(x² + y² + z²) ρ`. -/
@[kb "openstaxcalculus2016" "3:§5.6 definition (moments of inertia of a solid), p. 545"]
theorem solid_moments_of_inertia {E : Set (ℝ × ℝ × ℝ)} {ρ : ℝ × ℝ × ℝ → ℝ}
    (hx : IntegrableOn (fun p => (p.2.1 ^ 2 + p.2.2 ^ 2) * ρ p) E)
    (hy : IntegrableOn (fun p => (p.1 ^ 2 + p.2.2 ^ 2) * ρ p) E)
    (hz : IntegrableOn (fun p => (p.1 ^ 2 + p.2.1 ^ 2) * ρ p) E) :
    UndergradKB.Calculus.MassMoments.solidInertiaX E ρ = (∫ p in E, (p.2.1 ^ 2 + p.2.2 ^ 2) * ρ p) ∧
      UndergradKB.Calculus.MassMoments.solidInertiaY E ρ = (∫ p in E, (p.1 ^ 2 + p.2.2 ^ 2) * ρ p) ∧
      UndergradKB.Calculus.MassMoments.solidInertiaZ E ρ = (∫ p in E, (p.1 ^ 2 + p.2.1 ^ 2) * ρ p) ∧
      UndergradKB.Calculus.MassMoments.solidInertiaX E ρ +
          UndergradKB.Calculus.MassMoments.solidInertiaY E ρ +
          UndergradKB.Calculus.MassMoments.solidInertiaZ E ρ =
        2 * ∫ p in E, (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) * ρ p :=
  ⟨rfl, rfl, rfl, UndergradKB.Calculus.MassMoments.solidInertia_add hx hy hz⟩

/-- OpenStax Calculus 3:Definition (one-to-one transformation) (CA-599).
A transformation `T` of the plane is one-to-one on a set `S` when distinct points of `S` have distinct
images. -/
@[kb "openstaxcalculus2016" "3:Definition (one-to-one transformation), p. 554"]
theorem one_to_one_transformation (T : ℝ × ℝ → ℝ × ℝ) (S : Set (ℝ × ℝ)) :
    Set.InjOn T S ↔ ∀ p ∈ S, ∀ q ∈ S, T p = T q → p = q :=
  Iff.rfl

/-- OpenStax Calculus 3:Example 5.67 (CA-601).
The Jacobian determinant of the polar coordinate map is `r`, and that of the cylindrical coordinate map is
also `r`. -/
@[kb "openstaxcalculus2016" "3:Example 5.67, p. 557"]
theorem jacobian_polar_and_cylindrical (r θ : ℝ) :
    (fderivPolarCoordSymm (r, θ)).det = r ∧
      ((fderivPolarCoordSymm (r, θ)).prodMap (ContinuousLinearMap.id ℝ ℝ)).det = r :=
  ⟨UndergradKB.Calculus.det_polar_jacobian r θ, UndergradKB.Calculus.det_cylindrical_jacobian r θ⟩

end UndergradKB.Calculus.Course.V3C5
