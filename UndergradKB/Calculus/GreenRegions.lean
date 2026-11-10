import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import UndergradKB.Common.Attr
import UndergradKB.Calculus.GreenParam
import UndergradKB.Calculus.Green
import UndergradKB.Calculus.DivCurl

/-! # Calculus: Green's theorem on parametrized regions

OpenStax Calculus 3 §6.4. From `green_pullback_rect` (Green's theorem pulled back along a `C²` map of a rectangle):
Green's theorem in both forms for a region `D = Φ(R)` that is the image of a rectangle `R` under a `C²` map `Φ`
(injective, orientation preserving: these are the regions with a piecewise smooth boundary `Φ(∂R)` that can be
"straightened" into a rectangle, e.g. disks and ellipses by polar coordinates, regions between two graphs), the
area formulas, regions with a hole swept between two closed curves, invariance of the circulation of a curl-free
field under homotopies of closed curves, and the circulation of the swirl field `(-y, x)/(x²+y²)` around closed
curves that miss a ray from the origin (`0`) and around closed polar graphs `r = ρ(θ) > 0` (`2π`).

What is missing for the book's statement for every region bounded by a piecewise smooth simple closed curve: the
Jordan curve theorem and the straightening of a Jordan region into such pieces; neither is in Mathlib. -/

open MeasureTheory Set Real

namespace UndergradKB.Calculus

/-! ### Edges of a parametrized rectangle -/

section Edges

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasDerivAt_horizontal {Φ : ℝ × ℝ → F} {x c : ℝ} (h : DifferentiableAt ℝ Φ (x, c)) :
    HasDerivAt (fun t => Φ (t, c)) (fderiv ℝ Φ (x, c) (1, 0)) x := by
  exact h.hasFDerivAt.comp_hasDerivAt x ((hasDerivAt_id' x).prodMk (hasDerivAt_const x c))

theorem hasDerivAt_vertical {Φ : ℝ × ℝ → F} {c y : ℝ} (h : DifferentiableAt ℝ Φ (c, y)) :
    HasDerivAt (fun t => Φ (c, t)) (fderiv ℝ Φ (c, y) (0, 1)) y := by
  exact h.hasFDerivAt.comp_hasDerivAt y ((hasDerivAt_const y c).prodMk (hasDerivAt_id' y))

end Edges

theorem hasDerivAt_fst_comp {γ : ℝ → ℝ × ℝ} {v : ℝ × ℝ} {t : ℝ} (h : HasDerivAt γ v t) :
    HasDerivAt (fun t => (γ t).1) v.1 t := by
  exact (hasFDerivAt_fst (𝕜 := ℝ) (p := γ t)).comp_hasDerivAt t h

theorem hasDerivAt_snd_comp {γ : ℝ → ℝ × ℝ} {v : ℝ × ℝ} {t : ℝ} (h : HasDerivAt γ v t) :
    HasDerivAt (fun t => (γ t).2) v.2 t := by
  exact (hasFDerivAt_snd (𝕜 := ℝ) (p := γ t)).comp_hasDerivAt t h

/-! ### The work form of a planar field -/

/-- Bridging definition: the Jacobian determinant `x_u y_v - x_v y_u` of a map `Φ(u, v) = (x, y)` of the plane. -/
noncomputable def jacobian2 (Φ : ℝ × ℝ → ℝ × ℝ) (z : ℝ × ℝ) : ℝ :=
  (fderiv ℝ Φ z (1, 0)).1 * (fderiv ℝ Φ z (0, 1)).2 - (fderiv ℝ Φ z (1, 0)).2 * (fderiv ℝ Φ z (0, 1)).1

/-- The work form `v ↦ P v₁ + Q v₂` of the planar field `(P, Q)`. -/
noncomputable def planeForm (P Q : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  P p • ContinuousLinearMap.fst ℝ ℝ ℝ + Q p • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem planeForm_apply (P Q : ℝ × ℝ → ℝ) (p v : ℝ × ℝ) : planeForm P Q p v = P p * v.1 + Q p * v.2 := by
  simp [planeForm]

theorem contDiffOn_planeForm {P Q : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hP : ContDiffOn ℝ 1 P U)
    (hQ : ContDiffOn ℝ 1 Q U) : ContDiffOn ℝ 1 (planeForm P Q) U :=
  (hP.smul contDiffOn_const).add (hQ.smul contDiffOn_const)

/-- A linear form on the plane in terms of its values on the coordinate vectors. -/
theorem clm_plane_apply (L : ℝ × ℝ →L[ℝ] ℝ) (v : ℝ × ℝ) : L v = v.1 * L (1, 0) + v.2 * L (0, 1) := by
  have : v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
  conv_lhs => rw [this]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- `dω(a, b) = (Q_x - P_y)(a₁ b₂ - a₂ b₁)` for the work form of `(P, Q)`. -/
theorem planeForm_d {P Q : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hP : DifferentiableAt ℝ P p)
    (hQ : DifferentiableAt ℝ Q p) (a b : ℝ × ℝ) :
    fderiv ℝ (planeForm P Q) p a b - fderiv ℝ (planeForm P Q) p b a =
      curl2 P Q p * (a.1 * b.2 - a.2 * b.1) := by
  have h : HasFDerivAt (planeForm P Q)
      ((fderiv ℝ P p).smulRight (ContinuousLinearMap.fst ℝ ℝ ℝ) +
        (fderiv ℝ Q p).smulRight (ContinuousLinearMap.snd ℝ ℝ ℝ)) p :=
    (hP.hasFDerivAt.smul_const (ContinuousLinearMap.fst ℝ ℝ ℝ)).add
      (hQ.hasFDerivAt.smul_const (ContinuousLinearMap.snd ℝ ℝ ℝ))
  rw [h.fderiv]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, smul_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_eq_mul]
  rw [clm_plane_apply (fderiv ℝ P p) a, clm_plane_apply (fderiv ℝ P p) b, clm_plane_apply (fderiv ℝ Q p) a,
    clm_plane_apply (fderiv ℝ Q p) b, curl2, pdx2, pdy2]
  ring

theorem greenLineIntegral_horizontal (P Q : ℝ × ℝ → ℝ) {Φ : ℝ × ℝ → ℝ × ℝ} (hΦ : Differentiable ℝ Φ)
    (c a b : ℝ) :
    greenLineIntegral P Q (fun t => (Φ (t, c)).1) (fun t => (Φ (t, c)).2) a b =
      ∫ t in a..b, planeForm P Q (Φ (t, c)) (fderiv ℝ Φ (t, c) (1, 0)) := by
  unfold greenLineIntegral
  congr 1
  ext t
  have h := hasDerivAt_horizontal (hΦ (t, c))
  rw [(hasDerivAt_fst_comp h).deriv, (hasDerivAt_snd_comp h).deriv, planeForm_apply]

theorem greenLineIntegral_vertical (P Q : ℝ × ℝ → ℝ) {Φ : ℝ × ℝ → ℝ × ℝ} (hΦ : Differentiable ℝ Φ)
    (c a b : ℝ) :
    greenLineIntegral P Q (fun t => (Φ (c, t)).1) (fun t => (Φ (c, t)).2) a b =
      ∫ t in a..b, planeForm P Q (Φ (c, t)) (fderiv ℝ Φ (c, t) (0, 1)) := by
  unfold greenLineIntegral
  congr 1
  ext t
  have h := hasDerivAt_vertical (hΦ (c, t))
  rw [(hasDerivAt_fst_comp h).deriv, (hasDerivAt_snd_comp h).deriv, planeForm_apply]

/-! ### Green's theorem on a parametrized region -/

/-- OpenStax Calculus 3:Theorem 6.12 (CA-632), circulation form of Green's theorem pulled back to the parameter
rectangle: for a field `(P, Q)` of class `C¹` on an open set `U` and a `C²` map `Φ` of the rectangle
`[a,b]×[c,d]` into `U`, the integral over the rectangle of `(Q_x - P_y)(Φ) · det DΦ` equals the circulation of
`(P, Q)` around the image of the boundary (the images of the bottom and right edges forward, of the top and left edges
backward). -/
@[kb "openstaxcalculus2016" "3:Theorem 6.12, p. 644"]
theorem green_param (P Q : ℝ × ℝ → ℝ) (Φ : ℝ × ℝ → ℝ × ℝ) {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) (hΦ : ContDiff ℝ 2 Φ) {a b c d : ℝ}
    (hΦU : ∀ z ∈ uIcc a b ×ˢ uIcc c d, Φ z ∈ U) :
    (∫ x in a..b, ∫ y in c..d, curl2 P Q (Φ (x, y)) * jacobian2 Φ (x, y)) =
      greenLineIntegral P Q (fun t => (Φ (t, c)).1) (fun t => (Φ (t, c)).2) a b +
        greenLineIntegral P Q (fun t => (Φ (b, t)).1) (fun t => (Φ (b, t)).2) c d -
        greenLineIntegral P Q (fun t => (Φ (t, d)).1) (fun t => (Φ (t, d)).2) a b -
        greenLineIntegral P Q (fun t => (Φ (a, t)).1) (fun t => (Φ (a, t)).2) c d := by
  have hd : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  rw [greenLineIntegral_horizontal P Q hd, greenLineIntegral_vertical P Q hd,
    greenLineIntegral_horizontal P Q hd, greenLineIntegral_vertical P Q hd,
    ← green_pullback_rect (planeForm P Q) Φ hU (contDiffOn_planeForm hP hQ) hΦ hΦU]
  refine intervalIntegral.integral_congr (fun x hx => intervalIntegral.integral_congr (fun y hy => ?_))
  have hm : Φ (x, y) ∈ U := hΦU _ ⟨hx, hy⟩
  have hPd : DifferentiableAt ℝ P (Φ (x, y)) :=
    (hP.differentiableOn one_ne_zero _ hm).differentiableAt (hU.mem_nhds hm)
  have hQd : DifferentiableAt ℝ Q (Φ (x, y)) :=
    (hQ.differentiableOn one_ne_zero _ hm).differentiableAt (hU.mem_nhds hm)
  rw [planeForm_d hPd hQd, jacobian2]

/-- The determinant of a linear map of the plane. -/
theorem det_plane (L : ℝ × ℝ →L[ℝ] ℝ × ℝ) :
    L.det = (L (1, 0)).1 * (L (0, 1)).2 - (L (1, 0)).2 * (L (0, 1)).1 := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, Module.Basis.finTwoProd_zero, Module.Basis.finTwoProd_one,
    Module.Basis.coe_finTwoProd_repr, ContinuousLinearMap.coe_coe]
  simp
  ring

/-- A set integral over a closed rectangle of a function continuous there is the iterated interval integral. -/
theorem setIntegral_Icc_prod {f : ℝ × ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hf : ContinuousOn f (Icc a b ×ˢ Icc c d)) :
    ∫ p in Icc a b ×ˢ Icc c d, f p = ∫ x in a..b, ∫ y in c..d, f (x, y) := by
  have hi : IntegrableOn f (Icc a b ×ˢ Icc c d) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hf.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [Measure.volume_eq_prod, setIntegral_prod _ hi]
  simp only [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    ← intervalIntegral.integral_of_le hcd]

/-- A set between the open and the closed rectangle is almost everywhere equal to the closed rectangle. -/
theorem ae_eq_Icc_prod {S : Set (ℝ × ℝ)} {a b c d : ℝ} (hSsub : S ⊆ Icc a b ×ˢ Icc c d)
    (hSsup : Ioo a b ×ˢ Ioo c d ⊆ S) : S =ᵐ[volume] (Icc a b ×ˢ Icc c d : Set (ℝ × ℝ)) := by
  have h : (Ioo a b ×ˢ Ioo c d : Set (ℝ × ℝ)) =ᵐ[volume] (Icc a b ×ˢ Icc c d : Set (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc
  refine (Filter.EventuallyLE.antisymm (Filter.Eventually.of_forall hSsub) ?_)
  exact h.symm.le.trans (Filter.Eventually.of_forall hSsup)

/-- `curl2 P Q` is continuous on an open set where `P, Q` are `C¹`. -/
theorem continuousOn_curl2 {P Q : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) : ContinuousOn (curl2 P Q) U := by
  have cP := hP.continuousOn_fderiv_of_isOpen hU le_rfl
  have cQ := hQ.continuousOn_fderiv_of_isOpen hU le_rfl
  exact (cQ.clm_apply continuousOn_const).sub (cP.clm_apply continuousOn_const)

theorem continuous_jacobian2 {Φ : ℝ × ℝ → ℝ × ℝ} (hΦ : ContDiff ℝ 2 Φ) : Continuous (jacobian2 Φ) := by
  have c := hΦ.continuous_fderiv (by norm_num)
  have c1 : Continuous fun z => fderiv ℝ Φ z (1, 0) := c.clm_apply continuous_const
  have c2 : Continuous fun z => fderiv ℝ Φ z (0, 1) := c.clm_apply continuous_const
  unfold jacobian2
  fun_prop

/-- OpenStax Calculus 3:Theorem 6.12 (CA-632), circulation form of Green's theorem on a parametrized region:
let `D = Φ(S)` where `S` lies between the open and the closed rectangle `[a,b]×[c,d]`, `Φ` is `C²`, injective on
`S` and orientation preserving (`det DΦ ≥ 0` on `S`), so that the boundary of `D` is the image of the boundary of
the rectangle traversed counterclockwise. For a field `(P, Q)` of class `C¹` on an open set containing `Φ` of the
rectangle, `∬_D (Q_x - P_y) dA = ∮_{∂D} P dx + Q dy` (the four image edges). Examples: disks and ellipses (polar
coordinates, `S = (0,R]×[0,2π)`), regions between two graphs (`Φ(s,x) = (x, (1-s) g₁ x + s g₂ x)`). -/
@[kb "openstaxcalculus2016" "3:Theorem 6.12, p. 644"]
theorem green_param_image (P Q : ℝ × ℝ → ℝ) (Φ : ℝ × ℝ → ℝ × ℝ) {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) (hΦ : ContDiff ℝ 2 Φ) {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hΦU : ∀ z ∈ Icc a b ×ˢ Icc c d, Φ z ∈ U) {S : Set (ℝ × ℝ)}
    (hS : MeasurableSet S) (hSsub : S ⊆ Icc a b ×ˢ Icc c d) (hSsup : Ioo a b ×ˢ Ioo c d ⊆ S)
    (hinj : InjOn Φ S) (hjac : ∀ z ∈ S, 0 ≤ jacobian2 Φ z) :
    ∫ p in Φ '' S, curl2 P Q p =
      greenLineIntegral P Q (fun t => (Φ (t, c)).1) (fun t => (Φ (t, c)).2) a b +
        greenLineIntegral P Q (fun t => (Φ (b, t)).1) (fun t => (Φ (b, t)).2) c d -
        greenLineIntegral P Q (fun t => (Φ (t, d)).1) (fun t => (Φ (t, d)).2) a b -
        greenLineIntegral P Q (fun t => (Φ (a, t)).1) (fun t => (Φ (a, t)).2) c d := by
  have hd : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hS
    (fun z _ => (hd z).hasFDerivAt.hasFDerivWithinAt) hinj]
  rw [setIntegral_congr_fun hS (g := fun z => curl2 P Q (Φ z) * jacobian2 Φ z) (fun z hz => by
    simp only [smul_eq_mul]
    rw [det_plane, ← jacobian2, abs_of_nonneg (hjac z hz), mul_comm])]
  rw [setIntegral_congr_set (ae_eq_Icc_prod hSsub hSsup)]
  rw [setIntegral_Icc_prod (f := fun z => curl2 P Q (Φ z) * jacobian2 Φ z) hab hcd
    (((continuousOn_curl2 hU hP hQ).comp hΦ.continuous.continuousOn
    (fun z hz => hΦU z hz)).mul (continuous_jacobian2 hΦ).continuousOn)]
  exact green_param P Q Φ hU hP hQ hΦ (by rwa [uIcc_of_le hab, uIcc_of_le hcd])

/-- OpenStax Calculus 3:Theorem 6.13 (CA-634), flux form of Green's theorem on a parametrized region (same
hypotheses as `green_param_image`): `∬_D (P_x + Q_y) dA = ∮_{∂D} P dy - Q dx`, the outward flux of `(P, Q)` across
the boundary, written as the circulation of `(-Q, P)` along the four image edges. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.13, p. 650"]
theorem green_flux_param_image (P Q : ℝ × ℝ → ℝ) (Φ : ℝ × ℝ → ℝ × ℝ) {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) (hΦ : ContDiff ℝ 2 Φ) {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hΦU : ∀ z ∈ Icc a b ×ˢ Icc c d, Φ z ∈ U) {S : Set (ℝ × ℝ)}
    (hS : MeasurableSet S) (hSsub : S ⊆ Icc a b ×ˢ Icc c d) (hSsup : Ioo a b ×ˢ Ioo c d ⊆ S)
    (hinj : InjOn Φ S) (hjac : ∀ z ∈ S, 0 ≤ jacobian2 Φ z) :
    ∫ p in Φ '' S, div2 P Q p =
      greenLineIntegral (fun p => -Q p) P (fun t => (Φ (t, c)).1) (fun t => (Φ (t, c)).2) a b +
        greenLineIntegral (fun p => -Q p) P (fun t => (Φ (b, t)).1) (fun t => (Φ (b, t)).2) c d -
        greenLineIntegral (fun p => -Q p) P (fun t => (Φ (t, d)).1) (fun t => (Φ (t, d)).2) a b -
        greenLineIntegral (fun p => -Q p) P (fun t => (Φ (a, t)).1) (fun t => (Φ (a, t)).2) c d := by
  have h : curl2 (fun p => -Q p) P = div2 P Q := by
    funext p
    have hn : fderiv ℝ (fun p => -Q p) p = -fderiv ℝ Q p := fderiv_neg
    simp only [curl2, div2, pdy2, pdx2, hn, neg_apply]
    ring
  rw [← h]
  exact green_param_image _ _ Φ hU hQ.neg hP hΦ hab hcd hΦU hS hSsub hSsup hinj hjac

/-- Area by Green's theorem, the general step: if `Q_x - P_y = 1`, the area of the parametrized region is the
circulation of `(P, Q)` around its boundary. -/
theorem area_param_image_of_curl2_eq_one (P Q : ℝ × ℝ → ℝ) (hP : ContDiff ℝ 1 P) (hQ : ContDiff ℝ 1 Q)
    (h1 : curl2 P Q = fun _ => 1) (Φ : ℝ × ℝ → ℝ × ℝ) (hΦ : ContDiff ℝ 2 Φ) {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) {S : Set (ℝ × ℝ)}
    (hS : MeasurableSet S) (hSsub : S ⊆ Icc a b ×ˢ Icc c d) (hSsup : Ioo a b ×ˢ Ioo c d ⊆ S)
    (hinj : InjOn Φ S) (hjac : ∀ z ∈ S, 0 ≤ jacobian2 Φ z) :
    (volume (Φ '' S)).toReal =
      greenLineIntegral P Q (fun t => (Φ (t, c)).1) (fun t => (Φ (t, c)).2) a b +
        greenLineIntegral P Q (fun t => (Φ (b, t)).1) (fun t => (Φ (b, t)).2) c d -
        greenLineIntegral P Q (fun t => (Φ (t, d)).1) (fun t => (Φ (t, d)).2) a b -
        greenLineIntegral P Q (fun t => (Φ (a, t)).1) (fun t => (Φ (a, t)).2) c d := by
  rw [← green_param_image P Q Φ isOpen_univ hP.contDiffOn hQ.contDiffOn hΦ hab hcd
    (fun _ _ => mem_univ _) hS hSsub hSsup hinj hjac, h1, setIntegral_const, smul_eq_mul, mul_one,
    measureReal_def]

theorem curl2_zero_fst : curl2 (fun _ => 0) (fun p : ℝ × ℝ => p.1) = fun _ => 1 := by
  funext p
  simp [curl2, pdx2, pdy2, (hasFDerivAt_fst (p := p)).fderiv]

theorem curl2_neg_snd_zero : curl2 (fun p : ℝ × ℝ => -p.2) (fun _ => 0) = fun _ => 1 := by
  funext p
  simp [curl2, pdx2, pdy2, (hasFDerivAt_snd (p := p)).fderiv]

theorem curl2_half : curl2 (fun p : ℝ × ℝ => -p.2 / 2) (fun p : ℝ × ℝ => p.1 / 2) = fun _ => 1 := by
  funext p
  have h1 : HasFDerivAt (fun q : ℝ × ℝ => q.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) p := hasFDerivAt_fst
  have h2 : HasFDerivAt (fun q : ℝ × ℝ => q.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) p := hasFDerivAt_snd
  have h3 : HasFDerivAt (fun q : ℝ × ℝ => q.1 / 2) ((1 / 2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ) p := by
    convert h1.const_smul (1 / 2 : ℝ) using 1
    funext q; simp; ring
  have h4 : HasFDerivAt (fun q : ℝ × ℝ => -q.2 / 2) ((-1 / 2 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
    convert h2.const_smul (-1 / 2 : ℝ) using 1
    funext q; simp; ring
  rw [curl2, pdx2, pdy2, h3.fderiv, h4.fderiv]
  simp
  norm_num

/-- OpenStax Calculus 3:Equation 6.14 (CA-633), area of a parametrized region by Green's theorem (hypotheses on
`Φ` and `S` as in `green_param_image`): the area of `D = Φ(S)` is `∮_{∂D} x dy`, also `-∮_{∂D} y dx` and
`½ ∮_{∂D} (x dy - y dx)`, each line integral taken along the four image edges. -/
@[kb "openstaxcalculus2016" "3:Equation 6.14, p. 650"]
theorem area_param_image (Φ : ℝ × ℝ → ℝ × ℝ) (hΦ : ContDiff ℝ 2 Φ) {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) {S : Set (ℝ × ℝ)}
    (hS : MeasurableSet S) (hSsub : S ⊆ Icc a b ×ˢ Icc c d) (hSsup : Ioo a b ×ˢ Ioo c d ⊆ S)
    (hinj : InjOn Φ S) (hjac : ∀ z ∈ S, 0 ≤ jacobian2 Φ z) :
    let circ := fun P Q : ℝ × ℝ → ℝ =>
      greenLineIntegral P Q (fun t => (Φ (t, c)).1) (fun t => (Φ (t, c)).2) a b +
        greenLineIntegral P Q (fun t => (Φ (b, t)).1) (fun t => (Φ (b, t)).2) c d -
        greenLineIntegral P Q (fun t => (Φ (t, d)).1) (fun t => (Φ (t, d)).2) a b -
        greenLineIntegral P Q (fun t => (Φ (a, t)).1) (fun t => (Φ (a, t)).2) c d
    (volume (Φ '' S)).toReal = circ (fun _ => 0) (fun p => p.1) ∧
      (volume (Φ '' S)).toReal = circ (fun p => -p.2) (fun _ => 0) ∧
      (volume (Φ '' S)).toReal = circ (fun p => -p.2 / 2) (fun p => p.1 / 2) :=
  ⟨area_param_image_of_curl2_eq_one _ _ contDiff_const contDiff_fst curl2_zero_fst Φ hΦ hab hcd hS hSsub
      hSsup hinj hjac,
    area_param_image_of_curl2_eq_one _ _ contDiff_snd.neg contDiff_const curl2_neg_snd_zero Φ hΦ hab hcd hS
      hSsub hSsup hinj hjac,
    area_param_image_of_curl2_eq_one _ _ (contDiff_snd.neg.div_const 2) (contDiff_fst.div_const 2) curl2_half
      Φ hΦ hab hcd hS hSsub hSsup hinj hjac⟩

end UndergradKB.Calculus
