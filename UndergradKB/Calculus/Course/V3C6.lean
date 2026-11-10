import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.Topology.Connected.PathConnected
import UndergradKB.Calculus.CurlDivLimits
import UndergradKB.Calculus.DivCurl
import UndergradKB.Calculus.SourceFree
import UndergradKB.Calculus.LineIntegralLimits
import UndergradKB.Calculus.LineIntegrals
import UndergradKB.Calculus.Surfaces
import UndergradKB.Common.Attr

/-! Course layer, OpenStax Calculus Volume 3, Chapter 6 (vector calculus). -/

namespace UndergradKB.Calculus.Course.V3C6

open Filter Topology Set

/-- OpenStax Calculus 3:Theorem 6.1 (CA-608). On an open connected domain, two potential
functions of the same conservative field (same gradient) differ by a constant. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.1, p. 597"]
theorem potential_unique_up_to_constant {D : Set (EuclideanSpace ℝ (Fin 2))} (hD : IsOpen D)
    (hc : IsPreconnected D) {f g : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : DifferentiableOn ℝ f D)
    (hg : DifferentiableOn ℝ g D) (h : ∀ x ∈ D, gradient f x = gradient g x) :
    ∃ c : ℝ, ∀ x ∈ D, f x = g x + c := by
  obtain ⟨c, hc'⟩ := hD.exists_eq_add_of_fderiv_eq hc hf hg (fun x hx => by
    ext v
    rw [← inner_gradient_left, ← inner_gradient_left, h x hx])
  exact ⟨c, fun x hx => hc' hx⟩

/-- OpenStax Calculus 3:Theorem 6.2 (CA-609). Symmetry of mixed partials of a potential: if `f` is
`C²` near `p` then the partial in direction `v` of the partial in direction `w` equals the partial
in direction `w` of the partial in direction `v`. For a field `F = ∇f = (P, Q)` (resp. `(P,Q,R)`),
take `v, w` coordinate vectors to get `P_y = Q_x` (resp. `P_z = R_x`, `Q_z = R_y`). -/
@[kb "openstaxcalculus2016" "3:Theorem 6.2, p. 598"]
theorem mixed_partials_of_potential {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {p : E} (hf : ContDiffAt ℝ 2 f p) (v w : E) :
    lineDeriv ℝ (fun q => lineDeriv ℝ f q w) p v =
      lineDeriv ℝ (fun q => lineDeriv ℝ f q v) p w := by
  have hev : ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ f q := by
    have := hf.eventually (by simp)
    exact this.mono fun q hq => hq.differentiableAt (by norm_num)
  have hd1 : DifferentiableAt ℝ (fderiv ℝ f) p :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsymm := (hf.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField])) v w
  have key : ∀ u z : E, HasLineDerivAt ℝ (fun q => lineDeriv ℝ f q u)
      (fderiv ℝ (fderiv ℝ f) p z u) p z := by
    intro u z
    have h1 : HasFDerivAt (fun q => fderiv ℝ f q u) ((ContinuousLinearMap.apply ℝ ℝ u).comp
        (fderiv ℝ (fderiv ℝ f) p)) p :=
      (ContinuousLinearMap.apply ℝ ℝ u).hasFDerivAt.comp p hd1.hasFDerivAt
    have h2 := h1.hasLineDerivAt z
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards [hev] with q hq
    exact hq.lineDeriv_eq_fderiv
  rw [(key w v).lineDeriv, (key v w).lineDeriv, hsymm]

/-- OpenStax Calculus 3:Theorem 6.2 (CA-609). The planar instance: `P_y = Q_x` for `P = f_x`,
`Q = f_y`. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.2, p. 598"]
theorem mixed_partials_plane {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hf : ContDiffAt ℝ 2 f p) :
    lineDeriv ℝ (fun q => lineDeriv ℝ f q (1, 0)) p (0, 1) =
      lineDeriv ℝ (fun q => lineDeriv ℝ f q (0, 1)) p (1, 0) :=
  mixed_partials_of_potential hf (0, 1) (1, 0)

/-- OpenStax Calculus 3:Theorem 6.5 (CA-619). Line integrals are additive in the field. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.5, p. 612"]
theorem line_integral_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : E}
    {ω₁ ω₂ : E → E →L[ℝ] ℝ} {γ : Path a b} (h₁ : CurveIntegrable ω₁ γ)
    (h₂ : CurveIntegrable ω₂ γ) :
    curveIntegral (ω₁ + ω₂) γ = curveIntegral ω₁ γ + curveIntegral ω₂ γ :=
  curveIntegral_add h₁ h₂

/-- OpenStax Calculus 3:Theorem 6.5 (CA-619). Line integrals commute with constant multiples. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.5, p. 612"]
theorem line_integral_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : E}
    (c : ℝ) (ω : E → E →L[ℝ] ℝ) (γ : Path a b) :
    curveIntegral (c • ω) γ = c * curveIntegral ω γ := by
  rw [curveIntegral_smul, smul_eq_mul]

/-- OpenStax Calculus 3:Theorem 6.5 (CA-619). Reversing the orientation of the curve changes the
sign of the line integral. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.5, p. 612"]
theorem line_integral_reverse {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : E}
    (ω : E → E →L[ℝ] ℝ) (γ : Path a b) :
    curveIntegral ω γ.symm = -curveIntegral ω γ :=
  curveIntegral_symm ω γ

/-- OpenStax Calculus 3:Theorem 6.5 (CA-619). The line integral over a concatenation of curves is
the sum of the line integrals. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.5, p. 612"]
theorem line_integral_concat {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b c : E}
    {ω : E → E →L[ℝ] ℝ} {γ₁ : Path a b} {γ₂ : Path b c} (h₁ : CurveIntegrable ω γ₁)
    (h₂ : CurveIntegrable ω γ₂) :
    curveIntegral ω (γ₁.trans γ₂) = curveIntegral ω γ₁ + curveIntegral ω γ₂ :=
  curveIntegral_trans h₁ h₂

/-- OpenStax Calculus 3:§6.3 Definition (connected, simply connected regions) (CA-624). A region
`D` of the plane is simply connected iff it is path connected and every loop in it can be
contracted to a point inside it. -/
@[kb "openstaxcalculus2016" "3:§6.3 Definition (connected, simply connected regions), p. 626"]
theorem simply_connected_region_iff (D : Set (ℝ × ℝ)) :
    SimplyConnectedSpace D ↔
      IsPathConnected D ∧ ∀ (x : D) (γ : Path x x), γ.Homotopic (Path.refl x) := by
  rw [simply_connected_iff_loops_nullhomotopic, isPathConnected_iff_pathConnectedSpace]

/-- OpenStax Calculus 3:§6.4 Definition (harmonic function) (CA-637). A function on the plane is
harmonic at `p` iff it is `C²` near `p` and `f_xx + f_yy = 0` near `p`. -/
@[kb "openstaxcalculus2016" "3:§6.4 Definition (harmonic function), p. 655"]
theorem harmonic_iff_laplace {f : EuclideanSpace ℝ (Fin 2) → ℝ} {p : EuclideanSpace ℝ (Fin 2)} :
    InnerProductSpace.HarmonicAt f p ↔ ContDiffAt ℝ 2 f p ∧
      ∀ᶠ x in 𝓝 p, fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1) +
        fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single 1 1) (EuclideanSpace.single 1 1) = 0 := by
  unfold InnerProductSpace.HarmonicAt
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin 2) ℝ)]
  simp [Fin.sum_univ_two, iteratedFDeriv_two_apply, Filter.EventuallyEq]

/-! ## Results proved in undergrad-kb -/

section ProvedInKB

open Matrix
open UndergradKB.Calculus (lineIntegral lineIntegral2 IsConservativeOn IsPathIndependentOn
  IsConservative2 IsConservative3 form2 scalarLineIntegral scalarLineIntegral2
  scalarLineIntegral3 arcLength2 lineArcLength3 flux2 speed2 pdx2 pdy2 pdx3 pdy3 pdz3 div2 div3
  curl2 curl3 laplacian2 IsStreamFunction sphereParam cylinderParam coneParam graphParam
  revolutionParam paramSurfaceArea scalarSurfaceIntegral surfaceFlux unitNormal surfNormal
  surfVnorm IsRegularParam sphereNormal lineSpeed3)

/-- OpenStax Calculus 3:§6.2 Definition (scalar line integral) (CA-610).
For a `C¹` curve `r` and continuous `f`, the Riemann sums `∑ f(r tᵢ) ‖r tᵢ₊₁ - r tᵢ‖` over equal
parameter steps converge to `∫ f(r t) ‖r' t‖ dt`. -/
@[kb "openstaxcalculus2016" "3:§6.2 Definition (scalar line integral), p. 602"]
theorem scalar_line_integral_riemann_sums {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℝ → E} (hr : ContDiff ℝ 1 r) {f : E → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n,
        f (r (a + i * (b - a) / n)) * ‖r (a + (i + 1) * (b - a) / n) - r (a + i * (b - a) / n)‖)
      atTop (𝓝 (∫ t in a..b, f (r t) * ‖deriv r t‖)) :=
  UndergradKB.Calculus.LineIntegralLimits.line_integral_riemann_sums hr hf hab

/-- OpenStax Calculus 3:Theorem 6.3 (CA-612).
The scalar line integral along a smooth curve is `∫ f(r t) ‖r' t‖ dt`; in the plane the norm is
`√(x'² + y'²)`. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.3, p. 605"]
theorem scalar_line_integral_formula :
    (∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (r : ℝ → E) (a b : ℝ),
      scalarLineIntegral f r a b = ∫ t in a..b, f (r t) * ‖deriv r t‖) ∧
    (∀ (f : ℝ × ℝ → ℝ) (x y : ℝ → ℝ) (a b : ℝ), scalarLineIntegral2 f x y a b =
      ∫ t in a..b, f (x t, y t) * √(deriv x t ^ 2 + deriv y t ^ 2)) :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

/-- OpenStax Calculus 3:§6.2 Fact (arc length as line integral) (CA-613).
The scalar line integral of the constant function `1` is the arc length (plane and space). -/
@[kb "openstaxcalculus2016" "3:§6.2 Fact (arc length as line integral), p. 607"]
theorem arc_length_as_line_integral :
    (∀ (x y : ℝ → ℝ) (a b : ℝ), scalarLineIntegral2 (fun _ => 1) x y a b = arcLength2 x y a b) ∧
    (∀ (x y z : ℝ → ℝ) (a b : ℝ),
      scalarLineIntegral3 (fun _ => 1) x y z a b = lineArcLength3 x y z a b) :=
  ⟨UndergradKB.Calculus.scalarLineIntegral2_one, UndergradKB.Calculus.scalarLineIntegral3_one⟩

/-- OpenStax Calculus 3:§6.2 Definition (vector line integral) (CA-616).
The vector line integral `∫ F(r t) · r'(t) dt` is unchanged by a `C¹` reparametrization and changes
sign when the orientation is reversed. -/
@[kb "openstaxcalculus2016" "3:§6.2 Definition (vector line integral), p. 608"]
theorem vector_line_integral_invariance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ω : E → E →L[ℝ] ℝ} {U : Set E} (hω : ContinuousOn ω U) {r : ℝ → E} (hr : ContDiff ℝ 1 r) :
    (∀ {φ : ℝ → ℝ}, ContDiff ℝ 1 φ → ∀ {c d : ℝ}, (∀ s ∈ uIcc c d, r (φ s) ∈ U) →
      lineIntegral ω (r ∘ φ) c d = lineIntegral ω r (φ c) (φ d)) ∧
    (∀ {a b : ℝ}, (∀ t ∈ uIcc a b, r t ∈ U) →
      lineIntegral ω (fun t => r (a + b - t)) a b = - lineIntegral ω r a b) :=
  ⟨fun {_} hφ {_ _} hrU => UndergradKB.Calculus.lineIntegral_comp hω hr hφ hrU,
    fun {_ _} hrU => UndergradKB.Calculus.lineIntegral_neg_orientation hω hr hrU⟩

/-- OpenStax Calculus 3:Theorem 6.6 (CA-621).
For `F = (P, Q)` and a regular curve `(x(t), y(t))`, the flux across the curve is
`∫ (P y' - Q x') dt`. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.6, p. 617"]
theorem flux_across_plane_curve {P Q : ℝ × ℝ → ℝ} {x y : ℝ → ℝ} {a b : ℝ}
    (hreg : ∀ t ∈ uIcc a b, speed2 x y t ≠ 0) :
    flux2 P Q x y a b = ∫ t in a..b, (P (x t, y t) * deriv y t - Q (x t, y t) * deriv x t) :=
  UndergradKB.Calculus.flux2_eq hreg

/-- OpenStax Calculus 3:Theorem 6.7 (CA-625).
Fundamental theorem for line integrals: the integral of `∇f · r'` along a `C¹` curve is
`f(r b) - f(r a)` (stated in the plane and in space). -/
@[kb "openstaxcalculus2016" "3:Theorem 6.7, p. 628"]
theorem fundamental_theorem_line_integrals :
    (∀ {f : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}, IsOpen U → ContDiffOn ℝ 1 f U →
      ∀ {x y : ℝ → ℝ}, ContDiff ℝ 1 x → ContDiff ℝ 1 y → ∀ {a b : ℝ},
      (∀ t ∈ uIcc a b, (x t, y t) ∈ U) →
      ∫ t in a..b, (fderiv ℝ f (x t, y t) (1, 0) * deriv x t +
        fderiv ℝ f (x t, y t) (0, 1) * deriv y t) = f (x b, y b) - f (x a, y a)) ∧
    (∀ {f : ℝ × ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ × ℝ)}, IsOpen U → ContDiffOn ℝ 1 f U →
      ∀ {x y z : ℝ → ℝ}, ContDiff ℝ 1 x → ContDiff ℝ 1 y → ContDiff ℝ 1 z → ∀ {a b : ℝ},
      (∀ t ∈ uIcc a b, (x t, y t, z t) ∈ U) →
      ∫ t in a..b, (fderiv ℝ f (x t, y t, z t) (1, 0, 0) * deriv x t +
        fderiv ℝ f (x t, y t, z t) (0, 1, 0) * deriv y t +
        fderiv ℝ f (x t, y t, z t) (0, 0, 1) * deriv z t)
        = f (x b, y b, z b) - f (x a, y a, z a)) :=
  ⟨fun {_ _} hU hf {_ _} hx hy {_ _} hxy =>
      UndergradKB.Calculus.lineIntegral2_ftli_partials hU hf hx hy hxy,
    fun {_ _} hU hf {_ _ _} hx hy hz {_ _} hxyz =>
      UndergradKB.Calculus.lineIntegral3_ftli_partials hU hf hx hy hz hxyz⟩

/-- OpenStax Calculus 3:Theorem 6.8 (CA-628).
A continuous conservative field is independent of path. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.8, p. 630"]
theorem conservative_field_path_independent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ω : E → E →L[ℝ] ℝ} {U : Set E} (h : IsConservativeOn ω U) (hω : ContinuousOn ω U) :
    IsPathIndependentOn ω U :=
  UndergradKB.Calculus.IsConservativeOn.isPathIndependentOn h hω

/-- OpenStax Calculus 3:Theorem 6.9 (CA-629).
A continuous field on a convex open set whose integrals over triangles add up (the path
independence needed to define a potential by integrating from a base point) is conservative. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.9, p. 631"]
theorem path_independent_field_conservative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ω : E → E →L[ℝ] ℝ} {U : Set E} (hU : IsOpen U) (hc : Convex ℝ U) (hω : ContinuousOn ω U)
    (htri : ∀ a ∈ U, ∀ b ∈ U, ∀ c ∈ U,
      (∫ᶜ x in Path.segment a b, ω x) + (∫ᶜ x in Path.segment b c, ω x) =
        ∫ᶜ x in Path.segment a c, ω x) :
    IsConservativeOn ω U :=
  UndergradKB.Calculus.exists_potential_of_triangle hU hc hω htri

/-- OpenStax Calculus 3:Theorem 6.10 (CA-630).
On a convex open set, a `C¹` field with equal cross partials is conservative: in the plane
`P_y = Q_x`, in space `curl F = 0`. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.10, p. 636"]
theorem cross_partials_imply_conservative :
    (∀ {P Q : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}, IsOpen U → Convex ℝ U → ContDiffOn ℝ 1 P U →
      ContDiffOn ℝ 1 Q U → (∀ p ∈ U, pdy2 P p = pdx2 Q p) → IsConservative2 P Q U) ∧
    (∀ {P Q R : ℝ × ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ × ℝ)}, IsOpen U → Convex ℝ U →
      ContDiffOn ℝ 1 P U → ContDiffOn ℝ 1 Q U → ContDiffOn ℝ 1 R U →
      (∀ p ∈ U, curl3 P Q R p = 0) → IsConservative3 P Q R U) :=
  ⟨fun {_ _ _} hU hc hP hQ h => UndergradKB.Calculus.isConservative2_of_pdy_eq_pdx hU hc hP hQ h,
    fun {_ _ _ _} hU hc hP hQ hR h =>
      (UndergradKB.Calculus.isConservative3_iff_curl3_eq_zero hU hc hP hQ hR).2 h⟩

/-- OpenStax Calculus 3:Theorem 6.11 (CA-631).
On a convex open set, a planar `C¹` field is conservative if and only if `P_y = Q_x`. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.11, p. 637"]
theorem conservative_iff_cross_partials_equal {P Q : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hc : Convex ℝ U) (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) :
    IsConservative2 P Q U ↔ ∀ p ∈ U, pdy2 P p = pdx2 Q p :=
  UndergradKB.Calculus.isConservative2_iff_pdy_eq_pdx hU hc hP hQ

/-- OpenStax Calculus 3:§6.4 Fact (potentials of source-free conservative fields are harmonic)
(CA-638). A potential function of a divergence-free planar field is harmonic. -/
@[kb "openstaxcalculus2016" "3:§6.4 Fact (potentials of source-free conservative fields are harmonic), p. 655"]
theorem potential_of_source_free_field_harmonic {f P Q : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hf : ∀ p ∈ U, HasFDerivAt f (form2 P Q p) p)
    (hdiv : ∀ p ∈ U, div2 P Q p = 0) {p : ℝ × ℝ} (hp : p ∈ U) : laplacian2 f p = 0 :=
  UndergradKB.Calculus.laplacian2_eq_zero_of_potential hU hf hdiv hp

/-- OpenStax Calculus 3:§6.5 Definition (divergence) (CA-641).
The divergence of `(P, Q, R)` is `P_x + Q_y + R_z` (planar: `P_x + Q_y`). -/
@[kb "openstaxcalculus2016" "3:§6.5 Definition (divergence), p. 668"]
theorem divergence_formula :
    (∀ (P Q : ℝ × ℝ → ℝ) (p : ℝ × ℝ), div2 P Q p = pdx2 P p + pdy2 Q p) ∧
    (∀ (P Q R : ℝ × ℝ × ℝ → ℝ) (p : ℝ × ℝ × ℝ), div3 P Q R p = pdx3 P p + pdy3 Q p + pdz3 R p) :=
  ⟨fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- OpenStax Calculus 3:Theorem 6.14 (CA-642).
A field with a `C²` stream function is source free: `div F = 0`. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.14, p. 671"]
theorem stream_function_field_divergence_free {g P Q : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (h : IsStreamFunction g P Q U) (hg : ContDiffOn ℝ 2 g U) {p : ℝ × ℝ}
    (hp : p ∈ U) : div2 P Q p = 0 :=
  UndergradKB.Calculus.IsStreamFunction.div2_eq_zero hU h hg hp

/-- OpenStax Calculus 3:§6.5 Definition (curl) (CA-644).
The curl of `(P, Q, R)` is `(R_y - Q_z, P_z - R_x, Q_x - P_y)`; for a planar field the scalar
`Q_x - P_y`. -/
@[kb "openstaxcalculus2016" "3:§6.5 Definition (curl), p. 674"]
theorem curl_formula :
    (∀ (P Q : ℝ × ℝ → ℝ) (p : ℝ × ℝ), curl2 P Q p = pdx2 Q p - pdy2 P p) ∧
    (∀ (P Q R : ℝ × ℝ × ℝ → ℝ) (p : ℝ × ℝ × ℝ), curl3 P Q R p =
      (pdy3 R p - pdz3 Q p, pdz3 P p - pdx3 R p, pdx3 Q p - pdy3 P p)) :=
  ⟨fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- OpenStax Calculus 3:Theorem 6.16 (CA-646).
The divergence of the curl of a `C²` field in space is zero. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.16, p. 676"]
theorem divergence_of_curl_is_zero {P Q R : ℝ × ℝ × ℝ → ℝ} {p : ℝ × ℝ × ℝ}
    (hP : ContDiffAt ℝ 2 P p) (hQ : ContDiffAt ℝ 2 Q p) (hR : ContDiffAt ℝ 2 R p) :
    div3 (fun q => (curl3 P Q R q).1) (fun q => (curl3 P Q R q).2.1)
      (fun q => (curl3 P Q R q).2.2) p = 0 :=
  UndergradKB.Calculus.div3_curl3 hP hQ hR

/-- OpenStax Calculus 3:Theorem 6.17 (CA-647).
The curl of a gradient field of a `C²` function is zero, in the plane and in space. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.17, p. 677"]
theorem curl_of_gradient_is_zero :
    (∀ {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ}, ContDiffAt ℝ 2 f p → curl2 (pdx2 f) (pdy2 f) p = 0) ∧
    (∀ {f : ℝ × ℝ × ℝ → ℝ} {p : ℝ × ℝ × ℝ}, ContDiffAt ℝ 2 f p →
      curl3 (pdx3 f) (pdy3 f) (pdz3 f) p = 0) :=
  ⟨fun {_ _} hf => UndergradKB.Calculus.curl2_grad hf,
    fun {_ _} hf => UndergradKB.Calculus.curl3_grad hf⟩

/-- OpenStax Calculus 3:Theorem 6.18 (CA-648).
On a convex open set, a `C¹` field is conservative if and only if its curl vanishes
(plane or space). -/
@[kb "openstaxcalculus2016" "3:Theorem 6.18, p. 677"]
theorem conservative_iff_curl_zero :
    (∀ {P Q : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}, IsOpen U → Convex ℝ U → ContDiffOn ℝ 1 P U →
      ContDiffOn ℝ 1 Q U → (IsConservative2 P Q U ↔ ∀ p ∈ U, curl2 P Q p = 0)) ∧
    (∀ {P Q R : ℝ × ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ × ℝ)}, IsOpen U → Convex ℝ U →
      ContDiffOn ℝ 1 P U → ContDiffOn ℝ 1 Q U → ContDiffOn ℝ 1 R U →
      (IsConservative3 P Q R U ↔ ∀ p ∈ U, curl3 P Q R p = 0)) :=
  ⟨fun {_ _ _} hU hc hP hQ => UndergradKB.Calculus.isConservative2_iff_curl2_eq_zero hU hc hP hQ,
    fun {_ _ _ _} hU hc hP hQ hR =>
      UndergradKB.Calculus.isConservative3_iff_curl3_eq_zero hU hc hP hQ hR⟩

/-- OpenStax Calculus 3:Example 6.58 (CA-649).
Standard parameterizations: sphere, cylinder, cone, graph, and surface of revolution. -/
@[kb "openstaxcalculus2016" "3:Example 6.58, p. 682"]
theorem standard_surface_parameterizations :
    (∀ (R : ℝ) (p : ℝ × ℝ), sphereParam R p =
      ![R * Real.sin p.1 * Real.cos p.2, R * Real.sin p.1 * Real.sin p.2, R * Real.cos p.1]) ∧
    (∀ (R : ℝ) (p : ℝ × ℝ), cylinderParam R p = ![R * Real.cos p.1, R * Real.sin p.1, p.2]) ∧
    (∀ (k : ℝ) (p : ℝ × ℝ), coneParam k p = ![p.1 * Real.cos p.2, p.1 * Real.sin p.2, k * p.1]) ∧
    (∀ (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ), graphParam f p = ![p.1, p.2, f p]) ∧
    (∀ (f : ℝ → ℝ) (p : ℝ × ℝ),
      revolutionParam f p = ![p.1, f p.1 * Real.cos p.2, f p.1 * Real.sin p.2]) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- OpenStax Calculus 3:§6.6 Definition (surface area) (CA-651).
The area of a surface is `∬_D ‖r_u × r_v‖ dA`; for a graph `z = f(x, y)` this is
`∬ √(1 + f_x² + f_y²) dA`. -/
@[kb "openstaxcalculus2016" "3:§6.6 Definition (surface area), p. 690"]
theorem surface_area_double_integral :
    (∀ (r : ℝ × ℝ → Fin 3 → ℝ) (D : Set (ℝ × ℝ)),
      paramSurfaceArea r D = ∫ p in D, surfVnorm (surfNormal r p)) ∧
    (∀ (f : ℝ × ℝ → ℝ) (fx fy : ℝ × ℝ → ℝ)
      (_ : ∀ p : ℝ × ℝ, HasDerivAt (fun x => f (x, p.2)) (fx p) p.1)
      (_ : ∀ p : ℝ × ℝ, HasDerivAt (fun y => f (p.1, y)) (fy p) p.2) (D : Set (ℝ × ℝ)),
      paramSurfaceArea (graphParam f) D = ∫ p in D, Real.sqrt (1 + fx p ^ 2 + fy p ^ 2)) :=
  ⟨fun _ _ => rfl, fun f fx fy hx hy D => UndergradKB.Calculus.paramSurfaceArea_graph f fx fy hx hy D⟩

/-- OpenStax Calculus 3:Equation 6.19 (CA-654).
The scalar surface integral is `∬_D f(r(u, v)) ‖r_u × r_v‖ dA`; for `f = 1` it is the surface area. -/
@[kb "openstaxcalculus2016" "3:Equation 6.19, p. 695"]
theorem scalar_surface_integral_formula :
    (∀ (f : (Fin 3 → ℝ) → ℝ) (r : ℝ × ℝ → Fin 3 → ℝ) (D : Set (ℝ × ℝ)),
      scalarSurfaceIntegral f r D = ∫ p in D, f (r p) * surfVnorm (surfNormal r p)) ∧
    (∀ (r : ℝ × ℝ → Fin 3 → ℝ) (D : Set (ℝ × ℝ)),
      scalarSurfaceIntegral (fun _ => 1) r D = paramSurfaceArea r D) :=
  ⟨fun _ _ _ => rfl, UndergradKB.Calculus.scalarSurfaceIntegral_one⟩

/-- OpenStax Calculus 3:§6.6 Definition (surface integral of a vector field) (CA-656).
The flux of `F` through a regular parameterized surface is `∬ (F · N) dS` with `N` the unit normal
and `dS = ‖r_u × r_v‖ dA`. -/
@[kb "openstaxcalculus2016" "3:§6.6 Definition (surface integral of a vector field), p. 703"]
theorem surface_integral_vector_field (F : (Fin 3 → ℝ) → Fin 3 → ℝ) (r : ℝ × ℝ → Fin 3 → ℝ)
    (D : Set (ℝ × ℝ)) (hD : MeasurableSet D) (hr : IsRegularParam r D) :
    surfaceFlux F r D = ∫ p in D, (F (r p) ⬝ᵥ unitNormal r p) * surfVnorm (surfNormal r p) :=
  UndergradKB.Calculus.surfaceFlux_eq_unitNormal F r D hD hr

/-- OpenStax Calculus 3:Equation 6.21 (CA-657).
The flux across a parameterized surface is `∬_D F(r(u, v)) · (r_u × r_v) dA`. -/
@[kb "openstaxcalculus2016" "3:Equation 6.21, p. 703"]
theorem flux_parameterized_surface (F : (Fin 3 → ℝ) → Fin 3 → ℝ) (r : ℝ × ℝ → Fin 3 → ℝ)
    (D : Set (ℝ × ℝ)) : surfaceFlux F r D = ∫ p in D, F (r p) ⬝ᵥ surfNormal r p :=
  rfl

/-- OpenStax Calculus 3:§6.7 Fact (curl as circulation per unit area) (CA-660).
The circulation of a field around a small circle of radius `ε` divided by the area `π ε²` tends to
`Q_x - P_y` as `ε → 0⁺` (the component of the curl along the normal). -/
@[kb "openstaxcalculus2016" "3:§6.7 Fact (curl as circulation per unit area), p. 721"]
theorem curl_as_circulation_per_unit_area (P Q : ℝ × ℝ → ℝ) (hPc : Continuous P)
    (hQc : Continuous Q) (c : ℝ × ℝ) (hP : DifferentiableAt ℝ P c) (hQ : DifferentiableAt ℝ Q c) :
    Tendsto (fun ε : ℝ => (∫ t in (0 : ℝ)..2 * Real.pi,
        (P (c + ε • (Real.cos t, Real.sin t)) * (-ε * Real.sin t) +
          Q (c + ε • (Real.cos t, Real.sin t)) * (ε * Real.cos t)))
        / (Real.pi * ε ^ 2)) (𝓝[>] 0)
      (𝓝 (fderiv ℝ Q c (1, 0) - fderiv ℝ P c (0, 1))) :=
  UndergradKB.Calculus.circulation_per_area_tendsto P Q hPc hQc c hP hQ

/-- OpenStax Calculus 3:§6.8 Fact (divergence as flux per unit volume) (CA-662).
The flux of a field through a small sphere of radius `ε` divided by its volume tends to
`P_x + Q_y + R_z` as `ε → 0⁺`. -/
@[kb "openstaxcalculus2016" "3:§6.8 Fact (divergence as flux per unit volume), p. 737"]
theorem divergence_as_flux_per_unit_volume (P Q R : ℝ × ℝ × ℝ → ℝ) (hPc : Continuous P)
    (hQc : Continuous Q) (hRc : Continuous R) (c : ℝ × ℝ × ℝ) (hP : DifferentiableAt ℝ P c)
    (hQ : DifferentiableAt ℝ Q c) (hR : DifferentiableAt ℝ R c) :
    Tendsto (fun ε : ℝ => (∫ θ in (0 : ℝ)..2 * Real.pi, ∫ φ in (0 : ℝ)..Real.pi,
        (P (c + ε • sphereNormal φ θ) * (Real.sin φ * Real.cos θ) +
          Q (c + ε • sphereNormal φ θ) * (Real.sin φ * Real.sin θ) +
          R (c + ε • sphereNormal φ θ) * Real.cos φ) * (ε ^ 2 * Real.sin φ)) /
        (4 * Real.pi * ε ^ 3 / 3)) (𝓝[>] 0)
      (𝓝 (fderiv ℝ P c (1, 0, 0) + fderiv ℝ Q c (0, 1, 0) + fderiv ℝ R c (0, 0, 1))) :=
  UndergradKB.Calculus.flux_per_volume_tendsto P Q R hPc hQc hRc c hP hQ hR

end ProvedInKB

/-- OpenStax Calculus 3:§6.4 List (equivalent conditions for source free) (CA-636), on an open convex domain (the
book: simply connected): zero flux across closed curves, path-independent flux, a stream function, and
`div F = 0` are equivalent for a planar field continuous on the plane and `C¹` on the domain. -/
@[kb "openstaxcalculus2016" "3:§6.4 List (equivalent conditions for source free), p. 653"]
theorem source_free_equivalent_conditions {P Q : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hc : Convex ℝ U) (hPc : Continuous P) (hQc : Continuous Q) (hP : ContDiffOn ℝ 1 P U)
    (hQ : ContDiffOn ℝ 1 Q U) :
    [UndergradKB.Calculus.IsSourceFree2 P Q U, UndergradKB.Calculus.IsFluxPathIndependent2 P Q U,
      ∃ g, UndergradKB.Calculus.IsStreamFunction g P Q U,
      ∀ p ∈ U, UndergradKB.Calculus.div2 P Q p = 0].TFAE :=
  UndergradKB.Calculus.sourceFree_tfae hU hc hPc hQc hP hQ

/-- OpenStax Calculus 3:Theorem 6.15 (CA-643), on an open convex domain (the book: simply connected): a planar field,
continuous on the plane and `C¹` on the domain, is source free if and only if its divergence vanishes there. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.15, p. 672"]
theorem source_free_iff_div_zero {P Q : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hc : Convex ℝ U) (hPc : Continuous P) (hQc : Continuous Q) (hP : ContDiffOn ℝ 1 P U)
    (hQ : ContDiffOn ℝ 1 Q U) :
    UndergradKB.Calculus.IsSourceFree2 P Q U ↔ ∀ p ∈ U, UndergradKB.Calculus.div2 P Q p = 0 :=
  UndergradKB.Calculus.isSourceFree2_iff_div2_eq_zero hU hc hPc hQc hP hQ

/-! ## Wave 3: further results -/

/-- OpenStax Calculus 3:§6.1 Definition (gradient field) (CA-607).
A planar field `(P, Q)` (resp. a spatial field `(P, Q, R)`) is conservative on `U` exactly when some scalar
function has it as its derivative at every point of `U`, that is, when it is a gradient field. -/
@[kb "openstaxcalculus2016" "3:§6.1 Definition (gradient field), p. 595"]
theorem gradient_field_definition :
    (∀ (P Q : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ)), UndergradKB.Calculus.IsConservative2 P Q U ↔
      ∃ f : ℝ × ℝ → ℝ, ∀ p ∈ U, HasFDerivAt f (UndergradKB.Calculus.form2 P Q p) p) ∧
    (∀ (P Q R : ℝ × ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ × ℝ)),
      UndergradKB.Calculus.IsConservative3 P Q R U ↔
      ∃ f : ℝ × ℝ × ℝ → ℝ, ∀ p ∈ U, HasFDerivAt f (UndergradKB.Calculus.form3 P Q R p) p) :=
  ⟨fun _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl⟩

/-- OpenStax Calculus 3:§6.2 text after Definition (CA-611).
If `f` is continuous and the curve `r` is `C¹`, the integrand `f(r t) ‖r' t‖` of the scalar line integral
is integrable on every interval, so the scalar line integral exists. -/
@[kb "openstaxcalculus2016" "3:§6.2 text after Definition, p. 602"]
theorem scalar_line_integral_exists {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℝ → E} (hr : ContDiff ℝ 1 r) {f : E → ℝ} (hf : Continuous f) (a b : ℝ) :
    IntervalIntegrable (fun t => f (r t) * ‖deriv r t‖) MeasureTheory.volume a b :=
  UndergradKB.Calculus.LineIntegralLimits.lineIntegrand_intervalIntegrable hr hf a b

/-- OpenStax Calculus 3:Example 6.16 (CA-614).
A scalar line integral does not change when the curve is traversed backwards, nor under a `C¹`
reparameterization (with derivative of one sign), which reverses or keeps the endpoints accordingly. -/
@[kb "openstaxcalculus2016" "3:Example 6.16, p. 606"]
theorem scalar_line_integral_independent_of_parameterization {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} {U : Set E} (hf : ContinuousOn f U) {r : ℝ → E}
    (hr : ContDiff ℝ 1 r) :
    (∀ {φ : ℝ → ℝ}, ContDiff ℝ 1 φ → ∀ {c d : ℝ}, (∀ s ∈ uIcc c d, r (φ s) ∈ U) →
      (∀ s ∈ uIcc c d, 0 ≤ deriv φ s) →
      UndergradKB.Calculus.scalarLineIntegral f (r ∘ φ) c d =
        UndergradKB.Calculus.scalarLineIntegral f r (φ c) (φ d)) ∧
    (∀ {φ : ℝ → ℝ}, ContDiff ℝ 1 φ → ∀ {c d : ℝ}, (∀ s ∈ uIcc c d, r (φ s) ∈ U) →
      (∀ s ∈ uIcc c d, deriv φ s ≤ 0) →
      UndergradKB.Calculus.scalarLineIntegral f (r ∘ φ) c d =
        UndergradKB.Calculus.scalarLineIntegral f r (φ d) (φ c)) ∧
    (∀ {a b : ℝ}, (∀ t ∈ uIcc a b, r t ∈ U) →
      UndergradKB.Calculus.scalarLineIntegral f (fun t => r (a + b - t)) a b =
        UndergradKB.Calculus.scalarLineIntegral f r a b) :=
  ⟨fun hφ _ _ hrU hφ' => UndergradKB.Calculus.scalarLineIntegral_comp_of_nonneg hf hr hφ hrU hφ',
    fun hφ _ _ hrU hφ' => UndergradKB.Calculus.scalarLineIntegral_comp_of_nonpos hf hr hφ hrU hφ',
    fun hrU => UndergradKB.Calculus.scalarLineIntegral_reverse hf hr hrU⟩

/-- OpenStax Calculus 3:§6.2 Definition (flux across a curve) (CA-620).
The flux of `(P, Q)` across the curve `(x(t), y(t))` is the integral of `F · N` times the speed, where
`N = (y', -x') / ‖r'‖` is the unit normal to the right of the direction of travel. -/
@[kb "openstaxcalculus2016" "3:§6.2 Definition (flux across a curve), p. 617"]
theorem flux_across_curve_definition (P Q : ℝ × ℝ → ℝ) (x y : ℝ → ℝ) (a b : ℝ) :
    (∀ t, UndergradKB.Calculus.unitNormal2 x y t =
      (deriv y t / UndergradKB.Calculus.speed2 x y t,
        -deriv x t / UndergradKB.Calculus.speed2 x y t)) ∧
    UndergradKB.Calculus.flux2 P Q x y a b =
      ∫ t in a..b, (P (x t, y t) * (UndergradKB.Calculus.unitNormal2 x y t).1 +
        Q (x t, y t) * (UndergradKB.Calculus.unitNormal2 x y t).2) *
        UndergradKB.Calculus.speed2 x y t :=
  ⟨fun _ => rfl, rfl⟩

/-- OpenStax Calculus 3:§6.3 text (closed curves, first consequence of FTLI) (CA-627).
A conservative field has zero circulation around every closed `C¹` curve, in the general, planar and spatial
forms. -/
@[kb "openstaxcalculus2016" "3:§6.3 text (closed curves, first consequence of FTLI), p. 630"]
theorem conservative_field_closed_curve_zero :
    (∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {ω : E → E →L[ℝ] ℝ} {U : Set E},
      UndergradKB.Calculus.IsConservativeOn ω U → ContinuousOn ω U → ∀ {r : ℝ → E},
      ContDiff ℝ 1 r → ∀ {a b : ℝ}, (∀ t ∈ uIcc a b, r t ∈ U) → r a = r b →
      UndergradKB.Calculus.lineIntegral ω r a b = 0) ∧
    (∀ {P Q : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}, UndergradKB.Calculus.IsConservative2 P Q U →
      ContinuousOn P U → ContinuousOn Q U → ∀ {x y : ℝ → ℝ}, ContDiff ℝ 1 x → ContDiff ℝ 1 y →
      ∀ {a b : ℝ}, (∀ t ∈ uIcc a b, (x t, y t) ∈ U) → (x a, y a) = (x b, y b) →
      UndergradKB.Calculus.lineIntegral2 P Q x y a b = 0) ∧
    (∀ {P Q R : ℝ × ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ × ℝ)}, UndergradKB.Calculus.IsConservative3 P Q R U →
      ContinuousOn P U → ContinuousOn Q U → ContinuousOn R U → ∀ {x y z : ℝ → ℝ},
      ContDiff ℝ 1 x → ContDiff ℝ 1 y → ContDiff ℝ 1 z → ∀ {a b : ℝ},
      (∀ t ∈ uIcc a b, (x t, y t, z t) ∈ U) → (x a, y a, z a) = (x b, y b, z b) →
      UndergradKB.Calculus.lineIntegral3 P Q R x y z a b = 0) :=
  ⟨fun h hω _ hr _ _ hU hc => UndergradKB.Calculus.IsConservativeOn.lineIntegral_closed h hω hr hU hc,
    fun h hP hQ _ _ hx hy _ _ hU hc =>
      UndergradKB.Calculus.IsConservative2.lineIntegral2_closed h hP hQ hx hy hU hc,
    fun h hP hQ hR _ _ _ hx hy hz _ _ hU hc =>
      UndergradKB.Calculus.IsConservative3.lineIntegral3_closed h hP hQ hR hx hy hz hU hc⟩

/-- OpenStax Calculus 3:§6.4 text (source free) (CA-635).
A planar field is source free on `U` when its flux across every closed regular `C¹` curve in `U` vanishes; a
stream function `g` of `(P, Q)` has `g_y = P` and `g_x = -Q`, and a field with a stream function is source
free. -/
@[kb "openstaxcalculus2016" "3:§6.4 text (source free), p. 653"]
theorem source_free_and_stream_function {P Q : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} :
    (UndergradKB.Calculus.IsSourceFree2 P Q U ↔
      ∀ (x y : ℝ → ℝ) (a b : ℝ), ContDiff ℝ 1 x → ContDiff ℝ 1 y →
        (∀ t ∈ uIcc a b, (x t, y t) ∈ U) → (x a, y a) = (x b, y b) →
        (∀ t ∈ uIcc a b, UndergradKB.Calculus.speed2 x y t ≠ 0) →
        UndergradKB.Calculus.flux2 P Q x y a b = 0) ∧
    (∀ g : ℝ × ℝ → ℝ, UndergradKB.Calculus.IsStreamFunction g P Q U ↔
      ∀ p ∈ U, HasFDerivAt g (UndergradKB.Calculus.form2 (fun q => -Q q) P p) p) ∧
    (∀ g : ℝ × ℝ → ℝ, UndergradKB.Calculus.IsStreamFunction g P Q U → ContinuousOn P U →
      ContinuousOn Q U → UndergradKB.Calculus.IsSourceFree2 P Q U) :=
  ⟨Iff.rfl, fun _ => Iff.rfl, fun _ h hP hQ => h.isSourceFree2 hP hQ⟩

/-- OpenStax Calculus 3:Example 6.54 (CA-645).
The inverse-square field `r / ‖r‖³` has zero curl at every point other than the origin. -/
@[kb "openstaxcalculus2016" "3:Example 6.54, p. 676"]
theorem curl_inverse_square_field_zero {p : ℝ × ℝ × ℝ} (hp : p ≠ 0) :
    UndergradKB.Calculus.curl3 UndergradKB.Calculus.invSqP UndergradKB.Calculus.invSqQ
      UndergradKB.Calculus.invSqR p = 0 :=
  UndergradKB.Calculus.curl3_invSq hp

/-- OpenStax Calculus 3:§6.6 Definition (regular parameterization) (CA-650).
A parameterization `r(u, v)` is regular on `D` when `r_u × r_v` never vanishes there; graphs of
differentiable functions and cylinders (of nonzero radius) are regularly parameterized. -/
@[kb "openstaxcalculus2016" "3:§6.6 Definition (regular parameterization), p. 687"]
theorem regular_parameterization_definition :
    (∀ (r : ℝ × ℝ → Fin 3 → ℝ) (D : Set (ℝ × ℝ)), UndergradKB.Calculus.IsRegularParam r D ↔
      ∀ p ∈ D, UndergradKB.Calculus.surfNormal r p ≠ 0) ∧
    (∀ (f fx fy : ℝ × ℝ → ℝ), (∀ p, HasDerivAt (fun x => f (x, p.2)) (fx p) p.1) →
      (∀ p, HasDerivAt (fun y => f (p.1, y)) (fy p) p.2) → ∀ D : Set (ℝ × ℝ),
      UndergradKB.Calculus.IsRegularParam (UndergradKB.Calculus.graphParam f) D) ∧
    (∀ {R : ℝ}, R ≠ 0 → ∀ D : Set (ℝ × ℝ),
      UndergradKB.Calculus.IsRegularParam (UndergradKB.Calculus.cylinderParam R) D) :=
  ⟨fun _ _ => Iff.rfl, fun f fx fy hx hy D => UndergradKB.Calculus.graphParam_isRegular f fx fy hx hy D,
    fun hR D => UndergradKB.Calculus.cylinderParam_isRegular hR D⟩

/-- OpenStax Calculus 3:Example 6.62 (CA-652).
The lateral area of a cone of height `h` and base radius `ρ` is `π ρ √(ρ² + h²)`, and the area of a sphere of
radius `R` is `4 π R²`, both computed from the surface area integral. -/
@[kb "openstaxcalculus2016" "3:Example 6.62, p. 690"]
theorem cone_and_sphere_surface_area {ρ h : ℝ} (hρ : 0 < ρ) (hh : 0 < h) (R : ℝ) :
    UndergradKB.Calculus.paramSurfaceArea (UndergradKB.Calculus.coneParam (h / ρ))
        (Icc 0 ρ ×ˢ Icc 0 (2 * Real.pi)) = Real.pi * ρ * Real.sqrt (ρ ^ 2 + h ^ 2) ∧
      UndergradKB.Calculus.paramSurfaceArea (UndergradKB.Calculus.sphereParam R)
        UndergradKB.Calculus.sphereDomain = 4 * Real.pi * R ^ 2 :=
  ⟨UndergradKB.Calculus.paramSurfaceArea_cone hρ hh, UndergradKB.Calculus.paramSurfaceArea_sphere R⟩

/-- OpenStax Calculus 3:§6.6 Definition (surface integral of a scalar function) (CA-653).
The surface integral of `f` over the surface parameterized by `r` on `D` is the double integral over `D` of
`f(r(u, v)) ‖r_u × r_v‖`. -/
@[kb "openstaxcalculus2016" "3:§6.6 Definition (surface integral of a scalar function), p. 694"]
theorem scalar_surface_integral_definition (f : (Fin 3 → ℝ) → ℝ) (r : ℝ × ℝ → Fin 3 → ℝ)
    (D : Set (ℝ × ℝ)) :
    UndergradKB.Calculus.scalarSurfaceIntegral f r D =
      ∫ p in D, f (r p) * UndergradKB.Calculus.surfVnorm (UndergradKB.Calculus.surfNormal r p) :=
  rfl

/-- OpenStax Calculus 3:Example 6.80 (CA-663).
The inverse-square field `r / ‖r‖³` has zero divergence at every point other than the origin. -/
@[kb "openstaxcalculus2016" "3:Example 6.80, p. 737"]
theorem divergence_inverse_square_field_zero {p : ℝ × ℝ × ℝ} (hp : p ≠ 0) :
    UndergradKB.Calculus.div3 UndergradKB.Calculus.invSqP UndergradKB.Calculus.invSqQ
      UndergradKB.Calculus.invSqR p = 0 :=
  UndergradKB.Calculus.div3_invSq hp

end UndergradKB.Calculus.Course.V3C6
