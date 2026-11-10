import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Gradient.Basic
import UndergradKB.Common.Attr

/-! # Calculus: line integrals, conservative fields, fundamental theorem for line integrals

Vector and scalar line integrals along `C¹` curves, flux across plane curves, conservative fields and the
fundamental theorem for line integrals (OpenStax Calculus 3, chapter 6). Fields are given by components on
`ℝ × ℝ` (`P, Q`) and `ℝ × ℝ × ℝ` (`P, Q, R`); `form2`, `form3` turn components into the covector field
`F · (·)`, and `∇f = F` means `HasFDerivAt f (form2 P Q p) p`. The general results are stated once for a
covector field `ω : E → E →L[ℝ] ℝ` on a normed space and specialized to the plane and space.
Differences from the book: curves are `C¹` (not piecewise), and the converse "path independent implies
conservative" (`exists_potential_of_triangle`) is proved on open convex sets from polygonal path
independence. -/

namespace UndergradKB.Calculus
open Set MeasureTheory intervalIntegral

section General
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- OpenStax Calculus 3:Equation 6.9 (CA-616). The line integral of a covector field `ω` (the
field `F` with `ω x = ⟨F x, ·⟩`) along the curve `r : [a, b] → E`, `∫ₐᵇ ω(r t)(r' t) dt`. -/
@[kb "openstaxcalculus2016" "3:Equation 6.9, p. 609"]
noncomputable def lineIntegral (ω : E → E →L[ℝ] ℝ) (r : ℝ → E) (a b : ℝ) : ℝ :=
  ∫ t in a..b, ω (r t) (deriv r t)

/-- OpenStax Calculus 3:§6.1 Definition (CA-607). `ω` is conservative on `U`: it is the derivative of a
potential function `f` at every point of `U`. For the plane and space book forms see `IsConservative2`,
`IsConservative3`; for gradient fields in an inner product space see `IsConservativeField`. -/
@[kb "openstaxcalculus2016" "3:§6.1 Definition (conservative field, potential function), p. 596"]
def IsConservativeOn (ω : E → E →L[ℝ] ℝ) (U : Set E) : Prop :=
  ∃ f : E → ℝ, ∀ x ∈ U, HasFDerivAt f (ω x) x

/-- OpenStax Calculus 3:Theorem 6.7 (CA-625). Fundamental theorem for line integrals, general form: if
`f` has derivative `ω` at each point of `U`, `ω` is continuous on `U`, and `r` is a `C¹` curve running in `U`
on `[a, b]`, then `∫ₐᵇ ω(r t)(r' t) dt = f(r b) - f(r a)`. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.7, p. 628"]
theorem lineIntegral_ftli {f : E → ℝ} {ω : E → E →L[ℝ] ℝ} {U : Set E}
    (hf : ∀ x ∈ U, HasFDerivAt f (ω x) x) (hω : ContinuousOn ω U) {r : ℝ → E}
    (hr : ContDiff ℝ 1 r) {a b : ℝ} (hrU : ∀ t ∈ uIcc a b, r t ∈ U) :
    lineIntegral ω r a b = f (r b) - f (r a) := by
  unfold lineIntegral
  have hd : ∀ t ∈ uIcc a b, HasDerivAt (f ∘ r) (ω (r t) (deriv r t)) t := fun t ht =>
    (hf _ (hrU t ht)).comp_hasDerivAt t ((hr.differentiable one_ne_zero t).hasDerivAt)
  have hint : IntervalIntegrable (fun t => ω (r t) (deriv r t)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    exact (hω.comp hr.continuous.continuousOn hrU).clm_apply
      (hr.continuous_deriv le_rfl).continuousOn
  exact integral_eq_sub_of_hasDerivAt hd hint

/-- OpenStax Calculus 3:Equation 6.9 (CA-616). Change of variables for the vector line integral under any
`C¹` reparameterization `φ`: `∫_c^d ω((r∘φ)(s))((r∘φ)'(s)) ds = ∫_{φ c}^{φ d} ω(r t)(r' t) dt`. -/
@[kb "openstaxcalculus2016" "3:Equation 6.9, p. 609"]
theorem lineIntegral_comp {ω : E → E →L[ℝ] ℝ} {U : Set E} (hω : ContinuousOn ω U) {r : ℝ → E}
    (hr : ContDiff ℝ 1 r) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) {c d : ℝ}
    (hrU : ∀ s ∈ uIcc c d, r (φ s) ∈ U) :
    lineIntegral ω (r ∘ φ) c d = lineIntegral ω r (φ c) (φ d) := by
  unfold lineIntegral
  rw [← integral_comp_mul_deriv' (f := φ) (f' := deriv φ)
    (g := fun t => ω (r t) (deriv r t))]
  · refine integral_congr fun s _ => ?_
    have h1 : deriv (r ∘ φ) s = deriv φ s • deriv r (φ s) :=
      deriv.scomp s (hr.differentiable one_ne_zero _) (hφ.differentiable one_ne_zero s)
    simp only [Function.comp, h1, map_smul, smul_eq_mul]
    ring
  · exact fun x _ => (hφ.differentiable one_ne_zero x).hasDerivAt
  · exact (hφ.continuous_deriv le_rfl).continuousOn
  · have : ContinuousOn (fun t => ω (r t) (deriv r t)) (φ '' uIcc c d) := by
      refine ContinuousOn.clm_apply ?_ (hr.continuous_deriv le_rfl).continuousOn
      refine hω.comp hr.continuous.continuousOn ?_
      rintro _ ⟨s, hs, rfl⟩
      exact hrU s hs
    exact this

lemma reflect_mem_uIcc {a b s : ℝ} (hs : s ∈ uIcc a b) : a + b - s ∈ uIcc a b := by
  rw [mem_uIcc] at hs ⊢
  rcases hs with h | h
  · left; constructor <;> linarith [h.1, h.2]
  · right; constructor <;> linarith [h.1, h.2]

/-- OpenStax Calculus 3:§6.2 Definition (vector line integral) (CA-616). Reversing the orientation of
the curve, `t ↦ r(a + b - t)`, changes the sign of the vector line integral. -/
@[kb "openstaxcalculus2016" "3:§6.2 Definition (vector line integral), p. 608"]
theorem lineIntegral_neg_orientation {ω : E → E →L[ℝ] ℝ} {U : Set E} (hω : ContinuousOn ω U)
    {r : ℝ → E} (hr : ContDiff ℝ 1 r) {a b : ℝ} (hrU : ∀ t ∈ uIcc a b, r t ∈ U) :
    lineIntegral ω (fun t => r (a + b - t)) a b = - lineIntegral ω r a b := by
  have hφ : ContDiff ℝ 1 (fun t : ℝ => a + b - t) := contDiff_const.sub contDiff_id
  have := lineIntegral_comp hω hr hφ (c := a) (d := b) (fun s hs => hrU _ (reflect_mem_uIcc hs))
  have e : (fun t => r (a + b - t)) = r ∘ (fun t : ℝ => a + b - t) := rfl
  rw [e, this]
  simp only [add_sub_cancel_left, add_sub_cancel_right]
  unfold lineIntegral
  rw [integral_symm]

/-- OpenStax Calculus 3:Theorem 6.8 (CA-628). `ω` is independent of path on `U`: the line integral
along `C¹` curves in `U` depends only on the endpoints. (Piecewise smooth curves are not covered; see
`exists_potential_of_triangle` for how this is used.) -/
def IsPathIndependentOn (ω : E → E →L[ℝ] ℝ) (U : Set E) : Prop :=
  ∀ (r s : ℝ → E) (a b c d : ℝ), ContDiff ℝ 1 r → ContDiff ℝ 1 s →
    (∀ t ∈ uIcc a b, r t ∈ U) → (∀ t ∈ uIcc c d, s t ∈ U) → r a = s c → r b = s d →
    lineIntegral ω r a b = lineIntegral ω s c d

/-- OpenStax Calculus 3:Theorem 6.8 (CA-628). A conservative field with continuous `ω` is independent of path. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.8, p. 630"]
theorem IsConservativeOn.isPathIndependentOn {ω : E → E →L[ℝ] ℝ} {U : Set E}
    (h : IsConservativeOn ω U) (hω : ContinuousOn ω U) : IsPathIndependentOn ω U := by
  obtain ⟨f, hf⟩ := h
  intro r s a b c d hr hs hrU hsU h1 h2
  rw [lineIntegral_ftli hf hω hr hrU, lineIntegral_ftli hf hω hs hsU, h1, h2]

/-- OpenStax Calculus 3:§6.3 (CA-627). A conservative field has zero circulation around a closed
`C¹` curve. -/
@[kb "openstaxcalculus2016" "3:§6.3 text (closed curves, first consequence of FTLI), p. 630"]
theorem IsConservativeOn.lineIntegral_closed {ω : E → E →L[ℝ] ℝ} {U : Set E}
    (h : IsConservativeOn ω U) (hω : ContinuousOn ω U) {r : ℝ → E} (hr : ContDiff ℝ 1 r)
    {a b : ℝ} (hrU : ∀ t ∈ uIcc a b, r t ∈ U) (hclosed : r a = r b) :
    lineIntegral ω r a b = 0 := by
  obtain ⟨f, hf⟩ := h
  rw [lineIntegral_ftli hf hω hr hrU, hclosed, sub_self]

lemma contDiff_lineMap (a b : E) : ContDiff ℝ 1 (AffineMap.lineMap a b : ℝ → E) := by
  have : (AffineMap.lineMap a b : ℝ → E) = fun t => a + t • (b - a) := by
    ext t; simp [AffineMap.lineMap_apply, add_comm]
  rw [this]
  exact contDiff_const.add (contDiff_id.smul contDiff_const)

lemma deriv_lineMap (a b : E) (t : ℝ) : deriv (AffineMap.lineMap a b : ℝ → E) t = b - a :=
  (AffineMap.hasDerivAt_lineMap (a := a) (b := b) (x := t)).deriv

/-- Bridge to Mathlib: the line integral along the segment `t ↦ lineMap a b t`, `t ∈ [0, 1]`, is
Mathlib's `curveIntegral` along `Path.segment a b`. -/
theorem lineIntegral_lineMap_eq_curveIntegral (ω : E → E →L[ℝ] ℝ) (a b : E) :
    lineIntegral ω (AffineMap.lineMap a b) 0 1 = ∫ᶜ x in Path.segment a b, ω x := by
  rw [curveIntegral_segment]
  unfold lineIntegral
  simp only [deriv_lineMap]

/-- OpenStax Calculus 3:Theorem 6.7 (CA-625). The curve integral along a segment of a conservative
field on a convex set is the difference of the potential at the endpoints. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.7, p. 628"]
theorem IsConservativeOn.curveIntegral_segment {ω : E → E →L[ℝ] ℝ} {U : Set E}
    (hc : Convex ℝ U) (h : IsConservativeOn ω U) (hω : ContinuousOn ω U) {a b : E} (ha : a ∈ U)
    (hb : b ∈ U) :
    ∫ᶜ x in Path.segment a b, ω x = (Classical.choose h) b - (Classical.choose h) a := by
  rw [← lineIntegral_lineMap_eq_curveIntegral]
  have := lineIntegral_ftli (Classical.choose_spec h) hω (contDiff_lineMap a b) (a := 0) (b := 1)
    (fun t ht => by
      rw [uIcc_of_le zero_le_one] at ht
      exact hc.lineMap_mem ha hb ht)
  simpa using this

/-- OpenStax Calculus 3:Theorem 6.8 (CA-628). Conservative fields on a convex set have zero circulation
around every triangle (a closed polygonal path). -/
@[kb "openstaxcalculus2016" "3:Theorem 6.8, p. 630"]
theorem IsConservativeOn.curveIntegral_triangle {ω : E → E →L[ℝ] ℝ} {U : Set E}
    (hc : Convex ℝ U) (h : IsConservativeOn ω U) (hω : ContinuousOn ω U) {a b c : E}
    (ha : a ∈ U) (hb : b ∈ U) (hcU : c ∈ U) :
    (∫ᶜ x in Path.segment a b, ω x) + (∫ᶜ x in Path.segment b c, ω x) =
      ∫ᶜ x in Path.segment a c, ω x := by
  rw [h.curveIntegral_segment hc hω ha hb, h.curveIntegral_segment hc hω hb hcU,
    h.curveIntegral_segment hc hω ha hcU]
  ring

/-- OpenStax Calculus 3:Theorem 6.9 (CA-629). A continuous field on an open convex set whose circulation
around every triangle (closed polygon, which is piecewise smooth) vanishes, i.e. which is independent of
path for polygonal paths, is conservative; the potential is `x ↦ ∫ along segment c → x`. Only the
polygonal case of path independence is assumed; the general open connected set is not covered. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.9, p. 631"]
theorem exists_potential_of_triangle {ω : E → E →L[ℝ] ℝ} {U : Set E} (hU : IsOpen U)
    (hc : Convex ℝ U) (hω : ContinuousOn ω U)
    (htri : ∀ a ∈ U, ∀ b ∈ U, ∀ c ∈ U,
      (∫ᶜ x in Path.segment a b, ω x) + (∫ᶜ x in Path.segment b c, ω x) =
        ∫ᶜ x in Path.segment a c, ω x) :
    IsConservativeOn ω U := by
  rcases U.eq_empty_or_nonempty with rfl | ⟨c, hcU⟩
  · exact ⟨fun _ => 0, by simp⟩
  refine ⟨fun x => ∫ᶜ y in Path.segment c x, ω y, fun x hx => ?_⟩
  have h1 : HasFDerivAt (fun y => ∫ᶜ z in Path.segment x y, ω z) (ω x) x :=
    (HasFDerivWithinAt.curveIntegral_segment_source hc hω hx).hasFDerivAt (hU.mem_nhds hx)
  have h2 := h1.const_add (∫ᶜ y in Path.segment c x, ω y)
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards [hU.mem_nhds hx] with y hy
  rw [← htri c hcU x hx y hy]

end General

section Scalar
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- OpenStax Calculus 3:Theorem 6.3 (CA-612). The scalar line integral `∫ f ds = ∫ₐᵇ f(r t) ‖r' t‖ dt`
of `f` along the curve `r`; with the Euclidean norm this is the book's formula in the plane and in space. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.3, p. 605"]
noncomputable def scalarLineIntegral (f : E → ℝ) (r : ℝ → E) (a b : ℝ) : ℝ :=
  ∫ t in a..b, f (r t) * ‖deriv r t‖

private lemma scalar_comp_aux {f : E → ℝ} {U : Set E} (hf : ContinuousOn f U) {r : ℝ → E}
    (hr : ContDiff ℝ 1 r) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) {c d : ℝ}
    (hrU : ∀ s ∈ uIcc c d, r (φ s) ∈ U) :
    ∫ s in c..d, (f (r (φ s)) * ‖deriv r (φ s)‖) * deriv φ s
      = ∫ t in φ c..φ d, f (r t) * ‖deriv r t‖ := by
  have := integral_comp_mul_deriv' (a := c) (b := d) (f := φ) (f' := deriv φ)
    (g := fun t => f (r t) * ‖deriv r t‖)
    (fun x _ => (hφ.differentiable one_ne_zero x).hasDerivAt)
    (hφ.continuous_deriv le_rfl).continuousOn (by
      refine ContinuousOn.mul ?_ (hr.continuous_deriv le_rfl).continuousOn.norm
      refine hf.comp hr.continuous.continuousOn ?_
      rintro _ ⟨s, hs, rfl⟩
      exact hrU s hs)
  exact this

/-- OpenStax Calculus 3:Example 6.16 (CA-614). The scalar line integral does not depend on a one-to-one
orientation-preserving `C¹` reparameterization `φ` (`φ' ≥ 0`). -/
@[kb "openstaxcalculus2016" "3:Example 6.16, p. 606"]
theorem scalarLineIntegral_comp_of_nonneg {f : E → ℝ} {U : Set E} (hf : ContinuousOn f U)
    {r : ℝ → E} (hr : ContDiff ℝ 1 r) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) {c d : ℝ}
    (hrU : ∀ s ∈ uIcc c d, r (φ s) ∈ U) (hφ' : ∀ s ∈ uIcc c d, 0 ≤ deriv φ s) :
    scalarLineIntegral f (r ∘ φ) c d = scalarLineIntegral f r (φ c) (φ d) := by
  unfold scalarLineIntegral
  rw [← scalar_comp_aux hf hr hφ hrU]
  refine integral_congr fun s hs => ?_
  have h1 : deriv (r ∘ φ) s = deriv φ s • deriv r (φ s) :=
    deriv.scomp s (hr.differentiable one_ne_zero _) (hφ.differentiable one_ne_zero s)
  simp only [Function.comp, h1, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hφ' s hs)]
  ring

/-- OpenStax Calculus 3:Example 6.16 (CA-614). The same for an orientation-reversing `C¹`
reparameterization (`φ' ≤ 0`): the result is the integral over `[φ d, φ c]`. -/
@[kb "openstaxcalculus2016" "3:Example 6.16, p. 606"]
theorem scalarLineIntegral_comp_of_nonpos {f : E → ℝ} {U : Set E} (hf : ContinuousOn f U)
    {r : ℝ → E} (hr : ContDiff ℝ 1 r) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) {c d : ℝ}
    (hrU : ∀ s ∈ uIcc c d, r (φ s) ∈ U) (hφ' : ∀ s ∈ uIcc c d, deriv φ s ≤ 0) :
    scalarLineIntegral f (r ∘ φ) c d = scalarLineIntegral f r (φ d) (φ c) := by
  unfold scalarLineIntegral
  rw [integral_symm (φ c) (φ d), ← scalar_comp_aux hf hr hφ hrU, ← intervalIntegral.integral_neg]
  refine integral_congr fun s hs => ?_
  have h1 : deriv (r ∘ φ) s = deriv φ s • deriv r (φ s) :=
    deriv.scomp s (hr.differentiable one_ne_zero _) (hφ.differentiable one_ne_zero s)
  simp only [Function.comp, h1, norm_smul, Real.norm_eq_abs, abs_of_nonpos (hφ' s hs)]
  ring

/-- OpenStax Calculus 3:§6.2 Remark (CA-614). The scalar line integral ignores orientation: reversing the
curve does not change it. -/
@[kb "openstaxcalculus2016" "3:§6.2 Remark (scalar integrals ignore orientation), p. 608"]
theorem scalarLineIntegral_reverse {f : E → ℝ} {U : Set E} (hf : ContinuousOn f U)
    {r : ℝ → E} (hr : ContDiff ℝ 1 r) {a b : ℝ} (hrU : ∀ t ∈ uIcc a b, r t ∈ U) :
    scalarLineIntegral f (fun t => r (a + b - t)) a b = scalarLineIntegral f r a b := by
  have hφ : ContDiff ℝ 1 (fun t : ℝ => a + b - t) := contDiff_const.sub contDiff_id
  have := scalarLineIntegral_comp_of_nonpos hf hr hφ (c := a) (d := b)
    (fun s hs => hrU _ (reflect_mem_uIcc hs)) (fun s _ => by
      have : deriv (fun t : ℝ => a + b - t) s = -1 := by simp
      rw [this]; norm_num)
  have e : (fun t => r (a + b - t)) = r ∘ (fun t : ℝ => a + b - t) := rfl
  rw [e, this]
  simp

end Scalar

section Plane

/-- The covector field `v ↦ P(p) v₁ + Q(p) v₂` of the planar field `F = (P, Q)`. -/
noncomputable def form2 (P Q : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  P p • ContinuousLinearMap.fst ℝ ℝ ℝ + Q p • ContinuousLinearMap.snd ℝ ℝ ℝ

@[simp] lemma form2_apply (P Q : ℝ × ℝ → ℝ) (p v : ℝ × ℝ) :
    form2 P Q p v = P p * v.1 + Q p * v.2 := by
  simp [form2]

lemma continuousOn_form2 {P Q : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hP : ContinuousOn P U)
    (hQ : ContinuousOn Q U) : ContinuousOn (form2 P Q) U := by
  unfold form2
  exact (hP.smul continuousOn_const).add (hQ.smul continuousOn_const)

/-- OpenStax Calculus 3:Equation 6.9 (CA-616). The vector line integral of the planar field `(P, Q)` along
`r(t) = (x t, y t)`: `∫ₐᵇ (P(r t) x'(t) + Q(r t) y'(t)) dt`. -/
@[kb "openstaxcalculus2016" "3:Equation 6.9, p. 609"]
noncomputable def lineIntegral2 (P Q : ℝ × ℝ → ℝ) (x y : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ t in a..b, (P (x t, y t) * deriv x t + Q (x t, y t) * deriv y t)

lemma deriv_pair {x y : ℝ → ℝ} (hx : ContDiff ℝ 1 x) (hy : ContDiff ℝ 1 y) (t : ℝ) :
    deriv (fun s => (x s, y s)) t = (deriv x t, deriv y t) :=
  ((hx.differentiable one_ne_zero t).hasDerivAt.prodMk
    (hy.differentiable one_ne_zero t).hasDerivAt).deriv

lemma lineIntegral_form2 {P Q : ℝ × ℝ → ℝ} {x y : ℝ → ℝ} (hx : ContDiff ℝ 1 x)
    (hy : ContDiff ℝ 1 y) (a b : ℝ) :
    lineIntegral (form2 P Q) (fun t => (x t, y t)) a b = lineIntegral2 P Q x y a b := by
  unfold lineIntegral lineIntegral2
  refine integral_congr fun t _ => ?_
  simp only [deriv_pair hx hy, form2_apply]

/-- OpenStax Calculus 3:§6.1 Definition (CA-607). The planar field `F = (P, Q)` is conservative on `U`:
there is a potential `f` with `∇f = (P, Q)` (that is, `f` has derivative `P dx + Q dy`) at every point of `U`. -/
@[kb "openstaxcalculus2016" "3:§6.1 Definition (conservative field, potential function), p. 596"]
def IsConservative2 (P Q : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ)) : Prop :=
  IsConservativeOn (form2 P Q) U

/-- OpenStax Calculus 3:Theorem 6.7 (CA-625). Fundamental theorem for line integrals in the plane: if
`∇f = (P, Q)` on `U` with `P, Q` continuous and `r = (x, y)` is a `C¹` curve in `U`, then
`∫ₐᵇ (P x' + Q y') dt = f(r b) - f(r a)`. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.7, p. 628"]
theorem lineIntegral2_ftli {f : ℝ × ℝ → ℝ} {P Q : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hf : ∀ p ∈ U, HasFDerivAt f (form2 P Q p) p) (hP : ContinuousOn P U)
    (hQ : ContinuousOn Q U) {x y : ℝ → ℝ} (hx : ContDiff ℝ 1 x) (hy : ContDiff ℝ 1 y) {a b : ℝ}
    (hU : ∀ t ∈ uIcc a b, (x t, y t) ∈ U) :
    lineIntegral2 P Q x y a b = f (x b, y b) - f (x a, y a) := by
  rw [← lineIntegral_form2 hx hy]
  exact lineIntegral_ftli hf (continuousOn_form2 hP hQ) (hx.prodMk hy) hU

lemma fderiv_eq_form2 (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    fderiv ℝ f p = form2 (fun p => fderiv ℝ f p (1, 0)) (fun p => fderiv ℝ f p (0, 1)) p := by
  ext
  · simp
  · simp

/-- OpenStax Calculus 3:Theorem 6.7 (CA-625). Fundamental theorem for line integrals, book form: for
`f` of class `C¹` on an open set `U` containing the `C¹` curve `(x, y)`,
`∫ₐᵇ (f_x x' + f_y y') dt = f(r b) - f(r a)`. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.7, p. 628"]
theorem lineIntegral2_ftli_partials {f : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) {x y : ℝ → ℝ} (hx : ContDiff ℝ 1 x) (hy : ContDiff ℝ 1 y) {a b : ℝ}
    (hxy : ∀ t ∈ uIcc a b, (x t, y t) ∈ U) :
    ∫ t in a..b, (fderiv ℝ f (x t, y t) (1, 0) * deriv x t +
        fderiv ℝ f (x t, y t) (0, 1) * deriv y t) = f (x b, y b) - f (x a, y a) := by
  have hc := hf.continuousOn_fderiv_of_isOpen hU le_rfl
  exact lineIntegral2_ftli (P := fun p => fderiv ℝ f p (1, 0)) (Q := fun p => fderiv ℝ f p (0, 1))
    (fun p hp => by
      rw [← fderiv_eq_form2]
      exact ((hf.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hp)).hasFDerivAt)
    (hc.clm_apply continuousOn_const) (hc.clm_apply continuousOn_const) hx hy hxy

/-- OpenStax Calculus 3:§6.3 (CA-627). The circulation of a conservative planar field around a closed
`C¹` curve is zero. -/
@[kb "openstaxcalculus2016" "3:§6.3 text (closed curves, first consequence of FTLI), p. 630"]
theorem IsConservative2.lineIntegral2_closed {P Q : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (h : IsConservative2 P Q U) (hP : ContinuousOn P U) (hQ : ContinuousOn Q U) {x y : ℝ → ℝ}
    (hx : ContDiff ℝ 1 x) (hy : ContDiff ℝ 1 y) {a b : ℝ} (hU : ∀ t ∈ uIcc a b, (x t, y t) ∈ U)
    (hclosed : (x a, y a) = (x b, y b)) : lineIntegral2 P Q x y a b = 0 := by
  rw [← lineIntegral_form2 hx hy]
  exact IsConservativeOn.lineIntegral_closed h (continuousOn_form2 hP hQ) (hx.prodMk hy) hU hclosed

/-- OpenStax Calculus 3:Theorem 6.8 (CA-628). A conservative planar field is independent of path: two
`C¹` curves in `U` with the same endpoints give the same line integral. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.8, p. 630"]
theorem IsConservative2.lineIntegral2_pathIndependent {P Q : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (h : IsConservative2 P Q U) (hP : ContinuousOn P U) (hQ : ContinuousOn Q U)
    {x y u v : ℝ → ℝ} (hx : ContDiff ℝ 1 x) (hy : ContDiff ℝ 1 y) (hu : ContDiff ℝ 1 u)
    (hv : ContDiff ℝ 1 v) {a b c d : ℝ} (hU : ∀ t ∈ uIcc a b, (x t, y t) ∈ U)
    (hU' : ∀ t ∈ uIcc c d, (u t, v t) ∈ U) (h1 : (x a, y a) = (u c, v c))
    (h2 : (x b, y b) = (u d, v d)) :
    lineIntegral2 P Q x y a b = lineIntegral2 P Q u v c d := by
  rw [← lineIntegral_form2 hx hy, ← lineIntegral_form2 hu hv]
  exact IsConservativeOn.isPathIndependentOn h (continuousOn_form2 hP hQ) _ _ a b c d
    (hx.prodMk hy) (hu.prodMk hv) hU hU' h1 h2

/-- OpenStax Calculus 3:§6.2 Definition (CA-616). Reversing a curve changes the sign of the vector line
integral of a planar field. -/
@[kb "openstaxcalculus2016" "3:§6.2 Definition (vector line integral), p. 608"]
theorem lineIntegral2_reverse {P Q : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hP : ContinuousOn P U)
    (hQ : ContinuousOn Q U) {x y : ℝ → ℝ} (hx : ContDiff ℝ 1 x) (hy : ContDiff ℝ 1 y) {a b : ℝ}
    (hU : ∀ t ∈ uIcc a b, (x t, y t) ∈ U) :
    lineIntegral2 P Q (fun t => x (a + b - t)) (fun t => y (a + b - t)) a b
      = - lineIntegral2 P Q x y a b := by
  have hφ : ContDiff ℝ 1 (fun t : ℝ => a + b - t) := contDiff_const.sub contDiff_id
  rw [← lineIntegral_form2 hx hy, ← lineIntegral_form2 (x := fun t => x (a + b - t))
    (y := fun t => y (a + b - t)) (hx.comp hφ) (hy.comp hφ)]
  exact lineIntegral_neg_orientation (continuousOn_form2 hP hQ) (hx.prodMk hy) hU

/-! scalar line integral, coordinate form -/

/-- The speed `‖r'(t)‖ = √(x'(t)² + y'(t)²)` of the plane curve `(x, y)`. -/
noncomputable def speed2 (x y : ℝ → ℝ) (t : ℝ) : ℝ := √(deriv x t ^ 2 + deriv y t ^ 2)

/-- OpenStax Calculus 3:Equation 6.8 (CA-612). The scalar line integral of `f` along the plane curve
`(x, y)`: `∫ₐᵇ f(x t, y t) √(x'(t)² + y'(t)²) dt`. -/
@[kb "openstaxcalculus2016" "3:Equation 6.8, p. 605"]
noncomputable def scalarLineIntegral2 (f : ℝ × ℝ → ℝ) (x y : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ t in a..b, f (x t, y t) * speed2 x y t

/-- OpenStax Calculus 3:§6.2 Fact (CA-613). Length of the plane curve `(x, y)` on `[a, b]`, as the integral
of the speed `∫ₐᵇ ‖r' t‖ dt` (the book's arc-length formula). -/
@[kb "openstaxcalculus2016" "3:§6.2 Fact (arc length as line integral), p. 607"]
noncomputable def arcLength2 (x y : ℝ → ℝ) (a b : ℝ) : ℝ := ∫ t in a..b, speed2 x y t

/-- OpenStax Calculus 3:§6.2 Fact (CA-613). The scalar line integral of the constant `1` is the length
of the curve: `∫ 1 ds = ∫ ‖r'‖ dt`. -/
@[kb "openstaxcalculus2016" "3:§6.2 Fact (arc length as line integral), p. 607"]
theorem scalarLineIntegral2_one (x y : ℝ → ℝ) (a b : ℝ) :
    scalarLineIntegral2 (fun _ => 1) x y a b = arcLength2 x y a b := by
  simp [scalarLineIntegral2, arcLength2]

lemma speed2_comp {x y φ : ℝ → ℝ} (hx : ContDiff ℝ 1 x) (hy : ContDiff ℝ 1 y)
    (hφ : ContDiff ℝ 1 φ) (s : ℝ) :
    speed2 (x ∘ φ) (y ∘ φ) s = |deriv φ s| * speed2 x y (φ s) := by
  unfold speed2
  rw [deriv_comp s (hx.differentiable one_ne_zero _) (hφ.differentiable one_ne_zero s),
    deriv_comp s (hy.differentiable one_ne_zero _) (hφ.differentiable one_ne_zero s)]
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg _)]
  congr 1
  ring

lemma continuous_speed2 {x y : ℝ → ℝ} (hx : ContDiff ℝ 1 x) (hy : ContDiff ℝ 1 y) :
    Continuous (speed2 x y) := by
  unfold speed2
  have := hx.continuous_deriv le_rfl
  have := hy.continuous_deriv le_rfl
  fun_prop

private lemma scalar2_comp_aux {f : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hf : ContinuousOn f U)
    {x y φ : ℝ → ℝ} (hx : ContDiff ℝ 1 x) (hy : ContDiff ℝ 1 y) (hφ : ContDiff ℝ 1 φ) {c d : ℝ}
    (hU : ∀ s ∈ uIcc c d, (x (φ s), y (φ s)) ∈ U) :
    ∫ s in c..d, (f (x (φ s), y (φ s)) * speed2 x y (φ s)) * deriv φ s
      = ∫ t in φ c..φ d, f (x t, y t) * speed2 x y t := by
  refine integral_comp_mul_deriv' (a := c) (b := d) (f := φ) (f' := deriv φ)
    (g := fun t => f (x t, y t) * speed2 x y t)
    (fun x _ => (hφ.differentiable one_ne_zero x).hasDerivAt)
    (hφ.continuous_deriv le_rfl).continuousOn ?_
  refine ContinuousOn.mul ?_ (continuous_speed2 hx hy).continuousOn
  refine hf.comp (hx.continuous.prodMk hy.continuous).continuousOn ?_
  rintro _ ⟨s, hs, rfl⟩
  exact hU s hs

/-- OpenStax Calculus 3:Example 6.16 (CA-614). Coordinate form of invariance under an orientation-preserving
`C¹` reparameterization. -/
@[kb "openstaxcalculus2016" "3:Example 6.16, p. 606"]
theorem scalarLineIntegral2_comp_of_nonneg {f : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hf : ContinuousOn f U) {x y φ : ℝ → ℝ} (hx : ContDiff ℝ 1 x) (hy : ContDiff ℝ 1 y)
    (hφ : ContDiff ℝ 1 φ) {c d : ℝ} (hU : ∀ s ∈ uIcc c d, (x (φ s), y (φ s)) ∈ U)
    (hφ' : ∀ s ∈ uIcc c d, 0 ≤ deriv φ s) :
    scalarLineIntegral2 f (x ∘ φ) (y ∘ φ) c d = scalarLineIntegral2 f x y (φ c) (φ d) := by
  unfold scalarLineIntegral2
  rw [← scalar2_comp_aux hf hx hy hφ hU]
  refine integral_congr fun s hs => ?_
  simp only [Function.comp, speed2_comp hx hy hφ, abs_of_nonneg (hφ' s hs)]
  ring

/-- OpenStax Calculus 3:Example 6.16 (CA-614). Coordinate form of invariance under an
orientation-reversing `C¹` reparameterization. -/
@[kb "openstaxcalculus2016" "3:Example 6.16, p. 606"]
theorem scalarLineIntegral2_comp_of_nonpos {f : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hf : ContinuousOn f U) {x y φ : ℝ → ℝ} (hx : ContDiff ℝ 1 x) (hy : ContDiff ℝ 1 y)
    (hφ : ContDiff ℝ 1 φ) {c d : ℝ} (hU : ∀ s ∈ uIcc c d, (x (φ s), y (φ s)) ∈ U)
    (hφ' : ∀ s ∈ uIcc c d, deriv φ s ≤ 0) :
    scalarLineIntegral2 f (x ∘ φ) (y ∘ φ) c d = scalarLineIntegral2 f x y (φ d) (φ c) := by
  unfold scalarLineIntegral2
  rw [integral_symm (φ c) (φ d), ← scalar2_comp_aux hf hx hy hφ hU, ← intervalIntegral.integral_neg]
  refine integral_congr fun s hs => ?_
  simp only [Function.comp, speed2_comp hx hy hφ, abs_of_nonpos (hφ' s hs)]
  ring

/-- OpenStax Calculus 3:§6.2 Remark (CA-614). Coordinate form: reversing the plane curve does not change
the scalar line integral. -/
@[kb "openstaxcalculus2016" "3:§6.2 Remark (scalar integrals ignore orientation), p. 608"]
theorem scalarLineIntegral2_reverse {f : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hf : ContinuousOn f U)
    {x y : ℝ → ℝ} (hx : ContDiff ℝ 1 x) (hy : ContDiff ℝ 1 y) {a b : ℝ}
    (hU : ∀ t ∈ uIcc a b, (x t, y t) ∈ U) :
    scalarLineIntegral2 f (fun t => x (a + b - t)) (fun t => y (a + b - t)) a b
      = scalarLineIntegral2 f x y a b := by
  have hφ : ContDiff ℝ 1 (fun t : ℝ => a + b - t) := contDiff_const.sub contDiff_id
  have := scalarLineIntegral2_comp_of_nonpos hf hx hy hφ (c := a) (d := b)
    (fun s hs => hU _ (reflect_mem_uIcc hs)) (fun s _ => by
      have : deriv (fun t : ℝ => a + b - t) s = -1 := by simp
      rw [this]; norm_num)
  have e : (fun t => x (a + b - t)) = x ∘ (fun t : ℝ => a + b - t) := rfl
  have e' : (fun t => y (a + b - t)) = y ∘ (fun t : ℝ => a + b - t) := rfl
  rw [e, e', this]
  simp

/-! flux -/

/-- The unit normal `(y', -x') / ‖r'‖` of the plane curve `(x, y)` pointing to the right of the direction
of travel. -/
noncomputable def unitNormal2 (x y : ℝ → ℝ) (t : ℝ) : ℝ × ℝ :=
  (deriv y t / speed2 x y t, -deriv x t / speed2 x y t)

/-- OpenStax Calculus 3:§6.2 Definition (CA-620). The flux of the planar field `(P, Q)` across the curve
`(x, y)`: `∫ F · N ds` with `N` the right-pointing unit normal, written as `∫ₐᵇ (F·N)(r t) ‖r' t‖ dt`. -/
@[kb "openstaxcalculus2016" "3:§6.2 Definition (flux across a curve), p. 617"]
noncomputable def flux2 (P Q : ℝ × ℝ → ℝ) (x y : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ t in a..b, (P (x t, y t) * (unitNormal2 x y t).1 + Q (x t, y t) * (unitNormal2 x y t).2) *
    speed2 x y t

/-- OpenStax Calculus 3:Theorem 6.6 (CA-621). For a smooth curve (nonvanishing velocity), the flux across
it is `∫ₐᵇ (P y' - Q x') dt`. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.6, p. 617"]
theorem flux2_eq {P Q : ℝ × ℝ → ℝ} {x y : ℝ → ℝ} {a b : ℝ}
    (hreg : ∀ t ∈ uIcc a b, speed2 x y t ≠ 0) :
    flux2 P Q x y a b = ∫ t in a..b, (P (x t, y t) * deriv y t - Q (x t, y t) * deriv x t) := by
  unfold flux2
  refine integral_congr fun t ht => ?_
  have := hreg t ht
  simp only [unitNormal2]
  field_simp
  ring

/-- OpenStax Calculus 3:Theorem 6.6 (CA-621). The flux of `(P, Q)` is the vector line integral of the
rotated field `(-Q, P)`. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.6, p. 617"]
theorem flux2_eq_lineIntegral2 {P Q : ℝ × ℝ → ℝ} {x y : ℝ → ℝ} {a b : ℝ}
    (hreg : ∀ t ∈ uIcc a b, speed2 x y t ≠ 0) :
    flux2 P Q x y a b = lineIntegral2 (fun p => - Q p) P x y a b := by
  rw [flux2_eq hreg]
  unfold lineIntegral2
  refine integral_congr fun t _ => ?_
  simp only
  ring

end Plane

section Space

/-- The covector field `v ↦ P(p) v₁ + Q(p) v₂ + R(p) v₃` of the space field `F = (P, Q, R)`. -/
noncomputable def form3 (P Q R : ℝ × ℝ × ℝ → ℝ) (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ →L[ℝ] ℝ :=
  P p • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) +
    Q p • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) +
    R p • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

@[simp] lemma form3_apply (P Q R : ℝ × ℝ × ℝ → ℝ) (p v : ℝ × ℝ × ℝ) :
    form3 P Q R p v = P p * v.1 + Q p * v.2.1 + R p * v.2.2 := by
  simp [form3]

lemma continuousOn_form3 {P Q R : ℝ × ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ × ℝ)} (hP : ContinuousOn P U)
    (hQ : ContinuousOn Q U) (hR : ContinuousOn R U) : ContinuousOn (form3 P Q R) U := by
  unfold form3
  exact ((hP.smul continuousOn_const).add (hQ.smul continuousOn_const)).add
    (hR.smul continuousOn_const)

/-- OpenStax Calculus 3:Equation 6.9 (CA-616). The vector line integral of the space field `(P, Q, R)`
along `r(t) = (x t, y t, z t)`. -/
@[kb "openstaxcalculus2016" "3:Equation 6.9, p. 609"]
noncomputable def lineIntegral3 (P Q R : ℝ × ℝ × ℝ → ℝ) (x y z : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ t in a..b, (P (x t, y t, z t) * deriv x t + Q (x t, y t, z t) * deriv y t +
    R (x t, y t, z t) * deriv z t)

lemma deriv_triple {x y z : ℝ → ℝ} (hx : ContDiff ℝ 1 x) (hy : ContDiff ℝ 1 y)
    (hz : ContDiff ℝ 1 z) (t : ℝ) :
    deriv (fun s => (x s, y s, z s)) t = (deriv x t, deriv y t, deriv z t) :=
  ((hx.differentiable one_ne_zero t).hasDerivAt.prodMk
    ((hy.differentiable one_ne_zero t).hasDerivAt.prodMk
      (hz.differentiable one_ne_zero t).hasDerivAt)).deriv

lemma lineIntegral_form3 {P Q R : ℝ × ℝ × ℝ → ℝ} {x y z : ℝ → ℝ} (hx : ContDiff ℝ 1 x)
    (hy : ContDiff ℝ 1 y) (hz : ContDiff ℝ 1 z) (a b : ℝ) :
    lineIntegral (form3 P Q R) (fun t => (x t, y t, z t)) a b = lineIntegral3 P Q R x y z a b := by
  unfold lineIntegral lineIntegral3
  refine integral_congr fun t _ => ?_
  simp only [deriv_triple hx hy hz, form3_apply]

/-- OpenStax Calculus 3:§6.1 Definition (CA-607). The space field `F = (P, Q, R)` is conservative on `U`:
it is the gradient `∇f = (P, Q, R)` of a potential `f` at every point of `U`. -/
@[kb "openstaxcalculus2016" "3:§6.1 Definition (conservative field, potential function), p. 596"]
def IsConservative3 (P Q R : ℝ × ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ × ℝ)) : Prop :=
  IsConservativeOn (form3 P Q R) U

/-- OpenStax Calculus 3:Theorem 6.7 (CA-625). Fundamental theorem for line integrals in space, with
`∇f = (P, Q, R)` on `U`. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.7, p. 628"]
theorem lineIntegral3_ftli {f : ℝ × ℝ × ℝ → ℝ} {P Q R : ℝ × ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ × ℝ)}
    (hf : ∀ p ∈ U, HasFDerivAt f (form3 P Q R p) p) (hP : ContinuousOn P U)
    (hQ : ContinuousOn Q U) (hR : ContinuousOn R U) {x y z : ℝ → ℝ} (hx : ContDiff ℝ 1 x)
    (hy : ContDiff ℝ 1 y) (hz : ContDiff ℝ 1 z) {a b : ℝ}
    (hU : ∀ t ∈ uIcc a b, (x t, y t, z t) ∈ U) :
    lineIntegral3 P Q R x y z a b = f (x b, y b, z b) - f (x a, y a, z a) := by
  rw [← lineIntegral_form3 hx hy hz]
  exact lineIntegral_ftli hf (continuousOn_form3 hP hQ hR) (hx.prodMk (hy.prodMk hz)) hU

lemma fderiv_eq_form3 (f : ℝ × ℝ × ℝ → ℝ) (p : ℝ × ℝ × ℝ) :
    fderiv ℝ f p = form3 (fun p => fderiv ℝ f p (1, 0, 0)) (fun p => fderiv ℝ f p (0, 1, 0))
      (fun p => fderiv ℝ f p (0, 0, 1)) p := by
  refine ContinuousLinearMap.ext fun v => ?_
  have : v = v.1 • ((1, 0, 0) : ℝ × ℝ × ℝ) + v.2.1 • ((0, 1, 0) : ℝ × ℝ × ℝ) +
      v.2.2 • ((0, 0, 1) : ℝ × ℝ × ℝ) := by ext <;> simp
  conv_lhs => rw [this]
  simp only [map_add, map_smul, form3_apply, smul_eq_mul]
  ring

/-- OpenStax Calculus 3:Theorem 6.7 (CA-625). Fundamental theorem for line integrals in space, book form
with `f_x, f_y, f_z` for `f` of class `C¹` on an open set `U`. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.7, p. 628"]
theorem lineIntegral3_ftli_partials {f : ℝ × ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ × ℝ)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) {x y z : ℝ → ℝ} (hx : ContDiff ℝ 1 x) (hy : ContDiff ℝ 1 y)
    (hz : ContDiff ℝ 1 z) {a b : ℝ} (hxyz : ∀ t ∈ uIcc a b, (x t, y t, z t) ∈ U) :
    ∫ t in a..b, (fderiv ℝ f (x t, y t, z t) (1, 0, 0) * deriv x t +
        fderiv ℝ f (x t, y t, z t) (0, 1, 0) * deriv y t +
        fderiv ℝ f (x t, y t, z t) (0, 0, 1) * deriv z t) = f (x b, y b, z b) - f (x a, y a, z a) := by
  have hc := hf.continuousOn_fderiv_of_isOpen hU le_rfl
  exact lineIntegral3_ftli (P := fun p => fderiv ℝ f p (1, 0, 0))
    (Q := fun p => fderiv ℝ f p (0, 1, 0)) (R := fun p => fderiv ℝ f p (0, 0, 1))
    (fun p hp => by
      rw [← fderiv_eq_form3]
      exact ((hf.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hp)).hasFDerivAt)
    (hc.clm_apply continuousOn_const) (hc.clm_apply continuousOn_const)
    (hc.clm_apply continuousOn_const) hx hy hz hxyz

/-- OpenStax Calculus 3:§6.3 (CA-627). Zero circulation of a conservative space field around a closed
`C¹` curve. -/
@[kb "openstaxcalculus2016" "3:§6.3 text (closed curves, first consequence of FTLI), p. 630"]
theorem IsConservative3.lineIntegral3_closed {P Q R : ℝ × ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ × ℝ)}
    (h : IsConservative3 P Q R U) (hP : ContinuousOn P U) (hQ : ContinuousOn Q U)
    (hR : ContinuousOn R U) {x y z : ℝ → ℝ} (hx : ContDiff ℝ 1 x) (hy : ContDiff ℝ 1 y)
    (hz : ContDiff ℝ 1 z) {a b : ℝ} (hU : ∀ t ∈ uIcc a b, (x t, y t, z t) ∈ U)
    (hclosed : (x a, y a, z a) = (x b, y b, z b)) : lineIntegral3 P Q R x y z a b = 0 := by
  rw [← lineIntegral_form3 hx hy hz]
  exact IsConservativeOn.lineIntegral_closed h (continuousOn_form3 hP hQ hR)
    (hx.prodMk (hy.prodMk hz)) hU hclosed

/-- OpenStax Calculus 3:Theorem 6.8 (CA-628). A conservative space field is independent of path. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.8, p. 630"]
theorem IsConservative3.lineIntegral3_pathIndependent {P Q R : ℝ × ℝ × ℝ → ℝ}
    {U : Set (ℝ × ℝ × ℝ)} (h : IsConservative3 P Q R U) (hP : ContinuousOn P U)
    (hQ : ContinuousOn Q U) (hR : ContinuousOn R U) {x y z u v w : ℝ → ℝ} (hx : ContDiff ℝ 1 x)
    (hy : ContDiff ℝ 1 y) (hz : ContDiff ℝ 1 z) (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (hw : ContDiff ℝ 1 w) {a b c d : ℝ} (hU : ∀ t ∈ uIcc a b, (x t, y t, z t) ∈ U)
    (hU' : ∀ t ∈ uIcc c d, (u t, v t, w t) ∈ U) (h1 : (x a, y a, z a) = (u c, v c, w c))
    (h2 : (x b, y b, z b) = (u d, v d, w d)) :
    lineIntegral3 P Q R x y z a b = lineIntegral3 P Q R u v w c d := by
  rw [← lineIntegral_form3 hx hy hz, ← lineIntegral_form3 hu hv hw]
  exact IsConservativeOn.isPathIndependentOn h (continuousOn_form3 hP hQ hR) _ _ a b c d
    (hx.prodMk (hy.prodMk hz)) (hu.prodMk (hv.prodMk hw)) hU hU' h1 h2

/-- The speed `√(x'² + y'² + z'²)` of the space curve `(x, y, z)`. -/
noncomputable def lineSpeed3 (x y z : ℝ → ℝ) (t : ℝ) : ℝ :=
  √(deriv x t ^ 2 + deriv y t ^ 2 + deriv z t ^ 2)

/-- OpenStax Calculus 3:Theorem 6.4 (CA-612). Scalar line integral along the space curve `(x, y, z)`. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.4, p. 605"]
noncomputable def scalarLineIntegral3 (f : ℝ × ℝ × ℝ → ℝ) (x y z : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ t in a..b, f (x t, y t, z t) * lineSpeed3 x y z t

/-- OpenStax Calculus 3:§6.2 Fact (CA-613). Length of the space curve as the integral of the speed. -/
@[kb "openstaxcalculus2016" "3:§6.2 Fact (arc length as line integral), p. 607"]
noncomputable def lineArcLength3 (x y z : ℝ → ℝ) (a b : ℝ) : ℝ := ∫ t in a..b, lineSpeed3 x y z t

/-- OpenStax Calculus 3:§6.2 Fact (CA-613). `∫ 1 ds` along a space curve is its length. -/
@[kb "openstaxcalculus2016" "3:§6.2 Fact (arc length as line integral), p. 607"]
theorem scalarLineIntegral3_one (x y z : ℝ → ℝ) (a b : ℝ) :
    scalarLineIntegral3 (fun _ => 1) x y z a b = lineArcLength3 x y z a b := by
  simp [scalarLineIntegral3, lineArcLength3]

end Space

section Inner
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- OpenStax Calculus 3:§6.1 Definition (CA-607). A vector field `F` on an inner product space is
conservative on `U` if it is the gradient (Mathlib's `HasGradientAt`) of a potential function `f` on `U`. -/
@[kb "openstaxcalculus2016" "3:§6.1 Definition (conservative field, potential function), p. 596"]
def IsConservativeField (F : E → E) (U : Set E) : Prop :=
  ∃ f : E → ℝ, ∀ x ∈ U, HasGradientAt f (F x) x

/-- OpenStax Calculus 3:Theorem 6.7 (CA-625). Fundamental theorem for line integrals for a gradient field
in an inner product space: `∫ ⟨F(r t), r'(t)⟩ dt = f(r b) - f(r a)`. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.7, p. 628"]
theorem inner_lineIntegral_ftli {f : E → ℝ} {F : E → E} {U : Set E}
    (hf : ∀ x ∈ U, HasGradientAt f (F x) x) (hF : ContinuousOn F U) {r : ℝ → E}
    (hr : ContDiff ℝ 1 r) {a b : ℝ} (hrU : ∀ t ∈ uIcc a b, r t ∈ U) :
    ∫ t in a..b, inner ℝ (F (r t)) (deriv r t) = f (r b) - f (r a) := by
  have := lineIntegral_ftli (f := f) (ω := fun x => innerSL ℝ (F x)) (U := U) hf
    ((innerSL ℝ).continuous.comp_continuousOn hF) hr hrU
  simpa [lineIntegral] using this

end Inner
