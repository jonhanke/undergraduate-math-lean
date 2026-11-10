import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import UndergradKB.Common.Attr

/-! # Calculus: Green's theorem

OpenStax Calculus 3 §6.4. Mathlib has the divergence theorem for boxes (hence Green's theorem for rectangles);
there is no line integral over a general closed curve and no integration over a region bounded by a Jordan curve.
We prove Green's theorem (both forms) for rectangles, for regions between two graphs (type I and type II), and the
area formulas. The line integrals along the boundary are written, as in the book, as the sum of the integrals along
the four edges (rectangle), resp. along the two graph edges (the vertical edges contribute nothing to `∫ P dx`). -/

open MeasureTheory Set Real

namespace UndergradKB.Calculus

/-- Bridging definition: the line integral of `P dx + Q dy` around the positively (counterclockwise) oriented
boundary of `[a,b]×[c,d]`: bottom edge left to right, right edge up, top edge right to left, left edge down. -/
noncomputable def rectCirculation (P Q : ℝ × ℝ → ℝ) (a b c d : ℝ) : ℝ :=
  (∫ x in a..b, P (x, c)) + (∫ y in c..d, Q (b, y)) - (∫ x in a..b, P (x, d)) - ∫ y in c..d, Q (a, y)

/-- Bridging definition: the flux of `(P, Q)` across the positively oriented (outward normal) boundary of
`[a,b]×[c,d]`: `∮ P dy - Q dx` written over the four edges. -/
noncomputable def rectFlux (P Q : ℝ × ℝ → ℝ) (a b c d : ℝ) : ℝ :=
  (∫ y in c..d, P (b, y)) - (∫ y in c..d, P (a, y)) + (∫ x in a..b, Q (x, d)) - ∫ x in a..b, Q (x, c)

/-- OpenStax Calculus 3:Theorem 6.12 (CA-632), circulation form of Green's theorem for the rectangle
`[a,b]×[c,d]`: the double integral of `Q_x - P_y` equals the circulation of `(P, Q)` around the boundary.
The partials are the directional derivatives `fderiv _ p (1,0)` and `fderiv _ p (0,1)`. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.12, p. 644"]
theorem green_circulation_rect (P Q : ℝ × ℝ → ℝ) (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (hP : ContinuousOn P (Icc a b ×ˢ Icc c d)) (hQ : ContinuousOn Q (Icc a b ×ˢ Icc c d))
    (hPd : ∀ p ∈ Ioo a b ×ˢ Ioo c d, DifferentiableAt ℝ P p)
    (hQd : ∀ p ∈ Ioo a b ×ˢ Ioo c d, DifferentiableAt ℝ Q p)
    (hi : IntegrableOn (fun p => fderiv ℝ Q p (1, 0) - fderiv ℝ P p (0, 1)) (Icc a b ×ˢ Icc c d)) :
    (∫ x in a..b, ∫ y in c..d, (fderiv ℝ Q (x, y) (1, 0) - fderiv ℝ P (x, y) (0, 1))) =
      rectCirculation P Q a b c d := by
  have h := integral2_divergence_prod_of_hasFDerivAt Q (fun p => - P p)
    (fun p => fderiv ℝ Q p) (fun p => - fderiv ℝ P p) a c b d
    (by rwa [uIcc_of_le hab, uIcc_of_le hcd]) (by rw [uIcc_of_le hab, uIcc_of_le hcd]; exact hP.neg)
    (by
      intro p hp
      rw [min_eq_left hab, max_eq_right hab, min_eq_left hcd, max_eq_right hcd] at hp
      exact (hQd p hp).hasFDerivAt)
    (by
      intro p hp
      rw [min_eq_left hab, max_eq_right hab, min_eq_left hcd, max_eq_right hcd] at hp
      exact (hPd p hp).hasFDerivAt.neg)
    (by
      rw [uIcc_of_le hab, uIcc_of_le hcd]
      refine hi.congr_fun (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
      simp [sub_eq_add_neg])
  simp only [neg_apply, ← sub_eq_add_neg] at h
  rw [h, rectCirculation]
  simp only [intervalIntegral.integral_neg]
  ring

/-- OpenStax Calculus 3:Theorem 6.13 (CA-634), flux form of Green's theorem for the rectangle `[a,b]×[c,d]`:
the double integral of `P_x + Q_y` equals the outward flux of `(P, Q)` across the boundary. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.13, p. 650"]
theorem green_flux_rect (P Q : ℝ × ℝ → ℝ) (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (hP : ContinuousOn P (Icc a b ×ˢ Icc c d)) (hQ : ContinuousOn Q (Icc a b ×ˢ Icc c d))
    (hPd : ∀ p ∈ Ioo a b ×ˢ Ioo c d, DifferentiableAt ℝ P p)
    (hQd : ∀ p ∈ Ioo a b ×ˢ Ioo c d, DifferentiableAt ℝ Q p)
    (hi : IntegrableOn (fun p => fderiv ℝ P p (1, 0) + fderiv ℝ Q p (0, 1)) (Icc a b ×ˢ Icc c d)) :
    (∫ x in a..b, ∫ y in c..d, (fderiv ℝ P (x, y) (1, 0) + fderiv ℝ Q (x, y) (0, 1))) =
      rectFlux P Q a b c d := by
  have h := integral2_divergence_prod_of_hasFDerivAt P Q
    (fun p => fderiv ℝ P p) (fun p => fderiv ℝ Q p) a c b d
    (by rwa [uIcc_of_le hab, uIcc_of_le hcd]) (by rwa [uIcc_of_le hab, uIcc_of_le hcd])
    (by
      intro p hp
      rw [min_eq_left hab, max_eq_right hab, min_eq_left hcd, max_eq_right hcd] at hp
      exact (hPd p hp).hasFDerivAt)
    (by
      intro p hp
      rw [min_eq_left hab, max_eq_right hab, min_eq_left hcd, max_eq_right hcd] at hp
      exact (hQd p hp).hasFDerivAt)
    (by rwa [uIcc_of_le hab, uIcc_of_le hcd])
  rw [h, rectFlux]
  ring

/-- OpenStax Calculus 3:Equation 6.14 (CA-633), area of a rectangle by Green's theorem: `∮ x dy = -∮ y dx` over the
boundary of `[a,b]×[c,d]` both equal the area `(b-a)(d-c)`. -/
@[kb "openstaxcalculus2016" "3:Equation 6.14, p. 650"]
theorem rect_area_line_integrals (a b c d : ℝ) :
    rectCirculation (fun _ => 0) (fun p => p.1) a b c d = (b - a) * (d - c) ∧
    rectCirculation (fun p => - p.2) (fun _ => 0) a b c d = (b - a) * (d - c) := by
  simp only [rectCirculation, intervalIntegral.integral_const, intervalIntegral.integral_neg, smul_eq_mul]
  constructor <;> ring

/-- Area of the rectangle is the Lebesgue measure of `[a,b]×[c,d]`; with `rect_area_line_integrals` this
connects the line integral formulas of CA-633 to measure. -/
theorem rect_area_eq_volume (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) :
    (volume (Icc a b ×ˢ Icc c d)).toReal = (b - a) * (d - c) := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc,
    ← ENNReal.ofReal_mul (by linarith), ENNReal.toReal_ofReal (mul_nonneg (by linarith) (by linarith))]

/-! ### Regions between two graphs -/

/-- OpenStax Calculus 3:Theorem 6.12 (CA-632), type I region `a ≤ x ≤ b`, `g₁ x ≤ y ≤ g₂ x`, the `P dx` half of
Green's theorem: the line integral of `P dx` over the positively oriented boundary (lower graph left to right,
upper graph right to left; the vertical edges contribute `0` to `∫ P dx`) equals `-∬ P_y`, where `Py` is the
partial derivative of `P` in `y`. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.12, p. 644"]
theorem green_typeI_P (P Py : ℝ × ℝ → ℝ) (g₁ g₂ : ℝ → ℝ) (a b : ℝ)
    (hd : ∀ x ∈ uIcc a b, ∀ y ∈ uIcc (g₁ x) (g₂ x), HasDerivAt (fun t => P (x, t)) (Py (x, y)) y)
    (hint : ∀ x ∈ uIcc a b, IntervalIntegrable (fun y => Py (x, y)) volume (g₁ x) (g₂ x))
    (h₁ : IntervalIntegrable (fun x => P (x, g₁ x)) volume a b)
    (h₂ : IntervalIntegrable (fun x => P (x, g₂ x)) volume a b) :
    - (∫ x in a..b, ∫ y in g₁ x..g₂ x, Py (x, y)) =
      (∫ x in a..b, P (x, g₁ x)) - ∫ x in a..b, P (x, g₂ x) := by
  have : (∫ x in a..b, ∫ y in g₁ x..g₂ x, Py (x, y)) = ∫ x in a..b, (P (x, g₂ x) - P (x, g₁ x)) := by
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (hd x hx) (hint x hx)
  rw [this, intervalIntegral.integral_sub h₂ h₁]
  ring

/-- OpenStax Calculus 3:Theorem 6.12 (CA-632), type II region `c ≤ y ≤ d`, `h₁ y ≤ x ≤ h₂ y`, the `Q dy` half of
Green's theorem: the line integral of `Q dy` over the positively oriented boundary (right graph upward, left graph
downward) equals `∬ Q_x`. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.12, p. 644"]
theorem green_typeII_Q (Q Qx : ℝ × ℝ → ℝ) (h₁ h₂ : ℝ → ℝ) (c d : ℝ)
    (hd : ∀ y ∈ uIcc c d, ∀ x ∈ uIcc (h₁ y) (h₂ y), HasDerivAt (fun t => Q (t, y)) (Qx (x, y)) x)
    (hint : ∀ y ∈ uIcc c d, IntervalIntegrable (fun x => Qx (x, y)) volume (h₁ y) (h₂ y))
    (i₁ : IntervalIntegrable (fun y => Q (h₁ y, y)) volume c d)
    (i₂ : IntervalIntegrable (fun y => Q (h₂ y, y)) volume c d) :
    (∫ y in c..d, ∫ x in h₁ y..h₂ y, Qx (x, y)) =
      (∫ y in c..d, Q (h₂ y, y)) - ∫ y in c..d, Q (h₁ y, y) := by
  have : (∫ y in c..d, ∫ x in h₁ y..h₂ y, Qx (x, y)) = ∫ y in c..d, (Q (h₂ y, y) - Q (h₁ y, y)) := by
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (hd y hy) (hint y hy)
  rw [this, intervalIntegral.integral_sub i₂ i₁]

/-- OpenStax Calculus 3:Equation 6.14 (CA-633), area of a type I region `a ≤ x ≤ b`, `g₁ ≤ y ≤ g₂` (continuous
`g₁ ≤ g₂`) as `-∮ y dx`: Lebesgue measure of the region between the graphs equals `-(∫ g₁ - ∫ g₂)`, the line
integral `-∮ y dx` over the positively oriented boundary. -/
@[kb "openstaxcalculus2016" "3:Equation 6.14, p. 650"]
theorem area_typeI_eq_neg_line_integral (g₁ g₂ : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (c₁ : ContinuousOn g₁ (Icc a b)) (c₂ : ContinuousOn g₂ (Icc a b)) (hle : ∀ x ∈ Icc a b, g₁ x ≤ g₂ x) :
    (volume (regionBetween g₁ g₂ (Ioc a b))).toReal =
      - ((∫ x in a..b, g₁ x) - ∫ x in a..b, g₂ x) := by
  have i₁ : IntegrableOn g₁ (Ioc a b) := (c₁.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have i₂ : IntegrableOn g₂ (Ioc a b) := (c₂.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  rw [Measure.volume_eq_prod, volume_regionBetween_eq_integral i₁ i₂ measurableSet_Ioc
    (fun x hx => hle x (Ioc_subset_Icc_self hx)), ENNReal.toReal_ofReal]
  · rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
    simp only [Pi.sub_apply]
    rw [integral_sub i₂ i₁]
    ring
  · exact setIntegral_nonneg measurableSet_Ioc
      (fun x hx => sub_nonneg.2 (hle x (Ioc_subset_Icc_self hx)))

/-- OpenStax Calculus 3:Equation 6.14 (CA-633), area of a type II region `c ≤ y ≤ d`, `h₁ y ≤ x ≤ h₂ y` as
`∮ x dy`: with `Q = x` in `green_typeII_Q`, the iterated integral of `1` over the region is
`∮ x dy = ∫ h₂ - ∫ h₁`. -/
@[kb "openstaxcalculus2016" "3:Equation 6.14, p. 650"]
theorem area_typeII_eq_line_integral (h₁ h₂ : ℝ → ℝ) (c d : ℝ)
    (i₁ : IntervalIntegrable h₁ volume c d) (i₂ : IntervalIntegrable h₂ volume c d) :
    (∫ y in c..d, ∫ _ in h₁ y..h₂ y, (1 : ℝ)) = (∫ y in c..d, h₂ y) - ∫ y in c..d, h₁ y := by
  have := green_typeII_Q (fun p => p.1) (fun _ => 1) h₁ h₂ c d
    (fun y _ x _ => hasDerivAt_id' x) (fun y _ => by simp) i₁ i₂
  simpa using this

/-! ### Divergence theorem for a box -/

/-- OpenStax Calculus 3:Theorem 6.20 (CA-661), divergence theorem for a box `[a,b] ⊆ ℝ³` (`a i ≤ b i`): the triple
integral of `div F = ∑ᵢ ∂Fᵢ/∂xᵢ` over the box equals the total outward flux through the six faces: for each
coordinate `i`, the integral of `Fᵢ` over the front face (`xᵢ = bᵢ`) minus that over the back face (`xᵢ = aᵢ`), the
faces being boxes in the two remaining coordinates (`Fin.insertNth i t y` is the point with `i`-th coordinate `t` and
remaining coordinates `y`). `F` is continuous on the box, differentiable in its interior, with integrable divergence.
Only boxes (not general solids bounded by piecewise smooth surfaces) are covered. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.20, p. 730"]
theorem divergence_theorem_box (a b : Fin 3 → ℝ) (hle : a ≤ b) (F : (Fin 3 → ℝ) → Fin 3 → ℝ)
    (hc : ContinuousOn F (Icc a b))
    (hd : ∀ x ∈ pi univ (fun i => Ioo (a i) (b i)), DifferentiableAt ℝ F x)
    (hi : IntegrableOn (fun x => ∑ i, fderiv ℝ F x (Pi.single i 1) i) (Icc a b)) :
    (∫ x in Icc a b, ∑ i, fderiv ℝ F x (Pi.single i 1) i) =
      ∑ i : Fin 3, ((∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F (i.insertNth (b i) y) i) -
        ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F (i.insertNth (a i) y) i) :=
  integral_divergence_of_hasFDerivAt_off_countable a b hle F (fun x => fderiv ℝ F x) ∅ countable_empty hc
    (fun x hx => (hd x hx.1).hasFDerivAt) hi

/-! ### Stokes' theorem for a flat rectangle -/

/-- Bridging definition: the third component `∂F₂/∂x - ∂F₁/∂y` of the curl of a field `F` of `ℝ³` at the point
`x` (partials taken along coordinate lines). -/
noncomputable def curlZ (F : (Fin 3 → ℝ) → Fin 3 → ℝ) (x : Fin 3 → ℝ) : ℝ :=
  deriv (fun t => F (Function.update x 0 t) 1) (x 0) - deriv (fun t => F (Function.update x 1 t) 0) (x 1)

/-- OpenStax Calculus 3:Theorem 6.19 (CA-658), Stokes' theorem for the flat surface `r(x,y) = (x, y, 0)` over the
rectangle `[a,b]×[c,d]` (normal `r_x × r_y = (0,0,1)`, so the flux of `curl F` is `∬ (curl F)_z dA`): this equals the
circulation of `F` around the counterclockwise boundary. The field is `C¹` (in the plane `z = 0`). General surfaces
are out of reach (see the report): no surface integral machinery, no Stokes on curved surfaces in Mathlib. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.19, p. 714"]
theorem stokes_flat_rect (F : (Fin 3 → ℝ) → Fin 3 → ℝ) (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (hP : ContDiff ℝ 1 (fun p : ℝ × ℝ => F ![p.1, p.2, 0] 0))
    (hQ : ContDiff ℝ 1 (fun p : ℝ × ℝ => F ![p.1, p.2, 0] 1)) :
    (∫ x in a..b, ∫ y in c..d, curlZ F ![x, y, 0]) =
      rectCirculation (fun p : ℝ × ℝ => F ![p.1, p.2, 0] 0) (fun p : ℝ × ℝ => F ![p.1, p.2, 0] 1) a b c d := by
  set P : ℝ × ℝ → ℝ := fun p => F ![p.1, p.2, 0] 0 with hPdef
  set Q : ℝ × ℝ → ℝ := fun p => F ![p.1, p.2, 0] 1 with hQdef
  have hPd : Differentiable ℝ P := hP.differentiable one_ne_zero
  have hQd : Differentiable ℝ Q := hQ.differentiable one_ne_zero
  have hcurl : ∀ x y : ℝ, curlZ F ![x, y, 0] = fderiv ℝ Q (x, y) (1, 0) - fderiv ℝ P (x, y) (0, 1) := by
    intro x y
    have e0 : ∀ t : ℝ, Function.update (![x, y, 0] : Fin 3 → ℝ) 0 t = ![t, y, 0] := by
      intro t; ext i; fin_cases i <;> simp
    have e1 : ∀ t : ℝ, Function.update (![x, y, 0] : Fin 3 → ℝ) 1 t = ![x, t, 0] := by
      intro t; ext i; fin_cases i <;> simp
    have h1 : HasDerivAt (fun t : ℝ => Q (t, y)) (fderiv ℝ Q (x, y) (1, 0)) x := by
      have := (hQd (x, y)).hasFDerivAt.comp_hasDerivAt x
        ((hasDerivAt_id' x).prodMk (hasDerivAt_const x y))
      exact this
    have h2 : HasDerivAt (fun t : ℝ => P (x, t)) (fderiv ℝ P (x, y) (0, 1)) y := by
      have := (hPd (x, y)).hasFDerivAt.comp_hasDerivAt y
        ((hasDerivAt_const y x).prodMk (hasDerivAt_id' y))
      exact this
    simp only [curlZ, e0, e1]
    exact congrArg₂ (· - ·) h1.deriv h2.deriv
  simp only [hcurl]
  exact green_circulation_rect P Q a b c d hab hcd hP.continuous.continuousOn hQ.continuous.continuousOn
    (fun p _ => hPd p) (fun p _ => hQd p)
    (ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      (((hQ.continuous_fderiv one_ne_zero).clm_apply continuous_const).sub
        ((hP.continuous_fderiv one_ne_zero).clm_apply continuous_const)).continuousOn)

/-! ### The swirl field `(-y, x)/(x²+y²)` -/

/-- Bridging definition: line integral `∫ P dx + Q dy` of a planar field along the parametrized curve
`t ↦ (x t, y t)`, `a ≤ t ≤ b`. -/
noncomputable def greenLineIntegral (P Q : ℝ × ℝ → ℝ) (x y : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ t in a..b, (P (x t, y t) * deriv x t + Q (x t, y t) * deriv y t)

/-- The field `(-y, x)/(x²+y²)` of the book's Example 6.47: first component. -/
noncomputable def swirlP (p : ℝ × ℝ) : ℝ := - p.2 / (p.1 ^ 2 + p.2 ^ 2)

/-- The field `(-y, x)/(x²+y²)` of the book's Example 6.47: second component. -/
noncomputable def swirlQ (p : ℝ × ℝ) : ℝ := p.1 / (p.1 ^ 2 + p.2 ^ 2)

/-- OpenStax Calculus 3:Example 6.47 (CA-640), circle enclosing the origin: the circulation of
`(-y, x)/(x²+y²)` around the counterclockwise circle of radius `r > 0` centered at the origin is `2π`. -/
@[kb "openstaxcalculus2016" "3:Example 6.47, p. 658"]
theorem swirl_circulation_origin_circle (r : ℝ) (hr : 0 < r) :
    greenLineIntegral swirlP swirlQ (fun t => r * Real.cos t) (fun t => r * Real.sin t) 0 (2 * π) = 2 * π := by
  have h : ∀ t : ℝ, swirlP (r * Real.cos t, r * Real.sin t) * deriv (fun t => r * Real.cos t) t +
      swirlQ (r * Real.cos t, r * Real.sin t) * deriv (fun t => r * Real.sin t) t = 1 := by
    intro t
    have h1 : deriv (fun t => r * Real.cos t) t = - (r * Real.sin t) :=
      (((Real.hasDerivAt_cos t).const_mul r).deriv).trans (by ring)
    have h2 : deriv (fun t => r * Real.sin t) t = r * Real.cos t :=
      ((Real.hasDerivAt_sin t).const_mul r).deriv
    have h3 : (r * Real.cos t) ^ 2 + (r * Real.sin t) ^ 2 = r ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq t]
    have h4 : r ^ 2 ≠ 0 := by positivity
    simp only [swirlP, swirlQ, h1, h2, h3]
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq t]
  rw [greenLineIntegral]
  simp only [h]
  simp

/-- A field with a potential has zero circulation around a closed curve: if `t ↦ (x t, y t)` is a `C¹` closed
curve (`x 0 = x 2π`, `y 0 = y 2π`) in the open right half plane, then the circulation of the swirl field is `0`,
since `arctan (y/x)` is a potential on `x > 0`. -/
theorem swirl_circulation_closed_right (x y : ℝ → ℝ) (a b : ℝ)
    (hx : ∀ t ∈ uIcc a b, HasDerivAt x (deriv x t) t) (hy : ∀ t ∈ uIcc a b, HasDerivAt y (deriv y t) t)
    (hxi : IntervalIntegrable (deriv x) volume a b) (hyi : IntervalIntegrable (deriv y) volume a b)
    (hpos : ∀ t ∈ uIcc a b, 0 < x t) (hxc : x a = x b) (hyc : y a = y b) :
    greenLineIntegral swirlP swirlQ x y a b = 0 := by
  have hder : ∀ t ∈ uIcc a b, HasDerivAt (fun t => Real.arctan (y t / x t))
      (swirlP (x t, y t) * deriv x t + swirlQ (x t, y t) * deriv y t) t := by
    intro t ht
    have hxt := hpos t ht
    have h := ((hy t ht).div (hx t ht) hxt.ne').arctan
    convert h using 1
    simp only [swirlP, swirlQ, Pi.div_apply]
    have : 0 < x t ^ 2 + y t ^ 2 := by positivity
    field_simp
    ring
  have hxc' : ContinuousOn x (uIcc a b) := fun t ht => (hx t ht).continuousAt.continuousWithinAt
  have hyc' : ContinuousOn y (uIcc a b) := fun t ht => (hy t ht).continuousAt.continuousWithinAt
  have hP : ContinuousOn (fun t => swirlP (x t, y t)) (uIcc a b) := by
    refine (hyc'.neg).div (hxc'.pow 2 |>.add (hyc'.pow 2)) (fun t ht => ?_)
    have := hpos t ht
    positivity
  have hQ : ContinuousOn (fun t => swirlQ (x t, y t)) (uIcc a b) := by
    refine hxc'.div (hxc'.pow 2 |>.add (hyc'.pow 2)) (fun t ht => ?_)
    have := hpos t ht
    positivity
  have hint : IntervalIntegrable (fun t => swirlP (x t, y t) * deriv x t + swirlQ (x t, y t) * deriv y t)
      volume a b := (hxi.continuousOn_mul hP).add (hyi.continuousOn_mul hQ)
  rw [greenLineIntegral, intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint, hxc, hyc]
  simp

/-- OpenStax Calculus 3:Example 6.47 (CA-640), circle not enclosing the origin (the case where the circle lies in
the half plane `x > 0`, i.e. center `(p, q)` with `0 < r < p`): the circulation of `(-y, x)/(x²+y²)` around the
counterclockwise circle is `0`. (A circle not enclosing the origin in general position follows by rotating; not
done.) -/
@[kb "openstaxcalculus2016" "3:Example 6.47, p. 658"]
theorem swirl_circulation_circle_not_enclosing (p q r : ℝ) (hr : 0 < r) (hrp : r < p) :
    greenLineIntegral swirlP swirlQ (fun t => p + r * Real.cos t) (fun t => q + r * Real.sin t) 0 (2 * π) = 0 := by
  have hx : ∀ t, HasDerivAt (fun t => p + r * Real.cos t) (-(r * Real.sin t)) t := fun t => by
    simpa using ((Real.hasDerivAt_cos t).const_mul r).const_add p
  have hy : ∀ t, HasDerivAt (fun t => q + r * Real.sin t) (r * Real.cos t) t := fun t => by
    simpa using ((Real.hasDerivAt_sin t).const_mul r).const_add q
  have hxd : deriv (fun t => p + r * Real.cos t) = fun t => -(r * Real.sin t) := funext fun t => (hx t).deriv
  have hyd : deriv (fun t => q + r * Real.sin t) = fun t => r * Real.cos t := funext fun t => (hy t).deriv
  refine swirl_circulation_closed_right _ _ 0 (2 * π) (fun t _ => by rw [hxd]; exact hx t)
    (fun t _ => by rw [hyd]; exact hy t) ?_ ?_ (fun t _ => ?_) (by simp) (by simp)
  · rw [hxd]; exact (by fun_prop : Continuous fun t : ℝ => -(r * Real.sin t)).intervalIntegrable _ _
  · rw [hyd]; exact (by fun_prop : Continuous fun t : ℝ => r * Real.cos t).intervalIntegrable _ _
  · nlinarith [Real.neg_one_le_cos t, Real.cos_le_one t]

end UndergradKB.Calculus
