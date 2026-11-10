import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import UndergradKB.Common.Attr

/-! # Calculus: Green's theorem pulled back to a rectangle

The engine for wave 3 of the calculus coverage. For a `C¹` field of linear forms `ω` on an open set of a real
normed space (a "work form" `v ↦ F(x) · v`) and a `C²` map `r` of a rectangle `[a,b]×[c,d]` into that set, the
double integral over the rectangle of `dω(r_u, r_v) = Dω(r)(r_u)(r_v) - Dω(r)(r_v)(r_u)` equals the circulation of
`ω` around the image of the boundary of the rectangle (bottom edge, right edge, top edge reversed, left edge
reversed). The proof applies Mathlib's divergence theorem on rectangles
(`MeasureTheory.integral2_divergence_prod_of_hasFDerivAt`) to the pulled-back components
`p = ω(r)(r_u)`, `q = ω(r)(r_v)`; the second derivatives of `r` cancel by symmetry
(`ContDiffAt.isSymmSndFDerivAt`).

Specialisations: Green's theorem for regions parametrized by a rectangle (`GreenRegions.lean`), Stokes' theorem for
parametrized surfaces (`StokesParam.lean`), invariance of circulation under homotopies of closed curves. -/

open MeasureTheory Set

namespace UndergradKB.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Green's theorem pulled back to a rectangle: for `ω` of class `C¹` on an open set `U` and `r` of class `C²` mapping
the rectangle into `U`, the double integral of `dω(r_u, r_v)` over the rectangle equals the line integral of `ω`
around the image of the counterclockwise boundary of the rectangle, written as the four edge integrals. -/
theorem green_pullback_rect (ω : E → E →L[ℝ] ℝ) (r : ℝ × ℝ → E) {U : Set E} (hU : IsOpen U)
    (hω : ContDiffOn ℝ 1 ω U) (hr : ContDiff ℝ 2 r) {a b c d : ℝ}
    (hrU : ∀ z ∈ uIcc a b ×ˢ uIcc c d, r z ∈ U) :
    (∫ x in a..b, ∫ y in c..d,
      (fderiv ℝ ω (r (x, y)) (fderiv ℝ r (x, y) (1, 0)) (fderiv ℝ r (x, y) (0, 1)) -
        fderiv ℝ ω (r (x, y)) (fderiv ℝ r (x, y) (0, 1)) (fderiv ℝ r (x, y) (1, 0)))) =
      (∫ x in a..b, ω (r (x, c)) (fderiv ℝ r (x, c) (1, 0))) +
        (∫ y in c..d, ω (r (b, y)) (fderiv ℝ r (b, y) (0, 1))) -
        (∫ x in a..b, ω (r (x, d)) (fderiv ℝ r (x, d) (1, 0))) -
        (∫ y in c..d, ω (r (a, y)) (fderiv ℝ r (a, y) (0, 1))) := by
  set V := r ⁻¹' U with hVdef
  have hV : IsOpen V := hU.preimage hr.continuous
  have hRV : uIcc a b ×ˢ uIcc c d ⊆ V := fun z hz => hrU z hz
  have hr1 : ContDiff ℝ 1 (fderiv ℝ r) := hr.fderiv_right (by norm_num)
  -- derivative of the pulled-back component `z ↦ ω (r z) (r_e z)`
  set D : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ := fun e z =>
    (ω (r z)).comp ((fderiv ℝ (fderiv ℝ r) z).flip e) +
      ((fderiv ℝ ω (r z)).comp (fderiv ℝ r z)).flip (fderiv ℝ r z e) with hDdef
  have hD : ∀ e, ∀ z ∈ V, HasFDerivAt (fun z => ω (r z) (fderiv ℝ r z e)) (D e z) z := by
    intro e z hz
    have h1 : HasFDerivAt (fun z => ω (r z)) ((fderiv ℝ ω (r z)).comp (fderiv ℝ r z)) z :=
      ((hω.differentiableOn one_ne_zero (r z) hz).differentiableAt (hU.mem_nhds hz)).hasFDerivAt.comp z
        (hr.differentiable (by norm_num) z).hasFDerivAt
    have h2 : HasFDerivAt (fun z => fderiv ℝ r z e) ((fderiv ℝ (fderiv ℝ r) z).flip e) z := by
      have := ((hr1.differentiable one_ne_zero z).hasFDerivAt).clm_apply (hasFDerivAt_const e z)
      simpa using this
    exact h1.clm_apply h2
  have hDapp : ∀ e v z, D e z v =
      ω (r z) (fderiv ℝ (fderiv ℝ r) z v e) + fderiv ℝ ω (r z) (fderiv ℝ r z v) (fderiv ℝ r z e) := by
    intro e v z
    simp [hDdef]
  -- the integrand
  set G : ℝ × ℝ → ℝ := fun z =>
    fderiv ℝ ω (r z) (fderiv ℝ r z (1, 0)) (fderiv ℝ r z (0, 1)) -
      fderiv ℝ ω (r z) (fderiv ℝ r z (0, 1)) (fderiv ℝ r z (1, 0)) with hGdef
  have hDG : ∀ z, D (0, 1) z (1, 0) + (-D (1, 0) z) (0, 1) = G z := by
    intro z
    have hs := (hr.contDiffAt (x := z)).isSymmSndFDerivAt (by simp)
    rw [neg_apply, hDapp, hDapp, hs (1, 0) (0, 1), hGdef]
    ring
  have c1 : ContinuousOn (fun z => ω (r z)) V := hω.continuousOn.comp hr.continuous.continuousOn
    (fun z hz => hz)
  have c3 : ContinuousOn (fun z => fderiv ℝ ω (r z)) V :=
    (hω.continuousOn_fderiv_of_isOpen hU le_rfl).comp hr.continuous.continuousOn (fun z hz => hz)
  have c4 : Continuous (fun z => fderiv ℝ r z) := hr.continuous_fderiv (by norm_num)
  have hGc : ContinuousOn G V := by
    have e1 : Continuous (fun z => fderiv ℝ r z (1, 0)) := c4.clm_apply continuous_const
    have e2 : Continuous (fun z => fderiv ℝ r z (0, 1)) := c4.clm_apply continuous_const
    exact ((c3.clm_apply e1.continuousOn).clm_apply e2.continuousOn).sub
      ((c3.clm_apply e2.continuousOn).clm_apply e1.continuousOn)
  have hpc : ∀ e, ContinuousOn (fun z => ω (r z) (fderiv ℝ r z e)) V := fun e =>
    c1.clm_apply (c4.clm_apply continuous_const).continuousOn
  have hcomp : IsCompact (uIcc a b ×ˢ uIcc c d) := isCompact_uIcc.prod isCompact_uIcc
  have hint : IntegrableOn (fun z => D (0, 1) z (1, 0) + (-D (1, 0) z) (0, 1)) (uIcc a b ×ˢ uIcc c d) := by
    simp only [hDG]
    exact (hGc.mono hRV).integrableOn_compact hcomp
  have key := integral2_divergence_prod_of_hasFDerivAt
    (fun z => ω (r z) (fderiv ℝ r z (0, 1))) (fun z => -ω (r z) (fderiv ℝ r z (1, 0)))
    (D (0, 1)) (fun z => -D (1, 0) z) a c b d ((hpc _).mono hRV) ((hpc _).neg.mono hRV)
    (fun z hz => hD _ z (hRV (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self hz)))
    (fun z hz => (hD _ z (hRV (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self hz))).neg) hint
  simp only [hDG, intervalIntegral.integral_neg] at key
  rw [key]
  ring

end UndergradKB.Calculus
