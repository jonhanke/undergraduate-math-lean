import UndergradKB.RealAnalysis.RiemannLebesgue
import UndergradKB.RealAnalysis.DarbouxAdditivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import UndergradKB.Common.Attr

/-!
# The fundamental theorem of calculus for the Riemann (Darboux) integral (Lebl, Section 5.3)

Lebl's two forms of the fundamental theorem of calculus, for the Darboux integral `riemannIntegral` of
`UndergradKB.RealAnalysis.Darboux` (ported from ReasBook). ReasBook states them for Mathlib's interval integral;
here they are proved for the book's integral, through `riemannIntegral_eq_intervalIntegral`.
-/

open MeasureTheory Set Filter Topology

namespace UndergradKB.RealAnalysis

variable {a b : ℝ} {f : ℝ → ℝ}

/-- **Fundamental theorem of calculus, first form.** If `f` is Riemann integrable on `[a, b]`, `F` is continuous on
`[a, b]`, differentiable on `(a, b)` and `F' = f` there, then `∫_a^b f = F b - F a`. -/
@[kb "lebl2026" "Theorem 5.3.1, p. 200"]
theorem riemannIntegral_eq_sub_of_hasDerivAt {F : ℝ → ℝ} (hab : a ≤ b) (hf : RiemannIntegrableOn f a b)
    (hFc : ContinuousOn F (Icc a b)) (hFd : ∀ x ∈ Ioo a b, HasDerivAt F (f x) x) :
    riemannIntegral f a b hf = F b - F a := by
  rw [riemannIntegral_eq_intervalIntegral hab hf]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hFc hFd (hf.intervalIntegrable hab)

/-- The integral `∫_a^x f` of Lebl's second form, for `x ∈ [a, b]`, is the interval integral. -/
@[kb "lebl2026" "Theorem 5.3.3, p. 202"]
theorem riemannIntegral_primitive_eq {x : ℝ} (hf : RiemannIntegrableOn f a b) (hx : x ∈ Icc a b) :
    ∃ hfx : RiemannIntegrableOn f a x, riemannIntegral f a x hfx = ∫ t in a..x, f t :=
  ⟨riemannIntegrableOn_subinterval hf le_rfl hx.1 hx.2,
    riemannIntegral_eq_intervalIntegral hx.1 _⟩

/-- **Fundamental theorem of calculus, second form, continuity.** For `f` Riemann integrable on `[a, b]`,
`F x = ∫_a^x f` is continuous on `[a, b]`. -/
@[kb "lebl2026" "Theorem 5.3.3, p. 202"]
theorem continuousOn_primitive (hab : a ≤ b) (hf : RiemannIntegrableOn f a b) :
    ContinuousOn (fun x => ∫ t in a..x, f t) (Icc a b) := by
  have h := intervalIntegral.continuousOn_primitive_interval' (hf.intervalIntegrable hab) left_mem_uIcc
  rwa [uIcc_of_le hab] at h

/-- **Fundamental theorem of calculus, second form, derivative.** For `f` Riemann integrable on `[a, b]` and
continuous at `c ∈ (a, b)`, `F x = ∫_a^x f` is differentiable at `c` with `F' c = f c`. -/
@[kb "lebl2026" "Theorem 5.3.3, p. 202"]
theorem hasDerivAt_primitive {c : ℝ} (hf : RiemannIntegrableOn f a b) (hc : c ∈ Ioo a b)
    (hfc : ContinuousAt f c) : HasDerivAt (fun x => ∫ t in a..x, f t) (f c) c := by
  have hab : a ≤ b := hc.1.le.trans hc.2.le
  have hI : IntegrableOn f (Ioc a b) := (hf.integrableOn_and_integral_eq hab).1
  refine intervalIntegral.integral_hasDerivAt_right
    ((hf.intervalIntegrable hab).mono_set ?_) ⟨Ioo a b, isOpen_Ioo.mem_nhds hc,
      (hI.mono_set Ioo_subset_Ioc_self).aestronglyMeasurable⟩ hfc
  rw [uIcc_of_le hab, uIcc_of_le hc.1.le]
  exact Icc_subset_Icc le_rfl hc.2.le

end UndergradKB.RealAnalysis
