import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.MeanValue
import UndergradKB.Common.Attr

/-!
# Lebl, Notes on Diffy Qs, Chapters 0-1: course layer

Thin wrappers around Mathlib stating results of the first chapter in the book's terms.
-/

namespace UndergradKB.DifferentialEquations.Course.Ch1

open MeasureTheory

/-- Lebl §1.1 solving y'=f(x) (DE-013). For continuous `f`, the function
`x ↦ ∫_{x₀}^x f + y₀` solves `y' = f`, `y x₀ = y₀`. -/
@[kb "lebldiffyqs2026" "§1.1 solving y'=f(x), p. 21"]
theorem lebl_ivp_integral {f : ℝ → ℝ} (hf : Continuous f) (x₀ y₀ : ℝ) :
    (∀ x, HasDerivAt (fun x => (∫ t in x₀..x, f t) + y₀) (f x) x) ∧
      (∫ t in x₀..x₀, f t) + y₀ = y₀ := by
  refine ⟨fun x => ?_, by simp⟩
  exact ((hf.integral_hasStrictDerivAt x₀ x).hasDerivAt).add_const y₀

/-- Lebl §1.1 solving y'=f(x) (DE-013). Two differentiable functions with the same derivative
differ by a constant. -/
@[kb "lebldiffyqs2026" "§1.1 solving y'=f(x), p. 21"]
theorem lebl_antiderivative_unique {G H : ℝ → ℝ} (hG : Differentiable ℝ G)
    (hH : Differentiable ℝ H) (h : ∀ x, deriv G x = deriv H x) :
    ∃ c, ∀ x, G x = H x + c := by
  have hd : ∀ x, deriv (G - H) x = 0 := fun x => by
    rw [deriv_sub (hG x) (hH x), h x, sub_self]
  have hc := is_const_of_deriv_eq_zero (hG.sub hH) hd
  refine ⟨G 0 - H 0, fun x => ?_⟩
  have := hc x 0
  simp only [Pi.sub_apply] at this
  linarith

/-- Lebl §1.8.1 test M_y=N_x (DE-042). If `F` is twice continuously differentiable near a point
then its mixed second derivatives agree there (`F_xy = F_yx`). -/
@[kb "lebldiffyqs2026" "§1.8.1 test M_y=N_x, p. 65"]
theorem lebl_mixed_partials_symm {F : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hF : ContDiffAt ℝ 2 F p)
    (v w : ℝ × ℝ) : fderiv ℝ (fderiv ℝ F) p v w = fderiv ℝ (fderiv ℝ F) p w v :=
  (hF.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])) v w

/-- Lebl Theorem 1.8.1 (DE-043). On an open convex set a differentiable 1-form `ω` with
symmetric derivative (the condition `M_y = N_x`) is the derivative of a function `F`. -/
@[kb "lebldiffyqs2026" "Theorem 1.8.1, p. 65"]
theorem lebl_poincare {s : Set (ℝ × ℝ)} (hs : Convex ℝ s) (hso : IsOpen s)
    {ω : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ} (hω : DifferentiableOn ℝ ω s)
    (hdω : ∀ a ∈ s, ∀ x y, fderiv ℝ ω a x y = fderiv ℝ ω a y x) :
    ∃ F : ℝ × ℝ → ℝ, ∀ a ∈ s, HasFDerivAt F (ω a) a :=
  hs.exists_forall_hasFDerivAt_of_fderiv_symmetric hso hω hdω

end UndergradKB.DifferentialEquations.Course.Ch1
