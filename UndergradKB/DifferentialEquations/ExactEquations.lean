import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import UndergradKB.Common.Attr

/-! # Integrating factors for exact equations (Lebl §1.8.2)

Partial derivatives are derivatives of the slices `y ↦ M(x, y)` and `x ↦ N(x, y)`. -/

namespace UndergradKB.DifferentialEquations

/-- **Integrating factors** (Lebl, §1.8.2, DE-045): multiplying `M dx + N dy = 0` by `u(x, y)` gives an equation
satisfying the exactness test `(uM)_y = (uN)_x` at a point exactly when `(M_y - N_x) u = u_x N - u_y M` there. -/
@[kb "lebldiffyqs2026" "§1.8.2 integrating factors, p. 68"]
theorem integrating_factor_iff {M N u : ℝ → ℝ → ℝ} {x y My Nx ux uy : ℝ}
    (hMy : HasDerivAt (fun y => M x y) My y) (hNx : HasDerivAt (fun x => N x y) Nx x)
    (hux : HasDerivAt (fun x => u x y) ux x) (huy : HasDerivAt (fun y => u x y) uy y) :
    deriv (fun y => u x y * M x y) y = deriv (fun x => u x y * N x y) x ↔
      (My - Nx) * u x y = ux * N x y - uy * M x y := by
  rw [(huy.fun_mul hMy).deriv, (hux.fun_mul hNx).deriv]
  constructor <;> intro h <;> linarith

/-- **Exact equations have implicit solutions** (Lebl, §1.8, DE-040): if `F` is differentiable with
`F_x = M`, `F_y = N`, and `y` solves `M(x, y) + N(x, y) y' = 0` on an open interval `I`, then `F(x, y(x))` is constant
on `I` (so `F(x, y) = C` is an implicit solution). -/
@[kb "lebldiffyqs2026" "§1.8 exact equation, potential function, p. 63"]
theorem exact_implicit_solution {F : ℝ × ℝ → ℝ} (hF : Differentiable ℝ F) {M N : ℝ → ℝ → ℝ}
    (hM : ∀ x y, fderiv ℝ F (x, y) (1, 0) = M x y) (hN : ∀ x y, fderiv ℝ F (x, y) (0, 1) = N x y)
    {I : Set ℝ} (hIo : IsOpen I) (hIc : IsPreconnected I) {y y' : ℝ → ℝ}
    (hy : ∀ x ∈ I, HasDerivAt y (y' x) x) (hsol : ∀ x ∈ I, M x (y x) + N x (y x) * y' x = 0) :
    ∀ x₁ ∈ I, ∀ x₂ ∈ I, F (x₁, y x₁) = F (x₂, y x₂) := by
  have hd : ∀ x ∈ I, HasDerivAt (fun x => F (x, y x)) 0 x := by
    intro x hx
    have h := (hF (x, y x)).hasFDerivAt.comp_hasDerivAt x ((hasDerivAt_id x).prodMk (hy x hx))
    convert h using 1
    · rfl
    have : ((1 : ℝ), y' x) = (1, 0) + y' x • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
    rw [this, map_add, map_smul, hM, hN, smul_eq_mul, ← hsol x hx]
    ring
  intro x₁ h₁ x₂ h₂
  exact hIo.is_const_of_deriv_eq_zero hIc (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hd x hx).deriv) h₁ h₂

/-- **Path independence for conservative fields** (Lebl, §1.8, DE-041): if `(M, N) = ∇F` with `F` continuously
differentiable, the path integral of `M dx + N dy` along a `C¹` curve `γ : [a, b] → ℝ²` is `F(γ(b)) - F(γ(a))`. -/
@[kb "lebldiffyqs2026" "§1.8 conservative vector field and work, p. 64"]
theorem conservative_path_integral {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 1 F) {M N : ℝ → ℝ → ℝ}
    (hM : ∀ x y, fderiv ℝ F (x, y) (1, 0) = M x y) (hN : ∀ x y, fderiv ℝ F (x, y) (0, 1) = N x y)
    {γ γ' : ℝ → ℝ × ℝ} (hγ : ∀ t, HasDerivAt γ (γ' t) t) (hγ' : Continuous γ') (a b : ℝ) :
    ∫ t in a..b, (M (γ t).1 (γ t).2 * (γ' t).1 + N (γ t).1 (γ t).2 * (γ' t).2) =
      F (γ b) - F (γ a) := by
  have key : ∀ t, M (γ t).1 (γ t).2 * (γ' t).1 + N (γ t).1 (γ t).2 * (γ' t).2 =
      fderiv ℝ F (γ t) (γ' t) := by
    intro t
    have : γ' t = (γ' t).1 • ((1 : ℝ), (0 : ℝ)) + (γ' t).2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
    rw [this, map_add, map_smul, map_smul, ← hM, ← hN]
    simp [smul_eq_mul, mul_comm]
  simp_rw [key]
  have hγc : Continuous γ := continuous_iff_continuousAt.2 fun t => (hγ t).continuousAt
  have hcont : Continuous fun t => fderiv ℝ F (γ t) (γ' t) :=
    ((hF.continuous_fderiv one_ne_zero).comp hγc).clm_apply hγ'
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t _
    exact ((hF.differentiable one_ne_zero) (γ t)).hasFDerivAt.comp_hasDerivAt t (hγ t)
  · exact hcont.intervalIntegrable a b

end UndergradKB.DifferentialEquations
