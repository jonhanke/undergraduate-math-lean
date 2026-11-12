import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Pi
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import UndergradKB.Common.Attr

/-!
# Lebl, Notes on Diffy Qs, Chapter 2 (higher order linear ODEs): course layer

Thin wrappers around Mathlib stating results of the chapter in the book's terms.
-/

namespace UndergradKB.DifferentialEquations.Course.Ch2

open Complex

/-- Lebl §2.1 linear independence of two functions (DE-050). Two functions are linearly
independent iff no nontrivial combination `s f + t g` vanishes identically. -/
@[kb "lebldiffyqs2026" "§2.1 linear independence of two functions, p. 81"]
theorem lebl_two_functions_independent_iff (f g : ℝ → ℝ) :
    LinearIndependent ℝ ![f, g] ↔ ∀ s t : ℝ, s • f + t • g = 0 → s = 0 ∧ t = 0 :=
  LinearIndependent.pair_iff

/-- Lebl Definition candidates D027, D028 (DE-057). The complex number `a + ib` has real part
`a`, imaginary part `b`, and `i² = -1`. -/
@[kb "lebldiffyqs2026" "Definition candidates D027, D028, p. 86"]
theorem lebl_complex_re_im (a b : ℝ) :
    ((a : ℂ) + b * I).re = a ∧ ((a : ℂ) + b * I).im = b ∧ I * I = -1 := by
  refine ⟨by simp, by simp, I_mul_I⟩

/-- Lebl Theorem 2.2.2, Euler's formula (DE-058). `e^{iθ} = cos θ + i sin θ`, and
`e^{a+ib} = e^a (cos b + i sin b)`. -/
@[kb "lebldiffyqs2026" "Theorem 2.2.2, p. 87"]
theorem lebl_euler_formula (θ a b : ℂ) :
    exp (θ * I) = cos θ + sin θ * I ∧ exp (a + b * I) = exp a * (cos b + sin b * I) :=
  ⟨exp_mul_I θ, exp_add_mul_I a b⟩

/-- Lebl §2.3 linear independence (DE-060). Functions `y₀, …, y_{n-1}` are linearly independent
iff `c₁ y₁ + … + cₙ yₙ = 0` identically forces all coefficients to vanish. -/
@[kb "lebldiffyqs2026" "§2.3 linear independence, p. 90"]
theorem lebl_functions_independent_iff {n : ℕ} (y : Fin n → ℝ → ℝ) :
    LinearIndependent ℝ y ↔ ∀ c : Fin n → ℝ, ∑ i, c i • y i = 0 → ∀ i, c i = 0 :=
  Fintype.linearIndependent_iff

end UndergradKB.DifferentialEquations.Course.Ch2
