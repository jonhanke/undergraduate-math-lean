import Mathlib.Analysis.SpecialFunctions.Bessel
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import UndergradKB.Common.Attr

/-!
# Petkovsek–Wilf–Zeilberger, "A = B", Chapter 3 (hypergeometric database): thin wrappers
-/

namespace UndergradKB.Combinatorics.Course.AeqB

/-- CO-357. The Bessel function `J_p(x)` is `(x/2)^p` times a (regularized) `0F1` hypergeometric
function of `-(x/2)^2` with lower parameter `p + 1`. -/
@[kb "petkovsekwilfzeilberger1996" "Exercise 3.3.5, p. 49"]
theorem ex_3_3_5 (p x : ℂ) :
    Complex.besselJ p x = (x / 2) ^ p * Complex.regularizedHGFun 0 {p + 1} (-(x / 2) ^ 2) :=
  rfl

/-- CO-360. `Γ(n+1) = n!` and `(a)_n = Γ(n+a)/Γ(a)` (rising factorial). -/
@[kb "petkovsekwilfzeilberger1996" "text (gamma and rising factorials), p. 53"]
theorem text_p53_gamma_pochhammer :
    (∀ n : ℕ, Complex.Gamma (n + 1) = n.factorial) ∧
    (∀ (n : ℕ) (a : ℂ), (∀ k : ℕ, a ≠ -k) →
      Complex.Gamma (a + n) / Complex.Gamma a = (ascPochhammer ℂ n).eval a) :=
  ⟨Complex.Gamma_nat_eq_factorial, fun _ a ha => Complex.Gamma_add_nat_div_Gamma_eq a ha⟩

/-- CO-537. Euler's reflection formula `Γ(z) Γ(1-z) = π / sin(π z)`. -/
@[kb "petkovsekwilfzeilberger1996" "Equation 3.5.1, p. 54"]
theorem eq_3_5_1 (z : ℂ) :
    Complex.Gamma z * Complex.Gamma (1 - z) = Real.pi / Complex.sin (Real.pi * z) :=
  Complex.Gamma_mul_Gamma_one_sub z


/-- CO-358. The rising factorial `(a)_n = a (a+1) ⋯ (a+n-1)`, with `(a)_0 = 1`
(Mathlib's `ascPochhammer`). -/
@[kb "petkovsekwilfzeilberger1996" "Definition (unnumbered) rising factorial, p. 50"]
theorem def_p50_rising_factorial (a : ℝ) (n : ℕ) :
    (ascPochhammer ℝ 0).eval a = 1 ∧
      (ascPochhammer ℝ n).eval a = ∏ i ∈ Finset.range n, (a + i) := by
  refine ⟨by simp, ?_⟩
  induction n with
  | zero => simp
  | succ n ih => rw [ascPochhammer_succ_eval, ih, Finset.prod_range_succ]

/-- CO-536. The gamma function `Γ(z) = ∫_0^∞ t^{z-1} e^{-t} dt` (for real `z > 0`) extends the
factorial: `Γ(n+1) = n!`. -/
@[kb "petkovsekwilfzeilberger1996" "Definition (unnumbered) gamma function, p. 53"]
theorem def_p53_gamma (z : ℝ) (hz : 0 < z) (n : ℕ) :
    Real.Gamma z = ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * t ^ (z - 1) ∧
      Real.Gamma (n + 1) = n.factorial :=
  ⟨Real.Gamma_eq_integral hz, Real.Gamma_nat_eq_factorial n⟩

end UndergradKB.Combinatorics.Course.AeqB
