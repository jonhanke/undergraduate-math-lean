import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.Analysis.SpecialFunctions.Exp
import UndergradKB.Common.Attr

/-!
# Petkovsek–Wilf–Zeilberger, "A = B", Chapter 2 (the Sister Celine–Gosper era): thin wrappers
-/

namespace UndergradKB.Combinatorics.Course.AeqB
open ArithmeticFunction Filter Topology
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- CO-025. The sum of `μ(k)` over the divisors `k` of `n` is `1` if `n = 1` and `0` otherwise. -/
@[kb "petkovsekwilfzeilberger1996" "text (Möbius function), p. 32"]
theorem text_p32_moebius_sum (n : ℕ) :
    ∑ k ∈ n.divisors, (μ k : ℤ) = if n = 1 then 1 else 0 := by
  have h : ((μ * ζ : ArithmeticFunction ℤ)) n = (1 : ArithmeticFunction ℤ) n := by
    rw [moebius_mul_coe_zeta]
  rw [coe_mul_zeta_apply] at h
  rw [h]
  exact ArithmeticFunction.one_apply

/-- CO-209. Euler product: for `Re s > 1`, the product over primes of `(1 - p^{-s})⁻¹` converges
to `∑ n^{-s}`. -/
@[kb "petkovsekwilfzeilberger1996" "text (Euler product), p. 32"]
theorem text_p32_euler_product {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun N : ℕ ↦ ∏ p ∈ Nat.primesBelow N, (1 - (p : ℂ) ^ (-s))⁻¹) atTop
      (𝓝 (∑' n : ℕ, 1 / (n : ℂ) ^ s)) := by
  rw [← zeta_eq_tsum_one_div_nat_cpow hs]
  exact riemannZeta_eulerProduct hs

/-- CO-535. The exponential function satisfies `e(x + y) = e(x) e(y)`. -/
@[kb "petkovsekwilfzeilberger1996" "Exercise 2.1.1, p. 31"]
theorem ex_2_1_1 (x y : ℂ) : Complex.exp (x + y) = Complex.exp x * Complex.exp y :=
  Complex.exp_add x y

end UndergradKB.Combinatorics.Course.AeqB
