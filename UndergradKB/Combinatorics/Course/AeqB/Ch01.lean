import Mathlib.NumberTheory.SumFourSquares
import Mathlib.Data.Int.Fib.Lemmas
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Complex.Trigonometric
import UndergradKB.Common.Attr

/-!
# Petkovsek–Wilf–Zeilberger, "A = B", Chapter 1 (proof machines): thin wrappers over Mathlib
-/

namespace UndergradKB.Combinatorics.Course.AeqB

/-- CO-346. Euler's four-square identity: a product of two sums of four squares is a sum of four
squares, via an explicit bilinear formula. -/
@[kb "petkovsekwilfzeilberger1996" "Equation 1.3.2, p. 19"]
theorem eq_1_3_2 {R : Type*} [CommRing R] (a b c d x y z w : R) :
    (a * x - b * y - c * z - d * w) ^ 2 + (a * y + b * x + c * w - d * z) ^ 2 +
      (a * z - b * w + c * x + d * y) ^ 2 + (a * w + b * z - c * y + d * x) ^ 2 =
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) :=
  _root_.euler_four_squares a b c d x y z w

/-- CO-527. A rational number has a reduced form `a/b` with `b > 0` and `gcd(a,b) = 1`, and two
reduced forms of the same rational number coincide. -/
@[kb "petkovsekwilfzeilberger1996" "text (canonical form of rationals), p. 19"]
theorem text_p19_rat_reduced :
    (∀ q : ℚ, (q.num : ℚ) / q.den = q ∧ 0 < q.den ∧ q.num.natAbs.Coprime q.den) ∧
    (∀ a b c d : ℤ, 0 < b → 0 < d → a.natAbs.Coprime b.natAbs → c.natAbs.Coprime d.natAbs →
      (a : ℚ) / b = (c : ℚ) / d → a = c ∧ b = d) :=
  ⟨fun q => ⟨Rat.num_div_den q, q.den_pos, q.reduced⟩, fun _ _ _ _ => Rat.div_int_inj⟩

/-- CO-528. Two polynomials in several variables are equal iff all their coefficients agree. -/
@[kb "petkovsekwilfzeilberger1996" "text (canonical form of polynomials), p. 19"]
theorem text_p19_mvpoly_ext {σ R : Type*} [CommSemiring R] (p q : MvPolynomial σ R) :
    p = q ↔ ∀ m, p.coeff m = q.coeff m :=
  MvPolynomial.ext_iff

/-- CO-529. A polynomial of degree at most `L` is determined by its values at `L + 1` distinct
points. -/
@[kb "petkovsekwilfzeilberger1996" "text (polynomial identities by evaluation), p. 20"]
theorem text_p20_poly_eval {K : Type*} [CommRing K] [IsDomain K] (f g : Polynomial K) (L : ℕ)
    (s : Finset K) (hs : s.card = L + 1) (hf : f.degree ≤ L) (hg : g.degree ≤ L)
    (h : ∀ x ∈ s, f.eval x = g.eval x) : f = g := by
  have hL : (L : WithBot ℕ) < (s.card : WithBot ℕ) := by
    rw [hs]; exact_mod_cast Nat.lt_succ_self L
  exact Polynomial.eq_of_degrees_lt_of_eval_finset_eq s (hf.trans_lt hL) (hg.trans_lt hL) h

/-- CO-530. `cos x = (e^{ix} + e^{-ix})/2` and `sin x = (e^{ix} - e^{-ix})/(2i)`. -/
@[kb "petkovsekwilfzeilberger1996" "text (trigonometric identities), p. 22"]
theorem text_p22_cos_sin_exp (x : ℂ) :
    Complex.cos x = (Complex.exp (x * Complex.I) + Complex.exp (-x * Complex.I)) / 2 ∧
    Complex.sin x = (Complex.exp (x * Complex.I) - Complex.exp (-x * Complex.I)) /
      (2 * Complex.I) := by
  refine ⟨?_, ?_⟩
  · rw [eq_div_iff two_ne_zero, mul_comm, Complex.two_cos]
  · rw [eq_div_iff (mul_ne_zero two_ne_zero Complex.I_ne_zero)]
    linear_combination Complex.I * Complex.two_sin x +
      (Complex.exp (-x * Complex.I) - Complex.exp (x * Complex.I)) * Complex.I_mul_I

/-- CO-531. The addition formula for sine and the double-angle formula for cosine. -/
@[kb "petkovsekwilfzeilberger1996" "text (trigonometric identities), p. 22"]
theorem text_p22_trig (x y : ℝ) :
    Real.sin (x + y) = Real.sin x * Real.cos y + Real.cos x * Real.sin y ∧
    Real.cos (2 * x) = 2 * Real.cos x ^ 2 - 1 :=
  ⟨Real.sin_add x y, Real.cos_two_mul x⟩

/-- CO-232. Cassini's identity `F_{n+1} F_{n-1} - F_n² = (-1)^n`. -/
@[kb "petkovsekwilfzeilberger1996" "text (Cassini identity), p. 23"]
theorem text_p23_cassini (n : ℤ) :
    Int.fib (n + 1) * Int.fib (n - 1) - Int.fib n ^ 2 = (-1) ^ n.natAbs :=
  Int.fib_succ_mul_fib_pred_sub_fib_sq n

end UndergradKB.Combinatorics.Course.AeqB
