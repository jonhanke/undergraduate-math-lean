import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 3 (Stitz-Zeager): polynomials and complex numbers -/

namespace UndergradKB.Precalculus.Course

open Polynomial

/-- Definition 3.1: a polynomial `aₙxⁿ + ⋯ + a₀` with real coefficients, evaluated at a real number `x`, is the
sum `∑ aᵢ xⁱ` (PC-050). -/
@[kb "stitzzeager2013" "Definition 3.1, p. 247"]
theorem def_3_1_polynomial_function (n : ℕ) (a : ℕ → ℝ) (x : ℝ) :
    (∑ i ∈ Finset.range (n + 1), C (a i) * X ^ i : ℝ[X]).eval x = ∑ i ∈ Finset.range (n + 1), a i * x ^ i := by
  simp [eval_finsetSum]

/-- Definition 3.2: the leading coefficient of a nonzero polynomial is the coefficient of its top-degree term. -/
@[kb "stitzzeager2013" "Definition 3.2, p. 248"]
theorem def_3_2_leading_coeff (p : ℝ[X]) : p.leadingCoeff = p.coeff p.natDegree :=
  rfl

/-- Definition 3.2: the constant term of a polynomial is its value at zero (PC-051). -/
@[kb "stitzzeager2013" "Definition 3.2, p. 248"]
theorem def_3_2_constant_term (p : ℝ[X]) : p.coeff 0 = p.eval 0 :=
  coeff_zero_eq_eval_zero p

/-- Definition 3.2: a nonzero constant polynomial has degree `0`, and the zero polynomial has no degree, which
Mathlib records as `⊥` (PC-051). -/
@[kb "stitzzeager2013" "Definition 3.2, p. 248"]
theorem def_3_2_degree_constants (b : ℝ) (hb : b ≠ 0) :
    (C b : ℝ[X]).natDegree = 0 ∧ (C b : ℝ[X]).degree = 0 ∧ (0 : ℝ[X]).degree = ⊥ :=
  ⟨natDegree_C b, degree_C hb, degree_zero⟩

/-- Definition 3.3: `c` is a zero of multiplicity `m` of the nonzero polynomial `p` exactly when `(x - c)ᵐ` divides
`p` but `(x - c)ᵐ⁺¹` does not (PC-054). -/
@[kb "stitzzeager2013" "Definition 3.3, p. 256"]
theorem def_3_3_zero_multiplicity (p : ℝ[X]) (hp : p ≠ 0) (c : ℝ) (m : ℕ) :
    p.rootMultiplicity c = m ↔ (X - C c) ^ m ∣ p ∧ ¬ (X - C c) ^ (m + 1) ∣ p := by
  rw [← le_rootMultiplicity_iff hp, ← le_rootMultiplicity_iff hp]
  omega

/-- Theorem 3.5 (Remainder Theorem): dividing `p` by `x - c` leaves the constant remainder `p(c)` (PC-057). -/
@[kb "stitzzeager2013" "Theorem 3.5, p. 270"]
theorem thm_3_5_remainder_theorem (p : ℝ[X]) (c : ℝ) :
    p %ₘ (X - C c) = C (p.eval c) :=
  modByMonic_X_sub_C_eq_C_eval p c

/-- Theorem 3.6 (Factor Theorem): `c` is a zero of `p` exactly when `x - c` divides `p` (PC-058). -/
@[kb "stitzzeager2013" "Theorem 3.6, p. 270"]
theorem thm_3_6_factor_theorem (p : ℝ[X]) (c : ℝ) : p.eval c = 0 ↔ (X - C c) ∣ p :=
  dvd_iff_isRoot.symm

/-- Theorem 3.7: a nonzero real polynomial of degree `n` has at most `n` real zeros, counted with multiplicity
(PC-059). -/
@[kb "stitzzeager2013" "Theorem 3.7, p. 276"]
theorem thm_3_7_at_most_n_zeros (p : ℝ[X]) : Multiset.card p.roots ≤ p.natDegree :=
  card_roots' p

/-- Theorem 3.8 (Cauchy's Bound): with `M` the largest of `|aᵢ| / |aₙ|` for `i < n`, every real zero `x` of
`p = aₙxⁿ + ⋯ + a₀` satisfies `|x| < M + 1`. Here `M` is the largest `|aᵢ|` with `i < n`, divided by `|aₙ|` (PC-060). -/
@[kb "stitzzeager2013" "Theorem 3.8, p. 281"]
theorem thm_3_8_cauchy_bound (p : ℝ[X]) (hp : p ≠ 0) (x : ℝ) (hx : p.eval x = 0) :
    ‖x‖₊ < (Finset.range p.natDegree).sup (fun i => ‖p.coeff i‖₊) / ‖p.leadingCoeff‖₊ + 1 :=
  IsRoot.norm_lt_cauchyBound hp hx

/-- Theorem 3.9 (Rational Zeros Theorem): if the integer polynomial `p` has the rational zero `r = a / b` in lowest
terms, then the numerator `a` divides the constant term and the denominator `b` divides the leading coefficient
(PC-061). -/
@[kb "stitzzeager2013" "Theorem 3.9, p. 281"]
theorem thm_3_9_rational_zeros (p : ℤ[X]) (r : ℚ) (hr : aeval r p = 0) :
    IsFractionRing.num ℤ r ∣ p.coeff 0 ∧ (IsFractionRing.den ℤ r : ℤ) ∣ p.leadingCoeff :=
  ⟨num_dvd_of_is_root hr, den_dvd_of_is_root hr⟩

/-- Definition 3.5: every complex number is `a + bi` with `a`, `b` real, namely its real and imaginary parts
(PC-065). -/
@[kb "stitzzeager2013" "Definition 3.5, p. 299"]
theorem def_3_5_complex_number (z : ℂ) : z = (z.re : ℂ) + z.im * Complex.I ∧
    ∀ a b : ℝ, ((a : ℂ) + b * Complex.I).re = a ∧ ((a : ℂ) + b * Complex.I).im = b := by
  refine ⟨(Complex.re_add_im z).symm, fun a b => ?_⟩
  simp

/-- The complex conjugate of `a + bi` is `a - bi` (PC-066). -/
@[kb "stitzzeager2013" "§3.4, p. 300"]
theorem box_3_4_complex_conjugate (a b : ℝ) :
    (starRingEnd ℂ) ((a : ℂ) + b * Complex.I) = (a : ℂ) - b * Complex.I := by
  apply Complex.ext <;> simp

/-- Theorem 3.13 (Fundamental Theorem of Algebra): a complex polynomial of degree at least `1` has a complex zero
(PC-068). -/
@[kb "stitzzeager2013" "Theorem 3.13, p. 302"]
theorem thm_3_13_fundamental_theorem_of_algebra (p : ℂ[X]) (hp : 1 ≤ p.natDegree) :
    ∃ z : ℂ, p.eval z = 0 :=
  Complex.exists_root (natDegree_pos_iff_degree_pos.mp hp)

/-- Theorem 3.14 (Complex Factorization Theorem): a nonzero complex polynomial of degree `n` has `n` complex zeros
counted with multiplicity, and factors as its leading coefficient times the product of `x - z` over the zeros
(PC-069). -/
@[kb "stitzzeager2013" "Theorem 3.14, p. 302"]
theorem thm_3_14_complex_factorization (p : ℂ[X]) :
    Multiset.card p.roots = p.natDegree ∧
    p = C p.leadingCoeff * (p.roots.map fun z => X - C z).prod :=
  ⟨(IsAlgClosed.splits p).natDegree_eq_card_roots.symm, (IsAlgClosed.splits p).eq_prod_roots⟩

/-- Theorem 3.15 (Conjugate Pairs Theorem): if a polynomial with real coefficients vanishes at a complex number `z`,
it also vanishes at the conjugate of `z` (PC-070). -/
@[kb "stitzzeager2013" "Theorem 3.15, p. 303"]
theorem thm_3_15_conjugate_pairs (p : ℝ[X]) (z : ℂ) (hz : aeval z p = 0) :
    aeval ((starRingEnd ℂ) z) p = 0 := by
  rw [aeval_conj, hz, map_zero]

end UndergradKB.Precalculus.Course
