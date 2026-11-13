import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import UndergradKB.Common.Attr

/-!
# Lebl, Notes on Diffy Qs, Chapter 6 (the Laplace transform): course layer

Thin wrappers around Mathlib stating facts used in the chapter in the book's terms.  The Laplace transform
itself is not in Mathlib; it is developed in `UndergradKB/DifferentialEquations/Laplace.lean`,
`LaplaceUniqueness.lean` and `LaplaceDelta.lean`.
-/

namespace UndergradKB.DifferentialEquations.Course.Ch6

open Polynomial MeasureTheory
open scoped algebraMap

/-- Lebl §6.1 partial fractions (DE-170), Mathlib's general form: over a field `K` containing `ℝ[X]`, a fraction
`f / ∏ gᵢ` with monic pairwise coprime `gᵢ` equals a polynomial plus `∑ rᵢ / gᵢ` with `deg rᵢ < deg gᵢ`.
(For powers of factors, Mathlib has `Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse`.) -/
@[kb "lebldiffyqs2026" "§6.1 Partial fractions, p. 297"]
theorem lebl_partial_fractions (K : Type*) [Field K] [Algebra ℝ[X] K] [FaithfulSMul ℝ[X] K] (f : ℝ[X])
    {ι : Type*} {g : ι → ℝ[X]} {s : Finset ι} (hg : ∀ i ∈ s, (g i).Monic)
    (hcop : Set.Pairwise ↑s fun i j => IsCoprime (g i) (g j)) :
    ∃ (q : ℝ[X]) (r : ι → ℝ[X]), (∀ i ∈ s, (r i).degree < (g i).degree) ∧
      ((↑f : K) / ∏ i ∈ s, ↑(g i)) = ↑q + ∑ i ∈ s, (r i : K) / (g i : K) :=
  div_prod_eq_quo_add_sum_rem_div K f hg hcop

/-- Lebl §6.4.2 the delta function (DE-184), as Mathlib's Dirac measure: `∫ f dδ_a = f(a)`. -/
@[kb "lebldiffyqs2026" "§6.4.2 The delta function, p. 314"]
theorem lebl_dirac_integral (f : ℝ → ℝ) (a : ℝ) : ∫ x, f x ∂Measure.dirac a = f a :=
  integral_dirac f a

end UndergradKB.DifferentialEquations.Course.Ch6
