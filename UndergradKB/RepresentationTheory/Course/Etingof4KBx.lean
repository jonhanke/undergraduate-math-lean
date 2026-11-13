import UndergradKB.RepresentationTheory.FrobeniusTheorem
import UndergradKB.RepresentationTheory.FrobeniusDimension
import UndergradKB.Common.Attr

/-!
# Etingof et al., Introduction to Representation Theory: Chapter 4 (the dimension formula), repository proofs

Thin theorems in the book's terms for formula (5) of Chapter 4, the Frobenius dimension formula for the
Specht module `V_λ`, tagged with the source key `etingof2011` and the locator of the item in the book.
-/

namespace UndergradKB.RepresentationTheory.Course

open Finset UndergradKB.RepresentationTheory

variable {n N : ℕ}

/-- Etingof et al., formula (5): the dimension of the Specht module `V_λ` is `n!` times the product of the
differences `l_i - l_j` for `i < j`, divided by the product of the factorials `l_j !`, where
`l_j = λ_j + N - j`. -/
@[kb "etingof2011" "formula (5), p. 63"]
theorem etingof_4_formula_5_a (la : DiagramsOfSize n) (hN : la.1.colLen 0 ≤ N) :
    (Module.finrank ℂ (spechtIrrRep n la).V : ℂ) =
      ((n.factorial : ℂ) * ∏ i : Fin N, ∏ j ∈ Ioi i,
        ((((la.1.rowLen i + rhoExp N i : ℕ)) : ℂ) - ((la.1.rowLen j + rhoExp N j : ℕ) : ℂ))) /
      ∏ i : Fin N, (((la.1.rowLen i + rhoExp N i).factorial : ℕ) : ℂ) :=
  finrank_specht_eq la hN

open scoped Classical in
/-- Etingof et al., formula (5): the value at the identity of the Frobenius character for the weight `λ`,
multiplied by the product of the factorials `l_i !`, equals `n!` times the product of the differences
`l_i - l_j`. -/
@[kb "etingof2011" "formula (5), p. 63"]
theorem etingof_4_formula_5_b (lam : Fin N → ℕ) (hs : ∑ i, lam i = n) :
    frobChar n N lam 1 * ∏ i, (((lam i + rhoExp N i).factorial : ℕ) : ℂ) =
      (n.factorial : ℂ) * ∏ i, ∏ j ∈ Ioi i,
        ((((lam i + rhoExp N i : ℕ)) : ℂ) - ((lam j + rhoExp N j : ℕ) : ℂ)) :=
  frobChar_one lam hs

open scoped Classical in
/-- Etingof et al., formula (5): the value at the identity of the Frobenius character for the weight `λ` is
`n!` times the product of the differences `l_i - l_j` divided by the product of the factorials `l_i !`. -/
@[kb "etingof2011" "formula (5), p. 63"]
theorem etingof_4_formula_5_c (lam : Fin N → ℕ) (hs : ∑ i, lam i = n) :
    frobChar n N lam 1 = ((n.factorial : ℂ) * ∏ i, ∏ j ∈ Ioi i,
        ((((lam i + rhoExp N i : ℕ)) : ℂ) - ((lam j + rhoExp N j : ℕ) : ℂ))) /
      ∏ i, (((lam i + rhoExp N i).factorial : ℕ) : ℂ) :=
  frobChar_one_eq lam hs

end UndergradKB.RepresentationTheory.Course
