import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.WeylCharacter

/-! # Twisting by the determinant (Etingof et al., Proposition 4.64, character form)

Adding a full column to a diagram with at most `N` rows (`λ ↦ λ + 1^N`) multiplies the Schur polynomial by
`x_1 ⋯ x_N` (`schurPoly_add_one`).  With the Weyl character formula this says that the characters of `L_{λ+1^N}`
and of `L_λ ⊗ Λ^N V` agree at every diagonal matrix (`trace_swRepGL_diagonal_add_one`): the character of the top
exterior power `Λ^N V` at `diag(x)` is `det = x_1 ⋯ x_N`.

Not proved here: the isomorphism `L_{λ+1^N} ≅ L_λ ⊗ Λ^N V` itself, which in the book follows from the character
identity because polynomial representations of `GL_N` are determined by their characters (complete reducibility,
Theorem 4.66), not available.
-/

namespace UndergradKB.RepresentationTheory

open Matrix Finset

section Schur

variable {R : Type*} [CommRing R] {N : ℕ}

/-- Shifting every exponent by one multiplies the alternant by `x_1 ⋯ x_N`. -/
theorem alternant_add_one (l : Fin N → ℕ) :
    (alternant (fun j => l j + 1) : MvPolynomial (Fin N) R) =
      (∏ i : Fin N, MvPolynomial.X i) * alternant l := by
  unfold alternant
  have : (of fun i j => (MvPolynomial.X i : MvPolynomial (Fin N) R) ^ (l j + 1)) =
      diagonal (fun i => MvPolynomial.X i) * of fun i j => (MvPolynomial.X i : MvPolynomial (Fin N) R) ^ l j := by
    ext i j
    simp [diagonal_mul, pow_succ, mul_comm]
  rw [this, det_mul, det_diagonal]

theorem vandermondeDelta_ne_zero [IsDomain R] : (vandermondeDelta R N) ≠ 0 := by
  unfold vandermondeDelta
  refine prod_ne_zero_iff.2 fun i _ => prod_ne_zero_iff.2 fun j hj => sub_ne_zero.2 fun h => ?_
  have := MvPolynomial.X_injective h
  exact (ne_of_lt (mem_Ioi.1 hj)) this

/-- **Etingof et al., Proposition 4.64, on characters.**  `S_{λ+1^N} = x_1 ⋯ x_N · S_λ`. -/
@[kb "etingof2011" "Proposition 4.64, p. 67"]
theorem schurPoly_add_one [IsDomain R] (lam : Fin N → ℕ) :
    (schurPoly (fun j => lam j + 1) : MvPolynomial (Fin N) R) = (∏ i : Fin N, MvPolynomial.X i) * schurPoly lam := by
  have h1 := schurAlternant_eq_vandermondeDelta_mul_schurPoly (R := R) (fun j => lam j + 1)
  have h2 := schurAlternant_eq_vandermondeDelta_mul_schurPoly (R := R) lam
  have hA : (schurAlternant (fun j => lam j + 1) : MvPolynomial (Fin N) R) =
      (∏ i : Fin N, MvPolynomial.X i) * schurAlternant lam := by
    unfold schurAlternant
    rw [← alternant_add_one]
    congr 1
    funext j
    simp [schurExp]
    ring
  apply mul_left_cancel₀ (vandermondeDelta_ne_zero (R := R) (N := N))
  rw [← h1, hA, h2]
  ring

end Schur

section GLShift

variable {N n m : ℕ}

/-- **Etingof et al., Proposition 4.64, on characters.**  If `μ = λ + 1^N` (both with at most `N` rows), the
character of `L_μ` at `diag(x)` is `x_1 ⋯ x_N` times that of `L_λ`, i.e. the character of `L_λ ⊗ Λ^N V`. -/
@[kb "etingof2011" "Proposition 4.64, p. 67"]
theorem trace_swRepGL_diagonal_add_one (la : DiagramsOfSize n) (mu : DiagramsOfSize m)
    (hla : la.1.colLen 0 ≤ N) (hmu : mu.1.colLen 0 ≤ N) (h : ∀ j : Fin N, mu.1.rowLen j = la.1.rowLen j + 1)
    (x : Fin N → ℂ) (hx : ∀ i, x i ≠ 0) :
    LinearMap.trace ℂ _ (swRepGL N m mu (diagGL N x hx)) =
      (∏ i, x i) * LinearMap.trace ℂ _ (swRepGL N n la (diagGL N x hx)) := by
  rw [trace_swRepGL_diagonal, trace_swRepGL_diagonal]
  simp only [weylValue, hla, hmu, ↓reduceIte]
  have : (fun j : Fin N => mu.1.rowLen j) = fun j : Fin N => la.1.rowLen j + 1 := funext h
  rw [this, schurPoly_add_one, map_mul, map_prod]
  simp

end GLShift

end UndergradKB.RepresentationTheory
