import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Order
import UndergradKB.RepresentationTheory.Characters
import UndergradKB.RepresentationTheory.CharacterDetermines

/-! # Complex characters (Etingof et al., §3.4 and §3.5)

Over `ℂ` the value of a character at `g⁻¹` is the complex conjugate of its value at `g`. We prove this by averaging
a Hermitian form: for the matrices `M_h` of `ρ(h)` in some basis, `P = ∑ M_hᴴ M_h` is positive definite and
`M_gᴴ P M_g = P`, so `M_{g⁻¹} = P⁻¹ M_gᴴ P` has trace `conj (trace M_g)`.

Consequences:
* §3.4: the character of the dual representation is the complex conjugate of the character, and `V ≅ V*` if and
  only if the character is real valued;
* §3.5: the book's Hermitian inner product `(f₁, f₂) = |G|⁻¹ ∑ f₁(g) conj f₂(g)` agrees with the pairing used for
  characters, and the orthogonality relation (Theorem 3.8) in the book's Hermitian form.
-/

namespace UndergradKB.RepresentationTheory

open Representation Module Matrix ComplexConjugate
open scoped ComplexOrder

variable {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  (ρ : Representation ℂ G V)

/-- Over `ℂ`, `χ(g⁻¹)` is the complex conjugate of `χ(g)`. -/
theorem character_inv_eq_conj (g : G) : ρ.character g⁻¹ = conj (ρ.character g) := by
  classical
  let b := Module.finBasis ℂ V
  let M : G → Matrix (Fin (finrank ℂ V)) (Fin (finrank ℂ V)) ℂ := fun h ↦ LinearMap.toMatrix b b (ρ h)
  have hM : ∀ x y, M (x * y) = M x * M y := by
    intro x y; simp only [M, map_mul, LinearMap.toMatrix_mul]
  have hM1 : M 1 = 1 := by simp [M, LinearMap.toMatrix_one]
  have hunit : ∀ h, IsUnit (M h) := fun h ↦
    ⟨⟨M h, M h⁻¹, by rw [← hM, mul_inv_cancel, hM1], by rw [← hM, inv_mul_cancel, hM1]⟩, rfl⟩
  let P : Matrix (Fin (finrank ℂ V)) (Fin (finrank ℂ V)) ℂ := ∑ h, (M h)ᴴ * M h
  have hP : P.PosDef := by
    refine Matrix.posDef_sum Finset.univ_nonempty fun h _ ↦ ?_
    have := (Matrix.IsUnit.posDef_star_left_conjugate_iff (x := (1 : Matrix _ _ ℂ)) (hunit h)).mpr
      Matrix.PosDef.one
    simpa [star_eq_conjTranspose] using this
  have hinv : (M g)ᴴ * P * M g = P := by
    simp only [P, Finset.mul_sum, Finset.sum_mul]
    refine Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun h ↦ ?_)
    simp only [Equiv.coe_mulRight, hM, conjTranspose_mul, Matrix.mul_assoc]
  have hPu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.isUnit
  have hMinv : M g⁻¹ = P⁻¹ * (M g)ᴴ * P := by
    have h1 : M g * M g⁻¹ = 1 := by rw [← hM, mul_inv_cancel, hM1]
    calc M g⁻¹ = P⁻¹ * P * M g⁻¹ := by rw [nonsing_inv_mul _ hPu, Matrix.one_mul]
      _ = P⁻¹ * ((M g)ᴴ * P * M g) * M g⁻¹ := by rw [hinv]
      _ = P⁻¹ * (M g)ᴴ * P * (M g * M g⁻¹) := by simp only [Matrix.mul_assoc]
      _ = P⁻¹ * (M g)ᴴ * P := by rw [h1, Matrix.mul_one]
  have htr : ∀ h, ρ.character h = (M h).trace := fun h ↦ by
    simp only [character, M, LinearMap.trace_eq_matrix_trace ℂ b]
  rw [htr, htr, hMinv, Matrix.trace_mul_cycle, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mul,
    trace_conjTranspose]
  rfl

/-- **Etingof et al., §3.4**: the character of the dual representation is the complex conjugate of the
character. -/
@[kb "etingof2011" "§3.4, p. 36"]
theorem character_dual_eq_conj (g : G) : ρ.dual.character g = conj (ρ.character g) := by
  rw [char_dual, character_inv_eq_conj]

/-- **Etingof et al., §3.4**: a finite-dimensional complex representation of a finite group is isomorphic to its
dual if and only if its character is real valued. -/
@[kb "etingof2011" "§3.4, p. 36"]
theorem nonempty_equiv_dual_iff : Nonempty (Representation.Equiv ρ ρ.dual) ↔ ∀ g, conj (ρ.character g) = ρ.character g := by
  rw [nonempty_equiv_iff_character_eq_of_charZero]
  constructor
  · intro h g
    rw [← character_dual_eq_conj, ← h]
  · intro h
    funext g
    rw [character_dual_eq_conj, h]

/-- **Etingof et al., §3.5**: the Hermitian inner product `(f₁, f₂) = |G|⁻¹ ∑ f₁(g) conj (f₂(g))` on functions on
`G`. -/
@[kb "etingof2011" "§3.5, p. 37"]
noncomputable def hermitianPairing (f₁ f₂ : G → ℂ) : ℂ := (Nat.card G : ℂ)⁻¹ * ∑ g, f₁ g * conj (f₂ g)

/-- On a character in the second slot, the Hermitian inner product is the pairing used in Mathlib's orthogonality
relations (`χ(g⁻¹)` in place of `conj χ(g)`). -/
theorem hermitianPairing_character (f : G → ℂ) : hermitianPairing f ρ.character = pairing f ρ.character := by
  simp only [hermitianPairing, pairing_apply, character_inv_eq_conj]

/-- **Etingof et al., Theorem 3.8** (Hermitian form): for complex representations, `(χ_V, χ_W)` is the dimension
of the space of intertwining maps from `W` to `V`. -/
@[kb "etingof2011" "Theorem 3.8, p. 37"]
theorem hermitianPairing_character_eq_finrank {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ G W) :
    hermitianPairing ρ.character σ.character = finrank ℂ (IntertwiningMap σ ρ) := by
  have : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [hermitianPairing_character, pairing_apply, card_inv_mul_sum_char_mul_char_eq_finrank]

open scoped Classical in
/-- **Etingof et al., Theorem 3.8** (Hermitian form, irreducible case): the characters of irreducible complex
representations are orthonormal for the Hermitian inner product. -/
@[kb "etingof2011" "Theorem 3.8, p. 37"]
theorem hermitianPairing_irreducible {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ G W) [IsIrreducible ρ] [IsIrreducible σ] :
    hermitianPairing ρ.character σ.character = if Nonempty (Representation.Equiv σ ρ) then 1 else 0 := by
  have : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [hermitianPairing_character, pairing_apply, char_orthonormal]

end UndergradKB.RepresentationTheory
