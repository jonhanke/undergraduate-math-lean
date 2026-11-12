import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.FinGroupCharZero
import Mathlib.RepresentationTheory.Irreducible
import UndergradKB.Common.Attr

/-!
# Etingof et al., Introduction to Representation Theory: Chapter 3 (representations of finite groups)

Thin theorems in the book's terms about characters of finite-dimensional representations, each
tagged with the source key `etingof2011` and the locator of the item in the book.
-/

namespace UndergradKB.RepresentationTheory.Course

open Representation CategoryTheory

universe u

/-- Etingof et al., Section 3.2: the character of a finite-dimensional representation is a class
function, constant on conjugacy classes. -/
@[kb "etingof2011" "§3.2, p. 34"]
theorem etingof_sec_3_2_a {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (g h : G) : ρ.character (h * g * h⁻¹) = ρ.character g :=
  Representation.char_conj ρ g h

/-- Etingof et al., Section 3.2: the value of the character at the identity is the dimension of the
representation. -/
@[kb "etingof2011" "§3.2, p. 34"]
theorem etingof_sec_3_2_b {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : Representation k G V) :
    ρ.character 1 = Module.finrank k V :=
  Representation.char_one ρ

/-- Etingof et al., Theorem 3.8: for a finite group whose order is invertible in the field, the
scalar product of the characters of two finite-dimensional representations equals the dimension
of the space of intertwining operators between them. -/
@[kb "etingof2011" "Theorem 3.8, p. 37"]
theorem etingof_3_8_a {k G V W : Type*} [Field k] [Group G] [Fintype G]
    [Invertible (Nat.card G : k)] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W] (ρ : Representation k G V)
    (σ : Representation k G W) :
    (Nat.card G : k)⁻¹ * ∑ g : G, σ.character g * ρ.character g⁻¹ =
      Module.finrank k (IntertwiningMap ρ σ) :=
  Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ σ

open scoped Classical in
/-- Etingof et al., Theorem 3.8: over an algebraically closed field with invertible group order,
irreducible representations have orthonormal characters: the scalar product is `1` for
isomorphic representations and `0` otherwise. -/
@[kb "etingof2011" "Theorem 3.8, p. 37"]
theorem etingof_3_8_b {k G V W : Type*} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [Invertible (Nat.card G : k)] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρ : Representation k G V) (σ : Representation k G W) [IsIrreducible ρ] [IsIrreducible σ] :
    (Nat.card G : k)⁻¹ * ∑ g : G, ρ.character g * σ.character g⁻¹ =
      if Nonempty (Equiv σ ρ) then (1 : k) else (0 : k) :=
  Representation.char_orthonormal ρ σ

/-- Etingof et al., Section 3.5: over an algebraically closed field of characteristic zero, a
representation of a finite group is irreducible exactly when the norm of its character is `1`
(written with `χ(g⁻¹)` in place of the complex conjugate). -/
@[kb "etingof2011" "§3.5, p. 38"]
theorem etingof_sec_3_5 {k G : Type u} [Field k] [IsAlgClosed k] [CharZero k] [Group G] [Fintype G]
    (V : FDRep k G) :
    Simple V ↔ ∑ g : G, V.character g * V.character g⁻¹ = Nat.card G :=
  FDRep.simple_iff_char_is_norm_one V

end UndergradKB.RepresentationTheory.Course
