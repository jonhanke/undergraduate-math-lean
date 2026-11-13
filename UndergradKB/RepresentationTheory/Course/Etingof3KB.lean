import UndergradKB.RepresentationTheory.Maschke
import UndergradKB.RepresentationTheory.Characters
import UndergradKB.RepresentationTheory.CharactersMore
import UndergradKB.RepresentationTheory.CharactersChapter4
import UndergradKB.RepresentationTheory.CharacterDetermines
import UndergradKB.RepresentationTheory.AbelianCharacters
import UndergradKB.RepresentationTheory.ComplexCharacters
import UndergradKB.RepresentationTheory.Unitary
import UndergradKB.RepresentationTheory.MatrixElements
import UndergradKB.RepresentationTheory.CharacterTables
import UndergradKB.RepresentationTheory.CharacterTableA5
import UndergradKB.Common.Attr

/-!
# Etingof et al., Introduction to Representation Theory: Chapter 3, results proved in this repository

Course names for the Chapter 3 items of the checklist (representations of finite groups: character
theory) that are proved by declarations of this repository; the ones proved in Mathlib are in
`Course/Etingof3.lean`.  Each theorem restates a repository theorem in the book's terms and is proved
by it, and carries the source key `etingof2011` and the locator of the item in the book.
-/

namespace UndergradKB.RepresentationTheory.Course

open Representation MonoidAlgebra
open scoped ComplexConjugate

universe u v

/-- Etingof et al., Theorem 3.1: the group algebra of a finite group over a field is semisimple
exactly when the characteristic of the field does not divide the order of the group. -/
@[kb "etingof2011" "Theorem 3.1, p. 33"]
theorem etingof_3_1_a {k : Type*} {G : Type*} [Field k] [Group G] [Fintype G] :
    IsSemisimpleRing k[G] ↔ (Fintype.card G : k) ≠ 0 :=
  isSemisimpleRing_iff_card_ne_zero

/-- Etingof et al., Theorem 3.1: over an algebraically closed field whose characteristic does not
divide the order of the group, the squares of the dimensions at the identity of the irreducible
characters add up to the order of the group. -/
@[kb "etingof2011" "Theorem 3.1, p. 33"]
theorem etingof_3_1_b {k : Type u} {G : Type v} [Field k] [Group G] [Fintype G] [IsAlgClosed k]
    [Invertible (Nat.card G : k)] : ∑ χ : irrChars k G, (χ : G → k) 1 ^ 2 = Nat.card G :=
  sum_irrChars_one_sq

/-- Etingof et al., Theorem 3.1: in characteristic zero, the squares of the dimensions of a full
list of pairwise non-isomorphic irreducible representations add up to the order of the group. -/
@[kb "etingof2011" "Theorem 3.1, p. 33"]
theorem etingof_3_1_c {k : Type u} {G : Type v} [Field k] [Group G] [Fintype G] [IsAlgClosed k]
    [Invertible (Nat.card G : k)] [CharZero k] {ι : Type*} [Fintype ι] (X : ι → IrrRep k G)
    (hinj : ∀ i j, Nonempty (Representation.Equiv (X i).ρ (X j).ρ) → i = j)
    (hsurj : ∀ Y : IrrRep k G, ∃ i, Nonempty (Representation.Equiv Y.ρ (X i).ρ)) :
    ∑ i, Module.finrank k (X i).V ^ 2 = Nat.card G :=
  sum_finrank_sq X hinj hsurj

/-- Etingof et al., Proposition 3.2: if the group algebra of a finite group is semisimple, the
characteristic of the field does not divide the order of the group. -/
@[kb "etingof2011" "Proposition 3.2, p. 33"]
theorem etingof_3_2 {k : Type*} {G : Type*} [Field k] [Group G] [Fintype G]
    [IsSemisimpleRing k[G]] : (Fintype.card G : k) ≠ 0 :=
  card_ne_zero_of_isSemisimpleRing

/-- Etingof et al., Theorem 3.5: over an algebraically closed field whose characteristic does not
divide the order of the group, the irreducible characters span the class functions. -/
@[kb "etingof2011" "Theorem 3.5, p. 34"]
theorem etingof_3_5_a {k : Type u} {G : Type v} [Field k] [Group G] [Fintype G] [IsAlgClosed k]
    [Invertible (Nat.card G : k)] : Submodule.span k (irrChars k G) = classFunctions k G :=
  span_irrChars

/-- Etingof et al., Theorem 3.5: the irreducible characters are linearly independent, so together
with spanning they form a basis of the class functions. -/
@[kb "etingof2011" "Theorem 3.5, p. 34"]
theorem etingof_3_5_b {k : Type u} {G : Type v} [Field k] [Group G] [Fintype G] [IsAlgClosed k]
    [Invertible (Nat.card G : k)] : LinearIndepOn k id (irrChars k G) :=
  linearIndepOn_irrChars

/-- Etingof et al., Corollary 3.6: the number of irreducible characters equals the number of
conjugacy classes. -/
@[kb "etingof2011" "Corollary 3.6, p. 34"]
theorem etingof_3_6_a {k : Type u} {G : Type v} [Field k] [Group G] [Fintype G] [IsAlgClosed k]
    [Invertible (Nat.card G : k)] : Nat.card (irrChars k G) = Nat.card (ConjClasses G) :=
  card_irrChars

/-- Etingof et al., Corollary 3.6: there is a family of pairwise non-isomorphic irreducible
representations, containing a copy of every irreducible one, with as many members as the group has
conjugacy classes. -/
@[kb "etingof2011" "Corollary 3.6, p. 34"]
theorem etingof_3_6_b {k : Type u} {G : Type v} [Field k] [Group G] [Fintype G] [IsAlgClosed k]
    [Invertible (Nat.card G : k)] :
    ∃ (ι : Type (max u v)) (_ : Fintype ι) (X : ι → IrrRep k G),
      (∀ i j, Nonempty (Representation.Equiv (X i).ρ (X j).ρ) → i = j) ∧
      (∀ Y : IrrRep k G, ∃ i, Nonempty (Representation.Equiv Y.ρ (X i).ρ)) ∧
      Fintype.card ι = Nat.card (ConjClasses G) :=
  exists_irreducibles_card_eq_card_conjClasses

/-- Etingof et al., Corollary 3.7: in characteristic zero, two finite-dimensional representations
of a finite group with the same character are isomorphic. -/
@[kb "etingof2011" "Corollary 3.7, p. 35"]
theorem etingof_3_7_a {k : Type*} {G : Type*} {V : Type*} {W : Type*} [Field k] [CharZero k]
    [Group G] [Fintype G] [AddCommGroup V] [Module k V] [FiniteDimensional k V] [AddCommGroup W]
    [Module k W] [FiniteDimensional k W] (ρ : Representation k G V) (σ : Representation k G W)
    (h : ρ.character = σ.character) : Nonempty (ρ.Equiv σ) :=
  nonempty_equiv_of_character_eq ρ σ h

/-- Etingof et al., Corollary 3.7: in characteristic zero, two finite-dimensional representations
of a finite group are isomorphic exactly when their characters agree. -/
@[kb "etingof2011" "Corollary 3.7, p. 35"]
theorem etingof_3_7_b {k : Type*} {G : Type*} {V : Type*} {W : Type*} [Field k] [CharZero k]
    [Group G] [Fintype G] [AddCommGroup V] [Module k V] [FiniteDimensional k V] [AddCommGroup W]
    [Module k W] [FiniteDimensional k W] (ρ : Representation k G V) (σ : Representation k G W) :
    Nonempty (ρ.Equiv σ) ↔ ρ.character = σ.character :=
  nonempty_equiv_iff_character_eq_of_charZero ρ σ

/-- Etingof et al., §3.3: the group of complex characters of a finite abelian group has the same
number of elements as the group. -/
@[kb "etingof2011" "§3.3, p. 35"]
theorem etingof_sec_3_3_a (G : Type*) [CommGroup G] [Finite G] :
    Nat.card (G →* ℂˣ) = Nat.card G :=
  nat_card_monoidHom_units_complex G

/-- Etingof et al., §3.3: a finite abelian group is isomorphic, non-canonically, to its group of
complex characters. -/
@[kb "etingof2011" "§3.3, p. 35"]
theorem etingof_sec_3_3_b (G : Type*) [CommGroup G] [Finite G] : Nonempty (G ≃* (G →* ℂˣ)) :=
  nonempty_mulEquiv_monoidHom_units_complex G

/-- Etingof et al., §3.3: a finite abelian group is canonically isomorphic to its double dual, the
isomorphism sending an element to evaluation at it. -/
@[kb "etingof2011" "§3.3, p. 35"]
theorem etingof_sec_3_3_c (G : Type*) [CommGroup G] [Finite G] :
    ∃ e : G ≃* ((G →* ℂˣ) →* ℂˣ), ∀ (g : G) (χ : G →* ℂˣ), e g χ = χ g :=
  exists_mulEquiv_doubleDual_units_complex G

/-- Etingof et al., §3.4: the character of the dual representation at `g` is the complex conjugate
of the character of the representation at `g`. -/
@[kb "etingof2011" "§3.4, p. 36"]
theorem etingof_sec_3_4_a {G : Type*} {V : Type*} [Group G] [Fintype G] [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (g : G) :
    ρ.dual.character g = conj (ρ.character g) :=
  character_dual_eq_conj ρ g

/-- Etingof et al., §3.4: a complex representation of a finite group is isomorphic to its dual
exactly when its character is real valued. -/
@[kb "etingof2011" "§3.4, p. 36"]
theorem etingof_sec_3_4_b {G : Type*} {V : Type*} [Group G] [Fintype G] [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) :
    Nonempty (ρ.Equiv ρ.dual) ↔ ∀ g, conj (ρ.character g) = ρ.character g :=
  nonempty_equiv_dual_iff ρ

/-- Etingof et al., §3.4: the character of a complex representation of a finite group at `g⁻¹` is
the complex conjugate of its value at `g`. -/
@[kb "etingof2011" "§3.4, p. 36"]
theorem etingof_sec_3_4_c {G : Type*} {V : Type*} [Group G] [Fintype G] [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (g : G) :
    ρ.character g⁻¹ = conj (ρ.character g) :=
  character_inv_eq_conj ρ g

/-- Etingof et al., §3.5: on a character in the second slot, the Hermitian inner product agrees with
the pairing used in the orthogonality relations. -/
@[kb "etingof2011" "§3.5, p. 37"]
theorem etingof_sec_3_5_a {G : Type*} {V : Type*} [Group G] [Fintype G] [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (f : G → ℂ) :
    hermitianPairing f ρ.character = pairing f ρ.character :=
  hermitianPairing_character ρ f

/-- Etingof et al., §3.5: the Hermitian inner product of the characters of two complex
representations is the dimension of the space of intertwining maps between them. -/
@[kb "etingof2011" "§3.5, p. 37"]
theorem etingof_sec_3_5_b {G : Type*} {V : Type*} [Group G] [Fintype G] [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) {W : Type*} [AddCommGroup W]
    [Module ℂ W] [FiniteDimensional ℂ W] (σ : Representation ℂ G W) :
    hermitianPairing ρ.character σ.character =
      (Module.finrank ℂ (σ.IntertwiningMap ρ) : ℂ) :=
  hermitianPairing_character_eq_finrank ρ σ

open scoped Classical in
/-- Etingof et al., §3.5: the characters of two irreducible complex representations are orthonormal,
the inner product being one for isomorphic representations and zero otherwise. -/
@[kb "etingof2011" "§3.5, p. 37"]
theorem etingof_sec_3_5_c {G : Type*} {V : Type*} [Group G] [Fintype G] [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) {W : Type*} [AddCommGroup W]
    [Module ℂ W] [FiniteDimensional ℂ W] (σ : Representation ℂ G W) [ρ.IsIrreducible]
    [σ.IsIrreducible] :
    hermitianPairing ρ.character σ.character = if Nonempty (σ.Equiv ρ) then 1 else 0 :=
  hermitianPairing_irreducible ρ σ

open scoped Classical in
/-- Etingof et al., Theorem 3.9 (second orthogonality): the sum over irreducible characters of
`χ(g) χ(h⁻¹)` is the order of the centralizer of `g` when `g` and `h` are conjugate, and zero
otherwise. -/
@[kb "etingof2011" "Theorem 3.9, p. 38"]
theorem etingof_3_9 {k : Type u} {G : Type v} [Field k] [Group G] [Fintype G] [IsAlgClosed k]
    [Invertible (Nat.card G : k)] (g h : G) :
    ∑ χ : irrChars k G, (χ : G → k) g * (χ : G → k) h⁻¹ =
      if IsConj g h then (Nat.card (Subgroup.centralizer {g}) : k) else 0 :=
  sum_irrChars_mul_inv g h

/-- Etingof et al., Theorem 3.11: a finite-dimensional representation of a finite group on an inner
product space carries an invariant, conjugate-symmetric, positive definite sesquilinear form. -/
@[kb "etingof2011" "Theorem 3.11, p. 39"]
theorem etingof_3_11_a {G : Type*} {V : Type*} [Group G] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [Fintype G] (ρ : Representation ℂ G V) [FiniteDimensional ℂ V] :
    ∃ B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ,
      (∀ (h : G) (v w : V), B (ρ h v) (ρ h w) = B v w) ∧
      (∀ v w : V, conj (B v w) = B w v) ∧
      (∀ v : V, v ≠ 0 → (B v v).im = 0 ∧ 0 < (B v v).re) :=
  exists_invariant_posDef_form ρ

/-- Etingof et al., Theorem 3.11: every finite-dimensional complex representation of a finite group
has an invariant positive definite Hermitian form, so it is unitary. -/
@[kb "etingof2011" "Theorem 3.11, p. 39"]
theorem etingof_3_11_b {G : Type*} {V : Type*} [Group G] [Fintype G] [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) :
    ∃ B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ, IsPosDefHermitian B ∧ IsInvariantForm ρ B :=
  exists_invariantPosDefHermitian ρ

/-- Etingof et al., Theorem 3.11: two invariant positive definite Hermitian forms on an irreducible
complex representation are proportional by a positive scalar. -/
@[kb "etingof2011" "Theorem 3.11, p. 39"]
theorem etingof_3_11_c {G : Type*} {V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] {ρ : Representation ℂ G V} [IsIrreducible ρ]
    {B₁ B₂ : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (h₁ : IsPosDefHermitian B₁) (h₂ : IsPosDefHermitian B₂)
    (i₁ : IsInvariantForm ρ B₁) (i₂ : IsInvariantForm ρ B₂) :
    ∃ c : ℝ, 0 < c ∧ ∀ v w, B₂ v w = (c : ℂ) * B₁ v w :=
  posDef_forms_proportional h₁ h₂ i₁ i₂

/-- Etingof et al., §3.6: for a finite group, the complex conjugate of a finite-dimensional complex
representation is isomorphic to its dual. -/
@[kb "etingof2011" "§3.6, p. 39"]
theorem etingof_sec_3_6 {G : Type*} {V : Type*} [Group G] [AddCommGroup V] [Module ℂ V] [Fintype G]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) :
    Nonempty ((conjRepresentation ρ).Equiv ρ.dual) :=
  nonempty_equiv_conj_dual ρ

/-- Etingof et al., Theorem 3.12: a finite-dimensional unitary representation of any group is
completely reducible, every subrepresentation having a complement. -/
@[kb "etingof2011" "Theorem 3.12, p. 39"]
theorem etingof_3_12 {G : Type*} {V : Type*} [Group G] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] {ρ : Representation ℂ G V}
    (hρ : IsUnitaryRepresentation ρ) (W : Subrepresentation ρ) : ∃ W', IsCompl W W' :=
  IsUnitaryRepresentation.exists_isCompl hρ W

/-- Etingof et al., Proposition 3.14: matrix elements of two non-isomorphic irreducible
representations are orthogonal. -/
@[kb "etingof2011" "Proposition 3.14, p. 39"]
theorem etingof_3_14_a {k : Type*} {G : Type*} {V : Type*} {W : Type*} {ι : Type*} {κ : Type*}
    [Field k] [Group G] [Fintype G] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] {ρ : Representation k G V}
    {σ : Representation k G W} [ρ.IsIrreducible] [σ.IsIrreducible] (hne : ¬Nonempty (ρ.Equiv σ))
    (b : Module.Basis ι k V) (c : Module.Basis κ k W) (i j : ι) (l m : κ) :
    ∑ g, LinearMap.toMatrix b b (ρ g) i j * LinearMap.toMatrix c c (σ g⁻¹) l m = 0 :=
  sum_matrix_mul_matrix_inv_eq_zero hne b c i j l m

/-- Etingof et al., Proposition 3.14: for an irreducible representation, the matrix elements
`t_ij` and `t_lm` satisfy the orthogonality relation with value `|G| / dim V` when `i = m` and
`j = l`, and zero otherwise. -/
@[kb "etingof2011" "Proposition 3.14, p. 39"]
theorem etingof_3_14_b {k : Type*} {G : Type*} {V : Type*} {ι : Type*} [Field k] [Group G]
    [Fintype G] [AddCommGroup V] [Module k V] [Fintype ι] [DecidableEq ι] [IsAlgClosed k]
    [Invertible (Nat.card G : k)] {ρ : Representation k G V} [FiniteDimensional k V]
    [ρ.IsIrreducible] (b : Module.Basis ι k V) (i j l m : ι) :
    ∑ g, LinearMap.toMatrix b b (ρ g) i j * LinearMap.toMatrix b b (ρ g⁻¹) l m =
      if i = m ∧ j = l then (Nat.card G : k) / (Module.finrank k V : k) else 0 :=
  sum_matrix_mul_matrix_inv b i j l m

/-- Etingof et al., Example 3.15: the irreducible characters of the quaternion group of order 8 are
the four linear characters and one two-dimensional character. -/
@[kb "etingof2011" "Example 3.15, p. 41"]
theorem etingof_3_15_a :
    irrChars ℂ Q8 = insert q8Psi (Set.range fun p : Bool × Bool => q8Char p.1 p.2) :=
  irrChars_q8

/-- Etingof et al., Example 3.15: the quaternion group of order 8 has a two-dimensional irreducible
complex representation with the character `q8Psi`. -/
@[kb "etingof2011" "Example 3.15, p. 41"]
theorem etingof_3_15_b : ∃ X : IrrRep ℂ Q8, X.ρ.character = q8Psi ∧ Module.finrank ℂ X.V = 2 :=
  exists_irrRep_q8_dim_two

open S4Table in
/-- Etingof et al., Example 3.15: the irreducible complex characters of the symmetric group on four
letters are the trivial, sign, standard, standard times sign and two-dimensional characters. -/
@[kb "etingof2011" "Example 3.15, p. 41"]
theorem etingof_3_15_c :
    irrChars ℂ (Equiv.Perm (Fin 4)) = {s4Triv, s4Sign, s4Std, s4StdSign, s4Two} :=
  irrChars_perm_four

/-- Etingof et al., Example 3.15: the irreducible complex characters of the alternating group on
five letters are the five characters of its character table. -/
@[kb "etingof2011" "Example 3.15, p. 41"]
theorem etingof_3_15_d :
    irrChars ℂ A5Table.A5 = {a5Triv, a5Std, a5Five, a5ThreeP, a5ThreeM} :=
  irrChars_alternatingGroup_five

end UndergradKB.RepresentationTheory.Course
