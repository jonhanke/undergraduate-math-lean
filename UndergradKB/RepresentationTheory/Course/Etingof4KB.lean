import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.WeylShiftIso
import UndergradKB.RepresentationTheory.AlgebraicIntegers
import UndergradKB.RepresentationTheory.Burnside
import UndergradKB.RepresentationTheory.CharactersChapter4
import UndergradKB.RepresentationTheory.CharactersMore
import UndergradKB.RepresentationTheory.FrobeniusDivisibility
import UndergradKB.RepresentationTheory.FrobeniusSchur
import UndergradKB.RepresentationTheory.GroupDeterminant
import UndergradKB.RepresentationTheory.Induced
import UndergradKB.RepresentationTheory.Products
import UndergradKB.RepresentationTheory.RootsOfUnity
import UndergradKB.RepresentationTheory.DoubleCentralizer
import UndergradKB.RepresentationTheory.FrobeniusCounting
import UndergradKB.RepresentationTheory.FrobeniusDeterminant
import UndergradKB.RepresentationTheory.FrobeniusFormula
import UndergradKB.RepresentationTheory.FrobeniusKostka
import UndergradKB.RepresentationTheory.FrobeniusTheorem
import UndergradKB.RepresentationTheory.Artin
import UndergradKB.RepresentationTheory.GL2
import UndergradKB.RepresentationTheory.GL2Classes
import UndergradKB.RepresentationTheory.GL2Cuspidal
import UndergradKB.RepresentationTheory.GL2Cuspidal2
import UndergradKB.RepresentationTheory.GL2PrincipalSeries
import UndergradKB.RepresentationTheory.HookLength
import UndergradKB.RepresentationTheory.LittleGroup
import UndergradKB.RepresentationTheory.LittleGroupExhaust
import UndergradKB.RepresentationTheory.LittleGroupTheorem
import UndergradKB.RepresentationTheory.IsotypicDecomposition
import UndergradKB.RepresentationTheory.KostkaNumbers
import UndergradKB.RepresentationTheory.PowerSumsSchur
import UndergradKB.RepresentationTheory.SchurPolynomials
import UndergradKB.RepresentationTheory.SchurWeyl
import UndergradKB.RepresentationTheory.WeylCharacter
import UndergradKB.RepresentationTheory.WeylCharacterTrace
import UndergradKB.RepresentationTheory.SpechtModules
import UndergradKB.RepresentationTheory.SpechtRational
import UndergradKB.RepresentationTheory.SymmetricGroup
import UndergradKB.RepresentationTheory.SymmetricGroupSpecht
import UndergradKB.RepresentationTheory.VirtualCharacters

/-!
# Etingof et al., Introduction to Representation Theory: Chapter 4, results proved in this repository

Thin theorems in the book's terms for the items of Chapter 4 (more on finite groups) whose proofs
live in other files of this repository (as opposed to `Course/Etingof4.lean`, which collects the
items already in Mathlib).  The file covers Frobenius-Schur indicators, the group determinant,
algebraic integers, Burnside's theorem, products and induced representations, Young symmetrizers
and Specht modules, the Frobenius character formula, the hook length formula, the double
centralizer theorem and Schur-Weyl duality, Schur polynomials and the Weyl character formula,
the representations of `GL₂(𝔽_q)`, Artin's induction theorem, and the little group method.
Each wrapper is tagged with the source key `etingof2011` and the locator of the
item in the book.
-/

namespace UndergradKB.RepresentationTheory.Course

universe u v w

open Representation Module

section Types

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- Etingof et al., Section 4.1: a finite-dimensional representation with an invariant nondegenerate
symmetric form (real type) is not of complex type, that is, it is isomorphic to its dual. -/
@[kb "etingof2011" "§4.1, p. 47"]
theorem etingof_sec_4_1_a [FiniteDimensional k V] {ρ : Representation k G V}
    (h : IsRealType ρ) : ¬ IsComplexType ρ :=
  IsRealType.not_isComplexType h

/-- Etingof et al., Section 4.1: a finite-dimensional representation with an invariant nondegenerate
skew form (quaternionic type) is not of complex type, that is, it is isomorphic to its dual. -/
@[kb "etingof2011" "§4.1, p. 47"]
theorem etingof_sec_4_1_b [FiniteDimensional k V] {ρ : Representation k G V}
    (h : IsQuaternionicType ρ) : ¬ IsComplexType ρ :=
  IsQuaternionicType.not_isComplexType h

end Types

section FrobeniusSchurCount

variable {k : Type u} {G : Type v} [Field k] [Group G] [Fintype G] [IsAlgClosed k]
  [Invertible (Nat.card G : k)]

open scoped Classical in
/-- Etingof et al., Theorem 4.4: the number of group elements whose square is the identity equals
the sum over the irreducible representations of the dimension times the Frobenius-Schur
indicator. -/
@[kb "etingof2011" "Theorem 4.4, p. 47"]
theorem etingof_4_4 :
    ∑ χ : irrChars k G, (χ : G → k) 1 * fsIndicator (χ : G → k) =
      ((Finset.univ.filter fun g : G ↦ g ^ 2 = 1).card : k) :=
  sum_irrChars_one_mul_fsIndicator

open scoped Classical in
/-- Etingof et al., Corollary 4.5: if every irreducible representation has indicator one (all are
real), the sum of their dimensions is the number of elements squaring to the identity. -/
@[kb "etingof2011" "Corollary 4.5, p. 48"]
theorem etingof_4_5 (h : ∀ χ : irrChars k G, fsIndicator (χ : G → k) = 1) :
    ∑ χ : irrChars k G, (χ : G → k) 1 = ((Finset.univ.filter fun g : G ↦ g ^ 2 = 1).card : k) :=
  sum_irrChars_one_of_fsIndicator_eq_one h

end FrobeniusSchurCount

section GroupDeterminantSection

open MvPolynomial

variable {G : Type w} [Group G] [Fintype G]

/-- Etingof et al., Theorem 4.7: for a complete family of pairwise non-isomorphic irreducible
representations, the group determinant is a sign times the product of the polynomials
`det (sum x_g rho_i(g))` raised to the dimensions, these factors are irreducible, and distinct
members are not proportional. -/
@[kb "etingof2011" "Theorem 4.7, p. 48"]
theorem etingof_4_7 [DecidableEq G] {ι : Type*} [Fintype ι] (X : ι → IrrRep ℂ G)
    (hinj : ∀ i j, Nonempty (Representation.Equiv (X i).ρ (X j).ρ) → i = j)
    (hsurj : ∀ Y : IrrRep ℂ G, ∃ i, Nonempty (Representation.Equiv Y.ρ (X i).ρ)) :
    groupDeterminant G ℂ = C (((Equiv.Perm.sign (Equiv.inv G) : ℤˣ) : ℤ) : ℂ) *
        ∏ i, groupPoly (X i).ρ ^ finrank ℂ (X i).V ∧
      (∀ i, Irreducible (groupPoly (X i).ρ)) ∧
      (∀ i j (c : ℂ), groupPoly (X i).ρ = C c * groupPoly (X j).ρ → i = j) :=
  groupDeterminant_factorization X hinj hsurj

end GroupDeterminantSection

section GenericDeterminant

variable {K : Type*} {ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- Etingof et al., Lemma 4.8: the determinant of the generic square matrix, as a polynomial in
its independent entries, is irreducible. -/
@[kb "etingof2011" "Lemma 4.8, p. 48"]
theorem etingof_4_8 [Nonempty ι] : Irreducible (genericDet K ι) :=
  irreducible_genericDet

end GenericDeterminant

section AlgebraicNumbers

/-- Etingof et al., Proposition 4.11 (integer case): a complex number is an algebraic integer
exactly when it is a root of the characteristic polynomial of a square integer matrix. -/
@[kb "etingof2011" "Proposition 4.11, p. 49"]
theorem etingof_4_11_a (z : ℂ) :
    IsIntegral ℤ z ↔ ∃ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ),
      (A.map (Int.castRingHom ℂ)).charpoly.IsRoot z :=
  isIntegral_int_iff_exists_matrix_isRoot_charpoly z

/-- Etingof et al., Proposition 4.11 (rational case): a complex number is algebraic exactly when it
is a root of the characteristic polynomial of a square rational matrix. -/
@[kb "etingof2011" "Proposition 4.11, p. 49"]
theorem etingof_4_11_b (z : ℂ) :
    IsAlgebraic ℚ z ↔ ∃ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ),
      (A.map (algebraMap ℚ ℂ)).charpoly.IsRoot z :=
  isAlgebraic_rat_iff_exists_matrix_isRoot_charpoly z

open Polynomial in
/-- Etingof et al., Lemma 4.14: a root of the minimal polynomial of a sum of algebraic elements is
a sum of roots of the minimal polynomials of the summands. -/
@[kb "etingof2011" "Lemma 4.14, p. 51"]
theorem etingof_4_14_a {F E K ι : Type*} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K]
    [IsAlgClosed K] [Fintype ι] (x : ι → E) (hx : ∀ i, IsAlgebraic F (x i)) {β : K}
    (hβ : aeval β (minpoly F (∑ i, x i)) = 0) :
    ∃ y : ι → K, (∀ i, aeval (y i) (minpoly F (x i)) = 0) ∧ β = ∑ i, y i :=
  exists_conj_sum x hx hβ

/-- Etingof et al., Lemma 4.14: every algebraic conjugate of a sum of algebraic elements is the
sum of conjugates of the summands. -/
@[kb "etingof2011" "Lemma 4.14, p. 51"]
theorem etingof_4_14_b {F A ι : Type*} [Field F] [Field A] [Algebra F A] [IsAlgClosed A]
    [Fintype ι] (x : ι → A) (hx : ∀ i, IsAlgebraic F (x i)) {β : A}
    (hβ : IsConjRoot F (∑ i, x i) β) :
    ∃ y : ι → A, (∀ i, IsConjRoot F (x i) (y i)) ∧ β = ∑ i, y i :=
  exists_isConjRoot_sum x hx hβ

end AlgebraicNumbers

section Divisibility

variable {k G V : Type*} [Field k] [CharZero k] [IsAlgClosed k] [Group G] [Fintype G]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k G V)
  [IsIrreducible ρ]

include ρ in
/-- Etingof et al., Theorem 4.16: the dimension of an irreducible representation of a finite group
over an algebraically closed field of characteristic zero divides the order of the group. -/
@[kb "etingof2011" "Theorem 4.16, p. 51"]
theorem etingof_4_16 : finrank k V ∣ Fintype.card G :=
  finrank_dvd_card ρ

/-- Etingof et al., Proposition 4.17: for an irreducible representation and a group element `h`
with conjugacy class of size `|C|`, the number `|C| chi(h) / dim V` is an algebraic integer. -/
@[kb "etingof2011" "Proposition 4.17, p. 51"]
theorem etingof_4_17 (h : G) :
    IsIntegral ℤ ((conjCard h : k) * ρ.character h / finrank k V) :=
  isIntegral_conjCard_mul_character_div ρ h

end Divisibility

section BurnsideSection

/-- Etingof et al., Theorem 4.20 (Burnside): a finite group of order `p^a q^b` with `p` and `q`
prime is solvable. -/
@[kb "etingof2011" "Theorem 4.20, p. 52"]
theorem etingof_4_20_a {G : Type w} [Group G] [Finite G] {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hG : Nat.card G = p ^ a * q ^ b) : Group.IsSolvable G :=
  isSolvable_of_card_eq_prime_pow_mul_prime_pow hp hq hG

/-- Etingof et al., Theorem 4.20 (Burnside), in the form used for the induction: a finite group
all of whose prime divisors lie in `{p, q}` is solvable. -/
@[kb "etingof2011" "Theorem 4.20, p. 52"]
theorem etingof_4_20_b {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    ∀ (n : ℕ) (G : Type w) [Group G] [Finite G], Nat.card G = n →
      (∀ r : ℕ, r.Prime → r ∣ Nat.card G → r = p ∨ r = q) → Group.IsSolvable G :=
  isSolvable_of_forall_prime_dvd hp hq

/-- Etingof et al., Section 4.5 (Burnside's theorem): a finite group of order `p^a q^b` with `p`
and `q` prime is solvable. -/
@[kb "etingof2011" "§4.5 Burnside's theorem, p. 54"]
theorem etingof_sec_4_5 {G : Type w} [Group G] [Finite G] {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hG : Nat.card G = p ^ a * q ^ b) : Group.IsSolvable G :=
  isSolvable_of_card_eq_prime_pow_mul_prime_pow hp hq hG

end BurnsideSection

section BurnsideLemmas

variable {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  (ρ : Representation ℂ G V) [IsIrreducible ρ]

/-- Etingof et al., Theorem 4.21: for an irreducible complex representation and an element whose
conjugacy class has size prime to the dimension, either the character vanishes at the element or
the element acts as a scalar. -/
@[kb "etingof2011" "Theorem 4.21, p. 52"]
theorem etingof_4_21 (g : G) (hcop : Nat.Coprime (conjCard g) (finrank ℂ V)) :
    ρ.character g = 0 ∨ ∃ c : ℂ, ρ g = c • LinearMap.id :=
  character_eq_zero_or_eq_smul ρ g hcop

/-- Etingof et al., Lemma 4.22: if complex roots of unity have an algebraic integer as their
average, then they are all equal or their sum vanishes. -/
@[kb "etingof2011" "Lemma 4.22, p. 53"]
theorem etingof_4_22 {ι : Type*} [Fintype ι] [Nonempty ι] (ε : ι → ℂ) (m : ℕ)
    (hm : 0 < m) (hε : ∀ i, ε i ^ m = 1) (hint : IsIntegral ℤ ((∑ i, ε i) / Fintype.card ι)) :
    (∀ i j, ε i = ε j) ∨ ∑ i, ε i = 0 :=
  eq_or_sum_eq_zero_of_isIntegral_average ε m hm hε hint

end BurnsideLemmas

section ClassSize

variable {G : Type w} [Group G] [Fintype G]

/-- Etingof et al., Theorem 4.23: a conjugacy class of prime power size `p^k` with `k > 0` forces
a normal subgroup other than the trivial one and the whole group. -/
@[kb "etingof2011" "Theorem 4.23, p. 53"]
theorem etingof_4_23 {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (g : G)
    (hg : conjCard g = p ^ k) : ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ :=
  exists_normal_of_conjCard_eq_prime_pow hp hk g hg

/-- Etingof et al., Lemma 4.24: if the class of `g` has `p^k` elements with `k > 0`, some nontrivial
irreducible complex representation has dimension prime to `p` and character nonzero at `g`. -/
@[kb "etingof2011" "Lemma 4.24, p. 53"]
theorem etingof_4_24 {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (g : G)
    (hg : conjCard g = p ^ k) :
    ∃ X : IrrRep ℂ G, X.ρ.character ≠ 1 ∧ ¬ p ∣ finrank ℂ X.V ∧ X.ρ.character g ≠ 0 :=
  exists_irrRep_of_conjCard_eq_prime_pow hp hk g hg

end ClassSize

section ProductsSection

section External

variable {k G H V W : Type*} [Field k] [Group G] [Group H] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- Etingof et al., Theorem 4.25 (character part): the character of the external tensor product
of two representations is the product of their characters. -/
@[kb "etingof2011" "Theorem 4.25, p. 54"]
theorem etingof_4_25_a [FiniteDimensional k V] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k H W) (p : G × H) :
    (extTprod ρ σ).character p = ρ.character p.1 * σ.character p.2 :=
  extTprod_character ρ σ p

/-- Etingof et al., Theorem 4.25 (irreducibility part): the external tensor product of
finite-dimensional irreducible representations over an algebraically closed field is
irreducible. -/
@[kb "etingof2011" "Theorem 4.25, p. 54"]
theorem etingof_4_25_b [IsAlgClosed k] [FiniteDimensional k V] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k H W) [IsIrreducible ρ] [IsIrreducible σ] :
    IsIrreducible (extTprod ρ σ) :=
  isIrreducible_extTprod ρ σ

end External

section Classification

variable {k : Type u} {G H : Type v} [Field k] [Group G] [Group H] [Fintype G] [Fintype H]
  [IsAlgClosed k] [Invertible (Nat.card G : k)] [Invertible (Nat.card H : k)]

/-- Etingof et al., Theorem 4.25 (exhaustion): every irreducible representation of `G × H` is
isomorphic to an external tensor product of irreducible representations of `G` and `H`. -/
@[kb "etingof2011" "Theorem 4.25, p. 54"]
theorem etingof_4_25_c (Z : IrrRep k (G × H)) :
    ∃ (X : IrrRep k G) (Y : IrrRep k H),
      Nonempty (Representation.Equiv Z.ρ (X.extTprod Y).ρ) :=
  exists_equiv_extTprod Z

end Classification

end ProductsSection

section VirtualCharacterSection

variable {k : Type u} {G : Type v} [Field k] [Group G] [Fintype G] [IsAlgClosed k]
  [Invertible (Nat.card G : k)]

open scoped ComplexOrder in
/-- Etingof et al., Lemma 4.27: over the complex numbers, a virtual character of norm one whose
value at the identity is positive is the character of an irreducible representation. -/
@[kb "etingof2011" "Lemma 4.27, p. 54"]
theorem etingof_4_27_a {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {ζ : G → ℂ} (hζ : ζ ∈ virtualChars ℂ G) (h1 : pairing ζ ζ = 1) (hpos : 0 < ζ 1) :
    ζ ∈ irrChars ℂ G :=
  mem_irrChars_of_pairing_eq_one hζ h1 hpos

/-- Etingof et al., Lemma 4.27 (sign form, characteristic zero): a virtual character of norm one
is an irreducible character or the negative of one. -/
@[kb "etingof2011" "Lemma 4.27, p. 54"]
theorem etingof_4_27_b [CharZero k] {ζ : G → k} (hζ : ζ ∈ virtualChars k G)
    (h1 : pairing ζ ζ = 1) : ζ ∈ irrChars k G ∨ -ζ ∈ irrChars k G :=
  mem_irrChars_or_neg_of_pairing_eq_one hζ h1

end VirtualCharacterSection

section InducedSection

variable {k : Type u} {G : Type v} {V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  (H : Subgroup G) (ρ : Representation k H V)

/-- Etingof et al., Remark 4.30: the induced representation of a finite-dimensional representation
of a subgroup `H` of a finite group has dimension `dim V` times the index of `H`. -/
@[kb "etingof2011" "Remark 4.30, p. 55"]
theorem etingof_4_30 [Finite G] [Module.Finite k V] :
    finrank k (coindV H.subtype ρ) = finrank k V * H.index :=
  finrank_Ind H ρ

/-- Etingof et al., Theorem 4.32: the character of the induced representation at `g` is the sum,
over representatives `x` of the right cosets, of the extension by zero of the character of `V`
evaluated at `x g x⁻¹`. -/
@[kb "etingof2011" "Theorem 4.32, p. 55"]
theorem etingof_4_32_a [Fintype (RCosets H)] [Module.Finite k V] (g : G) :
    (Ind H ρ).character g = ∑ c : RCosets H, charExt H ρ (rep H c * g * (rep H c)⁻¹) :=
  character_Ind H ρ g

/-- Etingof et al., Theorem 4.32 (averaged form): when the order of `H` is invertible, the induced
character at `g` is the average, over all `x` in `G`, of the extended character at `x g x⁻¹`. -/
@[kb "etingof2011" "Theorem 4.32, p. 55"]
theorem etingof_4_32_b [Fintype (RCosets H)] [Module.Finite k V] [Fintype G]
    [Invertible (Nat.card H : k)] (g : G) :
    (Ind H ρ).character g = ⅟(Nat.card H : k) * ∑ x : G, charExt H ρ (x * g * x⁻¹) :=
  character_Ind_averaged H ρ g

end InducedSection

section YoungSymmetrizers

variable {mu : YoungDiagram}

/-- Etingof et al., Section 4.12 (within Definition 4.35): the row subgroup and the column subgroup
of a Young tableau meet trivially, which makes the Young symmetrizer nonzero. -/
@[kb "etingof2011" "§4.12 (within Definition 4.35), p. 58"]
theorem etingof_sec_4_12_a (T : YoungTableau mu) : rowSubgroup T ⊓ colSubgroup T = ⊥ :=
  rowSubgroup_inf_colSubgroup T

/-- Etingof et al., Section 4.12 (within Definition 4.35): the row sum `a_T` satisfies
`a_T * a_T = |P_T| a_T`. -/
@[kb "etingof2011" "§4.12 (within Definition 4.35), p. 58"]
theorem etingof_sec_4_12_b (T : YoungTableau mu) :
    rowSum T * rowSum T = (Nat.card (rowSubgroup T) : ℂ) • rowSum T :=
  rowSum_mul_self T

/-- Etingof et al., Section 4.12 (within Definition 4.35): the signed column sum `b_T` satisfies
`b_T * b_T = |Q_T| b_T`. -/
@[kb "etingof2011" "§4.12 (within Definition 4.35), p. 58"]
theorem etingof_sec_4_12_c (T : YoungTableau mu) :
    colSum T * colSum T = (Nat.card (colSubgroup T) : ℂ) • colSum T :=
  colSum_mul_self T

/-- Etingof et al., Lemma 4.40 (scalar form): for every element `x` of the group algebra of the
symmetric group, `a_T x b_T` is a scalar multiple of the Young symmetrizer, the scalar being a
linear functional of `x`. -/
@[kb "etingof2011" "Lemma 4.40, p. 59"]
theorem etingof_4_40_a (T : YoungTableau mu) :
    ∃ ℓ : MonoidAlgebra ℂ (Equiv.Perm (Fin mu.card)) →ₗ[ℂ] ℂ,
      ∀ x, rowSum T * x * colSum T = ℓ x • youngSymmetrizer T :=
  rowSum_mul_mul_colSum T

/-- Etingof et al., Lemma 4.40 (combinatorial core): if no two numbers in one row of `T` lie in
one column of the rearranged filling, the permutation factors as a row permutation times a column
permutation. -/
@[kb "etingof2011" "Lemma 4.40, p. 59"]
theorem etingof_4_40_b (T : YoungTableau mu) (g : Equiv.Perm (Fin mu.card))
    (hnc : ∀ a b, a ≠ b → T.rowOf a = T.rowOf b → T.colOf (g⁻¹ a) ≠ T.colOf (g⁻¹ b)) :
    ∃ p ∈ rowSubgroup T, ∃ q ∈ colSubgroup T, g = p * q :=
  exists_mem_rowSubgroup_mul_colSubgroup T g hnc

/-- Etingof et al., Lemma 4.41: if `la` is lexicographically larger than `mu`, then
`a_la x b_mu = 0` for every element `x` of the group algebra. -/
@[kb "etingof2011" "Lemma 4.41, p. 59"]
theorem etingof_4_41 {la mu : YoungDiagram} {n : ℕ} (Tl : la ≃ Fin n)
    (Tm : mu ≃ Fin n)
    (hlex : ∃ k, (∀ i < k, la.rowLen i = mu.rowLen i) ∧ mu.rowLen k < la.rowLen k)
    (x : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) : rowSumN Tl * x * colSumN Tm = 0 :=
  rowSumN_mul_mul_colSumN_of_lex Tl Tm hlex x

/-- Etingof et al., Lemma 4.42: the square of the Young symmetrizer is `n! / dim V` times itself,
where `V` is the left ideal it generates (whose dimension is nonzero). -/
@[kb "etingof2011" "Lemma 4.42, p. 60"]
theorem etingof_4_42 (T : YoungTableau mu) :
    Module.finrank ℂ ((Ideal.span {youngSymmetrizer T}).restrictScalars ℂ) ≠ 0 ∧
      youngSymmetrizer T * youngSymmetrizer T =
        ((mu.card.factorial : ℂ) /
          (Module.finrank ℂ ((Ideal.span {youngSymmetrizer T}).restrictScalars ℂ) : ℂ)) •
          youngSymmetrizer T :=
  youngSymmetrizer_mul_self T

end YoungSymmetrizers

section SpechtClassification

/-- Etingof et al., Theorem 4.36 (irreducibility): the left ideal generated by a Young symmetrizer
is a simple module over the group algebra of the symmetric group. -/
@[kb "etingof2011" "Theorem 4.36, p. 58"]
theorem etingof_4_36_a {mu : YoungDiagram} (T : YoungTableau mu) :
    IsSimpleModule (MonoidAlgebra ℂ (Equiv.Perm (Fin mu.card)))
      (Ideal.span {youngSymmetrizer T}) :=
  isSimpleModule_span_youngSymmetrizer T

/-- Etingof et al., Theorem 4.36 (non-isomorphism): the ideals attached to two different Young
diagrams with `n` boxes are not isomorphic as modules. -/
@[kb "etingof2011" "Theorem 4.36, p. 58"]
theorem etingof_4_36_b {la mu : YoungDiagram} {n : ℕ} (Tl : la ≃ Fin n)
    (Tm : mu ≃ Fin n) (h : la ≠ mu) :
    IsEmpty (Ideal.span {youngSymmetrizerN Tl} ≃ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin n))]
      Ideal.span {youngSymmetrizerN Tm}) :=
  isEmpty_linearEquiv_span_youngSymmetrizerN Tl Tm h

/-- Etingof et al., Theorem 4.36 (exhaustion): every irreducible representation of the symmetric
group over the complex numbers is isomorphic to a Specht module for some partition. -/
@[kb "etingof2011" "Theorem 4.36, p. 58"]
theorem etingof_4_36_c (n : ℕ) (Y : IrrRep ℂ (Equiv.Perm (Fin n))) :
    ∃ la : DiagramsOfSize n, Nonempty (Representation.Equiv Y.ρ
      (Representation.ofModule (k := ℂ) (G := Equiv.Perm (Fin n)) (spechtModule la))) :=
  exists_equiv_spechtModule n Y

/-- Etingof et al., Theorem 4.36 (bijection): the map from partitions of `n` to irreducible
characters of the symmetric group given by Specht modules is bijective. -/
@[kb "etingof2011" "Theorem 4.36, p. 58"]
theorem etingof_4_36_d (n : ℕ) : Function.Bijective (spechtChar n) :=
  spechtChar_bijective n

/-- Etingof et al., Theorem 4.36 (count form): the symmetric group on `n` letters has as many
irreducible characters as there are partitions of `n`. -/
@[kb "etingof2011" "Theorem 4.36, p. 58"]
theorem etingof_4_36_e (n : ℕ) :
    Nat.card (irrChars ℂ (Equiv.Perm (Fin n))) = Nat.card (Nat.Partition n) :=
  card_irrChars_perm_eq_card_partition n

/-- Etingof et al., Corollary 4.38 (rationality): every irreducible complex representation of the
symmetric group has a basis in which all permutations act by rational matrices. -/
@[kb "etingof2011" "Corollary 4.38, p. 59"]
theorem etingof_4_38_a (n : ℕ) (Y : IrrRep ℂ (Equiv.Perm (Fin n))) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b : Module.Basis ι ℂ Y.V)
      (M : Equiv.Perm (Fin n) → Matrix ι ι ℚ),
      ∀ g, LinearMap.toMatrix b b (Y.ρ g) = (M g).map (algebraMap ℚ ℂ) :=
  exists_rational_basis_irrep n Y

/-- Etingof et al., Corollary 4.38 (rational ideals): for a rational element `c` of a finite
group algebra, the left ideal of the complex group algebra generated by it has a basis in which
every group element acts by a rational matrix. -/
@[kb "etingof2011" "Corollary 4.38, p. 59"]
theorem etingof_4_38_b {G : Type} [Group G] [Fintype G] [DecidableEq G] (cQ : MonoidAlgebra ℚ G) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (B : Module.Basis ι ℂ (RestrictScalars ℂ (MonoidAlgebra ℂ G)
        (Ideal.span {ratToComplex G cQ}))) (M : G → Matrix ι ι ℚ),
      ∀ g, LinearMap.toMatrix B B (Representation.ofModule (k := ℂ) (G := G)
        (Ideal.span {ratToComplex G cQ}) g) = (M g).map (algebraMap ℚ ℂ) :=
  exists_rational_basis_ideal cQ

end SpechtClassification

section KostkaSection

variable {la mu : YoungDiagram} {n : ℕ}

/-- Etingof et al., Proposition 4.44 (vanishing, lexicographic form): if `mu` is lexicographically
smaller than `la`, there are no nonzero module maps from `U_la` to `V_mu`. -/
@[kb "etingof2011" "Proposition 4.44, p. 60"]
theorem etingof_4_44_a (Tl : la ≃ Fin n) (Tm : mu ≃ Fin n)
    (hlex : ∃ k, (∀ i < k, la.rowLen i = mu.rowLen i) ∧ mu.rowLen k < la.rowLen k) :
    Subsingleton (permIdeal Tl →ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin n))]
      Ideal.span {youngSymmetrizerN Tm}) :=
  subsingleton_hom_of_lex Tl Tm hlex

/-- Etingof et al., Proposition 4.44 (vanishing, dominance form): there are no nonzero module maps
from `U_la` to `V_mu` unless `la` is dominated by `mu`. -/
@[kb "etingof2011" "Proposition 4.44, p. 60"]
theorem etingof_4_44_b (Tl : la ≃ Fin n) (Tm : mu ≃ Fin n)
    (hd : ¬ RowDominance la mu) :
    Subsingleton (permIdeal Tl →ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin n))]
      Ideal.span {youngSymmetrizerN Tm}) :=
  subsingleton_hom_of_not_rowDominance Tl Tm hd

/-- Etingof et al., Proposition 4.44 (dimension part): the space of module maps from `U_la` to
`V_la` is one dimensional. -/
@[kb "etingof2011" "Proposition 4.44, p. 60"]
theorem etingof_4_44_c (T : la ≃ Fin n) :
    Module.finrank ℂ (permIdeal T →ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin n))]
      Ideal.span {youngSymmetrizerN T}) = 1 :=
  finrank_hom_self T

/-- Etingof et al., Section 4.15 Remark: the Kostka number `K_{mu la}` vanishes unless `la` is
dominated by `mu`. -/
@[kb "etingof2011" "§4.15 Remark, p. 63"]
theorem etingof_sec_4_15_a {n : ℕ} (mu la : DiagramsOfSize n)
    (h : ¬ RowDominance la.1 mu.1) : kostka mu la = 0 :=
  kostka_eq_zero_of_not_rowDominance mu la h

/-- Etingof et al., Section 4.15 Remark: the Kostka number `K_{mu la}` vanishes when `mu` is
lexicographically smaller than `la`. -/
@[kb "etingof2011" "§4.15 Remark, p. 63"]
theorem etingof_sec_4_15_b {n : ℕ} (mu la : DiagramsOfSize n)
    (hlex : ∃ k, (∀ i < k, la.1.rowLen i = mu.1.rowLen i) ∧ mu.1.rowLen k < la.1.rowLen k) :
    kostka mu la = 0 :=
  kostka_eq_zero_of_lex mu la hlex

/-- Etingof et al., Section 4.15 Remark: the diagonal Kostka number `K_{la la}` equals one. -/
@[kb "etingof2011" "§4.15 Remark, p. 63"]
theorem etingof_sec_4_15_c {n : ℕ} (la : DiagramsOfSize n) : kostka la la = 1 :=
  kostka_self la

end KostkaSection

section PermutationCharacters

open scoped Classical

/-- Etingof et al., Theorem 4.46: the trace of a group element on the permutation module
`C[G] a_H` is the number of fixed points of the element on `G / H`. -/
@[kb "etingof2011" "Theorem 4.46, p. 60"]
theorem etingof_4_46_a {G : Type*} [Group G] [Fintype G] (H : Subgroup G) (g : G) :
    LinearMap.trace ℂ (permSubspace H) (permAction H g) =
      (Nat.card (MulAction.fixedBy (G ⧸ H) g) : ℂ) :=
  trace_permAction H g

/-- Etingof et al., Theorem 4.46 (fixed-point form): the character of `U_la` at a permutation
is the number of cosets of the row stabiliser that it fixes. -/
@[kb "etingof2011" "Theorem 4.46, p. 60"]
theorem etingof_4_46_b {la : YoungDiagram} {n : ℕ} (T : la ≃ Fin n) (g : Equiv.Perm (Fin n)) :
    LinearMap.trace ℂ (permSubspace (rowStab T)) (permAction (rowStab T) g) =
      (Nat.card (MulAction.fixedBy (Equiv.Perm (Fin n) ⧸ rowStab T) g) : ℂ) :=
  character_permIdeal_eq_card_fixedBy T g

/-- Etingof et al., Theorem 4.46: the character of `U_la` at a permutation with `i_m` cycles of
length `m` is the coefficient of `x^la` in the product over `m` of the `m`-th power sums raised to
the power `i_m`. -/
@[kb "etingof2011" "Theorem 4.46, p. 60"]
theorem etingof_4_46_c {la : YoungDiagram} {n : ℕ} (T : la ≃ Fin n) {N : ℕ}
    (hN : la.colLen 0 ≤ N) (g : Equiv.Perm (Fin n)) :
    LinearMap.trace ℂ (permSubspace (rowStab T)) (permAction (rowStab T) g) =
      (∏ m ∈ Finset.Icc 1 n, MvPolynomial.psum (Fin N) ℂ m ^ cycleCount g m).coeff
        (Finsupp.equivFunOnFinite.symm fun j : Fin N => la.rowLen j) :=
  character_permIdeal_eq_coeff T hN g

end PermutationCharacters

section FrobeniusFormulaSection

open FrobeniusDet

/-- Etingof et al., Theorem 4.47 (Frobenius character formula): the character of the Specht module
of a diagram with at most `N` rows is the class function whose value is the coefficient of
`x^(la + rho)` in the Vandermonde product times the product of power sums. -/
@[kb "etingof2011" "Theorem 4.47, p. 61"]
theorem etingof_4_47_a {n N : ℕ} (la : DiagramsOfSize n) (hN : la.1.colLen 0 ≤ N) :
    ((spechtChar n la : irrChars ℂ (Equiv.Perm (Fin n))) : Equiv.Perm (Fin n) → ℂ) =
      frobChar n N (fun j => la.1.rowLen j) :=
  frobenius_character_formula la hN

/-- Etingof et al., Theorem 4.47 (orthonormality): for nonincreasing exponent vectors with sum `n`,
the class functions `theta_la` are orthonormal. -/
@[kb "etingof2011" "Theorem 4.47, p. 61"]
theorem etingof_4_47_b {n N : ℕ} {lam mu : Fin N → ℕ} (hl : Antitone lam) (hm : Antitone mu)
    (hsl : ∑ i, lam i = n) (hsm : ∑ i, mu i = n) :
    pairing (frobChar n N lam) (frobChar n N mu) = if lam = mu then 1 else 0 :=
  pairing_frobChar hl hm hsl hsm

/-- Etingof et al., Theorem 4.47 (a step of the proof): the class function `theta_la` is an
integer combination of permutation characters, that is, a virtual character. -/
@[kb "etingof2011" "Theorem 4.47, p. 61"]
theorem etingof_4_47_c {n N : ℕ} (lam : Fin N → ℕ) :
    frobChar n N lam ∈ virtualChars ℂ (Equiv.Perm (Fin n)) :=
  frobChar_mem_virtualChars lam

/-- Etingof et al., Theorem 4.47 (a step of the proof): the signed count of contingency tables
with prescribed row and column sums equals a signed count of permutations. -/
@[kb "etingof2011" "Theorem 4.47, p. 61"]
theorem etingof_4_47_d {N : ℕ} (a b : Fin N → ℕ) :
    ∑ σ : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
        ((Equiv.Perm.sign σ * Equiv.Perm.sign τ : ℤ) : ℂ) *
        (if (∀ i, rhoExp N (σ.symm i) ≤ a i) ∧ (∀ i, rhoExp N (τ.symm i) ≤ b i) then
          (contingency (fun i => a i - rhoExp N (σ.symm i))
            (fun i => b i - rhoExp N (τ.symm i)) : ℂ)
        else 0) =
      ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        (if b = a ∘ σ.symm then 1 else 0) :=
  signed_sum_contingency a b

/-- Etingof et al., Theorem 4.47 (a step of the proof): the polynomial Cauchy identity with
denominators cleared. -/
@[kb "etingof2011" "Theorem 4.47, p. 61"]
theorem etingof_4_47_e {N : ℕ} :
    ∑ σ : Equiv.Perm (Fin N), Equiv.Perm.sign σ •
        ∏ j, ∏ k ∈ Finset.univ.erase (σ j), (1 - xv j * yv k) =
      ∏ i, ∏ j ∈ Finset.Ioi i, ((xv i - xv j) * (yv i - yv j)) :=
  cauchy_poly

open scoped Classical in
/-- Etingof et al., Theorem 4.47 (a step of the proof): an orthogonality count of the coefficients
of the cycle polynomials in terms of contingency tables. -/
@[kb "etingof2011" "Theorem 4.47, p. 61"]
theorem etingof_4_47_f (n N : ℕ) (α β : Fin N → ℕ) (hα : ∑ i, α i = n) (hβ : ∑ i, β i = n) :
    ∑ g : Equiv.Perm (Fin n), (cyclePoly n N g).coeff (Finsupp.equivFunOnFinite.symm α) *
        (cyclePoly n N g).coeff (Finsupp.equivFunOnFinite.symm β) =
      (n.factorial : ℂ) * contingency α β :=
  sum_coeff_cyclePoly_mul n N α β hα hβ

/-- Etingof et al., Theorem 4.47 (a step of the proof): the pairing of the permutation character
given by the coefficient of `x^mu` with the Specht character of `la` is the Kostka number. -/
@[kb "etingof2011" "Theorem 4.47, p. 61"]
theorem etingof_4_47_g (n N : ℕ) (mu la : DiagramsOfSize n) (hN : mu.1.colLen 0 ≤ N) :
    pairing (fun g : Equiv.Perm (Fin n) =>
        (cyclePoly n N g).coeff (Finsupp.equivFunOnFinite.symm fun j : Fin N => mu.1.rowLen j))
      ((spechtChar n la : irrChars ℂ (Equiv.Perm (Fin n))) : Equiv.Perm (Fin n) → ℂ) =
        (kostka la mu : ℂ) :=
  pairing_coeffChar_spechtChar n N mu la hN

end FrobeniusFormulaSection

section CauchySection

open Matrix Finset Fin

variable {K : Type*} [Field K]

/-- Etingof et al., Lemma 4.48 (Cauchy determinant): the determinant of the matrix with entries
`1 / (z_i - y_j)` is a product of differences divided by the product of all `z_i - y_j`. -/
@[kb "etingof2011" "Lemma 4.48, p. 62"]
theorem etingof_4_48 {n : ℕ} (z y : Fin n → K) (h : ∀ i j, z i - y j ≠ 0) :
    det (of fun i j => 1 / (z i - y j)) =
      (∏ i, ∏ j ∈ Ioi i, ((z j - z i) * (y i - y j))) / ∏ i, ∏ j, (z i - y j) :=
  cauchy_det z y h

/-- Etingof et al., Corollary 4.49 (Cauchy identity): the determinant of the matrix with entries
`1 / (1 - x_i y_j)` equals the product ratio. -/
@[kb "etingof2011" "Corollary 4.49, p. 62"]
theorem etingof_4_49_a {n : ℕ} (x y : Fin n → K) (hx : ∀ i, x i ≠ 0)
    (h : ∀ i j, 1 - x i * y j ≠ 0) :
    det (of fun i j => 1 / (1 - x i * y j)) =
      (∏ i, ∏ j ∈ Ioi i, ((x i - x j) * (y i - y j))) / ∏ i, ∏ j, (1 - x i * y j) :=
  cauchy_identity x y hx h

/-- Etingof et al., Corollary 4.49 (Cauchy identity): the same product ratio written as a signed
sum over permutations of `1 / prod (1 - x_j y_sigma(j))`. -/
@[kb "etingof2011" "Corollary 4.49, p. 62"]
theorem etingof_4_49_b {n : ℕ} (x y : Fin n → K) (hx : ∀ i, x i ≠ 0)
    (h : ∀ i j, 1 - x i * y j ≠ 0) :
    ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ j, 1 / (1 - x j * y (σ j)) =
      (∏ i, ∏ j ∈ Ioi i, ((x i - x j) * (y i - y j))) / ∏ i, ∏ j, (1 - x i * y j) :=
  cauchy_identity_sum x y hx h

end CauchySection

/-- Etingof et al., Theorem 4.53 (hook length formula): the dimension of the irreducible
representation attached to a diagram, times the product of the hook lengths of its boxes, is
`n!`. -/
@[kb "etingof2011" "Theorem 4.53, p. 64"]
theorem etingof_4_53 {n : ℕ} (la : DiagramsOfSize n) :
    (Module.finrank ℂ (spechtIrrRep n la).V : ℂ) *
      ∏ c ∈ la.1.cells, (hookLength la.1 c : ℂ) = n.factorial :=
  finrank_specht_mul_prod_hook la

section DoubleCentralizerSection

section Centralizer

variable {k : Type*} [Field k] {E : Type*} [AddCommGroup E] [Module k E]
  [FiniteDimensional k E] (A : Subalgebra k (Module.End k E))

/-- Etingof et al., Theorem 4.54 (first part): for a semisimple subalgebra `A` of `End E`, the
centralizer of the centralizer of `A` is `A`. -/
@[kb "etingof2011" "Theorem 4.54, p. 64"]
theorem etingof_4_54_a [IsSemisimpleRing A] :
    Subalgebra.centralizer k (commutant A : Set (Module.End k E)) = A :=
  centralizer_centralizer_eq A

/-- Etingof et al., Theorem 4.54 (second part): the centralizer of a semisimple subalgebra of
`End E` is semisimple. -/
@[kb "etingof2011" "Theorem 4.54, p. 64"]
theorem etingof_4_54_b [IsSemisimpleRing A] : IsSemisimpleRing (commutant A) :=
  isSemisimpleRing_commutant A

end Centralizer

section Decomposition

variable {k : Type*} [Field k] {E : Type*} [AddCommGroup E] [Module k E]
  (A : Subalgebra k (Module.End k E))

/-- Etingof et al., Theorem 4.54 (simplicity part): for a semisimple subalgebra `A` of `End E` with
centralizer `B`, and a simple `A`-module `X` occurring in `E`, the space `Hom_A(X, E)` is a simple
`B`-module. -/
@[kb "etingof2011" "Theorem 4.54, p. 64"]
theorem etingof_4_54_c [IsSemisimpleModule A E] (X : Type*) [AddCommGroup X] [Module A X]
    [IsSimpleModule A X] [Nontrivial (X →ₗ[A] E)] :
    @IsSimpleModule (commutant A) _ (X →ₗ[A] E) _ (homCommutantModule A X) :=
  isSimpleModule_homCommutant A X

/-- Etingof et al., Theorem 4.54 (compatibility part): the decomposition of `E` into the spaces
`X_i ⊗ Hom_A(X_i, E)` is compatible with the centralizer, which acts on the second factor by
post-composition. -/
@[kb "etingof2011" "Theorem 4.54, p. 64"]
theorem etingof_4_54_d {ι : Type*} [Fintype ι] [DecidableEq ι] (X : ι → Type*)
    [∀ i, AddCommGroup (X i)] [∀ i, Module k (X i)] [∀ i, Module A (X i)]
    [∀ i, IsScalarTower k A (X i)]
    (b : commutant A) (i : ι) (x : X i) (f : X i →ₗ[A] E) :
    b.1 (isotypicEval k X (Pi.single i (x ⊗ₜ[k] f))) =
      isotypicEval k X (Pi.single i (x ⊗ₜ[k] (commutantComp A b f))) :=
  commutant_isotypicEval_single A X b i x f

end Decomposition

end DoubleCentralizerSection

section SchurWeylSection

open PiTensorProduct
open scoped TensorProduct

section Centralizers

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  {n : ℕ}

/-- Etingof et al., Theorem 4.55 (span form): in characteristic zero, the centralizer of the
symmetric group in `End (V^(tensor n))` is spanned by the operators `g tensor ... tensor g`. -/
@[kb "etingof2011" "Theorem 4.55, p. 64"]
theorem etingof_4_55_a [CharZero k] :
    (Subalgebra.centralizer k (Set.range (tensorPowerPermRep k n V))).toSubmodule
      = Submodule.span k (Set.range fun g : V →ₗ[k] V => tensorPowerMap n g) :=
  centralizer_perm_eq_span_tensorPowerMap

/-- Etingof et al., Theorem 4.55: in characteristic zero, the centralizer of the symmetric group
in `End (V^(tensor n))` is the subalgebra generated by the diagonal operators `Delta_n(b)`, that is,
the image of the universal enveloping algebra of `gl(V)`. -/
@[kb "etingof2011" "Theorem 4.55, p. 64"]
theorem etingof_4_55_b [CharZero k] :
    Subalgebra.centralizer k (Set.range (tensorPowerPermRep k n V))
      = Algebra.adjoin k (Set.range (diagAction (k := k) (V := V) n)) :=
  centralizer_perm_eq_adjoin_diagAction

/-- Etingof et al., Theorem 4.55 (a step of the proof): every endomorphism of `V^(tensor n)` is a
linear combination of tensor products of endomorphisms of `V`. -/
@[kb "etingof2011" "Theorem 4.55, p. 64"]
theorem etingof_4_55_c :
    Function.Surjective (piTensorHomMap : (⨂[k] _ : Fin n, V →ₗ[k] V) →ₗ[k] _) :=
  piTensorHomMap_surjective

/-- Etingof et al., Proposition 4.58: in characteristic zero, the operators `g tensor ... tensor g`
with `g` invertible span the centralizer of the symmetric group in `End (V^(tensor n))`. -/
@[kb "etingof2011" "Proposition 4.58, p. 65"]
theorem etingof_4_58 [CharZero k] :
    Submodule.span k (Set.range fun u : (V →ₗ[k] V)ˣ => tensorPowerMap n (u : V →ₗ[k] V))
      = (Subalgebra.centralizer k (Set.range (tensorPowerPermRep k n V))).toSubmodule :=
  span_tensorPowerMap_units_eq_centralizer

end Centralizers

/-- Etingof et al., Lemma 4.56 (first part): in characteristic zero, the symmetric tensors in
`U^(tensor n)` are spanned by the pure powers `u tensor ... tensor u`. -/
@[kb "etingof2011" "Lemma 4.56, p. 65"]
theorem etingof_4_56_a {k : Type*} [Field k] [CharZero k] {n : ℕ} {U : Type*} [AddCommGroup U]
    [Module k U] :
    symmetricTensors k n U = Submodule.span k (purePowers k n U) :=
  symmetricTensors_eq_span_purePowers

/-- Etingof et al., Lemma 4.56 (second part): in characteristic zero, the centralizer of the
symmetric group acting on `V^(tensor n)` is generated by the diagonal operators `Delta_n(a)`. -/
@[kb "etingof2011" "Lemma 4.56, p. 65"]
theorem etingof_4_56_b {k : Type*} [Field k] [CharZero k] {V : Type*} [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] {n : ℕ} :
    Subalgebra.centralizer k (Set.range (tensorPowerPermRep k n V))
      = Algebra.adjoin k (Set.range (diagAction (k := k) (V := V) n)) :=
  centralizer_perm_eq_adjoin_diagAction

section Duality

variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ)

/-- Etingof et al., Theorem 4.57 (Schur-Weyl duality): the images of the group algebra of the
symmetric group and of the enveloping algebra of `gl(V)` in `End (V^(tensor n))` are each other's
centralizers, and both are semisimple. -/
@[kb "etingof2011" "Theorem 4.57, p. 65"]
theorem etingof_4_57 :
    Subalgebra.centralizer ℂ (swImage V n : Set (Module.End ℂ (⨂[ℂ] _ : Fin n, V)))
        = Algebra.adjoin ℂ (Set.range (diagAction (k := ℂ) (V := V) n)) ∧
      Subalgebra.centralizer ℂ
        (Algebra.adjoin ℂ (Set.range (diagAction (k := ℂ) (V := V) n)) :
          Set (Module.End ℂ (⨂[ℂ] _ : Fin n, V))) = swImage V n ∧
      IsSemisimpleRing (swImage V n) ∧
      IsSemisimpleRing (Algebra.adjoin ℂ (Set.range (diagAction (k := ℂ) (V := V) n))) :=
  schurWeyl_duality n

/-- Etingof et al., Corollary 4.59 (equivariance): the Schur-Weyl decomposition intertwines
`g tensor ... tensor g` on `V^(tensor n)` with the action of `g` by post-composition on the
multiplicity spaces. -/
@[kb "etingof2011" "Corollary 4.59, p. 65"]
theorem etingof_4_59_a (g : V →ₗ[ℂ] V)
    (z : Π la : DiagramsOfSize n, spechtModule la ⊗[ℂ]
      (spechtModule la →ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin n))] tensorPowerModule V n)) :
    tensorPowerEnd n g (schurWeylDecomposition n z)
      = schurWeylDecomposition n
          (fun la => TensorProduct.map LinearMap.id (swPost n la g) (z la)) :=
  schurWeylDecomposition_equivariant n g z

/-- Etingof et al., Corollary 4.59 (dichotomy): each multiplicity space
`L_la = Hom_{S_n}(V_la, V^(tensor n))` is either zero or an irreducible representation of
`GL(V)`. -/
@[kb "etingof2011" "Corollary 4.59, p. 65"]
theorem etingof_4_59_b (la : DiagramsOfSize n) :
    Subsingleton (spechtModule la →ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin n))]
      tensorPowerModule V n) ∨
      Representation.IsIrreducible (k := ℂ)
        (V := spechtModule la →ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin n))] tensorPowerModule V n)
        (swRep n la) :=
  swRep_subsingleton_or_isIrreducible n la

end Duality

end SchurWeylSection

section SchurPolynomialSection

open Matrix Finset Fin

section Alternants

variable {R : Type*} [CommRing R] {N : ℕ} [Nontrivial R]

/-- Etingof et al., Section 4.20 (definition): the alternant `D_la` of an exponent vector equals
the Vandermonde product times the Schur polynomial `S_la`, so `S_la` is the quotient `D_la / Delta`. -/
@[kb "etingof2011" "§4.20 definition, p. 66"]
theorem etingof_sec_4_20 (lam : Fin N → ℕ) :
    schurAlternant (R := R) lam = vandermondeDelta R N * schurPoly lam :=
  schurAlternant_eq_vandermondeDelta_mul_schurPoly lam

end Alternants

section PowerSums

variable {N : ℕ}

/-- Etingof et al., Proposition 4.61: the product of power sums attached to a permutation is the
sum over partitions with at most `N` parts of the Frobenius class function times the Schur
polynomial. -/
@[kb "etingof2011" "Proposition 4.61, p. 66"]
theorem etingof_4_61_a (n : ℕ) (g : Equiv.Perm (Fin n)) :
    cyclePoly n N g = ∑ lam ∈ partitionVecs n N,
      frobChar n N lam g • (schurPoly lam : MvPolynomial (Fin N) ℂ) :=
  cyclePoly_eq_sum_frobChar_schurPoly n g

/-- Etingof et al., Proposition 4.61 (the coefficients are characters): for each partition with at
most `N` parts, the Frobenius class function is the character of the Specht module of the
corresponding diagram. -/
@[kb "etingof2011" "Proposition 4.61, p. 66"]
theorem etingof_4_61_b {n : ℕ} {lam : Fin N → ℕ} (hlam : lam ∈ partitionVecs n N) :
    ∃ la : DiagramsOfSize n, la.1.colLen 0 ≤ N ∧ (∀ j : Fin N, la.1.rowLen j = lam j) ∧
      ((spechtChar n la : irrChars ℂ (Equiv.Perm (Fin n))) : Equiv.Perm (Fin n) → ℂ) =
        frobChar n N lam :=
  exists_spechtChar_eq_frobChar hlam

/-- Etingof et al., Proposition 4.61 (a step of the proof): an alternating complex polynomial is
the combination of the alternants of its strictly decreasing exponents. -/
@[kb "etingof2011" "Proposition 4.61, p. 66"]
theorem etingof_4_61_c {F : MvPolynomial (Fin N) ℂ} (hF : IsAlternating F) :
    F = ∑ d ∈ F.support.filter (fun d : Fin N →₀ ℕ => StrictAnti ⇑d),
      F.coeff d • (alternant ⇑d : MvPolynomial (Fin N) ℂ) :=
  alternating_eq_sum_alternant hF

end PowerSums

section Evaluation

variable {N : ℕ}

/-- Etingof et al., Proposition 4.62 (first half): at a geometric progression the Schur polynomial
is a quotient of two products of differences of powers. -/
@[kb "etingof2011" "Proposition 4.62, p. 66"]
theorem etingof_4_62_a {K : Type*} [Field K] (z : K) (lam : Fin N → ℕ)
    (hz : ∀ i j : Fin N, i < j → z ^ (i : ℕ) ≠ z ^ (j : ℕ)) :
    MvPolynomial.aeval (fun i : Fin N => z ^ (i : ℕ)) (schurPoly (R := K) lam) =
      (∏ i : Fin N, ∏ j ∈ Ioi i, (z ^ schurExp lam j - z ^ schurExp lam i)) /
        ∏ i : Fin N, ∏ j ∈ Ioi i, (z ^ (i : ℕ) - z ^ (j : ℕ)) :=
  schurPoly_geom z lam hz

/-- Etingof et al., Proposition 4.62 (second half, denominators cleared): for a partition, the
value of the Schur polynomial at `(1, ..., 1)` times the product of the `j - i` is the product of
the `la_i - la_j + j - i`. -/
@[kb "etingof2011" "Proposition 4.62, p. 66"]
theorem etingof_4_62_b {R : Type*} [CommRing R] [IsDomain R] (lam : Fin N → ℕ)
    (hlam : Antitone lam) :
    MvPolynomial.aeval (fun _ : Fin N => (1 : R)) (schurPoly (R := R) lam) *
        (∏ i : Fin N, ∏ j ∈ Ioi i, (((j : ℕ) - (i : ℕ) : ℕ) : R)) =
      ∏ i : Fin N, ∏ j ∈ Ioi i, ((lam i - lam j + ((j : ℕ) - (i : ℕ)) : ℕ) : R) :=
  schurPoly_one_mul lam hlam

/-- Etingof et al., Proposition 4.62 (second half): in characteristic zero, the value of the Schur
polynomial of a partition at `(1, ..., 1)` is the product of `(la_i - la_j + j - i) / (j - i)`. -/
@[kb "etingof2011" "Proposition 4.62, p. 66"]
theorem etingof_4_62_c {K : Type*} [Field K] [CharZero K] (lam : Fin N → ℕ)
    (hlam : Antitone lam) :
    MvPolynomial.aeval (fun _ : Fin N => (1 : K)) (schurPoly (R := K) lam) =
      (∏ i : Fin N, ∏ j ∈ Ioi i, ((lam i - lam j + ((j : ℕ) - (i : ℕ)) : ℕ) : K)) /
        ∏ i : Fin N, ∏ j ∈ Ioi i, (((j : ℕ) - (i : ℕ) : ℕ) : K) :=
  schurPoly_one lam hlam

end Evaluation

end SchurPolynomialSection

section WeylSection

open PiTensorProduct
open scoped TensorProduct

/-- Etingof et al., Theorem 4.63 (Weyl character formula): the trace of a diagonal matrix on the
multiplicity space `L_la` is the Schur polynomial value when `la` has at most `N` rows and zero
otherwise. -/
@[kb "etingof2011" "Theorem 4.63, p. 67"]
theorem etingof_4_63_a {N n : ℕ} (la : DiagramsOfSize n) (x : Fin N → ℂ) (hx : ∀ i, x i ≠ 0) :
    LinearMap.trace ℂ _ (swRepGL N n la (diagGL N x hx)) = weylValue la x :=
  trace_swRepGL_diagonal la x hx

/-- Etingof et al., Theorem 4.63 (Weyl dimension formula): for a diagram with at most `N` rows,
the dimension of `L_la` is the product of `(la_i - la_j + j - i) / (j - i)`. -/
@[kb "etingof2011" "Theorem 4.63, p. 67"]
theorem etingof_4_63_b {N n : ℕ} (la : DiagramsOfSize n) (hN : la.1.colLen 0 ≤ N) :
    (Module.finrank ℂ (spechtModule la →ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin n))]
      tensorPowerModule (Fin N → ℂ) n) : ℂ) =
      (∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
          ((la.1.rowLen i - la.1.rowLen j + ((j : ℕ) - (i : ℕ)) : ℕ) : ℂ)) /
        ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (((j : ℕ) - (i : ℕ) : ℕ) : ℂ) :=
  finrank_swRepGL la hN

/-- Etingof et al., Theorem 4.63 (vanishing): the multiplicity space `L_la` is zero exactly when
`N` is smaller than the number of rows of `la`. -/
@[kb "etingof2011" "Theorem 4.63, p. 67"]
theorem etingof_4_63_c {N n : ℕ} (la : DiagramsOfSize n) :
    Module.finrank ℂ (spechtModule la →ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin n))]
      tensorPowerModule (Fin N → ℂ) n) = 0 ↔ N < la.1.colLen 0 :=
  finrank_swRepGL_eq_zero_iff la

/-- Etingof et al., Theorem 4.63 (trace through the decomposition): the trace of `sigma` composed
with `g tensor ... tensor g` on `V^(tensor n)` is the sum over diagrams of the Specht character
at `sigma` times the trace of `g` on `L_la`. -/
@[kb "etingof2011" "Theorem 4.63, p. 67"]
theorem etingof_4_63_d {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ)
    (σ : Equiv.Perm (Fin n)) (g : V →ₗ[ℂ] V) :
    LinearMap.trace ℂ (⨂[ℂ] _ : Fin n, V) (tensorPowerPermRep ℂ n V σ ∘ₗ tensorPowerMap n g) =
      ∑ la : DiagramsOfSize n,
        ((spechtChar n la : irrChars ℂ (Equiv.Perm (Fin n))) : Equiv.Perm (Fin n) → ℂ) σ *
          LinearMap.trace ℂ _ (swPost (V := V) n la g) :=
  trace_tensorPower_eq_sum n σ g

open scoped Classical in
/-- Etingof et al., Theorem 4.63 (a step of the proof): the trace of `sigma` composed with the
tensor power of a diagonal matrix is the product of power sums attached to `sigma` evaluated at the
diagonal entries. -/
@[kb "etingof2011" "Theorem 4.63, p. 67"]
theorem etingof_4_63_e (n N : ℕ) (σ : Equiv.Perm (Fin n)) (x : Fin N → ℂ) :
    LinearMap.trace ℂ (⨂[ℂ] _ : Fin n, Fin N → ℂ)
        (tensorPowerPermRep ℂ n (Fin N → ℂ) σ ∘ₗ
          tensorPowerMap n (Matrix.mulVecLin (Matrix.diagonal x))) =
      MvPolynomial.eval x (cyclePoly n N σ) :=
  trace_perm_comp_tensorPowerMap_diagonal n N σ x

end WeylSection

section GL2Section

open Matrix GL2

section Classes

variable {F : Type u} [Field F]

/-- Etingof et al., Section 4.24.1 (table): `GL_2(F_q)` has `q - 1` conjugacy classes of scalar
matrices. -/
@[kb "etingof2011" "§4.24.1 table, p. 69"]
theorem etingof_sec_4_24_1_a [Finite F] : (scalarClasses F).ncard = Nat.card F - 1 :=
  ncard_scalarClasses

/-- Etingof et al., Section 4.24.1 (table): `GL_2(F_q)` has `q - 1` parabolic conjugacy
classes. -/
@[kb "etingof2011" "§4.24.1 table, p. 69"]
theorem etingof_sec_4_24_1_b [Finite F] : (parabolicClasses F).ncard = Nat.card F - 1 :=
  ncard_parabolicClasses

/-- Etingof et al., Section 4.24.1 (table): `GL_2(F_q)` has `(q-1)(q-2)/2` hyperbolic conjugacy
classes. -/
@[kb "etingof2011" "§4.24.1 table, p. 69"]
theorem etingof_sec_4_24_1_c [Finite F] :
    (hyperbolicClasses F).ncard = (Nat.card F - 1) * (Nat.card F - 2) / 2 :=
  ncard_hyperbolicClasses

/-- Etingof et al., Section 4.24.1 (table): `GL_2(F_q)` has `q(q-1)/2` elliptic conjugacy
classes. -/
@[kb "etingof2011" "§4.24.1 table, p. 69"]
theorem etingof_sec_4_24_1_d [Finite F] :
    (ellipticClasses F).ncard = Nat.card F * (Nat.card F - 1) / 2 :=
  ncard_ellipticClasses

/-- Etingof et al., Section 4.24.1 (table): `GL_2(F_q)` has `q^2 - 1` conjugacy classes in
total. -/
@[kb "etingof2011" "§4.24.1 table, p. 69"]
theorem etingof_sec_4_24_1_e [Finite F] :
    Nat.card (ConjClasses (GL (Fin 2) F)) = Nat.card F ^ 2 - 1 :=
  nat_card_conjClasses

/-- Etingof et al., Section 4.24.1 (table): every conjugacy class of `GL_2(F)` is scalar,
parabolic, hyperbolic or elliptic. -/
@[kb "etingof2011" "§4.24.1 table, p. 69"]
theorem etingof_sec_4_24_1_f (c : ConjClasses (GL (Fin 2) F)) :
    c ∈ scalarClasses F ∨ c ∈ parabolicClasses F ∨ c ∈ hyperbolicClasses F ∨
      c ∈ ellipticClasses F :=
  conjClass_cover c

/-- Etingof et al., Section 4.24.1 (table): the conjugacy class of an elliptic element has
`q^2 - q` elements. -/
@[kb "etingof2011" "§4.24.1 table, p. 69"]
theorem etingof_sec_4_24_1_g [Finite F] {t n : F} (h : ∀ x : F, x ^ 2 - t * x + n ≠ 0) :
    (conjugatesOf (ellipticElt h : GL (Fin 2) F)).ncard = Nat.card F ^ 2 - Nat.card F :=
  ncard_conjugatesOf_elliptic h

/-- Etingof et al., Proposition 4.70: the commutator subgroup of `GL_2(F)` is the kernel of the
determinant, assuming some `a` has `a ≠ 0` and `a^2 ≠ 1`. -/
@[kb "etingof2011" "Proposition 4.70, p. 70"]
theorem etingof_4_70_a (h : ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1) :
    commutator (GL (Fin 2) F) = (GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ).ker :=
  commutator_GL2 h

/-- Etingof et al., Proposition 4.70: the commutator subgroup of `GL_2(F)` is the image of
`SL_2(F)`, assuming some `a` has `a ≠ 0` and `a^2 ≠ 1`. -/
@[kb "etingof2011" "Proposition 4.70, p. 70"]
theorem etingof_4_70_b (h : ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1) :
    commutator (GL (Fin 2) F) =
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F).range :=
  commutator_GL2_eq_range h

/-- Etingof et al., Section 4.24.2: distinct characters of `F^×` give distinct one-dimensional
representations `xi composed with det` of `GL_2(F)`. -/
@[kb "etingof2011" "§4.24.2, p. 70"]
theorem etingof_sec_4_24_2_a :
    Function.Injective (fun ξ : Fˣ →* ℂˣ => (detChar ξ : GL (Fin 2) F →* ℂˣ)) :=
  detChar_injective

/-- Etingof et al., Section 4.24.2: every one-dimensional representation of `GL_2(F)` is `xi`
composed with `det` for a unique character `xi` of `F^×`. -/
@[kb "etingof2011" "§4.24.2, p. 70"]
theorem etingof_sec_4_24_2_b (h : ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1) (φ : GL (Fin 2) F →* ℂˣ) :
    ∃! ξ : Fˣ →* ℂˣ, φ = detChar ξ :=
  exists_unique_detChar h φ

/-- Etingof et al., Section 4.24.2: `GL_2(F_q)` has exactly `q - 1` one-dimensional complex
representations. -/
@[kb "etingof2011" "§4.24.2, p. 70"]
theorem etingof_sec_4_24_2_c [Finite F] (h : ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1) :
    Nat.card (GL (Fin 2) F →* ℂˣ) = Nat.card F - 1 :=
  card_homs_GL2 h

/-- Etingof et al., Section 4.24.3 (definition): the principal series representation of
`GL_2(F_q)` has dimension `q + 1`. -/
@[kb "etingof2011" "§4.24.3 definition, p. 71"]
theorem etingof_sec_4_24_3_a [Finite F] (l₁ l₂ : Fˣ →* ℂˣ) :
    finrank ℂ (Representation.coindV (borel F).subtype (lineRep (borelChar l₁ l₂))) =
      Nat.card F + 1 :=
  finrank_principalSeries l₁ l₂

/-- Etingof et al., Section 4.24.3 (definition): the Borel subgroup has index `q + 1` in
`GL_2(F_q)`. -/
@[kb "etingof2011" "§4.24.3 definition, p. 71"]
theorem etingof_sec_4_24_3_b [Finite F] : (borel F).index = Nat.card F + 1 :=
  index_borel

end Classes

section PrincipalSeriesSection

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

/-- Etingof et al., Theorem 4.71 (irreducibility): for distinct characters, the principal series
representation of `GL_2(F_q)` is irreducible. -/
@[kb "etingof2011" "Theorem 4.71, p. 71"]
theorem etingof_4_71_a {l₁ l₂ : Fˣ →* ℂˣ} (hne : l₁ ≠ l₂) :
    IsIrreducible (principalSeries (F := F) l₁ l₂) :=
  isIrreducible_principalSeries hne

/-- Etingof et al., Theorem 4.71 (the equal case): the principal series `V_{mu,mu}` is the direct
sum of a line, on which `g` acts by `mu (det g)`, and an irreducible representation of dimension
`q`. -/
@[kb "etingof2011" "Theorem 4.71, p. 71"]
theorem etingof_4_71_b (μ : Fˣ →* ℂˣ) :
    ∃ S W : Subrepresentation (principalSeries (F := F) μ μ), IsCompl S W ∧
      finrank ℂ S.toSubmodule = 1 ∧
      (∀ g : GL (Fin 2) F, ∀ v ∈ S.toSubmodule,
        principalSeries μ μ g v = (μ (GeneralLinearGroup.det g) : ℂ) • v) ∧
      IsIrreducible W.toRepresentation ∧ finrank ℂ W.toSubmodule = Nat.card F :=
  principalSeries_diag_decomposition μ

/-- Etingof et al., Theorem 4.71 (isomorphisms): two irreducible principal series are isomorphic
exactly when their pairs of characters agree as unordered pairs. -/
@[kb "etingof2011" "Theorem 4.71, p. 71"]
theorem etingof_4_71_c {l₁ l₂ l₁' l₂' : Fˣ →* ℂˣ} (hne : l₁ ≠ l₂) (hne' : l₁' ≠ l₂') :
    Nonempty (Representation.Equiv (principalSeries (F := F) l₁ l₂) (principalSeries l₁' l₂')) ↔
      (l₁ = l₁' ∧ l₂ = l₂') ∨ (l₁ = l₂' ∧ l₂ = l₁') :=
  nonempty_equiv_principalSeries_iff hne hne'

end PrincipalSeriesSection

section ComplementarySeries

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
  {t n : F} (h : ∀ x : F, x ^ 2 - t * x + n ≠ 0)

/-- Etingof et al., Section 4.24.4: the character of the representation induced from a character
`nu` of the nonsplit torus, at a scalar matrix `c`, is `(q^2 - q) nu(c)`. -/
@[kb "etingof2011" "§4.24.4, p. 73"]
theorem etingof_sec_4_24_4_a (ν : torus h →* ℂˣ) (c : Fˣ) :
    (torusInd h ν).character (scal c) =
      ((Nat.card F ^ 2 - Nat.card F : ℕ) : ℂ) * (ν ⟨scal c, diag_mem_torus h c⟩ : ℂ) :=
  character_torusInd_scal h ν c

/-- Etingof et al., Section 4.24.4: the character of the representation induced from the nonsplit
torus vanishes on parabolic elements. -/
@[kb "etingof2011" "§4.24.4, p. 73"]
theorem etingof_sec_4_24_4_b (ν : torus h →* ℂˣ) (x : Fˣ) :
    (torusInd h ν).character (upperUnit x 1) = 0 :=
  character_torusInd_upper h ν x

/-- Etingof et al., Section 4.24.4: the character of the representation induced from the nonsplit
torus vanishes on hyperbolic elements. -/
@[kb "etingof2011" "§4.24.4, p. 73"]
theorem etingof_sec_4_24_4_c (ν : torus h →* ℂˣ) {x y : Fˣ} (hxy : x ≠ y) :
    (torusInd h ν).character (GL2.diagUnit x y) = 0 :=
  character_torusInd_diag h ν hxy

/-- Etingof et al., Section 4.24.4: at a nonscalar element `z` of the nonsplit torus, the induced
character is `nu(z) + nu(z^sigma)`, where `z^sigma` is the Galois conjugate of `z`. -/
@[kb "etingof2011" "§4.24.4, p. 73"]
theorem etingof_sec_4_24_4_d (ν : torus h →* ℂˣ) {z : GL (Fin 2) F} (hz : z ∈ torus h)
    (hz10 : (z : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) :
    (torusInd h ν).character z = (ν ⟨z, hz⟩ : ℂ) + (ν (sigmaT h ⟨z, hz⟩) : ℂ) :=
  character_torusInd_torus h ν hz hz10

/-- Etingof et al., Section 4.24.4: the Galois conjugation of the nonsplit torus is the `q`-th
power map. -/
@[kb "etingof2011" "§4.24.4, p. 73"]
theorem etingof_sec_4_24_4_e (z : torus h) : sigmaT h z = z ^ Nat.card F :=
  sigmaT_eq_pow h z

/-- Etingof et al., Section 4.24.4: the representation induced from `nu` is isomorphic to the one
induced from `nu^q`. -/
@[kb "etingof2011" "§4.24.4, p. 73"]
theorem etingof_sec_4_24_4_f (ν : torus h →* ℂˣ) :
    Nonempty (Representation.Equiv (torusInd h ν) (torusInd h (nuPow h ν))) :=
  nonempty_equiv_torusInd_nuPow h ν

/-- Etingof et al., Lemma 4.72 (norm): the virtual character `W_1 tensor V_{alpha,1} - V_{alpha,1}
- Y_nu` has norm one, where `nu` restricts to `alpha` on the scalars and `nu^q` differs from `nu`. -/
@[kb "etingof2011" "Lemma 4.72, p. 74"]
theorem etingof_4_72_a (α : Fˣ →* ℂˣ) (ν : torus h →* ℂˣ)
    (hα : ∀ c : Fˣ, ν ⟨scal c, diag_mem_torus h c⟩ = α c) (hq : nuPow h ν ≠ ν) :
    hermitianPairing (cuspChar h α ν) (cuspChar h α ν) = 1 :=
  hermitianPairing_cuspChar_nuPow h α ν hα hq

/-- Etingof et al., Lemma 4.72 (norm, Galois form): the same virtual character has norm one when
`nu` composed with the Galois conjugation differs from `nu`. -/
@[kb "etingof2011" "Lemma 4.72, p. 74"]
theorem etingof_4_72_b (α : Fˣ →* ℂˣ) (ν : torus h →* ℂˣ)
    (hα : ∀ c : Fˣ, ν ⟨scal c, diag_mem_torus h c⟩ = α c) (hσ : ν.comp (sigmaT h) ≠ ν) :
    hermitianPairing (cuspChar h α ν) (cuspChar h α ν) = 1 :=
  hermitianPairing_cuspChar h α ν hα hσ

/-- Etingof et al., Lemma 4.72 (value at one): the virtual character has value `q - 1` at the
identity. -/
@[kb "etingof2011" "Lemma 4.72, p. 74"]
theorem etingof_4_72_c (α : Fˣ →* ℂˣ) (ν : torus h →* ℂˣ)
    (hα : ∀ c : Fˣ, ν ⟨scal c, diag_mem_torus h c⟩ = α c) :
    cuspChar h α ν 1 = (Nat.card F : ℂ) - 1 :=
  cuspChar_one h α ν hα

/-- Etingof et al., Section 4.24.4 (conclusion): when `nu` restricts to `alpha` on the scalars and
`nu^q` differs from `nu`, there is an irreducible representation of dimension `q - 1` with the
character of the virtual representation above. -/
@[kb "etingof2011" "§4.24.4 conclusion, p. 75"]
theorem etingof_sec_4_24_4_conclusion_a (α : Fˣ →* ℂˣ) (ν : torus h →* ℂˣ)
    (hα : ∀ c : Fˣ, ν ⟨scal c, diag_mem_torus h c⟩ = α c) (hq : nuPow h ν ≠ ν) :
    ∃ X : IrrRep ℂ (GL (Fin 2) F), X.ρ.character = cuspChar h α ν ∧
      finrank ℂ X.V = Nat.card F - 1 :=
  exists_irrep_cuspidal_nuPow h α ν hα hq

/-- Etingof et al., Section 4.24.4 (conclusion): there are `q(q-1)/2` cuspidal characters, stated
as twice their number being `q^2 - q`. -/
@[kb "etingof2011" "§4.24.4 conclusion, p. 75"]
theorem etingof_sec_4_24_4_conclusion_b : 2 * (cuspSet h).ncard = Nat.card F ^ 2 - Nat.card F :=
  ncard_cuspSet h

/-- Etingof et al., Section 4.24.4 (conclusion): the irreducible characters of `GL_2(F_q)` are the
one-dimensional ones, the characters of the `q`-dimensional `W_mu`, those of the irreducible
principal series and the cuspidal ones. -/
@[kb "etingof2011" "§4.24.4 conclusion, p. 75"]
theorem etingof_sec_4_24_4_conclusion_c :
    irrChars ℂ (GL (Fin 2) F) = ((detSet ∪ wSet) ∪ psSet) ∪ cuspSet h :=
  irrChars_GL2_eq h

/-- Etingof et al., Section 4.24.4 (conclusion): the nonsplit torus is cyclic. -/
@[kb "etingof2011" "§4.24.4 conclusion, p. 75"]
theorem etingof_sec_4_24_4_conclusion_d : IsCyclic (torus h) :=
  isCyclic_torus h

end ComplementarySeries

section CharacterCount

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

/-- Etingof et al., Section 4.24.4 (conclusion): `GL_2(F_q)` has exactly `q^2 - 1` irreducible
characters. -/
@[kb "etingof2011" "§4.24.4 conclusion, p. 75"]
theorem etingof_sec_4_24_4_conclusion_e :
    Nat.card (irrChars ℂ (GL (Fin 2) F)) = Nat.card F ^ 2 - 1 :=
  card_irrChars_GL2

/-- Etingof et al., Section 4.24.4 (conclusion): for every finite field, the irreducible
characters of `GL_2(F_q)` are the four families, for a suitable irreducible quadratic. -/
@[kb "etingof2011" "§4.24.4 conclusion, p. 75"]
theorem etingof_sec_4_24_4_conclusion_f :
    ∃ (t n : F) (h : ∀ x : F, x ^ 2 - t * x + n ≠ 0),
      irrChars ℂ (GL (Fin 2) F) = ((detSet ∪ wSet) ∪ psSet) ∪ cuspSet h :=
  exists_irrChars_GL2_eq

end CharacterCount

end GL2Section

section ArtinSection

variable {k : Type u} {G : Type v} [Field k] [CharZero k] [IsAlgClosed k] [Group G] [Fintype G]

/-- Etingof et al., Theorem 4.73 (Artin): for a family `X` of subgroups, the following are
equivalent: every element lies in a conjugate of a member of `X`; the characters induced from
members of `X` span the class functions; every irreducible character is a rational combination of
such induced characters. -/
@[kb "etingof2011" "Theorem 4.73, p. 75"]
theorem etingof_4_73_a (X : Set (Subgroup G)) :
    List.TFAE [∀ g : G, ∃ H ∈ X, ∃ x : G, x * g * x⁻¹ ∈ H,
      Submodule.span k (indChars k X) = classFunctions k G,
      ∀ χ ∈ irrChars k G, χ ∈ Submodule.span ℚ (indChars k X)] :=
  artin_induction X

omit [IsAlgClosed k] in
/-- Etingof et al., Theorem 4.73 (Frobenius reciprocity step): the pairing of an induced class
function with a class function of `G` is the pairing on `H` with the restriction. -/
@[kb "etingof2011" "Theorem 4.73, p. 75"]
theorem etingof_4_73_b (H : Subgroup G) [Fintype H] (ψ : H → k) {φ : G → k}
    (hφ : φ ∈ classFunctions k G) :
    pairing (indClassFun H ψ) φ = pairing ψ (fun h : H ↦ φ h) :=
  pairing_indClassFun H ψ hφ

omit [CharZero k] [IsAlgClosed k] in
/-- Etingof et al., Theorem 4.73 (a step of the proof): the character of an induced representation
is the induced class function of the character. -/
@[kb "etingof2011" "Theorem 4.73, p. 75"]
theorem etingof_4_73_c (H : Subgroup G) {V : Type*} [AddCommGroup V] [Module k V]
    [Module.Finite k V] [Invertible (Nat.card H : k)] (ρ : Representation k H V) :
    (Ind H ρ).character = indClassFun H ρ.character :=
  character_Ind_eq_indClassFun H ρ

/-- Etingof et al., Corollary 4.74: the induced characters from cyclic subgroups span the class
functions, every irreducible character is a rational combination of them, and so is the character
of every finite-dimensional representation. -/
@[kb "etingof2011" "Corollary 4.74, p. 76"]
theorem etingof_4_74 :
    Submodule.span k (indChars k (cyclicSubgroups G)) = classFunctions k G ∧
    (∀ χ ∈ irrChars k G, χ ∈ Submodule.span ℚ (indChars k (cyclicSubgroups G))) ∧
    ∀ {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V] (ρ : Representation k G V),
      ρ.character ∈ Submodule.span ℚ (indChars k (cyclicSubgroups G)) :=
  artin_cyclic

end ArtinSection

section LittleGroupSection

section Irreducibility

variable {A : Type*} {G : Type*} [CommGroup A] [Group G] (φ : G →* MulAut A) (x : A →* ℂˣ)
  [Fintype A] [Fintype G] {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  (U : Representation ℂ (stabChar φ x) W)

/-- Etingof et al., Section 4.26 (construction): the character of the induced representation
`V_(O,U)` of `A ⋊ G` at `(l, g)` is a Mackey-type sum over `G` of `x(k l)` times the extension by
zero of the character of `U` at `k g k⁻¹`. -/
@[kb "etingof2011" "§4.26 construction, p. 76"]
theorem etingof_sec_4_26_kb (l : A) (g : G) :
    (Ind (littleSub φ x) (littleRep φ x U)).character ⟨l, g⟩ =
      (Nat.card (stabChar φ x) : ℂ)⁻¹ *
        ∑ k : G, (x (φ k l) : ℂ) * charExt (stabChar φ x) U (k * g * k⁻¹) :=
  character_littleInd φ x U l g

/-- Etingof et al., Theorem 4.75 (Mackey, character formula): the character of `V_(O,U)` at
`(l, g)` is a Mackey-type sum over `G`. -/
@[kb "etingof2011" "Theorem 4.75, p. 76"]
theorem etingof_4_75_a (l : A) (g : G) :
    (Ind (littleSub φ x) (littleRep φ x U)).character ⟨l, g⟩ =
      (Nat.card (stabChar φ x) : ℂ)⁻¹ *
        ∑ k : G, (x (φ k l) : ℂ) * charExt (stabChar φ x) U (k * g * k⁻¹) :=
  character_littleInd φ x U l g

/-- Etingof et al., Theorem 4.75 (irreducibility): for an irreducible representation `U` of the
stabiliser `G_x`, the induced representation `V_(O,U)` of `A ⋊ G` is irreducible. -/
@[kb "etingof2011" "Theorem 4.75, p. 76"]
theorem etingof_4_75_b [IsIrreducible U] :
    IsIrreducible (Ind (littleSub φ x) (littleRep φ x U)) :=
  isIrreducible_littleInd φ x U

/-- Etingof et al., Theorem 4.75 (distinct `U`): for non-isomorphic irreducible representations of
`G_x`, the representations `V_(O,U)` and `V_(O,U')` are not isomorphic. -/
@[kb "etingof2011" "Theorem 4.75, p. 76"]
theorem etingof_4_75_c [IsIrreducible U] {W' : Type*} [AddCommGroup W'] [Module ℂ W']
    [FiniteDimensional ℂ W'] (U' : Representation ℂ (stabChar φ x) W') [IsIrreducible U']
    (h : IsEmpty (Representation.Equiv U U')) :
    IsEmpty (Representation.Equiv (Ind (littleSub φ x) (littleRep φ x U))
      (Ind (littleSub φ x) (littleRep φ x U'))) :=
  isEmpty_equiv_littleInd φ x U U' h

/-- Etingof et al., Theorem 4.75 (distinct orbits): if `x'` is not in the `G`-orbit of `x`, then
`V_(O,U)` and `V_(O',U')` are not isomorphic. -/
@[kb "etingof2011" "Theorem 4.75, p. 76"]
theorem etingof_4_75_d [IsIrreducible U] (x' : A →* ℂˣ) {W' : Type*} [AddCommGroup W']
    [Module ℂ W'] [FiniteDimensional ℂ W'] (U' : Representation ℂ (stabChar φ x') W')
    (h : ∀ g : G, ∃ a, x' a ≠ x (φ g a)) :
    IsEmpty (Representation.Equiv (Ind (littleSub φ x) (littleRep φ x U))
      (Ind (littleSub φ x') (littleRep φ x' U'))) :=
  isEmpty_equiv_littleInd_of_not_mem_orbit φ x U x' U' h

end Irreducibility

/-- Etingof et al., Theorem 4.75 (exhaustion): every irreducible complex representation of
`A ⋊ G`, for `A` finite abelian and `G` finite, is isomorphic to some `V_(O,U)`. -/
@[kb "etingof2011" "Theorem 4.75, p. 76"]
theorem etingof_4_75_e {A : Type u} {G : Type v} [CommGroup A] [Group G] [Fintype A] [Fintype G]
    (φ : G →* MulAut A) (Y : IrrRep ℂ (A ⋊[φ] G)) :
    ∃ (x : A →* ℂˣ) (U : IrrRep ℂ (stabChar φ x)),
      Nonempty (Representation.Equiv Y.ρ (Ind (littleSub φ x) (littleRep φ x U.ρ))) :=
  exists_equiv_littleInd φ Y

end LittleGroupSection

/-- Etingof et al., Lemma 4.43: for an idempotent `e` of an algebra `A` and an `A`-module `M`, the
space of `A`-module maps from the left ideal `A e` to `M` is isomorphic, as a vector space, to
`e M`. -/
@[kb "etingof2011" "Lemma 4.43, p. 60"]
theorem etingof_4_43 {k : Type u} {A : Type v} {M : Type*} [CommSemiring k] [Ring A] [Algebra k A]
    [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M] {e : A}
    (he : IsIdempotentElem e) :
    Nonempty ((Ideal.span {e} →ₗ[A] M) ≃ₗ[k] idemSubmodule k M e) :=
  ⟨homIdealSpanEquiv he⟩

/-- Etingof et al., Proposition 4.64: adding a full column of length `N` to a diagram with at most `N` rows
corresponds to twisting `L_λ` by the top exterior power `Λ^N V` (the determinant). -/
@[kb "etingof2011" "Proposition 4.64, p. 67"]
theorem etingof_4_64 {n m N : ℕ} (la : DiagramsOfSize n) (mu : DiagramsOfSize m)
    (hla : la.1.colLen 0 ≤ N) (hmu : mu.1.colLen 0 ≤ N)
    (h : ∀ j : Fin N, mu.1.rowLen j = la.1.rowLen j + 1) :
    Nonempty (Representation.Equiv (swRepGL N m mu) ((swRepGL N n la).tprod (detRep N ℂ 1))) :=
  nonempty_equiv_swRepGL_add_one la mu hla hmu h

end UndergradKB.RepresentationTheory.Course
