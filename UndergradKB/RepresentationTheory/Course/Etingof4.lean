import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Solvable
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import UndergradKB.Common.Attr

/-!
# Etingof et al., Introduction to Representation Theory: Chapter 4 (more on finite groups)

Thin theorems in the book's terms for the items of Chapter 4 that Mathlib already contains:
algebraic numbers and integers, solvable groups, induced representations and Frobenius
reciprocity, the order of `GL₂(𝔽_q)` and semidirect products.  Each is tagged with the source key
`etingof2011` and the locator of the item in the book.
-/

namespace UndergradKB.RepresentationTheory.Course

universe u

open Polynomial

/-- Etingof et al., Definition 4.9: a complex number is an algebraic integer if it is a root of a
monic polynomial with integer coefficients. -/
@[kb "etingof2011" "Definition 4.9, p. 49"]
theorem etingof_4_9_a (z : ℂ) :
    IsIntegral ℤ z ↔ ∃ p : ℤ[X], p.Monic ∧ aeval z p = 0 :=
  Iff.rfl

/-- Etingof et al., Definition 4.9: a complex number is algebraic if it is a root of a monic
polynomial with rational coefficients. -/
@[kb "etingof2011" "Definition 4.9, p. 49"]
theorem etingof_4_9_b (z : ℂ) :
    IsAlgebraic ℚ z ↔ ∃ p : ℚ[X], p.Monic ∧ aeval z p = 0 :=
  isAlgebraic_iff_isIntegral

/-- Etingof et al., Proposition 4.12: sums and products of algebraic integers are algebraic
integers. -/
@[kb "etingof2011" "Proposition 4.12, p. 50"]
theorem etingof_4_12_a {z w : ℂ} (hz : IsIntegral ℤ z) (hw : IsIntegral ℤ w) :
    IsIntegral ℤ (z + w) ∧ IsIntegral ℤ (z * w) :=
  ⟨hz.add hw, hz.mul hw⟩

/-- Etingof et al., Proposition 4.12: the algebraic numbers form an algebraically closed field,
namely the algebraic closure of `ℚ` inside `ℂ`. -/
@[kb "etingof2011" "Proposition 4.12, p. 50"]
theorem etingof_4_12_b : IsAlgClosed (algebraicClosure ℚ ℂ) :=
  IsAlgClosure.isAlgClosed ℚ

/-- Etingof et al., Proposition 4.13: a rational number that is an algebraic integer is an
integer. -/
@[kb "etingof2011" "Proposition 4.13, p. 50"]
theorem etingof_4_13 (q : ℚ) : IsIntegral ℤ q ↔ ∃ n : ℤ, (n : ℚ) = q :=
  IsIntegrallyClosed.isIntegral_iff

/-- Etingof et al., Section 4.3: the algebraic conjugates of an algebraic number are the roots of
its minimal polynomial; the minimal polynomial is monic and annihilates the number. -/
@[kb "etingof2011" "§4.3, p. 50"]
theorem etingof_sec_4_3_a {z : ℂ} (hz : IsIntegral ℚ z) :
    (minpoly ℚ z).Monic ∧ aeval z (minpoly ℚ z) = 0 :=
  ⟨minpoly.monic hz, minpoly.aeval ℚ z⟩

/-- Etingof et al., Section 4.3: the minimal polynomial over `ℚ` of an algebraic integer is the
image of its minimal polynomial over `ℤ`, so it has integer coefficients. -/
@[kb "etingof2011" "§4.3, p. 51"]
theorem etingof_sec_4_3_b {z : ℂ} (hz : IsIntegral ℤ z) :
    minpoly ℚ z = (minpoly ℤ z).map (algebraMap ℤ ℚ) :=
  minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hz

/-- Etingof et al., Definition 4.18: a group is solvable if its derived series reaches the
trivial subgroup. -/
@[kb "etingof2011" "Definition 4.18, p. 52"]
theorem etingof_4_18 (G : Type*) [Group G] :
    Group.IsSolvable G ↔ ∃ n : ℕ, Subgroup.derivedSeries G n = ⊥ :=
  Group.isSolvable_def G

/-- Etingof et al., Definition 4.28: the induced representation consists of functions
`f : G → V` with `f (h x) = h · f x` for `h` in the subgroup, with `G` acting by translation
(Mathlib calls this construction coinduction along the inclusion). -/
@[kb "etingof2011" "Definition 4.28, p. 54"]
theorem etingof_4_28 {k G V : Type*} [Semiring k] [Group G] [AddCommMonoid V] [Module k V]
    (H : Subgroup G) (ρ : Representation k H V) (f : G → V) :
    f ∈ Representation.coindV H.subtype ρ ↔ ∀ (h : H) (x : G), f (h * x) = ρ h (f x) :=
  Representation.mem_coindV H.subtype ρ f

/-- Etingof et al., Remark 4.29: the induced representation is isomorphic to the space of
homomorphisms `Hom_H(k[G], V)`. -/
@[kb "etingof2011" "Remark 4.29, p. 55"]
theorem etingof_4_29 {k G H : Type u} [CommRing k] [Monoid G] [Monoid H] (φ : G →* H)
    (A : Rep.{u} k G) : Nonempty (Rep.coind φ A ≅ Rep.coind' φ A) :=
  ⟨Rep.coindIso φ A⟩

/-- Etingof et al., Theorem 4.33 (Frobenius reciprocity): homomorphisms from the restriction of
`B` to a subgroup into `A` correspond to homomorphisms from `B` into the induced
representation of `A`. -/
@[kb "etingof2011" "Theorem 4.33, p. 56"]
theorem etingof_4_33 {k G H : Type u} [CommRing k] [Monoid G] [Monoid H] (φ : G →* H)
    (B : Rep.{u} k H) (A : Rep.{u} k G) :
    Nonempty ((Rep.res φ B ⟶ A) ≃ₗ[k] (B ⟶ Rep.coind φ A)) :=
  ⟨Rep.resCoindHomEquiv φ B A⟩

/-- Etingof et al., Section 4.24.1: the order of `GL₂(𝔽_q)` is `(q² - 1)(q² - q)`. -/
@[kb "etingof2011" "§4.24.1, p. 68"]
theorem etingof_sec_4_24_1 (𝔽 : Type*) [Field 𝔽] [Fintype 𝔽] :
    Nat.card (Matrix.GeneralLinearGroup (Fin 2) 𝔽) =
      (Fintype.card 𝔽 ^ 2 - 1) * (Fintype.card 𝔽 ^ 2 - Fintype.card 𝔽) := by
  rw [Matrix.card_GL_field 2]
  simp [Fin.prod_univ_two]

/-- Etingof et al., Section 4.26: the semidirect product `A ⋊ G` is the set of pairs with product
`(a₁, g₁)(a₂, g₂) = (a₁ · g₁(a₂), g₁ g₂)`. -/
@[kb "etingof2011" "§4.26 definition, p. 76"]
theorem etingof_sec_4_26 {N G : Type*} [Group N] [Group G] (φ : G →* MulAut N) (a₁ a₂ : N)
    (g₁ g₂ : G) :
    (⟨a₁, g₁⟩ : N ⋊[φ] G) * ⟨a₂, g₂⟩ = ⟨a₁ * φ g₁ a₂, g₁ * g₂⟩ :=
  SemidirectProduct.mul_def _ _

end UndergradKB.RepresentationTheory.Course
