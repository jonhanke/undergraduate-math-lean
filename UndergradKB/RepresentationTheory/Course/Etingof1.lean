import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.RingQuot
import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.RingTheory.SimpleRing.Defs
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import UndergradKB.Common.Attr

/-!
# Etingof et al., Introduction to Representation Theory: Chapter 1 (basic notions)

Thin theorems in the book's terms, each proved by the Mathlib declaration named in its proof, so
that every central item of Chapter 1 has a Lean name that a course can cite.  Each statement is
tagged with the source key `etingof2011` and the locator of the item in the book.
-/

namespace UndergradKB.RepresentationTheory.Course

open scoped TensorProduct MonoidAlgebra Matrix
open Representation

universe u

section Algebras

/-- Etingof et al., Definition 1.3: the structure map of an algebra is central, so scalars commute
with every element of the algebra. -/
@[kb "etingof2011" "Definition 1.3, p. 7"]
theorem etingof_1_3 {k A : Type*} [CommSemiring k] [Semiring A] [Algebra k A] (r : k) (a : A) :
    algebraMap k A r * a = a * algebraMap k A r :=
  Algebra.commutes r a

/-- Etingof et al., Definition 1.4: the unit of an algebra is a two-sided identity. -/
@[kb "etingof2011" "Definition 1.4, p. 7"]
theorem etingof_1_4 {A : Type*} [Semiring A] (a : A) : 1 * a = a ∧ a * 1 = a :=
  ⟨one_mul a, mul_one a⟩

/-- Etingof et al., Proposition 1.5: the unit is determined by the multiplication, so two
structures with the same product have the same identity element. -/
@[kb "etingof2011" "Proposition 1.5, p. 7"]
theorem etingof_1_5 {A : Type*} (m₁ m₂ : MulOneClass A) (h : m₁.mul = m₂.mul) : m₁ = m₂ :=
  MulOneClass.ext h

/-- Etingof et al., Example 1.6: the ground field, polynomial algebras, endomorphism algebras,
free algebras and group algebras are all algebras over `k`. -/
@[kb "etingof2011" "Example 1.6, p. 7"]
theorem etingof_1_6 (k : Type*) [CommRing k] (σ X V G : Type*) [AddCommGroup V] [Module k V]
    [Monoid G] :
    Nonempty (Algebra k k) ∧ Nonempty (Algebra k (MvPolynomial σ k)) ∧
      Nonempty (Algebra k (Module.End k V)) ∧ Nonempty (Algebra k (FreeAlgebra k X)) ∧
      Nonempty (Algebra k k[G]) :=
  ⟨⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩⟩

/-- Etingof et al., Definition 1.7: the group algebra of a commutative group is a commutative
algebra. -/
@[kb "etingof2011" "Definition 1.7, p. 7"]
theorem etingof_1_7 {k G : Type*} [CommSemiring k] [CommMonoid G] (a b : k[G]) : a * b = b * a :=
  mul_comm a b

/-- Etingof et al., Definition 1.8: an algebra homomorphism is linear, multiplicative and
unit preserving. -/
@[kb "etingof2011" "Definition 1.8, p. 7"]
theorem etingof_1_8 {k A B : Type*} [CommSemiring k] [Semiring A] [Semiring B] [Algebra k A]
    [Algebra k B] (f : A →ₐ[k] B) (c : k) (a b : A) :
    f (c • a + b) = c • f a + f b ∧ f (a * b) = f a * f b ∧ f 1 = 1 :=
  ⟨by simp, map_mul f a b, map_one f⟩

/-- Etingof et al., Definition 1.9: a module over an algebra `A` acts through the algebra
homomorphism `A → End V`; here the action of `a` is the endomorphism `v ↦ a • v`. -/
@[kb "etingof2011" "Definition 1.9, p. 7"]
theorem etingof_1_9 {k A V : Type*} [CommSemiring k] [Semiring A] [Algebra k A] [AddCommMonoid V]
    [Module k V] [Module A V] [IsScalarTower k A V] (a : A) (v : V) :
    (Module.toModuleEnd k V : A →+* Module.End k V) a v = a • v :=
  rfl

/-- Etingof et al., Definition 1.11: a subrepresentation is a subspace stable under the action. -/
@[kb "etingof2011" "Definition 1.11, p. 8"]
theorem etingof_1_11 {k G V : Type*} [Semiring k] [Monoid G] [AddCommMonoid V] [Module k V]
    {ρ : Representation k G V} (S : Subrepresentation ρ) (g : G) {v : V}
    (hv : v ∈ S.toSubmodule) : ρ g v ∈ S.toSubmodule :=
  S.apply_mem_toSubmodule g hv

/-- Etingof et al., Definition 1.12: a representation of a group is irreducible exactly when the
corresponding module over the group algebra is simple. -/
@[kb "etingof2011" "Definition 1.12, p. 8"]
theorem etingof_1_12 {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) : IsIrreducible ρ ↔ IsSimpleModule k[G] ρ.asModule :=
  irreducible_iff_isSimpleModule_asModule ρ

/-- Etingof et al., Definition 1.13: an intertwining operator commutes with the group action. -/
@[kb "etingof2011" "Definition 1.13, p. 8"]
theorem etingof_1_13 {k G V W : Type*} [Semiring k] [Monoid G] [AddCommMonoid V]
    [AddCommMonoid W] [Module k V] [Module k W] {ρ : Representation k G V}
    {σ : Representation k G W} (f : IntertwiningMap ρ σ) (g : G) (v : V) :
    f (ρ g v) = σ g (f v) :=
  IntertwiningMap.isIntertwining ρ σ f g v

/-- Etingof et al., Definition 1.14: the direct sum of two representations acts componentwise. -/
@[kb "etingof2011" "Definition 1.14, p. 8"]
theorem etingof_1_14 {k G V W : Type*} [Semiring k] [Monoid G] [AddCommMonoid V]
    [AddCommMonoid W] [Module k V] [Module k W] (ρ : Representation k G V)
    (σ : Representation k G W) (g : G) (v : V) (w : W) :
    (ρ.prod σ) g (v, w) = (ρ g v, σ g w) :=
  rfl

/-- Etingof et al., Proposition 1.16 (Schur's lemma): an intertwining operator between two
irreducible representations is either bijective or zero. -/
@[kb "etingof2011" "Proposition 1.16, p. 8"]
theorem etingof_1_16 {k G V W : Type*} [Field k] [Monoid G] [AddCommGroup V] [AddCommGroup W]
    [Module k V] [Module k W] {ρ : Representation k G V} {σ : Representation k G W}
    [IsIrreducible ρ] [IsIrreducible σ] (f : IntertwiningMap ρ σ) :
    Function.Bijective f ∨ f = 0 :=
  IsIrreducible.bijective_or_eq_zero f

/-- Etingof et al., Corollary 1.17: over an algebraically closed field, every intertwining
endomorphism of a finite-dimensional irreducible representation is a scalar. -/
@[kb "etingof2011" "Corollary 1.17, p. 9"]
theorem etingof_1_17 {k G V : Type*} [Field k] [IsAlgClosed k] [Monoid G] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (ρ : Representation k G V) [IsIrreducible ρ] :
    Function.Bijective (algebraMap k (IntertwiningMap ρ ρ)) :=
  IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed

/-- Etingof et al., Corollary 1.18: over an algebraically closed field, a finite-dimensional
irreducible representation of a commutative group is one-dimensional. -/
@[kb "etingof2011" "Corollary 1.18, p. 9"]
theorem etingof_1_18 {k G V : Type*} [Field k] [IsAlgClosed k] [CommGroup G] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (ρ : Representation k G V) [IsIrreducible ρ] :
    Module.finrank k V = 1 :=
  IsIrreducible.finrank_eq_one_of_isMulCommutative ρ

/-- Etingof et al., Example 1.19(3): representations of the group algebra are the same as
representations of the group, as an equivalence of categories `Rep k G ≌ Mod k[G]`. -/
@[kb "etingof2011" "Example 1.19(3), p. 10"]
theorem etingof_1_19_3 {k G : Type u} [CommRing k] [Monoid G] :
    Nonempty (Rep.{u} k G ≌ ModuleCat.{u} k[G]) :=
  ⟨Rep.equivalenceModuleMonoidAlgebra⟩

/-- Etingof et al., Problem 1.22: the endomorphism algebra of an algebra as a module over itself
is the opposite algebra. -/
@[kb "etingof2011" "Problem 1.22, p. 10"]
theorem etingof_1_22 (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] :
    Nonempty (Aᵐᵒᵖ ≃ₐ[R] Module.End A A) :=
  ⟨AlgEquiv.moduleEndSelf R⟩

/-- Etingof et al., Section 1.4: left ideals of a ring are exactly its submodules as a module
over itself, i.e. the subrepresentations of the regular representation. -/
@[kb "etingof2011" "§1.4, p. 10"]
theorem etingof_sec_1_4_a (R : Type*) [Semiring R] : Ideal R = Submodule R R :=
  rfl

/-- Etingof et al., Section 1.4: a ring is simple when its only two-sided ideals are zero and the
whole ring. -/
@[kb "etingof2011" "§1.4, p. 10"]
theorem etingof_sec_1_4_b (R : Type*) [NonUnitalNonAssocRing R] :
    IsSimpleRing R ↔ IsSimpleOrder (TwoSidedIdeal R) :=
  isSimpleRing_iff R

/-- Etingof et al., Section 1.5: the quotient of a representation by a subrepresentation is
a representation, acting on classes by acting on representatives. -/
@[kb "etingof2011" "§1.5, p. 11"]
theorem etingof_sec_1_5 {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
    {ρ : Representation k G V} (S : Subrepresentation ρ) (g : G) (w : V) :
    S.quotient g (Submodule.Quotient.mk w) = Submodule.Quotient.mk (ρ g w) :=
  Subrepresentation.quotient_apply_mk S g w

/-- Etingof et al., Section 1.6: an algebra given by generators and relations is a quotient of the
free algebra, and the quotient map is surjective. -/
@[kb "etingof2011" "§1.6, p. 11"]
theorem etingof_sec_1_6 {S A : Type*} [CommSemiring S] [Semiring A] [Algebra S A]
    (r : A → A → Prop) : Function.Surjective (RingQuot.mkAlgHom S r) :=
  RingQuot.mkAlgHom_surjective S r

end Algebras

section Quivers

/-- Etingof et al., Definition 1.28: a quiver is a directed graph in which loops and multiple edges
are allowed; here is a quiver on one vertex with two distinct loops. -/
@[kb "etingof2011" "Definition 1.28, p. 13"]
theorem etingof_1_28 :
    ∃ Q : Quiver.{0, 0} Unit, ∃ e₁ e₂ : Q.Hom () (), e₁ ≠ e₂ :=
  ⟨⟨fun _ _ => Bool⟩, true, false, fun h => Bool.noConfusion h⟩

end Quivers

section LieAlgebras

attribute [local instance] LieRing.ofAssociativeRing

/-- Etingof et al., Definition 1.39: a Lie algebra has a skew-symmetric bracket satisfying the
Jacobi identity (stored in Mathlib in Leibniz form). -/
@[kb "etingof2011" "Definition 1.39, p. 15"]
theorem etingof_1_39 {L : Type*} [LieRing L] (x y z : L) :
    ⁅x, y⁆ = -⁅y, x⁆ ∧ ⁅x, x⁆ = 0 ∧ ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆ :=
  ⟨(lie_skew x y).symm, lie_self x, leibniz_lie x y z⟩

/-- Etingof et al., Section 1.9: three-dimensional space with the cross product satisfies the
Jacobi identity. -/
@[kb "etingof2011" "§1.9, p. 15"]
theorem etingof_sec_1_9_a {R : Type*} [CommRing R] (u v w : Fin 3 → R) :
    u ⨯₃ (v ⨯₃ w) = u ⨯₃ v ⨯₃ w + v ⨯₃ (u ⨯₃ w) :=
  leibniz_cross u v w

/-- Etingof et al., Definition 1.42: a Lie algebra homomorphism respects the bracket. -/
@[kb "etingof2011" "Definition 1.42, p. 16"]
theorem etingof_1_42 {R L₁ L₂ : Type*} [CommRing R] [LieRing L₁] [LieAlgebra R L₁] [LieRing L₂]
    [LieAlgebra R L₂] (f : L₁ →ₗ⁅R⁆ L₂) (x y : L₁) : f ⁅x, y⁆ = ⁅f x, f y⁆ :=
  LieHom.map_lie f x y

/-- Etingof et al., Definition 1.43: a representation of a Lie algebra is a Lie homomorphism to the
commutator Lie algebra of endomorphisms. -/
@[kb "etingof2011" "Definition 1.43, p. 16"]
theorem etingof_1_43 (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M]
    [Module R M] [LieRingModule L M] [LieModule R L M] (x y : L) :
    LieModule.toEnd R L M ⁅x, y⁆ = ⁅LieModule.toEnd R L M x, LieModule.toEnd R L M y⁆ :=
  LieHom.map_lie (LieModule.toEnd R L M) x y

/-- Etingof et al., Example 1.44: the adjoint representation sends `x` to `y ↦ [x, y]`. -/
@[kb "etingof2011" "Example 1.44, p. 16"]
theorem etingof_1_44 (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] (x y : L) :
    LieAlgebra.ad R L x y = ⁅x, y⁆ :=
  LieAlgebra.ad_apply R L x y

/-- Etingof et al., Definition 1.45: the universal enveloping algebra `U(g)` receives the Lie
algebra, and a Lie homomorphism `g → A` extends to an algebra homomorphism `U(g) → A`. -/
@[kb "etingof2011" "Definition 1.45, p. 16"]
theorem etingof_1_45 {R L A : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [Ring A]
    [Algebra R A] (f : L →ₗ⁅R⁆ A) (x : L) :
    UniversalEnvelopingAlgebra.lift R f (UniversalEnvelopingAlgebra.ι R x) = f x :=
  UniversalEnvelopingAlgebra.lift_ι_apply R f x

/-- Etingof et al., Section 1.9: algebra homomorphisms out of `U(g)` are determined by their
values on the generators, so a representation of `U(g)` is the same as one of `g`. -/
@[kb "etingof2011" "§1.9, p. 16"]
theorem etingof_sec_1_9_b {R L A : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [Ring A]
    [Algebra R A] {g₁ g₂ : UniversalEnvelopingAlgebra R L →ₐ[R] A}
    (h : g₁.toLieHom.comp (UniversalEnvelopingAlgebra.ι R) =
      g₂.toLieHom.comp (UniversalEnvelopingAlgebra.ι R)) : g₁ = g₂ :=
  UniversalEnvelopingAlgebra.hom_ext R h

end LieAlgebras

section Tensors

/-- Etingof et al., Definition 1.48: the tensor product is bilinear on pure tensors. -/
@[kb "etingof2011" "Definition 1.48, p. 17"]
theorem etingof_1_48 {k V W : Type*} [CommSemiring k] [AddCommMonoid V] [AddCommMonoid W]
    [Module k V] [Module k W] (c : k) (v v' : V) (w : W) :
    (c • v + v') ⊗ₜ[k] w = c • (v ⊗ₜ[k] w) + v' ⊗ₜ[k] w := by
  rw [TensorProduct.add_tmul, TensorProduct.smul_tmul']

/-- Etingof et al., Section 1.10: the tensor product of linear maps acts factor by factor on pure
tensors. -/
@[kb "etingof2011" "§1.10, p. 17"]
theorem etingof_sec_1_10 {k V W V' W' : Type*} [CommSemiring k] [AddCommMonoid V]
    [AddCommMonoid W] [AddCommMonoid V'] [AddCommMonoid W'] [Module k V] [Module k W]
    [Module k V'] [Module k W'] (f : V →ₗ[k] V') (g : W →ₗ[k] W') (v : V) (w : W) :
    TensorProduct.map f g (v ⊗ₜ[k] w) = f v ⊗ₜ[k] g w :=
  TensorProduct.map_tmul f g v w

/-- Etingof et al., Problem 1.49(a): bilinear maps `V × W → U` correspond to linear maps
`V ⊗ W → U`. -/
@[kb "etingof2011" "Problem 1.49(a)-(c), p. 18"]
theorem etingof_1_49_abc_a (k V W U : Type*) [CommRing k] [AddCommGroup V] [AddCommGroup W]
    [AddCommGroup U] [Module k V] [Module k W] [Module k U] :
    Nonempty ((V →ₗ[k] W →ₗ[k] U) ≃ₗ[k] (V ⊗[k] W →ₗ[k] U)) :=
  ⟨TensorProduct.lift.equiv (RingHom.id k) V W U⟩

/-- Etingof et al., Problem 1.49(b): the products of basis vectors form a basis of the tensor
product. -/
@[kb "etingof2011" "Problem 1.49(a)-(c), p. 18"]
theorem etingof_1_49_abc_b {k V W ι κ : Type*} [CommRing k] [AddCommGroup V] [AddCommGroup W]
    [Module k V] [Module k W] (b : Module.Basis ι k V) (c : Module.Basis κ k W) (i : ι) (j : κ) :
    Module.Basis.tensorProduct b c (i, j) = b i ⊗ₜ[k] c j :=
  Module.Basis.tensorProduct_apply b c i j

/-- Etingof et al., Problem 1.49(c): for finite-dimensional `V`, the space `V* ⊗ W` is isomorphic
to `Hom(V, W)`. -/
@[kb "etingof2011" "Problem 1.49(a)-(c), p. 18"]
theorem etingof_1_49_abc_c (k V W : Type*) [CommRing k] [AddCommGroup V] [AddCommGroup W]
    [Module k V] [Module k W] [Module.Finite k V] [Module.Free k V] :
    Nonempty (Module.Dual k V ⊗[k] W ≃ₗ[k] (V →ₗ[k] W)) :=
  ⟨dualTensorHomEquiv k V W⟩

/-- Etingof et al., Definition 1.50: for a vector space with a basis, the symmetric algebra is the
polynomial algebra on the basis. -/
@[kb "etingof2011" "Definition 1.50, p. 19"]
theorem etingof_1_50_a {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (b : Module.Basis I R M) : Nonempty (SymmetricAlgebra R M ≃ₐ[R] MvPolynomial I R) :=
  ⟨SymmetricAlgebra.equivMvPolynomial b⟩

/-- Etingof et al., Definition 1.50: in the exterior algebra every vector squares to zero. -/
@[kb "etingof2011" "Definition 1.50, p. 19"]
theorem etingof_1_50_b {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (m : M) :
    ExteriorAlgebra.ι R m * ExteriorAlgebra.ι R m = 0 :=
  ExteriorAlgebra.ι_sq_zero m

/-- Etingof et al., Definition 1.52: a Lie algebra acts on a tensor product of representations by
the Leibniz rule. -/
@[kb "etingof2011" "Definition 1.52, p. 20"]
theorem etingof_1_52 {R L M N : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M] [AddCommGroup N]
    [Module R N] [LieRingModule L N] [LieModule R L N] (x : L) (m : M) (n : N) :
    ⁅x, m ⊗ₜ[R] n⁆ = ⁅x, m⁆ ⊗ₜ[R] n + m ⊗ₜ[R] ⁅x, n⁆ :=
  TensorProduct.LieModule.lie_tmul_right x m n

/-- Etingof et al., Definition 1.53: a Lie algebra acts on the dual of a representation by
`(x · f)(m) = -f(x · m)`. -/
@[kb "etingof2011" "Definition 1.53, p. 20"]
theorem etingof_1_53 {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M]
    [Module R M] [LieRingModule L M] [LieModule R L M] (x : L) (f : M →ₗ[R] R) (m : M) :
    ⁅x, f⁆ m = -f ⁅x, m⁆ :=
  Module.Dual.lie_apply (L := L) (x := x) (m := m) f

end Tensors

end UndergradKB.RepresentationTheory.Course
