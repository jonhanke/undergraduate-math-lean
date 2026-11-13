import UndergradKB.RepresentationTheory.Sl2
import UndergradKB.RepresentationTheory.Sl2Reducibility
import UndergradKB.RepresentationTheory.Sl2Further
import UndergradKB.RepresentationTheory.AlgebrasMisc
import UndergradKB.RepresentationTheory.AlgebrasChapter1
import UndergradKB.RepresentationTheory.AlgebrasChapter2b
import UndergradKB.RepresentationTheory.JordanModules
import UndergradKB.RepresentationTheory.Basic
import UndergradKB.RepresentationTheory.Characters
import UndergradKB.RepresentationTheory.WeylAlgebra
import UndergradKB.RepresentationTheory.QWeylAlgebra
import UndergradKB.RepresentationTheory.PathAlgebraModules
import UndergradKB.RepresentationTheory.Quiver
import UndergradKB.RepresentationTheory.MixedTensors
import UndergradKB.RepresentationTheory.SymmetricPowers
import UndergradKB.RepresentationTheory.SymmetricPowersTrace
import UndergradKB.RepresentationTheory.BimoduleTensor
import UndergradKB.RepresentationTheory.TensorAlgebraRows
import UndergradKB.RepresentationTheory.GabrielConverse
import UndergradKB.Common.Attr

/-!
# Etingof et al., Introduction to Representation Theory: Chapter 1, results proved in this repository

Course names for the Chapter 1 items of the checklist that are proved by declarations of this
repository (as opposed to Mathlib; those are in `Course/Etingof1.lean`).  Each theorem restates a
repository theorem in the book's terms and is proved by it.  Each statement is tagged with the source
key `etingof2011` and the locator of the item in the book.
-/

namespace UndergradKB.RepresentationTheory.Course

open scoped TensorProduct
open Representation

universe u

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Etingof et al., Theorem 1.1: over an algebraically closed field of characteristic zero, a
finite-dimensional space with operators satisfying the `sl₂` relations is an internal direct sum of
invariant subspaces that are irreducible for the restricted operators. -/
@[kb "etingof2011" "Theorem 1.1, p. 5"]
theorem etingof_1_1_a {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    {h e f : Module.End k V} [FiniteDimensional k V] [CharZero k] [IsAlgClosed k]
    (r : Sl2.IsSl2Rel k h e f) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (S : ι → Submodule k V)
      (hS : ∀ i, Sl2.IsInv h e f (S i)),
      (∀ i, Sl2.IsIrreducibleRep (h.restrict (hS i).1) (e.restrict (hS i).2.1)
        (f.restrict (hS i).2.2)) ∧ DirectSum.IsInternal S :=
  Sl2.IsSl2Rel.exists_internal_irreducible r

/-- Etingof et al., Theorem 1.1: every invariant subspace of a finite-dimensional module over the
`sl₂` relations (over an algebraically closed field of characteristic zero) has an invariant
complement. -/
@[kb "etingof2011" "Theorem 1.1, p. 5"]
theorem etingof_1_1_b {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    {h e f : Module.End k V} [FiniteDimensional k V] [CharZero k] [IsAlgClosed k]
    (r : Sl2.IsSl2Rel k h e f) {W : Submodule k V} (hW : Sl2.IsInv h e f W) :
    ∃ W' : Submodule k V, Sl2.IsInv h e f W' ∧ IsCompl W W' :=
  Sl2.IsSl2Rel.complete_reducibility r hW

/-- Etingof et al., Theorem 1.1: for each `n` the standard module `k^(n+1)` is irreducible for the
`sl₂` relations, and every irreducible finite-dimensional module of dimension `n + 1` is isomorphic
to it. -/
@[kb "etingof2011" "Theorem 1.1, p. 5"]
theorem etingof_1_1_c {k : Type*} [Field k] [IsAlgClosed k] [CharZero k] (n : ℕ) :
    Sl2.IsIrreducibleRep (Sl2.stdH k n) (Sl2.stdE k n) (Sl2.stdF k n) ∧
      Module.finrank k (Fin (n + 1) → k) = n + 1 ∧
      ∀ {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
        (h e f : Module.End k V), Sl2.IsSl2Rel k h e f → Sl2.IsIrreducibleRep h e f →
        Module.finrank k V = n + 1 →
        ∃ φ : (Fin (n + 1) → k) ≃ₗ[k] V, (∀ x, φ (Sl2.stdH k n x) = h (φ x)) ∧
          (∀ x, φ (Sl2.stdE k n x) = e (φ x)) ∧ ∀ x, φ (Sl2.stdF k n x) = f (φ x) :=
  Sl2.irreducible_classification n

/-- Etingof et al., Example 1.10: a representation of the free algebra on a set `X` on `V` is the
same as an arbitrary choice of an operator on `V` for each element of `X`; the operator attached to
`x` is the image of the generator `x`. -/
@[kb "etingof2011" "Example 1.10, p. 8"]
theorem etingof_1_10 (k X V : Type*) [CommSemiring k] [AddCommMonoid V] [Module k V]
    (f : X → Module.End k V) (x : X) :
    ((freeAlgebraRepEquiv k X V) f) (FreeAlgebra.ι k x) = f x :=
  freeAlgebraRepEquiv_ι k X V f x

/-- Etingof et al., Example 1.19: over an algebraically closed field, every finite-dimensional
indecomposable module over `k[x]` is a Jordan block module `k[x]/(x - λ)^n`. -/
@[kb "etingof2011" "Example 1.19, p. 9"]
theorem etingof_1_19_a {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    [Module (Polynomial k) V] [IsScalarTower k (Polynomial k) V] [IsAlgClosed k]
    [FiniteDimensional k V] (hV : IsIndecomposableModule (Polynomial k) V) :
    ∃ lam n, 1 ≤ n ∧ Nonempty (V ≃ₗ[Polynomial k] JordanBlockModule k lam n) :=
  exists_linearEquiv_jordanBlock_of_isIndecomposableModule hV

/-- Etingof et al., Example 1.19: every Jordan block module `k[x]/(x - λ)^n` with `n ≥ 1` is
indecomposable. -/
@[kb "etingof2011" "Example 1.19, p. 9"]
theorem etingof_1_19_b {k : Type*} [Field k] (lam : k) {n : ℕ} (hn : 1 ≤ n) :
    IsIndecomposableModule (Polynomial k) (JordanBlockModule k lam n) :=
  isIndecomposableModule_jordanBlock lam hn

/-- Etingof et al., Example 1.19: a Jordan block module of size at least two is not irreducible, so
an indecomposable module need not be irreducible. -/
@[kb "etingof2011" "Example 1.19, p. 9"]
theorem etingof_1_19_c {k : Type*} [Field k] (lam : k) {n : ℕ} (hn : 2 ≤ n) :
    ¬IsSimpleModule (Polynomial k) (JordanBlockModule k lam n) :=
  not_isSimpleModule_jordanBlock lam hn

/-- Etingof et al., Example 1.19: over an algebraically closed field, a finite-dimensional
irreducible `k[x]`-module is one-dimensional, namely a Jordan block of size one. -/
@[kb "etingof2011" "Example 1.19, p. 9"]
theorem etingof_1_19_d {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    [Module (Polynomial k) V] [IsScalarTower k (Polynomial k) V] [IsAlgClosed k]
    [IsSimpleModule (Polynomial k) V] [FiniteDimensional k V] :
    ∃ lam, Nonempty (V ≃ₗ[Polynomial k] JordanBlockModule k lam 1) :=
  exists_linearEquiv_jordanBlock_one_of_isSimpleModule

/-- Etingof et al., Problem 1.20: every nonzero finite-dimensional representation of a group has an
irreducible subrepresentation. -/
@[kb "etingof2011" "Problem 1.20, p. 10"]
theorem etingof_1_20_a {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) [FiniteDimensional k V] [Nontrivial V] :
    ∃ W : Subrepresentation ρ, IsIrreducible W.toRepresentation :=
  exists_irreducible_subrepresentation ρ

/-- Etingof et al., Problem 1.20: a nonzero module over a `k`-algebra `A`, finite-dimensional over
`k`, has a simple submodule. -/
@[kb "etingof2011" "Problem 1.20, p. 10"]
theorem etingof_1_20_b {k : Type*} [Field k] (A M : Type*) [Ring A] [Algebra k A] [AddCommGroup M]
    [Module A M] [Module k M] [IsScalarTower k A M] [FiniteDimensional k M] [Nontrivial M] :
    ∃ N : Submodule A M, IsSimpleModule A N :=
  exists_isSimpleModule_submodule (k := k) A M

/-- Etingof et al., Problem 1.21: a central element of the algebra acts by a scalar on a
finite-dimensional irreducible module over an algebraically closed field. -/
@[kb "etingof2011" "Problem 1.21, p. 10"]
theorem etingof_1_21 (k : Type*) {A M : Type*} [Field k] [Ring A] [Algebra k A] [AddCommGroup M]
    [Module A M] [Module k M] [IsScalarTower k A M] [FiniteDimensional k M] [IsSimpleModule A M]
    [IsAlgClosed k] (z : A) (hz : z ∈ Subalgebra.center k A) :
    ∃ c : k, ∀ m : M, z • m = c • m :=
  exists_smul_eq_of_mem_center k z hz

/-- Etingof et al., Problem 1.23 (Dixmier's lemma): for an irreducible module of countable
dimension over a complex algebra, every module endomorphism is a scalar. -/
@[kb "etingof2011" "Problem 1.23, p. 10"]
theorem etingof_1_23 {A : Type*} {V : Type u} [Ring A] [Algebra ℂ A] [AddCommGroup V] [Module ℂ V]
    [Module A V] [IsScalarTower ℂ A V] [IsSimpleModule A V]
    (hV : Module.rank ℂ V ≤ Cardinal.aleph0) (φ : Module.End A V) :
    ∃ c : ℂ, φ = algebraMap ℂ (Module.End A V) c :=
  exists_eq_algebraMap_of_rank_le_aleph0 hV φ

/-- Etingof et al., Problem 1.25: a module is cyclic exactly when it is isomorphic to the quotient
of the algebra by a left ideal. -/
@[kb "etingof2011" "Problem 1.25, p. 11"]
theorem etingof_1_25 (A : Type*) {M : Type*} [Ring A] [AddCommGroup M] [Module A M] :
    IsCyclicModule A M ↔ ∃ I : Ideal A, Nonempty ((A ⧸ I) ≃ₗ[A] M) :=
  isCyclic_iff_exists_quotient_equiv A

/-- Etingof et al., §1.7: in the Weyl algebra the generators satisfy `y x = x y + 1`. -/
@[kb "etingof2011" "§1.7, p. 11"]
theorem etingof_sec_1_7_a {k : Type*} [CommRing k] :
    weylY k * weylX k = weylX k * weylY k + 1 :=
  weylY_mul_weylX

/-- Etingof et al., §1.7: in the `q`-Weyl algebra the generators satisfy `y x = q x y`. -/
@[kb "etingof2011" "§1.7, p. 11"]
theorem etingof_sec_1_7_b {k : Type*} [CommRing k] {q : kˣ} :
    qWeylY k q * qWeylX k q = (q : k) • (qWeylX k q * qWeylY k q) :=
  qWeylY_mul_qWeylX

/-- Etingof et al., §1.7: over a field of characteristic zero the monomials `x^i y^j` with
`i, j ≥ 0` are linearly independent in the Weyl algebra. -/
@[kb "etingof2011" "§1.7, p. 11"]
theorem etingof_sec_1_7_c {k : Type*} [Field k] [CharZero k] :
    LinearIndependent k fun p : ℕ × ℕ => weylX k ^ p.1 * weylY k ^ p.2 :=
  weyl_linearIndependent

/-- Etingof et al., §1.7: the monomials `x^i y^j` with `i, j ≥ 0` span the Weyl algebra. -/
@[kb "etingof2011" "§1.7, p. 11"]
theorem etingof_sec_1_7_d {k : Type*} [CommRing k] :
    Submodule.span k (Set.range fun p : ℕ × ℕ => weylX k ^ p.1 * weylY k ^ p.2) = ⊤ :=
  weyl_span

/-- Etingof et al., §1.7: the monomials `x^i y^j` with `i, j` integers are linearly independent in
the `q`-Weyl algebra. -/
@[kb "etingof2011" "§1.7, p. 11"]
theorem etingof_sec_1_7_e {k : Type*} [CommRing k] {q : kˣ} :
    LinearIndependent k fun p : ℤ × ℤ => qWeylMon k q p.1 p.2 :=
  qWeyl_linearIndependent

/-- Etingof et al., §1.7: the monomials `x^i y^j` with `i, j` integers span the `q`-Weyl algebra. -/
@[kb "etingof2011" "§1.7, p. 11"]
theorem etingof_sec_1_7_f {k : Type*} [CommRing k] {q : kˣ} :
    Submodule.span k (Set.range fun p : ℤ × ℤ => qWeylMon k q p.1 p.2) = ⊤ :=
  qWeyl_span

/-- Etingof et al., §1.7: the left regular representation of a group is faithful. -/
@[kb "etingof2011" "§1.7, p. 12"]
theorem etingof_sec_1_7_g {k G : Type*} [Semiring k] [Monoid G] [Nontrivial k] :
    IsFaithful (Representation.ofMulAction k G G) :=
  isFaithful_ofMulAction_self

/-- Etingof et al., §1.8: the quiver representation attached to the total space of a quiver
representation is isomorphic to the original one. -/
@[kb "etingof2011" "§1.8, p. 14"]
theorem etingof_sec_1_8_a (k : Type*) [Field k] {Q : Type*} [Quiver Q] [DecidableEq Q] [Fintype Q]
    (V : QRep k Q) : (QRep.ofModule k Q V.Total).Isomorphic V :=
  QRep.ofModule_total_isomorphic k V

/-- Etingof et al., §1.8: an irreducible quiver representation is indecomposable. -/
@[kb "etingof2011" "§1.8, p. 14"]
theorem etingof_sec_1_8_b {k : Type*} {Q : Type*} [Field k] [Quiver Q] {V : QRep k Q}
    (h : V.IsIrreducible) : V.IsIndecomposable :=
  QRep.IsIrreducible.isIndecomposable h

/-- Etingof et al., Example 1.40: the commutator of two derivations of a commutative algebra is the
commutator of the corresponding operators. -/
@[kb "etingof2011" "Example 1.40, p. 15"]
theorem etingof_1_40 (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    (D₁ D₂ : Derivation R A A) :
    ((⁅D₁, D₂⁆ : Derivation R A A) : Module.End R A) = (D₁ : Module.End R A) * D₂ - D₂ * D₁ :=
  derivation_commutator R A D₁ D₂

/-- Etingof et al., §1.9: the matrices `e`, `f`, `h` form an `sl₂`-triple. -/
@[kb "etingof2011" "§1.9, p. 15"]
theorem etingof_sec_1_9_c {k : Type*} [CommRing k] [Nontrivial k] [NeZero (2 : k)] :
    IsSl2Triple (sl2H k) (sl2E k) (sl2F k) :=
  isSl2Triple_sl2

/-- Etingof et al., §1.9: the matrices `e`, `f`, `h` have trace zero. -/
@[kb "etingof2011" "§1.9, p. 15"]
theorem etingof_sec_1_9_d {k : Type*} [CommRing k] :
    sl2E k ∈ LieAlgebra.SpecialLinear.sl (Fin 2) k ∧
      sl2F k ∈ LieAlgebra.SpecialLinear.sl (Fin 2) k ∧
        sl2H k ∈ LieAlgebra.SpecialLinear.sl (Fin 2) k :=
  sl2_mem_sl

/-- Etingof et al., §1.9: in the Heisenberg algebra `[x, y] = c`. -/
@[kb "etingof2011" "§1.9, p. 16"]
theorem etingof_sec_1_9_e {k : Type*} [CommRing k] : ⁅heisX k, heisY k⁆ = heisC k :=
  heis_lie_x_y

/-- Etingof et al., §1.9: in the Heisenberg algebra `x` commutes with `c`. -/
@[kb "etingof2011" "§1.9, p. 16"]
theorem etingof_sec_1_9_f {k : Type*} [CommRing k] : ⁅heisX k, heisC k⁆ = 0 :=
  heis_lie_x_c

/-- Etingof et al., §1.9: in the Heisenberg algebra `y` commutes with `c`. -/
@[kb "etingof2011" "§1.9, p. 16"]
theorem etingof_sec_1_9_g {k : Type*} [CommRing k] : ⁅heisY k, heisC k⁆ = 0 :=
  heis_lie_y_c

/-- Etingof et al., §1.9: the strictly upper triangular matrices are exactly the combinations of
`x`, `y`, `c`. -/
@[kb "etingof2011" "§1.9, p. 16"]
theorem etingof_sec_1_9_h {k : Type*} [CommRing k] (M : Matrix (Fin 3) (Fin 3) k) :
    M ∈ heisenberg k ↔ ∃ a b c : k, M = a • heisX k + b • heisY k + c • heisC k :=
  mem_heisenberg_iff M

/-- Etingof et al., §1.9: the elements `x`, `y`, `c` of the Heisenberg algebra are linearly
independent. -/
@[kb "etingof2011" "§1.9, p. 16"]
theorem etingof_sec_1_9_i {k : Type*} [CommRing k] [Nontrivial k] :
    LinearIndependent k ![heisX k, heisY k, heisC k] :=
  heis_linearIndependent

/-- Etingof et al., §1.9: in the two-dimensional Lie algebra `aff(1)` one has `[X, Y] = Y`. -/
@[kb "etingof2011" "§1.9, p. 16"]
theorem etingof_sec_1_9_j {k : Type*} [CommRing k] : ⁅aff1X k, aff1Y k⁆ = aff1Y k :=
  aff1_lie_X_Y

/-- Etingof et al., §1.9: the bracket of `X` and `Y` in `aff(1)` is nonzero, so this algebra is not
abelian. -/
@[kb "etingof2011" "§1.9, p. 16"]
theorem etingof_sec_1_9_k {k : Type*} [CommRing k] [Nontrivial k] : ⁅aff1X k, aff1Y k⁆ ≠ 0 :=
  aff1_lie_ne_zero

/-- Etingof et al., §1.9: the matrix attached to a vector in `R³` is skew-symmetric. -/
@[kb "etingof2011" "§1.9, p. 16"]
theorem etingof_sec_1_9_l (R : Type*) [CommRing R] (v : Fin 3 → R) :
    crossMatrix R v ∈ LieAlgebra.Orthogonal.so (Fin 3) R :=
  crossMatrix_mem_so R v

/-- Etingof et al., §1.9: the commutator of two such skew-symmetric matrices is the matrix of the
cross product. -/
@[kb "etingof2011" "§1.9, p. 16"]
theorem etingof_sec_1_9_m (R : Type*) [CommRing R] (v w : Fin 3 → R) :
    ⁅crossMatrix R v, crossMatrix R w⁆ = crossMatrix R (crossProduct v w) :=
  crossMatrix_lie R v w

/-- Etingof et al., §1.9: every skew-symmetric `3 × 3` matrix comes from a unique vector, so
`so(3)` is the space `R³` with the cross product. -/
@[kb "etingof2011" "§1.9, p. 16"]
theorem etingof_sec_1_9_n (R : Type*) [CommRing R] [NoZeroDivisors R] [CharZero R]
    (A : Matrix (Fin 3) (Fin 3) R) (hA : A ∈ LieAlgebra.Orthogonal.so (Fin 3) R) :
    ∃! v : Fin 3 → R, crossMatrix R v = A :=
  exists_unique_crossMatrix_of_mem_so R A hA

/-- Etingof et al., Example 1.47: any algebra map out of the enveloping algebra of the Heisenberg
algebra sending `c` to `1` factors uniquely through the Weyl algebra. -/
@[kb "etingof2011" "Example 1.47, p. 16"]
theorem etingof_1_47 {k : Type*} [CommRing k] {L : Type*} [LieRing L] [LieAlgebra k L]
    {b : Module.Basis (Fin 3) k L} (hb : IsHeisBasis b) {A : Type*} [Ring A] [Algebra k A]
    (g : UniversalEnvelopingAlgebra k L →ₐ[k] A) (hg : g (UniversalEnvelopingAlgebra.ι k (b 2)) = 1) :
    ∃! g' : WeylAlgebra k →ₐ[k] A, g'.comp (heisUToWeyl hb) = g :=
  weyl_universal_of_heisU hb g hg

/-- Etingof et al., §1.10: the basis of mixed tensors built from a basis of `V` and its dual
basis. -/
@[kb "etingof2011" "§1.10, p. 17"]
theorem etingof_sec_1_10_a {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k V) (m n : ℕ) (p : Fin n → ι)
    (q : Fin m → ι) :
    (mixedTensorBasis b m n) (p, q) =
      ((PiTensorProduct.tprod k) fun i => b (p i)) ⊗ₜ[k]
        (PiTensorProduct.tprod k) fun j => b.dualBasis (q j) :=
  mixedTensorBasis_apply b m n p q

/-- Etingof et al., §1.10: the space of tensors of type `(m, n)` has dimension `(dim V)^(n+m)`. -/
@[kb "etingof2011" "§1.10, p. 17"]
theorem etingof_sec_1_10_b {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (m n : ℕ) :
    Module.finrank k (MixedTensor k V m n) = Module.finrank k V ^ (n + m) :=
  finrank_mixedTensor m n

/-- Etingof et al., Problem 1.49(d): the `n`-th symmetric power of a finite-dimensional space has
dimension `choose (dim V + n - 1, n)`. -/
@[kb "etingof2011" "Problem 1.49(d), p. 18"]
theorem etingof_1_49_d_a {k : Type} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (n : ℕ) :
    Module.finrank k (SymmetricPower k (Fin n) V) = (Module.finrank k V + n - 1).choose n :=
  finrank_symmetricPower n

/-- Etingof et al., Problem 1.49(d): the `n`-th exterior power of a finite-dimensional space has
dimension `choose (dim V, n)`. -/
@[kb "etingof2011" "Problem 1.49(d), p. 18"]
theorem etingof_1_49_d_b {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (n : ℕ) :
    Module.finrank k (⋀[k]^n V) = (Module.finrank k V).choose n :=
  finrank_exteriorPower_eq n

/-- Etingof et al., Problem 1.49(e): in characteristic zero the symmetric tensors map bijectively
onto the symmetric power. -/
@[kb "etingof2011" "Problem 1.49(e)-(g), p. 18"]
theorem etingof_1_49_e_a {k : Type} [Field k] [CharZero k] {n : ℕ} {V : Type*} [AddCommGroup V]
    [Module k V] :
    Function.Bijective ⇑(SymmetricPower.mk k (Fin n) V ∘ₗ (symmetricTensors k n V).subtype) :=
  symmetricTensors_mk_bijective

/-- Etingof et al., Problem 1.49(e): in characteristic zero the antisymmetric tensors map
bijectively onto the exterior power, via the antisymmetrisation projection. -/
@[kb "etingof2011" "Problem 1.49(e)-(g), p. 18"]
theorem etingof_1_49_e_b {k : Type*} [Field k] [CharZero k] {n : ℕ} {V : Type*} [AddCommGroup V]
    [Module k V] :
    Function.Bijective ⇑(antiProj ∘ₗ (antisymmetricTensors k n V).subtype) :=
  antisymmetricTensors_antiProj_bijective

/-- Etingof et al., Problem 1.49(f): for a diagonalisable operator, the trace on the `n`-th
symmetric power is the sum over multisets of the products of eigenvalues. -/
@[kb "etingof2011" "Problem 1.49(e)-(g), p. 18"]
theorem etingof_1_49_e_c {k : Type} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type*}
    [AddCommGroup V] [Module k V] (b : Module.Basis ι k V) (n : ℕ) (x : ι → k) (A : V →ₗ[k] V)
    (hA : ∀ i, A (b i) = x i • b i) :
    LinearMap.trace k (SymmetricPower k (Fin n) V) (symMap n A) =
      ∑ m : Sym ι n, (Multiset.map x (m : Multiset ι)).prod :=
  trace_symMap_of_diagonal b n x A hA

/-- Etingof et al., Problem 1.49(f): the trace of the `n`-th exterior power of an operator is the
sum of its principal `n × n` minors. -/
@[kb "etingof2011" "Problem 1.49(e)-(g), p. 18"]
theorem etingof_1_49_e_d {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M] [LinearOrder I]
    [Fintype I] (n : ℕ) (b : Module.Basis I R M) (f : M →ₗ[R] M) :
    LinearMap.trace R (⋀[R]^n M) (exteriorPower.map n f) =
      ∑ s : Set.powersetCard I n,
        (Matrix.of fun i j =>
            LinearMap.toMatrix b b f ((Set.powersetCard.ofFinEmbEquiv.symm s) i)
              ((Set.powersetCard.ofFinEmbEquiv.symm s) j)).det :=
  trace_exteriorPower_map n b f

/-- Etingof et al., Problem 1.49(g): the top exterior power of an `N`-dimensional space is acted on
by an operator through its determinant. -/
@[kb "etingof2011" "Problem 1.49(e)-(g), p. 18"]
theorem etingof_1_49_e_e {k V : Type*} [Field k] [AddCommGroup V] [Module k V] {N : ℕ}
    (b : Module.Basis (Fin N) k V) (f : V →ₗ[k] V) :
    exteriorPower.map N f (exteriorPower.ιMulti k N ⇑b) =
      LinearMap.det f • exteriorPower.ιMulti k N ⇑b :=
  exteriorPower_top_map b f

/-- Etingof et al., Problem 1.49(g): multiplicativity of the determinant, deduced from the top
exterior power. -/
@[kb "etingof2011" "Problem 1.49(e)-(g), p. 18"]
theorem etingof_1_49_e_f {k V : Type*} [Field k] [AddCommGroup V] [Module k V] {N : ℕ}
    (b : Module.Basis (Fin N) k V) (f g : V →ₗ[k] V) :
    LinearMap.det (f ∘ₗ g) = LinearMap.det f * LinearMap.det g :=
  det_comp_via_exteriorPower b f g

/-- Etingof et al., exercise after Problem 1.49: the associativity isomorphism of balanced tensor
products of bimodules commutes with the outer left action. -/
@[kb "etingof2011" "Exercise after Problem 1.49, p. 18"]
theorem etingof_1_49_exercise_a {k : Type*} [CommRing k] {B : Type*} {C : Type*} [Ring B] [Ring C]
    {M : Type*} {N : Type*} {P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module k M] [Module k N] [Module k P] [Module Bᵐᵒᵖ M] [Module B N] [Module Cᵐᵒᵖ N]
    [Module C P] [SMulCommClass B Cᵐᵒᵖ N] [SMulCommClass B k N] [SMulCommClass Cᵐᵒᵖ k N]
    {A : Type*} [Semiring A] [Module A M] [SMulCommClass A Bᵐᵒᵖ M] [SMulCommClass A k M] (a : A)
    (x : BalTensor k C (BalTensor k B M N) P) :
    (BalTensor.assocEquiv k B C M N P) (a • x) = a • (BalTensor.assocEquiv k B C M N P) x :=
  BalTensor.assocEquiv_smul_left a x

/-- Etingof et al., exercise after Problem 1.49: the associativity isomorphism of balanced tensor
products of bimodules commutes with the outer right action. -/
@[kb "etingof2011" "Exercise after Problem 1.49, p. 18"]
theorem etingof_1_49_exercise_b {k : Type*} [CommRing k] {B : Type*} {C : Type*} [Ring B] [Ring C]
    {M : Type*} {N : Type*} {P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module k M] [Module k N] [Module k P] [Module Bᵐᵒᵖ M] [Module B N] [Module Cᵐᵒᵖ N]
    [Module C P] [SMulCommClass B Cᵐᵒᵖ N] [SMulCommClass B k N] [SMulCommClass Cᵐᵒᵖ k N]
    {D : Type*} [Semiring D] [Module D P] [SMulCommClass C D P] [SMulCommClass D k P] (d : D)
    (x : BalTensor k C (BalTensor k B M N) P) :
    (BalTensor.assocEquiv k B C M N P) (d • x) = d • (BalTensor.assocEquiv k B C M N P) x :=
  BalTensor.assocEquiv_smul_right d x

/-- Etingof et al., Problem 1.55(a)-(f): a primitive vector of a finite-dimensional `sl₂`-module in
characteristic zero has a natural number as its weight. -/
@[kb "etingof2011" "Problem 1.55(a)-(f), p. 20"]
theorem etingof_1_55_af_a {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    {h e f : Module.End k V} {v : V} {μ : k} [FiniteDimensional k V] [CharZero k]
    (r : Sl2.IsSl2Rel k h e f) (hv : Sl2.IsPrimitive h e v μ) : ∃ n : ℕ, μ = n :=
  Sl2.IsSl2Rel.exists_nat_weight r hv

/-- Etingof et al., Problem 1.55(a)-(f): the explicit matrix coefficients of `h`, `e`, `f` on the
vectors obtained from a primitive vector of weight `n` by applying `f`. -/
@[kb "etingof2011" "Problem 1.55(a)-(f), p. 20"]
theorem etingof_1_55_af_b {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    {h e f : Module.End k V} {v : V} {μ : k} [FiniteDimensional k V] [CharZero k]
    (r : Sl2.IsSl2Rel k h e f) (hv : Sl2.IsPrimitive h e v μ) {n : ℕ} (hn : μ = n) :
    (∀ i : ℕ, h ((f ^ i) v) = ((n : k) - 2 * i) • (f ^ i) v) ∧
      (∀ i : ℕ, f ((f ^ i) v) = (f ^ (i + 1)) v) ∧
        (f ^ (n + 1)) v = 0 ∧ e v = 0 ∧
          ∀ i : ℕ, e ((f ^ (i + 1)) v) = (((i : k) + 1) * ((n : k) - i)) • (f ^ i) v :=
  Sl2.IsSl2Rel.matrix_coefficients r hv hn

/-- Etingof et al., Problem 1.55(a)-(f): two irreducible finite-dimensional `sl₂`-modules of the
same dimension are isomorphic. -/
@[kb "etingof2011" "Problem 1.55(a)-(f), p. 20"]
theorem etingof_1_55_af_c {k : Type*} [Field k] {V W : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] {h e f : Module.End k V} {h' e' f' : Module.End k W}
    [FiniteDimensional k V] [FiniteDimensional k W] [CharZero k] [IsAlgClosed k]
    (r : Sl2.IsSl2Rel k h e f) (hirr : Sl2.IsIrreducibleRep h e f) (r' : Sl2.IsSl2Rel k h' e' f')
    (hirr' : Sl2.IsIrreducibleRep h' e' f') (hdim : Module.finrank k V = Module.finrank k W) :
    ∃ φ : V ≃ₗ[k] W, (∀ x, φ (h x) = h' (φ x)) ∧ (∀ x, φ (e x) = e' (φ x)) ∧
      ∀ x, φ (f x) = f' (φ x) :=
  Sl2.exists_linearEquiv_of_finrank_eq r hirr r' hirr' hdim

/-- Etingof et al., Problem 1.55(a)-(f): the standard module with the explicit matrices is an
irreducible representation of the `sl₂` relations. -/
@[kb "etingof2011" "Problem 1.55(a)-(f), p. 20"]
theorem etingof_1_55_af_d {k : Type*} [Field k] {n : ℕ} [IsAlgClosed k] [CharZero k] :
    Sl2.IsIrreducibleRep (Sl2.stdH k n) (Sl2.stdE k n) (Sl2.stdF k n) :=
  Sl2.isIrreducibleRep_std

/-- Etingof et al., Problem 1.55(g)-(k): complete reducibility of finite-dimensional `sl₂`-modules,
every invariant subspace has an invariant complement. -/
@[kb "etingof2011" "Problem 1.55(g)-(k), p. 21"]
theorem etingof_1_55_gk_a {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    {h e f : Module.End k V} [FiniteDimensional k V] [CharZero k] [IsAlgClosed k]
    (r : Sl2.IsSl2Rel k h e f) {W : Submodule k V} (hW : Sl2.IsInv h e f W) :
    ∃ W' : Submodule k V, Sl2.IsInv h e f W' ∧ IsCompl W W' :=
  Sl2.IsSl2Rel.complete_reducibility r hW

/-- Etingof et al., Problem 1.55(g)-(k): the Casimir element of the `sl₂` relations commutes with
`e`, `f` and `h`. -/
@[kb "etingof2011" "Problem 1.55(g)-(k), p. 21"]
theorem etingof_1_55_gk_b {k : Type*} {A : Type*} [Field k] [Ring A] [Algebra k A] {h e f : A}
    [CharZero k] (r : Sl2.IsSl2Rel k h e f) :
    Commute (Sl2.casimir k h e f) e ∧ Commute (Sl2.casimir k h e f) f ∧
      Commute (Sl2.casimir k h e f) h :=
  Sl2.IsSl2Rel.casimir_central r

/-- Etingof et al., Problem 1.55(g)-(k): on a module generated by a primitive vector of weight `μ`
the Casimir element acts as the scalar `μ (μ + 2) / 2`. -/
@[kb "etingof2011" "Problem 1.55(g)-(k), p. 21"]
theorem etingof_1_55_gk_c {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    {h e f : Module.End k V} {v : V} {μ : k} [CharZero k] (r : Sl2.IsSl2Rel k h e f)
    (hv : Sl2.IsPrimitive h e v μ)
    (hspan : Submodule.span k (Set.range fun i : ℕ => (f ^ i) v) = ⊤) :
    Sl2.casimir k h e f = (μ * (μ + 2) / 2) • (1 : Module.End k V) :=
  Sl2.IsSl2Rel.casimir_eq_smul_one r hv hspan

/-- Etingof et al., Problem 1.55(l): a nilpotent operator on a finite-dimensional space is the
`e`-operator of some representation of the `sl₂` relations. -/
@[kb "etingof2011" "Problem 1.55(l), p. 21"]
theorem etingof_1_55_l {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (E : Module.End k V) (hE : IsNilpotent E) :
    ∃ H F : Module.End k V, Sl2.IsSl2Rel k H E F :=
  Sl2.exists_sl2_of_isNilpotent E hE

/-- Etingof et al., Problem 1.55(m): the Clebsch-Gordan decomposition of the tensor product of the
standard modules `V_l` and `V_m` into irreducible summands of dimensions `l + m - 2i + 1`. -/
@[kb "etingof2011" "Problem 1.55(m), p. 21"]
theorem etingof_1_55_m_a {k : Type*} [Field k] [CharZero k] [IsAlgClosed k] (l m : ℕ) :
    ∃ (S : Fin (min l m + 1) → Submodule k
        (TensorProduct k (Fin (l + 1) → k) (Fin (m + 1) → k)))
      (hS : ∀ i, Sl2.IsInv (Sl2.tensorOp (Sl2.stdH k l) (Sl2.stdH k m))
        (Sl2.tensorOp (Sl2.stdE k l) (Sl2.stdE k m))
        (Sl2.tensorOp (Sl2.stdF k l) (Sl2.stdF k m)) (S i)),
      (∀ i, Sl2.IsIrreducibleRep ((Sl2.tensorOp (Sl2.stdH k l) (Sl2.stdH k m)).restrict (hS i).1)
        ((Sl2.tensorOp (Sl2.stdE k l) (Sl2.stdE k m)).restrict (hS i).2.1)
        ((Sl2.tensorOp (Sl2.stdF k l) (Sl2.stdF k m)).restrict (hS i).2.2)) ∧
      DirectSum.IsInternal S ∧
      ∀ i, Module.finrank k (S i) = l + m - 2 * (i : ℕ) + 1 :=
  Sl2.clebsch_gordan l m

/-- Etingof et al., Problem 1.55(m): the multiplicity count in the Clebsch-Gordan decomposition,
the summand of dimension `c + 1` occurs once exactly when `c = l + m - 2i` with `0 ≤ i ≤ min l m`
and not otherwise. -/
@[kb "etingof2011" "Problem 1.55(m), p. 21"]
theorem etingof_1_55_m_b {k : Type*} [Field k] [CharZero k] [IsAlgClosed k] (l m : ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (S : ι → Submodule k
        (TensorProduct k (Fin (l + 1) → k) (Fin (m + 1) → k)))
      (hS : ∀ i, Sl2.IsInv (Sl2.tensorOp (Sl2.stdH k l) (Sl2.stdH k m))
        (Sl2.tensorOp (Sl2.stdE k l) (Sl2.stdE k m))
        (Sl2.tensorOp (Sl2.stdF k l) (Sl2.stdF k m)) (S i)),
      (∀ i, Sl2.IsIrreducibleRep ((Sl2.tensorOp (Sl2.stdH k l) (Sl2.stdH k m)).restrict (hS i).1)
        ((Sl2.tensorOp (Sl2.stdE k l) (Sl2.stdE k m)).restrict (hS i).2.1)
        ((Sl2.tensorOp (Sl2.stdF k l) (Sl2.stdF k m)).restrict (hS i).2.2)) ∧
      DirectSum.IsInternal S ∧
      ∃ n : ι → ℕ, (∀ j, Module.finrank k (S j) = n j + 1) ∧ ∀ c : ℕ,
        Fintype.card {j // n j = c} =
          if c ≤ l + m ∧ (l + m - c) % 2 = 0 ∧ (l + m - c) / 2 ≤ min l m then 1 else 0 :=
  Sl2.clebsch_gordan_count l m

/-- Etingof et al., Problem 1.56 (Lie's theorem): a finite-dimensional irreducible representation
of a solvable Lie algebra over an algebraically closed field of characteristic zero is
one-dimensional. -/
@[kb "etingof2011" "Problem 1.56, p. 21"]
theorem etingof_1_56 {k L V : Type*} [Field k] [IsAlgClosed k] [CharZero k] [LieRing L]
    [LieAlgebra k L] [AddCommGroup V] [Module k V] [LieRingModule L V] [LieModule k L V]
    [Module.Finite k V] [LieAlgebra.IsSolvable L] [LieModule.IsIrreducible k L V] :
    Module.finrank k V = 1 :=
  finrank_eq_one_of_isIrreducible_of_isSolvable (L := L)

/-- Etingof et al., Example 1.46: the algebra with generators `h, e, f` and the three `sl₂`
relations is isomorphic, as an algebra, to the universal enveloping algebra of any Lie algebra with
a basis `h, e, f` having the `sl₂` brackets. -/
@[kb "etingof2011" "Example 1.46, p. 16"]
theorem etingof_1_46_a {k : Type*} [Field k] {L : Type*} [LieRing L] [LieAlgebra k L]
    (b : Module.Basis (Fin 3) k L) (hb : IsSl2Basis b) :
    Nonempty (Sl2Alg k ≃ₐ[k] UniversalEnvelopingAlgebra k L) :=
  ⟨sl2UEquiv hb⟩

/-- Etingof et al., Example 1.46: algebra maps out of the algebra presented by `h, e, f` with the
`sl₂` relations correspond bijectively to triples in the target algebra satisfying those
relations. -/
@[kb "etingof2011" "Example 1.46, p. 16"]
theorem etingof_1_46_b (k : Type*) [Field k] (A : Type*) [Ring A] [Algebra k A] :
    Nonempty ((Sl2Alg k →ₐ[k] A) ≃ {t : A × A × A // Sl2.IsSl2Rel k t.1 t.2.1 t.2.2}) :=
  ⟨sl2AlgHomEquiv k A⟩

/-- Etingof et al., §1.11: the tensor algebra of a module is, as an algebra, the direct sum of its
tensor powers with concatenation as multiplication. -/
@[kb "etingof2011" "§1.11, p. 19"]
theorem etingof_sec_1_11_a (R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M] :
    Nonempty (TensorAlgebra R M ≃ₐ[R] DirectSum ℕ (fun n => ⨂[R]^n M)) :=
  ⟨tensorAlgebraEquivDirectSum R M⟩

/-- Etingof et al., §1.11: a basis of a module identifies its tensor algebra with the free algebra
on the index set of the basis. -/
@[kb "etingof2011" "§1.11, p. 19"]
theorem etingof_sec_1_11_b {R M κ : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    (b : Module.Basis κ R M) : Nonempty (TensorAlgebra R M ≃ₐ[R] FreeAlgebra R κ) :=
  ⟨tensorAlgebraEquivFreeAlgebra b⟩

universe a

open scoped Classical in
/-- Etingof et al., Theorem 1.2 (Gabriel): over an infinite field, a connected finite quiver has
finitely many indecomposable representations exactly when it has no loops, no two arrows between
the same pair of vertices, and its underlying graph is a Dynkin diagram. -/
@[kb "etingof2011" "Theorem 1.2, p. 6"]
theorem etingof_1_2 {k : Type u} [Field k] {n : ℕ} [Infinite k] [Q : Quiver.{a} (Fin n)]
    [∀ i j : Fin n, Fintype (i ⟶ j)] (hc : (Gabriel.underlyingGraph Q).Connected) :
    Gabriel.IsFiniteType Q k ↔ (∀ i : Fin n, IsEmpty (i ⟶ i)) ∧
      (∀ i j : Fin n, Fintype.card (i ⟶ j) + Fintype.card (j ⟶ i) ≤ 1) ∧
      Roots.IsDynkin (Gabriel.underlyingGraph Q) :=
  Gabriel.gabriel_iff hc

end UndergradKB.RepresentationTheory.Course
