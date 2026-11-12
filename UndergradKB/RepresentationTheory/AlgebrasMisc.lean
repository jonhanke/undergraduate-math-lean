import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.Lie.Classical
import Mathlib.Algebra.Lie.LieTheorem
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.TensorAlgebra.Basis
import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.MatrixAlgebra
import UndergradKB.Common.Attr

/-! # Small gaps in chapters 1-2 of Etingof et al.

Thin statements, in the book's terms, closing the small missing pieces of rows that Mathlib covers only partly:
representations of the free algebra, derivations of an associative algebra as a Lie algebra, `so(3)` as the cross
product algebra, the tensor algebra, Lie's theorem for irreducible modules, the endomorphism ring as a free module,
the dual representation of an algebra and the Kronecker isomorphism of matrix algebras.
-/

namespace UndergradKB.RepresentationTheory

open Module TensorProduct

section FreeAlgebraRep

/-- **Etingof et al., Example 1.10**: a representation of the free algebra on a set `X` in a vector space `V` is
the same as an arbitrary family of operators on `V`, one for each generator. -/
@[kb "etingof2011" "Example 1.10, p. 8"]
noncomputable def freeAlgebraRepEquiv (k X V : Type*) [CommSemiring k] [AddCommMonoid V] [Module k V] :
    (X → Module.End k V) ≃ (FreeAlgebra k X →ₐ[k] Module.End k V) :=
  FreeAlgebra.lift k

/-- The representation of the free algebra attached to a family of operators sends each generator to its
operator. -/
theorem freeAlgebraRepEquiv_ι (k X V : Type*) [CommSemiring k] [AddCommMonoid V] [Module k V]
    (f : X → Module.End k V) (x : X) : freeAlgebraRepEquiv k X V f (FreeAlgebra.ι k x) = f x :=
  FreeAlgebra.lift_ι_apply f x

end FreeAlgebraRep

section DerivationLie

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]

/-- **Etingof et al., Example 1.40**: the derivations of an algebra `A` are closed under the commutator
bracket of endomorphisms, so that `Der(A)` is a Lie subalgebra of `End A`; here the bracket of two derivations is
a derivation whose underlying linear map is the commutator of the two underlying maps. -/
@[kb "etingof2011" "Example 1.40, p. 15"]
theorem derivation_commutator (D₁ D₂ : Derivation R A A) :
    ((⁅D₁, D₂⁆ : Derivation R A A) : Module.End R A) = (D₁ : Module.End R A) * D₂ - D₂ * D₁ := by
  rw [Derivation.commutator_coe_linear_map]
  rfl

end DerivationLie

section SoThree

variable (R : Type*) [CommRing R]

/-- The matrix of the operator `w ↦ v × w` on `R³`. -/
def crossMatrix (v : Fin 3 → R) : Matrix (Fin 3) (Fin 3) R :=
  !![0, -v 2, v 1; v 2, 0, -v 0; -v 1, v 0, 0]

theorem crossMatrix_mulVec (v w : Fin 3 → R) : (crossMatrix R v).mulVec w = crossProduct v w := by
  ext i
  fin_cases i <;> simp [crossMatrix, cross_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

/-- **Etingof et al., §1.9 (exercise)**: every matrix `crossMatrix v` is skew-symmetric. -/
theorem crossMatrix_mem_so (v : Fin 3 → R) : crossMatrix R v ∈ LieAlgebra.Orthogonal.so (Fin 3) R := by
  rw [LieAlgebra.Orthogonal.mem_so]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [crossMatrix]

/-- **Etingof et al., §1.9 (exercise)**: the commutator of the matrices of `v ×` and `w ×` is the matrix of
`(v × w) ×`; that is, `v ↦ crossMatrix v` carries the cross product to the commutator bracket. -/
@[kb "etingof2011" "§1.9, p. 16"]
theorem crossMatrix_lie (v w : Fin 3 → R) :
    ⁅crossMatrix R v, crossMatrix R w⁆ = crossMatrix R (crossProduct v w) := by
  rw [Ring.lie_def]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [crossMatrix, cross_apply] <;> ring

/-- **Etingof et al., §1.9 (exercise)**: every skew-symmetric `3 × 3` matrix is `crossMatrix v` for a unique
vector `v`, so that `so(3)` is identified with `R³` carrying the cross product. -/
@[kb "etingof2011" "§1.9, p. 16"]
theorem exists_unique_crossMatrix_of_mem_so [NoZeroDivisors R] [CharZero R] (A : Matrix (Fin 3) (Fin 3) R)
    (hA : A ∈ LieAlgebra.Orthogonal.so (Fin 3) R) : ∃! v : Fin 3 → R, crossMatrix R v = A := by
  rw [LieAlgebra.Orthogonal.mem_so] at hA
  have h := fun i j => congrFun (congrFun hA i) j
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
  refine ⟨![A 2 1, A 0 2, A 1 0], ?_, ?_⟩
  · have h00 := h 0 0
    have h11 := h 1 1
    have h22 := h 2 2
    have h01 := h 0 1
    have h02 := h 0 2
    have h12 := h 1 2
    have two : (2 : R) ≠ 0 := two_ne_zero
    have d0 : A 0 0 = 0 := by
      have : (2 : R) * A 0 0 = 0 := by linear_combination h00
      exact (mul_eq_zero.1 this).resolve_left two
    have d1 : A 1 1 = 0 := by
      have : (2 : R) * A 1 1 = 0 := by linear_combination h11
      exact (mul_eq_zero.1 this).resolve_left two
    have d2 : A 2 2 = 0 := by
      have : (2 : R) * A 2 2 = 0 := by linear_combination h22
      exact (mul_eq_zero.1 this).resolve_left two
    ext i j
    fin_cases i <;> fin_cases j <;> simp [crossMatrix, d0, d1, d2] <;> grind
  · intro v hv
    subst hv
    ext i
    fin_cases i <;> simp [crossMatrix]

end SoThree

section TensorAlgebraSection

variable (R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- **Etingof et al., §1.11**: the tensor algebra `TV` is the direct sum of the tensor powers `V^{⊗n}`, with
multiplication given by concatenation. -/
@[kb "etingof2011" "§1.11, p. 19"]
noncomputable def tensorAlgebraEquivDirectSum : TensorAlgebra R M ≃ₐ[R] DirectSum ℕ (fun n => ⨂[R]^n M) :=
  TensorAlgebra.equivDirectSum

variable {R M}

/-- **Etingof et al., §1.11**: choosing a basis of `V` identifies the tensor algebra with the free algebra on
that basis, sending basis vectors to the generators. -/
@[kb "etingof2011" "§1.11, p. 19"]
noncomputable def tensorAlgebraEquivFreeAlgebra {κ : Type*} (b : Module.Basis κ R M) :
    TensorAlgebra R M ≃ₐ[R] FreeAlgebra R κ :=
  TensorAlgebra.equivFreeAlgebra b

theorem tensorAlgebraEquivFreeAlgebra_ι {κ : Type*} (b : Module.Basis κ R M) (i : κ) :
    tensorAlgebraEquivFreeAlgebra b (TensorAlgebra.ι R (b i)) = FreeAlgebra.ι R i :=
  TensorAlgebra.equivFreeAlgebra_ι_apply b i

end TensorAlgebraSection

section LieTheorem

variable {k L V : Type*} [Field k] [IsAlgClosed k] [CharZero k] [LieRing L] [LieAlgebra k L]
  [AddCommGroup V] [Module k V] [LieRingModule L V] [LieModule k L V] [Module.Finite k V]

/-- **Etingof et al., Problem 1.56 (Lie's theorem)**: a finite-dimensional irreducible representation of a
solvable Lie algebra over an algebraically closed field of characteristic zero is one-dimensional. -/
@[kb "etingof2011" "Problem 1.56, p. 21"]
theorem finrank_eq_one_of_isIrreducible_of_isSolvable [LieAlgebra.IsSolvable L]
    [LieModule.IsIrreducible k L V] : finrank k V = 1 := by
  have : Nontrivial V := LieModule.nontrivial_of_isIrreducible k L V
  obtain ⟨χ, hχ⟩ := LieModule.exists_nontrivial_weightSpace_of_isSolvable k L V
  have hne : LieModule.weightSpace V χ ≠ ⊥ := by
    intro h
    rw [h] at hχ
    obtain ⟨⟨x, hx⟩, hx0⟩ := exists_ne (0 : (⊥ : LieSubmodule k L V))
    exact hx0 (Subtype.ext (by simpa using hx))
  have htop : LieModule.weightSpace V χ = ⊤ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top (LieModule.weightSpace V χ) with h | h
    · exact (hne h).elim
    · exact h
  have hall : ∀ (x : L) (v : V), ⁅x, v⁆ = χ x • v := by
    intro x v
    have : v ∈ LieModule.weightSpace V χ := by rw [htop]; trivial
    rw [LieModule.mem_weightSpace] at this
    exact this x
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let N : LieSubmodule k L V :=
    { Submodule.span k {v} with
      lie_mem := by
        intro x m hm
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hm
        rw [lie_smul, hall]
        exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)) }
  have hN : N = ⊤ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top N with h | h
    · exfalso
      apply hv
      have : v ∈ N := Submodule.mem_span_singleton_self v
      rw [h] at this
      simpa using this
    · exact h
  rw [finrank_eq_one_iff_of_ne_zero' v hv]
  intro w
  have : w ∈ N := by rw [hN]; trivial
  exact Submodule.mem_span_singleton.1 this

end LieTheorem

section EndAsModule

variable {k A V ι : Type*} [Field k] [Ring A] [Algebra k A] [AddCommGroup V] [Module k V] [Module A V]
  [IsScalarTower k A V]

/-- **Etingof et al., Example after Definition 2.1**: for a module `V` with a basis of size `n`, the space
`End_k V`, with `A` acting by composition on the left, is isomorphic as a left `A`-module to the direct sum of
`n` copies of `V`: an endomorphism is determined by the images of the basis vectors. -/
@[kb "etingof2011" "Definition 2.1 example, p. 23"]
noncomputable def endEquivPi (b : Module.Basis ι k V) : Module.End k V ≃ₗ[A] (ι → V) where
  toFun f := fun i => f (b i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun g := b.constr k g
  left_inv f := by
    apply b.ext
    intro i
    simp
  right_inv g := by
    ext i
    simp

end EndAsModule

section DualRep

variable (k A V : Type*) [CommSemiring k] [Semiring A] [Algebra k A] [AddCommGroup V] [Module k V] [Module A V]
  [IsScalarTower k A V]

/-- **Etingof et al., Definition 2.7**: the dual of a representation `V` of an algebra `A` is a representation
of the opposite algebra `Aᵐᵒᵖ` on `V*`, where `a` acts by the transpose of its action on `V`. -/
@[kb "etingof2011" "Definition 2.7, p. 24"]
noncomputable def dualRep : Aᵐᵒᵖ →ₐ[k] Module.End k (Module.Dual k V) where
  toFun a := (Algebra.lsmul k k V (MulOpposite.unop a)).dualMap
  map_one' := by ext; simp
  map_mul' a b := by
    ext f v
    simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp
  commutes' r := by
    ext f v
    simp [Algebra.algebraMap_eq_smul_one]

theorem dualRep_apply (a : A) (f : Module.Dual k V) (v : V) :
    dualRep k A V (MulOpposite.op a) f v = f (a • v) := rfl

end DualRep

section Kronecker

/-- **Etingof et al., §2.10**: `Mat_m(k) ⊗ Mat_n(k) ≅ Mat_{mn}(k)` as `k`-algebras. -/
@[kb "etingof2011" "§2.10, p. 31"]
noncomputable def matTensorMatEquiv (k : Type*) [CommRing k] (m n : ℕ) :
    Matrix (Fin m) (Fin m) k ⊗[k] Matrix (Fin n) (Fin n) k ≃ₐ[k] Matrix (Fin (m * n)) (Fin (m * n)) k :=
  (Matrix.kroneckerAlgEquiv (Fin m) (Fin n) k).trans
    (Matrix.reindexAlgEquiv k k finProdFinEquiv)

end Kronecker

end UndergradKB.RepresentationTheory
