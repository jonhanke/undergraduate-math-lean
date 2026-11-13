import UndergradKB.RepresentationTheory.AlgebrasChapter2
import UndergradKB.RepresentationTheory.AlgebrasChapter2b
import UndergradKB.RepresentationTheory.AlgebrasKrullSchmidt
import UndergradKB.RepresentationTheory.AlgebrasMatrixModules
import UndergradKB.RepresentationTheory.AlgebrasSemisimple
import UndergradKB.RepresentationTheory.AlgebraCharacters
import UndergradKB.RepresentationTheory.Extensions
import UndergradKB.RepresentationTheory.CliffordSemisimple
import UndergradKB.RepresentationTheory.CliffordStructure
import UndergradKB.RepresentationTheory.TensorProductAlgebras
import UndergradKB.RepresentationTheory.IsotypicDecomposition
import UndergradKB.RepresentationTheory.JordanHolderFitting
import UndergradKB.RepresentationTheory.AlgebrasMisc
import UndergradKB.Common.Attr

/-!
# Etingof et al., Introduction to Representation Theory: Chapter 2, results proved in this repository

Course names for the Chapter 2 items of the checklist (general theory of algebras and their
representations) that are proved by declarations of this repository; the ones proved in Mathlib are
in `Course/Etingof2.lean`.  Each theorem restates a repository theorem in the book's terms and is
proved by it, and carries the source key `etingof2011` and the locator of the item in the book.
-/

namespace UndergradKB.RepresentationTheory.Course

open scoped TensorProduct

universe u

/-- Etingof et al., Proposition 2.2: over an algebraically closed field, a submodule of a direct sum
of copies `n_i V_i` of pairwise non-isomorphic simple modules is the image of `r_i V_i` under an
injective map given by matrices of full rank `r_i`. -/
@[kb "etingof2011" "Proposition 2.2, p. 23"]
theorem etingof_2_2_a {k : Type*} {A : Type*} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, AddCommGroup (V i)]
    [∀ i, Module A (V i)] [∀ i, Module k (V i)] [∀ i, IsScalarTower k A (V i)]
    [∀ i, IsSimpleModule A (V i)] [∀ i, FiniteDimensional k (V i)]
    (hV : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j)) (n : ι → ℕ)
    (U : Submodule A (∀ i, Fin (n i) → V i)) :
    ∃ (r : ι → ℕ) (m : ∀ i, Matrix (Fin (n i)) (Fin (r i)) k), (∀ i, (m i).rank = r i) ∧
      Function.Injective (embedPi k A V m) ∧ U = LinearMap.range (embedPi k A V m) :=
  exists_matrices_eq_range_embedPi (k := k) hV n U

/-- Etingof et al., Proposition 2.2: every submodule of `⊕ n_i V_i` (with the `V_i` pairwise
non-isomorphic finite-dimensional simple modules over an algebraically closed field) is isomorphic
to `⊕ r_i V_i` for some `r_i ≤ n_i`. -/
@[kb "etingof2011" "Proposition 2.2, p. 23"]
theorem etingof_2_2_b (k : Type*) {A : Type*} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, AddCommGroup (V i)]
    [∀ i, Module A (V i)] [∀ i, Module k (V i)] [∀ i, IsScalarTower k A (V i)]
    [∀ i, IsSimpleModule A (V i)] [∀ i, FiniteDimensional k (V i)]
    (hV : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j)) (n : ι → ℕ)
    (U : Submodule A (∀ i, Fin (n i) → V i)) :
    ∃ r : ι → ℕ, (∀ i, r i ≤ n i) ∧ Nonempty (U ≃ₗ[A] ∀ i, Fin (r i) → V i) :=
  exists_linearEquiv_pi_copies k hV n U

/-- Etingof et al., Remark 2.3: for a single simple module `V`, a submodule of `V^n` is the image
of `V^r` under an injective map given by an `n × r` scalar matrix of rank `r`. -/
@[kb "etingof2011" "Remark 2.3, p. 23"]
theorem etingof_2_2_c {k : Type*} {A : Type*} {V : Type*} [Field k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module A V] [Module k V] [IsScalarTower k A V] {ι : Type*} [IsAlgClosed k]
    [IsSimpleModule A V] [FiniteDimensional k V] [Fintype ι] (U : Submodule A (ι → V)) :
    ∃ (r : ℕ) (m : Matrix ι (Fin r) k), m.rank = r ∧ Function.Injective (embedMatrix k A V m) ∧
      U = LinearMap.range (embedMatrix k A V m) :=
  exists_matrix_eq_range_embedMatrix U

/-- Etingof et al., Corollary 2.4: for an irreducible module over an algebraically closed field,
given linearly independent vectors `v_i` and arbitrary vectors `w_i` there is one algebra element
sending each `v_i` to `w_i`. -/
@[kb "etingof2011" "Corollary 2.4, p. 24"]
theorem etingof_2_4 {k : Type*} {A : Type*} {V : Type*} [Field k] [IsAlgClosed k] [Ring A]
    [Algebra k A] [AddCommGroup V] [Module A V] [Module k V] [IsScalarTower k A V]
    [IsSimpleModule A V] [FiniteDimensional k V] {ι : Type*} [Finite ι] (v : ι → V)
    (hv : LinearIndependent k v) (w : ι → V) : ∃ a : A, ∀ i, a • v i = w i :=
  exists_smul_eq_of_linearIndependent v hv w

/-- Etingof et al., Theorem 2.5 (density theorem): the action map from the algebra to the
endomorphisms of a finite-dimensional irreducible module over an algebraically closed field is
surjective. -/
@[kb "etingof2011" "Theorem 2.5, p. 24"]
theorem etingof_2_5_a {k : Type*} {A : Type*} {V : Type*} [Field k] [IsAlgClosed k] [Ring A]
    [Algebra k A] [AddCommGroup V] [Module A V] [Module k V] [IsScalarTower k A V]
    [IsSimpleModule A V] [FiniteDimensional k V] :
    Function.Surjective (Algebra.lsmul k k V : A →ₐ[k] Module.End k V) :=
  density_surjective

/-- Etingof et al., Theorem 2.5 (density theorem): for pairwise non-isomorphic finite-dimensional
irreducible modules `V_i`, the action map from the algebra to the product of the `End V_i` is
surjective. -/
@[kb "etingof2011" "Theorem 2.5, p. 24"]
theorem etingof_2_5_b {k : Type*} {A : Type*} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, AddCommGroup (V i)]
    [∀ i, Module A (V i)] [∀ i, Module k (V i)] [∀ i, IsScalarTower k A (V i)]
    [∀ i, IsSimpleModule A (V i)] [∀ i, FiniteDimensional k (V i)]
    (hV : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j)) :
    Function.Surjective
      (fun a : A => fun i => (Algebra.lsmul k k (V i) a : Module.End k (V i))) :=
  density_pi_surjective hV

/-- Etingof et al., Theorem 2.6: for a product of matrix algebras, each standard module `k^{d_i}`
is irreducible. -/
@[kb "etingof2011" "Theorem 2.6, p. 24"]
theorem etingof_2_6_a {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ι → ℕ}
    (i : ι) [NeZero (d i)] : IsSimpleModule (MatProd k d) (StdModule k d i) :=
  isSimpleModule_stdModule i

/-- Etingof et al., Theorem 2.6: every irreducible module over a product of matrix algebras is
isomorphic to one of the standard modules. -/
@[kb "etingof2011" "Theorem 2.6, p. 24"]
theorem etingof_2_6_b {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ι → ℕ}
    {S : Type*} [AddCommGroup S] [Module (MatProd k d) S] [IsSimpleModule (MatProd k d) S]
    [∀ i, NeZero (d i)] : ∃ i, Nonempty (S ≃ₗ[MatProd k d] StdModule k d i) :=
  exists_linearEquiv_stdModule

/-- Etingof et al., Theorem 2.6: distinct standard modules of a product of matrix algebras are not
isomorphic. -/
@[kb "etingof2011" "Theorem 2.6, p. 24"]
theorem etingof_2_6_c {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ι → ℕ}
    [∀ i, NeZero (d i)] {i j : ι} (hij : i ≠ j) :
    IsEmpty (StdModule k d i ≃ₗ[MatProd k d] StdModule k d j) :=
  isEmpty_linearEquiv_stdModule hij

/-- Etingof et al., Theorem 2.6: every finite-dimensional module over a product of matrix algebras
is a direct sum of standard modules. -/
@[kb "etingof2011" "Theorem 2.6, p. 24"]
theorem etingof_2_6_d {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ι → ℕ}
    [∀ i, NeZero (d i)] (M : Type*) [AddCommGroup M] [Module (MatProd k d) M]
    [Module.Finite (MatProd k d) M] :
    ∃ (n : ℕ) (c : Fin n → ι), Nonempty (M ≃ₗ[MatProd k d] ∀ j : Fin n, StdModule k d (c j)) :=
  exists_linearEquiv_pi_stdModule M

/-- Etingof et al., Proposition 2.10: the radical of an algebra is a two-sided ideal. -/
@[kb "etingof2011" "Proposition 2.10, p. 26"]
theorem etingof_2_10 (A : Type u) [Ring A] : (algebraRadical A).IsTwoSided :=
  algebraRadical_isTwoSided A

/-- Etingof et al., Proposition 2.11: every nilpotent two-sided ideal lies in the radical. -/
@[kb "etingof2011" "Proposition 2.11, p. 26"]
theorem etingof_2_11_a (A : Type u) [Ring A] (I : Ideal A) [I.IsTwoSided] (hI : IsNilpotent I) :
    I ≤ algebraRadical A :=
  le_algebraRadical_of_isNilpotent A I hI

/-- Etingof et al., Proposition 2.11: the radical of an Artinian algebra is nilpotent. -/
@[kb "etingof2011" "Proposition 2.11, p. 26"]
theorem etingof_2_11_b (A : Type u) [Ring A] [IsArtinianRing A] : IsNilpotent (algebraRadical A) :=
  isNilpotent_algebraRadical A

/-- Etingof et al., Proposition 2.11: the radical of an Artinian algebra is the largest nilpotent
two-sided ideal. -/
@[kb "etingof2011" "Proposition 2.11, p. 26"]
theorem etingof_2_11_c (A : Type u) [Ring A] [IsArtinianRing A] :
    IsGreatest {I : Ideal A | I.IsTwoSided ∧ IsNilpotent I} (algebraRadical A) :=
  isGreatest_algebraRadical A

/-- Etingof et al., Theorem 2.12: a finite-dimensional algebra over an algebraically closed field
has only finitely many pairwise non-isomorphic irreducible modules, at most its dimension. -/
@[kb "etingof2011" "Theorem 2.12, p. 26"]
theorem etingof_2_12 {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
    [FiniteDimensional k A] {ι : Type*} {V : ι → Type u} [∀ i, AddCommGroup (V i)]
    [∀ i, Module A (V i)] [∀ i, Module k (V i)] [∀ i, IsScalarTower k A (V i)]
    [∀ i, IsSimpleModule A (V i)] [∀ i, FiniteDimensional k (V i)]
    (hV : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j)) :
    Finite ι ∧ Nat.card ι ≤ Module.finrank k A :=
  finite_of_pairwise_nonIso hV

/-- Etingof et al., Corollary 2.13: the sum of the squares of the dimensions of the pairwise
non-isomorphic irreducible modules is at most the dimension of the algebra. -/
@[kb "etingof2011" "Corollary 2.13, p. 26"]
theorem etingof_2_13 {k : Type*} {A : Type*} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, AddCommGroup (V i)]
    [∀ i, Module A (V i)] [∀ i, Module k (V i)] [∀ i, IsScalarTower k A (V i)]
    [∀ i, IsSimpleModule A (V i)] [∀ i, FiniteDimensional k (V i)] [FiniteDimensional k A]
    (hV : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j)) :
    ∑ i, Module.finrank k (V i) ^ 2 ≤ Module.finrank k A :=
  sum_finrank_sq_le_finrank hV

/-- Etingof et al., Proposition 2.16: for a finite-dimensional algebra over an algebraically closed
field with irreducibles `V_i`, the following are equivalent: the radical vanishes, the sum of
squares of dimensions equals the dimension of the algebra, the algebra is a product of matrix
algebras, every module is completely reducible, the algebra is completely reducible over itself. -/
@[kb "etingof2011" "Proposition 2.16, p. 27"]
theorem etingof_2_16_a {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
    [FiniteDimensional k A] {ι : Type*} [Fintype ι] {V : ι → Type u} [∀ i, AddCommGroup (V i)]
    [∀ i, Module A (V i)] [∀ i, Module k (V i)] [∀ i, IsScalarTower k A (V i)]
    [∀ i, IsSimpleModule A (V i)] [∀ i, FiniteDimensional k (V i)]
    (hV : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j))
    (hcomp : ∀ (S : Type u) [AddCommGroup S] [Module A S] [IsSimpleModule A S],
      ∃ i, Nonempty (S ≃ₗ[A] V i)) :
    List.TFAE
      [ algebraRadical A = ⊥,
        ∑ i, Module.finrank k (V i) ^ 2 = Module.finrank k A,
        ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧
          Nonempty (A ≃ₐ[k] ∀ i, Matrix (Fin (d i)) (Fin (d i)) k),
        ∀ (M : Type u) [AddCommGroup M] [Module A M], IsSemisimpleModule A M,
        IsSemisimpleModule A A ] :=
  semisimple_tfae hV hcomp

/-- Etingof et al., Proposition 2.16: the sum of squares of the dimensions of the irreducible modules
equals the dimension of the algebra exactly when the radical vanishes. -/
@[kb "etingof2011" "Proposition 2.16, p. 27"]
theorem etingof_2_16_b {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
    {ι : Type*} [Fintype ι] {V : ι → Type u} [∀ i, AddCommGroup (V i)] [∀ i, Module A (V i)]
    [∀ i, Module k (V i)] [∀ i, IsScalarTower k A (V i)] [∀ i, IsSimpleModule A (V i)]
    [∀ i, FiniteDimensional k (V i)] [FiniteDimensional k A]
    (hV : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j))
    (hcomp : ∀ (S : Type u) [AddCommGroup S] [Module A S] [IsSimpleModule A S],
      ∃ i, Nonempty (S ≃ₗ[A] V i)) :
    ∑ i, Module.finrank k (V i) ^ 2 = Module.finrank k A ↔ algebraRadical A = ⊥ :=
  sum_finrank_sq_eq_finrank_iff hV hcomp

/-- Etingof et al., §2.6: the character of a representation vanishes on commutators. -/
@[kb "etingof2011" "§2.6, p. 27"]
theorem etingof_sec_2_6 (k : Type*) {A : Type*} {V : Type*} [Field k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module A V] [Module k V] [IsScalarTower k A V] (a b : A) :
    algebraCharacter (V := V) k (a * b - b * a) = 0 :=
  algebraCharacter_commutator k a b

/-- Etingof et al., Theorem 2.17: the characters of pairwise non-isomorphic finite-dimensional
irreducible modules over an algebraically closed field are linearly independent. -/
@[kb "etingof2011" "Theorem 2.17, p. 27"]
theorem etingof_2_17 {k : Type*} {A : Type*} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, AddCommGroup (V i)]
    [∀ i, Module A (V i)] [∀ i, Module k (V i)] [∀ i, IsScalarTower k A (V i)]
    [∀ i, IsSimpleModule A (V i)] [∀ i, FiniteDimensional k (V i)]
    (hV : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j)) :
    LinearIndependent k (fun i => algebraCharacter k (A := A) (V := V i)) :=
  linearIndependent_algebraCharacter hV

/-- Etingof et al., Theorem 2.18 (Jordan-Holder): two filtrations of a module with irreducible
quotients have the same length, and their quotients agree up to a permutation. -/
@[kb "etingof2011" "Theorem 2.18, p. 28"]
theorem etingof_2_18_a {R : Type*} {M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (F G : SimpleFiltration R M) :
    F.length = G.length ∧ ∃ σ : Fin F.length ≃ Fin G.length,
      ∀ i : Fin F.length, Nonempty (F.quotient i ≃ₗ[R] G.quotient (σ i)) :=
  SimpleFiltration.jordan_holder F G

/-- Etingof et al., Theorem 2.18 (Jordan-Holder): the length of such a filtration is the length of
the module. -/
@[kb "etingof2011" "Theorem 2.18, p. 28"]
theorem etingof_2_18_b {R : Type*} {M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (F : SimpleFiltration R M) : (F.length : ℕ∞) = Module.length R M :=
  SimpleFiltration.length_eq_moduleLength F

/-- Etingof et al., Theorem 2.19 (Krull-Schmidt): two decompositions of a module of finite length
into indecomposables have the same summands up to isomorphism and permutation. -/
@[kb "etingof2011" "Theorem 2.19, p. 29"]
theorem etingof_2_19_a {R : Type*} [Ring R] {ι : Type*} {κ : Type*} [Fintype ι] [Fintype κ]
    {N : ι → Type*} {N' : κ → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    [∀ j, AddCommGroup (N' j)] [∀ j, Module R (N' j)] [∀ i, IsNoetherian R (N i)]
    [∀ i, IsArtinian R (N i)] (hN : ∀ i, IsIndecomposableModule R (N i))
    (hN' : ∀ j, IsIndecomposableModule R (N' j)) (e : (∀ i, N i) ≃ₗ[R] ∀ j, N' j) :
    ∃ σ : ι ≃ κ, ∀ i, Nonempty (N i ≃ₗ[R] N' (σ i)) :=
  krullSchmidt_unique' hN hN' e

/-- Etingof et al., Theorem 2.19: a finite-dimensional representation of an algebra over a field
is a direct sum of indecomposable ones. -/
@[kb "etingof2011" "Theorem 2.19, p. 29"]
theorem etingof_2_19_b {k : Type*} {A : Type*} [Field k] [Ring A] [Algebra k A] (V : Type u)
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V] [FiniteDimensional k V] :
    ∃ (ι : Type) (_ : Fintype ι) (N : ι → Type u) (_ : ∀ i, AddCommGroup (N i))
      (_ : ∀ i, Module A (N i)), (∀ i, IsIndecomposableModule A (N i)) ∧
        Nonempty (V ≃ₗ[A] ∀ i, N i) :=
  exists_indecomposable_decomposition_of_finiteDimensional (k := k) (A := A) V

/-- Etingof et al., Theorem 2.19: a module that is both Noetherian and Artinian is a direct sum of
indecomposable modules. -/
@[kb "etingof2011" "Theorem 2.19, p. 29"]
theorem etingof_2_19_c {R : Type*} [Ring R] (M : Type u) [AddCommGroup M] [Module R M]
    [IsNoetherian R M] [IsArtinian R M] :
    ∃ (ι : Type) (_ : Fintype ι) (N : ι → Type u) (_ : ∀ i, AddCommGroup (N i))
      (_ : ∀ i, Module R (N i)), (∀ i, IsIndecomposableModule R (N i)) ∧
        Nonempty (M ≃ₗ[R] ∀ i, N i) :=
  exists_indecomposable_decomposition M

/-- Etingof et al., Lemma 2.20: every endomorphism of an indecomposable module of finite length is
an isomorphism or nilpotent. -/
@[kb "etingof2011" "Lemma 2.20, p. 29"]
theorem etingof_2_20_a {R : Type*} {M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [IsNoetherian R M] [IsArtinian R M] (hM : IsIndecomposableModule R M) (f : Module.End R M) :
    IsUnit f ∨ IsNilpotent f :=
  isUnit_or_isNilpotent_of_indecomposable hM f

/-- Etingof et al., Lemma 2.20: the sum of two nilpotent endomorphisms of an indecomposable module of
finite length is nilpotent. -/
@[kb "etingof2011" "Lemma 2.20, p. 29"]
theorem etingof_2_20_b {R : Type*} {M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [IsNoetherian R M] [IsArtinian R M] (hM : IsIndecomposableModule R M) {f g : Module.End R M}
    (hf : IsNilpotent f) (hg : IsNilpotent g) : IsNilpotent (f + g) :=
  isNilpotent_add_of_indecomposable hM hf hg

/-- Etingof et al., Problem 2.21: the split extension of `W` by `V` sits in an exact sequence with
the inclusion of `V` and the projection onto `W`. -/
@[kb "etingof2011" "Problem 2.21, p. 30"]
theorem etingof_2_21_a {k : Type*} {V : Type*} {W : Type*} [CommRing k] [AddCommGroup V]
    [Module k V] [AddCommGroup W] [Module k W] :
    Function.Injective (LinearMap.inl k V W) ∧ Function.Surjective (LinearMap.snd k V W) ∧
      Function.Exact (LinearMap.inl k V W) (LinearMap.snd k V W) :=
  Extensions.extension_exact

/-- Etingof et al., Problem 2.21: two extensions given by cocycles are isomorphic exactly when the
cocycles differ by a coboundary. -/
@[kb "etingof2011" "Problem 2.21, p. 30"]
theorem etingof_2_21_b {k : Type*} {A : Type*} {V : Type*} {W : Type*} [CommRing k] [Ring A]
    [Algebra k A] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    {ρV : A →ₐ[k] Module.End k V} {ρW : A →ₐ[k] Module.End k W} {c c' : A →ₗ[k] (W →ₗ[k] V)}
    (hc : Extensions.IsCocycle ρV ρW c) (hc' : Extensions.IsCocycle ρV ρW c') :
    Extensions.ExtIso hc hc' ↔ c - c' ∈ Extensions.coboundaries ρV ρW :=
  Extensions.extIso_iff hc hc'

/-- Etingof et al., Problem 2.21: two extensions given by cocycles are isomorphic exactly when the
cocycles define the same class in the quotient of cocycles by coboundaries. -/
@[kb "etingof2011" "Problem 2.21, p. 30"]
theorem etingof_2_21_c {k : Type*} {A : Type*} {V : Type*} {W : Type*} [CommRing k] [Ring A]
    [Algebra k A] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    {ρV : A →ₐ[k] Module.End k V} {ρW : A →ₐ[k] Module.End k W} {c c' : A →ₗ[k] (W →ₗ[k] V)}
    (hc : Extensions.IsCocycle ρV ρW c) (hc' : Extensions.IsCocycle ρV ρW c') :
    Extensions.ExtIso hc hc' ↔
      (QuotientAddGroup.mk (⟨c, hc⟩ : Extensions.cocycles ρV ρW) : Extensions.ExtOne ρV ρW) =
        QuotientAddGroup.mk (⟨c', hc'⟩ : Extensions.cocycles ρV ρW) :=
  Extensions.extIso_iff_mk_eq hc hc'

/-- Etingof et al., Problem 2.25: the Clifford algebra of a complex quadratic form is semisimple
exactly when the form is nondegenerate. -/
@[kb "etingof2011" "Problem 2.25, p. 31"]
theorem etingof_2_25_a {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (Q : QuadraticForm ℂ V) : IsSemisimpleRing (CliffordAlgebra Q) ↔ Q.Nondegenerate :=
  CliffordSemisimple.isSemisimpleRing_cliffordAlgebra_iff Q

/-- Etingof et al., Problem 2.25: the Clifford algebra of a nondegenerate complex quadratic form is
semisimple. -/
@[kb "etingof2011" "Problem 2.25, p. 31"]
theorem etingof_2_25_b {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (Q : QuadraticForm ℂ V) (hQ : Q.Nondegenerate) : IsSemisimpleRing (CliffordAlgebra Q) :=
  CliffordSemisimple.isSemisimpleRing_cliffordAlgebra Q hQ

/-- Etingof et al., Problem 2.25: the Clifford algebra of a complex quadratic form on a space of
dimension `n` has dimension `2^n`. -/
@[kb "etingof2011" "Problem 2.25, p. 31"]
theorem etingof_2_25_c {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (Q : QuadraticForm ℂ V) :
    Module.finrank ℂ (CliffordAlgebra Q) = 2 ^ Module.finrank ℂ V :=
  CliffordStructure.finrank_cliffordAlgebra Q

/-- Etingof et al., Problem 2.25: in even dimension `2m` the Clifford algebra of a nondegenerate
complex form is a full matrix algebra of size `2^m`. -/
@[kb "etingof2011" "Problem 2.25, p. 31"]
theorem etingof_2_25_d {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (Q : QuadraticForm ℂ V) (hQ : Q.Nondegenerate) (m : ℕ) (hm : Module.finrank ℂ V = 2 * m) :
    Nonempty (CliffordAlgebra Q ≃ₐ[ℂ] Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) :=
  CliffordStructure.nonempty_algEquiv_matrix_cliffordAlgebra Q hQ m hm

/-- Etingof et al., Problem 2.25: in odd dimension `2m + 1` the Clifford algebra of a nondegenerate
complex form is a product of two matrix algebras of size `2^m`. -/
@[kb "etingof2011" "Problem 2.25, p. 31"]
theorem etingof_2_25_e {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (Q : QuadraticForm ℂ V) (hQ : Q.Nondegenerate) (m : ℕ)
    (hm : Module.finrank ℂ V = 2 * m + 1) :
    Nonempty (CliffordAlgebra Q ≃ₐ[ℂ]
      Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ × Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) :=
  CliffordStructure.nonempty_algEquiv_prod_matrix_cliffordAlgebra Q hQ m hm

attribute [local instance] tensorModule

/-- Etingof et al., Theorem 2.26: the tensor product of an irreducible module of `A` and one of `B`
is an irreducible module of `A ⊗ B`. -/
@[kb "etingof2011" "Theorem 2.26, p. 31"]
theorem etingof_2_26_a (k : Type*) {A : Type*} {B : Type*} {V : Type*} {W : Type*} [Field k]
    [IsAlgClosed k] [Ring A] [Algebra k A] [Ring B] [Algebra k B] [AddCommGroup V] [Module k V]
    [Module A V] [IsScalarTower k A V] [AddCommGroup W] [Module k W] [Module B W]
    [IsScalarTower k B W] [IsSimpleModule A V] [IsSimpleModule B W] [FiniteDimensional k V] :
    IsSimpleModule (TensorProduct k A B) (TensorProduct k V W) :=
  isSimpleModule_tensorModule k

/-- Etingof et al., Theorem 2.26: every finite-dimensional irreducible module over `A ⊗ B` is the
tensor product of an irreducible `A`-module and an irreducible `B`-module. -/
@[kb "etingof2011" "Theorem 2.26, p. 31"]
theorem etingof_2_26_b (k : Type*) [Field k] [IsAlgClosed k] (A : Type*) (B : Type*) (M : Type*)
    [Ring A] [Algebra k A] [Ring B] [Algebra k B] [AddCommGroup M] [Module k M] [Module A M]
    [Module B M] [Module (TensorProduct k A B) M] [IsScalarTower k A M] [IsScalarTower k B M]
    [SMulCommClass A B M] [IsSimpleModule (TensorProduct k A B) M] [FiniteDimensional k M]
    (h : ∀ (a : A) (b : B) (m : M), a ⊗ₜ[k] b • m = a • b • m) :
    ∃ (V : Submodule A M) (W : Submodule B (V →ₗ[A] M)), IsSimpleModule A V ∧ IsSimpleModule B W ∧
      Nonempty (TensorProduct k V W ≃ₗ[TensorProduct k A B] M) :=
  exists_linearEquiv_tensor_of_isSimpleModule k A B M h

/-- Etingof et al., Theorem 2.26: the irreducible factors of such a tensor product are uniquely
determined up to isomorphism. -/
@[kb "etingof2011" "Theorem 2.26, p. 31"]
theorem etingof_2_26_c (k : Type*) [Field k] (A : Type*) (B : Type*) [Ring A] [Algebra k A]
    [Ring B] [Algebra k B] {V : Type*} {V' : Type*} {W : Type*} {W' : Type*} [AddCommGroup V]
    [Module k V] [Module A V] [IsScalarTower k A V] [AddCommGroup V'] [Module k V'] [Module A V']
    [IsScalarTower k A V'] [AddCommGroup W] [Module k W] [Module B W] [IsScalarTower k B W]
    [AddCommGroup W'] [Module k W'] [Module B W'] [IsScalarTower k B W'] [IsSimpleModule A V]
    [IsSimpleModule A V'] [IsSimpleModule B W] [IsSimpleModule B W'] [FiniteDimensional k V']
    [FiniteDimensional k W']
    (θ : TensorProduct k V W ≃ₗ[TensorProduct k A B] TensorProduct k V' W') :
    Nonempty (V ≃ₗ[A] V') ∧ Nonempty (W ≃ₗ[B] W') :=
  linearEquiv_of_tensor_linearEquiv k A B θ

/-- Etingof et al., §2.10: the tensor product of the matrix algebras of sizes `m` and `n` over a
commutative ring is isomorphic, as an algebra, to the matrix algebra of size `m * n`. -/
@[kb "etingof2011" "§2.10, p. 31"]
theorem etingof_sec_2_10_kb (k : Type*) [CommRing k] (m n : ℕ) :
    Nonempty (Matrix (Fin m) (Fin m) k ⊗[k] Matrix (Fin n) (Fin n) k ≃ₐ[k]
      Matrix (Fin (m * n)) (Fin (m * n)) k) :=
  ⟨matTensorMatEquiv k m n⟩

end UndergradKB.RepresentationTheory.Course
