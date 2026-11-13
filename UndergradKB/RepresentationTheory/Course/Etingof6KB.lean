import UndergradKB.RepresentationTheory.Categories
import UndergradKB.RepresentationTheory.CategoriesMore
import UndergradKB.RepresentationTheory.SchurFunctors
import UndergradKB.RepresentationTheory.ReflectionAdjunction
import UndergradKB.RepresentationTheory.LieAlgebraCategory
import UndergradKB.Common.Attr

/-!
# Etingof et al., Introduction to Representation Theory: Chapter 6 (introduction to categories), repository proofs

Thin theorems in the book's terms for the items of Chapter 6 that are proved in this repository
(local smallness, Schur functors, the double dual, adjoint functors, Morita equivalence, exactness,
Maschke in categorical form and the adjunction of reflection functors), each tagged with the source
key `etingof2011` and the locator of the item in the book.
-/

namespace UndergradKB.RepresentationTheory.Course

open CategoryTheory CategoryTheory.Limits
open PiTensorProduct
open scoped TensorProduct

universe u v w w' a

/-- Etingof et al., Section 6.1: a category is locally small exactly when every collection of morphisms
between two objects is small. -/
@[kb "etingof2011" "§6.1, p. 99"]
theorem etingof_sec_6_1_kb {C : Type u} [Category.{v} C] :
    LocallySmall.{w} C ↔ ∀ X Y : C, Small.{w} (X ⟶ Y) :=
  locallySmall_iff

section Schur

variable {k : Type*} [CommSemiring k] {n : ℕ} {V : Type*} [AddCommMonoid V] [Module k V]
  {W : Type*} [AddCommMonoid W] [Module k W]

/-- Etingof et al., Example 6.5(8): the tensor power of a linear map commutes with the permutation action
of the symmetric group, which is what makes the Schur functor well defined on morphisms. -/
@[kb "etingof2011" "Example 6.5(8), p. 100"]
theorem etingof_6_5_8_a (f : V →ₗ[k] W) (σ : Equiv.Perm (Fin n)) (x : ⨂[k] _ : Fin n, V) :
    tensorPowerMap n f (tensorPowerPermRep k n V σ x) =
      tensorPowerPermRep k n W σ (tensorPowerMap n f x) :=
  tensorPowerMap_perm f σ x

/-- Etingof et al., Example 6.5(8): the Schur functor sends the identity map to the identity. -/
@[kb "etingof2011" "Example 6.5(8), p. 100"]
theorem etingof_6_5_8_b {P : Type*} [AddCommMonoid P] [Module k P]
    (π : Representation k (Equiv.Perm (Fin n)) P) :
    schurHomMap π (LinearMap.id : V →ₗ[k] V) = LinearMap.id :=
  schurHomMap_id π

/-- Etingof et al., Example 6.5(8): the Schur functor preserves composition. -/
@[kb "etingof2011" "Example 6.5(8), p. 100"]
theorem etingof_6_5_8_c {P : Type*} [AddCommMonoid P] [Module k P] {U : Type*} [AddCommMonoid U]
    [Module k U] (π : Representation k (Equiv.Perm (Fin n)) P) (g : W →ₗ[k] U) (f : V →ₗ[k] W) :
    schurHomMap π (g ∘ₗ f) = schurHomMap π g ∘ₗ schurHomMap π f :=
  schurHomMap_comp π g f

end Schur

/-- Etingof et al., Example 6.7: the identity functor and the double dual functor are not isomorphic on all
vector spaces, because the evaluation map into the double dual of an infinite-dimensional space is never
bijective. -/
@[kb "etingof2011" "Example 6.7, p. 100"]
theorem etingof_6_7 {k : Type u} [Field k] (V : Type u) [AddCommGroup V] [Module k V]
    (h : ¬ FiniteDimensional k V) : ¬ Function.Bijective (Module.Dual.eval k V) :=
  not_bijective_eval_of_infinite k V h

/-- Etingof et al., Example 6.13(1): for a finite-dimensional representation `V` of a group, tensoring with
`V` has tensoring with the dual `V*` as a right adjoint and as a left adjoint. -/
@[kb "etingof2011" "Example 6.13(1), p. 103"]
theorem etingof_6_13_1 {k G : Type u} [Field k] [Group G] (V : FDRep k G) :
    Nonempty (MonoidalCategory.tensorLeft V ⊣ MonoidalCategory.tensorLeft Vᘁ) ∧
      Nonempty (MonoidalCategory.tensorLeft Vᘁ ⊣ MonoidalCategory.tensorLeft V) :=
  fdrep_tensorLeft_adjunctions V

/-- Etingof et al., Remark 6.16: a ring is Morita equivalent to the ring of square matrices over it. -/
@[kb "etingof2011" "Remark 6.16, p. 104"]
theorem etingof_6_16 (R : Type u) [Ring R] (ι : Type u) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    MoritaEquivalentRings R (Matrix ι ι R) :=
  MoritaEquivalentRings.matrix R ι

/-- Etingof et al., Example 6.22: when the order of a finite group is nonzero in the field, the category of
its representations is semisimple (every short exact sequence splits). -/
@[kb "etingof2011" "Example 6.22, p. 105"]
theorem etingof_6_22 {k : Type u} [Field k] {G : Type u} [Group G] [Finite G]
    [NeZero (Nat.card G : k)] : IsSemisimpleAbelianCategory (Rep.{u} k G) :=
  isSemisimpleAbelianCategory_rep

section Exact

variable (k : Type u) {G : Type u} [CommRing k] [Group G] (S : Subgroup G) [S.FiniteIndex]
  [DecidableRel (QuotientGroup.rightRel S)]

/-- Etingof et al., Example 6.23: induction from a subgroup of finite index is an exact functor. -/
@[kb "etingof2011" "Example 6.23, p. 105"]
theorem etingof_6_23_a : IsExactFunctor (Rep.indFunctor.{u} k S.subtype) :=
  isExactFunctor_indFunctor k S

end Exact

/-- Etingof et al., Example 6.23: restriction of representations along a group homomorphism is an exact
functor. -/
@[kb "etingof2011" "Example 6.23, p. 105"]
theorem etingof_6_23_b {k : Type u} [CommRing k] {G H : Type u} [Group G] [Group H] (φ : H →* G) :
    IsExactFunctor (Rep.resFunctor (k := k) φ) :=
  isExactFunctor_resFunctor φ

/-- Etingof et al., Example 6.23: `Hom(X, -)` is not right exact in general; for `X = Z/2` over the
integers it fails to preserve the surjection `Z → Z/2`. -/
@[kb "etingof2011" "Example 6.23, p. 105"]
theorem etingof_6_23_c :
    ¬ IsRightExactFunctor (preadditiveCoyonedaObj (ModuleCat.of ℤ (ZMod 2))) :=
  not_isRightExactFunctor_preadditiveCoyonedaObj_zmod_two

/-- Etingof et al., Example 6.23: tensoring with `Z/2` over the integers is not left exact. -/
@[kb "etingof2011" "Example 6.23, p. 105"]
theorem etingof_6_23_d :
    ¬ IsLeftExactFunctor (MonoidalCategory.tensorLeft (ModuleCat.of ℤ (ZMod 2))) :=
  not_isLeftExactFunctor_tensorLeft_zmod_two

section Adjunction

open scoped Classical

variable {k : Type u} [Field k] {Q : Type v} [Quiver.{a} Q]
  {V : QRep.{u, v, w, a} k Q} {i : Q} [Fintype (OutArrows i)] {hi : Quiver.IsSource i}
  {W W' : RevRep.{u, v, max (max a v) w, a} k i}

/-- Etingof et al., exercise after Section 5.7 (Chapter 6, p. 105): the bijection between morphisms out of
the reflected representation at a source and morphisms into the other reflection is natural in the target
`W`. -/
@[kb "etingof2011" "Exercise, p. 105"]
theorem etingof_6_exercise_c (g' : RevRep.Hom W W') (g : RevRep.Hom (reflectSource V i hi) W) :
    reflectAdjEquiv (@QRep.Hom.comp k Q _ (reversedAt i) _ _ _ g' g) =
      RevRevHom.postcomp
        (@reflectSinkMap k _ Q (reversedAt i) W W' g' i (fintypeInArrowsRev i)
          (isSink_reversedAt hi))
        (reflectAdjEquiv g) :=
  reflectAdjEquiv_postcomp g' g

/-- Etingof et al., exercise after Section 5.7 (Chapter 6, p. 105): the bijection between morphisms out of
the reflected representation at a source and morphisms into the other reflection is natural in `V`. -/
@[kb "etingof2011" "Exercise, p. 105"]
theorem etingof_6_exercise_d {V' : QRep.{u, v, w, a} k Q} (f : QRep.Hom V' V)
    (g : RevRep.Hom (reflectSource V i hi) W) :
    reflectAdjEquiv (@QRep.Hom.comp k Q _ (reversedAt i) _ _ _ g (reflectSourceMap f i hi)) =
      RevRevHom.precomp (reflectAdjEquiv g) f :=
  reflectAdjEquiv_precomp f g

end Adjunction

/-- Etingof et al., Example 6.5: the endomorphism monoid of the single object of the one-object
category of a monoid `M` is `M` itself. -/
@[kb "etingof2011" "Example 6.5, p. 99"]
theorem etingof_6_5_a (M : Type u) [Monoid M] :
    Nonempty (M ≃* End (SingleObj.star M)) :=
  ⟨singleObjEndMulEquiv M⟩

/-- Etingof et al., Example 6.5: functors from the path category of a quiver to a category `C`
correspond bijectively to assignments of an object to each vertex and a morphism to each arrow
(with `C` the category of vector spaces, these are the quiver representations). -/
@[kb "etingof2011" "Example 6.5, p. 99"]
theorem etingof_6_5_b (V : Type u) [Quiver.{v + 1} V] (C : Type*) [Category C] :
    Nonempty ((Paths V ⥤ C) ≃ (V ⥤q C)) :=
  ⟨pathsFunctorEquiv V C⟩

/-- Etingof et al., Example 6.7(3)(4): the endomorphisms of the identity functor of the category of
left `A`-modules form a ring isomorphic to the center of `A`. -/
@[kb "etingof2011" "Example 6.7(3)(4), p. 100"]
theorem etingof_6_7_3 (A : Type u) [Ring A] :
    Nonempty (CatCenter (ModuleCat.{u} A) ≃+* Subring.center A) :=
  ⟨catCenterModuleCatRingEquiv A⟩

/-- Etingof et al., Example 6.10: the forgetful functor from left `A`-modules to sets is
corepresented by the regular module `A`. -/
@[kb "etingof2011" "Example 6.10, p. 102"]
theorem etingof_6_10 (A : Type u) [Ring A] :
    Nonempty ((forget (ModuleCat.{u} A)).CorepresentableBy (ModuleCat.of A A)) :=
  ⟨forgetCorepresentableBy A⟩

/-- Etingof et al., Example 6.13(3): the universal enveloping algebra functor is left adjoint to the
functor sending an associative algebra to its Lie algebra under the commutator. -/
@[kb "etingof2011" "Example 6.13(3), p. 103"]
theorem etingof_6_13_3 (R : Type u) [CommRing R] :
    Nonempty (envelopingFunctor R ⊣ algToLie R) :=
  ⟨envelopingAdjunction R⟩

/-- Etingof et al., Example 6.13(4): the group algebra functor is left adjoint to the functor
sending an algebra to its group of units. -/
@[kb "etingof2011" "Example 6.13(4), p. 103"]
theorem etingof_6_13_4 (k : Type u) [CommRing k] :
    Nonempty (groupAlgebraFunctor k ⊣ algUnitsFunctor k) :=
  ⟨groupAlgebraAdjunction k⟩

/-- Etingof et al., Example 6.13(5): the symmetric algebra functor is left adjoint to the
forgetful functor from commutative algebras to modules. -/
@[kb "etingof2011" "Example 6.13(5), p. 103"]
theorem etingof_6_13_5_a (R : Type u) [CommRing R] :
    Nonempty (symmetricAlgebraFunctor R ⊣ commAlgForget R) :=
  ⟨symmetricAlgebraAdjunction R⟩

/-- Etingof et al., Example 6.13(5): the tensor algebra functor is left adjoint to the forgetful
functor from algebras to modules. -/
@[kb "etingof2011" "Example 6.13(5), p. 103"]
theorem etingof_6_13_5_b (R : Type u) [CommRing R] :
    Nonempty (AlgCat.tensorAlgebra.{u} R ⊣ forget₂ (AlgCat.{u} R) (ModuleCat.{u} R)) :=
  ⟨tensorAlgebraAdjunction R⟩

end UndergradKB.RepresentationTheory.Course
