import Mathlib.RepresentationTheory.FinGroupCharZero
import Mathlib.RepresentationTheory.FDRep
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.AlgCat.Basic
import Mathlib.Algebra.Category.AlgCat.TensorAlgebra
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Abelian.Projective.Basic
import Mathlib.CategoryTheory.Center.Basic
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import Mathlib.CategoryTheory.SingleObj
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.RingTheory.Morita.Matrix
import UndergradKB.Common.Attr

/-! # Categories and functors (Etingof et al., chapter 6)

Bridging statements for the basic category theory of the representation-theory chapter, stated in the book's
terms on top of Mathlib's category theory library:

* local smallness as "all morphism collections are small" (Section 6.1);
* a one-object category is a monoid, and a functor out of the path category of a quiver is the same as a quiver
  representation (Example 6.5);
* the identity functor and the double dual functor on finite-dimensional vector spaces (Example 6.7), and the
  centre of the category of modules over a ring (Example 6.7(4));
* the forgetful functor from modules is represented by the regular module (Example 6.10);
* Morita equivalence of rings (Remark 6.16);
* adjunctions: tensoring with a representation and with its dual, group algebra and units, symmetric and tensor
  algebras, enveloping algebras (Example 6.13);
* left exact, right exact and exact additive functors via short exact sequences (Definition 6.20), and the
  standard examples (Example 6.23);
* semisimple abelian categories, and `Rep k G` being one when `|G|` is invertible in `k` (Definition 6.21,
  Example 6.22, Maschke).
-/

universe u v w

namespace UndergradKB.RepresentationTheory

open CategoryTheory CategoryTheory.Limits

/-! ### Locally small categories -/

/-- A category is locally small (relative to the universe `w`) exactly when each hom-collection is `w`-small. -/
@[kb "etingof2011" "§6.1, p. 99"]
theorem locallySmall_iff {C : Type u} [Category.{v} C] :
    LocallySmall.{w} C ↔ ∀ X Y : C, Small.{w} (X ⟶ Y) :=
  ⟨fun h => h.hom_small, fun h => ⟨h⟩⟩

/-! ### One-object categories and quiver representations (Example 6.5) -/

section Examples

/-- The endomorphism monoid of the unique object of the one-object category of a monoid `M` is `M` itself. -/
@[kb "etingof2011" "Example 6.5, p. 99"]
def singleObjEndMulEquiv (M : Type u) [Monoid M] : M ≃* End (SingleObj.star M) :=
  SingleObj.toEnd M

/-- Functors from the path category of a quiver `V` to a category `C` correspond bijectively to prefunctors
`V ⥤q C`, that is to assignments of an object to each vertex and a morphism to each arrow.  With `C` the
category of vector spaces over `k` these are the representations of the quiver. -/
@[kb "etingof2011" "Example 6.5, p. 99"]
def pathsFunctorEquiv (V : Type u) [Quiver.{v + 1} V] (C : Type*) [Category C] :
    (Paths V ⥤ C) ≃ (V ⥤q C) where
  toFun F := Paths.of V ⋙q F.toPrefunctor
  invFun φ := Paths.lift φ
  left_inv F := by
    exact (Paths.lift_unique _ F rfl).symm
  right_inv φ := Paths.lift_spec φ

end Examples

/-! ### The double dual functor (Example 6.7) -/

section DoubleDual

open Module

variable (k : Type u) [Field k]

/-- The double dual functor on finite-dimensional vector spaces. -/
noncomputable def doubleDualFunctor : FGModuleCat.{u} k ⥤ FGModuleCat.{u} k where
  obj V := FGModuleCat.of k (Dual k (Dual k V))
  map f := FGModuleCat.ofHom f.hom.hom.dualMap.dualMap
  map_id V := by ext; rfl
  map_comp f g := by ext; rfl

/-- On finite-dimensional vector spaces the identity functor is naturally isomorphic to the double dual
functor, via the evaluation map. -/
@[kb "etingof2011" "Example 6.7, p. 100"]
noncomputable def idIsoDoubleDual : 𝟭 (FGModuleCat.{u} k) ≅ doubleDualFunctor k :=
  NatIso.ofComponents (fun V => (Module.evalEquiv k V).toFGModuleCatIso) (by
    intro V W f
    ext x
    rfl)

/-- Without the finite-dimensionality hypothesis the statement fails: the evaluation map into the double dual of
an infinite-dimensional vector space is never bijective. -/
@[kb "etingof2011" "Example 6.7, p. 100"]
theorem not_bijective_eval_of_infinite (V : Type u) [AddCommGroup V] [Module k V]
    (h : ¬ FiniteDimensional k V) : ¬ Function.Bijective (Dual.eval k V) := fun hb =>
  have : IsReflexive k V := ⟨hb⟩
  h inferInstance

end DoubleDual

/-! ### The centre of the category of modules (Example 6.7) -/

section Center

variable (A : Type u) [Ring A]

/-- A natural endomorphism of the identity functor of `A`-modules acts on every module by multiplication by the
element it sends `1 ∈ A` to. -/
theorem catCenter_app_apply (φ : CatCenter (ModuleCat.{u} A)) (M : ModuleCat.{u} A) (m : M) :
    (φ.app M).hom m = ((φ.app (ModuleCat.of A A)).hom 1) • m := by
  have w := CatCenter.naturality φ (ModuleCat.ofHom (LinearMap.toSpanSingleton A M m))
  have := congr(($(ModuleCat.hom_ext_iff.mp w)) (1 : A))
  simpa using this

/-- The element of `A` obtained from a natural endomorphism of the identity functor lies in the centre. -/
theorem catCenter_mem_center (φ : CatCenter (ModuleCat.{u} A)) :
    (φ.app (ModuleCat.of A A)).hom 1 ∈ Subring.center A := by
  rw [Subring.mem_center_iff]
  intro a
  have h := catCenter_app_apply A φ (ModuleCat.of A A) a
  have h2 : (φ.app (ModuleCat.of A A)).hom a = a * (φ.app (ModuleCat.of A A)).hom 1 := by
    simpa using (φ.app (ModuleCat.of A A)).hom.map_smul a 1
  rw [h2] at h
  simpa using h

/-- The centre of the category of `A`-modules (natural endomorphisms of the identity functor) is the centre of `A`:
a central element acts on each module by multiplication, and conversely.  (The other half of the example, that
the endomorphisms of the forgetful functor form `A` itself, is Mathlib's `ringEquivEndForget₂`, stated there
for the forgetful functor to abelian groups.) -/
@[kb "etingof2011" "Example 6.7(3)(4), p. 100"]
noncomputable def catCenterModuleCatRingEquiv : CatCenter (ModuleCat.{u} A) ≃+* Subring.center A where
  toFun φ := ⟨(φ.app (ModuleCat.of A A)).hom 1, catCenter_mem_center A φ⟩
  invFun c := End.of
    { app M := ModuleCat.ofHom
        { toFun m := (c : A) • m
          map_add' := by simp
          map_smul' := by
            intro a m
            simp only [smul_smul, RingHom.id_apply]
            rw [(Subring.mem_center_iff.mp c.2 a)] }
      naturality := by
        intro M N f
        ext m
        simp }
  left_inv φ := by
    ext M m
    rw [catCenter_app_apply A φ M m]
    rfl
  right_inv c := by
    apply Subtype.ext
    show (c : A) • (1 : A) = c
    simp
  map_add' φ ψ := by
    apply Subtype.ext
    rfl
  map_mul' φ ψ := by
    apply Subtype.ext
    show ((φ * ψ).app (ModuleCat.of A A)).hom 1 = _
    rw [CatCenter.mul_app]
    show (ψ.app (ModuleCat.of A A)).hom ((φ.app (ModuleCat.of A A)).hom 1) = _
    rw [catCenter_app_apply A ψ _ ((φ.app (ModuleCat.of A A)).hom 1)]
    exact (Subring.mem_center_iff.mp (catCenter_mem_center A φ) _)

end Center

/-! ### The forgetful functor is represented by the regular module (Example 6.10) -/

section Represented

variable (A : Type u) [Ring A]

/-- The forgetful functor from left `A`-modules to sets is corepresented by the regular module `A`: an
`A`-linear map out of `A` is determined by the image of `1`, which can be any element. -/
@[kb "etingof2011" "Example 6.10, p. 102"]
def forgetCorepresentableBy : (forget (ModuleCat.{u} A)).CorepresentableBy (ModuleCat.of A A) where
  homEquiv {M} :=
    { toFun f := f.hom (1 : A)
      invFun m := ModuleCat.ofHom (LinearMap.toSpanSingleton A M m)
      left_inv f := by
        ext
        simp
      right_inv m := by simp }
  homEquiv_comp := by intros; rfl

end Represented

/-! ### Morita equivalence (Remark 6.16) -/

section Morita

/-- Two rings are Morita equivalent if their categories of left modules are equivalent. -/
@[kb "etingof2011" "Remark 6.16, p. 104"]
def MoritaEquivalentRings (A B : Type u) [Ring A] [Ring B] : Prop :=
  Nonempty (ModuleCat.{u} A ≌ ModuleCat.{u} B)

namespace MoritaEquivalentRings

/-- Every ring is Morita equivalent to itself. -/
theorem refl (A : Type u) [Ring A] : MoritaEquivalentRings A A := ⟨CategoryTheory.Equivalence.refl⟩

/-- Morita equivalence is symmetric. -/
theorem symm {A B : Type u} [Ring A] [Ring B] (h : MoritaEquivalentRings A B) : MoritaEquivalentRings B A :=
  h.map CategoryTheory.Equivalence.symm

/-- Morita equivalence is transitive. -/
theorem trans {A B C : Type u} [Ring A] [Ring B] [Ring C] (h : MoritaEquivalentRings A B)
    (h' : MoritaEquivalentRings B C) : MoritaEquivalentRings A C := by
  obtain ⟨e⟩ := h
  obtain ⟨e'⟩ := h'
  exact ⟨e.trans e'⟩

/-- A ring is Morita equivalent to the ring of `n × n` matrices over it (for `n ≥ 1`). -/
theorem matrix (R : Type u) [Ring R] (ι : Type u) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    MoritaEquivalentRings R (Matrix ι ι R) := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact ⟨ModuleCat.matrixEquivalence R i⟩

end MoritaEquivalentRings

end Morita

/-! ### Tensoring with a representation and its dual (Example 6.13(1)) -/

section TensorDual

open MonoidalCategory

/-- For a finite-dimensional representation `V` of a group, tensoring with `V` has the functor tensoring with the
dual `V*` as a right adjoint and as a left adjoint. -/
@[kb "etingof2011" "Example 6.13(1), p. 103"]
theorem fdrep_tensorLeft_adjunctions {k G : Type u} [Field k] [Group G] (V : FDRep k G) :
    Nonempty (tensorLeft V ⊣ tensorLeft Vᘁ) ∧ Nonempty (tensorLeft Vᘁ ⊣ tensorLeft V) :=
  ⟨⟨@tensorLeftAdjunction _ _ _ Vᘁ V (BraidedCategory.exactPairing_swap V Vᘁ)⟩, ⟨tensorLeftAdjunction V Vᘁ⟩⟩

end TensorDual

/-! ### Group algebra and units (Example 6.13(4)) -/

section GroupAlgebra

variable (k : Type u) [CommRing k]

/-- The group of units of an algebra, as a functor from `k`-algebras to groups. -/
def algUnitsFunctor : AlgCat.{u} k ⥤ GrpCat.{u} where
  obj A := GrpCat.of Aˣ
  map f := GrpCat.ofHom (Units.map f.hom.toMonoidHom)
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- Group homomorphisms `G → Aˣ` correspond to algebra homomorphisms `k[G] → A`. -/
noncomputable def groupAlgebraHomEquiv (G : GrpCat.{u}) (A : AlgCat.{u} k) :
    (AlgCat.of k (MonoidAlgebra k G) ⟶ A) ≃ (G ⟶ (algUnitsFunctor k).obj A) where
  toFun h := GrpCat.ofHom (MonoidHom.toHomUnits
    ((h.hom : MonoidAlgebra k G →* A).comp (MonoidAlgebra.of k G)))
  invFun f := AlgCat.ofHom (MonoidAlgebra.lift k A G ((Units.coeHom A).comp f.hom))
  left_inv h := by
    apply AlgCat.hom_ext
    refine Eq.trans ?_ (MonoidAlgebra.lift_unique' h.hom).symm
    congr 1
  right_inv f := by
    ext g
    simp
    rfl

theorem groupAlgebraHomEquiv_naturality (X : GrpCat.{u}) (Y Y' : AlgCat.{u} k) (g : Y ⟶ Y')
    (h : AlgCat.of k (MonoidAlgebra k X) ⟶ Y) :
    groupAlgebraHomEquiv k X Y' (h ≫ g) = groupAlgebraHomEquiv k X Y h ≫ (algUnitsFunctor k).map g := by
  ext x
  simp [groupAlgebraHomEquiv, algUnitsFunctor]
  rfl

/-- The group algebra functor `G ↦ k[G]` from groups to `k`-algebras. -/
noncomputable def groupAlgebraFunctor : GrpCat.{u} ⥤ AlgCat.{u} k :=
  Adjunction.leftAdjointOfEquiv (G := algUnitsFunctor k) (F_obj := fun G => AlgCat.of k (MonoidAlgebra k G))
    (groupAlgebraHomEquiv k) (groupAlgebraHomEquiv_naturality k)

/-- The group algebra functor is left adjoint to the functor taking an algebra to its group of units. -/
@[kb "etingof2011" "Example 6.13(4), p. 103"]
noncomputable def groupAlgebraAdjunction : groupAlgebraFunctor k ⊣ algUnitsFunctor k :=
  Adjunction.adjunctionOfEquivLeft _ _

end GroupAlgebra

/-! ### Symmetric and tensor algebras (Example 6.13(5)) -/

section Symmetric

variable (R : Type u) [CommRing R]

/-- Forgetting a commutative algebra to its underlying module. -/
noncomputable def commAlgForget : CommAlgCat.{u} R ⥤ ModuleCat.{u} R :=
  forget₂ (CommAlgCat.{u} R) (AlgCat.{u} R) ⋙ forget₂ (AlgCat.{u} R) (ModuleCat.{u} R)

/-- Linear maps `M → A` correspond to algebra maps `S(M) → A` for commutative algebras `A`. -/
noncomputable def symmetricAlgebraHomEquiv (M : ModuleCat.{u} R) (A : CommAlgCat.{u} R) :
    (CommAlgCat.of R (SymmetricAlgebra R M) ⟶ A) ≃ (M ⟶ (commAlgForget R).obj A) where
  toFun h := ModuleCat.ofHom (h.hom.toLinearMap ∘ₗ SymmetricAlgebra.ι R M)
  invFun f := CommAlgCat.ofHom (SymmetricAlgebra.lift f.hom)
  left_inv h := by
    apply CommAlgCat.hom_ext
    apply SymmetricAlgebra.algHom_ext
    ext x
    exact SymmetricAlgebra.lift_ι_apply (h.hom.toLinearMap ∘ₗ SymmetricAlgebra.ι R M) x
  right_inv f := by
    ext x
    simp
    rfl

theorem symmetricAlgebraHomEquiv_naturality (M : ModuleCat.{u} R) (A A' : CommAlgCat.{u} R) (g : A ⟶ A')
    (h : CommAlgCat.of R (SymmetricAlgebra R M) ⟶ A) :
    symmetricAlgebraHomEquiv R M A' (h ≫ g) =
      symmetricAlgebraHomEquiv R M A h ≫ (commAlgForget R).map g := by
  ext x
  rfl

/-- The symmetric algebra functor from modules to commutative algebras. -/
noncomputable def symmetricAlgebraFunctor : ModuleCat.{u} R ⥤ CommAlgCat.{u} R :=
  Adjunction.leftAdjointOfEquiv (G := commAlgForget R) (F_obj := fun M => CommAlgCat.of R (SymmetricAlgebra R M))
    (symmetricAlgebraHomEquiv R) (symmetricAlgebraHomEquiv_naturality R)

/-- The symmetric algebra functor is left adjoint to the forgetful functor from commutative algebras to
modules. -/
@[kb "etingof2011" "Example 6.13(5), p. 103"]
noncomputable def symmetricAlgebraAdjunction : symmetricAlgebraFunctor R ⊣ commAlgForget R :=
  Adjunction.adjunctionOfEquivLeft _ _

/-- The tensor algebra functor is left adjoint to the forgetful functor from algebras to modules (this is
Mathlib's `AlgCat.tensorAlgebraAdj`). -/
@[kb "etingof2011" "Example 6.13(5), p. 103"]
noncomputable def tensorAlgebraAdjunction :
    AlgCat.tensorAlgebra.{u} R ⊣ forget₂ (AlgCat.{u} R) (ModuleCat.{u} R) :=
  AlgCat.tensorAlgebraAdj R

end Symmetric

/-! ### Universal enveloping algebra (Example 6.13(3)) -/

section Enveloping

open UniversalEnvelopingAlgebra

variable (R : Type u) [CommRing R] {L : Type v} [LieRing L] [LieAlgebra R L]
  {A : Type w} [Ring A] [Algebra R A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The universal enveloping algebra is left adjoint to the associative-algebra-to-Lie-algebra functor: the
bijection `Hom_Lie(L, A) ≃ Hom_alg(U L, A)` is natural in the algebra `A`.  Stated without categories of Lie
algebras, since Mathlib has none. -/
@[kb "etingof2011" "Example 6.13(3), p. 103"]
theorem enveloping_lift_natural {B : Type w} [Ring B] [Algebra R B] (f : L →ₗ⁅R⁆ A) (g : A →ₐ[R] B) :
    lift R (g.toLieHom.comp f) = g.comp (lift R f) := by
  apply (lift R).symm.injective
  ext x
  simp

end Enveloping

/-! ### Exactness of functors (Definition 6.20) -/

section Exactness

variable {C : Type u} {D : Type v} [Category.{w} C] [Category.{w} D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive]

/-- An additive functor is left exact if it sends every short exact sequence `0 → X → Y → Z → 0` to a sequence
`0 → F X → F Y → F Z` that is exact in the left and middle spots. -/
def IsLeftExactFunctor : Prop :=
  ∀ S : ShortComplex C, S.ShortExact → (S.map F).Exact ∧ Mono (F.map S.f)

/-- An additive functor is right exact if it sends every short exact sequence to a sequence
`F X → F Y → F Z → 0` that is exact in the middle and right spots. -/
def IsRightExactFunctor : Prop :=
  ∀ S : ShortComplex C, S.ShortExact → (S.map F).Exact ∧ Epi (F.map S.g)

/-- An additive functor is exact if it sends short exact sequences to short exact sequences. -/
def IsExactFunctor : Prop :=
  ∀ S : ShortComplex C, S.ShortExact → (S.map F).ShortExact

/-- Left exactness in the book's sense is the same as preserving finite limits. -/
@[kb "etingof2011" "Definition 6.20, p. 104"]
theorem isLeftExactFunctor_iff : IsLeftExactFunctor F ↔ PreservesFiniteLimits F :=
  (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono F).symm

/-- Right exactness in the book's sense is the same as preserving finite colimits. -/
@[kb "etingof2011" "Definition 6.20, p. 104"]
theorem isRightExactFunctor_iff : IsRightExactFunctor F ↔ PreservesFiniteColimits F :=
  (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi F).symm

/-- Exactness in the book's sense is the same as preserving both finite limits and finite colimits. -/
@[kb "etingof2011" "Definition 6.20, p. 104"]
theorem isExactFunctor_iff :
    IsExactFunctor F ↔ PreservesFiniteLimits F ∧ PreservesFiniteColimits F :=
  (Functor.exact_tfae F).out 1 4

/-- A functor is exact exactly when it is both left and right exact. -/
theorem isExactFunctor_iff_left_right : IsExactFunctor F ↔ IsLeftExactFunctor F ∧ IsRightExactFunctor F := by
  rw [isExactFunctor_iff, isLeftExactFunctor_iff, isRightExactFunctor_iff]

end Exactness

/-! ### Examples of exact functors (Example 6.23) -/

section ExactExamples

/-- Restriction of representations along a group homomorphism is an exact functor. -/
@[kb "etingof2011" "Example 6.23, p. 105"]
theorem isExactFunctor_resFunctor {k : Type u} [CommRing k] {G H : Type u} [Group G] [Group H] (φ : H →* G) :
    IsExactFunctor (Rep.resFunctor (k := k) φ) :=
  fun _ hS => Rep.shortExact_res φ |>.2 hS

/-- `Hom(X, -)` is left exact. -/
@[kb "etingof2011" "Example 6.23, p. 105"]
theorem isLeftExactFunctor_preadditiveCoyonedaObj {C : Type u} [Category.{v} C] [Abelian C] (X : C) :
    IsLeftExactFunctor (preadditiveCoyonedaObj X) := by
  rw [isLeftExactFunctor_iff]
  infer_instance

/-- `Hom(X, -)` is not right exact in general: for `X = Z/2` over the integers it fails to preserve the
surjection `Z → Z/2`, because `Z/2` is not projective. -/
@[kb "etingof2011" "Example 6.23, p. 105"]
theorem not_isRightExactFunctor_preadditiveCoyonedaObj_zmod_two :
    ¬ IsRightExactFunctor (preadditiveCoyonedaObj (ModuleCat.of ℤ (ZMod 2))) := by
  rw [isRightExactFunctor_iff]
  intro h
  have hP : Projective (ModuleCat.of ℤ (ZMod 2)) :=
    projective_of_preservesFiniteColimits_preadditiveCoyonedaObj _
  have hp : Module.Projective ℤ (ZMod 2) :=
    ModuleCat.projective_of_module_projective (ModuleCat.of ℤ (ZMod 2))
  obtain ⟨s, hs⟩ := Module.projective_lifting_property
    (AddMonoidHom.toIntLinearMap (Int.castAddHom (ZMod 2))) (LinearMap.id : ZMod 2 →ₗ[ℤ] ZMod 2)
    (fun x => ⟨x.val, by simp⟩)
  have h2 : (2 : ℤ) • s 1 = 0 := by
    rw [← map_smul]
    have : (2 : ℤ) • (1 : ZMod 2) = 0 := by decide
    rw [this, map_zero]
  have h0 : s 1 = 0 := by simpa using h2
  have h1 := LinearMap.congr_fun hs 1
  rw [LinearMap.comp_apply, h0] at h1
  revert h1
  decide

/-- Tensoring with a module over a commutative ring is right exact. -/
@[kb "etingof2011" "Example 6.23, p. 105"]
theorem isRightExactFunctor_tensorLeft {R : Type u} [CommRing R] (X : ModuleCat.{u} R) :
    IsRightExactFunctor (MonoidalCategory.tensorLeft X) := by
  rw [isRightExactFunctor_iff]
  infer_instance

/-- Tensoring is not left exact in general: tensoring the injection `Z → Z` (multiplication by `2`) with `Z/2`
gives the zero map on the nonzero module `Z/2 ⊗ Z`. -/
@[kb "etingof2011" "Example 6.23, p. 105"]
theorem not_isLeftExactFunctor_tensorLeft_zmod_two :
    ¬ IsLeftExactFunctor (MonoidalCategory.tensorLeft (ModuleCat.of ℤ (ZMod 2))) := by
  rw [isLeftExactFunctor_iff]
  intro h
  let f : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ := ModuleCat.ofHom (LinearMap.lsmul ℤ ℤ 2)
  have hmono : Mono f := (ModuleCat.mono_iff_injective f).2 (by
    intro a b hab
    have h2 : (2 : ℤ) * a = 2 * b := hab
    exact mul_left_cancel₀ (two_ne_zero : (2 : ℤ) ≠ 0) h2)
  have hm : Mono ((MonoidalCategory.tensorLeft (ModuleCat.of ℤ (ZMod 2))).map f) := inferInstance
  rw [ModuleCat.mono_iff_injective] at hm
  have key : ((MonoidalCategory.tensorLeft (ModuleCat.of ℤ (ZMod 2))).map f).hom
      ((1 : ZMod 2) ⊗ₜ[ℤ] (1 : ℤ)) = 0 := by
    show (LinearMap.lTensor (ZMod 2) (LinearMap.lsmul ℤ ℤ 2)) ((1 : ZMod 2) ⊗ₜ[ℤ] (1 : ℤ)) = 0
    rw [LinearMap.lTensor_tmul]
    have : (LinearMap.lsmul ℤ ℤ 2) (1 : ℤ) = (2 : ℤ) • (1 : ℤ) := rfl
    rw [this, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    have h2 : (2 : ℤ) • (1 : ZMod 2) = 0 := by decide
    rw [h2, TensorProduct.zero_tmul]
  have h0 := hm (key.trans (map_zero _).symm)
  have := congrArg (TensorProduct.rid ℤ (ZMod 2)) h0
  revert this
  simp

end ExactExamples

/-! ### Semisimple abelian categories (Definition 6.21, Example 6.22) -/

section Semisimple

/-- An abelian category is semisimple if every short exact sequence splits. -/
@[kb "etingof2011" "Definition 6.21, p. 105"]
def IsSemisimpleAbelianCategory (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  ∀ S : ShortComplex C, S.ShortExact → Nonempty S.Splitting

/-- Maschke, categorical form: if `G` is finite and its order is nonzero in the field `k`, the category of
representations of `G` over `k` is semisimple, since every representation is projective. -/
@[kb "etingof2011" "Example 6.22, p. 105"]
theorem isSemisimpleAbelianCategory_rep {k : Type u} [Field k] {G : Type u} [Group G] [Finite G]
    [NeZero (Nat.card G : k)] : IsSemisimpleAbelianCategory (Rep.{u} k G) :=
  fun _ hS => ⟨hS.splittingOfProjective⟩

end Semisimple

end UndergradKB.RepresentationTheory
