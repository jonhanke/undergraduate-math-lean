import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Yoneda
import Mathlib.RepresentationTheory.FiniteIndex
import UndergradKB.Common.Attr

/-!
# Etingof et al., Introduction to Representation Theory: Chapter 6 (introduction to categories)

Thin theorems in the book's terms for the items of Chapter 6 that Mathlib already contains,
each tagged with the source key `etingof2011` and the locator of the item in the book.
-/

namespace UndergradKB.RepresentationTheory.Course

open CategoryTheory

universe u v w

/-- Etingof et al., Definition 6.1: a category has associative composition and identity
morphisms that are units for composition. -/
@[kb "etingof2011" "Definition 6.1, p. 98"]
theorem etingof_6_1 {C : Type*} [Category C] {W X Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f ≫ g) ≫ h = f ≫ g ≫ h ∧ 𝟙 W ≫ f = f ∧ f ≫ 𝟙 X = f :=
  ⟨Category.assoc f g h, Category.id_comp f, Category.comp_id f⟩

/-- Etingof et al., Section 6.1: a category enriched over vector spaces (such as the category of
representations of an algebra) is linear: composition is bilinear in the morphisms. -/
@[kb "etingof2011" "§6.1, p. 99"]
theorem etingof_sec_6_1 {k C : Type*} [Semiring k] [Category C] [Preadditive C] [Linear k C]
    {X Y Z : C} (r : k) (f : X ⟶ Y) (g : Y ⟶ Z) :
    (r • f) ≫ g = r • (f ≫ g) ∧ f ≫ (r • g) = r • (f ≫ g) :=
  ⟨Linear.smul_comp X Y Z r f g, Linear.comp_smul X Y Z f r g⟩

/-- Etingof et al., Definition 6.3: a full subcategory has the objects satisfying a property and
the same morphisms; the inclusion functor is fully faithful. -/
@[kb "etingof2011" "Definition 6.3, p. 99"]
theorem etingof_6_3 {C : Type*} [Category C] (P : ObjectProperty C) :
    Nonempty P.ι.FullyFaithful :=
  ⟨P.fullyFaithfulι⟩

/-- Etingof et al., Definition 6.4: a functor preserves composition and identities. -/
@[kb "etingof2011" "Definition 6.4, p. 99"]
theorem etingof_6_4 {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Y)
    (g : Y ⟶ Z) : F.map (f ≫ g) = F.map f ≫ F.map g ∧ F.map (𝟙 X) = 𝟙 (F.obj X) :=
  ⟨F.map_comp f g, F.map_id X⟩

/-- Etingof et al., Definition 6.6: a morphism of functors is natural: its components commute
with the images of every morphism. -/
@[kb "etingof2011" "Definition 6.6, p. 100"]
theorem etingof_6_6_a {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (α : F ⟶ G) {X Y : C}
    (f : X ⟶ Y) : F.map f ≫ α.app Y = α.app X ≫ G.map f :=
  α.naturality f

/-- Etingof et al., Definition 6.6: a morphism of functors is an isomorphism as soon as all its
components are isomorphisms. -/
@[kb "etingof2011" "Definition 6.6, p. 100"]
theorem etingof_6_6_b {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (α : F ⟶ G)
    [∀ X, IsIso (α.app X)] : IsIso α :=
  NatIso.isIso_of_isIso_app α

/-- Etingof et al., Definition 6.8: an equivalence of categories consists of functors in both
directions whose two composites are isomorphic to the identity functors. -/
@[kb "etingof2011" "Definition 6.8, p. 101"]
theorem etingof_6_8 {C D : Type*} [Category C] [Category D] (e : C ≌ D) :
    Nonempty (𝟭 C ≅ e.functor ⋙ e.inverse) ∧ Nonempty (e.inverse ⋙ e.functor ≅ 𝟭 D) :=
  ⟨⟨e.unitIso⟩, ⟨e.counitIso⟩⟩

/-- Etingof et al., Section 6.5: a set-valued functor is representable when it is isomorphic to a
Hom functor out of some object. -/
@[kb "etingof2011" "§6.5, p. 101"]
theorem etingof_sec_6_5 {C : Type u} [Category.{v} C] (F : Cᵒᵖ ⥤ Type v) :
    F.IsRepresentable ↔ ∃ X : C, Nonempty (F.RepresentableBy X) :=
  ⟨fun h => h.has_representation, fun h => ⟨h⟩⟩

/-- Etingof et al., Lemma 6.9: a representing object of a functor is unique up to isomorphism. -/
@[kb "etingof2011" "Lemma 6.9, p. 102"]
theorem etingof_6_9 {C : Type u} [Category.{v} C] {F : Cᵒᵖ ⥤ Type v} {X Y : C}
    (hX : F.RepresentableBy X) (hY : F.RepresentableBy Y) : Nonempty (X ≅ Y) :=
  ⟨hX.uniqueUpToIso hY⟩

/-- Etingof et al., Definition 6.11: adjoint functors come with natural bijections between
`Hom (F X, Y)` and `Hom (X, G Y)`. -/
@[kb "etingof2011" "Definition 6.11, p. 102"]
theorem etingof_6_11 {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) (X : C) (Y : D) : Nonempty ((F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y)) :=
  ⟨adj.homEquiv X Y⟩

/-- Etingof et al., Section 6.6: left adjoints of a given functor are unique up to isomorphism. -/
@[kb "etingof2011" "§6.6, p. 102"]
theorem etingof_sec_6_6 {C D : Type*} [Category C] [Category D] {F F' : C ⥤ D} {G : D ⥤ C}
    (adj₁ : F ⊣ G) (adj₂ : F' ⊣ G) : Nonempty (F ≅ F') :=
  ⟨adj₁.leftAdjointUniq adj₂⟩

open scoped Classical in
/-- Etingof et al., Example 6.13(2): for a subgroup of finite index, the restriction functor
`Rep k G ⥤ Rep k K` is left adjoint to induction (Frobenius reciprocity). -/
@[kb "etingof2011" "Example 6.13(2), p. 103"]
theorem etingof_6_13_2 {k : Type u} {G : Type v} [CommRing k] [Group G] (K : Subgroup G)
    [K.FiniteIndex] :
    Nonempty (Rep.resFunctor.{max w u v} (k := k) K.subtype ⊣
      Rep.indFunctor.{max w u v} k K.subtype) :=
  ⟨Rep.resIndAdjunction.{w, u, v} k K⟩

/-- Etingof et al., Example 6.15: modules over a ring form an abelian category. -/
@[kb "etingof2011" "Example 6.15, p. 104"]
theorem etingof_6_15_a (A : Type u) [Ring A] : Nonempty (Abelian (ModuleCat.{v} A)) :=
  ⟨inferInstance⟩

/-- Etingof et al., Example 6.15: finite-dimensional vector spaces form an abelian category. -/
@[kb "etingof2011" "Example 6.15, p. 104"]
theorem etingof_6_15_b (k : Type u) [Field k] : Nonempty (Abelian (FGModuleCat k)) :=
  ⟨inferInstance⟩

/-- Etingof et al., Section 6.7: in a `k`-linear abelian category, composition of morphisms is
bilinear. -/
@[kb "etingof2011" "§6.7, p. 104"]
theorem etingof_sec_6_7 {k C : Type*} [Semiring k] [Category C] [Abelian C] [Linear k C]
    {X Y Z : C} (r : k) (f : X ⟶ Y) (g : Y ⟶ Z) :
    (r • f) ≫ g = r • (f ≫ g) ∧ f ≫ (r • g) = r • (f ≫ g) :=
  etingof_sec_6_1 r f g

/-- Etingof et al., Definition 6.17: a sequence of modules `X₁ → X₂ → X₃` is exact when every
element of `X₂` killed by the second map comes from `X₁`. -/
@[kb "etingof2011" "Definition 6.17, p. 104"]
theorem etingof_6_17 {R : Type u} [Ring R] (S : ShortComplex (ModuleCat.{v} R)) :
    S.Exact ↔ ∀ x₂ : S.X₂, S.g x₂ = 0 → ∃ x₁ : S.X₁, S.f x₁ = x₂ :=
  ShortComplex.moduleCat_exact_iff S

/-- Etingof et al., Definition 6.18: an additive functor induces additive maps on morphisms. -/
@[kb "etingof2011" "Definition 6.18, p. 104"]
theorem etingof_6_18 {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] {X Y : C} (f g : X ⟶ Y) : F.map (f + g) = F.map f + F.map g :=
  F.map_add

/-- Etingof et al., Exercise after Definition 6.18: a left adjoint preserves all colimits (hence
is right exact). -/
@[kb "etingof2011" "Exercise, p. 105"]
theorem etingof_6_exercise_a {C D : Type u} [Category.{v} C] [Category.{v} D] {F : C ⥤ D}
    {G : D ⥤ C} (adj : F ⊣ G) : Nonempty (Limits.PreservesColimitsOfSize.{v, v} F) :=
  ⟨adj.leftAdjoint_preservesColimits⟩

/-- Etingof et al., Exercise after Definition 6.18: a right adjoint preserves all limits (hence is
left exact). -/
@[kb "etingof2011" "Exercise, p. 105"]
theorem etingof_6_exercise_b {C D : Type u} [Category.{v} C] [Category.{v} D] {F : C ⥤ D}
    {G : D ⥤ C} (adj : F ⊣ G) : Nonempty (Limits.PreservesLimitsOfSize.{v, v} G) :=
  ⟨adj.rightAdjoint_preservesLimits⟩

end UndergradKB.RepresentationTheory.Course
