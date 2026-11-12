import Mathlib.Basic.Rel
import Mathlib.Data.Set.Image
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Function.Basic
import UndergradKB.Common

/-!
# Course layer: Hammack, Book of Proof, Chapter 12 (functions)

Thin theorems in the book's terms for the function rows of the Foundations checklist that are already in Mathlib.
-/

namespace UndergradKB.Foundations.Course

/-- FO-076. The inverse relation contains `(y, x)` exactly when the relation contains `(x, y)`. -/
@[kb "hammack2018" "Def 12.7, p. 251", kb "levin2025" "Def 2.6.6, p. 188"]
theorem hammack_def_12_7_inverse_relation {A B : Type*} (R : SetRel A B) (x : A) (y : B) :
    (y, x) ∈ R.inv ↔ (x, y) ∈ R :=
  SetRel.mem_inv

/-- FO-079. The range of `f` is the set of values `f x`. -/
@[kb "hammack2018" "Def 12.2, p. 237", kb "levin2025" "Summary §5.2, p. 433"]
theorem hammack_def_12_2_range {A B : Type*} (f : A → B) (y : B) :
    y ∈ Set.range f ↔ ∃ x, f x = y :=
  Set.mem_range

/-- FO-080. Two functions are equal iff they agree everywhere. -/
@[kb "hammack2018" "Def 12.3, p. 239"]
theorem hammack_def_12_3_function_ext {A B : Type*} (f g : A → B) : f = g ↔ ∀ x, f x = g x :=
  funext_iff

/-- FO-081. Injective: distinct inputs have distinct outputs. -/
@[kb "hammack2018" "Def 12.4, p. 240", kb "levin2025" "Box §5.2.2, p. 431"]
theorem hammack_def_12_4_injective {A B : Type*} (f : A → B) :
    Function.Injective f ↔ ∀ x y, x ≠ y → f x ≠ f y := by
  constructor
  · exact fun h x y hxy hf => hxy (h hf)
  · exact fun h x y hf => by_contra fun hxy => h x y hxy hf

/-- FO-082. Surjective: every element of the codomain is hit. -/
@[kb "hammack2018" "Def 12.4, p. 240", kb "levin2025" "Box §5.2.2, p. 431"]
theorem hammack_def_12_4_surjective {A B : Type*} (f : A → B) :
    Function.Surjective f ↔ ∀ y, ∃ x, f x = y :=
  Iff.rfl

/-- FO-083. Bijective means injective and surjective. -/
@[kb "hammack2018" "Def 12.4, p. 240", kb "levin2025" "Text §5.2.2, p. 431"]
theorem hammack_def_12_4_bijective {A B : Type*} (f : A → B) :
    Function.Bijective f ↔ Function.Injective f ∧ Function.Surjective f :=
  Iff.rfl

/-- FO-084. Pigeonhole: more elements in the domain than the codomain forbids injectivity; fewer forbids
surjectivity. -/
@[kb "hammack2018" "Prop §12.3, p. 245"]
theorem hammack_s12_3_pigeonhole {A B : Type*} [Fintype A] [Fintype B] (f : A → B) :
    (Fintype.card B < Fintype.card A → ¬ Function.Injective f) ∧
      (Fintype.card A < Fintype.card B → ¬ Function.Surjective f) := by
  refine ⟨fun h hf => ?_, fun h hf => ?_⟩
  · obtain ⟨x, y, hne, hxy⟩ := Fintype.exists_ne_map_eq_of_card_lt f h
    exact hne (hf hxy)
  · exact absurd (Fintype.card_le_of_surjective f hf) (not_le.mpr h)

/-- FO-086. The composite `g ∘ f` sends `x` to `g (f x)`. -/
@[kb "hammack2018" "Def 12.5, p. 247"]
theorem hammack_def_12_5_comp {A B C : Type*} (f : A → B) (g : B → C) (x : A) :
    (g ∘ f) x = g (f x) :=
  rfl

/-- FO-087. Composition of functions is associative. -/
@[kb "hammack2018" "Thm 12.1, p. 249"]
theorem hammack_thm_12_1_comp_assoc {A B C D : Type*} (f : A → B) (g : B → C) (h : C → D) :
    h ∘ (g ∘ f) = (h ∘ g) ∘ f :=
  rfl

/-- FO-088. Composites of injective (resp. surjective) functions are injective (resp. surjective). -/
@[kb "hammack2018" "Thm 12.2, p. 249"]
theorem hammack_thm_12_2_comp {A B C : Type*} {f : A → B} {g : B → C}
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hf' : Function.Surjective f) (hg' : Function.Surjective g) :
    Function.Injective (g ∘ f) ∧ Function.Surjective (g ∘ f) :=
  ⟨hg.comp hf, hg'.comp hf'⟩

/-- FO-089. The identity function is bijective. -/
@[kb "hammack2018" "Def 12.6, p. 250"]
theorem hammack_def_12_6_id_bijective {A : Type*} : Function.Bijective (id : A → A) :=
  Function.bijective_id

/-- FO-091. A bijection has an inverse function that undoes it on both sides. -/
@[kb "hammack2018" "Def 12.8, p. 252"]
theorem hammack_def_12_8_inverse {A B : Type*} (f : A → B) (hf : Function.Bijective f) :
    ∃ g : B → A, g ∘ f = id ∧ f ∘ g = id :=
  ⟨(Equiv.ofBijective f hf).symm, funext (Equiv.ofBijective f hf).symm_apply_apply,
    funext (Equiv.ofBijective f hf).apply_symm_apply⟩

/-- FO-092. Membership in the image `f(X)` and in the preimage `f⁻¹(Y)`. -/
@[kb "hammack2018" "Def 12.9, p. 254", kb "levin2025" "Text §5.2.3, p. 431"]
theorem hammack_def_12_9_image_preimage {A B : Type*} (f : A → B) (X : Set A) (Y : Set B) (y : B) (x : A) :
    (y ∈ f '' X ↔ ∃ a ∈ X, f a = y) ∧ (x ∈ f ⁻¹' Y ↔ f x ∈ Y) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- FO-093. `f(W ∩ X) ⊆ f(W) ∩ f(X)`. -/
@[kb "hammack2018" "Thm 12.4(1), p. 255"]
theorem hammack_thm_12_4_1 {A B : Type*} (f : A → B) (W X : Set A) :
    f '' (W ∩ X) ⊆ f '' W ∩ f '' X :=
  Set.image_inter_subset f W X

/-- FO-094. `f(W ∪ X) = f(W) ∪ f(X)`. -/
@[kb "hammack2018" "Thm 12.4(2), p. 255"]
theorem hammack_thm_12_4_2 {A B : Type*} (f : A → B) (W X : Set A) :
    f '' (W ∪ X) = f '' W ∪ f '' X :=
  Set.image_union f W X

/-- FO-095. `X ⊆ f⁻¹(f(X))`. -/
@[kb "hammack2018" "Thm 12.4(3), p. 255"]
theorem hammack_thm_12_4_3 {A B : Type*} (f : A → B) (X : Set A) : X ⊆ f ⁻¹' (f '' X) :=
  Set.subset_preimage_image f X

/-- FO-096. `f⁻¹(Y ∪ Z) = f⁻¹(Y) ∪ f⁻¹(Z)`. -/
@[kb "hammack2018" "Thm 12.4(4), p. 255"]
theorem hammack_thm_12_4_4 {A B : Type*} (f : A → B) (Y Z : Set B) :
    f ⁻¹' (Y ∪ Z) = f ⁻¹' Y ∪ f ⁻¹' Z :=
  Set.preimage_union

/-- FO-097. `f⁻¹(Y ∩ Z) = f⁻¹(Y) ∩ f⁻¹(Z)`. -/
@[kb "hammack2018" "Thm 12.4(5), p. 255"]
theorem hammack_thm_12_4_5 {A B : Type*} (f : A → B) (Y Z : Set B) :
    f ⁻¹' (Y ∩ Z) = f ⁻¹' Y ∩ f ⁻¹' Z :=
  Set.preimage_inter

/-- FO-098. `f(f⁻¹(Y)) ⊆ Y`. -/
@[kb "hammack2018" "Thm 12.4(6), p. 255"]
theorem hammack_thm_12_4_6 {A B : Type*} (f : A → B) (Y : Set B) : f '' (f ⁻¹' Y) ⊆ Y :=
  Set.image_preimage_subset f Y

end UndergradKB.Foundations.Course
