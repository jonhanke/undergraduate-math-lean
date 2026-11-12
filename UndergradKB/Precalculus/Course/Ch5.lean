import Mathlib.Logic.Function.Basic
import Mathlib.Basic.Real.Basic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 5 (Stitz-Zeager): composition, inverses, one-to-one functions -/

namespace UndergradKB.Precalculus.Course

/-- Definition 5.1: the composite `g ∘ f` sends `x` to `g (f x)` (PC-080). -/
@[kb "stitzzeager2013" "Definition 5.1, p. 372"]
theorem def_5_1_composition (f g : ℝ → ℝ) (x : ℝ) : (g ∘ f) x = g (f x) :=
  rfl

/-- Theorem 5.1: composition is associative, and the identity function is a two-sided unit (PC-081). -/
@[kb "stitzzeager2013" "Theorem 5.1, p. 379"]
theorem thm_5_1_composition_assoc_id (f g h : ℝ → ℝ) :
    (h ∘ g) ∘ f = h ∘ (g ∘ f) ∧ id ∘ f = f ∧ f ∘ id = f :=
  ⟨Function.comp_assoc h g f, Function.id_comp f, Function.comp_id f⟩

/-- Definition 5.2: `g` is an inverse of `f` when `g (f x) = x` and `f (g x) = x` for all `x`; a function that has an
inverse is exactly a bijection (PC-082). -/
@[kb "stitzzeager2013" "Definition 5.2, p. 391"]
theorem def_5_2_inverse_functions (f : ℝ → ℝ) :
    (∃ g : ℝ → ℝ, (∀ x, g (f x) = x) ∧ (∀ x, f (g x) = x)) ↔ Function.Bijective f :=
  Function.bijective_iff_has_inverse.symm

/-- Definition 5.3: `f` is one-to-one when `f c = f d` forces `c = d` (PC-085). -/
@[kb "stitzzeager2013" "Definition 5.3, p. 393"]
theorem def_5_3_one_to_one (f : ℝ → ℝ) :
    Function.Injective f ↔ ∀ c d : ℝ, f c = f d → c = d :=
  Iff.rfl

end UndergradKB.Precalculus.Course
