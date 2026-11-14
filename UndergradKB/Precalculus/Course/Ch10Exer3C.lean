import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 10 (Stitz-Zeager): exercises with the book's answers (wave 8), Sections 10.6 and 10.7 -/

namespace UndergradKB.Precalculus.Course

open Real

/-- Stitz-Zeager Exercise 10.6.226: `arctan(4x)` is defined for every real `x` (domain `(-∞, ∞)`), with
values strictly between `-π/2` and `π/2`. -/
@[kb "stitzzeager2013" "Exercise 10.6.226, p. 859"]
theorem exer_10_6_226 : ∀ x : ℝ, arctan (4 * x) ∈ Set.Ioo (-(π / 2)) (π / 2) :=
  fun x => ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩

end UndergradKB.Precalculus.Course
