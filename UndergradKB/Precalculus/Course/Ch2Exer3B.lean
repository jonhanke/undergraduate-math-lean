import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 2 (Stitz-Zeager): exercises with the book's answers (wave 8), Section 2.4, definite fact
of an exercise that prints no answer -/

namespace UndergradKB.Precalculus.Course

/-- Stitz-Zeager Exercise 2.4.44: `|f(x) - L| < ε` means `L - ε < f(x) < L + ε` (the value of `f` is within `ε` of
`L`). -/
@[kb "stitzzeager2013" "Exercise 2.4.44, p. 233"]
theorem exer_2_4_44 (f : ℝ → ℝ) (L ε : ℝ) (x : ℝ) :
    |f x - L| < ε ↔ L - ε < f x ∧ f x < L + ε := by
  rw [abs_lt]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

end UndergradKB.Precalculus.Course
