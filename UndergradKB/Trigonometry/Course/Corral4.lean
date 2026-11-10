import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import UndergradKB.Common.Attr

/-! # Course layer: Corral, *Trigonometry*, Chapter 4

Thin theorems in the book's terms whose proofs are Mathlib declarations.  All angles are in
radians.
-/

namespace UndergradKB.Trigonometry.Course.Corral

/-- For positive angles the sine is strictly smaller than the angle itself (TR-105). -/
@[kb "corraltrig" "Box §4.3, p. 104"]
theorem box_4_3_sin_lt (θ : ℝ) (h : 0 < θ) : Real.sin θ < θ :=
  Real.sin_lt h

end UndergradKB.Trigonometry.Course.Corral
