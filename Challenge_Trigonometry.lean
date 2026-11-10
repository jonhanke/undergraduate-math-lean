/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import UndergradKB.Trigonometry.Triangle.Heron
import UndergradKB.Trigonometry.Triangle.Tangents
import UndergradKB.Trigonometry.CosFixedPoint

/-!
# Headline statements of undergraduate-math-lean 0.1.0: trigonometry (Corral)

The main results of this topic that Mathlib and Tau Ceti lack, one theorem each, with every proof a deliberate
`sorry`: Heron's formula for the area of a triangle, the law of tangents, and the facts that `cos x = x` has
exactly one real solution and that iterating the cosine converges to it. To check what is claimed, read this file.
`Solution_Trigonometry.lean` proves the same statements from the library, and `lake comparator` (configured by
`comparator/Trigonometry.json`) checks that each proved statement is exactly the one here and uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Each statement is the library's statement, copied. The statements were not yet reviewed by a human (see the README).

## Definitions used

Besides Mathlib, the statements use these definitions of the library; a reader checking a statement should check
these too:

* `UndergradKB.Trigonometry.area` (Corral §2.4): the area of a triangle in a Euclidean affine space, defined as
  one half of a side (the base) times the height of the opposite vertex.
-/

namespace UndergradKB.Headlines.Trigonometry

open EuclideanGeometry Real Set Filter Topology
open scoped EuclideanGeometry

/-- **Heron's formula** (Corral §2.4): with `s` the semiperimeter, the area of a triangle is
`√(s(s-a)(s-b)(s-c))`. Related: Mathlib has the laws of sines and cosines but no formula for the area, and Tau Ceti
has none either. -/
theorem heron {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] (t : Affine.Triangle ℝ P)
    {a b c s : ℝ} (ha : a = dist (t.points 1) (t.points 2))
    (hb : b = dist (t.points 0) (t.points 2)) (hc : c = dist (t.points 0) (t.points 1))
    (hs : s = (a + b + c) / 2) :
    UndergradKB.Trigonometry.area t = √(s * (s - a) * (s - b) * (s - c)) := by
  sorry

/-- **Law of tangents** (Corral Theorem 2.3): `(a - b)/(a + b) = tan ½(A - B) / tan ½(A + B)` in any triangle,
with `a`, `b` the sides opposite the angles `A`, `B`. Related: Mathlib and Tau Ceti do not have it. -/
theorem law_of_tangents {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] (t : Affine.Triangle ℝ P)
    {a b A B : ℝ} (ha : a = dist (t.points 1) (t.points 2))
    (hb : b = dist (t.points 0) (t.points 2)) (hA : A = ∠ (t.points 1) (t.points 0) (t.points 2))
    (hB : B = ∠ (t.points 0) (t.points 1) (t.points 2)) :
    (a - b) / (a + b) = tan ((A - B) / 2) / tan ((A + B) / 2) := by
  sorry

/-- **The equation `cos x = x` has exactly one real solution** (Corral §6.2): there is exactly one real `c` with
`cos c = c`, and it lies between `0.72` and `0.76`. Related: neither Mathlib nor Tau Ceti has this. -/
theorem cos_eq_self_existsUnique :
    ∃! c : ℝ, cos c = c ∧ c ∈ Icc (0.72 : ℝ) 0.76 := by
  sorry

/-- **Iterating the cosine converges to its fixed point** (Corral §6.2): for every start `x₀`, the sequence
`x₀, cos x₀, cos (cos x₀), …` converges to the solution `c` of `cos c = c`. Related: neither Mathlib nor Tau Ceti
has this. -/
theorem tendsto_iterate_cos {c : ℝ} (hc : cos c = c) (x₀ : ℝ) :
    Tendsto (fun n : ℕ => cos^[n] x₀) atTop (𝓝 c) := by
  sorry

end UndergradKB.Headlines.Trigonometry
