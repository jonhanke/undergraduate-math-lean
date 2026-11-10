/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import UndergradKB.Trigonometry.Triangle.Heron
import UndergradKB.Trigonometry.Triangle.Tangents
import UndergradKB.Trigonometry.CosFixedPoint

/-!
# Proofs of the trigonometry headline statements

Proves the statements of `Challenge_Trigonometry.lean` from the library. `lake comparator` checks that each
statement here is exactly the one in `Challenge_Trigonometry.lean`.
-/

namespace UndergradKB.Headlines.Trigonometry

open EuclideanGeometry Real Set Filter Topology
open scoped EuclideanGeometry

theorem heron {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] (t : Affine.Triangle ℝ P)
    {a b c s : ℝ} (ha : a = dist (t.points 1) (t.points 2))
    (hb : b = dist (t.points 0) (t.points 2)) (hc : c = dist (t.points 0) (t.points 1))
    (hs : s = (a + b + c) / 2) :
    UndergradKB.Trigonometry.area t = √(s * (s - a) * (s - b) * (s - c)) :=
  UndergradKB.Trigonometry.heron t ha hb hc hs

theorem law_of_tangents {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] (t : Affine.Triangle ℝ P)
    {a b A B : ℝ} (ha : a = dist (t.points 1) (t.points 2))
    (hb : b = dist (t.points 0) (t.points 2)) (hA : A = ∠ (t.points 1) (t.points 0) (t.points 2))
    (hB : B = ∠ (t.points 0) (t.points 1) (t.points 2)) :
    (a - b) / (a + b) = tan ((A - B) / 2) / tan ((A + B) / 2) :=
  UndergradKB.Trigonometry.law_of_tangents t ha hb hA hB

theorem cos_eq_self_existsUnique :
    ∃! c : ℝ, cos c = c ∧ c ∈ Icc (0.72 : ℝ) 0.76 :=
  UndergradKB.Trigonometry.exists_unique_cos_eq_self

theorem tendsto_iterate_cos {c : ℝ} (hc : cos c = c) (x₀ : ℝ) :
    Tendsto (fun n : ℕ => cos^[n] x₀) atTop (𝓝 c) :=
  UndergradKB.Trigonometry.tendsto_iterate_cos hc x₀

end UndergradKB.Headlines.Trigonometry
