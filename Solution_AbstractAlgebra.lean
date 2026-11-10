/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import UndergradKB.AbstractAlgebra.Constructible
import UndergradKB.AbstractAlgebra.PiTranscendental
import UndergradKB.AbstractAlgebra.Galois

/-!
# Proofs of the abstract algebra headline statements (Judson and Beezer)

Each statement of `Challenge_AbstractAlgebra.lean` is proved here from the library. `lake comparator` (configured
by `comparator/AbstractAlgebra.json`) checks that each statement here is exactly the one in
`Challenge_AbstractAlgebra.lean` and that the proofs use only the standard axioms `propext`, `Classical.choice`
and `Quot.sound`.
-/

namespace UndergradKB.Headlines.AbstractAlgebra

theorem transcendental_pi : Transcendental ℚ Real.pi :=
  UndergradKB.AbstractAlgebra.transcendental_pi

theorem constructible_iff_sqrt_tower (x : ℝ) :
    UndergradKB.AbstractAlgebra.Constructible x ↔
      ∃ F, UndergradKB.AbstractAlgebra.SqrtTower F ∧ x ∈ F :=
  UndergradKB.AbstractAlgebra.constructible_iff_tower x

theorem not_constructible_cbrt_two :
    ¬ UndergradKB.AbstractAlgebra.Constructible ((2 : ℝ) ^ ((1 : ℝ) / 3)) :=
  UndergradKB.AbstractAlgebra.not_constructible_cbrt_two

theorem not_constructible_cos_pi_div_nine :
    ¬ UndergradKB.AbstractAlgebra.Constructible (Real.cos (Real.pi / 9)) :=
  UndergradKB.AbstractAlgebra.not_constructible_cos_twenty_degrees

theorem not_constructible_sqrt_pi :
    ¬ UndergradKB.AbstractAlgebra.Constructible (Real.sqrt Real.pi) :=
  UndergradKB.AbstractAlgebra.not_constructible_sqrt_pi

theorem quintic_not_solvable_by_radicals :
    ¬ UndergradKB.AbstractAlgebra.SolvableByRadicals ℚ UndergradKB.AbstractAlgebra.Quintic.quintic :=
  UndergradKB.AbstractAlgebra.Quintic.quintic_not_solvableByRadicals

end UndergradKB.Headlines.AbstractAlgebra
