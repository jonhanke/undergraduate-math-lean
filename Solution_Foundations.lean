/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import UndergradKB.Foundations.VizingTheorem

/-!
# Proofs of the proofs, logic and sets headline statements

Proves the statements of `Challenge_Foundations.lean` from the library. `lake comparator` checks that each
statement here is exactly the one in `Challenge_Foundations.lean`.
-/

namespace UndergradKB.Headlines.Foundations

open UndergradKB.Foundations

theorem vizing {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    chromaticIndex G = G.maxDegree ∨ chromaticIndex G = G.maxDegree + 1 :=
  UndergradKB.Foundations.levin_thm_2_5_9_vizing G

end UndergradKB.Headlines.Foundations
