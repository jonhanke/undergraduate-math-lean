import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.GroupAction.Quotient
import UndergradKB.Combinatorics.Polya.CycleIndex
import UndergradKB.Common.Attr

/-!
# Keller–Trotter, Chapter 15: course wrappers of results proved in this library (wave 4)
-/

namespace UndergradKB.Combinatorics.Course.KellerTrotter.Ch15c

open scoped Classical
open MulAction

/-- CO-316. For a finite group `G` acting on a finite set, the sum of the sizes of the stabilizers
of the points of the orbit of `x` equals `|G|`. -/
@[kb "kellertrotter2017" "Proposition 15.8, p. 322"]
theorem prop_15_8_sum_stabilizer_orbit {G X : Type*} [Group G] [Fintype G] [MulAction G X]
    [Fintype X] (x : X) :
    ∑ y ∈ (orbit G x).toFinset, Fintype.card (stabilizer G y) = Fintype.card G :=
  Polya.sum_card_stabilizer_orbit x

end UndergradKB.Combinatorics.Course.KellerTrotter.Ch15c
