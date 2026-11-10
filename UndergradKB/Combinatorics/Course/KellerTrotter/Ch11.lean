import Mathlib.Combinatorics.SimpleGraph.Girth
import UndergradKB.Common.Attr

/-!
# Keller–Trotter, Chapter 11 (Ramsey theory): thin course wrappers for definitions
-/

namespace UndergradKB.Combinatorics.Course.KellerTrotter

/-- CO-130. The girth of a graph is the length of a shortest cycle; Mathlib's `egirth` takes the
value `⊤` (infinite) exactly for forests. -/
@[kb "kellertrotter2017" "Definition (unnumbered) girth, p. 258"]
theorem def_p258_girth {V : Type*} (G : SimpleGraph V) : G.egirth = ⊤ ↔ G.IsAcyclic :=
  SimpleGraph.egirth_eq_top

end UndergradKB.Combinatorics.Course.KellerTrotter
