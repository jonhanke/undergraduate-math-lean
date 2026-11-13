import UndergradKB.Common
import UndergradKB.RealAnalysis.Darboux
import UndergradKB.RealAnalysis.DarbouxSplit
import UndergradKB.RealAnalysis.DarbouxAdditivity
import UndergradKB.RealAnalysis.DarbouxLinearity
import UndergradKB.RealAnalysis.DarbouxPrereq
import UndergradKB.RealAnalysis.DarbouxContinuous
import UndergradKB.RealAnalysis.DarbouxFinite
import UndergradKB.RealAnalysis.BookForm
import UndergradKB.RealAnalysis.RiemannLebesgue
import UndergradKB.RealAnalysis.FundamentalTheorem
import UndergradKB.RealAnalysis.Gaps
import UndergradKB.RealAnalysis.Rearrangement

/-! # Real analysis
Topic root. Import every file of the topic here; a topic imports Mathlib modules
and `UndergradKB.Common` only (docs/ARCHITECTURE.md). Coverage: docs/coverage/real-analysis/.

Book: J. Lebl, *Basic Analysis I* (`lebl2026`). Policy (wave 1, 2026-11-12): results ReasBook already has are cited
(checklist rows `in ReasBook`, pin 35bcb693); results the courses need that Mathlib lacks in the book's form are
ported from ReasBook (files whose header credits ReasBook, Apache 2.0, listed in `NOTICE`); the rest is proved here.
Results Mathlib has in the book's form get a thin wrapper tagged `@[kb "lebl2026" ...]`. -/
