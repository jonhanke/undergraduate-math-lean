import UndergradKB.Common.Attr
import UndergradKB.Trigonometry.Reciprocal
import UndergradKB.Trigonometry.Identities
import UndergradKB.Trigonometry.HalfAngle
import UndergradKB.Trigonometry.Inverse
import UndergradKB.Trigonometry.Equations
import UndergradKB.Trigonometry.PolarForm
import UndergradKB.Trigonometry.PolarCurves
import UndergradKB.Trigonometry.Roots
import UndergradKB.Trigonometry.Radian
import UndergradKB.Trigonometry.Ambiguous
import UndergradKB.Trigonometry.ArcLength
import UndergradKB.Trigonometry.Graphs
import UndergradKB.Trigonometry.CosFixedPoint
import UndergradKB.Trigonometry.Coterminal
import UndergradKB.Trigonometry.Limacon
import UndergradKB.Trigonometry.Argument
import UndergradKB.Trigonometry.Triangle.Incenter
import UndergradKB.Trigonometry.Course
import UndergradKB.Trigonometry.Quadrants
import UndergradKB.Trigonometry.RightTriangle
import UndergradKB.Trigonometry.Triangle.Area
import UndergradKB.Trigonometry.Triangle.Heron
import UndergradKB.Trigonometry.Triangle.Tangents
import UndergradKB.Trigonometry.LimaconConvex
import UndergradKB.Trigonometry.Segment
import UndergradKB.Trigonometry.Rose
import UndergradKB.Trigonometry.Secant
import UndergradKB.Trigonometry.Vocabulary
import UndergradKB.Trigonometry.Speed

/-! # Trigonometry (Corral; OpenStax Algebra and Trigonometry 2e)

Root of the topic: imports every file of the topic. Topic files import specific Mathlib modules (never all of
`Mathlib`) and `UndergradKB.Common.Attr`, never another topic (docs/ARCHITECTURE.md).

Note: the lakefile's `globs = ["UndergradKB.Trigonometry.+"]` builds the files below this root but not the
root itself, so the files import `UndergradKB.Common.Attr` (a module of the `Common` library) rather than the
`UndergradKB.Common` root. -/
