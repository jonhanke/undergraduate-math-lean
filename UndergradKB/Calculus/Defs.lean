import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import UndergradKB.Common.Attr

/-! # Calculus: shared bridging definitions

Small definitions for notions of OpenStax Calculus (Volumes 1–3) that Mathlib does not name. Only notions used by more
than one file of the topic live here; a notion used by one file is defined in that file. -/

namespace UndergradKB.Calculus

/-- The secant, `sec x = 1 / cos x` (OpenStax Calculus 1, §1.3). Mathlib has `Real.cot` but no secant. -/
noncomputable def sec (x : ℝ) : ℝ := 1 / Real.cos x

/-- The cosecant, `csc x = 1 / sin x` (OpenStax Calculus 1, §1.3). -/
noncomputable def csc (x : ℝ) : ℝ := 1 / Real.sin x

end UndergradKB.Calculus
