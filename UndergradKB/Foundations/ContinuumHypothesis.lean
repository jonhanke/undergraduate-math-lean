import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Continuum
import UndergradKB.Common

/-! # The continuum hypothesis (statement)

Hammack, *Book of Proof*, Section 14.4 (FO-309): the continuum hypothesis says there is no cardinality strictly between
`|ℕ| = ℵ₀` and `|ℝ| = 𝔠`. Hammack also reports its independence from the axioms of set theory (Gödel, Cohen); that
needs forcing and inner models, which Mathlib does not have, so only the statement and its standard reformulation
`𝔠 = ℵ₁` are formalized here.
-/

namespace UndergradKB.Foundations

open Cardinal

/-- The continuum hypothesis: no cardinal lies strictly between `ℵ₀` and `𝔠`. -/
def ContinuumHypothesis : Prop := ∀ c : Cardinal.{0}, ℵ₀ < c → ¬ c < (𝔠 : Cardinal.{0})

/-- FO-309. The continuum hypothesis holds iff `𝔠 = ℵ₁`. -/
@[kb "hammack2018" "§14.4, p. 301"]
theorem continuumHypothesis_iff : ContinuumHypothesis ↔ (𝔠 : Cardinal.{0}) = ℵ₁ := by
  have h1 : (ℵ₁ : Cardinal.{0}) ≤ 𝔠 := by rw [← succ_aleph0]; exact Order.succ_le_of_lt aleph0_lt_continuum
  constructor
  · intro h
    refine le_antisymm (not_lt.mp fun hlt => h ℵ₁ ?_ hlt) h1
    rw [← succ_aleph0]; exact Order.lt_succ_of_not_isMax (not_isMax _)
  · intro h c hc hc'
    rw [h, ← succ_aleph0] at hc'
    exact not_lt.mpr (Order.succ_le_of_lt hc) hc'

end UndergradKB.Foundations
