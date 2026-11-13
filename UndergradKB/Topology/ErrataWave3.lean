import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.ContinuousOn
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Order.Filter.Basic
import UndergradKB.Common.Attr

/-!
# Lemma A5.5.24 of Morris fails for an arbitrary neighbourhood `V` (TP-553)

The book's Lemma A5.5.24: if `V` is a neighbourhood of `0` in `ℝⁿ`, `U` a neighbourhood of `0` in an
abelian topological group `G`, and `f : V → U` is continuous, onto and additive whenever
`x, y, x + y ∈ V`, then `f` extends to a continuous homomorphism of `ℝⁿ` onto the subgroup generated
by `U`.

For a disconnected `V` this is false: take `n = 1`, `G = ℝ`, `V = (-1, 1) ∪ [10, 11]`, `f x = x` on
`(-1, 1)` and `f x = x - 21/2` on `[10, 11]`. Then `f` is continuous on `V`, maps `V` onto `(-1, 1)`,
and is additive on `V` (the only sums staying in `V` are those inside `(-1, 1)` or of a point of
`[10, 11]` and a point of `(-1, 1)`); but any additive extension `F` has `F x = x` near `0`, hence
`F (21/2) = 21/2 ≠ 0 = f (21/2)`. The lemma holds for a ball (or any connected `V`), which is the form
proved in `GroupsExtra.lean`, `GroupsWave2d.lean` and `GroupsWave2h.lean`.
-/

open Set Topology

namespace UndergradKB.Topology

/-- The map of the counterexample. -/
noncomputable def errataMap (x : ℝ) : ℝ := if x < 5 then x else x - 21 / 2

/-- The neighbourhood of the counterexample. -/
def errataNbhd : Set ℝ := Ioo (-1) 1 ∪ Icc 10 11

/-- Morris, Topology Without Tears, Lemma A5.5.24 (TP-553), as stated (for an arbitrary
neighbourhood `V`), is false: there is a neighbourhood `V` of `0` in `ℝ` and a continuous map `f` of
`V` onto the neighbourhood `(-1, 1)` of `0`, additive whenever `x, y, x + y ∈ V`, which has no
additive extension to `ℝ` at all (in particular no continuous homomorphism extends it). -/
@[kb "morris2024" "Lemma A5.5.24, p. 548"]
theorem not_extension_localHom_arbitrary_nbhd :
    ∃ (V : Set ℝ) (f : ℝ → ℝ), V ∈ 𝓝 (0 : ℝ) ∧ ContinuousOn f V ∧ f '' V = Ioo (-1) 1 ∧
      (∀ x ∈ V, ∀ y ∈ V, x + y ∈ V → f (x + y) = f x + f y) ∧
      ¬ ∃ F : ℝ →+ ℝ, ∀ x ∈ V, F x = f x := by
  refine ⟨errataNbhd, errataMap, ?_, ?_, ?_, ?_, ?_⟩
  · exact Filter.mem_of_superset (Ioo_mem_nhds (by norm_num) (by norm_num)) subset_union_left
  · -- `f` agrees with continuous functions on the two pieces, which are separated
    intro x hx
    rcases hx with hx | hx
    · have hU : Iio (5 : ℝ) ∈ 𝓝 x := Iio_mem_nhds (by linarith [hx.2])
      have : ContinuousAt errataMap x := by
        refine (continuous_id.continuousAt).congr ?_
        filter_upwards [hU] with y hy
        simp [errataMap, show y < 5 from hy]
      exact this.continuousWithinAt
    · have hU : Ioi (5 : ℝ) ∈ 𝓝 x := Ioi_mem_nhds (by linarith [hx.1])
      have : ContinuousAt errataMap x := by
        refine ((continuous_id.sub (continuous_const (y := (21 / 2 : ℝ)))).continuousAt).congr ?_
        filter_upwards [hU] with y hy
        simp [errataMap, show ¬ y < 5 from not_lt.2 (le_of_lt hy)]
      exact this.continuousWithinAt
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases hx with hx | hx
      · simp only [errataMap, show x < 5 by linarith [hx.2], ite_true]
        exact hx
      · simp only [errataMap, show ¬ x < 5 by linarith [hx.1], ite_false]
        constructor <;> linarith [hx.1, hx.2]
    · intro hy
      refine ⟨y, Or.inl hy, ?_⟩
      simp [errataMap, show y < 5 by linarith [hy.2]]
  · intro x hx y hy hxy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · have h1 : x < 5 := by linarith [hx.2]
      have h2 : y < 5 := by linarith [hy.2]
      have h3 : x + y < 5 := by linarith [hx.2, hy.2]
      simp [errataMap, h1, h2, h3]
    · have h1 : x < 5 := by linarith [hx.2]
      have h2 : ¬ y < 5 := by linarith [hy.1]
      have h3 : ¬ x + y < 5 := by linarith [hx.1, hy.1]
      simp only [errataMap, h1, h2, h3, ite_true, ite_false]
      ring
    · have h1 : ¬ x < 5 := by linarith [hx.1]
      have h2 : y < 5 := by linarith [hy.2]
      have h3 : ¬ x + y < 5 := by linarith [hx.1, hy.1]
      simp only [errataMap, h1, h2, h3, ite_true, ite_false]
      ring
    · exfalso
      rcases hxy with h | h
      · linarith [hx.1, hy.1, h.2]
      · linarith [hx.2, hy.2, h.2, hx.1, hy.1]
  · rintro ⟨F, hF⟩
    have h1 : F (1 / 2) = 1 / 2 := by
      rw [hF _ (Or.inl ⟨by norm_num, by norm_num⟩)]
      simp [errataMap]
      norm_num
    have h2 : F (21 / 2) = 0 := by
      rw [hF _ (Or.inr ⟨by norm_num, by norm_num⟩)]
      simp [errataMap]
      norm_num
    have h3 : F (21 / 2) = 21 • F (1 / 2) := by
      rw [← map_nsmul]
      norm_num
    rw [h1, h2] at h3
    norm_num at h3

end UndergradKB.Topology
