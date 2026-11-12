import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ConditionalProbability
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import UndergradKB.Common.Attr

/-!
# Buffon's needle (Grinstead–Snell, chapter 2)

A needle of length equal to the line spacing (both `1`) crosses a line with probability `2/π`.
-/

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal

namespace UndergradKB.Probability

/-- Grinstead–Snell Example 2.3 (PR-016). Buffon's needle with needle length equal to the line spacing
`1`: the distance `X` from the needle's centre to the nearest line is uniform on `[0, 1/2]`, the acute
angle `Θ` with the lines is uniform on `[0, π/2]`, and they are independent; the needle crosses a line
iff `X ≤ sin Θ / 2`, which happens with probability `2/π`. -/
@[kb "grinsteadsnell2006" "Example 2.3, p. 52"]
theorem buffon_crossing_prob {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X Θ : Ω → ℝ} (hX : pdf.IsUniform X (Icc 0 (1 / 2)) P)
    (hΘ : pdf.IsUniform Θ (Icc 0 (π / 2)) P) (hind : IndepFun X Θ P) :
    P.real {ω | X ω ≤ sin (Θ ω) / 2} = 2 / π := by
  have hpi := Real.pi_pos
  have hmX : P.map X = (volume : Measure ℝ)[|Icc 0 (1 / 2)] := hX.map_eq
  have hmΘ : P.map Θ = (volume : Measure ℝ)[|Icc 0 (π / 2)] := hΘ.map_eq
  have hjoint : P.map (fun ω => (X ω, Θ ω)) =
      ((volume : Measure ℝ)[|Icc 0 (1 / 2)]).prod ((volume : Measure ℝ)[|Icc 0 (π / 2)]) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hΘ.aemeasurable).1 hind,
      hmX, hmΘ]
  set S : Set (ℝ × ℝ) := {p | p.1 ≤ sin p.2 / 2} with hSdef
  have hS : MeasurableSet S := measurableSet_le measurable_fst (by fun_prop)
  have hXYm : AEMeasurable (fun ω => (X ω, Θ ω)) P := hX.aemeasurable.prodMk hΘ.aemeasurable
  have hslice : ∀ θ ∈ Icc 0 (π / 2),
      ((volume : Measure ℝ)[|Icc 0 (1 / 2)]) ((fun x : ℝ => (x, θ)) ⁻¹' S) =
        ENNReal.ofReal (sin θ) := by
    intro θ hθ
    have hs0 : 0 ≤ sin θ := sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2])
    have hs1 : sin θ ≤ 1 := sin_le_one θ
    have hpre : (fun x : ℝ => (x, θ)) ⁻¹' S = Iic (sin θ / 2) := rfl
    rw [hpre, cond_apply measurableSet_Icc]
    have : Icc (0 : ℝ) (1 / 2) ∩ Iic (sin θ / 2) = Icc 0 (sin θ / 2) := by
      ext x
      simp only [mem_inter_iff, mem_Icc, mem_Iic]
      constructor
      · rintro ⟨⟨a, _⟩, c⟩; exact ⟨a, c⟩
      · rintro ⟨a, c⟩; exact ⟨⟨a, by linarith⟩, c⟩
    rw [this, Real.volume_Icc, Real.volume_Icc, sub_zero, sub_zero,
      ← ENNReal.ofReal_inv_of_pos (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  have hM : (((volume : Measure ℝ)[|Icc 0 (1 / 2)]).prod ((volume : Measure ℝ)[|Icc 0 (π / 2)])) S
      = ENNReal.ofReal (2 / π) := by
    rw [Measure.prod_apply_symm hS, ProbabilityTheory.cond, lintegral_smul_measure,
      setLIntegral_congr_fun measurableSet_Icc hslice]
    have hint : ∫⁻ θ in Icc 0 (π / 2), ENNReal.ofReal (sin θ) = 1 := by
      have hc : IntegrableOn (fun θ => sin θ) (Icc 0 (π / 2)) :=
        continuous_sin.continuousOn.integrableOn_Icc
      rw [← ofReal_integral_eq_lintegral_ofReal hc
        ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun θ hθ =>
          sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2]))),
        integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by positivity),
        integral_sin]
      simp
    rw [hint, smul_eq_mul, mul_one, Real.volume_Icc, sub_zero,
      ← ENNReal.ofReal_inv_of_pos (by positivity)]
    congr 1
    field_simp
  have hset : {ω | X ω ≤ sin (Θ ω) / 2} = (fun ω => (X ω, Θ ω)) ⁻¹' S := rfl
  rw [measureReal_def, hset, ← Measure.map_apply_of_aemeasurable hXYm hS, hjoint, hM,
    ENNReal.toReal_ofReal (by positivity)]

end UndergradKB.Probability
