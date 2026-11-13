import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic
import UndergradKB.Common.Attr
import UndergradKB.Probability.ExamplesContinuous
import UndergradKB.Probability.Transforms

/-!
# Probability: geometric worked examples (Grinstead–Snell, Examples 2.6, 2.16, 6.21–6.24)

The meeting problem, the mean distance of a uniform point of the disk, two expectations on the unit
square, and Bertrand's paradox.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace UndergradKB.Probability

open ContExamples

namespace GeomExamples

instance : NullSingletonClass unitMeas := by unfold unitMeas; infer_instance

theorem unit_integral (f : ℝ → ℝ) : ∫ x, f x ∂unitMeas = ∫ x in (0 : ℝ)..1, f x := by
  rw [unitMeas, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]

theorem unitSquare_eq : unitSquareMeas =
    (volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
  rw [unitSquareMeas, unitMeas, Measure.volume_eq_prod, Measure.prod_restrict]

theorem integral_unitSquare {f : ℝ × ℝ → ℝ} (hf : Continuous f) :
    ∫ ω, f ω ∂unitSquareMeas = ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, f (x, y) := by
  have hint : Integrable f unitSquareMeas := by
    rw [unitSquare_eq]
    exact hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [unitSquareMeas, integral_prod f hint]
  simp_rw [unit_integral]

theorem unit_Iic_slice (t : ℝ) (ht : t ≤ 1) :
    unitMeas (Iic t) = ENNReal.ofReal (max t 0) := by
  rcases le_or_gt 0 t with h | h
  · rw [unit_Iic h ht, max_eq_left h]
  · rw [max_eq_right h.le, ENNReal.ofReal_zero, unitMeas, Measure.restrict_apply measurableSet_Iic]
    have : Iic t ∩ Icc (0 : ℝ) 1 = ∅ := by
      ext u; simp only [mem_inter_iff, mem_Iic, mem_Icc, mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2, _⟩; linarith
    rw [this]; simp

theorem measure_sub_gt {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    unitSquareMeas {ω | z < ω.1 - ω.2} = ENNReal.ofReal ((1 - z) ^ 2 / 2) := by
  have hm : MeasurableSet {ω : ℝ × ℝ | z < ω.1 - ω.2} :=
    measurableSet_lt (by fun_prop) (by fun_prop)
  rw [unitSquareMeas, Measure.prod_apply hm]
  have hslice : ∀ x ∈ Icc (0 : ℝ) 1, unitMeas (Prod.mk x ⁻¹' {ω : ℝ × ℝ | z < ω.1 - ω.2}) =
      ENNReal.ofReal (max (x - z) 0) := by
    intro x hx
    have : Prod.mk x ⁻¹' {ω : ℝ × ℝ | z < ω.1 - ω.2} = Iio (x - z) := by
      ext y; simp only [mem_preimage, mem_ofPred_eq, mem_Iio]; constructor <;> intro h <;> linarith
    rw [this, measure_congr Iio_ae_eq_Iic, unit_Iic_slice _ (by linarith [hx.2])]
  have hl : ∫⁻ x, unitMeas (Prod.mk x ⁻¹' {ω : ℝ × ℝ | z < ω.1 - ω.2}) ∂unitMeas =
      ∫⁻ x in Icc (0 : ℝ) 1, ENNReal.ofReal (max (x - z) 0) :=
    setLIntegral_congr_fun measurableSet_Icc hslice
  rw [hl]
  have hc : Continuous fun x : ℝ => max (x - z) 0 := by fun_prop
  rw [← ofReal_integral_eq_lintegral_ofReal hc.integrableOn_Icc
    (Filter.Eventually.of_forall fun x => le_max_right _ _)]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    ← intervalIntegral.integral_add_adjacent_intervals (b := z)
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have h1 : ∫ x in (0 : ℝ)..z, max (x - z) 0 = ∫ x in (0 : ℝ)..z, (0 : ℝ) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le hz0] at hx
    exact max_eq_right (by linarith [hx.2])
  have h2 : ∫ x in z..1, max (x - z) 0 = ∫ x in z..1, (x - z) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le hz1] at hx
    exact max_eq_left (by linarith [hx.1])
  rw [h1, h2, intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id
    intervalIntegrable_const, integral_id]
  simp
  ring

end GeomExamples

open GeomExamples ContExamples

/-- Grinstead–Snell Example 2.16 (PR-153), distribution function. For `(X,Y)` a uniform point of the unit
square (law `unitSquareMeas`), the waiting time `Z = |X - Y|` satisfies `P(Z ≤ z) = 1 - (1 - z)²` for
`0 ≤ z ≤ 1`. -/
@[kb "grinsteadsnell2006" "Example 2.16, p. 73"]
theorem unitSquare_abs_sub_cdf {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    unitSquareMeas.real {ω | |ω.1 - ω.2| ≤ z} = 1 - (1 - z) ^ 2 := by
  have hA := measure_sub_gt hz0 hz1
  have hmA : MeasurableSet {ω : ℝ × ℝ | z < ω.1 - ω.2} :=
    measurableSet_lt (by fun_prop) (by fun_prop)
  have hmB : MeasurableSet {ω : ℝ × ℝ | z < ω.2 - ω.1} :=
    measurableSet_lt (by fun_prop) (by fun_prop)
  have hB : unitSquareMeas {ω | z < ω.2 - ω.1} = ENNReal.ofReal ((1 - z) ^ 2 / 2) := by
    rw [← hA]
    have := (Measure.measurePreserving_swap (μ := unitMeas) (ν := unitMeas)).measure_preimage
      hmA.nullMeasurableSet
    rw [unitSquareMeas]
    exact this
  have hset : {ω : ℝ × ℝ | |ω.1 - ω.2| ≤ z} =
      ({ω : ℝ × ℝ | z < ω.1 - ω.2} ∪ {ω | z < ω.2 - ω.1})ᶜ := by
    ext ω
    simp only [mem_ofPred_eq, mem_compl_iff, mem_union, not_or, not_lt]
    rw [abs_le]; constructor
    · rintro ⟨h1, h2⟩; constructor <;> linarith
    · rintro ⟨h1, h2⟩; constructor <;> linarith
  have hdisj : Disjoint {ω : ℝ × ℝ | z < ω.1 - ω.2} {ω | z < ω.2 - ω.1} := by
    rw [Set.disjoint_left]; intro ω h1 h2; simp only [mem_ofPred_eq] at h1 h2; linarith
  rw [hset, probReal_compl_eq_one_sub (hmA.union hmB), measureReal_union hdisj hmB, measureReal_def,
    measureReal_def, hA, hB, ENNReal.toReal_ofReal (by positivity)]
  ring

/-- Grinstead–Snell Example 2.16 (PR-153), density. The waiting time `Z = |X - Y|` has density
`2(1 - z)` on `[0,1]`: `P(Z ≤ z) = ∫₀ᶻ 2(1 - t) dt`. -/
@[kb "grinsteadsnell2006" "Example 2.16, p. 73"]
theorem unitSquare_abs_sub_cdf_eq_integral {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    unitSquareMeas.real {ω | |ω.1 - ω.2| ≤ z} = ∫ t in (0 : ℝ)..z, 2 * (1 - t) := by
  rw [unitSquare_abs_sub_cdf hz0 hz1, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id,
    integral_id]
  simp
  ring

/-- Grinstead–Snell Example 6.22 (PR-153), through the density. `E(Z) = ∫₀¹ z · 2(1 - z) dz = 1/3`. -/
@[kb "grinsteadsnell2006" "Example 6.22, p. 277"]
theorem integral_mul_density_meeting : ∫ z in (0 : ℝ)..1, z * (2 * (1 - z)) = 1 / 3 := by
  have : ∀ z : ℝ, z * (2 * (1 - z)) = 2 * z - 2 * z ^ 2 := fun z => by ring
  simp_rw [this]
  rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_id, integral_pow]
  norm_num

/-- Grinstead–Snell Example 6.22 (PR-153), directly on the square. For `(X,Y)` uniform on the unit
square, `E|X - Y| = 1/3`. -/
@[kb "grinsteadsnell2006" "Example 6.22, p. 277"]
theorem integral_abs_sub_unitSquare : ∫ ω, |ω.1 - ω.2| ∂unitSquareMeas = 1 / 3 := by
  rw [integral_unitSquare (by fun_prop)]
  have hin : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      ∫ y in (0 : ℝ)..1, |x - y| = x ^ 2 / 2 + (1 - x) ^ 2 / 2 := by
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx
    have hc : Continuous fun y : ℝ => |x - y| := by fun_prop
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := x)
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
    have h1 : ∫ y in (0 : ℝ)..x, |x - y| = ∫ y in (0 : ℝ)..x, (x - y) := by
      refine intervalIntegral.integral_congr fun y hy => ?_
      rw [uIcc_of_le hx.1] at hy
      exact abs_of_nonneg (by linarith [hy.2])
    have h2 : ∫ y in x..1, |x - y| = ∫ y in x..1, (y - x) := by
      refine intervalIntegral.integral_congr fun y hy => ?_
      rw [uIcc_of_le hx.2] at hy
      rw [abs_sub_comm]
      exact abs_of_nonneg (by linarith [hy.1])
    rw [h1, h2, intervalIntegral.integral_sub intervalIntegrable_const
      intervalIntegral.intervalIntegrable_id, intervalIntegral.integral_sub
      intervalIntegral.intervalIntegrable_id intervalIntegrable_const, integral_id, integral_id]
    simp
    ring
  rw [intervalIntegral.integral_congr hin]
  have hp : ∀ x : ℝ, x ^ 2 / 2 + (1 - x) ^ 2 / 2 = x ^ 2 - x + 1 / 2 := fun x => by ring
  simp_rw [hp]
  rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _), integral_pow, integral_id]
  norm_num

/-- Grinstead–Snell Example 6.23 (PR-155). For `(X,Y)` uniform on the unit square, `A = X²` and `B = Y²`
have `E(A) = E(B) = 1/3` and `E(AB) = 1/9 = E(A)E(B)` (the independence of `A` and `B` is
`unitSquare_sq_indep`). -/
@[kb "grinsteadsnell2006" "Example 6.23, p. 279"]
theorem unitSquare_sq_expectations :
    ∫ ω, ω.1 ^ 2 ∂unitSquareMeas = 1 / 3 ∧ ∫ ω, ω.2 ^ 2 ∂unitSquareMeas = 1 / 3 ∧
    ∫ ω, ω.1 ^ 2 * ω.2 ^ 2 ∂unitSquareMeas = 1 / 9 ∧
    ∫ ω, ω.1 ^ 2 * ω.2 ^ 2 ∂unitSquareMeas =
      (∫ ω, ω.1 ^ 2 ∂unitSquareMeas) * ∫ ω, ω.2 ^ 2 ∂unitSquareMeas := by
  have h1 : ∫ ω, ω.1 ^ 2 ∂unitSquareMeas = 1 / 3 := by
    rw [integral_unitSquare (by fun_prop)]; simp [integral_pow]; norm_num
  have h2 : ∫ ω, ω.2 ^ 2 ∂unitSquareMeas = 1 / 3 := by
    rw [integral_unitSquare (by fun_prop)]; simp [integral_pow]; norm_num
  have h3 : ∫ ω, ω.1 ^ 2 * ω.2 ^ 2 ∂unitSquareMeas = 1 / 9 := by
    rw [integral_unitSquare (by fun_prop)]
    simp [integral_pow, intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const]
    norm_num
  exact ⟨h1, h2, h3, by rw [h1, h2, h3]; norm_num⟩

/-- Grinstead–Snell Example 6.24 (PR-155). For `(X,Y)` uniform on the unit square and `W = X + Y`:
`E(Y) = 1/2`, `E(W) = 1`, `E(YW) = 7/12`, which differs from `E(Y)E(W) = 1/2`, so `Y` and `W` are
not independent. -/
@[kb "grinsteadsnell2006" "Example 6.24, p. 279"]
theorem unitSquare_Y_W_expectations :
    ∫ ω, ω.2 ∂unitSquareMeas = 1 / 2 ∧ ∫ ω, (ω.1 + ω.2) ∂unitSquareMeas = 1 ∧
    ∫ ω, ω.2 * (ω.1 + ω.2) ∂unitSquareMeas = 7 / 12 ∧
    (∫ ω, ω.2 ∂unitSquareMeas) * ∫ ω, (ω.1 + ω.2) ∂unitSquareMeas = 1 / 2 ∧
    ∫ ω, ω.2 * (ω.1 + ω.2) ∂unitSquareMeas ≠
      (∫ ω, ω.2 ∂unitSquareMeas) * ∫ ω, (ω.1 + ω.2) ∂unitSquareMeas := by
  have h1 : ∫ ω, ω.2 ∂unitSquareMeas = 1 / 2 := by
    rw [integral_unitSquare (by fun_prop)]; simp [integral_id]
  have h2 : ∫ ω, (ω.1 + ω.2) ∂unitSquareMeas = 1 := by
    rw [integral_unitSquare (by fun_prop)]
    have hin : ∀ x : ℝ, ∫ y in (0 : ℝ)..1, (x + y) = x + 1 / 2 := fun x => by
      rw [intervalIntegral.integral_add intervalIntegrable_const
        intervalIntegral.intervalIntegrable_id]
      simp [integral_id]
    simp_rw [hin]
    rw [intervalIntegral.integral_add intervalIntegral.intervalIntegrable_id
        intervalIntegrable_const]
    simp [integral_id]
    norm_num
  have h3 : ∫ ω, ω.2 * (ω.1 + ω.2) ∂unitSquareMeas = 7 / 12 := by
    rw [integral_unitSquare (by fun_prop)]
    have : ∀ x y : ℝ, y * (x + y) = x * y + y ^ 2 := fun x y => by ring
    simp_rw [this]
    have hin : ∀ x : ℝ, ∫ y in (0 : ℝ)..1, (x * y + y ^ 2) = x / 2 + 1 / 3 := fun x => by
      rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_const_mul,
        integral_id, integral_pow]
      norm_num; ring
    simp_rw [hin]
    rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
        intervalIntegrable_const, intervalIntegral.integral_div, integral_id]
    norm_num
  rw [h1, h2, h3]
  norm_num

section Disk

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem tail_norm_uniform_disk {X : Ω → EuclideanSpace ℝ (Fin 2)}
    (hX : pdf.IsUniform X (Metric.ball 0 1) P) {t : ℝ} (ht : 0 < t) :
    P.real {ω | t < ‖X ω‖} = if t ≤ 1 then 1 - t ^ 2 else 0 := by
  have hn : AEMeasurable (fun ω => ‖X ω‖) P := hX.aemeasurable.norm
  have hc : {ω | t < ‖X ω‖} = {ω | ‖X ω‖ ≤ t}ᶜ := by ext ω; simp
  have hnm : NullMeasurableSet {ω | ‖X ω‖ ≤ t} P := hn.nullMeasurable measurableSet_Iic
  rw [hc, probReal_compl_eq_one_sub₀ hnm]
  split_ifs with h
  · rw [measureReal_norm_le_of_uniform_disk hX ht.le h]
  · push Not at h
    have h1 := measureReal_norm_le_of_uniform_disk hX zero_le_one le_rfl
    have h2 : P.real {ω | ‖X ω‖ ≤ 1} ≤ P.real {ω | ‖X ω‖ ≤ t} :=
      measureReal_mono (fun ω hω => le_trans hω h.le)
    have h3 : P.real {ω | ‖X ω‖ ≤ t} ≤ 1 := measureReal_le_one
    rw [one_pow] at h1
    linarith

/-- Grinstead–Snell Example 6.21 (PR-154). For a point `X` chosen uniformly in the unit disk, the
distance from the centre has mean `E‖X‖ = 2/3`. -/
@[kb "grinsteadsnell2006" "Example 6.21, p. 277"]
theorem integral_norm_uniform_disk {X : Ω → EuclideanSpace ℝ (Fin 2)}
    (hX : pdf.IsUniform X (Metric.ball 0 1) P) : ∫ ω, ‖X ω‖ ∂P = 2 / 3 := by
  have hn : AEMeasurable (fun ω => ‖X ω‖) P := hX.aemeasurable.norm
  have hbd : ∀ᵐ ω ∂P, ‖X ω‖ ≤ 1 := by
    have h1 := measureReal_norm_le_of_uniform_disk hX zero_le_one le_rfl
    rw [one_pow] at h1
    have hnm : NullMeasurableSet {ω | ‖X ω‖ ≤ 1} P := hn.nullMeasurable measurableSet_Iic
    have h2 : P {ω | ‖X ω‖ ≤ 1}ᶜ = 0 := by
      rw [prob_compl_eq_one_sub₀ hnm]
      have : P {ω | ‖X ω‖ ≤ 1} = 1 := by
        rw [measureReal_def] at h1
        have := (ENNReal.toReal_eq_one_iff _).1 h1
        exact this
      rw [this]; simp
    exact measure_eq_zero_iff_ae_notMem.1 h2 |>.mono fun ω hω => by simpa using hω
  have hint : Integrable (fun ω => ‖X ω‖) P :=
    Integrable.of_bound hn.aestronglyMeasurable 1 (hbd.mono fun ω hω => by
      simpa [abs_of_nonneg (norm_nonneg _)] using hω)
  rw [hint.integral_eq_integral_meas_lt (Filter.Eventually.of_forall fun ω => norm_nonneg _)]
  have hg : EqOn (fun t : ℝ => P.real {ω | t < ‖X ω‖})
      ((Ioc (0 : ℝ) 1).indicator (fun t => 1 - t ^ 2)) (Ioi 0) := by
    intro t ht
    simp only
    rw [tail_norm_uniform_disk hX ht]
    by_cases h : t ≤ 1
    · simp only [h, ↓reduceIte]; rw [indicator_of_mem (by exact ⟨ht, h⟩)]
    · simp only [h, ↓reduceIte]; rw [indicator_of_notMem (by simp [h])]
  rw [setIntegral_congr_fun measurableSet_Ioi hg, setIntegral_indicator measurableSet_Ioc]
  have : Ioi (0 : ℝ) ∩ Ioc 0 1 = Ioc 0 1 := by
    ext u; simp only [mem_inter_iff, mem_Ioi, mem_Ioc]; tauto
  rw [this, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_sub intervalIntegrable_const
      (Continuous.intervalIntegrable (by fun_prop) _ _), integral_pow]
  norm_num

/-- Grinstead–Snell Example 6.21 (PR-154), through the density `2x`: `∫₀¹ x · 2x dx = 2/3`. -/
@[kb "grinsteadsnell2006" "Example 6.21, p. 277"]
theorem integral_mul_density_disk : ∫ x in (0 : ℝ)..1, x * (2 * x) = 2 / 3 := by
  have : ∀ x : ℝ, x * (2 * x) = 2 * x ^ 2 := fun x => by ring
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num

end Disk

namespace GeomExamples

/-- The chord length `2√(1 - u²)` exceeds `√3` exactly when `|u| < 1/2`. -/
theorem sqrt3_lt_chord {u : ℝ} :
    Real.sqrt 3 < 2 * Real.sqrt (1 - u ^ 2) ↔ -(1 / 2) < u ∧ u < 1 / 2 := by
  have h2 : 2 * Real.sqrt (1 - u ^ 2) = Real.sqrt (4 * (1 - u ^ 2)) := by
    rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h2, Real.sqrt_lt_sqrt_iff (by norm_num)]
  constructor
  · intro h; constructor <;> nlinarith
  · rintro ⟨h1, h2⟩; nlinarith

/-- The chord length `√(2 - 2cos α)` exceeds `√3` exactly when `α ∈ (2π/3, 4π/3)`, for `α ∈ [0, 2π]`. -/
theorem sqrt3_lt_chord_angle {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 2 * Real.pi) :
    Real.sqrt 3 < Real.sqrt (2 - 2 * Real.cos α) ↔ 2 * Real.pi / 3 < α ∧ α < 4 * Real.pi / 3 := by
  rw [Real.sqrt_lt_sqrt_iff (by norm_num)]
  have hpi := Real.pi_pos
  have hcos : Real.cos α = - Real.cos (|α - Real.pi|) := by
    rw [Real.cos_abs, Real.cos_sub_pi, neg_neg]
  have habs : |α - Real.pi| ≤ Real.pi := abs_le.2 ⟨by linarith, by linarith⟩
  have key : 3 < 2 - 2 * Real.cos α ↔ |α - Real.pi| < Real.pi / 3 := by
    have hanti := Real.strictAntiOn_cos
    have hmem : |α - Real.pi| ∈ Icc 0 Real.pi := ⟨abs_nonneg _, habs⟩
    have hmem3 : Real.pi / 3 ∈ Icc 0 Real.pi := ⟨by positivity, by linarith⟩
    have := hanti.lt_iff_gt hmem3 hmem
    rw [Real.cos_pi_div_three] at this
    rw [hcos, ← this]
    constructor <;> intro h <;> linarith
  rw [key, abs_lt]
  constructor
  · rintro ⟨a, b⟩; constructor <;> linarith
  · rintro ⟨a, b⟩; constructor <;> linarith

end GeomExamples

/-- Grinstead–Snell Example 2.6 (PR-156), the endpoint-angle model. If the angle `α` of one endpoint
(the other fixed at angle `0`) is uniform on `[0, 2π]`, the chord has length `√(2 - 2cos α)` and it
exceeds `√3` with probability `1/3`. -/
@[kb "grinsteadsnell2006" "Example 2.6, p. 55"]
theorem bertrand_angle :
    (volume[|Icc (0 : ℝ) (2 * Real.pi)]).real
      {α | Real.sqrt 3 < Real.sqrt (2 - 2 * Real.cos α)} = 1 / 3 := by
  have hpi := Real.pi_pos
  have hS : Icc (0 : ℝ) (2 * Real.pi) ∩ {α | Real.sqrt 3 < Real.sqrt (2 - 2 * Real.cos α)} =
      Ioo (2 * Real.pi / 3) (4 * Real.pi / 3) := by
    ext α
    simp only [mem_inter_iff, mem_Icc, mem_ofPred_eq, mem_Ioo]
    constructor
    · rintro ⟨⟨h0, h1⟩, h⟩; exact (sqrt3_lt_chord_angle h0 h1).1 h
    · intro h
      have := h.1; have := h.2
      have hh := (sqrt3_lt_chord_angle (α := α) (by linarith) (by linarith)).2 h
      exact ⟨⟨by linarith, by linarith⟩, hh⟩
  have hm : MeasurableSet {α : ℝ | Real.sqrt 3 < Real.sqrt (2 - 2 * Real.cos α)} :=
    measurableSet_lt (by fun_prop) (by fun_prop)
  rw [measureReal_def, cond_apply measurableSet_Icc, hS, Real.volume_Icc, Real.volume_Ioo,
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal (by linarith),
    ENNReal.toReal_ofReal (by linarith)]
  field_simp
  ring

/-- Grinstead–Snell Example 2.6 (PR-156), the midpoint-distance model. If the signed distance `r` of the
chord from the centre is uniform on `[-1, 1]`, the chord has length `2√(1 - r²)` and it exceeds `√3`
with probability `1/2`. -/
@[kb "grinsteadsnell2006" "Example 2.6, p. 55"]
theorem bertrand_distance :
    (volume[|Icc (-1 : ℝ) 1]).real {r | Real.sqrt 3 < 2 * Real.sqrt (1 - r ^ 2)} = 1 / 2 := by
  have hS : Icc (-1 : ℝ) 1 ∩ {r | Real.sqrt 3 < 2 * Real.sqrt (1 - r ^ 2)} = Ioo (-(1 / 2)) (1 / 2) := by
    ext r
    simp only [mem_inter_iff, mem_Icc, mem_ofPred_eq, mem_Ioo, sqrt3_lt_chord]
    constructor
    · rintro ⟨_, h⟩; exact h
    · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith, by linarith⟩, h1, h2⟩
  rw [measureReal_def, cond_apply measurableSet_Icc, hS, Real.volume_Icc, Real.volume_Ioo,
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal (by norm_num),
    ENNReal.toReal_ofReal (by norm_num)]
  norm_num

/-- Grinstead–Snell Example 2.6 (PR-156), the midpoint-distance model on `[0, 1]`. If the distance `r` of
the chord from the centre is uniform on `[0, 1]` (law `unitMeas`), the chord has length `2√(1 - r²)`
and it exceeds `√3` with probability `1/2`. -/
@[kb "grinsteadsnell2006" "Example 2.6, p. 55"]
theorem bertrand_distance_unit :
    unitMeas.real {r | Real.sqrt 3 < 2 * Real.sqrt (1 - r ^ 2)} = 1 / 2 := by
  have hm : MeasurableSet {r : ℝ | Real.sqrt 3 < 2 * Real.sqrt (1 - r ^ 2)} :=
    measurableSet_lt (by fun_prop) (by fun_prop)
  have hS : {r : ℝ | Real.sqrt 3 < 2 * Real.sqrt (1 - r ^ 2)} ∩ Icc 0 1 = Ico 0 (1 / 2) := by
    ext r
    simp only [mem_inter_iff, mem_Icc, mem_ofPred_eq, mem_Ico, sqrt3_lt_chord]
    constructor
    · rintro ⟨⟨_, h⟩, h0, _⟩; exact ⟨h0, h⟩
    · rintro ⟨h0, h⟩; exact ⟨⟨by linarith, h⟩, h0, by linarith⟩
  rw [measureReal_def, unitMeas, Measure.restrict_apply hm, hS, Real.volume_Ico]
  norm_num

section DiskBall

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem measureReal_norm_lt_of_uniform_disk {X : Ω → EuclideanSpace ℝ (Fin 2)}
    (hX : pdf.IsUniform X (Metric.ball 0 1) P) {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    P.real {ω | ‖X ω‖ < r} = r ^ 2 := by
  have hm : P.map X = (volume : Measure (EuclideanSpace ℝ (Fin 2)))[|Metric.ball 0 1] := hX.map_eq
  have e : {ω | ‖X ω‖ < r} = X ⁻¹' Metric.ball 0 r := by
    ext ω; simp
  have hpi : ENNReal.ofReal Real.pi ≠ 0 := by simp [Real.pi_pos]
  have hpt : ENNReal.ofReal Real.pi ≠ ⊤ := ENNReal.ofReal_ne_top
  have hvol : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 ∩ Metric.ball 0 r) =
      ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi := by
    rw [inter_eq_right.2 (Metric.ball_subset_ball h1)]
    simp
  rw [measureReal_def, e, ← Measure.map_apply_of_aemeasurable hX.aemeasurable
    Metric.isOpen_ball.measurableSet, hm, cond_apply Metric.isOpen_ball.measurableSet, hvol]
  have : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1))⁻¹ *
      (ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi) = ENNReal.ofReal r ^ 2 := by
    rw [EuclideanSpace.volume_ball_fin_two]
    simp only [ENNReal.ofReal_one, one_pow, one_mul]
    rw [mul_comm, mul_assoc, ENNReal.mul_inv_cancel hpi hpt, mul_one]
  rw [this, ← ENNReal.ofReal_pow h0, ENNReal.toReal_ofReal (by positivity)]

/-- Grinstead–Snell Example 2.6 (PR-156), the midpoint model. If the midpoint `X` of the chord is uniform
in the unit disk, the chord has length `2√(1 - ‖X‖²)` and it exceeds `√3` with probability `1/4`
(the distance cdf `r²` at `r = 1/2`). -/
@[kb "grinsteadsnell2006" "Example 2.6, p. 55"]
theorem bertrand_midpoint {X : Ω → EuclideanSpace ℝ (Fin 2)}
    (hX : pdf.IsUniform X (Metric.ball 0 1) P) :
    P.real {ω | Real.sqrt 3 < 2 * Real.sqrt (1 - ‖X ω‖ ^ 2)} = 1 / 4 := by
  have : {ω | Real.sqrt 3 < 2 * Real.sqrt (1 - ‖X ω‖ ^ 2)} = {ω | ‖X ω‖ < 1 / 2} := by
    ext ω
    simp only [mem_ofPred_eq, sqrt3_lt_chord]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨by linarith [norm_nonneg (X ω)], h⟩
  rw [this, measureReal_norm_lt_of_uniform_disk hX (by norm_num) (by norm_num)]
  norm_num

end DiskBall

end UndergradKB.Probability
