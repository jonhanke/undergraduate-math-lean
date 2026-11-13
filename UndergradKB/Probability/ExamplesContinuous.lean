import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-!
# Probability: continuous worked examples (Grinstead–Snell, Examples 2.13 and 4.22)

A uniform point of `[0,1]` has law `unitMeas = volume.restrict (Icc 0 1)`; a uniform point of the unit
square has law `unitMeas.prod unitMeas` on `ℝ × ℝ`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace UndergradKB.Probability

/-- The uniform law on `[0,1]` (Lebesgue measure restricted to `[0,1]`). -/
noncomputable def unitMeas : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

instance : IsProbabilityMeasure unitMeas := ⟨by simp [unitMeas]⟩

namespace ContExamples

theorem unit_Iic {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : unitMeas (Iic t) = ENNReal.ofReal t := by
  rw [unitMeas, Measure.restrict_apply measurableSet_Iic]
  have : Iic t ∩ Icc (0 : ℝ) 1 = Icc 0 t := by
    ext u; simp only [mem_inter_iff, mem_Iic, mem_Icc]; constructor
    · rintro ⟨h, h', _⟩; exact ⟨h', h⟩
    · rintro ⟨h, h'⟩; exact ⟨h', h, by linarith⟩
  rw [this, Real.volume_Icc]; simp

theorem sq_cdf (r : ℝ) :
    unitMeas {u : ℝ | u ^ 2 ≤ r} = ENNReal.ofReal (min 1 (Real.sqrt r)) := by
  have hm : MeasurableSet {u : ℝ | u ^ 2 ≤ r} := measurableSet_le (by fun_prop) (by fun_prop)
  rw [unitMeas, Measure.restrict_apply hm]
  rcases lt_or_ge r 0 with hr | hr
  · have : {u : ℝ | u ^ 2 ≤ r} ∩ Icc 0 1 = ∅ := by
      ext u; simp only [mem_inter_iff, mem_setOf_eq, mem_empty_iff_false, iff_false]
      rintro ⟨h, _⟩; nlinarith [sq_nonneg u]
    rw [this, Real.sqrt_eq_zero_of_nonpos hr.le]; simp
  · have : {u : ℝ | u ^ 2 ≤ r} ∩ Icc 0 1 = Icc 0 (min 1 (Real.sqrt r)) := by
      ext u
      simp only [mem_inter_iff, mem_setOf_eq, mem_Icc, le_min_iff]
      constructor
      · rintro ⟨h, h0, h1⟩
        refine ⟨h0, h1, ?_⟩
        calc u = Real.sqrt (u ^ 2) := (Real.sqrt_sq h0).symm
          _ ≤ Real.sqrt r := Real.sqrt_le_sqrt h
      · rintro ⟨h0, h1, h2⟩
        refine ⟨?_, h0, h1⟩
        calc u ^ 2 ≤ (Real.sqrt r) ^ 2 := pow_le_pow_left₀ h0 h2 2
          _ = r := Real.sq_sqrt hr
    rw [this, Real.volume_Icc]; simp

/-- The integral of the derivative of the square root over `[0,s]`. -/
theorem lintegral_sqrt_density {s : ℝ} (hs : 0 ≤ s) :
    ∫⁻ x in Icc (0 : ℝ) s, ENNReal.ofReal (1 / (2 * Real.sqrt x)) = ENNReal.ofReal (Real.sqrt s) := by
  have hcont : ContinuousOn Real.sqrt (uIcc 0 s) := Real.continuous_sqrt.continuousOn
  have hder : ∀ x ∈ Ioo (min 0 s) (max 0 s),
      HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x := by
    intro x hx
    rw [min_eq_left hs] at hx
    exact Real.hasDerivAt_sqrt hx.1.ne'
  have hint : IntervalIntegrable (fun x : ℝ => 1 / (2 * Real.sqrt x)) volume 0 s :=
    intervalIntegral.intervalIntegrable_deriv_of_nonneg hcont hder (fun x _ => by positivity)
  have hftc : ∫ x in (0 : ℝ)..s, 1 / (2 * Real.sqrt x) = Real.sqrt s - Real.sqrt 0 := by
    refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hs
      (by simpa [uIcc_of_le hs] using hcont) (fun x hx => ?_) hint
    exact (Real.hasDerivAt_sqrt hx.1.ne').hasDerivWithinAt
  have hiof : IntegrableOn (fun x : ℝ => 1 / (2 * Real.sqrt x)) (Icc 0 s) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hs).1 hint
  rw [← ofReal_integral_eq_lintegral_ofReal hiof
    (Filter.Eventually.of_forall fun x => by positivity)]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs, hftc]
  simp

end ContExamples

open ContExamples

/-- Grinstead–Snell Example 2.13 (PR-135), cumulative distribution function. If `U` is a uniform point
of `[0,1]` (its law is `unitMeas`) and `X = U^2`, then `P(X ≤ r) = √r` for `0 ≤ r ≤ 1`, `0` for
`r ≤ 0` and `1` for `r ≥ 1` (all three cases at once as `min 1 √r`). -/
@[kb "grinsteadsnell2006" "Example 2.13, p. 70"]
theorem uniform_sq_cdf {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : Ω → ℝ}
    (hU : Measurable U) (hlaw : P.map U = unitMeas) (r : ℝ) :
    P {ω | U ω ^ 2 ≤ r} = ENNReal.ofReal (min 1 (Real.sqrt r)) := by
  have hm : MeasurableSet {u : ℝ | u ^ 2 ≤ r} := measurableSet_le (by fun_prop) (by fun_prop)
  have := Measure.map_apply (μ := P) hU hm
  rw [hlaw, sq_cdf] at this
  exact this.symm

/-- Grinstead–Snell Example 2.13 (PR-135), density. The law of `X = U^2` has density
`1/(2√x)` on `[0,1]` (and `0` elsewhere) with respect to Lebesgue measure. -/
@[kb "grinsteadsnell2006" "Example 2.13, p. 70"]
theorem uniform_sq_density {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : Ω → ℝ}
    (hU : Measurable U) (hlaw : P.map U = unitMeas) :
    P.map (fun ω => U ω ^ 2) =
      (volume.restrict (Icc (0 : ℝ) 1)).withDensity
        (fun x => ENNReal.ofReal (1 / (2 * Real.sqrt x))) := by
  have hsq : Measurable fun u : ℝ => u ^ 2 := by fun_prop
  have h1 : P.map (fun ω => U ω ^ 2) = unitMeas.map (fun u : ℝ => u ^ 2) := by
    rw [← hlaw, Measure.map_map hsq hU]; rfl
  rw [h1]
  have : IsFiniteMeasure (unitMeas.map (fun u : ℝ => u ^ 2)) := inferInstance
  refine Measure.ext_of_Iic _ _ fun r => ?_
  rw [Measure.map_apply hsq measurableSet_Iic, withDensity_apply _ measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic]
  have hpre : (fun u : ℝ => u ^ 2) ⁻¹' Iic r = {u | u ^ 2 ≤ r} := rfl
  rw [hpre, sq_cdf]
  rcases lt_or_ge r 0 with hr | hr
  · have : Iic r ∩ Icc (0 : ℝ) 1 = ∅ := by
      ext u; simp only [mem_inter_iff, mem_Iic, mem_Icc, mem_empty_iff_false, iff_false]
      rintro ⟨h, h0, _⟩; linarith
    rw [this, Real.sqrt_eq_zero_of_nonpos hr.le]; simp
  · have : Iic r ∩ Icc (0 : ℝ) 1 = Icc 0 (min r 1) := by
      ext u; simp only [mem_inter_iff, mem_Iic, mem_Icc, le_min_iff]
      constructor
      · rintro ⟨h, h0, h1⟩; exact ⟨h0, h, h1⟩
      · rintro ⟨h0, h, h1⟩; exact ⟨h, h0, h1⟩
    rw [this, lintegral_sqrt_density (le_min hr zero_le_one)]
    congr 1
    rcases le_total r 1 with h | h
    · rw [min_eq_left h, min_eq_right]
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt h
    · rw [min_eq_right h, min_eq_left]; simp
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt h

namespace ContExamples

theorem lintegral_tri {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    ∫⁻ x in Icc (0 : ℝ) a, ENNReal.ofReal (1 - x) = ENNReal.ofReal (a - a ^ 2 / 2) := by
  have hcont : Continuous fun x : ℝ => 1 - x := by fun_prop
  rw [← ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc)]
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha]
    congr 1
    rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id,
      integral_id]
    simp
  · refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun x hx => ?_)
    simp only [Pi.zero_apply]; linarith [hx.2]

/-- The slice `{y | x + y ≤ 1}` has `unitMeas`-measure `1 - x` for `x ∈ [0,1]`. -/
theorem slice_B {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    unitMeas (Prod.mk x ⁻¹' {ω : ℝ × ℝ | ω.1 + ω.2 ≤ 1}) = ENNReal.ofReal (1 - x) := by
  have : Prod.mk x ⁻¹' {ω : ℝ × ℝ | ω.1 + ω.2 ≤ 1} = Iic (1 - x) := by
    ext y; simp only [mem_preimage, mem_setOf_eq, mem_Iic]; constructor <;> intro h <;> linarith
  rw [this, unit_Iic (by linarith [hx.2]) (by linarith [hx.1])]

theorem measurableSet_B : MeasurableSet {ω : ℝ × ℝ | ω.1 + ω.2 ≤ 1} :=
  measurableSet_le (by fun_prop) (by fun_prop)

theorem measurableSet_A : MeasurableSet {ω : ℝ × ℝ | ω.1 ^ 2 ≤ 1 / 4} :=
  measurableSet_le (by fun_prop) (by fun_prop)

theorem sqrt_quarter : Real.sqrt (1 / 4) = 1 / 2 := by
  rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)

end ContExamples

/-- The law of a uniform point of the unit square: the product of two uniform laws on `[0,1]`. -/
noncomputable def unitSquareMeas : Measure (ℝ × ℝ) := unitMeas.prod unitMeas

instance : IsProbabilityMeasure unitSquareMeas := by unfold unitSquareMeas; infer_instance

/-- Grinstead–Snell Example 4.22 (PR-135), independence. For a uniform point `(ω₁, ω₂)` of the unit
square, `X₁ = ω₁²` and `X₂ = ω₂²` are independent, and their joint cdf is
`F₁₂(r₁, r₂) = √r₁ √r₂` for `0 ≤ r₁, r₂ ≤ 1`. -/
@[kb "grinsteadsnell2006" "Example 4.22, p. 174"]
theorem unitSquare_sq_indep :
    IndepFun (fun ω : ℝ × ℝ => ω.1 ^ 2) (fun ω : ℝ × ℝ => ω.2 ^ 2) unitSquareMeas ∧
    ∀ r₁ r₂ : ℝ, 0 ≤ r₁ → r₁ ≤ 1 → 0 ≤ r₂ → r₂ ≤ 1 →
      unitSquareMeas {ω | ω.1 ^ 2 ≤ r₁ ∧ ω.2 ^ 2 ≤ r₂} =
        ENNReal.ofReal (Real.sqrt r₁ * Real.sqrt r₂) := by
  refine ⟨indepFun_prod (X := fun u : ℝ => u ^ 2) (Y := fun u : ℝ => u ^ 2) (by fun_prop)
    (by fun_prop), ?_⟩
  intro r₁ r₂ h1 h1' h2 h2'
  have : {ω : ℝ × ℝ | ω.1 ^ 2 ≤ r₁ ∧ ω.2 ^ 2 ≤ r₂} =
      {u : ℝ | u ^ 2 ≤ r₁} ×ˢ {u : ℝ | u ^ 2 ≤ r₂} := rfl
  have hs : ∀ r : ℝ, 0 ≤ r → r ≤ 1 → min 1 (Real.sqrt r) = Real.sqrt r := fun r h h' =>
    min_eq_right (by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt h')
  rw [this, unitSquareMeas, Measure.prod_prod, sq_cdf, sq_cdf, hs _ h1 h1', hs _ h2 h2',
    ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]

/-- Grinstead–Snell Example 4.22 (PR-135), non-independence. With the same model, `X₁ = ω₁²` and
`X₃ = ω₁ + ω₂` are not independent: `P(X₁ ≤ 1/4, X₃ ≤ 1) = 3/8` while
`P(X₁ ≤ 1/4) P(X₃ ≤ 1) = (1/2)(1/2) = 1/4`. -/
@[kb "grinsteadsnell2006" "Example 4.22, p. 174"]
theorem unitSquare_not_indep :
    unitSquareMeas {ω | ω.1 ^ 2 ≤ 1 / 4 ∧ ω.1 + ω.2 ≤ 1} = ENNReal.ofReal (3 / 8) ∧
    unitSquareMeas {ω | ω.1 ^ 2 ≤ 1 / 4} = ENNReal.ofReal (1 / 2) ∧
    unitSquareMeas {ω | ω.1 + ω.2 ≤ 1} = ENNReal.ofReal (1 / 2) ∧
    ¬ IndepFun (fun ω : ℝ × ℝ => ω.1 ^ 2) (fun ω : ℝ × ℝ => ω.1 + ω.2) unitSquareMeas := by
  have hB : unitSquareMeas {ω | ω.1 + ω.2 ≤ 1} = ENNReal.ofReal (1 / 2) := by
    rw [unitSquareMeas, Measure.prod_apply measurableSet_B]
    have : ∫⁻ x, unitMeas (Prod.mk x ⁻¹' {ω : ℝ × ℝ | ω.1 + ω.2 ≤ 1}) ∂unitMeas =
        ∫⁻ x in Icc (0 : ℝ) 1, ENNReal.ofReal (1 - x) :=
      setLIntegral_congr_fun measurableSet_Icc (fun x hx => slice_B hx)
    rw [this, lintegral_tri zero_le_one le_rfl]
    congr 1; norm_num
  have hA : unitSquareMeas {ω | ω.1 ^ 2 ≤ 1 / 4} = ENNReal.ofReal (1 / 2) := by
    have : {ω : ℝ × ℝ | ω.1 ^ 2 ≤ 1 / 4} = {u : ℝ | u ^ 2 ≤ 1 / 4} ×ˢ (univ : Set ℝ) := by
      ext ω; simp
    rw [this, unitSquareMeas, Measure.prod_prod, measure_univ, mul_one, sq_cdf, sqrt_quarter]
    congr 1; norm_num
  have hS : MeasurableSet {ω : ℝ × ℝ | ω.1 ^ 2 ≤ 1 / 4 ∧ ω.1 + ω.2 ≤ 1} :=
    measurableSet_A.inter measurableSet_B
  have hAB : unitSquareMeas {ω | ω.1 ^ 2 ≤ 1 / 4 ∧ ω.1 + ω.2 ≤ 1} = ENNReal.ofReal (3 / 8) := by
    rw [unitSquareMeas, Measure.prod_apply hS]
    have hslice : ∀ x ∈ Icc (0 : ℝ) 1,
        unitMeas (Prod.mk x ⁻¹' {ω : ℝ × ℝ | ω.1 ^ 2 ≤ 1 / 4 ∧ ω.1 + ω.2 ≤ 1}) =
          (Iic (1 / 2 : ℝ)).indicator (fun x => ENNReal.ofReal (1 - x)) x := by
      intro x hx
      by_cases hx2 : x ≤ 1 / 2
      · rw [indicator_of_mem (by exact hx2), ← slice_B hx]
        congr 1
        ext y
        simp only [mem_preimage, mem_setOf_eq, and_iff_right_iff_imp]
        intro _; nlinarith [hx.1]
      · rw [indicator_of_notMem (by exact hx2)]
        have : Prod.mk x ⁻¹' {ω : ℝ × ℝ | ω.1 ^ 2 ≤ 1 / 4 ∧ ω.1 + ω.2 ≤ 1} = ∅ := by
          ext y
          simp only [mem_preimage, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
          intro h; exfalso; push Not at hx2; nlinarith
        rw [this]; simp
    have h1 : ∫⁻ x, unitMeas (Prod.mk x ⁻¹' {ω : ℝ × ℝ | ω.1 ^ 2 ≤ 1 / 4 ∧ ω.1 + ω.2 ≤ 1})
        ∂unitMeas = ∫⁻ x in Icc (0 : ℝ) 1,
          (Iic (1 / 2 : ℝ)).indicator (fun x => ENNReal.ofReal (1 - x)) x :=
      setLIntegral_congr_fun measurableSet_Icc hslice
    have hset : Iic (1 / 2 : ℝ) ∩ Icc 0 1 = Icc 0 (1 / 2) := by
      ext u; simp only [mem_inter_iff, mem_Iic, mem_Icc]; constructor
      · rintro ⟨h, h0, _⟩; exact ⟨h0, h⟩
      · rintro ⟨h0, h⟩; exact ⟨h, h0, by linarith⟩
    rw [h1, lintegral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
      hset, lintegral_tri (by norm_num) (by norm_num)]
    congr 1; norm_num
  refine ⟨hAB, hA, hB, fun h => ?_⟩
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at h
  have := h (Iic (1 / 4)) (Iic 1) measurableSet_Iic measurableSet_Iic
  have e1 : (fun ω : ℝ × ℝ => ω.1 ^ 2) ⁻¹' Iic (1 / 4) = {ω | ω.1 ^ 2 ≤ 1 / 4} := rfl
  have e2 : (fun ω : ℝ × ℝ => ω.1 + ω.2) ⁻¹' Iic 1 = {ω | ω.1 + ω.2 ≤ 1} := rfl
  have e3 : {ω : ℝ × ℝ | ω.1 ^ 2 ≤ 1 / 4} ∩ {ω | ω.1 + ω.2 ≤ 1} =
      {ω | ω.1 ^ 2 ≤ 1 / 4 ∧ ω.1 + ω.2 ≤ 1} := rfl
  rw [e1, e2, e3, hAB, hA, hB, ← ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_eq_ofReal_iff (by norm_num) (by norm_num)] at this
  norm_num at this

end UndergradKB.Probability
