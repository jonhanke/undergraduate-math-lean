import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import UndergradKB.Common.Attr

/-! # Calculus: areas between curves

OpenStax Calculus 1 §5.2, §6.1 and Calculus 2 §§1.2, 2.1: areas are Lebesgue measures `volume` of planar regions
in `ℝ × ℝ` (open between-the-graphs regions, which differ from the closed ones by a null set). -/

open MeasureTheory Set Real

namespace UndergradKB.Calculus

/-- Area of the region between two continuous graphs `g ≤ h` over `[a,b]` equals `∫_a^b (h - g)`. -/
theorem volume_regionBetween_Icc {g h : ℝ → ℝ} (hg : Continuous g) (hh : Continuous h)
    (hle : ∀ x, g x ≤ h x) {a b : ℝ} (hab : a ≤ b) :
    volume (regionBetween g h (Icc a b)) = ENNReal.ofReal (∫ x in a..b, (h x - g x)) := by
  rw [Measure.volume_eq_prod, volume_regionBetween_eq_lintegral' hg.measurable hh.measurable
    measurableSet_Icc]
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  rw [ofReal_integral_eq_lintegral_ofReal]
  · rfl
  · exact ((hh.sub hg).continuousOn).integrableOn_Icc
  · exact Filter.Eventually.of_forall fun x => sub_nonneg.2 (hle x)

/-- OpenStax Calculus 1:§5.2 Definition (CA-188): for continuous `f` on `[a,b]`, the area of the part of the
region between the graph and the x-axis lying above the axis, minus the area of the part below, is `∫_a^b f`. -/
@[kb "openstaxcalculus2016" "1:§5.2 Definition (net signed area, total area), p. 471"]
theorem net_signed_area {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b) :
    (volume {p : ℝ × ℝ | p.1 ∈ Icc a b ∧ 0 < p.2 ∧ p.2 < f p.1}).toReal -
      (volume {p : ℝ × ℝ | p.1 ∈ Icc a b ∧ f p.1 < p.2 ∧ p.2 < 0}).toReal =
    ∫ x in a..b, f x := by
  have h1 : {p : ℝ × ℝ | p.1 ∈ Icc a b ∧ 0 < p.2 ∧ p.2 < f p.1} =
      regionBetween (fun _ => 0) (fun x => max (f x) 0) (Icc a b) := by
    ext p
    simp only [regionBetween, mem_ofPred_eq, mem_Ioo, lt_max_iff]
    refine and_congr Iff.rfl ⟨fun ⟨h2, h3⟩ => ⟨h2, Or.inl h3⟩, ?_⟩
    rintro ⟨h2, h3 | h3⟩
    · exact ⟨h2, h3⟩
    · exact ⟨h2, by linarith⟩
  have h2 : {p : ℝ × ℝ | p.1 ∈ Icc a b ∧ f p.1 < p.2 ∧ p.2 < 0} =
      regionBetween (fun x => min (f x) 0) (fun _ => 0) (Icc a b) := by
    ext p
    simp only [regionBetween, mem_ofPred_eq, mem_Ioo, min_lt_iff]
    refine and_congr Iff.rfl ⟨fun ⟨h2, h3⟩ => ⟨Or.inl h2, h3⟩, ?_⟩
    rintro ⟨h2 | h2, h3⟩
    · exact ⟨h2, h3⟩
    · exact ⟨by linarith, h3⟩
  rw [h1, h2, volume_regionBetween_Icc continuous_const (hf.max continuous_const)
      (fun x => le_max_right _ _) hab,
    volume_regionBetween_Icc (hf.min continuous_const) continuous_const
      (fun x => min_le_right _ _) hab]
  have i1 : IntervalIntegrable (fun x => max (f x) 0 - 0) MeasureTheory.volume a b :=
    ((hf.max continuous_const).sub continuous_const).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun x => 0 - min (f x) 0) MeasureTheory.volume a b :=
    (continuous_const.sub (hf.min continuous_const)).intervalIntegrable _ _
  have n1 : 0 ≤ ∫ x in a..b, (max (f x) 0 - 0) :=
    intervalIntegral.integral_nonneg hab fun x _ => by simp
  have n2 : 0 ≤ ∫ x in a..b, (0 - min (f x) 0) :=
    intervalIntegral.integral_nonneg hab fun x _ => by simp
  rw [ENNReal.toReal_ofReal n1, ENNReal.toReal_ofReal n2, ← intervalIntegral.integral_sub i1 i2]
  apply intervalIntegral.integral_congr
  intro x _
  have := max_add_min (f x) 0
  simp only
  linarith [max_add_add_right (f x) 0 0, min_add_max (f x) 0]

/-- OpenStax Calculus 1:Theorem 6.2 (CA-250): for continuous `f`, `g` on `[a,b]` whose graphs may cross, the area
between the graphs is `∫_a^b |f - g|`. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.2, p. 551"]
theorem area_between_crossing {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) {a b : ℝ}
    (hab : a ≤ b) :
    volume {p : ℝ × ℝ | p.1 ∈ Icc a b ∧
      ((f p.1 < p.2 ∧ p.2 < g p.1) ∨ (g p.1 < p.2 ∧ p.2 < f p.1))} =
    ENNReal.ofReal (∫ x in a..b, |f x - g x|) := by
  have h1 : {p : ℝ × ℝ | p.1 ∈ Icc a b ∧
      ((f p.1 < p.2 ∧ p.2 < g p.1) ∨ (g p.1 < p.2 ∧ p.2 < f p.1))} =
      regionBetween (fun x => min (f x) (g x)) (fun x => max (f x) (g x)) (Icc a b) := by
    ext p
    simp only [regionBetween, mem_ofPred_eq, mem_Ioo, min_lt_iff, lt_max_iff]
    refine and_congr Iff.rfl ⟨?_, ?_⟩
    · rintro (⟨h2, h3⟩ | ⟨h2, h3⟩)
      · exact ⟨Or.inl h2, Or.inr h3⟩
      · exact ⟨Or.inr h2, Or.inl h3⟩
    · rintro ⟨h2 | h2, h3 | h3⟩
      · exact Or.inl ⟨h2, by linarith⟩
      · exact Or.inl ⟨h2, h3⟩
      · exact Or.inr ⟨h2, h3⟩
      · exact Or.inr ⟨h2, by linarith⟩
  rw [h1, volume_regionBetween_Icc (hf.min hg) (hf.max hg) (fun x => min_le_max) hab]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  simp only
  rw [max_sub_min_eq_abs']

/-- OpenStax Calculus 1:§5.2 Definition (CA-188): the total area between the graph of continuous `f` and the
x-axis over `[a,b]` is `∫_a^b |f|`. -/
@[kb "openstaxcalculus2016" "1:§5.2 Definition (net signed area, total area), p. 471"]
theorem total_area {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b) :
    volume {p : ℝ × ℝ | p.1 ∈ Icc a b ∧ ((0 < p.2 ∧ p.2 < f p.1) ∨ (f p.1 < p.2 ∧ p.2 < 0))} =
    ENNReal.ofReal (∫ x in a..b, |f x|) := by
  have := area_between_crossing hf (continuous_const (y := (0 : ℝ))) hab
  simpa [or_comm] using this

/-- OpenStax Calculus 1:Theorem 6.3 (CA-251): for continuous `v ≤ u` on `[c,d]`, the area between the curves
`x = v y` and `x = u y` is `∫_c^d (u - v)`. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.3, p. 554"]
theorem area_between_curves_in_y {u v : ℝ → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hle : ∀ y, v y ≤ u y) {c d : ℝ} (hcd : c ≤ d) :
    volume {p : ℝ × ℝ | p.2 ∈ Icc c d ∧ v p.2 < p.1 ∧ p.1 < u p.2} =
    ENNReal.ofReal (∫ y in c..d, (u y - v y)) := by
  have h1 : {p : ℝ × ℝ | p.2 ∈ Icc c d ∧ v p.2 < p.1 ∧ p.1 < u p.2} =
      Prod.swap ⁻¹' regionBetween v u (Icc c d) := by
    ext p
    simp [regionBetween]
  have hm : MeasurableSet (regionBetween v u (Icc c d)) :=
    measurableSet_regionBetween hv.measurable hu.measurable measurableSet_Icc
  rw [h1, Measure.volume_eq_prod, (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ))).measure_preimage hm.nullMeasurableSet, ← Measure.volume_eq_prod,
    volume_regionBetween_Icc hv hu hle hcd]

end UndergradKB.Calculus
