import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import UndergradKB.Common.Attr

/-! # Degrees and radians, sectors (Corral §1.1, §4.1, §4.3; OpenStax §7.1)

Mathlib measures angles in radians only. Here:
* `degToRad`, `radToDeg`: the conversion `x° = πx/180` radians (Corral §4.1, OpenStax §7.1), with
  `360° = 2π`;
* `sector r θ`: the open circular sector of radius `r` and central angle `θ` (`0 ≤ θ ≤ 2π`), placed
  symmetrically about the positive `x`-axis; `volume_sector`: its area is `½ r² θ` (Corral §4.3,
  OpenStax §7.1). The area is Mathlib's Lebesgue measure on `ℝ × ℝ`, computed by the change of variables to
  polar coordinates (`lintegral_comp_polarCoord_symm`).
-/

namespace UndergradKB.Trigonometry

open Real Set MeasureTheory

/-- An angle of `x` degrees measures `π x / 180` radians. -/
noncomputable def degToRad (x : ℝ) : ℝ := π * x / 180

/-- An angle of `x` radians measures `180 x / π` degrees. -/
noncomputable def radToDeg (x : ℝ) : ℝ := 180 * x / π

/-- **Degrees and radians**: `360° = 2π` radians, and the two conversions are inverse to each other.
(TR-099) -/
@[kb "corraltrig" "Box §4.1, p. 94"]
theorem degToRad_spec :
    degToRad 360 = 2 * π ∧ degToRad 180 = π ∧ (∀ x, radToDeg (degToRad x) = x) ∧
      ∀ x, degToRad (radToDeg x) = x := by
  have := pi_pos.ne'
  refine ⟨by rw [degToRad]; ring, by rw [degToRad]; ring, fun x => ?_, fun x => ?_⟩ <;>
    simp only [degToRad, radToDeg] <;> field_simp

/-- OpenStax's form of the conversion: `D / 180 = R / π` when `D` degrees equal `R` radians. (TR-099) -/
@[kb "openstaxalgtrig2e" "§7.1 Converting between radians and degrees, p. 685"]
theorem degToRad_iff (D R : ℝ) : degToRad D = R ↔ D / 180 = R / π := by
  have := pi_pos.ne'
  rw [degToRad]
  constructor <;> intro h
  · rw [← h]; field_simp
  · field_simp at h ⊢; linarith

/-- The (open) circular sector of radius `r` and central angle `θ`, symmetric about the positive `x`-axis:
the points `(ρ cos φ, ρ sin φ)` with `0 < ρ < r` and `-θ/2 < φ < θ/2`. -/
noncomputable def sector (r θ : ℝ) : Set (ℝ × ℝ) := polarCoord.symm '' (Ioo 0 r ×ˢ Ioo (-(θ / 2)) (θ / 2))

private lemma rect_subset_target {r θ : ℝ} (hθ' : θ ≤ 2 * π) :
    Ioo 0 r ×ˢ Ioo (-(θ / 2)) (θ / 2) ⊆ polarCoord.target := by
  rintro ⟨ρ, φ⟩ ⟨hρ, hφ⟩
  exact ⟨hρ.1, by simp only [mem_Ioo] at hφ ⊢; constructor <;> linarith [hφ.1, hφ.2]⟩

private lemma sector_eq {r θ : ℝ} (hθ' : θ ≤ 2 * π) :
    sector r θ = polarCoord.source ∩ polarCoord ⁻¹' (Ioo 0 r ×ˢ Ioo (-(θ / 2)) (θ / 2)) :=
  polarCoord.symm_image_eq_source_inter_preimage (rect_subset_target hθ')

private lemma isOpen_sector {r θ : ℝ} (hθ' : θ ≤ 2 * π) : IsOpen (sector r θ) := by
  rw [sector_eq hθ']
  exact polarCoord.continuousOn.isOpen_inter_preimage polarCoord.open_source
    (isOpen_Ioo.prod isOpen_Ioo)

/-- **Area of a sector**: a sector of radius `r` and central angle `θ` radians (`θ ≤ 2π`; for `θ ≤ 0` the sector is empty) has area
`½ r² θ`. (TR-103) -/
@[kb "corraltrig" "Box §4.3, p. 102"]
theorem volume_sector {r θ : ℝ} (hr : 0 ≤ r) (hθ' : θ ≤ 2 * π) :
    volume (sector r θ) = ENNReal.ofReal (r ^ 2 * θ / 2) := by
  set R := Ioo 0 r ×ˢ Ioo (-(θ / 2)) (θ / 2) with hR
  have hRt := rect_subset_target (r := r) hθ'
  rw [← lintegral_indicator_one (isOpen_sector hθ').measurableSet,
    ← lintegral_comp_polarCoord_symm]
  have key : ∀ p ∈ polarCoord.target, ENNReal.ofReal p.1 • (sector r θ).indicator 1
      (polarCoord.symm p) = R.indicator (fun p => ENNReal.ofReal p.1) p := by
    intro p hp
    have hmem : polarCoord.symm p ∈ sector r θ ↔ p ∈ R := by
      rw [sector_eq hθ', mem_inter_iff, mem_preimage, polarCoord.right_inv hp]
      exact ⟨fun h => h.2, fun h => ⟨polarCoord.map_target hp, h⟩⟩
    by_cases h : p ∈ R
    · rw [indicator_of_mem (hmem.2 h), indicator_of_mem h]; simp
    · rw [indicator_of_notMem (fun h' => h (hmem.1 h')), indicator_of_notMem h]; simp
  rw [setLIntegral_congr_fun polarCoord.open_target.measurableSet key,
    lintegral_indicator (measurableSet_Ioo.prod measurableSet_Ioo),
    Measure.restrict_restrict_of_subset hRt, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have := lintegral_prod_mul (μ := volume.restrict (Ioo 0 r))
    (ν := volume.restrict (Ioo (-(θ / 2)) (θ / 2))) (f := fun x => ENNReal.ofReal x)
    (g := fun _ => 1) measurable_id.ennreal_ofReal.aemeasurable aemeasurable_const
  simp only [mul_one, lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ioo] at this
  rw [this]
  have hint : ∫⁻ x in Ioo 0 r, ENNReal.ofReal x = ENNReal.ofReal (r ^ 2 / 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hr, integral_id]
    · congr 1; ring
    · exact (continuous_id.integrableOn_Icc).mono_set Ioo_subset_Icc_self
    · exact (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun x hx => hx.1.le)
  rw [hint, one_mul, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- **Sector area through the arc length**: with `s = rθ` the length of the arc, the sector area is
`½ r s`. (TR-104) -/
@[kb "corraltrig" "Box §4.3 (A = ½ r s), p. 102"]
theorem volume_sector_eq_half_mul_arc {r θ : ℝ} (hr : 0 ≤ r) (hθ' : θ ≤ 2 * π) :
    volume (sector r θ) = ENNReal.ofReal (r * (r * θ) / 2) := by
  rw [volume_sector hr hθ']; congr 1; ring

end UndergradKB.Trigonometry
