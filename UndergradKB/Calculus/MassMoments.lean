import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import UndergradKB.Common.Attr

/-! # Calculus: mass, moments, center of mass and moments of inertia

Laminas (regions `D` of the plane with a density `ρ`) and solids (regions of `ℝ × ℝ × ℝ`). The book's
physical quantities are integrals of the density against position; this file names them and proves the
facts that are real statements: constant density gives the centroid, symmetry kills a moment, the
perpendicular axis theorem `I₀ = Iₓ + I_y`, and the parallel axis theorem. -/

namespace UndergradKB.Calculus.MassMoments

open MeasureTheory Set

/-! ## Laminas -/

section Lamina

/-- Mass of a lamina occupying `D` with density `ρ`: the double integral of `ρ` over `D`. -/
noncomputable def laminaMass (D : Set (ℝ × ℝ)) (ρ : ℝ × ℝ → ℝ) : ℝ := ∫ p in D, ρ p

/-- Moment of a lamina about the `x`-axis: `∬ y ρ`. -/
noncomputable def laminaMomentX (D : Set (ℝ × ℝ)) (ρ : ℝ × ℝ → ℝ) : ℝ := ∫ p in D, p.2 * ρ p

/-- Moment of a lamina about the `y`-axis: `∬ x ρ`. -/
noncomputable def laminaMomentY (D : Set (ℝ × ℝ)) (ρ : ℝ × ℝ → ℝ) : ℝ := ∫ p in D, p.1 * ρ p

/-- Center of mass of a lamina: `(M_y / m, M_x / m)`. -/
noncomputable def laminaCenterOfMass (D : Set (ℝ × ℝ)) (ρ : ℝ × ℝ → ℝ) : ℝ × ℝ :=
  (laminaMomentY D ρ / laminaMass D ρ, laminaMomentX D ρ / laminaMass D ρ)

/-- Moment of inertia of a lamina about the `x`-axis: `∬ y² ρ`. -/
noncomputable def laminaInertiaX (D : Set (ℝ × ℝ)) (ρ : ℝ × ℝ → ℝ) : ℝ := ∫ p in D, p.2 ^ 2 * ρ p

/-- Moment of inertia of a lamina about the `y`-axis: `∬ x² ρ`. -/
noncomputable def laminaInertiaY (D : Set (ℝ × ℝ)) (ρ : ℝ × ℝ → ℝ) : ℝ := ∫ p in D, p.1 ^ 2 * ρ p

/-- Moment of inertia of a lamina about the origin (polar moment): `∬ (x² + y²) ρ`. -/
noncomputable def laminaInertiaO (D : Set (ℝ × ℝ)) (ρ : ℝ × ℝ → ℝ) : ℝ :=
  ∫ p in D, (p.1 ^ 2 + p.2 ^ 2) * ρ p

/-- Radius of gyration about the `x`-axis: `√(I_x / m)`. -/
noncomputable def laminaRadiusGyrationX (D : Set (ℝ × ℝ)) (ρ : ℝ × ℝ → ℝ) : ℝ :=
  Real.sqrt (laminaInertiaX D ρ / laminaMass D ρ)

/-- Radius of gyration about the `y`-axis: `√(I_y / m)`. -/
noncomputable def laminaRadiusGyrationY (D : Set (ℝ × ℝ)) (ρ : ℝ × ℝ → ℝ) : ℝ :=
  Real.sqrt (laminaInertiaY D ρ / laminaMass D ρ)

/-- Radius of gyration about the origin: `√(I₀ / m)`. -/
noncomputable def laminaRadiusGyrationO (D : Set (ℝ × ℝ)) (ρ : ℝ × ℝ → ℝ) : ℝ :=
  Real.sqrt (laminaInertiaO D ρ / laminaMass D ρ)

/-- OpenStax Calculus 3:§5.6 mass of a lamina (CA-589). The mass of a lamina of constant density `c` is
`c` times its area. -/
@[kb "openstaxcalculus2016" "3:§5.6 mass of a lamina (eq. 5.13), p. 537"]
theorem laminaMass_const (D : Set (ℝ × ℝ)) (c : ℝ) :
    laminaMass D (fun _ => c) = (volume D).toReal * c := by
  simp [laminaMass, setIntegral_const, Measure.real]

/-- OpenStax Calculus 3:§5.6 center of mass and centroid (CA-591). For a constant nonzero density the
density cancels: the center of mass is the centroid `(∬ x / area, ∬ y / area)`. -/
@[kb "openstaxcalculus2016" "3:§5.6 definition of center of mass and centroid, p. 536"]
theorem laminaCenterOfMass_const (D : Set (ℝ × ℝ)) {c : ℝ} (hc : c ≠ 0) :
    laminaCenterOfMass D (fun _ => c) =
      ((∫ p in D, p.1) / (volume D).toReal, (∫ p in D, p.2) / (volume D).toReal) := by
  have hm : laminaMass D (fun _ => c) = (volume D).toReal * c := laminaMass_const D c
  have h1 : laminaMomentY D (fun _ => c) = (∫ p in D, p.1) * c := by
    simp [laminaMomentY, integral_mul_const]
  have h2 : laminaMomentX D (fun _ => c) = (∫ p in D, p.2) * c := by
    simp [laminaMomentX, integral_mul_const]
  simp only [laminaCenterOfMass, hm, h1, h2]
  by_cases hv : (volume D).toReal = 0
  · simp [hv]
  · rw [mul_div_mul_right _ _ hc, mul_div_mul_right _ _ hc]

/-- The reflection `(x, y) ↦ (-x, y)` of the plane preserves Lebesgue measure. -/
theorem measurePreserving_reflectX :
    MeasurePreserving (fun p : ℝ × ℝ => (-p.1, p.2)) volume volume := by
  have := (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
    (MeasurePreserving.id (volume : Measure ℝ))
  exact this

/-- OpenStax Calculus 3:§5.6 center of mass (CA-591). If `D` is symmetric about the `y`-axis and `ρ` is
even in `x`, the moment about the `y`-axis vanishes, so the center of mass lies on the `y`-axis. -/
@[kb "openstaxcalculus2016" "3:§5.6 definition of center of mass and centroid, p. 536"]
theorem laminaMomentY_eq_zero_of_symm {D : Set (ℝ × ℝ)} {ρ : ℝ × ℝ → ℝ}
    (hD : (fun p : ℝ × ℝ => (-p.1, p.2)) ⁻¹' D = D)
    (hρ : ∀ p : ℝ × ℝ, ρ (-p.1, p.2) = ρ p) : laminaMomentY D ρ = 0 := by
  have hemb : MeasurableEmbedding (fun p : ℝ × ℝ => (-p.1, p.2)) :=
    (MeasurableEquiv.prodCongr (MeasurableEquiv.neg ℝ) (MeasurableEquiv.refl ℝ)).measurableEmbedding
  have h := measurePreserving_reflectX.setIntegral_preimage_emb hemb (fun p => p.1 * ρ p) D
  rw [hD] at h
  have h2 : ∫ p in D, p.1 * ρ p = -∫ p in D, p.1 * ρ p := by
    calc ∫ p in D, p.1 * ρ p = ∫ p in D, (-p.1) * ρ (-p.1, p.2) := h.symm
      _ = ∫ p in D, -(p.1 * ρ p) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
        simp [hρ p]
      _ = -∫ p in D, p.1 * ρ p := integral_neg _
  unfold laminaMomentY
  linarith

/-- OpenStax Calculus 3:§5.6 center of mass (CA-591). Under the same symmetry, the `x`-coordinate of the
center of mass is `0`. -/
@[kb "openstaxcalculus2016" "3:§5.6 definition of center of mass and centroid, p. 536"]
theorem laminaCenterOfMass_fst_eq_zero_of_symm {D : Set (ℝ × ℝ)} {ρ : ℝ × ℝ → ℝ}
    (hD : (fun p : ℝ × ℝ => (-p.1, p.2)) ⁻¹' D = D)
    (hρ : ∀ p : ℝ × ℝ, ρ (-p.1, p.2) = ρ p) : (laminaCenterOfMass D ρ).1 = 0 := by
  simp [laminaCenterOfMass, laminaMomentY_eq_zero_of_symm hD hρ]

/-- OpenStax Calculus 3:§5.6 moments of inertia (CA-592). Perpendicular axis theorem: the polar moment
is the sum of the moments about the two axes, `I₀ = Iₓ + I_y`, when `y² ρ` and `x² ρ` are integrable on
`D`. -/
@[kb "openstaxcalculus2016" "3:§5.6 moments I_x, I_y, I_0, p. 543"]
theorem laminaInertiaO_eq {D : Set (ℝ × ℝ)} {ρ : ℝ × ℝ → ℝ}
    (hx : IntegrableOn (fun p => p.2 ^ 2 * ρ p) D) (hy : IntegrableOn (fun p => p.1 ^ 2 * ρ p) D) :
    laminaInertiaO D ρ = laminaInertiaX D ρ + laminaInertiaY D ρ := by
  unfold laminaInertiaO laminaInertiaX laminaInertiaY
  rw [← integral_add hx hy]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only
  ring

/-- OpenStax Calculus 3:§5.6 moments of inertia (CA-592). The perpendicular axis theorem for a compact
lamina with continuous density: all integrals exist. -/
@[kb "openstaxcalculus2016" "3:§5.6 moments I_x, I_y, I_0, p. 543"]
theorem laminaInertiaO_eq_of_isCompact {D : Set (ℝ × ℝ)} {ρ : ℝ × ℝ → ℝ} (hD : IsCompact D)
    (hρ : ContinuousOn ρ D) :
    laminaInertiaO D ρ = laminaInertiaX D ρ + laminaInertiaY D ρ :=
  laminaInertiaO_eq
    ((by fun_prop : ContinuousOn (fun p : ℝ × ℝ => p.2 ^ 2) D).mul hρ |>.integrableOn_compact hD)
    ((by fun_prop : ContinuousOn (fun p : ℝ × ℝ => p.1 ^ 2) D).mul hρ |>.integrableOn_compact hD)

/-- OpenStax Calculus 3:§5.6 radii of gyration (CA-593). The square of the radius of gyration about the
`x`-axis is `I_x / m` (for nonnegative `I_x / m`). -/
@[kb "openstaxcalculus2016" "3:§5.6 radii of gyration, p. 543"]
theorem laminaRadiusGyrationX_sq {D : Set (ℝ × ℝ)} {ρ : ℝ × ℝ → ℝ} (hD : MeasurableSet D)
    (hρ : ∀ p ∈ D, 0 ≤ ρ p) (hm : 0 < laminaMass D ρ) :
    laminaRadiusGyrationX D ρ ^ 2 * laminaMass D ρ = laminaInertiaX D ρ := by
  have hI : 0 ≤ laminaInertiaX D ρ :=
    setIntegral_nonneg hD fun p hp => mul_nonneg (sq_nonneg _) (hρ p hp)
  unfold laminaRadiusGyrationX
  rw [Real.sq_sqrt (div_nonneg hI hm.le), div_mul_cancel₀ _ hm.ne']

/-- OpenStax Calculus 3:§5.6 radii of gyration (CA-593). About the `y`-axis. -/
@[kb "openstaxcalculus2016" "3:§5.6 radii of gyration, p. 543"]
theorem laminaRadiusGyrationY_sq {D : Set (ℝ × ℝ)} {ρ : ℝ × ℝ → ℝ} (hD : MeasurableSet D)
    (hρ : ∀ p ∈ D, 0 ≤ ρ p) (hm : 0 < laminaMass D ρ) :
    laminaRadiusGyrationY D ρ ^ 2 * laminaMass D ρ = laminaInertiaY D ρ := by
  have hI : 0 ≤ laminaInertiaY D ρ :=
    setIntegral_nonneg hD fun p hp => mul_nonneg (sq_nonneg _) (hρ p hp)
  unfold laminaRadiusGyrationY
  rw [Real.sq_sqrt (div_nonneg hI hm.le), div_mul_cancel₀ _ hm.ne']

/-- OpenStax Calculus 3:§5.6 radii of gyration (CA-593). About the origin. -/
@[kb "openstaxcalculus2016" "3:§5.6 radii of gyration, p. 543"]
theorem laminaRadiusGyrationO_sq {D : Set (ℝ × ℝ)} {ρ : ℝ × ℝ → ℝ} (hD : MeasurableSet D)
    (hρ : ∀ p ∈ D, 0 ≤ ρ p) (hm : 0 < laminaMass D ρ) :
    laminaRadiusGyrationO D ρ ^ 2 * laminaMass D ρ = laminaInertiaO D ρ := by
  have hI : 0 ≤ laminaInertiaO D ρ :=
    setIntegral_nonneg hD fun p hp =>
      mul_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (hρ p hp)
  unfold laminaRadiusGyrationO
  rw [Real.sq_sqrt (div_nonneg hI hm.le), div_mul_cancel₀ _ hm.ne']

/-- Moment of inertia of a lamina about the vertical line `x = h`: `∬ (x - h)² ρ`. -/
noncomputable def laminaInertiaVLine (D : Set (ℝ × ℝ)) (ρ : ℝ × ℝ → ℝ) (h : ℝ) : ℝ :=
  ∫ p in D, (p.1 - h) ^ 2 * ρ p

/-- Parallel axis theorem for a lamina (CA-592, bridging): the moment of inertia about the vertical
line `x = h` equals the moment `I_y` about the `y`-axis, minus `2 h M_y`, plus `h² m`. -/
@[kb "openstaxcalculus2016" "3:§5.6 moments I_x, I_y, I_0, p. 543"]
theorem laminaInertiaVLine_eq {D : Set (ℝ × ℝ)} {ρ : ℝ × ℝ → ℝ}
    (h2 : IntegrableOn (fun p => p.1 ^ 2 * ρ p) D) (h1 : IntegrableOn (fun p => p.1 * ρ p) D)
    (h0 : IntegrableOn ρ D) (h : ℝ) :
    laminaInertiaVLine D ρ h =
      laminaInertiaY D ρ - 2 * h * laminaMomentY D ρ + h ^ 2 * laminaMass D ρ := by
  unfold laminaInertiaVLine laminaInertiaY laminaMomentY laminaMass
  have e : ∀ p : ℝ × ℝ, (p.1 - h) ^ 2 * ρ p =
      (p.1 ^ 2 * ρ p - (2 * h) * (p.1 * ρ p)) + h ^ 2 * ρ p := fun p => by ring
  simp_rw [e]
  have hs : IntegrableOn (fun p : ℝ × ℝ => p.1 ^ 2 * ρ p - (2 * h) * (p.1 * ρ p)) D :=
    h2.sub (h1.const_mul (2 * h))
  rw [integral_add hs (h0.const_mul (h ^ 2)), integral_sub h2 (h1.const_mul (2 * h)),
    integral_const_mul, integral_const_mul]

/-- OpenStax Calculus 3:§5.6 moments of inertia (CA-592, parallel axis theorem). With
`x̄ = M_y / m` the `x`-coordinate of the center of mass, the moment of inertia about the vertical line
`x = h` is the moment about the vertical line through the center of mass plus `m (x̄ - h)²`. -/
@[kb "openstaxcalculus2016" "3:§5.6 moments I_x, I_y, I_0, p. 543"]
theorem laminaInertiaVLine_parallel_axis {D : Set (ℝ × ℝ)} {ρ : ℝ × ℝ → ℝ}
    (h2 : IntegrableOn (fun p => p.1 ^ 2 * ρ p) D) (h1 : IntegrableOn (fun p => p.1 * ρ p) D)
    (h0 : IntegrableOn ρ D) (hm : laminaMass D ρ ≠ 0) (h : ℝ) :
    laminaInertiaVLine D ρ h =
      laminaInertiaVLine D ρ (laminaCenterOfMass D ρ).1 +
        laminaMass D ρ * ((laminaCenterOfMass D ρ).1 - h) ^ 2 := by
  rw [laminaInertiaVLine_eq h2 h1 h0 h, laminaInertiaVLine_eq h2 h1 h0]
  simp only [laminaCenterOfMass]
  field_simp
  ring

end Lamina

/-! ## Solids -/

section Solid

/-- Mass of a solid `E ⊆ ℝ × ℝ × ℝ` with density `ρ`: the triple integral of `ρ` over `E`. -/
noncomputable def solidMass (E : Set (ℝ × ℝ × ℝ)) (ρ : ℝ × ℝ × ℝ → ℝ) : ℝ := ∫ p in E, ρ p

/-- Moment of a solid about the `yz`-plane: `∭ x ρ`. -/
noncomputable def solidMomentYZ (E : Set (ℝ × ℝ × ℝ)) (ρ : ℝ × ℝ × ℝ → ℝ) : ℝ :=
  ∫ p in E, p.1 * ρ p

/-- Moment of a solid about the `xz`-plane: `∭ y ρ`. -/
noncomputable def solidMomentXZ (E : Set (ℝ × ℝ × ℝ)) (ρ : ℝ × ℝ × ℝ → ℝ) : ℝ :=
  ∫ p in E, p.2.1 * ρ p

/-- Moment of a solid about the `xy`-plane: `∭ z ρ`. -/
noncomputable def solidMomentXY (E : Set (ℝ × ℝ × ℝ)) (ρ : ℝ × ℝ × ℝ → ℝ) : ℝ :=
  ∫ p in E, p.2.2 * ρ p

/-- Center of mass of a solid: the three moments divided by the mass. -/
noncomputable def solidCenterOfMass (E : Set (ℝ × ℝ × ℝ)) (ρ : ℝ × ℝ × ℝ → ℝ) : ℝ × ℝ × ℝ :=
  (solidMomentYZ E ρ / solidMass E ρ, solidMomentXZ E ρ / solidMass E ρ,
    solidMomentXY E ρ / solidMass E ρ)

/-- Moment of inertia of a solid about the `x`-axis: `∭ (y² + z²) ρ`. -/
noncomputable def solidInertiaX (E : Set (ℝ × ℝ × ℝ)) (ρ : ℝ × ℝ × ℝ → ℝ) : ℝ :=
  ∫ p in E, (p.2.1 ^ 2 + p.2.2 ^ 2) * ρ p

/-- Moment of inertia of a solid about the `y`-axis: `∭ (x² + z²) ρ`. -/
noncomputable def solidInertiaY (E : Set (ℝ × ℝ × ℝ)) (ρ : ℝ × ℝ × ℝ → ℝ) : ℝ :=
  ∫ p in E, (p.1 ^ 2 + p.2.2 ^ 2) * ρ p

/-- Moment of inertia of a solid about the `z`-axis: `∭ (x² + y²) ρ`. -/
noncomputable def solidInertiaZ (E : Set (ℝ × ℝ × ℝ)) (ρ : ℝ × ℝ × ℝ → ℝ) : ℝ :=
  ∫ p in E, (p.1 ^ 2 + p.2.1 ^ 2) * ρ p

/-- OpenStax Calculus 3:§5.6 mass of a solid (CA-594). A solid of constant density `c` has mass `c`
times its volume. -/
@[kb "openstaxcalculus2016" "3:§5.6 definition (mass of a solid, 3D), p. 545"]
theorem solidMass_const (E : Set (ℝ × ℝ × ℝ)) (c : ℝ) :
    solidMass E (fun _ => c) = (volume E).toReal * c := by
  simp [solidMass, setIntegral_const, Measure.real]

/-- OpenStax Calculus 3:§5.6 center of mass of a solid (CA-596). With constant nonzero density the
center of mass is the centroid `(∭ x, ∭ y, ∭ z) / volume`. -/
@[kb "openstaxcalculus2016" "3:§5.6 definition (center of mass of a solid), p. 545"]
theorem solidCenterOfMass_const (E : Set (ℝ × ℝ × ℝ)) {c : ℝ} (hc : c ≠ 0) :
    solidCenterOfMass E (fun _ => c) =
      ((∫ p in E, p.1) / (volume E).toReal, (∫ p in E, p.2.1) / (volume E).toReal,
        (∫ p in E, p.2.2) / (volume E).toReal) := by
  have hm : solidMass E (fun _ => c) = (volume E).toReal * c := solidMass_const E c
  have h1 : solidMomentYZ E (fun _ => c) = (∫ p in E, p.1) * c := by
    simp [solidMomentYZ, integral_mul_const]
  have h2 : solidMomentXZ E (fun _ => c) = (∫ p in E, p.2.1) * c := by
    simp [solidMomentXZ, integral_mul_const]
  have h3 : solidMomentXY E (fun _ => c) = (∫ p in E, p.2.2) * c := by
    simp [solidMomentXY, integral_mul_const]
  simp only [solidCenterOfMass, hm, h1, h2, h3]
  by_cases hv : (volume E).toReal = 0
  · simp [hv]
  · rw [mul_div_mul_right _ _ hc, mul_div_mul_right _ _ hc, mul_div_mul_right _ _ hc]

/-- OpenStax Calculus 3:§5.6 moments of inertia of a solid (CA-597). The three moments of inertia add up
to twice the second moment about the origin: `Iₓ + I_y + I_z = 2 ∭ (x² + y² + z²) ρ`, when the three
integrands are integrable. -/
@[kb "openstaxcalculus2016" "3:§5.6 definition (moments of inertia of a solid), p. 545"]
theorem solidInertia_add {E : Set (ℝ × ℝ × ℝ)} {ρ : ℝ × ℝ × ℝ → ℝ}
    (hx : IntegrableOn (fun p => (p.2.1 ^ 2 + p.2.2 ^ 2) * ρ p) E)
    (hy : IntegrableOn (fun p => (p.1 ^ 2 + p.2.2 ^ 2) * ρ p) E)
    (hz : IntegrableOn (fun p => (p.1 ^ 2 + p.2.1 ^ 2) * ρ p) E) :
    solidInertiaX E ρ + solidInertiaY E ρ + solidInertiaZ E ρ =
      2 * ∫ p in E, (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) * ρ p := by
  unfold solidInertiaX solidInertiaY solidInertiaZ
  have hxy : IntegrableOn (fun p : ℝ × ℝ × ℝ => (p.2.1 ^ 2 + p.2.2 ^ 2) * ρ p +
      (p.1 ^ 2 + p.2.2 ^ 2) * ρ p) E := hx.add hy
  rw [← integral_add hx hy, ← integral_add hxy hz, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [Pi.add_apply]
  ring

end Solid

end UndergradKB.Calculus.MassMoments
