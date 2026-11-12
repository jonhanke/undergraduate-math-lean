import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Real.Pi.Bounds
import UndergradKB.Common.Attr
import UndergradKB.Geometry.HypArea2
import UndergradKB.Geometry.HypTriangles
import UndergradKB.Geometry.Spherical2

/-! # Taurinus substitution (Petrunin, remark p. 138) and the area of an ideal triangle (Section 20I)

Part 1: the book remarks that replacing every distance `d` by `i·d` turns spherical formulas into
hyperbolic ones.  We do not formalize this meta-claim; we prove formal instances: the spherical
Pythagorean formula `cos c = cos a cos b` and the spherical law of cosines
`cos a = cos b cos c + sin b sin c cos α`, evaluated at the imaginary lengths `i·a`, `i·b`, `i·c` (with the
angle `α` unchanged), are equivalent to the hyperbolic formulas, and they hold for the h-lengths
of every triangle of the h-plane (disc model).

Part 2: the solid ideal triangle and its area `π`.
-/

namespace UndergradKB.Geometry

section Taurinus

open Complex ComplexConjugate

/-- The spherical Pythagorean formula `cos c = cos a cos b` (Theorem 16.12) evaluated at the imaginary
lengths `i a, i b, i c` is equivalent to the hyperbolic Pythagorean formula `cosh c = cosh a cosh b`. -/
@[kb "petrunin2025" "Remark on the Taurinus substitution (Pythagorean case), p. 138"]
theorem taurinus_pythagoras (a b c : ℝ) :
    Complex.cos (I * c) = Complex.cos (I * a) * Complex.cos (I * b) ↔
      Real.cosh c = Real.cosh a * Real.cosh b := by
  simp only [mul_comm I, Complex.cos_mul_I]
  rw [← Complex.ofReal_cosh, ← Complex.ofReal_cosh, ← Complex.ofReal_cosh, ← Complex.ofReal_mul,
    Complex.ofReal_inj]

/-- The spherical law of cosines `cos a = cos b cos c + sin b sin c cos α` (all lengths being angles of
the unit sphere) evaluated at the imaginary lengths `i a, i b, i c` is equivalent to the hyperbolic law of
cosines `cosh a = cosh b cosh c - sinh b sinh c cos α`. -/
@[kb "petrunin2025" "Remark on the Taurinus substitution (law of cosines), p. 138"]
theorem taurinus_law_cosines (a b c α : ℝ) :
    Complex.cos (I * a) = Complex.cos (I * b) * Complex.cos (I * c) +
        Complex.sin (I * b) * Complex.sin (I * c) * Complex.cos α ↔
      Real.cosh a = Real.cosh b * Real.cosh c - Real.sinh b * Real.sinh c * Real.cos α := by
  simp only [mul_comm I, Complex.cos_mul_I, Complex.sin_mul_I, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sinh]
  rw [← Complex.ofReal_inj]
  push_cast
  constructor <;> intro h
  · linear_combination h + (Complex.sinh b * Complex.sinh c *
      Complex.cos α) * Complex.I_sq
  · linear_combination h + (-(Complex.sinh b * Complex.sinh c *
      Complex.cos α)) * Complex.I_sq

/-- **Instance of the Taurinus substitution (law of cosines).**  For distinct points `A, B, C` of the
h-plane, the spherical law of cosines evaluated at the imaginary h-lengths `i·BC_h, i·AB_h, i·AC_h` and the
h-angle at `A` holds. -/
@[kb "petrunin2025" "Remark on the Taurinus substitution (law of cosines), p. 138"]
theorem taurinus_hyperbolic_law_cosines {A B C : ℂ} (hA : ‖A‖ < 1) (hB : ‖B‖ < 1) (hC : ‖C‖ < 1)
    (hBA : B ≠ A) (hCA : C ≠ A) :
    Complex.cos (I * hdist B C) = Complex.cos (I * hdist A B) * Complex.cos (I * hdist A C) +
      Complex.sin (I * hdist A B) * Complex.sin (I * hdist A C) * Complex.cos (hangle B A C) :=
  (taurinus_law_cosines _ _ _ _).mpr (hlaw_cosines hA hB hC hBA hCA)

/-- **Instance of the Taurinus substitution (Pythagoras).**  If the h-angle at `C` is a right angle (in the
form of the book's reduction to the centre), the spherical Pythagorean formula holds at the imaginary
h-lengths. -/
@[kb "petrunin2025" "Remark on the Taurinus substitution (Pythagorean case), p. 138"]
theorem taurinus_hyperbolic_pythagoras {A B C : ℂ} (hA : ‖A‖ < 1) (hB : ‖B‖ < 1) (hC : ‖C‖ < 1)
    (h : (mobius C A * conj (mobius C B)).re = 0) :
    Complex.cos (I * hdist A B) = Complex.cos (I * hdist C A) * Complex.cos (I * hdist C B) :=
  (taurinus_pythagoras _ _ _).mpr (cosh_hdist_pythagoras hA hB hC h)

end Taurinus

section Ideal

open Real MeasureTheory Set ComplexConjugate

/-- `z` lies on the closed side, containing the ideal point `c`, of the h-line joining the ideal points
`a`, `b` of the unit circle.  Under `w ↦ (w - a)/(w - b)` the unit circle goes to a line through `0`
and the h-line to its perpendicular through `0`, so the side is the sign of an inner product. -/
def hidealhalf (a b c z : ℂ) : Prop := 0 ≤ ((z - a) / (z - b) * conj ((c - a) / (c - b))).re

/-- The **solid ideal triangle** with three ideal vertices `a, b, c` on the unit circle: the points of
the open disc in the three closed h-half-planes bounded by the h-lines `ab`, `bc`, `ca` and containing
the opposite vertex. -/
@[kb "petrunin2025" "Section 20I, ideal triangle, p. 177"]
def hidealsolid (a b c : ℂ) : Set ℂ :=
  {z | ‖z‖ < 1 ∧ hidealhalf a b c z ∧ hidealhalf b c a z ∧ hidealhalf c a b z}

theorem hidealhalf_iff {a b c z : ℂ} (hzb : z ≠ b) (hcb : c ≠ b) :
    hidealhalf a b c z ↔ 0 ≤ ((z - a) * conj (z - b) * conj (c - a) * (c - b)).re := by
  have h1 : z - b ≠ 0 := sub_ne_zero.mpr hzb
  have h2 : c - b ≠ 0 := sub_ne_zero.mpr hcb
  have h1' : conj (z - b) ≠ 0 := (map_ne_zero _).mpr h1
  have h2' : conj (c - b) ≠ 0 := (map_ne_zero _).mpr h2
  have e : (z - a) / (z - b) * conj ((c - a) / (c - b)) =
      ((z - a) * conj (z - b) * conj (c - a) * (c - b)) /
        ((Complex.normSq (z - b) * Complex.normSq (c - b) : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, ← Complex.mul_conj, ← Complex.mul_conj, map_div₀]
    field_simp
  unfold hidealhalf
  rw [e, Complex.div_ofReal_re]
  have : 0 < Complex.normSq (z - b) * Complex.normSq (c - b) :=
    mul_pos (Complex.normSq_pos.mpr h1) (Complex.normSq_pos.mpr h2)
  rw [le_div_iff₀ this, zero_mul]

/-- The vertices of the symmetric ideal triangle: `-1`, `e^{iπ/3}`, `e^{-iπ/3}`. -/
noncomputable def idealA : ℂ := -1
noncomputable def idealB : ℂ := ⟨1 / 2, √3 / 2⟩
noncomputable def idealC : ℂ := ⟨1 / 2, -(√3 / 2)⟩

theorem sqrt3_sq : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)

theorem sqrt3_pow : √3 ^ 2 = 3 ∧ √3 ^ 4 = 9 ∧ √3 ^ 3 = 3 * √3 := by
  have := sqrt3_sq
  have h2 : √3 ^ 2 = 3 := by rw [sq]; exact this
  exact ⟨h2, by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2]; norm_num, by rw [pow_succ, h2]⟩

theorem Q_BCA (z : ℂ) :
    ((z - idealB) * conj (z - idealC) * conj (idealA - idealB) * (idealA - idealC)).re =
      3 / 2 * (z.re ^ 2 + z.im ^ 2 + 1 - 4 * z.re) := by
  obtain ⟨h2, h4, h3⟩ := sqrt3_pow
  simp [idealA, idealB, idealC, Complex.mul_re, Complex.mul_im]
  ring_nf
  simp only [h2, h4, h3]
  ring

/-- The defining polynomial `|z|² + 1 - 4 Re (z e^{-iφ})` of the (closed) side of the h-line `|z - 2 e^{iφ}|² = 3`
containing the origin. -/
noncomputable def idealPl (φ : ℝ) (z : ℂ) : ℝ :=
  ‖z‖ ^ 2 + 1 - 4 * (z.re * Real.cos φ + z.im * Real.sin φ)

theorem cos_two_pi_div_three : Real.cos (2 * π / 3) = -(1 / 2) := by
  have : 2 * π / 3 = π - π / 3 := by ring
  rw [this, Real.cos_pi_sub, Real.cos_pi_div_three]

theorem sin_two_pi_div_three : Real.sin (2 * π / 3) = √3 / 2 := by
  have : 2 * π / 3 = π - π / 3 := by ring
  rw [this, Real.sin_pi_sub, Real.sin_pi_div_three]

theorem Q_ABC (z : ℂ) :
    ((z - idealA) * conj (z - idealB) * conj (idealC - idealA) * (idealC - idealB)).re =
      3 / 2 * idealPl (2 * π / 3) z := by
  obtain ⟨h2, h4, h3⟩ := sqrt3_pow
  rw [idealPl, cos_two_pi_div_three, sin_two_pi_div_three, Complex.sq_norm, Complex.normSq_apply]
  simp [idealA, idealB, idealC, Complex.mul_re, Complex.mul_im]
  ring_nf
  simp only [h2, h4, h3]
  ring

theorem Q_CAB (z : ℂ) :
    ((z - idealC) * conj (z - idealA) * conj (idealB - idealC) * (idealB - idealA)).re =
      3 / 2 * idealPl (-(2 * π / 3)) z := by
  obtain ⟨h2, h4, h3⟩ := sqrt3_pow
  rw [idealPl, Real.cos_neg, Real.sin_neg, cos_two_pi_div_three, sin_two_pi_div_three, Complex.sq_norm,
    Complex.normSq_apply]
  simp [idealA, idealB, idealC, Complex.mul_re, Complex.mul_im]
  ring_nf
  simp only [h2, h4, h3]
  ring

theorem Q_BCA' (z : ℂ) :
    ((z - idealB) * conj (z - idealC) * conj (idealA - idealB) * (idealA - idealC)).re =
      3 / 2 * idealPl 0 z := by
  rw [Q_BCA, idealPl]
  simp [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem norm_ideal : ‖idealA‖ = 1 ∧ ‖idealB‖ = 1 ∧ ‖idealC‖ = 1 := by
  obtain ⟨h2, h4, h3⟩ := sqrt3_pow
  refine ⟨by simp [idealA], ?_, ?_⟩ <;>
  · rw [Complex.norm_def, Complex.normSq_apply]
    simp [idealB, idealC]
    nlinarith [sqrt3_sq]

theorem mem_hidealsolid_iff (z : ℂ) :
    z ∈ hidealsolid idealA idealB idealC ↔
      ‖z‖ < 1 ∧ 0 ≤ idealPl (2 * π / 3) z ∧ 0 ≤ idealPl 0 z ∧ 0 ≤ idealPl (-(2 * π / 3)) z := by
  obtain ⟨nA, nB, nC⟩ := norm_ideal
  have hAB : idealA ≠ idealB := by
    intro h; have := congrArg Complex.re h; simp [idealA, idealB] at this; linarith
  have hBC : idealB ≠ idealC := by
    intro h; have := congrArg Complex.im h; simp [idealB, idealC] at this
    have := Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 3); linarith
  have hAC : idealA ≠ idealC := by
    intro h; have := congrArg Complex.re h; simp [idealA, idealC] at this; linarith
  have key : ∀ y : ℂ, ‖y‖ < 1 → ‖y‖ = 1 → False := fun y h1 h2 => by rw [h2] at h1; exact lt_irrefl _ h1
  constructor
  · rintro ⟨hz, h1, h2, h3⟩
    have zA : z ≠ idealA := fun h => key z hz (by rw [h, nA])
    have zB : z ≠ idealB := fun h => key z hz (by rw [h, nB])
    have zC : z ≠ idealC := fun h => key z hz (by rw [h, nC])
    have h1' := (hidealhalf_iff zB hBC.symm).mp h1
    have h2' := (hidealhalf_iff zC hAC).mp h2
    have h3' := (hidealhalf_iff zA hAB.symm).mp h3
    rw [Q_ABC] at h1'
    rw [Q_BCA'] at h2'
    rw [Q_CAB] at h3'
    exact ⟨hz, by linarith, by linarith, by linarith⟩
  · rintro ⟨hz, h1, h2, h3⟩
    have zA : z ≠ idealA := fun h => key z hz (by rw [h, nA])
    have zB : z ≠ idealB := fun h => key z hz (by rw [h, nB])
    have zC : z ≠ idealC := fun h => key z hz (by rw [h, nC])
    refine ⟨hz, (hidealhalf_iff zB hBC.symm).mpr ?_, (hidealhalf_iff zC hAC).mpr ?_,
      (hidealhalf_iff zA hAB.symm).mpr ?_⟩
    · rw [Q_ABC]; linarith
    · rw [Q_BCA']; linarith
    · rw [Q_CAB]; linarith

/-! ### Polar description -/

/-- The three directions of the sides of the symmetric ideal triangle. -/
def IdealDir (φ : ℝ) : Prop := φ = 0 ∨ φ = 2 * π / 3 ∨ φ = -(2 * π / 3)

theorem ideal_cos_gt_half {t : ℝ} (ht : |t| < π / 3) : 1 / 2 < Real.cos t := by
  rw [← Real.cos_abs t, ← Real.cos_pi_div_three]
  exact Real.cos_lt_cos_of_nonneg_of_le_pi_div_two (abs_nonneg t) (by linarith [Real.pi_pos]) ht

theorem ideal_cos_le_half {x : ℝ} (h1 : π / 3 ≤ |x|) (h2 : |x| ≤ π) : Real.cos x ≤ 1 / 2 := by
  rw [← Real.cos_abs x, ← Real.cos_pi_div_three]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [Real.pi_pos]) h2 h1

theorem ideal_cos_shift_le {t : ℝ} (ht : |t| < π / 3) :
    Real.cos (t - 2 * π / 3) ≤ 1 / 2 ∧ Real.cos (t + 2 * π / 3) ≤ 1 / 2 := by
  obtain ⟨h1, h2⟩ := abs_lt.mp ht
  have hp := Real.pi_pos
  constructor
  · apply ideal_cos_le_half
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_neg (by linarith)]; linarith
  · apply ideal_cos_le_half
    · rw [abs_of_pos (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith

theorem ideal_cos_off {φ φ' θ : ℝ} (hφ : IdealDir φ) (hφ' : IdealDir φ') (hne : φ ≠ φ') (hθ : |θ - φ| < π / 3) :
    Real.cos (θ - φ') ≤ 1 / 2 := by
  obtain ⟨b1, b2⟩ := ideal_cos_shift_le hθ
  rcases hφ with h | h | h <;> rcases hφ' with h' | h' | h' <;> subst h <;> subst h'
  · exact absurd rfl hne
  · have e : θ - 2 * π / 3 = (θ - 0) - 2 * π / 3 := by ring
    rw [e]; exact b1
  · have e : θ - -(2 * π / 3) = (θ - 0) + 2 * π / 3 := by ring
    rw [e]; exact b2
  · have e : θ - 0 = (θ - 2 * π / 3) + 2 * π / 3 := by ring
    rw [e]; exact b2
  · exact absurd rfl hne
  · have e : θ - -(2 * π / 3) = ((θ - 2 * π / 3) - 2 * π / 3) + 2 * π := by ring
    rw [e, Real.cos_add_two_pi]; exact b1
  · have e : θ - 0 = (θ - -(2 * π / 3)) - 2 * π / 3 := by ring
    rw [e]; exact b1
  · have e : θ - 2 * π / 3 = ((θ - -(2 * π / 3)) + 2 * π / 3) - 2 * π := by ring
    rw [e, Real.cos_sub_two_pi]; exact b2
  · exact absurd rfl hne

theorem idealPl_polar (φ r θ : ℝ) :
    idealPl φ (Complex.polarCoord.symm (r, θ)) = r ^ 2 + 1 - 4 * r * Real.cos (θ - φ) := by
  rw [idealPl, Complex.norm_polarCoord_symm, sq_abs, Real.cos_sub]
  simp [Complex.polarCoord_symm_apply, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  ring

theorem mem_hidealsolid_polar {r θ : ℝ} (hr : 0 < r) :
    Complex.polarCoord.symm (r, θ) ∈ hidealsolid idealA idealB idealC ↔
      r < 1 ∧ 0 ≤ r ^ 2 + 1 - 4 * r * Real.cos (θ - 2 * π / 3) ∧ 0 ≤ r ^ 2 + 1 - 4 * r * Real.cos (θ - 0) ∧
        0 ≤ r ^ 2 + 1 - 4 * r * Real.cos (θ - -(2 * π / 3)) := by
  rw [mem_hidealsolid_iff, idealPl_polar, idealPl_polar, idealPl_polar, Complex.norm_polarCoord_symm, abs_of_pos hr]

theorem ideal_sector_iff {φ r θ : ℝ} (hφ : IdealDir φ) (hθ : |θ - φ| < π / 3) (hr : 0 < r) :
    (r < 1 ∧ 0 ≤ r ^ 2 + 1 - 4 * r * Real.cos (θ - 2 * π / 3) ∧ 0 ≤ r ^ 2 + 1 - 4 * r * Real.cos (θ - 0) ∧
        0 ≤ r ^ 2 + 1 - 4 * r * Real.cos (θ - -(2 * π / 3))) ↔ r ≤ geodR 2 φ θ := by
  have hk : 1 < 2 * Real.cos (θ - φ) := by linarith [ideal_cos_gt_half hθ]
  obtain ⟨hR0, hR1, hRe, -, -⟩ := geodR_facts hk
  have hRdef : geodR 2 φ θ = 2 * Real.cos (θ - φ) - Real.sqrt ((2 * Real.cos (θ - φ)) ^ 2 - 1) := rfl
  rw [hRdef]
  set k := 2 * Real.cos (θ - φ) with hkdef
  set R := k - Real.sqrt (k ^ 2 - 1) with hRd
  constructor
  · rintro ⟨hr1, h1, h2, h3⟩
    have hmain : 0 ≤ r ^ 2 + 1 - 2 * k * r := by
      have e : 4 * r * Real.cos (θ - φ) = 2 * k * r := by rw [hkdef]; ring
      rcases hφ with h | h | h
      · subst h; rw [e] at *; linarith [h2]
      · subst h; rw [e] at *; linarith [h1]
      · subst h; rw [e] at *; linarith [h3]
    by_contra hcon
    push Not at hcon
    nlinarith [mul_pos (sub_pos.mpr hcon) (by linarith : 0 < 2 * k - r - R)]
  · intro hrR
    have hr1 : r < 1 := lt_of_le_of_lt hrR hR1
    refine ⟨hr1, ?_⟩
    have key : ∀ φ', IdealDir φ' → 0 ≤ r ^ 2 + 1 - 4 * r * Real.cos (θ - φ') := by
      intro φ' hφ'
      by_cases he : φ = φ'
      · subst he
        have : 0 ≤ r ^ 2 + 1 - 2 * k * r := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hrR) (by linarith : 0 ≤ 2 * k - r - R)]
        have e : 4 * r * Real.cos (θ - φ) = 2 * k * r := by rw [hkdef]; ring
        rw [e]; exact this
      · have := ideal_cos_off hφ hφ' he hθ
        nlinarith [sq_nonneg (r - 1)]
    exact ⟨key _ (Or.inr (Or.inl rfl)), key _ (Or.inl rfl), key _ (Or.inr (Or.inr rfl))⟩

/-! ### The hyperbolic area as a measure; the three sectors -/

/-- The hyperbolic area measure `4/(1-|z|²)² dA` on the plane (supported in the disc only through
`harea`, which intersects with the disc). -/
noncomputable def hareaMeasure : Measure ℂ := volume.withDensity hdensity

theorem harea_eq_hmeasure (s : Set ℂ) : harea s = hareaMeasure (s ∩ Metric.ball 0 1) := by
  unfold harea hareaMeasure
  rw [withDensity_apply']

theorem hmeasure_null {N : Set ℂ} (h : volume N = 0) : hareaMeasure N = 0 :=
  withDensity_absolutelyContinuous _ _ h

theorem volume_line_im (c : ℝ) : volume {z : ℂ | z.im = c * z.re} = 0 := by
  let ℓ : ℂ →ₗ[ℝ] ℝ := Complex.imLm - c • Complex.reLm
  have h : {z : ℂ | z.im = c * z.re} = (LinearMap.ker ℓ : Set ℂ) := by
    ext z
    simp [ℓ, sub_eq_zero]
  rw [h]
  refine Measure.addHaar_submodule volume _ ?_
  intro htop
  have : (Complex.I : ℂ) ∈ LinearMap.ker ℓ := by rw [htop]; trivial
  simp [ℓ] at this

theorem measurableSet_radialSet_polar {Θ : Set ℝ} (hΘ : MeasurableSet Θ) (hΘπ : Θ ⊆ Ioo (-π) π) {R : ℝ → ℝ}
    (hR : Measurable R) : MeasurableSet (radialSet Θ R) := by
  have hE := measurableSet_radial hΘ hR
  have hEtarget : {p : ℝ × ℝ | p.2 ∈ Θ ∧ 0 < p.1 ∧ p.1 ≤ R p.2} ⊆ Complex.polarCoord.target := by
    rintro p ⟨h2, h1, -⟩
    exact ⟨h1, hΘπ h2⟩
  refine hE.image_of_continuousOn_injOn ?_ ?_
  · exact Complex.polarCoord.continuousOn_symm.mono hEtarget
  · exact Complex.polarCoord.symm.injOn.mono hEtarget

/-- The sector of the symmetric ideal triangle facing the side with centre direction `φ`. -/
noncomputable def idealSector (φ : ℝ) : Set ℂ := radialSet (Ioo (φ - π / 3) (φ + π / 3)) (geodR 2 φ)

theorem Tsec_subset {φ : ℝ} (hφ : IdealDir φ) : idealSector φ ⊆ hidealsolid idealA idealB idealC := by
  rintro _ ⟨⟨r, θ⟩, ⟨hθ, hr, hrR⟩, rfl⟩
  have hθ' : |θ - φ| < π / 3 := abs_lt.mpr ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  exact (mem_hidealsolid_polar hr).mpr ((ideal_sector_iff hφ hθ' hr).mpr hrR)

theorem Tsec_cover {z : ℂ} (hz : z ∈ hidealsolid idealA idealB idealC) :
    z ∈ idealSector 0 ∪ idealSector (2 * π / 3) ∪ idealSector (-(2 * π / 3)) ∪
      ({z : ℂ | z.im = √3 * z.re} ∪ {z : ℂ | z.im = -√3 * z.re} ∪ {z : ℂ | z.im = 0 * z.re}) := by
  have hp := Real.pi_pos
  by_cases h0 : z = 0
  · subst h0; simp
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr h0
  set θ := Complex.arg z with hθ
  have hzp : z = Complex.polarCoord.symm (‖z‖, θ) := by
    apply Complex.ext
    · simp [Complex.polarCoord_symm_apply, Complex.cos_ofReal_re, hθ, Complex.norm_mul_cos_arg]
    · simp [Complex.polarCoord_symm_apply, Complex.sin_ofReal_re, hθ, Complex.norm_mul_sin_arg]
  have hmem := (mem_hidealsolid_polar hr).mp (hzp ▸ hz)
  have hθ1 := Complex.neg_pi_lt_arg z
  have hθ2 := Complex.arg_le_pi z
  rw [← hθ] at hθ1 hθ2
  have hre : z.re = ‖z‖ * Real.cos θ := (Complex.norm_mul_cos_arg z).symm
  have him : z.im = ‖z‖ * Real.sin θ := (Complex.norm_mul_sin_arg z).symm
  have back : ∀ φ, IdealDir φ → |θ - φ| < π / 3 → z ∈ idealSector φ := by
    intro φ hφ hd
    have hle := (ideal_sector_iff hφ hd hr).mp hmem
    obtain ⟨hl, hu⟩ := abs_lt.mp hd
    refine ⟨(‖z‖, θ), ⟨⟨by linarith, by linarith⟩, hr, hle⟩, hzp.symm⟩
  by_cases a1 : |θ - 0| < π / 3
  · exact Or.inl (Or.inl (Or.inl (back 0 (Or.inl rfl) a1)))
  by_cases a2 : |θ - 2 * π / 3| < π / 3
  · exact Or.inl (Or.inl (Or.inr (back _ (Or.inr (Or.inl rfl)) a2)))
  by_cases a3 : |θ - -(2 * π / 3)| < π / 3
  · exact Or.inl (Or.inr (back _ (Or.inr (Or.inr rfl)) a3))
  refine Or.inr ?_
  rw [abs_lt] at a1 a2 a3
  push Not at a1 a2 a3
  have hθcases : θ = π / 3 ∨ θ = -(π / 3) ∨ θ = π := by
    by_cases c1 : θ ≤ -(π / 3)
    · by_cases c2 : θ = -(π / 3)
      · exact Or.inr (Or.inl c2)
      · exfalso
        have : θ < -(π / 3) := lt_of_le_of_ne c1 c2
        have := a3 (by linarith) 
        linarith
    · push Not at c1
      by_cases c3 : θ ≤ π / 3
      · by_cases c4 : θ = π / 3
        · exact Or.inl c4
        · exfalso
          have := a1 (by linarith)
          have : θ < π / 3 := lt_of_le_of_ne c3 c4
          linarith
      · push Not at c3
        by_cases c5 : θ = π
        · exact Or.inr (Or.inr c5)
        · exfalso
          have : θ < π := lt_of_le_of_ne hθ2 c5
          have := a2 (by linarith)
          linarith
  rcases hθcases with h | h | h
  · refine Or.inl (Or.inl ?_)
    show z.im = √3 * z.re
    rw [him, hre, h, Real.sin_pi_div_three, Real.cos_pi_div_three]; ring
  · refine Or.inl (Or.inr ?_)
    show z.im = -√3 * z.re
    rw [him, hre, h, Real.sin_neg, Real.cos_neg, Real.sin_pi_div_three, Real.cos_pi_div_three]; ring
  · refine Or.inr ?_
    show z.im = 0 * z.re
    rw [him, h, Real.sin_pi]; ring

theorem Tsec_disjoint {φ φ' : ℝ} (hφ : IdealDir φ) (hφ' : IdealDir φ') (hne : φ ≠ φ') :
    Disjoint (idealSector φ) (idealSector φ') := by
  have hp := Real.pi_pos
  rw [Set.disjoint_left]
  rintro _ ⟨⟨r, θ⟩, ⟨hθ, hr, -⟩, rfl⟩ ⟨⟨r', θ'⟩, ⟨hθ', hr', -⟩, h⟩
  have hinj := Complex.polarCoord.symm.injOn
    (show (r', θ') ∈ Complex.polarCoord.target from ⟨hr', ⟨by rcases hφ' with h | h | h <;> subst h <;> linarith [hθ'.1],
      by rcases hφ' with h | h | h <;> subst h <;> linarith [hθ'.2]⟩⟩)
    (show (r, θ) ∈ Complex.polarCoord.target from ⟨hr, ⟨by rcases hφ with h | h | h <;> subst h <;> linarith [hθ.1],
      by rcases hφ with h | h | h <;> subst h <;> linarith [hθ.2]⟩⟩) h
  have : θ' = θ := (Prod.mk.injEq _ _ _ _ ▸ hinj).2
  subst this
  obtain ⟨a1, a2⟩ := hθ
  obtain ⟨b1, b2⟩ := hθ'
  rcases hφ with h | h | h <;> rcases hφ' with h' | h' | h' <;> subst h <;> subst h' <;>
    first | exact hne rfl | linarith

theorem measurable_geodR_two (φ : ℝ) : Measurable (geodR 2 φ) := by
  have hc1 : Continuous fun θ : ℝ => 2 * Real.cos (θ - φ) :=
    continuous_const.mul (Real.continuous_cos.comp (continuous_id.sub continuous_const))
  have hc2 : Continuous fun θ : ℝ => Real.sqrt ((2 * Real.cos (θ - φ)) ^ 2 - 1) :=
    Real.continuous_sqrt.comp ((hc1.pow 2).sub continuous_const)
  exact (hc1.sub hc2).measurable

theorem Tsec_subset_ball {φ : ℝ} (hφ : IdealDir φ) : idealSector φ ⊆ Metric.ball 0 1 := fun z hz =>
  mem_ball_zero_iff.mpr ((Tsec_subset hφ hz).1)

theorem geodG_two_diff (φ : ℝ) :
    geodG 2 φ (φ + π / 3) - geodG 2 φ (φ - π / 3) = π / 3 := by
  have h3 : (0 : ℝ) < √3 := Real.sqrt_pos.mpr (by norm_num)
  have e : (2 : ℝ) ^ 2 - 1 = 3 := by norm_num
  have e1 : 2 * Real.sin (π / 3) / √3 = 1 := by
    rw [Real.sin_pi_div_three]; field_simp
  unfold geodG
  have a1 : φ + π / 3 - φ = π / 3 := by ring
  have a2 : φ - π / 3 - φ = -(π / 3) := by ring
  rw [a1, a2, e, Real.sin_neg, mul_neg, neg_div, e1, Real.arcsin_neg, Real.arcsin_one]
  ring

theorem Tsec_area {φ : ℝ} (hφ : IdealDir φ) : harea (idealSector φ) = ENNReal.ofReal (π / 3) := by
  have hp := Real.pi_pos
  have hp3 := Real.pi_gt_three
  let δ : ℕ → ℝ := fun n => 1 / 2 * (1 / ((n : ℝ) + 1))
  have hδ0 : ∀ n, 0 < δ n := fun n => by positivity
  have hδle : ∀ n, δ n ≤ 1 / 2 := fun n => by
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    simp only [δ]; linarith
  have hδanti : Antitone δ := fun m n hmn => by
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    simp only [δ]
    have : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  have hδt : Filter.Tendsto δ Filter.atTop (nhds 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 2 : ℝ)
    simpa [δ] using this
  have hφrange : -π ≤ φ - π / 3 ∧ φ + π / 3 ≤ π := by
    rcases hφ with h | h | h <;> subst h <;> constructor <;> linarith
  let A : ℕ → Set ℂ := fun n =>
    radialSet (Ioc (φ - π / 3 + δ n) (φ + π / 3 - δ n)) (geodR 2 φ)
  have hAmono : Monotone A := fun m n hmn => by
    refine Set.image_mono fun p hp => ?_
    obtain ⟨h1, h2, h3⟩ := hp
    have := hδanti hmn
    exact ⟨⟨by linarith [h1.1], by linarith [h1.2]⟩, h2, h3⟩
  have hunion : ⋃ n, A n = idealSector φ := by
    apply Set.Subset.antisymm
    · refine Set.iUnion_subset fun n => Set.image_mono fun p hp => ?_
      obtain ⟨h1, h2, h3⟩ := hp
      exact ⟨⟨by linarith [h1.1, hδ0 n], by linarith [h1.2, hδ0 n]⟩, h2, h3⟩
    · rintro _ ⟨⟨r, θ⟩, ⟨hθ, hr, hle⟩, rfl⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (lt_min (sub_pos.mpr hθ.1) (sub_pos.mpr hθ.2))
      have h1 := lt_of_lt_of_le hn (min_le_left _ _)
      have h2 := lt_of_lt_of_le hn (min_le_right _ _)
      have h0 : δ n ≤ 1 / ((n : ℝ) + 1) := by
        have : 0 < 1 / ((n : ℝ) + 1) := by positivity
        simp only [δ]; linarith
      exact Set.mem_iUnion.mpr ⟨n, (r, θ), ⟨⟨by linarith, by linarith⟩, hr, hle⟩, rfl⟩
  have hAarea : ∀ n, harea (A n) = ENNReal.ofReal
      (geodG 2 φ (φ + π / 3 - δ n) - geodG 2 φ (φ - π / 3 + δ n)) := by
    intro n
    have hd0 := hδ0 n
    have hd1 := hδle n
    refine harea_geodesic_sector (by norm_num) (by linarith) ?_ ?_
    · intro x hx
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    · intro θ hθ
      have : |θ - φ| < π / 3 := abs_lt.mpr ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
      linarith [ideal_cos_gt_half this]
  have hAhm : ∀ n, hareaMeasure (A n) = harea (A n) := fun n => by
    rw [harea_eq_hmeasure, inter_eq_left.mpr]
    exact fun z hz => mem_ball_zero_iff.mpr (Tsec_subset hφ (hunion ▸ Set.mem_iUnion.mpr ⟨n, hz⟩)).1
  have hT := tendsto_measure_iUnion_atTop (μ := hareaMeasure) hAmono
  rw [hunion] at hT
  have hG : Continuous (geodG 2 φ) := by
    unfold geodG
    exact (Real.continuous_arcsin.comp (by fun_prop)).sub continuous_id
  have hlim : Filter.Tendsto (fun n => ENNReal.ofReal
      (geodG 2 φ (φ + π / 3 - δ n) - geodG 2 φ (φ - π / 3 + δ n))) Filter.atTop
      (nhds (ENNReal.ofReal (π / 3))) := by
    refine ENNReal.tendsto_ofReal ?_
    have h1 : Filter.Tendsto (fun n => φ + π / 3 - δ n) Filter.atTop (nhds (φ + π / 3)) := by
      simpa using (tendsto_const_nhds (x := φ + π / 3)).sub hδt
    have h2 : Filter.Tendsto (fun n => φ - π / 3 + δ n) Filter.atTop (nhds (φ - π / 3)) := by
      simpa using (tendsto_const_nhds (x := φ - π / 3)).add hδt
    have key := ((hG.tendsto (φ + π / 3)).comp h1).sub ((hG.tendsto (φ - π / 3)).comp h2)
    rw [geodG_two_diff φ] at key
    exact key
  have hT' : Filter.Tendsto (fun n => hareaMeasure (A n)) Filter.atTop (nhds (hareaMeasure (idealSector φ))) := hT
  simp only [hAhm, hAarea] at hT'
  have := tendsto_nhds_unique hT' hlim
  rw [harea_eq_hmeasure, inter_eq_left.mpr (Tsec_subset_ball hφ)]
  exact this

/-- **The area of an ideal triangle is `π`** (Petrunin, Section 20I, p. 177), for the symmetric ideal
triangle with vertices `-1`, `e^{iπ/3}`, `e^{-iπ/3}` on the absolute.  (The general case is
`harea_hidealsolid`, which reduces to this one by a motion.)
The solid ideal triangle is cut by the rays to the origin into three sectors, each of area `π/3`
(the sector area of `harea_geodesic_sector`, taken as the limit when the bounding rays tend to the ideal
vertices). -/
@[kb "petrunin2025" "Section 20I, area of an ideal triangle, p. 177"]
theorem harea_hidealsolid_symmetric :
    harea (hidealsolid idealA idealB idealC) = ENNReal.ofReal π := by
  have hp := Real.pi_pos
  have d0 : IdealDir 0 := Or.inl rfl
  have d1 : IdealDir (2 * π / 3) := Or.inr (Or.inl rfl)
  have d2 : IdealDir (-(2 * π / 3)) := Or.inr (Or.inr rfl)
  have hmeas : ∀ φ, IdealDir φ → MeasurableSet (idealSector φ) := by
    intro φ hφ
    refine measurableSet_radialSet_polar measurableSet_Ioo ?_ (measurable_geodR_two φ)
    rcases hφ with h | h | h <;> subst h <;> intro x hx <;> constructor <;> linarith [hx.1, hx.2]
  have hhm : ∀ φ, IdealDir φ → hareaMeasure (idealSector φ) = ENNReal.ofReal (π / 3) := by
    intro φ hφ
    rw [← Tsec_area hφ, harea_eq_hmeasure, inter_eq_left.mpr (Tsec_subset_ball hφ)]
  set S := hidealsolid idealA idealB idealC with hS
  set N : Set ℂ := {z : ℂ | z.im = √3 * z.re} ∪ {z : ℂ | z.im = -√3 * z.re} ∪
    {z : ℂ | z.im = 0 * z.re} with hN
  have hNnull : hareaMeasure N = 0 := by
    apply hmeasure_null
    exact measure_union_null (measure_union_null (volume_line_im _) (volume_line_im _)) (volume_line_im _)
  set T := idealSector 0 ∪ idealSector (2 * π / 3) ∪ idealSector (-(2 * π / 3)) with hT
  have hTS : T ⊆ S := Set.union_subset (Set.union_subset (Tsec_subset d0) (Tsec_subset d1))
    (Tsec_subset d2)
  have hST : S ⊆ T ∪ N := fun z hz => Tsec_cover hz
  have hSball : S ⊆ Metric.ball 0 1 := fun z hz => mem_ball_zero_iff.mpr hz.1
  have hmT : hareaMeasure T = ENNReal.ofReal π := by
    have hne01 : (0 : ℝ) ≠ 2 * π / 3 := by intro h; linarith
    have hne02 : (0 : ℝ) ≠ -(2 * π / 3) := by intro h; linarith
    have hne12 : 2 * π / 3 ≠ -(2 * π / 3) := by intro h; linarith
    have hdis : Disjoint (idealSector 0 ∪ idealSector (2 * π / 3)) (idealSector (-(2 * π / 3))) :=
      (Tsec_disjoint d0 d2 hne02).union_left (Tsec_disjoint d1 d2 hne12)
    rw [hT, measure_union hdis (hmeas _ d2), measure_union (Tsec_disjoint d0 d1 hne01) (hmeas _ d1),
      hhm _ d0, hhm _ d1, hhm _ d2, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1; ring
  rw [harea_eq_hmeasure, inter_eq_left.mpr hSball]
  apply le_antisymm
  · calc hareaMeasure S ≤ hareaMeasure (T ∪ N) := measure_mono hST
      _ ≤ hareaMeasure T + hareaMeasure N := measure_union_le _ _
      _ = ENNReal.ofReal π := by rw [hNnull, add_zero, hmT]
  · rw [← hmT]; exact measure_mono hTS

end Ideal

section General

open Real MeasureTheory Set ComplexConjugate

theorem hidealhalf_swap (a b c z : ℂ) : hidealhalf a b c z ↔ hidealhalf b a c z := by
  unfold hidealhalf
  set X := (z - a) / (z - b) * conj ((c - a) / (c - b)) with hX
  have e : (z - b) / (z - a) * conj ((c - b) / (c - a)) = X⁻¹ := by
    rw [hX]; simp [map_div₀]; ring
  rw [e, Complex.inv_re]
  by_cases hn : Complex.normSq X = 0
  · have : X = 0 := Complex.normSq_eq_zero.mp hn
    simp [this]
  · have hpos : 0 < Complex.normSq X := lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm hn)
    rw [le_div_iff₀ hpos, zero_mul]

theorem hidealsolid_cyc (a b c : ℂ) : hidealsolid a b c = hidealsolid b c a := by
  ext z
  simp only [hidealsolid, mem_setOf_eq]
  tauto

theorem hidealsolid_swap12 (a b c : ℂ) : hidealsolid a b c = hidealsolid b a c := by
  ext z
  simp only [hidealsolid, mem_setOf_eq]
  rw [hidealhalf_swap a b c z, hidealhalf_swap b c a z, hidealhalf_swap c a b z]
  constructor
  · rintro ⟨h0, h1, h2, h3⟩; exact ⟨h0, h1, h3, h2⟩
  · rintro ⟨h0, h1, h2, h3⟩; exact ⟨h0, h1, h3, h2⟩

theorem hidealsolid_swap23 (a b c : ℂ) : hidealsolid a b c = hidealsolid a c b := by
  exact (hidealsolid_cyc c a b).symm.trans (hidealsolid_swap12 c a b)

theorem measurableSet_hidealsolid (a b c : ℂ) : MeasurableSet (hidealsolid a b c) := by
  have hm : ∀ a b c : ℂ, MeasurableSet {z | hidealhalf a b c z} := by
    intro a b c
    unfold hidealhalf
    refine measurableSet_le measurable_const (Complex.measurable_re.comp ?_)
    fun_prop
  have : hidealsolid a b c = Metric.ball 0 1 ∩ ({z | hidealhalf a b c z} ∩ ({z | hidealhalf b c a z} ∩
      {z | hidealhalf c a b z})) := by
    ext z; simp [hidealsolid, mem_ball_zero_iff]
  rw [this]
  exact Metric.isOpen_ball.measurableSet.inter ((hm _ _ _).inter ((hm _ _ _).inter (hm _ _ _)))

theorem den_ne_unit {w a : ℂ} (hw : ‖w‖ < 1) (ha : ‖a‖ = 1) : 1 - conj w * a ≠ 0 := by
  intro h
  have h1 : conj w * a = 1 := by linear_combination -h
  have h2 := congrArg norm h1
  rw [norm_mul, Complex.norm_conj, norm_one, ha] at h2
  linarith

theorem mobius_sub' {w z a : ℂ} (hz : 1 - conj w * z ≠ 0) (ha : 1 - conj w * a ≠ 0) :
    mobius w z - mobius w a =
      ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) * (z - a) / ((1 - conj w * z) * (1 - conj w * a)) := by
  have hn : ((‖w‖ ^ 2 : ℝ) : ℂ) = w * conj w := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  unfold mobius
  rw [div_sub_div _ _ hz ha, div_eq_div_iff (mul_ne_zero hz ha) (mul_ne_zero hz ha)]
  push_cast at hn ⊢
  rw [hn]
  ring

theorem ratio_alg {k x y Dz Da Db : ℂ} (hk : k ≠ 0) (hy : y ≠ 0) (hDz : Dz ≠ 0) (hDa : Da ≠ 0)
    (hDb : Db ≠ 0) : k * x / (Dz * Da) / (k * y / (Dz * Db)) = x / y * (Db / Da) := by
  field_simp

theorem hidealhalf_motion {w u a b c z : ℂ} (hw : ‖w‖ < 1) (hu : ‖u‖ = 1) (ha : ‖a‖ = 1)
    (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hz : ‖z‖ < 1) (hcb : c ≠ b) :
    hidealhalf (u * mobius w a) (u * mobius w b) (u * mobius w c) (u * mobius w z) ↔
      hidealhalf a b c z := by
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have Da := den_ne_unit hw ha
  have Db := den_ne_unit hw hb
  have Dc := den_ne_unit hw hc
  have Dz := mobius_den_ne hw hz
  have hk : ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
    exact_mod_cast this.ne'
  have hzb : z - b ≠ 0 := sub_ne_zero.mpr (fun h => by rw [h, hb] at hz; exact lt_irrefl _ hz)
  have hcb' : c - b ≠ 0 := sub_ne_zero.mpr hcb
  set κ : ℂ := (1 - conj w * b) / (1 - conj w * a) with hκ
  have hκ0 : κ ≠ 0 := div_ne_zero Db Da
  have e1 : (u * mobius w z - u * mobius w a) / (u * mobius w z - u * mobius w b) =
      (z - a) / (z - b) * κ := by
    rw [← mul_sub, ← mul_sub, mul_div_mul_left _ _ hu0, mobius_sub' Dz Da, mobius_sub' Dz Db, hκ]
    exact ratio_alg hk hzb Dz Da Db
  have e2 : (u * mobius w c - u * mobius w a) / (u * mobius w c - u * mobius w b) =
      (c - a) / (c - b) * κ := by
    rw [← mul_sub, ← mul_sub, mul_div_mul_left _ _ hu0, mobius_sub' Dc Da, mobius_sub' Dc Db, hκ]
    exact ratio_alg hk hcb' Dc Da Db
  unfold hidealhalf
  rw [e1, e2]
  have key : (z - a) / (z - b) * κ * conj ((c - a) / (c - b) * κ) =
      ((Complex.normSq κ : ℝ) : ℂ) * ((z - a) / (z - b) * conj ((c - a) / (c - b))) := by
    rw [map_mul, ← Complex.mul_conj κ]
    ring
  rw [key, Complex.re_ofReal_mul]
  exact mul_nonneg_iff_of_pos_left (Complex.normSq_pos.mpr hκ0)

theorem hidealsolid_image {w u a b c : ℂ} (hw : ‖w‖ < 1) (hu : ‖u‖ = 1) (ha : ‖a‖ = 1)
    (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    (fun z => u * mobius w z) '' hidealsolid a b c =
      hidealsolid (u * mobius w a) (u * mobius w b) (u * mobius w c) := by
  ext z'
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨hz1, h1, h2, h3⟩ := hz
    exact ⟨norm_motion_lt hw hu hz1,
      (hidealhalf_motion hw hu ha hb hc hz1 hbc.symm).mpr h1,
      (hidealhalf_motion hw hu hb hc ha hz1 hca.symm).mpr h2,
      (hidealhalf_motion hw hu hc ha hb hz1 hab.symm).mpr h3⟩
  · rintro ⟨hz1, h1, h2, h3⟩
    have hw' : ‖-w‖ < 1 := by rwa [norm_neg]
    have hy : ‖conj u * z'‖ < 1 := by rw [norm_mul, Complex.norm_conj, hu, one_mul]; exact hz1
    have hz2 : ‖mobius (-w) (conj u * z')‖ < 1 := norm_mobius_lt_one hw' hy
    have hg : u * mobius w (mobius (-w) (conj u * z')) = z' := by
      have := mobius_neg_mobius hw' hy
      rw [neg_neg] at this
      rw [this, ← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]
      simp
    refine ⟨mobius (-w) (conj u * z'), ?_, hg⟩
    rw [← hg] at h1 h2 h3
    exact ⟨hz2, (hidealhalf_motion hw hu ha hb hc hz2 hbc.symm).mp h1,
      (hidealhalf_motion hw hu hb hc ha hz2 hca.symm).mp h2,
      (hidealhalf_motion hw hu hc ha hb hz2 hab.symm).mp h3⟩

theorem harea_hidealsolid_motion {w u a b c : ℂ} (hw : ‖w‖ < 1) (hu : ‖u‖ = 1) (ha : ‖a‖ = 1)
    (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    harea (hidealsolid (u * mobius w a) (u * mobius w b) (u * mobius w c)) =
      harea (hidealsolid a b c) := by
  rw [← hidealsolid_image hw hu ha hb hc hab hbc hca]
  exact harea_motion hw hu (measurableSet_hidealsolid a b c) (fun z hz => mem_ball_zero_iff.mpr hz.1)

/-! ### Transitivity on triples of the absolute -/

/-- The point of the unit circle with stereographic coordinate `σ` (from the pole `-1`). -/
noncomputable def dd (σ : ℝ) : ℂ := (Complex.I - σ) / (Complex.I + σ)

theorem I_add_ne (σ : ℝ) : Complex.I + (σ : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this

theorem exists_dd {b : ℂ} (hb : ‖b‖ = 1) (hb1 : b ≠ -1) : ∃ σ : ℝ, b = dd σ := by
  have h1 : 1 + b ≠ 0 := fun h => hb1 (by linear_combination h)
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb
  have hcb : conj b = b⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hb]; simp
  set s : ℂ := Complex.I * (1 - b) / (1 + b) with hs
  have hreal : conj s = s := by
    rw [hs]
    simp only [map_div₀, map_mul, map_sub, map_add, map_one, Complex.conj_I, hcb]
    have : 1 + b⁻¹ ≠ 0 := by
      intro h; apply h1; field_simp at h; linear_combination h
    have h1' : b + 1 ≠ 0 := by rwa [add_comm]
    field_simp
    rw [← sub_eq_zero]
    ring_nf
  have hsr : ((s.re : ℝ) : ℂ) = s := Complex.conj_eq_iff_re.mp hreal
  refine ⟨s.re, ?_⟩
  rw [dd, hsr, hs]
  have h2 : Complex.I + Complex.I * (1 - b) / (1 + b) ≠ 0 := by
    have : Complex.I + Complex.I * (1 - b) / (1 + b) = 2 * Complex.I / (1 + b) := by
      field_simp; ring
    rw [this]; exact div_ne_zero (by simp) h1
  rw [eq_div_iff h2]
  field_simp
  ring

theorem motion_pq {p q z : ℂ} (hqp : ‖q‖ < ‖p‖) (hz : ‖z‖ ≤ 1) :
    (p / conj p) * mobius (-q / p) z = (p * z + q) / (conj q * z + conj p) := by
  have hp0 : p ≠ 0 := by
    intro h; rw [h] at hqp; simp at hqp; linarith [norm_nonneg q]
  have hcp : conj p ≠ 0 := by simpa using hp0
  have hD : conj q * z + conj p ≠ 0 := by
    intro h
    have h1 : conj p = -(conj q * z) := by linear_combination h
    have h2 := congrArg norm h1
    rw [norm_neg, norm_mul, Complex.norm_conj, Complex.norm_conj] at h2
    nlinarith [norm_nonneg q, norm_nonneg z]
  have hD' : conj p + conj q * z ≠ 0 := by rwa [add_comm]
  unfold mobius
  have e : 1 - conj (-q / p) * z = (conj p + conj q * z) / conj p := by
    rw [map_div₀, map_neg]; field_simp; ring
  rw [e]
  have h3 : (z - -q / p) = (p * z + q) / p := by field_simp; ring
  rw [h3]
  field_simp
  ring

/-- The parameters of the motion carrying the coordinates `σ ↦ λ(σ - m)`. -/
noncomputable def pP (l m : ℝ) : ℂ := ⟨-(1 + l), l * m⟩
noncomputable def qQ (l m : ℝ) : ℂ := ⟨-(1 - l), l * m⟩

theorem norm_qQ_lt {l m : ℝ} (hl : 0 < l) : ‖qQ l m‖ < ‖pP l m‖ := by
  have h : Complex.normSq (qQ l m) < Complex.normSq (pP l m) := by
    simp only [Complex.normSq_apply, qQ, pP]; nlinarith
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h
  by_contra hc
  push Not at hc
  nlinarith [norm_nonneg (qQ l m), norm_nonneg (pP l m)]

theorem motion_dd {l m : ℝ} (hl : 0 < l) (σ : ℝ) :
    (pP l m / conj (pP l m)) * mobius (-qQ l m / pP l m) (dd σ) = dd (l * (σ - m)) := by
  have hq := norm_qQ_lt (m := m) hl
  have hdn : ‖dd σ‖ = 1 := by
    rw [dd, norm_div]
    have h1 : ‖Complex.I - (σ : ℂ)‖ = ‖Complex.I + (σ : ℂ)‖ := by
      rw [Complex.norm_def, Complex.norm_def]
      congr 1
      simp [Complex.normSq_apply]
    rw [h1, div_self]
    exact norm_ne_zero_iff.mpr (I_add_ne σ)
  rw [motion_pq hq hdn.le]
  have hI := I_add_ne σ
  have hI2 : Complex.I + ((l * (σ - m) : ℝ) : ℂ) ≠ 0 := I_add_ne _
  have N : pP l m * (Complex.I - σ) + qQ l m * (Complex.I + σ) =
      -2 * (Complex.I - ((l * (σ - m) : ℝ) : ℂ)) := by
    apply Complex.ext <;> simp [pP, qQ] <;> ring
  have D : conj (qQ l m) * (Complex.I - σ) + conj (pP l m) * (Complex.I + σ) =
      -2 * (Complex.I + ((l * (σ - m) : ℝ) : ℂ)) := by
    apply Complex.ext <;> simp [pP, qQ] <;> ring
  have hnum : pP l m * dd σ + qQ l m =
      (-2 * (Complex.I - ((l * (σ - m) : ℝ) : ℂ))) / (Complex.I + σ) := by
    rw [← N, dd]; field_simp
  have hden : conj (qQ l m) * dd σ + conj (pP l m) =
      (-2 * (Complex.I + ((l * (σ - m) : ℝ) : ℂ))) / (Complex.I + σ) := by
    rw [← D, dd]; field_simp
  rw [hnum, hden, dd, div_div_div_cancel_right₀ hI]
  rw [mul_div_mul_left _ _ (by norm_num : (-2 : ℂ) ≠ 0)]

theorem motion_neg_one {l m : ℝ} (hl : 0 < l) :
    (pP l m / conj (pP l m)) * mobius (-qQ l m / pP l m) (-1) = -1 := by
  rw [motion_pq (norm_qQ_lt hl) (by simp)]
  have n : pP l m * (-1) + qQ l m = ((2 * l : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [pP, qQ] <;> ring
  have d : conj (qQ l m) * (-1) + conj (pP l m) = -((2 * l : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [pP, qQ] <;> ring
  rw [n, d]
  have : ((2 * l : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * l : ℝ) ≠ 0)
  field_simp

theorem idealB_eq : idealB = dd (1 / √3) := by
  have h3 : (0 : ℝ) < √3 := Real.sqrt_pos.mpr (by norm_num)
  have hI := I_add_ne (1 / √3)
  rw [dd, eq_div_iff hI]
  obtain ⟨h2, -, -⟩ := sqrt3_pow
  apply Complex.ext <;> simp [idealB] <;> field_simp <;> nlinarith [h2]

theorem idealC_eq : idealC = dd (-(1 / √3)) := by
  have h3 : (0 : ℝ) < √3 := Real.sqrt_pos.mpr (by norm_num)
  have hI := I_add_ne (-(1 / √3))
  rw [dd, eq_div_iff hI]
  obtain ⟨h2, -, -⟩ := sqrt3_pow
  apply Complex.ext <;> simp [idealC] <;> field_simp <;> nlinarith [h2]

theorem norm_dd (σ : ℝ) : ‖dd σ‖ = 1 := by
  rw [dd, norm_div]
  have h1 : ‖Complex.I - (σ : ℂ)‖ = ‖Complex.I + (σ : ℂ)‖ := by
    rw [Complex.norm_def, Complex.norm_def]
    congr 1
    simp [Complex.normSq_apply]
  rw [h1, div_self]
  exact norm_ne_zero_iff.mpr (I_add_ne σ)

theorem harea_dd {σb σc : ℝ} (h : σc < σb) (hb1 : dd σb ≠ -1) (hc1 : dd σc ≠ -1)
    (hbc : dd σb ≠ dd σc) :
    harea (hidealsolid (-1) (dd σb) (dd σc)) = ENNReal.ofReal π := by
  have h3 : (0 : ℝ) < √3 := Real.sqrt_pos.mpr (by norm_num)
  have hd : 0 < σb - σc := sub_pos.mpr h
  set l : ℝ := 2 / (√3 * (σb - σc)) with hl
  set m : ℝ := (σb + σc) / 2 with hm
  have hl0 : 0 < l := by positivity
  have hq := norm_qQ_lt (m := m) hl0
  have hp0 : 0 < ‖pP l m‖ := lt_of_le_of_lt (norm_nonneg _) hq
  have hw : ‖-qQ l m / pP l m‖ < 1 := by
    rw [norm_div, norm_neg, div_lt_one hp0]; exact hq
  have hu : ‖pP l m / conj (pP l m)‖ = 1 := by
    rw [norm_div, Complex.norm_conj, div_self hp0.ne']
  have m1 : ‖(-1 : ℂ)‖ = 1 := by simp
  have key := harea_hidealsolid_motion hw hu m1 (norm_dd σb) (norm_dd σc) (Ne.symm hb1)
    hbc (hc1)
  rw [motion_neg_one hl0, motion_dd hl0, motion_dd hl0] at key
  have e1 : l * (σb - m) = 1 / √3 := by
    rw [hl, hm]; field_simp; ring
  have e2 : l * (σc - m) = -(1 / √3) := by
    rw [hl, hm]; field_simp; ring
  rw [e1, e2, ← idealB_eq, ← idealC_eq] at key
  rw [← key]
  exact harea_hidealsolid_symmetric

theorem harea_normalized {b c : ℂ} (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hb1 : b ≠ -1) (hc1 : c ≠ -1)
    (hbc : b ≠ c) : harea (hidealsolid (-1) b c) = ENNReal.ofReal π := by
  obtain ⟨σb, rfl⟩ := exists_dd hb hb1
  obtain ⟨σc, rfl⟩ := exists_dd hc hc1
  rcases lt_trichotomy σc σb with h | h | h
  · exact harea_dd h hb1 hc1 hbc
  · exact absurd (by rw [h]) hbc
  · rw [hidealsolid_swap23]
    exact harea_dd h hc1 hb1 hbc.symm

/-- **The area of any ideal triangle is `π`** (Petrunin, Section 20I, p. 177): for three distinct points
`a, b, c` of the absolute (the unit circle), the solid ideal triangle `hidealsolid a b c` has hyperbolic
area `π`.  The proof moves `a` to `-1` by a rotation, then moves `b, c` to `e^{±iπ/3}` by an h-motion
(the explicit motion `σ ↦ λ(σ - m)` of stereographic coordinates), and uses the symmetric case
`harea_hidealsolid_symmetric` and the invariance of `harea` under motions. -/
@[kb "petrunin2025" "Section 20I, area of an ideal triangle, p. 177"]
theorem harea_hidealsolid {a b c : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    harea (hidealsolid a b c) = ENNReal.ofReal π := by
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  have hu : ‖-conj a‖ = 1 := by rw [norm_neg, Complex.norm_conj, ha]
  have hu0 : -conj a ≠ 0 := by intro h; rw [h] at hu; simp at hu
  have hua : -conj a * a = -1 := by
    rw [neg_mul, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, ha]; simp
  have h0 : ‖(0 : ℂ)‖ < 1 := by simp
  have key := harea_hidealsolid_motion h0 hu ha hb hc hab hbc hca
  simp only [mobius_zero_left] at key
  rw [hua] at key
  rw [← key]
  have nb : ‖-conj a * b‖ = 1 := by rw [norm_mul, hu, hb, one_mul]
  have nc : ‖-conj a * c‖ = 1 := by rw [norm_mul, hu, hc, one_mul]
  refine harea_normalized nb nc ?_ ?_ ?_
  · intro h; apply hab; apply mul_left_cancel₀ hu0; rw [hua, h]
  · intro h; apply hca; symm; apply mul_left_cancel₀ hu0; rw [hua, h]
  · intro h; exact hbc (mul_left_cancel₀ hu0 h)

end General

end UndergradKB.Geometry
