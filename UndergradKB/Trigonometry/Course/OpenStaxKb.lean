import UndergradKB.Common.Attr
import UndergradKB.Trigonometry.Coterminal
import UndergradKB.Trigonometry.RightTriangle
import UndergradKB.Trigonometry.Reciprocal
import UndergradKB.Trigonometry.Quadrants
import UndergradKB.Trigonometry.Identities
import UndergradKB.Trigonometry.HalfAngle
import UndergradKB.Trigonometry.Ambiguous
import UndergradKB.Trigonometry.Triangle.Tangents
import UndergradKB.Trigonometry.Triangle.Heron
import UndergradKB.Trigonometry.Triangle.Incenter
import UndergradKB.Trigonometry.Radian
import UndergradKB.Trigonometry.ArcLength
import UndergradKB.Trigonometry.Graphs
import UndergradKB.Trigonometry.Inverse
import UndergradKB.Trigonometry.Equations
import UndergradKB.Trigonometry.CosFixedPoint
import UndergradKB.Trigonometry.Argument
import UndergradKB.Trigonometry.PolarForm
import UndergradKB.Trigonometry.Roots
import UndergradKB.Trigonometry.PolarCurves
import UndergradKB.Trigonometry.Limacon
import UndergradKB.Trigonometry.Vocabulary
import UndergradKB.Trigonometry.Speed
import UndergradKB.Trigonometry.Segment
import UndergradKB.Trigonometry.LimaconConvex
import UndergradKB.Trigonometry.Rose
import UndergradKB.Trigonometry.Secant

/-! # Course layer: OpenStax *Algebra and Trigonometry* 2e, items proved in the knowledge base

Thin theorems in the book's terms whose proofs are the theorems of `UndergradKB/Trigonometry/*.lean`
listed in the coverage checklist (rows classified `in this library`).  All angles are in radians.
-/

namespace UndergradKB.Trigonometry.Course.OpenStax

open EuclideanGeometry Real Set ComplexConjugate

set_option linter.unusedVariables false

/-- Coterminal angles have the same sine and cosine (TR-006). -/
@[kb "openstaxalgtrig2e" "§7.1, p. 686"]
theorem s7_1_coterminal_same_values (θ : ℝ) (k : ℤ) :
    sin (θ + k * (2 * π)) = sin θ ∧ cos (θ + k * (2 * π)) = cos θ :=
  UndergradKB.Trigonometry.sin_cos_add_int_mul_two_pi θ k

/-- Adding any number of full turns gives a coterminal angle with the same sine and cosine (TR-006). -/
@[kb "openstaxalgtrig2e" "§7.1, p. 687"]
theorem s7_1_coterminal_infinitely_many (θ : ℝ) (k : ℤ) :
    sin (θ + k * (2 * π)) = sin θ ∧ cos (θ + k * (2 * π)) = cos θ :=
  UndergradKB.Trigonometry.sin_cos_add_int_mul_two_pi θ k

/-- Every angle is coterminal with exactly one angle in $[0, 2\pi)$ (TR-010). -/
@[kb "openstaxalgtrig2e" "§7.1, p. 687"]
theorem s7_1_coterminal_in_zero_two_pi (θ : ℝ) :
    ∃! φ, φ ∈ Ico 0 (2 * π) ∧ ∃ k : ℤ, φ = θ + k * (2 * π) :=
  UndergradKB.Trigonometry.existsUnique_coterminal_Ico θ

/-- Every angle is coterminal with exactly one angle in $[0, 360)$ degrees (TR-010). -/
@[kb "openstaxalgtrig2e" "§7.1, p. 688"]
theorem s7_1_coterminal_in_zero_360 (x : ℝ) :
    ∃! y, y ∈ Ico (0 : ℝ) 360 ∧ ∃ k : ℤ, y = x + k * 360 :=
  UndergradKB.Trigonometry.existsUnique_coterminal_Ico_deg x

/-- In a right triangle the two acute angles are complementary (TR-011). -/
@[kb "openstaxalgtrig2e" "§7.2, p. 703"]
theorem s7_2_acute_angles_complementary {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) (h12 : p₂ ≠ p₁) :
    ∠ p₂ p₃ p₁ + ∠ p₃ p₁ p₂ = π / 2 :=
  UndergradKB.Trigonometry.angle_add_angle_of_angle_eq_pi_div_two h h12

/-- Cosecant, secant and cotangent of an acute angle of a right triangle as ratios of sides (TR-016). -/
@[kb "openstaxalgtrig2e" "§7.2, p. 699"]
theorem s7_2_csc_sec_cot_ratios {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) (h0 : p₁ ≠ p₂ ∨ p₃ ≠ p₂) :
    UndergradKB.Trigonometry.csc (∠ p₂ p₃ p₁) = dist p₁ p₃ / dist p₁ p₂ ∧ UndergradKB.Trigonometry.sec (∠ p₂ p₃ p₁)
      = dist p₁ p₃ / dist p₃ p₂ ∧ cot (∠ p₂ p₃ p₁) = dist p₃ p₂ / dist p₁ p₂ :=
  ⟨UndergradKB.Trigonometry.csc_angle_of_angle_eq_pi_div_two h h0,
    UndergradKB.Trigonometry.sec_angle_of_angle_eq_pi_div_two h,
    UndergradKB.Trigonometry.cot_angle_of_angle_eq_pi_div_two h⟩

/-- Cosecant, secant and cotangent as hypotenuse over opposite, hypotenuse over adjacent, adjacent over opposite
    (TR-016). -/
@[kb "openstaxalgtrig2e" "§7.2, p. 700"]
theorem s7_2_csc_sec_cot_ratios_defined {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) (h0 : p₁ ≠ p₂ ∨ p₃ ≠ p₂) :
    UndergradKB.Trigonometry.csc (∠ p₂ p₃ p₁) = dist p₁ p₃ / dist p₁ p₂ ∧ UndergradKB.Trigonometry.sec (∠ p₂ p₃ p₁)
      = dist p₁ p₃ / dist p₃ p₂ ∧ cot (∠ p₂ p₃ p₁) = dist p₃ p₂ / dist p₁ p₂ :=
  ⟨UndergradKB.Trigonometry.csc_angle_of_angle_eq_pi_div_two h h0,
    UndergradKB.Trigonometry.sec_angle_of_angle_eq_pi_div_two h,
    UndergradKB.Trigonometry.cot_angle_of_angle_eq_pi_div_two h⟩

/-- Exact values of the functions at 30, 45 and 60 degrees (TR-018). -/
@[kb "openstaxalgtrig2e" "§7.2, p. 702"]
theorem s7_2_special_values_p702 :
    (tan (π / 6) = √3 / 3 ∧ cot (π / 6) = √3 ∧ UndergradKB.Trigonometry.sec (π / 6) = 2 * √3 / 3 ∧
      UndergradKB.Trigonometry.csc (π / 6) = 2) ∧ (tan (π / 4) = 1 ∧ cot (π / 4) = 1 ∧ UndergradKB.Trigonometry.sec
      (π / 4) = √2 ∧ UndergradKB.Trigonometry.csc (π / 4) = √2) ∧ (tan (π / 3) = √3 ∧ cot (π / 3) = √3 / 3 ∧
      UndergradKB.Trigonometry.sec (π / 3) = 2 ∧ UndergradKB.Trigonometry.csc (π / 3) = 2 * √3 / 3) :=
  UndergradKB.Trigonometry.six_functions_special_values

/-- Exact values of the functions at 30 degrees (TR-018). -/
@[kb "openstaxalgtrig2e" "§7.3, p. 716"]
theorem s7_3_special_values_p716 :
    (tan (π / 6) = √3 / 3 ∧ cot (π / 6) = √3 ∧ UndergradKB.Trigonometry.sec (π / 6) = 2 * √3 / 3 ∧
      UndergradKB.Trigonometry.csc (π / 6) = 2) :=
  UndergradKB.Trigonometry.six_functions_special_values.1

/-- Exact values of the functions at 60 degrees (TR-018). -/
@[kb "openstaxalgtrig2e" "§7.3, p. 719"]
theorem s7_3_special_values_p719 :
    (tan (π / 3) = √3 ∧ cot (π / 3) = √3 / 3 ∧ UndergradKB.Trigonometry.sec (π / 3) = 2 ∧
      UndergradKB.Trigonometry.csc (π / 3) = 2 * √3 / 3) :=
  UndergradKB.Trigonometry.six_functions_special_values.2.2

/-- Sides of a 45-45-90 triangle are in ratio 1 : 1 : sqrt 2 (TR-019). -/
@[kb "openstaxalgtrig2e" "§7.2, p. 701"]
theorem s7_2_triangle_45_45_90 {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) (hang : ∠ p₂ p₃ p₁ = π / 4) :
    dist p₁ p₂ = dist p₂ p₃ ∧ dist p₁ p₃ = √2 * dist p₂ p₃ :=
  UndergradKB.Trigonometry.right_triangle_pi_div_four h hang

/-- Sides of a 30-60-90 triangle are in ratio 1 : sqrt 3 : 2 (TR-019). -/
@[kb "openstaxalgtrig2e" "§7.2, p. 702"]
theorem s7_2_triangle_30_60_90 {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) (hang : ∠ p₂ p₃ p₁ = π / 6) :
    dist p₁ p₃ = 2 * dist p₁ p₂ ∧ dist p₂ p₃ = √3 * dist p₁ p₂ :=
  UndergradKB.Trigonometry.right_triangle_pi_div_six h hang

/-- Exact cosine of 15 degrees (TR-020). -/
@[kb "openstaxalgtrig2e" "§9.2, p. 824 (Ex 2)"]
theorem s9_2_cos_15_degrees :
    cos (π / 12) = (√6 + √2) / 4 :=
  UndergradKB.Trigonometry.cos_pi_div_twelve

/-- Exact tangent of 75 degrees (TR-020). -/
@[kb "openstaxalgtrig2e" "§9.2, p. 828 (Ex 5)"]
theorem s9_2_tan_75_degrees :
    tan (5 * π / 12) = (√6 + √2) / (√6 - √2) :=
  UndergradKB.Trigonometry.tan_five_pi_div_twelve

/-- Signs of sine, cosine and tangent in the four quadrants (TR-025). -/
@[kb "openstaxalgtrig2e" "§7.3, p. 722"]
theorem s7_3_quadrant_signs :
    (∀ θ : ℝ, 0 < θ → θ < π / 2 → 0 < sin θ ∧ 0 < cos θ ∧ 0 < tan θ) ∧ (∀ θ : ℝ, π / 2 < θ → θ < π → 0 < sin θ ∧ cos
      θ < 0 ∧ tan θ < 0) ∧ (∀ θ : ℝ, π < θ → θ < 3 * π / 2 → sin θ < 0 ∧ cos θ < 0 ∧ 0 < tan θ) ∧ ∀ θ : ℝ, 3 * π / 2
      < θ → θ < 2 * π → sin θ < 0 ∧ 0 < cos θ ∧ tan θ < 0 :=
  ⟨fun _ h₁ h₂ => UndergradKB.Trigonometry.quadrant_one_signs h₁ h₂, fun _ h₁ h₂ =>
    UndergradKB.Trigonometry.quadrant_two_signs h₁ h₂, fun _ h₁ h₂ => UndergradKB.Trigonometry.quadrant_three_signs
    h₁ h₂, fun _ h₁ h₂ => UndergradKB.Trigonometry.quadrant_four_signs h₁ h₂⟩

/-- Signs of sine, cosine and tangent in the four quadrants (TR-025). -/
@[kb "openstaxalgtrig2e" "§7.4, p. 732"]
theorem s7_4_quadrant_signs :
    (∀ θ : ℝ, 0 < θ → θ < π / 2 → 0 < sin θ ∧ 0 < cos θ ∧ 0 < tan θ) ∧ (∀ θ : ℝ, π / 2 < θ → θ < π → 0 < sin θ ∧ cos
      θ < 0 ∧ tan θ < 0) ∧ (∀ θ : ℝ, π < θ → θ < 3 * π / 2 → sin θ < 0 ∧ cos θ < 0 ∧ 0 < tan θ) ∧ ∀ θ : ℝ, 3 * π / 2
      < θ → θ < 2 * π → sin θ < 0 ∧ 0 < cos θ ∧ tan θ < 0 :=
  ⟨fun _ h₁ h₂ => UndergradKB.Trigonometry.quadrant_one_signs h₁ h₂, fun _ h₁ h₂ =>
    UndergradKB.Trigonometry.quadrant_two_signs h₁ h₂, fun _ h₁ h₂ => UndergradKB.Trigonometry.quadrant_three_signs
    h₁ h₂, fun _ h₁ h₂ => UndergradKB.Trigonometry.quadrant_four_signs h₁ h₂⟩

/-- Signs of sine, cosine and tangent in the four quadrants (TR-025). -/
@[kb "openstaxalgtrig2e" "§8.1, p. 752"]
theorem s8_1_quadrant_signs :
    (∀ θ : ℝ, 0 < θ → θ < π / 2 → 0 < sin θ ∧ 0 < cos θ ∧ 0 < tan θ) ∧ (∀ θ : ℝ, π / 2 < θ → θ < π → 0 < sin θ ∧ cos
      θ < 0 ∧ tan θ < 0) ∧ (∀ θ : ℝ, π < θ → θ < 3 * π / 2 → sin θ < 0 ∧ cos θ < 0 ∧ 0 < tan θ) ∧ ∀ θ : ℝ, 3 * π / 2
      < θ → θ < 2 * π → sin θ < 0 ∧ 0 < cos θ ∧ tan θ < 0 :=
  ⟨fun _ h₁ h₂ => UndergradKB.Trigonometry.quadrant_one_signs h₁ h₂, fun _ h₁ h₂ =>
    UndergradKB.Trigonometry.quadrant_two_signs h₁ h₂, fun _ h₁ h₂ => UndergradKB.Trigonometry.quadrant_three_signs
    h₁ h₂, fun _ h₁ h₂ => UndergradKB.Trigonometry.quadrant_four_signs h₁ h₂⟩

/-- Sine and cosine at the multiples of 30 and 45 degrees in quadrants II to IV (TR-027). -/
@[kb "openstaxalgtrig2e" "§7.3, p. 724"]
theorem s7_3_values_beyond_first_quadrant :
    ((sin (2 * π / 3) = √3 / 2 ∧ cos (2 * π / 3) = -(1 / 2)) ∧ (sin (3 * π / 4) = √2 / 2 ∧ cos (3 * π / 4) = -(√2 /
      2)) ∧ (sin (5 * π / 6) = 1 / 2 ∧ cos (5 * π / 6) = -(√3 / 2))) ∧ ((sin (7 * π / 6) = -(1 / 2) ∧ cos (7 * π /
      6) = -(√3 / 2)) ∧ (sin (5 * π / 4) = -(√2 / 2) ∧ cos (5 * π / 4) = -(√2 / 2)) ∧ (sin (4 * π / 3) = -(√3 / 2) ∧
      cos (4 * π / 3) = -(1 / 2))) ∧ ((sin (5 * π / 3) = -(√3 / 2) ∧ cos (5 * π / 3) = 1 / 2) ∧ (sin (7 * π / 4) =
      -(√2 / 2) ∧ cos (7 * π / 4) = √2 / 2) ∧ (sin (11 * π / 6) = -(1 / 2) ∧ cos (11 * π / 6) = √3 / 2)) :=
  ⟨UndergradKB.Trigonometry.sin_cos_second_quadrant, UndergradKB.Trigonometry.sin_cos_third_quadrant,
    UndergradKB.Trigonometry.sin_cos_fourth_quadrant⟩

/-- Reference angle of an angle in each quadrant (TR-029). -/
@[kb "openstaxalgtrig2e" "§7.1, p. 686"]
theorem s7_1_reference_angle :
    (∀ θ : ℝ, 0 ≤ θ → θ ≤ π / 2 → UndergradKB.Trigonometry.refAngle θ = θ) ∧ (∀ θ : ℝ, π / 2 < θ → θ ≤ π →
      UndergradKB.Trigonometry.refAngle θ = π - θ) ∧ (∀ θ : ℝ, π < θ → θ ≤ 3 * π / 2 →
      UndergradKB.Trigonometry.refAngle θ = θ - π) ∧ ∀ θ : ℝ, 3 * π / 2 < θ → UndergradKB.Trigonometry.refAngle θ =
      2 * π - θ :=
  ⟨fun θ _ h => by simp [UndergradKB.Trigonometry.refAngle, h],
    fun θ _ _ => by unfold UndergradKB.Trigonometry.refAngle; split_ifs <;>
      first | rfl | (exfalso; linarith [Real.pi_pos]),
    fun θ _ _ => by unfold UndergradKB.Trigonometry.refAngle; split_ifs <;>
      first | rfl | (exfalso; linarith [Real.pi_pos]),
    fun θ _ => by unfold UndergradKB.Trigonometry.refAngle; split_ifs <;>
      first | rfl | (exfalso; linarith [Real.pi_pos])⟩

/-- Reference angle of an angle in each quadrant (TR-029). -/
@[kb "openstaxalgtrig2e" "§7.3, p. 721"]
theorem s7_3_reference_angle :
    (∀ θ : ℝ, 0 ≤ θ → θ ≤ π / 2 → UndergradKB.Trigonometry.refAngle θ = θ) ∧ (∀ θ : ℝ, π / 2 < θ → θ ≤ π →
      UndergradKB.Trigonometry.refAngle θ = π - θ) ∧ (∀ θ : ℝ, π < θ → θ ≤ 3 * π / 2 →
      UndergradKB.Trigonometry.refAngle θ = θ - π) ∧ ∀ θ : ℝ, 3 * π / 2 < θ → UndergradKB.Trigonometry.refAngle θ =
      2 * π - θ :=
  ⟨fun θ _ h => by simp [UndergradKB.Trigonometry.refAngle, h],
    fun θ _ _ => by unfold UndergradKB.Trigonometry.refAngle; split_ifs <;>
      first | rfl | (exfalso; linarith [Real.pi_pos]),
    fun θ _ _ => by unfold UndergradKB.Trigonometry.refAngle; split_ifs <;>
      first | rfl | (exfalso; linarith [Real.pi_pos]),
    fun θ _ => by unfold UndergradKB.Trigonometry.refAngle; split_ifs <;>
      first | rfl | (exfalso; linarith [Real.pi_pos])⟩

/-- The reference angle of an angle in $[0, 2\pi)$ lies in $[0, \pi/2]$ (TR-040). -/
@[kb "openstaxalgtrig2e" "§7.3, p. 721"]
theorem s7_3_reference_angle_range {θ : ℝ} (h : θ ∈ Ico 0 (2 * π)) :
    UndergradKB.Trigonometry.refAngle θ ∈ Icc 0 (π / 2) :=
  UndergradKB.Trigonometry.refAngle_mem_Icc h

/-- Sine and cosine agree with those of the reference angle up to sign (TR-041). -/
@[kb "openstaxalgtrig2e" "Box §7.3, p. 722"]
theorem s7_3_reference_angle_values {θ : ℝ} (h : θ ∈ Ico 0 (2 * π)) :
    |sin θ| = sin (UndergradKB.Trigonometry.refAngle θ) ∧ |cos θ| = cos (UndergradKB.Trigonometry.refAngle θ) :=
  UndergradKB.Trigonometry.abs_sin_cos_eq_refAngle h

/-- Secant is even (TR-042). -/
@[kb "openstaxalgtrig2e" "Box §7.4, p. 734"]
theorem s7_4_sec_even (x : ℝ) :
    UndergradKB.Trigonometry.sec (-x) = UndergradKB.Trigonometry.sec x :=
  UndergradKB.Trigonometry.sec_neg x

/-- Secant is even (TR-042). -/
@[kb "openstaxalgtrig2e" "§8.2, p. 775"]
theorem s8_2_sec_even (x : ℝ) :
    UndergradKB.Trigonometry.sec (-x) = UndergradKB.Trigonometry.sec x :=
  UndergradKB.Trigonometry.sec_neg x

/-- Cosecant is odd (TR-042). -/
@[kb "openstaxalgtrig2e" "§8.2, p. 776"]
theorem s8_2_csc_odd (x : ℝ) :
    UndergradKB.Trigonometry.csc (-x) = - UndergradKB.Trigonometry.csc x :=
  UndergradKB.Trigonometry.csc_neg x

/-- Cotangent is odd (TR-042). -/
@[kb "openstaxalgtrig2e" "§8.2, p. 782"]
theorem s8_2_cot_odd (x : ℝ) :
    cot (-x) = - cot x :=
  UndergradKB.Trigonometry.cot_neg x

/-- Secant is even, cosecant and cotangent are odd (TR-043). -/
@[kb "openstaxalgtrig2e" "Box §9.1, p. 813"]
theorem s9_1_reciprocal_parity_p813 (x : ℝ) :
    UndergradKB.Trigonometry.sec (-x) = UndergradKB.Trigonometry.sec x ∧ UndergradKB.Trigonometry.csc (-x) = -
      UndergradKB.Trigonometry.csc x ∧ cot (-x) = - cot x :=
  ⟨UndergradKB.Trigonometry.sec_neg x, UndergradKB.Trigonometry.csc_neg x, UndergradKB.Trigonometry.cot_neg x⟩

/-- Secant is even, cosecant and cotangent are odd (TR-043). -/
@[kb "openstaxalgtrig2e" "Box §9.1, p. 815"]
theorem s9_1_reciprocal_parity_p815 (x : ℝ) :
    UndergradKB.Trigonometry.sec (-x) = UndergradKB.Trigonometry.sec x ∧ UndergradKB.Trigonometry.csc (-x) = -
      UndergradKB.Trigonometry.csc x ∧ cot (-x) = - cot x :=
  ⟨UndergradKB.Trigonometry.sec_neg x, UndergradKB.Trigonometry.csc_neg x, UndergradKB.Trigonometry.cot_neg x⟩

/-- Reciprocal relations between the six trigonometric functions (TR-044). -/
@[kb "openstaxalgtrig2e" "§7.2, p. 700"]
theorem s7_2_reciprocal_definitions (x : ℝ) :
    UndergradKB.Trigonometry.sec x = 1 / cos x ∧ UndergradKB.Trigonometry.csc x = 1 / sin x ∧ cot x = 1 / tan x ∧
      cos x = 1 / UndergradKB.Trigonometry.sec x ∧ sin x = 1 / UndergradKB.Trigonometry.csc x ∧ tan x = 1 / cot x :=
  ⟨UndergradKB.Trigonometry.sec_eq_one_div_cos x, UndergradKB.Trigonometry.csc_eq_one_div_sin x,
    UndergradKB.Trigonometry.cot_eq_one_div_tan x, UndergradKB.Trigonometry.cos_eq_one_div_sec x,
    UndergradKB.Trigonometry.sin_eq_one_div_csc x, UndergradKB.Trigonometry.tan_eq_one_div_cot x⟩

/-- Reciprocal relations between the six trigonometric functions (TR-044). -/
@[kb "openstaxalgtrig2e" "§9.1, p. 814 (Table 3)"]
theorem s9_1_reciprocal_definitions (x : ℝ) :
    UndergradKB.Trigonometry.sec x = 1 / cos x ∧ UndergradKB.Trigonometry.csc x = 1 / sin x ∧ cot x = 1 / tan x ∧
      cos x = 1 / UndergradKB.Trigonometry.sec x ∧ sin x = 1 / UndergradKB.Trigonometry.csc x ∧ tan x = 1 / cot x :=
  ⟨UndergradKB.Trigonometry.sec_eq_one_div_cos x, UndergradKB.Trigonometry.csc_eq_one_div_sin x,
    UndergradKB.Trigonometry.cot_eq_one_div_tan x, UndergradKB.Trigonometry.cos_eq_one_div_sec x,
    UndergradKB.Trigonometry.sin_eq_one_div_csc x, UndergradKB.Trigonometry.tan_eq_one_div_cot x⟩

/-- Cofunction identities for secant, cosecant and cotangent (TR-045). -/
@[kb "openstaxalgtrig2e" "§7.2, p. 703"]
theorem s7_2_cofunctions_reciprocal (x : ℝ) :
    UndergradKB.Trigonometry.sec (π / 2 - x) = UndergradKB.Trigonometry.csc x ∧ UndergradKB.Trigonometry.csc (π / 2
      - x) = UndergradKB.Trigonometry.sec x ∧ cot (π / 2 - x) = tan x :=
  ⟨UndergradKB.Trigonometry.sec_pi_div_two_sub x, UndergradKB.Trigonometry.csc_pi_div_two_sub x,
    UndergradKB.Trigonometry.cot_pi_div_two_sub x⟩

/-- Cofunction identities for secant, cosecant and cotangent (TR-045). -/
@[kb "openstaxalgtrig2e" "§9.2, p. 831 (Fig 6)"]
theorem s9_2_cofunctions_reciprocal (x : ℝ) :
    UndergradKB.Trigonometry.sec (π / 2 - x) = UndergradKB.Trigonometry.csc x ∧ UndergradKB.Trigonometry.csc (π / 2
      - x) = UndergradKB.Trigonometry.sec x ∧ cot (π / 2 - x) = tan x :=
  ⟨UndergradKB.Trigonometry.sec_pi_div_two_sub x, UndergradKB.Trigonometry.csc_pi_div_two_sub x,
    UndergradKB.Trigonometry.cot_pi_div_two_sub x⟩

/-- Products of the reciprocal pairs equal one wherever defined (TR-047). -/
@[kb "openstaxalgtrig2e" "§7.4, p. 729"]
theorem s7_4_reciprocal_products_p729 (x : ℝ) (hs : sin x ≠ 0) (hc : cos x ≠ 0) :
    cos x * UndergradKB.Trigonometry.sec x = 1 ∧ sin x * UndergradKB.Trigonometry.csc x = 1 ∧ tan x * cot x = 1 :=
  ⟨UndergradKB.Trigonometry.cos_mul_sec x hc, UndergradKB.Trigonometry.sin_mul_csc x hs,
    UndergradKB.Trigonometry.tan_mul_cot x hs hc⟩

/-- Products of the reciprocal pairs equal one wherever defined (TR-047). -/
@[kb "openstaxalgtrig2e" "§7.4, p. 734"]
theorem s7_4_reciprocal_products_p734 (x : ℝ) (hs : sin x ≠ 0) (hc : cos x ≠ 0) :
    cos x * UndergradKB.Trigonometry.sec x = 1 ∧ sin x * UndergradKB.Trigonometry.csc x = 1 ∧ tan x * cot x = 1 :=
  ⟨UndergradKB.Trigonometry.cos_mul_sec x hc, UndergradKB.Trigonometry.sin_mul_csc x hs,
    UndergradKB.Trigonometry.tan_mul_cot x hs hc⟩

/-- Products of the reciprocal pairs equal one wherever defined (TR-047). -/
@[kb "openstaxalgtrig2e" "§9.1, p. 814 (Table 3)"]
theorem s9_1_reciprocal_products (x : ℝ) (hs : sin x ≠ 0) (hc : cos x ≠ 0) :
    cos x * UndergradKB.Trigonometry.sec x = 1 ∧ sin x * UndergradKB.Trigonometry.csc x = 1 ∧ tan x * cot x = 1 :=
  ⟨UndergradKB.Trigonometry.cos_mul_sec x hc, UndergradKB.Trigonometry.sin_mul_csc x hs,
    UndergradKB.Trigonometry.tan_mul_cot x hs hc⟩

/-- One plus tangent squared is secant squared (TR-053). -/
@[kb "openstaxalgtrig2e" "§7.4, p. 736"]
theorem s7_4_one_add_tan_sq (x : ℝ) (h : cos x ≠ 0) :
    1 + tan x ^ 2 = UndergradKB.Trigonometry.sec x ^ 2 :=
  UndergradKB.Trigonometry.one_add_tan_sq_eq_sec_sq x h

/-- One plus tangent squared is secant squared (TR-053). -/
@[kb "openstaxalgtrig2e" "§9.1, p. 812 (Table 1; 1+tan^2=sec^2)"]
theorem s9_1_one_add_tan_sq (x : ℝ) (h : cos x ≠ 0) :
    1 + tan x ^ 2 = UndergradKB.Trigonometry.sec x ^ 2 :=
  UndergradKB.Trigonometry.one_add_tan_sq_eq_sec_sq x h

/-- Cotangent squared plus one is cosecant squared (TR-054). -/
@[kb "openstaxalgtrig2e" "§7.4, p. 736"]
theorem s7_4_cot_sq_add_one (x : ℝ) (h : sin x ≠ 0) :
    cot x ^ 2 + 1 = UndergradKB.Trigonometry.csc x ^ 2 :=
  UndergradKB.Trigonometry.cot_sq_add_one_eq_csc_sq x h

/-- Cotangent squared plus one is cosecant squared (TR-054). -/
@[kb "openstaxalgtrig2e" "§9.1, p. 812 (Table 1; 1+cot^2=csc^2)"]
theorem s9_1_cot_sq_add_one (x : ℝ) (h : sin x ≠ 0) :
    cot x ^ 2 + 1 = UndergradKB.Trigonometry.csc x ^ 2 :=
  UndergradKB.Trigonometry.cot_sq_add_one_eq_csc_sq x h

/-- Tangent of the angle between two lines of given slopes (TR-064). -/
@[kb "openstaxalgtrig2e" "Ex 10 §9.2, p. 833"]
theorem s9_2_angle_between_lines (m₁ m₂ : ℝ) :
    tan (arctan m₂ - arctan m₁) = (m₂ - m₁) / (1 + m₁ * m₂) ∧ |tan (arctan m₂ - arctan m₁)| = |(m₂ - m₁) / (1 + m₁ *
      m₂)| :=
  ⟨UndergradKB.Trigonometry.tan_arctan_sub_arctan m₁ m₂, UndergradKB.Trigonometry.abs_tan_arctan_sub_arctan m₁ m₂⟩

/-- Reduction formula for the square of the tangent (TR-069). -/
@[kb "openstaxalgtrig2e" "§9.3, p. 842 (reduction formula for tan^2)"]
theorem s9_3_tan_sq_reduction (t : ℝ) :
    tan t ^ 2 = (1 - cos (2 * t)) / (1 + cos (2 * t)) :=
  UndergradKB.Trigonometry.tan_sq_eq_one_sub_cos_two_mul_div t

/-- Half-angle formulas for the tangent (TR-071). -/
@[kb "openstaxalgtrig2e" "§9.3, p. 844"]
theorem s9_3_tan_half_angle (α : ℝ) :
    |tan (α / 2)| = √((1 - cos α) / (1 + cos α)) ∧ tan (α / 2) = sin α / (1 + cos α) ∧ tan (α / 2) = (1 - cos α) /
      sin α :=
  UndergradKB.Trigonometry.tan_half_formulas α

/-- Number of triangles in the ambiguous case SSA (TR-075). -/
@[kb "openstaxalgtrig2e" "§10.1, p. 883 (box)"]
theorem s10_1_ambiguous_case_count {a b A : ℝ} (h0 : 0 < a) (hb : 0 < b) (hA0 : 0 < A) (hA1 : A < π) :
    (A < π / 2 → (a < b * sin A → (UndergradKB.Trigonometry.ssaSolutions a b A).ncard = 0) ∧ (a = b * sin A →
      (UndergradKB.Trigonometry.ssaSolutions a b A).ncard = 1) ∧ (b * sin A < a → a < b →
      (UndergradKB.Trigonometry.ssaSolutions a b A).ncard = 2) ∧ (b ≤ a → (UndergradKB.Trigonometry.ssaSolutions a b
      A).ncard = 1)) ∧ (π / 2 ≤ A → (a ≤ b → (UndergradKB.Trigonometry.ssaSolutions a b A).ncard = 0) ∧ (b < a →
      (UndergradKB.Trigonometry.ssaSolutions a b A).ncard = 1)) :=
  UndergradKB.Trigonometry.ncard_ssaSolutions h0 hb hA0 hA1

/-- The two solutions of the ambiguous case with $b \sin A < a < b$ (TR-075). -/
@[kb "openstaxalgtrig2e" "§10.1, p. 883 (box)"]
theorem s10_1_ambiguous_case_two_solutions {a b A : ℝ} (h0 : 0 < a) (hb : 0 < b) (hA0 : 0 < A) (hA : A < π / 2) (h1
    : b * sin A < a) (h2 : a < b) :
    UndergradKB.Trigonometry.ssaSolutions a b A = {b * cos A - √(a ^ 2 - (b * sin A) ^ 2), b * cos A + √(a ^ 2 - (b
      * sin A) ^ 2)} :=
  UndergradKB.Trigonometry.ssaSolutions_acute_two h0 hb hA0 hA h1 h2

/-- The third side of a triangle is a solution of the SSA data (TR-075). -/
@[kb "openstaxalgtrig2e" "§10.1, p. 883 (box)"]
theorem s10_1_ambiguous_case_triangle_solution {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (t : Affine.Triangle ℝ P) :
    dist (t.points 0) (t.points 1) ∈ UndergradKB.Trigonometry.ssaSolutions (dist (t.points 1) (t.points 2)) (dist
      (t.points 0) (t.points 2)) (∠ (t.points 1) (t.points 0) (t.points 2)) :=
  UndergradKB.Trigonometry.dist_mem_ssaSolutions t

/-- SSA data may leave zero, one or two triangles (TR-078). -/
@[kb "openstaxalgtrig2e" "§10.1, p. 880"]
theorem s10_1_ssa_may_leave_several_triangles {a b A : ℝ} (h0 : 0 < a) (hb : 0 < b) (hA0 : 0 < A) (hA1 : A < π) :
    (A < π / 2 → (a < b * sin A → (UndergradKB.Trigonometry.ssaSolutions a b A).ncard = 0) ∧ (a = b * sin A →
      (UndergradKB.Trigonometry.ssaSolutions a b A).ncard = 1) ∧ (b * sin A < a → a < b →
      (UndergradKB.Trigonometry.ssaSolutions a b A).ncard = 2) ∧ (b ≤ a → (UndergradKB.Trigonometry.ssaSolutions a b
      A).ncard = 1)) ∧ (π / 2 ≤ A → (a ≤ b → (UndergradKB.Trigonometry.ssaSolutions a b A).ncard = 0) ∧ (b < a →
      (UndergradKB.Trigonometry.ssaSolutions a b A).ncard = 1)) :=
  UndergradKB.Trigonometry.ncard_ssaSolutions h0 hb hA0 hA1

/-- SSA data may leave zero, one or two triangles (TR-078). -/
@[kb "openstaxalgtrig2e" "§10.2, p. 887"]
theorem s10_2_ssa_may_leave_several_triangles {a b A : ℝ} (h0 : 0 < a) (hb : 0 < b) (hA0 : 0 < A) (hA1 : A < π) :
    (A < π / 2 → (a < b * sin A → (UndergradKB.Trigonometry.ssaSolutions a b A).ncard = 0) ∧ (a = b * sin A →
      (UndergradKB.Trigonometry.ssaSolutions a b A).ncard = 1) ∧ (b * sin A < a → a < b →
      (UndergradKB.Trigonometry.ssaSolutions a b A).ncard = 2) ∧ (b ≤ a → (UndergradKB.Trigonometry.ssaSolutions a b
      A).ncard = 1)) ∧ (π / 2 ≤ A → (a ≤ b → (UndergradKB.Trigonometry.ssaSolutions a b A).ncard = 0) ∧ (b < a →
      (UndergradKB.Trigonometry.ssaSolutions a b A).ncard = 1)) :=
  UndergradKB.Trigonometry.ncard_ssaSolutions h0 hb hA0 hA1

/-- Area is half the product of two sides and the sine of the included angle (TR-082). -/
@[kb "openstaxalgtrig2e" "§10.1, p. 887 (box)"]
theorem s10_1_area_half_bc_sin_a {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] (t : Affine.Triangle ℝ P) {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠
    i₃) :
    UndergradKB.Trigonometry.area t = 1 / 2 * dist (t.points i₁) (t.points i₂) * dist (t.points i₁) (t.points i₃) *
      sin (∠ (t.points i₂) (t.points i₁) (t.points i₃)) :=
  UndergradKB.Trigonometry.area_eq_half_mul_sin_included t h₁₂ h₁₃ h₂₃

/-- Area is half a side times the height on it (TR-082). -/
@[kb "openstaxalgtrig2e" "§10.1, p. 887 (box)"]
theorem s10_1_area_half_base_height {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] (t : Affine.Triangle ℝ P) {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠
    i₃) :
    UndergradKB.Trigonometry.area t = dist (t.points i₂) (t.points i₃) * t.height i₁ / 2 :=
  UndergradKB.Trigonometry.area_eq_dist_mul_height_div_two t h₁₂ h₁₃ h₂₃

/-- Heron's formula (TR-084). -/
@[kb "openstaxalgtrig2e" "§10.2, p. 903 (box)"]
theorem s10_2_heron {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V
    P] (t : Affine.Triangle ℝ P) {a b c s : ℝ} (ha : a = dist (t.points 1) (t.points 2)) (hb : b = dist (t.points 0)
    (t.points 2)) (hc : c = dist (t.points 0) (t.points 1)) (hs : s = (a + b + c) / 2) :
    UndergradKB.Trigonometry.area t = √(s * (s - a) * (s - b) * (s - c)) :=
  UndergradKB.Trigonometry.heron_openstax t ha hb hc hs

/-- Degrees and radians: 360 degrees is 2 pi radians (TR-099). -/
@[kb "openstaxalgtrig2e" "§7.1, p. 685"]
theorem s7_1_degrees_radians :
    UndergradKB.Trigonometry.degToRad 360 = 2 * π ∧ UndergradKB.Trigonometry.degToRad 180 = π ∧ (∀ x,
      UndergradKB.Trigonometry.radToDeg (UndergradKB.Trigonometry.degToRad x) = x) ∧ ∀ x,
      UndergradKB.Trigonometry.degToRad (UndergradKB.Trigonometry.radToDeg x) = x :=
  UndergradKB.Trigonometry.degToRad_spec

/-- Converting between degrees and radians by a proportion (TR-099). -/
@[kb "openstaxalgtrig2e" "§7.1, p. 685"]
theorem s7_1_degrees_radians_proportion (D R : ℝ) :
    UndergradKB.Trigonometry.degToRad D = R ↔ D / 180 = R / π :=
  UndergradKB.Trigonometry.degToRad_iff D R

/-- Radian measure of a central angle is arc length over radius (TR-100). -/
@[kb "openstaxalgtrig2e" "§7.1, p. 682"]
theorem s7_1_radian_measure (c : ℂ) {r θ : ℝ} (hr : 0 < r) (hθ : 0 ≤ θ) :
    (eVariationOn (fun φ : ℝ => c + r * Complex.exp (φ * Complex.I)) (Icc 0 θ)).toReal / r = θ :=
  UndergradKB.Trigonometry.radian_eq_arc_div_radius c hr hθ

/-- Length of a circular arc (TR-102). -/
@[kb "openstaxalgtrig2e" "§7.1, p. 682"]
theorem s7_1_arc_length_variation (c : ℂ) {r α β : ℝ} (hr : 0 ≤ r) (hαβ : α ≤ β) :
    eVariationOn (fun φ : ℝ => c + r * Complex.exp (φ * Complex.I)) (Icc α β) = ENNReal.ofReal (r * (β - α)) :=
  UndergradKB.Trigonometry.eVariationOn_arc c hr hαβ

/-- Arc length $s = r\theta$ (TR-102). -/
@[kb "openstaxalgtrig2e" "§7.1, p. 689"]
theorem s7_1_arc_length (c : ℂ) {r θ : ℝ} (hr : 0 ≤ r) (hθ : 0 ≤ θ) :
    (eVariationOn (fun φ : ℝ => c + r * Complex.exp (φ * Complex.I)) (Icc 0 θ)).toReal = r * θ :=
  UndergradKB.Trigonometry.arc_length' c hr hθ

/-- Arc length $s = r\theta$ (TR-102). -/
@[kb "openstaxalgtrig2e" "§7.3, p. 711"]
theorem s7_3_arc_length (c : ℂ) {r θ : ℝ} (hr : 0 ≤ r) (hθ : 0 ≤ θ) :
    eVariationOn (fun φ : ℝ => c + r * Complex.exp (φ * Complex.I)) (Icc 0 θ) = ENNReal.ofReal (r * θ) :=
  UndergradKB.Trigonometry.arc_length c hr hθ

/-- Area of a sector is $r^2\theta/2$ (TR-103). -/
@[kb "openstaxalgtrig2e" "§7.1, p. 690"]
theorem s7_1_sector_area {r θ : ℝ} (hr : 0 ≤ r) (hθ' : θ ≤ 2 * π) :
    MeasureTheory.volume (UndergradKB.Trigonometry.sector r θ) = ENNReal.ofReal (r ^ 2 * θ / 2) :=
  UndergradKB.Trigonometry.volume_sector hr hθ'

/-- Linear speed is angular speed times radius (TR-108). -/
@[kb "openstaxalgtrig2e" "§7.1, p. 692"]
theorem s7_1_linear_speed (c : ℂ) {r ω t : ℝ} (hr : 0 ≤ r) (hω : 0 ≤ ω) (ht : 0 ≤ t) :
    eVariationOn (fun τ : ℝ => c + r * Complex.exp ((ω * τ : ℝ) * Complex.I)) (Icc 0 t) = ENNReal.ofReal ((ω * r) *
      t) :=
  UndergradKB.Trigonometry.linear_speed c hr hω ht

/-- Circumference of a circle is $2\pi r$ (TR-111). -/
@[kb "openstaxalgtrig2e" "§7.1, p. 680"]
theorem s7_1_circumference (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    eVariationOn (fun φ : ℝ => c + r * Complex.exp (φ * Complex.I)) (Icc 0 (2 * π)) = ENNReal.ofReal (2 * π * r) :=
  UndergradKB.Trigonometry.circumference c hr

/-- The period of the sine is its least positive period (TR-121). -/
@[kb "openstaxalgtrig2e" "§7.4, p. 737"]
theorem s7_4_period_definition :
    IsLeast {p | 0 < p ∧ Function.Periodic sin p} (2 * π) :=
  UndergradKB.Trigonometry.isLeast_period_sin

/-- The period of the sine is its least positive period (TR-121). -/
@[kb "openstaxalgtrig2e" "§8.1, p. 752"]
theorem s8_1_period_definition :
    IsLeast {p | 0 < p ∧ Function.Periodic sin p} (2 * π) :=
  UndergradKB.Trigonometry.isLeast_period_sin

/-- Least periods of the six trigonometric functions (TR-122). -/
@[kb "openstaxalgtrig2e" "§7.4, p. 737"]
theorem s7_4_periods_of_the_six_functions :
    IsLeast {p | 0 < p ∧ Function.Periodic sin p} (2 * π) ∧ IsLeast {p | 0 < p ∧ Function.Periodic cos p} (2 * π) ∧
      IsLeast {p | 0 < p ∧ Function.Periodic tan p} (π) ∧ IsLeast {p | 0 < p ∧ Function.Periodic cot p} (π) ∧
      IsLeast {p | 0 < p ∧ Function.Periodic UndergradKB.Trigonometry.sec p} (2 * π) ∧ IsLeast {p | 0 < p ∧
      Function.Periodic UndergradKB.Trigonometry.csc p} (2 * π) :=
  ⟨UndergradKB.Trigonometry.isLeast_period_sin, UndergradKB.Trigonometry.isLeast_period_cos,
    UndergradKB.Trigonometry.isLeast_period_tan, UndergradKB.Trigonometry.isLeast_period_cot,
    UndergradKB.Trigonometry.isLeast_period_sec, UndergradKB.Trigonometry.isLeast_period_csc⟩

/-- Least periods of the six trigonometric functions (TR-122). -/
@[kb "openstaxalgtrig2e" "§8.1, p. 752"]
theorem s8_1_periods_of_the_six_functions :
    IsLeast {p | 0 < p ∧ Function.Periodic sin p} (2 * π) ∧ IsLeast {p | 0 < p ∧ Function.Periodic cos p} (2 * π) ∧
      IsLeast {p | 0 < p ∧ Function.Periodic tan p} (π) ∧ IsLeast {p | 0 < p ∧ Function.Periodic cot p} (π) ∧
      IsLeast {p | 0 < p ∧ Function.Periodic UndergradKB.Trigonometry.sec p} (2 * π) ∧ IsLeast {p | 0 < p ∧
      Function.Periodic UndergradKB.Trigonometry.csc p} (2 * π) :=
  ⟨UndergradKB.Trigonometry.isLeast_period_sin, UndergradKB.Trigonometry.isLeast_period_cos,
    UndergradKB.Trigonometry.isLeast_period_tan, UndergradKB.Trigonometry.isLeast_period_cot,
    UndergradKB.Trigonometry.isLeast_period_sec, UndergradKB.Trigonometry.isLeast_period_csc⟩

/-- The period of the tangent is pi (TR-122). -/
@[kb "openstaxalgtrig2e" "§8.2, p. 770"]
theorem s8_2_period_of_tangent :
    IsLeast {p | 0 < p ∧ Function.Periodic tan p} (π) :=
  UndergradKB.Trigonometry.isLeast_period_tan

/-- The periods of secant and cosecant are $2\pi$ (TR-122). -/
@[kb "openstaxalgtrig2e" "§8.2, p. 775"]
theorem s8_2_periods_of_secant_cosecant :
    IsLeast {p | 0 < p ∧ Function.Periodic UndergradKB.Trigonometry.sec p} (2 * π) ∧ IsLeast {p | 0 < p ∧
      Function.Periodic UndergradKB.Trigonometry.csc p} (2 * π) :=
  ⟨UndergradKB.Trigonometry.isLeast_period_sec, UndergradKB.Trigonometry.isLeast_period_csc⟩

/-- Phase shift of a sinusoid (TR-123). -/
@[kb "openstaxalgtrig2e" "§8.1, p. 756"]
theorem s8_1_phase_shift_p756 (A ω φ : ℝ) (hω : ω ≠ 0) (x : ℝ) :
    A * sin (ω * x - φ) = A * sin (ω * (x - φ / ω)) :=
  UndergradKB.Trigonometry.sinusoid_phase_shift A ω φ hω x

/-- Phase shift of a sinusoid (TR-123). -/
@[kb "openstaxalgtrig2e" "§8.1, p. 757"]
theorem s8_1_phase_shift_p757 (A ω φ : ℝ) (hω : ω ≠ 0) (x : ℝ) :
    A * sin (ω * x - φ) = A * sin (ω * (x - φ / ω)) :=
  UndergradKB.Trigonometry.sinusoid_phase_shift A ω φ hω x

/-- Phase shift of a sinusoid (TR-123). -/
@[kb "openstaxalgtrig2e" "§8.2, p. 773"]
theorem s8_2_phase_shift (A ω φ : ℝ) (hω : ω ≠ 0) (x : ℝ) :
    A * sin (ω * x - φ) = A * sin (ω * (x - φ / ω)) :=
  UndergradKB.Trigonometry.sinusoid_phase_shift A ω φ hω x

/-- Periods of $\sin\omega x$, $\cos\omega x$, $\tan\omega x$ (TR-124). -/
@[kb "openstaxalgtrig2e" "§8.1, p. 754"]
theorem s8_1_period_of_scaled_functions {ω : ℝ} (hω : 0 < ω) :
    IsLeast {p | 0 < p ∧ Function.Periodic (fun x => sin (ω * x)) p} (2 * π / ω) ∧ IsLeast {p | 0 < p ∧
      Function.Periodic (fun x => cos (ω * x)) p} (2 * π / ω) ∧ IsLeast {p | 0 < p ∧ Function.Periodic (fun x => tan
      (ω * x)) p} (π / ω) :=
  ⟨UndergradKB.Trigonometry.isLeast_period_sin_mul hω, UndergradKB.Trigonometry.isLeast_period_cos_mul hω,
    UndergradKB.Trigonometry.isLeast_period_tan_mul hω⟩

/-- Periods of $\sin\omega x$, $\cos\omega x$, $\tan\omega x$ (TR-124). -/
@[kb "openstaxalgtrig2e" "§8.2, p. 771"]
theorem s8_2_period_of_scaled_functions {ω : ℝ} (hω : 0 < ω) :
    IsLeast {p | 0 < p ∧ Function.Periodic (fun x => sin (ω * x)) p} (2 * π / ω) ∧ IsLeast {p | 0 < p ∧
      Function.Periodic (fun x => cos (ω * x)) p} (2 * π / ω) ∧ IsLeast {p | 0 < p ∧ Function.Periodic (fun x => tan
      (ω * x)) p} (π / ω) :=
  ⟨UndergradKB.Trigonometry.isLeast_period_sin_mul hω, UndergradKB.Trigonometry.isLeast_period_cos_mul hω,
    UndergradKB.Trigonometry.isLeast_period_tan_mul hω⟩

/-- Amplitude, period and phase shift of a general sinusoid (TR-126). -/
@[kb "openstaxalgtrig2e" "§8.1, p. 757 (general sinusoid)"]
theorem s8_1_amplitude_period_phase (A B C D : ℝ) (hB : 0 < B) :
    UndergradKB.Trigonometry.amplitude (fun x => A * sin (B * x - C) + D) = |A| ∧ IsLeast {p | 0 < p ∧
      Function.Periodic (fun x => sin (B * x)) p} (2 * π / B) ∧ ∀ x, A * sin (B * x - C) = A * sin (B * (x - C / B))
      :=
  ⟨UndergradKB.Trigonometry.amplitude_sinusoid A B C D hB.ne', UndergradKB.Trigonometry.isLeast_period_sin_mul hB,
    fun x => UndergradKB.Trigonometry.sinusoid_phase_shift A B C hB.ne' x⟩

/-- Amplitude, period and phase shift of a general sinusoid (TR-126). -/
@[kb "openstaxalgtrig2e" "§8.2, p. 773 (general sinusoid)"]
theorem s8_2_amplitude_period_phase (A B C D : ℝ) (hB : 0 < B) :
    UndergradKB.Trigonometry.amplitude (fun x => A * sin (B * x - C) + D) = |A| ∧ IsLeast {p | 0 < p ∧
      Function.Periodic (fun x => sin (B * x)) p} (2 * π / B) ∧ ∀ x, A * sin (B * x - C) = A * sin (B * (x - C / B))
      :=
  ⟨UndergradKB.Trigonometry.amplitude_sinusoid A B C D hB.ne', UndergradKB.Trigonometry.isLeast_period_sin_mul hB,
    fun x => UndergradKB.Trigonometry.sinusoid_phase_shift A B C hB.ne' x⟩

/-- Amplitude of a sinusoid is the absolute value of its coefficient (TR-127). -/
@[kb "openstaxalgtrig2e" "§8.1, p. 755"]
theorem s8_1_amplitude (A B C D : ℝ) (hB : B ≠ 0) :
    UndergradKB.Trigonometry.amplitude (fun x => A * sin (B * x - C) + D) = |A| ∧ range (fun x => A * sin (B * x -
      C) + D) = Icc (D - |A|) (D + |A|) :=
  ⟨UndergradKB.Trigonometry.amplitude_sinusoid A B C D hB, UndergradKB.Trigonometry.range_sinusoid A B C D hB⟩

/-- Range and midline of a general sinusoid (TR-128). -/
@[kb "openstaxalgtrig2e" "Box §8.1, p. 757"]
theorem s8_1_midline_range (A B C D : ℝ) (hB : B ≠ 0) :
    range (fun x => A * sin (B * x - C) + D) = Icc (D - |A|) (D + |A|) ∧ UndergradKB.Trigonometry.midline (fun x =>
      A * sin (B * x - C) + D) = D :=
  ⟨UndergradKB.Trigonometry.range_sinusoid A B C D hB, UndergradKB.Trigonometry.midline_sinusoid A B C D hB⟩

/-- Range and midline of a general sinusoid (TR-128). -/
@[kb "openstaxalgtrig2e" "Box §8.1, p. 758"]
theorem s8_1_midline_range_p758 (A B C D : ℝ) (hB : B ≠ 0) :
    range (fun x => A * sin (B * x - C) + D) = Icc (D - |A|) (D + |A|) ∧ UndergradKB.Trigonometry.midline (fun x =>
      A * sin (B * x - C) + D) = D :=
  ⟨UndergradKB.Trigonometry.range_sinusoid A B C D hB, UndergradKB.Trigonometry.midline_sinusoid A B C D hB⟩

/-- Range and period of a transformed tangent (TR-130). -/
@[kb "openstaxalgtrig2e" "Box §8.2, p. 771"]
theorem s8_2_tan_range_period (A B C D : ℝ) (hA : A ≠ 0) (hB : 0 < B) :
    range (fun x => A * tan (B * x - C) + D) = univ ∧ IsLeast {p | 0 < p ∧ Function.Periodic (fun x => tan (B * x))
      p} (π / B) :=
  ⟨UndergradKB.Trigonometry.range_tan_transformed A B C D hA hB.ne', UndergradKB.Trigonometry.isLeast_period_tan_mul
    hB⟩

/-- Range and period of a transformed tangent (TR-130). -/
@[kb "openstaxalgtrig2e" "Box §8.2, p. 773"]
theorem s8_2_tan_range_period_p773 (A B C D : ℝ) (hA : A ≠ 0) (hB : 0 < B) :
    range (fun x => A * tan (B * x - C) + D) = univ ∧ IsLeast {p | 0 < p ∧ Function.Periodic (fun x => tan (B * x))
      p} (π / B) :=
  ⟨UndergradKB.Trigonometry.range_tan_transformed A B C D hA hB.ne', UndergradKB.Trigonometry.isLeast_period_tan_mul
    hB⟩

/-- Range, domain and period of the secant (TR-131). -/
@[kb "openstaxalgtrig2e" "Box §8.2, p. 775"]
theorem s8_2_secant_properties (x : ℝ) (hc : cos x ≠ 0) :
    1 ≤ |UndergradKB.Trigonometry.sec x| ∧ (UndergradKB.Trigonometry.sec x = 0 ↔ cos x = 0) ∧ IsLeast {p | 0 < p ∧
      Function.Periodic UndergradKB.Trigonometry.sec p} (2 * π) :=
  ⟨UndergradKB.Trigonometry.one_le_abs_sec x hc, UndergradKB.Trigonometry.sec_eq_zero_iff x,
    UndergradKB.Trigonometry.isLeast_period_sec⟩

/-- Range, domain and period of the cosecant (TR-131). -/
@[kb "openstaxalgtrig2e" "Box §8.2, p. 776"]
theorem s8_2_cosecant_properties (x : ℝ) (hs : sin x ≠ 0) :
    1 ≤ |UndergradKB.Trigonometry.csc x| ∧ (UndergradKB.Trigonometry.csc x = 0 ↔ sin x = 0) ∧ IsLeast {p | 0 < p ∧
      Function.Periodic UndergradKB.Trigonometry.csc p} (2 * π) :=
  ⟨UndergradKB.Trigonometry.one_le_abs_csc x hs, UndergradKB.Trigonometry.csc_eq_zero_iff x,
    UndergradKB.Trigonometry.isLeast_period_csc⟩

/-- Periods of secant and cosecant (TR-131). -/
@[kb "openstaxalgtrig2e" "Box §8.2, p. 777"]
theorem s8_2_secant_cosecant_periods :
    IsLeast {p | 0 < p ∧ Function.Periodic UndergradKB.Trigonometry.sec p} (2 * π) ∧ IsLeast {p | 0 < p ∧
      Function.Periodic UndergradKB.Trigonometry.csc p} (2 * π) :=
  ⟨UndergradKB.Trigonometry.isLeast_period_sec, UndergradKB.Trigonometry.isLeast_period_csc⟩

/-- Properties of the cotangent (TR-132). -/
@[kb "openstaxalgtrig2e" "Box §8.2, p. 782"]
theorem s8_2_cotangent_properties (x : ℝ) :
    StrictAntiOn cot (Ioo 0 π) ∧ cot (x + π) = cot x ∧ cot (-x) = - cot x ∧ IsLeast {p | 0 < p ∧ Function.Periodic
      cot p} (π) :=
  ⟨UndergradKB.Trigonometry.cot_strictAntiOn, UndergradKB.Trigonometry.cot_add_pi x,
    UndergradKB.Trigonometry.cot_neg x, UndergradKB.Trigonometry.isLeast_period_cot⟩

/-- Properties of the cotangent (TR-132). -/
@[kb "openstaxalgtrig2e" "Box §8.2, p. 783"]
theorem s8_2_cotangent_properties_p783 (x : ℝ) :
    StrictAntiOn cot (Ioo 0 π) ∧ cot (x + π) = cot x ∧ cot (-x) = - cot x ∧ IsLeast {p | 0 < p ∧ Function.Periodic
      cot p} (π) :=
  ⟨UndergradKB.Trigonometry.cot_strictAntiOn, UndergradKB.Trigonometry.cot_add_pi x,
    UndergradKB.Trigonometry.cot_neg x, UndergradKB.Trigonometry.isLeast_period_cot⟩

/-- Symmetry test about the line $\theta = \pi/2$ (TR-133). -/
@[kb "openstaxalgtrig2e" "§10.4, p. 925-926 (box and Fig 2)"]
theorem s10_4_symmetry_about_line_pi_div_two {F : ℝ → ℝ → Prop} (h : (∀ r θ, F r θ → F (-r) (-θ)) ∨ ∀ r θ, F r θ → F
    r (π - θ)) :
    ∀ z ∈ UndergradKB.Trigonometry.polarGraph F, -conj z ∈ UndergradKB.Trigonometry.polarGraph F :=
  UndergradKB.Trigonometry.polarGraph_symm_line_pi_div_two h

/-- Symmetry test about the polar axis (TR-134). -/
@[kb "openstaxalgtrig2e" "§10.4, p. 925-926 (box and Fig 2)"]
theorem s10_4_symmetry_about_polar_axis {F : ℝ → ℝ → Prop} (h : (∀ r θ, F r θ → F r (-θ)) ∨ ∀ r θ, F r θ → F (-r) (π
    - θ)) :
    ∀ z ∈ UndergradKB.Trigonometry.polarGraph F, conj z ∈ UndergradKB.Trigonometry.polarGraph F :=
  UndergradKB.Trigonometry.polarGraph_symm_polarAxis h

/-- Symmetry test about the pole (TR-135). -/
@[kb "openstaxalgtrig2e" "§10.4, p. 925-926 (box and Fig 2)"]
theorem s10_4_symmetry_about_pole {F : ℝ → ℝ → Prop} (h : ∀ r θ, F r θ → F (-r) θ) :
    ∀ z ∈ UndergradKB.Trigonometry.polarGraph F, -z ∈ UndergradKB.Trigonometry.polarGraph F :=
  UndergradKB.Trigonometry.polarGraph_symm_pole h

/-- The equations $r = a\cos\theta$ and $r = a\sin\theta$ are circles through the pole (TR-137). -/
@[kb "openstaxalgtrig2e" "§10.4, p. 929 (box)"]
theorem s10_4_circles_through_pole (a : ℝ) :
    UndergradKB.Trigonometry.polarGraph (fun r θ => r = a * cos θ) = Metric.sphere ((a / 2 : ℝ) : ℂ) (|a| / 2) ∧
      UndergradKB.Trigonometry.polarGraph (fun r θ => r = a * sin θ) = Metric.sphere ((a / 2 : ℝ) * Complex.I) (|a|
      / 2) :=
  ⟨UndergradKB.Trigonometry.polarGraph_cos_eq_sphere a, UndergradKB.Trigonometry.polarGraph_sin_eq_sphere a⟩

/-- Cardioids pass through the pole and are symmetric (TR-138). -/
@[kb "openstaxalgtrig2e" "§10.4, p. 930 (box; D129)"]
theorem s10_4_cardioids (a : ℝ) :
    ((0 : ℂ) ∈ UndergradKB.Trigonometry.polarGraph (fun r θ => r = a * (1 + cos θ)) ∧ ∀ z ∈
      UndergradKB.Trigonometry.polarGraph (fun r θ => r = a * (1 + cos θ)), conj z ∈
      UndergradKB.Trigonometry.polarGraph (fun r θ => r = a * (1 + cos θ))) ∧ ((0 : ℂ) ∈
      UndergradKB.Trigonometry.polarGraph (fun r θ => r = a * (1 + sin θ)) ∧ ∀ z ∈
      UndergradKB.Trigonometry.polarGraph (fun r θ => r = a * (1 + sin θ)), -conj z ∈
      UndergradKB.Trigonometry.polarGraph (fun r θ => r = a * (1 + sin θ))) :=
  ⟨UndergradKB.Trigonometry.cardioid_cos a, UndergradKB.Trigonometry.cardioid_sin a⟩

/-- A limacon with an inner loop passes through the pole twice (TR-140). -/
@[kb "openstaxalgtrig2e" "§10.4, p. 934 (box)"]
theorem s10_4_limacon_inner_loop {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    {θ | θ ∈ Ico 0 (2 * π) ∧ a + b * cos θ = 0} = {arccos (-a / b), 2 * π - arccos (-a / b)} ∧ {θ | θ ∈ Ico 0 (2 *
      π) ∧ a + b * cos θ = 0}.ncard = 2 :=
  UndergradKB.Trigonometry.limacon_inner_loop_pole ha hab

/-- Symmetries of the lemniscates (TR-141). -/
@[kb "openstaxalgtrig2e" "§10.4, p. 935 (box)"]
theorem s10_4_lemniscate_symmetries (a : ℝ) :
    (∀ z ∈ UndergradKB.Trigonometry.polarGraph (fun r θ => r ^ 2 = a ^ 2 * cos (2 * θ)), -z ∈
      UndergradKB.Trigonometry.polarGraph (fun r θ => r ^ 2 = a ^ 2 * cos (2 * θ)) ∧ conj z ∈
      UndergradKB.Trigonometry.polarGraph (fun r θ => r ^ 2 = a ^ 2 * cos (2 * θ)) ∧ -conj z ∈
      UndergradKB.Trigonometry.polarGraph (fun r θ => r ^ 2 = a ^ 2 * cos (2 * θ))) ∧ ∀ z ∈
      UndergradKB.Trigonometry.polarGraph (fun r θ => r ^ 2 = a ^ 2 * sin (2 * θ)), -z ∈
      UndergradKB.Trigonometry.polarGraph (fun r θ => r ^ 2 = a ^ 2 * sin (2 * θ)) :=
  UndergradKB.Trigonometry.lemniscate_symmetries a

/-- Exact values of the inverse sine, cosine and tangent (TR-160). -/
@[kb "openstaxalgtrig2e" "Ex. 2 §8.3, p. 794"]
theorem s8_3_inverse_special_values :
    (arcsin (1 / 2) = π / 6 ∧ arcsin (√2 / 2) = π / 4 ∧ arcsin (√3 / 2) = π / 3) ∧ (arccos (1 / 2) = π / 3 ∧ arccos
      (√2 / 2) = π / 4 ∧ arccos (√3 / 2) = π / 6 ∧ arccos (-(1 / 2)) = 2 * π / 3) ∧ (arctan 1 = π / 4 ∧ arctan (√3)
      = π / 3 ∧ arctan (1 / √3) = π / 6) :=
  ⟨UndergradKB.Trigonometry.arcsin_special_values, UndergradKB.Trigonometry.arccos_special_values,
    UndergradKB.Trigonometry.arctan_special_values⟩

/-- $\arcsin(\cos t)$ and $\arccos(\sin t)$ (TR-162). -/
@[kb "openstaxalgtrig2e" "Box §8.3, p. 797"]
theorem s8_3_inverse_cofunction_compositions :
    (∀ t : ℝ, 0 ≤ t → t ≤ π → arcsin (cos t) = π / 2 - t) ∧ ∀ t : ℝ, -(π / 2) ≤ t → t ≤ π / 2 → arccos (sin t) = π /
      2 - t :=
  ⟨fun _ h₀ h₁ => UndergradKB.Trigonometry.arcsin_cos h₀ h₁, fun _ h₀ h₁ => UndergradKB.Trigonometry.arccos_sin h₀
    h₁⟩

/-- Adding multiples of the period to a solution gives solutions (TR-165). -/
@[kb "openstaxalgtrig2e" "§9.5, p. 857"]
theorem s9_5_general_solution {f : ℝ → ℝ} {p a x : ℝ} (hf : Function.Periodic f p) (hx : f x = a) (k : ℤ) :
    f (x + k * p) = a :=
  UndergradKB.Trigonometry.periodic_solutions hf hx k

/-- General solution of $\sin x = a$ (TR-172). -/
@[kb "openstaxalgtrig2e" "Box §9.5, p. 857"]
theorem s9_5_sin_eq_a {a x : ℝ} (ha₁ : -1 ≤ a) (ha₂ : a ≤ 1) :
    sin x = a ↔ ∃ k : ℤ, x = arcsin a + 2 * k * π ∨ x = π - arcsin a + 2 * k * π :=
  UndergradKB.Trigonometry.sin_eq_iff ha₁ ha₂

/-- General solution of $\sin x = a$ (TR-172). -/
@[kb "openstaxalgtrig2e" "Ex 8 §9.5, p. 860"]
theorem s9_5_sin_eq_a_ex8 {a x : ℝ} (ha₁ : -1 ≤ a) (ha₂ : a ≤ 1) :
    sin x = a ↔ ∃ k : ℤ, x = arcsin a + 2 * k * π ∨ x = π - arcsin a + 2 * k * π :=
  UndergradKB.Trigonometry.sin_eq_iff ha₁ ha₂

/-- General solution of $\cos x = a$ (TR-173). -/
@[kb "openstaxalgtrig2e" "Box §9.5, p. 857"]
theorem s9_5_cos_eq_a {a x : ℝ} (ha₁ : -1 ≤ a) (ha₂ : a ≤ 1) :
    cos x = a ↔ ∃ k : ℤ, x = arccos a + 2 * k * π ∨ x = -arccos a + 2 * k * π :=
  UndergradKB.Trigonometry.cos_eq_iff ha₁ ha₂

/-- General solution of $\cos x = a$ (TR-173). -/
@[kb "openstaxalgtrig2e" "Ex 9 §9.5, p. 861"]
theorem s9_5_cos_eq_a_ex9 {a x : ℝ} (ha₁ : -1 ≤ a) (ha₂ : a ≤ 1) :
    cos x = a ↔ ∃ k : ℤ, x = arccos a + 2 * k * π ∨ x = -arccos a + 2 * k * π :=
  UndergradKB.Trigonometry.cos_eq_iff ha₁ ha₂

/-- General solution of $\tan x = a$ (TR-174). -/
@[kb "openstaxalgtrig2e" "Box §9.5, p. 858"]
theorem s9_5_tan_eq_a {a x : ℝ} (hc : cos x ≠ 0) :
    tan x = a ↔ ∃ k : ℤ, x = arctan a + k * π :=
  UndergradKB.Trigonometry.tan_eq_iff hc

/-- General solution of $\tan x = a$ (TR-174). -/
@[kb "openstaxalgtrig2e" "Ex 6 §9.5, p. 859"]
theorem s9_5_tan_eq_a_ex6 {a x : ℝ} (hc : cos x ≠ 0) :
    tan x = a ↔ ∃ k : ℤ, x = arctan a + k * π :=
  UndergradKB.Trigonometry.tan_eq_iff hc

/-- Equations with a multiple angle (TR-175). -/
@[kb "openstaxalgtrig2e" "Box §9.5, p. 867"]
theorem s9_5_multiple_angle (f : ℝ → ℝ) (a : ℝ) {k : ℝ} (hk : 0 < k) :
    {x | x ∈ Ico 0 (2 * π) ∧ f (k * x) = a} = (fun u => u / k) '' {u | u ∈ Ico 0 (2 * k * π) ∧ f u = a} :=
  UndergradKB.Trigonometry.solutions_mul_angle f a hk

/-- Equations with a multiple angle (TR-175). -/
@[kb "openstaxalgtrig2e" "Ex 17 §9.5, p. 866"]
theorem s9_5_multiple_angle_ex17 (f : ℝ → ℝ) (a : ℝ) {k : ℝ} (hk : 0 < k) :
    {x | x ∈ Ico 0 (2 * π) ∧ f (k * x) = a} = (fun u => u / k) '' {u | u ∈ Ico 0 (2 * k * π) ∧ f u = a} :=
  UndergradKB.Trigonometry.solutions_mul_angle f a hk

/-- Moduli multiply and arguments add (TR-188). -/
@[kb "openstaxalgtrig2e" "§10.5, p. 950 (box)"]
theorem s10_5_polar_product (r₁ r₂ α β : ℝ) :
    (r₁ * (Real.cos α + Real.sin α * Complex.I)) * (r₂ * (Real.cos β + Real.sin β * Complex.I)) = (r₁ * r₂ : ℝ) *
      (Real.cos (α + β) + Real.sin (α + β) * Complex.I) :=
  UndergradKB.Trigonometry.cis_mul_cis r₁ r₂ α β

/-- Moduli divide and arguments subtract (TR-189). -/
@[kb "openstaxalgtrig2e" "§10.5, p. 950 (box)"]
theorem s10_5_polar_quotient (r₁ : ℝ) {r₂ : ℝ} (h : r₂ ≠ 0) (α β : ℝ) :
    (r₁ * (Real.cos α + Real.sin α * Complex.I)) / (r₂ * (Real.cos β + Real.sin β * Complex.I)) = (r₁ / r₂ : ℝ) *
      (Real.cos (α - β) + Real.sin (α - β) * Complex.I) :=
  UndergradKB.Trigonometry.cis_div_cis r₁ h α β

/-- De Moivre's theorem (TR-190). -/
@[kb "openstaxalgtrig2e" "§10.5, p. 951 (box)"]
theorem s10_5_de_moivre (r θ : ℝ) (n : ℕ) :
    (r * (Real.cos θ + Real.sin θ * Complex.I)) ^ n = (r ^ n : ℝ) * (Real.cos (n * θ) + Real.sin (n * θ) *
      Complex.I) :=
  UndergradKB.Trigonometry.de_moivre_nat r θ n

/-- De Moivre's theorem for integer exponents (TR-190). -/
@[kb "openstaxalgtrig2e" "§10.5, p. 951 (box)"]
theorem s10_5_de_moivre_integer (r θ : ℝ) (n : ℤ) :
    (r * (Real.cos θ + Real.sin θ * Complex.I)) ^ n = (r ^ n : ℝ) * (Real.cos (n * θ) + Real.sin (n * θ) *
      Complex.I) :=
  UndergradKB.Trigonometry.de_moivre r θ n

/-- The $n$th roots of a complex number in polar form (TR-191). -/
@[kb "openstaxalgtrig2e" "§10.5, p. 952 (box)"]
theorem s10_5_nth_roots {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    {z : ℂ | z ^ n = (r : ℂ) * ((Real.cos θ : ℝ) + (Real.sin θ : ℝ) * Complex.I)} = ↑((Finset.range n).image
      (UndergradKB.Trigonometry.nthRootPolar n r θ)) :=
  UndergradKB.Trigonometry.nthRoots_eq_image hn hr θ

/-- The candidate roots are roots and are distinct (TR-191). -/
@[kb "openstaxalgtrig2e" "§10.5, p. 952 (box)"]
theorem s10_5_nth_roots_distinct {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    (∀ k : ℕ, (UndergradKB.Trigonometry.nthRootPolar n r θ k) ^ n = (r : ℂ) * ((Real.cos θ : ℝ) + (Real.sin θ : ℝ) *
      Complex.I)) ∧ Set.InjOn (UndergradKB.Trigonometry.nthRootPolar n r θ) (Finset.range n : Set ℕ) :=
  ⟨fun k => UndergradKB.Trigonometry.nthRootPolar_pow hn hr θ k, UndergradKB.Trigonometry.nthRootPolar_injOn hn hr
    θ⟩

/-- Polar coordinates are not unique (TR-194). -/
@[kb "openstaxalgtrig2e" "§10.3, p. 911"]
theorem s10_3_polar_coordinates_not_unique (r θ : ℝ) (k : ℤ) :
    UndergradKB.Trigonometry.polarPoint r (θ + k * (2 * π)) = UndergradKB.Trigonometry.polarPoint r θ :=
  UndergradKB.Trigonometry.polarPoint_add_int_mul_two_pi r θ k

/-- Negative and zero radius in polar coordinates (TR-195). -/
@[kb "openstaxalgtrig2e" "§10.3, p. 913 (Ex 2)"]
theorem s10_3_negative_radius_ex2 (r θ : ℝ) :
    UndergradKB.Trigonometry.polarPoint (-r) θ = UndergradKB.Trigonometry.polarPoint r (θ + π) ∧
      UndergradKB.Trigonometry.polarPoint r (θ + 2 * π) = UndergradKB.Trigonometry.polarPoint r θ ∧
      UndergradKB.Trigonometry.polarPoint 0 θ = 0 :=
  ⟨UndergradKB.Trigonometry.polarPoint_neg_eq_add_pi r θ, UndergradKB.Trigonometry.polarPoint_add_two_pi r θ,
    UndergradKB.Trigonometry.polarPoint_zero_radius θ⟩

/-- Negative and zero radius in polar coordinates (TR-195). -/
@[kb "openstaxalgtrig2e" "§10.3, p. 917 (Ex 5 analysis)"]
theorem s10_3_negative_radius_ex5 (r θ : ℝ) :
    UndergradKB.Trigonometry.polarPoint (-r) θ = UndergradKB.Trigonometry.polarPoint r (θ + π) ∧
      UndergradKB.Trigonometry.polarPoint r (θ + 2 * π) = UndergradKB.Trigonometry.polarPoint r θ ∧
      UndergradKB.Trigonometry.polarPoint 0 θ = 0 :=
  ⟨UndergradKB.Trigonometry.polarPoint_neg_eq_add_pi r θ, UndergradKB.Trigonometry.polarPoint_add_two_pi r θ,
    UndergradKB.Trigonometry.polarPoint_zero_radius θ⟩

/-- Radius and tangent of the angle from rectangular coordinates (TR-197). -/
@[kb "openstaxalgtrig2e" "§10.3, p. 915 (box)"]
theorem s10_3_polar_to_rectangular_radius {r θ : ℝ} (hr : r ≠ 0) :
    (UndergradKB.Trigonometry.polarPoint r θ).re ^ 2 + (UndergradKB.Trigonometry.polarPoint r θ).im ^ 2 = r ^ 2 ∧
      tan θ = (UndergradKB.Trigonometry.polarPoint r θ).im / (UndergradKB.Trigonometry.polarPoint r θ).re :=
  ⟨UndergradKB.Trigonometry.polarPoint_sq_add_sq r θ, UndergradKB.Trigonometry.tan_eq_im_div_re hr⟩

/-- Polar equations $r = a\sec\theta$, $r = a\csc\theta$ are lines (TR-199). -/
@[kb "openstaxalgtrig2e" "§10.3, p. 920 (Ex 9 and remark)"]
theorem s10_3_horizontal_vertical_lines (f : ℝ → ℝ) {x y : ℝ} (hxy : x ≠ y) (hf : f x ≠ f y) :
    f x + (f x - f y) / (x - y) * (UndergradKB.Trigonometry.secantStep f x y - x) = 0 :=
  UndergradKB.Trigonometry.secantLine_secantStep f hxy hf

/-- Sine and cosine of complementary angles (TR-002). -/
@[kb "openstaxalgtrig2e" "§9.2, p. 831"]
theorem s9_2_complementary_cofunction {α β : ℝ} (h : AreComplementary α β) :
    sin β = cos α ∧ cos β = sin α :=
  UndergradKB.Trigonometry.sin_cos_of_complementary h

/-- An angle in standard position is a rotation of the initial side (TR-005). -/
@[kb "openstaxalgtrig2e" "§7.1, p. 676"]
theorem s7_1_standard_position_p676 (θ : ℝ) :
    Complex.exp (θ * Complex.I) * 1 = UndergradKB.Trigonometry.polarPoint 1 θ ∧ ((Complex.arg (Complex.exp (θ *
      Complex.I)) : ℝ) : Real.Angle) = (θ : Real.Angle) ∧ (∀ z : ℂ, z ≠ 0 → ((Complex.arg (Complex.exp (θ *
      Complex.I) * z) : ℝ) : Real.Angle) = (Complex.arg z : ℝ) + (θ : Real.Angle)) ∧ (0 < θ → θ < π → 0 <
      (Complex.exp (θ * Complex.I)).im) ∧ (-π < θ → θ < 0 → (Complex.exp (θ * Complex.I)).im < 0) :=
  UndergradKB.Trigonometry.standardPosition θ

/-- Counterclockwise rotation is positive, clockwise negative (TR-005). -/
@[kb "openstaxalgtrig2e" "§7.1, p. 677"]
theorem s7_1_standard_position_p677 (θ : ℝ) :
    Complex.exp (θ * Complex.I) * 1 = UndergradKB.Trigonometry.polarPoint 1 θ ∧ ((Complex.arg (Complex.exp (θ *
      Complex.I)) : ℝ) : Real.Angle) = (θ : Real.Angle) ∧ (∀ z : ℂ, z ≠ 0 → ((Complex.arg (Complex.exp (θ *
      Complex.I) * z) : ℝ) : Real.Angle) = (Complex.arg z : ℝ) + (θ : Real.Angle)) ∧ (0 < θ → θ < π → 0 <
      (Complex.exp (θ * Complex.I)).im) ∧ (-π < θ → θ < 0 → (Complex.exp (θ * Complex.I)).im < 0) :=
  UndergradKB.Trigonometry.standardPosition θ

/-- An angle is determined by its two sides (TR-008). -/
@[kb "openstaxalgtrig2e" "§7.1, p. 675"]
theorem s7_1_angle_determined_by_sides {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] {O A B A' B' : P} (hA : A' ∈ ray O A) (hA' : A' ≠ O) (hB : B' ∈ ray O B) (hB' : B' ≠ O) :
    ∠ A' O B' = ∠ A O B :=
  UndergradKB.Trigonometry.angle_eq_of_mem_ray hA hA' hB hB'

/-- One degree is 1/360 of a full rotation (TR-009). -/
@[kb "openstaxalgtrig2e" "§7.1, p. 676"]
theorem s7_1_degree_is_turn_div_360 :
    UndergradKB.Trigonometry.degToRad 1 = 2 * π / 360 ∧ ((UndergradKB.Trigonometry.degToRad 360 : ℝ) : Real.Angle) =
      0 ∧ ∀ x : ℝ, ((UndergradKB.Trigonometry.degToRad (x + 360) : ℝ) : Real.Angle) =
      ((UndergradKB.Trigonometry.degToRad x : ℝ) : Real.Angle) :=
  UndergradKB.Trigonometry.degToRad_one_eq_turn_div

/-- The hypotenuse is the longest side of a right triangle (TR-012). -/
@[kb "openstaxalgtrig2e" "§7.2, p. 698"]
theorem s7_2_hypotenuse_legs {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) (h12 : p₁ ≠ p₂) (h32 : p₃ ≠ p₂) :
    dist p₁ p₂ < dist p₁ p₃ ∧ dist p₃ p₂ < dist p₁ p₃ ∧ dist p₁ p₃ ^ 2 = dist p₁ p₂ ^ 2 + dist p₃ p₂ ^ 2 :=
  UndergradKB.Trigonometry.hypotenuse_longest h h12 h32

/-- Sine, cosine and tangent from the opposite and adjacent sides (TR-012). -/
@[kb "openstaxalgtrig2e" "§7.2, p. 699"]
theorem s7_2_opposite_adjacent_sides {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) (h12 : p₁ ≠ p₂) :
    sin (∠ p₂ p₃ p₁) = dist p₁ p₂ / dist p₁ p₃ ∧ cos (∠ p₂ p₃ p₁) = dist p₃ p₂ / dist p₁ p₃ ∧ tan (∠ p₂ p₃ p₁) =
      dist p₁ p₂ / dist p₃ p₂ :=
  UndergradKB.Trigonometry.ratios_opposite_adjacent h h12

/-- Angles of elevation and depression (TR-022). -/
@[kb "openstaxalgtrig2e" "§7.2, p. 705"]
theorem s7_2_elevation_depression {d h : ℝ} (hd : 0 < d) :
    UndergradKB.Trigonometry.elevationAngle d h = arctan (|h| / d) ∧ |h| = d * tan
      (UndergradKB.Trigonometry.elevationAngle d h) :=
  UndergradKB.Trigonometry.elevationAngle_eq_arctan hd

/-- The six functions from a point on the terminal side (TR-023). -/
@[kb "openstaxalgtrig2e" "§7.4, p. 729"]
theorem s7_4_functions_of_terminal_point {z : ℂ} (hz : z ≠ 0) :
    ‖z‖ = √(z.re ^ 2 + z.im ^ 2) ∧ sin (Complex.arg z) = z.im / ‖z‖ ∧ cos (Complex.arg z) = z.re / ‖z‖ ∧ tan
      (Complex.arg z) = z.im / z.re ∧ UndergradKB.Trigonometry.csc (Complex.arg z) = ‖z‖ / z.im ∧
      UndergradKB.Trigonometry.sec (Complex.arg z) = ‖z‖ / z.re ∧ cot (Complex.arg z) = z.re / z.im :=
  UndergradKB.Trigonometry.trig_of_point_arg hz

/-- The six functions at 0, 90, 180, 270 degrees (TR-026). -/
@[kb "openstaxalgtrig2e" "§7.3, p. 713"]
theorem s7_3_values_at_quadrantal_angles :
    (sin 0 = 0 ∧ cos 0 = 1 ∧ tan 0 = 0 ∧ UndergradKB.Trigonometry.sec 0 = 1) ∧ (sin (π / 2) = 1 ∧ cos (π / 2) = 0 ∧
      cot (π / 2) = 0 ∧ UndergradKB.Trigonometry.csc (π / 2) = 1) ∧ (sin π = 0 ∧ cos π = -1 ∧ tan π = 0 ∧
      UndergradKB.Trigonometry.sec π = -1) ∧ (sin (3 * π / 2) = -1 ∧ cos (3 * π / 2) = 0 ∧ cot (3 * π / 2) = 0 ∧
      UndergradKB.Trigonometry.csc (3 * π / 2) = -1) :=
  UndergradKB.Trigonometry.six_functions_quadrantal

/-- The undefined entries are unbounded near the angle (TR-026). -/
@[kb "openstaxalgtrig2e" "§7.4, p. 731"]
theorem s7_4_undefined_at_quadrantal_angles :
    (∀ x : ℝ, cos x = 0 → Filter.Tendsto (fun t => |tan t|) (nhdsWithin x {x}ᶜ) Filter.atTop ∧ Filter.Tendsto (fun t
      => |UndergradKB.Trigonometry.sec t|) (nhdsWithin x {x}ᶜ) Filter.atTop) ∧ (∀ x : ℝ, sin x = 0 → Filter.Tendsto
      (fun t => |cot t|) (nhdsWithin x {x}ᶜ) Filter.atTop ∧ Filter.Tendsto (fun t => |UndergradKB.Trigonometry.csc
      t|) (nhdsWithin x {x}ᶜ) Filter.atTop) :=
  ⟨fun _ hx => UndergradKB.Trigonometry.abs_tan_sec_tendsto_atTop hx, fun _ hx =>
    UndergradKB.Trigonometry.abs_cot_csc_tendsto_atTop hx⟩

/-- A point of the unit circle at angle t is (cos t, sin t) (TR-036). -/
@[kb "openstaxalgtrig2e" "§7.3, p. 712"]
theorem s7_3_unit_circle_point {t : ℝ} (ht : 0 ≤ t) :
    eVariationOn (fun φ : ℝ => Complex.exp (φ * Complex.I)) (Icc 0 t) = ENNReal.ofReal t ∧ Complex.exp (t *
      Complex.I) = ⟨cos t, sin t⟩ ∧ ‖Complex.exp (t * Complex.I)‖ = 1 :=
  UndergradKB.Trigonometry.unitCircle_arc_point ht

/-- Quadrantal angles (TR-037). -/
@[kb "openstaxalgtrig2e" "Box §7.1, p. 678"]
theorem s7_1_quadrantal_angles (θ : ℝ) :
    (UndergradKB.Trigonometry.IsQuadrantal θ ↔ sin θ = 0 ∨ cos θ = 0) ∧ (UndergradKB.Trigonometry.IsQuadrantal θ ↔
      (UndergradKB.Trigonometry.polarPoint 1 θ).re = 0 ∨ (UndergradKB.Trigonometry.polarPoint 1 θ).im = 0) :=
  UndergradKB.Trigonometry.isQuadrantal_iff θ

/-- Every point off the axes lies in exactly one quadrant (TR-039). -/
@[kb "openstaxalgtrig2e" "§7.3, p. 711"]
theorem s7_3_quadrants_unique {z : ℂ} (hx : z.re ≠ 0) (hy : z.im ≠ 0) :
    ∃! k : Fin 4, UndergradKB.Trigonometry.InQuadrant k z :=
  UndergradKB.Trigonometry.existsUnique_quadrant hx hy

/-- A point on an axis lies in no quadrant (TR-039). -/
@[kb "openstaxalgtrig2e" "§7.3, p. 711"]
theorem s7_3_axes_in_no_quadrant {z : ℂ} (h : z.re = 0 ∨ z.im = 0) (k : Fin 4) :
    ¬ UndergradKB.Trigonometry.InQuadrant k z :=
  UndergradKB.Trigonometry.not_inQuadrant_of_axis h k

/-- The quadrant of the terminal side of an angle (TR-039). -/
@[kb "openstaxalgtrig2e" "§7.3, p. 711"]
theorem s7_3_angle_in_quadrant {r θ : ℝ} (hr : 0 < r) (k : Fin 4) (h1 : (k : ℕ) * (π / 2) < θ) (h2 : θ < ((k : ℕ) +
    1) * (π / 2)) :
    UndergradKB.Trigonometry.InQuadrant k (UndergradKB.Trigonometry.polarPoint r θ) :=
  UndergradKB.Trigonometry.polarPoint_mem_quadrant hr k h1 h2

/-- Average linear speed (TR-106). -/
@[kb "openstaxalgtrig2e" "§7.1, p. 692"]
theorem s7_1_average_linear_speed (c : ℂ) {r ω t : ℝ} (hr : 0 ≤ r) (hω : 0 ≤ ω) (ht : 0 < t) :
    UndergradKB.Trigonometry.avgLinearSpeed (eVariationOn (fun τ : ℝ => c + r * Complex.exp ((ω * τ : ℝ) *
      Complex.I)) (Icc 0 t)).toReal t = ω * r :=
  UndergradKB.Trigonometry.avgLinearSpeed_uniform_circular c hr hω ht

/-- Average angular speed (TR-107). -/
@[kb "openstaxalgtrig2e" "§7.1, p. 692"]
theorem s7_1_average_angular_speed (c : ℂ) {r ω t : ℝ} (hr : 0 ≤ r) (hω : 0 ≤ ω) (ht : 0 < t) :
    UndergradKB.Trigonometry.avgAngularSpeed (ω * t) t = ω ∧ UndergradKB.Trigonometry.avgLinearSpeed (eVariationOn
      (fun τ : ℝ => c + r * Complex.exp ((ω * τ : ℝ) * Complex.I)) (Icc 0 t)).toReal t = r *
      UndergradKB.Trigonometry.avgAngularSpeed (ω * t) t :=
  UndergradKB.Trigonometry.avgAngularSpeed_uniform_circular c hr hω ht

/-- One-loop limacon r = a + b cos t is convex iff a is at least 2|b|, otherwise dimpled (TR-139). -/
@[kb "openstaxalgtrig2e" "§10.4, p. 932 (box)"]
theorem s10_4_limacon_cos_dimpled_convex (a b : ℝ) :
    (∀ θ : ℝ, deriv (UndergradKB.Trigonometry.limaconCosX a b) θ * deriv (deriv
      (UndergradKB.Trigonometry.limaconCosY a b)) θ - deriv (UndergradKB.Trigonometry.limaconCosY a b) θ * deriv
      (deriv (UndergradKB.Trigonometry.limaconCosX a b)) θ = a ^ 2 + 3 * a * b * cos θ + 2 * b ^ 2) ∧ (0 < |b| → |b|
      < a → ((∀ θ, 0 ≤ deriv (UndergradKB.Trigonometry.limaconCosX a b) θ * deriv (deriv
      (UndergradKB.Trigonometry.limaconCosY a b)) θ - deriv (UndergradKB.Trigonometry.limaconCosY a b) θ * deriv
      (deriv (UndergradKB.Trigonometry.limaconCosX a b)) θ) ↔ 2 * |b| ≤ a)) ∧ (|b| < a → a < 2 * |b| → ∃ θ, deriv
      (UndergradKB.Trigonometry.limaconCosX a b) θ * deriv (deriv (UndergradKB.Trigonometry.limaconCosY a b)) θ -
      deriv (UndergradKB.Trigonometry.limaconCosY a b) θ * deriv (deriv (UndergradKB.Trigonometry.limaconCosX a b))
      θ < 0) :=
  ⟨fun θ => UndergradKB.Trigonometry.limaconCos_curvature a b θ, fun hb hab =>
    UndergradKB.Trigonometry.limaconCos_convex_iff hb hab, fun hab h2 => UndergradKB.Trigonometry.limaconCos_dimple
    hab h2⟩

/-- One-loop limacon r = a + b sin t is convex iff a is at least 2|b|, otherwise dimpled (TR-139). -/
@[kb "openstaxalgtrig2e" "§10.4, p. 932 (box)"]
theorem s10_4_limacon_sin_dimpled_convex (a b : ℝ) :
    (∀ θ : ℝ, deriv (UndergradKB.Trigonometry.limaconSinX a b) θ * deriv (deriv
      (UndergradKB.Trigonometry.limaconSinY a b)) θ - deriv (UndergradKB.Trigonometry.limaconSinY a b) θ * deriv
      (deriv (UndergradKB.Trigonometry.limaconSinX a b)) θ = a ^ 2 + 3 * a * b * sin θ + 2 * b ^ 2) ∧ (0 < |b| → |b|
      < a → ((∀ θ, 0 ≤ deriv (UndergradKB.Trigonometry.limaconSinX a b) θ * deriv (deriv
      (UndergradKB.Trigonometry.limaconSinY a b)) θ - deriv (UndergradKB.Trigonometry.limaconSinY a b) θ * deriv
      (deriv (UndergradKB.Trigonometry.limaconSinX a b)) θ) ↔ 2 * |b| ≤ a)) ∧ (|b| < a → a < 2 * |b| → ∃ θ, deriv
      (UndergradKB.Trigonometry.limaconSinX a b) θ * deriv (deriv (UndergradKB.Trigonometry.limaconSinY a b)) θ -
      deriv (UndergradKB.Trigonometry.limaconSinY a b) θ * deriv (deriv (UndergradKB.Trigonometry.limaconSinX a b))
      θ < 0) :=
  ⟨fun θ => UndergradKB.Trigonometry.limaconSin_curvature a b θ, fun hb hab =>
    UndergradKB.Trigonometry.limaconSin_convex_iff hb hab, fun hab h2 => UndergradKB.Trigonometry.limaconSin_dimple
    hab h2⟩

/-- Petals of r = a cos nt have length |a| (TR-142). -/
@[kb "openstaxalgtrig2e" "§10.4, p. 937 (box)"]
theorem s10_4_rose_cos_petal_length (a : ℝ) (n : ℕ) :
    (∀ z ∈ UndergradKB.Trigonometry.roseCos a n, ‖z‖ ≤ |a|) ∧ ∃ z ∈ UndergradKB.Trigonometry.roseCos a n, ‖z‖ = |a|
      :=
  UndergradKB.Trigonometry.roseCos_petal_length a n

/-- Petals of r = a sin nt have length |a| (TR-142). -/
@[kb "openstaxalgtrig2e" "§10.4, p. 937 (box)"]
theorem s10_4_rose_sin_petal_length (a : ℝ) {n : ℕ} (hn : 0 < n) :
    (∀ z ∈ UndergradKB.Trigonometry.roseSin a n, ‖z‖ ≤ |a|) ∧ ∃ z ∈ UndergradKB.Trigonometry.roseSin a n, ‖z‖ = |a|
      :=
  UndergradKB.Trigonometry.roseSin_petal_length a hn

/-- Number of petals of r = a cos nt (TR-143). -/
@[kb "openstaxalgtrig2e" "§10.4, p. 937 (box; Ex 8-9)"]
theorem s10_4_rose_cos_petal_count {a : ℝ} (ha : a ≠ 0) {n : ℕ} (hn : 0 < n) :
    (UndergradKB.Trigonometry.roseCosTips a n).ncard = if Odd n then n else 2 * n :=
  UndergradKB.Trigonometry.roseCos_petal_count ha hn

/-- Number of petals of r = a sin nt (TR-143). -/
@[kb "openstaxalgtrig2e" "§10.4, p. 937 (box; Ex 8-9)"]
theorem s10_4_rose_sin_petal_count {a : ℝ} (ha : a ≠ 0) {n : ℕ} (hn : 0 < n) :
    (UndergradKB.Trigonometry.roseSinTips a n).ncard = if Odd n then n else 2 * n :=
  UndergradKB.Trigonometry.roseSin_petal_count ha hn

/-- The Archimedes spiral winds out at a constant rate (TR-144). -/
@[kb "openstaxalgtrig2e" "§10.4, p. 939 (box)"]
theorem s10_4_archimedes_spiral {θ : ℝ} (h : 0 ≤ θ) :
    ‖UndergradKB.Trigonometry.polarPoint θ θ‖ = θ ∧ ‖UndergradKB.Trigonometry.polarPoint (θ + 2 * π) (θ + 2 * π)‖ =
      ‖UndergradKB.Trigonometry.polarPoint θ θ‖ + 2 * π :=
  ⟨UndergradKB.Trigonometry.archimedesSpiral_norm h, UndergradKB.Trigonometry.archimedesSpiral_turn h⟩

/-- The Archimedes spiral has none of the three symmetries (TR-144). -/
@[kb "openstaxalgtrig2e" "Ex 10 §10.4, p. 940"]
theorem s10_4_archimedes_spiral_no_symmetry :
    ¬ (∀ z ∈ UndergradKB.Trigonometry.archimedesSpiral, conj z ∈ UndergradKB.Trigonometry.archimedesSpiral) ∧ ¬ (∀ z
      ∈ UndergradKB.Trigonometry.archimedesSpiral, -conj z ∈ UndergradKB.Trigonometry.archimedesSpiral) ∧ ¬ (∀ z ∈
      UndergradKB.Trigonometry.archimedesSpiral, -z ∈ UndergradKB.Trigonometry.archimedesSpiral) :=
  UndergradKB.Trigonometry.archimedesSpiral_no_symmetry

end UndergradKB.Trigonometry.Course.OpenStax
