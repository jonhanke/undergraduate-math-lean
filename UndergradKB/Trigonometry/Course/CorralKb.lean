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

/-! # Course layer: Corral, *Trigonometry*, items proved in the knowledge base

Thin theorems in the book's terms whose proofs are the theorems of `UndergradKB/Trigonometry/*.lean`
listed in the coverage checklist (rows classified `in undergrad-kb`).  All angles are in radians.
-/

namespace UndergradKB.Trigonometry.Course.Corral

open EuclideanGeometry Real Set ComplexConjugate

set_option linter.unusedVariables false

/-- Coterminal angles have the same sine and cosine (TR-006). -/
@[kb "corraltrig" "Def §1.4, p. 37"]
theorem def_1_4_coterminal_same_values (θ : ℝ) (k : ℤ) :
    sin (θ + k * (2 * π)) = sin θ ∧ cos (θ + k * (2 * π)) = cos θ :=
  UndergradKB.Trigonometry.sin_cos_add_int_mul_two_pi θ k

/-- In a right triangle the two acute angles are complementary (TR-011). -/
@[kb "corraltrig" "Box §1.1, p. 10"]
theorem box_1_1_acute_angles_complementary {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace
    P] [NormedAddTorsor V P] {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) (h12 : p₂ ≠ p₁) :
    ∠ p₂ p₃ p₁ + ∠ p₃ p₁ p₂ = π / 2 :=
  UndergradKB.Trigonometry.angle_add_angle_of_angle_eq_pi_div_two h h12

/-- The hypotenuse of a right triangle is longer than each leg (TR-014). -/
@[kb "corraltrig" "Box §1.1, p. 12"]
theorem box_1_1_hypotenuse_longest {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) (h12 : p₁ ≠ p₂) (h32 : p₃ ≠ p₂) :
    dist p₁ p₂ < dist p₁ p₃ ∧ dist p₃ p₂ < dist p₁ p₃ :=
  UndergradKB.Trigonometry.legs_lt_hypotenuse h h12 h32

/-- Cosecant, secant and cotangent of an acute angle of a right triangle as ratios of sides (TR-016). -/
@[kb "corraltrig" "Table 1.2, p. 15"]
theorem table_1_2_csc_sec_cot_ratios {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) (h0 : p₁ ≠ p₂ ∨ p₃ ≠ p₂) :
    UndergradKB.Trigonometry.csc (∠ p₂ p₃ p₁) = dist p₁ p₃ / dist p₁ p₂ ∧ UndergradKB.Trigonometry.sec (∠ p₂ p₃ p₁)
      = dist p₁ p₃ / dist p₃ p₂ ∧ cot (∠ p₂ p₃ p₁) = dist p₃ p₂ / dist p₁ p₂ :=
  ⟨UndergradKB.Trigonometry.csc_angle_of_angle_eq_pi_div_two h h0,
    UndergradKB.Trigonometry.sec_angle_of_angle_eq_pi_div_two h,
    UndergradKB.Trigonometry.cot_angle_of_angle_eq_pi_div_two h⟩

/-- Side ratios of a right triangle depend only on the acute angle (TR-017). -/
@[kb "corraltrig" "Box §1.2, p. 17"]
theorem box_1_2_ratios_independent_of_triangle {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] {p₁ p₂ p₃ q₁ q₂ q₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) (h' : ∠ q₁ q₂ q₃ = π / 2)
    (h0 : p₁ ≠ p₂ ∨ p₃ ≠ p₂) (h0' : q₁ ≠ q₂ ∨ q₃ ≠ q₂) (hang : ∠ p₂ p₃ p₁ = ∠ q₂ q₃ q₁) :
    dist p₁ p₂ / dist p₁ p₃ = dist q₁ q₂ / dist q₁ q₃ ∧ dist p₃ p₂ / dist p₁ p₃ = dist q₃ q₂ / dist q₁ q₃ ∧ dist p₁
      p₂ / dist p₃ p₂ = dist q₁ q₂ / dist q₃ q₂ :=
  UndergradKB.Trigonometry.side_ratios_eq_of_angle_eq h h' h0 h0' hang

/-- Exact values of the four remaining functions at 45 degrees (TR-018). -/
@[kb "corraltrig" "Ex 1.6, p. 17"]
theorem ex_1_6_values_at_45_degrees :
    (tan (π / 4) = 1 ∧ cot (π / 4) = 1 ∧ UndergradKB.Trigonometry.sec (π / 4) = √2 ∧ UndergradKB.Trigonometry.csc (π
      / 4) = √2) :=
  UndergradKB.Trigonometry.six_functions_special_values.2.1

/-- Exact values of the four remaining functions at 30 and 60 degrees (TR-018). -/
@[kb "corraltrig" "Ex 1.7, p. 18"]
theorem ex_1_7_values_at_30_60_degrees :
    (tan (π / 6) = √3 / 3 ∧ cot (π / 6) = √3 ∧ UndergradKB.Trigonometry.sec (π / 6) = 2 * √3 / 3 ∧
      UndergradKB.Trigonometry.csc (π / 6) = 2) ∧ (tan (π / 3) = √3 ∧ cot (π / 3) = √3 / 3 ∧
      UndergradKB.Trigonometry.sec (π / 3) = 2 ∧ UndergradKB.Trigonometry.csc (π / 3) = 2 * √3 / 3) :=
  ⟨UndergradKB.Trigonometry.six_functions_special_values.1,
    UndergradKB.Trigonometry.six_functions_special_values.2.2⟩

/-- Sides of a 45-45-90 triangle are in ratio 1 : 1 : sqrt 2 (TR-019). -/
@[kb "corraltrig" "Box §1.2, p. 19"]
theorem box_1_2_triangle_45_45_90 {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) (hang : ∠ p₂ p₃ p₁ = π / 4) :
    dist p₁ p₂ = dist p₂ p₃ ∧ dist p₁ p₃ = √2 * dist p₂ p₃ :=
  UndergradKB.Trigonometry.right_triangle_pi_div_four h hang

/-- Sides of a 30-60-90 triangle are in ratio 1 : sqrt 3 : 2 (TR-019). -/
@[kb "corraltrig" "Box §1.2, p. 19"]
theorem box_1_2_triangle_30_60_90 {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) (hang : ∠ p₂ p₃ p₁ = π / 6) :
    dist p₁ p₃ = 2 * dist p₁ p₂ ∧ dist p₂ p₃ = √3 * dist p₁ p₂ :=
  UndergradKB.Trigonometry.right_triangle_pi_div_six h hang

/-- Exact sine, cosine and tangent of 75 degrees (TR-020). -/
@[kb "corraltrig" "Ex 1.10, p. 20"]
theorem ex_1_10_values_at_75_degrees :
    sin (5 * π / 12) = (√6 + √2) / 4 ∧ cos (5 * π / 12) = (√6 - √2) / 4 ∧ tan (5 * π / 12) = (√6 + √2) / (√6 - √2)
      :=
  ⟨UndergradKB.Trigonometry.sin_five_pi_div_twelve, UndergradKB.Trigonometry.cos_five_pi_div_twelve,
    UndergradKB.Trigonometry.tan_five_pi_div_twelve⟩

/-- Signs of sine, cosine and tangent in the four quadrants (TR-025). -/
@[kb "corraltrig" "Fig 1.4.5, p. 34"]
theorem fig_1_4_5_quadrant_signs :
    (∀ θ : ℝ, 0 < θ → θ < π / 2 → 0 < sin θ ∧ 0 < cos θ ∧ 0 < tan θ) ∧ (∀ θ : ℝ, π / 2 < θ → θ < π → 0 < sin θ ∧ cos
      θ < 0 ∧ tan θ < 0) ∧ (∀ θ : ℝ, π < θ → θ < 3 * π / 2 → sin θ < 0 ∧ cos θ < 0 ∧ 0 < tan θ) ∧ ∀ θ : ℝ, 3 * π / 2
      < θ → θ < 2 * π → sin θ < 0 ∧ 0 < cos θ ∧ tan θ < 0 :=
  ⟨fun _ h₁ h₂ => UndergradKB.Trigonometry.quadrant_one_signs h₁ h₂, fun _ h₁ h₂ =>
    UndergradKB.Trigonometry.quadrant_two_signs h₁ h₂, fun _ h₁ h₂ => UndergradKB.Trigonometry.quadrant_three_signs
    h₁ h₂, fun _ h₁ h₂ => UndergradKB.Trigonometry.quadrant_four_signs h₁ h₂⟩

/-- Signs of sine, cosine and tangent in the four quadrants (TR-025). -/
@[kb "corraltrig" "Box §1.4, p. 39"]
theorem box_1_4_quadrant_signs :
    (∀ θ : ℝ, 0 < θ → θ < π / 2 → 0 < sin θ ∧ 0 < cos θ ∧ 0 < tan θ) ∧ (∀ θ : ℝ, π / 2 < θ → θ < π → 0 < sin θ ∧ cos
      θ < 0 ∧ tan θ < 0) ∧ (∀ θ : ℝ, π < θ → θ < 3 * π / 2 → sin θ < 0 ∧ cos θ < 0 ∧ 0 < tan θ) ∧ ∀ θ : ℝ, 3 * π / 2
      < θ → θ < 2 * π → sin θ < 0 ∧ 0 < cos θ ∧ tan θ < 0 :=
  ⟨fun _ h₁ h₂ => UndergradKB.Trigonometry.quadrant_one_signs h₁ h₂, fun _ h₁ h₂ =>
    UndergradKB.Trigonometry.quadrant_two_signs h₁ h₂, fun _ h₁ h₂ => UndergradKB.Trigonometry.quadrant_three_signs
    h₁ h₂, fun _ h₁ h₂ => UndergradKB.Trigonometry.quadrant_four_signs h₁ h₂⟩

/-- Sine and cosine at the multiples of 30 and 45 degrees in quadrants II to IV (TR-027). -/
@[kb "corraltrig" "Table 1.3, p. 37"]
theorem table_1_3_values_beyond_first_quadrant :
    ((sin (2 * π / 3) = √3 / 2 ∧ cos (2 * π / 3) = -(1 / 2)) ∧ (sin (3 * π / 4) = √2 / 2 ∧ cos (3 * π / 4) = -(√2 /
      2)) ∧ (sin (5 * π / 6) = 1 / 2 ∧ cos (5 * π / 6) = -(√3 / 2))) ∧ ((sin (7 * π / 6) = -(1 / 2) ∧ cos (7 * π /
      6) = -(√3 / 2)) ∧ (sin (5 * π / 4) = -(√2 / 2) ∧ cos (5 * π / 4) = -(√2 / 2)) ∧ (sin (4 * π / 3) = -(√3 / 2) ∧
      cos (4 * π / 3) = -(1 / 2))) ∧ ((sin (5 * π / 3) = -(√3 / 2) ∧ cos (5 * π / 3) = 1 / 2) ∧ (sin (7 * π / 4) =
      -(√2 / 2) ∧ cos (7 * π / 4) = √2 / 2) ∧ (sin (11 * π / 6) = -(1 / 2) ∧ cos (11 * π / 6) = √3 / 2)) :=
  ⟨UndergradKB.Trigonometry.sin_cos_second_quadrant, UndergradKB.Trigonometry.sin_cos_third_quadrant,
    UndergradKB.Trigonometry.sin_cos_fourth_quadrant⟩

/-- Reference angle of an angle in each quadrant (TR-029). -/
@[kb "corraltrig" "Def §1.4, p. 37"]
theorem def_1_4_reference_angle :
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

/-- The tangent of t plus 90 degrees is minus the cotangent of t (TR-030). -/
@[kb "corraltrig" "Box §1.5, p. 40"]
theorem box_1_5_tan_add_half_turn_quarter (x : ℝ) :
    tan (x + π / 2) = - cot x :=
  UndergradKB.Trigonometry.tan_add_pi_div_two x

/-- The tangent of t minus 90 degrees is minus the cotangent of t (TR-031). -/
@[kb "corraltrig" "Box §1.5, p. 42"]
theorem box_1_5_tan_sub_quarter_turn (x : ℝ) :
    tan (x - π / 2) = - cot x :=
  UndergradKB.Trigonometry.tan_sub_pi_div_two x

/-- Reciprocal relations between the six trigonometric functions (TR-044). -/
@[kb "corraltrig" "Box §1.2, p. 15"]
theorem box_1_2_reciprocal_definitions (x : ℝ) :
    UndergradKB.Trigonometry.sec x = 1 / cos x ∧ UndergradKB.Trigonometry.csc x = 1 / sin x ∧ cot x = 1 / tan x ∧
      cos x = 1 / UndergradKB.Trigonometry.sec x ∧ sin x = 1 / UndergradKB.Trigonometry.csc x ∧ tan x = 1 / cot x :=
  ⟨UndergradKB.Trigonometry.sec_eq_one_div_cos x, UndergradKB.Trigonometry.csc_eq_one_div_sin x,
    UndergradKB.Trigonometry.cot_eq_one_div_tan x, UndergradKB.Trigonometry.cos_eq_one_div_sec x,
    UndergradKB.Trigonometry.sin_eq_one_div_csc x, UndergradKB.Trigonometry.tan_eq_one_div_cot x⟩

/-- Cofunction identities for secant, cosecant and cotangent (TR-045). -/
@[kb "corraltrig" "Thm 1.2, p. 19"]
theorem thm_1_2_cofunctions (x : ℝ) :
    UndergradKB.Trigonometry.sec (π / 2 - x) = UndergradKB.Trigonometry.csc x ∧ UndergradKB.Trigonometry.csc (π / 2
      - x) = UndergradKB.Trigonometry.sec x ∧ cot (π / 2 - x) = tan x :=
  ⟨UndergradKB.Trigonometry.sec_pi_div_two_sub x, UndergradKB.Trigonometry.csc_pi_div_two_sub x,
    UndergradKB.Trigonometry.cot_pi_div_two_sub x⟩

/-- Products of the reciprocal pairs equal one wherever defined (TR-047). -/
@[kb "corraltrig" "Box §3.1, p. 73"]
theorem box_3_1_reciprocal_products (x : ℝ) (hs : sin x ≠ 0) (hc : cos x ≠ 0) :
    cos x * UndergradKB.Trigonometry.sec x = 1 ∧ sin x * UndergradKB.Trigonometry.csc x = 1 ∧ tan x * cot x = 1 :=
  ⟨UndergradKB.Trigonometry.cos_mul_sec x hc, UndergradKB.Trigonometry.sin_mul_csc x hs,
    UndergradKB.Trigonometry.tan_mul_cot x hs hc⟩

/-- One plus tangent squared is secant squared (TR-053). -/
@[kb "corraltrig" "Eq 3.10, p. 75"]
theorem eq_3_10_one_add_tan_sq (x : ℝ) (h : cos x ≠ 0) :
    1 + tan x ^ 2 = UndergradKB.Trigonometry.sec x ^ 2 :=
  UndergradKB.Trigonometry.one_add_tan_sq_eq_sec_sq x h

/-- Cotangent squared plus one is cosecant squared (TR-054). -/
@[kb "corraltrig" "Eq 3.11, p. 75"]
theorem eq_3_11_cot_sq_add_one (x : ℝ) (h : sin x ≠ 0) :
    cot x ^ 2 + 1 = UndergradKB.Trigonometry.csc x ^ 2 :=
  UndergradKB.Trigonometry.cot_sq_add_one_eq_csc_sq x h

/-- Sum of the cosines of the angles of a triangle (TR-055). -/
@[kb "corraltrig" "Ex 3.18, p. 92"]
theorem ex_3_18_cos_sum_triangle (A B C : ℝ) (h : A + B + C = π) :
    cos A + cos B + cos C = 1 + 4 * sin (A / 2) * sin (B / 2) * sin (C / 2) :=
  UndergradKB.Trigonometry.cos_add_cos_add_cos_triangle A B C h

/-- Product of the sines of the half angles of a triangle is at most one eighth (TR-056). -/
@[kb "corraltrig" "Ex 3.19, p. 92"]
theorem ex_3_19_sin_half_product_bound (A B C : ℝ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (h : A + B + C = π) :
    sin (A / 2) * sin (B / 2) * sin (C / 2) ≤ 1 / 8 :=
  UndergradKB.Trigonometry.sin_half_mul_le A B C hA hB hC h

/-- The sum of the cosines of the angles of a triangle lies in $(1, 3/2]$ (TR-057). -/
@[kb "corraltrig" "Ex 3.20, p. 92"]
theorem ex_3_20_cos_sum_bounds (A B C : ℝ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (h : A + B + C = π) :
    1 < cos A + cos B + cos C ∧ cos A + cos B + cos C ≤ 3 / 2 :=
  UndergradKB.Trigonometry.one_lt_cos_add_cos_add_cos_le A B C hA hB hC h

/-- Sine and cosine of a sum of three angles (TR-061). -/
@[kb "corraltrig" "Ex 3.9, p. 82"]
theorem ex_3_9_sin_cos_triple_sum (A B C : ℝ) :
    sin (A + B + C) = sin A * cos B * cos C + cos A * sin B * cos C + cos A * cos B * sin C - sin A * sin B * sin C
      ∧ cos (A + B + C) = cos A * cos B * cos C - sin A * sin B * cos C - sin A * cos B * sin C - cos A * sin B *
      sin C :=
  ⟨UndergradKB.Trigonometry.sin_add_add A B C, UndergradKB.Trigonometry.cos_add_add A B C⟩

/-- Tangents of angles summing to pi (TR-062). -/
@[kb "corraltrig" "Ex 3.10, p. 82"]
theorem ex_3_10_tan_sum_triangle (A B C : ℝ) (h : A + B + C = π) (hA : cos A ≠ 0) (hB : cos B ≠ 0) (hC : cos C ≠ 0)
    :
    tan A + tan B + tan C = tan A * tan B * tan C :=
  UndergradKB.Trigonometry.tan_add_tan_add_tan_eq A B C h hA hB hC

/-- A sine identity for four angles summing to pi (TR-063). -/
@[kb "corraltrig" "Ex 3.11, p. 82"]
theorem ex_3_11_sin_product_sum (A B C D : ℝ) (h : A + B + C + D = π) :
    sin A * sin B + sin C * sin D = sin (A + C) * sin (B + C) :=
  UndergradKB.Trigonometry.sin_mul_sin_add_sin_mul_sin A B C D h

/-- Tangent squared of a half angle (TR-069). -/
@[kb "corraltrig" "Eq 3.30, p. 87"]
theorem eq_3_30_tan_sq_half (θ : ℝ) :
    tan (θ / 2) ^ 2 = (1 - cos θ) / (1 + cos θ) :=
  UndergradKB.Trigonometry.tan_sq_half θ

/-- Half-angle formulas for tangent and cotangent (TR-071). -/
@[kb "corraltrig" "Eq 3.33-3.36, p. 88"]
theorem eq_3_33_to_3_36_tan_cot_half_angle (θ : ℝ) :
    |tan (θ / 2)| = √((1 - cos θ) / (1 + cos θ)) ∧ tan (θ / 2) = (1 - cos θ) / sin θ ∧ tan (θ / 2) = sin θ / (1 +
      cos θ) ∧ cot (θ / 2) = sin θ / (1 - cos θ) ∧ cot (θ / 2) = (1 + cos θ) / sin θ :=
  ⟨UndergradKB.Trigonometry.abs_tan_half θ, UndergradKB.Trigonometry.tan_half_eq_one_sub_cos_div_sin θ,
    UndergradKB.Trigonometry.tan_half_eq_sin_div_one_add_cos θ,
    UndergradKB.Trigonometry.cot_half_eq_sin_div_one_sub_cos θ,
    UndergradKB.Trigonometry.cot_half_eq_one_add_cos_div_sin θ⟩

/-- Number of triangles in the ambiguous case SSA (TR-075). -/
@[kb "corraltrig" "Table 2.1, p. 50"]
theorem table_2_1_ambiguous_case_count {a b A : ℝ} (h0 : 0 < a) (hb : 0 < b) (hA0 : 0 < A) (hA1 : A < π) :
    (A < π / 2 → (a < b * sin A → (UndergradKB.Trigonometry.ssaSolutions a b A).ncard = 0) ∧ (a = b * sin A →
      (UndergradKB.Trigonometry.ssaSolutions a b A).ncard = 1) ∧ (b * sin A < a → a < b →
      (UndergradKB.Trigonometry.ssaSolutions a b A).ncard = 2) ∧ (b ≤ a → (UndergradKB.Trigonometry.ssaSolutions a b
      A).ncard = 1)) ∧ (π / 2 ≤ A → (a ≤ b → (UndergradKB.Trigonometry.ssaSolutions a b A).ncard = 0) ∧ (b < a →
      (UndergradKB.Trigonometry.ssaSolutions a b A).ncard = 1)) :=
  UndergradKB.Trigonometry.ncard_ssaSolutions h0 hb hA0 hA1

/-- The two solutions of the ambiguous case with $b \sin A < a < b$ (TR-075). -/
@[kb "corraltrig" "Table 2.1, p. 50"]
theorem table_2_1_ambiguous_case_two_solutions {a b A : ℝ} (h0 : 0 < a) (hb : 0 < b) (hA0 : 0 < A) (hA : A < π / 2)
    (h1 : b * sin A < a) (h2 : a < b) :
    UndergradKB.Trigonometry.ssaSolutions a b A = {b * cos A - √(a ^ 2 - (b * sin A) ^ 2), b * cos A + √(a ^ 2 - (b
      * sin A) ^ 2)} :=
  UndergradKB.Trigonometry.ssaSolutions_acute_two h0 hb hA0 hA h1 h2

/-- The third side of a triangle is a solution of the SSA data (TR-075). -/
@[kb "corraltrig" "Table 2.1, p. 50"]
theorem table_2_1_ambiguous_case_triangle_solution {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (t : Affine.Triangle ℝ P) :
    dist (t.points 0) (t.points 1) ∈ UndergradKB.Trigonometry.ssaSolutions (dist (t.points 1) (t.points 2)) (dist
      (t.points 0) (t.points 2)) (∠ (t.points 1) (t.points 0) (t.points 2)) :=
  UndergradKB.Trigonometry.dist_mem_ssaSolutions t

/-- Law of tangents (TR-080). -/
@[kb "corraltrig" "Theorem 2.3, p. 59"]
theorem thm_2_3_law_of_tangents {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] (t : Affine.Triangle ℝ P) {a b A B : ℝ} (ha : a = dist (t.points 1) (t.points 2)) (hb : b
    = dist (t.points 0) (t.points 2)) (hA : A = ∠ (t.points 1) (t.points 0) (t.points 2)) (hB : B = ∠ (t.points 0)
    (t.points 1) (t.points 2)) :
    (a - b) / (a + b) = tan ((A - B) / 2) / tan ((A + B) / 2) :=
  UndergradKB.Trigonometry.law_of_tangents t ha hb hA hB

/-- Law of tangents for numbers satisfying the law of sines (TR-080). -/
@[kb "corraltrig" "Ex 3.17, p. 91"]
theorem ex_3_17_law_of_tangents_real {a b A B C : ℝ} (ha : 0 < a) (hb : 0 < b) (hA : 0 < A) (hB : 0 < B) (hC : 0 <
    C) (hs : A + B + C = π) (hab : a * sin B = b * sin A) :
    (a - b) / (a + b) = tan ((A - B) / 2) / tan ((A + B) / 2) :=
  UndergradKB.Trigonometry.law_of_tangents_real ha hb hA hB hC hs hab

/-- Mollweide's equations (TR-081). -/
@[kb "corraltrig" "Box §2.3 (Mollweide's equations), p. 60"]
theorem box_2_3_mollweide {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] (t : Affine.Triangle ℝ P) {a b c A B C : ℝ} (ha : a = dist (t.points 1) (t.points 2)) (hb
    : b = dist (t.points 0) (t.points 2)) (hc : c = dist (t.points 0) (t.points 1)) (hA : A = ∠ (t.points 1)
    (t.points 0) (t.points 2)) (hB : B = ∠ (t.points 0) (t.points 1) (t.points 2)) (hC : C = ∠ (t.points 0)
    (t.points 2) (t.points 1)) :
    (a - b) / c = sin ((A - B) / 2) / cos (C / 2) ∧ (a + b) / c = cos ((A - B) / 2) / sin (C / 2) :=
  UndergradKB.Trigonometry.mollweide t ha hb hc hA hB hC

/-- Mollweide's equations for numbers satisfying the law of sines (TR-081). -/
@[kb "corraltrig" "Ex 3.16, p. 91"]
theorem ex_3_16_mollweide_real {a b c A B C : ℝ} (hc : 0 < c) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hs : A + B + C
    = π) (hab : a * sin B = b * sin A) (hac : a * sin C = c * sin A) :
    (a - b) / c = sin ((A - B) / 2) / cos (C / 2) ∧ (a + b) / c = cos ((A - B) / 2) / sin (C / 2) :=
  UndergradKB.Trigonometry.mollweide_real hc hA hB hC hs hab hac

/-- Area is half the product of two sides and the sine of the included angle (TR-082). -/
@[kb "corraltrig" "Box §2.4, p. 62"]
theorem box_2_4_area_half_bc_sin_a {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] (t : Affine.Triangle ℝ P) {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠
    i₃) :
    UndergradKB.Trigonometry.area t = dist (t.points i₁) (t.points i₂) * dist (t.points i₁) (t.points i₃) * sin (∠
      (t.points i₂) (t.points i₁) (t.points i₃)) / 2 :=
  UndergradKB.Trigonometry.area_eq_mul_mul_sin_div_two t h₁₂ h₁₃ h₂₃

/-- Area is half a side times the height on it (TR-082). -/
@[kb "corraltrig" "Box §2.4, p. 62"]
theorem box_2_4_area_half_base_height {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] (t : Affine.Triangle ℝ P) {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠
    i₃) :
    UndergradKB.Trigonometry.area t = dist (t.points i₂) (t.points i₃) * t.height i₁ / 2 :=
  UndergradKB.Trigonometry.area_eq_dist_mul_height_div_two t h₁₂ h₁₃ h₂₃

/-- Area from one side and the angles (TR-083). -/
@[kb "corraltrig" "Box §2.4, p. 63"]
theorem box_2_4_area_one_side_two_angles {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace
    P] [NormedAddTorsor V P] (t : Affine.Triangle ℝ P) {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂
    ≠ i₃) :
    UndergradKB.Trigonometry.area t = dist (t.points i₂) (t.points i₃) ^ 2 * sin (∠ (t.points i₁) (t.points i₂)
      (t.points i₃)) * sin (∠ (t.points i₁) (t.points i₃) (t.points i₂)) / (2 * sin (∠ (t.points i₂) (t.points i₁)
      (t.points i₃))) :=
  UndergradKB.Trigonometry.area_eq_sq_mul_sin_mul_sin_div_sin t h₁₂ h₁₃ h₂₃

/-- Heron's formula (TR-084). -/
@[kb "corraltrig" "Box §2.4, p. 63"]
theorem box_2_4_heron {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor
    V P] (t : Affine.Triangle ℝ P) {a b c s : ℝ} (ha : a = dist (t.points 1) (t.points 2)) (hb : b = dist (t.points
    0) (t.points 2)) (hc : c = dist (t.points 0) (t.points 1)) (hs : s = (a + b + c) / 2) :
    UndergradKB.Trigonometry.area t = √(s * (s - a) * (s - b) * (s - c)) :=
  UndergradKB.Trigonometry.heron t ha hb hc hs

/-- Kahan's stable form of Heron's formula (TR-085). -/
@[kb "corraltrig" "Box §2.4, p. 65"]
theorem box_2_4_heron_kahan {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] (t : Affine.Triangle ℝ P) {a b c : ℝ} (ha : a = dist (t.points 1) (t.points 2)) (hb : b =
    dist (t.points 0) (t.points 2)) (hc : c = dist (t.points 0) (t.points 1)) :
    UndergradKB.Trigonometry.area t = 1 / 4 * √((a + (b + c)) * (c - (a - b)) * (c + (a - b)) * (a + (b - c))) :=
  UndergradKB.Trigonometry.heron_kahan t ha hb hc

/-- Qin Jiushao's form of the area (TR-085). -/
@[kb "corraltrig" "Box §2.4, p. 66"]
theorem box_2_4_qin_jiushao {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] (t : Affine.Triangle ℝ P) {a b c : ℝ} (ha : a = dist (t.points 1) (t.points 2)) (hb : b =
    dist (t.points 0) (t.points 2)) (hc : c = dist (t.points 0) (t.points 1)) :
    UndergradKB.Trigonometry.area t = 1 / 2 * √(a ^ 2 * c ^ 2 - ((a ^ 2 + c ^ 2 - b ^ 2) / 2) ^ 2) :=
  UndergradKB.Trigonometry.area_eq_qin_jiushao t ha hb hc

/-- The circumcenter lies on the perpendicular bisector of each side (TR-093). -/
@[kb "corraltrig" "Cor 2.7, p. 69"]
theorem cor_2_7_circumcenter_on_perp_bisector {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (t : Affine.Triangle ℝ P) {i j : Fin 3} (hij : i ≠ j) :
    t.circumcenter ∈ AffineSubspace.perpBisector (t.points i) (t.points j) :=
  UndergradKB.Trigonometry.circumcenter_mem_perpBisector t hij

/-- Area equals $abc/(4R)$ (TR-094). -/
@[kb "corraltrig" "Thm 2.8, p. 70"]
theorem thm_2_8_area_and_circumradius {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] (t : Affine.Triangle ℝ P) {a b c : ℝ} (ha : a = dist (t.points 1) (t.points 2)) (hb : b =
    dist (t.points 0) (t.points 2)) (hc : c = dist (t.points 0) (t.points 1)) :
    UndergradKB.Trigonometry.area t = a * b * c / (4 * t.circumradius) ∧ t.circumradius = a * b * c / (4 *
      UndergradKB.Trigonometry.area t) :=
  UndergradKB.Trigonometry.area_eq_mul_mul_mul_div_four_mul_circumradius t ha hb hc

/-- Circumradius from the sides (TR-095). -/
@[kb "corraltrig" "Cor 2.9, p. 70"]
theorem cor_2_9_circumradius_from_sides {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] (t : Affine.Triangle ℝ P) {a b c s : ℝ} (ha : a = dist (t.points 1) (t.points 2)) (hb : b
    = dist (t.points 0) (t.points 2)) (hc : c = dist (t.points 0) (t.points 1)) (hs : s = (a + b + c) / 2) :
    t.circumradius = a * b * c / (4 * √(s * (s - a) * (s - b) * (s - c))) :=
  UndergradKB.Trigonometry.circumradius_eq_heron t ha hb hc hs

/-- The incenter lies on the bisector of each angle (TR-096). -/
@[kb "corraltrig" "Box §2.5, p. 70"]
theorem box_2_5_incenter_on_bisectors {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] (t : Affine.Triangle ℝ P) {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠
    i₃) :
    ∠ (t.points i₂) (t.points i₁) t.incenter = ∠ t.incenter (t.points i₁) (t.points i₃) :=
  UndergradKB.Trigonometry.angle_points_incenter_eq t h₁₂ h₁₃ h₂₃

/-- Inradius and half angles (TR-097). -/
@[kb "corraltrig" "Thm 2.10, p. 71"]
theorem thm_2_10_inradius_half_angle {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] (t : Affine.Triangle ℝ P) {a b c s : ℝ} (ha : a = dist (t.points 1) (t.points 2)) (hb : b
    = dist (t.points 0) (t.points 2)) (hc : c = dist (t.points 0) (t.points 1)) (hs : s = (a + b + c) / 2) :
    t.inradius = (s - a) * tan (∠ (t.points 1) (t.points 0) (t.points 2) / 2) :=
  UndergradKB.Trigonometry.inradius_eq_mul_tan_half t ha hb hc hs

/-- Inradius equals the area over the semiperimeter (TR-098). -/
@[kb "corraltrig" "Thm 2.11, p. 71"]
theorem thm_2_11_inradius_area_semiperimeter {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (t : Affine.Triangle ℝ P) {a b c s : ℝ} (ha : a = dist (t.points 1)
    (t.points 2)) (hb : b = dist (t.points 0) (t.points 2)) (hc : c = dist (t.points 0) (t.points 1)) (hs : s = (a +
    b + c) / 2) :
    t.inradius = UndergradKB.Trigonometry.area t / s :=
  UndergradKB.Trigonometry.inradius_eq_area_div_semiperimeter t ha hb hc hs

/-- Inradius from the sides (TR-098). -/
@[kb "corraltrig" "Thm 2.11, p. 71"]
theorem thm_2_11_inradius_from_sides {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] (t : Affine.Triangle ℝ P) {a b c s : ℝ} (ha : a = dist (t.points 1) (t.points 2)) (hb : b
    = dist (t.points 0) (t.points 2)) (hc : c = dist (t.points 0) (t.points 1)) (hs : s = (a + b + c) / 2) :
    t.inradius = √((s - a) * (s - b) * (s - c) / s) :=
  UndergradKB.Trigonometry.inradius_eq_sqrt t ha hb hc hs

/-- Degrees and radians: 360 degrees is 2 pi radians (TR-099). -/
@[kb "corraltrig" "Box §4.1, p. 94-95"]
theorem box_4_1_degrees_radians :
    UndergradKB.Trigonometry.degToRad 360 = 2 * π ∧ UndergradKB.Trigonometry.degToRad 180 = π ∧ (∀ x,
      UndergradKB.Trigonometry.radToDeg (UndergradKB.Trigonometry.degToRad x) = x) ∧ ∀ x,
      UndergradKB.Trigonometry.degToRad (UndergradKB.Trigonometry.radToDeg x) = x :=
  UndergradKB.Trigonometry.degToRad_spec

/-- Radian measure of a central angle is arc length over radius (TR-100). -/
@[kb "corraltrig" "Box §4.1, p. 95"]
theorem box_4_1_radian_measure (c : ℂ) {r θ : ℝ} (hr : 0 < r) (hθ : 0 ≤ θ) :
    (eVariationOn (fun φ : ℝ => c + r * Complex.exp (φ * Complex.I)) (Icc 0 θ)).toReal / r = θ :=
  UndergradKB.Trigonometry.radian_eq_arc_div_radius c hr hθ

/-- Arc length $s = r\theta$ (TR-102). -/
@[kb "corraltrig" "Box §4.2, p. 98"]
theorem box_4_2_arc_length (c : ℂ) {r θ : ℝ} (hr : 0 ≤ r) (hθ : 0 ≤ θ) :
    eVariationOn (fun φ : ℝ => c + r * Complex.exp (φ * Complex.I)) (Icc 0 θ) = ENNReal.ofReal (r * θ) :=
  UndergradKB.Trigonometry.arc_length c hr hθ

/-- Area of a sector is $r^2\theta/2$ (TR-103). -/
@[kb "corraltrig" "Box §4.3, p. 102"]
theorem box_4_3_sector_area {r θ : ℝ} (hr : 0 ≤ r) (hθ' : θ ≤ 2 * π) :
    MeasureTheory.volume (UndergradKB.Trigonometry.sector r θ) = ENNReal.ofReal (r ^ 2 * θ / 2) :=
  UndergradKB.Trigonometry.volume_sector hr hθ'

/-- Area of a sector is $rs/2$ with $s$ the arc length (TR-104). -/
@[kb "corraltrig" "Box §4.3, p. 102"]
theorem box_4_3_sector_area_arc {r θ : ℝ} (hr : 0 ≤ r) (hθ' : θ ≤ 2 * π) :
    MeasureTheory.volume (UndergradKB.Trigonometry.sector r θ) = ENNReal.ofReal (r * (r * θ) / 2) :=
  UndergradKB.Trigonometry.volume_sector_eq_half_mul_arc hr hθ'

/-- Linear speed is angular speed times radius (TR-108). -/
@[kb "corraltrig" "Box §4.4, p. 107"]
theorem box_4_4_linear_speed (c : ℂ) {r ω t : ℝ} (hr : 0 ≤ r) (hω : 0 ≤ ω) (ht : 0 ≤ t) :
    eVariationOn (fun τ : ℝ => c + r * Complex.exp ((ω * τ : ℝ) * Complex.I)) (Icc 0 t) = ENNReal.ofReal ((ω * r) *
      t) :=
  UndergradKB.Trigonometry.linear_speed c hr hω ht

/-- The slope is the tangent of the inclination (TR-112). -/
@[kb "corraltrig" "Box §1.5, p. 41"]
theorem box_1_5_slope_is_tan_inclination (m : ℝ) :
    tan (arctan m) = m ∧ -(π / 2) < arctan m ∧ arctan m < π / 2 :=
  UndergradKB.Trigonometry.tan_arctan_slope m

/-- Cotangent is minus the tangent shifted by pi/2 (TR-117). -/
@[kb "corraltrig" "Box §5.1, p. 114"]
theorem box_5_1_cot_eq_neg_tan_shift (x : ℝ) :
    cot x = - tan (x + π / 2) :=
  UndergradKB.Trigonometry.cot_eq_neg_tan_add_pi_div_two x

/-- Writing $a\sin x + b\cos x$ as a single sinusoid (TR-118). -/
@[kb "corraltrig" "Example 5.9, p. 114"]
theorem ex_5_9_amplitude_phase_form (a b : ℝ) (hab : a ≠ 0 ∨ b ≠ 0) :
    ∃ φ : ℝ, cos φ = a / √(a ^ 2 + b ^ 2) ∧ sin φ = b / √(a ^ 2 + b ^ 2) ∧ ∀ x, a * sin x + b * cos x = √(a ^ 2 + b
      ^ 2) * sin (x + φ) :=
  UndergradKB.Trigonometry.exists_amplitude_phase a b hab

/-- The amplitude bounds $a\sin x + b\cos x$ (TR-118). -/
@[kb "corraltrig" "Box §5.2, p. 116"]
theorem box_5_2_amplitude_bound (a b x : ℝ) :
    |a * sin x + b * cos x| ≤ √(a ^ 2 + b ^ 2) :=
  UndergradKB.Trigonometry.abs_mul_sin_add_mul_cos_le a b x

/-- The amplitude of $a\sin x + b\cos x$ is attained (TR-118). -/
@[kb "corraltrig" "Box §5.2, p. 116"]
theorem box_5_2_amplitude_attained (a b : ℝ) (hab : a ≠ 0 ∨ b ≠ 0) :
    ∃ x, a * sin x + b * cos x = √(a ^ 2 + b ^ 2) :=
  UndergradKB.Trigonometry.exists_mul_sin_add_mul_cos_eq a b hab

/-- Period of a sum of periodic functions (TR-119). -/
@[kb "corraltrig" "Example 5.10, p. 115"]
theorem ex_5_10_period_of_sum {f g : ℝ → ℝ} {p q L : ℝ} {m n : ℕ} (hf : Function.Periodic f p) (hg :
    Function.Periodic g q) (hm : L = m * p) (hn : L = n * q) :
    Function.Periodic (f + g) L :=
  UndergradKB.Trigonometry.periodic_add_of_common_multiple hf hg hm hn

/-- Period of a sum of periodic functions (TR-119). -/
@[kb "corraltrig" "Box §5.2, p. 115"]
theorem box_5_2_period_of_sum {f g : ℝ → ℝ} {p q L : ℝ} {m n : ℕ} (hf : Function.Periodic f p) (hg :
    Function.Periodic g q) (hm : L = m * p) (hn : L = n * q) :
    Function.Periodic (f + g) L :=
  UndergradKB.Trigonometry.periodic_add_of_common_multiple hf hg hm hn

/-- The period of the sine is its least positive period (TR-121). -/
@[kb "corraltrig" "Box §5.2, p. 117 (eq 5.1)"]
theorem box_5_2_period_definition :
    IsLeast {p | 0 < p ∧ Function.Periodic sin p} (2 * π) :=
  UndergradKB.Trigonometry.isLeast_period_sin

/-- Least periods of the six trigonometric functions (TR-122). -/
@[kb "corraltrig" "Example 5.3, p. 117"]
theorem ex_5_3_periods_of_the_six_functions :
    IsLeast {p | 0 < p ∧ Function.Periodic sin p} (2 * π) ∧ IsLeast {p | 0 < p ∧ Function.Periodic cos p} (2 * π) ∧
      IsLeast {p | 0 < p ∧ Function.Periodic tan p} (π) ∧ IsLeast {p | 0 < p ∧ Function.Periodic cot p} (π) ∧
      IsLeast {p | 0 < p ∧ Function.Periodic UndergradKB.Trigonometry.sec p} (2 * π) ∧ IsLeast {p | 0 < p ∧
      Function.Periodic UndergradKB.Trigonometry.csc p} (2 * π) :=
  ⟨UndergradKB.Trigonometry.isLeast_period_sin, UndergradKB.Trigonometry.isLeast_period_cos,
    UndergradKB.Trigonometry.isLeast_period_tan, UndergradKB.Trigonometry.isLeast_period_cot,
    UndergradKB.Trigonometry.isLeast_period_sec, UndergradKB.Trigonometry.isLeast_period_csc⟩

/-- Phase shift of a sinusoid (TR-123). -/
@[kb "corraltrig" "Box §5.2, p. 117"]
theorem box_5_2_phase_shift (A ω φ : ℝ) (hω : ω ≠ 0) (x : ℝ) :
    A * sin (ω * x - φ) = A * sin (ω * (x - φ / ω)) :=
  UndergradKB.Trigonometry.sinusoid_phase_shift A ω φ hω x

/-- Phase shift of a sinusoid (TR-123). -/
@[kb "corraltrig" "Example 5.11-5.12, p. 117"]
theorem ex_5_11_phase_shift (A ω φ : ℝ) (hω : ω ≠ 0) (x : ℝ) :
    A * sin (ω * x - φ) = A * sin (ω * (x - φ / ω)) :=
  UndergradKB.Trigonometry.sinusoid_phase_shift A ω φ hω x

/-- Periods of $\sin\omega x$, $\cos\omega x$, $\tan\omega x$ (TR-124). -/
@[kb "corraltrig" "Box §5.2, p. 118"]
theorem box_5_2_period_of_scaled_functions {ω : ℝ} (hω : 0 < ω) :
    IsLeast {p | 0 < p ∧ Function.Periodic (fun x => sin (ω * x)) p} (2 * π / ω) ∧ IsLeast {p | 0 < p ∧
      Function.Periodic (fun x => cos (ω * x)) p} (2 * π / ω) ∧ IsLeast {p | 0 < p ∧ Function.Periodic (fun x => tan
      (ω * x)) p} (π / ω) :=
  ⟨UndergradKB.Trigonometry.isLeast_period_sin_mul hω, UndergradKB.Trigonometry.isLeast_period_cos_mul hω,
    UndergradKB.Trigonometry.isLeast_period_tan_mul hω⟩

/-- Periods of $\sin\omega x$, $\cos\omega x$, $\tan\omega x$ (TR-124). -/
@[kb "corraltrig" "Example 5.4, p. 117"]
theorem ex_5_4_period_of_scaled_functions {ω : ℝ} (hω : 0 < ω) :
    IsLeast {p | 0 < p ∧ Function.Periodic (fun x => sin (ω * x)) p} (2 * π / ω) ∧ IsLeast {p | 0 < p ∧
      Function.Periodic (fun x => cos (ω * x)) p} (2 * π / ω) ∧ IsLeast {p | 0 < p ∧ Function.Periodic (fun x => tan
      (ω * x)) p} (π / ω) :=
  ⟨UndergradKB.Trigonometry.isLeast_period_sin_mul hω, UndergradKB.Trigonometry.isLeast_period_cos_mul hω,
    UndergradKB.Trigonometry.isLeast_period_tan_mul hω⟩

/-- Amplitude, period and phase shift of a general sinusoid (TR-126). -/
@[kb "corraltrig" "Box §5.2 (general sinusoid), p. 118"]
theorem box_5_2_amplitude_period_phase (A B C D : ℝ) (hB : 0 < B) :
    UndergradKB.Trigonometry.amplitude (fun x => A * sin (B * x - C) + D) = |A| ∧ IsLeast {p | 0 < p ∧
      Function.Periodic (fun x => sin (B * x)) p} (2 * π / B) ∧ ∀ x, A * sin (B * x - C) = A * sin (B * (x - C / B))
      :=
  ⟨UndergradKB.Trigonometry.amplitude_sinusoid A B C D hB.ne', UndergradKB.Trigonometry.isLeast_period_sin_mul hB,
    fun x => UndergradKB.Trigonometry.sinusoid_phase_shift A B C hB.ne' x⟩

/-- Amplitude of a sinusoid is the absolute value of its coefficient (TR-127). -/
@[kb "corraltrig" "Box §5.2, p. 119"]
theorem box_5_2_amplitude (A B C D : ℝ) (hB : B ≠ 0) :
    UndergradKB.Trigonometry.amplitude (fun x => A * sin (B * x - C) + D) = |A| ∧ range (fun x => A * sin (B * x -
      C) + D) = Icc (D - |A|) (D + |A|) :=
  ⟨UndergradKB.Trigonometry.amplitude_sinusoid A B C D hB, UndergradKB.Trigonometry.range_sinusoid A B C D hB⟩

/-- The inverse cotangent (TR-154). -/
@[kb "corraltrig" "Box §5.3, p. 126 (eqs 5.8, 5.9)"]
theorem box_5_3_arccot :
    InjOn cot (Ioo 0 π) ∧ (∀ x, UndergradKB.Trigonometry.arccot x ∈ Ioo 0 π) ∧ (∀ x, cot
      (UndergradKB.Trigonometry.arccot x) = x) ∧ ∀ y ∈ Ioo 0 π, UndergradKB.Trigonometry.arccot (cot y) = y :=
  UndergradKB.Trigonometry.arccot_spec

/-- The inverse secant and cosecant (TR-155). -/
@[kb "corraltrig" "Box §5.3, p. 126 (eqs 5.10-5.13)"]
theorem box_5_3_arcsec_arccsc :
    ((∀ x : ℝ, 1 ≤ |x| → UndergradKB.Trigonometry.arcsec x ∈ Icc 0 π ∧ UndergradKB.Trigonometry.arcsec x ≠ π / 2 ∧
      UndergradKB.Trigonometry.sec (UndergradKB.Trigonometry.arcsec x) = x) ∧ ∀ y ∈ Icc 0 π, y ≠ π / 2 →
      UndergradKB.Trigonometry.arcsec (UndergradKB.Trigonometry.sec y) = y) ∧ ((∀ x : ℝ, 1 ≤ |x| →
      UndergradKB.Trigonometry.arccsc x ∈ Icc (-(π / 2)) (π / 2) ∧ UndergradKB.Trigonometry.arccsc x ≠ 0 ∧
      UndergradKB.Trigonometry.csc (UndergradKB.Trigonometry.arccsc x) = x) ∧ ∀ y ∈ Icc (-(π / 2)) (π / 2), y ≠ 0 →
      UndergradKB.Trigonometry.arccsc (UndergradKB.Trigonometry.csc y) = y) :=
  ⟨UndergradKB.Trigonometry.arcsec_spec, UndergradKB.Trigonometry.arccsc_spec⟩

/-- Arctangent plus arccotangent is pi/2 (TR-156). -/
@[kb "corraltrig" "Example 5.21, p. 127"]
theorem ex_5_21_arctan_add_arccot (x : ℝ) :
    arctan x + UndergradKB.Trigonometry.arccot x = π / 2 :=
  UndergradKB.Trigonometry.arctan_add_arccot x

/-- Lines are perpendicular iff their slopes have product minus one (TR-164). -/
@[kb "corraltrig" "Ex 1.26, p. 41"]
theorem ex_1_26_perpendicular_slopes (m₁ m₂ : ℝ) :
    inner ℝ (!₂[(1 : ℝ), m₁]) (!₂[(1 : ℝ), m₂]) = 0 ↔ m₁ * m₂ = -1 :=
  UndergradKB.Trigonometry.inner_slope_vectors_eq_zero_iff m₁ m₂

/-- Adding multiples of the period to a solution gives solutions (TR-165). -/
@[kb "corraltrig" "Box §6.1, p. 137"]
theorem box_6_1_general_solution {f : ℝ → ℝ} {p a x : ℝ} (hf : Function.Periodic f p) (hx : f x = a) (k : ℤ) :
    f (x + k * p) = a :=
  UndergradKB.Trigonometry.periodic_solutions hf hx k

/-- Solving $a\sin t + b\cos t = c$ via a single sinusoid (TR-169). -/
@[kb "corraltrig" "Example 6.8, p. 140"]
theorem ex_6_8_sin_cos_equation (a b : ℝ) (hab : a ≠ 0 ∨ b ≠ 0) :
    ∃ φ : ℝ, cos φ = a / √(a ^ 2 + b ^ 2) ∧ sin φ = b / √(a ^ 2 + b ^ 2) ∧ ∀ x, a * sin x + b * cos x = √(a ^ 2 + b
      ^ 2) * sin (x + φ) :=
  UndergradKB.Trigonometry.exists_amplitude_phase a b hab

/-- Iterating the cosine converges to its fixed point (TR-171). -/
@[kb "corraltrig" "D033, p. 144"]
theorem d033_cosine_iteration {c : ℝ} (hc : cos c = c) (x₀ : ℝ) :
    Filter.Tendsto (fun n : ℕ => cos^[n] x₀) Filter.atTop (nhds c) :=
  UndergradKB.Trigonometry.tendsto_iterate_cos hc x₀

/-- The equation $\cos x = x$ has exactly one real solution (TR-171). -/
@[kb "corraltrig" "Box §6.2 (cos x = x), p. 141"]
theorem box_6_2_cos_eq_x :
    ∃! c : ℝ, cos c = c ∧ c ∈ Icc (0.72 : ℝ) 0.76 :=
  UndergradKB.Trigonometry.exists_unique_cos_eq_self

/-- Any two solutions of $\cos x = x$ agree (TR-171). -/
@[kb "corraltrig" "Box §6.2 (cos x = x), p. 141"]
theorem box_6_2_cos_eq_x_unique {x y : ℝ} (hx : cos x = x) (hy : cos y = y) :
    x = y :=
  UndergradKB.Trigonometry.cos_eq_self_unique hx hy

/-- The argument is determined up to full turns (TR-187). -/
@[kb "corraltrig" "Box §6.3, p. 149"]
theorem box_6_3_argument_up_to_turns {r r' α β : ℝ} (hr : 0 < r) (hr' : 0 < r') :
    (UndergradKB.Trigonometry.polarPoint r α = UndergradKB.Trigonometry.polarPoint r' β → ∃ k : ℤ, β = α + k * (2 *
      π)) ∧ (UndergradKB.Trigonometry.polarPoint r α = UndergradKB.Trigonometry.polarPoint r' β ↔ r = r' ∧ ∃ k : ℤ,
      β = α + k * (2 * π)) :=
  ⟨UndergradKB.Trigonometry.eq_add_int_mul_two_pi_of_polarPoint_eq hr hr',
    UndergradKB.Trigonometry.polarPoint_eq_iff hr hr'⟩

/-- Moduli multiply and arguments add (TR-188). -/
@[kb "corraltrig" "Box §6.3 (6.5), p. 150"]
theorem box_6_3_polar_product (r₁ r₂ α β : ℝ) :
    (r₁ * (Real.cos α + Real.sin α * Complex.I)) * (r₂ * (Real.cos β + Real.sin β * Complex.I)) = (r₁ * r₂ : ℝ) *
      (Real.cos (α + β) + Real.sin (α + β) * Complex.I) :=
  UndergradKB.Trigonometry.cis_mul_cis r₁ r₂ α β

/-- Moduli divide and arguments subtract (TR-189). -/
@[kb "corraltrig" "Box §6.3 (6.6), p. 150"]
theorem box_6_3_polar_quotient (r₁ : ℝ) {r₂ : ℝ} (h : r₂ ≠ 0) (α β : ℝ) :
    (r₁ * (Real.cos α + Real.sin α * Complex.I)) / (r₂ * (Real.cos β + Real.sin β * Complex.I)) = (r₁ / r₂ : ℝ) *
      (Real.cos (α - β) + Real.sin (α - β) * Complex.I) :=
  UndergradKB.Trigonometry.cis_div_cis r₁ h α β

/-- De Moivre's theorem (TR-190). -/
@[kb "corraltrig" "Thm 6.1, p. 151"]
theorem thm_6_1_de_moivre (r θ : ℝ) (n : ℤ) :
    (r * (Real.cos θ + Real.sin θ * Complex.I)) ^ n = (r ^ n : ℝ) * (Real.cos (n * θ) + Real.sin (n * θ) *
      Complex.I) :=
  UndergradKB.Trigonometry.de_moivre r θ n

/-- The $n$th roots of a complex number in polar form (TR-191). -/
@[kb "corraltrig" "Box §6.3 (6.8), p. 152"]
theorem box_6_3_nth_roots {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    {z : ℂ | z ^ n = (r : ℂ) * ((Real.cos θ : ℝ) + (Real.sin θ : ℝ) * Complex.I)} = ↑((Finset.range n).image
      (UndergradKB.Trigonometry.nthRootPolar n r θ)) :=
  UndergradKB.Trigonometry.nthRoots_eq_image hn hr θ

/-- The candidate roots are roots and are distinct (TR-191). -/
@[kb "corraltrig" "Box §6.3 (6.8), p. 152"]
theorem box_6_3_nth_roots_distinct {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    (∀ k : ℕ, (UndergradKB.Trigonometry.nthRootPolar n r θ k) ^ n = (r : ℂ) * ((Real.cos θ : ℝ) + (Real.sin θ : ℝ) *
      Complex.I)) ∧ Set.InjOn (UndergradKB.Trigonometry.nthRootPolar n r θ) (Finset.range n : Set ℕ) :=
  ⟨fun k => UndergradKB.Trigonometry.nthRootPolar_pow hn hr θ k, UndergradKB.Trigonometry.nthRootPolar_injOn hn hr
    θ⟩

/-- The $n$th roots lie equally spaced on a circle (TR-192). -/
@[kb "corraltrig" "Box §6.3, p. 153"]
theorem box_6_3_roots_equally_spaced {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    (∀ k : ℕ, ‖UndergradKB.Trigonometry.nthRootPolar n r θ k‖ = r ^ (1 / n : ℝ)) ∧ ∀ k : ℕ,
      UndergradKB.Trigonometry.nthRootPolar n r θ (k + 1) = UndergradKB.Trigonometry.nthRootPolar n r θ k *
      ((Real.cos (2 * π / n) : ℝ) + (Real.sin (2 * π / n) : ℝ) * Complex.I) :=
  ⟨fun k => UndergradKB.Trigonometry.norm_nthRootPolar n hr θ k, fun k => UndergradKB.Trigonometry.nthRootPolar_succ
    hn r θ k⟩

/-- Polar coordinates are determined up to full turns (TR-194). -/
@[kb "corraltrig" "D037, p. 154"]
theorem d037_polar_coordinates_not_unique {r r' α β : ℝ} (hr : 0 < r) (hr' : 0 < r') :
    (UndergradKB.Trigonometry.polarPoint r α = UndergradKB.Trigonometry.polarPoint r' β → ∃ k : ℤ, β = α + k * (2 *
      π)) ∧ (UndergradKB.Trigonometry.polarPoint r α = UndergradKB.Trigonometry.polarPoint r' β ↔ r = r' ∧ ∃ k : ℤ,
      β = α + k * (2 * π)) :=
  ⟨UndergradKB.Trigonometry.eq_add_int_mul_two_pi_of_polarPoint_eq hr hr',
    UndergradKB.Trigonometry.polarPoint_eq_iff hr hr'⟩

/-- Negative and zero radius in polar coordinates (TR-195). -/
@[kb "corraltrig" "Box §6.4, p. 154"]
theorem box_6_4_negative_radius_convention (r θ : ℝ) :
    UndergradKB.Trigonometry.polarPoint (-r) θ = UndergradKB.Trigonometry.polarPoint r (θ + π) ∧
      UndergradKB.Trigonometry.polarPoint r (θ + 2 * π) = UndergradKB.Trigonometry.polarPoint r θ ∧
      UndergradKB.Trigonometry.polarPoint 0 θ = 0 :=
  ⟨UndergradKB.Trigonometry.polarPoint_neg_eq_add_pi r θ, UndergradKB.Trigonometry.polarPoint_add_two_pi r θ,
    UndergradKB.Trigonometry.polarPoint_zero_radius θ⟩

/-- Radius and tangent of the angle from rectangular coordinates (TR-197). -/
@[kb "corraltrig" "Box §6.4 (6.10), p. 157"]
theorem box_6_4_polar_to_rectangular_radius {r θ : ℝ} (hr : r ≠ 0) :
    (UndergradKB.Trigonometry.polarPoint r θ).re ^ 2 + (UndergradKB.Trigonometry.polarPoint r θ).im ^ 2 = r ^ 2 ∧
      tan θ = (UndergradKB.Trigonometry.polarPoint r θ).im / (UndergradKB.Trigonometry.polarPoint r θ).re :=
  ⟨UndergradKB.Trigonometry.polarPoint_sq_add_sq r θ, UndergradKB.Trigonometry.tan_eq_im_div_re hr⟩

/-- Distance between points in polar coordinates (TR-198). -/
@[kb "corraltrig" "Example 6.20 (6.11), p. 159"]
theorem ex_6_20_distance_in_polar_coordinates (r₁ θ₁ r₂ θ₂ : ℝ) :
    dist ((r₁ * Real.cos θ₁ : ℝ) + (r₁ * Real.sin θ₁ : ℝ) * Complex.I) ((r₂ * Real.cos θ₂ : ℝ) + (r₂ * Real.sin θ₂ :
      ℝ) * Complex.I) = √(r₁ ^ 2 + r₂ ^ 2 - 2 * r₁ * r₂ * Real.cos (θ₁ - θ₂)) :=
  UndergradKB.Trigonometry.dist_polar r₁ θ₁ r₂ θ₂

/-- Every nonzero angle is exactly one of acute, right, obtuse, straight (TR-001). -/
@[kb "corraltrig" "Box §1.1, p. 9"]
theorem box_1_1_kinds_of_angles {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] (A O B : P) (h : 0 < ∠ A O B) :
    (UndergradKB.Trigonometry.IsAcuteAngle (∠ A O B) ∨ UndergradKB.Trigonometry.IsRightAngle (∠ A O B) ∨
      UndergradKB.Trigonometry.IsObtuseAngle (∠ A O B) ∨ UndergradKB.Trigonometry.IsStraightAngle (∠ A O B)) ∧ ¬
      (UndergradKB.Trigonometry.IsAcuteAngle (∠ A O B) ∧ UndergradKB.Trigonometry.IsRightAngle (∠ A O B)) ∧ ¬
      (UndergradKB.Trigonometry.IsAcuteAngle (∠ A O B) ∧ UndergradKB.Trigonometry.IsObtuseAngle (∠ A O B)) ∧ ¬
      (UndergradKB.Trigonometry.IsAcuteAngle (∠ A O B) ∧ UndergradKB.Trigonometry.IsStraightAngle (∠ A O B)) ∧ ¬
      (UndergradKB.Trigonometry.IsRightAngle (∠ A O B) ∧ UndergradKB.Trigonometry.IsObtuseAngle (∠ A O B)) ∧ ¬
      (UndergradKB.Trigonometry.IsRightAngle (∠ A O B) ∧ UndergradKB.Trigonometry.IsStraightAngle (∠ A O B)) ∧ ¬
      (UndergradKB.Trigonometry.IsObtuseAngle (∠ A O B) ∧ UndergradKB.Trigonometry.IsStraightAngle (∠ A O B)) :=
  UndergradKB.Trigonometry.angle_kind_unique A O B h

/-- A triangle has at least two acute angles (TR-001). -/
@[kb "corraltrig" "Box §1.1, p. 9"]
theorem box_1_1_two_acute_angles {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] {p₁ p₂ p₃ : P} (h12 : p₂ ≠ p₁) (h1 : 0 < ∠ p₁ p₂ p₃) (h2 : 0 < ∠ p₂ p₃ p₁) (h3 : 0 < ∠ p₃
    p₁ p₂) :
    (UndergradKB.Trigonometry.IsAcuteAngle (∠ p₁ p₂ p₃) ∧ UndergradKB.Trigonometry.IsAcuteAngle (∠ p₂ p₃ p₁)) ∨
      (UndergradKB.Trigonometry.IsAcuteAngle (∠ p₂ p₃ p₁) ∧ UndergradKB.Trigonometry.IsAcuteAngle (∠ p₃ p₁ p₂)) ∨
      (UndergradKB.Trigonometry.IsAcuteAngle (∠ p₁ p₂ p₃) ∧ UndergradKB.Trigonometry.IsAcuteAngle (∠ p₃ p₁ p₂)) :=
  UndergradKB.Trigonometry.two_angles_acute h12 h1 h2 h3

/-- Sine and cosine of complementary, supplementary and conjugate angles (TR-002). -/
@[kb "corraltrig" "Box §1.1, p. 10"]
theorem box_1_1_complementary_supplementary_conjugate {α β : ℝ} :
    (UndergradKB.Trigonometry.AreComplementary α β → sin β = cos α ∧ cos β = sin α) ∧
      (UndergradKB.Trigonometry.AreSupplementary α β → sin β = sin α ∧ cos β = - cos α) ∧
      (UndergradKB.Trigonometry.AreConjugate α β → sin β = - sin α ∧ cos β = cos α) :=
  ⟨fun h => UndergradKB.Trigonometry.sin_cos_of_complementary h, fun h =>
    UndergradKB.Trigonometry.sin_cos_of_supplementary h, fun h => UndergradKB.Trigonometry.sin_cos_of_conjugate h⟩

/-- The angles of a linear pair are supplementary (TR-002). -/
@[kb "corraltrig" "Box §1.1, p. 10"]
theorem box_1_1_linear_pair_supplementary {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace
    P] [NormedAddTorsor V P] {A O C : P} (B : P) (h : Sbtw ℝ A O C) :
    UndergradKB.Trigonometry.AreSupplementary (∠ A O B) (∠ B O C) :=
  UndergradKB.Trigonometry.areSupplementary_angle_of_sbtw B h

/-- A minute is 1/60 of a degree and a second is 1/60 of a minute (TR-004). -/
@[kb "corraltrig" "Box §1.3, p. 24"]
theorem box_1_3_minutes_seconds :
    UndergradKB.Trigonometry.dmsToDeg 0 1 0 = 1 / 60 ∧ UndergradKB.Trigonometry.dmsToDeg 0 0 1 =
      UndergradKB.Trigonometry.dmsToDeg 0 (1 / 60) 0 ∧ ∀ d m s : ℝ, UndergradKB.Trigonometry.degToRad
      (UndergradKB.Trigonometry.dmsToDeg d m s) = π * (d + m / 60 + s / 3600) / 180 :=
  ⟨UndergradKB.Trigonometry.dmsToDeg_minute_second.1, UndergradKB.Trigonometry.dmsToDeg_minute_second.2, fun d m s
    => UndergradKB.Trigonometry.degToRad_dmsToDeg d m s⟩

/-- An angle in standard position is a rotation of the initial side (TR-005). -/
@[kb "corraltrig" "Def §1.4, p. 32"]
theorem def_1_4_standard_position (θ : ℝ) :
    Complex.exp (θ * Complex.I) * 1 = UndergradKB.Trigonometry.polarPoint 1 θ ∧ ((Complex.arg (Complex.exp (θ *
      Complex.I)) : ℝ) : Real.Angle) = (θ : Real.Angle) ∧ (∀ z : ℂ, z ≠ 0 → ((Complex.arg (Complex.exp (θ *
      Complex.I) * z) : ℝ) : Real.Angle) = (Complex.arg z : ℝ) + (θ : Real.Angle)) ∧ (0 < θ → θ < π → 0 <
      (Complex.exp (θ * Complex.I)).im) ∧ (-π < θ → θ < 0 → (Complex.exp (θ * Complex.I)).im < 0) :=
  UndergradKB.Trigonometry.standardPosition θ

/-- A gradian is 1/400 of a full turn (TR-007). -/
@[kb "corraltrig" "Box §4.1, p. 96 (footnote)"]
theorem box_4_1_gradians :
    UndergradKB.Trigonometry.gradToRad 400 = 2 * π ∧ UndergradKB.Trigonometry.gradToRad 100 = π / 2 ∧
      UndergradKB.Trigonometry.gradToRad 100 = UndergradKB.Trigonometry.degToRad 90 :=
  UndergradKB.Trigonometry.gradToRad_spec

/-- The hypotenuse is the longest side of a right triangle (TR-012). -/
@[kb "corraltrig" "Def §1.1, p. 12"]
theorem def_1_1_hypotenuse_legs {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) (h12 : p₁ ≠ p₂) (h32 : p₃ ≠ p₂) :
    dist p₁ p₂ < dist p₁ p₃ ∧ dist p₃ p₂ < dist p₁ p₃ ∧ dist p₁ p₃ ^ 2 = dist p₁ p₂ ^ 2 + dist p₃ p₂ ^ 2 :=
  UndergradKB.Trigonometry.hypotenuse_longest h h12 h32

/-- The six functions from a point on the terminal side (TR-023). -/
@[kb "corraltrig" "Box §1.4, p. 33"]
theorem box_1_4_functions_of_terminal_point {x y r θ : ℝ} (hr : 0 < r) (hx : x = r * cos θ) (hy : y = r * sin θ) :
    r = √(x ^ 2 + y ^ 2) ∧ sin θ = y / r ∧ cos θ = x / r ∧ tan θ = y / x ∧ UndergradKB.Trigonometry.csc θ = r / y ∧
      UndergradKB.Trigonometry.sec θ = r / x ∧ cot θ = x / y :=
  UndergradKB.Trigonometry.trig_of_point hr hx hy

/-- The six functions at 0, 90, 180, 270 degrees (TR-026). -/
@[kb "corraltrig" "Ex 1.23, p. 36"]
theorem ex_1_23_values_at_quadrantal_angles :
    (sin 0 = 0 ∧ cos 0 = 1 ∧ tan 0 = 0 ∧ UndergradKB.Trigonometry.sec 0 = 1) ∧ (sin (π / 2) = 1 ∧ cos (π / 2) = 0 ∧
      cot (π / 2) = 0 ∧ UndergradKB.Trigonometry.csc (π / 2) = 1) ∧ (sin π = 0 ∧ cos π = -1 ∧ tan π = 0 ∧
      UndergradKB.Trigonometry.sec π = -1) ∧ (sin (3 * π / 2) = -1 ∧ cos (3 * π / 2) = 0 ∧ cot (3 * π / 2) = 0 ∧
      UndergradKB.Trigonometry.csc (3 * π / 2) = -1) :=
  UndergradKB.Trigonometry.six_functions_quadrantal

/-- A point of the unit circle at angle t is (cos t, sin t) (TR-036). -/
@[kb "corraltrig" "Box §5.1, p. 110"]
theorem box_5_1_unit_circle_point {t : ℝ} (ht : 0 ≤ t) :
    eVariationOn (fun φ : ℝ => Complex.exp (φ * Complex.I)) (Icc 0 t) = ENNReal.ofReal t ∧ Complex.exp (t *
      Complex.I) = ⟨cos t, sin t⟩ ∧ ‖Complex.exp (t * Complex.I)‖ = 1 :=
  UndergradKB.Trigonometry.unitCircle_arc_point ht

/-- Area of the segment cut off by a chord (TR-086). -/
@[kb "corraltrig" "Box §4.3, p. 104"]
theorem box_4_3_circular_segment_area {r θ : ℝ} (hr : 0 < r) (hθ : 0 ≤ θ) (hθ' : θ ≤ 2 * π) :
    MeasureTheory.volume (UndergradKB.Trigonometry.circSegment r θ) = ENNReal.ofReal (r ^ 2 * (θ - sin θ) / 2) :=
  UndergradKB.Trigonometry.volume_circSegment hr hθ hθ'

/-- Average linear speed (TR-106). -/
@[kb "corraltrig" "Box §4.4, p. 107"]
theorem box_4_4_average_linear_speed (c : ℂ) {r ω t : ℝ} (hr : 0 ≤ r) (hω : 0 ≤ ω) (ht : 0 < t) :
    UndergradKB.Trigonometry.avgLinearSpeed (eVariationOn (fun τ : ℝ => c + r * Complex.exp ((ω * τ : ℝ) *
      Complex.I)) (Icc 0 t)).toReal t = ω * r :=
  UndergradKB.Trigonometry.avgLinearSpeed_uniform_circular c hr hω ht

/-- Average angular speed (TR-107). -/
@[kb "corraltrig" "Box §4.4, p. 107"]
theorem box_4_4_average_angular_speed (c : ℂ) {r ω t : ℝ} (hr : 0 ≤ r) (hω : 0 ≤ ω) (ht : 0 < t) :
    UndergradKB.Trigonometry.avgAngularSpeed (ω * t) t = ω ∧ UndergradKB.Trigonometry.avgLinearSpeed (eVariationOn
      (fun τ : ℝ => c + r * Complex.exp ((ω * τ : ℝ) * Complex.I)) (Icc 0 t)).toReal t = r *
      UndergradKB.Trigonometry.avgAngularSpeed (ω * t) t :=
  UndergradKB.Trigonometry.avgAngularSpeed_uniform_circular c hr hω ht

/-- Revolutions per minute and radians per second (TR-109). -/
@[kb "corraltrig" "Box §4.4, p. 108"]
theorem box_4_4_revolutions_per_minute :
    (∀ N, UndergradKB.Trigonometry.radPerSecToRpm (UndergradKB.Trigonometry.rpmToRadPerSec N) = N) ∧ (∀ w,
      UndergradKB.Trigonometry.rpmToRadPerSec (UndergradKB.Trigonometry.radPerSecToRpm w) = w) ∧
      UndergradKB.Trigonometry.rpmToRadPerSec 1 = 2 * π / 60 :=
  UndergradKB.Trigonometry.rpm_conversions

/-- Meshing gears (TR-110). -/
@[kb "corraltrig" "Box §4.4, p. 109 (eq 4.11)"]
theorem box_4_4_meshing_gears (c₁ c₂ : ℂ) {r₁ r₂ ω₁ ω₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hω₁ : 0 ≤ ω₁) (hω₂ : 0 ≤
    ω₂) :
    (∀ t : ℝ, 0 ≤ t → eVariationOn (fun τ : ℝ => c₁ + r₁ * Complex.exp ((ω₁ * τ : ℝ) * Complex.I)) (Icc 0 t) =
      eVariationOn (fun τ : ℝ => c₂ + r₂ * Complex.exp ((ω₂ * τ : ℝ) * Complex.I)) (Icc 0 t)) ↔ ω₁ * r₁ = ω₂ * r₂ :=
  UndergradKB.Trigonometry.gears_equal_distance_iff c₁ c₂ hr₁ hr₂ hω₁ hω₂

/-- Sinusoids are in phase iff their phase shifts agree modulo the period (TR-125). -/
@[kb "corraltrig" "Box §5.2, p. 118"]
theorem box_5_2_in_phase {A A' ω c₁ c₂ : ℝ} (hA : 0 < A) (hA' : 0 < A') (hω : 0 < ω) :
    UndergradKB.Trigonometry.InPhase (fun x => A * sin (ω * (x - c₁))) (fun x => A' * sin (ω * (x - c₂))) ↔ ∃ k : ℤ,
      c₁ - c₂ = k * (2 * π / ω) :=
  UndergradKB.Trigonometry.inPhase_sin_iff hA hA' hω

/-- Leading and lagging sinusoids (TR-125). -/
@[kb "corraltrig" "Box §5.2, p. 118"]
theorem box_5_2_leading_lagging (ω c₁ c₂ : ℝ) :
    UndergradKB.Trigonometry.Leads (fun x => sin (ω * (x - c₁))) (fun x => sin (ω * (x - c₂))) (c₂ - c₁) :=
  UndergradKB.Trigonometry.leads_sin_shift ω c₁ c₂

/-- The limit of the secant method is a root (TR-170). -/
@[kb "corraltrig" "D032, p. 142"]
theorem d032_secant_method_limit {f : ℝ → ℝ} {K : NNReal} (hf : LipschitzWith K f) {x₀ x₁ L : ℝ} (hne : ∀ n, f
    (secantSeq f x₀ x₁ (n + 1)) ≠ f (secantSeq f x₀ x₁ n)) (hL : Filter.Tendsto (secantSeq f x₀ x₁) Filter.atTop
    (nhds L)) :
    f L = 0 :=
  UndergradKB.Trigonometry.secantSeq_limit_root hf hne hL

/-- The secant step is the intercept of the secant line (TR-170). -/
@[kb "corraltrig" "Box §6.2, p. 142"]
theorem box_6_2_secant_step (f : ℝ → ℝ) {x y : ℝ} (hxy : x ≠ y) (hf : f x ≠ f y) :
    f x + (f x - f y) / (x - y) * (UndergradKB.Trigonometry.secantStep f x y - x) = 0 :=
  UndergradKB.Trigonometry.secantLine_secantStep f hxy hf

/-- The secant method is exact for a linear function (TR-170). -/
@[kb "corraltrig" "Box §6.2, p. 142"]
theorem box_6_2_secant_step_exact_for_lines {m q x y : ℝ} (hm : m ≠ 0) (hxy : x ≠ y) :
    UndergradKB.Trigonometry.secantStep (fun t => m * t + q) x y = -q / m :=
  UndergradKB.Trigonometry.secantStep_affine hm hxy

end UndergradKB.Trigonometry.Course.Corral
