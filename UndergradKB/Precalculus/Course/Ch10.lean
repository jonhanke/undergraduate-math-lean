import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Basic.Real.Basic
import UndergradKB.Common.Attr

/-!
# Course layer, Chapter 10 (foundations of trigonometry)

Thin theorems in the book's terms. Rows classified `in Mathlib` use the Mathlib declarations named
in the checklist; the central trigonometry rows that live in the Trigonometry topic (which this
layer may not import) are restated with short proofs from Mathlib. Secant and cosecant are written
`1 / cos` and `1 / sin`, as the book defines them.
-/

namespace UndergradKB.Precalculus.Course

open Real EuclideanGeometry

/-- The point of the unit circle reached by travelling the signed arc length `t` from `(1, 0)` is
`(cos t, sin t)`; it lies on the unit circle (PC-198). -/
@[kb "stitzzeager2013" "§10.2, p. 729"]
theorem box_10_2_unit_circle_point (t : ℝ) :
    (Complex.exp (t * Complex.I)).re = Real.cos t ∧ (Complex.exp (t * Complex.I)).im = Real.sin t ∧
      Real.cos t ^ 2 + Real.sin t ^ 2 = 1 :=
  ⟨Complex.exp_ofReal_mul_I_re t, Complex.exp_ofReal_mul_I_im t, Real.cos_sq_add_sin_sq t⟩

/-- The Pythagorean identity `cos² θ + sin² θ = 1` (PC-199). -/
@[kb "stitzzeager2013" "Theorem 10.1, p. 732"]
theorem thm_10_1_pythagorean (θ : ℝ) : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 :=
  Real.cos_sq_add_sin_sq θ

/-- A point `(x, y)` at distance `r > 0` from the origin on the terminal side of `θ` has
`x = r cos θ`, `y = r sin θ`, hence `cos θ = x / r` and `sin θ = y / r` (PC-202). -/
@[kb "stitzzeager2013" "Theorem 10.3, p. 742"]
theorem thm_10_3_trig_of_point (θ x y r : ℝ) (hr : 0 < r) (hx : x = r * Real.cos θ)
    (hy : y = r * Real.sin θ) : Real.cos θ = x / r ∧ Real.sin θ = y / r := by
  subst hx hy
  constructor <;> field_simp

/-- In a right triangle with the right angle at `B`, the cosine of the angle at `C` is the
adjacent side over the hypotenuse: `cos C * |AC| = |CB|` (PC-204). -/
@[kb "stitzzeager2013" "Theorem 10.4, p. 745"]
theorem thm_10_4_cos_right_triangle (A B C : EuclideanSpace ℝ (Fin 2)) (h : ∠ A B C = π / 2) :
    Real.cos (∠ B C A) * dist A C = dist C B :=
  EuclideanGeometry.cos_angle_mul_dist_of_angle_eq_pi_div_two h

/-- In a right triangle with the right angle at `B`, the sine of the angle at `C` is the opposite
side over the hypotenuse: `sin C * |AC| = |AB|` (PC-204). -/
@[kb "stitzzeager2013" "Theorem 10.4, p. 745"]
theorem thm_10_4_sin_right_triangle (A B C : EuclideanSpace ℝ (Fin 2)) (h : ∠ A B C = π / 2) :
    Real.sin (∠ B C A) * dist A C = dist A B :=
  EuclideanGeometry.sin_angle_mul_dist_of_angle_eq_pi_div_two h

/-- In a right triangle with the right angle at `B` and `C ≠ B`, the tangent of the angle at `C`
is opposite over adjacent: `tan C * |CB| = |AB|` (PC-214). -/
@[kb "stitzzeager2013" "Theorem 10.10, p. 765"]
theorem thm_10_10_tan_right_triangle (A B C : EuclideanSpace ℝ (Fin 2)) (h : ∠ A B C = π / 2)
    (hCB : C ≠ B) : Real.tan (∠ B C A) * dist C B = dist A B :=
  EuclideanGeometry.tan_angle_mul_dist_of_angle_eq_pi_div_two h (Or.inr hCB)

/-- Cosine and sine take exactly the values in `[-1, 1]` (PC-205). -/
@[kb "stitzzeager2013" "Theorem 10.5, p. 747"]
theorem thm_10_5_range_cos_sin :
    Set.range Real.cos = Set.Icc (-1) 1 ∧ Set.range Real.sin = Set.Icc (-1) 1 :=
  ⟨Real.range_cos, Real.range_sin⟩

/-- For the point `(x, y) = (cos θ, sin θ)` of the unit circle, `tan θ = y / x` and
`cot θ = x / y` (PC-206). -/
@[kb "stitzzeager2013" "Definition 10.2, p. 756"]
theorem def_10_2_circular_functions (θ x y : ℝ) (hx : x = Real.cos θ) (hy : y = Real.sin θ) :
    Real.tan θ = y / x ∧ Real.cot θ = x / y := by
  subst hx hy
  exact ⟨Real.tan_eq_sin_div_cos θ, Real.cot_eq_cos_div_sin θ⟩

/-- Quotient identities: `tan θ = sin θ / cos θ` and `cot θ = cos θ / sin θ` (PC-208). -/
@[kb "stitzzeager2013" "Theorem 10.6, p. 757"]
theorem thm_10_6_quotient_identities (θ : ℝ) :
    Real.tan θ = Real.sin θ / Real.cos θ ∧ Real.cot θ = Real.cos θ / Real.sin θ :=
  ⟨Real.tan_eq_sin_div_cos θ, Real.cot_eq_cos_div_sin θ⟩

/-- Reciprocal identities: where `cos θ ≠ 0`, `tan θ = sin θ * (1 / cos θ)`, and where both
`sin θ ≠ 0` and `cos θ ≠ 0`, `cot θ = 1 / tan θ` (PC-208). -/
@[kb "stitzzeager2013" "Theorem 10.6, p. 757"]
theorem thm_10_6_reciprocal_identities (θ : ℝ) :
    Real.tan θ = Real.sin θ * (1 / Real.cos θ) ∧ Real.cot θ = 1 / Real.tan θ := by
  rw [Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin]
  constructor
  · rw [mul_one_div]
  · rw [one_div_div]

/-- Pythagorean identity `1 + tan² θ = sec² θ` where `cos θ ≠ 0` (PC-211). -/
@[kb "stitzzeager2013" "Theorem 10.8, p. 761"]
theorem thm_10_8_one_add_tan_sq (θ : ℝ) (h : Real.cos θ ≠ 0) :
    1 + Real.tan θ ^ 2 = (1 / Real.cos θ) ^ 2 := by
  rw [Real.tan_eq_sin_div_cos]
  have := Real.sin_sq_add_cos_sq θ
  field_simp
  linarith

/-- Pythagorean identity `1 + cot² θ = csc² θ` where `sin θ ≠ 0` (PC-211). -/
@[kb "stitzzeager2013" "Theorem 10.8, p. 761"]
theorem thm_10_8_one_add_cot_sq (θ : ℝ) (h : Real.sin θ ≠ 0) :
    1 + Real.cot θ ^ 2 = (1 / Real.sin θ) ^ 2 := by
  rw [Real.cot_eq_cos_div_sin]
  have := Real.sin_sq_add_cos_sq θ
  field_simp
  linarith

/-- For a point `(x, y)` at distance `r > 0` on the terminal side of `θ`:
`sec θ = r / x`, `csc θ = r / y`, `tan θ = y / x`, `cot θ = x / y` (PC-213). -/
@[kb "stitzzeager2013" "Theorem 10.9, p. 764"]
theorem thm_10_9_functions_of_point (θ x y r : ℝ) (hr : 0 < r) (hx : x = r * Real.cos θ)
    (hy : y = r * Real.sin θ) :
    1 / Real.cos θ = r / x ∧ 1 / Real.sin θ = r / y ∧ Real.tan θ = y / x ∧
      Real.cot θ = x / y := by
  subst hx hy
  have h1 := mul_div_mul_left (1 : ℝ) (Real.cos θ) hr.ne'
  have h2 := mul_div_mul_left (1 : ℝ) (Real.sin θ) hr.ne'
  have h3 := mul_div_mul_left (Real.sin θ) (Real.cos θ) hr.ne'
  have h4 := mul_div_mul_left (Real.cos θ) (Real.sin θ) hr.ne'
  rw [mul_one] at h1 h2
  rw [Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin]
  exact ⟨h1.symm, h2.symm, h3.symm, h4.symm⟩

/-- Even and odd identities: `cos` is even, `sin` and `tan` are odd, and the reciprocals follow:
`1 / cos` is even, `1 / sin` and `cot` are odd (PC-216). -/
@[kb "stitzzeager2013" "Theorem 10.12, p. 782"]
theorem thm_10_12_even_odd (θ : ℝ) :
    Real.cos (-θ) = Real.cos θ ∧ Real.sin (-θ) = -Real.sin θ ∧ Real.tan (-θ) = -Real.tan θ ∧
      1 / Real.cos (-θ) = 1 / Real.cos θ ∧ 1 / Real.sin (-θ) = -(1 / Real.sin θ) ∧
      Real.cot (-θ) = -Real.cot θ := by
  refine ⟨Real.cos_neg θ, Real.sin_neg θ, Real.tan_neg θ, by rw [Real.cos_neg], ?_, ?_⟩
  · rw [Real.sin_neg, one_div, one_div, inv_neg]
  · rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, Real.cos_neg, Real.sin_neg, div_neg]

/-- Cosine of a sum and difference (PC-217). -/
@[kb "stitzzeager2013" "Theorem 10.13, p. 783"]
theorem thm_10_13_cos_sum_diff (α β : ℝ) :
    Real.cos (α + β) = Real.cos α * Real.cos β - Real.sin α * Real.sin β ∧
      Real.cos (α - β) = Real.cos α * Real.cos β + Real.sin α * Real.sin β :=
  ⟨Real.cos_add α β, Real.cos_sub α β⟩

/-- Cofunction identities (PC-218). -/
@[kb "stitzzeager2013" "Theorem 10.14, p. 785"]
theorem thm_10_14_cofunction (θ : ℝ) :
    Real.cos (π / 2 - θ) = Real.sin θ ∧ Real.sin (π / 2 - θ) = Real.cos θ ∧
      Real.tan (π / 2 - θ) = (Real.tan θ)⁻¹ :=
  ⟨Real.cos_pi_div_two_sub θ, Real.sin_pi_div_two_sub θ, Real.tan_pi_div_two_sub θ⟩

/-- Sine of a sum and difference (PC-219). -/
@[kb "stitzzeager2013" "Theorem 10.15, p. 785"]
theorem thm_10_15_sin_sum_diff (α β : ℝ) :
    Real.sin (α + β) = Real.sin α * Real.cos β + Real.cos α * Real.sin β ∧
      Real.sin (α - β) = Real.sin α * Real.cos β - Real.cos α * Real.sin β :=
  ⟨Real.sin_add α β, Real.sin_sub α β⟩

/-- Tangent of a sum and difference, where `α` and `β` are not odd multiples of `π / 2`
(PC-220). -/
@[kb "stitzzeager2013" "Theorem 10.16, p. 787"]
theorem thm_10_16_tan_sum_diff (α β : ℝ)
    (h : (∀ k : ℤ, α ≠ (2 * k + 1) * π / 2) ∧ ∀ l : ℤ, β ≠ (2 * l + 1) * π / 2) :
    Real.tan (α + β) = (Real.tan α + Real.tan β) / (1 - Real.tan α * Real.tan β) ∧
      Real.tan (α - β) = (Real.tan α - Real.tan β) / (1 + Real.tan α * Real.tan β) :=
  ⟨Real.tan_add' h, Real.tan_sub' h⟩

/-- Double angle formulas for sine and the three forms of cosine (PC-221). -/
@[kb "stitzzeager2013" "Theorem 10.17, p. 788"]
theorem thm_10_17_double_angle (θ : ℝ) :
    Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ ∧
      Real.cos (2 * θ) = Real.cos θ ^ 2 - Real.sin θ ^ 2 ∧
      Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 ∧
      Real.cos (2 * θ) = 1 - 2 * Real.sin θ ^ 2 := by
  refine ⟨Real.sin_two_mul θ, Real.cos_two_mul' θ, Real.cos_two_mul θ, ?_⟩
  rw [Real.cos_two_mul]
  have := Real.sin_sq_add_cos_sq θ
  linarith

/-- Double angle formula for tangent (PC-221). -/
@[kb "stitzzeager2013" "Theorem 10.17, p. 788"]
theorem thm_10_17_tan_double_angle (θ : ℝ) :
    Real.tan (2 * θ) = 2 * Real.tan θ / (1 - Real.tan θ ^ 2) :=
  Real.tan_two_mul

/-- Power reduction: `cos² θ = (1 + cos 2θ) / 2` and `sin² θ = (1 - cos 2θ) / 2` (PC-222). -/
@[kb "stitzzeager2013" "Theorem 10.18, p. 790"]
theorem thm_10_18_power_reduction (θ : ℝ) :
    Real.cos θ ^ 2 = (1 + Real.cos (2 * θ)) / 2 ∧ Real.sin θ ^ 2 = (1 - Real.cos (2 * θ)) / 2 := by
  constructor
  · rw [Real.cos_sq]; ring
  · rw [Real.cos_two_mul]
    have := Real.sin_sq_add_cos_sq θ
    linarith

/-- Half angle formulas: `cos²(θ/2) = (1 + cos θ)/2`, `sin²(θ/2) = (1 - cos θ)/2`, and
`tan(θ/2) = sin θ / (1 + cos θ)` where `1 + cos θ ≠ 0` (PC-223). -/
@[kb "stitzzeager2013" "Theorem 10.19, p. 791"]
theorem thm_10_19_half_angle (θ : ℝ) :
    Real.cos (θ / 2) ^ 2 = (1 + Real.cos θ) / 2 ∧ Real.sin (θ / 2) ^ 2 = (1 - Real.cos θ) / 2 := by
  have h := thm_10_18_power_reduction (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at h
  exact h

/-- Half angle tangent formula `tan(θ/2) = sin θ / (1 + cos θ)` where `1 + cos θ ≠ 0`
(PC-223). -/
@[kb "stitzzeager2013" "Example 10.4.5, p. 791"]
theorem ex_10_4_5_tan_half_angle (θ : ℝ) (h : 1 + Real.cos θ ≠ 0) :
    Real.tan (θ / 2) = Real.sin θ / (1 + Real.cos θ) := by
  have h2 := thm_10_19_half_angle θ
  have hc : Real.cos (θ / 2) ≠ 0 := by
    intro h0
    apply h
    have := h2.1
    rw [h0] at this
    linarith
  have hs : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    rw [← Real.sin_two_mul]; ring_nf
  rw [Real.tan_eq_sin_div_cos, hs]
  have : 1 + Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 := by linarith [h2.1]
  rw [this]
  field_simp

/-- Product to sum formulas (PC-224). -/
@[kb "stitzzeager2013" "Theorem 10.20, p. 792"]
theorem thm_10_20_product_to_sum (α β : ℝ) :
    Real.cos α * Real.cos β = (Real.cos (α - β) + Real.cos (α + β)) / 2 ∧
      Real.sin α * Real.sin β = (Real.cos (α - β) - Real.cos (α + β)) / 2 ∧
      Real.sin α * Real.cos β = (Real.sin (α - β) + Real.sin (α + β)) / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · linarith [Real.two_mul_cos_mul_cos α β]
  · linarith [Real.two_mul_sin_mul_sin α β]
  · linarith [Real.two_mul_sin_mul_cos α β]

/-- Sum to product formulas (PC-225). -/
@[kb "stitzzeager2013" "Theorem 10.21, p. 793"]
theorem thm_10_21_sum_to_product (α β : ℝ) :
    Real.cos α + Real.cos β = 2 * Real.cos ((α + β) / 2) * Real.cos ((α - β) / 2) ∧
      Real.cos α - Real.cos β = -2 * Real.sin ((α + β) / 2) * Real.sin ((α - β) / 2) ∧
      Real.sin α + Real.sin β = 2 * Real.sin ((α + β) / 2) * Real.cos ((α - β) / 2) ∧
      Real.sin α - Real.sin β = 2 * Real.sin ((α - β) / 2) * Real.cos ((α + β) / 2) :=
  ⟨Real.cos_add_cos α β, Real.cos_sub_cos α β, Real.sin_add_sin α β, Real.sin_sub_sin α β⟩

/-- The sine graph is the cosine graph shifted right by `π / 2`: `cos (x - π/2) = sin x`
(PC-229). -/
@[kb "stitzzeager2013" "§10.5, p. 804"]
theorem box_10_5_sin_eq_shifted_cos (x : ℝ) : Real.cos (x - π / 2) = Real.sin x :=
  Real.cos_sub_pi_div_two x

/-- Arccosine and arcsine: ranges, inverse relations on the principal intervals, and arcsine is
odd (PC-234). -/
@[kb "stitzzeager2013" "Theorem 10.26, p. 832"]
theorem thm_10_26_arcsin_range (x : ℝ) :
    -(π / 2) ≤ Real.arcsin x ∧ Real.arcsin x ≤ π / 2 :=
  ⟨Real.neg_pi_div_two_le_arcsin x, Real.arcsin_le_pi_div_two x⟩

/-- The range of `arccos` is `[0, π]` (PC-234). -/
@[kb "stitzzeager2013" "Theorem 10.26, p. 832"]
theorem thm_10_26_arccos_range (x : ℝ) : 0 ≤ Real.arccos x ∧ Real.arccos x ≤ π :=
  ⟨Real.arccos_nonneg x, Real.arccos_le_pi x⟩

/-- `sin (arcsin x) = x` and `cos (arccos x) = x` for `x ∈ [-1, 1]` (PC-234). -/
@[kb "stitzzeager2013" "Theorem 10.26, p. 832"]
theorem thm_10_26_sin_arcsin_cos_arccos (x : ℝ) (h1 : -1 ≤ x) (h2 : x ≤ 1) :
    Real.sin (Real.arcsin x) = x ∧ Real.cos (Real.arccos x) = x :=
  ⟨Real.sin_arcsin h1 h2, Real.cos_arccos h1 h2⟩

/-- `arcsin (sin x) = x` on `[-π/2, π/2]` and `arccos (cos x) = x` on `[0, π]` (PC-234). -/
@[kb "stitzzeager2013" "Theorem 10.26, p. 832"]
theorem thm_10_26_arcsin_sin_arccos_cos (x y : ℝ) (hx : -(π / 2) ≤ x ∧ x ≤ π / 2)
    (hy : 0 ≤ y ∧ y ≤ π) :
    Real.arcsin (Real.sin x) = x ∧ Real.arccos (Real.cos y) = y :=
  ⟨Real.arcsin_sin hx.1 hx.2, Real.arccos_cos hy.1 hy.2⟩

/-- Arcsine is an odd function (PC-234). -/
@[kb "stitzzeager2013" "Theorem 10.26, p. 832"]
theorem thm_10_26_arcsin_odd (x : ℝ) : Real.arcsin (-x) = -Real.arcsin x :=
  Real.arcsin_neg x

/-- Arctangent: range `(-π/2, π/2)`, `tan (arctan x) = x`, `arctan (tan x) = x` on
`(-π/2, π/2)`, and arctangent is odd (PC-235). -/
@[kb "stitzzeager2013" "Theorem 10.27, p. 836"]
theorem thm_10_27_arctan (x y : ℝ) (hy : -(π / 2) < y ∧ y < π / 2) :
    Set.range Real.arctan = Set.Ioo (-(π / 2)) (π / 2) ∧ Real.tan (Real.arctan x) = x ∧
      Real.arctan (Real.tan y) = y ∧ Real.arctan (-x) = -Real.arctan x :=
  ⟨Real.range_arctan, Real.tan_arctan x, Real.arctan_tan hy.1 hy.2, Real.arctan_neg x⟩

/-- Arctangent tends to `π / 2` at plus infinity and to `-π / 2` at minus infinity (PC-235). -/
@[kb "stitzzeager2013" "Theorem 10.27, p. 836"]
theorem thm_10_27_arctan_limits :
    Filter.Tendsto Real.arctan Filter.atTop (nhdsWithin (π / 2) (Set.Iio (π / 2))) ∧
      Filter.Tendsto Real.arctan Filter.atBot (nhdsWithin (-(π / 2)) (Set.Ioi (-(π / 2)))) :=
  ⟨Real.tendsto_arctan_atTop, Real.tendsto_arctan_atBot⟩

end UndergradKB.Precalculus.Course
