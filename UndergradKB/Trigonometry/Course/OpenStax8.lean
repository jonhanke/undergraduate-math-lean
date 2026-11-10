import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle
import UndergradKB.Common.Attr

/-! # Course layer: OpenStax *Algebra and Trigonometry* 2e, Chapter 8

Thin theorems in the book's terms (graphs of tangent, inverse trigonometric functions) whose
proofs are Mathlib declarations.  All angles are in radians.
-/

namespace UndergradKB.Trigonometry.Course.OpenStax

open Filter Set EuclideanGeometry
open scoped Topology

/-- Tangent is sine over cosine and is undefined where cosine vanishes, at odd multiples of `π/2`
(TR-114). -/
@[kb "openstaxalgtrig2e" "§8.2, p. 770"]
theorem s8_2_tan_domain :
    (∀ x : ℝ, Real.tan x = Real.sin x / Real.cos x) ∧
      ∀ x : ℝ, Real.cos x = 0 ↔ ∃ k : ℤ, x = (2 * k + 1) * Real.pi / 2 :=
  ⟨Real.tan_eq_sin_div_cos, fun _ => Real.cos_eq_zero_iff⟩

/-- Tangent repeats every `π` radians (TR-115). -/
@[kb "openstaxalgtrig2e" "§8.2, p. 770"]
theorem s8_2_tan_period (x : ℝ) : Real.tan (x + Real.pi) = Real.tan x :=
  Real.tan_periodic x

/-- Tangent grows without bound as the angle approaches `π/2` from below and falls without bound
as it approaches `-π/2` from above (TR-129). -/
@[kb "openstaxalgtrig2e" "§8.2, p. 770"]
theorem s8_2_tan_asymptotes :
    Tendsto Real.tan (𝓝[<] (Real.pi / 2)) atTop ∧
      Tendsto Real.tan (𝓝[>] (-(Real.pi / 2))) atBot :=
  ⟨Real.tendsto_tan_pi_div_two, Real.tendsto_tan_neg_pi_div_two⟩

/-- Arcsine takes values in `[-π/2, π/2]`, where sine is one-to-one (TR-145). -/
@[kb "openstaxalgtrig2e" "§8.3, p. 791"]
theorem s8_3_arcsin_range :
    (∀ x : ℝ, -(Real.pi / 2) ≤ Real.arcsin x ∧ Real.arcsin x ≤ Real.pi / 2) ∧
      InjOn Real.sin (Icc (-(Real.pi / 2)) (Real.pi / 2)) :=
  ⟨fun x => ⟨Real.neg_pi_div_two_le_arcsin x, Real.arcsin_le_pi_div_two x⟩, Real.injOn_sin⟩

/-- Arccosine takes values in `[0, π]`, where cosine is one-to-one (TR-148). -/
@[kb "openstaxalgtrig2e" "§8.3, p. 791"]
theorem s8_3_arccos_range :
    (∀ x : ℝ, 0 ≤ Real.arccos x ∧ Real.arccos x ≤ Real.pi) ∧
      InjOn Real.cos (Icc 0 Real.pi) :=
  ⟨fun x => ⟨Real.arccos_nonneg x, Real.arccos_le_pi x⟩, Real.injOn_cos⟩

/-- Arctangent has range `(-π/2, π/2)` and is one-to-one (TR-150). -/
@[kb "openstaxalgtrig2e" "§8.3, p. 791"]
theorem s8_3_arctan_range :
    Set.range Real.arctan = Ioo (-(Real.pi / 2)) (Real.pi / 2) ∧
      Function.Injective Real.arctan :=
  ⟨Real.range_arctan, Real.arctan_injective⟩

/-- Sine, cosine and tangent are not one-to-one on the real line, but are on the restricted
intervals (TR-158). -/
@[kb "openstaxalgtrig2e" "§8.3, p. 791"]
theorem s8_3_restricted_injective :
    ¬ Function.Injective Real.sin ∧ ¬ Function.Injective Real.cos ∧
      ¬ Function.Injective Real.tan ∧
      InjOn Real.sin (Icc (-(Real.pi / 2)) (Real.pi / 2)) ∧ InjOn Real.cos (Icc 0 Real.pi) ∧
      StrictMonoOn Real.tan (Ioo (-(Real.pi / 2)) (Real.pi / 2)) :=
  ⟨Real.sin_periodic.not_injective (by positivity), Real.cos_periodic.not_injective
    (by positivity), Real.tan_periodic.not_injective Real.pi_ne_zero, Real.injOn_sin,
    Real.injOn_cos, Real.strictMonoOn_tan⟩

/-- For `θ` in the principal interval, `arcsin x = θ` exactly when `x = sin θ` (TR-159). -/
@[kb "openstaxalgtrig2e" "§8.3, p. 793"]
theorem s8_3_arcsin_iff (x θ : ℝ) (hθ : θ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    Real.arcsin x = θ ↔ x = Real.sin θ :=
  Real.arcsin_eq_iff_eq_sin hθ

/-- For `θ` in `[0, π]`, `x = cos θ` gives `arccos x = θ` (TR-159). -/
theorem s8_3_arccos_of_cos (x θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi) (h : x = Real.cos θ) :
    Real.arccos x = θ :=
  Real.arccos_eq_of_eq_cos h0 h1 h

/-- For `θ` in `(-π/2, π/2)`, `tan θ = x` gives `arctan x = θ` (TR-159). -/
theorem s8_3_arctan_of_tan (x θ : ℝ) (h : Real.tan θ = x)
    (hθ : θ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) : Real.arctan x = θ :=
  Real.arctan_eq_of_tan_eq h hθ

/-- Arcsine undoes sine on `[-π/2, π/2]`, and sine undoes arcsine on `[-1, 1]` (TR-146). -/
@[kb "openstaxalgtrig2e" "§8.3, p. 796"]
theorem s8_3_arcsin_sin :
    (∀ t : ℝ, -(Real.pi / 2) ≤ t → t ≤ Real.pi / 2 → Real.arcsin (Real.sin t) = t) ∧
      (∀ x : ℝ, -1 ≤ x → x ≤ 1 → Real.sin (Real.arcsin x) = x) :=
  ⟨fun _ h1 h2 => Real.arcsin_sin h1 h2, fun _ h1 h2 => Real.sin_arcsin h1 h2⟩

/-- Arccosine undoes cosine on `[0, π]`, and cosine undoes arccosine on `[-1, 1]` (TR-149). -/
@[kb "openstaxalgtrig2e" "§8.3, p. 796"]
theorem s8_3_arccos_cos :
    (∀ t : ℝ, 0 ≤ t → t ≤ Real.pi → Real.arccos (Real.cos t) = t) ∧
      (∀ x : ℝ, -1 ≤ x → x ≤ 1 → Real.cos (Real.arccos x) = x) :=
  ⟨fun _ h1 h2 => Real.arccos_cos h1 h2, fun _ h1 h2 => Real.cos_arccos h1 h2⟩

/-- Arctangent undoes tangent on `(-π/2, π/2)`, and tangent undoes arctangent everywhere
(TR-151). -/
@[kb "openstaxalgtrig2e" "§8.3, p. 796"]
theorem s8_3_arctan_tan :
    (∀ t : ℝ, -(Real.pi / 2) < t → t < Real.pi / 2 → Real.arctan (Real.tan t) = t) ∧
      (∀ x : ℝ, Real.tan (Real.arctan x) = x) :=
  ⟨fun _ h1 h2 => Real.arctan_tan h1 h2, Real.tan_arctan⟩

/-- Composite identities with arcsine and arccosine (TR-152). -/
@[kb "openstaxalgtrig2e" "§8.3, p. 798"]
theorem s8_3_cos_arcsin (x : ℝ) :
    Real.cos (Real.arcsin x) = √(1 - x ^ 2) ∧ Real.sin (Real.arccos x) = √(1 - x ^ 2) :=
  ⟨Real.cos_arcsin x, Real.sin_arccos x⟩

/-- Further composites of trigonometric and inverse trigonometric functions (TR-163). -/
@[kb "openstaxalgtrig2e" "§8.3, p. 798"]
theorem s8_3_composites (x : ℝ) :
    Real.sin (Real.arccos x) = √(1 - x ^ 2) ∧ Real.sin (Real.arctan x) = x / √(1 + x ^ 2) ∧
      Real.cos (Real.arctan x) = 1 / √(1 + x ^ 2) ∧
      Real.tan (Real.arccos x) = √(1 - x ^ 2) / x :=
  ⟨Real.sin_arccos x, Real.sin_arctan x, Real.cos_arctan x, Real.tan_arccos x⟩

section Geometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- In a right triangle an acute angle is the arccosine, arcsine or arctangent of the
corresponding side ratio (TR-161). -/
@[kb "openstaxalgtrig2e" "§8.3, p. 795"]
theorem s8_3_angle_from_ratios {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = Real.pi / 2) :
    ∠ p₂ p₃ p₁ = Real.arccos (dist p₃ p₂ / dist p₁ p₃) ∧
      (p₁ ≠ p₂ ∨ p₃ ≠ p₂ → ∠ p₂ p₃ p₁ = Real.arcsin (dist p₁ p₂ / dist p₁ p₃)) ∧
      (p₃ ≠ p₂ → ∠ p₂ p₃ p₁ = Real.arctan (dist p₁ p₂ / dist p₃ p₂)) :=
  ⟨angle_eq_arccos_of_angle_eq_pi_div_two h, fun h0 => angle_eq_arcsin_of_angle_eq_pi_div_two h h0,
    fun h0 => angle_eq_arctan_of_angle_eq_pi_div_two h h0⟩

end Geometry

end UndergradKB.Trigonometry.Course.OpenStax
