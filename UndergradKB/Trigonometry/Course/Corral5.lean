import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import UndergradKB.Common.Attr

/-! # Course layer: Corral, *Trigonometry*, Chapter 5

Thin theorems in the book's terms (graphs, domains and ranges, inverse trigonometric functions)
whose proofs are Mathlib declarations.  All angles are in radians.
-/

namespace UndergradKB.Trigonometry.Course.Corral

open Filter Set
open scoped Topology

/-- The cosine graph is the sine graph shifted left by `π/2` (TR-113). -/
@[kb "corraltrig" "Box §5.1, p. 111"]
theorem box_5_1_cos_eq_sin_shift (x : ℝ) : Real.cos x = Real.sin (x + Real.pi / 2) :=
  (Real.sin_add_pi_div_two x).symm

/-- Tangent is sine over cosine, is undefined exactly where cosine vanishes, and blows up at
`±π/2` (TR-114). -/
@[kb "corraltrig" "Box §5.1, p. 112"]
theorem box_5_1_tan_asymptotes :
    (∀ x : ℝ, Real.tan x = Real.sin x / Real.cos x) ∧
      (∀ x : ℝ, Real.cos x = 0 ↔ ∃ k : ℤ, x = (2 * k + 1) * Real.pi / 2) ∧
      Tendsto Real.tan (𝓝[<] (Real.pi / 2)) atTop ∧
      Tendsto Real.tan (𝓝[>] (-(Real.pi / 2))) atBot :=
  ⟨Real.tan_eq_sin_div_cos, fun _ => Real.cos_eq_zero_iff, Real.tendsto_tan_pi_div_two,
    Real.tendsto_tan_neg_pi_div_two⟩

/-- Tangent repeats every `π` radians (TR-115). -/
@[kb "corraltrig" "Box §5.1, p. 112"]
theorem box_5_1_tan_period (x : ℝ) : Real.tan (x + Real.pi) = Real.tan x :=
  Real.tan_periodic x

/-- Sine and cosine have range `[-1, 1]`; tangent takes every real value; tangent is undefined at
odd multiples of `π/2` (TR-120). -/
@[kb "corraltrig" "Box §5.2, p. 116"]
theorem box_5_2_ranges :
    Set.range Real.sin = Icc (-1) 1 ∧ Set.range Real.cos = Icc (-1) 1 ∧
      Function.Surjective Real.tan :=
  ⟨Real.range_sin, Real.range_cos, Real.tan_surjective⟩

/-- Arcsine takes values in `[-π/2, π/2]`, and sine is one-to-one on that interval (TR-145). -/
@[kb "corraltrig" "Box §5.3, p. 121"]
theorem box_5_3_arcsin_range :
    (∀ x : ℝ, -(Real.pi / 2) ≤ Real.arcsin x ∧ Real.arcsin x ≤ Real.pi / 2) ∧
      InjOn Real.sin (Icc (-(Real.pi / 2)) (Real.pi / 2)) :=
  ⟨fun x => ⟨Real.neg_pi_div_two_le_arcsin x, Real.arcsin_le_pi_div_two x⟩, Real.injOn_sin⟩

/-- Arcsine undoes sine on `[-π/2, π/2]`, and sine undoes arcsine on `[-1, 1]` (TR-146). -/
@[kb "corraltrig" "Box §5.3, p. 121"]
theorem box_5_3_arcsin_sin :
    (∀ y : ℝ, -(Real.pi / 2) ≤ y → y ≤ Real.pi / 2 → Real.arcsin (Real.sin y) = y) ∧
      (∀ x : ℝ, -1 ≤ x → x ≤ 1 → Real.sin (Real.arcsin x) = x) :=
  ⟨fun _ h1 h2 => Real.arcsin_sin h1 h2, fun _ h1 h2 => Real.sin_arcsin h1 h2⟩

/-- Arccosine takes values in `[0, π]`, and cosine is one-to-one on that interval (TR-148). -/
@[kb "corraltrig" "Box §5.3, p. 122"]
theorem box_5_3_arccos_range :
    (∀ x : ℝ, 0 ≤ Real.arccos x ∧ Real.arccos x ≤ Real.pi) ∧
      InjOn Real.cos (Icc 0 Real.pi) :=
  ⟨fun x => ⟨Real.arccos_nonneg x, Real.arccos_le_pi x⟩, Real.injOn_cos⟩

/-- Arccosine undoes cosine on `[0, π]`, and cosine undoes arccosine on `[-1, 1]` (TR-149). -/
@[kb "corraltrig" "Box §5.3, p. 123"]
theorem box_5_3_arccos_cos :
    (∀ y : ℝ, 0 ≤ y → y ≤ Real.pi → Real.arccos (Real.cos y) = y) ∧
      (∀ x : ℝ, -1 ≤ x → x ≤ 1 → Real.cos (Real.arccos x) = x) :=
  ⟨fun _ h1 h2 => Real.arccos_cos h1 h2, fun _ h1 h2 => Real.cos_arccos h1 h2⟩

/-- Arctangent has range `(-π/2, π/2)` and is one-to-one (TR-150). -/
@[kb "corraltrig" "Box §5.3, p. 125"]
theorem box_5_3_arctan_range :
    Set.range Real.arctan = Ioo (-(Real.pi / 2)) (Real.pi / 2) ∧
      Function.Injective Real.arctan :=
  ⟨Real.range_arctan, Real.arctan_injective⟩

/-- Arctangent undoes tangent on `(-π/2, π/2)`, and tangent undoes arctangent everywhere
(TR-151). -/
@[kb "corraltrig" "Box §5.3, p. 125"]
theorem box_5_3_arctan_tan :
    (∀ y : ℝ, -(Real.pi / 2) < y → y < Real.pi / 2 → Real.arctan (Real.tan y) = y) ∧
      (∀ x : ℝ, Real.tan (Real.arctan x) = x) :=
  ⟨fun _ h1 h2 => Real.arctan_tan h1 h2, Real.tan_arctan⟩

/-- The cosine of an arcsine is the square root of one minus the square (TR-152). -/
@[kb "corraltrig" "Example 5.19, p. 125"]
theorem ex_5_19_cos_arcsin (x : ℝ) : Real.cos (Real.arcsin x) = √(1 - x ^ 2) :=
  Real.cos_arcsin x

/-- The tangent of an arcsine is `x / √(1 - x²)` (TR-153). -/
@[kb "corraltrig" "Example 5.20, p. 125"]
theorem ex_5_20_tan_arcsin (x : ℝ) : Real.tan (Real.arcsin x) = x / √(1 - x ^ 2) :=
  Real.tan_arcsin x

/-- The sum of two arctangents is the arctangent of `(a+b)/(1-ab)` when `ab < 1`, with a correction
of `±π` when `ab > 1` (TR-157). -/
@[kb "corraltrig" "Example 5.22, p. 127"]
theorem ex_5_22_arctan_sum (a b : ℝ) :
    (a * b < 1 → Real.arctan a + Real.arctan b = Real.arctan ((a + b) / (1 - a * b))) ∧
      (1 < a * b → 0 < a →
        Real.arctan a + Real.arctan b = Real.arctan ((a + b) / (1 - a * b)) + Real.pi) ∧
      (1 < a * b → a < 0 →
        Real.arctan a + Real.arctan b = Real.arctan ((a + b) / (1 - a * b)) - Real.pi) :=
  ⟨fun h => Real.arctan_add h, fun h ha => Real.arctan_add_eq_add_pi h ha,
    fun h ha => Real.arctan_add_eq_sub_pi h ha⟩

end UndergradKB.Trigonometry.Course.Corral
