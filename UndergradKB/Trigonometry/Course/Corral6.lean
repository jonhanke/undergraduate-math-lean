import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.Complex.Polynomial.Basic
import UndergradKB.Common.Attr

/-! # Course layer: Corral, *Trigonometry*, Chapter 6

Thin theorems in the book's terms (trigonometric equations, complex numbers and their polar form)
whose proofs are Mathlib declarations.  All angles are in radians.
-/

namespace UndergradKB.Trigonometry.Course.Corral

open Complex ComplexConjugate

/-- Two sines are equal exactly when the angles differ by a multiple of `2π` or sum to an odd
multiple of `π` (TR-166). -/
@[kb "corraltrig" "Example 6.1, p. 137"]
theorem ex_6_1_sin_eq_sin_iff (x y : ℝ) :
    Real.sin x = Real.sin y ↔
      ∃ k : ℤ, y = 2 * k * Real.pi + x ∨ y = (2 * k + 1) * Real.pi - x :=
  Real.sin_eq_sin_iff

/-- Two cosines are equal exactly when the angles agree up to sign and a multiple of `2π`
(TR-168). -/
@[kb "corraltrig" "Example 6.6, p. 139"]
theorem ex_6_6_cos_eq_cos_iff (x y : ℝ) :
    Real.cos x = Real.cos y ↔ ∃ k : ℤ, y = 2 * k * Real.pi + x ∨ y = 2 * k * Real.pi - x :=
  Real.cos_eq_cos_iff

/-- The imaginary unit squares to `-1`, and every complex number is `a + b i` (TR-176). -/
@[kb "corraltrig" "D034, p. 147"]
theorem d034_imaginary_unit : Complex.I ^ 2 = -1 ∧ ∀ a b : ℝ, (⟨a, b⟩ : ℂ) = a + b * Complex.I :=
  ⟨Complex.I_sq, fun a b => Complex.mk_eq_add_mul_I a b⟩

/-- The real part of `a + b i` is `a` and the imaginary part is the real number `b` (TR-177). -/
@[kb "corraltrig" "D035, p. 147"]
theorem d035_real_imaginary_part (a b : ℝ) :
    ((a : ℂ) + b * Complex.I).re = a ∧ ((a : ℂ) + b * Complex.I).im = b := by
  simp

/-- A real number `a` is the complex number `a + 0 i` (TR-178). -/
@[kb "corraltrig" "D036, p. 147"]
theorem d036_real_as_complex (a : ℝ) :
    (a : ℂ).re = a ∧ (a : ℂ).im = 0 ∧ Function.Injective (fun x : ℝ => (x : ℂ)) :=
  ⟨Complex.ofReal_re a, Complex.ofReal_im a, Complex.ofReal_injective⟩

/-- Two complex numbers are equal exactly when their real and imaginary parts agree (TR-179). -/
@[kb "corraltrig" "Box §6.3, p. 147"]
theorem box_6_3_equality (a b c d : ℝ) :
    (a : ℂ) + b * Complex.I = c + d * Complex.I ↔ a = c ∧ b = d := by
  simp [Complex.ext_iff]

/-- Addition and subtraction act componentwise (TR-180). -/
@[kb "corraltrig" "Box §6.3, p. 147"]
theorem box_6_3_add_sub (z w : ℂ) :
    (z + w).re = z.re + w.re ∧ (z + w).im = z.im + w.im ∧
      (z - w).re = z.re - w.re ∧ (z - w).im = z.im - w.im :=
  ⟨Complex.add_re z w, Complex.add_im z w, Complex.sub_re z w, Complex.sub_im z w⟩

/-- The product `(a+bi)(c+di)` has real part `ac - bd` and imaginary part `ad + bc` (TR-181). -/
@[kb "corraltrig" "Box §6.3, p. 147"]
theorem box_6_3_mul (z w : ℂ) :
    (z * w).re = z.re * w.re - z.im * w.im ∧ (z * w).im = z.re * w.im + z.im * w.re :=
  ⟨Complex.mul_re z w, Complex.mul_im z w⟩

/-- Multiplying `a + bi` by its conjugate gives `a² + b²` (TR-182). -/
@[kb "corraltrig" "Box §6.3, p. 147"]
theorem box_6_3_mul_conj (a b : ℝ) :
    ((a : ℂ) + b * Complex.I) * ((a : ℂ) - b * Complex.I) = ((a ^ 2 + b ^ 2 : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [sq]
  · simp [sq]; ring

/-- The real and imaginary parts of a quotient, with the squared modulus of the divisor as
denominator (TR-183). -/
@[kb "corraltrig" "Box §6.3, p. 147"]
theorem box_6_3_div (z w : ℂ) :
    (z / w).re = z.re * w.re / Complex.normSq w + z.im * w.im / Complex.normSq w ∧
      (z / w).im = z.im * w.re / Complex.normSq w - z.re * w.im / Complex.normSq w :=
  ⟨Complex.div_re z w, Complex.div_im z w⟩

/-- Conjugation keeps the real part and negates the imaginary part (TR-184). -/
@[kb "corraltrig" "Box §6.3, p. 148"]
theorem box_6_3_conj (z : ℂ) : ((starRingEnd ℂ) z).re = z.re ∧ ((starRingEnd ℂ) z).im = -z.im :=
  ⟨Complex.conj_re z, Complex.conj_im z⟩

/-- The modulus of `z` is `√(a² + b²)` where `z = a + bi` (TR-185). -/
@[kb "corraltrig" "Box §6.3, p. 148"]
theorem box_6_3_modulus (z : ℂ) :
    ‖z‖ = √(z.re * z.re + z.im * z.im) ∧ ‖z‖ ^ 2 = z.re * z.re + z.im * z.im :=
  ⟨by rw [Complex.norm_def, Complex.normSq_apply], by rw [Complex.sq_norm, Complex.normSq_apply]⟩

/-- Polar form: every complex number is its modulus times `cos t + i sin t`, where `t` is the
principal argument; the cosine and sine are `x / r` and `y / r` for nonzero `z` (TR-186). -/
@[kb "corraltrig" "Box §6.3, p. 149"]
theorem box_6_3_polar_form (z : ℂ) :
    (‖z‖ : ℂ) * (Complex.cos (Complex.arg z) + Complex.sin (Complex.arg z) * Complex.I) = z ∧
      (z ≠ 0 → Real.cos (Complex.arg z) = z.re / ‖z‖ ∧ Real.sin (Complex.arg z) = z.im / ‖z‖) :=
  ⟨Complex.norm_mul_cos_add_sin_mul_I z, fun h => ⟨Complex.cos_arg h, Complex.sin_arg z⟩⟩

/-- The complex numbers form an algebraically closed field, so every non-constant polynomial has
a root (TR-193). -/
@[kb "corraltrig" "Box §6.3, p. 153"]
theorem box_6_3_fundamental_theorem :
    IsAlgClosed ℂ ∧ ∀ f : Polynomial ℂ, 0 < f.degree → ∃ z : ℂ, f.IsRoot z :=
  ⟨Complex.isAlgClosed, fun _ hf => Complex.exists_root hf⟩

/-- Polar coordinates: `x = r cos t` and `y = r sin t` (TR-196). -/
@[kb "corraltrig" "Box §6.4, p. 157"]
theorem box_6_4_polar_to_rectangular (r t : ℝ) :
    polarCoord.symm (r, t) = (r * Real.cos t, r * Real.sin t) :=
  polarCoord_symm_apply (r, t)

/-- For a complex number, the real and imaginary parts are `r cos t` and `r sin t` (TR-196). -/
theorem box_6_4_complex_polar (z : ℂ) :
    ‖z‖ * Real.cos (Complex.arg z) = z.re ∧ ‖z‖ * Real.sin (Complex.arg z) = z.im :=
  ⟨Complex.norm_mul_cos_arg z, Complex.norm_mul_sin_arg z⟩

end UndergradKB.Trigonometry.Course.Corral
