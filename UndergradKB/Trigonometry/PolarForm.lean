import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import UndergradKB.Common.Attr

/-! # Polar form of complex numbers (Corral §6.3; OpenStax §10.5)

The books write a complex number in polar (trigonometric) form `r (cos θ + i sin θ)` (`r cis θ`). Mathlib has
the pieces (`Complex.exp_mul_I`, `Complex.exp_add`, `Complex.exp_int_mul`, `Complex.norm_mul`); here they are
assembled into the books' statements:
* `cis_mul_cis`: moduli multiply and arguments add (Corral eq 6.5, OpenStax §10.5);
* `cis_div_cis`: moduli divide and arguments subtract (Corral eq 6.6);
* `de_moivre`: `(r cis θ)ⁿ = rⁿ cis (nθ)` for every integer `n` (Corral Theorem 6.1, OpenStax §10.5);
* `dist_polar`: the distance between points with polar coordinates `(r₁, θ₁)`, `(r₂, θ₂)` (Corral eq 6.11).
-/

namespace UndergradKB.Trigonometry

open Complex

/-- `cos θ + i sin θ = exp (iθ)` for real `θ` (with the real cosine and sine). -/
lemma cos_add_sin_mul_I_eq_exp (θ : ℝ) :
    (Real.cos θ : ℂ) + Real.sin θ * I = Complex.exp (θ * I) := by
  rw [Complex.exp_mul_I]; push_cast; ring

/-- **Product in polar form**: `r₁ (cos α + i sin α) · r₂ (cos β + i sin β) = r₁ r₂ (cos (α+β) + i sin (α+β))`.
(TR-188) -/
@[kb "corraltrig" "Box §6.3 (eq 6.5), p. 150"]
theorem cis_mul_cis (r₁ r₂ α β : ℝ) :
    (r₁ * (Real.cos α + Real.sin α * I)) * (r₂ * (Real.cos β + Real.sin β * I)) =
      (r₁ * r₂ : ℝ) * (Real.cos (α + β) + Real.sin (α + β) * I) := by
  rw [cos_add_sin_mul_I_eq_exp, cos_add_sin_mul_I_eq_exp, cos_add_sin_mul_I_eq_exp]
  push_cast
  rw [add_mul, Complex.exp_add]
  ring

/-- The OpenStax form of the product rule. (TR-188) -/
@[kb "openstaxalgtrig2e" "§10.5 Products of complex numbers in polar form, p. 950"]
theorem cis_mul_cis' (r₁ r₂ θ₁ θ₂ : ℝ) :
    (r₁ * (Real.cos θ₁ + Real.sin θ₁ * I)) * (r₂ * (Real.cos θ₂ + Real.sin θ₂ * I)) =
      (r₁ * r₂ : ℝ) * (Real.cos (θ₁ + θ₂) + Real.sin (θ₁ + θ₂) * I) :=
  cis_mul_cis r₁ r₂ θ₁ θ₂

/-- **Quotient in polar form**: for `r₂ ≠ 0`,
`r₁ (cos α + i sin α) / (r₂ (cos β + i sin β)) = (r₁/r₂) (cos (α-β) + i sin (α-β))`. (TR-189) -/
@[kb "corraltrig" "Box §6.3 (eq 6.6), p. 150"]
theorem cis_div_cis (r₁ : ℝ) {r₂ : ℝ} (h : r₂ ≠ 0) (α β : ℝ) :
    (r₁ * (Real.cos α + Real.sin α * I)) / (r₂ * (Real.cos β + Real.sin β * I)) =
      (r₁ / r₂ : ℝ) * (Real.cos (α - β) + Real.sin (α - β) * I) := by
  rw [cos_add_sin_mul_I_eq_exp, cos_add_sin_mul_I_eq_exp, cos_add_sin_mul_I_eq_exp]
  have h' : (r₂ : ℂ) ≠ 0 := by exact_mod_cast h
  rw [div_eq_iff (mul_ne_zero h' (Complex.exp_ne_zero _))]
  push_cast
  rw [sub_mul, Complex.exp_sub]
  field_simp

/-- The OpenStax form of the quotient rule. (TR-189) -/
@[kb "openstaxalgtrig2e" "§10.5 Quotients of complex numbers in polar form, p. 950"]
theorem cis_div_cis' (r₁ : ℝ) {r₂ : ℝ} (h : r₂ ≠ 0) (θ₁ θ₂ : ℝ) :
    (r₁ * (Real.cos θ₁ + Real.sin θ₁ * I)) / (r₂ * (Real.cos θ₂ + Real.sin θ₂ * I)) =
      (r₁ / r₂ : ℝ) * (Real.cos (θ₁ - θ₂) + Real.sin (θ₁ - θ₂) * I) :=
  cis_div_cis r₁ h θ₁ θ₂

/-- **De Moivre's theorem**: `(r (cos θ + i sin θ))ⁿ = rⁿ (cos nθ + i sin nθ)` for every integer `n`.
(TR-190) -/
@[kb "corraltrig" "Theorem 6.1, p. 151"]
theorem de_moivre (r θ : ℝ) (n : ℤ) :
    (r * (Real.cos θ + Real.sin θ * I)) ^ n =
      (r ^ n : ℝ) * (Real.cos (n * θ) + Real.sin (n * θ) * I) := by
  rw [cos_add_sin_mul_I_eq_exp, cos_add_sin_mul_I_eq_exp, mul_zpow, ← Complex.exp_int_mul]
  push_cast
  ring_nf

/-- De Moivre's theorem for natural exponents, as stated in OpenStax §10.5. (TR-190) -/
@[kb "openstaxalgtrig2e" "§10.5 De Moivre's theorem, p. 951"]
theorem de_moivre_nat (r θ : ℝ) (n : ℕ) :
    (r * (Real.cos θ + Real.sin θ * I)) ^ n =
      (r ^ n : ℝ) * (Real.cos (n * θ) + Real.sin (n * θ) * I) := by
  have := de_moivre r θ n
  simpa using this

/-- **Distance in polar coordinates**: the points with polar coordinates `(r₁, θ₁)` and `(r₂, θ₂)` are at
distance `√(r₁² + r₂² - 2 r₁ r₂ cos (θ₁ - θ₂))` (the plane is `ℂ`). (TR-198) -/
@[kb "corraltrig" "Example 6.20 (eq 6.11), p. 159"]
theorem dist_polar (r₁ θ₁ r₂ θ₂ : ℝ) :
    dist ((r₁ * Real.cos θ₁ : ℝ) + (r₁ * Real.sin θ₁ : ℝ) * I)
        ((r₂ * Real.cos θ₂ : ℝ) + (r₂ * Real.sin θ₂ : ℝ) * I) =
      √(r₁ ^ 2 + r₂ ^ 2 - 2 * r₁ * r₂ * Real.cos (θ₁ - θ₂)) := by
  rw [Complex.dist_eq, ← Real.sqrt_sq (norm_nonneg _), Complex.sq_norm, Complex.normSq_apply]
  congr 1
  simp only [sub_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
    sub_self, add_zero, sub_im, add_im, mul_im, zero_add]
  rw [Real.cos_sub]
  linear_combination r₁ ^ 2 * Real.sin_sq_add_cos_sq θ₁ + r₂ ^ 2 * Real.sin_sq_add_cos_sq θ₂

end UndergradKB.Trigonometry
