import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import UndergradKB.Trigonometry.PolarCurves

/-! # Arguments and polar coordinates are determined up to full turns (Corral §6.3, §6.4; OpenStax §10.3)

* `eq_add_int_mul_two_pi_of_polarPoint_eq`: if `r (cos α + i sin α) = r' (cos β + i sin β)` with `r, r' > 0`, then
  `r = r'` and `β = α + 2πk` for an integer `k` (the argument of a nonzero complex number is determined up to
  full turns; Corral's text says `πk`, which is a misprint: see the checklist);
* `polarPoint_eq_iff`: two pairs of polar coordinates with positive radius give the same point exactly when the
  radii agree and the angles differ by a multiple of `2π`;
* `periodic_add_of_common_multiple`: a sum of two periodic functions is periodic with any common multiple of
  their periods (Corral §5.2).
-/

namespace UndergradKB.Trigonometry

open Complex Real

private lemma polarPoint_eq_exp (r θ : ℝ) : polarPoint r θ = r * Complex.exp (θ * I) := by
  rw [polarPoint, Complex.exp_mul_I]; push_cast; ring

/-- **Polar coordinates with positive radius** give the same point exactly when the radii are equal and the
angles differ by a whole number of turns. (TR-194, TR-187) -/
@[kb "corraltrig" "Box §6.3 (argument up to full turns), p. 149"]
theorem polarPoint_eq_iff {r r' α β : ℝ} (hr : 0 < r) (hr' : 0 < r') :
    polarPoint r α = polarPoint r' β ↔ r = r' ∧ ∃ k : ℤ, β = α + k * (2 * π) := by
  constructor
  · intro h
    have hn : r = r' := by
      have := congrArg norm h
      rwa [polarPoint_eq_exp, polarPoint_eq_exp, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I,
        Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hr.le,
        Real.norm_of_nonneg hr'.le, mul_one, mul_one] at this
    subst hn
    refine ⟨rfl, ?_⟩
    rw [polarPoint_eq_exp, polarPoint_eq_exp] at h
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have he : Complex.exp (α * I) = Complex.exp (β * I) := mul_left_cancel₀ hr0 h
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 he
    refine ⟨-n, ?_⟩
    have := congrArg Complex.im hn
    simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero, add_im,
      intCast_re, intCast_im, zero_mul, sub_zero, re_ofNat, im_ofNat, mul_re] at this
    push_cast
    linarith
  · rintro ⟨rfl, k, rfl⟩
    rw [polarPoint_eq_exp, polarPoint_eq_exp]
    congr 1
    rw [show ((α + k * (2 * π) : ℝ) : ℂ) * I = α * I + k * (2 * π * I) by push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- OpenStax's statement: `(r, θ)` and `(r, θ + 2πk)` name the same point, so polar coordinates are not unique.
(TR-194) -/
@[kb "openstaxalgtrig2e" "§10.3 (polar coordinates are not unique), p. 911"]
theorem polarPoint_add_int_mul_two_pi (r θ : ℝ) (k : ℤ) :
    polarPoint r (θ + k * (2 * π)) = polarPoint r θ := by
  simp only [polarPoint]
  rw [Real.sin_periodic.int_mul k θ, Real.cos_periodic.int_mul k θ]

/-- **Argument of a nonzero complex number**: if `r (cos α + i sin α) = r' (cos β + i sin β)` with `r, r' > 0`
then `β = α + 2πk` for an integer `k`. (TR-187) -/
theorem eq_add_int_mul_two_pi_of_polarPoint_eq {r r' α β : ℝ} (hr : 0 < r) (hr' : 0 < r')
    (h : polarPoint r α = polarPoint r' β) : ∃ k : ℤ, β = α + k * (2 * π) :=
  ((polarPoint_eq_iff hr hr').1 h).2

/-- **Period of a sum of periodic functions**: if `f` has period `p`, `g` has period `q`, and `L = m p = n q`
for natural numbers `m, n`, then `f + g` has period `L`. (TR-119) -/
@[kb "corraltrig" "Box §5.2 (period of a sum), p. 115"]
theorem periodic_add_of_common_multiple {f g : ℝ → ℝ} {p q L : ℝ} {m n : ℕ}
    (hf : Function.Periodic f p) (hg : Function.Periodic g q) (hm : L = m * p) (hn : L = n * q) :
    Function.Periodic (f + g) L := by
  have h1 := hf.nat_mul m
  have h2 := hg.nat_mul n
  rw [← hm] at h1
  rw [← hn] at h2
  exact h1.add h2

end UndergradKB.Trigonometry
