import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import UndergradKB.Trigonometry.Reciprocal

/-! # Inverse cotangent, secant and cosecant (Corral §5.3; OpenStax §8.3)

Mathlib has `Real.arcsin`, `Real.arccos`, `Real.arctan`, but not the inverses of the reciprocal functions.
Following Corral §5.3 we define
* `arccot x = π/2 - arctan x`, the inverse of `cot` restricted to `(0, π)`;
* `arcsec x = arccos (1/x)`, the inverse of `sec` restricted to `[0, π]` minus `π/2` (for `|x| ≥ 1`);
* `arccsc x = arcsin (1/x)`, the inverse of `csc` restricted to `[-π/2, π/2]` minus `0` (for `|x| ≥ 1`).
The theorems `cot_arccot`, `arccot_cot`, `arccot_mem_Ioo` (and the analogues for `arcsec`, `arccsc`) show that
these are the book's inverse functions (each is characterised by them).

Also: the composition rules `arcsin (cos t) = π/2 - t` and `arccos (sin t) = π/2 - t` (OpenStax §8.3) and the
exact values of the inverse functions at the special arguments (OpenStax §8.3 Example 2).
-/

namespace UndergradKB.Trigonometry

open Real Set

/-- The inverse cotangent, `arccot x = π/2 - arctan x` (values in `(0, π)`, see `arccot_mem_Ioo`). -/
noncomputable def arccot (x : ℝ) : ℝ := π / 2 - arctan x

/-- The inverse secant, `arcsec x = arccos (1/x)` (meaningful for `|x| ≥ 1`). -/
noncomputable def arcsec (x : ℝ) : ℝ := arccos (1 / x)

/-- The inverse cosecant, `arccsc x = arcsin (1/x)` (meaningful for `|x| ≥ 1`). -/
noncomputable def arccsc (x : ℝ) : ℝ := arcsin (1 / x)

private lemma cot_pi_div_two_sub' (θ : ℝ) : cot (π / 2 - θ) = tan θ := by
  rw [cot_eq_cos_div_sin, cos_pi_div_two_sub, sin_pi_div_two_sub, tan_eq_sin_div_cos]

/-- `arccot x ∈ (0, π)` for every real `x`. -/
theorem arccot_mem_Ioo (x : ℝ) : arccot x ∈ Ioo 0 π := by
  have h := arctan_mem_Ioo x
  exact ⟨by rw [arccot]; linarith [h.2], by rw [arccot]; linarith [h.1]⟩

/-- `cot (arccot x) = x` for every real `x`. -/
theorem cot_arccot (x : ℝ) : cot (arccot x) = x := by
  rw [arccot, cot_pi_div_two_sub', tan_arctan]

/-- `arccot (cot y) = y` for `0 < y < π`. -/
theorem arccot_cot {y : ℝ} (h₀ : 0 < y) (h₁ : y < π) : arccot (cot y) = y := by
  have : cot y = tan (π / 2 - y) := by rw [← cot_pi_div_two_sub', sub_sub_cancel]
  rw [arccot, this, arctan_tan (by linarith) (by linarith)]
  ring

/-- The inverse cotangent (Corral §5.3): `cot` is one-to-one on `(0, π)`, `arccot` maps `ℝ` into `(0, π)`,
`cot (arccot x) = x` for all `x` and `arccot (cot y) = y` for `0 < y < π`. (TR-154) -/
@[kb "corraltrig" "Box §5.3 (eqs 5.8, 5.9), p. 126"]
theorem arccot_spec :
    InjOn cot (Ioo 0 π) ∧ (∀ x, arccot x ∈ Ioo 0 π) ∧ (∀ x, cot (arccot x) = x) ∧
      ∀ y ∈ Ioo 0 π, arccot (cot y) = y := by
  refine ⟨fun y hy z hz h => ?_, arccot_mem_Ioo, cot_arccot, fun y hy => arccot_cot hy.1 hy.2⟩
  rw [← arccot_cot hy.1 hy.2, h, arccot_cot hz.1 hz.2]

/-- `arctan x + arccot x = π/2` for every real `x`. (TR-156) -/
@[kb "corraltrig" "Example 5.21, p. 127"]
theorem arctan_add_arccot (x : ℝ) : arctan x + arccot x = π / 2 := by
  rw [arccot]; ring

/-- The inverse secant (Corral §5.3): for `|x| ≥ 1`, `arcsec x ∈ [0, π]`, `arcsec x ≠ π/2` and
`sec (arcsec x) = x`; for `0 ≤ y ≤ π` with `y ≠ π/2`, `arcsec (sec y) = y`. (TR-155) -/
@[kb "corraltrig" "Box §5.3 (eqs 5.12, 5.13), p. 126"]
theorem arcsec_spec :
    (∀ x, 1 ≤ |x| → arcsec x ∈ Icc 0 π ∧ arcsec x ≠ π / 2 ∧ sec (arcsec x) = x) ∧
      ∀ y ∈ Icc 0 π, y ≠ π / 2 → arcsec (sec y) = y := by
  constructor
  · intro x hx
    have hx0 : x ≠ 0 := by rintro rfl; norm_num at hx
    have h1 : |1 / x| ≤ 1 := by
      rw [abs_div, abs_one, div_le_one (abs_pos.2 hx0)]; exact hx
    refine ⟨⟨arccos_nonneg _, arccos_le_pi _⟩, ?_, ?_⟩
    · rw [arcsec, Ne, arccos_eq_pi_div_two]; exact one_div_ne_zero hx0
    · rw [sec, arcsec, cos_arccos (abs_le.1 h1).1 (abs_le.1 h1).2]; simp
  · intro y hy _
    rw [arcsec, sec, one_div, inv_inv, arccos_cos hy.1 hy.2]

/-- The inverse cosecant (Corral §5.3): for `|x| ≥ 1`, `arccsc x ∈ [-π/2, π/2]`, `arccsc x ≠ 0` and
`csc (arccsc x) = x`; for `-π/2 ≤ y ≤ π/2` with `y ≠ 0`, `arccsc (csc y) = y`. (TR-155) -/
@[kb "corraltrig" "Box §5.3 (eqs 5.10, 5.11), p. 126"]
theorem arccsc_spec :
    (∀ x, 1 ≤ |x| → arccsc x ∈ Icc (-(π / 2)) (π / 2) ∧ arccsc x ≠ 0 ∧ csc (arccsc x) = x) ∧
      ∀ y ∈ Icc (-(π / 2)) (π / 2), y ≠ 0 → arccsc (csc y) = y := by
  constructor
  · intro x hx
    have hx0 : x ≠ 0 := by rintro rfl; norm_num at hx
    have h1 : |1 / x| ≤ 1 := by
      rw [abs_div, abs_one, div_le_one (abs_pos.2 hx0)]; exact hx
    refine ⟨arcsin_mem_Icc _, ?_, ?_⟩
    · rw [arccsc, Ne, arcsin_eq_zero_iff]; exact one_div_ne_zero hx0
    · rw [csc, arccsc, sin_arcsin (abs_le.1 h1).1 (abs_le.1 h1).2]; simp
  · intro y hy _
    rw [arccsc, csc, one_div, inv_inv, arcsin_sin hy.1 hy.2]

/-- `arcsin (cos t) = π/2 - t` for `0 ≤ t ≤ π`. (TR-162) -/
@[kb "openstaxalgtrig2e" "§8.3 (compositions with cofunctions), p. 797"]
theorem arcsin_cos {t : ℝ} (h₀ : 0 ≤ t) (h₁ : t ≤ π) : arcsin (cos t) = π / 2 - t := by
  rw [← sin_pi_div_two_sub, arcsin_sin (by linarith) (by linarith)]

/-- `arccos (sin t) = π/2 - t` for `-π/2 ≤ t ≤ π/2`. (TR-162) -/
theorem arccos_sin {t : ℝ} (h₀ : -(π / 2) ≤ t) (h₁ : t ≤ π / 2) : arccos (sin t) = π / 2 - t := by
  rw [← cos_pi_div_two_sub, arccos_cos (by linarith) (by linarith)]

/-- Exact values of the inverse sine at `1/2`, `√2/2`, `√3/2` (OpenStax §8.3 Example 2). (TR-160) -/
@[kb "openstaxalgtrig2e" "§8.3 Example 2, p. 794"]
theorem arcsin_special_values :
    arcsin (1 / 2) = π / 6 ∧ arcsin (√2 / 2) = π / 4 ∧ arcsin (√3 / 2) = π / 3 := by
  refine ⟨arcsin_eq_of_sin_eq (by rw [sin_pi_div_six]) ⟨by linarith [pi_pos], by linarith [pi_pos]⟩,
    arcsin_eq_of_sin_eq (by rw [sin_pi_div_four]) ⟨by linarith [pi_pos], by linarith [pi_pos]⟩,
    arcsin_eq_of_sin_eq (by rw [sin_pi_div_three]) ⟨by linarith [pi_pos], by linarith [pi_pos]⟩⟩

/-- Exact values of the inverse cosine at `1/2`, `√2/2`, `√3/2` and `-1/2`. (TR-160) -/
theorem arccos_special_values :
    arccos (1 / 2) = π / 3 ∧ arccos (√2 / 2) = π / 4 ∧ arccos (√3 / 2) = π / 6 ∧
      arccos (-(1 / 2)) = 2 * π / 3 := by
  refine ⟨arccos_eq_of_eq_cos (by linarith [pi_pos]) (by linarith [pi_pos]) (by rw [cos_pi_div_three]),
    arccos_eq_of_eq_cos (by linarith [pi_pos]) (by linarith [pi_pos]) (by rw [cos_pi_div_four]),
    arccos_eq_of_eq_cos (by linarith [pi_pos]) (by linarith [pi_pos]) (by rw [cos_pi_div_six]), ?_⟩
  rw [arccos_neg, arccos_eq_of_eq_cos (y := π / 3) (by linarith [pi_pos]) (by linarith [pi_pos])
    (by rw [cos_pi_div_three])]
  ring

/-- Exact values of the inverse tangent at `1`, `√3` and `1/√3`. (TR-160) -/
theorem arctan_special_values :
    arctan 1 = π / 4 ∧ arctan (√3) = π / 3 ∧ arctan (1 / √3) = π / 6 := by
  refine ⟨arctan_one, arctan_eq_of_tan_eq (by rw [tan_pi_div_three])
    ⟨by linarith [pi_pos], by linarith [pi_pos]⟩, arctan_eq_of_tan_eq ?_
    ⟨by linarith [pi_pos], by linarith [pi_pos]⟩⟩
  rw [tan_pi_div_six, one_div]

end UndergradKB.Trigonometry
