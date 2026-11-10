import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import UndergradKB.Common.Attr

/-! # Dimpled and convex limaçons (OpenStax §10.4)

The one-loop limaçon `r = a + b cos θ` (`0 < |b| < a`) is traced by `θ ↦ (x θ, y θ)` with
`x θ = (a + b cos θ) cos θ`, `y θ = (a + b cos θ) sin θ`. A smooth closed curve traced once counterclockwise is
convex exactly when it never turns clockwise, i.e. when the curvature numerator `x' y'' - y' x''` (the sign of
the signed curvature) is never negative. Here:

* `limaconCos_curvature`: `x' y'' - y' x'' = a² + 3ab cos θ + 2b²` (computed with Mathlib's `deriv`);
* `limaconCos_convex_iff`: for `0 < |b| < a` the numerator is nonnegative for every `θ` iff `a ≥ 2|b|`
  (convex limaçon), and `limaconCos_dimple`: for `|b| < a < 2|b|` it is negative at the point opposite to the
  bulge (dimpled limaçon);
* the same for `r = a + b sin θ` (`limaconSin_curvature`, `limaconSin_convex_iff`, `limaconSin_dimple`);
  the four sign versions `a ± b cos θ`, `a ± b sin θ` are the cases `b > 0` and `b < 0`.

Mathlib has no notion of a convex plane curve, so convexity is expressed by the curvature sign (the classical
criterion for a closed curve of turning number one).
-/

namespace UndergradKB.Trigonometry

open Real

section Cos

variable (a b : ℝ)

/-- First coordinate of the limaçon `r = a + b cos θ`. -/
noncomputable def limaconCosX (θ : ℝ) : ℝ := (a + b * cos θ) * cos θ

/-- Second coordinate of the limaçon `r = a + b cos θ`. -/
noncomputable def limaconCosY (θ : ℝ) : ℝ := (a + b * cos θ) * sin θ

private lemma hasDerivAt_cosX (θ : ℝ) :
    HasDerivAt (limaconCosX a b) (-(a * sin θ) - 2 * b * (sin θ * cos θ)) θ := by
  have := (((hasDerivAt_cos θ).const_mul b).const_add a).mul (hasDerivAt_cos θ)
  convert this using 1
  all_goals first | rfl | ring

private lemma hasDerivAt_cosY (θ : ℝ) :
    HasDerivAt (limaconCosY a b) (a * cos θ + b * (cos θ ^ 2 - sin θ ^ 2)) θ := by
  have := (((hasDerivAt_cos θ).const_mul b).const_add a).mul (hasDerivAt_sin θ)
  convert this using 1
  all_goals first | rfl | ring

private lemma deriv_cosX : deriv (limaconCosX a b) = fun θ => -(a * sin θ) - 2 * b * (sin θ * cos θ) :=
  funext fun θ => (hasDerivAt_cosX a b θ).deriv

private lemma deriv_cosY : deriv (limaconCosY a b) = fun θ => a * cos θ + b * (cos θ ^ 2 - sin θ ^ 2) :=
  funext fun θ => (hasDerivAt_cosY a b θ).deriv

private lemma deriv2_cosX (θ : ℝ) :
    deriv (deriv (limaconCosX a b)) θ = -(a * cos θ) - 2 * b * (cos θ ^ 2 - sin θ ^ 2) := by
  rw [deriv_cosX]
  have := (((hasDerivAt_sin θ).const_mul a).neg).sub
    (((hasDerivAt_sin θ).mul (hasDerivAt_cos θ)).const_mul (2 * b))
  refine HasDerivAt.deriv ?_
  convert this using 1
  ring

private lemma deriv2_cosY (θ : ℝ) :
    deriv (deriv (limaconCosY a b)) θ = -(a * sin θ) - 4 * b * (sin θ * cos θ) := by
  rw [deriv_cosY]
  have := ((hasDerivAt_cos θ).const_mul a).add
    ((((hasDerivAt_cos θ).pow 2).sub ((hasDerivAt_sin θ).pow 2)).const_mul b)
  refine HasDerivAt.deriv ?_
  convert this using 1
  simp only [Nat.cast_ofNat]; ring

/-- **Curvature of the limaçon** `r = a + b cos θ`: `x' y'' - y' x'' = a² + 3ab cos θ + 2b²`. (TR-139) -/
theorem limaconCos_curvature (θ : ℝ) :
    deriv (limaconCosX a b) θ * deriv (deriv (limaconCosY a b)) θ -
        deriv (limaconCosY a b) θ * deriv (deriv (limaconCosX a b)) θ =
      a ^ 2 + 3 * a * b * cos θ + 2 * b ^ 2 := by
  rw [deriv2_cosX, deriv2_cosY, deriv_cosX, deriv_cosY]
  have h := sin_sq_add_cos_sq θ
  linear_combination (a ^ 2 + 3 * a * b * cos θ + 2 * b ^ 2 * (sin θ ^ 2 + cos θ ^ 2 + 1)) * h

/-- The minimum over `θ` of `a² + 3ab cos θ + 2b²`, for `a ≥ 0`, is `(a - |b|)(a - 2|b|)`, attained where
`b cos θ = -|b|`. -/
private lemma curv_nonneg_iff {a b : ℝ} (hb : 0 < |b|) (hab : |b| < a) :
    (∀ θ, 0 ≤ a ^ 2 + 3 * a * b * cos θ + 2 * b ^ 2) ↔ 2 * |b| ≤ a := by
  have ha : 0 < a := hb.trans hab
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    rcases le_or_gt 0 b with hb0 | hb0
    · have := h π
      rw [cos_pi, abs_of_nonneg hb0] at *
      nlinarith
    · have := h 0
      rw [cos_zero, abs_of_neg hb0] at *
      nlinarith
  · intro h θ
    have hc : -|b| ≤ b * cos θ := by
      have := abs_le.1 (show |b * cos θ| ≤ |b| by
        rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg b) (abs_cos_le_one θ))
      exact this.1
    have hbb : b ^ 2 = |b| ^ 2 := (sq_abs b).symm
    nlinarith

/-- **Convex limaçon** (OpenStax §10.4): for `0 < |b| < a` the one-loop limaçon `r = a + b cos θ` never turns
clockwise (curvature numerator `≥ 0` for all `θ`) exactly when `a ≥ 2|b|`. (TR-139) -/
@[kb "openstaxalgtrig2e" "§10.4 One-loop limaçons (dimpled and convex), p. 932"]
theorem limaconCos_convex_iff {a b : ℝ} (hb : 0 < |b|) (hab : |b| < a) :
    (∀ θ, 0 ≤ deriv (limaconCosX a b) θ * deriv (deriv (limaconCosY a b)) θ -
        deriv (limaconCosY a b) θ * deriv (deriv (limaconCosX a b)) θ) ↔ 2 * |b| ≤ a := by
  simp only [limaconCos_curvature]
  exact curv_nonneg_iff hb hab

/-- **Dimpled limaçon** (OpenStax §10.4): for `|b| < a < 2|b|` the limaçon `r = a + b cos θ` turns clockwise at the
point on the axis opposite to its bulge (`θ = π` for `b > 0`, `θ = 0` for `b < 0`): the dimple. (TR-139) -/
theorem limaconCos_dimple {a b : ℝ} (hab : |b| < a) (h2 : a < 2 * |b|) :
    ∃ θ, deriv (limaconCosX a b) θ * deriv (deriv (limaconCosY a b)) θ -
        deriv (limaconCosY a b) θ * deriv (deriv (limaconCosX a b)) θ < 0 := by
  simp only [limaconCos_curvature]
  rcases le_or_gt 0 b with hb0 | hb0
  · refine ⟨π, ?_⟩
    rw [cos_pi]; rw [abs_of_nonneg hb0] at hab h2; nlinarith
  · refine ⟨0, ?_⟩
    rw [cos_zero]; rw [abs_of_neg hb0] at hab h2; nlinarith

end Cos

section Sin

variable (a b : ℝ)

/-- First coordinate of the limaçon `r = a + b sin θ`. -/
noncomputable def limaconSinX (θ : ℝ) : ℝ := (a + b * sin θ) * cos θ

/-- Second coordinate of the limaçon `r = a + b sin θ`. -/
noncomputable def limaconSinY (θ : ℝ) : ℝ := (a + b * sin θ) * sin θ

private lemma hasDerivAt_sinX (θ : ℝ) :
    HasDerivAt (limaconSinX a b) (-(a * sin θ) + b * (cos θ ^ 2 - sin θ ^ 2)) θ := by
  have := (((hasDerivAt_sin θ).const_mul b).const_add a).mul (hasDerivAt_cos θ)
  convert this using 1
  all_goals first | rfl | ring

private lemma hasDerivAt_sinY (θ : ℝ) :
    HasDerivAt (limaconSinY a b) (a * cos θ + 2 * b * (sin θ * cos θ)) θ := by
  have := (((hasDerivAt_sin θ).const_mul b).const_add a).mul (hasDerivAt_sin θ)
  convert this using 1
  all_goals first | rfl | ring

private lemma deriv_sinX : deriv (limaconSinX a b) = fun θ => -(a * sin θ) + b * (cos θ ^ 2 - sin θ ^ 2) :=
  funext fun θ => (hasDerivAt_sinX a b θ).deriv

private lemma deriv_sinY : deriv (limaconSinY a b) = fun θ => a * cos θ + 2 * b * (sin θ * cos θ) :=
  funext fun θ => (hasDerivAt_sinY a b θ).deriv

private lemma deriv2_sinX (θ : ℝ) :
    deriv (deriv (limaconSinX a b)) θ = -(a * cos θ) - 4 * b * (sin θ * cos θ) := by
  rw [deriv_sinX]
  have := (((hasDerivAt_sin θ).const_mul a).neg).add
    ((((hasDerivAt_cos θ).pow 2).sub ((hasDerivAt_sin θ).pow 2)).const_mul b)
  refine HasDerivAt.deriv ?_
  convert this using 1
  simp only [Nat.cast_ofNat]; ring

private lemma deriv2_sinY (θ : ℝ) :
    deriv (deriv (limaconSinY a b)) θ = -(a * sin θ) + 2 * b * (cos θ ^ 2 - sin θ ^ 2) := by
  rw [deriv_sinY]
  have := ((hasDerivAt_cos θ).const_mul a).add
    (((hasDerivAt_sin θ).mul (hasDerivAt_cos θ)).const_mul (2 * b))
  refine HasDerivAt.deriv ?_
  convert this using 1
  ring

/-- **Curvature of the limaçon** `r = a + b sin θ`: `x' y'' - y' x'' = a² + 3ab sin θ + 2b²`. (TR-139) -/
theorem limaconSin_curvature (θ : ℝ) :
    deriv (limaconSinX a b) θ * deriv (deriv (limaconSinY a b)) θ -
        deriv (limaconSinY a b) θ * deriv (deriv (limaconSinX a b)) θ =
      a ^ 2 + 3 * a * b * sin θ + 2 * b ^ 2 := by
  rw [deriv2_sinX, deriv2_sinY, deriv_sinX, deriv_sinY]
  have h := sin_sq_add_cos_sq θ
  linear_combination (a ^ 2 + 3 * a * b * sin θ + 2 * b ^ 2 * (sin θ ^ 2 + cos θ ^ 2 + 1)) * h

/-- **Convex limaçon** `r = a + b sin θ` (OpenStax §10.4): for `0 < |b| < a` the curvature numerator is
nonnegative for all `θ` exactly when `a ≥ 2|b|`. (TR-139) -/
theorem limaconSin_convex_iff {a b : ℝ} (hb : 0 < |b|) (hab : |b| < a) :
    (∀ θ, 0 ≤ deriv (limaconSinX a b) θ * deriv (deriv (limaconSinY a b)) θ -
        deriv (limaconSinY a b) θ * deriv (deriv (limaconSinX a b)) θ) ↔ 2 * |b| ≤ a := by
  simp only [limaconSin_curvature]
  have key : (∀ θ, 0 ≤ a ^ 2 + 3 * a * b * sin θ + 2 * b ^ 2) ↔
      ∀ θ, 0 ≤ a ^ 2 + 3 * a * b * cos θ + 2 * b ^ 2 := by
    constructor
    · intro h θ; have := h (θ + π / 2); rwa [sin_add_pi_div_two] at this
    · intro h θ; have := h (θ - π / 2); rwa [cos_sub_pi_div_two] at this
  rw [key]
  exact curv_nonneg_iff hb hab

/-- **Dimpled limaçon** `r = a + b sin θ`: for `|b| < a < 2|b|` the curve turns clockwise somewhere. (TR-139) -/
theorem limaconSin_dimple {a b : ℝ} (hab : |b| < a) (h2 : a < 2 * |b|) :
    ∃ θ, deriv (limaconSinX a b) θ * deriv (deriv (limaconSinY a b)) θ -
        deriv (limaconSinY a b) θ * deriv (deriv (limaconSinX a b)) θ < 0 := by
  simp only [limaconSin_curvature]
  rcases le_or_gt 0 b with hb0 | hb0
  · refine ⟨-(π / 2), ?_⟩
    rw [sin_neg, sin_pi_div_two]; rw [abs_of_nonneg hb0] at hab h2; nlinarith
  · refine ⟨π / 2, ?_⟩
    rw [sin_pi_div_two]; rw [abs_of_neg hb0] at hab h2; nlinarith

end Sin

end UndergradKB.Trigonometry
