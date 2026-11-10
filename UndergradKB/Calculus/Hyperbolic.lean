import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import UndergradKB.Common.Attr

/-! # Calculus: hyperbolic and inverse hyperbolic functions

Mathlib has `Real.sinh`, `Real.cosh`, `Real.tanh`, `Real.arsinh`, `Real.arcosh`, `Real.artanh`. Missing, and defined
here: `sech`, `csch`, `coth` (as the reciprocals / ratios of `cosh`, `sinh`), and `arcoth`, `arsech`, `arcsch`
(defined as `artanh (1/x)`, `arcosh (1/x)`, `arsinh (1/x)`, i.e. as inverses of `coth`, `sech`, `csch`; their
logarithm formulas of the book are proved as theorems). -/

namespace UndergradKB.Calculus

open Real Filter Topology Set intervalIntegral

/-- The hyperbolic secant `sech x = 1 / cosh x` (OpenStax Calculus 1:§1.5, 2:§2.9). -/
noncomputable def sech (x : ℝ) : ℝ := 1 / Real.cosh x

/-- The hyperbolic cosecant `csch x = 1 / sinh x` (OpenStax Calculus 1:§1.5, 2:§2.9). -/
noncomputable def csch (x : ℝ) : ℝ := 1 / Real.sinh x

/-- The hyperbolic cotangent `coth x = cosh x / sinh x` (OpenStax Calculus 1:§1.5, 2:§2.9). -/
noncomputable def coth (x : ℝ) : ℝ := Real.cosh x / Real.sinh x

/-- Inverse hyperbolic cotangent, defined as `artanh (1/x)`, the inverse of `coth` on `|x| > 1`
(OpenStax Calculus 2:§2.9). -/
noncomputable def arcoth (x : ℝ) : ℝ := Real.artanh x⁻¹

/-- Inverse hyperbolic secant, defined as `arcosh (1/x)`, the inverse of `sech` on `(0, 1]`
(OpenStax Calculus 2:§2.9). -/
noncomputable def arsech (x : ℝ) : ℝ := Real.arcosh x⁻¹

/-- Inverse hyperbolic cosecant, defined as `arsinh (1/x)`, the inverse of `csch` on `x ≠ 0`
(OpenStax Calculus 2:§2.9). -/
noncomputable def arcsch (x : ℝ) : ℝ := Real.arsinh x⁻¹

/-! ## Definitions and identities (CA-042, CA-043) -/

/-- OpenStax Calculus 1:§1.5 Definition (hyperbolic functions) (CA-042): `sinh x = (e^x - e^(-x))/2`. -/
@[kb "openstaxcalculus2016" "1:§1.5 Definition (hyperbolic functions), p. 98"]
theorem sinh_eq_exp (x : ℝ) : sinh x = (exp x - exp (-x)) / 2 := Real.sinh_eq x

/-- OpenStax Calculus 1:§1.5 Definition (hyperbolic functions) (CA-042): `cosh x = (e^x + e^(-x))/2`. -/
@[kb "openstaxcalculus2016" "1:§1.5 Definition (hyperbolic functions), p. 98"]
theorem cosh_eq_exp (x : ℝ) : cosh x = (exp x + exp (-x)) / 2 := Real.cosh_eq x

/-- OpenStax Calculus 1:§1.5 Definition (hyperbolic functions) (CA-042): `tanh x = (e^x - e^(-x))/(e^x + e^(-x))`. -/
@[kb "openstaxcalculus2016" "1:§1.5 Definition (hyperbolic functions), p. 98"]
theorem tanh_eq_exp (x : ℝ) : tanh x = (exp x - exp (-x)) / (exp x + exp (-x)) := by
  rw [Real.tanh_eq_sinh_div_cosh, sinh_eq_exp, cosh_eq_exp, div_div_div_cancel_right₀ two_ne_zero]

/-- OpenStax Calculus 1:§1.5 Definition (hyperbolic functions) (CA-042): `sech x = 2/(e^x + e^(-x))`. -/
@[kb "openstaxcalculus2016" "1:§1.5 Definition (hyperbolic functions), p. 98"]
theorem sech_eq_exp (x : ℝ) : sech x = 2 / (exp x + exp (-x)) := by
  rw [sech, cosh_eq_exp, one_div_div]

/-- OpenStax Calculus 1:§1.5 Definition (hyperbolic functions) (CA-042): `csch x = 2/(e^x - e^(-x))`. -/
@[kb "openstaxcalculus2016" "1:§1.5 Definition (hyperbolic functions), p. 98"]
theorem csch_eq_exp (x : ℝ) : csch x = 2 / (exp x - exp (-x)) := by
  rw [csch, sinh_eq_exp, one_div_div]

/-- OpenStax Calculus 1:§1.5 Definition (hyperbolic functions) (CA-042): `coth x = (e^x + e^(-x))/(e^x - e^(-x))`. -/
@[kb "openstaxcalculus2016" "1:§1.5 Definition (hyperbolic functions), p. 98"]
theorem coth_eq_exp (x : ℝ) : coth x = (exp x + exp (-x)) / (exp x - exp (-x)) := by
  rw [coth, sinh_eq_exp, cosh_eq_exp, div_div_div_cancel_right₀ two_ne_zero]

/-- OpenStax Calculus 1:§1.5 Rule: Identities Involving Hyperbolic Functions (CA-043): `cosh x + sinh x = e^x`. -/
@[kb "openstaxcalculus2016" "1:§1.5 Rule: Identities Involving Hyperbolic Functions, p. 100"]
theorem cosh_add_sinh (x : ℝ) : cosh x + sinh x = exp x := by
  rw [cosh_eq_exp, sinh_eq_exp]; ring

/-- OpenStax Calculus 1:§1.5 Rule: Identities Involving Hyperbolic Functions (CA-043): `cosh x - sinh x = e^(-x)`. -/
@[kb "openstaxcalculus2016" "1:§1.5 Rule: Identities Involving Hyperbolic Functions, p. 100"]
theorem cosh_sub_sinh_eq (x : ℝ) : cosh x - sinh x = exp (-x) := by
  rw [cosh_eq_exp, sinh_eq_exp]; ring

/-- OpenStax Calculus 1:§1.5 Rule: Identities Involving Hyperbolic Functions (CA-043): `cosh² x - sinh² x = 1`. -/
@[kb "openstaxcalculus2016" "1:§1.5 Rule: Identities Involving Hyperbolic Functions, p. 100"]
theorem cosh_sq_sub_sinh_sq_eq (x : ℝ) : cosh x ^ 2 - sinh x ^ 2 = 1 := by
  rw [Real.cosh_sq]; ring

/-- OpenStax Calculus 1:§1.5 Rule: Identities Involving Hyperbolic Functions (CA-043): `1 - tanh² x = sech² x`. -/
@[kb "openstaxcalculus2016" "1:§1.5 Rule: Identities Involving Hyperbolic Functions, p. 100"]
theorem one_sub_tanh_sq (x : ℝ) : 1 - tanh x ^ 2 = sech x ^ 2 := by
  have hc := Real.cosh_pos x
  rw [Real.tanh_eq_sinh_div_cosh, sech]
  field_simp
  have := cosh_sq_sub_sinh_sq_eq x
  linarith

/-- OpenStax Calculus 1:§1.5 Rule: Identities Involving Hyperbolic Functions (CA-043): `coth² x - 1 = csch² x`
for `x ≠ 0`. -/
@[kb "openstaxcalculus2016" "1:§1.5 Rule: Identities Involving Hyperbolic Functions, p. 100"]
theorem coth_sq_sub_one {x : ℝ} (hx : x ≠ 0) : coth x ^ 2 - 1 = csch x ^ 2 := by
  have hs : sinh x ≠ 0 := fun h => hx (Real.sinh_eq_zero.mp h)
  rw [coth, csch]
  field_simp
  have := cosh_sq_sub_sinh_sq_eq x
  linarith

/-- OpenStax Calculus 1:§1.5 Rule: Identities Involving Hyperbolic Functions (CA-043): `sinh (x + y)`. -/
@[kb "openstaxcalculus2016" "1:§1.5 Rule: Identities Involving Hyperbolic Functions, p. 100"]
theorem sinh_add_eq (x y : ℝ) : sinh (x + y) = sinh x * cosh y + cosh x * sinh y := Real.sinh_add x y

/-- OpenStax Calculus 1:§1.5 Rule: Identities Involving Hyperbolic Functions (CA-043): `cosh (x + y)`. -/
@[kb "openstaxcalculus2016" "1:§1.5 Rule: Identities Involving Hyperbolic Functions, p. 100"]
theorem cosh_add_eq (x y : ℝ) : cosh (x + y) = cosh x * cosh y + sinh x * sinh y := Real.cosh_add x y

/-- OpenStax Calculus 1:§1.5 Rule: Identities Involving Hyperbolic Functions (CA-043): `sinh (2x) = 2 sinh x cosh x`. -/
@[kb "openstaxcalculus2016" "1:§1.5 Rule: Identities Involving Hyperbolic Functions, p. 100"]
theorem sinh_double (x : ℝ) : sinh (2 * x) = 2 * sinh x * cosh x := by
  rw [two_mul, sinh_add_eq]; ring

/-- OpenStax Calculus 1:§1.5 Rule: Identities Involving Hyperbolic Functions (CA-043):
`cosh (2x) = cosh² x + sinh² x`. -/
@[kb "openstaxcalculus2016" "1:§1.5 Rule: Identities Involving Hyperbolic Functions, p. 100"]
theorem cosh_double (x : ℝ) : cosh (2 * x) = cosh x ^ 2 + sinh x ^ 2 := by
  rw [two_mul, cosh_add_eq]; ring

/-! ## Logarithm formulas and domains of the inverse hyperbolic functions (CA-044, CA-045) -/

/-- OpenStax Calculus 1:§1.5 Definition (inverse hyperbolic functions) (CA-044): `arsinh x = ln (x + √(x²+1))`. -/
@[kb "openstaxcalculus2016" "1:§1.5 Definition (inverse hyperbolic functions), p. 101"]
theorem arsinh_eq_log (x : ℝ) : arsinh x = log (x + √(x ^ 2 + 1)) := by
  rw [Real.arsinh, add_comm (1:ℝ) (x ^ 2)]

/-- OpenStax Calculus 1:§1.5 Definition (inverse hyperbolic functions) (CA-044): `arcosh x = ln (x + √(x²-1))`. -/
@[kb "openstaxcalculus2016" "1:§1.5 Definition (inverse hyperbolic functions), p. 101"]
theorem arcosh_eq_log (x : ℝ) : arcosh x = log (x + √(x ^ 2 - 1)) := rfl

/-- OpenStax Calculus 1:§1.5 Definition (inverse hyperbolic functions) (CA-044):
`artanh x = ½ ln ((1+x)/(1-x))` for `|x| < 1`. -/
@[kb "openstaxcalculus2016" "1:§1.5 Definition (inverse hyperbolic functions), p. 101"]
theorem artanh_eq_log {x : ℝ} (hx : |x| < 1) : artanh x = 1 / 2 * log ((1 + x) / (1 - x)) :=
  Real.artanh_eq_half_log ⟨by linarith [abs_lt.mp hx |>.1], by linarith [abs_lt.mp hx |>.2]⟩

/-- OpenStax Calculus 1:§1.5 Definition (inverse hyperbolic functions) (CA-044):
`arcoth x = ½ ln ((x+1)/(x-1))` for `|x| > 1`. -/
@[kb "openstaxcalculus2016" "1:§1.5 Definition (inverse hyperbolic functions), p. 101"]
theorem arcoth_eq_log {x : ℝ} (hx : 1 < |x|) : arcoth x = 1 / 2 * log ((x + 1) / (x - 1)) := by
  have hx0 : x ≠ 0 := by rintro rfl; norm_num at hx
  have hx1 : x - 1 ≠ 0 := by
    intro h; have : x = 1 := by linarith
    rw [this] at hx; simp at hx
  have hi : |x⁻¹| < 1 := by
    rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hx
  rw [arcoth, artanh_eq_log hi]
  congr 2
  field_simp

/-- OpenStax Calculus 1:§1.5 Definition (inverse hyperbolic functions) (CA-044):
`arsech x = ln ((1 + √(1-x²))/x)` for `0 < x ≤ 1`. -/
@[kb "openstaxcalculus2016" "1:§1.5 Definition (inverse hyperbolic functions), p. 101"]
theorem arsech_eq_log {x : ℝ} (hx : 0 < x) (_hx1 : x ≤ 1) : arsech x = log ((1 + √(1 - x ^ 2)) / x) := by
  rw [arsech, arcosh]
  congr 1
  have : √(x⁻¹ ^ 2 - 1) = √(1 - x ^ 2) / x := by
    have : x⁻¹ ^ 2 - 1 = (1 - x ^ 2) / x ^ 2 := by field_simp
    rw [this, Real.sqrt_div' _ (sq_nonneg x), Real.sqrt_sq hx.le]
  rw [this]; field_simp

/-- OpenStax Calculus 1:§1.5 Definition (inverse hyperbolic functions) (CA-044):
`arcsch x = ln (1/x + √(1+x²)/|x|)` for `x ≠ 0`. -/
@[kb "openstaxcalculus2016" "1:§1.5 Definition (inverse hyperbolic functions), p. 101"]
theorem arcsch_eq_log {x : ℝ} (hx : x ≠ 0) : arcsch x = log (1 / x + √(1 + x ^ 2) / |x|) := by
  rw [arcsch, Real.arsinh]
  congr 1
  have : √(1 + x⁻¹ ^ 2) = √(1 + x ^ 2) / |x| := by
    have : 1 + x⁻¹ ^ 2 = (1 + x ^ 2) / |x| ^ 2 := by rw [sq_abs]; field_simp; ring
    rw [this, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq (abs_nonneg x)]
  rw [this, one_div]

/-- Helper: inversion is a bijection between two sets that it exchanges. -/
theorem bijOn_inv_of_mapsTo {s t : Set ℝ} (h1 : MapsTo (fun x : ℝ => x⁻¹) s t)
    (h2 : MapsTo (fun x : ℝ => x⁻¹) t s) : BijOn (fun x : ℝ => x⁻¹) s t :=
  Set.InvOn.bijOn ⟨fun x _ => inv_inv x, fun x _ => inv_inv x⟩ h1 h2

/-- OpenStax Calculus 2:§2.9 Table 2.3 (CA-045): `arsinh` is a bijection of `ℝ` onto `ℝ`. -/
@[kb "openstaxcalculus2016" "2:§2.9 Table 2.3 (inverse hyperbolic function domains and ranges), p. 224"]
theorem arsinh_bijective : Function.Bijective arsinh :=
  Function.bijective_iff_has_inverse.mpr ⟨sinh, Real.sinh_arsinh, Real.arsinh_sinh⟩

/-- OpenStax Calculus 2:§2.9 Table 2.3 (CA-045): `arcosh` maps `[1, ∞)` bijectively onto `[0, ∞)`. -/
@[kb "openstaxcalculus2016" "2:§2.9 Table 2.3 (inverse hyperbolic function domains and ranges), p. 224"]
theorem arcosh_bijOn' : BijOn arcosh (Ici 1) (Ici 0) := Real.arcosh_bijOn

/-- OpenStax Calculus 2:§2.9 Table 2.3 (CA-045): `artanh` maps `(-1, 1)` bijectively onto `ℝ`. -/
@[kb "openstaxcalculus2016" "2:§2.9 Table 2.3 (inverse hyperbolic function domains and ranges), p. 224"]
theorem artanh_bijOn' : BijOn artanh (Ioo (-1) 1) univ := Real.artanh_bijOn

/-- OpenStax Calculus 2:§2.9 Table 2.3 (CA-045): `arcoth` maps `{x | 1 < |x|}` bijectively onto `{y | y ≠ 0}`. -/
@[kb "openstaxcalculus2016" "2:§2.9 Table 2.3 (inverse hyperbolic function domains and ranges), p. 224"]
theorem arcoth_bijOn : BijOn arcoth {x : ℝ | 1 < |x|} {y : ℝ | y ≠ 0} := by
  have hinv : BijOn (fun x : ℝ => x⁻¹) {x : ℝ | 1 < |x|} {x : ℝ | |x| < 1 ∧ x ≠ 0} := by
    refine bijOn_inv_of_mapsTo (fun x hx => ?_) (fun x hx => ?_)
    · have hx0 : x ≠ 0 := by rintro rfl; norm_num at hx
      exact ⟨by simp only [abs_inv]; exact inv_lt_one_of_one_lt₀ hx, inv_ne_zero hx0⟩
    · have hx0 : 0 < |x| := abs_pos.mpr hx.2
      show 1 < |x⁻¹|
      rw [abs_inv]; exact one_lt_inv₀ hx0 |>.mpr hx.1
  have hart : BijOn artanh {x : ℝ | |x| < 1 ∧ x ≠ 0} {y : ℝ | y ≠ 0} := by
    have h := Real.artanh_bijOn
    refine ⟨fun x hx => ?_, h.injOn.mono (fun x hx => abs_lt.mp hx.1), fun y hy => ?_⟩
    · intro h0
      have : artanh x = artanh 0 := by rw [h0, Real.artanh_zero]
      exact hx.2 (h.injOn (abs_lt.mp hx.1) ⟨by norm_num, by norm_num⟩ this)
    · obtain ⟨x, hx, rfl⟩ := h.surjOn (mem_univ y)
      refine ⟨x, ⟨abs_lt.mpr hx, ?_⟩, rfl⟩
      rintro rfl; exact hy Real.artanh_zero
  exact hart.comp hinv

/-- OpenStax Calculus 2:§2.9 Table 2.3 (CA-045): `arsech` maps `(0, 1]` bijectively onto `[0, ∞)`. -/
@[kb "openstaxcalculus2016" "2:§2.9 Table 2.3 (inverse hyperbolic function domains and ranges), p. 224"]
theorem arsech_bijOn : BijOn arsech (Ioc 0 1) (Ici 0) := by
  have hinv : BijOn (fun x : ℝ => x⁻¹) (Ioc 0 1) (Ici 1) := by
    refine bijOn_inv_of_mapsTo (fun x hx => ?_) (fun x hx => ?_)
    · exact (one_le_inv₀ hx.1).mpr hx.2
    · have hx0 : 0 < x := by have : (1:ℝ) ≤ x := hx; linarith
      exact ⟨inv_pos.mpr hx0, inv_le_one_of_one_le₀ hx⟩
  exact Real.arcosh_bijOn.comp hinv

/-- OpenStax Calculus 2:§2.9 Table 2.3 (CA-045): `arcsch` maps `{x | x ≠ 0}` bijectively onto `{y | y ≠ 0}`. -/
@[kb "openstaxcalculus2016" "2:§2.9 Table 2.3 (inverse hyperbolic function domains and ranges), p. 224"]
theorem arcsch_bijOn : BijOn arcsch {x : ℝ | x ≠ 0} {y : ℝ | y ≠ 0} := by
  have hinv : BijOn (fun x : ℝ => x⁻¹) {x : ℝ | x ≠ 0} {x : ℝ | x ≠ 0} :=
    bijOn_inv_of_mapsTo (fun x hx => inv_ne_zero hx) (fun x hx => inv_ne_zero hx)
  have hs : BijOn arsinh {x : ℝ | x ≠ 0} {y : ℝ | y ≠ 0} := by
    have hb := arsinh_bijective
    refine ⟨fun x hx h0 => hx ?_, hb.1.injOn, fun y hy => ?_⟩
    · have : arsinh x = arsinh 0 := by rw [h0, Real.arsinh_zero]
      exact hb.1 this
    · obtain ⟨x, rfl⟩ := hb.2 y
      exact ⟨x, fun h0 => hy (by rw [h0, Real.arsinh_zero]), rfl⟩
  exact hs.comp hinv

/-! ## Derivatives of the hyperbolic functions (CA-130, CA-300) -/

private theorem sinh_ne_zero' {x : ℝ} (hx : x ≠ 0) : sinh x ≠ 0 := fun h => hx (Real.sinh_eq_zero.mp h)

/-- OpenStax Calculus 2:§2.9 Table 2.2 (CA-130, CA-300): `sinh' = cosh`. -/
@[kb "openstaxcalculus2016" "2:§2.9 Table 2.2 (derivatives of the hyperbolic functions), p. 222"]
theorem hasDerivAt_sinh' (x : ℝ) : HasDerivAt sinh (cosh x) x := Real.hasDerivAt_sinh x

/-- OpenStax Calculus 2:§2.9 Table 2.2 (CA-130, CA-300): `cosh' = sinh`. -/
@[kb "openstaxcalculus2016" "2:§2.9 Table 2.2 (derivatives of the hyperbolic functions), p. 222"]
theorem hasDerivAt_cosh' (x : ℝ) : HasDerivAt cosh (sinh x) x := Real.hasDerivAt_cosh x

/-- OpenStax Calculus 2:§2.9 Table 2.2 (CA-130, CA-300): `tanh' = sech²`. -/
@[kb "openstaxcalculus2016" "2:§2.9 Table 2.2 (derivatives of the hyperbolic functions), p. 222"]
theorem hasDerivAt_tanh (x : ℝ) : HasDerivAt tanh (sech x ^ 2) x := by
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne'
  have e : tanh = fun y => sinh y / cosh y := funext Real.tanh_eq_sinh_div_cosh
  rw [e]
  refine h.congr_deriv ?_
  have hc := Real.cosh_pos x
  rw [sech]
  field_simp
  have := cosh_sq_sub_sinh_sq_eq x
  linarith

/-- OpenStax Calculus 2:§2.9 Table 2.2 (CA-130, CA-300): `coth' = -csch²` for `x ≠ 0`. -/
@[kb "openstaxcalculus2016" "2:§2.9 Table 2.2 (derivatives of the hyperbolic functions), p. 222"]
theorem hasDerivAt_coth {x : ℝ} (hx : x ≠ 0) : HasDerivAt coth (-(csch x ^ 2)) x := by
  have hs := sinh_ne_zero' hx
  have h := (Real.hasDerivAt_cosh x).div (Real.hasDerivAt_sinh x) hs
  refine h.congr_deriv ?_
  rw [csch]
  field_simp
  have := cosh_sq_sub_sinh_sq_eq x
  linarith

/-- OpenStax Calculus 2:§2.9 Table 2.2 (CA-130, CA-300): `sech' = -sech · tanh`. -/
@[kb "openstaxcalculus2016" "2:§2.9 Table 2.2 (derivatives of the hyperbolic functions), p. 222"]
theorem hasDerivAt_sech (x : ℝ) : HasDerivAt sech (-(sech x * tanh x)) x := by
  have hc := Real.cosh_pos x
  have h := (hasDerivAt_const x (1:ℝ)).div (Real.hasDerivAt_cosh x) hc.ne'
  show HasDerivAt (fun y => 1 / cosh y) _ x
  refine h.congr_deriv ?_
  rw [sech, Real.tanh_eq_sinh_div_cosh]
  field_simp
  ring

/-- OpenStax Calculus 2:§2.9 Table 2.2 (CA-130, CA-300): `csch' = -csch · coth` for `x ≠ 0`. -/
@[kb "openstaxcalculus2016" "2:§2.9 Table 2.2 (derivatives of the hyperbolic functions), p. 222"]
theorem hasDerivAt_csch {x : ℝ} (hx : x ≠ 0) : HasDerivAt csch (-(csch x * coth x)) x := by
  have hs := sinh_ne_zero' hx
  have h := (hasDerivAt_const x (1:ℝ)).div (Real.hasDerivAt_sinh x) hs
  show HasDerivAt (fun y => 1 / sinh y) _ x
  refine h.congr_deriv ?_
  rw [csch, coth]
  field_simp
  ring

/-! ## Antiderivatives of the hyperbolic functions (CA-211, CA-301) -/

/-- OpenStax Calculus 2:§2.9 integration formulas (CA-211, CA-301): `-sech` is an antiderivative of `sech · tanh`. -/
@[kb "openstaxcalculus2016" "2:§2.9 Integration formulas for hyperbolic functions, p. 223"]
theorem hasDerivAt_neg_sech (x : ℝ) : HasDerivAt (fun y => -sech y) (sech x * tanh x) x := by
  exact ((hasDerivAt_sech x).neg).congr_deriv (by ring)

/-- OpenStax Calculus 2:§2.9 integration formulas (CA-211, CA-301): `-csch` is an antiderivative of `csch · coth`
on `x ≠ 0`. -/
@[kb "openstaxcalculus2016" "2:§2.9 Integration formulas for hyperbolic functions, p. 223"]
theorem hasDerivAt_neg_csch {x : ℝ} (hx : x ≠ 0) : HasDerivAt (fun y => -csch y) (csch x * coth x) x := by
  exact ((hasDerivAt_csch hx).neg).congr_deriv (by ring)

/-- OpenStax Calculus 2:§2.9 integration formulas (CA-211, CA-301): `-coth` is an antiderivative of `csch²`
on `x ≠ 0`. -/
@[kb "openstaxcalculus2016" "2:§2.9 Integration formulas for hyperbolic functions, p. 223"]
theorem hasDerivAt_neg_coth {x : ℝ} (hx : x ≠ 0) : HasDerivAt (fun y => -coth y) (csch x ^ 2) x := by
  exact ((hasDerivAt_coth hx).neg).congr_deriv (by ring)

theorem continuous_sech : Continuous sech := by
  unfold sech
  exact continuous_const.div Real.continuous_cosh fun x => (Real.cosh_pos x).ne'

theorem continuous_tanh' : Continuous tanh := by
  rw [show tanh = fun y => sinh y / cosh y from funext Real.tanh_eq_sinh_div_cosh]
  exact Real.continuous_sinh.div Real.continuous_cosh fun x => (Real.cosh_pos x).ne'

private theorem continuousOn_csch {a b : ℝ} (h : 0 ∉ uIcc a b) : ContinuousOn csch (uIcc a b) := by
  unfold csch
  exact continuousOn_const.div Real.continuous_sinh.continuousOn fun x hx =>
    sinh_ne_zero' (fun h0 => h (h0 ▸ hx))

private theorem continuousOn_coth {a b : ℝ} (h : 0 ∉ uIcc a b) : ContinuousOn coth (uIcc a b) := by
  unfold coth
  exact Real.continuous_cosh.continuousOn.div Real.continuous_sinh.continuousOn fun x hx =>
    sinh_ne_zero' (fun h0 => h (h0 ▸ hx))

/-- OpenStax Calculus 2:§2.9 integration formulas (CA-211, CA-301): `∫ₐᵇ sinh = cosh b - cosh a`. -/
@[kb "openstaxcalculus2016" "2:§2.9 Integration formulas for hyperbolic functions, p. 223"]
theorem integral_sinh (a b : ℝ) : ∫ x in a..b, sinh x = cosh b - cosh a :=
  integral_eq_sub_of_hasDerivAt (fun x _ => Real.hasDerivAt_cosh x)
    (Real.continuous_sinh.intervalIntegrable a b)

/-- OpenStax Calculus 2:§2.9 integration formulas (CA-211, CA-301): `∫ₐᵇ cosh = sinh b - sinh a`. -/
@[kb "openstaxcalculus2016" "2:§2.9 Integration formulas for hyperbolic functions, p. 223"]
theorem integral_cosh (a b : ℝ) : ∫ x in a..b, cosh x = sinh b - sinh a :=
  integral_eq_sub_of_hasDerivAt (fun x _ => Real.hasDerivAt_sinh x)
    (Real.continuous_cosh.intervalIntegrable a b)

/-- OpenStax Calculus 2:§2.9 integration formulas (CA-211, CA-301): `∫ₐᵇ sech² = tanh b - tanh a`. -/
@[kb "openstaxcalculus2016" "2:§2.9 Integration formulas for hyperbolic functions, p. 223"]
theorem integral_sech_sq (a b : ℝ) : ∫ x in a..b, sech x ^ 2 = tanh b - tanh a :=
  integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_tanh x)
    ((continuous_sech.pow 2).intervalIntegrable a b)

/-- OpenStax Calculus 2:§2.9 integration formulas (CA-211, CA-301): `∫ₐᵇ sech · tanh = sech a - sech b`. -/
@[kb "openstaxcalculus2016" "2:§2.9 Integration formulas for hyperbolic functions, p. 223"]
theorem integral_sech_mul_tanh (a b : ℝ) : ∫ x in a..b, sech x * tanh x = sech a - sech b := by
  rw [integral_eq_sub_of_hasDerivAt (f := fun y => -sech y) (fun x _ => hasDerivAt_neg_sech x)
    ((continuous_sech.mul continuous_tanh').intervalIntegrable a b)]
  ring

/-- OpenStax Calculus 2:§2.9 integration formulas (CA-211, CA-301): `∫ₐᵇ csch² = coth a - coth b`
when `0` is not between `a` and `b`. -/
@[kb "openstaxcalculus2016" "2:§2.9 Integration formulas for hyperbolic functions, p. 223"]
theorem integral_csch_sq {a b : ℝ} (h : 0 ∉ uIcc a b) :
    ∫ x in a..b, csch x ^ 2 = coth a - coth b := by
  rw [integral_eq_sub_of_hasDerivAt (f := fun y => -coth y)
    (fun x hx => hasDerivAt_neg_coth (fun h0 => h (h0 ▸ hx)))
    (((continuousOn_csch h).pow 2).intervalIntegrable)]
  ring

/-- OpenStax Calculus 2:§2.9 integration formulas (CA-211, CA-301): `∫ₐᵇ csch · coth = csch a - csch b`
when `0` is not between `a` and `b`. -/
@[kb "openstaxcalculus2016" "2:§2.9 Integration formulas for hyperbolic functions, p. 223"]
theorem integral_csch_mul_coth {a b : ℝ} (h : 0 ∉ uIcc a b) :
    ∫ x in a..b, csch x * coth x = csch a - csch b := by
  rw [integral_eq_sub_of_hasDerivAt (f := fun y => -csch y)
    (fun x hx => hasDerivAt_neg_csch (fun h0 => h (h0 ▸ hx)))
    ((continuousOn_csch h).mul (continuousOn_coth h) |>.intervalIntegrable)]
  ring

/-! ## Derivatives of the inverse hyperbolic functions (CA-131, CA-302) -/

/-- OpenStax Calculus 2:§2.9 Table 2.4 (CA-131, CA-302): `arsinh' x = 1/√(x²+1)`. -/
@[kb "openstaxcalculus2016" "2:§2.9 Table 2.4 (derivatives of inverse hyperbolic functions), p. 225"]
theorem hasDerivAt_arsinh' (x : ℝ) : HasDerivAt arsinh (1 / √(x ^ 2 + 1)) x := by
  refine (Real.hasDerivAt_arsinh x).congr_deriv ?_
  rw [add_comm 1, one_div]

/-- OpenStax Calculus 2:§2.9 Table 2.4 (CA-131, CA-302): `arcosh' x = 1/√(x²-1)` for `x > 1`. -/
@[kb "openstaxcalculus2016" "2:§2.9 Table 2.4 (derivatives of inverse hyperbolic functions), p. 225"]
theorem hasDerivAt_arcosh' {x : ℝ} (hx : 1 < x) : HasDerivAt arcosh (1 / √(x ^ 2 - 1)) x := by
  rw [one_div]; exact Real.hasDerivAt_arcosh hx

/-- OpenStax Calculus 2:§2.9 Table 2.4 (CA-131, CA-302): `artanh' x = 1/(1-x²)` for `|x| < 1`. -/
@[kb "openstaxcalculus2016" "2:§2.9 Table 2.4 (derivatives of inverse hyperbolic functions), p. 225"]
theorem hasDerivAt_artanh {x : ℝ} (hx : |x| < 1) : HasDerivAt artanh (1 / (1 - x ^ 2)) x := by
  have hx' := abs_lt.mp hx
  have h1 : (1 + x) ≠ 0 := by linarith
  have h2 : (1 - x) ≠ 0 := by linarith
  have hA : HasDerivAt (fun y : ℝ => 1 + y) 1 x := (hasDerivAt_id x).const_add 1
  have hB : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := (hasDerivAt_id x).const_sub 1
  have h := ((hA.log h1).sub (hB.log h2)).const_mul (1 / 2)
  have hev : (fun y : ℝ => 1 / 2 * (log (1 + y) - log (1 - y))) =ᶠ[𝓝 x] artanh := by
    filter_upwards [isOpen_Ioo.mem_nhds (show x ∈ Ioo (-1 : ℝ) 1 from ⟨hx'.1, hx'.2⟩)] with y hy
    rw [Real.artanh_eq_half_log ⟨hy.1.le, hy.2.le⟩,
      Real.log_div (by linarith [hy.1]) (by linarith [hy.2])]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith
  refine (h.congr_deriv ?_).congr_of_eventuallyEq hev.symm
  field_simp
  ring

/-- OpenStax Calculus 2:§2.9 Table 2.4 (CA-131, CA-302): `arcoth' x = 1/(1-x²)` for `|x| > 1`. -/
@[kb "openstaxcalculus2016" "2:§2.9 Table 2.4 (derivatives of inverse hyperbolic functions), p. 225"]
theorem hasDerivAt_arcoth {x : ℝ} (hx : 1 < |x|) : HasDerivAt arcoth (1 / (1 - x ^ 2)) x := by
  have hx0 : x ≠ 0 := by rintro rfl; norm_num at hx
  have hi : |x⁻¹| < 1 := by rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hx
  have hsq : 1 < x ^ 2 := by
    have := sq_abs x
    nlinarith [abs_nonneg x]
  have h := (hasDerivAt_artanh hi).comp x (hasDerivAt_inv hx0)
  refine h.congr_deriv ?_
  have : 1 - x ^ 2 ≠ 0 := by linarith
  have : x ^ 2 - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- OpenStax Calculus 2:§2.9 Table 2.4 (CA-131, CA-302): `arsech' x = -1/(x √(1-x²))` for `0 < x < 1`. -/
@[kb "openstaxcalculus2016" "2:§2.9 Table 2.4 (derivatives of inverse hyperbolic functions), p. 225"]
theorem hasDerivAt_arsech {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    HasDerivAt arsech (-1 / (x * √(1 - x ^ 2))) x := by
  have hi : 1 < x⁻¹ := one_lt_inv₀ hx |>.mpr hx1
  have h := (hasDerivAt_arcosh' hi).comp x (hasDerivAt_inv hx.ne')
  refine h.congr_deriv ?_
  have hs : √(x⁻¹ ^ 2 - 1) = √(1 - x ^ 2) / x := by
    have : x⁻¹ ^ 2 - 1 = (1 - x ^ 2) / x ^ 2 := by field_simp
    rw [this, Real.sqrt_div' _ (sq_nonneg x), Real.sqrt_sq hx.le]
  have hp : 0 < √(1 - x ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  rw [hs]
  field_simp

/-- OpenStax Calculus 2:§2.9 Table 2.4 (CA-131, CA-302): `arcsch' x = -1/(|x| √(1+x²))` for `x ≠ 0`. -/
@[kb "openstaxcalculus2016" "2:§2.9 Table 2.4 (derivatives of inverse hyperbolic functions), p. 225"]
theorem hasDerivAt_arcsch {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt arcsch (-1 / (|x| * √(1 + x ^ 2))) x := by
  have h := (Real.hasDerivAt_arsinh x⁻¹).comp x (hasDerivAt_inv hx)
  refine h.congr_deriv ?_
  have hs : √(1 + x⁻¹ ^ 2) = √(1 + x ^ 2) / |x| := by
    have : 1 + x⁻¹ ^ 2 = (1 + x ^ 2) / |x| ^ 2 := by rw [sq_abs]; field_simp; ring
    rw [this, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq (abs_nonneg x)]
  have hp : 0 < √(1 + x ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have ha : 0 < |x| := abs_pos.mpr hx
  rw [hs]
  have hx2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  rw [hx2]
  field_simp

/-! ## Integrals giving inverse hyperbolic functions (CA-212, CA-303) -/

/-- OpenStax Calculus 2:§2.9 integration formulas with inverse hyperbolic functions (CA-212, CA-303):
`d/du arsinh (u/a) = 1/√(a²+u²)` for `a > 0`. -/
@[kb "openstaxcalculus2016" "2:§2.9 Integration formulas with inverse hyperbolic functions, p. 226"]
theorem hasDerivAt_arsinh_div {a : ℝ} (ha : 0 < a) (u : ℝ) :
    HasDerivAt (fun y => arsinh (y / a)) (1 / √(a ^ 2 + u ^ 2)) u := by
  have h := (hasDerivAt_arsinh' (u / a)).comp u ((hasDerivAt_id u).div_const a)
  refine h.congr_deriv ?_
  have hs : √((u / a) ^ 2 + 1) = √(a ^ 2 + u ^ 2) / a := by
    have : (u / a) ^ 2 + 1 = (a ^ 2 + u ^ 2) / a ^ 2 := by field_simp; ring
    rw [this, Real.sqrt_div' _ (sq_nonneg a), Real.sqrt_sq ha.le]
  have hp : 0 < √(a ^ 2 + u ^ 2) := Real.sqrt_pos.mpr (by positivity)
  rw [hs]
  field_simp

/-- OpenStax Calculus 2:§2.9 integration formulas with inverse hyperbolic functions (CA-212, CA-303):
`d/du arcosh (u/a) = 1/√(u²-a²)` for `u > a > 0`. -/
@[kb "openstaxcalculus2016" "2:§2.9 Integration formulas with inverse hyperbolic functions, p. 226"]
theorem hasDerivAt_arcosh_div {a : ℝ} (ha : 0 < a) {u : ℝ} (hu : a < u) :
    HasDerivAt (fun y => arcosh (y / a)) (1 / √(u ^ 2 - a ^ 2)) u := by
  have hi : 1 < u / a := (one_lt_div ha).mpr hu
  have h := (hasDerivAt_arcosh' hi).comp u ((hasDerivAt_id u).div_const a)
  refine h.congr_deriv ?_
  have hs : √((u / a) ^ 2 - 1) = √(u ^ 2 - a ^ 2) / a := by
    have : (u / a) ^ 2 - 1 = (u ^ 2 - a ^ 2) / a ^ 2 := by field_simp
    rw [this, Real.sqrt_div' _ (sq_nonneg a), Real.sqrt_sq ha.le]
  have hp : 0 < √(u ^ 2 - a ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  rw [hs]
  field_simp

/-- OpenStax Calculus 2:§2.9 integration formulas with inverse hyperbolic functions (CA-212, CA-303):
`d/du (1/a) artanh (u/a) = 1/(a²-u²)` for `|u| < a`, `a > 0`. -/
@[kb "openstaxcalculus2016" "2:§2.9 Integration formulas with inverse hyperbolic functions, p. 226"]
theorem hasDerivAt_artanh_div {a : ℝ} (ha : 0 < a) {u : ℝ} (hu : |u| < a) :
    HasDerivAt (fun y => (1 / a) * artanh (y / a)) (1 / (a ^ 2 - u ^ 2)) u := by
  have hi : |u / a| < 1 := by
    rw [abs_div, abs_of_pos ha]; exact (div_lt_one ha).mpr hu
  have h := ((hasDerivAt_artanh hi).comp u ((hasDerivAt_id u).div_const a)).const_mul (1 / a)
  refine h.congr_deriv ?_
  have : a ^ 2 - u ^ 2 ≠ 0 := by nlinarith [sq_abs u, abs_nonneg u]
  have h2 : 1 - (u / a) ^ 2 ≠ 0 := by
    intro h0; apply this; field_simp at h0; linarith
  field_simp

/-- OpenStax Calculus 2:§2.9 integration formulas with inverse hyperbolic functions (CA-212, CA-303):
`d/du (1/a) arcoth (u/a) = 1/(a²-u²)` for `|u| > a > 0`. -/
@[kb "openstaxcalculus2016" "2:§2.9 Integration formulas with inverse hyperbolic functions, p. 226"]
theorem hasDerivAt_arcoth_div {a : ℝ} (ha : 0 < a) {u : ℝ} (hu : a < |u|) :
    HasDerivAt (fun y => (1 / a) * arcoth (y / a)) (1 / (a ^ 2 - u ^ 2)) u := by
  have hi : 1 < |u / a| := by
    rw [abs_div, abs_of_pos ha]; exact (one_lt_div ha).mpr hu
  have h := ((hasDerivAt_arcoth hi).comp u ((hasDerivAt_id u).div_const a)).const_mul (1 / a)
  refine h.congr_deriv ?_
  have : a ^ 2 - u ^ 2 ≠ 0 := by nlinarith [sq_abs u, abs_nonneg u]
  have h2 : 1 - (u / a) ^ 2 ≠ 0 := by
    intro h0; apply this; field_simp at h0; linarith
  field_simp

/-- OpenStax Calculus 2:§2.9 integration formulas with inverse hyperbolic functions (CA-212, CA-303):
`d/du (-(1/a)) arsech (u/a) = 1/(u √(a²-u²))` for `0 < u < a`. -/
@[kb "openstaxcalculus2016" "2:§2.9 Integration formulas with inverse hyperbolic functions, p. 226"]
theorem hasDerivAt_arsech_div {a : ℝ} (ha : 0 < a) {u : ℝ} (hu : 0 < u) (hua : u < a) :
    HasDerivAt (fun y => -(1 / a) * arsech (y / a)) (1 / (u * √(a ^ 2 - u ^ 2))) u := by
  have h0 : 0 < u / a := div_pos hu ha
  have h1 : u / a < 1 := (div_lt_one ha).mpr hua
  have h := ((hasDerivAt_arsech h0 h1).comp u ((hasDerivAt_id u).div_const a)).const_mul (-(1 / a))
  refine h.congr_deriv ?_
  have hs : √(1 - (u / a) ^ 2) = √(a ^ 2 - u ^ 2) / a := by
    have : 1 - (u / a) ^ 2 = (a ^ 2 - u ^ 2) / a ^ 2 := by field_simp
    rw [this, Real.sqrt_div' _ (sq_nonneg a), Real.sqrt_sq ha.le]
  have hp : 0 < √(a ^ 2 - u ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  rw [hs]
  field_simp

/-- OpenStax Calculus 2:§2.9 integration formulas with inverse hyperbolic functions (CA-212, CA-303):
`d/du (-(1/a)) arcsch (u/a) = 1/(u √(a²+u²))` for `u > 0`, `a > 0`. -/
@[kb "openstaxcalculus2016" "2:§2.9 Integration formulas with inverse hyperbolic functions, p. 226"]
theorem hasDerivAt_arcsch_div {a : ℝ} (ha : 0 < a) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun y => -(1 / a) * arcsch (y / a)) (1 / (u * √(a ^ 2 + u ^ 2))) u := by
  have h0 : u / a ≠ 0 := (div_pos hu ha).ne'
  have h := ((hasDerivAt_arcsch h0).comp u ((hasDerivAt_id u).div_const a)).const_mul (-(1 / a))
  refine h.congr_deriv ?_
  have hs : √(1 + (u / a) ^ 2) = √(a ^ 2 + u ^ 2) / a := by
    have : 1 + (u / a) ^ 2 = (a ^ 2 + u ^ 2) / a ^ 2 := by field_simp
    rw [this, Real.sqrt_div' _ (sq_nonneg a), Real.sqrt_sq ha.le]
  have hp : 0 < √(a ^ 2 + u ^ 2) := Real.sqrt_pos.mpr (by positivity)
  rw [hs, abs_of_pos (div_pos hu ha)]
  field_simp

end UndergradKB.Calculus
