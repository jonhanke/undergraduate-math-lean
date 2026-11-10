import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import UndergradKB.Common.Attr
import UndergradKB.Calculus.Defs
import UndergradKB.Calculus.Trig

/-! # Calculus: derivatives of the trigonometric and inverse trigonometric functions

Derivatives of `cot`, `sec`, `csc`, the cyclic behaviour of the derivatives of `sin` and `cos`, chain-rule forms, and
derivatives of `arccot`, `arcsec`, `arccsc`. -/

namespace UndergradKB.Calculus

open Real Set

/-! ## Derivatives of cot, sec, csc -/

/-- OpenStax Calculus 1:Theorem 3.9 (CA-108). `(cot x)' = -csc² x` where `sin x ≠ 0`. -/
@[kb "openstaxcalculus2016" "1:Theorem 3.9, p. 254"]
theorem hasDerivAt_cot {x : ℝ} (h : Real.sin x ≠ 0) : HasDerivAt Real.cot (-(csc x ^ 2)) x := by
  have e : Real.cot = fun y => Real.cos y / Real.sin y := funext Real.cot_eq_cos_div_sin
  rw [e]
  refine ((Real.hasDerivAt_cos x).div (Real.hasDerivAt_sin x) h).congr_deriv ?_
  unfold csc
  have := Real.sin_sq_add_cos_sq x
  field_simp
  linarith

/-- OpenStax Calculus 1:Theorem 3.9 (CA-109). `(sec x)' = sec x tan x` where `cos x ≠ 0`. -/
@[kb "openstaxcalculus2016" "1:Theorem 3.9, p. 254"]
theorem hasDerivAt_sec {x : ℝ} (h : Real.cos x ≠ 0) : HasDerivAt sec (sec x * Real.tan x) x := by
  have e : sec = fun y => 1 / Real.cos y := rfl
  rw [e]
  refine ((hasDerivAt_const x (1 : ℝ)).div (Real.hasDerivAt_cos x) h).congr_deriv ?_
  beta_reduce
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  ring

/-- OpenStax Calculus 1:Theorem 3.9 (CA-110). `(csc x)' = -csc x cot x` where `sin x ≠ 0`. -/
@[kb "openstaxcalculus2016" "1:Theorem 3.9, p. 254"]
theorem hasDerivAt_csc {x : ℝ} (h : Real.sin x ≠ 0) :
    HasDerivAt csc (-(csc x * Real.cot x)) x := by
  have e : csc = fun y => 1 / Real.sin y := rfl
  rw [e]
  refine ((hasDerivAt_const x (1 : ℝ)).div (Real.hasDerivAt_sin x) h).congr_deriv ?_
  beta_reduce
  rw [Real.cot_eq_cos_div_sin]
  field_simp
  ring

/-- Companion to CA-108–110: `(tan x)' = sec² x` where `cos x ≠ 0`. -/
@[kb "openstaxcalculus2016" "1:Theorem 3.9, p. 254"]
theorem hasDerivAt_tan_sec_sq {x : ℝ} (h : Real.cos x ≠ 0) : HasDerivAt Real.tan (sec x ^ 2) x := by
  have := Real.hasDerivAt_tan h
  unfold sec
  rwa [one_div_pow]

/-! ## Derivatives of sin and cos of all orders -/

/-- OpenStax Calculus 1:Example 3.45 (CA-111). The `n`-th derivative of `sin` depends only on `n mod 4`. -/
@[kb "openstaxcalculus2016" "1:Example 3.45, p. 255"]
theorem iteratedDeriv_sin (n : ℕ) :
    iteratedDeriv n Real.sin =
      if n % 4 = 0 then Real.sin else if n % 4 = 1 then Real.cos
      else if n % 4 = 2 then -Real.sin else -Real.cos := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    have h : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
    rcases h with h | h | h | h
    · have h' : (n + 1) % 4 = 1 := by omega
      simp [h, h', Real.deriv_sin]
    · have h' : (n + 1) % 4 = 2 := by omega
      simp [h, h', Real.deriv_cos]
      rfl
    · have h' : (n + 1) % 4 = 3 := by omega
      simp [h, h', Real.deriv_sin]
      rfl
    · have h' : (n + 1) % 4 = 0 := by omega
      simp [h, h', Real.deriv_cos]

/-- OpenStax Calculus 1:Example 3.46 (CA-111). The `n`-th derivative of `cos` depends only on `n mod 4`. -/
@[kb "openstaxcalculus2016" "1:Example 3.46, p. 255"]
theorem iteratedDeriv_cos (n : ℕ) :
    iteratedDeriv n Real.cos =
      if n % 4 = 0 then Real.cos else if n % 4 = 1 then -Real.sin
      else if n % 4 = 2 then -Real.cos else Real.sin := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    have h : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
    rcases h with h | h | h | h
    · have h' : (n + 1) % 4 = 1 := by omega
      simp [h, h', Real.deriv_cos]
      rfl
    · have h' : (n + 1) % 4 = 2 := by omega
      simp [h, h', Real.deriv_sin]
      rfl
    · have h' : (n + 1) % 4 = 3 := by omega
      simp [h, h', Real.deriv_cos]
    · have h' : (n + 1) % 4 = 0 := by omega
      simp [h, h', Real.deriv_sin]

/-- OpenStax Calculus 1:Example 3.45 (CA-111). Period four: `sin⁽ⁿ⁺⁴⁾ = sin⁽ⁿ⁾`. -/
@[kb "openstaxcalculus2016" "1:Example 3.45, p. 255"]
theorem iteratedDeriv_sin_add_four (n : ℕ) : iteratedDeriv (n + 4) Real.sin = iteratedDeriv n Real.sin := by
  rw [iteratedDeriv_sin, iteratedDeriv_sin]
  have : (n + 4) % 4 = n % 4 := by omega
  rw [this]

/-- OpenStax Calculus 1:Example 3.46 (CA-111). Period four: `cos⁽ⁿ⁺⁴⁾ = cos⁽ⁿ⁾`. -/
@[kb "openstaxcalculus2016" "1:Example 3.46, p. 255"]
theorem iteratedDeriv_cos_add_four (n : ℕ) : iteratedDeriv (n + 4) Real.cos = iteratedDeriv n Real.cos := by
  rw [iteratedDeriv_cos, iteratedDeriv_cos]
  have : (n + 4) % 4 = n % 4 := by omega
  rw [this]

/-! ## Chain-rule forms -/

section Chain

variable {g : ℝ → ℝ} {g' x : ℝ}

/-- OpenStax Calculus 1:Theorem 3.10 (CA-114). `(sin g)' = g' cos g`. -/
@[kb "openstaxcalculus2016" "1:Theorem 3.10, p. 262"]
theorem hasDerivAt_sin_comp (hg : HasDerivAt g g' x) :
    HasDerivAt (fun y => Real.sin (g y)) (g' * Real.cos (g x)) x := by
  simpa [mul_comm] using hg.sin

/-- OpenStax Calculus 1:Theorem 3.10 (CA-114). `(cos g)' = -g' sin g`. -/
@[kb "openstaxcalculus2016" "1:Theorem 3.10, p. 262"]
theorem hasDerivAt_cos_comp (hg : HasDerivAt g g' x) :
    HasDerivAt (fun y => Real.cos (g y)) (-(g' * Real.sin (g x))) x := by
  have := hg.cos
  convert this using 1
  ring

/-- OpenStax Calculus 1:Theorem 3.10 (CA-114). `(tan g)' = g' sec² g` where `cos (g x) ≠ 0`. -/
@[kb "openstaxcalculus2016" "1:Theorem 3.10, p. 262"]
theorem hasDerivAt_tan_comp (hg : HasDerivAt g g' x) (h : Real.cos (g x) ≠ 0) :
    HasDerivAt (fun y => Real.tan (g y)) (g' * sec (g x) ^ 2) x := by
  exact ((hasDerivAt_tan_sec_sq h).comp x hg).congr_deriv (by ring)

/-- OpenStax Calculus 1:Theorem 3.10 (CA-114). `(cot g)' = -g' csc² g` where `sin (g x) ≠ 0`. -/
@[kb "openstaxcalculus2016" "1:Theorem 3.10, p. 262"]
theorem hasDerivAt_cot_comp (hg : HasDerivAt g g' x) (h : Real.sin (g x) ≠ 0) :
    HasDerivAt (fun y => Real.cot (g y)) (-(g' * csc (g x) ^ 2)) x := by
  exact ((hasDerivAt_cot h).comp x hg).congr_deriv (by ring)

/-- OpenStax Calculus 1:Theorem 3.10 (CA-114). `(sec g)' = g' sec g tan g` where `cos (g x) ≠ 0`. -/
@[kb "openstaxcalculus2016" "1:Theorem 3.10, p. 262"]
theorem hasDerivAt_sec_comp (hg : HasDerivAt g g' x) (h : Real.cos (g x) ≠ 0) :
    HasDerivAt (fun y => sec (g y)) (g' * (sec (g x) * Real.tan (g x))) x := by
  exact ((hasDerivAt_sec h).comp x hg).congr_deriv (by ring)

/-- OpenStax Calculus 1:Theorem 3.10 (CA-114). `(csc g)' = -g' csc g cot g` where `sin (g x) ≠ 0`. -/
@[kb "openstaxcalculus2016" "1:Theorem 3.10, p. 262"]
theorem hasDerivAt_csc_comp (hg : HasDerivAt g g' x) (h : Real.sin (g x) ≠ 0) :
    HasDerivAt (fun y => csc (g y)) (-(g' * (csc (g x) * Real.cot (g x)))) x := by
  exact ((hasDerivAt_csc h).comp x hg).congr_deriv (by ring)

end Chain

/-! ## Derivatives of the inverse trigonometric functions -/

/-- OpenStax Calculus 1:Theorem 3.13 (CA-121). `(arccot x)' = -1/(1+x²)`. -/
@[kb "openstaxcalculus2016" "1:Theorem 3.13, p. 272"]
theorem hasDerivAt_arccot (x : ℝ) : HasDerivAt arccot (-(1 / (1 + x ^ 2))) x := by
  unfold arccot
  exact (Real.hasDerivAt_arctan x).const_sub (π / 2)

/-- `√(1 - 1/y²) = √(y² - 1)/|y|` for `|y| > 1`. -/
theorem sqrt_one_sub_inv_sq {y : ℝ} (hy : 1 < |y|) :
    √(1 - (y⁻¹) ^ 2) = √(y ^ 2 - 1) / |y| := by
  have h0 : y ≠ 0 := by rintro rfl; simp at hy; linarith
  have h1 : 0 ≤ y ^ 2 - 1 := by nlinarith [sq_abs y, abs_nonneg y]
  have : 1 - (y⁻¹) ^ 2 = (y ^ 2 - 1) / y ^ 2 := by field_simp
  rw [this, Real.sqrt_div h1, Real.sqrt_sq_eq_abs]

/-- OpenStax Calculus 1:Theorem 3.13 (CA-121). `(arcsec x)' = 1/(|x| √(x²-1))` for `|x| > 1`. -/
@[kb "openstaxcalculus2016" "1:Theorem 3.13, p. 272"]
theorem hasDerivAt_arcsec {x : ℝ} (hx : 1 < |x|) :
    HasDerivAt arcsec (1 / (|x| * √(x ^ 2 - 1))) x := by
  have h0 : x ≠ 0 := by rintro rfl; simp at hx; linarith
  have hne1 : x⁻¹ ≠ -1 := by
    intro h; have := congrArg abs h; rw [abs_inv] at this; simp at this; linarith
  have hne2 : x⁻¹ ≠ 1 := by
    intro h; have := congrArg abs h; rw [abs_inv] at this; simp at this; linarith
  have h := (Real.hasDerivAt_arccos hne1 hne2).comp x (hasDerivAt_inv h0)
  have e : arcsec = Real.arccos ∘ (fun y => y⁻¹) := by funext y; simp [arcsec]
  rw [e]
  refine h.congr_deriv ?_
  rw [sqrt_one_sub_inv_sq hx]
  have hs : 0 < √(x ^ 2 - 1) := Real.sqrt_pos.2 (by nlinarith [sq_abs x, abs_nonneg x])
  have hx2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have hxa : 0 < |x| := by linarith
  rw [hx2]
  field_simp

/-- OpenStax Calculus 1:Theorem 3.13 (CA-121). `(arccsc x)' = -1/(|x| √(x²-1))` for `|x| > 1`. -/
@[kb "openstaxcalculus2016" "1:Theorem 3.13, p. 272"]
theorem hasDerivAt_arccsc {x : ℝ} (hx : 1 < |x|) :
    HasDerivAt arccsc (-(1 / (|x| * √(x ^ 2 - 1)))) x := by
  have h0 : x ≠ 0 := by rintro rfl; simp at hx; linarith
  have hne1 : x⁻¹ ≠ -1 := by
    intro h; have := congrArg abs h; rw [abs_inv] at this; simp at this; linarith
  have hne2 : x⁻¹ ≠ 1 := by
    intro h; have := congrArg abs h; rw [abs_inv] at this; simp at this; linarith
  have h := (Real.hasDerivAt_arcsin hne1 hne2).comp x (hasDerivAt_inv h0)
  have e : arccsc = Real.arcsin ∘ (fun y => y⁻¹) := by funext y; simp [arccsc]
  rw [e]
  refine h.congr_deriv ?_
  rw [sqrt_one_sub_inv_sq hx]
  have hs : 0 < √(x ^ 2 - 1) := Real.sqrt_pos.2 (by nlinarith [sq_abs x, abs_nonneg x])
  have hx2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have hxa : 0 < |x| := by linarith
  rw [hx2]
  field_simp

end UndergradKB.Calculus
