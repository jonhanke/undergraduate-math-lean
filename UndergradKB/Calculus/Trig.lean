import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import UndergradKB.Common.Attr
import UndergradKB.Calculus.Defs

/-! # Calculus: trigonometric identities, inverse trigonometric functions, continuity

Reciprocal and Pythagorean identities, the generalized sine function, the six inverse trigonometric functions
(arccot, arcsec, arccsc are defined here with the book's principal ranges), and continuity of the six
trigonometric functions on their domains. -/

namespace UndergradKB.Calculus

open Real Set

/-! ## Reciprocal and Pythagorean identities -/

/-- OpenStax Calculus 1:§1.3 (CA-017). Reciprocal identities: `tan = sin / cos`, `cot = 1 / tan`,
`sec = 1 / cos`, `csc = 1 / sin`, and `cot = cos / sin`. -/
@[kb "openstaxcalculus2016" "1:§1.3 Rule: Trigonometric Identities (reciprocal identities), p. 66"]
theorem reciprocal_identities (x : ℝ) :
    Real.tan x = Real.sin x / Real.cos x ∧ Real.cot x = 1 / Real.tan x ∧
    sec x = 1 / Real.cos x ∧ csc x = 1 / Real.sin x ∧ Real.cot x = Real.cos x / Real.sin x := by
  refine ⟨Real.tan_eq_sin_div_cos x, ?_, rfl, rfl, Real.cot_eq_cos_div_sin x⟩
  rw [Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin, one_div, inv_div]

/-- OpenStax Calculus 1:§1.3 (CA-017). Where cosine is nonzero, `sec x * cos x = 1`. -/
@[kb "openstaxcalculus2016" "1:§1.3 Definition (trigonometric functions), p. 63"]
theorem sec_mul_cos {x : ℝ} (h : Real.cos x ≠ 0) : sec x * Real.cos x = 1 := by
  unfold sec; field_simp

/-- OpenStax Calculus 1:§1.3 (CA-017). Where sine is nonzero, `csc x * sin x = 1`. -/
@[kb "openstaxcalculus2016" "1:§1.3 Definition (trigonometric functions), p. 63"]
theorem csc_mul_sin {x : ℝ} (h : Real.sin x ≠ 0) : csc x * Real.sin x = 1 := by
  unfold csc; field_simp

/-- OpenStax Calculus 1:§1.3 (CA-019). `sin² x + cos² x = 1`. -/
@[kb "openstaxcalculus2016" "1:§1.3 Rule: Trigonometric Identities (Pythagorean), p. 66"]
theorem sin_sq_add_cos_sq' (x : ℝ) : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 :=
  Real.sin_sq_add_cos_sq x

/-- OpenStax Calculus 1:§1.3 (CA-019). `1 + tan² x = sec² x` wherever `cos x ≠ 0`. -/
@[kb "openstaxcalculus2016" "1:§1.3 Rule: Trigonometric Identities (Pythagorean), p. 66"]
theorem one_add_tan_sq {x : ℝ} (h : Real.cos x ≠ 0) : 1 + Real.tan x ^ 2 = sec x ^ 2 := by
  unfold sec
  rw [Real.tan_eq_sin_div_cos]
  have := Real.sin_sq_add_cos_sq x
  field_simp
  linarith

/-- OpenStax Calculus 1:§1.3 (CA-019). `1 + cot² x = csc² x` wherever `sin x ≠ 0`. -/
@[kb "openstaxcalculus2016" "1:§1.3 Rule: Trigonometric Identities (Pythagorean), p. 66"]
theorem one_add_cot_sq {x : ℝ} (h : Real.sin x ≠ 0) : 1 + Real.cot x ^ 2 = csc x ^ 2 := by
  unfold csc
  rw [Real.cot_eq_cos_div_sin]
  have := Real.sin_sq_add_cos_sq x
  field_simp
  linarith

/-! ## The generalized sine function -/

/-- OpenStax Calculus 1:§1.3 (CA-022). `x ↦ A sin(B(x-α)) + d` is `2π/|B|`-periodic for `B ≠ 0`. -/
@[kb "openstaxcalculus2016" "1:§1.3 Key Equations (generalized sine function), p. 108"]
theorem generalized_sin_periodic (A B α d : ℝ) (hB : B ≠ 0) :
    Function.Periodic (fun x => A * Real.sin (B * (x - α)) + d) (2 * π / |B|) := by
  intro x
  simp only
  rcases lt_or_gt_of_ne hB with hneg | hpos
  · have h : B * (x + 2 * π / |B| - α) = B * (x - α) - 2 * π := by
      rw [abs_of_neg hneg]; field_simp; ring
    rw [h, Real.sin_sub_two_pi]
  · have h : B * (x + 2 * π / |B| - α) = B * (x - α) + 2 * π := by
      rw [abs_of_pos hpos]; field_simp; ring
    rw [h, Real.sin_add_two_pi]

/-- OpenStax Calculus 1:§1.3 (CA-022). The range of `x ↦ A sin(B(x-α)) + d` (`B ≠ 0`) is
`[d - |A|, d + |A|]`. -/
@[kb "openstaxcalculus2016" "1:§1.3 Key Equations (generalized sine function), p. 108"]
theorem generalized_sin_range (A B α d : ℝ) (hB : B ≠ 0) :
    Set.range (fun x => A * Real.sin (B * (x - α)) + d) = Icc (d - |A|) (d + |A|) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    have h1 := Real.abs_sin_le_one (B * (x - α))
    have h2 : |A * Real.sin (B * (x - α))| ≤ |A| := by
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) h1
    have := abs_le.mp h2
    constructor <;> simp only <;> linarith [this.1, this.2]
  · rintro ⟨h1, h2⟩
    by_cases hA : A = 0
    · subst hA
      simp at h1 h2
      exact ⟨0, by simp; linarith⟩
    · have hApos : 0 < |A| := abs_pos.mpr hA
      have hs : |(y - d) / A| ≤ 1 := by
        rw [abs_div, div_le_one hApos, abs_le]; constructor <;> linarith
      have hs' := abs_le.mp hs
      refine ⟨(Real.arcsin ((y - d) / A)) / B + α, ?_⟩
      simp only
      rw [add_sub_cancel_right, mul_div_cancel₀ _ hB, Real.sin_arcsin hs'.1 hs'.2]
      field_simp; ring

/-! ## Inverse trigonometric functions -/

/-- The inverse cotangent with the book's principal range `(0, π)`: `arccot x = π/2 - arctan x`
(OpenStax Calculus 1, §1.4). -/
noncomputable def arccot (x : ℝ) : ℝ := π / 2 - Real.arctan x

/-- The inverse secant with the book's principal range `[0, π] \ {π/2}`, for `|x| ≥ 1`:
`arcsec x = arccos (1/x)` (OpenStax Calculus 1, §1.4). -/
noncomputable def arcsec (x : ℝ) : ℝ := Real.arccos (1 / x)

/-- The inverse cosecant with the book's principal range `[-π/2, π/2] \ {0}`, for `|x| ≥ 1`:
`arccsc x = arcsin (1/x)` (OpenStax Calculus 1, §1.4). -/
noncomputable def arccsc (x : ℝ) : ℝ := Real.arcsin (1 / x)

/-- OpenStax Calculus 1:§1.4 (CA-029). The principal range of `arccot` is `(0, π)`. -/
@[kb "openstaxcalculus2016" "1:§1.4 Definition (inverse trigonometric functions), p. 81"]
theorem arccot_mem_Ioo (x : ℝ) : arccot x ∈ Ioo 0 π := by
  unfold arccot
  have := Real.arctan_lt_pi_div_two x
  have := Real.neg_pi_div_two_lt_arctan x
  constructor <;> linarith [Real.pi_pos]

/-- OpenStax Calculus 1:§1.4 (CA-029). For `|x| ≥ 1`, `arcsec x ∈ [0, π]` and `arcsec x ≠ π/2`. -/
@[kb "openstaxcalculus2016" "1:§1.4 Definition (inverse trigonometric functions), p. 81"]
theorem arcsec_mem {x : ℝ} (hx : 1 ≤ |x|) : arcsec x ∈ Icc 0 π ∧ arcsec x ≠ π / 2 := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx; linarith
  refine ⟨⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩, ?_⟩
  intro h
  have h2 : Real.cos (arcsec x) = 0 := by rw [h]; exact Real.cos_pi_div_two
  unfold arcsec at h2
  have h3 : |1 / x| ≤ 1 := by
    rw [abs_div, abs_one, div_le_one (by linarith)]; exact hx
  rw [Real.cos_arccos (abs_le.mp h3).1 (abs_le.mp h3).2] at h2
  simp at h2
  exact hx0 h2

/-- OpenStax Calculus 1:§1.4 (CA-029). For `|x| ≥ 1`, `arccsc x ∈ [-π/2, π/2]` and `arccsc x ≠ 0`. -/
@[kb "openstaxcalculus2016" "1:§1.4 Definition (inverse trigonometric functions), p. 81"]
theorem arccsc_mem {x : ℝ} (hx : 1 ≤ |x|) : arccsc x ∈ Icc (-(π / 2)) (π / 2) ∧ arccsc x ≠ 0 := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx; linarith
  refine ⟨⟨Real.neg_pi_div_two_le_arcsin _, Real.arcsin_le_pi_div_two _⟩, ?_⟩
  intro h
  have h3 : |1 / x| ≤ 1 := by
    rw [abs_div, abs_one, div_le_one (by linarith)]; exact hx
  have h2 : Real.sin (arccsc x) = 0 := by rw [h]; exact Real.sin_zero
  unfold arccsc at h2
  rw [Real.sin_arcsin (abs_le.mp h3).1 (abs_le.mp h3).2] at h2
  simp at h2
  exact hx0 h2

/-- OpenStax Calculus 1:§1.4 (CA-030). `sin (arcsin x) = x` on `[-1, 1]`. -/
@[kb "openstaxcalculus2016" "1:§1.4 Inverse trigonometric functions, p. 82"]
theorem sin_arcsin' {x : ℝ} (h1 : -1 ≤ x) (h2 : x ≤ 1) : Real.sin (Real.arcsin x) = x :=
  Real.sin_arcsin h1 h2

/-- OpenStax Calculus 1:§1.4 (CA-030). `arcsin (sin x) = x` on `[-π/2, π/2]`. -/
@[kb "openstaxcalculus2016" "1:§1.4 Inverse trigonometric functions, p. 82"]
theorem arcsin_sin' {x : ℝ} (h1 : -(π / 2) ≤ x) (h2 : x ≤ π / 2) :
    Real.arcsin (Real.sin x) = x := Real.arcsin_sin h1 h2

/-- OpenStax Calculus 1:§1.4 (CA-030). `cos (arccos x) = x` on `[-1, 1]`. -/
@[kb "openstaxcalculus2016" "1:§1.4 Inverse trigonometric functions, p. 82"]
theorem cos_arccos' {x : ℝ} (h1 : -1 ≤ x) (h2 : x ≤ 1) : Real.cos (Real.arccos x) = x :=
  Real.cos_arccos h1 h2

/-- OpenStax Calculus 1:§1.4 (CA-030). `arccos (cos x) = x` on `[0, π]`. -/
@[kb "openstaxcalculus2016" "1:§1.4 Inverse trigonometric functions, p. 82"]
theorem arccos_cos' {x : ℝ} (h1 : 0 ≤ x) (h2 : x ≤ π) : Real.arccos (Real.cos x) = x :=
  Real.arccos_cos h1 h2

/-- OpenStax Calculus 1:§1.4 (CA-030). `tan (arctan x) = x` for all `x`. -/
@[kb "openstaxcalculus2016" "1:§1.4 Inverse trigonometric functions, p. 82"]
theorem tan_arctan' (x : ℝ) : Real.tan (Real.arctan x) = x := Real.tan_arctan x

/-- OpenStax Calculus 1:§1.4 (CA-030). `arctan (tan x) = x` on `(-π/2, π/2)`. -/
@[kb "openstaxcalculus2016" "1:§1.4 Inverse trigonometric functions, p. 82"]
theorem arctan_tan' {x : ℝ} (h1 : -(π / 2) < x) (h2 : x < π / 2) :
    Real.arctan (Real.tan x) = x := Real.arctan_tan h1 h2

/-- OpenStax Calculus 1:§1.4 (CA-030). `cot (arccot x) = x` for all `x`. -/
@[kb "openstaxcalculus2016" "1:§1.4 Inverse trigonometric functions, p. 82"]
theorem cot_arccot (x : ℝ) : Real.cot (arccot x) = x := by
  unfold arccot
  rw [Real.cot_eq_cos_div_sin, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub,
    ← Real.tan_eq_sin_div_cos, Real.tan_arctan]

/-- OpenStax Calculus 1:§1.4 (CA-030). `arccot (cot x) = x` on `(0, π)`. -/
@[kb "openstaxcalculus2016" "1:§1.4 Inverse trigonometric functions, p. 82"]
theorem arccot_cot {x : ℝ} (h1 : 0 < x) (h2 : x < π) : arccot (Real.cot x) = x := by
  have h : Real.cot x = Real.tan (π / 2 - x) := by
    rw [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, Real.cos_pi_div_two_sub,
      Real.sin_pi_div_two_sub]
  unfold arccot
  rw [h, Real.arctan_tan (by linarith) (by linarith)]
  ring

/-- OpenStax Calculus 1:§1.4 (CA-030). `sec (arcsec x) = x` for `|x| ≥ 1`. -/
@[kb "openstaxcalculus2016" "1:§1.4 Inverse trigonometric functions, p. 82"]
theorem sec_arcsec {x : ℝ} (hx : 1 ≤ |x|) : sec (arcsec x) = x := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx; linarith
  have h3 : |1 / x| ≤ 1 := by
    rw [abs_div, abs_one, div_le_one (by linarith)]; exact hx
  unfold sec arcsec
  rw [Real.cos_arccos (abs_le.mp h3).1 (abs_le.mp h3).2]
  field_simp

/-- OpenStax Calculus 1:§1.4 (CA-030). `arcsec (sec x) = x` for `x ∈ [0, π]`, `x ≠ π/2`. -/
@[kb "openstaxcalculus2016" "1:§1.4 Inverse trigonometric functions, p. 82"]
theorem arcsec_sec {x : ℝ} (h1 : 0 ≤ x) (h2 : x ≤ π) (_h3 : x ≠ π / 2) :
    arcsec (sec x) = x := by
  unfold arcsec sec
  rw [one_div_one_div]
  exact Real.arccos_cos h1 h2

/-- OpenStax Calculus 1:§1.4 (CA-030). `csc (arccsc x) = x` for `|x| ≥ 1`. -/
@[kb "openstaxcalculus2016" "1:§1.4 Inverse trigonometric functions, p. 82"]
theorem csc_arccsc {x : ℝ} (hx : 1 ≤ |x|) : csc (arccsc x) = x := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx; linarith
  have h3 : |1 / x| ≤ 1 := by
    rw [abs_div, abs_one, div_le_one (by linarith)]; exact hx
  unfold csc arccsc
  rw [Real.sin_arcsin (abs_le.mp h3).1 (abs_le.mp h3).2]
  field_simp

/-- OpenStax Calculus 1:§1.4 (CA-030). `arccsc (csc x) = x` for `x ∈ [-π/2, π/2]`, `x ≠ 0`. -/
@[kb "openstaxcalculus2016" "1:§1.4 Inverse trigonometric functions, p. 82"]
theorem arccsc_csc {x : ℝ} (h1 : -(π / 2) ≤ x) (h2 : x ≤ π / 2) (_h3 : x ≠ 0) :
    arccsc (csc x) = x := by
  unfold arccsc csc
  rw [one_div_one_div]
  exact Real.arcsin_sin h1 h2

/-! ## Continuity -/

/-- OpenStax Calculus 1:Theorem 2.10 (CA-081). `tan` is continuous on `{x | cos x ≠ 0}`. -/
@[kb "openstaxcalculus2016" "1:Theorem 2.10, p. 171"]
theorem continuousOn_tan' : ContinuousOn Real.tan {x | Real.cos x ≠ 0} := by
  have : Real.tan = fun x => Real.sin x / Real.cos x := funext Real.tan_eq_sin_div_cos
  rw [this]
  exact Real.continuous_sin.continuousOn.div Real.continuous_cos.continuousOn (fun x hx => hx)

/-- OpenStax Calculus 1:Theorem 2.10 (CA-081). `cot` is continuous on `{x | sin x ≠ 0}`. -/
@[kb "openstaxcalculus2016" "1:Theorem 2.10, p. 171"]
theorem continuousOn_cot : ContinuousOn Real.cot {x | Real.sin x ≠ 0} := by
  have : Real.cot = fun x => Real.cos x / Real.sin x := funext Real.cot_eq_cos_div_sin
  rw [this]
  exact Real.continuous_cos.continuousOn.div Real.continuous_sin.continuousOn (fun x hx => hx)

/-- OpenStax Calculus 1:Theorem 2.10 (CA-081). `sec` is continuous on `{x | cos x ≠ 0}`. -/
@[kb "openstaxcalculus2016" "1:Theorem 2.10, p. 171"]
theorem continuousOn_sec : ContinuousOn sec {x | Real.cos x ≠ 0} := by
  unfold sec
  exact continuousOn_const.div Real.continuous_cos.continuousOn (fun x hx => hx)

/-- OpenStax Calculus 1:Theorem 2.10 (CA-081). `csc` is continuous on `{x | sin x ≠ 0}`. -/
@[kb "openstaxcalculus2016" "1:Theorem 2.10, p. 171"]
theorem continuousOn_csc : ContinuousOn csc {x | Real.sin x ≠ 0} := by
  unfold csc
  exact continuousOn_const.div Real.continuous_sin.continuousOn (fun x hx => hx)

end UndergradKB.Calculus
