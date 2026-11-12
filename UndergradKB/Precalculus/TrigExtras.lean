import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import UndergradKB.Common.Attr

/-!
# Trigonometry extras (Stitz–Zeager, Precalculus, Chapters 10 and 11)

Frequency and circular motion, the geometric meaning of tangent and secant, Pythagorean
conjugates, two worked identities, the calculus-friendly arcsecant and arccosecant, inverse
trigonometric composites, arccotangent, and the undamped spring-mass model.
-/

namespace UndergradKB.Precalculus

open UndergradKB Real

/-! ### Frequency (PC-197) -/

/-- Angular frequency `ω = 2π f` of a motion with ordinary frequency `f`. -/
noncomputable def angularFrequency (f : ℝ) : ℝ := 2 * π * f

/-- Period `T = 1/f` of a motion with ordinary frequency `f`. -/
noncomputable def periodOfFrequency (f : ℝ) : ℝ := 1 / f

/-- For positive frequency `f`, `t ↦ sin (ω t)` and `t ↦ cos (ω t)` repeat every `T = 1/f`
(PC-197). -/
@[kb "stitzzeager2013" "§10.1, p. 720"]
theorem frequency_period_periodic {f : ℝ} (hf : 0 < f) :
    Function.Periodic (fun t => Real.sin (angularFrequency f * t)) (periodOfFrequency f) ∧
    Function.Periodic (fun t => Real.cos (angularFrequency f * t)) (periodOfFrequency f) := by
  have key : angularFrequency f * periodOfFrequency f = 2 * π := by
    unfold angularFrequency periodOfFrequency
    field_simp
  constructor
  · intro t
    simp only [mul_add, key]
    exact Real.sin_add_two_pi _
  · intro t
    simp only [mul_add, key]
    exact Real.cos_add_two_pi _

/-! ### Circular motion (PC-203) -/

/-- Position at time `t` of an object on a circle of radius `r` with angular velocity `ω`,
starting at `(r, 0)`. -/
noncomputable def circularMotion (r ω t : ℝ) : ℝ × ℝ := (r * Real.cos (ω * t), r * Real.sin (ω * t))

/-- The object starts at `(r,0)`, stays at distance `r` from the origin, and for `r > 0`
its polar angle is `ω t` (as an angle, i.e. modulo `2π`) (PC-203). -/
@[kb "stitzzeager2013" "Equation 10.3, p. 744"]
theorem circular_motion_on_circle (r ω t : ℝ) :
    circularMotion r ω 0 = (r, 0) ∧
    (circularMotion r ω t).1 ^ 2 + (circularMotion r ω t).2 ^ 2 = r ^ 2 ∧
    (0 < r → ((Complex.arg ⟨(circularMotion r ω t).1, (circularMotion r ω t).2⟩ : ℝ) :
        Real.Angle) = ((ω * t : ℝ) : Real.Angle)) := by
  refine ⟨by simp [circularMotion], ?_, ?_⟩
  · simp only [circularMotion]
    nlinarith [Real.sin_sq_add_cos_sq (ω * t)]
  · intro hr
    have h : (⟨r * Real.cos (ω * t), r * Real.sin (ω * t)⟩ : ℂ) =
        (r : ℂ) * (Real.cos (ω * t) + Real.sin (ω * t) * Complex.I) := by
      apply Complex.ext <;> simp [-Complex.ofReal_cos, -Complex.ofReal_sin]
    simp only [circularMotion]
    rw [h, Complex.arg_real_mul _ hr]
    have := Complex.arg_cos_add_sin_mul_I_coe_angle ((ω * t : ℝ) : Real.Angle)
    simpa [Real.Angle.cos_coe, Real.Angle.sin_coe] using this

/-! ### Geometric meaning of tangent and secant (PC-207) -/

/-- The secant of a real angle (reciprocal of cosine). -/
noncomputable def secant (θ : ℝ) : ℝ := (Real.cos θ)⁻¹

/-- The cosecant of a real angle (reciprocal of sine). -/
noncomputable def cosecant (θ : ℝ) : ℝ := (Real.sin θ)⁻¹

/-- If `cos θ ≠ 0`, the line through the origin at angle `θ` meets the line `x = 1` at exactly
one point, namely `(1, tan θ)`, and the origin is at distance `|sec θ|` from it (PC-207). -/
@[kb "stitzzeager2013" "§10.3, p. 757"]
theorem tan_sec_on_line_x_eq_one {θ : ℝ} (h : Real.cos θ ≠ 0) :
    (∃! t : ℝ, t * Real.cos θ = 1) ∧
    (∀ t : ℝ, t * Real.cos θ = 1 → (t * Real.cos θ, t * Real.sin θ) = (1, Real.tan θ)) ∧
    Real.sqrt (1 ^ 2 + Real.tan θ ^ 2) = |secant θ| := by
  refine ⟨⟨(Real.cos θ)⁻¹, by field_simp, fun t ht => ?_⟩, ?_, ?_⟩
  · field_simp; linarith
  · intro t ht
    refine Prod.ext ht ?_
    simp only
    rw [Real.tan_eq_sin_div_cos]
    field_simp
    have : t = (Real.cos θ)⁻¹ := by field_simp; linarith
    rw [this]; field_simp
  · have h1 : 1 ^ 2 + Real.tan θ ^ 2 = (secant θ) ^ 2 := by
      unfold secant
      rw [Real.tan_eq_sin_div_cos]
      field_simp
      nlinarith [Real.sin_sq_add_cos_sq θ]
    rw [h1, Real.sqrt_sq_eq_abs]

/-! ### Pythagorean conjugates (PC-212) -/

/-- Products of Pythagorean conjugates (PC-212). -/
@[kb "stitzzeager2013" "§10.3, p. 763"]
theorem pythagorean_conjugates (θ : ℝ) :
    (1 - Real.cos θ) * (1 + Real.cos θ) = Real.sin θ ^ 2 ∧
    (1 - Real.sin θ) * (1 + Real.sin θ) = Real.cos θ ^ 2 ∧
    (Real.cos θ ≠ 0 → (secant θ - Real.tan θ) * (secant θ + Real.tan θ) = 1) ∧
    (Real.sin θ ≠ 0 →
      (cosecant θ - Real.cos θ / Real.sin θ) * (cosecant θ + Real.cos θ / Real.sin θ) = 1) := by
  refine ⟨by nlinarith [Real.sin_sq_add_cos_sq θ], by nlinarith [Real.sin_sq_add_cos_sq θ],
    fun h => ?_, fun h => ?_⟩
  · unfold secant
    rw [Real.tan_eq_sin_div_cos]
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq θ]
  · unfold cosecant
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq θ]

/-! ### Two worked identities (PC-226) -/

/-- `cos 3θ = 4cos³θ − 3cosθ` and, when `cos θ ≠ 0`, `sin 2θ = 2 tan θ / (1 + tan² θ)`
(PC-226). -/
@[kb "stitzzeager2013" "Example 10.4.3, p. 788"]
theorem cos_three_and_sin_two_tan (θ : ℝ) :
    Real.cos (3 * θ) = 4 * Real.cos θ ^ 3 - 3 * Real.cos θ ∧
    (Real.cos θ ≠ 0 → Real.sin (2 * θ) = 2 * Real.tan θ / (1 + Real.tan θ ^ 2)) := by
  refine ⟨Real.cos_three_mul θ, fun h => ?_⟩
  rw [Real.sin_two_mul, Real.tan_eq_sin_div_cos]
  have h2 : 1 + (Real.sin θ / Real.cos θ) ^ 2 = (Real.cos θ ^ 2)⁻¹ := by
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [h2]
  field_simp

/-! ### Calculus-friendly arcsecant and arccosecant (PC-237) -/

/-- Arcsecant with the ranges `[0, π/2) ∪ [π, 3π/2)` (valid for `|x| ≥ 1`). -/
noncomputable def arcsecCF (x : ℝ) : ℝ :=
  if 1 ≤ x then Real.arccos x⁻¹ else 2 * π - Real.arccos x⁻¹

/-- Arccosecant with the ranges `(0, π/2] ∪ (π, 3π/2]` (valid for `|x| ≥ 1`). -/
noncomputable def arccscCF (x : ℝ) : ℝ :=
  if 1 ≤ x then Real.arcsin x⁻¹ else π - Real.arcsin x⁻¹

private lemma abs_cases {x : ℝ} (h : 1 ≤ |x|) : 1 ≤ x ∨ x ≤ -1 := by
  rcases le_abs'.mp h with h | h
  · exact Or.inr h
  · exact Or.inl h

private lemma inv_mem {x : ℝ} (h : 1 ≤ |x|) : -1 ≤ x⁻¹ ∧ x⁻¹ ≤ 1 := by
  rcases abs_cases h with h | h
  · have : 0 < x := by linarith
    exact ⟨by linarith [inv_pos.mpr this], inv_le_one_of_one_le₀ h⟩
  · have hx : x < 0 := by linarith
    refine ⟨?_, by linarith [inv_lt_zero.mpr hx]⟩
    rw [inv_eq_one_div, le_div_iff_of_neg hx]; linarith

private lemma cos_arcsecCF {x : ℝ} (h : 1 ≤ |x|) : Real.cos (arcsecCF x) = x⁻¹ := by
  obtain ⟨h1, h2⟩ := inv_mem h
  unfold arcsecCF
  split_ifs
  · exact Real.cos_arccos h1 h2
  · rw [Real.cos_two_pi_sub]; exact Real.cos_arccos h1 h2

private lemma arcsecCF_mem {x : ℝ} (h : 1 ≤ |x|) :
    arcsecCF x ∈ Set.Ico 0 (π / 2) ∪ Set.Ico π (3 * π / 2) := by
  unfold arcsecCF
  split_ifs with hx
  · left
    refine ⟨Real.arccos_nonneg _, Real.arccos_lt_pi_div_two.mpr (inv_pos.mpr (by linarith))⟩
  · right
    have hx' : x ≤ -1 := by
      rcases abs_cases h with h | h
      · exact absurd h hx
      · exact h
    have hneg : x⁻¹ < 0 := inv_lt_zero.mpr (by linarith)
    have h1 : π / 2 < Real.arccos x⁻¹ := by
      by_contra hc
      have := Real.arccos_le_pi_div_two.mp (not_lt.mp hc)
      linarith
    have h2 := Real.arccos_le_pi x⁻¹
    constructor <;> linarith [Real.pi_pos]

private lemma arcsecCF_sec {t : ℝ} (ht : t ∈ Set.Ico 0 (π / 2) ∪ Set.Ico π (3 * π / 2)) :
    arcsecCF (secant t) = t := by
  rcases ht with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have hc : 0 < Real.cos t :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩
    have : 1 ≤ secant t := by
      unfold secant
      exact one_le_inv₀ hc |>.mpr (Real.cos_le_one t)
    unfold arcsecCF
    rw [if_pos this]
    unfold secant
    rw [inv_inv]
    exact Real.arccos_cos h0 (by linarith [Real.pi_pos])
  · have hc : Real.cos t < 0 := by
      have : 0 < Real.cos (t - π) :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
      rw [Real.cos_sub_pi] at this; linarith
    have : ¬ 1 ≤ secant t := by
      unfold secant; have := inv_lt_zero.mpr hc; linarith
    unfold arcsecCF
    rw [if_neg this]
    unfold secant
    rw [inv_inv]
    have : Real.cos t = Real.cos (2 * π - t) := (Real.cos_two_pi_sub t).symm
    rw [this, Real.arccos_cos (by linarith) (by linarith)]
    ring

private lemma abs_secant_ge {t : ℝ} (ht : t ∈ Set.Ico 0 (π / 2) ∪ Set.Ico π (3 * π / 2)) :
    1 ≤ |secant t| := by
  have hc : Real.cos t ≠ 0 := by
    rcases ht with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩).ne'
    · have : 0 < Real.cos (t - π) :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
      rw [Real.cos_sub_pi] at this; linarith
  unfold secant
  rw [abs_inv]
  exact one_le_inv₀ (abs_pos.mpr hc) |>.mpr (Real.abs_cos_le_one t)

/-- Properties of the calculus-friendly arcsecant: range, characterisation by secant, and the
inverse relations (`x < -1` in the comparison with `arccos`, since both sides agree at `-1`). -/
@[kb "stitzzeager2013" "Theorem 10.29, p. 843"]
theorem arcsecCF_properties :
    (∀ x : ℝ, 1 ≤ |x| → arcsecCF x ∈ Set.Ico 0 (π / 2) ∪ Set.Ico π (3 * π / 2)) ∧
    (∀ x t : ℝ, 1 ≤ |x| → (arcsecCF x = t ↔
      (t ∈ Set.Ico 0 (π / 2) ∪ Set.Ico π (3 * π / 2)) ∧ secant t = x)) ∧
    (∀ x : ℝ, 1 ≤ x → arcsecCF x = Real.arccos x⁻¹) ∧
    (∀ x : ℝ, x < -1 → arcsecCF x ≠ Real.arccos x⁻¹) ∧
    (∀ x : ℝ, 1 ≤ |x| → secant (arcsecCF x) = x) ∧
    (∀ t : ℝ, t ∈ Set.Ico 0 (π / 2) ∪ Set.Ico π (3 * π / 2) → arcsecCF (secant t) = t) := by
  have hsec : ∀ x : ℝ, 1 ≤ |x| → secant (arcsecCF x) = x := by
    intro x h
    unfold secant
    rw [cos_arcsecCF h, inv_inv]
  refine ⟨fun x h => arcsecCF_mem h, fun x t h => ⟨?_, ?_⟩, fun x hx => ?_, fun x hx => ?_, hsec,
    fun t ht => arcsecCF_sec ht⟩
  · rintro rfl; exact ⟨arcsecCF_mem h, hsec x h⟩
  · rintro ⟨ht, rfl⟩; exact arcsecCF_sec ht
  · unfold arcsecCF; rw [if_pos hx]
  · unfold arcsecCF
    rw [if_neg (by linarith)]
    intro he
    have h1 : Real.arccos x⁻¹ = π := by linarith
    have h2 : x⁻¹ = -1 := by
      have := congrArg Real.cos h1
      rwa [Real.cos_arccos (inv_mem (by rw [abs_of_neg (by linarith)]; linarith)).1
        (inv_mem (by rw [abs_of_neg (by linarith)]; linarith)).2, Real.cos_pi] at this
    have : x = -1 := by
      have := congrArg (fun y => y⁻¹) h2
      simpa using this
    linarith

private lemma sin_arccscCF {x : ℝ} (h : 1 ≤ |x|) : Real.sin (arccscCF x) = x⁻¹ := by
  obtain ⟨h1, h2⟩ := inv_mem h
  unfold arccscCF
  split_ifs
  · exact Real.sin_arcsin h1 h2
  · rw [Real.sin_pi_sub]; exact Real.sin_arcsin h1 h2

private lemma arccscCF_mem {x : ℝ} (h : 1 ≤ |x|) :
    arccscCF x ∈ Set.Ioc 0 (π / 2) ∪ Set.Ioc π (3 * π / 2) := by
  unfold arccscCF
  split_ifs with hx
  · left
    exact ⟨Real.arcsin_pos.mpr (inv_pos.mpr (by linarith)), Real.arcsin_le_pi_div_two _⟩
  · right
    have hx' : x ≤ -1 := by
      rcases abs_cases h with h | h
      · exact absurd h hx
      · exact h
    have hneg : x⁻¹ < 0 := inv_lt_zero.mpr (by linarith)
    have h1 := Real.arcsin_lt_zero.mpr hneg
    have h2 := Real.neg_pi_div_two_le_arcsin x⁻¹
    constructor <;> linarith [Real.pi_pos]

private lemma sin_ne_zero_of_mem {t : ℝ} (ht : t ∈ Set.Ioc 0 (π / 2) ∪ Set.Ioc π (3 * π / 2)) :
    Real.sin t ≠ 0 := by
  rcases ht with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact (Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])).ne'
  · have : 0 < Real.sin (t - π) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    rw [Real.sin_sub_pi] at this; linarith

private lemma arccscCF_csc {t : ℝ} (ht : t ∈ Set.Ioc 0 (π / 2) ∪ Set.Ioc π (3 * π / 2)) :
    arccscCF (cosecant t) = t := by
  rcases ht with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have hc : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
    have : 1 ≤ cosecant t := by
      unfold cosecant
      exact one_le_inv₀ hc |>.mpr (Real.sin_le_one t)
    unfold arccscCF
    rw [if_pos this]
    unfold cosecant
    rw [inv_inv]
    exact Real.arcsin_sin (by linarith [Real.pi_pos]) h1
  · have hc : Real.sin t < 0 := by
      have : 0 < Real.sin (t - π) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
      rw [Real.sin_sub_pi] at this; linarith
    have : ¬ 1 ≤ cosecant t := by
      unfold cosecant; have := inv_lt_zero.mpr hc; linarith
    unfold arccscCF
    rw [if_neg this]
    unfold cosecant
    rw [inv_inv]
    have : Real.sin t = Real.sin (π - t) := (Real.sin_pi_sub t).symm
    rw [this, Real.arcsin_sin (by linarith) (by linarith [Real.pi_pos])]
    ring

/-- Properties of the calculus-friendly arccosecant: range, characterisation by cosecant,
and the inverse relations (`x < -1` in the comparison with `arcsin`, since the two sides
differ there). -/
@[kb "stitzzeager2013" "Theorem 10.29, p. 843"]
theorem arccscCF_properties :
    (∀ x : ℝ, 1 ≤ |x| → arccscCF x ∈ Set.Ioc 0 (π / 2) ∪ Set.Ioc π (3 * π / 2)) ∧
    (∀ x t : ℝ, 1 ≤ |x| → (arccscCF x = t ↔
      (t ∈ Set.Ioc 0 (π / 2) ∪ Set.Ioc π (3 * π / 2)) ∧ cosecant t = x)) ∧
    (∀ x : ℝ, 1 ≤ x → arccscCF x = Real.arcsin x⁻¹) ∧
    (∀ x : ℝ, x ≤ -1 → arccscCF x ≠ Real.arcsin x⁻¹) ∧
    (∀ x : ℝ, 1 ≤ |x| → cosecant (arccscCF x) = x) ∧
    (∀ t : ℝ, t ∈ Set.Ioc 0 (π / 2) ∪ Set.Ioc π (3 * π / 2) → arccscCF (cosecant t) = t) := by
  have hcsc : ∀ x : ℝ, 1 ≤ |x| → cosecant (arccscCF x) = x := by
    intro x h
    unfold cosecant
    rw [sin_arccscCF h, inv_inv]
  refine ⟨fun x h => arccscCF_mem h, fun x t h => ⟨?_, ?_⟩, fun x hx => ?_, fun x hx => ?_, hcsc,
    fun t ht => arccscCF_csc ht⟩
  · rintro rfl; exact ⟨arccscCF_mem h, hcsc x h⟩
  · rintro ⟨ht, rfl⟩; exact arccscCF_csc ht
  · unfold arccscCF; rw [if_pos hx]
  · unfold arccscCF
    rw [if_neg (by linarith)]
    intro he
    have h1 : Real.arcsin x⁻¹ = π / 2 := by linarith
    have h2 := Real.arcsin_eq_pi_div_two.mp h1
    have : x⁻¹ < 0 := inv_lt_zero.mpr (by linarith)
    linarith

/-! ### Composites of inverse trigonometric functions (PC-238) -/

private lemma sin_arcsecCF_mul_nonneg {x : ℝ} (h : 1 ≤ |x|) : 0 ≤ Real.sin (arcsecCF x) * x := by
  rcases abs_cases h with hx | hx
  · unfold arcsecCF
    rw [if_pos hx, Real.sin_arccos]
    exact mul_nonneg (Real.sqrt_nonneg _) (by linarith)
  · unfold arcsecCF
    rw [if_neg (by linarith), Real.sin_two_pi_sub, Real.sin_arccos]
    have : -Real.sqrt (1 - x⁻¹ ^ 2) ≤ 0 := neg_nonpos.mpr (Real.sqrt_nonneg _)
    nlinarith

/-- `tan (arcsec x) = √(x² − 1)` for `|x| ≥ 1`, with the calculus-friendly arcsecant (PC-238). -/
@[kb "stitzzeager2013" "Example 10.6.4, p. 843"]
theorem tan_arcsecCF (x : ℝ) (h : 1 ≤ |x|) : Real.tan (arcsecCF x) = Real.sqrt (x ^ 2 - 1) := by
  have hx0 : x ≠ 0 := by
    rintro rfl; simp at h; linarith
  have hc := cos_arcsecCF h
  have hnn := sin_arcsecCF_mul_nonneg h
  have hsq : (Real.sin (arcsecCF x) * x) ^ 2 = x ^ 2 - 1 := by
    have := Real.sin_sq_add_cos_sq (arcsecCF x)
    rw [hc] at this
    have h2 : Real.sin (arcsecCF x) ^ 2 = 1 - x⁻¹ ^ 2 := by linarith
    rw [mul_pow, h2]; field_simp
  have : Real.tan (arcsecCF x) = Real.sin (arcsecCF x) * x := by
    rw [Real.tan_eq_sin_div_cos, hc, div_inv_eq_mul]
  rw [this, ← hsq, Real.sqrt_sq hnn]

private lemma cos_arccscCF_mul_nonneg {x : ℝ} (h : 1 ≤ |x|) : 0 ≤ Real.cos (arccscCF x) * x := by
  rcases abs_cases h with hx | hx
  · unfold arccscCF
    rw [if_pos hx, Real.cos_arcsin]
    exact mul_nonneg (Real.sqrt_nonneg _) (by linarith)
  · unfold arccscCF
    rw [if_neg (by linarith), Real.cos_pi_sub, Real.cos_arcsin]
    have : -Real.sqrt (1 - x⁻¹ ^ 2) ≤ 0 := neg_nonpos.mpr (Real.sqrt_nonneg _)
    nlinarith

/-- `cos (arccsc y) = √(y² − 1) / y` for `|y| ≥ 1`, with the calculus-friendly arccosecant
(PC-238). -/
@[kb "stitzzeager2013" "Example 10.6.4, p. 843"]
theorem cos_arccscCF (y : ℝ) (h : 1 ≤ |y|) :
    Real.cos (arccscCF y) = Real.sqrt (y ^ 2 - 1) / y := by
  have hy0 : y ≠ 0 := by
    rintro rfl; simp at h; linarith
  have hs := sin_arccscCF h
  have hnn := cos_arccscCF_mul_nonneg h
  have hsq : (Real.cos (arccscCF y) * y) ^ 2 = y ^ 2 - 1 := by
    have := Real.sin_sq_add_cos_sq (arccscCF y)
    rw [hs] at this
    have h2 : Real.cos (arccscCF y) ^ 2 = 1 - y⁻¹ ^ 2 := by linarith
    rw [mul_pow, h2]; field_simp
  rw [eq_div_iff hy0, ← hsq, Real.sqrt_sq hnn]

/-- The same for `cos (arccsc (4x))` with `|4x| ≥ 1` (PC-238). -/
@[kb "stitzzeager2013" "Example 10.6.4, p. 843"]
theorem cos_arccscCF_four_mul (x : ℝ) (h : 1 ≤ |4 * x|) :
    Real.cos (arccscCF (4 * x)) = Real.sqrt (16 * x ^ 2 - 1) / (4 * x) := by
  rw [cos_arccscCF _ h]
  congr 2
  ring

/-- `tan (arccos x) = √(1 − x²)/x` for `x ∈ [-1,1]`, `x ≠ 0`; `cos (2 arcsin x) = 1 − 2x²`
for `x ∈ [-1,1]`; `tan (2 arctan x) = 2x/(1 − x²)` for `x² ≠ 1` (PC-238). -/
@[kb "stitzzeager2013" "Example 10.6.2, p. 837"]
theorem inverse_trig_composites :
    (∀ x : ℝ, -1 ≤ x → x ≤ 1 → x ≠ 0 → Real.tan (Real.arccos x) = Real.sqrt (1 - x ^ 2) / x) ∧
    (∀ x : ℝ, -1 ≤ x → x ≤ 1 → Real.cos (2 * Real.arcsin x) = 1 - 2 * x ^ 2) ∧
    (∀ x : ℝ, x ^ 2 ≠ 1 → Real.tan (2 * Real.arctan x) = 2 * x / (1 - x ^ 2)) := by
  refine ⟨fun x _ _ _ => Real.tan_arccos x, fun x h1 h2 => ?_, fun x hx => ?_⟩
  · rw [Real.cos_two_mul, Real.cos_sq', Real.sin_arcsin h1 h2]; ring
  · have hpos : 0 < 1 + x ^ 2 := by positivity
    have hs : Real.sqrt (1 + x ^ 2) ^ 2 = 1 + x ^ 2 := Real.sq_sqrt hpos.le
    have hs0 : Real.sqrt (1 + x ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
    have hx' : 1 - x ^ 2 ≠ 0 := fun h => hx (by linarith)
    rw [Real.tan_eq_sin_div_cos, Real.sin_two_mul, Real.cos_two_mul, Real.sin_arctan,
      Real.cos_arctan]
    have h3 : 2 * (1 / Real.sqrt (1 + x ^ 2)) ^ 2 - 1 = (1 - x ^ 2) / (1 + x ^ 2) := by
      rw [div_pow, hs]; field_simp; ring
    rw [h3]
    field_simp
    rw [hs]

/-! ### Arccotangent (PC-239) -/

/-- Arccotangent with range `(0, π)`: `arccot x = π/2 − arctan x`. -/
noncomputable def arccotR (x : ℝ) : ℝ := π / 2 - Real.arctan x

/-- `arccot x` lies in `(0, π)`, `cot (arccot x) = x`, and `arccot x` equals `arctan (1/x)`
for `x > 0`, `π + arctan (1/x)` for `x < 0`, and `π/2` at `0` (PC-239). -/
@[kb "stitzzeager2013" "Example 10.6.5, p. 845"]
theorem arccotR_properties :
    (∀ x : ℝ, arccotR x ∈ Set.Ioo 0 π) ∧
    (∀ x : ℝ, Real.cot (arccotR x) = x) ∧
    (∀ x : ℝ, 0 < x → arccotR x = Real.arctan x⁻¹) ∧
    (∀ x : ℝ, x < 0 → arccotR x = π + Real.arctan x⁻¹) ∧
    arccotR 0 = π / 2 := by
  refine ⟨fun x => ?_, fun x => ?_, fun x hx => ?_, fun x hx => ?_, by simp [arccotR]⟩
  · have h1 := Real.arctan_lt_pi_div_two x
    have h2 := Real.neg_pi_div_two_lt_arctan x
    unfold arccotR
    constructor <;> linarith
  · unfold arccotR
    rw [Real.cot_eq_cos_div_sin, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub,
      ← Real.tan_eq_sin_div_cos, Real.tan_arctan]
  · unfold arccotR
    rw [Real.arctan_inv_of_pos hx]
  · unfold arccotR
    rw [Real.arctan_inv_of_neg hx]; ring

/-! ### The undamped spring-mass system (PC-242) -/

/-- Position `A sin (ω t + φ)` of an undamped spring-mass system. -/
noncomputable def springMotion (A ω φ t : ℝ) : ℝ := A * Real.sin (ω * t + φ)

/-- With `ω = √(k/m)`, `A = √(x₀² + (v₀/ω)²)` and a phase `φ` with `A sin φ = x₀`,
`A ω cos φ = v₀`, the function `x(t) = A sin (ω t + φ)` solves `m x'' + k x = 0` with
`x(0) = x₀` and `x'(0) = v₀`; such a phase `φ` always exists (PC-242). -/
@[kb "stitzzeager2013" "Theorem 11.1, p. 899"]
theorem spring_mass_solution {m k x₀ v₀ : ℝ} (hm : 0 < m) (hk : 0 < k) :
    let ω := Real.sqrt (k / m)
    let A := Real.sqrt (x₀ ^ 2 + (v₀ / ω) ^ 2)
    (∃ φ : ℝ, A * Real.sin φ = x₀ ∧ A * ω * Real.cos φ = v₀) ∧
    ∀ φ : ℝ, A * Real.sin φ = x₀ → A * ω * Real.cos φ = v₀ →
      (∀ t, m * deriv (deriv (springMotion A ω φ)) t + k * springMotion A ω φ t = 0) ∧
      springMotion A ω φ 0 = x₀ ∧ deriv (springMotion A ω φ) 0 = v₀ := by
  intro ω A
  have hω : 0 < ω := Real.sqrt_pos.mpr (div_pos hk hm)
  have hω2 : ω ^ 2 = k / m := Real.sq_sqrt (div_pos hk hm).le
  refine ⟨?_, fun φ h1 h2 => ?_⟩
  · set z : ℂ := ⟨v₀ / ω, x₀⟩ with hz
    have hn : ‖z‖ = A := by
      rw [Complex.norm_def, Complex.normSq_apply]
      simp only [hz, A]
      congr 1
      ring
    refine ⟨Complex.arg z, ?_, ?_⟩
    · have := Complex.norm_mul_sin_arg z
      rw [hn] at this; simpa [hz] using this
    · have := Complex.norm_mul_cos_arg z
      rw [hn] at this
      have h' : A * Real.cos (Complex.arg z) = v₀ / ω := by simpa [hz] using this
      calc A * ω * Real.cos (Complex.arg z) = ω * (A * Real.cos (Complex.arg z)) := by ring
        _ = v₀ := by rw [h']; field_simp
  · have hd1 : ∀ t, HasDerivAt (springMotion A ω φ) (A * ω * Real.cos (ω * t + φ)) t := by
      intro t
      have h := ((((hasDerivAt_id t).const_mul ω).add_const φ).sin).const_mul A
      simp only [id, mul_one] at h
      exact h.congr_deriv (by ring)
    have hd1' : deriv (springMotion A ω φ) = fun t => A * ω * Real.cos (ω * t + φ) :=
      funext fun t => (hd1 t).deriv
    have hd2 : ∀ t, HasDerivAt (fun t => A * ω * Real.cos (ω * t + φ))
        (-(A * ω ^ 2 * Real.sin (ω * t + φ))) t := by
      intro t
      have h := ((((hasDerivAt_id t).const_mul ω).add_const φ).cos).const_mul (A * ω)
      simp only [id, mul_one] at h
      exact h.congr_deriv (by ring)
    refine ⟨fun t => ?_, by simp [springMotion, h1], ?_⟩
    · rw [hd1', (hd2 t).deriv, hω2]
      unfold springMotion
      field_simp
      ring
    · rw [hd1']; simp [h2]

end UndergradKB.Precalculus
