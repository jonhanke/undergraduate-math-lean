import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 10 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 10.3
(right triangles and identities)

Reciprocal functions are written `(cos θ)⁻¹`, `(sin θ)⁻¹`, `cos θ / sin θ`; identities are stated under
the hypotheses that all quantities are defined. -/

namespace UndergradKB.Precalculus.Course

open Real

set_option hygiene false in
/-- Closes an identity between trigonometric expressions after clearing denominators. -/
local macro "idt" : tactic =>
  `(tactic| first
    | ((try simp only [tan_eq_sin_div_cos]); field_simp; done)
    | ((try simp only [tan_eq_sin_div_cos]); field_simp; ring_nf; done)
    | ((try simp only [tan_eq_sin_div_cos]); field_simp; nlinarith [sin_sq_add_cos_sq θ]))

/-! ## Right triangles -/

/-- Stitz-Zeager Exercise 10.3.66: a right triangle with a `60°` angle, hypotenuse `c`, opposite leg `9` and
adjacent leg `a` has `c = 6√3` and `a = 3√3` (so the third angle is `30°`). -/
@[kb "stitzzeager2013" "Exercise 10.3.66, p. 772"]
theorem exer_10_3_66 : ∀ a c : ℝ, (sin (π / 3) * c = 9 ∧ cos (π / 3) * c = a) ↔
    (c = 6 * √3 ∧ a = 3 * √3) := by
  intro a c
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hp : 0 < √3 := by positivity
  rw [sin_pi_div_three, cos_pi_div_three]
  constructor
  · rintro ⟨h1, h2⟩
    have hc : c = 6 * √3 := by
      have : (c - 6 * √3) * √3 = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact absurd h hp.ne'
    exact ⟨hc, by rw [← h2, hc]; ring⟩
  · rintro ⟨rfl, rfl⟩
    constructor <;> nlinarith

/-- Stitz-Zeager Exercise 10.3.70: with `θ = 30°` and opposite side `4`, the adjacent side is `4√3 ≈ 6.928`. -/
@[kb "stitzzeager2013" "Exercise 10.3.70, p. 773"]
theorem exer_10_3_70 : (∀ x : ℝ, x ≠ 0 → (tan (π / 6) = 4 / x ↔ x = 4 * √3)) ∧
    |4 * √3 - 6.928| ≤ 0.001 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hp : 0 < √3 := by positivity
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [tan_pi_div_six, div_eq_div_iff hp.ne' hx]
    constructor <;> intro h <;> nlinarith
  · have h1 : (1.7320 : ℝ) < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
    have h2 : √3 < (1.7321 : ℝ) := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    rw [abs_le]; constructor <;> linarith

/-- Stitz-Zeager Exercise 10.3.71: `10 sin 15° = 5(√6 - √2)/2 ≈ 2.588`. -/
@[kb "stitzzeager2013" "Exercise 10.3.71, p. 773"]
theorem exer_10_3_71 : 10 * sin (π / 12) = 5 * (√6 - √2) / 2 ∧
    |10 * sin (π / 12) - 2.588| ≤ 0.001 := by
  have h : 10 * sin (π / 12) = 5 * (√6 - √2) / 2 := by
    have e : π / 12 = π / 3 - π / 4 := by ring
    have h6 : √6 = √3 * √2 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
    rw [e, sin_sub, sin_pi_div_three, cos_pi_div_four, cos_pi_div_three, sin_pi_div_four, h6]
    ring
  refine ⟨h, ?_⟩
  rw [h]
  have a1 : (2.4494 : ℝ) < √6 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have a2 : √6 < (2.4495 : ℝ) := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have b1 : (1.41421 : ℝ) < √2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have b2 : √2 < (1.41422 : ℝ) := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  rw [abs_le]; constructor <;> linarith

/-! ## Identities (Exercises 82 - 132) -/

/-- Stitz-Zeager Exercise 10.3.82: `cos θ sec θ = 1`. -/
@[kb "stitzzeager2013" "Exercise 10.3.82, p. 774"]
theorem exer_10_3_82 (θ : ℝ) (hc : cos θ ≠ 0) : cos θ * (cos θ)⁻¹ = 1 := by idt

/-- Stitz-Zeager Exercise 10.3.83: `tan θ cos θ = sin θ`. -/
@[kb "stitzzeager2013" "Exercise 10.3.83, p. 774"]
theorem exer_10_3_83 (θ : ℝ) (hc : cos θ ≠ 0) : tan θ * cos θ = sin θ := by idt

/-- Stitz-Zeager Exercise 10.3.84: `sin θ csc θ = 1`. -/
@[kb "stitzzeager2013" "Exercise 10.3.84, p. 774"]
theorem exer_10_3_84 (θ : ℝ) (hs : sin θ ≠ 0) : sin θ * (sin θ)⁻¹ = 1 := by idt

/-- Stitz-Zeager Exercise 10.3.85: `tan θ cot θ = 1`. -/
@[kb "stitzzeager2013" "Exercise 10.3.85, p. 774"]
theorem exer_10_3_85 (θ : ℝ) (hc : cos θ ≠ 0) (hs : sin θ ≠ 0) : tan θ * (cos θ / sin θ) = 1 := by idt

/-- Stitz-Zeager Exercise 10.3.86: `csc θ cos θ = cot θ`. -/
@[kb "stitzzeager2013" "Exercise 10.3.86, p. 774"]
theorem exer_10_3_86 (θ : ℝ) : (sin θ)⁻¹ * cos θ = cos θ / sin θ := by idt

/-- Stitz-Zeager Exercise 10.3.87: `sin θ / cos² θ = sec θ tan θ`. -/
@[kb "stitzzeager2013" "Exercise 10.3.87, p. 774"]
theorem exer_10_3_87 (θ : ℝ) (hc : cos θ ≠ 0) : sin θ / cos θ ^ 2 = (cos θ)⁻¹ * tan θ := by idt

/-- Stitz-Zeager Exercise 10.3.88: `cos θ / sin² θ = csc θ cot θ`. -/
@[kb "stitzzeager2013" "Exercise 10.3.88, p. 774"]
theorem exer_10_3_88 (θ : ℝ) (hs : sin θ ≠ 0) : cos θ / sin θ ^ 2 = (sin θ)⁻¹ * (cos θ / sin θ) := by idt

/-- Stitz-Zeager Exercise 10.3.89: `(1 + sin θ)/cos θ = sec θ + tan θ`. -/
@[kb "stitzzeager2013" "Exercise 10.3.89, p. 774"]
theorem exer_10_3_89 (θ : ℝ) (hc : cos θ ≠ 0) : (1 + sin θ) / cos θ = (cos θ)⁻¹ + tan θ := by idt

/-- Stitz-Zeager Exercise 10.3.90: `(1 - cos θ)/sin θ = csc θ - cot θ`. -/
@[kb "stitzzeager2013" "Exercise 10.3.90, p. 774"]
theorem exer_10_3_90 (θ : ℝ) (hs : sin θ ≠ 0) : (1 - cos θ) / sin θ = (sin θ)⁻¹ - cos θ / sin θ := by idt

/-- Stitz-Zeager Exercise 10.3.91: `cos θ / (1 - sin² θ) = sec θ`. -/
@[kb "stitzzeager2013" "Exercise 10.3.91, p. 774"]
theorem exer_10_3_91 (θ : ℝ) (hc : cos θ ≠ 0) : cos θ / (1 - sin θ ^ 2) = (cos θ)⁻¹ := by
  have h : 1 - sin θ ^ 2 = cos θ ^ 2 := by linarith [sin_sq_add_cos_sq θ]
  rw [h]; field_simp

/-- Stitz-Zeager Exercise 10.3.92: `sin θ / (1 - cos² θ) = csc θ`. -/
@[kb "stitzzeager2013" "Exercise 10.3.92, p. 774"]
theorem exer_10_3_92 (θ : ℝ) (hs : sin θ ≠ 0) : sin θ / (1 - cos θ ^ 2) = (sin θ)⁻¹ := by
  have h : 1 - cos θ ^ 2 = sin θ ^ 2 := by linarith [sin_sq_add_cos_sq θ]
  rw [h]; field_simp

/-- Stitz-Zeager Exercise 10.3.93: `sec θ / (1 + tan² θ) = cos θ`. -/
@[kb "stitzzeager2013" "Exercise 10.3.93, p. 774"]
theorem exer_10_3_93 (θ : ℝ) (hc : cos θ ≠ 0) : (cos θ)⁻¹ / (1 + tan θ ^ 2) = cos θ := by
  have h : 1 + tan θ ^ 2 = (cos θ ^ 2)⁻¹ := by
    rw [tan_eq_sin_div_cos]; field_simp; linarith [sin_sq_add_cos_sq θ]
  rw [h]; field_simp

/-- Stitz-Zeager Exercise 10.3.94: `csc θ / (1 + cot² θ) = sin θ`. -/
@[kb "stitzzeager2013" "Exercise 10.3.94, p. 775"]
theorem exer_10_3_94 (θ : ℝ) (hs : sin θ ≠ 0) : (sin θ)⁻¹ / (1 + (cos θ / sin θ) ^ 2) = sin θ := by
  have h : 1 + (cos θ / sin θ) ^ 2 = (sin θ ^ 2)⁻¹ := by
    field_simp; linarith [sin_sq_add_cos_sq θ]
  rw [h]; field_simp

/-- Stitz-Zeager Exercise 10.3.95: `tan θ / (sec² θ - 1) = cot θ`. -/
@[kb "stitzzeager2013" "Exercise 10.3.95, p. 775"]
theorem exer_10_3_95 (θ : ℝ) (hc : cos θ ≠ 0) (hs : sin θ ≠ 0) :
    tan θ / (((cos θ)⁻¹) ^ 2 - 1) = cos θ / sin θ := by
  have h : ((cos θ)⁻¹) ^ 2 - 1 = sin θ ^ 2 / cos θ ^ 2 := by
    field_simp; linarith [sin_sq_add_cos_sq θ]
  rw [h, tan_eq_sin_div_cos]; field_simp

/-- Stitz-Zeager Exercise 10.3.96: `cot θ / (csc² θ - 1) = tan θ`. -/
@[kb "stitzzeager2013" "Exercise 10.3.96, p. 775"]
theorem exer_10_3_96 (θ : ℝ) (hc : cos θ ≠ 0) (hs : sin θ ≠ 0) :
    (cos θ / sin θ) / (((sin θ)⁻¹) ^ 2 - 1) = tan θ := by
  have h : ((sin θ)⁻¹) ^ 2 - 1 = cos θ ^ 2 / sin θ ^ 2 := by
    field_simp; linarith [sin_sq_add_cos_sq θ]
  rw [h, tan_eq_sin_div_cos]; field_simp

/-- Stitz-Zeager Exercise 10.3.97: `4 cos² θ + 4 sin² θ = 4`. -/
@[kb "stitzzeager2013" "Exercise 10.3.97, p. 775"]
theorem exer_10_3_97 (θ : ℝ) : 4 * cos θ ^ 2 + 4 * sin θ ^ 2 = 4 := by
  linarith [sin_sq_add_cos_sq θ]

/-- Stitz-Zeager Exercise 10.3.98: `9 - cos² θ - sin² θ = 8`. -/
@[kb "stitzzeager2013" "Exercise 10.3.98, p. 775"]
theorem exer_10_3_98 (θ : ℝ) : 9 - cos θ ^ 2 - sin θ ^ 2 = 8 := by
  linarith [sin_sq_add_cos_sq θ]

/-- Stitz-Zeager Exercise 10.3.99: `tan³ θ = tan θ sec² θ - tan θ`. -/
@[kb "stitzzeager2013" "Exercise 10.3.99, p. 775"]
theorem exer_10_3_99 (θ : ℝ) (hc : cos θ ≠ 0) : tan θ ^ 3 = tan θ * ((cos θ)⁻¹) ^ 2 - tan θ := by
  have h : ((cos θ)⁻¹) ^ 2 = 1 + tan θ ^ 2 := by
    rw [tan_eq_sin_div_cos]; field_simp; linarith [sin_sq_add_cos_sq θ]
  rw [h]; ring

/-- Stitz-Zeager Exercise 10.3.100: `sin⁵ θ = (1 - cos² θ)² sin θ`. -/
@[kb "stitzzeager2013" "Exercise 10.3.100, p. 775"]
theorem exer_10_3_100 (θ : ℝ) : sin θ ^ 5 = (1 - cos θ ^ 2) ^ 2 * sin θ := by
  have h : 1 - cos θ ^ 2 = sin θ ^ 2 := by linarith [sin_sq_add_cos_sq θ]
  rw [h]; ring

/-- Stitz-Zeager Exercise 10.3.101: `sec¹⁰ θ = (1 + tan² θ)⁴ sec² θ`. -/
@[kb "stitzzeager2013" "Exercise 10.3.101, p. 775"]
theorem exer_10_3_101 (θ : ℝ) (hc : cos θ ≠ 0) :
    ((cos θ)⁻¹) ^ 10 = (1 + tan θ ^ 2) ^ 4 * ((cos θ)⁻¹) ^ 2 := by
  have h : ((cos θ)⁻¹) ^ 2 = 1 + tan θ ^ 2 := by
    rw [tan_eq_sin_div_cos]; field_simp; linarith [sin_sq_add_cos_sq θ]
  rw [← h]; ring

/-- Stitz-Zeager Exercise 10.3.102: `cos² θ tan³ θ = tan θ - sin θ cos θ`. -/
@[kb "stitzzeager2013" "Exercise 10.3.102, p. 775"]
theorem exer_10_3_102 (θ : ℝ) (hc : cos θ ≠ 0) :
    cos θ ^ 2 * tan θ ^ 3 = tan θ - sin θ * cos θ := by
  rw [tan_eq_sin_div_cos]
  field_simp
  have := sin_sq_add_cos_sq θ
  have h : cos θ ^ 2 = 1 - sin θ ^ 2 := by linarith
  rw [h]; ring

/-- Stitz-Zeager Exercise 10.3.103: `sec⁴ θ - sec² θ = tan² θ + tan⁴ θ`. -/
@[kb "stitzzeager2013" "Exercise 10.3.103, p. 775"]
theorem exer_10_3_103 (θ : ℝ) (hc : cos θ ≠ 0) :
    ((cos θ)⁻¹) ^ 4 - ((cos θ)⁻¹) ^ 2 = tan θ ^ 2 + tan θ ^ 4 := by
  have h : ((cos θ)⁻¹) ^ 2 = 1 + tan θ ^ 2 := by
    rw [tan_eq_sin_div_cos]; field_simp; linarith [sin_sq_add_cos_sq θ]
  have h4 : ((cos θ)⁻¹) ^ 4 = (((cos θ)⁻¹) ^ 2) ^ 2 := by ring
  rw [h4, h]; ring

/-- Stitz-Zeager Exercise 10.3.108: `tan θ + cot θ = sec θ csc θ`. -/
@[kb "stitzzeager2013" "Exercise 10.3.108, p. 775"]
theorem exer_10_3_108 (θ : ℝ) (hc : cos θ ≠ 0) (hs : sin θ ≠ 0) :
    tan θ + cos θ / sin θ = (cos θ)⁻¹ * (sin θ)⁻¹ := by
  rw [tan_eq_sin_div_cos]; field_simp; linarith [sin_sq_add_cos_sq θ]

/-- Stitz-Zeager Exercise 10.3.109: `csc θ - sin θ = cot θ cos θ`. -/
@[kb "stitzzeager2013" "Exercise 10.3.109, p. 775"]
theorem exer_10_3_109 (θ : ℝ) (hs : sin θ ≠ 0) : (sin θ)⁻¹ - sin θ = cos θ / sin θ * cos θ := by
  field_simp; linarith [sin_sq_add_cos_sq θ]

/-- Stitz-Zeager Exercise 10.3.110: `cos θ - sec θ = -tan θ sin θ`. -/
@[kb "stitzzeager2013" "Exercise 10.3.110, p. 775"]
theorem exer_10_3_110 (θ : ℝ) (hc : cos θ ≠ 0) : cos θ - (cos θ)⁻¹ = -tan θ * sin θ := by
  rw [tan_eq_sin_div_cos]; field_simp; linarith [sin_sq_add_cos_sq θ]

/-- Stitz-Zeager Exercise 10.3.111: `cos θ (tan θ + cot θ) = csc θ`. -/
@[kb "stitzzeager2013" "Exercise 10.3.111, p. 775"]
theorem exer_10_3_111 (θ : ℝ) (hc : cos θ ≠ 0) (hs : sin θ ≠ 0) :
    cos θ * (tan θ + cos θ / sin θ) = (sin θ)⁻¹ := by
  rw [tan_eq_sin_div_cos]; field_simp; linarith [sin_sq_add_cos_sq θ]

/-- Stitz-Zeager Exercise 10.3.112: `sin θ (tan θ + cot θ) = sec θ`. -/
@[kb "stitzzeager2013" "Exercise 10.3.112, p. 775"]
theorem exer_10_3_112 (θ : ℝ) (hc : cos θ ≠ 0) (hs : sin θ ≠ 0) :
    sin θ * (tan θ + cos θ / sin θ) = (cos θ)⁻¹ := by
  rw [tan_eq_sin_div_cos]; field_simp; linarith [sin_sq_add_cos_sq θ]

end UndergradKB.Precalculus.Course
