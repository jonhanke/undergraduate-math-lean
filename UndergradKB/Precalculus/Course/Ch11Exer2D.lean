import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Sqrt
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.PolarComplex

/-! # Course layer, Chapter 11 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 11.4 (equations)

The point named by `(r, θ)` is `polarPoint r θ = (r cos θ, r sin θ)`; `polarGraphRadius a` and `polarGraphAngle α`
are the polar graphs `r = a` and `θ = α`. -/

namespace UndergradKB.Precalculus.Course

open Real Set

/-! ## Helpers -/

/-- A point `(x, y)` other than the origin, written with its modulus and argument. -/
private theorem w4d_polar (x y : ℝ) (h0 : x ^ 2 + y ^ 2 ≠ 0) :
    ∃ ρ φ : ℝ, 0 < ρ ∧ x = ρ * cos φ ∧ y = ρ * sin φ := by
  set z : ℂ := ⟨x, y⟩ with hz
  have hn : 0 < ‖z‖ := by
    rw [norm_pos_iff]
    intro hz0
    apply h0
    have h1 := congrArg Complex.re hz0
    have h2 := congrArg Complex.im hz0
    simp [hz] at h1 h2
    rw [h1, h2]; ring
  exact ⟨‖z‖, Complex.arg z, hn, (Complex.norm_mul_cos_arg z).symm, (Complex.norm_mul_sin_arg z).symm⟩

/-- The polar graph `r = a cos θ + b sin θ` is the circle `x² + y² = a x + b y`. -/
private theorem w4d_circ (f : ℝ → ℝ) (a b : ℝ) (hf : ∀ θ, f θ = a * cos θ + b * sin θ) :
    {p : ℝ × ℝ | ∃ θ, p = polarPoint (f θ) θ} = {p | p.1 ^ 2 + p.2 ^ 2 = a * p.1 + b * p.2} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨θ, h⟩
    simp only [polarPoint, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [hf]
    linear_combination (a * cos θ + b * sin θ) ^ 2 * sin_sq_add_cos_sq θ
  · intro h
    by_cases h0 : x ^ 2 + y ^ 2 = 0
    · have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
      have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
      set z0 : ℂ := ⟨-b, a⟩ with hz0
      have h1 := Complex.norm_mul_cos_arg z0
      have h2 := Complex.norm_mul_sin_arg z0
      have h1' : ‖z0‖ * cos (Complex.arg z0) = -b := h1
      have h2' : ‖z0‖ * sin (Complex.arg z0) = a := h2
      have hz : ‖z0‖ * (a * cos (Complex.arg z0) + b * sin (Complex.arg z0)) = 0 := by
        linear_combination a * h1' + b * h2'
      refine ⟨Complex.arg z0, ?_⟩
      have hf0 : f (Complex.arg z0) = 0 := by
        rw [hf]
        rcases mul_eq_zero.mp hz with h3 | h3
        · have h4 : z0 = 0 := norm_eq_zero.mp h3
          have ha : a = 0 := by
            have := congrArg Complex.im h4; simpa [hz0] using this
          have hb : b = 0 := by
            have := congrArg Complex.re h4; simpa [hz0] using this
          rw [ha, hb]; ring
        · exact h3
      simp [polarPoint, hx, hy, hf0]
    · obtain ⟨ρ, φ, hρ, hx, hy⟩ := w4d_polar x y h0
      have e1 : x ^ 2 + y ^ 2 = ρ ^ 2 := by
        rw [hx, hy]; linear_combination ρ ^ 2 * sin_sq_add_cos_sq φ
      have hr : ρ = a * cos φ + b * sin φ := by
        apply mul_left_cancel₀ hρ.ne'
        rw [hx, hy] at h
        have e2 : (ρ * cos φ) ^ 2 + (ρ * sin φ) ^ 2 = ρ ^ 2 := by linear_combination ρ ^ 2 * sin_sq_add_cos_sq φ
        linear_combination h - e2
      refine ⟨φ, ?_⟩
      simp only [polarPoint, Prod.mk.injEq]
      rw [hf, ← hr]
      exact ⟨hx, hy⟩

/-- The polar graph `r = c sec θ` is the line `x = c`. -/
private theorem w4d_hline (c : ℝ) (hc : c ≠ 0) :
    {p : ℝ × ℝ | ∃ θ, cos θ ≠ 0 ∧ p = polarPoint (c / cos θ) θ} = {p | p.1 = c} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨θ, hθ, h⟩
    simp only [polarPoint, Prod.mk.injEq] at h
    rw [h.1]; field_simp
  · intro h
    subst h
    have hs : 0 < √(1 + (y / x) ^ 2) := Real.sqrt_pos.mpr (by positivity)
    refine ⟨arctan (y / x), ?_, ?_⟩
    · rw [Real.cos_arctan]; positivity
    · simp only [polarPoint, Prod.mk.injEq, Real.cos_arctan, Real.sin_arctan]
      constructor <;> field_simp

/-- The polar graph `r = c csc θ` is the line `y = c`. -/
private theorem w4d_vline (c : ℝ) (hc : c ≠ 0) :
    {p : ℝ × ℝ | ∃ θ, sin θ ≠ 0 ∧ p = polarPoint (c / sin θ) θ} = {p | p.2 = c} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨θ, hθ, h⟩
    simp only [polarPoint, Prod.mk.injEq] at h
    rw [h.2]; field_simp
  · intro h
    subst h
    have hs : 0 < √(1 + (x / y) ^ 2) := Real.sqrt_pos.mpr (by positivity)
    refine ⟨π / 2 - arctan (x / y), ?_, ?_⟩
    · rw [sin_pi_div_two_sub, Real.cos_arctan]; positivity
    · simp only [polarPoint, Prod.mk.injEq, sin_pi_div_two_sub, cos_pi_div_two_sub, Real.cos_arctan,
        Real.sin_arctan]
      constructor <;> field_simp

/-! ## Section 11.4, equations -/

/-- Stitz-Zeager Exercise 11.4.58: the point named by `(r, θ)` is on `x = -3` exactly when `r = -3 sec θ`
(where `cos θ ≠ 0`). -/
@[kb "stitzzeager2013" "Exercise 11.4.58, p. 943"]
theorem exer_11_4_58 (r θ : ℝ) (h : cos θ ≠ 0) :
    (polarPoint r θ).1 = -3 ↔ r = -3 * (cos θ)⁻¹ := by
  simp only [polarPoint]
  rw [eq_mul_inv_iff_mul_eq₀ h]

/-- Stitz-Zeager Exercise 11.4.59: the point named by `(r, θ)` is on `y = 7` exactly when `r = 7 csc θ`
(where `sin θ ≠ 0`). -/
@[kb "stitzzeager2013" "Exercise 11.4.59, p. 943"]
theorem exer_11_4_59 (r θ : ℝ) (h : sin θ ≠ 0) :
    (polarPoint r θ).2 = 7 ↔ r = 7 * (sin θ)⁻¹ := by
  simp only [polarPoint]
  rw [eq_mul_inv_iff_mul_eq₀ h]

/-- Stitz-Zeager Exercise 11.4.60: the line `y = 0` is the polar graph `θ = 0`. -/
@[kb "stitzzeager2013" "Exercise 11.4.60, p. 943"]
theorem exer_11_4_60 : {p : ℝ × ℝ | p.2 = 0} = polarGraphAngle 0 := by
  rw [polar_graph_circle_and_line.2]
  ext p
  simp only [Set.mem_ofPred_eq, sin_zero, cos_zero]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 11.4.61: the line `y = -x` is the polar graph `θ = 3π/4`. -/
@[kb "stitzzeager2013" "Exercise 11.4.61, p. 943"]
theorem exer_11_4_61 : {p : ℝ × ℝ | p.2 = -p.1} = polarGraphAngle (3 * π / 4) := by
  rw [polar_graph_circle_and_line.2]
  have e : 3 * π / 4 = π - π / 4 := by ring
  have h2 : (0 : ℝ) < √2 := by positivity
  ext p
  simp only [Set.mem_ofPred_eq, e, sin_pi_sub, cos_pi_sub, sin_pi_div_four, cos_pi_div_four]
  constructor
  · intro h; rw [h]; ring
  · intro h
    have : (√2 / 2) * (p.1 + p.2) = 0 := by linarith
    rcases mul_eq_zero.mp this with h3 | h3
    · exfalso; linarith
    · linarith

/-- Stitz-Zeager Exercise 11.4.62: the line `y = √3 x` is the polar graph `θ = π/3`. -/
@[kb "stitzzeager2013" "Exercise 11.4.62, p. 943"]
theorem exer_11_4_62 : {p : ℝ × ℝ | p.2 = √3 * p.1} = polarGraphAngle (π / 3) := by
  rw [polar_graph_circle_and_line.2]
  ext p
  simp only [Set.mem_ofPred_eq, sin_pi_div_three, cos_pi_div_three]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 11.4.63: the line `y = 2x` is the polar graph `θ = arctan 2`. -/
@[kb "stitzzeager2013" "Exercise 11.4.63, p. 943"]
theorem exer_11_4_63 : {p : ℝ × ℝ | p.2 = 2 * p.1} = polarGraphAngle (arctan 2) := by
  rw [polar_graph_circle_and_line.2]
  have hs : 0 < √(1 + (2 : ℝ) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  ext p
  simp only [Set.mem_ofPred_eq, Real.sin_arctan, Real.cos_arctan]
  constructor
  · intro h; rw [h]; field_simp
  · intro h; field_simp at h; linarith

/-- Stitz-Zeager Exercise 11.4.64: the circle `x² + y² = 25` is the polar graph `r = 5`. -/
@[kb "stitzzeager2013" "Exercise 11.4.64, p. 943"]
theorem exer_11_4_64 : {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 = 25} = polarGraphRadius 5 := by
  rw [polar_graph_circle_and_line.1 5 (by norm_num)]
  ext p
  simp only [Set.mem_ofPred_eq, sq_abs]
  norm_num

/-- Stitz-Zeager Exercise 11.4.65: the circle `x² + y² = 117` is the polar graph `r = √117`. -/
@[kb "stitzzeager2013" "Exercise 11.4.65, p. 943"]
theorem exer_11_4_65 : {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 = 117} = polarGraphRadius (√117) := by
  rw [polar_graph_circle_and_line.1 _ (by positivity)]
  ext p
  simp only [Set.mem_ofPred_eq, sq_abs]
  rw [Real.sq_sqrt (by norm_num)]

/-- Stitz-Zeager Exercise 11.4.67: the point named by `(r, θ)` is on `x = 3y + 1` exactly when
`r = 1/(cos θ - 3 sin θ)` (where `cos θ - 3 sin θ ≠ 0`). -/
@[kb "stitzzeager2013" "Exercise 11.4.67, p. 943"]
theorem exer_11_4_67 (r θ : ℝ) (h : cos θ - 3 * sin θ ≠ 0) :
    (polarPoint r θ).1 = 3 * (polarPoint r θ).2 + 1 ↔ r = 1 / (cos θ - 3 * sin θ) := by
  simp only [polarPoint]
  rw [eq_div_iff h]
  constructor <;> intro h' <;> linarith

/-- Stitz-Zeager Exercise 11.4.68: the point named by `(r, θ)` is on `y = -3x²` exactly when `r = 0` or
`r = -sec θ tan θ / 3` (where `cos θ ≠ 0`). -/
@[kb "stitzzeager2013" "Exercise 11.4.68, p. 943"]
theorem exer_11_4_68 (r θ : ℝ) (h : cos θ ≠ 0) :
    (polarPoint r θ).2 = -3 * (polarPoint r θ).1 ^ 2 ↔
      r = 0 ∨ r = -((cos θ)⁻¹ * (sin θ / cos θ)) / 3 := by
  simp only [polarPoint]
  constructor
  · intro h1
    by_cases hr : r = 0
    · exact Or.inl hr
    · right
      have h2 : sin θ = -3 * r * cos θ ^ 2 := by
        apply mul_left_cancel₀ hr
        linear_combination h1
      field_simp
      linear_combination h2
  · rintro (rfl | h1)
    · simp
    · rw [h1]
      field_simp

/-- Stitz-Zeager Exercise 11.4.69: the point named by `(r, θ)` is on `4x = y²` exactly when `r = 0` or
`r = 4 csc θ cot θ` (where `sin θ ≠ 0`). -/
@[kb "stitzzeager2013" "Exercise 11.4.69, p. 943"]
theorem exer_11_4_69 (r θ : ℝ) (h : sin θ ≠ 0) :
    4 * (polarPoint r θ).1 = (polarPoint r θ).2 ^ 2 ↔
      r = 0 ∨ r = 4 * (sin θ)⁻¹ * (cos θ / sin θ) := by
  simp only [polarPoint]
  constructor
  · intro h1
    by_cases hr : r = 0
    · exact Or.inl hr
    · right
      have h2 : 4 * cos θ = r * sin θ ^ 2 := by
        apply mul_left_cancel₀ hr
        linear_combination h1
      field_simp
      linear_combination -h2
  · rintro (rfl | h1)
    · simp
    · rw [h1]
      field_simp

/-- Stitz-Zeager Exercise 11.4.71: the point named by `(r, θ)` is on `x² - 4x + y² = 0` exactly when
`r = 0` or `r = 4 cos θ`. -/
@[kb "stitzzeager2013" "Exercise 11.4.71, p. 943"]
theorem exer_11_4_71 (r θ : ℝ) :
    (polarPoint r θ).1 ^ 2 - 4 * (polarPoint r θ).1 + (polarPoint r θ).2 ^ 2 = 0 ↔
      r = 0 ∨ r = 4 * cos θ := by
  simp only [polarPoint]
  have h : (r * cos θ) ^ 2 - 4 * (r * cos θ) + (r * sin θ) ^ 2 = r * (r - 4 * cos θ) := by
    linear_combination r ^ 2 * sin_sq_add_cos_sq θ
  rw [h, mul_eq_zero, sub_eq_zero]

/-- Stitz-Zeager Exercise 11.4.72: the point named by `(r, θ)` is on `x² + y² = x` exactly when `r = 0` or
`r = cos θ`. -/
@[kb "stitzzeager2013" "Exercise 11.4.72, p. 943"]
theorem exer_11_4_72 (r θ : ℝ) :
    (polarPoint r θ).1 ^ 2 + (polarPoint r θ).2 ^ 2 = (polarPoint r θ).1 ↔ r = 0 ∨ r = cos θ := by
  simp only [polarPoint]
  have h : (r * cos θ) ^ 2 + (r * sin θ) ^ 2 - r * cos θ = r * (r - cos θ) := by
    linear_combination r ^ 2 * sin_sq_add_cos_sq θ
  rw [← sub_eq_zero, h, mul_eq_zero, sub_eq_zero]

/-- Stitz-Zeager Exercise 11.4.73: the point named by `(r, θ)` is on `y² = 7y - x²` exactly when `r = 0` or
`r = 7 sin θ`. -/
@[kb "stitzzeager2013" "Exercise 11.4.73, p. 943"]
theorem exer_11_4_73 (r θ : ℝ) :
    (polarPoint r θ).2 ^ 2 = 7 * (polarPoint r θ).2 - (polarPoint r θ).1 ^ 2 ↔
      r = 0 ∨ r = 7 * sin θ := by
  simp only [polarPoint]
  have h : (r * sin θ) ^ 2 - (7 * (r * sin θ) - (r * cos θ) ^ 2) = r * (r - 7 * sin θ) := by
    linear_combination r ^ 2 * sin_sq_add_cos_sq θ
  rw [← sub_eq_zero, h, mul_eq_zero, sub_eq_zero]

/-- Stitz-Zeager Exercise 11.4.74: the point named by `(r, θ)` is on `(x + 2)² + y² = 4` exactly when
`r = 0` or `r = -4 cos θ`. -/
@[kb "stitzzeager2013" "Exercise 11.4.74, p. 943"]
theorem exer_11_4_74 (r θ : ℝ) :
    ((polarPoint r θ).1 + 2) ^ 2 + (polarPoint r θ).2 ^ 2 = 4 ↔ r = 0 ∨ r = -4 * cos θ := by
  simp only [polarPoint]
  have h : ((r * cos θ) + 2) ^ 2 + (r * sin θ) ^ 2 - 4 = r * (r - -4 * cos θ) := by
    linear_combination r ^ 2 * sin_sq_add_cos_sq θ
  rw [← sub_eq_zero, h, mul_eq_zero, sub_eq_zero]

/-- Stitz-Zeager Exercise 11.4.75: the point named by `(r, θ)` is on `x² + (y - 3)² = 9` exactly when
`r = 0` or `r = 6 sin θ`. -/
@[kb "stitzzeager2013" "Exercise 11.4.75, p. 943"]
theorem exer_11_4_75 (r θ : ℝ) :
    (polarPoint r θ).1 ^ 2 + ((polarPoint r θ).2 - 3) ^ 2 = 9 ↔ r = 0 ∨ r = 6 * sin θ := by
  simp only [polarPoint]
  have h : (r * cos θ) ^ 2 + (r * sin θ - 3) ^ 2 - 9 = r * (r - 6 * sin θ) := by
    linear_combination r ^ 2 * sin_sq_add_cos_sq θ
  rw [← sub_eq_zero, h, mul_eq_zero, sub_eq_zero]

/-- Stitz-Zeager Exercise 11.4.76: the point named by `(r, θ)` is on `4x² + 4(y - 1/2)² = 1` exactly when
`r = 0` or `r = sin θ`. -/
@[kb "stitzzeager2013" "Exercise 11.4.76, p. 943"]
theorem exer_11_4_76 (r θ : ℝ) :
    4 * (polarPoint r θ).1 ^ 2 + 4 * ((polarPoint r θ).2 - 1 / 2) ^ 2 = 1 ↔ r = 0 ∨ r = sin θ := by
  simp only [polarPoint]
  have h : 4 * (r * cos θ) ^ 2 + 4 * (r * sin θ - 1 / 2) ^ 2 - 1 = 4 * (r * (r - sin θ)) := by
    linear_combination 4 * r ^ 2 * sin_sq_add_cos_sq θ
  rw [← sub_eq_zero, h, mul_eq_zero, mul_eq_zero, sub_eq_zero]
  simp

/-- Stitz-Zeager Exercise 11.4.77: the polar graph `r = 7` is the circle `x² + y² = 49`. -/
@[kb "stitzzeager2013" "Exercise 11.4.77, p. 943"]
theorem exer_11_4_77 : polarGraphRadius 7 = {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 = 49} := by
  rw [polar_graph_circle_and_line.1 7 (by norm_num)]
  ext p
  simp only [Set.mem_ofPred_eq, sq_abs]
  norm_num

/-- Stitz-Zeager Exercise 11.4.78: the polar graph `r = -3` is the circle `x² + y² = 9`. -/
@[kb "stitzzeager2013" "Exercise 11.4.78, p. 943"]
theorem exer_11_4_78 : polarGraphRadius (-3) = {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 = 9} := by
  rw [polar_graph_circle_and_line.1 (-3) (by norm_num)]
  ext p
  simp only [Set.mem_ofPred_eq, sq_abs]
  norm_num

/-- Stitz-Zeager Exercise 11.4.79: the polar graph `r = √2` is the circle `x² + y² = 2`. -/
@[kb "stitzzeager2013" "Exercise 11.4.79, p. 943"]
theorem exer_11_4_79 : polarGraphRadius (√2) = {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 = 2} := by
  rw [polar_graph_circle_and_line.1 _ (by positivity)]
  ext p
  simp only [Set.mem_ofPred_eq, sq_abs]
  rw [Real.sq_sqrt (by norm_num)]

/-- Stitz-Zeager Exercise 11.4.80: the polar graph `θ = π/4` is the line `y = x`. -/
@[kb "stitzzeager2013" "Exercise 11.4.80, p. 943"]
theorem exer_11_4_80 : polarGraphAngle (π / 4) = {p : ℝ × ℝ | p.2 = p.1} := by
  rw [polar_graph_circle_and_line.2]
  have h2 : (0 : ℝ) < √2 := by positivity
  ext p
  simp only [Set.mem_ofPred_eq, sin_pi_div_four, cos_pi_div_four]
  constructor
  · intro h
    have : (√2 / 2) * (p.1 - p.2) = 0 := by linarith
    rcases mul_eq_zero.mp this with h3 | h3
    · exfalso; linarith
    · linarith
  · intro h; rw [h]

/-- Stitz-Zeager Exercise 11.4.81: the polar graph `θ = 2π/3` is the line `y = -√3 x`. -/
@[kb "stitzzeager2013" "Exercise 11.4.81, p. 943"]
theorem exer_11_4_81 : polarGraphAngle (2 * π / 3) = {p : ℝ × ℝ | p.2 = -(√3 * p.1)} := by
  rw [polar_graph_circle_and_line.2]
  have e : 2 * π / 3 = π - π / 3 := by ring
  ext p
  simp only [Set.mem_ofPred_eq, e, sin_pi_sub, cos_pi_sub, sin_pi_div_three, cos_pi_div_three]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 11.4.82: the polar graph `θ = π` is the line `y = 0`. -/
@[kb "stitzzeager2013" "Exercise 11.4.82, p. 943"]
theorem exer_11_4_82 : polarGraphAngle π = {p : ℝ × ℝ | p.2 = 0} := by
  rw [polar_graph_circle_and_line.2]
  ext p
  simp only [Set.mem_ofPred_eq, sin_pi, cos_pi]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 11.4.83: the polar graph `θ = 3π/2` is the line `x = 0`. -/
@[kb "stitzzeager2013" "Exercise 11.4.83, p. 943"]
theorem exer_11_4_83 : polarGraphAngle (3 * π / 2) = {p : ℝ × ℝ | p.1 = 0} := by
  rw [polar_graph_circle_and_line.2]
  have e : 3 * π / 2 = π / 2 + π := by ring
  ext p
  simp only [Set.mem_ofPred_eq, e, sin_add_pi, cos_add_pi, sin_pi_div_two, cos_pi_div_two]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 11.4.85: the polar graph `5r = cos θ` is the circle `5x² + 5y² = x`. -/
@[kb "stitzzeager2013" "Exercise 11.4.85, p. 943"]
theorem exer_11_4_85 :
    {p : ℝ × ℝ | ∃ θ, p = polarPoint (cos θ / 5) θ} = {p | 5 * p.1 ^ 2 + 5 * p.2 ^ 2 = p.1} := by
  refine (w4d_circ (fun θ => cos θ / 5) (1 / 5) 0 (fun θ => by ring)).trans ?_
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 11.4.86: the polar graph `r = 3 sin θ` is the circle `x² + y² = 3y`. -/
@[kb "stitzzeager2013" "Exercise 11.4.86, p. 943"]
theorem exer_11_4_86 :
    {p : ℝ × ℝ | ∃ θ, p = polarPoint (3 * sin θ) θ} = {p | p.1 ^ 2 + p.2 ^ 2 = 3 * p.2} := by
  refine (w4d_circ (fun θ => 3 * sin θ) 0 3 (fun θ => by ring)).trans ?_
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 11.4.87: the polar graph `r = -2 sin θ` is the circle `x² + y² = -2y`. -/
@[kb "stitzzeager2013" "Exercise 11.4.87, p. 943"]
theorem exer_11_4_87 :
    {p : ℝ × ℝ | ∃ θ, p = polarPoint (-2 * sin θ) θ} = {p | p.1 ^ 2 + p.2 ^ 2 = -2 * p.2} := by
  refine (w4d_circ (fun θ => -2 * sin θ) 0 (-2) (fun θ => by ring)).trans ?_
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 11.4.89: the polar graph `12 r = csc θ` is the line `y = 1/12`. -/
@[kb "stitzzeager2013" "Exercise 11.4.89, p. 943"]
theorem exer_11_4_89 :
    {p : ℝ × ℝ | ∃ θ, sin θ ≠ 0 ∧ p = polarPoint (1 / 12 / sin θ) θ} = {p | p.2 = 1 / 12} :=
  w4d_vline (1 / 12) (by norm_num)

/-- Stitz-Zeager Exercise 11.4.90: the polar graph `r = -2 sec θ` is the line `x = -2`. -/
@[kb "stitzzeager2013" "Exercise 11.4.90, p. 943"]
theorem exer_11_4_90 :
    {p : ℝ × ℝ | ∃ θ, cos θ ≠ 0 ∧ p = polarPoint (-2 / cos θ) θ} = {p | p.1 = -2} :=
  w4d_hline (-2) (by norm_num)

/-- Stitz-Zeager Exercise 11.4.91: the polar graph `r = -√5 csc θ` is the line `y = -√5`. -/
@[kb "stitzzeager2013" "Exercise 11.4.91, p. 943"]
theorem exer_11_4_91 :
    {p : ℝ × ℝ | ∃ θ, sin θ ≠ 0 ∧ p = polarPoint (-√5 / sin θ) θ} = {p | p.2 = -√5} :=
  w4d_vline (-√5) (by have : (0 : ℝ) < √5 := by positivity
                      linarith)

/-- Stitz-Zeager Exercise 11.4.92: the polar graph `r = 2 sec θ tan θ` is the parabola `x² = 2y`. -/
@[kb "stitzzeager2013" "Exercise 11.4.92, p. 943"]
theorem exer_11_4_92 :
    {p : ℝ × ℝ | ∃ θ, cos θ ≠ 0 ∧ p = polarPoint (2 * (1 / cos θ) * (sin θ / cos θ)) θ} =
      {p | p.1 ^ 2 = 2 * p.2} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨θ, hθ, h⟩
    simp only [polarPoint, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    field_simp
  · intro h
    have hs : 0 < √(1 + (x / 2) ^ 2) := Real.sqrt_pos.mpr (by positivity)
    refine ⟨arctan (x / 2), ?_, ?_⟩
    · rw [Real.cos_arctan]; positivity
    · simp only [polarPoint, Prod.mk.injEq, Real.cos_arctan, Real.sin_arctan]
      constructor
      · field_simp
      · field_simp
        nlinarith [h]

/-- Stitz-Zeager Exercise 11.4.93: the polar graph `r = -csc θ cot θ` is the parabola `y² = -x`. -/
@[kb "stitzzeager2013" "Exercise 11.4.93, p. 943"]
theorem exer_11_4_93 :
    {p : ℝ × ℝ | ∃ θ, sin θ ≠ 0 ∧ p = polarPoint (-(1 / sin θ) * (cos θ / sin θ)) θ} =
      {p | p.2 ^ 2 = -p.1} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨θ, hθ, h⟩
    simp only [polarPoint, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    field_simp
  · intro h
    have hs : 0 < √(1 + (-y) ^ 2) := Real.sqrt_pos.mpr (by positivity)
    refine ⟨π / 2 - arctan (-y), ?_, ?_⟩
    · rw [sin_pi_div_two_sub, Real.cos_arctan]; positivity
    · simp only [polarPoint, Prod.mk.injEq, sin_pi_div_two_sub, cos_pi_div_two_sub, Real.cos_arctan,
        Real.sin_arctan]
      constructor
      · field_simp
        nlinarith [h]
      · field_simp

/-- Stitz-Zeager Exercise 11.4.94: the polar graph `r² = sin 2θ` is the curve `(x² + y²)² = 2xy`. -/
@[kb "stitzzeager2013" "Exercise 11.4.94, p. 943"]
theorem exer_11_4_94 :
    {p : ℝ × ℝ | ∃ θ r : ℝ, r ^ 2 = sin (2 * θ) ∧ p = polarPoint r θ} =
      {p | (p.1 ^ 2 + p.2 ^ 2) ^ 2 = 2 * p.1 * p.2} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨θ, r, hr, h⟩
    simp only [polarPoint, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [sin_two_mul] at hr
    have e : (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 := by
      linear_combination r ^ 2 * sin_sq_add_cos_sq θ
    rw [e]
    have : 2 * (r * cos θ) * (r * sin θ) = r ^ 2 * (2 * sin θ * cos θ) := by ring
    rw [this, ← hr]; ring
  · intro h
    by_cases h0 : x ^ 2 + y ^ 2 = 0
    · have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
      have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
      exact ⟨0, 0, by simp, by simp [polarPoint, hx, hy]⟩
    · obtain ⟨ρ, φ, hρ, hx, hy⟩ := w4d_polar x y h0
      have e1 : x ^ 2 + y ^ 2 = ρ ^ 2 := by
        rw [hx, hy]; linear_combination ρ ^ 2 * sin_sq_add_cos_sq φ
      refine ⟨φ, ρ, ?_, by simp only [polarPoint, Prod.mk.injEq]; exact ⟨hx, hy⟩⟩
      rw [sin_two_mul]
      rw [e1] at h
      have h2 : ρ ^ 2 * (ρ ^ 2 - 2 * sin φ * cos φ) = 0 := by
        rw [hx, hy] at h
        linear_combination h
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exfalso; exact hρ.ne' (pow_eq_zero_iff (two_ne_zero)|>.mp h3)
      · linarith

/-- Stitz-Zeager Exercise 11.4.95: the polar graph `r = 1 - 2 cos θ` is the curve
`(x² + 2x + y²)² = x² + y²`. -/
@[kb "stitzzeager2013" "Exercise 11.4.95, p. 943"]
theorem exer_11_4_95 :
    {p : ℝ × ℝ | ∃ θ, p = polarPoint (1 - 2 * cos θ) θ} =
      {p | (p.1 ^ 2 + 2 * p.1 + p.2 ^ 2) ^ 2 = p.1 ^ 2 + p.2 ^ 2} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨θ, h⟩
    simp only [polarPoint, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have h1 : ((1 - 2 * cos θ) * cos θ) ^ 2 + 2 * ((1 - 2 * cos θ) * cos θ) +
        ((1 - 2 * cos θ) * sin θ) ^ 2 = 1 - 2 * cos θ := by
      linear_combination (1 - 2 * cos θ) ^ 2 * sin_sq_add_cos_sq θ
    rw [h1]
    linear_combination (-(1 - 2 * cos θ) ^ 2) * sin_sq_add_cos_sq θ
  · intro h
    by_cases h0 : x ^ 2 + y ^ 2 = 0
    · have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
      have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
      refine ⟨π / 3, ?_⟩
      simp [polarPoint, hx, hy, cos_pi_div_three]
    · obtain ⟨ρ, φ, hρ, hx, hy⟩ := w4d_polar x y h0
      have e1 : x ^ 2 + y ^ 2 = ρ ^ 2 := by
        rw [hx, hy]; linear_combination ρ ^ 2 * sin_sq_add_cos_sq φ
      have h2 : (ρ ^ 2 + 2 * ρ * cos φ) ^ 2 = ρ ^ 2 := by
        have : x ^ 2 + 2 * x + y ^ 2 = ρ ^ 2 + 2 * ρ * cos φ := by have e2 := e1; rw [hx, hy] at e2 ⊢; linarith
        rw [this, e1] at h
        exact h
      have h3 : (ρ + 2 * cos φ - 1) * (ρ + 2 * cos φ + 1) = 0 := by
        have : ρ ^ 2 * ((ρ + 2 * cos φ - 1) * (ρ + 2 * cos φ + 1)) = 0 := by
          linear_combination h2
        rcases mul_eq_zero.mp this with h4 | h4
        · exfalso; exact hρ.ne' (pow_eq_zero_iff (two_ne_zero) |>.mp h4)
        · exact h4
      rcases mul_eq_zero.mp h3 with h4 | h4
      · refine ⟨φ, ?_⟩
        simp only [polarPoint, Prod.mk.injEq]
        rw [show 1 - 2 * cos φ = ρ by linarith]
        exact ⟨hx, hy⟩
      · refine ⟨φ + π, ?_⟩
        have h5 := (polar_point_same_names ρ φ 0).2.1
        norm_num at h5
        rw [cos_add_pi, show 1 - 2 * -cos φ = -ρ by linarith, h5]
        exact Prod.ext hx hy

/-- Stitz-Zeager Exercise 11.4.96: the polar graph `r = 1 + sin θ` is the curve
`(x² + y² - y)² = x² + y²` (ERRATUM: the book prints `(x² + y² + y)²`; the correct sign is `-y`). -/
@[kb "stitzzeager2013" "Exercise 11.4.96, p. 943"]
theorem exer_11_4_96 :
    {p : ℝ × ℝ | ∃ θ, p = polarPoint (1 + sin θ) θ} =
      {p | (p.1 ^ 2 + p.2 ^ 2 - p.2) ^ 2 = p.1 ^ 2 + p.2 ^ 2} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨θ, h⟩
    simp only [polarPoint, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have h1 : ((1 + sin θ) * cos θ) ^ 2 + ((1 + sin θ) * sin θ) ^ 2 - (1 + sin θ) * sin θ =
        1 + sin θ := by
      linear_combination (1 + sin θ) ^ 2 * sin_sq_add_cos_sq θ
    rw [h1]
    linear_combination (-(1 + sin θ) ^ 2) * sin_sq_add_cos_sq θ
  · intro h
    by_cases h0 : x ^ 2 + y ^ 2 = 0
    · have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
      have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
      refine ⟨-(π / 2), ?_⟩
      simp [polarPoint, hx, hy]
    · obtain ⟨ρ, φ, hρ, hx, hy⟩ := w4d_polar x y h0
      have e1 : x ^ 2 + y ^ 2 = ρ ^ 2 := by
        rw [hx, hy]; linear_combination ρ ^ 2 * sin_sq_add_cos_sq φ
      have h2 : (ρ ^ 2 - ρ * sin φ) ^ 2 = ρ ^ 2 := by
        have : x ^ 2 + y ^ 2 - y = ρ ^ 2 - ρ * sin φ := by have e2 := e1; rw [hx, hy] at e2 ⊢; linarith
        rw [this, e1] at h
        exact h
      have h3 : (ρ - sin φ - 1) * (ρ - sin φ + 1) = 0 := by
        have : ρ ^ 2 * ((ρ - sin φ - 1) * (ρ - sin φ + 1)) = 0 := by
          linear_combination h2
        rcases mul_eq_zero.mp this with h4 | h4
        · exfalso; exact hρ.ne' (pow_eq_zero_iff (two_ne_zero) |>.mp h4)
        · exact h4
      rcases mul_eq_zero.mp h3 with h4 | h4
      · refine ⟨φ, ?_⟩
        simp only [polarPoint, Prod.mk.injEq]
        rw [show 1 + sin φ = ρ by linarith]
        exact ⟨hx, hy⟩
      · refine ⟨φ + π, ?_⟩
        have h5 := (polar_point_same_names ρ φ 0).2.1
        norm_num at h5
        rw [sin_add_pi, show 1 + -sin φ = -ρ by linarith, h5]
        exact Prod.ext hx hy

end UndergradKB.Precalculus.Course
