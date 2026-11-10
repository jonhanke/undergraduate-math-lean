import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.PiL2
import UndergradKB.Common.Attr

/-! # Further trigonometric identities (Corral Chapters 1, 3, 5, 6; OpenStax §9.2)

Triple-angle-sum expansions, identities for the angles of a triangle, exact values at `5π/12`,
the amplitude-phase form `a sin x + b cos x = √(a²+b²) sin (x + φ)`, and slope/angle facts for lines.
-/

namespace UndergradKB.Trigonometry

open Real

/-- `sin (A + B + C)` expanded (TR-061). -/
@[kb "corraltrig" "Ex 3.9, p. 82"]
theorem sin_add_add (A B C : ℝ) :
    sin (A + B + C) = sin A * cos B * cos C + cos A * sin B * cos C + cos A * cos B * sin C
      - sin A * sin B * sin C := by
  rw [sin_add, sin_add, cos_add]; ring

/-- `cos (A + B + C)` expanded (TR-061). -/
theorem cos_add_add (A B C : ℝ) :
    cos (A + B + C) = cos A * cos B * cos C - sin A * sin B * cos C - sin A * cos B * sin C
      - cos A * sin B * sin C := by
  rw [cos_add, sin_add, cos_add]; ring

/-- If `A + B + C = π` and the cosines are nonzero then `tan A + tan B + tan C = tan A tan B tan C`
(TR-062). -/
@[kb "corraltrig" "Ex 3.10, p. 82"]
theorem tan_add_tan_add_tan_eq (A B C : ℝ) (h : A + B + C = π) (hA : cos A ≠ 0) (hB : cos B ≠ 0)
    (hC : cos C ≠ 0) : tan A + tan B + tan C = tan A * tan B * tan C := by
  have hC' : C = π - (A + B) := by linarith
  subst hC'
  rw [cos_pi_sub, cos_add] at hC
  rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos, tan_eq_sin_div_cos, sin_pi_sub, cos_pi_sub, sin_add,
    cos_add]
  have hC2 : cos A * cos B - sin A * sin B ≠ 0 := fun h0 => hC (by rw [h0, neg_zero])
  field_simp
  ring

/-- If `A + B + C + D = π` then `sin A sin B + sin C sin D = sin (A + C) sin (B + C)` (TR-063). -/
@[kb "corraltrig" "Ex 3.11, p. 82"]
theorem sin_mul_sin_add_sin_mul_sin (A B C D : ℝ) (h : A + B + C + D = π) :
    sin A * sin B + sin C * sin D = sin (A + C) * sin (B + C) := by
  have hD : D = π - (A + B + C) := by linarith
  subst hD
  rw [sin_pi_sub]
  simp only [sin_add, cos_add]
  have := sin_sq_add_cos_sq C
  linear_combination (-(sin A * sin B)) * this

/-- Auxiliary: `cos (2x) = 1 - 2 sin² x`. -/
private theorem cos_two_mul_eq (x : ℝ) : cos (2 * x) = 1 - 2 * sin x ^ 2 := by
  rw [cos_two_mul]; linear_combination 2 * sin_sq_add_cos_sq x

/-- In a triangle `cos A + cos B + cos C = 1 + 4 sin (A/2) sin (B/2) sin (C/2)` (TR-055). -/
@[kb "corraltrig" "Ex 3.18, p. 92"]
theorem cos_add_cos_add_cos_triangle (A B C : ℝ) (h : A + B + C = π) :
    cos A + cos B + cos C = 1 + 4 * sin (A / 2) * sin (B / 2) * sin (C / 2) := by
  obtain ⟨a, rfl⟩ : ∃ a, A = 2 * a := ⟨A / 2, by ring⟩
  obtain ⟨b, rfl⟩ : ∃ b, B = 2 * b := ⟨B / 2, by ring⟩
  have hC : C = π - (2 * a + 2 * b) := by linarith
  have hC2 : C / 2 = π / 2 - (a + b) := by linarith
  rw [hC2, hC, sin_pi_div_two_sub, cos_pi_sub, cos_add, cos_add, cos_two_mul_eq,
    cos_two_mul_eq, sin_two_mul, sin_two_mul]
  rw [mul_div_cancel_left₀ a two_ne_zero, mul_div_cancel_left₀ b two_ne_zero]
  ring

/-- In a triangle `sin (A/2) sin (B/2) sin (C/2) ≤ 1/8` (TR-056). -/
@[kb "corraltrig" "Ex 3.19, p. 92"]
theorem sin_half_mul_le (A B C : ℝ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (h : A + B + C = π) :
    sin (A / 2) * sin (B / 2) * sin (C / 2) ≤ 1 / 8 := by
  have hC2 : C / 2 = π / 2 - (A / 2 + B / 2) := by linarith
  have ht : 0 < cos (A / 2 + B / 2) := by
    apply cos_pos_of_mem_Ioo; constructor <;> linarith
  have hu : cos (A / 2 - B / 2) ≤ 1 := cos_le_one _
  have hp : sin (A / 2) * sin (B / 2) = (cos (A / 2 - B / 2) - cos (A / 2 + B / 2)) / 2 := by
    rw [cos_sub, cos_add]; ring
  rw [hC2, sin_pi_div_two_sub, hp]
  nlinarith [sq_nonneg (cos (A / 2 + B / 2) - 1 / 2), mul_le_mul_of_nonneg_right hu ht.le]

/-- In a triangle `1 < cos A + cos B + cos C ≤ 3/2` (TR-057). -/
@[kb "corraltrig" "Ex 3.20, p. 92"]
theorem one_lt_cos_add_cos_add_cos_le (A B C : ℝ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (h : A + B + C = π) :
    1 < cos A + cos B + cos C ∧ cos A + cos B + cos C ≤ 3 / 2 := by
  rw [cos_add_cos_add_cos_triangle A B C h]
  have h1 := sin_half_mul_le A B C hA hB hC h
  have p1 : 0 < sin (A / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have p2 : 0 < sin (B / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have p3 : 0 < sin (C / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have := mul_pos (mul_pos p1 p2) p3
  constructor <;> nlinarith

/-- `sin (5π/12) = (√6 + √2)/4` (TR-020). -/
@[kb "corraltrig" "Ex 1.10, p. 20"]
theorem sin_five_pi_div_twelve : sin (5 * π / 12) = (√6 + √2) / 4 := by
  have e : 5 * π / 12 = π / 4 + π / 6 := by ring
  have h6 : √6 = √2 * √3 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
  rw [e, sin_add, sin_pi_div_four, cos_pi_div_four, sin_pi_div_six, cos_pi_div_six, h6]; ring

/-- `cos (5π/12) = (√6 - √2)/4` (TR-020). -/
theorem cos_five_pi_div_twelve : cos (5 * π / 12) = (√6 - √2) / 4 := by
  have e : 5 * π / 12 = π / 4 + π / 6 := by ring
  have h6 : √6 = √2 * √3 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
  rw [e, cos_add, sin_pi_div_four, cos_pi_div_four, sin_pi_div_six, cos_pi_div_six, h6]; ring

/-- `tan (5π/12) = (√6 + √2)/(√6 - √2)` (TR-020). -/
theorem tan_five_pi_div_twelve : tan (5 * π / 12) = (√6 + √2) / (√6 - √2) := by
  rw [tan_eq_sin_div_cos, sin_five_pi_div_twelve, cos_five_pi_div_twelve]
  have : (0:ℝ) < √6 - √2 := by
    have : √2 < √6 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  field_simp

/-- `cos (π/12) = (√6 + √2)/4` (TR-020, OpenStax Example 1). -/
@[kb "openstaxalgtrig2e" "§9.2, p. 824 (Ex 2)"]
theorem cos_pi_div_twelve : cos (π / 12) = (√6 + √2) / 4 := by
  have e : π / 12 = π / 4 - π / 6 := by ring
  have h6 : √6 = √2 * √3 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
  rw [e, cos_sub, sin_pi_div_four, cos_pi_div_four, sin_pi_div_six, cos_pi_div_six, h6]; ring

/-- For `(a, b) ≠ (0, 0)` there is an angle `φ` with `cos φ = a/√(a²+b²)`, `sin φ = b/√(a²+b²)`,
and then `a sin x + b cos x = √(a²+b²) sin (x + φ)` for all `x` (TR-118, TR-169). -/
@[kb "corraltrig" "Example 5.9, p. 114"]
theorem exists_amplitude_phase (a b : ℝ) (hab : a ≠ 0 ∨ b ≠ 0) :
    ∃ φ : ℝ, cos φ = a / √(a ^ 2 + b ^ 2) ∧ sin φ = b / √(a ^ 2 + b ^ 2) ∧
      ∀ x, a * sin x + b * cos x = √(a ^ 2 + b ^ 2) * sin (x + φ) := by
  have hz : (⟨a, b⟩ : ℂ) ≠ 0 := by
    intro h0
    have h1 := congrArg Complex.re h0
    have h2 := congrArg Complex.im h0
    simp at h1 h2
    tauto
  have hn : ‖(⟨a, b⟩ : ℂ)‖ = √(a ^ 2 + b ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]; congr 1; simp; ring
  have hpos : 0 < √(a ^ 2 + b ^ 2) := by
    rw [← hn]; exact norm_pos_iff.2 hz
  have hc : cos (Complex.arg ⟨a, b⟩) = a / √(a ^ 2 + b ^ 2) := by
    rw [Complex.cos_arg hz, hn]
  have hs : sin (Complex.arg ⟨a, b⟩) = b / √(a ^ 2 + b ^ 2) := by
    rw [Complex.sin_arg, hn]
  refine ⟨Complex.arg ⟨a, b⟩, hc, hs, fun x => ?_⟩
  rw [sin_add, hc, hs]
  field_simp

/-- Amplitude bound: `|a sin x + b cos x| ≤ √(a²+b²)` (TR-118). -/
@[kb "corraltrig" "Box §5.2, p. 116"]
theorem abs_mul_sin_add_mul_cos_le (a b x : ℝ) : |a * sin x + b * cos x| ≤ √(a ^ 2 + b ^ 2) := by
  apply Real.abs_le_sqrt
  nlinarith [sq_nonneg (a * cos x - b * sin x), sin_sq_add_cos_sq x]

/-- The amplitude `√(a²+b²)` is attained (TR-118). -/
theorem exists_mul_sin_add_mul_cos_eq (a b : ℝ) (hab : a ≠ 0 ∨ b ≠ 0) :
    ∃ x, a * sin x + b * cos x = √(a ^ 2 + b ^ 2) := by
  obtain ⟨φ, -, -, h⟩ := exists_amplitude_phase a b hab
  refine ⟨π / 2 - φ, ?_⟩
  rw [h, show π / 2 - φ + φ = π / 2 by ring, sin_pi_div_two, mul_one]

/-- The tangent of the angle between lines of inclinations `arctan m₁`, `arctan m₂`:
`tan (arctan m₂ - arctan m₁) = (m₂ - m₁)/(1 + m₁ m₂)`; no hypothesis is needed since both sides
are `0` when `1 + m₁ m₂ = 0` (TR-064). -/
@[kb "openstaxalgtrig2e" "Ex 10 §9.2, p. 833"]
theorem tan_arctan_sub_arctan (m₁ m₂ : ℝ) :
    tan (arctan m₂ - arctan m₁) = (m₂ - m₁) / (1 + m₁ * m₂) := by
  rw [tan_eq_sin_div_cos, sin_sub, cos_sub, sin_arctan, sin_arctan, cos_arctan, cos_arctan]
  have h1 : (0:ℝ) < √(1 + m₁ ^ 2) := Real.sqrt_pos.2 (by positivity)
  have h2 : (0:ℝ) < √(1 + m₂ ^ 2) := Real.sqrt_pos.2 (by positivity)
  have e1 : m₂ / √(1 + m₂ ^ 2) * (1 / √(1 + m₁ ^ 2)) - 1 / √(1 + m₂ ^ 2) * (m₁ / √(1 + m₁ ^ 2))
      = (m₂ - m₁) / (√(1 + m₂ ^ 2) * √(1 + m₁ ^ 2)) := by field_simp
  have e2 : 1 / √(1 + m₂ ^ 2) * (1 / √(1 + m₁ ^ 2)) + m₂ / √(1 + m₂ ^ 2) * (m₁ / √(1 + m₁ ^ 2))
      = (1 + m₁ * m₂) / (√(1 + m₂ ^ 2) * √(1 + m₁ ^ 2)) := by field_simp
  rw [e1, e2]
  field_simp

/-- Acute-angle form: `|tan (arctan m₂ - arctan m₁)| = |(m₂ - m₁)/(1 + m₁ m₂)|` (TR-064). -/
theorem abs_tan_arctan_sub_arctan (m₁ m₂ : ℝ) :
    |tan (arctan m₂ - arctan m₁)| = |(m₂ - m₁) / (1 + m₁ * m₂)| := by
  rw [tan_arctan_sub_arctan m₁ m₂]

/-- Two lines with direction vectors `(1, m₁)`, `(1, m₂)` are perpendicular iff `m₁ m₂ = -1`
(TR-164). -/
@[kb "corraltrig" "Ex 1.26, p. 41"]
theorem inner_slope_vectors_eq_zero_iff (m₁ m₂ : ℝ) :
    inner ℝ (!₂[(1:ℝ), m₁]) (!₂[(1:ℝ), m₂]) = 0 ↔ m₁ * m₂ = -1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  constructor <;> intro h <;> linarith

/-- The slope `m` is the tangent of the inclination `arctan m`, which lies in `(-π/2, π/2)`
(TR-112). -/
@[kb "corraltrig" "Box §1.5, p. 41"]
theorem tan_arctan_slope (m : ℝ) :
    tan (arctan m) = m ∧ -(π / 2) < arctan m ∧ arctan m < π / 2 :=
  ⟨tan_arctan m, neg_pi_div_two_lt_arctan m, arctan_lt_pi_div_two m⟩

end UndergradKB.Trigonometry
