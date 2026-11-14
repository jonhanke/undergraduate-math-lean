import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Sqrt
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.PolarComplex

/-! # Course layer, Chapter 11 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 11.5

Graphs of polar equations: the curves `r = a + b cos θ + c sin θ` (circles, cardioids, limaçons) and the
lemniscates are described by an equation in `x` and `y`. -/

namespace UndergradKB.Precalculus.Course

open Real Set

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-! ## Helpers -/

private theorem w5_polar (x y : ℝ) (h0 : x ^ 2 + y ^ 2 ≠ 0) :
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

/-- The origin lies on `r = a + b cos θ + c sin θ` when `a² ≤ b² + c²`. -/
private theorem w5_zero (a b c : ℝ) (h : a ^ 2 ≤ b ^ 2 + c ^ 2) :
    ∃ θ : ℝ, a + b * cos θ + c * sin θ = 0 := by
  by_cases hR : b ^ 2 + c ^ 2 = 0
  · have hb : b = 0 := by nlinarith [sq_nonneg b, sq_nonneg c]
    have hc : c = 0 := by nlinarith [sq_nonneg b, sq_nonneg c]
    have ha : a = 0 := by nlinarith [sq_nonneg a]
    exact ⟨0, by rw [ha, hb, hc]; ring⟩
  · set z : ℂ := ⟨b, c⟩ with hz
    have hn : ‖z‖ ^ 2 = b ^ 2 + c ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_mk]; ring
    have hpos : 0 < ‖z‖ := by
      rw [norm_pos_iff]; intro h0
      apply hR
      have h1 := congrArg Complex.re h0
      have h2 := congrArg Complex.im h0
      simp [hz] at h1 h2
      rw [h1, h2]; ring
    have h1 : ‖z‖ * cos (Complex.arg z) = b := Complex.norm_mul_cos_arg z
    have h2 : ‖z‖ * sin (Complex.arg z) = c := Complex.norm_mul_sin_arg z
    have hu1 : -1 ≤ -a / ‖z‖ := by
      rw [le_div_iff₀ hpos]; nlinarith [sq_nonneg (‖z‖ - |a|), abs_nonneg a, sq_abs a]
    have hu2 : -a / ‖z‖ ≤ 1 := by
      rw [div_le_iff₀ hpos]; nlinarith [sq_nonneg (‖z‖ - |a|), abs_nonneg a, sq_abs a]
    have hcos := cos_arccos hu1 hu2
    refine ⟨Complex.arg z + arccos (-a / ‖z‖), ?_⟩
    rw [cos_add, sin_add]
    have : b * (cos (Complex.arg z) * cos (arccos (-a / ‖z‖)) - sin (Complex.arg z) * sin (arccos (-a / ‖z‖))) +
        c * (sin (Complex.arg z) * cos (arccos (-a / ‖z‖)) + cos (Complex.arg z) * sin (arccos (-a / ‖z‖))) =
        (b * cos (Complex.arg z) + c * sin (Complex.arg z)) * cos (arccos (-a / ‖z‖)) +
        (c * cos (Complex.arg z) - b * sin (Complex.arg z)) * sin (arccos (-a / ‖z‖)) := by ring
    have e1 : b * cos (Complex.arg z) + c * sin (Complex.arg z) = ‖z‖ := by
      have := sin_sq_add_cos_sq (Complex.arg z)
      rw [← h1, ← h2]; linear_combination ‖z‖ * this
    have e2 : c * cos (Complex.arg z) - b * sin (Complex.arg z) = 0 := by
      rw [← h1, ← h2]; ring
    rw [add_assoc, this, e1, e2, hcos]
    field_simp
    ring

/-- The polar graph `r = a + b cos θ + c sin θ` (with `a² ≤ b² + c²`, so that it passes through the pole)
is the curve `(x² + y² - b x - c y)² = a² (x² + y²)`. -/
private theorem w5_lima (f : ℝ → ℝ) (a b c : ℝ) (hf : ∀ θ, f θ = a + b * cos θ + c * sin θ)
    (hab : a ^ 2 ≤ b ^ 2 + c ^ 2) :
    {p : ℝ × ℝ | ∃ θ, p = polarPoint (f θ) θ} =
      {p | (p.1 ^ 2 + p.2 ^ 2 - b * p.1 - c * p.2) ^ 2 = a ^ 2 * (p.1 ^ 2 + p.2 ^ 2)} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨θ, h⟩
    simp only [polarPoint, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [hf]
    have e : (((a + b * cos θ + c * sin θ) * cos θ) ^ 2 + ((a + b * cos θ + c * sin θ) * sin θ) ^ 2 -
        b * ((a + b * cos θ + c * sin θ) * cos θ) - c * ((a + b * cos θ + c * sin θ) * sin θ)) =
        (a + b * cos θ + c * sin θ) * a := by
      linear_combination (a + b * cos θ + c * sin θ) ^ 2 * sin_sq_add_cos_sq θ
    rw [e]
    linear_combination (-(a ^ 2) * (a + b * cos θ + c * sin θ) ^ 2) * sin_sq_add_cos_sq θ
  · intro h
    by_cases h0 : x ^ 2 + y ^ 2 = 0
    · have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
      have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
      obtain ⟨θ, hθ⟩ := w5_zero a b c hab
      refine ⟨θ, ?_⟩
      simp [polarPoint, hx, hy, hf, hθ]
    · obtain ⟨ρ, φ, hρ, hx, hy⟩ := w5_polar x y h0
      have e1 : x ^ 2 + y ^ 2 = ρ ^ 2 := by
        rw [hx, hy]; linear_combination ρ ^ 2 * sin_sq_add_cos_sq φ
      have e2 : x ^ 2 + y ^ 2 - b * x - c * y = ρ * (ρ - (b * cos φ + c * sin φ)) := by
        rw [hx, hy]; linear_combination ρ ^ 2 * sin_sq_add_cos_sq φ
      rw [e2, e1] at h
      have h3 : ((ρ - (b * cos φ + c * sin φ)) - a) * ((ρ - (b * cos φ + c * sin φ)) + a) = 0 := by
        have : ρ ^ 2 * (((ρ - (b * cos φ + c * sin φ)) - a) * ((ρ - (b * cos φ + c * sin φ)) + a)) = 0 := by
          linear_combination h
        rcases mul_eq_zero.mp this with h4 | h4
        · exfalso; exact hρ.ne' (pow_eq_zero_iff (two_ne_zero) |>.mp h4)
        · exact h4
      rcases mul_eq_zero.mp h3 with h4 | h4
      · refine ⟨φ, ?_⟩
        simp only [polarPoint, Prod.mk.injEq]
        rw [hf, show a + b * cos φ + c * sin φ = ρ by linarith]
        exact ⟨hx, hy⟩
      · refine ⟨φ + π, ?_⟩
        have h5 := (polar_point_same_names ρ φ 0).2.1
        norm_num at h5
        rw [hf, cos_add_pi, sin_add_pi, show a + b * -cos φ + c * -sin φ = -ρ by linarith, h5]
        exact Prod.ext hx hy

/-! ## Section 11.5: circles, cardioids, limaçons -/

/-- Stitz-Zeager Exercise 11.5.9: the cardioid `r = 3 - 3 cos θ` is `(x² + y² + 3x)² = 9 (x² + y²)`. -/
@[kb "stitzzeager2013" "Exercise 11.5.9, p. 970"]
theorem exer_11_5_9 :
    {p : ℝ × ℝ | ∃ θ, p = polarPoint (3 - 3 * cos θ) θ} =
      {p | (p.1 ^ 2 + p.2 ^ 2 + 3 * p.1) ^ 2 = 9 * (p.1 ^ 2 + p.2 ^ 2)} := by
  rw [w5_lima (fun θ => 3 - 3 * cos θ) 3 (-3) 0 (fun θ => by ring) (by norm_num)]
  ext p
  simp only [Set.mem_ofPred_eq]
  constructor <;> intro h <;> linear_combination h

/-- Stitz-Zeager Exercise 11.5.10: the cardioid `r = 5 + 5 sin θ` is `(x² + y² - 5y)² = 25 (x² + y²)`. -/
@[kb "stitzzeager2013" "Exercise 11.5.10, p. 970"]
theorem exer_11_5_10 :
    {p : ℝ × ℝ | ∃ θ, p = polarPoint (5 + 5 * sin θ) θ} =
      {p | (p.1 ^ 2 + p.2 ^ 2 - 5 * p.2) ^ 2 = 25 * (p.1 ^ 2 + p.2 ^ 2)} := by
  rw [w5_lima (fun θ => 5 + 5 * sin θ) 5 0 5 (fun θ => by ring) (by norm_num)]
  ext p
  simp only [Set.mem_ofPred_eq]
  constructor <;> intro h <;> linear_combination h

/-- Stitz-Zeager Exercise 11.5.11: the cardioid `r = 2 + 2 cos θ` is `(x² + y² - 2x)² = 4 (x² + y²)`. -/
@[kb "stitzzeager2013" "Exercise 11.5.11, p. 970"]
theorem exer_11_5_11 :
    {p : ℝ × ℝ | ∃ θ, p = polarPoint (2 + 2 * cos θ) θ} =
      {p | (p.1 ^ 2 + p.2 ^ 2 - 2 * p.1) ^ 2 = 4 * (p.1 ^ 2 + p.2 ^ 2)} := by
  rw [w5_lima (fun θ => 2 + 2 * cos θ) 2 2 0 (fun θ => by ring) (by norm_num)]
  ext p
  simp only [Set.mem_ofPred_eq]
  constructor <;> intro h <;> linear_combination h

/-- Stitz-Zeager Exercise 11.5.12: the cardioid `r = 1 - sin θ` is `(x² + y² + y)² = x² + y²`. -/
@[kb "stitzzeager2013" "Exercise 11.5.12, p. 970"]
theorem exer_11_5_12 :
    {p : ℝ × ℝ | ∃ θ, p = polarPoint (1 - sin θ) θ} =
      {p | (p.1 ^ 2 + p.2 ^ 2 + p.2) ^ 2 = p.1 ^ 2 + p.2 ^ 2} := by
  rw [w5_lima (fun θ => 1 - sin θ) 1 0 (-1) (fun θ => by ring) (by norm_num)]
  ext p
  simp only [Set.mem_ofPred_eq]
  constructor <;> intro h <;> linear_combination h

/-- Stitz-Zeager Exercise 11.5.13: the limaçon `r = 1 - 2 cos θ` is `(x² + y² + 2x)² = x² + y²`. -/
@[kb "stitzzeager2013" "Exercise 11.5.13, p. 970"]
theorem exer_11_5_13 :
    {p : ℝ × ℝ | ∃ θ, p = polarPoint (1 - 2 * cos θ) θ} =
      {p | (p.1 ^ 2 + p.2 ^ 2 + 2 * p.1) ^ 2 = p.1 ^ 2 + p.2 ^ 2} := by
  rw [w5_lima (fun θ => 1 - 2 * cos θ) 1 (-2) 0 (fun θ => by ring) (by norm_num)]
  ext p
  simp only [Set.mem_ofPred_eq]
  constructor <;> intro h <;> linear_combination h

/-- Stitz-Zeager Exercise 11.5.14: the limaçon `r = 1 - 2 sin θ` is `(x² + y² + 2y)² = x² + y²`. -/
@[kb "stitzzeager2013" "Exercise 11.5.14, p. 970"]
theorem exer_11_5_14 :
    {p : ℝ × ℝ | ∃ θ, p = polarPoint (1 - 2 * sin θ) θ} =
      {p | (p.1 ^ 2 + p.2 ^ 2 + 2 * p.2) ^ 2 = p.1 ^ 2 + p.2 ^ 2} := by
  rw [w5_lima (fun θ => 1 - 2 * sin θ) 1 0 (-2) (fun θ => by ring) (by norm_num)]
  ext p
  simp only [Set.mem_ofPred_eq]
  constructor <;> intro h <;> linear_combination h

/-- Stitz-Zeager Exercise 11.5.15: the limaçon `r = 2√3 + 4 cos θ` is `(x² + y² - 4x)² = 12 (x² + y²)`. -/
@[kb "stitzzeager2013" "Exercise 11.5.15, p. 970"]
theorem exer_11_5_15 :
    {p : ℝ × ℝ | ∃ θ, p = polarPoint (2 * √3 + 4 * cos θ) θ} =
      {p | (p.1 ^ 2 + p.2 ^ 2 - 4 * p.1) ^ 2 = 12 * (p.1 ^ 2 + p.2 ^ 2)} := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [w5_lima (fun θ => 2 * √3 + 4 * cos θ) (2 * √3) 4 0 (fun θ => by ring) (by nlinarith)]
  ext p
  simp only [Set.mem_ofPred_eq]
  constructor <;> intro h <;> nlinarith [h]

/-- Stitz-Zeager Exercise 11.5.16: the limaçon `r = 3 - 5 cos θ` is `(x² + y² + 5x)² = 9 (x² + y²)`. -/
@[kb "stitzzeager2013" "Exercise 11.5.16, p. 970"]
theorem exer_11_5_16 :
    {p : ℝ × ℝ | ∃ θ, p = polarPoint (3 - 5 * cos θ) θ} =
      {p | (p.1 ^ 2 + p.2 ^ 2 + 5 * p.1) ^ 2 = 9 * (p.1 ^ 2 + p.2 ^ 2)} := by
  rw [w5_lima (fun θ => 3 - 5 * cos θ) 3 (-5) 0 (fun θ => by ring) (by norm_num)]
  ext p
  simp only [Set.mem_ofPred_eq]
  constructor <;> intro h <;> linear_combination h

/-- Stitz-Zeager Exercise 11.5.17: the limaçon `r = 3 - 5 sin θ` is `(x² + y² + 5y)² = 9 (x² + y²)`. -/
@[kb "stitzzeager2013" "Exercise 11.5.17, p. 970"]
theorem exer_11_5_17 :
    {p : ℝ × ℝ | ∃ θ, p = polarPoint (3 - 5 * sin θ) θ} =
      {p | (p.1 ^ 2 + p.2 ^ 2 + 5 * p.2) ^ 2 = 9 * (p.1 ^ 2 + p.2 ^ 2)} := by
  rw [w5_lima (fun θ => 3 - 5 * sin θ) 3 0 (-5) (fun θ => by ring) (by norm_num)]
  ext p
  simp only [Set.mem_ofPred_eq]
  constructor <;> intro h <;> linear_combination h

/-- Stitz-Zeager Exercise 11.5.18: the limaçon `r = 2 + 7 sin θ` is `(x² + y² - 7y)² = 4 (x² + y²)`. -/
@[kb "stitzzeager2013" "Exercise 11.5.18, p. 970"]
theorem exer_11_5_18 :
    {p : ℝ × ℝ | ∃ θ, p = polarPoint (2 + 7 * sin θ) θ} =
      {p | (p.1 ^ 2 + p.2 ^ 2 - 7 * p.2) ^ 2 = 4 * (p.1 ^ 2 + p.2 ^ 2)} := by
  rw [w5_lima (fun θ => 2 + 7 * sin θ) 2 0 7 (fun θ => by ring) (by norm_num)]
  ext p
  simp only [Set.mem_ofPred_eq]
  constructor <;> intro h <;> linear_combination h

/-! ## Section 11.5: lemniscates -/

/-- Stitz-Zeager Exercise 11.5.19: the lemniscate `r² = sin 2θ` is `(x² + y²)² = 2xy`. -/
@[kb "stitzzeager2013" "Exercise 11.5.19, p. 970"]
theorem exer_11_5_19 :
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
    · obtain ⟨ρ, φ, hρ, hx, hy⟩ := w5_polar x y h0
      have e1 : x ^ 2 + y ^ 2 = ρ ^ 2 := by
        rw [hx, hy]; linear_combination ρ ^ 2 * sin_sq_add_cos_sq φ
      refine ⟨φ, ρ, ?_, by simp only [polarPoint, Prod.mk.injEq]; exact ⟨hx, hy⟩⟩
      rw [sin_two_mul]
      rw [e1] at h
      have h2 : ρ ^ 2 * (ρ ^ 2 - 2 * sin φ * cos φ) = 0 := by
        rw [hx, hy] at h
        linear_combination h
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exfalso; exact hρ.ne' (pow_eq_zero_iff (two_ne_zero) |>.mp h3)
      · linarith

/-- Stitz-Zeager Exercise 11.5.20: the lemniscate `r² = 4 cos 2θ` is `(x² + y²)² = 4 (x² - y²)`. -/
@[kb "stitzzeager2013" "Exercise 11.5.20, p. 970"]
theorem exer_11_5_20 :
    {p : ℝ × ℝ | ∃ θ r : ℝ, r ^ 2 = 4 * cos (2 * θ) ∧ p = polarPoint r θ} =
      {p | (p.1 ^ 2 + p.2 ^ 2) ^ 2 = 4 * (p.1 ^ 2 - p.2 ^ 2)} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨θ, r, hr, h⟩
    simp only [polarPoint, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [cos_two_mul] at hr
    have e : (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 := by
      linear_combination r ^ 2 * sin_sq_add_cos_sq θ
    rw [e]
    have h2 : 4 * ((r * cos θ) ^ 2 - (r * sin θ) ^ 2) = 4 * r ^ 2 * (2 * cos θ ^ 2 - 1) := by
      linear_combination (-4 * r ^ 2) * sin_sq_add_cos_sq θ
    rw [h2]
    linear_combination r ^ 2 * hr
  · intro h
    by_cases h0 : x ^ 2 + y ^ 2 = 0
    · have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
      have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
      exact ⟨π / 4, 0, by rw [show 2 * (π / 4) = π / 2 by ring, cos_pi_div_two]; norm_num, by simp [polarPoint, hx, hy]⟩
    · obtain ⟨ρ, φ, hρ, hx, hy⟩ := w5_polar x y h0
      have e1 : x ^ 2 + y ^ 2 = ρ ^ 2 := by
        rw [hx, hy]; linear_combination ρ ^ 2 * sin_sq_add_cos_sq φ
      refine ⟨φ, ρ, ?_, by simp only [polarPoint, Prod.mk.injEq]; exact ⟨hx, hy⟩⟩
      rw [cos_two_mul]
      rw [e1] at h
      have h2 : ρ ^ 2 * (ρ ^ 2 - 4 * (2 * cos φ ^ 2 - 1)) = 0 := by
        rw [hx, hy] at h
        linear_combination h + (-4 * ρ ^ 2) * sin_sq_add_cos_sq φ
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exfalso; exact hρ.ne' (pow_eq_zero_iff (two_ne_zero) |>.mp h3)
      · linarith

/-! ## Section 11.6: conics in polar form -/

/-- The polar graph `r = c / D(θ)` with `D(θ) = a - u cos θ - v sin θ` and `c ≠ 0` (all branches, negative `r`
included) is the curve `a² (x² + y²) = (u x + v y + c)²`. -/
private theorem w6_conic (D : ℝ → ℝ) (a u v c : ℝ) (hc : c ≠ 0)
    (hD : ∀ θ, D θ = a - u * cos θ - v * sin θ) :
    {p : ℝ × ℝ | ∃ θ : ℝ, D θ ≠ 0 ∧ p = polarPoint (c / D θ) θ} =
      {p | a ^ 2 * (p.1 ^ 2 + p.2 ^ 2) = (u * p.1 + v * p.2 + c) ^ 2} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨θ, hne, h⟩
    simp only [polarPoint, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨r, hr⟩ : ∃ r, r = c / D θ := ⟨_, rfl⟩
    rw [← hr]
    have hrD : r * D θ = c := by rw [hr]; field_simp
    rw [hD θ] at hrD
    have hL : u * (r * cos θ) + v * (r * sin θ) + c = a * r := by
      linear_combination (-1) * hrD
    rw [hL]
    linear_combination (a ^ 2 * r ^ 2) * sin_sq_add_cos_sq θ
  · intro h
    by_cases h0 : x ^ 2 + y ^ 2 = 0
    · exfalso
      have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
      have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
      rw [hx, hy] at h
      apply hc
      nlinarith [sq_nonneg c]
    · obtain ⟨ρ, φ, hρ, hx, hy⟩ := w5_polar x y h0
      rw [hx, hy] at h
      have h3 : (a * ρ - (u * (ρ * cos φ) + v * (ρ * sin φ) + c)) *
          (a * ρ + (u * (ρ * cos φ) + v * (ρ * sin φ) + c)) = 0 := by
        linear_combination h - (a ^ 2 * ρ ^ 2) * sin_sq_add_cos_sq φ
      rcases mul_eq_zero.mp h3 with h4 | h4
      · have hρD : ρ * D φ = c := by rw [hD]; linear_combination h4
        have hne : D φ ≠ 0 := by
          intro hz; rw [hz, mul_zero] at hρD; exact hc hρD.symm
        refine ⟨φ, hne, ?_⟩
        have : c / D φ = ρ := (div_eq_iff hne).mpr (by linarith [hρD])
        rw [this]
        simp only [polarPoint, Prod.mk.injEq]
        exact ⟨hx, hy⟩
      · have hρD : ρ * D (φ + π) = -c := by
          rw [hD, cos_add_pi, sin_add_pi]; linear_combination h4
        have hne : D (φ + π) ≠ 0 := by
          intro hz; rw [hz, mul_zero] at hρD
          exact hc (by linarith)
        refine ⟨φ + π, hne, ?_⟩
        have : c / D (φ + π) = -ρ := (div_eq_iff hne).mpr (by linarith [hρD])
        rw [this]
        have h5 := (polar_point_same_names ρ φ 0).2.1
        norm_num at h5
        rw [h5]
        exact Prod.ext hx hy

/-- Stitz-Zeager Exercise 11.6.13: the polar graph `r = 4/(1 + 3 cos θ)` is the hyperbola
`4 (x - 3/2)² - y²/2 = 1` (focus at the pole, center `(3/2, 0)`, vertices `(1, 0)` and `(2, 0)`). -/
@[kb "stitzzeager2013" "Exercise 11.6.13, p. 998"]
theorem exer_11_6_13 :
    {p : ℝ × ℝ | ∃ θ : ℝ, 1 + 3 * cos θ ≠ 0 ∧ p = polarPoint (4 / (1 + 3 * cos θ)) θ} =
      {p | 4 * (p.1 - 3 / 2) ^ 2 - p.2 ^ 2 / 2 = 1} := by
  have h := w6_conic (fun θ => 1 + 3 * cos θ) 1 (-3) 0 4 (by norm_num) (fun θ => by ring)
  refine h.trans ?_
  ext p
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h; linear_combination (-1 / 2 : ℝ) * h
  · intro h; linear_combination (-2 : ℝ) * h

/-- Stitz-Zeager Exercise 11.6.14: the polar graph `r = 2/(1 - 2 sin θ)` is the hyperbola
`(9/4)(y + 4/3)² - (3/4) x² = 1` (center `(0, -4/3)`, vertices `(0, -2/3)` and `(0, -2)`). -/
@[kb "stitzzeager2013" "Exercise 11.6.14, p. 998"]
theorem exer_11_6_14 :
    {p : ℝ × ℝ | ∃ θ : ℝ, 1 - 2 * sin θ ≠ 0 ∧ p = polarPoint (2 / (1 - 2 * sin θ)) θ} =
      {p | 9 * (p.2 + 4 / 3) ^ 2 / 4 - 3 * p.1 ^ 2 / 4 = 1} := by
  have h := w6_conic (fun θ => 1 - 2 * sin θ) 1 0 2 2 (by norm_num) (fun θ => by ring)
  refine h.trans ?_
  ext p
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h; linear_combination (-3 / 4 : ℝ) * h
  · intro h; linear_combination (-4 / 3 : ℝ) * h

/-- Stitz-Zeager Exercise 11.6.15: the polar graph `r = 2/(1 + sin (θ - π/3))` (the parabola `r = 2/(1 + sin θ)`
rotated through `π/3`) is the curve `x² + y² = (√3 x/2 - y/2 + 2)²`. -/
@[kb "stitzzeager2013" "Exercise 11.6.15, p. 998"]
theorem exer_11_6_15 :
    {p : ℝ × ℝ | ∃ θ : ℝ, 1 + sin (θ - π / 3) ≠ 0 ∧ p = polarPoint (2 / (1 + sin (θ - π / 3))) θ} =
      {p | p.1 ^ 2 + p.2 ^ 2 = (√3 / 2 * p.1 - 1 / 2 * p.2 + 2) ^ 2} := by
  have h := w6_conic (fun θ => 1 + sin (θ - π / 3)) 1 (√3 / 2) (-(1 / 2)) 2 (by norm_num)
    (fun θ => by rw [sin_sub, cos_pi_div_three, sin_pi_div_three]; ring)
  refine h.trans ?_
  ext p
  simp only [Set.mem_ofPred_eq]
  constructor <;> intro h <;> linear_combination h

/-- Stitz-Zeager Exercise 11.6.16: the polar graph `r = 6/(3 - cos (θ + π/4))` (the ellipse `r = 6/(3 - cos θ)`
rotated through `-π/4`) is the curve `9 (x² + y²) = (√2 x/2 - √2 y/2 + 6)²`. -/
@[kb "stitzzeager2013" "Exercise 11.6.16, p. 998"]
theorem exer_11_6_16 :
    {p : ℝ × ℝ | ∃ θ : ℝ, 3 - cos (θ + π / 4) ≠ 0 ∧ p = polarPoint (6 / (3 - cos (θ + π / 4))) θ} =
      {p | 9 * (p.1 ^ 2 + p.2 ^ 2) = (√2 / 2 * p.1 - √2 / 2 * p.2 + 6) ^ 2} := by
  have h := w6_conic (fun θ => 3 - cos (θ + π / 4)) 3 (√2 / 2) (-(√2 / 2)) 6 (by norm_num)
    (fun θ => by rw [cos_add, cos_pi_div_four, sin_pi_div_four]; ring)
  refine h.trans ?_
  ext p
  simp only [Set.mem_ofPred_eq]
  constructor <;> intro h <;> linear_combination h

end UndergradKB.Precalculus.Course
