import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Real.Pi.Bounds
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 11 (Stitz-Zeager): exercises with the book's answers

Section 11.10 (parametric equations): parametrized curves are described by the point sets
(`(x(t), y(t))` for `t` in the parameter range) and their rectangular equations. -/

namespace UndergradKB.Precalculus.Course

open Real Set

set_option linter.unusedSimpArgs false

/-! ## Helpers -/

private theorem x11i_unit (X Y : ℝ) (h : X ^ 2 + Y ^ 2 = 1) :
    ∃ t : ℝ, 0 ≤ t ∧ t < 2 * π ∧ cos t = X ∧ sin t = Y := by
  set z : ℂ := ⟨X, Y⟩ with hz
  have hn : ‖z‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_apply]
    have : z.re * z.re + z.im * z.im = 1 := by simp only [hz]; nlinarith
    rw [this]; simp
  have c1 : cos (Complex.arg z) = X := by
    have := Complex.norm_mul_cos_arg z
    rw [hn] at this; simpa [hz] using this
  have c2 : sin (Complex.arg z) = Y := by
    have := Complex.norm_mul_sin_arg z
    rw [hn] at this; simpa [hz] using this
  have hpi := pi_pos
  have h1 := Complex.arg_le_pi z
  have h2 := Complex.neg_pi_lt_arg z
  by_cases hh : 0 ≤ Complex.arg z
  · exact ⟨Complex.arg z, hh, by linarith, c1, c2⟩
  · refine ⟨Complex.arg z + 2 * π, by linarith, by linarith, ?_, ?_⟩
    · rw [cos_add_two_pi]; exact c1
    · rw [sin_add_two_pi]; exact c2

/-- The ellipse `((x - a)/u)² + ((y - b)/v)² = 1` is traced by `(a + u cos t, b + v sin t)`, `0 ≤ t < 2π`. -/
private theorem x11i_ell (a b u v : ℝ) :
    {p : ℝ × ℝ | ∃ t : ℝ, 0 ≤ t ∧ t < 2 * π ∧ p = (a + u * cos t, b + v * sin t)} ⊇
        {p : ℝ × ℝ | ((p.1 - a) / u) ^ 2 + ((p.2 - b) / v) ^ 2 = 1} ∩ {p | u ≠ 0 ∧ v ≠ 0} ∧
      ∀ t : ℝ, ((a + u * cos t - a) / u) ^ 2 + ((b + v * sin t - b) / v) ^ 2 = 1 ∨ u = 0 ∨ v = 0 := by
  refine ⟨?_, fun t => ?_⟩
  · rintro ⟨x, y⟩ ⟨h, hu, hv⟩
    simp only [Set.mem_ofPred_eq] at h hu hv
    obtain ⟨t, h0, h1, c1, c2⟩ := x11i_unit ((x - a) / u) ((y - b) / v) h
    refine ⟨t, h0, h1, ?_⟩
    simp only [Prod.mk.injEq]
    constructor
    · rw [c1]; field_simp; ring
    · rw [c2]; field_simp; ring
  · by_cases hu : u = 0
    · exact Or.inr (Or.inl hu)
    by_cases hv : v = 0
    · exact Or.inr (Or.inr hv)
    left
    have e1 : (a + u * cos t - a) / u = cos t := by field_simp; ring
    have e2 : (b + v * sin t - b) / v = sin t := by field_simp; ring
    rw [e1, e2]; exact cos_sq_add_sin_sq t

/-- For `u, v ≠ 0` the curve `(a + u cos t, b + v sin t)`, `0 ≤ t < 2π`, is exactly the ellipse
`((x - a)/u)² + ((y - b)/v)² = 1`. -/
private theorem x11i_ellipse {a b u v : ℝ} (hu : u ≠ 0) (hv : v ≠ 0) :
    {p : ℝ × ℝ | ∃ t : ℝ, 0 ≤ t ∧ t < 2 * π ∧ p = (a + u * cos t, b + v * sin t)} =
      {p : ℝ × ℝ | ((p.1 - a) / u) ^ 2 + ((p.2 - b) / v) ^ 2 = 1} := by
  obtain ⟨hsub, hall⟩ := x11i_ell a b u v
  apply Set.Subset.antisymm
  · rintro p ⟨t, -, -, rfl⟩
    simp only [Set.mem_ofPred_eq]
    rcases hall t with h | h | h
    · exact h
    · exact absurd h hu
    · exact absurd h hv
  · intro p hp
    exact hsub ⟨hp, hu, hv⟩

/-! ## Section 11.10 -/

/-- Stitz-Zeager Exercise 11.10.25: the directed segment from `(3, -5)` to `(-2, 2)` is parametrized by
`x = 3 - 5t`, `y = -5 + 7t`, `0 ≤ t ≤ 1`. -/
@[kb "stitzzeager2013" "Exercise 11.10.25, p. 1072"]
theorem exer_11_10_25 :
    {p : ℝ × ℝ | ∃ t ∈ Icc (0 : ℝ) 1, p = (3 - 5 * t, -5 + 7 * t)} = segment ℝ ((3 : ℝ), (-5 : ℝ)) (-2, 2) := by
  rw [segment_eq_image']
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t, ht, ?_⟩
    simp only [Prod.smul_mk, Prod.mk_sub_mk, Prod.mk_add_mk, smul_eq_mul, Prod.mk.injEq]
    constructor <;> ring
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t, ht, ?_⟩
    simp only [Prod.smul_mk, Prod.mk_sub_mk, Prod.mk_add_mk, smul_eq_mul, Prod.mk.injEq]
    constructor <;> ring

/-- Stitz-Zeager Exercise 11.10.27: the curve `y = 4 - x²` from `(-2, 0)` to `(2, 0)` is parametrized by
`x = t`, `y = 4 - t²`, `-2 ≤ t ≤ 2`. -/
@[kb "stitzzeager2013" "Exercise 11.10.27, p. 1072"]
theorem exer_11_10_27 :
    {p : ℝ × ℝ | ∃ t ∈ Icc (-2 : ℝ) 2, p = (t, 4 - t ^ 2)} =
      {p | p.2 = 4 - p.1 ^ 2 ∧ p.1 ∈ Icc (-2 : ℝ) 2} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨t, ht, rfl, rfl⟩
    exact ⟨rfl, ht⟩
  · rintro ⟨h1, h2⟩
    exact ⟨x, h2, rfl, h1⟩

/-- Stitz-Zeager Exercise 11.10.28: the same curve with the parameter shifted so that `t = 0` is the point
`(-2, 0)`: `x = t - 2`, `y = 4t - t²`, `0 ≤ t ≤ 4`. -/
@[kb "stitzzeager2013" "Exercise 11.10.28, p. 1072"]
theorem exer_11_10_28 :
    {p : ℝ × ℝ | ∃ t ∈ Icc (0 : ℝ) 4, p = (t - 2, 4 * t - t ^ 2)} =
      {p | p.2 = 4 - p.1 ^ 2 ∧ p.1 ∈ Icc (-2 : ℝ) 2} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, Prod.mk.injEq, mem_Icc]
  constructor
  · rintro ⟨t, ⟨h0, h4⟩, rfl, rfl⟩
    refine ⟨by ring, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨x + 2, ⟨by linarith, by linarith⟩, by ring, by rw [h1]; ring⟩

/-- Stitz-Zeager Exercise 11.10.29: the curve `x = y² - 9` from `(-5, -2)` to `(0, 3)` is parametrized by
`x = t² - 9`, `y = t`, `-2 ≤ t ≤ 3`. -/
@[kb "stitzzeager2013" "Exercise 11.10.29, p. 1072"]
theorem exer_11_10_29 :
    {p : ℝ × ℝ | ∃ t ∈ Icc (-2 : ℝ) 3, p = (t ^ 2 - 9, t)} =
      {p | p.1 = p.2 ^ 2 - 9 ∧ p.2 ∈ Icc (-2 : ℝ) 3} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨t, ht, rfl, rfl⟩
    exact ⟨rfl, ht⟩
  · rintro ⟨h1, h2⟩
    exact ⟨y, h2, h1, rfl⟩

/-- Stitz-Zeager Exercise 11.10.31: the circle `x² + y² = 25`, counter-clockwise from `(5, 0)`, is
`x = 5 cos t`, `y = 5 sin t`, `0 ≤ t < 2π`. -/
@[kb "stitzzeager2013" "Exercise 11.10.31, p. 1072"]
theorem exer_11_10_31 :
    {p : ℝ × ℝ | ∃ t : ℝ, 0 ≤ t ∧ t < 2 * π ∧ p = (5 * cos t, 5 * sin t)} =
      {p | p.1 ^ 2 + p.2 ^ 2 = 25} := by
  have h := @x11i_ellipse 0 0 5 5 (by norm_num) (by norm_num)
  simp only [zero_add] at h
  rw [h]
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, sub_zero]
  constructor <;> intro h <;> nlinarith

/-- Stitz-Zeager Exercise 11.10.32: the circle `(x - 1)² + y² = 4`, counter-clockwise, is
`x = 1 + 2 cos t`, `y = 2 sin t`, `0 ≤ t < 2π`. -/
@[kb "stitzzeager2013" "Exercise 11.10.32, p. 1072"]
theorem exer_11_10_32 :
    {p : ℝ × ℝ | ∃ t : ℝ, 0 ≤ t ∧ t < 2 * π ∧ p = (1 + 2 * cos t, 2 * sin t)} =
      {p | (p.1 - 1) ^ 2 + p.2 ^ 2 = 4} := by
  have h := @x11i_ellipse 1 0 2 2 (by norm_num) (by norm_num)
  simp only [zero_add] at h
  rw [h]
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, sub_zero]
  constructor <;> intro h <;> nlinarith

/-- Stitz-Zeager Exercise 11.10.33: the circle `x² + y² - 6y = 0`, counter-clockwise, is
`x = 3 cos t`, `y = 3 + 3 sin t`, `0 ≤ t < 2π`. -/
@[kb "stitzzeager2013" "Exercise 11.10.33, p. 1072"]
theorem exer_11_10_33 :
    {p : ℝ × ℝ | ∃ t : ℝ, 0 ≤ t ∧ t < 2 * π ∧ p = (3 * cos t, 3 + 3 * sin t)} =
      {p | p.1 ^ 2 + p.2 ^ 2 - 6 * p.2 = 0} := by
  have h := @x11i_ellipse 0 3 3 3 (by norm_num) (by norm_num)
  simp only [zero_add] at h
  rw [h]
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, sub_zero]
  constructor <;> intro h <;> nlinarith

/-- Stitz-Zeager Exercise 11.10.35: the circle `(x - 3)² + (y + 1)² = 117` is
`x = 3 + √117 cos t`, `y = -1 + √117 sin t`, `0 ≤ t < 2π`. -/
@[kb "stitzzeager2013" "Exercise 11.10.35, p. 1072"]
theorem exer_11_10_35 :
    {p : ℝ × ℝ | ∃ t : ℝ, 0 ≤ t ∧ t < 2 * π ∧ p = (3 + √117 * cos t, -1 + √117 * sin t)} =
      {p | (p.1 - 3) ^ 2 + (p.2 + 1) ^ 2 = 117} := by
  have hs : (0 : ℝ) < √117 := by positivity
  have hss : √117 * √117 = 117 := Real.mul_self_sqrt (by norm_num)
  have h := @x11i_ellipse 3 (-1) (√117) (√117) hs.ne' hs.ne'
  rw [h]
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, sub_neg_eq_add]
  field_simp
  constructor <;> intro h <;> nlinarith

/-- Stitz-Zeager Exercise 11.10.36: the ellipse `(x - 1)² + 9y² = 9` is `x = 1 + 3 cos t`, `y = sin t`,
`0 ≤ t < 2π`. -/
@[kb "stitzzeager2013" "Exercise 11.10.36, p. 1072"]
theorem exer_11_10_36 :
    {p : ℝ × ℝ | ∃ t : ℝ, 0 ≤ t ∧ t < 2 * π ∧ p = (1 + 3 * cos t, sin t)} =
      {p | (p.1 - 1) ^ 2 + 9 * p.2 ^ 2 = 9} := by
  have h := @x11i_ellipse 1 0 3 1 (by norm_num) (by norm_num)
  simp only [zero_add, one_mul] at h
  rw [h]
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, sub_zero, div_one]
  constructor <;> intro h <;> nlinarith

/-- Stitz-Zeager Exercise 11.10.37: the ellipse `9x² + 4y² + 24y = 0` is `x = 2 cos t`, `y = 3 sin t - 3`,
`0 ≤ t < 2π`. -/
@[kb "stitzzeager2013" "Exercise 11.10.37, p. 1072"]
theorem exer_11_10_37 :
    {p : ℝ × ℝ | ∃ t : ℝ, 0 ≤ t ∧ t < 2 * π ∧ p = (2 * cos t, -3 + 3 * sin t)} =
      {p | 9 * p.1 ^ 2 + 4 * p.2 ^ 2 + 24 * p.2 = 0} := by
  have h := @x11i_ellipse 0 (-3) 2 3 (by norm_num) (by norm_num)
  simp only [zero_add] at h
  rw [h]
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, sub_zero, sub_neg_eq_add]
  field_simp
  constructor <;> intro h <;> nlinarith

/-- Stitz-Zeager Exercise 11.10.38: the same ellipse traversed clockwise from `(0, 0)` is
`x = 2 sin t`, `y = -3 + 3 cos t`, `0 ≤ t < 2π`. -/
@[kb "stitzzeager2013" "Exercise 11.10.38, p. 1072"]
theorem exer_11_10_38 :
    {p : ℝ × ℝ | ∃ t : ℝ, 0 ≤ t ∧ t < 2 * π ∧ p = (2 * sin t, -3 + 3 * cos t)} =
      {p | 9 * p.1 ^ 2 + 4 * p.2 ^ 2 + 24 * p.2 = 0} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨t, -, -, rfl, rfl⟩
    nlinarith [sin_sq_add_cos_sq t]
  · intro h
    obtain ⟨t, h0, h1, c1, c2⟩ := x11i_unit ((y + 3) / 3) (x / 2) (by nlinarith)
    exact ⟨t, h0, h1, by rw [c2]; ring, by rw [c1]; ring⟩

/-- Stitz-Zeager Exercise 11.10.44: eliminating `t` from the projectile equations `x = v₀ cos θ t`,
`y = -g t²/2 + v₀ sin θ t + s₀` (`v₀ cos θ ≠ 0`) gives the parabola
`y = -(g sec² θ/(2v₀²)) x² + tan θ x + s₀`. -/
@[kb "stitzzeager2013" "Exercise 11.10.44, p. 1073"]
theorem exer_11_10_44a (g v₀ θ s₀ : ℝ) (hv : v₀ ≠ 0) (hc : cos θ ≠ 0) :
    {p : ℝ × ℝ | ∃ t : ℝ, p = (v₀ * cos θ * t, -(g / 2) * t ^ 2 + v₀ * sin θ * t + s₀)} =
      {p | p.2 = -(g * ((cos θ)⁻¹) ^ 2 / (2 * v₀ ^ 2)) * p.1 ^ 2 + tan θ * p.1 + s₀} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, Prod.mk.injEq, tan_eq_sin_div_cos]
  constructor
  · rintro ⟨t, rfl, rfl⟩
    field_simp
  · intro h
    refine ⟨x / (v₀ * cos θ), by field_simp, ?_⟩
    rw [h]
    field_simp

/-- Stitz-Zeager Exercise 11.10.44 (maximum height): for `g > 0` the height `y(t)` of the projectile never
exceeds `v₀² sin² θ/(2g) + s₀`, and the value is attained at `t = v₀ sin θ/g`, where `x = v₀² sin 2θ/(2g)`. -/
@[kb "stitzzeager2013" "Exercise 11.10.44, p. 1073"]
theorem exer_11_10_44b (g v₀ θ s₀ : ℝ) (hg : 0 < g) :
    (∀ t : ℝ, -(g / 2) * t ^ 2 + v₀ * sin θ * t + s₀ ≤ v₀ ^ 2 * sin θ ^ 2 / (2 * g) + s₀) ∧
      -(g / 2) * (v₀ * sin θ / g) ^ 2 + v₀ * sin θ * (v₀ * sin θ / g) + s₀ =
        v₀ ^ 2 * sin θ ^ 2 / (2 * g) + s₀ ∧
      v₀ * cos θ * (v₀ * sin θ / g) = v₀ ^ 2 * sin (2 * θ) / (2 * g) := by
  refine ⟨fun t => ?_, ?_, ?_⟩
  · have : v₀ ^ 2 * sin θ ^ 2 / (2 * g) + s₀ - (-(g / 2) * t ^ 2 + v₀ * sin θ * t + s₀) =
        g / 2 * (t - v₀ * sin θ / g) ^ 2 := by
      field_simp; ring
    nlinarith [sq_nonneg (t - v₀ * sin θ / g)]
  · field_simp; ring
  · rw [sin_two_mul]; field_simp

/-- Stitz-Zeager Exercise 11.10.45: a sheaf released at `5` ft at `85°` with maximum height `31.5` ft
(`g = 32`) has initial speed `v₀ = √1696/sin 85°` (for `v₀ > 0`), which is between `41.33` and `41.35`
ft/s (the book says about `41.34`). -/
@[kb "stitzzeager2013" "Exercise 11.10.45, p. 1074"]
theorem exer_11_10_45 (v₀ : ℝ) (hv : 0 < v₀) :
    (v₀ ^ 2 * sin (85 * π / 180) ^ 2 / (2 * 32) + 5 = 31.5 ↔ v₀ = √1696 / sin (85 * π / 180)) ∧
      41.33 < √1696 / sin (85 * π / 180) ∧ √1696 / sin (85 * π / 180) < 41.35 := by
  have hpi := pi_pos
  have h1 := pi_gt_d2
  have h2 := pi_lt_d2
  have e : sin (85 * π / 180) = cos (π / 36) := by
    rw [← cos_pi_div_two_sub]; congr 1; ring
  have hx : 0 < π / 36 := by positivity
  have hcpos : 0 < cos (π / 36) := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hc1 := one_sub_sq_div_two_le_cos (x := π / 36)
  have hs := sin_gt_sub_cube hx
  have hcs := sin_sq_add_cos_sq (π / 36)
  have hsq : (1696 : ℝ) = √1696 * √1696 := (Real.mul_self_sqrt (by norm_num)).symm
  have hr1 : (41.18 : ℝ) < √1696 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hr2 : √1696 < 41.19 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  rw [e]
  have hcu : cos (π / 36) < 0.9962 := by
    have hsp : 0.0871 < sin (π / 36) := by nlinarith [mul_pos hx hx, mul_pos (mul_pos hx hx) hx]
    nlinarith
  have hcl : 0.99617 < cos (π / 36) := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [eq_div_iff hcpos.ne']
    constructor
    · intro h
      have : (v₀ * cos (π / 36)) ^ 2 = 1696 := by nlinarith
      have h' : v₀ * cos (π / 36) = √1696 := by
        have := (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp (this.trans (Real.sq_sqrt (by norm_num)).symm)
        exact this
      exact h'
    · intro h
      have h' : (v₀ * cos (π / 36)) ^ 2 = 1696 := by rw [h]; exact Real.sq_sqrt (by norm_num)
      nlinarith
  · rw [lt_div_iff₀ hcpos]; nlinarith
  · rw [div_lt_iff₀ hcpos]; nlinarith

/-- Stitz-Zeager Exercise 11.10.46: for a vertical launch (`θ = π/2`) with `g = 9.8`, `x(t) = 0` and
`y(t) = -4.9 t² + v₀ t + s₀`. -/
@[kb "stitzzeager2013" "Exercise 11.10.46, p. 1074"]
theorem exer_11_10_46 (v₀ s₀ t : ℝ) :
    v₀ * cos (π / 2) * t = 0 ∧ -(9.8 / 2) * t ^ 2 + v₀ * sin (π / 2) * t + s₀ = -4.9 * t ^ 2 + v₀ * t + s₀ := by
  rw [cos_pi_div_two, sin_pi_div_two]
  constructor <;> ring

/-- Stitz-Zeager Exercise 11.10.49: `x = cosh t`, `y = sinh t` parametrize exactly the right half of the
hyperbola `x² - y² = 1`. -/
@[kb "stitzzeager2013" "Exercise 11.10.49, p. 1074"]
theorem exer_11_10_49 :
    {p : ℝ × ℝ | ∃ t : ℝ, p = (cosh t, sinh t)} = {p | p.1 ^ 2 - p.2 ^ 2 = 1 ∧ 0 < p.1} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨t, rfl, rfl⟩
    exact ⟨by rw [cosh_sq]; ring, cosh_pos t⟩
  · rintro ⟨h1, h2⟩
    refine ⟨arsinh y, ?_, (sinh_arsinh y).symm⟩
    rw [cosh_arsinh]
    have : x ^ 2 = 1 + y ^ 2 := by linarith
    rw [← this, Real.sqrt_sq h2.le]

end UndergradKB.Precalculus.Course
