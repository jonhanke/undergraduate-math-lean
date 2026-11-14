import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Convex.Segment
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.PolarComplex

/-! # Course layer, Chapter 11 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 11.10

For each parametrization the curve traced is described by an equation in `x` and `y` together with the
range of the coordinates (the orientation is the direction of increasing `t`). -/

namespace UndergradKB.Precalculus.Course

open Real Set

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-! ## Helpers -/

private theorem w10_circ {u v : ℝ} (h : u ^ 2 + v ^ 2 = 1) :
    ∃ t ∈ Ico 0 (2 * π), cos t = u ∧ sin t = v := by
  set z : ℂ := ⟨u, v⟩ with hz
  have hn : ‖z‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_mk]
    rw [show u * u + v * v = 1 by nlinarith]; simp
  have h1 := Complex.norm_mul_cos_arg z
  have h2 := Complex.norm_mul_sin_arg z
  rw [hn, one_mul] at h1 h2
  have hc : cos (Complex.arg z) = u := h1
  have hs : sin (Complex.arg z) = v := h2
  have hp := pi_pos
  have a1 := Complex.arg_le_pi z
  have a2 := Complex.neg_pi_lt_arg z
  by_cases h0 : 0 ≤ Complex.arg z
  · exact ⟨Complex.arg z, ⟨h0, by linarith⟩, hc, hs⟩
  · refine ⟨Complex.arg z + 2 * π, ⟨by linarith, by linarith⟩, ?_, ?_⟩
    · rw [cos_add_two_pi, hc]
    · rw [sin_add_two_pi, hs]

/-! ## Section 11.10: eliminating the parameter -/

/-- Stitz-Zeager Exercise 11.10.1: `x = 4t - 3`, `y = 6t - 2`, `0 ≤ t ≤ 1` traces the segment
`y = (3/2) x + 5/2`, `-3 ≤ x ≤ 1`, from `(-3, -2)` to `(1, 4)`. -/
@[kb "stitzzeager2013" "Exercise 11.10.1, p. 1071"]
theorem exer_11_10_1 :
    {p : ℝ × ℝ | ∃ t ∈ Icc (0 : ℝ) 1, p = (4 * t - 3, 6 * t - 2)} =
      {p | p.2 = 3 / 2 * p.1 + 5 / 2 ∧ p.1 ∈ Icc (-3 : ℝ) 1} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, Prod.mk.injEq, mem_Icc]
  constructor
  · rintro ⟨t, ⟨h0, h4⟩, rfl, rfl⟩
    refine ⟨by ring, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(x + 3) / 4, ⟨by linarith, by linarith⟩, by ring, by rw [h1]; ring⟩

/-- Stitz-Zeager Exercise 11.10.2: `x = 4t - 1`, `y = 3 - 4t`, `0 ≤ t ≤ 1` traces the segment `y = 2 - x`,
`-1 ≤ x ≤ 3`, from `(-1, 3)` to `(3, -1)`. -/
@[kb "stitzzeager2013" "Exercise 11.10.2, p. 1071"]
theorem exer_11_10_2 :
    {p : ℝ × ℝ | ∃ t ∈ Icc (0 : ℝ) 1, p = (4 * t - 1, 3 - 4 * t)} =
      {p | p.2 = 2 - p.1 ∧ p.1 ∈ Icc (-1 : ℝ) 3} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, Prod.mk.injEq, mem_Icc]
  constructor
  · rintro ⟨t, ⟨h0, h4⟩, rfl, rfl⟩
    refine ⟨by ring, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(x + 1) / 4, ⟨by linarith, by linarith⟩, by ring, by rw [h1]; ring⟩

/-- Stitz-Zeager Exercise 11.10.3: `x = 2t`, `y = t²`, `-1 ≤ t ≤ 2` traces the parabola arc `y = x²/4`,
`-2 ≤ x ≤ 4`. -/
@[kb "stitzzeager2013" "Exercise 11.10.3, p. 1071"]
theorem exer_11_10_3 :
    {p : ℝ × ℝ | ∃ t ∈ Icc (-1 : ℝ) 2, p = (2 * t, t ^ 2)} =
      {p | p.2 = p.1 ^ 2 / 4 ∧ p.1 ∈ Icc (-2 : ℝ) 4} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, Prod.mk.injEq, mem_Icc]
  constructor
  · rintro ⟨t, ⟨h0, h4⟩, rfl, rfl⟩
    refine ⟨by ring, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨x / 2, ⟨by linarith, by linarith⟩, by ring, by rw [h1]; ring⟩

/-- Stitz-Zeager Exercise 11.10.4: `x = t - 1`, `y = 3 + 2t - t²`, `0 ≤ t ≤ 3` traces the parabola arc
`y = 4 - x²`, `-1 ≤ x ≤ 2`. -/
@[kb "stitzzeager2013" "Exercise 11.10.4, p. 1071"]
theorem exer_11_10_4 :
    {p : ℝ × ℝ | ∃ t ∈ Icc (0 : ℝ) 3, p = (t - 1, 3 + 2 * t - t ^ 2)} =
      {p | p.2 = 4 - p.1 ^ 2 ∧ p.1 ∈ Icc (-1 : ℝ) 2} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, Prod.mk.injEq, mem_Icc]
  constructor
  · rintro ⟨t, ⟨h0, h4⟩, rfl, rfl⟩
    refine ⟨by ring, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨x + 1, ⟨by linarith, by linarith⟩, by ring, by rw [h1]; ring⟩

/-- Stitz-Zeager Exercise 11.10.5: `x = t² + 2t + 1`, `y = t + 1`, `t ≤ 1` traces the half parabola `x = y²`,
`y ≤ 2`. -/
@[kb "stitzzeager2013" "Exercise 11.10.5, p. 1071"]
theorem exer_11_10_5 :
    {p : ℝ × ℝ | ∃ t ∈ Iic (1 : ℝ), p = (t ^ 2 + 2 * t + 1, t + 1)} =
      {p | p.1 = p.2 ^ 2 ∧ p.2 ≤ 2} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, Prod.mk.injEq, mem_Iic]
  constructor
  · rintro ⟨t, h0, rfl, rfl⟩
    exact ⟨by ring, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨y - 1, by linarith, by rw [h1]; ring, by ring⟩

/-- Stitz-Zeager Exercise 11.10.6: `x = (18 - t²)/9`, `y = t/3`, `t ≥ -3` traces the half parabola
`x = 2 - y²`, `y ≥ -1`. -/
@[kb "stitzzeager2013" "Exercise 11.10.6, p. 1071"]
theorem exer_11_10_6 :
    {p : ℝ × ℝ | ∃ t ∈ Ici (-3 : ℝ), p = ((18 - t ^ 2) / 9, t / 3)} =
      {p | p.1 = 2 - p.2 ^ 2 ∧ -1 ≤ p.2} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, Prod.mk.injEq, mem_Ici]
  constructor
  · rintro ⟨t, h0, rfl, rfl⟩
    exact ⟨by ring, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨3 * y, by linarith, by rw [h1]; ring, by ring⟩

/-- Stitz-Zeager Exercise 11.10.7: `x = t`, `y = t³` traces the cubic `y = x³`. -/
@[kb "stitzzeager2013" "Exercise 11.10.7, p. 1071"]
theorem exer_11_10_7 :
    {p : ℝ × ℝ | ∃ t : ℝ, p = (t, t ^ 3)} = {p | p.2 = p.1 ^ 3} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨t, rfl, rfl⟩; rfl
  · intro h; exact ⟨x, rfl, h⟩

/-- Stitz-Zeager Exercise 11.10.8: `x = t³`, `y = t` traces the curve `x = y³`. -/
@[kb "stitzzeager2013" "Exercise 11.10.8, p. 1071"]
theorem exer_11_10_8 :
    {p : ℝ × ℝ | ∃ t : ℝ, p = (t ^ 3, t)} = {p | p.1 = p.2 ^ 3} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨t, rfl, rfl⟩; rfl
  · intro h; exact ⟨y, h, rfl⟩

/-- Stitz-Zeager Exercise 11.10.9: `x = cos t`, `y = sin t`, `-π/2 ≤ t ≤ π/2` traces the right half of the unit
circle `x² + y² = 1`, `x ≥ 0`. -/
@[kb "stitzzeager2013" "Exercise 11.10.9, p. 1071"]
theorem exer_11_10_9 :
    {p : ℝ × ℝ | ∃ t ∈ Icc (-(π / 2)) (π / 2), p = (cos t, sin t)} =
      {p | p.1 ^ 2 + p.2 ^ 2 = 1 ∧ 0 ≤ p.1} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, Prod.mk.injEq, mem_Icc]
  constructor
  · rintro ⟨t, ⟨h0, h4⟩, rfl, rfl⟩
    exact ⟨by linarith [sin_sq_add_cos_sq t], cos_nonneg_of_neg_pi_div_two_le_of_le h0 h4⟩
  · rintro ⟨h1, h2⟩
    have hy1 : -1 ≤ y := by nlinarith
    have hy2 : y ≤ 1 := by nlinarith
    refine ⟨arcsin y, ⟨neg_pi_div_two_le_arcsin y, arcsin_le_pi_div_two y⟩, ?_, (sin_arcsin hy1 hy2).symm⟩
    rw [cos_arcsin]
    exact ((Real.sqrt_eq_iff_mul_self_eq (by nlinarith) h2).mpr (by nlinarith)).symm

/-- Stitz-Zeager Exercise 11.10.10: `x = 3 cos t`, `y = 3 sin t`, `0 ≤ t ≤ π` traces the upper half of the
circle `x² + y² = 9`. -/
@[kb "stitzzeager2013" "Exercise 11.10.10, p. 1071"]
theorem exer_11_10_10 :
    {p : ℝ × ℝ | ∃ t ∈ Icc (0 : ℝ) π, p = (3 * cos t, 3 * sin t)} =
      {p | p.1 ^ 2 + p.2 ^ 2 = 9 ∧ 0 ≤ p.2} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, Prod.mk.injEq, mem_Icc]
  constructor
  · rintro ⟨t, ⟨h0, h4⟩, rfl, rfl⟩
    exact ⟨by nlinarith [sin_sq_add_cos_sq t], by linarith [sin_nonneg_of_nonneg_of_le_pi h0 h4]⟩
  · rintro ⟨h1, h2⟩
    have hx1 : -1 ≤ x / 3 := by nlinarith
    have hx2 : x / 3 ≤ 1 := by nlinarith
    refine ⟨arccos (x / 3), ⟨arccos_nonneg _, arccos_le_pi _⟩, by rw [cos_arccos hx1 hx2]; ring, ?_⟩
    rw [sin_arccos]
    have : 1 - (x / 3) ^ 2 = (y / 3) ^ 2 := by nlinarith
    rw [this, Real.sqrt_sq (by linarith)]
    ring

/-- Stitz-Zeager Exercise 11.10.11: `x = -1 + 3 cos t`, `y = 4 sin t`, `0 ≤ t ≤ 2π` traces the ellipse
`(x + 1)²/9 + y²/16 = 1`. -/
@[kb "stitzzeager2013" "Exercise 11.10.11, p. 1071"]
theorem exer_11_10_11 :
    {p : ℝ × ℝ | ∃ t ∈ Icc (0 : ℝ) (2 * π), p = (-1 + 3 * cos t, 4 * sin t)} =
      {p | (p.1 + 1) ^ 2 / 9 + p.2 ^ 2 / 16 = 1} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, Prod.mk.injEq, mem_Icc]
  constructor
  · rintro ⟨t, ⟨h0, h4⟩, rfl, rfl⟩
    nlinarith [sin_sq_add_cos_sq t]
  · intro h
    obtain ⟨t, ⟨h0, h1⟩, hc, hs⟩ := w10_circ (u := (x + 1) / 3) (v := y / 4) (by nlinarith)
    exact ⟨t, ⟨h0, h1.le⟩, by rw [hc]; ring, by rw [hs]; ring⟩

/-- Stitz-Zeager Exercise 11.10.13: `x = 2 cos t`, `y = sec t`, `0 ≤ t < π/2` traces the branch `x y = 2`,
`0 < x ≤ 2`. -/
@[kb "stitzzeager2013" "Exercise 11.10.13, p. 1071"]
theorem exer_11_10_13 :
    {p : ℝ × ℝ | ∃ t ∈ Ico (0 : ℝ) (π / 2), p = (2 * cos t, (cos t)⁻¹)} =
      {p | p.1 * p.2 = 2 ∧ 0 < p.1 ∧ p.1 ≤ 2} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, Prod.mk.injEq, mem_Ico]
  constructor
  · rintro ⟨t, ⟨h0, h4⟩, rfl, rfl⟩
    have hc : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], h4⟩
    refine ⟨by field_simp, by linarith, by linarith [cos_le_one t]⟩
  · rintro ⟨h1, h2, h3⟩
    have hy : y = 2 / x := by field_simp; linarith
    have hx1 : -1 ≤ x / 2 := by linarith
    have hx2 : x / 2 ≤ 1 := by linarith
    have hc : cos (arccos (x / 2)) = x / 2 := cos_arccos hx1 hx2
    refine ⟨arccos (x / 2), ⟨arccos_nonneg _, arccos_lt_pi_div_two.mpr (by linarith)⟩, ?_, ?_⟩
    · rw [hc]; ring
    · rw [hc, hy]; field_simp

/-- Stitz-Zeager Exercise 11.10.14: `x = 2 tan t`, `y = cot t`, `0 < t < π/2` traces the branch `x y = 2`,
`x > 0`. -/
@[kb "stitzzeager2013" "Exercise 11.10.14, p. 1071"]
theorem exer_11_10_14 :
    {p : ℝ × ℝ | ∃ t ∈ Ioo (0 : ℝ) (π / 2), p = (2 * tan t, (tan t)⁻¹)} =
      {p | p.1 * p.2 = 2 ∧ 0 < p.1} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, Prod.mk.injEq, mem_Ioo]
  constructor
  · rintro ⟨t, ⟨h0, h4⟩, rfl, rfl⟩
    have ht : 0 < tan t := tan_pos_of_pos_of_lt_pi_div_two h0 h4
    exact ⟨by field_simp, by linarith⟩
  · rintro ⟨h1, h2⟩
    have hy : y = 2 / x := by field_simp; linarith
    have hp : 0 < arctan (x / 2) := arctan_pos.2 (by linarith)
    refine ⟨arctan (x / 2), ⟨hp, arctan_lt_pi_div_two _⟩, ?_, ?_⟩
    · rw [tan_arctan]; ring
    · rw [tan_arctan, hy]; field_simp

/-- Stitz-Zeager Exercise 11.10.15: `x = sec t`, `y = tan t`, `-π/2 < t < π/2` traces the right branch of
the hyperbola `x² - y² = 1`, `x > 0`. -/
@[kb "stitzzeager2013" "Exercise 11.10.15, p. 1071"]
theorem exer_11_10_15 :
    {p : ℝ × ℝ | ∃ t ∈ Ioo (-(π / 2)) (π / 2), p = ((cos t)⁻¹, tan t)} =
      {p | p.1 ^ 2 - p.2 ^ 2 = 1 ∧ 0 < p.1} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, Prod.mk.injEq, mem_Ioo]
  constructor
  · rintro ⟨t, ⟨h0, h4⟩, rfl, rfl⟩
    have hc : 0 < cos t := cos_pos_of_mem_Ioo ⟨h0, h4⟩
    have := sin_sq_add_cos_sq t
    refine ⟨?_, by positivity⟩
    rw [tan_eq_sin_div_cos]
    field_simp
    linarith
  · rintro ⟨h1, h2⟩
    have hs : √(1 + y ^ 2) = x := by
      rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) h2.le]; nlinarith
    refine ⟨arctan y, ⟨neg_pi_div_two_lt_arctan y, arctan_lt_pi_div_two y⟩, ?_, (tan_arctan y).symm⟩
    rw [cos_arctan, hs]; field_simp

/-- Stitz-Zeager Exercise 11.10.16: `x = sec t`, `y = tan t`, `π/2 < t < 3π/2` traces the left branch of the
hyperbola `x² - y² = 1`, `x < 0`. -/
@[kb "stitzzeager2013" "Exercise 11.10.16, p. 1071"]
theorem exer_11_10_16 :
    {p : ℝ × ℝ | ∃ t ∈ Ioo (π / 2) (3 * π / 2), p = ((cos t)⁻¹, tan t)} =
      {p | p.1 ^ 2 - p.2 ^ 2 = 1 ∧ p.1 < 0} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, Prod.mk.injEq, mem_Ioo]
  constructor
  · rintro ⟨t, ⟨h0, h4⟩, rfl, rfl⟩
    have hc : cos t < 0 := by
      have e : cos t = -cos (t - π) := by rw [cos_sub_pi]; ring
      have : 0 < cos (t - π) := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
      linarith
    have hc' : cos t ≠ 0 := hc.ne
    have := sin_sq_add_cos_sq t
    refine ⟨?_, inv_lt_zero.mpr hc⟩
    rw [tan_eq_sin_div_cos]
    field_simp
    linarith
  · rintro ⟨h1, h2⟩
    have hs : √(1 + y ^ 2) = -x := by
      rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by linarith)]; nlinarith
    have ha := neg_pi_div_two_lt_arctan y
    have hb := arctan_lt_pi_div_two y
    refine ⟨π + arctan y, ⟨by linarith, by linarith⟩, ?_, ?_⟩
    · rw [add_comm π, cos_add_pi, cos_arctan, hs]; field_simp
    · rw [add_comm π, tan_add_pi, tan_arctan]

/-- Stitz-Zeager Exercise 11.10.17: `x = tan t`, `y = 2 sec t`, `-π/2 < t < π/2` traces the upper branch of
`y²/4 - x² = 1`, `y > 0`. -/
@[kb "stitzzeager2013" "Exercise 11.10.17, p. 1071"]
theorem exer_11_10_17 :
    {p : ℝ × ℝ | ∃ t ∈ Ioo (-(π / 2)) (π / 2), p = (tan t, 2 * (cos t)⁻¹)} =
      {p | p.2 ^ 2 / 4 - p.1 ^ 2 = 1 ∧ 0 < p.2} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, Prod.mk.injEq, mem_Ioo]
  constructor
  · rintro ⟨t, ⟨h0, h4⟩, rfl, rfl⟩
    have hc : 0 < cos t := cos_pos_of_mem_Ioo ⟨h0, h4⟩
    have := sin_sq_add_cos_sq t
    refine ⟨?_, by positivity⟩
    rw [tan_eq_sin_div_cos]
    field_simp
    linarith
  · rintro ⟨h1, h2⟩
    have hs : √(1 + x ^ 2) = y / 2 := by
      rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by linarith)]; nlinarith
    refine ⟨arctan x, ⟨neg_pi_div_two_lt_arctan x, arctan_lt_pi_div_two x⟩, (tan_arctan x).symm, ?_⟩
    rw [cos_arctan, hs]; field_simp

/-- Stitz-Zeager Exercise 11.10.18: `x = tan t`, `y = 2 sec t`, `π/2 < t < 3π/2` traces the lower branch of
`y²/4 - x² = 1`, `y < 0`. -/
@[kb "stitzzeager2013" "Exercise 11.10.18, p. 1071"]
theorem exer_11_10_18 :
    {p : ℝ × ℝ | ∃ t ∈ Ioo (π / 2) (3 * π / 2), p = (tan t, 2 * (cos t)⁻¹)} =
      {p | p.2 ^ 2 / 4 - p.1 ^ 2 = 1 ∧ p.2 < 0} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, Prod.mk.injEq, mem_Ioo]
  constructor
  · rintro ⟨t, ⟨h0, h4⟩, rfl, rfl⟩
    have hc : cos t < 0 := by
      have e : cos t = -cos (t - π) := by rw [cos_sub_pi]; ring
      have : 0 < cos (t - π) := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
      linarith
    have hc' : cos t ≠ 0 := hc.ne
    have := sin_sq_add_cos_sq t
    refine ⟨?_, by have := inv_lt_zero.mpr hc; linarith⟩
    rw [tan_eq_sin_div_cos]
    field_simp
    linarith
  · rintro ⟨h1, h2⟩
    have hs : √(1 + x ^ 2) = -(y / 2) := by
      rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by linarith)]; nlinarith
    have ha := neg_pi_div_two_lt_arctan x
    have hb := arctan_lt_pi_div_two x
    refine ⟨π + arctan x, ⟨by linarith, by linarith⟩, ?_, ?_⟩
    · rw [add_comm π, tan_add_pi, tan_arctan]
    · rw [add_comm π, cos_add_pi, cos_arctan, hs]; field_simp

/-- Stitz-Zeager Exercise 11.10.19: `x = cos t`, `y = t`, `0 ≤ t ≤ π` traces the curve `x = cos y`,
`0 ≤ y ≤ π`. -/
@[kb "stitzzeager2013" "Exercise 11.10.19, p. 1071"]
theorem exer_11_10_19 :
    {p : ℝ × ℝ | ∃ t ∈ Icc (0 : ℝ) π, p = (cos t, t)} = {p | p.1 = cos p.2 ∧ p.2 ∈ Icc (0 : ℝ) π} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨t, ht, rfl, rfl⟩; exact ⟨rfl, ht⟩
  · rintro ⟨h1, h2⟩; exact ⟨y, h2, h1, rfl⟩

/-- Stitz-Zeager Exercise 11.10.20: `x = sin t`, `y = t`, `-π/2 ≤ t ≤ π/2` traces the curve `x = sin y`,
`-π/2 ≤ y ≤ π/2`. -/
@[kb "stitzzeager2013" "Exercise 11.10.20, p. 1071"]
theorem exer_11_10_20 :
    {p : ℝ × ℝ | ∃ t ∈ Icc (-(π / 2)) (π / 2), p = (sin t, t)} =
      {p | p.1 = sin p.2 ∧ p.2 ∈ Icc (-(π / 2)) (π / 2)} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨t, ht, rfl, rfl⟩; exact ⟨rfl, ht⟩
  · rintro ⟨h1, h2⟩; exact ⟨y, h2, h1, rfl⟩

/-! ## Section 11.10: parametrizations of oriented curves and further exercises -/

/-- Stitz-Zeager Exercise 11.10.26: the directed segment from `(-2, -1)` to `(3, -4)` is parametrized by
`x = 5t - 2`, `y = -1 - 3t`, `0 ≤ t ≤ 1`. -/
@[kb "stitzzeager2013" "Exercise 11.10.26, p. 1072"]
theorem exer_11_10_26 :
    {p : ℝ × ℝ | ∃ t ∈ Icc (0 : ℝ) 1, p = (5 * t - 2, -1 - 3 * t)} =
      segment ℝ ((-2 : ℝ), (-1 : ℝ)) (3, -4) := by
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

/-- Stitz-Zeager Exercise 11.10.30: the curve `x = y² - 9` from `(0, 3)` to `(-5, -2)` is parametrized by
`x = t² - 6t`, `y = 3 - t`, `0 ≤ t ≤ 5` (`t = 0` is the point `(0, 3)`). -/
@[kb "stitzzeager2013" "Exercise 11.10.30, p. 1072"]
theorem exer_11_10_30 :
    {p : ℝ × ℝ | ∃ t ∈ Icc (0 : ℝ) 5, p = (t ^ 2 - 6 * t, 3 - t)} =
      {p | p.1 = p.2 ^ 2 - 9 ∧ p.2 ∈ Icc (-2 : ℝ) 3} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, Prod.mk.injEq, mem_Icc]
  constructor
  · rintro ⟨t, ⟨h0, h4⟩, rfl, rfl⟩
    refine ⟨by ring, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨3 - y, ⟨by linarith, by linarith⟩, by rw [h1]; ring, by ring⟩

/-- Stitz-Zeager Exercise 11.10.34: the circle `x² + y² - 6y = 0` traversed clockwise from `(0, 0)` is
`x = 3 cos t`, `y = 3 - 3 sin t`... (the points traced for `0 ≤ t < 2π` form exactly the circle). -/
@[kb "stitzzeager2013" "Exercise 11.10.34, p. 1072"]
theorem exer_11_10_34 :
    {p : ℝ × ℝ | ∃ t ∈ Ico (0 : ℝ) (2 * π), p = (3 * cos t, 3 - 3 * sin t)} =
      {p | p.1 ^ 2 + p.2 ^ 2 - 6 * p.2 = 0} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨t, ht, rfl, rfl⟩
    nlinarith [sin_sq_add_cos_sq t]
  · intro h
    obtain ⟨t, ht, hc, hs⟩ := w10_circ (u := x / 3) (v := (3 - y) / 3) (by nlinarith)
    exact ⟨t, ht, by rw [hc]; ring, by rw [hs]; ring⟩

/-- Stitz-Zeager Exercise 11.10.40: the curve `x = t³ + 3t - 4`, `y = t` is the graph of the inverse of
`f(x) = x³ + 3x - 4`, i.e. the reflection in the line `y = x` of the graph of `f`. -/
@[kb "stitzzeager2013" "Exercise 11.10.40, p. 1072"]
theorem exer_11_10_40 :
    {p : ℝ × ℝ | ∃ t : ℝ, p = (t ^ 3 + 3 * t - 4, t)} =
      {p | (p.2, p.1) ∈ {q : ℝ × ℝ | q.2 = q.1 ^ 3 + 3 * q.1 - 4}} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨t, rfl, rfl⟩; rfl
  · intro h; exact ⟨y, h, rfl⟩

/-- Stitz-Zeager Exercise 11.10.41: the polar curve `r = 6 cos 2θ` has the parametric equations
`x = 6 cos 2θ cos θ`, `y = 6 cos 2θ sin θ`. -/
@[kb "stitzzeager2013" "Exercise 11.10.41, p. 1072"]
theorem exer_11_10_41 :
    ∀ θ : ℝ, polarPoint (6 * cos (2 * θ)) θ = (6 * cos (2 * θ) * cos θ, 6 * cos (2 * θ) * sin θ) :=
  fun _ => rfl

/-- Stitz-Zeager Exercise 11.10.42: a passenger on the London Eye is at `x = 67.5 cos (πt/15 - π/2) =
67.5 sin (πt/15)`, `y = 67.5 sin (πt/15 - π/2) + 67.5 = 67.5 - 67.5 cos (πt/15)`. -/
@[kb "stitzzeager2013" "Exercise 11.10.42, p. 1072"]
theorem exer_11_10_42 (t : ℝ) :
    67.5 * cos (π / 15 * t - π / 2) = 67.5 * sin (π / 15 * t) ∧
      67.5 * sin (π / 15 * t - π / 2) + 67.5 = 67.5 - 67.5 * cos (π / 15 * t) := by
  rw [cos_sub_pi_div_two, sin_sub_pi_div_two]
  constructor <;> ring

/-- Stitz-Zeager Exercise 11.10.47: `cosh t = (eᵗ + e⁻ᵗ)/2` has domain all of `ℝ` and range `[1, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 11.10.47, p. 1074"]
theorem exer_11_10_47 :
    Set.range (fun t : ℝ => (Real.exp t + Real.exp (-t)) / 2) = Ici 1 := by
  ext y
  simp only [Set.mem_range, mem_Ici]
  constructor
  · rintro ⟨t, rfl⟩
    have h1 : 0 < Real.exp t := Real.exp_pos t
    have h2 : 0 < Real.exp (-t) := Real.exp_pos (-t)
    have h3 : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [sq_nonneg (Real.exp t - Real.exp (-t))]
  · intro hy
    have hs := Real.sq_sqrt (show 0 ≤ y ^ 2 - 1 by nlinarith)
    have hs0 := Real.sqrt_nonneg (y ^ 2 - 1)
    have hpos : 0 < y + √(y ^ 2 - 1) := by linarith
    refine ⟨Real.log (y + √(y ^ 2 - 1)), ?_⟩
    rw [Real.exp_neg, Real.exp_log hpos]
    have : (y + √(y ^ 2 - 1))⁻¹ = y - √(y ^ 2 - 1) := by
      exact inv_eq_of_mul_eq_one_right (by nlinarith)
    rw [this]; ring

/-- Stitz-Zeager Exercise 11.10.48: `sinh t = (eᵗ - e⁻ᵗ)/2` has domain and range all of `ℝ`. -/
@[kb "stitzzeager2013" "Exercise 11.10.48, p. 1074"]
theorem exer_11_10_48 :
    Set.range (fun t : ℝ => (Real.exp t - Real.exp (-t)) / 2) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  obtain ⟨t, ht⟩ := Real.sinh_surjective y
  exact ⟨t, by rw [← ht, Real.sinh_eq]⟩

/-- Stitz-Zeager Exercise 11.10.50: `cosh t = cos (i t)` and `sinh t = -i sin (i t)`; compare with
`cos t = (e^{it} + e^{-it})/2`, `sin t = (e^{it} - e^{-it})/(2i)`. -/
@[kb "stitzzeager2013" "Exercise 11.10.50, p. 1074"]
theorem exer_11_10_50 (t : ℂ) :
    (Complex.exp t + Complex.exp (-t)) / 2 = Complex.cos (t * Complex.I) ∧
      (Complex.exp t - Complex.exp (-t)) / 2 * Complex.I = Complex.sin (t * Complex.I) := by
  rw [Complex.cos_mul_I, Complex.sin_mul_I, Complex.cosh, Complex.sinh]
  constructor
  · rfl
  · rfl

/-- Stitz-Zeager Exercise 11.10.51: `sech t = 1/cosh t = 2/(eᵗ + e⁻ᵗ)`, `csch t = 2/(eᵗ - e⁻ᵗ)`,
`tanh t = (eᵗ - e⁻ᵗ)/(eᵗ + e⁻ᵗ)` and `coth t = (eᵗ + e⁻ᵗ)/(eᵗ - e⁻ᵗ)` (with `x / 0 = 0` conventions at the poles). -/
@[kb "stitzzeager2013" "Exercise 11.10.51, p. 1074"]
theorem exer_11_10_51 (t : ℝ) :
    1 / ((Real.exp t + Real.exp (-t)) / 2) = 2 / (Real.exp t + Real.exp (-t)) ∧
      1 / ((Real.exp t - Real.exp (-t)) / 2) = 2 / (Real.exp t - Real.exp (-t)) ∧
      (Real.exp t - Real.exp (-t)) / 2 / ((Real.exp t + Real.exp (-t)) / 2) =
        (Real.exp t - Real.exp (-t)) / (Real.exp t + Real.exp (-t)) ∧
      (Real.exp t + Real.exp (-t)) / 2 / ((Real.exp t - Real.exp (-t)) / 2) =
        (Real.exp t + Real.exp (-t)) / (Real.exp t - Real.exp (-t)) := by
  refine ⟨by field_simp, by field_simp, ?_, ?_⟩
  · have : 0 < Real.exp t + Real.exp (-t) := by positivity
    field_simp
  · rw [div_div_div_cancel_right₀ (by norm_num)]

end UndergradKB.Precalculus.Course
