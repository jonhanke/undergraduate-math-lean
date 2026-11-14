import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 11 (Stitz-Zeager): exercises with the book's answers (wave 8), Section 11.5 -/

namespace UndergradKB.Precalculus.Course

open Real

/-! ## Roses (Exercises 3-8): size and the labelled zero directions -/

/-- Stitz-Zeager Exercise 11.5.3: the rose `r = 2 sin 2θ` has `|r| ≤ 2`, tip value `2` at `θ = π/4`, and
passes through the pole at `θ = 0` and `θ = π/2`. -/
@[kb "stitzzeager2013" "Exercise 11.5.3, p. 970"]
theorem exer_11_5_3 : (∀ θ : ℝ, |2 * sin (2 * θ)| ≤ 2) ∧ 2 * sin (2 * (π / 4)) = 2 ∧
    2 * sin (2 * 0) = 0 ∧ 2 * sin (2 * (π / 2)) = 0 := by
  refine ⟨fun θ => ?_, ?_, by simp, ?_⟩
  · have := abs_sin_le_one (2 * θ)
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  · rw [show 2 * (π / 4) = π / 2 by ring, Real.sin_pi_div_two]; norm_num
  · rw [show 2 * (π / 2) = π by ring, Real.sin_pi]; norm_num

/-- Stitz-Zeager Exercise 11.5.4: the rose `r = 4 cos 2θ` has `|r| ≤ 4`, tip value `4` at `θ = 0`, and
passes through the pole at `θ = π/4` and `θ = 3π/4`. -/
@[kb "stitzzeager2013" "Exercise 11.5.4, p. 970"]
theorem exer_11_5_4 : (∀ θ : ℝ, |4 * cos (2 * θ)| ≤ 4) ∧ 4 * cos (2 * 0) = 4 ∧
    4 * cos (2 * (π / 4)) = 0 ∧ 4 * cos (2 * (3 * π / 4)) = 0 := by
  refine ⟨fun θ => ?_, by simp, ?_, ?_⟩
  · have := abs_cos_le_one (2 * θ)
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    linarith
  · rw [show 2 * (π / 4) = π / 2 by ring, Real.cos_pi_div_two]; norm_num
  · rw [show 2 * (3 * π / 4) = π / 2 + π by ring, Real.cos_add_pi, Real.cos_pi_div_two]; norm_num

/-- Stitz-Zeager Exercise 11.5.5: the rose `r = 5 sin 3θ` has `|r| ≤ 5`, tip value `5` at `θ = π/6`, and
passes through the pole at `θ = π/3` and `θ = 2π/3`. -/
@[kb "stitzzeager2013" "Exercise 11.5.5, p. 970"]
theorem exer_11_5_5 : (∀ θ : ℝ, |5 * sin (3 * θ)| ≤ 5) ∧ 5 * sin (3 * (π / 6)) = 5 ∧
    5 * sin (3 * (π / 3)) = 0 ∧ 5 * sin (3 * (2 * π / 3)) = 0 := by
  refine ⟨fun θ => ?_, ?_, ?_, ?_⟩
  · have := abs_sin_le_one (3 * θ)
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5)]
    linarith
  · rw [show 3 * (π / 6) = π / 2 by ring, Real.sin_pi_div_two]; norm_num
  · rw [show 3 * (π / 3) = π by ring, Real.sin_pi]; norm_num
  · rw [show 3 * (2 * π / 3) = 2 * π by ring, Real.sin_two_pi]; norm_num

/-- Stitz-Zeager Exercise 11.5.6: the rose `r = cos 5θ` has `|r| ≤ 1`, tip value `1` at `θ = 0`, and
passes through the pole at `θ = π/10` and `θ = 3π/10`. -/
@[kb "stitzzeager2013" "Exercise 11.5.6, p. 970"]
theorem exer_11_5_6 : (∀ θ : ℝ, |cos (5 * θ)| ≤ 1) ∧ cos (5 * 0) = 1 ∧
    cos (5 * (π / 10)) = 0 ∧ cos (5 * (3 * π / 10)) = 0 := by
  refine ⟨fun θ => abs_cos_le_one _, by simp, ?_, ?_⟩
  · rw [show 5 * (π / 10) = π / 2 by ring, Real.cos_pi_div_two]
  · rw [show 5 * (3 * π / 10) = π / 2 + π by ring, Real.cos_add_pi, Real.cos_pi_div_two]; norm_num

/-- Stitz-Zeager Exercise 11.5.7: the rose `r = sin 4θ` has `|r| ≤ 1`, tip value `1` at `θ = π/8`, and
passes through the pole at `θ = π/4` and `θ = 3π/4`. -/
@[kb "stitzzeager2013" "Exercise 11.5.7, p. 970"]
theorem exer_11_5_7 : (∀ θ : ℝ, |sin (4 * θ)| ≤ 1) ∧ sin (4 * (π / 8)) = 1 ∧
    sin (4 * (π / 4)) = 0 ∧ sin (4 * (3 * π / 4)) = 0 := by
  refine ⟨fun θ => abs_sin_le_one _, ?_, ?_, ?_⟩
  · rw [show 4 * (π / 8) = π / 2 by ring, Real.sin_pi_div_two]
  · rw [show 4 * (π / 4) = π by ring, Real.sin_pi]
  · rw [show 4 * (3 * π / 4) = π + 2 * π by ring, Real.sin_add_two_pi, Real.sin_pi]

/-- Stitz-Zeager Exercise 11.5.8: the rose `r = 3 cos 4θ` has `|r| ≤ 3`, tip value `3` at `θ = 0`, and
passes through the pole at `θ = π/8` and `θ = 3π/8`. -/
@[kb "stitzzeager2013" "Exercise 11.5.8, p. 970"]
theorem exer_11_5_8 : (∀ θ : ℝ, |3 * cos (4 * θ)| ≤ 3) ∧ 3 * cos (4 * 0) = 3 ∧
    3 * cos (4 * (π / 8)) = 0 ∧ 3 * cos (4 * (3 * π / 8)) = 0 := by
  refine ⟨fun θ => ?_, by simp, ?_, ?_⟩
  · have := abs_cos_le_one (4 * θ)
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    linarith
  · rw [show 4 * (π / 8) = π / 2 by ring, Real.cos_pi_div_two]; norm_num
  · rw [show 4 * (3 * π / 8) = π / 2 + π by ring, Real.cos_add_pi, Real.cos_pi_div_two]; norm_num

/-! ## Symmetry of polar graphs (Exercises 62-64) -/

/-- The set of rectangular points on the graph of `r = f θ`. -/
def ch11e3bGraph (f : ℝ → ℝ) : Set (ℝ × ℝ) := {p | ∃ θ : ℝ, p = (f θ * cos θ, f θ * sin θ)}

/-- Stitz-Zeager Exercise 11.5.62: if `f` is even, the graph of `r = f θ` is symmetric about the
`x`-axis. -/
@[kb "stitzzeager2013" "Exercise 11.5.62, p. 973"]
theorem exer_11_5_62_w8 (f : ℝ → ℝ) (hf : ∀ θ, f (-θ) = f θ) :
    ∀ x y : ℝ, (x, y) ∈ ch11e3bGraph f → (x, -y) ∈ ch11e3bGraph f := by
  rintro x y ⟨θ, h⟩
  refine ⟨-θ, ?_⟩
  simp only [Prod.mk.injEq] at h ⊢
  obtain ⟨rfl, rfl⟩ := h
  rw [hf θ, Real.cos_neg, Real.sin_neg]
  exact ⟨by ring, by ring⟩

/-- Stitz-Zeager Exercise 11.5.62(a): `f θ = 2 + 4 cos θ` is even and its graph is symmetric about the
`x`-axis. -/
@[kb "stitzzeager2013" "Exercise 11.5.62a, p. 973"]
theorem exer_11_5_62_w8_a : (∀ θ : ℝ, 2 + 4 * cos (-θ) = 2 + 4 * cos θ) ∧
    ∀ x y : ℝ, (x, y) ∈ ch11e3bGraph (fun θ => 2 + 4 * cos θ) →
      (x, -y) ∈ ch11e3bGraph (fun θ => 2 + 4 * cos θ) :=
  ⟨fun θ => by rw [Real.cos_neg],
   exer_11_5_62_w8 _ (fun θ => by simp only [Real.cos_neg])⟩

/-- Stitz-Zeager Exercise 11.5.62(b): `f θ = 3 sin 2θ` is not even, yet the graph of `r = 3 sin 2θ` is
symmetric about the `x`-axis. -/
@[kb "stitzzeager2013" "Exercise 11.5.62b, p. 973"]
theorem exer_11_5_62_w8_b : ¬ (∀ θ : ℝ, 3 * sin (2 * (-θ)) = 3 * sin (2 * θ)) ∧
    ∀ x y : ℝ, (x, y) ∈ ch11e3bGraph (fun θ => 3 * sin (2 * θ)) →
      (x, -y) ∈ ch11e3bGraph (fun θ => 3 * sin (2 * θ)) := by
  constructor
  · intro h
    have h1 := h (π / 4)
    rw [show 2 * (-(π / 4)) = -(π / 2) by ring, Real.sin_neg, Real.sin_pi_div_two,
      show 2 * (π / 4) = π / 2 by ring, Real.sin_pi_div_two] at h1
    norm_num at h1
  · rintro x y ⟨θ, h⟩
    refine ⟨π - θ, ?_⟩
    simp only [Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    have e : sin (2 * (π - θ)) = -sin (2 * θ) := by
      rw [show 2 * (π - θ) = 2 * π - 2 * θ by ring, Real.sin_two_pi_sub]
    rw [e, Real.cos_pi_sub, Real.sin_pi_sub]
    exact ⟨by ring, by ring⟩

/-- Stitz-Zeager Exercise 11.5.63 (corrected form): if `f` is odd, the graph of `r = f θ` is symmetric
about the `y`-axis (the point `(x, y)` goes to `(-x, y)` via `θ ↦ -θ`). -/
@[kb "stitzzeager2013" "Exercise 11.5.63, p. 973"]
theorem exer_11_5_63_w8 (f : ℝ → ℝ) (hf : ∀ θ, f (-θ) = -f θ) :
    ∀ x y : ℝ, (x, y) ∈ ch11e3bGraph f → (-x, y) ∈ ch11e3bGraph f := by
  rintro x y ⟨θ, h⟩
  refine ⟨-θ, ?_⟩
  simp only [Prod.mk.injEq] at h ⊢
  obtain ⟨rfl, rfl⟩ := h
  rw [hf θ, Real.cos_neg, Real.sin_neg]
  exact ⟨by ring, by ring⟩

/-- Stitz-Zeager Exercise 11.5.63(a): `f θ = 5 sin 2θ` is odd and its graph is symmetric about the
origin (via `θ ↦ θ + π`). -/
@[kb "stitzzeager2013" "Exercise 11.5.63a, p. 973"]
theorem exer_11_5_63_w8_a : (∀ θ : ℝ, 5 * sin (2 * (-θ)) = -(5 * sin (2 * θ))) ∧
    ∀ x y : ℝ, (x, y) ∈ ch11e3bGraph (fun θ => 5 * sin (2 * θ)) →
      (-x, -y) ∈ ch11e3bGraph (fun θ => 5 * sin (2 * θ)) := by
  constructor
  · intro θ
    rw [show 2 * (-θ) = -(2 * θ) by ring, Real.sin_neg]; ring
  · rintro x y ⟨θ, h⟩
    refine ⟨θ + π, ?_⟩
    simp only [Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    rw [show 2 * (θ + π) = 2 * θ + 2 * π by ring, Real.sin_add_two_pi, Real.cos_add_pi,
      Real.sin_add_pi]
    exact ⟨by ring, by ring⟩

/-- Stitz-Zeager Exercise 11.5.63(b): `f θ = 3 cos 2θ` is not odd, yet the graph of `r = 3 cos 2θ` is
symmetric about the origin (via `θ ↦ θ + π`). -/
@[kb "stitzzeager2013" "Exercise 11.5.63b, p. 973"]
theorem exer_11_5_63_w8_b : ¬ (∀ θ : ℝ, 3 * cos (2 * (-θ)) = -(3 * cos (2 * θ))) ∧
    ∀ x y : ℝ, (x, y) ∈ ch11e3bGraph (fun θ => 3 * cos (2 * θ)) →
      (-x, -y) ∈ ch11e3bGraph (fun θ => 3 * cos (2 * θ)) := by
  constructor
  · intro h
    have h1 := h 0
    norm_num at h1
  · rintro x y ⟨θ, h⟩
    refine ⟨θ + π, ?_⟩
    simp only [Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    rw [show 2 * (θ + π) = 2 * θ + 2 * π by ring, Real.cos_add_two_pi, Real.cos_add_pi,
      Real.sin_add_pi]
    exact ⟨by ring, by ring⟩

/-- Stitz-Zeager Exercise 11.5.64: if `f (π - θ) = f θ`, the graph of `r = f θ` is symmetric about the
`y`-axis. -/
@[kb "stitzzeager2013" "Exercise 11.5.64, p. 973"]
theorem exer_11_5_64_w8 (f : ℝ → ℝ) (hf : ∀ θ, f (π - θ) = f θ) :
    ∀ x y : ℝ, (x, y) ∈ ch11e3bGraph f → (-x, y) ∈ ch11e3bGraph f := by
  rintro x y ⟨θ, h⟩
  refine ⟨π - θ, ?_⟩
  simp only [Prod.mk.injEq] at h ⊢
  obtain ⟨rfl, rfl⟩ := h
  rw [hf θ, Real.cos_pi_sub, Real.sin_pi_sub]
  exact ⟨by ring, by ring⟩

/-- Stitz-Zeager Exercise 11.5.64(a): `f θ = 4 - 2 sin θ` satisfies `f (π - θ) = f θ` and its graph is
symmetric about the `y`-axis. -/
@[kb "stitzzeager2013" "Exercise 11.5.64a, p. 973"]
theorem exer_11_5_64_w8_a : (∀ θ : ℝ, 4 - 2 * sin (π - θ) = 4 - 2 * sin θ) ∧
    ∀ x y : ℝ, (x, y) ∈ ch11e3bGraph (fun θ => 4 - 2 * sin θ) →
      (-x, y) ∈ ch11e3bGraph (fun θ => 4 - 2 * sin θ) :=
  ⟨fun θ => by rw [Real.sin_pi_sub],
   exer_11_5_64_w8 _ (fun θ => by simp only [Real.sin_pi_sub])⟩

/-- Stitz-Zeager Exercise 11.5.64(b): for `f θ = 5 sin 2θ`, `f (π - π/4) ≠ f (π/4)`, yet the graph of
`r = 5 sin 2θ` is symmetric about the `y`-axis (it is odd). -/
@[kb "stitzzeager2013" "Exercise 11.5.64b, p. 973"]
theorem exer_11_5_64_w8_b : 5 * sin (2 * (π - π / 4)) ≠ 5 * sin (2 * (π / 4)) ∧
    ∀ x y : ℝ, (x, y) ∈ ch11e3bGraph (fun θ => 5 * sin (2 * θ)) →
      (-x, y) ∈ ch11e3bGraph (fun θ => 5 * sin (2 * θ)) := by
  constructor
  · rw [show 2 * (π - π / 4) = π / 2 + π by ring, Real.sin_add_pi, Real.sin_pi_div_two,
      show 2 * (π / 4) = π / 2 by ring, Real.sin_pi_div_two]
    norm_num
  · exact exer_11_5_63_w8 _ (fun θ => by
      simp only [mul_neg, Real.sin_neg])

/-! ## Regions (Exercises 41, 43, 48), as Cartesian set equalities -/

/-- Every point of the plane has polar coordinates `r ≥ 0`, `θ ∈ (-π, π]`. -/
theorem ch11e3b_polar (x y : ℝ) : ∃ r θ : ℝ, 0 ≤ r ∧ r ^ 2 = x ^ 2 + y ^ 2 ∧ -π < θ ∧ θ ≤ π ∧
    x = r * cos θ ∧ y = r * sin θ := by
  by_cases h : x = 0 ∧ y = 0
  · obtain ⟨hx, hy⟩ := h
    refine ⟨0, 0, le_refl _, by simp [hx, hy], by linarith [Real.pi_pos], by linarith [Real.pi_pos],
      by simp [hx], by simp [hy]⟩
  · have hz : (⟨x, y⟩ : ℂ) ≠ 0 := by
      intro h0
      apply h
      exact ⟨congrArg Complex.re h0, congrArg Complex.im h0⟩
    have hn : ‖(⟨x, y⟩ : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    refine ⟨‖(⟨x, y⟩ : ℂ)‖, Complex.arg ⟨x, y⟩, norm_nonneg _, ?_, Complex.neg_pi_lt_arg _,
      Complex.arg_le_pi _, ?_, ?_⟩
    · rw [Complex.sq_norm, Complex.normSq_apply]
      simp only
      ring
    · rw [Complex.cos_arg hz]
      show x = ‖(⟨x, y⟩ : ℂ)‖ * (x / ‖(⟨x, y⟩ : ℂ)‖)
      field_simp
    · rw [Complex.sin_arg]
      show y = ‖(⟨x, y⟩ : ℂ)‖ * (y / ‖(⟨x, y⟩ : ℂ)‖)
      field_simp

/-- Every point of the plane has polar coordinates `r ≥ 0`, `θ ∈ [0, 2π)`. -/
theorem ch11e3b_polar2 (x y : ℝ) : ∃ r θ : ℝ, 0 ≤ r ∧ r ^ 2 = x ^ 2 + y ^ 2 ∧ 0 ≤ θ ∧ θ < 2 * π ∧
    x = r * cos θ ∧ y = r * sin θ := by
  obtain ⟨r, θ, hr, hr2, h1, h2, hx, hy⟩ := ch11e3b_polar x y
  have hp := Real.pi_pos
  by_cases hθ : 0 ≤ θ
  · refine ⟨r, θ, hr, hr2, hθ, by linarith, hx, hy⟩
  · refine ⟨r, θ + 2 * π, hr, hr2, by linarith, by linarith, ?_, ?_⟩
    · rw [Real.cos_add_two_pi]; exact hx
    · rw [Real.sin_add_two_pi]; exact hy

/-- Stitz-Zeager Exercise 11.5.41: the region inside the circle `r = 5` is the closed disk of radius 5. -/
@[kb "stitzzeager2013" "Exercise 11.5.41, p. 971"]
theorem exer_11_5_41 :
    {p : ℝ × ℝ | ∃ r θ : ℝ, 0 ≤ r ∧ r ≤ 5 ∧ 0 ≤ θ ∧ θ ≤ 2 * π ∧
      p = (r * cos θ, r * sin θ)} = {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ 25} := by
  ext ⟨x, y⟩
  simp only [Set.mem_setOf_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨r, θ, hr0, hr5, _, _, rfl, rfl⟩
    have h := Real.sin_sq_add_cos_sq θ
    have e : (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 := by linear_combination r ^ 2 * h
    rw [e]
    nlinarith
  · intro h
    obtain ⟨r, θ, hr, hr2, h1, h2, hx, hy⟩ := ch11e3b_polar2 x y
    exact ⟨r, θ, hr, by nlinarith, h1, h2.le, hx, hy⟩

/-- Stitz-Zeager Exercise 11.5.48: the region inside the circle `r = 5` and outside the circle `r = 3`
is the closed annulus `9 ≤ x² + y² ≤ 25`. -/
@[kb "stitzzeager2013" "Exercise 11.5.48, p. 971"]
theorem exer_11_5_48_w8 :
    {p : ℝ × ℝ | ∃ r θ : ℝ, 3 ≤ r ∧ r ≤ 5 ∧ 0 ≤ θ ∧ θ ≤ 2 * π ∧
      p = (r * cos θ, r * sin θ)} = {p : ℝ × ℝ | 9 ≤ p.1 ^ 2 + p.2 ^ 2 ∧ p.1 ^ 2 + p.2 ^ 2 ≤ 25} := by
  ext ⟨x, y⟩
  simp only [Set.mem_setOf_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨r, θ, hr3, hr5, _, _, rfl, rfl⟩
    have h := Real.sin_sq_add_cos_sq θ
    have e : (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 := by linear_combination r ^ 2 * h
    rw [e]
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    obtain ⟨r, θ, hr, hr2, h3, h4, hx, hy⟩ := ch11e3b_polar2 x y
    exact ⟨r, θ, by nlinarith, by nlinarith, h3, h4.le, hx, hy⟩

/-- Stitz-Zeager Exercise 11.5.43: the part of the disk inside `r = 6 sin θ` with `π/2 ≤ θ ≤ π` (its left
half) is `{x ≤ 0, x² + y² ≤ 6y}`. -/
@[kb "stitzzeager2013" "Exercise 11.5.43, p. 971"]
theorem exer_11_5_43 :
    {p : ℝ × ℝ | ∃ r θ : ℝ, 0 ≤ r ∧ r ≤ 6 * sin θ ∧ π / 2 ≤ θ ∧ θ ≤ π ∧
      p = (r * cos θ, r * sin θ)} = {p : ℝ × ℝ | p.1 ≤ 0 ∧ p.1 ^ 2 + p.2 ^ 2 ≤ 6 * p.2} := by
  ext ⟨x, y⟩
  simp only [Set.mem_setOf_eq, Prod.mk.injEq]
  have hp := Real.pi_pos
  constructor
  · rintro ⟨r, θ, hr0, hr6, h1, h2, rfl, rfl⟩
    have hc : cos θ ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le h1 (by linarith)
    have h := Real.sin_sq_add_cos_sq θ
    have e : (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 := by linear_combination r ^ 2 * h
    refine ⟨by nlinarith, ?_⟩
    rw [e]
    nlinarith
  · rintro ⟨hx0, hxy⟩
    obtain ⟨r, θ, hr, hr2, h1, h2, hx, hy⟩ := ch11e3b_polar x y
    have hy0 : 0 ≤ y := by nlinarith [sq_nonneg x, sq_nonneg y]
    by_cases hr0 : r = 0
    · refine ⟨0, π / 2, le_refl _, by rw [Real.sin_pi_div_two]; norm_num, le_refl _, by linarith, ?_, ?_⟩
      · rw [hx, hr0]; simp
      · rw [hy, hr0]; simp
    · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
      have hsin : 0 ≤ sin θ := by
        by_contra hneg
        have hneg' : sin θ < 0 := lt_of_not_ge hneg
        nlinarith
      have hcos : cos θ ≤ 0 := by
        by_contra hneg
        have hneg' : 0 < cos θ := lt_of_not_ge hneg
        nlinarith
      have hθ0 : 0 ≤ θ := by
        by_contra hneg
        have hneg' : θ < 0 := lt_of_not_ge hneg
        have := Real.sin_neg_of_neg_of_neg_pi_lt hneg' h1
        linarith
      have hθ2 : π / 2 ≤ θ := by
        by_contra hneg
        have hneg' : θ < π / 2 := lt_of_not_ge hneg
        have := Real.cos_pos_of_mem_Ioo ⟨by linarith, hneg'⟩
        linarith
      refine ⟨r, θ, hr, ?_, hθ2, h2, hx, hy⟩
      have : r * r ≤ r * (6 * sin θ) := by nlinarith
      exact le_of_mul_le_mul_left this hrp

end UndergradKB.Precalculus.Course
