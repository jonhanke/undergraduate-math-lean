import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Data.Int.Interval
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 11 (Stitz-Zeager): exercises with the book's answers (wave 8), Section 11.5 (regions 49, 50) -/

namespace UndergradKB.Precalculus.Course

open Real

/-- Every point of the plane has polar coordinates `r ≥ 0`, `θ ∈ (-π, π]`. -/
theorem ch11e3h_polar (x y : ℝ) : ∃ r θ : ℝ, 0 ≤ r ∧ r ^ 2 = x ^ 2 + y ^ 2 ∧ -π < θ ∧ θ ≤ π ∧
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

/-- An angle in `[-π, π]` with nonnegative cosine lies in `[-π/2, π/2]`. -/
theorem ch11e3h_cosnn (θ : ℝ) (h1 : -π ≤ θ) (h2 : θ ≤ π) (h : 0 ≤ cos θ) :
    -(π / 2) ≤ θ ∧ θ ≤ π / 2 := by
  have hp := Real.pi_pos
  constructor
  · by_contra hn
    have hlt : θ < -(π / 2) := lt_of_not_ge hn
    have := Real.cos_neg_of_pi_div_two_lt_of_lt (x := -θ) (by linarith) (by linarith)
    rw [Real.cos_neg] at this
    linarith
  · by_contra hn
    have hlt : π / 2 < θ := lt_of_not_ge hn
    have := Real.cos_neg_of_pi_div_two_lt_of_lt (x := θ) hlt (by linarith)
    linarith

/-- An angle in `(-π, π]` with nonnegative sine is nonnegative. -/
theorem ch11e3h_sinnn (θ : ℝ) (h1 : -π < θ) (h : 0 ≤ sin θ) : 0 ≤ θ := by
  by_contra hn
  have hlt : θ < 0 := lt_of_not_ge hn
  have := Real.sin_neg_of_neg_of_neg_pi_lt hlt h1
  linarith

/-- Stitz-Zeager Exercise 11.5.49: the region inside `r = 3 cos θ` and outside `r = sin θ` (given as two
angular pieces, the second ending at `arctan 3`) is `{x² + y² ≤ 3x, y ≤ x² + y²}`. -/
@[kb "stitzzeager2013" "Exercise 11.5.49, p. 971"]
theorem exer_11_5_49 :
    {p : ℝ × ℝ | ∃ r θ : ℝ, ((0 ≤ r ∧ r ≤ 3 * cos θ ∧ -(π / 2) ≤ θ ∧ θ ≤ 0) ∨
      (sin θ ≤ r ∧ r ≤ 3 * cos θ ∧ 0 ≤ θ ∧ θ ≤ arctan 3)) ∧ p = (r * cos θ, r * sin θ)} =
    {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ 3 * p.1 ∧ p.2 ≤ p.1 ^ 2 + p.2 ^ 2} := by
  ext ⟨x, y⟩
  simp only [Set.mem_setOf_eq, Prod.mk.injEq]
  have hp := Real.pi_pos
  have hat := Real.arctan_lt_pi_div_two 3
  constructor
  · rintro ⟨r, θ, hcase, rfl, rfl⟩
    have h := Real.sin_sq_add_cos_sq θ
    have e : (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 := by linear_combination r ^ 2 * h
    rcases hcase with ⟨hr0, hr1, h1, h2⟩ | ⟨hr0, hr1, h1, h2⟩
    · have hc : 0 ≤ cos θ := Real.cos_nonneg_of_mem_Icc ⟨h1, by linarith⟩
      have hs : sin θ ≤ 0 := Real.sin_nonpos_of_nonpos_of_neg_pi_le h2 (by linarith)
      rw [e]
      constructor
      · nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hr1)]
      · nlinarith [mul_nonneg hr0 (neg_nonneg.mpr hs), sq_nonneg r]
    · have hc : 0 ≤ cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
      have hs : 0 ≤ sin θ := Real.sin_nonneg_of_nonneg_of_le_pi h1 (by linarith)
      have hr : 0 ≤ r := le_trans hs hr0
      rw [e]
      constructor
      · nlinarith [mul_nonneg hr (sub_nonneg.mpr hr1)]
      · nlinarith [mul_nonneg hr (sub_nonneg.mpr hr0)]
  · rintro ⟨h1, h2⟩
    obtain ⟨r, θ, hr, hr2, ht1, ht2, hx, hy⟩ := ch11e3h_polar x y
    rw [← hr2] at h1 h2
    by_cases hr0 : r = 0
    · refine ⟨0, 0, Or.inl ⟨le_refl _, by simp, by linarith, le_refl _⟩, ?_, ?_⟩
      · rw [hx, hr0]; simp
      · rw [hy, hr0]; simp
    · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
      rw [hx] at h1
      have hcos : 0 ≤ cos θ := by
        by_contra hneg
        have hneg' : cos θ < 0 := lt_of_not_ge hneg
        nlinarith [mul_neg_of_pos_of_neg hrp hneg']
      obtain ⟨b1, b2⟩ := ch11e3h_cosnn θ ht1.le ht2 hcos
      have hle : r ≤ 3 * cos θ := by
        have : r * r ≤ r * (3 * cos θ) := by nlinarith
        exact le_of_mul_le_mul_left this hrp
      by_cases hθ : θ ≤ 0
      · exact ⟨r, θ, Or.inl ⟨hr, hle, b1, hθ⟩, hx, hy⟩
      · have hθ' : 0 < θ := lt_of_not_ge hθ
        rw [hy] at h2
        have hsr : sin θ ≤ r := by
          have : r * sin θ ≤ r * r := by nlinarith
          exact le_of_mul_le_mul_left this hrp
        have hcpos : 0 < cos θ := by
          by_contra hneg
          have hneg' : cos θ ≤ 0 := not_lt.mp hneg
          nlinarith
        have hlt : θ < π / 2 := by
          by_contra hneg
          have hge : π / 2 ≤ θ := not_lt.mp hneg
          have := Real.cos_nonpos_of_pi_div_two_le_of_le hge (by linarith)
          linarith
        have htan : tan θ ≤ 3 := by
          rw [Real.tan_eq_sin_div_cos, div_le_iff₀ hcpos]
          linarith
        have harc : θ ≤ arctan 3 := by
          have := Real.arctan_strictMono.monotone htan
          rwa [Real.arctan_tan (by linarith) hlt] at this
        exact ⟨r, θ, Or.inr ⟨hsr, hle, hθ'.le, harc⟩, hx, hy⟩

/-- `sin φ ≤ 1/2` for `0 ≤ φ ≤ π/6`. -/
theorem ch11e3h_lo (φ : ℝ) (h0 : 0 ≤ φ) (h1 : φ ≤ π / 6) : sin φ ≤ 1 / 2 := by
  have hp := Real.pi_pos
  have := Real.sin_le_sin_of_le_of_le_pi_div_two (x := φ) (y := π / 6) (by linarith)
    (by linarith) h1
  rwa [Real.sin_pi_div_six] at this

/-- `sin φ ≥ 1/2` for `π/6 ≤ φ ≤ 5π/6`. -/
theorem ch11e3h_mid (φ : ℝ) (h0 : π / 6 ≤ φ) (h1 : φ ≤ 5 * π / 6) : 1 / 2 ≤ sin φ := by
  have hp := Real.pi_pos
  by_cases h : φ ≤ π / 2
  · have := Real.sin_le_sin_of_le_of_le_pi_div_two (x := π / 6) (y := φ) (by linarith) h h0
    rwa [Real.sin_pi_div_six] at this
  · have :=Real.sin_le_sin_of_le_of_le_pi_div_two (x := π / 6) (y := π - φ) (by linarith) (by linarith)
      (by linarith)
    rwa [Real.sin_pi_div_six, Real.sin_pi_sub] at this

/-- `sin φ ≤ 1/2` for `5π/6 ≤ φ ≤ π`. -/
theorem ch11e3h_hi (φ : ℝ) (h0 : 5 * π / 6 ≤ φ) (h1 : φ ≤ π) : sin φ ≤ 1 / 2 := by
  have := ch11e3h_lo (π - φ) (by linarith) (by linarith)
  rwa [Real.sin_pi_sub] at this

/-- Stitz-Zeager Exercise 11.5.50: the part of the region inside the circle `r = 3` and inside the rose
`r = 6 sin 2θ` that lies in Quadrant I (three angular pieces) is
`{x ≥ 0, y ≥ 0, x² + y² ≤ 9, (x² + y²)³ ≤ 144 (xy)²}`. -/
@[kb "stitzzeager2013" "Exercise 11.5.50, p. 971"]
theorem exer_11_5_50 :
    {p : ℝ × ℝ | ∃ r θ : ℝ, 0 ≤ r ∧ ((r ≤ 6 * sin (2 * θ) ∧ 0 ≤ θ ∧ θ ≤ π / 12) ∨
      (r ≤ 3 ∧ π / 12 ≤ θ ∧ θ ≤ 5 * π / 12) ∨
      (r ≤ 6 * sin (2 * θ) ∧ 5 * π / 12 ≤ θ ∧ θ ≤ π / 2)) ∧ p = (r * cos θ, r * sin θ)} =
    {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 ^ 2 + p.2 ^ 2 ≤ 9 ∧
      (p.1 ^ 2 + p.2 ^ 2) ^ 3 ≤ 144 * (p.1 * p.2) ^ 2} := by
  ext ⟨x, y⟩
  simp only [Set.mem_setOf_eq, Prod.mk.injEq]
  have hp := Real.pi_pos
  constructor
  · rintro ⟨r, θ, hr0, hcase, rfl, rfl⟩
    have key : 0 ≤ θ ∧ θ ≤ π / 2 ∧ r ≤ 3 ∧ r ≤ 6 * sin (2 * θ) := by
      rcases hcase with ⟨h6, h1, h2⟩ | ⟨h3, h1, h2⟩ | ⟨h6, h1, h2⟩
      · have := ch11e3h_lo (2 * θ) (by linarith) (by linarith)
        exact ⟨h1, by linarith, by linarith, h6⟩
      · have := ch11e3h_mid (2 * θ) (by linarith) (by linarith)
        exact ⟨by linarith, by linarith, h3, by linarith⟩
      · have := ch11e3h_hi (2 * θ) (by linarith) (by linarith)
        exact ⟨by linarith, h2, by linarith, h6⟩
    obtain ⟨k0, k1, k3, k6⟩ := key
    have hc : 0 ≤ cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith, k1⟩
    have hs : 0 ≤ sin θ := Real.sin_nonneg_of_nonneg_of_le_pi k0 (by linarith)
    have h := Real.sin_sq_add_cos_sq θ
    have e : (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 := by linear_combination r ^ 2 * h
    rw [Real.sin_two_mul] at k6
    have k6' : r ≤ 12 * (sin θ * cos θ) := by linarith
    have h3 : r ^ 3 ≤ 12 * ((r * cos θ) * (r * sin θ)) := by
      nlinarith [mul_le_mul_of_nonneg_left k6' (sq_nonneg r)]
    have h3' := pow_le_pow_left₀ (pow_nonneg hr0 3) h3 2
    refine ⟨mul_nonneg hr0 hc, mul_nonneg hr0 hs, ?_, ?_⟩
    · rw [e]; nlinarith
    · rw [e]
      calc (r ^ 2) ^ 3 = (r ^ 3) ^ 2 := by ring
        _ ≤ (12 * ((r * cos θ) * (r * sin θ))) ^ 2 := h3'
        _ = 144 * ((r * cos θ) * (r * sin θ)) ^ 2 := by ring
  · rintro ⟨hx0, hy0, h9, hcube⟩
    obtain ⟨r, θ, hr, hr2, ht1, ht2, hx, hy⟩ := ch11e3h_polar x y
    by_cases hr0 : r = 0
    · refine ⟨0, 0, le_refl _, Or.inl ⟨by simp, le_refl _, by linarith⟩, ?_, ?_⟩
      · rw [hx, hr0]; simp
      · rw [hy, hr0]; simp
    · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
      have hcos : 0 ≤ cos θ := by
        by_contra hneg
        have hneg' : cos θ < 0 := lt_of_not_ge hneg
        nlinarith [mul_neg_of_pos_of_neg hrp hneg']
      have hsin : 0 ≤ sin θ := by
        by_contra hneg
        have hneg' : sin θ < 0 := lt_of_not_ge hneg
        nlinarith [mul_neg_of_pos_of_neg hrp hneg']
      obtain ⟨b1, b2⟩ := ch11e3h_cosnn θ ht1.le ht2 hcos
      have b0 := ch11e3h_sinnn θ ht1 hsin
      have hr3 : r ≤ 3 := by nlinarith
      rw [← hr2, hx, hy] at hcube
      have h4 : r ^ 4 * r ^ 2 ≤ r ^ 4 * (144 * (sin θ * cos θ) ^ 2) := by
        calc r ^ 4 * r ^ 2 = (r ^ 2) ^ 3 := by ring
          _ ≤ 144 * ((r * cos θ) * (r * sin θ)) ^ 2 := hcube
          _ = r ^ 4 * (144 * (sin θ * cos θ) ^ 2) := by ring
      have h5 : r ^ 2 ≤ 144 * (sin θ * cos θ) ^ 2 :=
        le_of_mul_le_mul_left h4 (by positivity)
      have hsc : 0 ≤ sin θ * cos θ := mul_nonneg hsin hcos
      have h6 : r ≤ 12 * (sin θ * cos θ) := by
        by_contra hneg
        have hneg' : 12 * (sin θ * cos θ) < r := lt_of_not_ge hneg
        nlinarith
      have h6' : r ≤ 6 * sin (2 * θ) := by rw [Real.sin_two_mul]; linarith
      by_cases hA : θ ≤ π / 12
      · exact ⟨r, θ, hr, Or.inl ⟨h6', b0, hA⟩, hx, hy⟩
      · have hA' : π / 12 < θ := lt_of_not_ge hA
        by_cases hB : θ ≤ 5 * π / 12
        · exact ⟨r, θ, hr, Or.inr (Or.inl ⟨hr3, hA'.le, hB⟩), hx, hy⟩
        · have hB' : 5 * π / 12 < θ := lt_of_not_ge hB
          exact ⟨r, θ, hr, Or.inr (Or.inr ⟨h6', hB'.le, b2⟩), hx, hy⟩

/-- The pole passes of `r = sin(nθ)` in `[0, 2π)`: exactly the `2n` angles `kπ/n`, `0 ≤ k < 2n`. -/
theorem ch11e3h_zeros_sin (n : ℕ) (hn : 0 < n) :
    {θ : ℝ | 0 ≤ θ ∧ θ < 2 * π ∧ sin ((n : ℝ) * θ) = 0}.ncard = 2 * n := by
  have hp := Real.pi_pos
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := hnp.ne'
  have hset : {θ : ℝ | 0 ≤ θ ∧ θ < 2 * π ∧ sin ((n : ℝ) * θ) = 0} =
      ↑((Finset.Ico (0 : ℤ) (2 * n)).image (fun k : ℤ => (k : ℝ) * π / n)) := by
    ext θ
    simp only [Set.mem_setOf_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_Ico]
    constructor
    · rintro ⟨h0, h2, hs⟩
      obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hs
      have hnθ0 : 0 ≤ (n : ℝ) * θ := mul_nonneg hnp.le h0
      have hnθ2 : (n : ℝ) * θ < 2 * π * n := by nlinarith
      have hk0 : 0 ≤ k := by
        by_contra h
        have h' : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
        nlinarith
      have hk1 : k < 2 * n := by
        by_contra h
        have h' : (2 * n : ℝ) ≤ k := by exact_mod_cast (by omega : 2 * (n : ℤ) ≤ k)
        nlinarith
      refine ⟨k, ⟨hk0, hk1⟩, ?_⟩
      field_simp
      linarith
    · rintro ⟨k, ⟨a, b⟩, rfl⟩
      have hk0 : (0 : ℝ) ≤ k := by exact_mod_cast a
      have hk1 : (k : ℝ) + 1 ≤ 2 * n := by exact_mod_cast (by omega : k + 1 ≤ 2 * (n : ℤ))
      refine ⟨by positivity, ?_, ?_⟩
      · rw [div_lt_iff₀ hnp]; nlinarith
      · have e : (n : ℝ) * ((k : ℝ) * π / n) = (k : ℝ) * π := by field_simp
        rw [e, Real.sin_int_mul_pi]
  rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injective]
  · simp
    omega
  · intro a b h
    have h' := (div_left_inj' hnne).mp h
    have h'' : (a : ℝ) = b := mul_right_cancel₀ hp.ne' h'
    exact_mod_cast h''

/-- The pole passes of `r = cos(nθ)` in `[0, 2π)`: exactly the `2n` angles `(2k+1)π/(2n)`, `0 ≤ k < 2n`. -/
theorem ch11e3h_zeros_cos (n : ℕ) (hn : 0 < n) :
    {θ : ℝ | 0 ≤ θ ∧ θ < 2 * π ∧ cos ((n : ℝ) * θ) = 0}.ncard = 2 * n := by
  have hp := Real.pi_pos
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := hnp.ne'
  have hset : {θ : ℝ | 0 ≤ θ ∧ θ < 2 * π ∧ cos ((n : ℝ) * θ) = 0} =
      ↑((Finset.Ico (0 : ℤ) (2 * n)).image (fun k : ℤ => (2 * (k : ℝ) + 1) * π / (2 * n))) := by
    ext θ
    simp only [Set.mem_setOf_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_Ico]
    constructor
    · rintro ⟨h0, h2, hs⟩
      obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp hs
      have hnθ0 : 0 ≤ (n : ℝ) * θ := mul_nonneg hnp.le h0
      have hnθ2 : (n : ℝ) * θ < 2 * π * n := by nlinarith
      have hk0 : 0 ≤ k := by
        by_contra h
        have h' : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
        nlinarith
      have hk1 : k < 2 * n := by
        by_contra h
        have h' : (2 * n : ℝ) ≤ k := by exact_mod_cast (by omega : 2 * (n : ℤ) ≤ k)
        nlinarith
      refine ⟨k, ⟨hk0, hk1⟩, ?_⟩
      field_simp
      linarith
    · rintro ⟨k, ⟨a, b⟩, rfl⟩
      have hk0 : (0 : ℝ) ≤ k := by exact_mod_cast a
      have hk1 : (k : ℝ) + 1 ≤ 2 * n := by exact_mod_cast (by omega : k + 1 ≤ 2 * (n : ℤ))
      refine ⟨by positivity, ?_, ?_⟩
      · rw [div_lt_iff₀ (by positivity)]; nlinarith
      · have e : (n : ℝ) * ((2 * (k : ℝ) + 1) * π / (2 * n)) = (2 * (k : ℝ) + 1) * π / 2 := by
          field_simp
        rw [e]
        exact Real.cos_eq_zero_iff.mpr ⟨k, rfl⟩
  rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injective]
  · simp
    omega
  · intro a b h
    have h' := (div_left_inj' (by positivity : (2 * (n : ℝ)) ≠ 0)).mp h
    have h'' : (2 * (a : ℝ) + 1) = 2 * b + 1 := mul_right_cancel₀ hp.ne' h'
    have : (a : ℝ) = b := by linarith
    exact_mod_cast this

/-- Stitz-Zeager Exercise 11.5.61: for the rose `r = sin(nθ)` or `r = cos(nθ)` there are exactly `2n`
pole passes in `[0, 2π)`, so `2n` half-turn-separated loops; shifting `θ` by `π` multiplies `r` by `(-1)^n`,
so for odd `n` the loop at `θ + π` is the same point set as at `θ` (the loops pair up: `n` petals), while for
even `n` it is the opposite point (all `2n` loops are distinct: `2n` petals). -/
@[kb "stitzzeager2013" "Exercise 11.5.61, p. 973"]
theorem exer_11_5_61 (n : ℕ) (hn : 0 < n) :
    {θ : ℝ | 0 ≤ θ ∧ θ < 2 * π ∧ sin ((n : ℝ) * θ) = 0}.ncard = 2 * n ∧
    {θ : ℝ | 0 ≤ θ ∧ θ < 2 * π ∧ cos ((n : ℝ) * θ) = 0}.ncard = 2 * n ∧
    (∀ θ : ℝ, sin ((n : ℝ) * (θ + π)) = (-1) ^ n * sin ((n : ℝ) * θ) ∧
      cos ((n : ℝ) * (θ + π)) = (-1) ^ n * cos ((n : ℝ) * θ)) ∧
    (Odd n → ∀ θ : ℝ,
      (sin ((n : ℝ) * (θ + π)) * cos (θ + π), sin ((n : ℝ) * (θ + π)) * sin (θ + π)) =
        (sin ((n : ℝ) * θ) * cos θ, sin ((n : ℝ) * θ) * sin θ) ∧
      (cos ((n : ℝ) * (θ + π)) * cos (θ + π), cos ((n : ℝ) * (θ + π)) * sin (θ + π)) =
        (cos ((n : ℝ) * θ) * cos θ, cos ((n : ℝ) * θ) * sin θ)) ∧
    (Even n → ∀ θ : ℝ, sin ((n : ℝ) * (θ + π)) = sin ((n : ℝ) * θ) ∧
      cos ((n : ℝ) * (θ + π)) = cos ((n : ℝ) * θ)) := by
  have key : ∀ θ : ℝ, sin ((n : ℝ) * (θ + π)) = (-1) ^ n * sin ((n : ℝ) * θ) ∧
      cos ((n : ℝ) * (θ + π)) = (-1) ^ n * cos ((n : ℝ) * θ) := by
    intro θ
    rw [mul_add]
    exact ⟨by rw [Real.sin_add_nat_mul_pi], by rw [Real.cos_add_nat_mul_pi]⟩
  refine ⟨ch11e3h_zeros_sin n hn, ch11e3h_zeros_cos n hn, key, ?_, ?_⟩
  · intro hodd θ
    obtain ⟨k1, k2⟩ := key θ
    rw [hodd.neg_one_pow] at k1 k2
    rw [k1, k2, Real.cos_add_pi, Real.sin_add_pi]
    refine ⟨?_, ?_⟩ <;> ext <;> simp
  · intro heven θ
    obtain ⟨k1, k2⟩ := key θ
    rw [heven.neg_one_pow] at k1 k2
    exact ⟨by rw [k1]; ring, by rw [k2]; ring⟩

end UndergradKB.Precalculus.Course
