import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Interval.Set.Basic
import UndergradKB.Precalculus.Radicals
import UndergradKB.Precalculus.RationalExponents
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 5 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 5.3 (more graphs) -/

namespace UndergradKB.Precalculus.Course

open Set UndergradKB.Precalculus

private theorem x5w7e_cube_pos (y : ℝ) : 0 < principalRoot 3 y ↔ 0 < y := by
  have h := principalRoot_pow (n := 3) (x := y) (by norm_num) (Or.inl (by decide))
  constructor
  · intro hr; rw [← h]; exact pow_pos hr 3
  · intro hy; by_contra hc
    have : principalRoot 3 y ≤ 0 := not_lt.1 hc
    have : principalRoot 3 y ^ 3 ≤ 0 := Odd.pow_nonpos (by decide) this
    linarith

private theorem x5w7e_cube_neg (y : ℝ) : principalRoot 3 y < 0 ↔ y < 0 := by
  have h := principalRoot_pow (n := 3) (x := y) (by norm_num) (Or.inl (by decide))
  constructor
  · intro hr; rw [← h]; exact Odd.pow_neg (by decide) hr
  · intro hy; by_contra hc
    have : 0 ≤ principalRoot 3 y := not_lt.1 hc
    have : 0 ≤ principalRoot 3 y ^ 3 := pow_nonneg this 3
    linarith

private theorem x5w7e_cube_zero (y : ℝ) : principalRoot 3 y = 0 ↔ y = 0 := by
  have h := principalRoot_pow (n := 3) (x := y) (by norm_num) (Or.inl (by decide))
  constructor
  · intro hr; rw [← h, hr]; norm_num
  · intro hy
    have : principalRoot 3 y ^ 3 = 0 := by rw [h, hy]
    exact pow_eq_zero_iff (by norm_num) |>.1 this

/-- Stitz-Zeager Exercise 5.3.7: `f(x) = x^(2/3) (x-7)^(1/3)` (book's powers, real roots) is defined on all of
`ℝ`, vanishes exactly at `0` and `7`, and is negative on `(-∞, 0)` and `(0, 7)`, positive on `(7, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 5.3.7, p. 419"]
theorem exer_5_3_7 (f : ℝ → ℝ) (hf : f = fun x => bookRatPow x 2 3 * bookRatPow (x - 7) 1 3) :
    (∀ x : ℝ, BookRatPowDefined x 2 3 ∧ BookRatPowDefined (x - 7) 1 3) ∧
    (∀ x : ℝ, f x = 0 ↔ x = 0 ∨ x = 7) ∧
    (∀ x : ℝ, x < 0 → f x < 0) ∧ (∀ x : ℝ, 0 < x → x < 7 → f x < 0) ∧ (∀ x : ℝ, 7 < x → 0 < f x) := by
  subst hf
  have e : ∀ x : ℝ, bookRatPow x 2 3 * bookRatPow (x - 7) 1 3 =
      principalRoot 3 x ^ 2 * principalRoot 3 (x - 7) := by
    intro x; simp [bookRatPow]
  have sq_pos : ∀ x : ℝ, x ≠ 0 → 0 < principalRoot 3 x ^ 2 := by
    intro x hx
    have : principalRoot 3 x ≠ 0 := fun h => hx ((x5w7e_cube_zero x).1 h)
    positivity
  refine ⟨fun x => ⟨⟨by norm_num, Or.inl (by decide), Or.inl (by norm_num)⟩,
    ⟨by norm_num, Or.inl (by decide), Or.inl (by norm_num)⟩⟩, ?_, ?_, ?_, ?_⟩
  · intro x
    simp only [e, mul_eq_zero, pow_eq_zero_iff (two_ne_zero), x5w7e_cube_zero, sub_eq_zero]
  · intro x hx
    simp only [e]
    exact mul_neg_of_pos_of_neg (sq_pos x hx.ne) ((x5w7e_cube_neg _).2 (by linarith))
  · intro x h1 h2
    simp only [e]
    exact mul_neg_of_pos_of_neg (sq_pos x h1.ne') ((x5w7e_cube_neg _).2 (by linarith))
  · intro x hx
    simp only [e]
    exact mul_pos (sq_pos x (by linarith)) ((x5w7e_cube_pos _).2 (by linarith))

/-- Stitz-Zeager Exercise 5.3.8: `f(x) = x^(3/2) (x-7)^(1/3)` has domain `[0, ∞)`, zeros `0` and `7`, is negative on
`(0, 7)` and positive on `(7, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 5.3.8, p. 419"]
theorem exer_5_3_8 (f : ℝ → ℝ) (hf : f = fun x => bookRatPow x 3 2 * bookRatPow (x - 7) 1 3) :
    {x : ℝ | BookRatPowDefined x 3 2} = Ici 0 ∧
    (∀ x : ℝ, 0 ≤ x → (f x = 0 ↔ x = 0 ∨ x = 7)) ∧
    (∀ x : ℝ, 0 < x → x < 7 → f x < 0) ∧ (∀ x : ℝ, 7 < x → 0 < f x) := by
  subst hf
  have e : ∀ x : ℝ, bookRatPow x 3 2 * bookRatPow (x - 7) 1 3 =
      principalRoot 2 x ^ 3 * principalRoot 3 (x - 7) := by
    intro x; simp [bookRatPow]
  have pos2 : ∀ x : ℝ, 0 < x → 0 < principalRoot 2 x ^ 3 := by
    intro x hx
    rw [principalRoot_of_nonneg hx.le]
    positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext x
    simp only [mem_ofPred_eq, mem_Ici, BookRatPowDefined]
    constructor
    · rintro ⟨_, h, _⟩; rcases h with h | h
      · exact absurd h (by decide)
      · exact h
    · intro h; exact ⟨by norm_num, Or.inr h, Or.inl (by norm_num)⟩
  · intro x hx
    simp only [e, mul_eq_zero, pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0), x5w7e_cube_zero, sub_eq_zero]
    rcases hx.eq_or_lt with h | h
    · subst h
      have : principalRoot 2 0 = 0 := by
        rw [principalRoot_of_nonneg le_rfl]; simp
      simp [this]
    · have : principalRoot 2 x ≠ 0 := by
        intro h'; have := pos2 x h; rw [h'] at this; simp at this
      constructor
      · rintro (h' | h')
        · exact absurd h' this
        · right; exact h'
      · rintro (h' | h')
        · exact absurd h' h.ne'
        · right; exact h'
  · intro x h1 h2
    simp only [e]
    exact mul_neg_of_pos_of_neg (pos2 x h1) ((x5w7e_cube_neg _).2 (by linarith))
  · intro x hx
    simp only [e]
    exact mul_pos (pos2 x (by linarith)) ((x5w7e_cube_pos _).2 (by linarith))

/-- Stitz-Zeager Exercise 5.3.9: `f(x) = √(x(x+5)(x-4))` has domain `[-5, 0] ∪ [4, ∞)`, zeros `-5, 0, 4`, and is
positive at every other point of its domain. -/
@[kb "stitzzeager2013" "Exercise 5.3.9, p. 419"]
theorem exer_5_3_9 (f : ℝ → ℝ) (hf : f = fun x => Real.sqrt (x * (x + 5) * (x - 4))) :
    {x : ℝ | 0 ≤ x * (x + 5) * (x - 4)} = Icc (-5) 0 ∪ Ici 4 ∧
    (∀ x ∈ Icc (-5 : ℝ) 0 ∪ Ici 4, f x = 0 ↔ x = -5 ∨ x = 0 ∨ x = 4) ∧
    (∀ x ∈ Icc (-5 : ℝ) 0 ∪ Ici 4, x ≠ -5 → x ≠ 0 → x ≠ 4 → 0 < f x) := by
  subst hf
  have dom : {x : ℝ | 0 ≤ x * (x + 5) * (x - 4)} = Icc (-5) 0 ∪ Ici 4 := by
    ext x; simp only [mem_ofPred_eq, mem_union, mem_Icc, mem_Ici]
    constructor
    · intro h
      by_contra hc; push Not at hc
      obtain ⟨hc1, hc2⟩ := hc
      rcases lt_or_ge x (-5) with h1 | h1
      · have : 0 < x * (x + 5) := mul_pos_of_neg_of_neg (by linarith) (by linarith)
        have := mul_neg_of_pos_of_neg this (by linarith : x - 4 < 0)
        linarith
      · have h0 : 0 < x := by
          by_contra h0; exact absurd (hc1 h1) (by linarith [not_lt.1 h0])
        have : 0 < x * (x + 5) := mul_pos h0 (by linarith)
        have := mul_neg_of_pos_of_neg this (by linarith [hc2] : x - 4 < 0)
        linarith
    · rintro (⟨h1, h2⟩ | h)
      · exact mul_nonneg_of_nonpos_of_nonpos
          (mul_nonpos_of_nonpos_of_nonneg h2 (by linarith)) (by linarith)
      · exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  refine ⟨dom, fun x hx => ?_, fun x hx h1 h2 h3 => ?_⟩
  · have hp : 0 ≤ x * (x + 5) * (x - 4) := by
      have : x ∈ {x : ℝ | 0 ≤ x * (x + 5) * (x - 4)} := by rw [dom]; exact hx
      exact this
    show Real.sqrt (x * (x + 5) * (x - 4)) = 0 ↔ _
    simp only [Real.sqrt_eq_zero hp, mul_eq_zero, add_eq_zero_iff_eq_neg, sub_eq_zero]
    tauto
  · have hp : 0 ≤ x * (x + 5) * (x - 4) := by
      have : x ∈ {x : ℝ | 0 ≤ x * (x + 5) * (x - 4)} := by rw [dom]; exact hx
      exact this
    show 0 < Real.sqrt (x * (x + 5) * (x - 4))
    refine Real.sqrt_pos.2 (lt_of_le_of_ne hp (fun h => ?_))
    have := h.symm
    simp only [mul_eq_zero, sub_eq_zero] at this
    rcases this with (h | h) | h
    · exact h2 h
    · exact h1 (by linarith)
    · exact h3 h

/-- Stitz-Zeager Exercise 5.3.10: `f(x) = ∛(x³+3x²-6x-8)` is defined on `ℝ`, has zeros `-4, -1, 2`, and its sign
is `-`, `+`, `-`, `+` on `(-∞,-4)`, `(-4,-1)`, `(-1,2)`, `(2,∞)`. -/
@[kb "stitzzeager2013" "Exercise 5.3.10, p. 419"]
theorem exer_5_3_10 (f : ℝ → ℝ) (hf : f = fun x => principalRoot 3 (x ^ 3 + 3 * x ^ 2 - 6 * x - 8)) :
    (∀ x : ℝ, f x = 0 ↔ x = -4 ∨ x = -1 ∨ x = 2) ∧
    (∀ x : ℝ, x < -4 → f x < 0) ∧ (∀ x : ℝ, -4 < x → x < -1 → 0 < f x) ∧
    (∀ x : ℝ, -1 < x → x < 2 → f x < 0) ∧ (∀ x : ℝ, 2 < x → 0 < f x) := by
  subst hf
  have hp : ∀ x : ℝ, x ^ 3 + 3 * x ^ 2 - 6 * x - 8 = (x + 4) * (x + 1) * (x - 2) := by
    intro x; ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simp only [x5w7e_cube_zero, hp, mul_eq_zero, add_eq_zero_iff_eq_neg, sub_eq_zero]
    constructor
    · rintro ((h | h) | h)
      · left; exact h
      · right; left; exact h
      · right; right; exact h
    · rintro (h | h | h)
      · left; left; exact h
      · left; right; exact h
      · right; exact h
  · intro x h
    simp only [x5w7e_cube_neg, hp]
    exact mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg (by linarith) (by linarith)) (by linarith)
  · intro x h1 h2
    simp only [x5w7e_cube_pos, hp]
    exact mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg (by linarith) (by linarith)) (by linarith)
  · intro x h1 h2
    simp only [x5w7e_cube_neg, hp]
    exact mul_neg_of_pos_of_neg (mul_pos (by linarith) (by linarith)) (by linarith)
  · intro x h
    simp only [x5w7e_cube_pos, hp]
    exact mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)

end UndergradKB.Precalculus.Course
