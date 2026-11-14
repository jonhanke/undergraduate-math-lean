import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Interval.Set.Basic
import UndergradKB.Precalculus.Radicals
import UndergradKB.Precalculus.RationalExponents
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 5 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 5.3 (graphs) -/

namespace UndergradKB.Precalculus.Course

open Set UndergradKB.Precalculus

/-! ## Section 5.3: domains, zeros and signs of algebraic functions -/

private theorem x5w7_cube_pos (y : ℝ) : 0 < principalRoot 3 y ↔ 0 < y := by
  have h := principalRoot_pow (n := 3) (x := y) (by norm_num) (Or.inl (by decide))
  constructor
  · intro hr; rw [← h]; exact pow_pos hr 3
  · intro hy; by_contra hc
    have : principalRoot 3 y ≤ 0 := not_lt.1 hc
    have : principalRoot 3 y ^ 3 ≤ 0 := Odd.pow_nonpos (by decide) this
    linarith

private theorem x5w7_cube_neg (y : ℝ) : principalRoot 3 y < 0 ↔ y < 0 := by
  have h := principalRoot_pow (n := 3) (x := y) (by norm_num) (Or.inl (by decide))
  constructor
  · intro hr; rw [← h]; exact Odd.pow_neg (by decide) hr
  · intro hy; by_contra hc
    have : 0 ≤ principalRoot 3 y := not_lt.1 hc
    have : 0 ≤ principalRoot 3 y ^ 3 := pow_nonneg this 3
    linarith

private theorem x5w7_cube_zero (y : ℝ) : principalRoot 3 y = 0 ↔ y = 0 := by
  have h := principalRoot_pow (n := 3) (x := y) (by norm_num) (Or.inl (by decide))
  constructor
  · intro hr; rw [← h, hr]; norm_num
  · intro hy
    have : principalRoot 3 y ^ 3 = 0 := by rw [h, hy]
    exact pow_eq_zero_iff (by norm_num) |>.1 this

/-- Stitz-Zeager Exercise 5.3.3: `f(x) = x√(1-x²)` has domain `[-1, 1]`, zeros `-1, 0, 1`, is negative on
`(-1, 0)` and positive on `(0, 1)`. -/
@[kb "stitzzeager2013" "Exercise 5.3.3, p. 419"]
theorem exer_5_3_3 (f : ℝ → ℝ) (hf : f = fun x => x * Real.sqrt (1 - x ^ 2)) :
    {x : ℝ | 0 ≤ 1 - x ^ 2} = Icc (-1) 1 ∧
    (∀ x ∈ Icc (-1 : ℝ) 1, f x = 0 ↔ x = -1 ∨ x = 0 ∨ x = 1) ∧
    (∀ x : ℝ, -1 < x → x < 0 → f x < 0) ∧ (∀ x : ℝ, 0 < x → x < 1 → 0 < f x) := by
  subst hf
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext x; simp only [mem_ofPred_eq, mem_Icc]
    constructor
    · intro h; constructor <;> nlinarith
    · rintro ⟨h1, h2⟩; nlinarith
  · intro x hx
    simp only [mul_eq_zero, Real.sqrt_eq_zero']
    constructor
    · rintro (h | h)
      · right; left; exact h
      · have : x ^ 2 = 1 := by nlinarith [hx.1, hx.2]
        have : (x - 1) * (x + 1) = 0 := by ring_nf; linarith
        rcases mul_eq_zero.1 this with h | h
        · right; right; linarith
        · left; linarith
    · rintro (h | h | h) <;> subst h <;> norm_num
  · intro x h1 h2
    have : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.2 (by nlinarith)
    nlinarith
  · intro x h1 h2
    have : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.2 (by nlinarith)
    positivity

/-- Stitz-Zeager Exercise 5.3.4: `f(x) = x√(x²-1)` has domain `(-∞, -1] ∪ [1, ∞)`, zeros `±1`, is negative
for `x < -1` and positive for `x > 1`. -/
@[kb "stitzzeager2013" "Exercise 5.3.4, p. 419"]
theorem exer_5_3_4 (f : ℝ → ℝ) (hf : f = fun x => x * Real.sqrt (x ^ 2 - 1)) :
    {x : ℝ | 0 ≤ x ^ 2 - 1} = Iic (-1) ∪ Ici 1 ∧
    (∀ x ∈ Iic (-1 : ℝ) ∪ Ici 1, f x = 0 ↔ x = -1 ∨ x = 1) ∧
    (∀ x : ℝ, x < -1 → f x < 0) ∧ (∀ x : ℝ, 1 < x → 0 < f x) := by
  subst hf
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext x; simp only [mem_ofPred_eq, mem_union, mem_Iic, mem_Ici]
    constructor
    · intro h; by_contra hc; push Not at hc; nlinarith [hc.1, hc.2]
    · rintro (h | h) <;> nlinarith
  · intro x hx
    have hx0 : x ≠ 0 := by rintro rfl; rcases hx with h | h <;> simp at h <;> linarith
    simp only [mul_eq_zero, Real.sqrt_eq_zero', hx0, false_or]
    constructor
    · intro h
      have : x ^ 2 = 1 := by
        rcases hx with h' | h' <;> simp only [mem_Iic, mem_Ici] at h' <;> nlinarith
      have : (x - 1) * (x + 1) = 0 := by ring_nf; linarith
      rcases mul_eq_zero.1 this with h | h
      · right; linarith
      · left; linarith
    · rintro (h | h) <;> subst h <;> norm_num
  · intro x h
    have : 0 < Real.sqrt (x ^ 2 - 1) := Real.sqrt_pos.2 (by nlinarith)
    nlinarith
  · intro x h
    have : 0 < Real.sqrt (x ^ 2 - 1) := Real.sqrt_pos.2 (by nlinarith)
    positivity

/-- Stitz-Zeager Exercise 5.3.6: `f(x) = 5x / ∛(x³+8)` has domain all `x ≠ -2`, its only zero is `0`, and its
sign is `+` on `(-∞, -2)`, `-` on `(-2, 0)`, `+` on `(0, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 5.3.6, p. 419"]
theorem exer_5_3_6 (f : ℝ → ℝ) (hf : f = fun x => 5 * x / principalRoot 3 (x ^ 3 + 8)) :
    {x : ℝ | principalRoot 3 (x ^ 3 + 8) ≠ 0} = {x | x ≠ -2} ∧
    (∀ x : ℝ, x ≠ -2 → (f x = 0 ↔ x = 0)) ∧
    (∀ x : ℝ, x < -2 → 0 < f x) ∧ (∀ x : ℝ, -2 < x → x < 0 → f x < 0) ∧ (∀ x : ℝ, 0 < x → 0 < f x) := by
  subst hf
  have key : ∀ x : ℝ, 0 < x + 2 ↔ 0 < x ^ 3 + 8 := by
    intro x
    have : x ^ 3 + 8 = (x + 2) * ((x - 1) ^ 2 + 3) := by ring
    rw [this]
    exact (mul_pos_iff_of_pos_right (by positivity)).symm
  have key0 : ∀ x : ℝ, x ^ 3 + 8 = 0 → x = -2 := by
    intro x h
    have : (x + 2) * ((x - 1) ^ 2 + 3) = 0 := by rw [← h]; ring
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · nlinarith [sq_nonneg (x - 1)]
  have key' : ∀ x : ℝ, x + 2 < 0 ↔ x ^ 3 + 8 < 0 := by
    intro x
    have : x ^ 3 + 8 = (x + 2) * ((x - 1) ^ 2 + 3) := by ring
    rw [this]
    constructor
    · intro h; exact mul_neg_of_neg_of_pos h (by positivity)
    · intro h; by_contra hc
      have : 0 ≤ (x + 2) * ((x - 1) ^ 2 + 3) := mul_nonneg (not_lt.1 hc) (by positivity)
      linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext x; simp only [mem_ofPred_eq, Ne, x5w7_cube_zero]
    constructor
    · intro h h'; apply h; subst h'; norm_num
    · intro h h'
      exact h (key0 x h')
  · intro x hx
    have hne : principalRoot 3 (x ^ 3 + 8) ≠ 0 := by
      rw [Ne, x5w7_cube_zero]; intro h
      exact hx (key0 x h)
    rw [div_eq_zero_iff]
    constructor
    · rintro (h | h)
      · linarith
      · exact absurd h hne
    · intro h; left; rw [h]; norm_num
  · intro x hx
    have h1 : principalRoot 3 (x ^ 3 + 8) < 0 := (x5w7_cube_neg _).2 ((key' x).1 (by linarith))
    exact div_pos_of_neg_of_neg (by linarith) h1
  · intro x h1 h2
    have h3 : 0 < principalRoot 3 (x ^ 3 + 8) := (x5w7_cube_pos _).2 ((key x).1 (by linarith))
    exact div_neg_of_neg_of_pos (by linarith) h3
  · intro x hx
    have h3 : 0 < principalRoot 3 (x ^ 3 + 8) := (x5w7_cube_pos _).2 ((key x).1 (by linarith))
    positivity

end UndergradKB.Precalculus.Course
