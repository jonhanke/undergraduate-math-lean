import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Logic.Function.Iterate
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 5 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 5.1 (rest) -/

namespace UndergradKB.Precalculus.Course

open Set

/-- Stitz-Zeager Exercise 5.1.23: for `f(x) = x/(2x+1)`, `g(x) = (2x+1)/x`: `(g∘f)(x) = (4x+1)/x` with domain
`x ≠ -1/2, 0`; `(f∘g)(x) = (2x+1)/(5x+2)` with domain `x ≠ 0, -2/5`; `(f∘f)(x) = x/(4x+1)` with domain
`x ≠ -1/2, -1/4`. -/
@[kb "stitzzeager2013" "Exercise 5.1.23, p. 381"]
theorem exer_5_1_23 (f g : ℝ → ℝ) (hf : f = fun x => x / (2 * x + 1)) (hg : g = fun x => (2 * x + 1) / x) :
    ({x : ℝ | 2 * x + 1 ≠ 0 ∧ f x ≠ 0} = {x | x ≠ -1 / 2 ∧ x ≠ 0} ∧
      ∀ x : ℝ, x ≠ -1 / 2 → x ≠ 0 → (g ∘ f) x = (4 * x + 1) / x) ∧
    ({x : ℝ | x ≠ 0 ∧ 2 * g x + 1 ≠ 0} = {x | x ≠ 0 ∧ x ≠ -2 / 5} ∧
      ∀ x : ℝ, x ≠ 0 → x ≠ -2 / 5 → (f ∘ g) x = (2 * x + 1) / (5 * x + 2)) ∧
    ({x : ℝ | 2 * x + 1 ≠ 0 ∧ 2 * f x + 1 ≠ 0} = {x | x ≠ -1 / 2 ∧ x ≠ -1 / 4} ∧
      ∀ x : ℝ, x ≠ -1 / 2 → x ≠ -1 / 4 → (f ∘ f) x = x / (4 * x + 1)) := by
  subst hf hg
  have a1 : ∀ x : ℝ, x ≠ -1 / 2 → 2 * x + 1 ≠ 0 := fun x h h' => h (by linarith)
  refine ⟨⟨?_, fun x h1 h2 => ?_⟩, ⟨?_, fun x h1 h2 => ?_⟩, ⟨?_, fun x h1 h2 => ?_⟩⟩
  · ext x; simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun h => h1 (by linarith), fun h => h2 ?_⟩
      simp [h]
    · rintro ⟨h1, h2⟩
      have := a1 x h1
      exact ⟨this, by simp [this, h2]⟩
  · have := a1 x h1
    simp only [Function.comp]; field_simp; ring
  · ext x; simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun h => h2 ?_⟩
      subst h; field_simp; linarith
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun h => h2 ?_⟩
      field_simp at h; linarith
  · have h5 : 5 * x + 2 ≠ 0 := fun h => h2 (by linarith)
    simp only [Function.comp]; field_simp; ring
  · ext x; simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      have h1' : x ≠ -1 / 2 := fun h => h1 (by linarith)
      refine ⟨h1', fun h => h2 ?_⟩
      subst h; norm_num
    · rintro ⟨h1, h2⟩
      have := a1 x h1
      refine ⟨this, fun h => h2 ?_⟩
      field_simp at h; linarith
  · have := a1 x h1
    have h4 : 4 * x + 1 ≠ 0 := fun h => h2 (by linarith)
    simp only [Function.comp]
    have h5 : 2 * (x / (2 * x + 1)) + 1 = (4 * x + 1) / (2 * x + 1) := by field_simp; ring
    rw [h5, div_div_div_cancel_right₀ this]

/-- Stitz-Zeager Exercise 5.1.24 (composition `f ∘ g`): for `f(x) = 2x/(x²-4)`, `g(x) = √(1-x)`:
`(f∘g)(x) = -2√(1-x)/(x+3)`, with domain `(-∞, -3) ∪ (-3, 1]`. -/
@[kb "stitzzeager2013" "Exercise 5.1.24, p. 381"]
theorem exer_5_1_24 (f g : ℝ → ℝ) (hf : f = fun x => 2 * x / (x ^ 2 - 4))
    (hg : g = fun x => Real.sqrt (1 - x)) :
    {x : ℝ | 0 ≤ 1 - x ∧ g x ^ 2 - 4 ≠ 0} = Iio (-3) ∪ Ioc (-3) 1 ∧
    ∀ x : ℝ, x ≤ 1 → x ≠ -3 → (f ∘ g) x = -2 * Real.sqrt (1 - x) / (x + 3) := by
  subst hf hg
  constructor
  · ext x; simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      rw [Real.sq_sqrt h1] at h2
      by_cases h : x < -3
      · exact Or.inl h
      · right; refine ⟨?_, by linarith⟩
        rcases lt_or_eq_of_le (not_lt.1 h) with h' | h'
        · exact h'
        · exact absurd (by rw [← h']; norm_num) h2
    · rintro (h | ⟨h1, h2⟩)
      · refine ⟨by linarith, ?_⟩
        rw [Real.sq_sqrt (by linarith)]; intro h'; linarith
      · refine ⟨by linarith, ?_⟩
        rw [Real.sq_sqrt (by linarith)]; intro h'; linarith
  · intro x hx h3
    have h3' : x + 3 ≠ 0 := fun h => h3 (by linarith)
    simp only [Function.comp]
    rw [Real.sq_sqrt (by linarith)]
    have : (1 - x - 4) = -(x + 3) := by ring
    rw [this, div_neg, ← neg_div, neg_mul]

/-- Stitz-Zeager Exercise 5.1.26: `(h∘f∘g)(x) = |-2√x| = 2√x` for `x ≥ 0` (`f(x) = -2x`, `g = √`, `h = |·|`). -/
@[kb "stitzzeager2013" "Exercise 5.1.26, p. 382"]
theorem exer_5_1_26 : ∀ x : ℝ, |-2 * Real.sqrt x| = 2 * Real.sqrt x := by
  intro x
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg x)]; norm_num

/-- Stitz-Zeager Exercise 5.1.28: `(g∘h∘f)(x) = √|-2x| = √(2|x|)` for every real `x`. -/
@[kb "stitzzeager2013" "Exercise 5.1.28, p. 382"]
theorem exer_5_1_28 : ∀ x : ℝ, Real.sqrt |-2 * x| = Real.sqrt (2 * |x|) := by
  intro x
  rw [abs_mul]; norm_num

/-- Stitz-Zeager Exercise 5.1.30: `(f∘g∘h)(x) = -2√|x|`, defined for every real `x` (`f(x) = -2x`, `g = √`,
`h = |·|`); it is `-2 · g(h x)` and always `≤ 0`. -/
@[kb "stitzzeager2013" "Exercise 5.1.30, p. 382"]
theorem exer_5_1_30 : ∀ x : ℝ, (fun y : ℝ => -2 * y) (Real.sqrt (|x|)) = -2 * Real.sqrt |x| ∧
    -2 * Real.sqrt |x| ≤ 0 := by
  intro x
  exact ⟨rfl, by linarith [Real.sqrt_nonneg |x|]⟩

/-! ### Decompositions (31-43) -/

/-- Stitz-Zeager Exercise 5.1.31: `p(x) = (2x+3)³ = (g∘f)(x)` with `f(x) = 2x+3`, `g(x) = x³`. -/
@[kb "stitzzeager2013" "Exercise 5.1.31, p. 382"]
theorem exer_5_1_31 : ∀ x : ℝ, (2 * x + 3) ^ 3 = ((fun y : ℝ => y ^ 3) ∘ (fun y : ℝ => 2 * y + 3)) x :=
  fun _ => rfl

/-- Stitz-Zeager Exercise 5.1.32: `P(x) = (x²-x+1)⁵ = (g∘f)(x)` with `f(x) = x²-x+1`, `g(x) = x⁵`. -/
@[kb "stitzzeager2013" "Exercise 5.1.32, p. 382"]
theorem exer_5_1_32 :
    ∀ x : ℝ, (x ^ 2 - x + 1) ^ 5 = ((fun y : ℝ => y ^ 5) ∘ (fun y : ℝ => y ^ 2 - y + 1)) x :=
  fun _ => rfl

/-- Stitz-Zeager Exercise 5.1.33: `h(x) = √(2x-1) = (g∘f)(x)` with `f(x) = 2x-1`, `g = √`. -/
@[kb "stitzzeager2013" "Exercise 5.1.33, p. 382"]
theorem exer_5_1_33 : ∀ x : ℝ, Real.sqrt (2 * x - 1) = (Real.sqrt ∘ (fun y : ℝ => 2 * y - 1)) x :=
  fun _ => rfl

/-- Stitz-Zeager Exercise 5.1.34: `H(x) = |7-3x| = (g∘f)(x)` with `f(x) = 7-3x`, `g(x) = |x|`. -/
@[kb "stitzzeager2013" "Exercise 5.1.34, p. 382"]
theorem exer_5_1_34 : ∀ x : ℝ, |7 - 3 * x| = ((fun y : ℝ => |y|) ∘ (fun y : ℝ => 7 - 3 * y)) x :=
  fun _ => rfl

/-- Stitz-Zeager Exercise 5.1.35: `r(x) = 2/(5x+1) = (g∘f)(x)` with `f(x) = 5x+1`, `g(x) = 2/x`. -/
@[kb "stitzzeager2013" "Exercise 5.1.35, p. 382"]
theorem exer_5_1_35 : ∀ x : ℝ, 2 / (5 * x + 1) = ((fun y : ℝ => 2 / y) ∘ (fun y : ℝ => 5 * y + 1)) x :=
  fun _ => rfl

/-- Stitz-Zeager Exercise 5.1.36: `R(x) = 7/(x²-1) = (g∘f)(x)` with `f(x) = x²-1`, `g(x) = 7/x`. -/
@[kb "stitzzeager2013" "Exercise 5.1.36, p. 382"]
theorem exer_5_1_36 : ∀ x : ℝ, 7 / (x ^ 2 - 1) = ((fun y : ℝ => 7 / y) ∘ (fun y : ℝ => y ^ 2 - 1)) x :=
  fun _ => rfl

/-- Stitz-Zeager Exercise 5.1.37: `q(x) = (|x|+1)/(|x|-1) = (g∘f)(x)` with `f(x) = |x|`, `g(x) = (x+1)/(x-1)`. -/
@[kb "stitzzeager2013" "Exercise 5.1.37, p. 382"]
theorem exer_5_1_37 : ∀ x : ℝ, (|x| + 1) / (|x| - 1) =
    ((fun y : ℝ => (y + 1) / (y - 1)) ∘ (fun y : ℝ => |y|)) x :=
  fun _ => rfl

/-- Stitz-Zeager Exercise 5.1.38: `Q(x) = (2x³+1)/(x³-1) = (g∘f)(x)` with `f(x) = x³`, `g(x) = (2x+1)/(x-1)`. -/
@[kb "stitzzeager2013" "Exercise 5.1.38, p. 382"]
theorem exer_5_1_38 : ∀ x : ℝ, (2 * x ^ 3 + 1) / (x ^ 3 - 1) =
    ((fun y : ℝ => (2 * y + 1) / (y - 1)) ∘ (fun y : ℝ => y ^ 3)) x :=
  fun _ => rfl

/-- Stitz-Zeager Exercise 5.1.39: `v(x) = (2x+1)/(3-4x) = (g∘f)(x)` with `f(x) = 2x`, `g(x) = (x+1)/(3-2x)`. -/
@[kb "stitzzeager2013" "Exercise 5.1.39, p. 382"]
theorem exer_5_1_39 : ∀ x : ℝ, (2 * x + 1) / (3 - 4 * x) =
    ((fun y : ℝ => (y + 1) / (3 - 2 * y)) ∘ (fun y : ℝ => 2 * y)) x := by
  intro x; simp only [Function.comp]; ring_nf

/-- Stitz-Zeager Exercise 5.1.40: `w(x) = x²/(x⁴+1) = (g∘f)(x)` with `f(x) = x²`, `g(x) = x/(x²+1)`. -/
@[kb "stitzzeager2013" "Exercise 5.1.40, p. 382"]
theorem exer_5_1_40 : ∀ x : ℝ, x ^ 2 / (x ^ 4 + 1) =
    ((fun y : ℝ => y / (y ^ 2 + 1)) ∘ (fun y : ℝ => y ^ 2)) x := by
  intro x; simp only [Function.comp]; ring_nf

/-- Stitz-Zeager Exercise 5.1.41: `F(x) = √((x³+6)/(x³-9)) = h(g(f(x)))` with `f(x) = x³`, `g(x) = (x+6)/(x-9)`,
`h = √`. -/
@[kb "stitzzeager2013" "Exercise 5.1.41, p. 382"]
theorem exer_5_1_41 : ∀ x : ℝ, Real.sqrt ((x ^ 3 + 6) / (x ^ 3 - 9)) =
    (Real.sqrt ∘ (fun y : ℝ => (y + 6) / (y - 9)) ∘ (fun y : ℝ => y ^ 3)) x :=
  fun _ => rfl

/-- Stitz-Zeager Exercise 5.1.42: `F(x) = 3√(-x+2) - 4 = k(j(f(h(g(x)))))` with `g(x) = -x`, `h(x) = x+2`,
`f = √`, `j(x) = 3x`, `k(x) = x-4`. -/
@[kb "stitzzeager2013" "Exercise 5.1.42, p. 382"]
theorem exer_5_1_42 : ∀ x : ℝ, 3 * Real.sqrt (-x + 2) - 4 =
    ((fun y : ℝ => y - 4) ∘ (fun y : ℝ => 3 * y) ∘ Real.sqrt ∘ (fun y : ℝ => y + 2) ∘ (fun y : ℝ => -y)) x :=
  fun _ => rfl

/-! ### Finite functions (44-55) -/

/-- The finite function `f` of Exercises 5.1.44-5.1.55, as a lookup table. -/
def ch5W7FinF (a : ℤ) : Option ℤ := List.lookup a [(-3, 4), (-2, 2), (-1, 0), (0, 1), (1, 3), (2, 4), (3, -1)]

/-- The finite function `g` of Exercises 5.1.44-5.1.55, as a lookup table. -/
def ch5W7FinG (a : ℤ) : Option ℤ := List.lookup a [(-3, -2), (-2, 0), (-1, -4), (0, 0), (1, -3), (2, 1), (3, 2)]

/-- Stitz-Zeager Exercise 5.1.44: `f(g(3)) = f(2) = 4`. -/
@[kb "stitzzeager2013" "Exercise 5.1.44, p. 382"]
theorem exer_5_1_44 : (ch5W7FinG 3).bind ch5W7FinF = some 4 := by decide

/-- Stitz-Zeager Exercise 5.1.45: `g(-1) = -4`, which is not in the domain of `f`, so `f(g(-1))` is undefined. -/
@[kb "stitzzeager2013" "Exercise 5.1.45, p. 382"]
theorem exer_5_1_45 : (ch5W7FinG (-1)).bind ch5W7FinF = none := by decide

/-- Stitz-Zeager Exercise 5.1.46: `(f∘f)(0) = f(1) = 3`. -/
@[kb "stitzzeager2013" "Exercise 5.1.46, p. 382"]
theorem exer_5_1_46 : (ch5W7FinF 0).bind ch5W7FinF = some 3 := by decide

/-- Stitz-Zeager Exercise 5.1.47: `(f∘g)(-3) = f(-2) = 2`. -/
@[kb "stitzzeager2013" "Exercise 5.1.47, p. 382"]
theorem exer_5_1_47 : (ch5W7FinG (-3)).bind ch5W7FinF = some 2 := by decide

/-- Stitz-Zeager Exercise 5.1.48: `(g∘f)(3) = g(-1) = -4`. -/
@[kb "stitzzeager2013" "Exercise 5.1.48, p. 382"]
theorem exer_5_1_48 : (ch5W7FinF 3).bind ch5W7FinG = some (-4) := by decide

/-- Stitz-Zeager Exercise 5.1.49: `f(-3) = 4`, not in the domain of `g`, so `g(f(-3))` is undefined. -/
@[kb "stitzzeager2013" "Exercise 5.1.49, p. 382"]
theorem exer_5_1_49 : (ch5W7FinF (-3)).bind ch5W7FinG = none := by decide

/-- Stitz-Zeager Exercise 5.1.50: `(g∘g)(-2) = g(0) = 0`. -/
@[kb "stitzzeager2013" "Exercise 5.1.50, p. 383"]
theorem exer_5_1_50 : (ch5W7FinG (-2)).bind ch5W7FinG = some 0 := by decide

/-- Stitz-Zeager Exercise 5.1.51: `(g∘f)(-2) = g(2) = 1`. -/
@[kb "stitzzeager2013" "Exercise 5.1.51, p. 383"]
theorem exer_5_1_51 : (ch5W7FinF (-2)).bind ch5W7FinG = some 1 := by decide

/-- Stitz-Zeager Exercise 5.1.52: `g(f(g(0))) = g(f(0)) = g(1) = -3`. -/
@[kb "stitzzeager2013" "Exercise 5.1.52, p. 383"]
theorem exer_5_1_52 :
    (((ch5W7FinG 0).bind ch5W7FinF).bind ch5W7FinG) = some (-3) := by decide

/-- Stitz-Zeager Exercise 5.1.53: `f(f(f(-1))) = f(f(0)) = f(1) = 3`. -/
@[kb "stitzzeager2013" "Exercise 5.1.53, p. 383"]
theorem exer_5_1_53 : (((ch5W7FinF (-1)).bind ch5W7FinF).bind ch5W7FinF) = some 3 := by
  decide

/-- Stitz-Zeager Exercise 5.1.54: `f(f(f(f(f(1))))) = 3`. -/
@[kb "stitzzeager2013" "Exercise 5.1.54, p. 383"]
theorem exer_5_1_54 :
    (Nat.iterate (fun o : Option ℤ => o.bind ch5W7FinF) 5 (some 1)) = some 3 := by decide

/-! ### Applications (62, 63) -/

/-- Stitz-Zeager Exercise 5.1.62: `V(x) = x³` and `x(t) = t+1` give `V(x(t)) = (t+1)³`. -/
@[kb "stitzzeager2013" "Exercise 5.1.62, p. 383"]
theorem exer_5_1_62 (V x : ℝ → ℝ) (hV : V = fun s => s ^ 3) (hx : x = fun t => t + 1) :
    ∀ t, (V ∘ x) t = (t + 1) ^ 3 := by
  subst hV hx; intro t; rfl

end UndergradKB.Precalculus.Course
