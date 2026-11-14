import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Basic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 2 (Stitz-Zeager): exercises with the book's answers (wave 8), Sections 2.1, 2.2, 2.4 -/

namespace UndergradKB.Precalculus.Course

open Set

/-! ## Section 2.1 -/

/-- Stitz-Zeager Exercise 2.1.63: the line parallel to `y = 6` through `(3,-2)` is `y = -2`. -/
@[kb "stitzzeager2013" "Exercise 2.1.63, p. 179"]
theorem exer_2_1_63 (m b : ℝ) : (m = 0 ∧ m * 3 + b = -2) ↔ (m = 0 ∧ b = -2) := by
  constructor
  · rintro ⟨h1, h2⟩; subst h1; constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 2.1.64: the line parallel to the vertical line `x = 1` through `(-5,0)` is the vertical
line `x = -5`; it contains the point, is `{(-5, y)}`, and misses `x = 1`. -/
@[kb "stitzzeager2013" "Exercise 2.1.64, p. 179"]
theorem exer_2_1_64 :
    ((-5, 0) ∈ {p : ℝ × ℝ | p.1 = -5}) ∧ {p : ℝ × ℝ | p.1 = -5} = range (fun y : ℝ => (-5, y)) ∧
      Disjoint {p : ℝ × ℝ | p.1 = 1} {p : ℝ × ℝ | p.1 = -5} := by
  refine ⟨rfl, ?_, ?_⟩
  · ext p
    simp only [mem_ofPred_eq, mem_range]
    constructor
    · intro h; exact ⟨p.2, Prod.ext h.symm rfl⟩
    · rintro ⟨y, rfl⟩; rfl
  · rw [Set.disjoint_left]
    intro p h1 h2
    simp only [mem_ofPred_eq] at h1 h2
    linarith

/-- Stitz-Zeager Exercise 2.1.69: the line through `(3,-2)` perpendicular to the horizontal line `y = 6` is the
vertical line `x = 3`: it contains the point, meets `y = 6` only at `(3,6)`, and its direction `(0,1)` is orthogonal
to the direction `(1,0)` of `y = 6`. -/
@[kb "stitzzeager2013" "Exercise 2.1.69, p. 179"]
theorem exer_2_1_69 :
    ((3, -2) ∈ {p : ℝ × ℝ | p.1 = 3}) ∧ {p : ℝ × ℝ | p.1 = 3} ∩ {p : ℝ × ℝ | p.2 = 6} = {(3, 6)} ∧
      (0 : ℝ) * 1 + 1 * 0 = 0 := by
  refine ⟨rfl, ?_, by norm_num⟩
  ext p
  simp only [mem_inter_iff, mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact Prod.ext h1 h2
  · rintro rfl; exact ⟨rfl, rfl⟩

/-- Stitz-Zeager Exercise 2.1.70: the line through `(-5,0)` perpendicular to the vertical line `x = 1` is the
horizontal line `y = 0`: it contains the point, meets `x = 1` only at `(1,0)`, and its direction `(1,0)` is
orthogonal to the direction `(0,1)` of `x = 1`. -/
@[kb "stitzzeager2013" "Exercise 2.1.70, p. 179"]
theorem exer_2_1_70 :
    ((-5, 0) ∈ {p : ℝ × ℝ | p.2 = 0}) ∧ {p : ℝ × ℝ | p.2 = 0} ∩ {p : ℝ × ℝ | p.1 = 1} = {(1, 0)} ∧
      (1 : ℝ) * 0 + 0 * 1 = 0 := by
  refine ⟨rfl, ?_, by norm_num⟩
  ext p
  simp only [mem_inter_iff, mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact Prod.ext h2 h1
  · rintro rfl; exact ⟨rfl, rfl⟩

/-- Stitz-Zeager Exercise 2.1.71: for the points `O(0,0)`, `P(1,m₁)`, `Q(1,m₂)`, the Pythagorean relation
`d₁² + d₂² = d₃²` holds exactly when `m₁ m₂ = -1` (the perpendicularity criterion for slopes). -/
@[kb "stitzzeager2013" "Exercise 2.1.71, p. 179"]
theorem exer_2_1_71 (m₁ m₂ : ℝ) (_h1 : 0 < m₁) (_h2 : m₂ < 0) :
    (√((1 - 0) ^ 2 + (m₁ - 0) ^ 2)) ^ 2 + (√((1 - 0) ^ 2 + (m₂ - 0) ^ 2)) ^ 2 =
        (√((1 - 1) ^ 2 + (m₁ - m₂) ^ 2)) ^ 2 ↔ m₁ * m₂ = -1 := by
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  constructor <;> intro h <;> nlinarith

/-- Stitz-Zeager Exercise 2.1.73(b): the point-slope form `y - y₀ = m (x - x₀)` is obtained from the identity
function `I(x) = x` by a shift right by `x₀`, a vertical scaling by `m`, and a shift up by `y₀`. -/
@[kb "stitzzeager2013" "Exercise 2.1.73, p. 180"]
theorem exer_2_1_73 (I : ℝ → ℝ) (hI : ∀ x, I x = x) (m x₀ y₀ : ℝ) :
    (∀ x, ((fun t => t + y₀) ∘ (fun t => m * t) ∘ I ∘ (fun t => t - x₀)) x = y₀ + m * (x - x₀)) ∧
      ∀ x y : ℝ, y = ((fun t => t + y₀) ∘ (fun t => m * t) ∘ I ∘ (fun t => t - x₀)) x ↔
        y - y₀ = m * (x - x₀) := by
  have key : ∀ x, ((fun t => t + y₀) ∘ (fun t => m * t) ∘ I ∘ (fun t => t - x₀)) x = y₀ + m * (x - x₀) := by
    intro x; simp only [Function.comp, hI]; ring
  refine ⟨key, fun x y => ?_⟩
  rw [key]; constructor <;> intro h <;> linarith

/-! ## Section 2.2 -/

/-- Stitz-Zeager Exercise 2.2.1: `|x| = 6` exactly when `x = 6` or `x = -6`. -/
@[kb "stitzzeager2013" "Exercise 2.2.1, p. 195"]
theorem exer_2_2_1 : {x : ℝ | |x| = 6} = {-6, 6} := by
  ext x
  simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · intro h
    rcases abs_cases x with ⟨h1, _⟩ | ⟨h1, _⟩
    · right; linarith
    · left; linarith
  · rintro (rfl | rfl) <;> norm_num

/-- Stitz-Zeager Exercise 2.2.34 (printed as 35 in the Answers): the V-shaped graph with zeros `±4` and
`y`-intercept `4` is that of `f(x) = ||x| - 4|`: `f(0) = 4`, zeros exactly `-4` and `4`, slope `-1` left of `-4`,
`+1` on `[-4, 0]`, `-1` on `[0, 4]`, `+1` right of `4`. -/
@[kb "stitzzeager2013" "Exercise 2.2.34, p. 195"]
theorem exer_2_2_34 (f : ℝ → ℝ) (hf : ∀ x, f x = |(|x| - 4)|) :
    f 0 = 4 ∧ {x : ℝ | f x = 0} = {-4, 4} ∧ (∀ x, x ≤ -4 → f x = -x - 4) ∧
      (∀ x ∈ Icc (-4 : ℝ) 0, f x = x + 4) ∧ (∀ x ∈ Icc (0 : ℝ) 4, f x = 4 - x) ∧ (∀ x, 4 ≤ x → f x = x - 4) := by
  refine ⟨by rw [hf]; norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · ext x
    simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff, hf, abs_eq_zero, sub_eq_zero]
    constructor
    · intro h
      rcases abs_cases x with ⟨h1, _⟩ | ⟨h1, _⟩
      · right; linarith
      · left; linarith
    · rintro (rfl | rfl) <;> norm_num
  · intro x hx
    rw [hf, abs_of_nonpos (by linarith : x ≤ 0), abs_of_nonneg (by linarith)]
  · rintro x ⟨h1, h2⟩
    rw [hf, abs_of_nonpos h2, abs_of_nonpos (by linarith)]; ring
  · rintro x ⟨h1, h2⟩
    rw [hf, abs_of_nonneg h1, abs_of_nonpos (by linarith)]; ring
  · intro x hx
    rw [hf, abs_of_nonneg (by linarith : (0 : ℝ) ≤ x), abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - 4)]

/-- Stitz-Zeager Exercise 2.2.35: the power rule (for integer exponents), the quotient rule, and the criterion
`|x| = c` for `c > 0` (Theorem 2.1, parts 2, 3 and 5). -/
@[kb "stitzzeager2013" "Exercise 2.2.35, p. 195"]
theorem exer_2_2_35 :
    (∀ (a : ℝ) (n : ℤ), |a ^ n| = |a| ^ n) ∧ (∀ a b : ℝ, b ≠ 0 → |a / b| = |a| / |b|) ∧
      (∀ x c : ℝ, 0 < c → (|x| = c ↔ x = c ∨ -x = c)) := by
  refine ⟨fun a n => abs_zpow a n, fun a b _ => abs_div a b, fun x c hc => ?_⟩
  constructor
  · intro h
    rcases abs_cases x with ⟨h1, _⟩ | ⟨h1, _⟩
    · left; linarith
    · right; linarith
  · rintro (rfl | h)
    · exact abs_of_pos hc
    · rw [← abs_neg, h]; exact abs_of_pos hc

/-! ## Section 2.4 -/

/-- Stitz-Zeager Exercise 2.4.51: `|x| ≤ c` is `-c ≤ x ≤ c` for `c > 0`; `|x| < c` has no solution for `c ≤ 0` and
`|x| ≤ c` none for `c < 0`; `|x| > c` is `x < -c` or `x > c` for `c ≥ 0` (Theorem 2.4, parts 2, 3, 4). -/
@[kb "stitzzeager2013" "Exercise 2.4.51, p. 233"]
theorem exer_2_4_51 :
    (∀ x c : ℝ, 0 < c → (|x| ≤ c ↔ -c ≤ x ∧ x ≤ c)) ∧
      ((∀ x c : ℝ, c ≤ 0 → ¬ |x| < c) ∧ (∀ x c : ℝ, c < 0 → ¬ |x| ≤ c)) ∧
      (∀ x c : ℝ, 0 ≤ c → (c < |x| ↔ x < -c ∨ c < x)) := by
  refine ⟨fun x c _ => abs_le, ⟨fun x c hc h => ?_, fun x c hc h => ?_⟩, fun x c _ => ?_⟩
  · linarith [abs_nonneg x]
  · linarith [abs_nonneg x]
  · rw [lt_abs]
    constructor
    · rintro (h | h)
      · right; exact h
      · left; linarith
    · rintro (h | h)
      · right; linarith
      · left; exact h

end UndergradKB.Precalculus.Course
