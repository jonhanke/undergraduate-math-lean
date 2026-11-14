import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.Radicals

/-! # Course layer, Chapter 1 (Stitz-Zeager): exercises with the book's answers (wave 8), Section 1.7, definite facts
of exercises that print no answer -/

namespace UndergradKB.Precalculus.Course

open UndergradKB.Precalculus

/-- Stitz-Zeager Exercise 1.7.65: horizontal scalings as vertical scalings: `(2x)³ = 8x³`, `|5x| = 5|x|`,
`∛(27x) = 3∛x`, `(x/2)² = x²/4`; and with the sign flipped: `(-2x)³ = -8x³`, `|-5x| = 5|x|`, `∛(-27x) = -3∛x`,
`(-x/2)² = x²/4`. -/
@[kb "stitzzeager2013" "Exercise 1.7.65, p. 155"]
theorem exer_1_7_65 :
    ((∀ x : ℝ, (2 * x) ^ 3 = 8 * x ^ 3) ∧ (∀ x : ℝ, |5 * x| = 5 * |x|) ∧
      (∀ x : ℝ, principalRoot 3 (27 * x) = 3 * principalRoot 3 x) ∧
      (∀ x : ℝ, (1 / 2 * x) ^ 2 = 1 / 4 * x ^ 2)) ∧
    ((∀ x : ℝ, (-2 * x) ^ 3 = -8 * x ^ 3) ∧ (∀ x : ℝ, |-5 * x| = 5 * |x|) ∧
      (∀ x : ℝ, principalRoot 3 (-27 * x) = -3 * principalRoot 3 x) ∧
      (∀ x : ℝ, (-(1 / 2) * x) ^ 2 = 1 / 4 * x ^ 2)) := by
  have h27 : principalRoot 3 27 = 3 :=
    (principalRoot_unique (n := 3) (by norm_num) (Or.inl (by decide)) (Or.inl (by decide))
      (by norm_num)).symm
  have hm27 : principalRoot 3 (-27) = -3 :=
    (principalRoot_unique (n := 3) (by norm_num) (Or.inl (by decide)) (Or.inl (by decide))
      (by norm_num)).symm
  refine ⟨⟨fun x => by ring, fun x => ?_, fun x => ?_, fun x => by ring⟩,
    ⟨fun x => by ring, fun x => ?_, fun x => ?_, fun x => by ring⟩⟩
  · rw [abs_mul]; norm_num
  · rw [principalRoot_mul (by norm_num) (Or.inl (by decide)), h27]
  · rw [abs_mul]; norm_num
  · rw [principalRoot_mul (by norm_num) (Or.inl (by decide)), hm27]

/-- Stitz-Zeager Exercise 1.7.67: reflecting an even function across the `y`-axis gives back the same function. -/
@[kb "stitzzeager2013" "Exercise 1.7.67, p. 155"]
theorem exer_1_7_67 (f : ℝ → ℝ) (hf : ∀ x, f (-x) = f x) : (fun x => f (-x)) = f := by
  funext x; exact hf x

/-- Stitz-Zeager Exercise 1.7.68: reflecting an odd function across the `y`-axis gives the same graph as reflecting
it across the `x`-axis: `f(-x) = -f(x)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.68, p. 155"]
theorem exer_1_7_68 (f : ℝ → ℝ) (hf : ∀ x, f (-x) = -f x) : (fun x => f (-x)) = fun x => -f x := by
  funext x; exact hf x

/-- Stitz-Zeager Exercise 1.7.69: reflecting an even function across the `x`-axis gives `-f`, again an even
function. -/
@[kb "stitzzeager2013" "Exercise 1.7.69, p. 155"]
theorem exer_1_7_69 (f : ℝ → ℝ) (hf : ∀ x, f (-x) = f x) :
    ∀ x, (fun t => -f t) (-x) = (fun t => -f t) x := by
  intro x; simp only [hf]

/-- Stitz-Zeager Exercise 1.7.70: reflecting an odd function across the `x`-axis gives the same graph as reflecting
it across the `y`-axis: `-f(x) = f(-x)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.70, p. 155"]
theorem exer_1_7_70 (f : ℝ → ℝ) (hf : ∀ x, f (-x) = -f x) : (fun x => -f x) = fun x => f (-x) := by
  funext x; exact (hf x).symm

/-- Stitz-Zeager Exercise 1.7.71: symmetry about the origin means reflecting the graph across the `x`-axis and then the
`y`-axis (the function `x ↦ -f(-x)`) gives back the same graph: `f` is odd iff `-f(-x) = f(x)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.71, p. 155"]
theorem exer_1_7_71 (f : ℝ → ℝ) : (∀ x, f (-x) = -f x) ↔ (fun x => -f (-x)) = f := by
  constructor
  · intro h; funext x; rw [h]; simp
  · intro h x
    have := congrFun h (-x)
    simp only [neg_neg] at this
    exact this.symm

end UndergradKB.Precalculus.Course
