import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 1 (Stitz-Zeager): exercises with the book's answers (wave 8), Sections 1.1-1.6, definite
facts of exercises that print no answer -/

namespace UndergradKB.Precalculus.Course

open Set Filter Topology

/-- Stitz-Zeager Exercise 1.1.38: `D(1,4)` completes `A(-3,1)`, `B(4,0)`, `C(0,-3)` to a square: the four sides
`CA, AD, DB, BC` have squared length `25`, the diagonals `AB` and `CD` have squared length `50`. -/
@[kb "stitzzeager2013" "Exercise 1.1.38, p. 28"]
theorem exer_1_1_38 :
    ((-3 - 0) ^ 2 + (1 - (-3)) ^ 2 = (25 : ℝ)) ∧ ((-3 - 1) ^ 2 + (1 - 4) ^ 2 = (25 : ℝ)) ∧
      ((1 - 4) ^ 2 + (4 - 0) ^ 2 = (25 : ℝ)) ∧ ((4 - 0) ^ 2 + (0 - (-3)) ^ 2 = (25 : ℝ)) ∧
      ((-3 - 4) ^ 2 + (1 - 0) ^ 2 = (50 : ℝ)) ∧ ((0 - 1) ^ 2 + (-3 - 4) ^ 2 = (50 : ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

/-- Stitz-Zeager Exercise 1.1.39: the interval `(0,1)` contains infinitely many numbers. -/
@[kb "stitzzeager2013" "Exercise 1.1.39, p. 28"]
theorem exer_1_1_39 : (Ioo (0 : ℝ) 1).Infinite := Set.Ioo_infinite (by norm_num)

/-- Stitz-Zeager Exercise 1.2.37: in the relation of pairs (odd integer, even integer), `(1,0)` and `(3,2)` belong,
`(2,0)` and `(1,1)` do not. -/
@[kb "stitzzeager2013" "Exercise 1.2.37, p. 43"]
theorem exer_1_2_37 :
    let R : Set (ℤ × ℤ) := {p | Odd p.1 ∧ Even p.2}
    ((1, 0) ∈ R ∧ (3, 2) ∈ R) ∧ ((2, 0) ∉ R ∧ (1, 1) ∉ R) := by
  intro R
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · show Odd (1 : ℤ) ∧ Even (0 : ℤ)
    decide
  · show Odd (3 : ℤ) ∧ Even (2 : ℤ)
    decide
  · show ¬ (Odd (2 : ℤ) ∧ Even (0 : ℤ))
    decide
  · show ¬ (Odd (1 : ℤ) ∧ Even (1 : ℤ))
    decide

/-- Stitz-Zeager Exercise 1.2.38: in `{(x,1) | x irrational}`, the points `(√2,1)` and `(π,1)` belong, while
`(1,1)` and `(√2,2)` do not. -/
@[kb "stitzzeager2013" "Exercise 1.2.38, p. 43"]
theorem exer_1_2_38 :
    let R : Set (ℝ × ℝ) := {p | p.2 = 1 ∧ Irrational p.1}
    ((√2, 1) ∈ R ∧ (Real.pi, 1) ∈ R) ∧ ((1, 1) ∉ R ∧ (√2, 2) ∉ R) := by
  intro R
  refine ⟨⟨⟨rfl, irrational_sqrt_two⟩, ⟨rfl, irrational_pi⟩⟩, ?_, ?_⟩
  · intro h
    exact Rat.not_irrational 1 (by simpa using h.2)
  · intro h
    have := h.1
    norm_num at this

/-- Stitz-Zeager Exercise 1.3.50: on the folium `x³ + y³ = 3xy` the line `x = 1` meets two different points
(it fails the vertical line test). -/
@[kb "stitzzeager2013" "Exercise 1.3.50, p. 64"]
theorem exer_1_3_50 :
    ∃ y₁ y₂ : ℝ, y₁ ≠ y₂ ∧ (1 : ℝ) ^ 3 + y₁ ^ 3 = 3 * 1 * y₁ ∧ (1 : ℝ) ^ 3 + y₂ ^ 3 = 3 * 1 * y₂ := by
  have hc : Continuous (fun y : ℝ => y ^ 3 - 3 * y + 1) := by fun_prop
  obtain ⟨y₁, h1, e1⟩ := intermediate_value_Ioo (show (-2 : ℝ) ≤ -1 by norm_num) hc.continuousOn
    (show (0 : ℝ) ∈ Ioo ((fun y : ℝ => y ^ 3 - 3 * y + 1) (-2)) ((fun y : ℝ => y ^ 3 - 3 * y + 1) (-1)) by
      constructor <;> norm_num)
  obtain ⟨y₂, h2, e2⟩ := intermediate_value_Ioo' (show (0 : ℝ) ≤ 1 by norm_num) hc.continuousOn
    (show (0 : ℝ) ∈ Ioo ((fun y : ℝ => y ^ 3 - 3 * y + 1) 1) ((fun y : ℝ => y ^ 3 - 3 * y + 1) 0) by
      constructor <;> norm_num)
  simp only at e1 e2
  refine ⟨y₁, y₂, ?_, by linarith, by linarith⟩
  intro h
  have := h1.2
  have := h2.1
  linarith

/-- Stitz-Zeager Exercise 1.3.51: on `x⁴ = x² + y²` the line `x = 2` meets the two points `y = ±2√3`. -/
@[kb "stitzzeager2013" "Exercise 1.3.51, p. 64"]
theorem exer_1_3_51 :
    ∃ y₁ y₂ : ℝ, y₁ ≠ y₂ ∧ (2 : ℝ) ^ 4 = 2 ^ 2 + y₁ ^ 2 ∧ (2 : ℝ) ^ 4 = 2 ^ 2 + y₂ ^ 2 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hp : 0 < √3 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨2 * √3, -(2 * √3), ?_, ?_, ?_⟩
  · intro h; linarith
  · nlinarith
  · nlinarith

/-- Stitz-Zeager Exercise 1.3.52: on `y² = x³ + 3x²` the line `x = 1` meets the two points `y = ±2`. -/
@[kb "stitzzeager2013" "Exercise 1.3.52, p. 64"]
theorem exer_1_3_52 :
    ∃ y₁ y₂ : ℝ, y₁ ≠ y₂ ∧ y₁ ^ 2 = (1 : ℝ) ^ 3 + 3 * 1 ^ 2 ∧ y₂ ^ 2 = (1 : ℝ) ^ 3 + 3 * 1 ^ 2 :=
  ⟨2, -2, by norm_num, by norm_num, by norm_num⟩

/-- Stitz-Zeager Exercise 1.4.76: `f(x) = kx` satisfies `f(a+b) = f(a) + f(b)`, while `x²`, `√x`, `3x + 7` and
`1/x` fail it (at `a = b = 1`). -/
@[kb "stitzzeager2013" "Exercise 1.4.76, p. 79"]
theorem exer_1_4_76 :
    (∀ k a b : ℝ, k * (a + b) = k * a + k * b) ∧ ¬ ((1 + 1 : ℝ) ^ 2 = 1 ^ 2 + 1 ^ 2) ∧
      ¬ (√((1 : ℝ) + 1) = √1 + √1) ∧ ¬ (3 * ((1 : ℝ) + 1) + 7 = (3 * 1 + 7) + (3 * 1 + 7)) ∧
      ¬ (1 / ((1 : ℝ) + 1) = 1 / 1 + 1 / 1) := by
  refine ⟨fun k a b => by ring, by norm_num, ?_, by norm_num, by norm_num⟩
  intro h
  rw [Real.sqrt_one] at h
  have h2 : (1 : ℝ) + 1 = 2 := by norm_num
  rw [h2] at h
  have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  rw [h] at this
  norm_num at this

/-- Stitz-Zeager Exercise 1.6.93: the greatest integer function has a local maximum at every real number, a local
minimum at every non-integer, and no local minimum at an integer. -/
@[kb "stitzzeager2013" "Exercise 1.6.93, p. 123"]
theorem exer_1_6_93 :
    (∀ x : ℝ, IsLocalMax (fun t : ℝ => (⌊t⌋ : ℝ)) x) ∧
      (∀ x : ℝ, (∀ n : ℤ, x ≠ n) → IsLocalMin (fun t : ℝ => (⌊t⌋ : ℝ)) x) ∧
      (∀ n : ℤ, ¬ IsLocalMin (fun t : ℝ => (⌊t⌋ : ℝ)) n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    show ∀ᶠ y in 𝓝 x, (⌊y⌋ : ℝ) ≤ ⌊x⌋
    filter_upwards [Iio_mem_nhds (show x < (⌊x⌋ : ℝ) + 1 from Int.lt_floor_add_one x)] with y hy
    have h1 : ⌊y⌋ < ⌊x⌋ + 1 := Int.floor_lt.mpr (by push_cast; exact hy)
    have h2 : ⌊y⌋ ≤ ⌊x⌋ := by omega
    exact_mod_cast h2
  · intro x hx
    show ∀ᶠ y in 𝓝 x, (⌊x⌋ : ℝ) ≤ ⌊y⌋
    have hne : (⌊x⌋ : ℝ) ≠ x := fun h => hx ⌊x⌋ h.symm
    have hlt : (⌊x⌋ : ℝ) < x := lt_of_le_of_ne (Int.floor_le x) hne
    filter_upwards [Ioo_mem_nhds hlt (Int.lt_floor_add_one x)] with y hy
    have h1 : ⌊x⌋ ≤ ⌊y⌋ := Int.le_floor.mpr hy.1.le
    exact_mod_cast h1
  · intro n h
    have h1 : ∀ᶠ y in 𝓝[<] (n : ℝ), (⌊(n : ℝ)⌋ : ℝ) ≤ ⌊y⌋ := nhdsWithin_le_nhds h
    obtain ⟨y, hy, hyn⟩ := (h1.and eventually_mem_nhdsWithin).exists
    rw [Int.floor_intCast] at hy
    have hy' : n ≤ ⌊y⌋ := by exact_mod_cast hy
    have h3 : ⌊y⌋ < n := Int.floor_lt.mpr (by exact_mod_cast (show y < (n : ℝ) from hyn))
    omega

/-- Stitz-Zeager Exercise 1.6.96: the population model `P(t) = 150t/(t + 15)` stays below `150` for `t ≥ 0`, so it
never reaches `200`. -/
@[kb "stitzzeager2013" "Exercise 1.6.96, p. 123"]
theorem exer_1_6_96 (P : ℝ → ℝ) (hP : ∀ t, P t = 150 * t / (t + 15)) :
    (∀ t, 0 ≤ t → P t < 150) ∧ ∀ t, 0 ≤ t → P t ≠ 200 := by
  have h1 : ∀ t, 0 ≤ t → P t < 150 := by
    intro t ht
    rw [hP, div_lt_iff₀ (by linarith)]
    linarith
  exact ⟨h1, fun t ht h => by linarith [h1 t ht]⟩

/-- Stitz-Zeager Exercise 1.6.97: sums, differences, products and quotients of two even functions, of two odd
functions, and of an even and an odd function. -/
@[kb "stitzzeager2013" "Exercise 1.6.97, p. 123"]
theorem exer_1_6_97 :
    (∀ f g : ℝ → ℝ, (∀ x, f (-x) = f x) → (∀ x, g (-x) = g x) →
      (∀ x, f (-x) + g (-x) = f x + g x) ∧ (∀ x, f (-x) - g (-x) = f x - g x) ∧
      (∀ x, f (-x) * g (-x) = f x * g x) ∧ (∀ x, f (-x) / g (-x) = f x / g x)) ∧
    (∀ f g : ℝ → ℝ, (∀ x, f (-x) = -f x) → (∀ x, g (-x) = -g x) →
      (∀ x, f (-x) + g (-x) = -(f x + g x)) ∧ (∀ x, f (-x) - g (-x) = -(f x - g x)) ∧
      (∀ x, f (-x) * g (-x) = f x * g x) ∧ (∀ x, f (-x) / g (-x) = f x / g x)) ∧
    (∀ f g : ℝ → ℝ, (∀ x, f (-x) = f x) → (∀ x, g (-x) = -g x) →
      (∀ x, f (-x) * g (-x) = -(f x * g x)) ∧ (∀ x, f (-x) / g (-x) = -(f x / g x))) := by
  refine ⟨fun f g hf hg => ⟨fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_⟩,
    fun f g hf hg => ⟨fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_⟩,
    fun f g hf hg => ⟨fun x => ?_, fun x => ?_⟩⟩
  · rw [hf, hg]
  · rw [hf, hg]
  · rw [hf, hg]
  · rw [hf, hg]
  · rw [hf, hg]; ring
  · rw [hf, hg]; ring
  · rw [hf, hg]; ring
  · rw [hf, hg, neg_div_neg_eq]
  · rw [hf, hg]; ring
  · rw [hf, hg, div_neg]

end UndergradKB.Precalculus.Course
