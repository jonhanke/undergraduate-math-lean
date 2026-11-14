import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 4 (Stitz-Zeager): exercises with the book's answers (wave 8), Section 4.2, definite facts
of exercises that print no answer -/

namespace UndergradKB.Precalculus.Course

open Set Filter Topology

/-- Stitz-Zeager Exercise 4.2.21: for `c ≠ 0`, `(ax+b)/(cx+d) = a/c + ((bc-ad)/c²)/(x + d/c)`, a transformation of
`1/x` (shift left by `d/c`, scale by `(bc-ad)/c²`, shift up by `a/c`); when `bc = ad` the function is constant `a/c`
(so `bc - ad ≠ 0` is needed). -/
@[kb "stitzzeager2013" "Exercise 4.2.21, p. 345"]
theorem exer_4_2_21 (a b c d : ℝ) (hc : c ≠ 0) :
    (∀ x : ℝ, c * x + d ≠ 0 →
      (a * x + b) / (c * x + d) = a / c + ((b * c - a * d) / c ^ 2) / (x + d / c)) ∧
    (b * c = a * d → ∀ x : ℝ, c * x + d ≠ 0 → (a * x + b) / (c * x + d) = a / c) := by
  constructor
  · intro x hx
    have hx' : x + d / c ≠ 0 := by
      intro h
      apply hx
      have : c * (x + d / c) = 0 := by rw [h]; ring
      have h2 : c * (x + d / c) = c * x + d := by field_simp
      linarith
    have hx'' : x + d / c = (c * x + d) / c := by field_simp
    have hbc : (b * c - a * d) / c ^ 2 / ((c * x + d) / c) = (b * c - a * d) / (c * (c * x + d)) := by
      field_simp
    rw [hx'', hbc, div_add_div _ _ hc (mul_ne_zero hc hx), div_eq_div_iff hx (mul_ne_zero hc (mul_ne_zero hc hx))]
    ring
  · intro h x hx
    rw [div_eq_div_iff hx hc]
    linarith

/-- Stitz-Zeager Exercise 4.2.22: `p(x) = (4x + x³)/x` equals `4 + x²` for `x ≠ 0`, so its graph is that parabola
with a hole at `(0,4)`: `p(x) → 4` as `x → 0`, `x ≠ 0`. -/
@[kb "stitzzeager2013" "Exercise 4.2.22, p. 345"]
theorem exer_4_2_22 :
    (∀ x : ℝ, x ≠ 0 → (4 * x + x ^ 3) / x = 4 + x ^ 2) ∧
      Tendsto (fun x : ℝ => (4 * x + x ^ 3) / x) (𝓝[≠] 0) (𝓝 4) := by
  have key : ∀ x : ℝ, x ≠ 0 → (4 * x + x ^ 3) / x = 4 + x ^ 2 := by
    intro x hx; field_simp
  refine ⟨key, ?_⟩
  have h1 : Tendsto (fun x : ℝ => 4 + x ^ 2) (𝓝[≠] 0) (𝓝 4) := by
    have hc : Continuous (fun x : ℝ => 4 + x ^ 2) := by fun_prop
    have := (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
    simpa using this
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (key x hx).symm

/-- Stitz-Zeager Exercise 4.2.23: for `g(x) = (x⁴ - 8x³ + 24x² - 72x + 135)/(x³ - 9x² + 15x - 7)`: the numerator is
`(x-3)(x-5)(x²+9)` and the denominator `(x-1)²(x-7)`; the `x`-intercepts are `3` and `5`, the `y`-intercept is
`-135/7`, neither `1` nor `7` is a hole (numerator `80` and `464` there), and the slant asymptote is `y = x + 1`
(`g(x) = x + 1 + (18x² - 80x + 142)/(x³ - 9x² + 15x - 7)`). -/
@[kb "stitzzeager2013" "Exercise 4.2.23, p. 346"]
theorem exer_4_2_23 (g : ℝ → ℝ)
    (hg : ∀ x, g x = (x ^ 4 - 8 * x ^ 3 + 24 * x ^ 2 - 72 * x + 135) / (x ^ 3 - 9 * x ^ 2 + 15 * x - 7)) :
    (∀ x : ℝ, x ^ 4 - 8 * x ^ 3 + 24 * x ^ 2 - 72 * x + 135 = (x - 3) * (x - 5) * (x ^ 2 + 9)) ∧
      (∀ x : ℝ, x ^ 3 - 9 * x ^ 2 + 15 * x - 7 = (x - 1) ^ 2 * (x - 7)) ∧
      {x : ℝ | x ^ 3 - 9 * x ^ 2 + 15 * x - 7 ≠ 0 ∧ g x = 0} = {3, 5} ∧ g 0 = -135 / 7 ∧
      ((1 : ℝ) ^ 4 - 8 * 1 ^ 3 + 24 * 1 ^ 2 - 72 * 1 + 135 = 80) ∧
      ((7 : ℝ) ^ 4 - 8 * 7 ^ 3 + 24 * 7 ^ 2 - 72 * 7 + 135 = 464) ∧
      ∀ x : ℝ, x ^ 3 - 9 * x ^ 2 + 15 * x - 7 ≠ 0 →
        g x = (x + 1) + (18 * x ^ 2 - 80 * x + 142) / (x ^ 3 - 9 * x ^ 2 + 15 * x - 7) := by
  have hN : ∀ x : ℝ, x ^ 4 - 8 * x ^ 3 + 24 * x ^ 2 - 72 * x + 135 = (x - 3) * (x - 5) * (x ^ 2 + 9) := by
    intro x; ring
  have hD : ∀ x : ℝ, x ^ 3 - 9 * x ^ 2 + 15 * x - 7 = (x - 1) ^ 2 * (x - 7) := by
    intro x; ring
  refine ⟨hN, hD, ?_, by rw [hg]; norm_num, by norm_num, by norm_num, ?_⟩
  · ext x
    simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff, hg]
    constructor
    · rintro ⟨hx, h⟩
      rw [div_eq_zero_iff] at h
      rcases h with h | h
      · rw [hN] at h
        have h9 : x ^ 2 + 9 ≠ 0 := by positivity
        rcases mul_eq_zero.mp h with h | h
        · rcases mul_eq_zero.mp h with h | h
          · left; linarith
          · right; linarith
        · exact absurd h h9
      · exact absurd h hx
    · rintro (rfl | rfl)
      · refine ⟨by norm_num, ?_⟩
        rw [hN]; norm_num
      · refine ⟨by norm_num, ?_⟩
        rw [hN]; norm_num
  · intro x hx
    rw [hg, add_div' _ _ _ hx]
    congr 1
    ring

end UndergradKB.Precalculus.Course
