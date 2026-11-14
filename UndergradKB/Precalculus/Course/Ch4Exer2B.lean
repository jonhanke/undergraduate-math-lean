import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.ComputeDegree
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Polynomial
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.Rational

/-! # Course layer, Chapter 4 (Stitz-Zeager): exercises with the book's answers (wave 7), Sections 4.2-4.3 -/

namespace UndergradKB.Precalculus.Course

open Polynomial Filter Topology Set

/-! ## Helpers -/

private theorem w7y_diff_ends (f g : ℝ → ℝ) (p q : ℝ[X]) (m n : ℕ) (hp : p.natDegree ≤ m)
    (hq : q.natDegree = n) (hmn : m < n) (h : ∀ x, q.eval x ≠ 0 → f x - g x = p.eval x / q.eval x) :
    Tendsto (fun x => f x - g x) atTop (𝓝 0) ∧ Tendsto (fun x => f x - g x) atBot (𝓝 0) := by
  have hq0 : q ≠ 0 := by
    rintro rfl
    simp at hq
    omega
  have hdeg : p.degree < q.degree := degree_lt_degree (by omega)
  refine ⟨(Polynomial.div_tendsto_atTop_zero_of_degree_lt p q hdeg).congr' ?_,
    (Polynomial.div_tendsto_atBot_zero_of_degree_lt p q hdeg).congr' ?_⟩
  · filter_upwards [Polynomial.eventually_atTop_not_isRoot q hq0] with x hx
    exact (h x hx).symm
  · filter_upwards [Polynomial.eventually_atBot_not_isRoot q hq0] with x hx
    exact (h x hx).symm

private theorem w7y_hor (f : ℝ → ℝ) (c : ℝ) (p q : ℝ[X]) (m n : ℕ) (hp : p.natDegree ≤ m)
    (hq : q.natDegree = n) (hmn : m < n) (h : ∀ x, q.eval x ≠ 0 → f x - c = p.eval x / q.eval x) :
    Tendsto f atTop (𝓝 c) ∧ Tendsto f atBot (𝓝 c) := by
  obtain ⟨h1, h2⟩ := w7y_diff_ends f (fun _ => c) p q m n hp hq hmn h
  exact ⟨tendsto_sub_nhds_zero_iff.mp h1, tendsto_sub_nhds_zero_iff.mp h2⟩

/-- Approach from below: a limit `c` together with eventual values below `c`. -/
private theorem w7y_below {f : ℝ → ℝ} {l : Filter ℝ} {c : ℝ} (h : Tendsto f l (𝓝 c))
    (hs : ∀ᶠ x in l, f x < c) : Tendsto f l (𝓝[<] c) :=
  tendsto_nhdsWithin_iff.mpr ⟨h, hs.mono fun x hx => hx⟩

/-- Approach from above: a limit `c` together with eventual values above `c`. -/
private theorem w7y_above {f : ℝ → ℝ} {l : Filter ℝ} {c : ℝ} (h : Tendsto f l (𝓝 c))
    (hs : ∀ᶠ x in l, c < f x) : Tendsto f l (𝓝[>] c) :=
  tendsto_nhdsWithin_iff.mpr ⟨h, hs.mono fun x hx => hx⟩

local macro "ev_simp" : tactic =>
  `(tactic| simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X, eval_neg, eval_one] at *)

/-! ## Section 4.2 -/

/-- Stitz-Zeager Exercise 4.2.6: `f(x) = x/(x²+x-12)` has x- and y-intercept `(0,0)` (the only zero away from the
poles `-4`, `3`), approaches `0` from below as `x → -∞` and from above as `x → ∞`. -/
@[kb "stitzzeager2013" "Exercise 4.2.6, p. 333"]
theorem exer_4_2_6 :
    (∀ x : ℝ, x ≠ -4 → x ≠ 3 → (x / (x ^ 2 + x - 12) = 0 ↔ x = 0)) ∧ (0 : ℝ) / (0 ^ 2 + 0 - 12) = 0 ∧
    Tendsto (fun x : ℝ => x / (x ^ 2 + x - 12)) atBot (𝓝[<] 0) ∧
    Tendsto (fun x : ℝ => x / (x ^ 2 + x - 12)) atTop (𝓝[>] 0) := by
  have hh := w7y_hor (fun x : ℝ => x / (x ^ 2 + x - 12)) 0 X (X ^ 2 + X - C 12) 1 2
    (by compute_degree) (by compute_degree!) (by norm_num) (fun x hx => by
      ev_simp
      simp [hx])
  refine ⟨fun x h1 h2 => ?_, by norm_num, w7y_below hh.2 ?_, w7y_above hh.1 ?_⟩
  · have hd : x ^ 2 + x - 12 ≠ 0 := by
      rw [show x ^ 2 + x - 12 = (x + 4) * (x - 3) by ring]
      exact mul_ne_zero (fun h => h1 (by linarith)) (fun h => h2 (by linarith))
    rw [div_eq_zero_iff]
    constructor
    · rintro (h | h)
      · exact h
      · exact absurd h hd
    · intro h; left; exact h
  · filter_upwards [eventually_lt_atBot (-4 : ℝ)] with x hx
    exact div_neg_of_neg_of_pos (by linarith) (by nlinarith)
  · filter_upwards [eventually_gt_atTop (3 : ℝ)] with x hx
    exact div_pos (by linarith) (by nlinarith)

/-- Stitz-Zeager Exercise 4.2.7: `f(x) = 4x/(x²+4)` has x- and y-intercept `(0,0)` (the only zero), approaches `0`
from below as `x → -∞` and from above as `x → ∞`. -/
@[kb "stitzzeager2013" "Exercise 4.2.7, p. 333"]
theorem exer_4_2_7 :
    (∀ x : ℝ, 4 * x / (x ^ 2 + 4) = 0 ↔ x = 0) ∧ (4 * (0 : ℝ)) / (0 ^ 2 + 4) = 0 ∧
    Tendsto (fun x : ℝ => 4 * x / (x ^ 2 + 4)) atBot (𝓝[<] 0) ∧
    Tendsto (fun x : ℝ => 4 * x / (x ^ 2 + 4)) atTop (𝓝[>] 0) := by
  have hh := w7y_hor (fun x : ℝ => 4 * x / (x ^ 2 + 4)) 0 (C 4 * X) (X ^ 2 + C 4) 1 2
    (by compute_degree) (by compute_degree!) (by norm_num) (fun x hx => by
      ev_simp
      simp)
  refine ⟨fun x => ?_, by norm_num, w7y_below hh.2 ?_, w7y_above hh.1 ?_⟩
  · have hd : x ^ 2 + 4 ≠ 0 := by positivity
    rw [div_eq_zero_iff]
    constructor
    · rintro (h | h)
      · linarith
      · exact absurd h hd
    · intro h; left; rw [h]; norm_num
  · filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
    exact div_neg_of_neg_of_pos (by linarith) (by positivity)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact div_pos (by linarith) (by positivity)

/-- Stitz-Zeager Exercise 4.2.8: `f(x) = 4x/(x²-4)` has x- and y-intercept `(0,0)` (the only zero away from the poles
`±2`), approaches `0` from below as `x → -∞` and from above as `x → ∞`. -/
@[kb "stitzzeager2013" "Exercise 4.2.8, p. 333"]
theorem exer_4_2_8 :
    (∀ x : ℝ, x ≠ -2 → x ≠ 2 → (4 * x / (x ^ 2 - 4) = 0 ↔ x = 0)) ∧ (4 * (0 : ℝ)) / (0 ^ 2 - 4) = 0 ∧
    Tendsto (fun x : ℝ => 4 * x / (x ^ 2 - 4)) atBot (𝓝[<] 0) ∧
    Tendsto (fun x : ℝ => 4 * x / (x ^ 2 - 4)) atTop (𝓝[>] 0) := by
  have hh := w7y_hor (fun x : ℝ => 4 * x / (x ^ 2 - 4)) 0 (C 4 * X) (X ^ 2 - C 4) 1 2
    (by compute_degree) (by compute_degree!) (by norm_num) (fun x hx => by
      ev_simp
      simp)
  refine ⟨fun x h1 h2 => ?_, by norm_num, w7y_below hh.2 ?_, w7y_above hh.1 ?_⟩
  · have hd : x ^ 2 - 4 ≠ 0 := by
      rw [show x ^ 2 - 4 = (x + 2) * (x - 2) by ring]
      exact mul_ne_zero (fun h => h1 (by linarith)) (fun h => h2 (by linarith))
    rw [div_eq_zero_iff]
    constructor
    · rintro (h | h)
      · linarith
      · exact absurd h hd
    · intro h; left; rw [h]; norm_num
  · filter_upwards [eventually_lt_atBot (-2 : ℝ)] with x hx
    exact div_neg_of_neg_of_pos (by linarith) (by nlinarith)
  · filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx
    exact div_pos (by linarith) (by nlinarith)

/-- Stitz-Zeager Exercise 4.2.9: `f(x) = (x²-x-12)/(x²+x-6)` has x-intercept `(4,0)` (away from the poles `-3`, `2`),
y-intercept `(0,2)`, approaches `1` from above as `x → -∞` and from below as `x → ∞`. -/
@[kb "stitzzeager2013" "Exercise 4.2.9, p. 333"]
theorem exer_4_2_9 :
    (∀ x : ℝ, x ≠ -3 → x ≠ 2 → ((x ^ 2 - x - 12) / (x ^ 2 + x - 6) = 0 ↔ x = 4)) ∧
    ((0 : ℝ) ^ 2 - 0 - 12) / (0 ^ 2 + 0 - 6) = 2 ∧
    Tendsto (fun x : ℝ => (x ^ 2 - x - 12) / (x ^ 2 + x - 6)) atBot (𝓝[>] 1) ∧
    Tendsto (fun x : ℝ => (x ^ 2 - x - 12) / (x ^ 2 + x - 6)) atTop (𝓝[<] 1) := by
  have hh := w7y_hor (fun x : ℝ => (x ^ 2 - x - 12) / (x ^ 2 + x - 6)) 1 (C (-2) * X - C 6)
    (X ^ 2 + X - C 6) 1 2 (by compute_degree) (by compute_degree!) (by norm_num) (fun x hx => by
      ev_simp
      rw [eq_div_iff hx, sub_mul, div_mul_cancel₀ _ hx]
      ring)
  have hd : ∀ x : ℝ, x ≠ -3 → x ≠ 2 → x ^ 2 + x - 6 ≠ 0 := by
    intro x h1 h2
    rw [show x ^ 2 + x - 6 = (x + 3) * (x - 2) by ring]
    exact mul_ne_zero (fun h => h1 (by linarith)) (fun h => h2 (by linarith))
  have key : ∀ x : ℝ, x ≠ -3 → x ≠ 2 →
      (x ^ 2 - x - 12) / (x ^ 2 + x - 6) - 1 = -2 / (x - 2) := by
    intro x h1 h2
    have h3 : x - 2 ≠ 0 := sub_ne_zero.mpr h2
    have h4 := hd x h1 h2
    rw [div_sub_one h4, div_eq_div_iff h4 h3]
    have : x + 3 ≠ 0 := fun h => h1 (by linarith)
    ring
  refine ⟨fun x h1 h2 => ?_, by norm_num, w7y_above hh.2 ?_, w7y_below hh.1 ?_⟩
  · rw [div_eq_zero_iff]
    constructor
    · rintro (h | h)
      · have : (x - 4) * (x + 3) = 0 := by linarith
        rcases mul_eq_zero.mp this with h | h
        · linarith
        · exact absurd (by linarith) h1
      · exact absurd h (hd x h1 h2)
    · intro h; left; rw [h]; norm_num
  · filter_upwards [eventually_lt_atBot (-3 : ℝ)] with x hx
    have := key x (by linarith) (by linarith)
    have h5 : 0 < -2 / (x - 2) := div_pos_of_neg_of_neg (by norm_num) (by linarith)
    linarith
  · filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx
    have := key x (by linarith) (by linarith)
    have h5 : -2 / (x - 2) < 0 := div_neg_of_neg_of_pos (by norm_num) (by linarith)
    linarith

/-- Stitz-Zeager Exercise 4.2.13: `f(x) = (x³+2x²+x)/(x²-x-2)` has x- and y-intercept `(0,0)` (the only zero away from
`-1` and `2`); its graph lies below the slant asymptote `y = x + 3` for `x < -1` and above it for `x > 2`. -/
@[kb "stitzzeager2013" "Exercise 4.2.13, p. 333"]
theorem exer_4_2_13 :
    (∀ x : ℝ, x ≠ -1 → x ≠ 2 → ((x ^ 3 + 2 * x ^ 2 + x) / (x ^ 2 - x - 2) = 0 ↔ x = 0)) ∧
    ((0 : ℝ) ^ 3 + 2 * 0 ^ 2 + 0) / (0 ^ 2 - 0 - 2) = 0 ∧
    (∀ x : ℝ, x < -1 → (x ^ 3 + 2 * x ^ 2 + x) / (x ^ 2 - x - 2) < x + 3) ∧
    (∀ x : ℝ, 2 < x → x + 3 < (x ^ 3 + 2 * x ^ 2 + x) / (x ^ 2 - x - 2)) := by
  have hd : ∀ x : ℝ, x ≠ -1 → x ≠ 2 → x ^ 2 - x - 2 ≠ 0 := by
    intro x h1 h2
    rw [show x ^ 2 - x - 2 = (x + 1) * (x - 2) by ring]
    exact mul_ne_zero (fun h => h1 (by linarith)) (fun h => h2 (by linarith))
  have key : ∀ x : ℝ, x ^ 2 - x - 2 ≠ 0 →
      (x ^ 3 + 2 * x ^ 2 + x) / (x ^ 2 - x - 2) - (x + 3) = (6 * x + 6) / (x ^ 2 - x - 2) := by
    intro x h
    rw [div_sub' h, div_eq_div_iff h h]
    ring
  refine ⟨fun x h1 h2 => ?_, by norm_num, fun x hx => ?_, fun x hx => ?_⟩
  · rw [div_eq_zero_iff]
    constructor
    · rintro (h | h)
      · have : x * (x + 1) ^ 2 = 0 := by linarith
        rcases mul_eq_zero.mp this with h | h
        · exact h
        · exact absurd (by linarith [pow_eq_zero_iff (two_ne_zero) |>.mp h]) h1
      · exact absurd h (hd x h1 h2)
    · intro h; left; rw [h]; norm_num
  · have h1 : x ≠ -1 := by intro h; linarith
    have h2 : x ≠ 2 := by intro h; linarith
    have := key x (hd x h1 h2)
    have h5 : (6 * x + 6) / (x ^ 2 - x - 2) < 0 :=
      div_neg_of_neg_of_pos (by linarith) (by nlinarith)
    linarith
  · have h1 : x ≠ -1 := by intro h; linarith
    have h2 : x ≠ 2 := by intro h; linarith
    have := key x (hd x h1 h2)
    have h5 : 0 < (6 * x + 6) / (x ^ 2 - x - 2) := div_pos (by linarith) (by nlinarith)
    linarith

/-- Stitz-Zeager Exercise 4.2.14: `f(x) = (-x³+4x)/(x²-9)` has x-intercepts `(-2,0)`, `(0,0)`, `(2,0)` (away from the
poles `±3`), y-intercept `(0,0)`; its graph lies above the slant asymptote `y = -x` for `x < -3` and below it for
`x > 3`. -/
@[kb "stitzzeager2013" "Exercise 4.2.14, p. 333"]
theorem exer_4_2_14 :
    (∀ x : ℝ, x ≠ -3 → x ≠ 3 → ((-x ^ 3 + 4 * x) / (x ^ 2 - 9) = 0 ↔ x = -2 ∨ x = 0 ∨ x = 2)) ∧
    (-(0 : ℝ) ^ 3 + 4 * 0) / (0 ^ 2 - 9) = 0 ∧
    (∀ x : ℝ, x < -3 → -x < (-x ^ 3 + 4 * x) / (x ^ 2 - 9)) ∧
    (∀ x : ℝ, 3 < x → (-x ^ 3 + 4 * x) / (x ^ 2 - 9) < -x) := by
  have hd : ∀ x : ℝ, x ≠ -3 → x ≠ 3 → x ^ 2 - 9 ≠ 0 := by
    intro x h1 h2
    rw [show x ^ 2 - 9 = (x + 3) * (x - 3) by ring]
    exact mul_ne_zero (fun h => h1 (by linarith)) (fun h => h2 (by linarith))
  have key : ∀ x : ℝ, x ^ 2 - 9 ≠ 0 →
      (-x ^ 3 + 4 * x) / (x ^ 2 - 9) - (-x) = (-5 * x) / (x ^ 2 - 9) := by
    intro x h
    rw [sub_neg_eq_add, div_add' _ _ _ h, div_eq_div_iff h h]
    ring
  refine ⟨fun x h1 h2 => ?_, by norm_num, fun x hx => ?_, fun x hx => ?_⟩
  · rw [div_eq_zero_iff]
    constructor
    · rintro (h | h)
      · have : x * (x - 2) * (x + 2) = 0 := by linarith
        rcases mul_eq_zero.mp this with h | h
        · rcases mul_eq_zero.mp h with h | h
          · right; left; exact h
          · right; right; linarith
        · left; linarith
      · exact absurd h (hd x h1 h2)
    · rintro (h | h | h) <;> left <;> rw [h] <;> norm_num
  · have h1 : x ≠ -3 := by intro h; linarith
    have h2 : x ≠ 3 := by intro h; linarith
    have := key x (hd x h1 h2)
    have h5 : 0 < (-5 * x) / (x ^ 2 - 9) := div_pos (by linarith) (by nlinarith)
    linarith
  · have h1 : x ≠ -3 := by intro h; linarith
    have h2 : x ≠ 3 := by intro h; linarith
    have := key x (hd x h1 h2)
    have h5 : (-5 * x) / (x ^ 2 - 9) < 0 := div_neg_of_neg_of_pos (by linarith) (by nlinarith)
    linarith

end UndergradKB.Precalculus.Course
