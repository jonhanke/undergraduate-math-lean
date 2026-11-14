import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic.ComputeDegree
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Polynomial
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.Polynomials

/-! # Course layer, Chapter 4 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 4.1 -/

namespace UndergradKB.Precalculus.Course

open Polynomial Filter Topology Set

/-! ## Helpers -/

private theorem w7x_inv_r (c : ℝ) : Tendsto (fun x : ℝ => (x - c)⁻¹) (𝓝[>] c) atTop := by
  have h : Tendsto (fun x : ℝ => x - c) (𝓝[>] c) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun x : ℝ => x - c) (𝓝 c) (𝓝 (c - c)) := tendsto_id.sub_const c
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact sub_pos.mpr (mem_Ioi.mp hx)
  exact tendsto_inv_nhdsGT_zero.comp h

private theorem w7x_inv_l (c : ℝ) : Tendsto (fun x : ℝ => (x - c)⁻¹) (𝓝[<] c) atBot := by
  have h : Tendsto (fun x : ℝ => x - c) (𝓝[<] c) (𝓝[<] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun x : ℝ => x - c) (𝓝 c) (𝓝 (c - c)) := tendsto_id.sub_const c
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact sub_neg.mpr (mem_Iio.mp hx)
  exact tendsto_inv_nhdsLT_zero.comp h

private theorem w7x_pole_rt {f g : ℝ → ℝ} {c : ℝ} (hg : ContinuousAt g c) (hc : 0 < g c)
    (hf : ∀ x, x ≠ c → |x - c| < 1 → f x = g x / (x - c)) : Tendsto f (𝓝[>] c) atTop := by
  have h := (hg.tendsto.mono_left nhdsWithin_le_nhds).pos_mul_atTop hc (w7x_inv_r c)
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show c < c + 1 by linarith)] with x hx
  show g x * (x - c)⁻¹ = f x
  rw [hf x (ne_of_gt hx.1) (by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2])]
  exact (div_eq_mul_inv _ _).symm

private theorem w7x_pole_rb {f g : ℝ → ℝ} {c : ℝ} (hg : ContinuousAt g c) (hc : g c < 0)
    (hf : ∀ x, x ≠ c → |x - c| < 1 → f x = g x / (x - c)) : Tendsto f (𝓝[>] c) atBot := by
  have h := (hg.tendsto.mono_left nhdsWithin_le_nhds).neg_mul_atTop hc (w7x_inv_r c)
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show c < c + 1 by linarith)] with x hx
  show g x * (x - c)⁻¹ = f x
  rw [hf x (ne_of_gt hx.1) (by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2])]
  exact (div_eq_mul_inv _ _).symm

private theorem w7x_pole_lb {f g : ℝ → ℝ} {c : ℝ} (hg : ContinuousAt g c) (hc : 0 < g c)
    (hf : ∀ x, x ≠ c → |x - c| < 1 → f x = g x / (x - c)) : Tendsto f (𝓝[<] c) atBot := by
  have h := (hg.tendsto.mono_left nhdsWithin_le_nhds).pos_mul_atBot hc (w7x_inv_l c)
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show c - 1 < c by linarith)] with x hx
  show g x * (x - c)⁻¹ = f x
  rw [hf x (ne_of_lt hx.2) (by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2])]
  exact (div_eq_mul_inv _ _).symm

private theorem w7x_pole_lt {f g : ℝ → ℝ} {c : ℝ} (hg : ContinuousAt g c) (hc : g c < 0)
    (hf : ∀ x, x ≠ c → |x - c| < 1 → f x = g x / (x - c)) : Tendsto f (𝓝[<] c) atTop := by
  have h := (hg.tendsto.mono_left nhdsWithin_le_nhds).neg_mul_atBot hc (w7x_inv_l c)
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show c - 1 < c by linarith)] with x hx
  show g x * (x - c)⁻¹ = f x
  rw [hf x (ne_of_lt hx.2) (by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2])]
  exact (div_eq_mul_inv _ _).symm

/-- Triple pole from the right with negative numerator: `f = g/(x-c)^3`, `g(c) < 0` gives `f → -∞`. -/
private theorem w7x_pole3_r {f g : ℝ → ℝ} {c : ℝ} (hg : ContinuousAt g c) (hc : g c < 0)
    (hf : ∀ x, x ≠ c → |x - c| < 1 → f x = g x / (x - c) ^ 3) : Tendsto f (𝓝[>] c) atBot := by
  have h0 : Tendsto (fun x : ℝ => (x - c) ^ 3) (𝓝[>] c) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun x : ℝ => (x - c) ^ 3) (𝓝 c) (𝓝 ((c - c) ^ 3)) :=
        ((continuous_id.sub continuous_const).pow 3).tendsto c
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have := sub_pos.mpr (mem_Ioi.mp hx)
      show 0 < (x - c) ^ 3
      positivity
  have h1 := tendsto_inv_nhdsGT_zero.comp h0
  have h := (hg.tendsto.mono_left nhdsWithin_le_nhds).neg_mul_atTop hc h1
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show c < c + 1 by linarith)] with x hx
  show g x * ((x - c) ^ 3)⁻¹ = f x
  rw [hf x (ne_of_gt hx.1) (by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2])]
  exact (div_eq_mul_inv _ _).symm

/-- Triple pole from the left with negative numerator: `f = g/(x-c)^3`, `g(c) < 0` gives `f → ∞`. -/
private theorem w7x_pole3_l {f g : ℝ → ℝ} {c : ℝ} (hg : ContinuousAt g c) (hc : g c < 0)
    (hf : ∀ x, x ≠ c → |x - c| < 1 → f x = g x / (x - c) ^ 3) : Tendsto f (𝓝[<] c) atTop := by
  have h0 : Tendsto (fun x : ℝ => (x - c) ^ 3) (𝓝[<] c) (𝓝[<] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun x : ℝ => (x - c) ^ 3) (𝓝 c) (𝓝 ((c - c) ^ 3)) :=
        ((continuous_id.sub continuous_const).pow 3).tendsto c
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have := sub_neg.mpr (mem_Iio.mp hx)
      show (x - c) ^ 3 < 0
      exact Odd.pow_neg (by decide) this
  have h1 := tendsto_inv_nhdsLT_zero.comp h0
  have h := (hg.tendsto.mono_left nhdsWithin_le_nhds).neg_mul_atBot hc h1
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show c - 1 < c by linarith)] with x hx
  show g x * ((x - c) ^ 3)⁻¹ = f x
  rw [hf x (ne_of_lt hx.2) (by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2])]
  exact (div_eq_mul_inv _ _).symm

/-- `f - g → 0` at both infinities when `f - g = p/q` off the roots of `q` and `deg p < deg q`. -/
private theorem w7x_diff_ends (f g : ℝ → ℝ) (p q : ℝ[X]) (m n : ℕ) (hp : p.natDegree ≤ m)
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

/-- Horizontal asymptote `y = c` at both ends, from `f - c = p/q` with `deg p < deg q`. -/
private theorem w7x_hor (f : ℝ → ℝ) (c : ℝ) (p q : ℝ[X]) (m n : ℕ) (hp : p.natDegree ≤ m)
    (hq : q.natDegree = n) (hmn : m < n) (h : ∀ x, q.eval x ≠ 0 → f x - c = p.eval x / q.eval x) :
    Tendsto f atTop (𝓝 c) ∧ Tendsto f atBot (𝓝 c) := by
  obtain ⟨h1, h2⟩ := w7x_diff_ends f (fun _ => c) p q m n hp hq hmn h
  exact ⟨tendsto_sub_nhds_zero_iff.mp h1, tendsto_sub_nhds_zero_iff.mp h2⟩

local macro "ev_simp" : tactic =>
  `(tactic| simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X, eval_neg, eval_one] at *)

/-! ## Section 4.1 -/

/-- Stitz-Zeager Exercise 4.1.7: `f(x) = 4x/(x²+4)` is defined on all of `ℝ` and has the horizontal
asymptote `y = 0` at both ends. -/
@[kb "stitzzeager2013" "Exercise 4.1.7, p. 326"]
theorem exer_4_1_7 :
    (∀ x : ℝ, x ^ 2 + 4 ≠ 0) ∧
    Tendsto (fun x : ℝ => 4 * x / (x ^ 2 + 4)) atBot (𝓝 0) ∧
    Tendsto (fun x : ℝ => 4 * x / (x ^ 2 + 4)) atTop (𝓝 0) := by
  have hh := w7x_hor (fun x : ℝ => 4 * x / (x ^ 2 + 4)) 0 (C 4 * X) (X ^ 2 + C 4) 1 2
    (by compute_degree) (by compute_degree!) (by norm_num) (fun x hx => by
      ev_simp
      simp)
  exact ⟨fun x => by positivity, hh.2, hh.1⟩

/-- Stitz-Zeager Exercise 4.1.8: `f(x) = 4x/(x²-4)` has vertical asymptotes `x = -2` and `x = 2` (`f → -∞` from
the left and `f → ∞` from the right at each), and the horizontal asymptote `y = 0` at both ends. -/
@[kb "stitzzeager2013" "Exercise 4.1.8, p. 326"]
theorem exer_4_1_8 :
    (Tendsto (fun x : ℝ => 4 * x / (x ^ 2 - 4)) (𝓝[<] (-2)) atBot ∧
      Tendsto (fun x : ℝ => 4 * x / (x ^ 2 - 4)) (𝓝[>] (-2)) atTop) ∧
    (Tendsto (fun x : ℝ => 4 * x / (x ^ 2 - 4)) (𝓝[<] 2) atBot ∧
      Tendsto (fun x : ℝ => 4 * x / (x ^ 2 - 4)) (𝓝[>] 2) atTop) ∧
    Tendsto (fun x : ℝ => 4 * x / (x ^ 2 - 4)) atBot (𝓝 0) ∧
    Tendsto (fun x : ℝ => 4 * x / (x ^ 2 - 4)) atTop (𝓝 0) := by
  have hv1 : ∀ x : ℝ, x ≠ -2 → |x - (-2)| < 1 → 4 * x / (x ^ 2 - 4) = (4 * x / (x - 2)) / (x - (-2)) := by
    intro x _ _
    rw [div_div]
    congr 1
    ring
  have hv2 : ∀ x : ℝ, x ≠ 2 → |x - 2| < 1 → 4 * x / (x ^ 2 - 4) = (4 * x / (x + 2)) / (x - 2) := by
    intro x _ _
    rw [div_div]
    congr 1
    ring
  have hg1 : ContinuousAt (fun x : ℝ => 4 * x / (x - 2)) (-2) := by fun_prop (disch := norm_num)
  have hg2 : ContinuousAt (fun x : ℝ => 4 * x / (x + 2)) 2 := by fun_prop (disch := norm_num)
  have hh := w7x_hor (fun x : ℝ => 4 * x / (x ^ 2 - 4)) 0 (C 4 * X) (X ^ 2 - C 4) 1 2
    (by compute_degree) (by compute_degree!) (by norm_num) (fun x hx => by
      ev_simp
      simp)
  exact ⟨⟨w7x_pole_lb hg1 (by norm_num) hv1, w7x_pole_rt hg1 (by norm_num) hv1⟩,
    ⟨w7x_pole_lb hg2 (by norm_num) hv2, w7x_pole_rt hg2 (by norm_num) hv2⟩, hh.2, hh.1⟩

/-- Stitz-Zeager Exercise 4.1.10: `f(x) = (3x²-5x-2)/(x²-9)` has the vertical asymptotes `x = -3` (`f → ∞` from the
left, `-∞` from the right) and `x = 3` (`-∞` from the left, `∞` from the right), and the horizontal asymptote
`y = 3` at both ends. -/
@[kb "stitzzeager2013" "Exercise 4.1.10, p. 326"]
theorem exer_4_1_10 :
    (Tendsto (fun x : ℝ => (3 * x ^ 2 - 5 * x - 2) / (x ^ 2 - 9)) (𝓝[<] (-3)) atTop ∧
      Tendsto (fun x : ℝ => (3 * x ^ 2 - 5 * x - 2) / (x ^ 2 - 9)) (𝓝[>] (-3)) atBot) ∧
    (Tendsto (fun x : ℝ => (3 * x ^ 2 - 5 * x - 2) / (x ^ 2 - 9)) (𝓝[<] 3) atBot ∧
      Tendsto (fun x : ℝ => (3 * x ^ 2 - 5 * x - 2) / (x ^ 2 - 9)) (𝓝[>] 3) atTop) ∧
    Tendsto (fun x : ℝ => (3 * x ^ 2 - 5 * x - 2) / (x ^ 2 - 9)) atBot (𝓝 3) ∧
    Tendsto (fun x : ℝ => (3 * x ^ 2 - 5 * x - 2) / (x ^ 2 - 9)) atTop (𝓝 3) := by
  have hv1 : ∀ x : ℝ, x ≠ -3 → |x - (-3)| < 1 →
      (3 * x ^ 2 - 5 * x - 2) / (x ^ 2 - 9) = ((3 * x ^ 2 - 5 * x - 2) / (x - 3)) / (x - (-3)) := by
    intro x _ _
    rw [div_div]
    congr 1
    ring
  have hv2 : ∀ x : ℝ, x ≠ 3 → |x - 3| < 1 →
      (3 * x ^ 2 - 5 * x - 2) / (x ^ 2 - 9) = ((3 * x ^ 2 - 5 * x - 2) / (x + 3)) / (x - 3) := by
    intro x _ _
    rw [div_div]
    congr 1
    ring
  have hg1 : ContinuousAt (fun x : ℝ => (3 * x ^ 2 - 5 * x - 2) / (x - 3)) (-3) := by
    fun_prop (disch := norm_num)
  have hg2 : ContinuousAt (fun x : ℝ => (3 * x ^ 2 - 5 * x - 2) / (x + 3)) 3 := by
    fun_prop (disch := norm_num)
  have hh := w7x_hor (fun x : ℝ => (3 * x ^ 2 - 5 * x - 2) / (x ^ 2 - 9)) 3 (C (-5) * X + C 25)
    (X ^ 2 - C 9) 1 2 (by compute_degree) (by compute_degree!) (by norm_num) (fun x hx => by
      ev_simp
      rw [eq_div_iff hx, sub_mul, div_mul_cancel₀ _ hx]
      ring)
  exact ⟨⟨w7x_pole_lt hg1 (by norm_num) hv1, w7x_pole_rb hg1 (by norm_num) hv1⟩,
    ⟨w7x_pole_lb hg2 (by norm_num) hv2, w7x_pole_rt hg2 (by norm_num) hv2⟩, hh.2, hh.1⟩

/-- Stitz-Zeager Exercise 4.1.12: `f(x) = (x³-3x+1)/(x²+1)` is defined on all of `ℝ` and has the slant asymptote
`y = x` at both ends. -/
@[kb "stitzzeager2013" "Exercise 4.1.12, p. 326"]
theorem exer_4_1_12 :
    (∀ x : ℝ, x ^ 2 + 1 ≠ 0) ∧
    Tendsto (fun x : ℝ => (x ^ 3 - 3 * x + 1) / (x ^ 2 + 1) - x) atBot (𝓝 0) ∧
    Tendsto (fun x : ℝ => (x ^ 3 - 3 * x + 1) / (x ^ 2 + 1) - x) atTop (𝓝 0) := by
  have hs := w7x_diff_ends (fun x : ℝ => (x ^ 3 - 3 * x + 1) / (x ^ 2 + 1)) (fun x => x)
    (C (-4) * X + C 1) (X ^ 2 + C 1) 1 2 (by compute_degree) (by compute_degree!) (by norm_num)
    (fun x hx => by
      ev_simp
      rw [eq_div_iff hx, sub_mul, div_mul_cancel₀ _ hx]
      ring)
  exact ⟨fun x => by positivity, hs.2, hs.1⟩

/-- Stitz-Zeager Exercise 4.1.14: `f(x) = (-x³+4x)/(x²-9)` has the vertical asymptotes `x = -3` and `x = 3` (`f → ∞`
from the left, `f → -∞` from the right at each), and the slant asymptote `y = -x` at both ends. -/
@[kb "stitzzeager2013" "Exercise 4.1.14, p. 326"]
theorem exer_4_1_14 :
    (Tendsto (fun x : ℝ => (-x ^ 3 + 4 * x) / (x ^ 2 - 9)) (𝓝[<] (-3)) atTop ∧
      Tendsto (fun x : ℝ => (-x ^ 3 + 4 * x) / (x ^ 2 - 9)) (𝓝[>] (-3)) atBot) ∧
    (Tendsto (fun x : ℝ => (-x ^ 3 + 4 * x) / (x ^ 2 - 9)) (𝓝[<] 3) atTop ∧
      Tendsto (fun x : ℝ => (-x ^ 3 + 4 * x) / (x ^ 2 - 9)) (𝓝[>] 3) atBot) ∧
    Tendsto (fun x : ℝ => (-x ^ 3 + 4 * x) / (x ^ 2 - 9) - (-x)) atBot (𝓝 0) ∧
    Tendsto (fun x : ℝ => (-x ^ 3 + 4 * x) / (x ^ 2 - 9) - (-x)) atTop (𝓝 0) := by
  have hv1 : ∀ x : ℝ, x ≠ -3 → |x - (-3)| < 1 →
      (-x ^ 3 + 4 * x) / (x ^ 2 - 9) = ((-x ^ 3 + 4 * x) / (x - 3)) / (x - (-3)) := by
    intro x _ _
    rw [div_div]
    congr 1
    ring
  have hv2 : ∀ x : ℝ, x ≠ 3 → |x - 3| < 1 →
      (-x ^ 3 + 4 * x) / (x ^ 2 - 9) = ((-x ^ 3 + 4 * x) / (x + 3)) / (x - 3) := by
    intro x _ _
    rw [div_div]
    congr 1
    ring
  have hg1 : ContinuousAt (fun x : ℝ => (-x ^ 3 + 4 * x) / (x - 3)) (-3) := by
    fun_prop (disch := norm_num)
  have hg2 : ContinuousAt (fun x : ℝ => (-x ^ 3 + 4 * x) / (x + 3)) 3 := by
    fun_prop (disch := norm_num)
  have hs := w7x_diff_ends (fun x : ℝ => (-x ^ 3 + 4 * x) / (x ^ 2 - 9)) (fun x => -x)
    (C (-5) * X) (X ^ 2 - C 9) 1 2 (by compute_degree) (by compute_degree!) (by norm_num)
    (fun x hx => by
      ev_simp
      rw [eq_div_iff hx, sub_mul, div_mul_cancel₀ _ hx]
      ring)
  exact ⟨⟨w7x_pole_lt hg1 (by norm_num) hv1, w7x_pole_rb hg1 (by norm_num) hv1⟩,
    ⟨w7x_pole_lt hg2 (by norm_num) hv2, w7x_pole_rb hg2 (by norm_num) hv2⟩, hs.2, hs.1⟩

/-- Stitz-Zeager Exercise 4.1.15: `f(x) = (-5x⁴-3x³+x²-10)/(x³-3x²+3x-1)` has the vertical asymptote `x = 1`
(`f → ∞` from the left, `f → -∞` from the right) and the slant asymptote `y = -5x - 18` at both ends. -/
@[kb "stitzzeager2013" "Exercise 4.1.15, p. 326"]
theorem exer_4_1_15 :
    Tendsto (fun x : ℝ => (-5 * x ^ 4 - 3 * x ^ 3 + x ^ 2 - 10) / (x ^ 3 - 3 * x ^ 2 + 3 * x - 1))
      (𝓝[<] 1) atTop ∧
    Tendsto (fun x : ℝ => (-5 * x ^ 4 - 3 * x ^ 3 + x ^ 2 - 10) / (x ^ 3 - 3 * x ^ 2 + 3 * x - 1))
      (𝓝[>] 1) atBot ∧
    Tendsto (fun x : ℝ => (-5 * x ^ 4 - 3 * x ^ 3 + x ^ 2 - 10) / (x ^ 3 - 3 * x ^ 2 + 3 * x - 1) -
      (-5 * x - 18)) atBot (𝓝 0) ∧
    Tendsto (fun x : ℝ => (-5 * x ^ 4 - 3 * x ^ 3 + x ^ 2 - 10) / (x ^ 3 - 3 * x ^ 2 + 3 * x - 1) -
      (-5 * x - 18)) atTop (𝓝 0) := by
  have hv : ∀ x : ℝ, x ≠ 1 → |x - 1| < 1 →
      (-5 * x ^ 4 - 3 * x ^ 3 + x ^ 2 - 10) / (x ^ 3 - 3 * x ^ 2 + 3 * x - 1) =
        (-5 * x ^ 4 - 3 * x ^ 3 + x ^ 2 - 10) / (x - 1) ^ 3 := by
    intro x _ _
    congr 1
    ring
  have hg : ContinuousAt (fun x : ℝ => -5 * x ^ 4 - 3 * x ^ 3 + x ^ 2 - 10) 1 := by fun_prop
  have hs := w7x_diff_ends
    (fun x : ℝ => (-5 * x ^ 4 - 3 * x ^ 3 + x ^ 2 - 10) / (x ^ 3 - 3 * x ^ 2 + 3 * x - 1))
    (fun x => -5 * x - 18) (C (-38) * X ^ 2 + C 49 * X - C 28)
    (X ^ 3 - C 3 * X ^ 2 + C 3 * X - C 1) 2 3 (by compute_degree) (by compute_degree!) (by norm_num)
    (fun x hx => by
      ev_simp
      rw [eq_div_iff hx, sub_mul, div_mul_cancel₀ _ hx]
      ring)
  exact ⟨w7x_pole3_l hg (by norm_num) hv, w7x_pole3_r hg (by norm_num) hv, hs.2, hs.1⟩

/-- Stitz-Zeager Exercise 4.1.16: `f(x) = x³/(1-x)` has the vertical asymptote `x = 1` (`f → ∞` from the left,
`f → -∞` from the right), no horizontal or slant asymptote, and `f → -∞` at both ends. -/
@[kb "stitzzeager2013" "Exercise 4.1.16, p. 326"]
theorem exer_4_1_16 :
    Tendsto (fun x : ℝ => x ^ 3 / (1 - x)) (𝓝[<] 1) atTop ∧
    Tendsto (fun x : ℝ => x ^ 3 / (1 - x)) (𝓝[>] 1) atBot ∧
    Tendsto (fun x : ℝ => x ^ 3 / (1 - x)) atBot atBot ∧
    Tendsto (fun x : ℝ => x ^ 3 / (1 - x)) atTop atBot := by
  have hv : ∀ x : ℝ, x ≠ 1 → |x - 1| < 1 → x ^ 3 / (1 - x) = (-x ^ 3) / (x - 1) := by
    intro x hx _
    have h1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx
    have h2 : 1 - x ≠ 0 := fun h => h1 (by linarith)
    rw [div_eq_div_iff h2 h1]
    ring
  have hg : ContinuousAt (fun x : ℝ => -x ^ 3) 1 := by fun_prop
  have key : ∀ x : ℝ, x ≠ 1 → x ^ 3 / (1 - x) = -(x ^ 2 + x + 1) + (1 - x)⁻¹ := by
    intro x hx
    have h2 : 1 - x ≠ 0 := fun h => hx (by linarith)
    field_simp
    ring
  have hp : 0 < (X ^ 2 + X + 1 : ℝ[X]).degree := by
    have : (X ^ 2 + X + 1 : ℝ[X]).natDegree = 2 := by compute_degree!
    rw [degree_eq_natDegree (by intro h; rw [h] at this; simp at this), this]; norm_num
  have hpl : (X ^ 2 + X + 1 : ℝ[X]).natDegree = 2 := by compute_degree!
  have hpc : (X ^ 2 + X + 1 : ℝ[X]).leadingCoeff = 1 := by
    rw [leadingCoeff, hpl]; compute_degree!
  have hbot := ((poly_tendsto_atBot_cases _ hp).1 (by rw [hpl]; decide)).1 (by rw [hpc]; norm_num)
  have htop : Tendsto (fun x : ℝ => (X ^ 2 + X + 1 : ℝ[X]).eval x) atTop atTop :=
    Polynomial.tendsto_atTop_of_leadingCoeff_nonneg _ hp (by rw [hpc]; norm_num)
  have hev : ∀ x : ℝ, (X ^ 2 + X + 1 : ℝ[X]).eval x = x ^ 2 + x + 1 := by intro x; simp
  have hinv_top : Tendsto (fun x : ℝ => (1 - x)⁻¹) atTop (𝓝 0) := by
    have : Tendsto (fun x : ℝ => 1 - x) atTop atBot := by
      simpa [sub_eq_add_neg, add_comm] using tendsto_atBot_add_const_right atTop (1 : ℝ)
        tendsto_neg_atTop_atBot
    exact tendsto_inv_atBot_zero.comp this
  have hinv_bot : Tendsto (fun x : ℝ => (1 - x)⁻¹) atBot (𝓝 0) := by
    have : Tendsto (fun x : ℝ => 1 - x) atBot atTop := by
      simpa [sub_eq_add_neg, add_comm] using tendsto_atTop_add_const_right atBot (1 : ℝ)
        tendsto_neg_atBot_atTop
    exact tendsto_inv_atTop_zero.comp this
  refine ⟨w7x_pole_lt hg (by norm_num) hv, w7x_pole_rb hg (by norm_num) hv, ?_, ?_⟩
  · have h1 : Tendsto (fun x : ℝ => -(x ^ 2 + x + 1)) atBot atBot := by
      have := tendsto_neg_atTop_atBot.comp hbot
      exact this.congr (fun x => by simp only [Function.comp, hev])
    refine (h1.atBot_add hinv_bot).congr' ?_
    filter_upwards [eventually_ne_atBot (1 : ℝ)] with x hx
    exact (key x hx).symm
  · have h1 : Tendsto (fun x : ℝ => -(x ^ 2 + x + 1)) atTop atBot := by
      have := tendsto_neg_atTop_atBot.comp htop
      exact this.congr (fun x => by simp only [Function.comp, hev])
    refine (h1.atBot_add hinv_top).congr' ?_
    filter_upwards [eventually_ne_atTop (1 : ℝ)] with x hx
    exact (key x hx).symm

/-- Stitz-Zeager Exercise 4.1.21: the average cost `C̄(x) = C(x)/x = 100 + 2000/x` of `C(x) = 100x + 2000`:
`C̄(1) = 2100`, `C̄(100) = 120`, `C̄(x) = 200` exactly at `x = 20`, `C̄ → ∞` as `x → 0⁺` and `C̄ → 100` as `x → ∞`. -/
@[kb "stitzzeager2013" "Exercise 4.1.21, p. 327"]
theorem exer_4_1_21 (C : ℝ → ℝ) (hC : ∀ x, C x = 100 * x + 2000) :
    (∀ x : ℝ, x ≠ 0 → C x / x = 100 + 2000 / x) ∧ C 1 / 1 = 2100 ∧ C 100 / 100 = 120 ∧
      (∀ x : ℝ, 0 < x → (C x / x = 200 ↔ x = 20)) ∧
      Tendsto (fun x : ℝ => C x / x) (𝓝[>] 0) atTop ∧ Tendsto (fun x : ℝ => C x / x) atTop (𝓝 100) := by
  have hq : ∀ x : ℝ, x ≠ 0 → C x / x = 100 + 2000 / x := by
    intro x hx
    rw [hC]; field_simp
  refine ⟨hq, by rw [hC]; norm_num, by rw [hC]; norm_num, fun x hx => ?_, ?_, ?_⟩
  · rw [hq x hx.ne']
    constructor
    · intro h
      have : 2000 / x = 100 := by linarith
      field_simp at this
      linarith
    · rintro rfl; norm_num
  · have h1 : Tendsto (fun x : ℝ => 2000 * x⁻¹) (𝓝[>] 0) atTop :=
      Tendsto.const_mul_atTop (by norm_num) tendsto_inv_nhdsGT_zero
    have h2 := tendsto_atTop_add_const_left _ (100 : ℝ) h1
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [hq x (ne_of_gt hx)]; simp [div_eq_mul_inv]
  · have h1 : Tendsto (fun x : ℝ => 2000 * x⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero.const_mul (2000 : ℝ)
    have h2 := h1.const_add 100
    simp only [add_zero] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [hq x hx.ne']; simp [div_eq_mul_inv]

/-- Stitz-Zeager Exercise 4.1.22: the power `P(x) = 25x/(x + 3.9)²` is at most `25/15.6` with equality exactly
at `x = 3.9` (so the maximum power is about `1.603` mW at about `3.9` kΩ), and `P(x) → 0` as `x → ∞`. -/
@[kb "stitzzeager2013" "Exercise 4.1.22, p. 327"]
theorem exer_4_1_22 (P : ℝ → ℝ) (hP : ∀ x, P x = 25 * x / (x + 39 / 10) ^ 2) :
    (∀ x : ℝ, 0 ≤ x → P x ≤ P (39 / 10)) ∧ P (39 / 10) = 125 / 78 ∧
      1.60 < (125 / 78 : ℝ) ∧ (125 / 78 : ℝ) < 1.61 ∧ Tendsto P atTop (𝓝 0) := by
  refine ⟨fun x hx => ?_, by rw [hP]; norm_num, by norm_num, by norm_num, ?_⟩
  · rw [hP, hP]
    have hpos : 0 < (x + 39 / 10) ^ 2 := by positivity
    rw [div_le_div_iff₀ hpos (by norm_num)]
    nlinarith [sq_nonneg (x - 39 / 10)]
  · have hh := w7x_hor P 0 (C 25 * X) ((X + C (39 / 10)) ^ 2) 1 2
      (by compute_degree) (by compute_degree!) (by norm_num) (fun x hx => by
        ev_simp
        rw [hP]; simp)
    exact hh.1

end UndergradKB.Precalculus.Course
