import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic.ComputeDegree
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Polynomial
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 4 (Stitz-Zeager): exercises with the book's answers -/

namespace UndergradKB.Precalculus.Course

open Polynomial Filter Topology Set

/-! ## Helpers -/

private theorem x4_inv_r (c : ℝ) : Tendsto (fun x : ℝ => (x - c)⁻¹) (𝓝[>] c) atTop := by
  have h : Tendsto (fun x : ℝ => x - c) (𝓝[>] c) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun x : ℝ => x - c) (𝓝 c) (𝓝 (c - c)) := tendsto_id.sub_const c
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact sub_pos.mpr (mem_Ioi.mp hx)
  exact tendsto_inv_nhdsGT_zero.comp h

private theorem x4_inv_l (c : ℝ) : Tendsto (fun x : ℝ => (x - c)⁻¹) (𝓝[<] c) atBot := by
  have h : Tendsto (fun x : ℝ => x - c) (𝓝[<] c) (𝓝[<] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun x : ℝ => x - c) (𝓝 c) (𝓝 (c - c)) := tendsto_id.sub_const c
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact sub_neg.mpr (mem_Iio.mp hx)
  exact tendsto_inv_nhdsLT_zero.comp h

/-- Right-hand pole, positive numerator factor: `f = g/(x-c)`, `g(c) > 0`. -/
private theorem x4_pole_rt {f g : ℝ → ℝ} {c : ℝ} (hg : ContinuousAt g c) (hc : 0 < g c)
    (hf : ∀ x, x ≠ c → |x - c| < 1 → f x = g x / (x - c)) : Tendsto f (𝓝[>] c) atTop := by
  have h := (hg.tendsto.mono_left nhdsWithin_le_nhds).pos_mul_atTop hc (x4_inv_r c)
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show c < c + 1 by linarith)] with x hx
  show g x * (x - c)⁻¹ = f x
  rw [hf x (ne_of_gt hx.1) (by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2])]
  exact (div_eq_mul_inv _ _).symm

private theorem x4_pole_rb {f g : ℝ → ℝ} {c : ℝ} (hg : ContinuousAt g c) (hc : g c < 0)
    (hf : ∀ x, x ≠ c → |x - c| < 1 → f x = g x / (x - c)) : Tendsto f (𝓝[>] c) atBot := by
  have h := (hg.tendsto.mono_left nhdsWithin_le_nhds).neg_mul_atTop hc (x4_inv_r c)
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show c < c + 1 by linarith)] with x hx
  show g x * (x - c)⁻¹ = f x
  rw [hf x (ne_of_gt hx.1) (by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2])]
  exact (div_eq_mul_inv _ _).symm

private theorem x4_pole_lb {f g : ℝ → ℝ} {c : ℝ} (hg : ContinuousAt g c) (hc : 0 < g c)
    (hf : ∀ x, x ≠ c → |x - c| < 1 → f x = g x / (x - c)) : Tendsto f (𝓝[<] c) atBot := by
  have h := (hg.tendsto.mono_left nhdsWithin_le_nhds).pos_mul_atBot hc (x4_inv_l c)
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show c - 1 < c by linarith)] with x hx
  show g x * (x - c)⁻¹ = f x
  rw [hf x (ne_of_lt hx.2) (by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2])]
  exact (div_eq_mul_inv _ _).symm

private theorem x4_pole_lt {f g : ℝ → ℝ} {c : ℝ} (hg : ContinuousAt g c) (hc : g c < 0)
    (hf : ∀ x, x ≠ c → |x - c| < 1 → f x = g x / (x - c)) : Tendsto f (𝓝[<] c) atTop := by
  have h := (hg.tendsto.mono_left nhdsWithin_le_nhds).neg_mul_atBot hc (x4_inv_l c)
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show c - 1 < c by linarith)] with x hx
  show g x * (x - c)⁻¹ = f x
  rw [hf x (ne_of_lt hx.2) (by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2])]
  exact (div_eq_mul_inv _ _).symm

/-- Double pole: `f = g/(x-c)^2`, `g(c) > 0` gives `f → ∞` from both sides. -/
private theorem x4_pole2 {f g : ℝ → ℝ} {c : ℝ} (hg : ContinuousAt g c) (hc : 0 < g c)
    (hf : ∀ x, x ≠ c → |x - c| < 1 → f x = g x / (x - c) ^ 2) :
    Tendsto f (𝓝[<] c) atTop ∧ Tendsto f (𝓝[>] c) atTop := by
  have h0 : Tendsto (fun x : ℝ => (x - c) ^ 2) (𝓝[≠] c) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun x : ℝ => (x - c) ^ 2) (𝓝 c) (𝓝 ((c - c) ^ 2)) :=
        ((continuous_id.sub continuous_const).pow 2).tendsto c
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have : x - c ≠ 0 := sub_ne_zero.mpr hx
      show 0 < (x - c) ^ 2
      positivity
  have h1 := tendsto_inv_nhdsGT_zero.comp h0
  have h2 : Tendsto f (𝓝[≠] c) atTop := by
    refine ((hg.tendsto.mono_left nhdsWithin_le_nhds).pos_mul_atTop hc h1).congr' ?_
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds c one_pos)]
      with x hx1 hx2
    rw [Metric.mem_ball, Real.dist_eq] at hx2
    show g x * ((x - c) ^ 2)⁻¹ = f x
    rw [hf x hx1 hx2]
    exact (div_eq_mul_inv _ _).symm
  exact ⟨h2.mono_left (nhdsWithin_mono _ fun x hx => ne_of_lt hx),
    h2.mono_left (nhdsWithin_mono _ fun x hx => ne_of_gt hx)⟩

/-- Hole: `f = g` near `c` (but at `c`), `g` continuous at `c`, so the limit of `f` at `c` is `g c`. -/
private theorem x4_hole {f g : ℝ → ℝ} {c : ℝ} (hg : ContinuousAt g c)
    (hf : ∀ x, x ≠ c → |x - c| < 1 → f x = g x) : Tendsto f (𝓝[≠] c) (𝓝 (g c)) := by
  refine (hg.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds c one_pos)]
    with x hx1 hx2
  rw [Metric.mem_ball, Real.dist_eq] at hx2
  exact (hf x hx1 hx2).symm

/-- `f - g → 0` at both infinities when `f - g = p/q` off the roots of `q` and `deg p < deg q`. -/
private theorem x4_diff_ends (f g : ℝ → ℝ) (p q : ℝ[X]) (m n : ℕ) (hp : p.natDegree ≤ m)
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
private theorem x4_hor (f : ℝ → ℝ) (c : ℝ) (p q : ℝ[X]) (m n : ℕ) (hp : p.natDegree ≤ m)
    (hq : q.natDegree = n) (hmn : m < n) (h : ∀ x, q.eval x ≠ 0 → f x - c = p.eval x / q.eval x) :
    Tendsto f atTop (𝓝 c) ∧ Tendsto f atBot (𝓝 c) := by
  obtain ⟨h1, h2⟩ := x4_diff_ends f (fun _ => c) p q m n hp hq hmn h
  exact ⟨tendsto_sub_nhds_zero_iff.mp h1, tendsto_sub_nhds_zero_iff.mp h2⟩

local macro "ev_simp" : tactic =>
  `(tactic| simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X, eval_neg, eval_one] at *)

/-! ## Section 4.2 -/

/-- Stitz-Zeager Exercise 4.2.1: `f(x) = 4/(x+2)` has `y`-intercept `(0, 2)`, no `x`-intercept, the vertical
asymptote `x = -2` (`f → -∞` from the left, `f → ∞` from the right), and the horizontal asymptote `y = 0`. -/
@[kb "stitzzeager2013" "Exercise 4.2.1, p. 345"]
theorem exer_4_2_1 :
    4 / ((0 : ℝ) + 2) = 2 ∧ (∀ x : ℝ, x ≠ -2 → 4 / (x + 2) ≠ 0) ∧
    Tendsto (fun x : ℝ => 4 / (x + 2)) (𝓝[<] (-2)) atBot ∧
    Tendsto (fun x : ℝ => 4 / (x + 2)) (𝓝[>] (-2)) atTop ∧
    Tendsto (fun x : ℝ => 4 / (x + 2)) atBot (𝓝 0) ∧ Tendsto (fun x : ℝ => 4 / (x + 2)) atTop (𝓝 0) := by
  have hv : ∀ x : ℝ, x ≠ -2 → |x - (-2)| < 1 → 4 / (x + 2) = 4 / (x - (-2)) := by
    intro x _ _
    rw [sub_neg_eq_add]
  have hh := x4_hor (fun x : ℝ => 4 / (x + 2)) 0 (C 4) (X + C 2) 0 1
    (by compute_degree) (by compute_degree!) (by norm_num) (fun x hx => by
      ev_simp
      rw [eq_div_iff hx, sub_mul, div_mul_cancel₀ _ hx]
      ring)
  refine ⟨by norm_num, fun x hx => div_ne_zero (by norm_num) (fun h => hx (by linarith)),
    x4_pole_lb (g := fun _ => (4 : ℝ)) continuousAt_const (by norm_num) hv,
    x4_pole_rt (g := fun _ => (4 : ℝ)) continuousAt_const (by norm_num) hv, hh.2, hh.1⟩

/-- Stitz-Zeager Exercise 4.2.2: `f(x) = 5x/(6-2x)` has intercept `(0, 0)` (the only zero away from `x = 3`), the
vertical asymptote `x = 3` (`f → ∞` from the left, `f → -∞` from the right) and the horizontal asymptote
`y = -5/2`. -/
@[kb "stitzzeager2013" "Exercise 4.2.2, p. 345"]
theorem exer_4_2_2 :
    5 * (0 : ℝ) / (6 - 2 * 0) = 0 ∧ (∀ x : ℝ, x ≠ 3 → (5 * x / (6 - 2 * x) = 0 ↔ x = 0)) ∧
    Tendsto (fun x : ℝ => 5 * x / (6 - 2 * x)) (𝓝[<] 3) atTop ∧
    Tendsto (fun x : ℝ => 5 * x / (6 - 2 * x)) (𝓝[>] 3) atBot ∧
    Tendsto (fun x : ℝ => 5 * x / (6 - 2 * x)) atBot (𝓝 (-5 / 2)) ∧
    Tendsto (fun x : ℝ => 5 * x / (6 - 2 * x)) atTop (𝓝 (-5 / 2)) := by
  have hv : ∀ x : ℝ, x ≠ 3 → |x - 3| < 1 → 5 * x / (6 - 2 * x) = (5 * x / (-2)) / (x - 3) := by
    intro x _ _
    rw [div_div]
    congr 1
    ring
  have hg : ContinuousAt (fun x : ℝ => 5 * x / (-2)) 3 := by fun_prop
  have hh := x4_hor (fun x : ℝ => 5 * x / (6 - 2 * x)) (-5 / 2) (C 15) (C 6 - C 2 * X) 0 1
    (by compute_degree) (by compute_degree!) (by norm_num) (fun x hx => by
      ev_simp
      rw [eq_div_iff hx, sub_mul, div_mul_cancel₀ _ hx]
      ring)
  refine ⟨by norm_num, fun x hx => ?_, x4_pole_lt hg (by norm_num) hv, x4_pole_rb hg (by norm_num) hv,
    hh.2, hh.1⟩
  have h6 : 6 - 2 * x ≠ 0 := fun h => hx (by linarith)
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · linarith
    · exact absurd h h6
  · intro h
    left
    rw [h]
    norm_num

/-- Stitz-Zeager Exercise 4.2.3: `f(x) = 1/x²` has the vertical asymptote `x = 0` (`f → ∞` from both sides) and the
horizontal asymptote `y = 0`, approached from above at both ends. -/
@[kb "stitzzeager2013" "Exercise 4.2.3, p. 345"]
theorem exer_4_2_3 :
    Tendsto (fun x : ℝ => 1 / x ^ 2) (𝓝[<] 0) atTop ∧ Tendsto (fun x : ℝ => 1 / x ^ 2) (𝓝[>] 0) atTop ∧
    Tendsto (fun x : ℝ => 1 / x ^ 2) atBot (𝓝[>] 0) ∧ Tendsto (fun x : ℝ => 1 / x ^ 2) atTop (𝓝[>] 0) := by
  have hv : ∀ x : ℝ, x ≠ 0 → |x - 0| < 1 → 1 / x ^ 2 = 1 / (x - 0) ^ 2 := by
    intro x _ _
    rw [sub_zero]
  have hh := x4_hor (fun x : ℝ => 1 / x ^ 2) 0 (C 1) (X ^ 2) 0 2
    (by compute_degree) (by compute_degree!) (by norm_num) (fun x hx => by
      ev_simp
      rw [sub_zero])
  have hp := x4_pole2 (g := fun _ => (1 : ℝ)) continuousAt_const (by norm_num) hv
  refine ⟨hp.1, hp.2, tendsto_nhdsWithin_iff.mpr ⟨hh.2, ?_⟩, tendsto_nhdsWithin_iff.mpr ⟨hh.1, ?_⟩⟩
  · filter_upwards [eventually_lt_atBot 0] with x hx
    show 0 < 1 / x ^ 2
    have : x ≠ 0 := ne_of_lt hx
    positivity
  · filter_upwards [eventually_gt_atTop 0] with x hx
    show 0 < 1 / x ^ 2
    positivity

/-- Stitz-Zeager Exercise 4.2.4: `f(x) = 1/(x²+x-12)` has `y`-intercept `(0, -1/12)`, vertical asymptotes `x = -4`
(`f → ∞` from the left, `-∞` from the right) and `x = 3` (`-∞` from the left, `∞` from the right), and the horizontal
asymptote `y = 0`. -/
@[kb "stitzzeager2013" "Exercise 4.2.4, p. 345"]
theorem exer_4_2_4 :
    1 / ((0 : ℝ) ^ 2 + 0 - 12) = -1 / 12 ∧
    (Tendsto (fun x : ℝ => 1 / (x ^ 2 + x - 12)) (𝓝[<] (-4)) atTop ∧
      Tendsto (fun x : ℝ => 1 / (x ^ 2 + x - 12)) (𝓝[>] (-4)) atBot) ∧
    (Tendsto (fun x : ℝ => 1 / (x ^ 2 + x - 12)) (𝓝[<] 3) atBot ∧
      Tendsto (fun x : ℝ => 1 / (x ^ 2 + x - 12)) (𝓝[>] 3) atTop) ∧
    Tendsto (fun x : ℝ => 1 / (x ^ 2 + x - 12)) atBot (𝓝 0) ∧
    Tendsto (fun x : ℝ => 1 / (x ^ 2 + x - 12)) atTop (𝓝 0) := by
  have hv1 : ∀ x : ℝ, x ≠ -4 → |x - (-4)| < 1 → 1 / (x ^ 2 + x - 12) = (1 / (x - 3)) / (x - (-4)) := by
    intro x _ _
    rw [div_div]
    congr 1
    ring
  have hv2 : ∀ x : ℝ, x ≠ 3 → |x - 3| < 1 → 1 / (x ^ 2 + x - 12) = (1 / (x + 4)) / (x - 3) := by
    intro x _ _
    rw [div_div]
    congr 1
    ring
  have hg1 : ContinuousAt (fun x : ℝ => 1 / (x - 3)) (-4) := by fun_prop (disch := norm_num)
  have hg2 : ContinuousAt (fun x : ℝ => 1 / (x + 4)) 3 := by fun_prop (disch := norm_num)
  have hh := x4_hor (fun x : ℝ => 1 / (x ^ 2 + x - 12)) 0 (C 1) (X ^ 2 + X - C 12) 0 2
    (by compute_degree) (by compute_degree!) (by norm_num) (fun x hx => by
      ev_simp
      rw [sub_zero])
  exact ⟨by norm_num, ⟨x4_pole_lt hg1 (by norm_num) hv1, x4_pole_rb hg1 (by norm_num) hv1⟩,
    ⟨x4_pole_lb hg2 (by norm_num) hv2, x4_pole_rt hg2 (by norm_num) hv2⟩, hh.2, hh.1⟩

/-- Stitz-Zeager Exercise 4.2.5: `f(x) = (2x-1)/(-2x²-5x+3)` equals `-1/(x+3)` away from `1/2` and `-3`, so it has a
hole at `(1/2, -2/7)`, `y`-intercept `(0, -1/3)`, the vertical asymptote `x = -3` (`f → ∞` from the left, `-∞` from
the right), and the horizontal asymptote `y = 0`. -/
@[kb "stitzzeager2013" "Exercise 4.2.5, p. 345"]
theorem exer_4_2_5 :
    (∀ x : ℝ, x ≠ 1 / 2 → x ≠ -3 → (2 * x - 1) / (-2 * x ^ 2 - 5 * x + 3) = -1 / (x + 3)) ∧
    (2 * (0 : ℝ) - 1) / (-2 * 0 ^ 2 - 5 * 0 + 3) = -1 / 3 ∧
    Tendsto (fun x : ℝ => (2 * x - 1) / (-2 * x ^ 2 - 5 * x + 3)) (𝓝[≠] (1 / 2)) (𝓝 (-2 / 7)) ∧
    Tendsto (fun x : ℝ => (2 * x - 1) / (-2 * x ^ 2 - 5 * x + 3)) (𝓝[<] (-3)) atTop ∧
    Tendsto (fun x : ℝ => (2 * x - 1) / (-2 * x ^ 2 - 5 * x + 3)) (𝓝[>] (-3)) atBot ∧
    Tendsto (fun x : ℝ => (2 * x - 1) / (-2 * x ^ 2 - 5 * x + 3)) atBot (𝓝 0) ∧
    Tendsto (fun x : ℝ => (2 * x - 1) / (-2 * x ^ 2 - 5 * x + 3)) atTop (𝓝 0) := by
  have key : ∀ x : ℝ, x ≠ 1 / 2 → x ≠ -3 → (2 * x - 1) / (-2 * x ^ 2 - 5 * x + 3) = -1 / (x + 3) := by
    intro x h1 h2
    have h1' : 2 * x - 1 ≠ 0 := fun h => h1 (by linarith)
    have h2' : x + 3 ≠ 0 := fun h => h2 (by linarith)
    have h3 : -2 * x ^ 2 - 5 * x + 3 ≠ 0 := by
      rw [show -2 * x ^ 2 - 5 * x + 3 = -((2 * x - 1) * (x + 3)) by ring]
      exact neg_ne_zero.mpr (mul_ne_zero h1' h2')
    rw [div_eq_div_iff h3 h2']
    ring
  have hg : ContinuousAt (fun x : ℝ => -1 / (x + 3)) (1 / 2) := by fun_prop (disch := norm_num)
  have hh := x4_hor (fun x : ℝ => (2 * x - 1) / (-2 * x ^ 2 - 5 * x + 3)) 0 (C 2 * X - C 1)
    (C (-2) * X ^ 2 - C 5 * X + C 3) 1 2 (by compute_degree) (by compute_degree!) (by norm_num)
    (fun x hx => by
      ev_simp
      rw [sub_zero])
  have hv : ∀ x : ℝ, x ≠ -3 → |x - (-3)| < 1 →
      (2 * x - 1) / (-2 * x ^ 2 - 5 * x + 3) = -1 / (x - (-3)) := by
    intro x hx hx1
    have h1 : x ≠ 1 / 2 := by
      intro h; have := abs_lt.mp hx1; linarith [this.1, this.2]
    rw [key x h1 hx, sub_neg_eq_add]
  refine ⟨key, by norm_num, ?_, x4_pole_lt (g := fun _ => (-1 : ℝ)) continuousAt_const (by norm_num) hv,
    x4_pole_rb (g := fun _ => (-1 : ℝ)) continuousAt_const (by norm_num) hv, hh.2, hh.1⟩
  have := x4_hole hg (f := fun x : ℝ => (2 * x - 1) / (-2 * x ^ 2 - 5 * x + 3)) (fun x hx hx1 => by
    have h2 : x ≠ -3 := by
      intro h; have := abs_lt.mp hx1; linarith [this.1, this.2]
    exact key x hx h2)
  convert this using 2
  norm_num

/-- Stitz-Zeager Exercise 4.2.10: `f(x) = (3x²-5x-2)/(x²-9)` has `x`-intercepts `(-1/3, 0)` and `(2, 0)`,
`y`-intercept `(0, 2/9)`, vertical asymptotes `x = -3` (`f → ∞` from the left, `-∞` from the right) and `x = 3`
(`-∞` from the left, `∞` from the right), and the horizontal asymptote `y = 3`. -/
@[kb "stitzzeager2013" "Exercise 4.2.10, p. 345"]
theorem exer_4_2_10 :
    (∀ x : ℝ, x ^ 2 - 9 ≠ 0 → ((3 * x ^ 2 - 5 * x - 2) / (x ^ 2 - 9) = 0 ↔ x = -1 / 3 ∨ x = 2)) ∧
    (3 * (0 : ℝ) ^ 2 - 5 * 0 - 2) / (0 ^ 2 - 9) = 2 / 9 ∧
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
  have hh := x4_hor (fun x : ℝ => (3 * x ^ 2 - 5 * x - 2) / (x ^ 2 - 9)) 3 (C (-5) * X + C 25)
    (X ^ 2 - C 9) 1 2 (by compute_degree) (by compute_degree!) (by norm_num) (fun x hx => by
      ev_simp
      rw [eq_div_iff hx, sub_mul, div_mul_cancel₀ _ hx]
      ring)
  refine ⟨fun x hx => ?_, by norm_num, ⟨x4_pole_lt hg1 (by norm_num) hv1, x4_pole_rb hg1 (by norm_num) hv1⟩,
    ⟨x4_pole_lb hg2 (by norm_num) hv2, x4_pole_rt hg2 (by norm_num) hv2⟩, hh.2, hh.1⟩
  rw [div_eq_zero_iff, show 3 * x ^ 2 - 5 * x - 2 = (3 * x + 1) * (x - 2) by ring, mul_eq_zero]
  constructor
  · rintro ((h | h) | h)
    · left; linarith
    · right; linarith
    · exact absurd h hx
  · rintro (h | h)
    · left; left; linarith
    · left; right; linarith

/-- Stitz-Zeager Exercise 4.2.11: `f(x) = (x²-x-6)/(x+1)` has `x`-intercepts `(-2, 0)` and `(3, 0)`, `y`-intercept
`(0, -6)`, the vertical asymptote `x = -1` (`f → ∞` from the left, `-∞` from the right) and the slant asymptote
`y = x - 2`. -/
@[kb "stitzzeager2013" "Exercise 4.2.11, p. 345"]
theorem exer_4_2_11 :
    (∀ x : ℝ, x + 1 ≠ 0 → ((x ^ 2 - x - 6) / (x + 1) = 0 ↔ x = -2 ∨ x = 3)) ∧
    ((0 : ℝ) ^ 2 - 0 - 6) / (0 + 1) = -6 ∧
    Tendsto (fun x : ℝ => (x ^ 2 - x - 6) / (x + 1)) (𝓝[<] (-1)) atTop ∧
    Tendsto (fun x : ℝ => (x ^ 2 - x - 6) / (x + 1)) (𝓝[>] (-1)) atBot ∧
    Tendsto (fun x : ℝ => (x ^ 2 - x - 6) / (x + 1) - (x - 2)) atBot (𝓝 0) ∧
    Tendsto (fun x : ℝ => (x ^ 2 - x - 6) / (x + 1) - (x - 2)) atTop (𝓝 0) := by
  have hv : ∀ x : ℝ, x ≠ -1 → |x - (-1)| < 1 →
      (x ^ 2 - x - 6) / (x + 1) = (x ^ 2 - x - 6) / (x - (-1)) := by
    intro x _ _
    rw [sub_neg_eq_add]
  have hg : ContinuousAt (fun x : ℝ => x ^ 2 - x - 6) (-1) := by fun_prop
  have hs := x4_diff_ends (fun x : ℝ => (x ^ 2 - x - 6) / (x + 1)) (fun x => x - 2) (C (-4)) (X + C 1)
    0 1 (by compute_degree) (by compute_degree!) (by norm_num) (fun x hx => by
      ev_simp
      rw [eq_div_iff hx, sub_mul, div_mul_cancel₀ _ hx]
      ring)
  refine ⟨fun x hx => ?_, by norm_num, x4_pole_lt hg (by norm_num) hv, x4_pole_rb hg (by norm_num) hv,
    hs.2, hs.1⟩
  rw [div_eq_zero_iff, show x ^ 2 - x - 6 = (x + 2) * (x - 3) by ring, mul_eq_zero]
  constructor
  · rintro ((h | h) | h)
    · left; linarith
    · right; linarith
    · exact absurd h hx
  · rintro (h | h)
    · left; left; linarith
    · left; right; linarith

/-- Stitz-Zeager Exercise 4.2.12: `f(x) = (x²-x)/(3-x)` has `x`-intercepts `(0, 0)` and `(1, 0)`, the vertical
asymptote `x = 3` (`f → ∞` from the left, `-∞` from the right) and the slant asymptote `y = -x - 2`. -/
@[kb "stitzzeager2013" "Exercise 4.2.12, p. 345"]
theorem exer_4_2_12 :
    (∀ x : ℝ, x ≠ 3 → ((x ^ 2 - x) / (3 - x) = 0 ↔ x = 0 ∨ x = 1)) ∧
    Tendsto (fun x : ℝ => (x ^ 2 - x) / (3 - x)) (𝓝[<] 3) atTop ∧
    Tendsto (fun x : ℝ => (x ^ 2 - x) / (3 - x)) (𝓝[>] 3) atBot ∧
    Tendsto (fun x : ℝ => (x ^ 2 - x) / (3 - x) - (-x - 2)) atBot (𝓝 0) ∧
    Tendsto (fun x : ℝ => (x ^ 2 - x) / (3 - x) - (-x - 2)) atTop (𝓝 0) := by
  have hv : ∀ x : ℝ, x ≠ 3 → |x - 3| < 1 → (x ^ 2 - x) / (3 - x) = (x - x ^ 2) / (x - 3) := by
    intro x hx _
    have h1 : x - 3 ≠ 0 := sub_ne_zero.mpr hx
    have h2 : 3 - x ≠ 0 := fun h => h1 (by linarith)
    rw [div_eq_div_iff h2 h1]
    ring
  have hg : ContinuousAt (fun x : ℝ => x - x ^ 2) 3 := by fun_prop
  have hs := x4_diff_ends (fun x : ℝ => (x ^ 2 - x) / (3 - x)) (fun x => -x - 2) (C 6) (C 3 - X)
    0 1 (by compute_degree) (by compute_degree!) (by norm_num) (fun x hx => by
      ev_simp
      rw [eq_div_iff hx, sub_mul, div_mul_cancel₀ _ hx]
      ring)
  refine ⟨fun x hx => ?_, x4_pole_lt hg (by norm_num) hv, x4_pole_rb hg (by norm_num) hv, hs.2, hs.1⟩
  have h6 : 3 - x ≠ 0 := fun h => hx (by linarith)
  rw [div_eq_zero_iff, show x ^ 2 - x = x * (x - 1) by ring, mul_eq_zero]
  constructor
  · rintro ((h | h) | h)
    · left; exact h
    · right; linarith
    · exact absurd h h6
  · rintro (h | h)
    · left; left; exact h
    · left; right; linarith

/-- Stitz-Zeager Exercise 4.2.15: `f(x) = (x³-2x²+3x)/(2x²+2)` is defined on all of `ℝ`, has the single zero
`x = 0`, and the slant asymptote `y = x/2 - 1` at both ends. -/
@[kb "stitzzeager2013" "Exercise 4.2.15, p. 345"]
theorem exer_4_2_15 :
    (∀ x : ℝ, 2 * x ^ 2 + 2 ≠ 0) ∧
    (∀ x : ℝ, (x ^ 3 - 2 * x ^ 2 + 3 * x) / (2 * x ^ 2 + 2) = 0 ↔ x = 0) ∧
    Tendsto (fun x : ℝ => (x ^ 3 - 2 * x ^ 2 + 3 * x) / (2 * x ^ 2 + 2) - (1 / 2 * x - 1)) atBot (𝓝 0) ∧
    Tendsto (fun x : ℝ => (x ^ 3 - 2 * x ^ 2 + 3 * x) / (2 * x ^ 2 + 2) - (1 / 2 * x - 1)) atTop (𝓝 0) := by
  have hne : ∀ x : ℝ, 2 * x ^ 2 + 2 ≠ 0 := fun x => by positivity
  have hs := x4_diff_ends (fun x : ℝ => (x ^ 3 - 2 * x ^ 2 + 3 * x) / (2 * x ^ 2 + 2))
    (fun x => 1 / 2 * x - 1) (C 2 * X + C 2) (C 2 * X ^ 2 + C 2) 1 2 (by compute_degree)
    (by compute_degree!) (by norm_num) (fun x hx => by
      ev_simp
      rw [eq_div_iff hx, sub_mul, div_mul_cancel₀ _ hx]
      ring)
  refine ⟨hne, fun x => ?_, hs.2, hs.1⟩
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · have h' : x * (x ^ 2 - 2 * x + 3) = 0 := by linarith
      rcases mul_eq_zero.mp h' with h'' | h''
      · exact h''
      · nlinarith [sq_nonneg (x - 1)]
    · exact absurd h (hne x)
  · intro h
    left
    rw [h]
    norm_num

/-- Stitz-Zeager Exercise 4.2.16: `f(x) = (x²-2x+1)/(x³+x²-2x)` equals `(x-1)/(x(x+2))` for `x ≠ 1`, so it has a hole
at `(1, 0)`, vertical asymptotes `x = -2` (`f → -∞` from the left, `∞` from the right) and `x = 0` (`∞` from the left,
`-∞` from the right), and the horizontal asymptote `y = 0`. -/
@[kb "stitzzeager2013" "Exercise 4.2.16, p. 345"]
theorem exer_4_2_16 :
    Tendsto (fun x : ℝ => (x ^ 2 - 2 * x + 1) / (x ^ 3 + x ^ 2 - 2 * x)) (𝓝[≠] 1) (𝓝 0) ∧
    (Tendsto (fun x : ℝ => (x ^ 2 - 2 * x + 1) / (x ^ 3 + x ^ 2 - 2 * x)) (𝓝[<] (-2)) atBot ∧
      Tendsto (fun x : ℝ => (x ^ 2 - 2 * x + 1) / (x ^ 3 + x ^ 2 - 2 * x)) (𝓝[>] (-2)) atTop) ∧
    (Tendsto (fun x : ℝ => (x ^ 2 - 2 * x + 1) / (x ^ 3 + x ^ 2 - 2 * x)) (𝓝[<] 0) atTop ∧
      Tendsto (fun x : ℝ => (x ^ 2 - 2 * x + 1) / (x ^ 3 + x ^ 2 - 2 * x)) (𝓝[>] 0) atBot) ∧
    Tendsto (fun x : ℝ => (x ^ 2 - 2 * x + 1) / (x ^ 3 + x ^ 2 - 2 * x)) atBot (𝓝 0) ∧
    Tendsto (fun x : ℝ => (x ^ 2 - 2 * x + 1) / (x ^ 3 + x ^ 2 - 2 * x)) atTop (𝓝 0) := by
  have key : ∀ x : ℝ, x ≠ 1 → x ≠ 0 → x ≠ -2 →
      (x ^ 2 - 2 * x + 1) / (x ^ 3 + x ^ 2 - 2 * x) = (x - 1) / (x * (x + 2)) := by
    intro x h1 h0 h2
    have h1' : x - 1 ≠ 0 := sub_ne_zero.mpr h1
    have h2' : x + 2 ≠ 0 := fun h => h2 (by linarith)
    have h3 : x ^ 3 + x ^ 2 - 2 * x ≠ 0 := by
      rw [show x ^ 3 + x ^ 2 - 2 * x = x * (x - 1) * (x + 2) by ring]
      exact mul_ne_zero (mul_ne_zero h0 h1') h2'
    rw [div_eq_div_iff h3 (mul_ne_zero h0 h2')]
    ring
  have hg : ContinuousAt (fun x : ℝ => (x - 1) / (x * (x + 2))) 1 := by fun_prop (disch := norm_num)
  have hg1 : ContinuousAt (fun x : ℝ => (x - 1) / x) (-2) := by fun_prop (disch := norm_num)
  have hg2 : ContinuousAt (fun x : ℝ => (x - 1) / (x + 2)) 0 := by fun_prop (disch := norm_num)
  have hh := x4_hor (fun x : ℝ => (x ^ 2 - 2 * x + 1) / (x ^ 3 + x ^ 2 - 2 * x)) 0
    (X ^ 2 - C 2 * X + C 1) (X ^ 3 + X ^ 2 - C 2 * X) 2 3 (by compute_degree) (by compute_degree!)
    (by norm_num) (fun x hx => by
      ev_simp
      rw [sub_zero])
  have hv1 : ∀ x : ℝ, x ≠ -2 → |x - (-2)| < 1 → (x ^ 2 - 2 * x + 1) / (x ^ 3 + x ^ 2 - 2 * x) =
      ((x - 1) / x) / (x - (-2)) := by
    intro x hx hx1
    have h0 : x ≠ 0 := by
      intro h; have := abs_lt.mp hx1; linarith [this.1, this.2]
    have h1 : x ≠ 1 := by
      intro h; have := abs_lt.mp hx1; linarith [this.1, this.2]
    rw [key x h1 h0 hx, div_div, sub_neg_eq_add]
  have hv2 : ∀ x : ℝ, x ≠ 0 → |x - 0| < 1 → (x ^ 2 - 2 * x + 1) / (x ^ 3 + x ^ 2 - 2 * x) =
      ((x - 1) / (x + 2)) / (x - 0) := by
    intro x hx hx1
    have h2 : x ≠ -2 := by
      intro h; have := abs_lt.mp hx1; linarith [this.1, this.2]
    have h1 : x ≠ 1 := by
      intro h; have := abs_lt.mp hx1; linarith [this.1, this.2]
    rw [key x h1 hx h2, div_div, sub_zero, mul_comm]
  refine ⟨?_, ⟨x4_pole_lb hg1 (by norm_num) hv1, x4_pole_rt hg1 (by norm_num) hv1⟩,
    ⟨x4_pole_lt hg2 (by norm_num) hv2, x4_pole_rb hg2 (by norm_num) hv2⟩, hh.2, hh.1⟩
  have := x4_hole hg (f := fun x : ℝ => (x ^ 2 - 2 * x + 1) / (x ^ 3 + x ^ 2 - 2 * x)) (fun x hx hx1 => by
    have h0 : x ≠ 0 := by
      intro h; have := abs_lt.mp hx1; linarith [this.1, this.2]
    have h2 : x ≠ -2 := by
      intro h; have := abs_lt.mp hx1; linarith [this.1, this.2]
    exact key x hx h0 h2)
  convert this using 2
  norm_num

/-- Stitz-Zeager Exercise 4.2.19: `h(x) = (-2x+1)/x` is the graph of `1/x` shifted down `2` units: for `x ≠ 0`,
`(-2x+1)/x = -2 + 1/x`. -/
@[kb "stitzzeager2013" "Exercise 4.2.19, p. 345"]
theorem exer_4_2_19 (x : ℝ) (hx : x ≠ 0) : (-2 * x + 1) / x = -2 + 1 / x := by
  field_simp

/-- Stitz-Zeager Exercise 4.2.20: `j(x) = (3x-7)/(x-2)` is a reflection and shifts of `1/x`: for `x ≠ 2`,
`(3x-7)/(x-2) = 3 - 1/(x-2)`. -/
@[kb "stitzzeager2013" "Exercise 4.2.20, p. 345"]
theorem exer_4_2_20 (x : ℝ) (hx : x ≠ 2) : (3 * x - 7) / (x - 2) = 3 - 1 / (x - 2) := by
  have h : x - 2 ≠ 0 := sub_ne_zero.mpr hx
  field_simp
  ring

end UndergradKB.Precalculus.Course
