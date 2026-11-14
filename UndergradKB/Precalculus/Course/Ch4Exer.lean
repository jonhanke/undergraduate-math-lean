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

/-! ## Section 4.1 -/

/-- Stitz-Zeager Exercise 4.1.1: `f(x) = x/(3x-6)` is defined exactly away from `x = 2`; `f → -∞` as `x → 2⁻`,
`f → ∞` as `x → 2⁺`, and `y = 1/3` is the horizontal asymptote at both ends. -/
@[kb "stitzzeager2013" "Exercise 4.1.1, p. 326"]
theorem exer_4_1_1 :
    (∀ x : ℝ, 3 * x - 6 ≠ 0 ↔ x ≠ 2) ∧
    Tendsto (fun x : ℝ => x / (3 * x - 6)) (𝓝[<] 2) atBot ∧
    Tendsto (fun x : ℝ => x / (3 * x - 6)) (𝓝[>] 2) atTop ∧
    Tendsto (fun x : ℝ => x / (3 * x - 6)) atBot (𝓝 (1 / 3)) ∧
    Tendsto (fun x : ℝ => x / (3 * x - 6)) atTop (𝓝 (1 / 3)) := by
  have hv : ∀ x : ℝ, x ≠ 2 → |x - 2| < 1 → x / (3 * x - 6) = (x / 3) / (x - 2) := by
    intro x _ _
    rw [div_div]
    congr 1
    ring
  have hg : ContinuousAt (fun x : ℝ => x / 3) 2 := by fun_prop
  have hh := x4_hor (fun x : ℝ => x / (3 * x - 6)) (1 / 3) (C 2) (C 3 * X - C 6) 0 1
    (by compute_degree) (by compute_degree!) (by norm_num) (fun x hx => by
      ev_simp
      rw [eq_div_iff hx, sub_mul, div_mul_cancel₀ _ hx]
      ring)
  refine ⟨fun x => ⟨fun h h' => h (by rw [h']; norm_num), fun h h' => h (by linarith)⟩,
    x4_pole_lb hg (by norm_num) hv, x4_pole_rt hg (by norm_num) hv, hh.2, hh.1⟩

/-- Stitz-Zeager Exercise 4.1.2: `f(x) = (3+7x)/(5-2x)` is defined exactly away from `x = 5/2`; `f → ∞` as
`x → (5/2)⁻`, `f → -∞` as `x → (5/2)⁺`, and `y = -7/2` is the horizontal asymptote at both ends. -/
@[kb "stitzzeager2013" "Exercise 4.1.2, p. 326"]
theorem exer_4_1_2 :
    (∀ x : ℝ, 5 - 2 * x ≠ 0 ↔ x ≠ 5 / 2) ∧
    Tendsto (fun x : ℝ => (3 + 7 * x) / (5 - 2 * x)) (𝓝[<] (5 / 2)) atTop ∧
    Tendsto (fun x : ℝ => (3 + 7 * x) / (5 - 2 * x)) (𝓝[>] (5 / 2)) atBot ∧
    Tendsto (fun x : ℝ => (3 + 7 * x) / (5 - 2 * x)) atBot (𝓝 (-7 / 2)) ∧
    Tendsto (fun x : ℝ => (3 + 7 * x) / (5 - 2 * x)) atTop (𝓝 (-7 / 2)) := by
  have hv : ∀ x : ℝ, x ≠ 5 / 2 → |x - 5 / 2| < 1 →
      (3 + 7 * x) / (5 - 2 * x) = ((3 + 7 * x) / (-2)) / (x - 5 / 2) := by
    intro x _ _
    rw [div_div]
    congr 1
    ring
  have hg : ContinuousAt (fun x : ℝ => (3 + 7 * x) / (-2)) (5 / 2) := by fun_prop
  have hh := x4_hor (fun x : ℝ => (3 + 7 * x) / (5 - 2 * x)) (-7 / 2) (C (41 / 2)) (C 5 - C 2 * X) 0 1
    (by compute_degree) (by compute_degree!) (by norm_num) (fun x hx => by
      ev_simp
      rw [eq_div_iff hx, sub_mul, div_mul_cancel₀ _ hx]
      ring)
  refine ⟨fun x => ⟨fun h h' => h (by rw [h']; norm_num), fun h h' => h (by linarith)⟩,
    x4_pole_lt hg (by norm_num) hv, x4_pole_rb hg (by norm_num) hv, hh.2, hh.1⟩

/-- Stitz-Zeager Exercise 4.1.3: `f(x) = x/(x²+x-12)` has vertical asymptotes `x = -4` (`f → -∞` from the left,
`f → ∞` from the right) and `x = 3` (same pattern), and horizontal asymptote `y = 0` at both ends. -/
@[kb "stitzzeager2013" "Exercise 4.1.3, p. 326"]
theorem exer_4_1_3 :
    (Tendsto (fun x : ℝ => x / (x ^ 2 + x - 12)) (𝓝[<] (-4)) atBot ∧
      Tendsto (fun x : ℝ => x / (x ^ 2 + x - 12)) (𝓝[>] (-4)) atTop) ∧
    (Tendsto (fun x : ℝ => x / (x ^ 2 + x - 12)) (𝓝[<] 3) atBot ∧
      Tendsto (fun x : ℝ => x / (x ^ 2 + x - 12)) (𝓝[>] 3) atTop) ∧
    Tendsto (fun x : ℝ => x / (x ^ 2 + x - 12)) atBot (𝓝 0) ∧
    Tendsto (fun x : ℝ => x / (x ^ 2 + x - 12)) atTop (𝓝 0) := by
  have hv1 : ∀ x : ℝ, x ≠ -4 → |x - (-4)| < 1 → x / (x ^ 2 + x - 12) = (x / (x - 3)) / (x - (-4)) := by
    intro x _ _
    rw [div_div]
    congr 1
    ring
  have hv2 : ∀ x : ℝ, x ≠ 3 → |x - 3| < 1 → x / (x ^ 2 + x - 12) = (x / (x + 4)) / (x - 3) := by
    intro x _ _
    rw [div_div]
    congr 1
    ring
  have hg1 : ContinuousAt (fun x : ℝ => x / (x - 3)) (-4) := by fun_prop (disch := norm_num)
  have hg2 : ContinuousAt (fun x : ℝ => x / (x + 4)) 3 := by fun_prop (disch := norm_num)
  have hh := x4_hor (fun x : ℝ => x / (x ^ 2 + x - 12)) 0 X (X ^ 2 + X - C 12) 1 2
    (by compute_degree) (by compute_degree!) (by norm_num) (fun x hx => by
      ev_simp
      rw [eq_div_iff hx, sub_mul, div_mul_cancel₀ _ hx]
      ring)
  exact ⟨⟨x4_pole_lb hg1 (by norm_num) hv1, x4_pole_rt hg1 (by norm_num) hv1⟩,
    ⟨x4_pole_lb hg2 (by norm_num) hv2, x4_pole_rt hg2 (by norm_num) hv2⟩, hh.2, hh.1⟩

/-- Stitz-Zeager Exercise 4.1.4: `f(x) = x/(x²+1)` is defined and continuous on all of `ℝ` (no vertical
asymptote, no hole) and has horizontal asymptote `y = 0` at both ends. -/
@[kb "stitzzeager2013" "Exercise 4.1.4, p. 326"]
theorem exer_4_1_4 :
    (∀ x : ℝ, x ^ 2 + 1 ≠ 0) ∧ Continuous (fun x : ℝ => x / (x ^ 2 + 1)) ∧
    Tendsto (fun x : ℝ => x / (x ^ 2 + 1)) atBot (𝓝 0) ∧
    Tendsto (fun x : ℝ => x / (x ^ 2 + 1)) atTop (𝓝 0) := by
  have hh := x4_hor (fun x : ℝ => x / (x ^ 2 + 1)) 0 X (X ^ 2 + 1) 1 2
    (by compute_degree) (by compute_degree!) (by norm_num) (fun x hx => by
      ev_simp
      simp)
  exact ⟨fun x => by positivity,
    Continuous.div (f := fun x : ℝ => x) (g := fun x : ℝ => x ^ 2 + 1) continuous_id
      (by fun_prop) (fun x => by positivity), hh.2, hh.1⟩

/-- Stitz-Zeager Exercise 4.1.5: `f(x) = (x+7)/(x+3)²` has the vertical asymptote `x = -3` (`f → ∞` from both
sides) and horizontal asymptote `y = 0` at both ends. -/
@[kb "stitzzeager2013" "Exercise 4.1.5, p. 326"]
theorem exer_4_1_5 :
    Tendsto (fun x : ℝ => (x + 7) / (x + 3) ^ 2) (𝓝[<] (-3)) atTop ∧
    Tendsto (fun x : ℝ => (x + 7) / (x + 3) ^ 2) (𝓝[>] (-3)) atTop ∧
    Tendsto (fun x : ℝ => (x + 7) / (x + 3) ^ 2) atBot (𝓝 0) ∧
    Tendsto (fun x : ℝ => (x + 7) / (x + 3) ^ 2) atTop (𝓝 0) := by
  have hv : ∀ x : ℝ, x ≠ -3 → |x - (-3)| < 1 → (x + 7) / (x + 3) ^ 2 = (x + 7) / (x - (-3)) ^ 2 := by
    intro x _ _
    ring_nf
  have hg : ContinuousAt (fun x : ℝ => x + 7) (-3) := by fun_prop
  have hh := x4_hor (fun x : ℝ => (x + 7) / (x + 3) ^ 2) 0 (X + C 7) ((X + C 3) ^ 2) 1 2
    (by compute_degree) (by compute_degree!) (by norm_num) (fun x hx => by
      ev_simp
      simp)
  have := x4_pole2 hg (by norm_num) hv
  exact ⟨this.1, this.2, hh.2, hh.1⟩

/-- Stitz-Zeager Exercise 4.1.6: `f(x) = (x³+1)/(x²-1)` has a hole at `(-1, -3/2)` (the values tend to `-3/2` as
`x → -1`, `x ≠ -1`), the vertical asymptote `x = 1` (`f → -∞` from the left, `f → ∞` from the right), and the slant
asymptote `y = x` at both ends. -/
@[kb "stitzzeager2013" "Exercise 4.1.6, p. 326"]
theorem exer_4_1_6 :
    Tendsto (fun x : ℝ => (x ^ 3 + 1) / (x ^ 2 - 1)) (𝓝[≠] (-1)) (𝓝 (-3 / 2)) ∧
    Tendsto (fun x : ℝ => (x ^ 3 + 1) / (x ^ 2 - 1)) (𝓝[<] 1) atBot ∧
    Tendsto (fun x : ℝ => (x ^ 3 + 1) / (x ^ 2 - 1)) (𝓝[>] 1) atTop ∧
    Tendsto (fun x : ℝ => (x ^ 3 + 1) / (x ^ 2 - 1) - x) atBot (𝓝 0) ∧
    Tendsto (fun x : ℝ => (x ^ 3 + 1) / (x ^ 2 - 1) - x) atTop (𝓝 0) := by
  have key : ∀ x : ℝ, x + 1 ≠ 0 → x - 1 ≠ 0 → (x ^ 3 + 1) / (x ^ 2 - 1) = (x ^ 2 - x + 1) / (x - 1) := by
    intro x h1 h2
    have h3 : x ^ 2 - 1 ≠ 0 := by
      rw [show x ^ 2 - 1 = (x + 1) * (x - 1) by ring]; exact mul_ne_zero h1 h2
    rw [div_eq_div_iff h3 h2]
    ring
  have hg : ContinuousAt (fun x : ℝ => (x ^ 2 - x + 1) / (x - 1)) (-1) := by
    fun_prop (disch := norm_num)
  have hg1 : ContinuousAt (fun x : ℝ => x ^ 2 - x + 1) 1 := by fun_prop
  have hs := x4_diff_ends (fun x : ℝ => (x ^ 3 + 1) / (x ^ 2 - 1)) (fun x => x) (X + C 1) (X ^ 2 - C 1) 1 2
    (by compute_degree) (by compute_degree!) (by norm_num) (fun x hx => by
      ev_simp
      rw [eq_div_iff hx, sub_mul, div_mul_cancel₀ _ hx]
      ring)
  refine ⟨?_, x4_pole_lb hg1 (by norm_num) ?_, x4_pole_rt hg1 (by norm_num) ?_, hs.2, hs.1⟩
  · have := x4_hole hg (f := fun x : ℝ => (x ^ 3 + 1) / (x ^ 2 - 1)) (fun x hx hx1 => by
      have h1 : x + 1 ≠ 0 := fun h => hx (by linarith)
      have h2 : x - 1 ≠ 0 := by
        intro h; have := abs_lt.mp hx1; linarith [this.1, this.2]
      exact key x h1 h2)
    convert this using 2
    norm_num
  · intro x hx hx1
    have h1 : x + 1 ≠ 0 := by
      intro h; have := abs_lt.mp hx1; linarith [this.1, this.2]
    exact key x h1 (sub_ne_zero.mpr hx)
  · intro x hx hx1
    have h1 : x + 1 ≠ 0 := by
      intro h; have := abs_lt.mp hx1; linarith [this.1, this.2]
    exact key x h1 (sub_ne_zero.mpr hx)

/-- Stitz-Zeager Exercise 4.1.9: `f(x) = (x²-x-12)/(x²+x-6)` has a hole at `(-3, 7/5)`, the vertical asymptote
`x = 2` (`f → ∞` from the left, `f → -∞` from the right), and the horizontal asymptote `y = 1`. -/
@[kb "stitzzeager2013" "Exercise 4.1.9, p. 326"]
theorem exer_4_1_9 :
    Tendsto (fun x : ℝ => (x ^ 2 - x - 12) / (x ^ 2 + x - 6)) (𝓝[≠] (-3)) (𝓝 (7 / 5)) ∧
    Tendsto (fun x : ℝ => (x ^ 2 - x - 12) / (x ^ 2 + x - 6)) (𝓝[<] 2) atTop ∧
    Tendsto (fun x : ℝ => (x ^ 2 - x - 12) / (x ^ 2 + x - 6)) (𝓝[>] 2) atBot ∧
    Tendsto (fun x : ℝ => (x ^ 2 - x - 12) / (x ^ 2 + x - 6)) atBot (𝓝 1) ∧
    Tendsto (fun x : ℝ => (x ^ 2 - x - 12) / (x ^ 2 + x - 6)) atTop (𝓝 1) := by
  have key : ∀ x : ℝ, x + 3 ≠ 0 → x - 2 ≠ 0 → (x ^ 2 - x - 12) / (x ^ 2 + x - 6) = (x - 4) / (x - 2) := by
    intro x h1 h2
    have h3 : x ^ 2 + x - 6 ≠ 0 := by
      rw [show x ^ 2 + x - 6 = (x + 3) * (x - 2) by ring]; exact mul_ne_zero h1 h2
    rw [div_eq_div_iff h3 h2]
    ring
  have hg : ContinuousAt (fun x : ℝ => (x - 4) / (x - 2)) (-3) := by fun_prop (disch := norm_num)
  have hg1 : ContinuousAt (fun x : ℝ => x - 4) 2 := by fun_prop
  have hh := x4_hor (fun x : ℝ => (x ^ 2 - x - 12) / (x ^ 2 + x - 6)) 1 (C (-2) * X - C 6)
    (X ^ 2 + X - C 6) 1 2 (by compute_degree) (by compute_degree!) (by norm_num) (fun x hx => by
      ev_simp
      rw [eq_div_iff hx, sub_mul, div_mul_cancel₀ _ hx]
      ring)
  have hv : ∀ x : ℝ, x ≠ 2 → |x - 2| < 1 → (x ^ 2 - x - 12) / (x ^ 2 + x - 6) = (x - 4) / (x - 2) := by
    intro x hx hx1
    have h1 : x + 3 ≠ 0 := by
      intro h; have := abs_lt.mp hx1; linarith [this.1, this.2]
    exact key x h1 (sub_ne_zero.mpr hx)
  refine ⟨?_, x4_pole_lt hg1 (by norm_num) hv, x4_pole_rb hg1 (by norm_num) hv, hh.2, hh.1⟩
  have := x4_hole hg (f := fun x : ℝ => (x ^ 2 - x - 12) / (x ^ 2 + x - 6)) (fun x hx hx1 => by
    have h2 : x - 2 ≠ 0 := by
      intro h; have := abs_lt.mp hx1; linarith [this.1, this.2]
    exact key x (fun h => hx (by linarith)) h2)
  convert this using 2
  norm_num

/-- Stitz-Zeager Exercise 4.1.11: `f(x) = (x³+2x²+x)/(x²-x-2)` has a hole at `(-1, 0)`, the vertical asymptote
`x = 2` (`f → -∞` from the left, `f → ∞` from the right), and the slant asymptote `y = x + 3` at both ends. -/
@[kb "stitzzeager2013" "Exercise 4.1.11, p. 326"]
theorem exer_4_1_11 :
    Tendsto (fun x : ℝ => (x ^ 3 + 2 * x ^ 2 + x) / (x ^ 2 - x - 2)) (𝓝[≠] (-1)) (𝓝 0) ∧
    Tendsto (fun x : ℝ => (x ^ 3 + 2 * x ^ 2 + x) / (x ^ 2 - x - 2)) (𝓝[<] 2) atBot ∧
    Tendsto (fun x : ℝ => (x ^ 3 + 2 * x ^ 2 + x) / (x ^ 2 - x - 2)) (𝓝[>] 2) atTop ∧
    Tendsto (fun x : ℝ => (x ^ 3 + 2 * x ^ 2 + x) / (x ^ 2 - x - 2) - (x + 3)) atBot (𝓝 0) ∧
    Tendsto (fun x : ℝ => (x ^ 3 + 2 * x ^ 2 + x) / (x ^ 2 - x - 2) - (x + 3)) atTop (𝓝 0) := by
  have key : ∀ x : ℝ, x + 1 ≠ 0 → x - 2 ≠ 0 →
      (x ^ 3 + 2 * x ^ 2 + x) / (x ^ 2 - x - 2) = (x ^ 2 + x) / (x - 2) := by
    intro x h1 h2
    have h3 : x ^ 2 - x - 2 ≠ 0 := by
      rw [show x ^ 2 - x - 2 = (x + 1) * (x - 2) by ring]; exact mul_ne_zero h1 h2
    rw [div_eq_div_iff h3 h2]
    ring
  have hg : ContinuousAt (fun x : ℝ => (x ^ 2 + x) / (x - 2)) (-1) := by fun_prop (disch := norm_num)
  have hg1 : ContinuousAt (fun x : ℝ => x ^ 2 + x) 2 := by fun_prop
  have hs := x4_diff_ends (fun x : ℝ => (x ^ 3 + 2 * x ^ 2 + x) / (x ^ 2 - x - 2)) (fun x => x + 3)
    (C 6 * X + C 6) (X ^ 2 - X - C 2) 1 2 (by compute_degree) (by compute_degree!) (by norm_num)
    (fun x hx => by
      ev_simp
      rw [eq_div_iff hx, sub_mul, div_mul_cancel₀ _ hx]
      ring)
  have hv : ∀ x : ℝ, x ≠ 2 → |x - 2| < 1 →
      (x ^ 3 + 2 * x ^ 2 + x) / (x ^ 2 - x - 2) = (x ^ 2 + x) / (x - 2) := by
    intro x hx hx1
    have h1 : x + 1 ≠ 0 := by
      intro h; have := abs_lt.mp hx1; linarith [this.1, this.2]
    exact key x h1 (sub_ne_zero.mpr hx)
  refine ⟨?_, x4_pole_lb hg1 (by norm_num) hv, x4_pole_rt hg1 (by norm_num) hv, hs.2, hs.1⟩
  have := x4_hole hg (f := fun x : ℝ => (x ^ 3 + 2 * x ^ 2 + x) / (x ^ 2 - x - 2)) (fun x hx hx1 => by
    have h2 : x - 2 ≠ 0 := by
      intro h; have := abs_lt.mp hx1; linarith [this.1, this.2]
    exact key x (fun h => hx (by linarith)) h2)
  convert this using 2
  norm_num

/-- Stitz-Zeager Exercise 4.1.13: `f(x) = (2x²+5x-3)/(3x+2)` has the vertical asymptote `x = -2/3` (`f → ∞` from
the left, `f → -∞` from the right) and the slant asymptote `y = (2/3)x + 11/9` at both ends. -/
@[kb "stitzzeager2013" "Exercise 4.1.13, p. 326"]
theorem exer_4_1_13 :
    Tendsto (fun x : ℝ => (2 * x ^ 2 + 5 * x - 3) / (3 * x + 2)) (𝓝[<] (-2 / 3)) atTop ∧
    Tendsto (fun x : ℝ => (2 * x ^ 2 + 5 * x - 3) / (3 * x + 2)) (𝓝[>] (-2 / 3)) atBot ∧
    Tendsto (fun x : ℝ => (2 * x ^ 2 + 5 * x - 3) / (3 * x + 2) - (2 / 3 * x + 11 / 9)) atBot (𝓝 0) ∧
    Tendsto (fun x : ℝ => (2 * x ^ 2 + 5 * x - 3) / (3 * x + 2) - (2 / 3 * x + 11 / 9)) atTop (𝓝 0) := by
  have hv : ∀ x : ℝ, x ≠ -2 / 3 → |x - (-2 / 3)| < 1 →
      (2 * x ^ 2 + 5 * x - 3) / (3 * x + 2) = ((2 * x ^ 2 + 5 * x - 3) / 3) / (x - (-2 / 3)) := by
    intro x _ _
    rw [div_div]
    congr 1
    ring
  have hg : ContinuousAt (fun x : ℝ => (2 * x ^ 2 + 5 * x - 3) / 3) (-2 / 3) := by fun_prop
  have hs := x4_diff_ends (fun x : ℝ => (2 * x ^ 2 + 5 * x - 3) / (3 * x + 2))
    (fun x => 2 / 3 * x + 11 / 9) (C (-49 / 9)) (C 3 * X + C 2) 0 1 (by compute_degree)
    (by compute_degree!) (by norm_num) (fun x hx => by
      ev_simp
      rw [eq_div_iff hx, sub_mul, div_mul_cancel₀ _ hx]
      ring)
  exact ⟨x4_pole_lt hg (by norm_num) hv, x4_pole_rb hg (by norm_num) hv, hs.2, hs.1⟩

/-- Stitz-Zeager Exercise 4.1.17: `f(x) = (18-2x²)/(x²-9)` equals `-2` wherever it is defined, so the graph has
holes at `(-3, -2)` and `(3, -2)` (limit `-2` at both) and the horizontal asymptote `y = -2`. -/
@[kb "stitzzeager2013" "Exercise 4.1.17, p. 326"]
theorem exer_4_1_17 :
    (∀ x : ℝ, x ^ 2 - 9 ≠ 0 → (18 - 2 * x ^ 2) / (x ^ 2 - 9) = -2) ∧
    Tendsto (fun x : ℝ => (18 - 2 * x ^ 2) / (x ^ 2 - 9)) (𝓝[≠] (-3)) (𝓝 (-2)) ∧
    Tendsto (fun x : ℝ => (18 - 2 * x ^ 2) / (x ^ 2 - 9)) (𝓝[≠] 3) (𝓝 (-2)) ∧
    Tendsto (fun x : ℝ => (18 - 2 * x ^ 2) / (x ^ 2 - 9)) atBot (𝓝 (-2)) ∧
    Tendsto (fun x : ℝ => (18 - 2 * x ^ 2) / (x ^ 2 - 9)) atTop (𝓝 (-2)) := by
  have key : ∀ x : ℝ, x ^ 2 - 9 ≠ 0 → (18 - 2 * x ^ 2) / (x ^ 2 - 9) = -2 := by
    intro x hx
    rw [div_eq_iff hx]
    ring
  have hh := x4_hor (fun x : ℝ => (18 - 2 * x ^ 2) / (x ^ 2 - 9)) (-2) 0 (X ^ 2 - C 9) 0 2
    (by simp) (by compute_degree!) (by norm_num) (fun x hx => by
      ev_simp
      rw [key x hx]
      simp)
  refine ⟨key, ?_, ?_, hh.2, hh.1⟩
  · have := x4_hole (f := fun x : ℝ => (18 - 2 * x ^ 2) / (x ^ 2 - 9)) (g := fun _ => (-2 : ℝ))
      (c := -3) continuousAt_const (fun x hx hx1 => by
        apply key
        have h1 : x - 3 ≠ 0 := by
          intro h; have := abs_lt.mp hx1; linarith [this.1, this.2]
        rw [show x ^ 2 - 9 = (x - (-3)) * (x - 3) by ring]
        exact mul_ne_zero (sub_ne_zero.mpr hx) h1)
    exact this
  · have := x4_hole (f := fun x : ℝ => (18 - 2 * x ^ 2) / (x ^ 2 - 9)) (g := fun _ => (-2 : ℝ))
      (c := 3) continuousAt_const (fun x hx hx1 => by
        apply key
        have h1 : x + 3 ≠ 0 := by
          intro h; have := abs_lt.mp hx1; linarith [this.1, this.2]
        rw [show x ^ 2 - 9 = (x - 3) * (x + 3) by ring]
        exact mul_ne_zero (sub_ne_zero.mpr hx) h1)
    exact this

/-- Stitz-Zeager Exercise 4.1.18: `(x³-4x²-4x-5)/(x²+x+1)` is defined for every real `x` and equals `x - 5`
everywhere (no vertical asymptote, no hole, the slant asymptote is the graph itself). -/
@[kb "stitzzeager2013" "Exercise 4.1.18, p. 326"]
theorem exer_4_1_18 :
    (∀ x : ℝ, x ^ 2 + x + 1 ≠ 0) ∧
    ∀ x : ℝ, (x ^ 3 - 4 * x ^ 2 - 4 * x - 5) / (x ^ 2 + x + 1) = x - 5 := by
  have hne : ∀ x : ℝ, x ^ 2 + x + 1 ≠ 0 := fun x => ne_of_gt (by nlinarith [sq_nonneg (x + 1 / 2)])
  refine ⟨hne, fun x => ?_⟩
  rw [div_eq_iff (hne x)]
  ring

/-- Stitz-Zeager Exercise 4.1.19: for the cost `C(p) = 1770p/(100-p)`, `0 ≤ p < 100`, of removing `p`% of the
fish: `C(25) = 590`, `C(95) = 33630`, the cost grows without bound as `p → 100⁻`, and `C(p) = 40000` exactly when
`p = 400000/4177`, which is about `95.76` (here `95.75 < p < 95.77`). -/
@[kb "stitzzeager2013" "Exercise 4.1.19, p. 326"]
theorem exer_4_1_19 :
    1770 * (25 : ℝ) / (100 - 25) = 590 ∧ 1770 * (95 : ℝ) / (100 - 95) = 33630 ∧
    Tendsto (fun p : ℝ => 1770 * p / (100 - p)) (𝓝[<] 100) atTop ∧
    (∀ p : ℝ, p < 100 → (1770 * p / (100 - p) = 40000 ↔ p = 400000 / 4177)) ∧
    (95.75 : ℝ) < 400000 / 4177 ∧ (400000 / 4177 : ℝ) < 95.77 := by
  have hv : ∀ p : ℝ, p ≠ 100 → |p - 100| < 1 → 1770 * p / (100 - p) = (-1770 * p) / (p - 100) := by
    intro p hp _
    have h1 : p - 100 ≠ 0 := sub_ne_zero.mpr hp
    have h2 : 100 - p ≠ 0 := fun h => h1 (by linarith)
    rw [div_eq_div_iff h2 h1]
    ring
  have hg : ContinuousAt (fun p : ℝ => -1770 * p) 100 := by fun_prop
  refine ⟨by norm_num, by norm_num, x4_pole_lt hg (by norm_num) hv, fun p hp => ?_, by norm_num,
    by norm_num⟩
  have h2 : 100 - p ≠ 0 := by intro h; linarith
  rw [div_eq_iff h2]
  constructor
  · intro h; linarith
  · rintro rfl; norm_num

/-- Stitz-Zeager Exercise 4.1.20: the population model `P(t) = 150t/(t+15)` has the horizontal asymptote `y = 150`
as `t → ∞`: the population levels off at `150`. -/
@[kb "stitzzeager2013" "Exercise 4.1.20, p. 326"]
theorem exer_4_1_20 : Tendsto (fun t : ℝ => 150 * t / (t + 15)) atTop (𝓝 150) := by
  have hh := x4_hor (fun t : ℝ => 150 * t / (t + 15)) 150 (C (-2250)) (X + C 15) 0 1
    (by compute_degree) (by compute_degree!) (by norm_num) (fun x hx => by
      ev_simp
      rw [eq_div_iff hx, sub_mul, div_mul_cancel₀ _ hx]
      ring)
  exact hh.1

end UndergradKB.Precalculus.Course
