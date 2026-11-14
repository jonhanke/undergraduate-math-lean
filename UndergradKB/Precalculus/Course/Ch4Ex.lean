import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Polynomial
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.Rational
import UndergradKB.Precalculus.Course.Ch4

/-! # Course layer, Chapter 4 (Stitz-Zeager): worked examples -/

namespace UndergradKB.Precalculus.Course

open Polynomial Filter Topology Set

/-! ## Helpers -/

/-- Vertical asymptote from a right-hand pole: `f = p/q` near `c`, `q(c) = 0`, `p(c) ≠ 0`. -/
private theorem va_of {f : ℝ → ℝ} {p q : ℝ[X]} {c : ℝ} (hq : ∃ x, q.eval x ≠ 0) (hqc : q.eval c = 0)
    (hpc : p.eval c ≠ 0) (hf : ∀ x, x ≠ c → |x - c| < 1 → f x = p.eval x / q.eval x) :
    IsVerticalAsymptote f c := by
  have hq0 : q ≠ 0 := by
    obtain ⟨x, hx⟩ := hq
    rintro rfl
    simp at hx
  have hev : ∀ᶠ x in 𝓝[>] c, f x = p.eval x / q.eval x := by
    filter_upwards [Ioo_mem_nhdsGT (show c < c + 1 by linarith)] with x hx
    refine hf x (ne_of_gt hx.1) ?_
    rw [abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  rcases tendsto_div_of_eval_eq_zero_right hq0 hqc hpc with h | h
  · exact Or.inr (Or.inr (Or.inl (h.congr' (hev.mono fun x hx => hx.symm))))
  · exact Or.inr (Or.inr (Or.inr (h.congr' (hev.mono fun x hx => hx.symm))))

/-- A continuous function has no vertical asymptote. -/
private theorem not_va_of_continuous {f : ℝ → ℝ} (hf : Continuous f) (c : ℝ) :
    ¬ IsVerticalAsymptote f c := by
  have hl : Tendsto f (𝓝[<] c) (𝓝 (f c)) := (hf.tendsto c).mono_left nhdsWithin_le_nhds
  have hr : Tendsto f (𝓝[>] c) (𝓝 (f c)) := (hf.tendsto c).mono_left nhdsWithin_le_nhds
  rintro (h | h | h | h)
  · exact not_tendsto_atTop_of_tendsto_nhds hl h
  · exact not_tendsto_atBot_of_tendsto_nhds hl h
  · exact not_tendsto_atTop_of_tendsto_nhds hr h
  · exact not_tendsto_atBot_of_tendsto_nhds hr h

private theorem tendsto_div_zero_atTop (a b : ℝ) :
    Tendsto (fun x : ℝ => a / (x + b)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ b tendsto_id)

private theorem tendsto_div_zero_atBot (a b : ℝ) :
    Tendsto (fun x : ℝ => a / (x + b)) atBot (𝓝 0) :=
  tendsto_const_nhds.div_atBot (tendsto_atBot_add_const_right _ b tendsto_id)

/-- `p(x)/q(x) → 0` at both infinities when `deg p < deg q`. -/
private theorem tendsto_zero_ends (p q : ℝ[X]) (h : p.degree < q.degree) :
    Tendsto (fun x => p.eval x / q.eval x) atTop (𝓝 0) ∧
      Tendsto (fun x => p.eval x / q.eval x) atBot (𝓝 0) :=
  thm_4_2_horizontal_asymptote_numerator_smaller p q h

/-- Slant-asymptote helper: if `f(x) - (mx+b) = a/(x - c)` beyond `u` on the right and below `l` on the left,
then `f(x) - (mx+b) → 0` at both infinities. -/
private theorem slant_aux (f : ℝ → ℝ) (m b a c u l : ℝ)
    (hu : ∀ x, u < x → f x - (m * x + b) = a / (x + -c))
    (hl : ∀ x, x < l → f x - (m * x + b) = a / (x + -c)) :
    Tendsto (fun x => f x - (m * x + b)) atTop (𝓝 0) ∧
      Tendsto (fun x => f x - (m * x + b)) atBot (𝓝 0) :=
  ⟨(tendsto_div_zero_atTop a (-c)).congr'
      ((eventually_gt_atTop u).mono fun x hx => (hu x hx).symm),
   (tendsto_div_zero_atBot a (-c)).congr'
      ((eventually_lt_atBot l).mono fun x hx => (hl x hx).symm)⟩

/-! ## Section 4.1 -/

/-- Stitz-Zeager Example 4.1.1(b): for `x ≠ -1`, `2 - 3/(x+1)` equals `(2x-1)/(x+1)`. -/
@[kb "stitzzeager2013" "Example 4.1.1, p. 313"]
theorem ex_4_1_1_b (x : ℝ) (hx : x ≠ -1) : 2 - 3 / (x + 1) = (2 * x - 1) / (x + 1) := by
  have h : x + 1 ≠ 0 := fun h => hx (by linarith)
  field_simp
  ring

/-- Stitz-Zeager Example 4.1.1(c): for `x ≠ ±1`, the difference of the two fractions with denominator `x²-1`
simplifies to `(2x-1)/(x+1)`. -/
@[kb "stitzzeager2013" "Example 4.1.1, p. 313"]
theorem ex_4_1_1_c (x : ℝ) (h1 : x ≠ 1) (h2 : x ≠ -1) :
    (2 * x ^ 2 - 1) / (x ^ 2 - 1) - (3 * x - 2) / (x ^ 2 - 1) = (2 * x - 1) / (x + 1) := by
  have ha : x - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hb : x + 1 ≠ 0 := fun h => h2 (by linarith)
  have hc : x ^ 2 - 1 ≠ 0 := by
    rw [show x ^ 2 - 1 = (x - 1) * (x + 1) by ring]
    exact mul_ne_zero ha hb
  field_simp
  ring

/-- Stitz-Zeager Example 4.1.1(d): for `x ≠ ±1`, `x ≠ 2/3`, the quotient of the two fractions simplifies to
`(2x²-1)/(3x-2)`. -/
@[kb "stitzzeager2013" "Example 4.1.1, p. 313"]
theorem ex_4_1_1_d (x : ℝ) (h1 : x ≠ 1) (h2 : x ≠ -1) (h3 : x ≠ 2 / 3) :
    ((2 * x ^ 2 - 1) / (x ^ 2 - 1)) / ((3 * x - 2) / (x ^ 2 - 1)) = (2 * x ^ 2 - 1) / (3 * x - 2) := by
  have ha : x - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hb : x + 1 ≠ 0 := fun h => h2 (by linarith)
  have hc : x ^ 2 - 1 ≠ 0 := by
    rw [show x ^ 2 - 1 = (x - 1) * (x + 1) by ring]
    exact mul_ne_zero ha hb
  have hd : 3 * x - 2 ≠ 0 := fun h => h3 (by linarith)
  field_simp

/-- Stitz-Zeager Example 4.1.2(a): the lines `x = ±√3` are vertical asymptotes of `2x/(x²-3)`. -/
@[kb "stitzzeager2013" "Example 4.1.2, p. 318"]
theorem ex_4_1_2_a :
    IsVerticalAsymptote (fun x : ℝ => 2 * x / (x ^ 2 - 3)) (-Real.sqrt 3) ∧
    IsVerticalAsymptote (fun x : ℝ => 2 * x / (x ^ 2 - 3)) (Real.sqrt 3) := by
  have hs : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hf : ∀ x : ℝ, 2 * x / (x ^ 2 - 3) = (C 2 * X : ℝ[X]).eval x / (X ^ 2 - C 3 : ℝ[X]).eval x := by
    intro x; simp
  constructor
  · refine va_of (p := C 2 * X) (q := X ^ 2 - C 3) ⟨0, by simp⟩ (by simp [hsq]) (by simp)
      (fun x _ _ => hf x)
  · refine va_of (p := C 2 * X) (q := X ^ 2 - C 3) ⟨0, by simp⟩ (by simp [hsq]) (by simp)
      (fun x _ _ => hf x)

/-- Stitz-Zeager Example 4.1.2(b): `(x²-x-6)/(x²-9)` reduces to `(x+2)/(x+3)` away from `±3`; `x = -3` is a
vertical asymptote, and there is a hole at `(3, 5/6)`: the values tend to `5/6` as `x → 3`, `x ≠ 3`. -/
@[kb "stitzzeager2013" "Example 4.1.2, p. 318"]
theorem ex_4_1_2_b :
    (∀ x : ℝ, x ≠ 3 → x ≠ -3 → (x ^ 2 - x - 6) / (x ^ 2 - 9) = (x + 2) / (x + 3)) ∧
    IsVerticalAsymptote (fun x : ℝ => (x ^ 2 - x - 6) / (x ^ 2 - 9)) (-3) ∧
    Tendsto (fun x : ℝ => (x ^ 2 - x - 6) / (x ^ 2 - 9)) (𝓝[≠] 3) (𝓝 (5 / 6)) := by
  have key : ∀ x : ℝ, x ≠ 3 → x ≠ -3 → (x ^ 2 - x - 6) / (x ^ 2 - 9) = (x + 2) / (x + 3) := by
    intro x h1 h2
    have ha : x - 3 ≠ 0 := sub_ne_zero.mpr h1
    have hb : x + 3 ≠ 0 := fun h => h2 (by linarith)
    have hc : x ^ 2 - 9 ≠ 0 := by
      rw [show x ^ 2 - 9 = (x - 3) * (x + 3) by ring]
      exact mul_ne_zero ha hb
    field_simp
    ring
  refine ⟨key, ?_, ?_⟩
  · refine va_of (p := X + C 2) (q := X + C 3) ⟨0, by simp⟩ (by simp) (by norm_num)
      (fun x hx hx1 => ?_)
    have hb : x + 3 ≠ 0 := fun h => hx (by linarith)
    have h1 : x ≠ 3 := by
      intro h; rw [abs_lt] at hx1; linarith [hx1.1, hx1.2]
    simpa using key x h1 (fun h => hb (by linarith))
  · have hc : ContinuousAt (fun x : ℝ => (x + 2) / (x + 3)) 3 :=
      (continuousAt_id.add continuousAt_const).div (continuousAt_id.add continuousAt_const)
        (by show (3 : ℝ) + 3 ≠ 0; norm_num)
    have h1 : Tendsto (fun x : ℝ => (x + 2) / (x + 3)) (𝓝[≠] 3) (𝓝 (5 / 6)) := by
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {3}ᶜ))
      convert this using 2
      norm_num
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin,
      (eventually_ne_nhds (show (3 : ℝ) ≠ -3 by norm_num)).filter_mono nhdsWithin_le_nhds] with x h1 h2
    exact (key x h1 h2).symm

/-- Stitz-Zeager Example 4.1.2(c): `(x²-x-6)/(x²+9)` is defined for every real `x` and its graph has no
vertical asymptote and no hole. -/
@[kb "stitzzeager2013" "Example 4.1.2, p. 318"]
theorem ex_4_1_2_c :
    (∀ x : ℝ, x ^ 2 + 9 ≠ 0) ∧
    ∀ c : ℝ, ¬ IsVerticalAsymptote (fun x : ℝ => (x ^ 2 - x - 6) / (x ^ 2 + 9)) c := by
  refine ⟨fun x => by positivity, fun c => not_va_of_continuous ?_ c⟩
  exact Continuous.div (f := fun x : ℝ => x ^ 2 - x - 6) (g := fun x : ℝ => x ^ 2 + 9)
    (by fun_prop) (by fun_prop) (fun x => by positivity)

/-- Stitz-Zeager Example 4.1.2(d): `(x²-x-6)/(x²+4x+4)` reduces to `(x-3)/(x+2)` for `x ≠ -2`, and `x = -2` is
a vertical asymptote. -/
@[kb "stitzzeager2013" "Example 4.1.2, p. 318"]
theorem ex_4_1_2_d :
    (∀ x : ℝ, x ≠ -2 → (x ^ 2 - x - 6) / (x ^ 2 + 4 * x + 4) = (x - 3) / (x + 2)) ∧
    IsVerticalAsymptote (fun x : ℝ => (x ^ 2 - x - 6) / (x ^ 2 + 4 * x + 4)) (-2) := by
  have key : ∀ x : ℝ, x ≠ -2 → (x ^ 2 - x - 6) / (x ^ 2 + 4 * x + 4) = (x - 3) / (x + 2) := by
    intro x h
    have hb : x + 2 ≠ 0 := fun h' => h (by linarith)
    rw [show x ^ 2 + 4 * x + 4 = (x + 2) ^ 2 by ring]
    field_simp
    ring
  refine ⟨key, ?_⟩
  refine va_of (p := X - C 3) (q := X + C 2) ⟨0, by simp⟩ (by simp) (by norm_num)
    (fun x hx _ => ?_)
  simpa using key x hx

/-- Stitz-Zeager Example 4.1.3(a): the doomsday population `P(t) = 100/(5-t)²` has `P(0) = 4`. -/
@[kb "stitzzeager2013" "Example 4.1.3, p. 319"]
theorem ex_4_1_3_a : (fun t : ℝ => 100 / (5 - t) ^ 2) 0 = 4 := by norm_num

/-- Stitz-Zeager Example 4.1.3(b): on `0 ≤ t < 5` the population `100/(5-t)²` equals `100` exactly when
`t = 4`. -/
@[kb "stitzzeager2013" "Example 4.1.3, p. 319"]
theorem ex_4_1_3_b (t : ℝ) (h0 : 0 ≤ t) (h5 : t < 5) : 100 / (5 - t) ^ 2 = 100 ↔ t = 4 := by
  have hpos : 0 < 5 - t := by linarith
  have hne : (5 - t) ^ 2 ≠ 0 := by positivity
  rw [div_eq_iff hne]
  constructor
  · intro h
    have : (5 - t - 1) * (5 - t + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h <;> linarith
  · rintro rfl; norm_num

/-- Stitz-Zeager Example 4.1.3(c): as `t → 5⁻`, the population `100/(5-t)²` grows without bound. -/
@[kb "stitzzeager2013" "Example 4.1.3, p. 319"]
theorem ex_4_1_3_c : Tendsto (fun t : ℝ => 100 / (5 - t) ^ 2) (𝓝[<] 5) atTop := by
  have h0 : Tendsto (fun t : ℝ => (5 - t) ^ 2) (𝓝[<] 5) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun t : ℝ => (5 - t) ^ 2) (𝓝 5) (𝓝 ((5 - 5) ^ 2)) :=
        ((tendsto_const_nhds.sub tendsto_id).pow 2)
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have : 0 < 5 - t := by simp only [mem_Iio] at ht; linarith
      exact pow_pos this 2
  have := h0.inv_tendsto_nhdsGT_zero.const_mul_atTop (show (0 : ℝ) < 100 by norm_num)
  refine this.congr (fun t => ?_)
  simp [div_eq_mul_inv]

/-- Stitz-Zeager Example 4.1.4(a): `5x/(x²+1)` tends to `0` as `x → ±∞`, so `y = 0` is its horizontal
asymptote. -/
@[kb "stitzzeager2013" "Example 4.1.4, p. 321"]
theorem ex_4_1_4_a :
    Tendsto (fun x : ℝ => 5 * x / (x ^ 2 + 1)) atTop (𝓝 0) ∧
    Tendsto (fun x : ℝ => 5 * x / (x ^ 2 + 1)) atBot (𝓝 0) := by
  have h := tendsto_zero_ends (C 5 * X) (X ^ 2 + 1) (by
    rw [degree_C_mul_X (by norm_num), show (X ^ 2 + 1 : ℝ[X]).degree = 2 by compute_degree!]
    norm_num)
  simpa using h

/-- Stitz-Zeager Example 4.1.4(b): `(x²-4)/(x+1)` has no horizontal asymptote. -/
@[kb "stitzzeager2013" "Example 4.1.4, p. 321"]
theorem ex_4_1_4_b : ∀ c : ℝ, ¬ IsHorizontalAsymptote (fun x : ℝ => (x ^ 2 - 4) / (x + 1)) c := by
  have h := (horizontal_asymptote_rational (p := (X ^ 2 - 4 : ℝ[X])) (q := X + 1)
    (by intro h; have := congrArg (eval 0) h; simp at this)).2.2 (by
      rw [show (X + 1 : ℝ[X]).degree = 1 by compute_degree!,
        show (X ^ 2 - 4 : ℝ[X]).degree = 2 by compute_degree!]
      norm_num)
  simpa using h

/-- Stitz-Zeager Example 4.1.4(c): `(6x³-3x+1)/(5-2x³)` has the horizontal asymptote `y = -3`. -/
@[kb "stitzzeager2013" "Example 4.1.4, p. 321"]
theorem ex_4_1_4_c :
    Tendsto (fun x : ℝ => (6 * x ^ 3 - 3 * x + 1) / (5 - 2 * x ^ 3)) atTop (𝓝 (-3)) ∧
    Tendsto (fun x : ℝ => (6 * x ^ 3 - 3 * x + 1) / (5 - 2 * x ^ 3)) atBot (𝓝 (-3)) := by
  have h := thm_4_2_horizontal_asymptote_equal_degree (C 6 * X ^ 3 - C 3 * X + 1) (5 - C 2 * X ^ 3) (by
    rw [show (C 6 * X ^ 3 - C 3 * X + 1 : ℝ[X]).degree = 3 by compute_degree!,
      show (5 - C 2 * X ^ 3 : ℝ[X]).degree = 3 by compute_degree!])
  have hp : (C 6 * X ^ 3 - C 3 * X + 1 : ℝ[X]).leadingCoeff = 6 := by
    rw [leadingCoeff, show (C 6 * X ^ 3 - C 3 * X + 1 : ℝ[X]).natDegree = 3 by compute_degree!]
    simp [coeff_X, coeff_one]
  have hq : (5 - C 2 * X ^ 3 : ℝ[X]).leadingCoeff = -2 := by
    rw [leadingCoeff, show (5 - C 2 * X ^ 3 : ℝ[X]).natDegree = 3 by compute_degree!]
    simp
  rw [hp, hq] at h
  norm_num at h
  simpa using h

/-- Stitz-Zeager Example 4.1.5(a): the flu model `N(t) = 500 - 450/(1+3t)` has `N(0) = 50`. -/
@[kb "stitzzeager2013" "Example 4.1.5, p. 322"]
theorem ex_4_1_5_a : (fun t : ℝ => 500 - 450 / (1 + 3 * t)) 0 = 50 := by norm_num

/-- Stitz-Zeager Example 4.1.5(b): for `t ≥ 0`, `500 - 450/(1+3t) = 300` exactly when `t = 5/12`. -/
@[kb "stitzzeager2013" "Example 4.1.5, p. 322"]
theorem ex_4_1_5_b (t : ℝ) (ht : 0 ≤ t) : 500 - 450 / (1 + 3 * t) = 300 ↔ t = 5 / 12 := by
  have hne : 1 + 3 * t ≠ 0 := by positivity
  constructor
  · intro h
    field_simp at h
    linarith
  · rintro rfl; norm_num

/-- Stitz-Zeager Example 4.1.5(c): `500 - 450/(1+3t) → 500` as `t → ∞`. -/
@[kb "stitzzeager2013" "Example 4.1.5, p. 322"]
theorem ex_4_1_5_c : Tendsto (fun t : ℝ => 500 - 450 / (1 + 3 * t)) atTop (𝓝 500) := by
  have h : Tendsto (fun t : ℝ => 450 / (3 * t + 1)) atTop (𝓝 0) := by
    have h3 : Tendsto (fun t : ℝ => 3 * t + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 (tendsto_id.const_mul_atTop (by norm_num))
    exact tendsto_const_nhds.div_atTop h3
  have := (tendsto_const_nhds (x := (500 : ℝ))).sub h
  simpa [add_comm] using this

/-- Stitz-Zeager Example 4.1.6(a): the line `y = -x + 3` is a slant asymptote of `(x²-4x+2)/(1-x)` at both ends. -/
@[kb "stitzzeager2013" "Example 4.1.6, p. 324"]
theorem ex_4_1_6_a :
    Tendsto (fun x : ℝ => (x ^ 2 - 4 * x + 2) / (1 - x) - (-1 * x + 3)) atTop (𝓝 0) ∧
    Tendsto (fun x : ℝ => (x ^ 2 - 4 * x + 2) / (1 - x) - (-1 * x + 3)) atBot (𝓝 0) := by
  have key : ∀ x : ℝ, x ≠ 1 → (x ^ 2 - 4 * x + 2) / (1 - x) - (-1 * x + 3) = 1 / (x + -1) := by
    intro x hx
    have h1 : 1 - x ≠ 0 := fun h => hx (by linarith)
    have h2 : x + -1 ≠ 0 := fun h => hx (by linarith)
    field_simp
    ring
  exact slant_aux (fun x : ℝ => (x ^ 2 - 4 * x + 2) / (1 - x)) (-1) 3 1 1 1 1
    (fun x hx => key x (by linarith)) (fun x hx => key x (by linarith))

/-- Stitz-Zeager Example 4.1.6(b): `(x²-4)/(x-2)` equals `x + 2` for `x ≠ 2` (a hole at `(2, 4)`), so `y = x + 2`
is a slant asymptote at both ends. -/
@[kb "stitzzeager2013" "Example 4.1.6, p. 324"]
theorem ex_4_1_6_b :
    (∀ x : ℝ, x ≠ 2 → (x ^ 2 - 4) / (x - 2) = x + 2) ∧
    Tendsto (fun x : ℝ => (x ^ 2 - 4) / (x - 2)) (𝓝[≠] 2) (𝓝 4) ∧
    Tendsto (fun x : ℝ => (x ^ 2 - 4) / (x - 2) - (1 * x + 2)) atTop (𝓝 0) ∧
    Tendsto (fun x : ℝ => (x ^ 2 - 4) / (x - 2) - (1 * x + 2)) atBot (𝓝 0) := by
  have key : ∀ x : ℝ, x ≠ 2 → (x ^ 2 - 4) / (x - 2) = x + 2 := by
    intro x hx
    have h1 : x - 2 ≠ 0 := sub_ne_zero.mpr hx
    field_simp
    ring
  have hs := slant_aux (fun x : ℝ => (x ^ 2 - 4) / (x - 2)) 1 2 0 2 2 2
    (fun x hx => by rw [key x (by linarith)]; simp) (fun x hx => by rw [key x (by linarith)]; simp)
  refine ⟨key, ?_, hs⟩
  have hc : Tendsto (fun x : ℝ => x + 2) (𝓝[≠] 2) (𝓝 4) := by
    have : Tendsto (fun x : ℝ => x + 2) (𝓝 2) (𝓝 (2 + 2)) := tendsto_id.add_const 2
    norm_num at this
    exact this.mono_left nhdsWithin_le_nhds
  exact hc.congr' (by filter_upwards [self_mem_nhdsWithin] with x hx using (key x hx).symm)

/-- Stitz-Zeager Example 4.1.6(c): `y = x` is a slant asymptote of `(x³+1)/(x²-4)` at both ends. -/
@[kb "stitzzeager2013" "Example 4.1.6, p. 324"]
theorem ex_4_1_6_c :
    Tendsto (fun x : ℝ => (x ^ 3 + 1) / (x ^ 2 - 4) - (1 * x + 0)) atTop (𝓝 0) ∧
    Tendsto (fun x : ℝ => (x ^ 3 + 1) / (x ^ 2 - 4) - (1 * x + 0)) atBot (𝓝 0) := by
  have h := tendsto_zero_ends (C 4 * X + 1) (X ^ 2 - C 4) (by
    rw [show (C 4 * X + 1 : ℝ[X]).degree = 1 by compute_degree!,
      show (X ^ 2 - C 4 : ℝ[X]).degree = 2 by compute_degree!]
    norm_num)
  have key : ∀ x : ℝ, 2 < |x| → (x ^ 3 + 1) / (x ^ 2 - 4) - (1 * x + 0) = (4 * x + 1) / (x ^ 2 - 4) := by
    intro x hx
    have h1 : x ^ 2 - 4 ≠ 0 := by
      have : 4 < x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
      linarith
    field_simp
    ring
  constructor
  · refine (by simpa using h.1 : Tendsto (fun x : ℝ => (4 * x + 1) / (x ^ 2 - 4)) atTop (𝓝 0)).congr'
      ((eventually_gt_atTop 2).mono fun x hx => ?_)
    exact (key x (by rw [abs_of_pos (by linarith)]; exact hx)).symm
  · refine (by simpa using h.2 : Tendsto (fun x : ℝ => (4 * x + 1) / (x ^ 2 - 4)) atBot (𝓝 0)).congr'
      ((eventually_lt_atBot (-2)).mono fun x hx => ?_)
    exact (key x (by rw [abs_of_neg (by linarith)]; linarith)).symm

/-! ## Section 4.2 -/

/-- Stitz-Zeager Example 4.2.1: for `f(x) = 3x/(x²-4)`: the only intercept is `(0,0)`, the lines `x = ±2` are
vertical asymptotes, and `y = 0` is the horizontal asymptote (`f → 0` at both ends). -/
@[kb "stitzzeager2013" "Example 4.2.1, p. 334"]
theorem ex_4_2_1 :
    (∀ x : ℝ, x ^ 2 - 4 ≠ 0 → (3 * x / (x ^ 2 - 4) = 0 ↔ x = 0)) ∧
    (fun x : ℝ => 3 * x / (x ^ 2 - 4)) 0 = 0 ∧
    IsVerticalAsymptote (fun x : ℝ => 3 * x / (x ^ 2 - 4)) (-2) ∧
    IsVerticalAsymptote (fun x : ℝ => 3 * x / (x ^ 2 - 4)) 2 ∧
    Tendsto (fun x : ℝ => 3 * x / (x ^ 2 - 4)) atTop (𝓝 0) ∧
    Tendsto (fun x : ℝ => 3 * x / (x ^ 2 - 4)) atBot (𝓝 0) := by
  have hf : ∀ x : ℝ, 3 * x / (x ^ 2 - 4) = (C 3 * X : ℝ[X]).eval x / (X ^ 2 - C 4 : ℝ[X]).eval x := by
    intro x; simp
  have hd : (C 3 * X : ℝ[X]).degree < (X ^ 2 - C 4 : ℝ[X]).degree := by
    rw [degree_C_mul_X (by norm_num), show (X ^ 2 - C 4 : ℝ[X]).degree = 2 by compute_degree!]
    norm_num
  have h := tendsto_zero_ends _ _ hd
  refine ⟨fun x hx => ?_, by norm_num, ?_, ?_, by simpa using h.1, by simpa using h.2⟩
  · rw [div_eq_zero_iff]
    constructor
    · rintro (h | h)
      · linarith
      · exact absurd h hx
    · intro h; left; rw [h]; norm_num
  · exact va_of (p := C 3 * X) (q := X ^ 2 - C 4) ⟨0, by simp⟩ (by simp; norm_num) (by simp)
      (fun x _ _ => hf x)
  · exact va_of (p := C 3 * X) (q := X ^ 2 - C 4) ⟨0, by simp⟩ (by simp; norm_num) (by simp)
      (fun x _ _ => hf x)

/-- Stitz-Zeager Example 4.2.2: for `g(x) = (2x²-3x-5)/(x²-x-6)`: away from the poles its zeros are `5/2` and
`-1`; `g(0) = 5/6`; the lines `x = -2`, `x = 3` are vertical asymptotes; `g → 2` at both ends; and the graph meets
its horizontal asymptote `y = 2` exactly at `x = 7`. -/
@[kb "stitzzeager2013" "Example 4.2.2, p. 337"]
theorem ex_4_2_2 :
    (∀ x : ℝ, x ≠ -2 → x ≠ 3 →
      ((2 * x ^ 2 - 3 * x - 5) / (x ^ 2 - x - 6) = 0 ↔ x = 5 / 2 ∨ x = -1)) ∧
    (fun x : ℝ => (2 * x ^ 2 - 3 * x - 5) / (x ^ 2 - x - 6)) 0 = 5 / 6 ∧
    IsVerticalAsymptote (fun x : ℝ => (2 * x ^ 2 - 3 * x - 5) / (x ^ 2 - x - 6)) (-2) ∧
    IsVerticalAsymptote (fun x : ℝ => (2 * x ^ 2 - 3 * x - 5) / (x ^ 2 - x - 6)) 3 ∧
    Tendsto (fun x : ℝ => (2 * x ^ 2 - 3 * x - 5) / (x ^ 2 - x - 6)) atTop (𝓝 2) ∧
    Tendsto (fun x : ℝ => (2 * x ^ 2 - 3 * x - 5) / (x ^ 2 - x - 6)) atBot (𝓝 2) ∧
    (∀ x : ℝ, x ≠ -2 → x ≠ 3 → ((2 * x ^ 2 - 3 * x - 5) / (x ^ 2 - x - 6) = 2 ↔ x = 7)) := by
  have hf : ∀ x : ℝ, (2 * x ^ 2 - 3 * x - 5) / (x ^ 2 - x - 6) =
      (2 * X ^ 2 - C 3 * X - 5 : ℝ[X]).eval x / (X ^ 2 - X - 6 : ℝ[X]).eval x := by
    intro x; simp
  have hden : ∀ x : ℝ, x ≠ -2 → x ≠ 3 → x ^ 2 - x - 6 ≠ 0 := by
    intro x h1 h2
    rw [show x ^ 2 - x - 6 = (x + 2) * (x - 3) by ring]
    exact mul_ne_zero (fun h => h1 (by linarith)) (sub_ne_zero.mpr h2)
  have h := thm_4_2_horizontal_asymptote_equal_degree (2 * X ^ 2 - C 3 * X - 5 : ℝ[X]) (X ^ 2 - X - 6) (by
    rw [show (2 * X ^ 2 - C 3 * X - 5 : ℝ[X]).degree = 2 by compute_degree!,
      show (X ^ 2 - X - 6 : ℝ[X]).degree = 2 by compute_degree!])
  have hp : (2 * X ^ 2 - C 3 * X - 5 : ℝ[X]).leadingCoeff = 2 := by
    rw [leadingCoeff, show (2 * X ^ 2 - C 3 * X - 5 : ℝ[X]).natDegree = 2 by compute_degree!]
    simp [coeff_X, coeff_one]
  have hq : (X ^ 2 - X - 6 : ℝ[X]).leadingCoeff = 1 := by
    rw [leadingCoeff, show (X ^ 2 - X - 6 : ℝ[X]).natDegree = 2 by compute_degree!]
    simp [coeff_X, coeff_one]
  rw [hp, hq] at h
  refine ⟨fun x h1 h2 => ?_, by norm_num, ?_, ?_, by simpa using h.1, by simpa using h.2, fun x h1 h2 => ?_⟩
  · have := hden x h1 h2
    rw [div_eq_zero_iff]
    constructor
    · rintro (h | h)
      · have : (2 * x - 5) * (x + 1) = 0 := by linarith
        rcases mul_eq_zero.mp this with h | h
        · left; linarith
        · right; linarith
      · exact absurd h this
    · rintro (h | h) <;> left <;> rw [h] <;> norm_num
  · exact va_of (p := 2 * X ^ 2 - C 3 * X - 5) (q := X ^ 2 - X - 6) ⟨0, by simp⟩ (by simp; norm_num)
      (by simp; norm_num) (fun x _ _ => hf x)
  · exact va_of (p := 2 * X ^ 2 - C 3 * X - 5) (q := X ^ 2 - X - 6) ⟨0, by simp⟩ (by simp; norm_num)
      (by simp; norm_num) (fun x _ _ => hf x)
  · have := hden x h1 h2
    rw [div_eq_iff this]
    constructor
    · intro h; linarith
    · rintro rfl; norm_num

/-- Stitz-Zeager Example 4.2.3: for `h(x) = (2x³+5x²+4x+1)/(x²+3x+2)`: for `x ≠ -1, -2` it equals
`(2x+1)(x+1)/(x+2)`; its only zero in the domain is `-1/2`; `h(0) = 1/2`; `x = -2` is a vertical asymptote; there is a
hole at `(-1, 0)`; `y = 2x - 1` is a slant asymptote at both ends; and the graph never meets this line. -/
@[kb "stitzzeager2013" "Example 4.2.3, p. 340"]
theorem ex_4_2_3 :
    (∀ x : ℝ, x ≠ -1 → x ≠ -2 → (2 * x ^ 3 + 5 * x ^ 2 + 4 * x + 1) / (x ^ 2 + 3 * x + 2) =
      (2 * x + 1) * (x + 1) / (x + 2)) ∧
    (∀ x : ℝ, x ≠ -1 → x ≠ -2 →
      ((2 * x ^ 3 + 5 * x ^ 2 + 4 * x + 1) / (x ^ 2 + 3 * x + 2) = 0 ↔ x = -1 / 2)) ∧
    (fun x : ℝ => (2 * x ^ 3 + 5 * x ^ 2 + 4 * x + 1) / (x ^ 2 + 3 * x + 2)) 0 = 1 / 2 ∧
    IsVerticalAsymptote (fun x : ℝ => (2 * x ^ 3 + 5 * x ^ 2 + 4 * x + 1) / (x ^ 2 + 3 * x + 2)) (-2) ∧
    Tendsto (fun x : ℝ => (2 * x ^ 3 + 5 * x ^ 2 + 4 * x + 1) / (x ^ 2 + 3 * x + 2)) (𝓝[≠] (-1)) (𝓝 0) ∧
    Tendsto (fun x : ℝ => (2 * x ^ 3 + 5 * x ^ 2 + 4 * x + 1) / (x ^ 2 + 3 * x + 2) - (2 * x + -1))
      atTop (𝓝 0) ∧
    Tendsto (fun x : ℝ => (2 * x ^ 3 + 5 * x ^ 2 + 4 * x + 1) / (x ^ 2 + 3 * x + 2) - (2 * x + -1))
      atBot (𝓝 0) ∧
    (∀ x : ℝ, x ≠ -1 → x ≠ -2 →
      (2 * x ^ 3 + 5 * x ^ 2 + 4 * x + 1) / (x ^ 2 + 3 * x + 2) ≠ 2 * x - 1) := by
  have key : ∀ x : ℝ, x ≠ -1 → x ≠ -2 → (2 * x ^ 3 + 5 * x ^ 2 + 4 * x + 1) / (x ^ 2 + 3 * x + 2) =
      (2 * x + 1) * (x + 1) / (x + 2) := by
    intro x h1 h2
    have ha : x + 1 ≠ 0 := fun h => h1 (by linarith)
    have hb : x + 2 ≠ 0 := fun h => h2 (by linarith)
    have hc : x ^ 2 + 3 * x + 2 ≠ 0 := by
      rw [show x ^ 2 + 3 * x + 2 = (x + 1) * (x + 2) by ring]
      exact mul_ne_zero ha hb
    rw [div_eq_div_iff hc hb]
    ring
  have key2 : ∀ x : ℝ, x ≠ -1 → x ≠ -2 → (2 * x + 1) * (x + 1) / (x + 2) - (2 * x + -1) = 3 / (x + 2) := by
    intro x h1 h2
    have hb : x + 2 ≠ 0 := fun h => h2 (by linarith)
    field_simp
    ring
  have hs := slant_aux (fun x : ℝ => (2 * x ^ 3 + 5 * x ^ 2 + 4 * x + 1) / (x ^ 2 + 3 * x + 2)) 2 (-1) 3 (-2) 0 (-3)
    (fun x hx => by rw [key x (by linarith) (by linarith)]; exact key2 x (by linarith) (by linarith))
    (fun x hx => by rw [key x (by linarith) (by linarith)]; exact key2 x (by linarith) (by linarith))
  refine ⟨key, fun x h1 h2 => ?_, by norm_num, ?_, ?_, hs.1, hs.2, fun x h1 h2 h => ?_⟩
  · rw [key x h1 h2, div_eq_zero_iff]
    have hb : x + 2 ≠ 0 := fun h => h2 (by linarith)
    have ha : x + 1 ≠ 0 := fun h => h1 (by linarith)
    constructor
    · rintro (h | h)
      · rcases mul_eq_zero.mp h with h | h
        · linarith
        · exact absurd h ha
      · exact absurd h hb
    · intro h; left; rw [h]; norm_num
  · refine va_of (p := (2 * X + 1) * (X + 1)) (q := X + C 2) ⟨0, by simp⟩ (by simp) (by simp; norm_num)
      (fun x hx hx1 => ?_)
    have h1 : x ≠ -1 := by
      intro h; rw [abs_lt] at hx1; linarith [hx1.1, hx1.2]
    simpa using key x h1 hx
  · have hc : ContinuousAt (fun x : ℝ => (2 * x + 1) * (x + 1) / (x + 2)) (-1) :=
      (((continuousAt_const.mul continuousAt_id).add continuousAt_const).mul
        (continuousAt_id.add continuousAt_const)).div (continuousAt_id.add continuousAt_const)
        (by show (-1 : ℝ) + 2 ≠ 0; norm_num)
    have h1 : Tendsto (fun x : ℝ => (2 * x + 1) * (x + 1) / (x + 2)) (𝓝[≠] (-1)) (𝓝 0) := by
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {-1}ᶜ))
      convert this using 2
      norm_num
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin,
      (eventually_ne_nhds (show (-1 : ℝ) ≠ -2 by norm_num)).filter_mono nhdsWithin_le_nhds] with x h1 h2
    exact (key x h1 h2).symm
  · rw [key x h1 h2] at h
    have hb : x + 2 ≠ 0 := fun h => h2 (by linarith)
    have := key2 x h1 h2
    rw [h, show 2 * x - 1 - (2 * x + -1) = 0 by ring] at this
    have h3 : (3 : ℝ) / (x + 2) ≠ 0 := div_ne_zero (by norm_num) hb
    exact h3 this.symm

/-- Stitz-Zeager Example 4.2.4: `r(x) = (x⁴+1)/(x²+1)` is defined on all of `ℝ`, equals `x² - 1 + 2/(x²+1)`, has no
zero, has `r(0) = 1`, no vertical asymptote, and `r(x) - (x² - 1) → 0` at both ends. -/
@[kb "stitzzeager2013" "Example 4.2.4, p. 343"]
theorem ex_4_2_4 :
    (∀ x : ℝ, (x ^ 4 + 1) / (x ^ 2 + 1) = x ^ 2 - 1 + 2 / (x ^ 2 + 1)) ∧
    (∀ x : ℝ, (x ^ 4 + 1) / (x ^ 2 + 1) ≠ 0) ∧
    (fun x : ℝ => (x ^ 4 + 1) / (x ^ 2 + 1)) 0 = 1 ∧
    (∀ c : ℝ, ¬ IsVerticalAsymptote (fun x : ℝ => (x ^ 4 + 1) / (x ^ 2 + 1)) c) ∧
    Tendsto (fun x : ℝ => (x ^ 4 + 1) / (x ^ 2 + 1) - (x ^ 2 - 1)) atTop (𝓝 0) ∧
    Tendsto (fun x : ℝ => (x ^ 4 + 1) / (x ^ 2 + 1) - (x ^ 2 - 1)) atBot (𝓝 0) := by
  have key : ∀ x : ℝ, (x ^ 4 + 1) / (x ^ 2 + 1) = x ^ 2 - 1 + 2 / (x ^ 2 + 1) := by
    intro x
    have : x ^ 2 + 1 ≠ 0 := by positivity
    field_simp
    ring
  have h := tendsto_zero_ends (C 2) (X ^ 2 + 1) (by
    rw [show (C 2 : ℝ[X]).degree = 0 from degree_C (by norm_num),
      show (X ^ 2 + 1 : ℝ[X]).degree = 2 by compute_degree!]
    norm_num)
  have e : (fun x : ℝ => (x ^ 4 + 1) / (x ^ 2 + 1) - (x ^ 2 - 1)) = fun x => 2 / (x ^ 2 + 1) := by
    funext x; rw [key x]; ring
  refine ⟨key, fun x => by positivity, by norm_num, fun c => not_va_of_continuous ?_ c, ?_, ?_⟩
  · exact Continuous.div (f := fun x : ℝ => x ^ 4 + 1) (g := fun x : ℝ => x ^ 2 + 1)
      (by fun_prop) (by fun_prop) (fun x => by positivity)
  · rw [e]; simpa using h.1
  · rw [e]; simpa using h.2

/-! ## Section 4.3 -/

/-- Stitz-Zeager Example 4.3.1(1): for `x ≠ 1`, `(x³-2x+1)/(x-1) = x/2 - 1` exactly when `x = -1/2` or `x = 0`. -/
@[kb "stitzzeager2013" "Example 4.3.1, p. 354"]
theorem ex_4_3_1_a (x : ℝ) (hx : x ≠ 1) :
    (x ^ 3 - 2 * x + 1) / (x - 1) = x / 2 - 1 ↔ x = -1 / 2 ∨ x = 0 := by
  have h1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  have key : (x ^ 3 - 2 * x + 1) / (x - 1) = x ^ 2 + x - 1 := by
    field_simp
    ring
  rw [key]
  constructor
  · intro h
    have : x * (2 * x + 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · right; exact h
    · left; linarith
  · rintro (h | h) <;> rw [h] <;> norm_num

/-- Stitz-Zeager Example 4.3.1(2): the solution set of `(x³-2x+1)/(x-1) ≥ x/2 - 1` (with `x ≠ 1`) is
`(-∞, -1/2] ∪ [0, 1) ∪ (1, ∞)`. -/
@[kb "stitzzeager2013" "Example 4.3.1, p. 354"]
theorem ex_4_3_1_b :
    {x : ℝ | x ≠ 1 ∧ (x ^ 3 - 2 * x + 1) / (x - 1) ≥ x / 2 - 1} = Iic (-1 / 2) ∪ Ico 0 1 ∪ Ioi 1 := by
  ext x
  simp only [mem_setOf_eq, mem_union, mem_Iic, mem_Ico, mem_Ioi]
  constructor
  · rintro ⟨hx, h⟩
    have h1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx
    have key : (x ^ 3 - 2 * x + 1) / (x - 1) = x ^ 2 + x - 1 := by
      field_simp
      ring
    rw [key] at h
    have h2 : 0 ≤ x * (2 * x + 1) := by nlinarith
    rcases lt_or_gt_of_ne hx with hlt | hgt
    · by_cases h0 : x ≤ -1 / 2
      · left; left; exact h0
      · push_neg at h0
        left; right
        refine ⟨?_, hlt⟩
        by_contra hneg
        push_neg at hneg
        nlinarith
    · right; exact hgt
  · intro h
    have hx : x ≠ 1 := by
      rcases h with (h | h) | h
      · linarith
      · exact ne_of_lt h.2
      · exact ne_of_gt h
    refine ⟨hx, ?_⟩
    have h1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx
    have key : (x ^ 3 - 2 * x + 1) / (x - 1) = x ^ 2 + x - 1 := by
      field_simp
      ring
    rw [key]
    rcases h with (h | h) | h
    · nlinarith
    · nlinarith [h.1]
    · nlinarith

/-- Stitz-Zeager Example 4.3.2: with river speed `R` (`0 < R < 6`), the round trip `5/(6+R) + 5/(6-R) = 3`
holds exactly when `R = 4`. -/
@[kb "stitzzeager2013" "Example 4.3.2, p. 355"]
theorem ex_4_3_2 (R : ℝ) (h0 : 0 < R) (h6 : R < 6) : 5 / (6 + R) + 5 / (6 - R) = 3 ↔ R = 4 := by
  have ha : 6 + R ≠ 0 := by linarith
  have hb : 6 - R ≠ 0 := by linarith
  constructor
  · intro h
    field_simp at h
    have : (R - 4) * (R + 4) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h <;> linarith
  · rintro rfl; norm_num

/-- Stitz-Zeager Example 4.3.3: if Taylor alone needs `4` hours and together they need `3`, then Carl alone needs
`t` hours with `1/3 = 1/4 + 1/t` exactly when `t = 12`. -/
@[kb "stitzzeager2013" "Example 4.3.3, p. 357"]
theorem ex_4_3_3 (t : ℝ) (ht : 0 < t) : 1 / 3 = 1 / 4 + 1 / t ↔ t = 12 := by
  have : t ≠ 0 := ht.ne'
  constructor
  · intro h
    field_simp at h
    linarith
  · rintro rfl; norm_num

/-- Stitz-Zeager Example 4.3.4(1): for `x > 0` the average cost `(80x+150)/x` equals `80 + 150/x`. -/
@[kb "stitzzeager2013" "Example 4.3.4, p. 358"]
theorem ex_4_3_4_a (x : ℝ) (hx : 0 < x) : (80 * x + 150) / x = 80 + 150 / x := by
  field_simp

/-- Stitz-Zeager Example 4.3.4(2): for `x > 0`, the average cost `(80x+150)/x` is below `100` exactly when
`x > 15/2`. -/
@[kb "stitzzeager2013" "Example 4.3.4, p. 358"]
theorem ex_4_3_4_b (x : ℝ) (hx : 0 < x) : (80 * x + 150) / x < 100 ↔ 15 / 2 < x := by
  rw [div_lt_iff₀ hx]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Example 4.3.4(3): the average cost `(80x+150)/x` always exceeds `80` for `x > 0` and tends to
`80` as `x → ∞`. -/
@[kb "stitzzeager2013" "Example 4.3.4, p. 358"]
theorem ex_4_3_4_c :
    (∀ x : ℝ, 0 < x → 80 < (80 * x + 150) / x) ∧
    Tendsto (fun x : ℝ => (80 * x + 150) / x) atTop (𝓝 80) := by
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [lt_div_iff₀ hx]; linarith
  · have h : Tendsto (fun x : ℝ => 150 / (x + 0)) atTop (𝓝 0) := tendsto_div_zero_atTop 150 0
    have h2 := (tendsto_const_nhds (x := (80 : ℝ))).add h
    refine (by simpa using h2 : Tendsto (fun x : ℝ => 80 + 150 / x) atTop (𝓝 80)).congr'
      ((eventually_gt_atTop 0).mono fun x hx => ?_)
    field_simp

/-- Stitz-Zeager Example 4.3.5(2): for `x > 0` the height `1000/x²` is at least `x` exactly when `x ≤ 10`. -/
@[kb "stitzzeager2013" "Example 4.3.5, p. 360"]
theorem ex_4_3_5_b (x : ℝ) (hx : 0 < x) : 1000 / x ^ 2 ≥ x ↔ x ≤ 10 := by
  have h2 : 0 < x ^ 2 := by positivity
  rw [ge_iff_le, le_div_iff₀ h2]
  constructor
  · intro h; by_contra hc; push_neg at hc; nlinarith
  · intro h; nlinarith

/-- Stitz-Zeager Example 4.3.5(3): the height `1000/x²` grows without bound as `x → 0⁺` and tends to `0` as
`x → ∞`. -/
@[kb "stitzzeager2013" "Example 4.3.5, p. 360"]
theorem ex_4_3_5_c :
    Tendsto (fun x : ℝ => 1000 / x ^ 2) (𝓝[>] 0) atTop ∧
    Tendsto (fun x : ℝ => 1000 / x ^ 2) atTop (𝓝 0) := by
  constructor
  · have h0 : Tendsto (fun x : ℝ => x ^ 2) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Tendsto (fun x : ℝ => x ^ 2) (𝓝 0) (𝓝 (0 ^ 2)) := (tendsto_id.pow 2)
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx
        exact pow_pos (mem_Ioi.mp hx) 2
    have := h0.inv_tendsto_nhdsGT_zero.const_mul_atTop (show (0 : ℝ) < 1000 by norm_num)
    refine this.congr (fun x => ?_)
    simp [div_eq_mul_inv]
  · exact tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))

/-- Stitz-Zeager Example 4.3.5(4): the surface area `x² + 4xh` of the open box with `h = 1000/x²` is
`x² + 4000/x`. -/
@[kb "stitzzeager2013" "Example 4.3.5, p. 360"]
theorem ex_4_3_5_d (x : ℝ) (hx : 0 < x) : x ^ 2 + 4 * x * (1000 / x ^ 2) = x ^ 2 + 4000 / x := by
  field_simp
  ring

end UndergradKB.Precalculus.Course
