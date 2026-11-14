import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Group.EvenFunction
import Mathlib.Order.Interval.Set.Basic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 1 (Stitz-Zeager): worked examples -/

namespace UndergradKB.Precalculus.Course

open Set

/-! ## Section 1.1 -/

/-- Stitz-Zeager Example 1.1.1(a): `x ≤ -2` or `x ≥ 2` is `(-∞,-2] ∪ [2,∞)`. -/
@[kb "stitzzeager2013" "Example 1.1.1, p. 17"]
theorem ex_1_1_1_a : {x : ℝ | x ≤ -2 ∨ x ≥ 2} = Iic (-2) ∪ Ici 2 := by
  ext x; simp [ge_iff_le]

/-- Stitz-Zeager Example 1.1.1(b): the reals other than `3` form `(-∞,3) ∪ (3,∞)`. -/
@[kb "stitzzeager2013" "Example 1.1.1, p. 17"]
theorem ex_1_1_1_b : {x : ℝ | x ≠ 3} = Iio 3 ∪ Ioi 3 := by
  ext x; simp [lt_or_lt_iff_ne]

/-- Stitz-Zeager Example 1.1.1(c): the reals other than `±3` form three open intervals. -/
@[kb "stitzzeager2013" "Example 1.1.1, p. 17"]
theorem ex_1_1_1_c : {x : ℝ | x ≠ 3 ∧ x ≠ -3} = Iio (-3) ∪ Ioo (-3) 3 ∪ Ioi 3 := by
  ext x
  simp only [mem_setOf_eq, mem_union, mem_Iio, mem_Ioo, mem_Ioi]
  constructor
  · rintro ⟨h1, h2⟩
    rcases lt_trichotomy x 3 with h | h | h
    · rcases lt_trichotomy x (-3) with h' | h' | h'
      · exact Or.inl (Or.inl h')
      · exact absurd h' h2
      · exact Or.inl (Or.inr ⟨h', h⟩)
    · exact absurd h h1
    · exact Or.inr h
  · rintro ((h | ⟨h1, h2⟩) | h)
    · exact ⟨ne_of_lt (by linarith), ne_of_lt h⟩
    · exact ⟨ne_of_lt h2, ne_of_gt h1⟩
    · exact ⟨ne_of_gt h, ne_of_gt (by linarith)⟩

/-- Stitz-Zeager Example 1.1.1(d): `-1 < x ≤ 3` or `x = 5` is `(-1,3] ∪ {5}`. -/
@[kb "stitzzeager2013" "Example 1.1.1, p. 17"]
theorem ex_1_1_1_d : {x : ℝ | (-1 < x ∧ x ≤ 3) ∨ x = 5} = Ioc (-1) 3 ∪ {5} := by
  ext x; simp [or_comm]

/-- Stitz-Zeager Example 1.1.3: the reflections of `(-2,3)` in the x-axis, the y-axis and the origin
(Definition 1.3) are `(-2,-3)`, `(2,3)` and `(2,-3)`. -/
@[kb "stitzzeager2013" "Example 1.1.3, p. 21"]
theorem ex_1_1_3_symmetric_points (c d : ℝ) :
    ((-2 = c ∧ 3 = -d) ↔ (c = -2 ∧ d = -3)) ∧ ((-2 = -c ∧ 3 = d) ↔ (c = 2 ∧ d = 3)) ∧
      ((-2 = -c ∧ 3 = -d) ↔ (c = 2 ∧ d = -3)) := by
  refine ⟨?_, ?_, ?_⟩ <;> constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- Stitz-Zeager Example 1.1.4: the distance from `(-2,3)` to `(1,-3)` is `3√5`. -/
@[kb "stitzzeager2013" "Example 1.1.4, p. 23"]
theorem ex_1_1_4_distance :
    Real.sqrt ((1 - (-2)) ^ 2 + (-3 - 3) ^ 2) = 3 * Real.sqrt 5 := by
  rw [show ((1:ℝ) - (-2)) ^ 2 + (-3 - 3) ^ 2 = 3 ^ 2 * 5 by norm_num,
    Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]

/-- Stitz-Zeager Example 1.1.5: the points `(1,y)` at distance `4` from `(3,2)` are exactly
`y = 2 ± 2√3`. -/
@[kb "stitzzeager2013" "Example 1.1.5, p. 24"]
theorem ex_1_1_5_points_at_distance (y : ℝ) :
    Real.sqrt ((1 - 3) ^ 2 + (y - 2) ^ 2) = 4 ↔ y = 2 + 2 * Real.sqrt 3 ∨ y = 2 - 2 * Real.sqrt 3 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by norm_num)]
  constructor
  · intro h
    have : (y - 2 - 2 * Real.sqrt 3) * (y - 2 + 2 * Real.sqrt 3) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  · rintro (h | h) <;> subst h <;> nlinarith

/-- Stitz-Zeager Example 1.1.6: the midpoint of `(-2,3)` and `(1,-3)` is `(-1/2, 0)`. -/
@[kb "stitzzeager2013" "Example 1.1.6, p. 25"]
theorem ex_1_1_6_midpoint :
    (((-2 : ℝ) + 1) / 2, (3 + (-3 : ℝ)) / 2) = (-1 / 2, 0) := by
  ext <;> norm_num

/-! ## Section 1.2 -/

/-- Stitz-Zeager Example 1.2.2: the point `(2,-1)` is not on the graph of `x² + y³ = 1`. -/
@[kb "stitzzeager2013" "Example 1.2.2, p. 36"]
theorem ex_1_2_2_not_on_graph : ¬ ((2 : ℝ) ^ 2 + (-1) ^ 3 = 1) := by norm_num

/-- Stitz-Zeager Example 1.2.3: several tabulated points lie on the graph of `x² + y³ = 1`. -/
@[kb "stitzzeager2013" "Example 1.2.3, p. 36"]
theorem ex_1_2_3_table_points :
    ((-3 : ℝ) ^ 2 + (-2) ^ 3 = 1) ∧ ((-1 : ℝ) ^ 2 + 0 ^ 3 = 1) ∧ ((0 : ℝ) ^ 2 + 1 ^ 3 = 1) ∧
      ((1 : ℝ) ^ 2 + 0 ^ 3 = 1) ∧ ((3 : ℝ) ^ 2 + (-2) ^ 3 = 1) := by
  norm_num

/-- Stitz-Zeager Example 1.2.4: the circle `(x-2)² + y² = 1` has x-intercepts `x = 1, 3`. -/
@[kb "stitzzeager2013" "Example 1.2.4, p. 38"]
theorem ex_1_2_4_x_intercepts (x : ℝ) : (x - 2) ^ 2 + 0 ^ 2 = 1 ↔ x = 1 ∨ x = 3 := by
  constructor
  · intro h
    have : (x - 1) * (x - 3) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  · rintro (h | h) <;> subst h <;> norm_num

/-- Stitz-Zeager Example 1.2.4: the circle `(x-2)² + y² = 1` has no y-intercept. -/
@[kb "stitzzeager2013" "Example 1.2.4, p. 38"]
theorem ex_1_2_4_no_y_intercept (y : ℝ) : ¬ ((0 - 2) ^ 2 + y ^ 2 = 1) := by
  nlinarith [sq_nonneg y]

/-- Stitz-Zeager Example 1.2.4: the graph of `(x-2)² + y² = 1` is symmetric about the x-axis but
not about the y-axis or the origin. -/
@[kb "stitzzeager2013" "Example 1.2.4, p. 38"]
theorem ex_1_2_4_symmetry :
    (∀ x y : ℝ, (x - 2) ^ 2 + (-y) ^ 2 = 1 ↔ (x - 2) ^ 2 + y ^ 2 = 1) ∧
      (∃ x y : ℝ, (x - 2) ^ 2 + y ^ 2 = 1 ∧ ¬ ((-x - 2) ^ 2 + y ^ 2 = 1)) ∧
      (∃ x y : ℝ, (x - 2) ^ 2 + y ^ 2 = 1 ∧ ¬ ((-x - 2) ^ 2 + (-y) ^ 2 = 1)) := by
  refine ⟨fun x y => by rw [neg_sq], ⟨1, 0, ?_⟩, ⟨1, 0, ?_⟩⟩ <;> norm_num

/-! ## Section 1.3 -/

/-- Stitz-Zeager Example 1.3.4: the relation `{(-3,2),(0,1),(4,2),(5,2)}` has domain `{-3,0,4,5}`
and range `{1,2}`. -/
@[kb "stitzzeager2013" "Example 1.3.4, p. 57"]
theorem ex_1_3_4_domain_range :
    Prod.fst '' ({(-3, 2), (0, 1), (4, 2), (5, 2)} : Set (ℝ × ℝ)) = {-3, 0, 4, 5} ∧
      Prod.snd '' ({(-3, 2), (0, 1), (4, 2), (5, 2)} : Set (ℝ × ℝ)) = {1, 2} := by
  constructor
  · simp [image_insert_eq]
  · ext y
    simp only [image_insert_eq, image_singleton, mem_insert_iff, mem_singleton_iff]
    tauto

/-- Every real number has a real cube root. -/
private theorem exists_cube_root (t : ℝ) : ∃ y : ℝ, y ^ 3 = t := by
  rcases le_total 0 t with h | h
  · refine ⟨t ^ ((1 : ℝ) / 3), ?_⟩
    rw [← Real.rpow_natCast, ← Real.rpow_mul h]; norm_num
  · refine ⟨-((-t) ^ ((1 : ℝ) / 3)), ?_⟩
    have h' : 0 ≤ -t := by linarith
    have : ((-t) ^ ((1 : ℝ) / 3)) ^ 3 = -t := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul h']; norm_num
    calc (-((-t) ^ ((1 : ℝ) / 3))) ^ 3 = -(((-t) ^ ((1 : ℝ) / 3)) ^ 3) := by ring
      _ = t := by rw [this]; ring

/-- Stitz-Zeager Example 1.3.5(1): `x³ + y² = 1` does not give `y` as a function of `x`; at `x = 0`
both `y = 1` and `y = -1` work. -/
@[kb "stitzzeager2013" "Example 1.3.5, p. 59"]
theorem ex_1_3_5_a_not_function :
    ∃ x y₁ y₂ : ℝ, x ^ 3 + y₁ ^ 2 = 1 ∧ x ^ 3 + y₂ ^ 2 = 1 ∧ y₁ ≠ y₂ :=
  ⟨0, 1, -1, by norm_num, by norm_num, by norm_num⟩

/-- Stitz-Zeager Example 1.3.5(2): `x² + y³ = 1` does give `y` as a function of `x`. -/
@[kb "stitzzeager2013" "Example 1.3.5, p. 59"]
theorem ex_1_3_5_b_function (x : ℝ) : ∃! y : ℝ, x ^ 2 + y ^ 3 = 1 := by
  obtain ⟨y, hy⟩ := exists_cube_root (1 - x ^ 2)
  refine ⟨y, by linarith, fun z hz => ?_⟩
  exact (Odd.pow_inj (by decide : Odd 3)).mp (by linarith)

/-- Stitz-Zeager Example 1.3.5(3): `x² y = 1 - 3y` gives `y = 1/(x²+3)`, a function of `x`. -/
@[kb "stitzzeager2013" "Example 1.3.5, p. 59"]
theorem ex_1_3_5_c_function (x y : ℝ) : x ^ 2 * y = 1 - 3 * y ↔ y = 1 / (x ^ 2 + 3) := by
  have h : x ^ 2 + 3 ≠ 0 := by positivity
  rw [eq_div_iff h]
  constructor <;> intro h <;> linarith

/-! ## Section 1.4 -/

/-- Stitz-Zeager Example 1.4.1: adding 4 then multiplying by 3 gives `g x = 3x + 12`, so `g 5 = 27`. -/
@[kb "stitzzeager2013" "Example 1.4.1, p. 68"]
theorem ex_1_4_1_composite_steps :
    (fun x : ℝ => 3 * (x + 4)) 5 = 27 ∧ ∀ x : ℝ, 3 * (x + 4) = 3 * x + 12 :=
  ⟨by norm_num, fun x => by ring⟩

/-- Stitz-Zeager Example 1.4.2(1a): for `f x = -x² + 3x + 4`, `f(-1) = 0`, `f 0 = 4`, `f 2 = 6`. -/
@[kb "stitzzeager2013" "Example 1.4.2, p. 68"]
theorem ex_1_4_2_a_values :
    (fun x : ℝ => -x ^ 2 + 3 * x + 4) (-1) = 0 ∧ (fun x : ℝ => -x ^ 2 + 3 * x + 4) 0 = 4 ∧
      (fun x : ℝ => -x ^ 2 + 3 * x + 4) 2 = 6 := by
  norm_num

/-- Stitz-Zeager Example 1.4.2(1b): `f (2x) = -4x² + 6x + 4` and `2 f x = -2x² + 6x + 8`. -/
@[kb "stitzzeager2013" "Example 1.4.2, p. 68"]
theorem ex_1_4_2_b_scaling (x : ℝ) :
    (fun x : ℝ => -x ^ 2 + 3 * x + 4) (2 * x) = -4 * x ^ 2 + 6 * x + 4 ∧
      2 * (fun x : ℝ => -x ^ 2 + 3 * x + 4) x = -2 * x ^ 2 + 6 * x + 8 := by
  constructor <;> ring

/-- Stitz-Zeager Example 1.4.2(1c): `f (x+2) = -x² - x + 6`, `f x + 2 = -x² + 3x + 6`,
`f x + f 2 = -x² + 3x + 10`. -/
@[kb "stitzzeager2013" "Example 1.4.2, p. 68"]
theorem ex_1_4_2_c_shifts (x : ℝ) :
    (fun x : ℝ => -x ^ 2 + 3 * x + 4) (x + 2) = -x ^ 2 - x + 6 ∧
      (fun x : ℝ => -x ^ 2 + 3 * x + 4) x + 2 = -x ^ 2 + 3 * x + 6 ∧
      (fun x : ℝ => -x ^ 2 + 3 * x + 4) x + (fun x : ℝ => -x ^ 2 + 3 * x + 4) 2 =
        -x ^ 2 + 3 * x + 10 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num <;> ring

/-- Stitz-Zeager Example 1.4.2(2): `-x² + 3x + 4 = 4` exactly when `x = 0` or `x = 3`. -/
@[kb "stitzzeager2013" "Example 1.4.2, p. 68"]
theorem ex_1_4_2_d_solve (x : ℝ) : -x ^ 2 + 3 * x + 4 = 4 ↔ x = 0 ∨ x = 3 := by
  constructor
  · intro h
    have : x * (3 - x) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · left; exact h
    · right; linarith
  · rintro (h | h) <;> subst h <;> norm_num

/-- Stitz-Zeager Example 1.4.3(1): `√(4-3x)` is defined exactly for `x ≤ 4/3`. -/
@[kb "stitzzeager2013" "Example 1.4.3, p. 70"]
theorem ex_1_4_3_a_domain : {x : ℝ | 0 ≤ 4 - 3 * x} = Iic (4 / 3) := by
  ext x; simp only [mem_setOf_eq, mem_Iic]; constructor <;> intro h <;> linarith

/-- Stitz-Zeager Example 1.4.3(3): `2 / (1 - 4x/(x-3))` makes sense exactly off `x = -1` and `x = 3`. -/
@[kb "stitzzeager2013" "Example 1.4.3, p. 70"]
theorem ex_1_4_3_c_domain :
    {x : ℝ | x - 3 ≠ 0 ∧ 1 - 4 * x / (x - 3) ≠ 0} = Iio (-1) ∪ Ioo (-1) 3 ∪ Ioi 3 := by
  ext x
  simp only [mem_setOf_eq, mem_union, mem_Iio, mem_Ioo, mem_Ioi]
  constructor
  · rintro ⟨h1, h2⟩
    have hx : x ≠ -1 := by
      rintro rfl; apply h2; norm_num
    have hx3 : x ≠ 3 := fun h => h1 (by rw [h]; norm_num)
    rcases lt_trichotomy x 3 with h | h | h
    · rcases lt_trichotomy x (-1) with h' | h' | h'
      · exact Or.inl (Or.inl h')
      · exact absurd h' hx
      · exact Or.inl (Or.inr ⟨h', h⟩)
    · exact absurd h hx3
    · exact Or.inr h
  · intro h
    have hx3 : x - 3 ≠ 0 := by
      rcases h with (h | ⟨_, h⟩) | h <;> intro h0 <;> linarith [h0]
    refine ⟨hx3, fun h0 => ?_⟩
    have : x - 3 - 4 * x = 0 := by
      field_simp at h0; linarith
    have hx : x = -1 := by linarith
    rcases h with (h | ⟨h, _⟩) | h <;> linarith

/-- Stitz-Zeager Example 1.4.3(4): `⁴√(2x+1) / (x²-1)` makes sense exactly for `x ≥ -1/2`, `x ≠ 1`. -/
@[kb "stitzzeager2013" "Example 1.4.3, p. 70"]
theorem ex_1_4_3_d_domain :
    {x : ℝ | 0 ≤ 2 * x + 1 ∧ x ^ 2 - 1 ≠ 0} = Ico (-1 / 2) 1 ∪ Ioi 1 := by
  ext x
  simp only [mem_setOf_eq, mem_union, mem_Ico, mem_Ioi]
  constructor
  · rintro ⟨h1, h2⟩
    have hx : x ≠ 1 := by rintro rfl; apply h2; norm_num
    rcases lt_or_gt_of_ne hx with h | h
    · left; exact ⟨by linarith, h⟩
    · right; exact h
  · intro h
    have h1 : 0 ≤ 2 * x + 1 := by rcases h with ⟨h, _⟩ | h <;> linarith
    refine ⟨h1, fun h0 => ?_⟩
    have : (x - 1) * (x + 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h' <;> rcases h with ⟨h, h2⟩ | h <;> linarith

/-- Stitz-Zeager Example 1.4.3(5): `4 / (6 - √(t+3))` makes sense exactly for `t ≥ -3`, `t ≠ 33`. -/
@[kb "stitzzeager2013" "Example 1.4.3, p. 70"]
theorem ex_1_4_3_e_domain :
    {t : ℝ | 0 ≤ t + 3 ∧ 6 - Real.sqrt (t + 3) ≠ 0} = Ico (-3) 33 ∪ Ioi 33 := by
  ext t
  simp only [mem_setOf_eq, mem_union, mem_Ico, mem_Ioi]
  have key : ∀ t : ℝ, 0 ≤ t + 3 → (6 - Real.sqrt (t + 3) = 0 ↔ t = 33) := by
    intro t ht
    constructor
    · intro h
      have : Real.sqrt (t + 3) = 6 := by linarith
      have := Real.sq_sqrt ht
      nlinarith
    · rintro rfl
      rw [show (33 : ℝ) + 3 = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]; norm_num
  constructor
  · rintro ⟨h1, h2⟩
    have hx : t ≠ 33 := fun h => h2 ((key t h1).mpr h)
    rcases lt_or_gt_of_ne hx with h | h
    · left; exact ⟨by linarith, h⟩
    · right; exact h
  · intro h
    have h1 : 0 ≤ t + 3 := by rcases h with ⟨h, _⟩ | h <;> linarith
    refine ⟨h1, fun h0 => ?_⟩
    have := (key t h1).mp h0
    rcases h with ⟨_, h⟩ | h <;> linarith

/-- Stitz-Zeager Example 1.4.3(6): `3x²/x` makes sense (as a quotient with nonzero denominator)
exactly for `x ≠ 0`. -/
@[kb "stitzzeager2013" "Example 1.4.3, p. 70"]
theorem ex_1_4_3_f_domain : {x : ℝ | x ≠ 0} = Iio 0 ∪ Ioi 0 := by
  ext x; simp [lt_or_lt_iff_ne]

/-- Stitz-Zeager Example 1.4.4(1): for the rocket height `h t = -5t² + 100t` (`t ≤ 20`), else `0`,
`h 10 = 500` and `h 60 = 0`. -/
@[kb "stitzzeager2013" "Example 1.4.4, p. 73"]
theorem ex_1_4_4_a_values :
    (fun t : ℝ => if t ≤ 20 then -5 * t ^ 2 + 100 * t else 0) 10 = 500 ∧
      (fun t : ℝ => if t ≤ 20 then -5 * t ^ 2 + 100 * t else 0) 60 = 0 := by
  constructor <;> norm_num

/-- Stitz-Zeager Example 1.4.4(2): for `t ≥ 0`, the rocket height equals `375` exactly when `t = 5`
or `t = 15`. -/
@[kb "stitzzeager2013" "Example 1.4.4, p. 73"]
theorem ex_1_4_4_b_solve (t : ℝ) (ht : 0 ≤ t) :
    (if t ≤ 20 then -5 * t ^ 2 + 100 * t else 0) = (375 : ℝ) ↔ t = 5 ∨ t = 15 := by
  by_cases h : t ≤ 20
  · rw [if_pos h]
    constructor
    · intro h0
      have : (t - 5) * (t - 15) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h
      · left; linarith
      · right; linarith
    · rintro (h | h) <;> subst h <;> norm_num
  · rw [if_neg h]
    constructor
    · intro h0; norm_num at h0
    · rintro (h' | h') <;> exfalso <;> apply h <;> linarith

/-! ## Section 1.5 -/

/-- Stitz-Zeager Example 1.5.2(1): for `f x = x² - x - 2` and `h ≠ 0`, the difference quotient is
`2x + h - 1`. -/
@[kb "stitzzeager2013" "Example 1.5.2, p. 91"]
theorem ex_1_5_2_a_quadratic (x h : ℝ) (hh : h ≠ 0) :
    ((x + h) ^ 2 - (x + h) - 2 - (x ^ 2 - x - 2)) / h = 2 * x + h - 1 := by
  field_simp; ring

/-- Stitz-Zeager Example 1.5.2(2): for `g x = 3/(2x+1)`, the difference quotient is
`-6 / ((2x+2h+1)(2x+1))`. -/
@[kb "stitzzeager2013" "Example 1.5.2, p. 91"]
theorem ex_1_5_2_b_rational (x h : ℝ) (hh : h ≠ 0) (h1 : 2 * x + 1 ≠ 0) (h2 : 2 * x + 2 * h + 1 ≠ 0) :
    (3 / (2 * (x + h) + 1) - 3 / (2 * x + 1)) / h = -6 / ((2 * x + 2 * h + 1) * (2 * x + 1)) := by
  have h2' : 2 * (x + h) + 1 ≠ 0 := by intro h0; apply h2; linarith
  field_simp; ring

/-- Stitz-Zeager Example 1.5.2(3): for `r x = √x`, `x ≥ 0` and `h > 0`, the difference quotient is
`1 / (√(x+h) + √x)`. -/
@[kb "stitzzeager2013" "Example 1.5.2, p. 91"]
theorem ex_1_5_2_c_sqrt (x h : ℝ) (hx : 0 ≤ x) (hh : 0 < h) :
    (Real.sqrt (x + h) - Real.sqrt x) / h = 1 / (Real.sqrt (x + h) + Real.sqrt x) := by
  have h1 : 0 < Real.sqrt (x + h) := Real.sqrt_pos.mpr (by linarith)
  have h2 := Real.sqrt_nonneg x
  have h3 := Real.sq_sqrt (show 0 ≤ x + h by linarith)
  have h4 := Real.sq_sqrt hx
  rw [div_eq_div_iff hh.ne' (by positivity)]
  nlinarith

/-- Stitz-Zeager Example 1.5.3: with `C x = 100x + 2000` and `p x = 450 - 15x`, `C 0 = 2000`,
`C 10 = 3000`, `p 0 = 450`, `p 20 = 150`. -/
@[kb "stitzzeager2013" "Example 1.5.3, p. 94"]
theorem ex_1_5_3_a_values :
    (100 * (0 : ℝ) + 2000 = 2000) ∧ (100 * (10 : ℝ) + 2000 = 3000) ∧
      (450 - 15 * (0 : ℝ) = 450) ∧ (450 - 15 * (20 : ℝ) = 150) := by
  norm_num

/-- Stitz-Zeager Example 1.5.3(4): the price `450 - 15x` is zero exactly when `x = 30`. -/
@[kb "stitzzeager2013" "Example 1.5.3, p. 94"]
theorem ex_1_5_3_b_price_zero (x : ℝ) : 450 - 15 * x = 0 ↔ x = 30 := by
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Example 1.5.3(5): revenue `x * p x = 450x - 15x²` and profit `R - C = -15x² + 350x - 2000`. -/
@[kb "stitzzeager2013" "Example 1.5.3, p. 94"]
theorem ex_1_5_3_c_revenue_profit (x : ℝ) :
    x * (450 - 15 * x) = -15 * x ^ 2 + 450 * x ∧
      x * (450 - 15 * x) - (100 * x + 2000) = -15 * x ^ 2 + 350 * x - 2000 := by
  constructor <;> ring

/-- Stitz-Zeager Example 1.5.3(6): revenue at `0` items is `0` and profit is `-2000`. -/
@[kb "stitzzeager2013" "Example 1.5.3, p. 94"]
theorem ex_1_5_3_d_zero_items :
    (0 : ℝ) * (450 - 15 * 0) = 0 ∧ (0 : ℝ) * (450 - 15 * 0) - (100 * 0 + 2000) = -2000 := by
  norm_num

/-- Stitz-Zeager Example 1.5.3(7): the profit `-15x² + 350x - 2000` vanishes exactly at `x = 10`
and `x = 40/3`. -/
@[kb "stitzzeager2013" "Example 1.5.3, p. 94"]
theorem ex_1_5_3_e_break_even (x : ℝ) :
    -15 * x ^ 2 + 350 * x - 2000 = 0 ↔ x = 10 ∨ x = 40 / 3 := by
  constructor
  · intro h
    have : (x - 10) * (3 * x - 40) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  · rintro (h | h) <;> subst h <;> norm_num

/-! ## Section 1.6 -/

/-- Stitz-Zeager Example 1.6.1: the zeros of `x² - x - 6` are `-2` and `3`, and its value at `0` is `-6`. -/
@[kb "stitzzeager2013" "Example 1.6.1, p. 105"]
theorem ex_1_6_1_intercepts (x : ℝ) :
    (x ^ 2 - x - 6 = 0 ↔ x = -2 ∨ x = 3) ∧ ((0 : ℝ) ^ 2 - 0 - 6 = -6) := by
  refine ⟨?_, by norm_num⟩
  constructor
  · intro h
    have : (x + 2) * (x - 3) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  · rintro (h | h) <;> subst h <;> norm_num

/-- Stitz-Zeager Example 1.6.2: for the piecewise function `4 - x²` (`x < 1`), `x - 3` (`x ≥ 1`),
the zeros are `-2` and `3`, and `f 0 = 4`, `f 1 = -2`. -/
@[kb "stitzzeager2013" "Example 1.6.2, p. 106"]
theorem ex_1_6_2_zeros_and_values (x : ℝ) :
    ((if x < 1 then 4 - x ^ 2 else x - 3) = (0 : ℝ) ↔ x = -2 ∨ x = 3) ∧
      (fun x : ℝ => if x < 1 then 4 - x ^ 2 else x - 3) 0 = 4 ∧
      (fun x : ℝ => if x < 1 then 4 - x ^ 2 else x - 3) 1 = -2 := by
  refine ⟨?_, by norm_num, by norm_num⟩
  by_cases h : x < 1
  · rw [if_pos h]
    constructor
    · intro h0
      have : (2 - x) * (2 + x) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h' | h'
      · linarith
      · left; linarith
    · rintro (h' | h')
      · subst h'; norm_num
      · exfalso; linarith
  · rw [if_neg h]
    constructor
    · intro h0; right; linarith
    · rintro (h' | h')
      · exfalso; apply h; linarith
      · linarith

/-- Stitz-Zeager Example 1.6.3(1): `5/(2 - x²)` is even. -/
@[kb "stitzzeager2013" "Example 1.6.3, p. 107"]
theorem ex_1_6_3_a_even : Function.Even (fun x : ℝ => 5 / (2 - x ^ 2)) := by
  intro x; simp

/-- Stitz-Zeager Example 1.6.3(2): `5x/(2 - x²)` is odd (and not even, since `g 1 = 5`, `g (-1) = -5`). -/
@[kb "stitzzeager2013" "Example 1.6.3, p. 107"]
theorem ex_1_6_3_b_odd :
    Function.Odd (fun x : ℝ => 5 * x / (2 - x ^ 2)) ∧ ¬ Function.Even (fun x : ℝ => 5 * x / (2 - x ^ 2)) := by
  constructor
  · intro x; simp [neg_div]
  · intro h
    have := h 1
    norm_num at this

/-- Stitz-Zeager Example 1.6.3(3): `5x/(2 - x³)` is neither even nor odd. -/
@[kb "stitzzeager2013" "Example 1.6.3, p. 107"]
theorem ex_1_6_3_c_neither :
    ¬ Function.Even (fun x : ℝ => 5 * x / (2 - x ^ 3)) ∧ ¬ Function.Odd (fun x : ℝ => 5 * x / (2 - x ^ 3)) := by
  constructor
  · intro h
    have := h 1
    norm_num at this
  · intro h
    have := h 1
    norm_num at this

/-- Stitz-Zeager Example 1.6.3(4): `5x/(2x - x³)` is even (the factor `x` cancels away from `0`). -/
@[kb "stitzzeager2013" "Example 1.6.3, p. 107"]
theorem ex_1_6_3_d_even : Function.Even (fun x : ℝ => 5 * x / (2 * x - x ^ 3)) := by
  intro x
  dsimp only
  rw [show 2 * -x - (-x) ^ 3 = -(2 * x - x ^ 3) by ring, ← neg_div_neg_eq]
  ring_nf

/-- Stitz-Zeager Example 1.6.3(5): `x² - x/100 - 1` is neither even nor odd. -/
@[kb "stitzzeager2013" "Example 1.6.3, p. 107"]
theorem ex_1_6_3_e_neither :
    ¬ Function.Even (fun x : ℝ => x ^ 2 - x / 100 - 1) ∧ ¬ Function.Odd (fun x : ℝ => x ^ 2 - x / 100 - 1) := by
  constructor
  · intro h
    have := h 1
    norm_num at this
  · intro h
    have := h 0
    norm_num at this

/-- Stitz-Zeager Example 1.6.3(6): the piecewise function `x + 3` (`x < 0`), `-x + 3` (`x ≥ 0`) is even. -/
@[kb "stitzzeager2013" "Example 1.6.3, p. 107"]
theorem ex_1_6_3_f_even : Function.Even (fun x : ℝ => if x < 0 then x + 3 else -x + 3) := by
  intro x
  dsimp only
  rcases lt_trichotomy x 0 with h | h | h
  · rw [if_neg (not_lt.mpr (by linarith)), if_pos h]; ring
  · subst h; simp
  · rw [if_pos (by linarith : -x < 0), if_neg (not_lt.mpr h.le)]

/-- Stitz-Zeager Example 1.6.5: `15x/(x²+3)` has maximum value `5√3/2` at `x = √3` and minimum
value `-5√3/2` at `x = -√3`. -/
@[kb "stitzzeager2013" "Example 1.6.5, p. 117"]
theorem ex_1_6_5_extrema :
    (∀ x : ℝ, 15 * x / (x ^ 2 + 3) ≤ 5 * Real.sqrt 3 / 2) ∧
      15 * Real.sqrt 3 / (Real.sqrt 3 ^ 2 + 3) = 5 * Real.sqrt 3 / 2 ∧
      (∀ x : ℝ, -(5 * Real.sqrt 3 / 2) ≤ 15 * x / (x ^ 2 + 3)) ∧
      15 * (-Real.sqrt 3) / ((-Real.sqrt 3) ^ 2 + 3) = -(5 * Real.sqrt 3 / 2) := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨fun x => ?_, ?_, fun x => ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (x - Real.sqrt 3)]
  · rw [h3, div_eq_iff (by norm_num)]; ring
  · rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (x + Real.sqrt 3)]
  · rw [neg_sq, h3, div_eq_iff (by norm_num)]; ring

end UndergradKB.Precalculus.Course
