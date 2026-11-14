import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Interval.Set.Basic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 1 (Stitz-Zeager): worked examples, wave 5 -/

namespace UndergradKB.Precalculus.Course

open Set

/-! ## Section 1.1 -/

/-- Stitz-Zeager Example 1.1.2: of the plotted points, `E(5,0)` and `G(-7,0)` lie on the x-axis, `F(0,5)` and
`H(0,-9)` on the y-axis, `O` on both, and `A`, `B`, `C`, `D` lie in the four open quadrants (I, II, III, IV). -/
@[kb "stitzzeager2013" "Example 1.1.2, p. 19"]
theorem ex_1_1_2_axes_and_quadrants :
    (((5 : ℝ), (0 : ℝ)).2 = 0 ∧ ((-7 : ℝ), (0 : ℝ)).2 = 0) ∧
      (((0 : ℝ), (5 : ℝ)).1 = 0 ∧ ((0 : ℝ), (-9 : ℝ)).1 = 0) ∧
      (∀ p : ℝ × ℝ, p.1 = 0 ∧ p.2 = 0 ↔ p = (0, 0)) ∧
      ((0 : ℝ) < 5 ∧ (0 : ℝ) < 8) ∧ ((-5 / 2 : ℝ) < 0 ∧ (0 : ℝ) < 3) ∧
      ((-5.8 : ℝ) < 0 ∧ (-3 : ℝ) < 0) ∧ ((0 : ℝ) < 4.5 ∧ (-1 : ℝ) < 0) := by
  refine ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, fun p => by rw [Prod.ext_iff], ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    ⟨?_, ?_⟩⟩ <;> norm_num

/-! ## Section 1.2 -/

/-- Stitz-Zeager Example 1.2.1(1): the finite relation `A` consists of exactly the four listed points, among them
two with the same x-coordinate `-3`. -/
@[kb "stitzzeager2013" "Example 1.2.1, p. 32"]
theorem ex_1_2_1_a_finite_relation :
    (({(0, 0), (-3, 1), (4, 2), (-3, 2)} : Finset (ℝ × ℝ)).card = 4) ∧
      (((-3 : ℝ), (1 : ℝ)) ∈ ({(0, 0), (-3, 1), (4, 2), (-3, 2)} : Set (ℝ × ℝ))) ∧
      (((-3 : ℝ), (2 : ℝ)) ∈ ({(0, 0), (-3, 1), (4, 2), (-3, 2)} : Set (ℝ × ℝ))) := by
  refine ⟨?_, by simp, by simp⟩
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_singleton] <;> norm_num

/-- Stitz-Zeager Example 1.2.1(2,3): `HLS₁` (with `x ≤ 4`) is `HLS₂` (with `x < 4`) together with the endpoint
`(4,3)`; the endpoint `(4,3)` is not in `HLS₂`, but points such as `(3.9,3)` and `(3.99,3)` are, so `HLS₂` does not
stop at `(3,3)`. -/
@[kb "stitzzeager2013" "Example 1.2.1, p. 32"]
theorem ex_1_2_1_b_horizontal_segments :
    ({p : ℝ × ℝ | p.2 = 3 ∧ -2 ≤ p.1 ∧ p.1 ≤ 4} =
        {p : ℝ × ℝ | p.2 = 3 ∧ -2 ≤ p.1 ∧ p.1 < 4} ∪ {((4 : ℝ), (3 : ℝ))}) ∧
      (((4 : ℝ), (3 : ℝ)) ∉ {p : ℝ × ℝ | p.2 = 3 ∧ -2 ≤ p.1 ∧ p.1 < 4}) ∧
      (((3.9 : ℝ), (3 : ℝ)) ∈ {p : ℝ × ℝ | p.2 = 3 ∧ -2 ≤ p.1 ∧ p.1 < 4}) ∧
      (((3.99 : ℝ), (3 : ℝ)) ∈ {p : ℝ × ℝ | p.2 = 3 ∧ -2 ≤ p.1 ∧ p.1 < 4}) ∧
      ({p : ℝ × ℝ | p.2 = 3 ∧ -2 ≤ p.1 ∧ p.1 < 4} ≠ {p : ℝ × ℝ | p.2 = 3 ∧ -2 ≤ p.1 ∧ p.1 ≤ 3}) := by
  refine ⟨?_, by norm_num, by norm_num, by norm_num, ?_⟩
  · ext ⟨x, y⟩
    simp only [mem_ofPred_eq, mem_union, mem_singleton_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨hy, h1, h2⟩
      rcases h2.lt_or_eq with h | h
      · exact Or.inl ⟨hy, h1, h⟩
      · exact Or.inr ⟨h, hy⟩
    · rintro (⟨hy, h1, h2⟩ | ⟨rfl, rfl⟩)
      · exact ⟨hy, h1, h2.le⟩
      · norm_num
  · intro h
    have : ((3.5 : ℝ), (3 : ℝ)) ∈ {p : ℝ × ℝ | p.2 = 3 ∧ -2 ≤ p.1 ∧ p.1 < 4} := by norm_num
    rw [h] at this
    norm_num at this

/-- Stitz-Zeager Example 1.2.1(4,5,6): the vertical line `V` contains `(3,y)` for every real `y`; the horizontal
line `H : y = -2` contains `(x,-2)` for every `x`; the strip `1 < y ≤ 3` contains `(0,3)` but neither `(0,1)` nor
`(0,4)`. -/
@[kb "stitzzeager2013" "Example 1.2.1, p. 32"]
theorem ex_1_2_1_c_lines_and_strip :
    (∀ y : ℝ, (3, y) ∈ {p : ℝ × ℝ | p.1 = 3}) ∧ (∀ x : ℝ, (x, -2) ∈ {p : ℝ × ℝ | p.2 = -2}) ∧
      (((0 : ℝ), (3 : ℝ)) ∈ {p : ℝ × ℝ | 1 < p.2 ∧ p.2 ≤ 3}) ∧
      (((0 : ℝ), (1 : ℝ)) ∉ {p : ℝ × ℝ | 1 < p.2 ∧ p.2 ≤ 3}) ∧
      (((0 : ℝ), (4 : ℝ)) ∉ {p : ℝ × ℝ | 1 < p.2 ∧ p.2 ≤ 3}) := by
  refine ⟨fun y => rfl, fun x => rfl, by norm_num, by norm_num, by norm_num⟩

/-! ## Section 1.3 -/

/-- Stitz-Zeager Example 1.3.1(1): in `R₁ = {(-2,1),(1,3),(1,4),(3,-1)}` the x-coordinate `1` is matched with two
different y-values, so `R₁` does not describe `y` as a function of `x`. -/
@[kb "stitzzeager2013" "Example 1.3.1, p. 55"]
theorem ex_1_3_1_a_not_function :
    ¬ ∀ x y₁ y₂ : ℝ, (x, y₁) ∈ ({(-2, 1), (1, 3), (1, 4), (3, -1)} : Set (ℝ × ℝ)) →
      (x, y₂) ∈ ({(-2, 1), (1, 3), (1, 4), (3, -1)} : Set (ℝ × ℝ)) → y₁ = y₂ := by
  intro h
  have := h 1 3 4 (by simp) (by simp)
  norm_num at this

/-- Stitz-Zeager Example 1.3.1(2): in `R₂ = {(-2,1),(1,3),(2,3),(3,-1)}` every x-coordinate occurs once, so `R₂`
describes `y` as a function of `x` (although two points share the y-coordinate `3`). -/
@[kb "stitzzeager2013" "Example 1.3.1, p. 55"]
theorem ex_1_3_1_b_function :
    (∀ x y₁ y₂ : ℝ, (x, y₁) ∈ ({(-2, 1), (1, 3), (2, 3), (3, -1)} : Set (ℝ × ℝ)) →
      (x, y₂) ∈ ({(-2, 1), (1, 3), (2, 3), (3, -1)} : Set (ℝ × ℝ)) → y₁ = y₂) ∧
    (((1 : ℝ), (3 : ℝ)) ∈ ({(-2, 1), (1, 3), (2, 3), (3, -1)} : Set (ℝ × ℝ)) ∧
      ((2 : ℝ), (3 : ℝ)) ∈ ({(-2, 1), (1, 3), (2, 3), (3, -1)} : Set (ℝ × ℝ))) := by
  refine ⟨fun x y₁ y₂ h1 h2 => ?_, by simp, by simp⟩
  simp only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq] at h1 h2
  rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases h2 with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> first | rfl | (norm_num at h)

/-- Stitz-Zeager Example 1.3.3 (vertical line test, in an abstract form): if `S` is a
relation giving `y` as a function of `x` and has the point `(1, y₀)` with `y₀ ≠ 2`, then adding the point `(1,2)`
(as for `S₁`) violates the test; if instead `S` has no point on the line `x = 1` (the open circle of `S₂`), adding
`(1,2)` keeps the relation a function. -/
@[kb "stitzzeager2013" "Example 1.3.3, p. 56"]
theorem ex_1_3_3_vertical_line_test (S : Set (ℝ × ℝ))
    (hS : ∀ x y₁ y₂ : ℝ, (x, y₁) ∈ S → (x, y₂) ∈ S → y₁ = y₂) :
    ((∃ y₀ : ℝ, y₀ ≠ 2 ∧ (1, y₀) ∈ S) →
      ¬ ∀ x y₁ y₂ : ℝ, (x, y₁) ∈ insert ((1 : ℝ), (2 : ℝ)) S →
        (x, y₂) ∈ insert ((1 : ℝ), (2 : ℝ)) S → y₁ = y₂) ∧
    ((∀ y : ℝ, (1, y) ∉ S) →
      ∀ x y₁ y₂ : ℝ, (x, y₁) ∈ insert ((1 : ℝ), (2 : ℝ)) S →
        (x, y₂) ∈ insert ((1 : ℝ), (2 : ℝ)) S → y₁ = y₂) := by
  constructor
  · rintro ⟨y₀, hy₀, hmem⟩ h
    exact hy₀ (h 1 y₀ 2 (Or.inr hmem) (Or.inl rfl))
  · intro hno x y₁ y₂ h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · simp only [Prod.mk.injEq] at h1 h2
      rw [h1.2, h2.2]
    · simp only [Prod.mk.injEq] at h1
      exact absurd (h1.1 ▸ h2) (hno y₂)
    · simp only [Prod.mk.injEq] at h2
      exact absurd (h2.1 ▸ h1) (hno y₁)
    · exact hS x y₁ y₂ h1 h2

/-! ## Section 1.6 -/

/-- Stitz-Zeager Example 1.6.6: the squared distance `x² + ((x-3)²)²` from the origin to the point `(x,(x-3)²)` of
the parabola is at least `5`, with equality exactly at `x = 2`; so the closest point is `(2,1)` (distance `√5`),
the exact value behind the calculator's `(2.00, 1.00)`. -/
@[kb "stitzzeager2013" "Example 1.6.6, p. 117"]
theorem ex_1_6_6_closest_point (x : ℝ) :
    Real.sqrt 5 ≤ Real.sqrt (x ^ 2 + ((x - 3) ^ 2) ^ 2) ∧
      (Real.sqrt (x ^ 2 + ((x - 3) ^ 2) ^ 2) = Real.sqrt 5 ↔ x = 2) := by
  have key : x ^ 2 + ((x - 3) ^ 2) ^ 2 - 5 = (x - 2) ^ 2 * ((x - 4) ^ 2 + 3) := by ring
  have hge : 5 ≤ x ^ 2 + ((x - 3) ^ 2) ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg (x - 2)) (add_nonneg (sq_nonneg (x - 4)) (by norm_num : (0 : ℝ) ≤ 3))]
  refine ⟨Real.sqrt_le_sqrt hge, ?_⟩
  rw [Real.sqrt_inj (by positivity) (by norm_num)]
  constructor
  · intro h
    have h0 : (x - 2) ^ 2 * ((x - 4) ^ 2 + 3) = 0 := by rw [← key, h]; norm_num
    rcases mul_eq_zero.1 h0 with h1 | h1
    · nlinarith [sq_nonneg (x - 2)]
    · nlinarith [sq_nonneg (x - 4)]
  · rintro rfl
    norm_num

/-! ## Section 1.7 -/

/-- Stitz-Zeager Example 1.7.1: starting from `f(x) = √x` on `[0,∞)` (range `[0,∞)`, through `(0,0)`, `(1,1)`,
`(4,2)`), `g(x) = √x - 1` has range `[-1,∞)` and passes through `(0,-1)`, `(1,0)`, `(4,1)`. -/
@[kb "stitzzeager2013" "Example 1.7.1, p. 135"]
theorem ex_1_7_1_a_g :
    (Real.sqrt '' Ici (0 : ℝ) = Ici 0) ∧
      ((fun x : ℝ => Real.sqrt x - 1) '' Ici 0 = Ici (-1)) ∧
      (Real.sqrt 0 - 1 = -1 ∧ Real.sqrt 1 - 1 = 0 ∧ Real.sqrt 4 - 1 = 1) := by
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  refine ⟨?_, ?_, by simp, by simp, by rw [h4]; norm_num⟩
  · ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      exact Real.sqrt_nonneg x
    · intro hy
      exact ⟨y ^ 2, mem_Ici.2 (sq_nonneg y), Real.sqrt_sq hy⟩
  · ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      have := Real.sqrt_nonneg x
      exact (by linarith : (-1 : ℝ) ≤ Real.sqrt x - 1)
    · intro hy
      have hy' := mem_Ici.1 hy
      exact ⟨(y + 1) ^ 2, mem_Ici.2 (sq_nonneg _), by
        show Real.sqrt ((y + 1) ^ 2) - 1 = y
        rw [Real.sqrt_sq (by linarith)]; ring⟩

/-- Stitz-Zeager Example 1.7.1(3): `j(x) = √(x-1) = f(x-1)` has domain `[1,∞)` (where `x - 1 ≥ 0`) and range `[0,∞)`,
and passes through `(1,0)`, `(2,1)`, `(5,2)`. -/
@[kb "stitzzeager2013" "Example 1.7.1, p. 135"]
theorem ex_1_7_1_b_j :
    ({x : ℝ | 0 ≤ x - 1} = Ici 1) ∧ ((fun x : ℝ => Real.sqrt (x - 1)) '' Ici 1 = Ici 0) ∧
      (Real.sqrt (1 - 1) = 0 ∧ Real.sqrt (2 - 1) = 1 ∧ Real.sqrt (5 - 1) = 2) := by
  refine ⟨by ext x; simp [sub_nonneg], ?_, by simp, by norm_num, ?_⟩
  · ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      exact Real.sqrt_nonneg _
    · intro hy
      exact ⟨y ^ 2 + 1, by simp [sq_nonneg], by
        show Real.sqrt (y ^ 2 + 1 - 1) = y
        rw [add_sub_cancel_right]; exact Real.sqrt_sq hy⟩
  · rw [show (5 : ℝ) - 1 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- Stitz-Zeager Example 1.7.1(4): `m(x) = √(x+3) - 2 = f(x+3) - 2` has domain `[-3,∞)` and range `[-2,∞)`, and
passes through `(-3,-2)`, `(-2,-1)`, `(1,0)`. -/
@[kb "stitzzeager2013" "Example 1.7.1, p. 135"]
theorem ex_1_7_1_c_m :
    ({x : ℝ | 0 ≤ x + 3} = Ici (-3)) ∧ ((fun x : ℝ => Real.sqrt (x + 3) - 2) '' Ici (-3) = Ici (-2)) ∧
      (Real.sqrt (-3 + 3) - 2 = -2 ∧ Real.sqrt (-2 + 3) - 2 = -1 ∧ Real.sqrt (1 + 3) - 2 = 0) := by
  refine ⟨by ext x; simp [← sub_nonneg, sub_neg_eq_add], ?_, by simp, by norm_num, ?_⟩
  · ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      have := Real.sqrt_nonneg (x + 3)
      exact (by linarith : (-2 : ℝ) ≤ Real.sqrt (x + 3) - 2)
    · intro hy
      have hy' := mem_Ici.1 hy
      refine ⟨(y + 2) ^ 2 - 3, ?_, ?_⟩
      · simp only [mem_Ici]; nlinarith [sq_nonneg (y + 2)]
      · show Real.sqrt ((y + 2) ^ 2 - 3 + 3) - 2 = y
        rw [sub_add_cancel, Real.sqrt_sq (by linarith)]; ring
  · rw [show (1 : ℝ) + 3 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]; norm_num

/-- Stitz-Zeager Example 1.7.2(1): `g(x) = √(-x) = f(-x)` has domain `(-∞,0]` and range `[0,∞)`, and passes through
`(-1,1)` and `(-4,2)`. -/
@[kb "stitzzeager2013" "Example 1.7.2, p. 138"]
theorem ex_1_7_2_a_g :
    ({x : ℝ | 0 ≤ -x} = Iic 0) ∧ ((fun x : ℝ => Real.sqrt (-x)) '' Iic 0 = Ici 0) ∧
      (Real.sqrt (-(-1)) = 1 ∧ Real.sqrt (-(-4)) = 2) := by
  refine ⟨by ext x; simp, ?_, by simp, ?_⟩
  · ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      exact Real.sqrt_nonneg _
    · intro hy
      exact ⟨-(y ^ 2), by simp [sq_nonneg], by
        show Real.sqrt (-(-(y ^ 2))) = y
        rw [neg_neg]; exact Real.sqrt_sq hy⟩
  · rw [neg_neg, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- Stitz-Zeager Example 1.7.2(2): `j(x) = √(3-x)` has domain `(-∞,3]`, range `[0,∞)`; it equals `j₁(-x)` with
`j₁(x) = √(x+3)` (shift left by `3`, then reflect), and passes through `(-1,2)`, `(2,1)`, `(3,0)`. -/
@[kb "stitzzeager2013" "Example 1.7.2, p. 138"]
theorem ex_1_7_2_b_j :
    ({x : ℝ | 0 ≤ 3 - x} = Iic 3) ∧ ((fun x : ℝ => Real.sqrt (3 - x)) '' Iic 3 = Ici 0) ∧
      (∀ x : ℝ, Real.sqrt (3 - x) = (fun t : ℝ => Real.sqrt (t + 3)) (-x)) ∧
      (Real.sqrt (3 - (-1)) = 2 ∧ Real.sqrt (3 - 2) = 1 ∧ Real.sqrt (3 - 3) = 0) := by
  refine ⟨by ext x; simp [sub_nonneg], ?_, fun x => by ring_nf, ?_, by norm_num, by simp⟩
  · ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      exact Real.sqrt_nonneg _
    · intro hy
      exact ⟨3 - y ^ 2, by simp [sq_nonneg], by
        show Real.sqrt (3 - (3 - y ^ 2)) = y
        rw [sub_sub_cancel]; exact Real.sqrt_sq hy⟩
  · rw [show (3 : ℝ) - -1 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- Stitz-Zeager Example 1.7.2(3): `m(x) = 3 - √x = -f(x) + 3` has domain `[0,∞)` and range `(-∞,3]`, and passes
through `(0,3)`, `(1,2)`, `(4,1)`. -/
@[kb "stitzzeager2013" "Example 1.7.2, p. 138"]
theorem ex_1_7_2_c_m :
    ((fun x : ℝ => 3 - Real.sqrt x) '' Ici 0 = Iic 3) ∧
      (3 - Real.sqrt 0 = 3 ∧ 3 - Real.sqrt 1 = 2 ∧ 3 - Real.sqrt 4 = 1) := by
  refine ⟨?_, by simp, by norm_num, ?_⟩
  · ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      have := Real.sqrt_nonneg x
      exact (by linarith : 3 - Real.sqrt x ≤ 3)
    · intro hy
      have hy' := mem_Iic.1 hy
      exact ⟨(3 - y) ^ 2, mem_Ici.2 (sq_nonneg _), by
        show 3 - Real.sqrt ((3 - y) ^ 2) = y
        rw [Real.sqrt_sq (by linarith)]; ring⟩
  · rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]; norm_num

/-- Stitz-Zeager Example 1.7.3(1,2): `g(x) = 3√x` has range `[0,∞)` and passes through `(1,3)` and `(4,6)`;
`j(x) = √(9x)` has domain `[0,∞)`, range `[0,∞)` and passes through `(1/9,1)` and `(4/9,2)` (indeed `j = g`). -/
@[kb "stitzzeager2013" "Example 1.7.3, p. 144"]
theorem ex_1_7_3_a_g_and_j :
    ((fun x : ℝ => 3 * Real.sqrt x) '' Ici 0 = Ici 0) ∧
      ((fun x : ℝ => Real.sqrt (9 * x)) '' Ici 0 = Ici 0) ∧
      (3 * Real.sqrt 1 = 3 ∧ 3 * Real.sqrt 4 = 6) ∧
      (Real.sqrt (9 * (1 / 9)) = 1 ∧ Real.sqrt (9 * (4 / 9)) = 2) ∧
      (∀ x : ℝ, 0 ≤ x → Real.sqrt (9 * x) = 3 * Real.sqrt x) := by
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hj : ∀ x : ℝ, 0 ≤ x → Real.sqrt (9 * x) = 3 * Real.sqrt x := fun x hx => by
    rw [Real.sqrt_mul (by norm_num), show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  refine ⟨?_, ?_, ⟨by simp, by rw [h4]; norm_num⟩, ⟨by norm_num, ?_⟩, hj⟩
  · ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      have := Real.sqrt_nonneg x
      show 0 ≤ 3 * Real.sqrt x
      linarith
    · intro hy
      have hy' := mem_Ici.1 hy
      exact ⟨(y / 3) ^ 2, mem_Ici.2 (sq_nonneg _), by
        show 3 * Real.sqrt ((y / 3) ^ 2) = y
        rw [Real.sqrt_sq (by positivity)]; ring⟩
  · ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      exact Real.sqrt_nonneg _
    · intro hy
      have hy' := mem_Ici.1 hy
      refine ⟨(y / 3) ^ 2, mem_Ici.2 (sq_nonneg _), ?_⟩
      show Real.sqrt (9 * (y / 3) ^ 2) = y
      rw [hj _ (sq_nonneg _), Real.sqrt_sq (by positivity)]; ring
  · rw [show (9 : ℝ) * (4 / 9) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- Stitz-Zeager Example 1.7.3(3): `m(x) = 1 - √((x+3)/2)`, written `-f(x/2 + 3/2) + 1`, has domain `[-3,∞)` and
range `(-∞,1]`, and passes through `(-3,1)`, `(-1,0)`, `(5,-1)`. -/
@[kb "stitzzeager2013" "Example 1.7.3, p. 144"]
theorem ex_1_7_3_b_m :
    ({x : ℝ | 0 ≤ (x + 3) / 2} = Ici (-3)) ∧
      ((fun x : ℝ => 1 - Real.sqrt ((x + 3) / 2)) '' Ici (-3) = Iic 1) ∧
      (∀ x : ℝ, 1 - Real.sqrt ((x + 3) / 2) = -Real.sqrt (1 / 2 * x + 3 / 2) + 1) ∧
      (1 - Real.sqrt ((-3 + 3) / 2) = 1 ∧ 1 - Real.sqrt ((-1 + 3) / 2) = 0 ∧
        1 - Real.sqrt ((5 + 3) / 2) = -1) := by
  refine ⟨?_, ?_, fun x => ?_, by simp, by norm_num, ?_⟩
  · ext x; simp only [mem_ofPred_eq, mem_Ici]; constructor <;> intro h <;> linarith
  · ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      have := Real.sqrt_nonneg ((x + 3) / 2)
      exact (by linarith : 1 - Real.sqrt ((x + 3) / 2) ≤ 1)
    · intro hy
      have hy' := mem_Iic.1 hy
      refine ⟨2 * (1 - y) ^ 2 - 3, ?_, ?_⟩
      · simp only [mem_Ici]; nlinarith [sq_nonneg (1 - y)]
      · have : (2 * (1 - y) ^ 2 - 3 + 3) / 2 = (1 - y) ^ 2 := by ring
        show 1 - Real.sqrt ((2 * (1 - y) ^ 2 - 3 + 3) / 2) = y
        rw [this, Real.sqrt_sq (by linarith)]; ring
  · ring_nf
  · rw [show (5 : ℝ) + 3 = 8 by norm_num, show (8 : ℝ) / 2 = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
    norm_num

/-- Stitz-Zeager Example 1.7.4: if `f` has the key values `f(-4) = -3`, `f(-2) = 0`, `f(0) = 3`, `f(2) = 0`,
`f(4) = -3`, then `g(x) = (4 - 3 f(1-2x)) / 2 = -(3/2) f(-2x+1) + 2` has `g(5/2) = 13/2`, `g(3/2) = 2`,
`g(1/2) = -5/2`, `g(-1/2) = 2`, `g(-3/2) = 13/2`. -/
@[kb "stitzzeager2013" "Example 1.7.4, p. 148"]
theorem ex_1_7_4_key_points (f : ℝ → ℝ)
    (h₁ : f (-4) = -3) (h₂ : f (-2) = 0) (h₃ : f 0 = 3) (h₄ : f 2 = 0) (h₅ : f 4 = -3) :
    (∀ x : ℝ, (4 - 3 * f (1 - 2 * x)) / 2 = -(3 / 2) * f (-2 * x + 1) + 2) ∧
      (4 - 3 * f (1 - 2 * (5 / 2))) / 2 = 13 / 2 ∧ (4 - 3 * f (1 - 2 * (3 / 2))) / 2 = 2 ∧
      (4 - 3 * f (1 - 2 * (1 / 2))) / 2 = -5 / 2 ∧ (4 - 3 * f (1 - 2 * (-1 / 2))) / 2 = 2 ∧
      (4 - 3 * f (1 - 2 * (-3 / 2))) / 2 = 13 / 2 := by
  refine ⟨fun x => by rw [show -2 * x + 1 = 1 - 2 * x by ring]; ring, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 1 - 2 * (5 / 2 : ℝ) = -4 by norm_num, h₁]; norm_num
  · rw [show 1 - 2 * (3 / 2 : ℝ) = -2 by norm_num, h₂]; norm_num
  · rw [show 1 - 2 * (1 / 2 : ℝ) = 0 by norm_num, h₃]; norm_num
  · rw [show 1 - 2 * (-1 / 2 : ℝ) = 2 by norm_num, h₄]; norm_num
  · rw [show 1 - 2 * (-3 / 2 : ℝ) = 4 by norm_num, h₅]; norm_num

/-- Stitz-Zeager Example 1.7.5: applying to `f(x) = x²` the shift up `2`, the reflection across the x-axis, the shift
right `1` and the horizontal stretch by `2` gives `g(x) = -((x/2 - 1)² + 2) = -x²/4 + x - 3`, via the stages
`g₁ = x²+2`, `g₂ = -x²-2`, `g₃ = -x²+2x-3`. -/
@[kb "stitzzeager2013" "Example 1.7.5, p. 150"]
theorem ex_1_7_5_transformations :
    ∃ g₁ g₂ g₃ g : ℝ → ℝ,
      (∀ x, g₁ x = x ^ 2 + 2) ∧ (∀ x, g₂ x = -g₁ x) ∧ (∀ x, g₂ x = -x ^ 2 - 2) ∧
      (∀ x, g₃ x = g₂ (x - 1)) ∧ (∀ x, g₃ x = -x ^ 2 + 2 * x - 3) ∧
      (∀ x, g x = g₃ (1 / 2 * x)) ∧ (∀ x, g x = -(1 / 4) * x ^ 2 + x - 3) := by
  refine ⟨fun x => x ^ 2 + 2, fun x => -(x ^ 2 + 2), fun x => -((x - 1) ^ 2 + 2),
    fun x => -((1 / 2 * x - 1) ^ 2 + 2), fun x => rfl, fun x => rfl, fun x => by ring,
    fun x => rfl, fun x => by ring, fun x => by ring_nf, fun x => by ring⟩

end UndergradKB.Precalculus.Course
