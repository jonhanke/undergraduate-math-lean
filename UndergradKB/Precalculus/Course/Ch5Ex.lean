import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Sqrt
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.InverseFunctions
import UndergradKB.Precalculus.Radicals

/-! # Course layer, Chapter 5 (Stitz-Zeager): worked examples -/

namespace UndergradKB.Precalculus.Course

open Set Filter Topology Real UndergradKB.Precalculus

/-! ## Section 5.1 -/

/-- Stitz-Zeager Example 5.1.1(1): for `f(x) = x²-4x`, `g(x) = 2 - √(x+3)`, we have `(g ∘ f)(1) = 2`. -/
@[kb "stitzzeager2013" "Example 5.1.1, p. 372"]
theorem ex_5_1_1_a :
    ((fun x : ℝ => 2 - √(x + 3)) ∘ (fun x : ℝ => x ^ 2 - 4 * x)) 1 = 2 := by
  simp only [Function.comp]
  have : √((1 : ℝ) ^ 2 - 4 * 1 + 3) = 0 := by norm_num
  linarith

/-- Stitz-Zeager Example 5.1.1(2): `(f ∘ g)(1) = 0`. -/
@[kb "stitzzeager2013" "Example 5.1.1, p. 372"]
theorem ex_5_1_1_b :
    ((fun x : ℝ => x ^ 2 - 4 * x) ∘ (fun x : ℝ => 2 - √(x + 3))) 1 = 0 := by
  simp only [Function.comp]
  have : √((1 : ℝ) + 3) = 2 := by
    rw [show (1 : ℝ) + 3 = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [this]; norm_num

/-- Stitz-Zeager Example 5.1.1(3): `(g ∘ g)(6) = 2 - √2`. -/
@[kb "stitzzeager2013" "Example 5.1.1, p. 372"]
theorem ex_5_1_1_c :
    ((fun x : ℝ => 2 - √(x + 3)) ∘ (fun x : ℝ => 2 - √(x + 3))) 6 = 2 - √2 := by
  simp only [Function.comp]
  have : √((6 : ℝ) + 3) = 3 := by
    rw [show (6 : ℝ) + 3 = 3 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [this]; norm_num

/-- Stitz-Zeager Example 5.1.1(4): `(g ∘ f)(x) = 2 - √(x²-4x+3)`, defined exactly for `x ≤ 1` or `x ≥ 3`. -/
@[kb "stitzzeager2013" "Example 5.1.1, p. 372"]
theorem ex_5_1_1_d :
    (∀ x : ℝ, ((fun x : ℝ => 2 - √(x + 3)) ∘ (fun x : ℝ => x ^ 2 - 4 * x)) x = 2 - √(x ^ 2 - 4 * x + 3)) ∧
    {x : ℝ | 0 ≤ x ^ 2 - 4 * x + 3} = Iic 1 ∪ Ici 3 := by
  refine ⟨fun x => rfl, ?_⟩
  ext x
  simp only [mem_setOf_eq, mem_union, mem_Iic, mem_Ici]
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    nlinarith [hc.1, hc.2]
  · rintro (h | h) <;> nlinarith

/-- Stitz-Zeager Example 5.1.1(5): `(f ∘ g)(x) = x - 1` for `x ≥ -3`, the domain of `g`. -/
@[kb "stitzzeager2013" "Example 5.1.1, p. 372"]
theorem ex_5_1_1_e (x : ℝ) (hx : -3 ≤ x) :
    ((fun x : ℝ => x ^ 2 - 4 * x) ∘ (fun x : ℝ => 2 - √(x + 3))) x = x - 1 := by
  simp only [Function.comp]
  have h := Real.sq_sqrt (show 0 ≤ x + 3 by linarith)
  nlinarith

/-- Stitz-Zeager Example 5.1.1(6): for `h(x) = 2x/(x+1)`, `(g ∘ h)(x) = 2 - √((5x+3)/(x+1))`, whose domain is
`(-∞, -1) ∪ [-3/5, ∞)`. -/
@[kb "stitzzeager2013" "Example 5.1.1, p. 372"]
theorem ex_5_1_1_f :
    (∀ x : ℝ, x ≠ -1 → ((fun x : ℝ => 2 - √(x + 3)) ∘ (fun x : ℝ => 2 * x / (x + 1))) x =
      2 - √((5 * x + 3) / (x + 1))) ∧
    {x : ℝ | x ≠ -1 ∧ 0 ≤ 2 * x / (x + 1) + 3} = Iio (-1) ∪ Ici (-3 / 5) := by
  have key : ∀ x : ℝ, x ≠ -1 → 2 * x / (x + 1) + 3 = (5 * x + 3) / (x + 1) := by
    intro x hx
    have : x + 1 ≠ 0 := fun h => hx (by linarith)
    field_simp
    ring
  refine ⟨fun x hx => ?_, ?_⟩
  · simp only [Function.comp]
    rw [key x hx]
  · ext x
    simp only [mem_setOf_eq, mem_union, mem_Iio, mem_Ici]
    constructor
    · rintro ⟨hx, h⟩
      rw [key x hx, div_nonneg_iff] at h
      rcases h with h | h
      · right; linarith [h.1, h.2]
      · left; exact lt_of_le_of_ne (by linarith [h.2]) hx
    · rintro (h | h)
      · refine ⟨by linarith, ?_⟩
        rw [key x (by linarith), div_nonneg_iff]
        right; constructor <;> linarith
      · have hx : x ≠ -1 := by
          intro h1
          rw [h1] at h
          norm_num at h
        refine ⟨hx, ?_⟩
        rw [key x hx, div_nonneg_iff]
        by_cases h1 : x < -1
        · right; constructor <;> linarith
        · left; constructor <;> linarith [lt_of_le_of_ne (not_lt.mp h1) (Ne.symm hx)]

/-- Stitz-Zeager Example 5.1.1(7): for `x ≥ -3`, `x ≠ 6`, `(h ∘ g)(x) = (4 - 2√(x+3))/(3 - √(x+3))`; the
domain of `h ∘ g` is `[-3, 6) ∪ (6, ∞)`. -/
@[kb "stitzzeager2013" "Example 5.1.1, p. 372"]
theorem ex_5_1_1_g :
    (∀ x : ℝ, -3 ≤ x → x ≠ 6 → ((fun x : ℝ => 2 * x / (x + 1)) ∘ (fun x : ℝ => 2 - √(x + 3))) x =
      (4 - 2 * √(x + 3)) / (3 - √(x + 3))) ∧
    {x : ℝ | -3 ≤ x ∧ 2 - √(x + 3) + 1 ≠ 0} = Ico (-3) 6 ∪ Ioi 6 := by
  refine ⟨fun x hx h6 => ?_, ?_⟩
  · simp only [Function.comp]
    congr 1 <;> ring
  · ext x
    simp only [mem_setOf_eq, mem_union, mem_Ico, mem_Ioi]
    constructor
    · rintro ⟨hx, h⟩
      have hne : x ≠ 6 := by
        rintro rfl
        apply h
        have : √((6 : ℝ) + 3) = 3 := by
          rw [show (6 : ℝ) + 3 = 3 ^ 2 by norm_num]
          exact Real.sqrt_sq (by norm_num)
        rw [this]; norm_num
      rcases lt_or_gt_of_ne hne with h6 | h6
      · left; exact ⟨hx, h6⟩
      · right; exact h6
    · intro h
      have hx : -3 ≤ x := by
        rcases h with h | h
        · exact h.1
        · linarith
      refine ⟨hx, ?_⟩
      intro h0
      have h3 : √(x + 3) = 3 := by linarith
      have : x + 3 = 9 := by
        have := Real.sq_sqrt (show 0 ≤ x + 3 by linarith)
        rw [h3] at this; linarith
      rcases h with h | h
      · linarith [h.2]
      · linarith

/-- Stitz-Zeager Example 5.1.1(8): for `h(x) = 2x/(x+1)`, `(h ∘ h)(x) = 4x/(3x+1)` for `x ≠ -1, -1/3`. -/
@[kb "stitzzeager2013" "Example 5.1.1, p. 372"]
theorem ex_5_1_1_h (x : ℝ) (h1 : x ≠ -1) (h2 : x ≠ -1 / 3) :
    ((fun x : ℝ => 2 * x / (x + 1)) ∘ (fun x : ℝ => 2 * x / (x + 1))) x = 4 * x / (3 * x + 1) := by
  simp only [Function.comp]
  have ha : x + 1 ≠ 0 := fun h => h1 (by linarith)
  have hb : 3 * x + 1 ≠ 0 := fun h => h2 (by linarith)
  have hc : 2 * x / (x + 1) + 1 = (3 * x + 1) / (x + 1) := by
    field_simp
    ring
  rw [hc]
  field_simp
  ring

/-- Stitz-Zeager Example 5.1.2: the sphere's area `S(r) = 4πr²` with radius `r(t) = 3t²` gives
`(S ∘ r)(t) = 36π t⁴`. -/
@[kb "stitzzeager2013" "Example 5.1.2, p. 379"]
theorem ex_5_1_2 :
    ((fun r : ℝ => 4 * π * r ^ 2) ∘ (fun t : ℝ => 3 * t ^ 2)) = fun t => 36 * π * t ^ 4 := by
  funext t
  simp only [Function.comp]
  ring

/-- Stitz-Zeager Example 5.1.3(1): `F(x) = |3x - 1|` is the composite of `x ↦ |x|` with `x ↦ 3x - 1`. -/
@[kb "stitzzeager2013" "Example 5.1.3, p. 379"]
theorem ex_5_1_3_a : (fun x : ℝ => |3 * x - 1|) = (fun u : ℝ => |u|) ∘ (fun x : ℝ => 3 * x - 1) := rfl

/-- Stitz-Zeager Example 5.1.3(2): `G(x) = 2/(x²+1)` is the composite `h ∘ g ∘ f` of squaring, adding one, and
dividing into `2`. -/
@[kb "stitzzeager2013" "Example 5.1.3, p. 379"]
theorem ex_5_1_3_b : (fun x : ℝ => 2 / (x ^ 2 + 1)) =
    (fun u : ℝ => 2 / u) ∘ (fun u : ℝ => u + 1) ∘ (fun x : ℝ => x ^ 2) := rfl

/-- Stitz-Zeager Example 5.1.3(3): `H(x) = (√x + 1)/(√x - 1)` is the composite of `x ↦ (x+1)/(x-1)` with
the square root. -/
@[kb "stitzzeager2013" "Example 5.1.3, p. 379"]
theorem ex_5_1_3_c : (fun x : ℝ => (√x + 1) / (√x - 1)) =
    (fun u : ℝ => (u + 1) / (u - 1)) ∘ (fun x : ℝ => √x) := rfl

/-! ## Section 5.2 -/

/-- Stitz-Zeager Example 5.2.1(1): `f(x) = (1 - 2x)/5` is one-to-one. -/
@[kb "stitzzeager2013" "Example 5.2.1, p. 394"]
theorem ex_5_2_1_a : Function.Injective (fun x : ℝ => (1 - 2 * x) / 5) := by
  intro c d h
  simp only at h
  linarith

/-- Stitz-Zeager Example 5.2.1(2): `g(x) = 2x/(1-x)` is one-to-one on its domain `x ≠ 1`. -/
@[kb "stitzzeager2013" "Example 5.2.1, p. 394"]
theorem ex_5_2_1_b : InjOn (fun x : ℝ => 2 * x / (1 - x)) {x | x ≠ 1} := by
  intro c hc d hd h
  simp only [mem_setOf_eq] at hc hd h
  have h1 : 1 - c ≠ 0 := fun h => hc (by linarith)
  have h2 : 1 - d ≠ 0 := fun h => hd (by linarith)
  rw [div_eq_div_iff h1 h2] at h
  linarith

/-- Stitz-Zeager Example 5.2.1(3): `h(x) = x² - 2x + 4` is not one-to-one, since `h(0) = h(2) = 4`. -/
@[kb "stitzzeager2013" "Example 5.2.1, p. 394"]
theorem ex_5_2_1_c : ¬ Function.Injective (fun x : ℝ => x ^ 2 - 2 * x + 4) := by
  intro h
  have := @h 0 2 (by norm_num)
  norm_num at this

/-- Stitz-Zeager Example 5.2.2(1): the inverse of `f(x) = (1 - 2x)/5` is `f⁻¹(x) = -5x/2 + 1/2`, on all of `ℝ`. -/
@[kb "stitzzeager2013" "Example 5.2.2, p. 396"]
theorem ex_5_2_2_a :
    InverseOn (fun x : ℝ => (1 - 2 * x) / 5) (fun x : ℝ => -5 / 2 * x + 1 / 2) univ univ := by
  refine ⟨fun x _ => ⟨mem_univ _, ?_⟩, fun y _ => ⟨mem_univ _, ?_⟩⟩ <;> ring

/-- Stitz-Zeager Example 5.2.2(2): the inverse of `g(x) = 2x/(1-x)` (domain `x ≠ 1`, range `y ≠ -2`) is
`g⁻¹(x) = x/(x+2)`. -/
@[kb "stitzzeager2013" "Example 5.2.2, p. 396"]
theorem ex_5_2_2_b :
    InverseOn (fun x : ℝ => 2 * x / (1 - x)) (fun x : ℝ => x / (x + 2)) {x | x ≠ 1} {y | y ≠ -2} := by
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · simp only [mem_setOf_eq] at hx ⊢
    have h1 : 1 - x ≠ 0 := fun h => hx (by linarith)
    have h2 : 2 * x / (1 - x) + 2 = 2 / (1 - x) := by
      field_simp
      ring
    refine ⟨?_, ?_⟩
    · intro h
      have : 2 * x = -2 * (1 - x) := by
        field_simp at h; linarith
      linarith
    · rw [h2]
      field_simp
  · simp only [mem_setOf_eq] at hy ⊢
    have h1 : y + 2 ≠ 0 := fun h => hy (by linarith)
    have h2 : 1 - y / (y + 2) = 2 / (y + 2) := by
      field_simp
      ring
    refine ⟨?_, ?_⟩
    · intro h
      have : y = y + 2 := by field_simp at h; linarith
      linarith
    · rw [h2]
      field_simp

/-- Stitz-Zeager Example 5.2.3(1): on `x ≤ 1`, `j(x) = x² - 2x + 4` has range `[3, ∞)` and inverse
`j⁻¹(x) = 1 - √(x-3)`. -/
@[kb "stitzzeager2013" "Example 5.2.3, p. 401"]
theorem ex_5_2_3_a :
    InverseOn (fun x : ℝ => x ^ 2 - 2 * x + 4) (fun x : ℝ => 1 - √(x - 3)) (Iic 1) (Ici 3) := by
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · simp only [mem_Iic, mem_Ici] at hx ⊢
    refine ⟨by nlinarith, ?_⟩
    have : x ^ 2 - 2 * x + 4 - 3 = (1 - x) ^ 2 := by ring
    rw [this, Real.sqrt_sq (by linarith)]
    ring
  · simp only [mem_Iic, mem_Ici] at hy ⊢
    have h := Real.sq_sqrt (show 0 ≤ y - 3 by linarith)
    have h0 := Real.sqrt_nonneg (y - 3)
    refine ⟨by linarith, ?_⟩
    nlinarith

/-- Stitz-Zeager Example 5.2.3(2): `k(x) = √(x+2) - 1` (domain `[-2, ∞)`, range `[-1, ∞)`) has inverse
`k⁻¹(x) = x² + 2x - 1` on `x ≥ -1`. -/
@[kb "stitzzeager2013" "Example 5.2.3, p. 401"]
theorem ex_5_2_3_b :
    InverseOn (fun x : ℝ => √(x + 2) - 1) (fun x : ℝ => x ^ 2 + 2 * x - 1) (Ici (-2)) (Ici (-1)) := by
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · simp only [mem_Ici] at hx ⊢
    have h := Real.sq_sqrt (show 0 ≤ x + 2 by linarith)
    have h0 := Real.sqrt_nonneg (x + 2)
    refine ⟨by linarith, ?_⟩
    nlinarith
  · simp only [mem_Ici] at hy ⊢
    refine ⟨by nlinarith, ?_⟩
    have : y ^ 2 + 2 * y - 1 + 2 = (y + 1) ^ 2 := by ring
    rw [this, Real.sqrt_sq (by linarith)]
    ring

/-- Stitz-Zeager Example 5.2.4(1): the price-demand function `p(x) = -1.5x + 250` on `[0, 166]` has range
`[1, 250]` and inverse `p⁻¹(x) = (500 - 2x)/3`. -/
@[kb "stitzzeager2013" "Example 5.2.4, p. 404"]
theorem ex_5_2_4_a :
    InverseOn (fun x : ℝ => -(3 / 2) * x + 250) (fun x : ℝ => (500 - 2 * x) / 3) (Icc 0 166) (Icc 1 250) := by
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · simp only [mem_Icc] at hx ⊢
    refine ⟨⟨by linarith, by linarith⟩, by ring⟩
  · simp only [mem_Icc] at hy ⊢
    refine ⟨⟨by linarith, by linarith⟩, by ring⟩

/-- Stitz-Zeager Example 5.2.4(2): `p⁻¹(220) = 20`. -/
@[kb "stitzzeager2013" "Example 5.2.4, p. 404"]
theorem ex_5_2_4_b : (fun x : ℝ => (500 - 2 * x) / 3) 220 = 20 := by norm_num

/-- Stitz-Zeager Example 5.2.4(3): the profit `P(x) = -1.5x² + 170x - 150` composed with `p⁻¹` is
`-(2/3)x² + 220x - 40450/3`. -/
@[kb "stitzzeager2013" "Example 5.2.4, p. 404"]
theorem ex_5_2_4_c :
    ((fun x : ℝ => -(3 / 2) * x ^ 2 + 170 * x - 150) ∘ (fun x : ℝ => (500 - 2 * x) / 3)) =
      fun x => -(2 / 3) * x ^ 2 + 220 * x - 40450 / 3 := by
  funext x
  simp only [Function.comp]
  ring

/-- Stitz-Zeager Example 5.2.4(4): the profit as a function of price, `-(2/3)x² + 220x - 40450/3`, is largest at
the price `x = 165`. -/
@[kb "stitzzeager2013" "Example 5.2.4, p. 404"]
theorem ex_5_2_4_d (x : ℝ) :
    -(2 / 3) * x ^ 2 + 220 * x - 40450 / 3 ≤ -(2 / 3) * 165 ^ 2 + 220 * 165 - 40450 / 3 := by
  nlinarith [sq_nonneg (x - 165)]

/-! ## Section 5.3 -/

/-- Stitz-Zeager Example 5.3.1(1): `f(x) = 3x·∛(2-x)` is defined on all of `ℝ`, vanishes exactly at `0` and `2`,
and is positive exactly on `(0, 2)`. -/
@[kb "stitzzeager2013" "Example 5.3.1, p. 411"]
theorem ex_5_3_1_a :
    (∀ x : ℝ, 3 * x * principalRoot 3 (2 - x) = 0 ↔ x = 0 ∨ x = 2) ∧
    (∀ x : ℝ, 0 < 3 * x * principalRoot 3 (2 - x) ↔ 0 < x ∧ x < 2) := by
  have hodd : Odd 3 := by decide
  have hr : ∀ x : ℝ, (principalRoot 3 (2 - x)) ^ 3 = 2 - x := fun x =>
    ((principalRoot_eq_iff_odd hodd (2 - x) _).mp rfl)
  refine ⟨fun x => ?_, fun x => ?_⟩
  · rw [mul_eq_zero, mul_eq_zero]
    constructor
    · rintro ((h | h) | h)
      · norm_num at h
      · left; exact h
      · right
        have := hr x
        rw [h] at this
        linarith
    · rintro (h | h)
      · left; right; exact h
      · right
        have : principalRoot 3 (2 - x) = principalRoot 3 0 := by rw [h]; norm_num
        rw [this]
        exact (principalRoot_eq_iff_odd hodd 0 0).mpr (by norm_num) |>.symm
  · have hp := Odd.pow_pos_iff (a := principalRoot 3 (2 - x)) hodd
    have hn := Odd.pow_neg_iff (a := principalRoot 3 (2 - x)) hodd
    rw [hr x] at hp hn
    rw [mul_pos_iff]
    constructor
    · rintro (⟨a, b⟩ | ⟨a, b⟩)
      · exact ⟨by linarith, by linarith [hp.mpr b]⟩
      · have := hn.mpr b
        linarith
    · rintro ⟨a, b⟩
      left
      exact ⟨by linarith, hp.mp (by linarith)⟩

/-- Stitz-Zeager Example 5.3.1(2): the domain of `g(x) = √(2 - ⁴√(x+3))` is `[-3, 13]`, and `g` vanishes there
only at `x = 13`. -/
@[kb "stitzzeager2013" "Example 5.3.1, p. 411"]
theorem ex_5_3_1_b :
    {x : ℝ | 0 ≤ x + 3 ∧ 0 ≤ 2 - (x + 3) ^ ((1 : ℝ) / 4)} = Icc (-3) 13 ∧
    ∀ x ∈ Icc (-3 : ℝ) 13, √(2 - (x + 3) ^ ((1 : ℝ) / 4)) = 0 ↔ x = 13 := by
  have h4 : ∀ y : ℝ, 0 ≤ y → (y ^ ((1 : ℝ) / 4)) ^ 4 = y := by
    intro y hy
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy]
    norm_num
  have hdom : ∀ x : ℝ, 0 ≤ x + 3 → (0 ≤ 2 - (x + 3) ^ ((1 : ℝ) / 4) ↔ x ≤ 13) := by
    intro x hx
    have ht := Real.rpow_nonneg hx ((1 : ℝ) / 4)
    have he := h4 _ hx
    set t := (x + 3) ^ ((1 : ℝ) / 4)
    constructor
    · intro h
      have : t ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ ht (by linarith) 4
      linarith
    · intro h
      by_contra hc
      push_neg at hc
      have : (2 : ℝ) ^ 4 < t ^ 4 := pow_lt_pow_left₀ (by linarith) (by norm_num) (by norm_num)
      linarith
  refine ⟨?_, fun x hx => ?_⟩
  · ext x
    simp only [mem_setOf_eq, mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, (hdom x h1).mp h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, (hdom x (by linarith)).mpr h2⟩
  · obtain ⟨h1, h2⟩ := hx
    have hx0 : 0 ≤ x + 3 := by linarith
    have hnn := (hdom x hx0).mpr h2
    have ht := Real.rpow_nonneg hx0 ((1 : ℝ) / 4)
    have he := h4 _ hx0
    set t := (x + 3) ^ ((1 : ℝ) / 4)
    rw [Real.sqrt_eq_zero hnn]
    constructor
    · intro h
      have : t = 2 := by linarith
      rw [this] at he
      linarith
    · intro h
      have : t ^ 4 = 2 ^ 4 := by rw [he]; linarith
      have := (pow_left_inj₀ ht (by norm_num) (by norm_num)).mp this
      linarith

/-- Stitz-Zeager Example 5.3.1(3): `h(x) = ∛(8x/(x+1))` (for `x ≠ -1`) vanishes exactly at `x = 0`. -/
@[kb "stitzzeager2013" "Example 5.3.1, p. 411"]
theorem ex_5_3_1_c (x : ℝ) (hx : x ≠ -1) : principalRoot 3 (8 * x / (x + 1)) = 0 ↔ x = 0 := by
  have hodd : Odd 3 := by decide
  have h1 : x + 1 ≠ 0 := fun h => hx (by linarith)
  rw [eq_comm, principalRoot_eq_iff_odd hodd]
  constructor
  · intro h
    have : 8 * x / (x + 1) = 0 := by rw [← h]; norm_num
    rcases div_eq_zero_iff.mp this with h | h
    · linarith
    · exact absurd h h1
  · rintro rfl; norm_num

/-- Stitz-Zeager Example 5.3.1(4): `k(x) = 2x/√(x²-1)` is defined exactly for `x < -1` or `x > 1`, has no zero
there, and tends to `2` as `x → ∞` and to `-2` as `x → -∞` (two horizontal asymptotes). -/
@[kb "stitzzeager2013" "Example 5.3.1, p. 411"]
theorem ex_5_3_1_d :
    {x : ℝ | 0 < x ^ 2 - 1} = Iio (-1) ∪ Ioi 1 ∧
    (∀ x : ℝ, 0 < x ^ 2 - 1 → 2 * x / √(x ^ 2 - 1) ≠ 0) ∧
    Tendsto (fun x : ℝ => 2 * x / √(x ^ 2 - 1)) atTop (𝓝 2) ∧
    Tendsto (fun x : ℝ => 2 * x / √(x ^ 2 - 1)) atBot (𝓝 (-2)) := by
  refine ⟨?_, fun x hx => ?_, ?_, ?_⟩
  · ext x
    simp only [mem_setOf_eq, mem_union, mem_Iio, mem_Ioi]
    constructor
    · intro h
      by_contra hc
      push_neg at hc
      nlinarith [hc.1, hc.2]
    · rintro (h | h) <;> nlinarith
  · have hs : 0 < √(x ^ 2 - 1) := Real.sqrt_pos.mpr hx
    have : x ≠ 0 := by
      rintro rfl
      norm_num at hx
    exact div_ne_zero (mul_ne_zero (by norm_num) this) hs.ne'
  · have hlim : Tendsto (fun x : ℝ => 2 / √(1 - (x⁻¹) ^ 2)) atTop (𝓝 2) := by
      have h1 : Tendsto (fun x : ℝ => 1 - (x⁻¹) ^ 2) atTop (𝓝 1) := by
        have := (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_inv_atTop_zero.pow 2)
        simpa using this
      have := (tendsto_const_nhds (x := (2 : ℝ))).div h1.sqrt (by simp)
      rwa [Real.sqrt_one, div_one] at this
    refine hlim.congr' ((eventually_gt_atTop 1).mono fun x hx => ?_)
    have hx0 : 0 < x := by linarith
    have h1 : 0 < x ^ 2 - 1 := by nlinarith
    have e : 1 - (x⁻¹) ^ 2 = (x ^ 2 - 1) / x ^ 2 := by field_simp
    rw [e, Real.sqrt_div h1.le, Real.sqrt_sq hx0.le]
    have hs : 0 < √(x ^ 2 - 1) := Real.sqrt_pos.mpr h1
    field_simp
  · have hlim : Tendsto (fun x : ℝ => -(2 / √(1 - (x⁻¹) ^ 2))) atBot (𝓝 (-2)) := by
      have h1 : Tendsto (fun x : ℝ => 1 - (x⁻¹) ^ 2) atBot (𝓝 1) := by
        have := (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_inv_atBot_zero.pow 2)
        simpa using this
      have := ((tendsto_const_nhds (x := (2 : ℝ))).div h1.sqrt (by simp)).neg
      rwa [Real.sqrt_one, div_one] at this
    refine hlim.congr' ((eventually_lt_atBot (-1)).mono fun x hx => ?_)
    have hx0 : x < 0 := by linarith
    have h1 : 0 < x ^ 2 - 1 := by nlinarith
    have hxne : x ≠ 0 := hx0.ne
    have e : 1 - (x⁻¹) ^ 2 = (x ^ 2 - 1) / x ^ 2 := by field_simp
    rw [e, Real.sqrt_div h1.le, Real.sqrt_sq_eq_abs, abs_of_neg hx0]
    have hs : 0 < √(x ^ 2 - 1) := Real.sqrt_pos.mpr h1
    field_simp

/-- Stitz-Zeager Example 5.3.2(1): with `∛x²` written `(∛x)²`, the inequality `x^(2/3) < x^(4/3) - 6` holds
exactly for `x < -3√3` or `x > 3√3`. -/
@[kb "stitzzeager2013" "Example 5.3.2, p. 414"]
theorem ex_5_3_2_a :
    {x : ℝ | (principalRoot 3 x) ^ 2 < (principalRoot 3 x) ^ 4 - 6} = Iio (-(3 * √3)) ∪ Ioi (3 * √3) := by
  have hodd : Odd 3 := by decide
  ext x
  simp only [mem_setOf_eq, mem_union, mem_Iio, mem_Ioi]
  set r := principalRoot 3 x with hr
  have hr3 : r ^ 3 = x := (principalRoot_eq_iff_odd hodd x r).mp rfl
  have hs : (3 * √3) ^ 2 = 27 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hs0 : 0 < 3 * √3 := by positivity
  have h1 : (r ^ 2) ^ 2 - r ^ 2 - 6 = (r ^ 2 - 3) * (r ^ 2 + 2) := by ring
  have key : r ^ 2 < r ^ 4 - 6 ↔ 3 < r ^ 2 := by
    constructor
    · intro h
      by_contra hc
      push_neg at hc
      nlinarith [sq_nonneg r]
    · intro h; nlinarith [sq_nonneg r]
  rw [key]
  have hx2 : x ^ 2 = (r ^ 2) ^ 3 := by rw [← hr3]; ring
  have : 3 < r ^ 2 ↔ 27 < x ^ 2 := by
    rw [hx2]
    constructor
    · intro h; nlinarith [sq_nonneg r]
    · intro h
      by_contra hc
      push_neg at hc
      have : (r ^ 2) ^ 3 ≤ 3 ^ 3 := pow_le_pow_left₀ (sq_nonneg r) hc 3
      linarith
  rw [this, ← hs, sq_lt_sq, abs_of_pos hs0, lt_abs]
  constructor
  · rintro (h | h)
    · right; exact h
    · left; linarith
  · rintro (h | h)
    · right; linarith
    · left; exact h

/-- Stitz-Zeager Example 5.3.2(2): for `x ≠ 2`, `3(2-x)^(1/3) ≤ x(2-x)^(-2/3)` holds exactly when `x ≥ 3/2`
(here `(2-x)^(1/3)` is `∛(2-x)` and `(2-x)^(-2/3)` is its reciprocal square). -/
@[kb "stitzzeager2013" "Example 5.3.2, p. 414"]
theorem ex_5_3_2_b (x : ℝ) (hx : x ≠ 2) :
    3 * principalRoot 3 (2 - x) ≤ x * ((principalRoot 3 (2 - x)) ^ 2)⁻¹ ↔ 3 / 2 ≤ x := by
  have hodd : Odd 3 := by decide
  set c := principalRoot 3 (2 - x) with hc
  have hc3 : c ^ 3 = 2 - x := (principalRoot_eq_iff_odd hodd (2 - x) c).mp rfl
  have hc0 : c ≠ 0 := by
    intro h
    rw [h] at hc3
    apply hx
    linarith
  have hc2 : 0 < c ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hc2]
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

end UndergradKB.Precalculus.Course
