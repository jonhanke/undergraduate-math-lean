import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Interval.Set.Basic
import UndergradKB.Precalculus.Radicals
import UndergradKB.Precalculus.RationalExponents
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 5 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 5.3 (inequalities) -/

namespace UndergradKB.Precalculus.Course

open Set UndergradKB.Precalculus

private theorem x5w7g_cube_pos (y : ℝ) : 0 < principalRoot 3 y ↔ 0 < y := by
  have h := principalRoot_pow (n := 3) (x := y) (by norm_num) (Or.inl (by decide))
  constructor
  · intro hr; rw [← h]; exact pow_pos hr 3
  · intro hy; by_contra hc
    have : principalRoot 3 y ≤ 0 := not_lt.1 hc
    have : principalRoot 3 y ^ 3 ≤ 0 := Odd.pow_nonpos (by decide) this
    linarith

private theorem x5w7g_cube_neg (y : ℝ) : principalRoot 3 y < 0 ↔ y < 0 := by
  have h := principalRoot_pow (n := 3) (x := y) (by norm_num) (Or.inl (by decide))
  constructor
  · intro hr; rw [← h]; exact Odd.pow_neg (by decide) hr
  · intro hy; by_contra hc
    have : 0 ≤ principalRoot 3 y := not_lt.1 hc
    have : 0 ≤ principalRoot 3 y ^ 3 := pow_nonneg this 3
    linarith

private theorem x5w7g_cube_ne (y : ℝ) (hy : y ≠ 0) : principalRoot 3 y ≠ 0 := by
  intro h
  have := principalRoot_pow (n := 3) (x := y) (by norm_num) (Or.inl (by decide))
  rw [h] at this; apply hy; rw [← this]; norm_num

/-- Stitz-Zeager Exercise 5.3.29: `2(x-2)^(-1/3) - (2/3) x (x-2)^(-4/3) ≤ 0` (book's powers) has solution set
`(-∞, 2) ∪ (2, 3]`. -/
@[kb "stitzzeager2013" "Exercise 5.3.29, p. 420"]
theorem exer_5_3_29 :
    {x : ℝ | x - 2 ≠ 0 ∧
      2 * bookRatPow (x - 2) (-1) 3 - 2 / 3 * x * bookRatPow (x - 2) (-4) 3 ≤ 0} = Iio 2 ∪ Ioc 2 3 := by
  have L : ∀ x : ℝ, x - 2 ≠ 0 → 2 * bookRatPow (x - 2) (-1) 3 - 2 / 3 * x * bookRatPow (x - 2) (-4) 3 =
      (x - 3) * (4 / (3 * principalRoot 3 (x - 2) ^ 4)) := by
    intro x hx
    have hr := principalRoot_pow (n := 3) (x := x - 2) (by norm_num) (Or.inl (by decide))
    have hr0 := x5w7g_cube_ne _ hx
    simp only [bookRatPow, zpow_neg, zpow_ofNat]
    generalize principalRoot 3 (x - 2) = r at hr hr0 ⊢
    have hx' : x = r ^ 3 + 2 := by linarith
    subst hx'
    field_simp
    ring
  have K : ∀ x : ℝ, x - 2 ≠ 0 → 0 < 4 / (3 * principalRoot 3 (x - 2) ^ 4) := by
    intro x hx
    have := x5w7g_cube_ne _ hx
    positivity
  ext x; simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ioc]
  constructor
  · rintro ⟨hx, h⟩
    rw [L x hx] at h
    have h3 : x - 3 ≤ 0 := by
      by_contra hc; push Not at hc; linarith [mul_pos hc (K x hx)]
    rcases lt_or_gt_of_ne hx with h' | h'
    · left; linarith
    · right; exact ⟨by linarith, by linarith⟩
  · intro h
    have hx : x - 2 ≠ 0 := by rcases h with h | h <;> [exact (by linarith : x - 2 < 0).ne; exact (by linarith [h.1] : 0 < x - 2).ne']
    refine ⟨hx, ?_⟩
    rw [L x hx]
    have h3 : x - 3 ≤ 0 := by
      rcases h with h | h
      · linarith
      · linarith [h.2]
    exact mul_nonpos_of_nonpos_of_nonneg h3 (K x hx).le

/-- Stitz-Zeager Exercise 5.3.31: `2x^(-1/3)(x-3)^(1/3) + x^(2/3)(x-3)^(-2/3) ≥ 0` (book's powers) has solution
set `(-∞, 0) ∪ [2, 3) ∪ (3, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 5.3.31, p. 420"]
theorem exer_5_3_31 :
    {x : ℝ | x ≠ 0 ∧ x - 3 ≠ 0 ∧
      0 ≤ 2 * bookRatPow x (-1) 3 * bookRatPow (x - 3) 1 3 +
        bookRatPow x 2 3 * bookRatPow (x - 3) (-2) 3} = Iio 0 ∪ Ico 2 3 ∪ Ioi 3 := by
  have h3 : Odd 3 := by decide
  have L : ∀ x : ℝ, x ≠ 0 → x - 3 ≠ 0 →
      2 * bookRatPow x (-1) 3 * bookRatPow (x - 3) 1 3 + bookRatPow x 2 3 * bookRatPow (x - 3) (-2) 3 =
      3 * (x - 2) / (principalRoot 3 x * principalRoot 3 (x - 3) ^ 2) := by
    intro x hx hx3
    have ha := principalRoot_pow (n := 3) (x := x) (by norm_num) (Or.inl h3)
    have hb := principalRoot_pow (n := 3) (x := x - 3) (by norm_num) (Or.inl h3)
    have ha0 := x5w7g_cube_ne _ hx
    have hb0 := x5w7g_cube_ne _ hx3
    simp only [bookRatPow, zpow_neg, zpow_ofNat, pow_one]
    generalize principalRoot 3 x = a at ha ha0 ⊢
    generalize principalRoot 3 (x - 3) = b at hb hb0 ⊢
    have e : 2 * a⁻¹ * b + a ^ 2 * (b ^ 2)⁻¹ = (2 * b ^ 3 + a ^ 3) / (a * b ^ 2) := by
      field_simp
    rw [e, hb, ha]; ring_nf
  ext x
  simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ico, mem_Ioi]
  have hb2 : ∀ x : ℝ, x - 3 ≠ 0 → 0 < principalRoot 3 (x - 3) ^ 2 := by
    intro x hx3
    have := x5w7g_cube_ne _ hx3
    positivity
  constructor
  · rintro ⟨hx, hx3, h⟩
    rw [L x hx hx3] at h
    rcases lt_or_gt_of_ne hx with hneg | hpos
    · left; left; exact hneg
    · have ha : 0 < principalRoot 3 x := (x5w7g_cube_pos x).2 hpos
      have hD : 0 < principalRoot 3 x * principalRoot 3 (x - 3) ^ 2 := mul_pos ha (hb2 x hx3)
      rcases (div_nonneg_iff).1 h with ⟨h1, _⟩ | ⟨_, h2⟩
      · have h2x : 2 ≤ x := by linarith
        rcases lt_or_gt_of_ne hx3 with h' | h'
        · left; right; exact ⟨h2x, by linarith⟩
        · right; linarith
      · linarith
  · intro h
    have hx : x ≠ 0 := by
      rcases h with (h | h) | h
      · exact h.ne
      · exact (by linarith [h.1] : x ≠ 0)
      · exact (by linarith : x ≠ 0)
    have hx3 : x - 3 ≠ 0 := by
      rcases h with (h | h) | h
      · exact (by linarith : x - 3 ≠ 0)
      · exact (by linarith [h.2] : x - 3 ≠ 0)
      · exact (by linarith : x - 3 ≠ 0)
    refine ⟨hx, hx3, ?_⟩
    rw [L x hx hx3]
    rcases h with (h | h) | h
    · have ha : principalRoot 3 x < 0 := (x5w7g_cube_neg x).2 h
      exact div_nonneg_of_nonpos (by linarith)
        (mul_nonpos_of_nonpos_of_nonneg ha.le (hb2 x hx3).le)
    · have ha : 0 < principalRoot 3 x := (x5w7g_cube_pos x).2 (by linarith [h.1])
      exact div_nonneg (by linarith [h.1]) (mul_pos ha (hb2 x hx3)).le
    · have ha : 0 < principalRoot 3 x := (x5w7g_cube_pos x).2 (by linarith)
      exact div_nonneg (by linarith) (mul_pos ha (hb2 x hx3)).le

/-- Stitz-Zeager Exercise 5.3.32: `∛(x³+3x²-6x-8) > x + 1` has solution set `(-∞, -1)`. -/
@[kb "stitzzeager2013" "Exercise 5.3.32, p. 420"]
theorem exer_5_3_32 :
    {x : ℝ | x + 1 < principalRoot 3 (x ^ 3 + 3 * x ^ 2 - 6 * x - 8)} = Iio (-1) := by
  have h3 : Odd 3 := by decide
  ext x
  simp only [mem_ofPred_eq, mem_Iio]
  have hr := principalRoot_pow (n := 3) (x := x ^ 3 + 3 * x ^ 2 - 6 * x - 8) (by norm_num) (Or.inl h3)
  have key : x + 1 < principalRoot 3 (x ^ 3 + 3 * x ^ 2 - 6 * x - 8) ↔
      (x + 1) ^ 3 < (principalRoot 3 (x ^ 3 + 3 * x ^ 2 - 6 * x - 8)) ^ 3 :=
    (h3.strictMono_pow.lt_iff_lt).symm
  rw [key, hr]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- Stitz-Zeager Exercise 5.3.33: `(1/3) x^(3/4) (x-3)^(-2/3) + (3/4) x^(-1/4) (x-3)^(1/3) < 0` (book's powers,
defined for `x > 0`, `x ≠ 3`) has solution set `(0, 27/13)`. -/
@[kb "stitzzeager2013" "Exercise 5.3.33, p. 420"]
theorem exer_5_3_33 :
    {x : ℝ | 0 < x ∧ x - 3 ≠ 0 ∧
      1 / 3 * bookRatPow x 3 4 * bookRatPow (x - 3) (-2) 3 +
        3 / 4 * bookRatPow x (-1) 4 * bookRatPow (x - 3) 1 3 < 0} = Ioo 0 (27 / 13) := by
  have h3 : Odd 3 := by decide
  have L : ∀ x : ℝ, 0 < x → x - 3 ≠ 0 →
      1 / 3 * bookRatPow x 3 4 * bookRatPow (x - 3) (-2) 3 + 3 / 4 * bookRatPow x (-1) 4 * bookRatPow (x - 3) 1 3 =
      (13 * x - 27) / (12 * principalRoot 4 x * principalRoot 3 (x - 3) ^ 2) := by
    intro x hx hx3
    have hs := principalRoot_pow (n := 4) (x := x) (by norm_num) (Or.inr hx.le)
    have hb := principalRoot_pow (n := 3) (x := x - 3) (by norm_num) (Or.inl h3)
    have hs0 : 0 < principalRoot 4 x := by
      rw [principalRoot_of_nonneg hx.le]; exact Real.rpow_pos_of_pos hx _
    have hb0 := x5w7g_cube_ne _ hx3
    simp only [bookRatPow, zpow_neg, zpow_ofNat, pow_one]
    generalize principalRoot 4 x = s at hs hs0 ⊢
    generalize principalRoot 3 (x - 3) = b at hb hb0 ⊢
    have e : 1 / 3 * s ^ 3 * (b ^ 2)⁻¹ + 3 / 4 * s⁻¹ * b = (4 * s ^ 4 + 9 * b ^ 3) / (12 * s * b ^ 2) := by
      field_simp; ring
    rw [e, hb, hs]; ring_nf
  ext x
  simp only [mem_ofPred_eq, mem_Ioo]
  constructor
  · rintro ⟨hx, hx3, h⟩
    refine ⟨hx, ?_⟩
    rw [L x hx hx3] at h
    have hs0 : 0 < principalRoot 4 x := by
      rw [principalRoot_of_nonneg hx.le]; exact Real.rpow_pos_of_pos hx _
    have hb0 := x5w7g_cube_ne _ hx3
    have hD : 0 < 12 * principalRoot 4 x * principalRoot 3 (x - 3) ^ 2 := by positivity
    by_contra hc; push Not at hc
    have : 0 ≤ (13 * x - 27) / (12 * principalRoot 4 x * principalRoot 3 (x - 3) ^ 2) :=
      div_nonneg (by linarith) hD.le
    linarith
  · rintro ⟨hx, hx2⟩
    have hx3 : x - 3 ≠ 0 := by intro h; linarith
    refine ⟨hx, hx3, ?_⟩
    rw [L x hx hx3]
    have hs0 : 0 < principalRoot 4 x := by
      rw [principalRoot_of_nonneg hx.le]; exact Real.rpow_pos_of_pos hx _
    have hb0 := x5w7g_cube_ne _ hx3
    have hD : 0 < 12 * principalRoot 4 x * principalRoot 3 (x - 3) ^ 2 := by positivity
    exact div_neg_of_neg_of_pos (by linarith) hD

/-- Stitz-Zeager Exercise 5.3.34: `x^(-1/3)(x-3)^(-2/3) - x^(-4/3)(x-3)^(-5/3)(x²-3x+2) ≥ 0` (book's powers)
has solution set `(-∞, 0) ∪ (0, 3)`. -/
@[kb "stitzzeager2013" "Exercise 5.3.34, p. 420"]
theorem exer_5_3_34 :
    {x : ℝ | x ≠ 0 ∧ x - 3 ≠ 0 ∧
      0 ≤ bookRatPow x (-1) 3 * bookRatPow (x - 3) (-2) 3 -
        bookRatPow x (-4) 3 * bookRatPow (x - 3) (-5) 3 * (x ^ 2 - 3 * x + 2)} = Iio 0 ∪ Ioo 0 3 := by
  have h3 : Odd 3 := by decide
  have L : ∀ x : ℝ, x ≠ 0 → x - 3 ≠ 0 →
      bookRatPow x (-1) 3 * bookRatPow (x - 3) (-2) 3 -
        bookRatPow x (-4) 3 * bookRatPow (x - 3) (-5) 3 * (x ^ 2 - 3 * x + 2) =
      -2 / (principalRoot 3 x ^ 4 * principalRoot 3 (x - 3) ^ 5) := by
    intro x hx hx3
    have ha := principalRoot_pow (n := 3) (x := x) (by norm_num) (Or.inl h3)
    have hb := principalRoot_pow (n := 3) (x := x - 3) (by norm_num) (Or.inl h3)
    have ha0 := x5w7g_cube_ne _ hx
    have hb0 := x5w7g_cube_ne _ hx3
    simp only [bookRatPow, zpow_neg, zpow_ofNat, pow_one]
    generalize principalRoot 3 x = a at ha ha0 ⊢
    generalize principalRoot 3 (x - 3) = b at hb hb0 ⊢
    have e : a⁻¹ * (b ^ 2)⁻¹ - (a ^ 4)⁻¹ * (b ^ 5)⁻¹ * (x ^ 2 - 3 * x + 2) =
        (a ^ 3 * b ^ 3 - (x ^ 2 - 3 * x + 2)) / (a ^ 4 * b ^ 5) := by
      field_simp
    rw [e, show a ^ 3 * b ^ 3 = x * (x - 3) by rw [ha, hb]]
    ring_nf
  ext x
  simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ioo]
  constructor
  · rintro ⟨hx, hx3, h⟩
    rw [L x hx hx3] at h
    have ha4 : 0 < principalRoot 3 x ^ 4 := by
      have := x5w7g_cube_ne _ hx
      positivity
    have hb0 := x5w7g_cube_ne _ hx3
    have hb5 : principalRoot 3 (x - 3) ^ 5 < 0 := by
      by_contra hc; push Not at hc
      have hne : principalRoot 3 (x - 3) ^ 5 ≠ 0 := pow_ne_zero _ hb0
      have : 0 < principalRoot 3 x ^ 4 * principalRoot 3 (x - 3) ^ 5 :=
        mul_pos ha4 (lt_of_le_of_ne hc (Ne.symm hne))
      have := div_neg_of_neg_of_pos (by norm_num : (-2 : ℝ) < 0) this
      linarith
    have hb : principalRoot 3 (x - 3) < 0 := by
      by_contra hc; push Not at hc
      have := pow_nonneg hc 5
      linarith
    have hx3' : x < 3 := by have := (x5w7g_cube_neg (x - 3)).1 hb; linarith
    rcases lt_or_gt_of_ne hx with h' | h'
    · left; exact h'
    · right; exact ⟨h', hx3'⟩
  · intro h
    have hx : x ≠ 0 := by
      rcases h with h | h
      · exact h.ne
      · exact h.1.ne'
    have hx3' : x < 3 := by
      rcases h with h | h
      · linarith
      · exact h.2
    have hx3 : x - 3 ≠ 0 := by intro h'; linarith
    refine ⟨hx, hx3, ?_⟩
    rw [L x hx hx3]
    have ha4 : 0 < principalRoot 3 x ^ 4 := by
      have := x5w7g_cube_ne _ hx
      positivity
    have hb : principalRoot 3 (x - 3) < 0 := (x5w7g_cube_neg _).2 (by linarith)
    have hb5 : principalRoot 3 (x - 3) ^ 5 < 0 := Odd.pow_neg (by decide) hb
    exact div_nonneg_of_nonpos (by norm_num) (mul_nonpos_of_nonneg_of_nonpos ha4.le hb5.le)

/-- Stitz-Zeager Exercise 5.3.35: `(2/3)(x+4)^(3/5)(x-2)^(-1/3) + (3/5)(x+4)^(-2/5)(x-2)^(2/3) ≥ 0` (book's powers)
has solution set `(-∞, -4) ∪ (-4, -22/19] ∪ (2, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 5.3.35, p. 420"]
theorem exer_5_3_35 :
    {x : ℝ | x + 4 ≠ 0 ∧ x - 2 ≠ 0 ∧
      0 ≤ 2 / 3 * bookRatPow (x + 4) 3 5 * bookRatPow (x - 2) (-1) 3 +
        3 / 5 * bookRatPow (x + 4) (-2) 5 * bookRatPow (x - 2) 2 3} =
    Iio (-4) ∪ Ioc (-4) (-22 / 19) ∪ Ioi 2 := by
  have h3 : Odd 3 := by decide
  have h5 : Odd 5 := by decide
  have L : ∀ x : ℝ, x + 4 ≠ 0 → x - 2 ≠ 0 →
      2 / 3 * bookRatPow (x + 4) 3 5 * bookRatPow (x - 2) (-1) 3 +
        3 / 5 * bookRatPow (x + 4) (-2) 5 * bookRatPow (x - 2) 2 3 =
      (19 * x + 22) / (15 * principalRoot 5 (x + 4) ^ 2 * principalRoot 3 (x - 2)) := by
    intro x hx hx2
    have ha := principalRoot_pow (n := 5) (x := x + 4) (by norm_num) (Or.inl h5)
    have hb := principalRoot_pow (n := 3) (x := x - 2) (by norm_num) (Or.inl h3)
    have ha0 : principalRoot 5 (x + 4) ≠ 0 := by
      intro h; rw [h] at ha; apply hx; rw [← ha]; norm_num
    have hb0 := x5w7g_cube_ne _ hx2
    simp only [bookRatPow, zpow_neg, zpow_ofNat, pow_one]
    generalize principalRoot 5 (x + 4) = a at ha ha0 ⊢
    generalize principalRoot 3 (x - 2) = b at hb hb0 ⊢
    have e : 2 / 3 * a ^ 3 * b⁻¹ + 3 / 5 * (a ^ 2)⁻¹ * b ^ 2 = (10 * a ^ 5 + 9 * b ^ 3) / (15 * a ^ 2 * b) := by
      field_simp; ring
    rw [e, ha, hb]; ring_nf
  have hd : ∀ x : ℝ, x + 4 ≠ 0 → 0 < principalRoot 5 (x + 4) ^ 2 := by
    intro x hx
    have ha0 : principalRoot 5 (x + 4) ≠ 0 := by
      intro h
      have ha := principalRoot_pow (n := 5) (x := x + 4) (by norm_num) (Or.inl (by decide))
      rw [h] at ha; apply hx; rw [← ha]; norm_num
    positivity
  ext x
  simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ioc, mem_Ioi]
  constructor
  · rintro ⟨hx, hx2, h⟩
    rw [L x hx hx2] at h
    rcases lt_or_gt_of_ne hx2 with hlt | hgt
    · have hb : principalRoot 3 (x - 2) < 0 := (x5w7g_cube_neg _).2 (by linarith)
      have hD : 15 * principalRoot 5 (x + 4) ^ 2 * principalRoot 3 (x - 2) < 0 :=
        mul_neg_of_pos_of_neg (by have := hd x hx; positivity) hb
      rcases (div_nonneg_iff).1 h with ⟨_, h2⟩ | ⟨h1, _⟩
      · linarith
      · have hxle : x ≤ -22 / 19 := by linarith
        rcases lt_or_gt_of_ne hx with h' | h'
        · left; left; linarith
        · left; right; exact ⟨by linarith, hxle⟩
    · right; linarith
  · intro h
    have hx : x + 4 ≠ 0 := by
      rcases h with (h | h) | h
      · exact (by linarith : x + 4 ≠ 0)
      · exact (by linarith [h.1] : x + 4 ≠ 0)
      · exact (by linarith : x + 4 ≠ 0)
    have hx2 : x - 2 ≠ 0 := by
      rcases h with (h | h) | h
      · exact (by linarith : x - 2 ≠ 0)
      · exact (by linarith [h.2] : x - 2 ≠ 0)
      · exact (by linarith : x - 2 ≠ 0)
    refine ⟨hx, hx2, ?_⟩
    rw [L x hx hx2]
    have hpos := hd x hx
    rcases h with (h | h) | h
    · have hb : principalRoot 3 (x - 2) < 0 := (x5w7g_cube_neg _).2 (by linarith)
      exact div_nonneg_of_nonpos (by linarith)
        (mul_neg_of_pos_of_neg (by positivity) hb).le
    · have hb : principalRoot 3 (x - 2) < 0 := (x5w7g_cube_neg _).2 (by linarith [h.2])
      exact div_nonneg_of_nonpos (by linarith [h.2])
        (mul_neg_of_pos_of_neg (by positivity) hb).le
    · have hb : 0 < principalRoot 3 (x - 2) := (x5w7g_cube_pos _).2 (by linarith)
      exact div_nonneg (by linarith) (mul_pos (by positivity) hb).le

end UndergradKB.Precalculus.Course
