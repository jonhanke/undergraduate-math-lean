import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 10 (Stitz-Zeager): exercises with the book's answers (wave 7), rounded decimal answers.

Each rounded value is stated as two strict bounds around the exact expression the exercise determines. -/

namespace UndergradKB.Precalculus.Course

open Real

private lemma num10_pi_deg (d : ℝ) (hd : 0 ≤ d) :
    d * 3.141592653 / 180 ≤ d * π / 180 ∧ d * π / 180 ≤ d * 3.141592654 / 180 := by
  have p1 := pi_gt_d20
  have p2 := pi_lt_d20
  constructor <;> nlinarith

private lemma num10_sin_bd {y yl yu : ℝ} (h0 : 0 ≤ yl) (hl : yl ≤ y) (hu : y ≤ yu) (h1 : yu ≤ 1) :
    yl - yl ^ 3 / 6 - yu ^ 5 / 100 ≤ sin y ∧ sin y ≤ yu - yu ^ 3 / 6 + yu ^ 5 / 100 := by
  have y0 : 0 ≤ y := by linarith
  have hb := Real.sin_bound (x := y) (by rw [abs_of_nonneg y0]; linarith)
  rw [abs_of_nonneg y0] at hb
  have h4 : y ^ 5 ≤ yu ^ 5 := pow_le_pow_left₀ y0 hu 5
  obtain ⟨b1, b2⟩ := abs_le.1 hb
  have yu0 : 0 ≤ yu := by linarith
  have m1 : yl - yl ^ 3 / 6 ≤ y - y ^ 3 / 6 := by
    have : 0 ≤ (y - yl) * (1 - (y ^ 2 + y * yl + yl ^ 2) / 6) := by
      apply mul_nonneg (by linarith); nlinarith
    nlinarith
  have m2 : y - y ^ 3 / 6 ≤ yu - yu ^ 3 / 6 := by
    have : 0 ≤ (yu - y) * (1 - (yu ^ 2 + y * yu + y ^ 2) / 6) := by
      apply mul_nonneg (by linarith); nlinarith
    nlinarith
  constructor <;> linarith

private lemma num10_cos_bd {y yl yu : ℝ} (h0 : 0 ≤ yl) (hl : yl ≤ y) (hu : y ≤ yu) (h1 : yu ≤ 1) :
    1 - yu ^ 2 / 2 - yu ^ 4 * (5 / 96) ≤ cos y ∧ cos y ≤ 1 - yl ^ 2 / 2 + yu ^ 4 * (5 / 96) := by
  have y0 : 0 ≤ y := by linarith
  have hb := Real.cos_bound (x := y) (by rw [abs_of_nonneg y0]; linarith)
  rw [abs_of_nonneg y0] at hb
  have h4 : y ^ 4 ≤ yu ^ 4 := pow_le_pow_left₀ y0 hu 4
  obtain ⟨b1, b2⟩ := abs_le.1 hb
  have a1 : y ^ 2 ≤ yu ^ 2 := pow_le_pow_left₀ y0 hu 2
  have a2 : yl ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ h0 hl 2
  constructor <;> linarith

/-- One doubling step on bounds `(sl, su, cl, cu)` of `(sin y, sin y, cos y, cos y)`. -/
private noncomputable def nStep (t : ℝ × ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (2 * t.1 * t.2.2.1, 2 * t.2.1 * t.2.2.2, 2 * t.2.2.1 ^ 2 - 1, 2 * t.2.2.2 ^ 2 - 1)

private noncomputable def nIt : ℕ → ℝ × ℝ × ℝ × ℝ → ℝ × ℝ × ℝ × ℝ
  | 0, t => t
  | n + 1, t => nIt n (nStep t)

private noncomputable def nOk : ℕ → ℝ × ℝ × ℝ × ℝ → Prop
  | 0, _ => True
  | n + 1, t => (0 ≤ t.1 ∧ 0 ≤ t.2.2.1) ∧ nOk n (nStep t)

private noncomputable def nP (y : ℝ) (t : ℝ × ℝ × ℝ × ℝ) : Prop :=
  t.1 ≤ sin y ∧ sin y ≤ t.2.1 ∧ t.2.2.1 ≤ cos y ∧ cos y ≤ t.2.2.2

private lemma num10_step {y : ℝ} {t : ℝ × ℝ × ℝ × ℝ} (h : nP y t) (h0 : 0 ≤ t.1 ∧ 0 ≤ t.2.2.1) :
    nP (2 * y) (nStep t) := by
  obtain ⟨a1, a2, b1, b2⟩ := h
  obtain ⟨s0, c0⟩ := h0
  have k0 : 0 ≤ cos y := by linarith
  have u0 : 0 ≤ sin y := by linarith
  have cu0 : 0 ≤ t.2.2.2 := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sin_two_mul]; simp only [nStep]; nlinarith [mul_le_mul a1 b1 c0 u0]
  · rw [sin_two_mul]; simp only [nStep]; nlinarith [mul_le_mul a2 b2 k0 (by linarith : 0 ≤ t.2.1)]
  · rw [cos_two_mul]; simp only [nStep]; nlinarith
  · rw [cos_two_mul]; simp only [nStep]; nlinarith

private lemma num10_iter (n : ℕ) : ∀ (y : ℝ) (t : ℝ × ℝ × ℝ × ℝ), nP y t → nOk n t →
    nP (2 ^ n * y) (nIt n t) := by
  induction n with
  | zero => intro y t h _; simpa [nIt] using h
  | succ n ih =>
    intro y t h hok
    have := ih (2 * y) (nStep t) (num10_step h hok.1) hok.2
    simpa [nIt, pow_succ, mul_assoc, mul_comm, mul_left_comm] using this

private noncomputable def nBase (zl zu : ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (zl - zl ^ 3 / 6 - zu ^ 5 / 100, zu - zu ^ 3 / 6 + zu ^ 5 / 100,
      1 - 2 * (zu / 2 - (zu / 2) ^ 3 / 6 + (zu / 2) ^ 5 / 100) ^ 2,
      1 - 2 * (zl / 2 - (zl / 2) ^ 3 / 6 - (zu / 2) ^ 5 / 100) ^ 2)

private def nBaseOk (zl zu : ℝ) : Prop := 0 ≤ zl / 2 - (zl / 2) ^ 3 / 6 - (zu / 2) ^ 5 / 100

/-- Base case: bounds on `sin z` and `cos z = 1 - 2 sin² (z/2)` for `zl ≤ z ≤ zu ≤ 1`, `0 ≤ zl`. -/
private lemma num10_base {z zl zu : ℝ} (h0 : 0 ≤ zl) (hl : zl ≤ z) (hu : z ≤ zu) (h1 : zu ≤ 1)
    (hb : nBaseOk zl zu) : nP z (nBase zl zu) := by
  obtain ⟨a1, a2⟩ := num10_sin_bd h0 hl hu h1
  obtain ⟨b1, b2⟩ := num10_sin_bd (y := z / 2) (yl := zl / 2) (yu := zu / 2) (by linarith) (by linarith)
    (by linarith) (by linarith)
  have hc : cos z = 1 - 2 * sin (z / 2) ^ 2 := by
    have h := sin_sq_add_cos_sq (z / 2)
    have h2 : cos z = 2 * cos (z / 2) ^ 2 - 1 := by
      rw [← cos_two_mul]; congr 1; ring
    rw [h2]; nlinarith
  unfold nBaseOk at hb
  have hs0 : 0 ≤ sin (z / 2) := b1.trans' hb
  have q1 : (zl / 2 - (zl / 2) ^ 3 / 6 - (zu / 2) ^ 5 / 100) ^ 2 ≤ sin (z / 2) ^ 2 := pow_le_pow_left₀ hb b1 2
  have q2 : sin (z / 2) ^ 2 ≤ (zu / 2 - (zu / 2) ^ 3 / 6 + (zu / 2) ^ 5 / 100) ^ 2 := pow_le_pow_left₀ hs0 b2 2
  refine ⟨a1, a2, ?_, ?_⟩
  · simp only [nBase]; rw [hc]; linarith
  · simp only [nBase]; rw [hc]; linarith

/-- Bounds on `sin` and `cos` of `d` degrees (`0 ≤ d ≤ 180`) by seven doublings from `d/128` degrees. -/
private lemma num10_deg (d : ℝ) (h0 : 0 ≤ d) (h1 : d ≤ 180)
    (hok : nBaseOk (d * 3.141592653 / 23040) (d * 3.141592654 / 23040) ∧
      nOk 7 (nBase (d * 3.141592653 / 23040) (d * 3.141592654 / 23040))) :
    nP (d * π / 180) (nIt 7 (nBase (d * 3.141592653 / 23040) (d * 3.141592654 / 23040))) := by
  obtain ⟨p1, p2⟩ := num10_pi_deg d h0
  have y1 : d * 3.141592653 / 23040 ≤ d * π / 23040 := by linarith
  have y2 : d * π / 23040 ≤ d * 3.141592654 / 23040 := by linarith
  have y3 : d * 3.141592654 / 23040 ≤ 1 := by linarith
  have y0 : 0 ≤ d * 3.141592653 / 23040 := by positivity
  have := num10_iter 7 (d * π / 23040) _ (num10_base y0 y1 y2 y3 hok.1) hok.2
  have e : (2 : ℝ) ^ 7 * (d * π / 23040) = d * π / 180 := by ring
  rw [e] at this
  exact this

/-- Decimal wrapper: `lo ≤ sin d° ≤ hi` (side conditions by `norm_num [nBaseOk, nOk, nIt, nStep, nBase]`). -/
private lemma num10_sd (d lo hi : ℝ) (h0 : 0 ≤ d) (h1 : d ≤ 180)
    (hok : nBaseOk (d * 3.141592653 / 23040) (d * 3.141592654 / 23040) ∧ nOk 7 (nBase (d * 3.141592653 / 23040) (d * 3.141592654 / 23040)))
    (hl : lo ≤ (nIt 7 (nBase (d * 3.141592653 / 23040) (d * 3.141592654 / 23040))).1)
    (hh : (nIt 7 (nBase (d * 3.141592653 / 23040) (d * 3.141592654 / 23040))).2.1 ≤ hi) :
    lo ≤ sin (d * π / 180) ∧ sin (d * π / 180) ≤ hi := by
  obtain ⟨a, b, -, -⟩ := num10_deg d h0 h1 hok
  exact ⟨hl.trans a, b.trans hh⟩

/-- Decimal wrapper: `lo ≤ cos d° ≤ hi`. -/
private lemma num10_cd (d lo hi : ℝ) (h0 : 0 ≤ d) (h1 : d ≤ 180)
    (hok : nBaseOk (d * 3.141592653 / 23040) (d * 3.141592654 / 23040) ∧ nOk 7 (nBase (d * 3.141592653 / 23040) (d * 3.141592654 / 23040)))
    (hl : lo ≤ (nIt 7 (nBase (d * 3.141592653 / 23040) (d * 3.141592654 / 23040))).2.2.1)
    (hh : (nIt 7 (nBase (d * 3.141592653 / 23040) (d * 3.141592654 / 23040))).2.2.2 ≤ hi) :
    lo ≤ cos (d * π / 180) ∧ cos (d * π / 180) ≤ hi := by
  obtain ⟨-, -, a, b⟩ := num10_deg d h0 h1 hok
  exact ⟨hl.trans a, b.trans hh⟩

/-- If `cos b° < q < cos a°` (with `0 ≤ a ≤ b ≤ 180`) then `a < arccos q` in degrees `< b`. -/
private lemma num10_arccos_deg {q a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 180)
    (h1 : cos (b * π / 180) < q) (h2 : q < cos (a * π / 180)) :
    a < arccos q * 180 / π ∧ arccos q * 180 / π < b := by
  have hp := pi_pos
  have a0 : 0 ≤ a * π / 180 := by positivity
  have b0 : 0 ≤ b * π / 180 := by
    have : 0 ≤ b := by linarith
    positivity
  have bp : b * π / 180 ≤ π := by
    have := mul_le_mul_of_nonneg_right hb hp.le; linarith
  have ab : a * π / 180 ≤ π := by
    have := mul_le_mul_of_nonneg_right (show a ≤ 180 by linarith) hp.le; linarith
  have hq1 : q ≤ 1 := by linarith [cos_le_one (a * π / 180)]
  have hq0 : -1 ≤ q := by linarith [neg_one_le_cos (b * π / 180)]
  have l1 : arccos q < b * π / 180 := by
    have := strictAntiOn_arccos ⟨by linarith [neg_one_le_cos (b * π / 180)], by linarith⟩ ⟨hq0, hq1⟩ h1
    rwa [arccos_cos b0 bp] at this
  have l2 : a * π / 180 < arccos q := by
    have := strictAntiOn_arccos ⟨hq0, hq1⟩ ⟨by linarith [neg_one_le_cos (a * π / 180)], cos_le_one _⟩ h2
    rwa [arccos_cos a0 ab] at this
  constructor
  · rw [lt_div_iff₀ hp]; linarith
  · rw [div_lt_iff₀ hp]; linarith


/-- If `sin a° < t cos a°` and `t cos b° < sin b°` (`0 ≤ a ≤ b < 90`) then `a < arctan t` in degrees `< b`. -/
private lemma num10_arctan_deg {t a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 90)
    (h1 : sin (a * π / 180) < t * cos (a * π / 180)) (h2 : t * cos (b * π / 180) < sin (b * π / 180)) :
    a < arctan t * 180 / π ∧ arctan t * 180 / π < b := by
  have hp := pi_pos
  have a0 : 0 ≤ a * π / 180 := by positivity
  have b0 : 0 ≤ b * π / 180 := by
    have : 0 ≤ b := by linarith
    positivity
  have bh : b * π / 180 < π / 2 := by
    have := mul_lt_mul_of_pos_right hb hp; linarith
  have ah : a * π / 180 < π / 2 := by
    have := mul_lt_mul_of_pos_right (show a < 90 by linarith) hp; linarith
  have ca : 0 < cos (a * π / 180) := cos_pos_of_mem_Ioo ⟨by linarith, ah⟩
  have cb : 0 < cos (b * π / 180) := cos_pos_of_mem_Ioo ⟨by linarith, bh⟩
  have t1 : tan (a * π / 180) < t := by rw [tan_eq_sin_div_cos, div_lt_iff₀ ca]; linarith
  have t2 : t < tan (b * π / 180) := by rw [tan_eq_sin_div_cos, lt_div_iff₀ cb]; linarith
  have l1 := arctan_strictMono t1
  have l2 := arctan_strictMono t2
  rw [arctan_tan (by linarith) ah] at l1
  rw [arctan_tan (by linarith) bh] at l2
  constructor
  · rw [lt_div_iff₀ hp]; linarith
  · rw [div_lt_iff₀ hp]; linarith

/-- If `sin a° < q < sin b°` (`0 ≤ a ≤ b ≤ 90`) then `a < arcsin q` in degrees `< b`. -/
private lemma num10_arcsin_deg {q a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 90)
    (h1 : sin (a * π / 180) < q) (h2 : q < sin (b * π / 180)) :
    a < arcsin q * 180 / π ∧ arcsin q * 180 / π < b := by
  have hp := pi_pos
  have a0 : 0 ≤ a * π / 180 := by positivity
  have b0 : 0 ≤ b * π / 180 := by
    have : 0 ≤ b := by linarith
    positivity
  have bh : b * π / 180 ≤ π / 2 := by
    have := mul_le_mul_of_nonneg_right hb hp.le; linarith
  have ah : a * π / 180 ≤ π / 2 := by
    have := mul_le_mul_of_nonneg_right (show a ≤ 90 by linarith) hp.le; linarith
  have hq1 : q ≤ 1 := by linarith [sin_le_one (b * π / 180)]
  have hq0 : -1 ≤ q := by linarith [neg_one_le_sin (a * π / 180)]
  have hs : sin (arcsin q) = q := sin_arcsin hq0 hq1
  have l1 : a * π / 180 < arcsin q := by
    by_contra h
    replace h := not_lt.1 h
    have := sin_le_sin_of_le_of_le_pi_div_two (neg_pi_div_two_le_arcsin q) ah h
    rw [hs] at this; linarith
  have l2 : arcsin q < b * π / 180 := by
    by_contra h
    replace h := not_lt.1 h
    have := sin_le_sin_of_le_of_le_pi_div_two (by linarith) (arcsin_le_pi_div_two q) h
    rw [hs] at this; linarith
  constructor
  · rw [lt_div_iff₀ hp]; linarith
  · rw [div_lt_iff₀ hp]; linarith

/-- Radian version: `lo ≤ sin x ≤ hi` for `xl ≤ x ≤ xu`, `0 ≤ xl`, `xu < π` (side conditions by norm_num). -/
private lemma num10_rs {x xl xu lo hi : ℝ} (h0 : 0 ≤ xl) (hl : xl ≤ x) (hu : x ≤ xu) (h1 : xu ≤ 128)
    (hok : nBaseOk (xl / 128) (xu / 128) ∧ nOk 7 (nBase (xl / 128) (xu / 128)))
    (hlo : lo ≤ (nIt 7 (nBase (xl / 128) (xu / 128))).1)
    (hhi : (nIt 7 (nBase (xl / 128) (xu / 128))).2.1 ≤ hi) : lo ≤ sin x ∧ sin x ≤ hi := by
  have y1 : xl / 128 ≤ x / 128 := by linarith
  have y2 : x / 128 ≤ xu / 128 := by linarith
  have y3 : xu / 128 ≤ 1 := by linarith
  have y0 : 0 ≤ xl / 128 := by positivity
  have := num10_iter 7 (x / 128) _ (num10_base y0 y1 y2 y3 hok.1) hok.2
  have e : (2 : ℝ) ^ 7 * (x / 128) = x := by ring
  rw [e] at this
  obtain ⟨a, b, -, -⟩ := this
  exact ⟨hlo.trans a, b.trans hhi⟩

/-- Radian version: `lo ≤ cos x ≤ hi`. -/
private lemma num10_rc {x xl xu lo hi : ℝ} (h0 : 0 ≤ xl) (hl : xl ≤ x) (hu : x ≤ xu) (h1 : xu ≤ 128)
    (hok : nBaseOk (xl / 128) (xu / 128) ∧ nOk 7 (nBase (xl / 128) (xu / 128)))
    (hlo : lo ≤ (nIt 7 (nBase (xl / 128) (xu / 128))).2.2.1)
    (hhi : (nIt 7 (nBase (xl / 128) (xu / 128))).2.2.2 ≤ hi) : lo ≤ cos x ∧ cos x ≤ hi := by
  have y1 : xl / 128 ≤ x / 128 := by linarith
  have y2 : x / 128 ≤ xu / 128 := by linarith
  have y3 : xu / 128 ≤ 1 := by linarith
  have y0 : 0 ≤ xl / 128 := by positivity
  have := num10_iter 7 (x / 128) _ (num10_base y0 y1 y2 y3 hok.1) hok.2
  have e : (2 : ℝ) ^ 7 * (x / 128) = x := by ring
  rw [e] at this
  obtain ⟨-, -, a, b⟩ := this
  exact ⟨hlo.trans a, b.trans hhi⟩
set_option maxHeartbeats 1600000 in
/-- Stitz-Zeager Exercise 10.2.49: `sin 78.95° ≈ 0.981` (three decimals), as `0.9805 < sin 78.95° < 0.9815`. -/
@[kb "stitzzeager2013" "Exercise 10.2.49, p. 748"]
theorem exer_10_2_49 :
    (0.9805 : ℝ) < sin (78.95 * π / 180) ∧ sin (78.95 * π / 180) < 0.9815 := by
  obtain ⟨al, au⟩ := num10_sd 78.95 0.981460296 0.981460298 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  constructor <;> linarith

set_option maxHeartbeats 1600000 in
/-- Stitz-Zeager Exercise 10.2.50: `cos (-2.01) ≈ -0.425`, as `-0.4255 < cos (-2.01) < -0.4245`. -/
@[kb "stitzzeager2013" "Exercise 10.2.50, p. 748"]
theorem exer_10_2_50 :
    (-0.4255 : ℝ) < cos (-2.01) ∧ cos (-2.01) < -0.4245 := by
  rw [cos_neg]
  obtain ⟨al, au⟩ := num10_rc (x := 2.01) (xl := 2.01) (xu := 2.01) (lo := (-0.425218853)) (hi := (-0.425218851)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  constructor <;> linarith

set_option maxHeartbeats 1600000 in
/-- Stitz-Zeager Exercise 10.2.51: `sin 392.994 ≈ -0.291` (radians; `392.994 = 125π + 0.2949...` up to `62` full turns), as `-0.2915 < sin 392.994 < -0.2905`. -/
@[kb "stitzzeager2013" "Exercise 10.2.51, p. 748"]
theorem exer_10_2_51 :
    (-0.2915 : ℝ) < sin 392.994 ∧ sin 392.994 < -0.2905 := by
  have p1 := pi_gt_d20
  have p2 := pi_lt_d20
  rw [show (392.994 : ℝ) = (392.994 - 125 * π) + π + ((62 : ℕ) : ℝ) * (2 * π) by push_cast; ring,
    sin_add_nat_mul_two_pi, sin_add_pi]
  obtain ⟨al, au⟩ := num10_rs (x := 392.994 - 125 * π) (xl := 0.294918301) (xu := 0.294918302) (lo := 0.290661679) (hi := 0.290661681) (by norm_num) (by linarith) (by linarith) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  constructor <;> linarith

set_option maxHeartbeats 1600000 in
/-- Stitz-Zeager Exercise 10.2.52: `cos 207° ≈ -0.891`, as `-0.8915 < cos 207° < -0.8905`. -/
@[kb "stitzzeager2013" "Exercise 10.2.52, p. 748"]
theorem exer_10_2_52 :
    (-0.8915 : ℝ) < cos (207 * π / 180) ∧ cos (207 * π / 180) < -0.8905 := by
  rw [show (207 : ℝ) * π / 180 = 27 * π / 180 + π by ring, cos_add_pi]
  obtain ⟨al, au⟩ := num10_cd 27 0.891006524 0.891006525 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  constructor <;> linarith

set_option maxHeartbeats 1600000 in
/-- Stitz-Zeager Exercise 10.2.54: `cos e ≈ -0.912`, as `-0.9125 < cos e < -0.9115` (with `e = exp 1`). -/
@[kb "stitzzeager2013" "Exercise 10.2.54, p. 748"]
theorem exer_10_2_54 :
    (-0.9125 : ℝ) < cos (Real.exp 1) ∧ cos (Real.exp 1) < -0.9115 := by
  obtain ⟨al, au⟩ := num10_rc (x := Real.exp 1) (xl := 2.7182818283) (xu := 2.7182818286) (lo := (-0.911733915)) (hi := (-0.911733914)) (by norm_num) (exp_one_gt_d9.le) (exp_one_lt_d9.le) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  constructor <;> linarith

set_option maxHeartbeats 1600000 in
/-- Stitz-Zeager Exercise 10.2.57: in the right triangle with hypotenuse `8` and angle `33°`, the legs `8 cos 33° ≈ 6.709` and `8 sin 33° ≈ 4.357` (three decimals). -/
@[kb "stitzzeager2013" "Exercise 10.2.57, p. 748"]
theorem exer_10_2_57 :
    ((6.7085 : ℝ) < 8 * cos (33 * π / 180) ∧ 8 * cos (33 * π / 180) < 6.7095) ∧
      ((4.3566 : ℝ) < 8 * sin (33 * π / 180) ∧ 8 * sin (33 * π / 180) < 4.3576) := by
  obtain ⟨al, au⟩ := num10_cd 33 0.838670567 0.838670569 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨bl, bu⟩ := num10_sd 33 0.544639034 0.544639036 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith

set_option maxHeartbeats 1600000 in
/-- Stitz-Zeager Exercise 10.2.58: in the right triangle with angle `42°` (so `β`'s complement is `48°`) and leg `6`, the hypotenuse is `c = 6 / sin 48° ≈ 8.074` and the other leg `√(c² - 6²) ≈ 5.402` (three decimals). -/
@[kb "stitzzeager2013" "Exercise 10.2.58, p. 748"]
theorem exer_10_2_58 :
    ((8.0735 : ℝ) < 6 / sin (48 * π / 180) ∧ 6 / sin (48 * π / 180) < 8.0745) ∧
      ((5.4015 : ℝ) < √((6 / sin (48 * π / 180)) ^ 2 - 6 ^ 2) ∧ √((6 / sin (48 * π / 180)) ^ 2 - 6 ^ 2) < 5.4025) := by
  obtain ⟨al, au⟩ := num10_sd 48 0.743144825 0.743144826 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  have hB : 0 < sin (48 * π / 180) := by linarith
  have c1 : (8.0737963 : ℝ) < 6 / sin (48 * π / 180) := by rw [lt_div_iff₀ hB]; linarith
  have c2 : 6 / sin (48 * π / 180) < (8.0737964 : ℝ) := by rw [div_lt_iff₀ hB]; linarith
  generalize 6 / sin (48 * π / 180) = c at c1 c2 ⊢
  have hc0 : 0 < c := by linarith
  refine ⟨⟨by linarith, by linarith⟩, ?_, ?_⟩
  · rw [Real.lt_sqrt (by norm_num)]; nlinarith
  · rw [Real.sqrt_lt' (by norm_num)]; nlinarith

set_option maxHeartbeats 1600000 in
/-- Stitz-Zeager Exercise 10.2.59: the hypotenuse `4 / cos 12° ≈ 4.089` (three decimals). -/
@[kb "stitzzeager2013" "Exercise 10.2.59, p. 748"]
theorem exer_10_2_59 :
    (4.0885 : ℝ) < 4 / cos (12 * π / 180) ∧ 4 / cos (12 * π / 180) < 4.0895 := by
  obtain ⟨al, au⟩ := num10_cd 12 0.978147600 0.978147601 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  have hB : 0 < cos (12 * π / 180) := by linarith
  constructor
  · rw [lt_div_iff₀ hB]; linarith
  · rw [div_lt_iff₀ hB]; linarith

set_option maxHeartbeats 1600000 in
/-- Stitz-Zeager Exercise 10.2.60: the adjacent side `5280 cos 78.123° ≈ 1086.68` (two decimals). -/
@[kb "stitzzeager2013" "Exercise 10.2.60, p. 748"]
theorem exer_10_2_60 :
    (1086.675 : ℝ) < 5280 * cos (78.123 * π / 180) ∧ 5280 * cos (78.123 * π / 180) < 1086.685 := by
  obtain ⟨al, au⟩ := num10_cd 78.123 0.205811369 0.205811371 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  constructor <;> linarith

set_option maxHeartbeats 1600000 in
/-- Stitz-Zeager Exercise 10.2.61: the hypotenuse `117.42 / sin 59° ≈ 136.99` (two decimals). -/
@[kb "stitzzeager2013" "Exercise 10.2.61, p. 748"]
theorem exer_10_2_61 :
    (136.985 : ℝ) < 117.42 / sin (59 * π / 180) ∧ 117.42 / sin (59 * π / 180) < 136.995 := by
  obtain ⟨al, au⟩ := num10_sd 59 0.857167300 0.857167301 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  have hB : 0 < sin (59 * π / 180) := by linarith
  constructor
  · rw [lt_div_iff₀ hB]; linarith
  · rw [div_lt_iff₀ hB]; linarith

set_option maxHeartbeats 1600000 in
/-- Stitz-Zeager Exercise 10.2.62: the opposite side `10 sin 5° ≈ 0.872` (three decimals). -/
@[kb "stitzzeager2013" "Exercise 10.2.62, p. 748"]
theorem exer_10_2_62 :
    (0.8715 : ℝ) < 10 * sin (5 * π / 180) ∧ 10 * sin (5 * π / 180) < 0.8725 := by
  obtain ⟨al, au⟩ := num10_sd 5 0.087155742 0.087155743 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  constructor <;> linarith

set_option maxHeartbeats 1600000 in
/-- Stitz-Zeager Exercise 10.2.63: the adjacent side `10 cos 5° ≈ 9.962` (three decimals). -/
@[kb "stitzzeager2013" "Exercise 10.2.63, p. 748"]
theorem exer_10_2_63 :
    (9.9615 : ℝ) < 10 * cos (5 * π / 180) ∧ 10 * cos (5 * π / 180) < 9.9625 := by
  obtain ⟨al, au⟩ := num10_cd 5 0.996194698 0.996194699 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  constructor <;> linarith

set_option maxHeartbeats 1600000 in
/-- Stitz-Zeager Exercise 10.2.64: the hypotenuse `c = 306 / sin 37.5° ≈ 502.660` (three decimals) and the adjacent side `√(c² - 306²)`, which is `398.7865 < · < 398.7875` (about `398.787`; the book prints `398.797`). -/
@[kb "stitzzeager2013" "Exercise 10.2.64, p. 748"]
theorem exer_10_2_64 :
    ((502.6595 : ℝ) < 306 / sin (37.5 * π / 180) ∧ 306 / sin (37.5 * π / 180) < 502.6605) ∧
      ((398.7865 : ℝ) < √((306 / sin (37.5 * π / 180)) ^ 2 - 306 ^ 2) ∧ √((306 / sin (37.5 * π / 180)) ^ 2 - 306 ^ 2) < 398.7875) := by
  obtain ⟨al, au⟩ := num10_sd 37.5 0.608761428 0.608761430 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  have hB : 0 < sin (37.5 * π / 180) := by linarith
  have c1 : (502.6599664 : ℝ) < 306 / sin (37.5 * π / 180) := by rw [lt_div_iff₀ hB]; linarith
  have c2 : 306 / sin (37.5 * π / 180) < (502.6599682 : ℝ) := by rw [div_lt_iff₀ hB]; linarith
  generalize 306 / sin (37.5 * π / 180) = c at c1 c2 ⊢
  have hc0 : 0 < c := by linarith
  refine ⟨⟨by linarith, by linarith⟩, ?_, ?_⟩
  · rw [Real.lt_sqrt (by norm_num)]; nlinarith
  · rw [Real.sqrt_lt' (by norm_num)]; nlinarith

end UndergradKB.Precalculus.Course
