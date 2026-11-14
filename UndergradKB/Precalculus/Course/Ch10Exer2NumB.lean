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
/-- Stitz-Zeager Exercise 10.3.35: `csc 78.95° ≈ 1.019` (three decimals), as `1.0185 < 1 / sin 78.95° < 1.0195`. -/
@[kb "stitzzeager2013" "Exercise 10.3.35, p. 771"]
theorem exer_10_3_35 :
    (1.0185 : ℝ) < 1 / sin (78.95 * π / 180) ∧ 1 / sin (78.95 * π / 180) < 1.0195 := by
  obtain ⟨al, au⟩ := num10_sd 78.95 0.981460296 0.981460298 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  have hB : 0 < sin (78.95 * π / 180) := by linarith
  constructor
  · rw [lt_div_iff₀ hB]; linarith
  · rw [div_lt_iff₀ hB]; linarith

set_option maxHeartbeats 1600000 in
/-- Stitz-Zeager Exercise 10.3.36: `tan (-2.01) ≈ 2.129` (radians; the exact value is just above `2.1285`), as `2.1285 < tan (-2.01) < 2.1295`. -/
@[kb "stitzzeager2013" "Exercise 10.3.36, p. 771"]
theorem exer_10_3_36 :
    (2.1285 : ℝ) < tan (-2.01) ∧ tan (-2.01) < 2.1295 := by
  rw [tan_neg, tan_eq_sin_div_cos, show -(sin 2.01 / cos 2.01) = sin 2.01 / (-cos 2.01) by ring]
  obtain ⟨al, au⟩ := num10_rs (x := 2.01) (xl := 2.01) (xu := 2.01) (lo := 0.905090562) (hi := 0.905090564) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨bl, bu⟩ := num10_rc (x := 2.01) (xl := 2.01) (xu := 2.01) (lo := (-0.425218853)) (hi := (-0.425218851)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  have hB : 0 < -cos 2.01 := by linarith
  constructor
  · rw [lt_div_iff₀ hB]; linarith
  · rw [div_lt_iff₀ hB]; linarith

set_option maxHeartbeats 1600000 in
/-- Stitz-Zeager Exercise 10.3.37: `cot 392.994 ≈ 3.292` (radians), as `3.2915 < cos 392.994 / sin 392.994 < 3.2925`. -/
@[kb "stitzzeager2013" "Exercise 10.3.37, p. 771"]
theorem exer_10_3_37 :
    (3.2915 : ℝ) < cos 392.994 / sin 392.994 ∧ cos 392.994 / sin 392.994 < 3.2925 := by
  have p1 := pi_gt_d20
  have p2 := pi_lt_d20
  rw [show (392.994 : ℝ) = (392.994 - 125 * π) + π + ((62 : ℕ) : ℝ) * (2 * π) by push_cast; ring,
    sin_add_nat_mul_two_pi, cos_add_nat_mul_two_pi, sin_add_pi, cos_add_pi, neg_div_neg_eq]
  obtain ⟨al, au⟩ := num10_rs (x := 392.994 - 125 * π) (xl := 0.294918301) (xu := 0.294918302) (lo := 0.290661679) (hi := 0.290661681) (by norm_num) (by linarith) (by linarith) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨bl, bu⟩ := num10_rc (x := 392.994 - 125 * π) (xl := 0.294918301) (xu := 0.294918302) (lo := 0.956825891) (hi := 0.956825893) (by norm_num) (by linarith) (by linarith) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  have hB : 0 < sin (392.994 - 125 * π) := by linarith
  constructor
  · rw [lt_div_iff₀ hB]; linarith
  · rw [div_lt_iff₀ hB]; linarith

set_option maxHeartbeats 1600000 in
/-- Stitz-Zeager Exercise 10.3.38: `sec 207° ≈ -1.122`, as `-1.1225 < 1 / cos 207° < -1.1215`. -/
@[kb "stitzzeager2013" "Exercise 10.3.38, p. 771"]
theorem exer_10_3_38 :
    (-1.1225 : ℝ) < 1 / cos (207 * π / 180) ∧ 1 / cos (207 * π / 180) < -1.1215 := by
  rw [show 1 / cos (207 * π / 180) = -(1 / cos (27 * π / 180)) by
    rw [show (207 : ℝ) * π / 180 = 27 * π / 180 + π by ring, cos_add_pi]; ring]
  obtain ⟨al, au⟩ := num10_cd 27 0.891006524 0.891006525 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  have hB : 0 < cos (27 * π / 180) := by linarith
  have h1 : 1 / cos (27 * π / 180) < 1.1225 := by rw [div_lt_iff₀ hB]; linarith
  have h2 : 1.1215 < 1 / cos (27 * π / 180) := by rw [lt_div_iff₀ hB]; linarith
  constructor <;> linarith

set_option maxHeartbeats 1600000 in
/-- Stitz-Zeager Exercise 10.3.39: `csc 5.902 ≈ -2.688` (radians; `5.902 = 2π - 0.3811...`), as `-2.6885 < 1 / sin 5.902 < -2.6875`. -/
@[kb "stitzzeager2013" "Exercise 10.3.39, p. 771"]
theorem exer_10_3_39 :
    (-2.6885 : ℝ) < 1 / sin 5.902 ∧ 1 / sin 5.902 < -2.6875 := by
  have p1 := pi_gt_d20
  have p2 := pi_lt_d20
  have e : 1 / sin 5.902 = -(1 / sin (2 * π - 5.902)) := by
    have := sin_two_pi_sub (5.902 : ℝ)
    rw [this]; ring
  rw [e]
  obtain ⟨al, au⟩ := num10_rs (x := 2 * π - 5.902) (xl := 0.381185307) (xu := 0.381185308) (lo := 0.372020961) (hi := 0.372020963) (by norm_num) (by linarith) (by linarith) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  have hB : 0 < sin (2 * π - 5.902) := by linarith
  have h1 : 1 / sin (2 * π - 5.902) < 2.6885 := by rw [div_lt_iff₀ hB]; linarith
  have h2 : 2.6875 < 1 / sin (2 * π - 5.902) := by rw [lt_div_iff₀ hB]; linarith
  constructor <;> linarith

set_option maxHeartbeats 1600000 in
/-- Stitz-Zeager Exercise 10.3.40: `tan 39.672° ≈ 0.829`, as `0.8285 < tan 39.672° < 0.8295`. -/
@[kb "stitzzeager2013" "Exercise 10.3.40, p. 771"]
theorem exer_10_3_40 :
    (0.8285 : ℝ) < tan (39.672 * π / 180) ∧ tan (39.672 * π / 180) < 0.8295 := by
  rw [tan_eq_sin_div_cos]
  obtain ⟨al, au⟩ := num10_sd 39.672 0.638391741 0.638391742 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨bl, bu⟩ := num10_cd 39.672 0.769711623 0.769711625 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  have hB : 0 < cos (39.672 * π / 180) := by linarith
  constructor
  · rw [lt_div_iff₀ hB]; linarith
  · rw [div_lt_iff₀ hB]; linarith

set_option maxHeartbeats 1600000 in
/-- Stitz-Zeager Exercise 10.3.41: `cot 3° ≈ 19.081`, as `19.0805 < cos 3° / sin 3° < 19.0815`. -/
@[kb "stitzzeager2013" "Exercise 10.3.41, p. 771"]
theorem exer_10_3_41 :
    (19.0805 : ℝ) < cos (3 * π / 180) / sin (3 * π / 180) ∧ cos (3 * π / 180) / sin (3 * π / 180) < 19.0815 := by
  obtain ⟨al, au⟩ := num10_sd 3 0.052335956 0.052335957 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨bl, bu⟩ := num10_cd 3 0.998629534 0.998629535 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  have hB : 0 < sin (3 * π / 180) := by linarith
  constructor
  · rw [lt_div_iff₀ hB]; linarith
  · rw [div_lt_iff₀ hB]; linarith

set_option maxHeartbeats 1600000 in
/-- Stitz-Zeager Exercise 10.3.42: `sec 0.45 ≈ 1.111` (radians), as `1.1105 < 1 / cos 0.45 < 1.1115`. -/
@[kb "stitzzeager2013" "Exercise 10.3.42, p. 771"]
theorem exer_10_3_42 :
    (1.1105 : ℝ) < 1 / cos 0.45 ∧ 1 / cos 0.45 < 1.1115 := by
  obtain ⟨al, au⟩ := num10_rc (x := 0.45) (xl := 0.45) (xu := 0.45) (lo := 0.900447102) (hi := 0.900447103) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  have hB : 0 < cos 0.45 := by linarith
  constructor
  · rw [lt_div_iff₀ hB]; linarith
  · rw [div_lt_iff₀ hB]; linarith

set_option maxHeartbeats 1600000 in
/-- Stitz-Zeager Exercise 10.3.72: the opposite side `2 tan 87° ≈ 38.162` (three decimals). -/
@[kb "stitzzeager2013" "Exercise 10.3.72, p. 773"]
theorem exer_10_3_72 :
    (38.1615 : ℝ) < 2 * tan (87 * π / 180) ∧ 2 * tan (87 * π / 180) < 38.1625 := by
  rw [tan_eq_sin_div_cos, show 2 * (sin (87 * π / 180) / cos (87 * π / 180)) = (2 * sin (87 * π / 180)) / cos (87 * π / 180) by ring]
  obtain ⟨al, au⟩ := num10_sd 87 0.998629534 0.998629536 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨bl, bu⟩ := num10_cd 87 0.052335956 0.052335957 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  have hB : 0 < cos (87 * π / 180) := by linarith
  constructor
  · rw [lt_div_iff₀ hB]; linarith
  · rw [div_lt_iff₀ hB]; linarith

set_option maxHeartbeats 1600000 in
/-- Stitz-Zeager Exercise 10.3.73: the hypotenuse `14 csc 38.2° = 14 / sin 38.2° ≈ 22.639` (three decimals). -/
@[kb "stitzzeager2013" "Exercise 10.3.73, p. 773"]
theorem exer_10_3_73 :
    (22.6385 : ℝ) < 14 / sin (38.2 * π / 180) ∧ 14 / sin (38.2 * π / 180) < 22.6395 := by
  obtain ⟨al, au⟩ := num10_sd 38.2 0.618408395 0.618408396 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  have hB : 0 < sin (38.2 * π / 180) := by linarith
  constructor
  · rw [lt_div_iff₀ hB]; linarith
  · rw [div_lt_iff₀ hB]; linarith

set_option maxHeartbeats 1600000 in
/-- Stitz-Zeager Exercise 10.3.74: the adjacent side `3.98 cos 2.05° ≈ 3.977` (three decimals). -/
@[kb "stitzzeager2013" "Exercise 10.3.74, p. 773"]
theorem exer_10_3_74 :
    (3.9765 : ℝ) < 3.98 * cos (2.05 * π / 180) ∧ 3.98 * cos (2.05 * π / 180) < 3.9775 := by
  obtain ⟨al, au⟩ := num10_cd 2.05 0.999359990 0.999359991 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  constructor <;> linarith

set_option maxHeartbeats 1600000 in
/-- Stitz-Zeager Exercise 10.3.75: the opposite side `31 tan 42°` is about `27.9125`, so to three decimals `27.913` (the book prints `27.912`), as `27.9125 < 31 tan 42° < 27.9135`. -/
@[kb "stitzzeager2013" "Exercise 10.3.75, p. 773"]
theorem exer_10_3_75 :
    (27.9125 : ℝ) < 31 * tan (42 * π / 180) ∧ 31 * tan (42 * π / 180) < 27.9135 := by
  rw [tan_eq_sin_div_cos, show 31 * (sin (42 * π / 180) / cos (42 * π / 180)) = (31 * sin (42 * π / 180)) / cos (42 * π / 180) by ring]
  obtain ⟨al, au⟩ := num10_sd 42 0.669130606 0.669130607 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨bl, bu⟩ := num10_cd 42 0.743144825 0.743144826 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  have hB : 0 < cos (42 * π / 180) := by linarith
  constructor
  · rw [lt_div_iff₀ hB]; linarith
  · rw [div_lt_iff₀ hB]; linarith

set_option maxHeartbeats 1600000 in
/-- Stitz-Zeager Exercise 10.3.76: the tree's height `120 tan 21.4°` is about `47` feet (nearest foot). -/
@[kb "stitzzeager2013" "Exercise 10.3.76, p. 773"]
theorem exer_10_3_76 :
    (46.5 : ℝ) < 120 * tan (21.4 * π / 180) ∧ 120 * tan (21.4 * π / 180) < 47.5 := by
  rw [tan_eq_sin_div_cos, show 120 * (sin (21.4 * π / 180) / cos (21.4 * π / 180)) = (120 * sin (21.4 * π / 180)) / cos (21.4 * π / 180) by ring]
  obtain ⟨al, au⟩ := num10_sd 21.4 0.364876784 0.364876785 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨bl, bu⟩ := num10_cd 21.4 0.931055815 0.931055816 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  have hB : 0 < cos (21.4 * π / 180) := by linarith
  constructor
  · rw [lt_div_iff₀ hB]; linarith
  · rw [div_lt_iff₀ hB]; linarith

set_option maxHeartbeats 1600000 in
/-- Stitz-Zeager Exercise 10.3.77: the lights are `5000 (tan 7.970° - tan 7.125°)` feet apart, about `75` (nearest foot). -/
@[kb "stitzzeager2013" "Exercise 10.3.77, p. 773"]
theorem exer_10_3_77 :
    (74.5 : ℝ) < 5000 * (tan (7.970 * π / 180) - tan (7.125 * π / 180)) ∧ 5000 * (tan (7.970 * π / 180) - tan (7.125 * π / 180)) < 75.5 := by
  obtain ⟨s1l, s1u⟩ := num10_sd 7.970 0.138654578 0.138654579 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c1l, c1u⟩ := num10_cd 7.970 0.990340803 0.990340804 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨s2l, s2u⟩ := num10_sd 7.125 0.124034451 0.124034452 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c2l, c2u⟩ := num10_cd 7.125 0.992277912 0.992277913 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  have hc1 : 0 < cos (7.970 * π / 180) := by linarith
  have t1l : (0.140006 : ℝ) < tan (7.970 * π / 180) := by rw [tan_eq_sin_div_cos, lt_div_iff₀ hc1]; linarith
  have t1u : tan (7.970 * π / 180) < (0.140007 : ℝ) := by rw [tan_eq_sin_div_cos, div_lt_iff₀ hc1]; linarith
  have hc2 : 0 < cos (7.125 * π / 180) := by linarith
  have t2l : (0.124999 : ℝ) < tan (7.125 * π / 180) := by rw [tan_eq_sin_div_cos, lt_div_iff₀ hc2]; linarith
  have t2u : tan (7.125 * π / 180) < (0.125000 : ℝ) := by rw [tan_eq_sin_div_cos, div_lt_iff₀ hc2]; linarith
  constructor <;> linarith

set_option maxHeartbeats 1600000 in
/-- Stitz-Zeager Exercise 10.3.78 (b): a fire seen at depression `2.5°` from a `200` foot tower is `200 / tan 2.5°` feet away, about `4581` (nearest foot). -/
@[kb "stitzzeager2013" "Exercise 10.3.78, p. 774"]
theorem exer_10_3_78_b :
    (4580.5 : ℝ) < 200 / tan (2.5 * π / 180) ∧ 200 / tan (2.5 * π / 180) < 4581.5 := by
  rw [tan_eq_sin_div_cos, div_div_eq_mul_div]
  obtain ⟨al, au⟩ := num10_sd 2.5 0.043619387 0.043619388 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨bl, bu⟩ := num10_cd 2.5 0.999048221 0.999048222 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  have hB : 0 < sin (2.5 * π / 180) := by linarith
  constructor
  · rw [lt_div_iff₀ hB]; linarith
  · rw [div_lt_iff₀ hB]; linarith

set_option maxHeartbeats 1600000 in
/-- Stitz-Zeager Exercise 10.3.78 (c): the Sasquatch travelled `200 cot 6° - 200 cot 6.5°` feet in ten seconds, about `147`; it was `200 cot 6.5°` about `1755` feet from the tower; its speed (feet per ten seconds to miles per hour) is about `10`, and the remaining time in minutes is about `2`. -/
@[kb "stitzzeager2013" "Exercise 10.3.78, p. 774"]
theorem exer_10_3_78_c :
    ((146.5 : ℝ) < 200 / tan (6 * π / 180) - 200 / tan (6.5 * π / 180) ∧ 200 / tan (6 * π / 180) - 200 / tan (6.5 * π / 180) < 147.5) ∧
      ((1754.5 : ℝ) < 200 / tan (6.5 * π / 180) ∧ 200 / tan (6.5 * π / 180) < 1755.5) ∧
      ((9.5 : ℝ) < (200 / tan (6 * π / 180) - 200 / tan (6.5 * π / 180)) / 10 * 3600 / 5280 ∧ (200 / tan (6 * π / 180) - 200 / tan (6.5 * π / 180)) / 10 * 3600 / 5280 < 10.5) ∧
      ((1.5 : ℝ) < (200 / tan (6.5 * π / 180)) / ((200 / tan (6 * π / 180) - 200 / tan (6.5 * π / 180)) / 10) / 60 ∧ (200 / tan (6.5 * π / 180)) / ((200 / tan (6 * π / 180) - 200 / tan (6.5 * π / 180)) / 10) / 60 < 2.5) := by
  obtain ⟨s1l, s1u⟩ := num10_sd 6 0.104528463 0.104528464 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c1l, c1u⟩ := num10_cd 6 0.994521895 0.994521896 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨s2l, s2u⟩ := num10_sd 6.5 0.113203213 0.113203214 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c2l, c2u⟩ := num10_cd 6.5 0.993571855 0.993571856 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  have hs1 : 0 < sin (6 * π / 180) := by linarith
  have x1l : (1902.87287 : ℝ) < 200 / tan (6 * π / 180) := by rw [tan_eq_sin_div_cos, div_div_eq_mul_div, lt_div_iff₀ hs1]; linarith
  have x1u : 200 / tan (6 * π / 180) < (1902.87290 : ℝ) := by rw [tan_eq_sin_div_cos, div_div_eq_mul_div, div_lt_iff₀ hs1]; linarith
  have hs2 : 0 < sin (6.5 * π / 180) := by linarith
  have x2l : (1755.37746 : ℝ) < 200 / tan (6.5 * π / 180) := by rw [tan_eq_sin_div_cos, div_div_eq_mul_div, lt_div_iff₀ hs2]; linarith
  have x2u : 200 / tan (6.5 * π / 180) < (1755.37749 : ℝ) := by rw [tan_eq_sin_div_cos, div_div_eq_mul_div, div_lt_iff₀ hs2]; linarith
  generalize 200 / tan (6 * π / 180) = X1 at x1l x1u ⊢
  generalize 200 / tan (6.5 * π / 180) = X2 at x2l x2u ⊢
  have hY : 0 < (X1 - X2) / 10 * 60 := by linarith
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ?_, ?_⟩
  · rw [div_div, lt_div_iff₀ (by linarith)]; linarith
  · rw [div_div, div_lt_iff₀ (by linarith)]; linarith

set_option maxHeartbeats 6400000 in
/-- Stitz-Zeager Exercise 10.6.208: the acute angles of the `3, 4, 5` right triangle are `arctan (3/4) ≈ 36.87°` and `arctan (4/3) ≈ 53.13°` (two decimals). -/
@[kb "stitzzeager2013" "Exercise 10.6.208, p. 858"]
theorem exer_10_6_208 :
    ((36.865 : ℝ) < arctan (3 / 4) * 180 / π ∧ arctan (3 / 4) * 180 / π < 36.875) ∧
      ((53.125 : ℝ) < arctan (4 / 3) * 180 / π ∧ arctan (4 / 3) * 180 / π < 53.135) := by
  obtain ⟨a0l, a0u⟩ := num10_sd 36.865 0.599931613 0.599931614 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨b0l, b0u⟩ := num10_cd 36.865 0.800051285 0.800051286 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c0l, c0u⟩ := num10_sd 36.875 0.600071239 0.600071241 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨d0l, d0u⟩ := num10_cd 36.875 0.799946565 0.799946566 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨a1l, a1u⟩ := num10_sd 53.125 0.799946564 0.799946566 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨b1l, b1u⟩ := num10_cd 53.125 0.600071239 0.600071241 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c1l, c1u⟩ := num10_sd 53.135 0.800051284 0.800051286 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨d1l, d1u⟩ := num10_cd 53.135 0.599931613 0.599931614 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  have h0 := num10_arctan_deg (t := 3 / 4) (a := 36.865) (b := 36.875) (by norm_num) (by norm_num) (by norm_num)
    (by linarith) (by linarith)
  have h1 := num10_arctan_deg (t := 4 / 3) (a := 53.125) (b := 53.135) (by norm_num) (by norm_num) (by norm_num)
    (by linarith) (by linarith)
  exact ⟨h0, h1⟩

set_option maxHeartbeats 6400000 in
/-- Stitz-Zeager Exercise 10.6.209: the acute angles of the `5, 12, 13` right triangle are `arctan (5/12) ≈ 22.62°` and `arctan (12/5) ≈ 67.38°` (two decimals). -/
@[kb "stitzzeager2013" "Exercise 10.6.209, p. 858"]
theorem exer_10_6_209 :
    ((22.615 : ℝ) < arctan (5 / 12) * 180 / π ∧ arctan (5 / 12) * 180 / π < 22.625) ∧
      ((67.375 : ℝ) < arctan (12 / 5) * 180 / π ∧ arctan (12 / 5) * 180 / π < 67.385) := by
  obtain ⟨a0l, a0u⟩ := num10_sd 22.615 0.384537005 0.384537006 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨b0l, b0u⟩ := num10_cd 22.615 0.923109577 0.923109578 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c0l, c0u⟩ := num10_sd 22.625 0.384698112 0.384698113 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨d0l, d0u⟩ := num10_cd 22.625 0.923042448 0.923042449 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨a1l, a1u⟩ := num10_sd 67.375 0.923042448 0.923042449 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨b1l, b1u⟩ := num10_cd 67.375 0.384698112 0.384698113 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c1l, c1u⟩ := num10_sd 67.385 0.923109576 0.923109578 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨d1l, d1u⟩ := num10_cd 67.385 0.384537005 0.384537006 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  have h0 := num10_arctan_deg (t := 5 / 12) (a := 22.615) (b := 22.625) (by norm_num) (by norm_num) (by norm_num)
    (by linarith) (by linarith)
  have h1 := num10_arctan_deg (t := 12 / 5) (a := 67.375) (b := 67.385) (by norm_num) (by norm_num) (by norm_num)
    (by linarith) (by linarith)
  exact ⟨h0, h1⟩

set_option maxHeartbeats 6400000 in
/-- Stitz-Zeager Exercise 10.6.210: the acute angles of the `336, 527, 625` right triangle are `arctan (336/527) ≈ 32.52°` and `arctan (527/336) ≈ 57.48°` (two decimals). -/
@[kb "stitzzeager2013" "Exercise 10.6.210, p. 858"]
theorem exer_10_6_210 :
    ((32.515 : ℝ) < arctan (336 / 527) * 180 / π ∧ arctan (336 / 527) * 180 / π < 32.525) ∧
      ((57.475 : ℝ) < arctan (527 / 336) * 180 / π ∧ arctan (527 / 336) * 180 / π < 57.485) := by
  obtain ⟨a0l, a0u⟩ := num10_sd 32.515 0.537520389 0.537520390 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨b0l, b0u⟩ := num10_cd 32.515 0.843250752 0.843250753 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c0l, c0u⟩ := num10_sd 32.525 0.537667556 0.537667557 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨d0l, d0u⟩ := num10_cd 32.525 0.843156924 0.843156925 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨a1l, a1u⟩ := num10_sd 57.475 0.843156924 0.843156925 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨b1l, b1u⟩ := num10_cd 57.475 0.537667556 0.537667557 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c1l, c1u⟩ := num10_sd 57.485 0.843250751 0.843250753 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨d1l, d1u⟩ := num10_cd 57.485 0.537520389 0.537520390 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  have h0 := num10_arctan_deg (t := 336 / 527) (a := 32.515) (b := 32.525) (by norm_num) (by norm_num) (by norm_num)
    (by linarith) (by linarith)
  have h1 := num10_arctan_deg (t := 527 / 336) (a := 57.475) (b := 57.485) (by norm_num) (by norm_num) (by norm_num)
    (by linarith) (by linarith)
  exact ⟨h0, h1⟩

set_option maxHeartbeats 6400000 in
/-- Stitz-Zeager Exercise 10.6.211: a `1000` foot guy wire reaching the ground `360` feet from the tower makes the angle `arccos (360/1000) ≈ 68.9°` with the ground. -/
@[kb "stitzzeager2013" "Exercise 10.6.211, p. 858"]
theorem exer_10_6_211 :
    (68.85 : ℝ) < arccos (360 / 1000) * 180 / π ∧ arccos (360 / 1000) * 180 / π < 68.95 := by
  obtain ⟨b0l, b0u⟩ := num10_cd 68.85 0.360810826 0.360810827 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨d0l, d0u⟩ := num10_cd 68.95 0.359182515 0.359182516 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  have := num10_arccos_deg (q := 360 / 1000) (a := 68.85) (b := 68.95) (by norm_num) (by norm_num) (by norm_num)
    (by linarith) (by linarith)
  exact this

set_option maxHeartbeats 6400000 in
/-- Stitz-Zeager Exercise 10.6.212: the angle of depression of a fire `10` miles (`52800` feet) from the base of a `7117` foot canyon wall is `arctan (7117/52800) ≈ 7.7°`. -/
@[kb "stitzzeager2013" "Exercise 10.6.212, p. 858"]
theorem exer_10_6_212 :
    (7.65 : ℝ) < arctan (7117 / 52800) * 180 / π ∧ arctan (7117 / 52800) * 180 / π < 7.75 := by
  obtain ⟨a0l, a0u⟩ := num10_sd 7.65 0.133121338 0.133121339 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨b0l, b0u⟩ := num10_cd 7.65 0.991099747 0.991099748 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c0l, c0u⟩ := num10_sd 7.75 0.134850930 0.134850931 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨d0l, d0u⟩ := num10_cd 7.75 0.990865897 0.990865898 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  have := num10_arctan_deg (t := 7117 / 52800) (a := 7.65) (b := 7.75) (by norm_num) (by norm_num) (by norm_num)
    (by linarith) (by linarith)
  exact this

set_option maxHeartbeats 6400000 in
/-- Stitz-Zeager Exercise 10.6.213: an `18` inch rod under a `14` inch deep shelf makes the angle `arcsin (14/18) ≈ 51°` with the wall (nearest degree). -/
@[kb "stitzzeager2013" "Exercise 10.6.213, p. 858"]
theorem exer_10_6_213 :
    (50.5 : ℝ) < arcsin (14 / 18) * 180 / π ∧ arcsin (14 / 18) * 180 / π < 51.5 := by
  obtain ⟨a0l, a0u⟩ := num10_sd 50.5 0.771624583 0.771624584 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c0l, c0u⟩ := num10_sd 51.5 0.782608156 0.782608158 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  have := num10_arcsin_deg (q := 14 / 18) (a := 50.5) (b := 51.5) (by norm_num) (by norm_num) (by norm_num)
    (by linarith) (by linarith)
  exact this

set_option maxHeartbeats 6400000 in
/-- Stitz-Zeager Exercise 10.6.214: a `300` foot cable with the parasailor `100` feet up makes the angle `arcsin (100/300) ≈ 19.5°` with the water. -/
@[kb "stitzzeager2013" "Exercise 10.6.214, p. 858"]
theorem exer_10_6_214 :
    (19.45 : ℝ) < arcsin (100 / 300) * 180 / π ∧ arcsin (100 / 300) * 180 / π < 19.55 := by
  obtain ⟨a0l, a0u⟩ := num10_sd 19.45 0.332984122 0.332984123 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c0l, c0u⟩ := num10_sd 19.55 0.334629341 0.334629342 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  have := num10_arcsin_deg (q := 100 / 300) (a := 19.45) (b := 19.55) (by norm_num) (by norm_num) (by norm_num)
    (by linarith) (by linarith)
  exact this

set_option maxHeartbeats 6400000 in
/-- Stitz-Zeager Exercise 10.6.215: from a `200` foot tower with a `300` foot range the smallest angle of depression is `arcsin (200/300) ≈ 41.81°` (two decimals). -/
@[kb "stitzzeager2013" "Exercise 10.6.215, p. 858"]
theorem exer_10_6_215 :
    (41.805 : ℝ) < arcsin (200 / 300) * 180 / π ∧ arcsin (200 / 300) * 180 / π < 41.815 := by
  obtain ⟨a0l, a0u⟩ := num10_sd 41.805 0.666597522 0.666597523 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c0l, c0u⟩ := num10_sd 41.815 0.666727612 0.666727613 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  have := num10_arcsin_deg (q := 200 / 300) (a := 41.805) (b := 41.815) (by norm_num) (by norm_num) (by norm_num)
    (by linarith) (by linarith)
  exact this

end UndergradKB.Precalculus.Course
