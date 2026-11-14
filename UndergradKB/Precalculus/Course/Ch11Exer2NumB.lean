import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 11 (Stitz-Zeager): exercises with the book's answers (wave 7), rounded decimal answers.

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
/-- Stitz-Zeager Exercise 11.8.53: the boat's velocity is the sum of its own `17` mph at `S68°W` and the current `8` mph east, with westward part `N = 17 sin 68° - 8` and southward part `D = 17 cos 68°`. Its speed `√(N² + D²)` is `9.5 < v < 10.5` (about `10`) and the heading `S x W` has `x = arctan (N/D)` between `50.55°` and `50.65°` (about `50.6°`). -/
@[kb "stitzzeager2013" "Exercise 11.8.53, p. 1039"]
theorem exer_11_8_53 :
    ((9.5 : ℝ) < √((17 * sin (68 * π / 180) - 8) ^ 2 + (17 * cos (68 * π / 180)) ^ 2) ∧ √((17 * sin (68 * π / 180) - 8) ^ 2 + (17 * cos (68 * π / 180)) ^ 2) < 10.5) ∧
      ((50.55 : ℝ) < arctan ((17 * sin (68 * π / 180) - 8) / (17 * cos (68 * π / 180))) * 180 / π ∧ arctan ((17 * sin (68 * π / 180) - 8) / (17 * cos (68 * π / 180))) * 180 / π < 50.65) := by
  obtain ⟨s1l, s1u⟩ := num10_sd 68 0.927183608 0.927184058 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c2l, c2u⟩ := num10_cd 68 0.374606472 0.374606823 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨s3l, s3u⟩ := num10_sd 50.55 0.772179188 0.772179502 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c4l, c4u⟩ := num10_cd 50.55 0.635404533 0.635404751 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨s5l, s5u⟩ := num10_sd 50.65 0.773287001 0.773287316 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c6l, c6u⟩ := num10_cd 50.65 0.634055858 0.634056077 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = 17 * sin (68 * π / 180) - 8 := ⟨_, rfl⟩
  obtain ⟨Dn, hD⟩ : ∃ Dn : ℝ, Dn = 17 * cos (68 * π / 180) := ⟨_, rfl⟩
  rw [← hN, ← hD]
  have hNb : 7.7621213 < N ∧ N < 7.7621290 := by rw [hN]; constructor <;> linarith
  have hDb : 6.3683100 < Dn ∧ Dn < 6.3683160 := by rw [hD]; constructor <;> linarith
  obtain ⟨hN1, hN2⟩ := hNb
  obtain ⟨hD1, hD2⟩ := hDb
  have hDp : 0 < Dn := by linarith
  constructor
  · have h1 : (9.500000000 : ℝ) < √(N ^ 2 + Dn ^ 2) := by
      rw [Real.lt_sqrt (by norm_num)]
      nlinarith [sq_nonneg (N - 7.762125), sq_nonneg (Dn - 6.368313)]
    have h2 : √(N ^ 2 + Dn ^ 2) < (10.500000000 : ℝ) := by
      rw [Real.sqrt_lt' (by norm_num)]
      nlinarith [mul_nonneg (sub_nonneg.2 hN1.le) (sub_nonneg.2 hN2.le), mul_nonneg (sub_nonneg.2 hD1.le) (sub_nonneg.2 hD2.le)]
    constructor <;> linarith
  · have ht1 : (1.2188656 : ℝ) < N / Dn := by rw [lt_div_iff₀ hDp]; linarith
    have ht2 : N / Dn < (1.2188680 : ℝ) := by rw [div_lt_iff₀ hDp]; linarith
    have hca : 0 < cos (50.55 * π / 180) := by linarith
    have hcb : 0 < cos (50.65 * π / 180) := by linarith
    have := num10_arctan_deg (t := N / Dn) (a := 50.55) (b := 50.65) (by norm_num) (by norm_num) (by norm_num)
      (by nlinarith [mul_pos (sub_pos.2 ht1) hca]) (by nlinarith [mul_pos (sub_pos.2 ht2) hcb])
    exact this

set_option maxHeartbeats 1600000 in
/-- Stitz-Zeager Exercise 11.8.54: the HMS Sasquatch's velocity is its own `42` mph at `S20°E` plus the `5` mph current at `N60°E`: eastward `N = 42 sin 20° + 5 sin 60°`, southward `D = 42 cos 20° - 5 cos 60°`. The speed `√(N² + D²)` is `40.5 < v < 41.5` (about `41`) and the heading `S x E` has `x = arctan (N/D)` between `26.75°` and `26.85°` (about `26.8°`). -/
@[kb "stitzzeager2013" "Exercise 11.8.54, p. 1041"]
theorem exer_11_8_54 :
    ((40.5 : ℝ) < √((42 * sin (20 * π / 180) + 5 * sin (60 * π / 180)) ^ 2 + (42 * cos (20 * π / 180) - 5 * cos (60 * π / 180)) ^ 2) ∧ √((42 * sin (20 * π / 180) + 5 * sin (60 * π / 180)) ^ 2 + (42 * cos (20 * π / 180) - 5 * cos (60 * π / 180)) ^ 2) < 41.5) ∧
      ((26.75 : ℝ) < arctan ((42 * sin (20 * π / 180) + 5 * sin (60 * π / 180)) / (42 * cos (20 * π / 180) - 5 * cos (60 * π / 180))) * 180 / π ∧ arctan ((42 * sin (20 * π / 180) + 5 * sin (60 * π / 180)) / (42 * cos (20 * π / 180) - 5 * cos (60 * π / 180))) * 180 / π < 26.85) := by
  obtain ⟨s1l, s1u⟩ := num10_sd 20 0.342020070 0.342020184 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨s2l, s2u⟩ := num10_sd 60 0.866025185 0.866025571 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c3l, c3u⟩ := num10_cd 20 0.939692607 0.939692646 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c4l, c4u⟩ := num10_cd 60 0.499999899 0.500000189 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨s5l, s5u⟩ := num10_sd 26.75 0.450098343 0.450098498 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c6l, c6u⟩ := num10_cd 26.75 0.892978920 0.892978988 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨s7l, s7u⟩ := num10_sd 26.85 0.451656199 0.451656354 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c8l, c8u⟩ := num10_cd 26.85 0.892191990 0.892192058 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = 42 * sin (20 * π / 180) + 5 * sin (60 * π / 180) := ⟨_, rfl⟩
  obtain ⟨Dn, hD⟩ : ∃ Dn : ℝ, Dn = 42 * cos (20 * π / 180) - 5 * cos (60 * π / 180) := ⟨_, rfl⟩
  rw [← hN, ← hD]
  have hNb : 18.6949688 < N ∧ N < 18.6949756 := by rw [hN]; constructor <;> linarith
  have hDb : 36.9670885 < Dn ∧ Dn < 36.9670917 := by rw [hD]; constructor <;> linarith
  obtain ⟨hN1, hN2⟩ := hNb
  obtain ⟨hD1, hD2⟩ := hDb
  have hDp : 0 < Dn := by linarith
  constructor
  · have h1 : (40.500000000 : ℝ) < √(N ^ 2 + Dn ^ 2) := by
      rw [Real.lt_sqrt (by norm_num)]
      nlinarith [sq_nonneg (N - 18.694972), sq_nonneg (Dn - 36.967090)]
    have h2 : √(N ^ 2 + Dn ^ 2) < (41.500000000 : ℝ) := by
      rw [Real.sqrt_lt' (by norm_num)]
      nlinarith [mul_nonneg (sub_nonneg.2 hN1.le) (sub_nonneg.2 hN2.le), mul_nonneg (sub_nonneg.2 hD1.le) (sub_nonneg.2 hD2.le)]
    constructor <;> linarith
  · have ht1 : (0.5057192 : ℝ) < N / Dn := by rw [lt_div_iff₀ hDp]; linarith
    have ht2 : N / Dn < (0.5057195 : ℝ) := by rw [div_lt_iff₀ hDp]; linarith
    have hca : 0 < cos (26.75 * π / 180) := by linarith
    have hcb : 0 < cos (26.85 * π / 180) := by linarith
    have := num10_arctan_deg (t := N / Dn) (a := 26.75) (b := 26.85) (by norm_num) (by norm_num) (by norm_num)
      (by nlinarith [mul_pos (sub_pos.2 ht1) hca]) (by nlinarith [mul_pos (sub_pos.2 ht2) hcb])
    exact this

set_option maxHeartbeats 1600000 in
/-- Stitz-Zeager Exercise 11.8.55: to cover `100` miles at `S20°E` in three hours against the `5` mph current at `N60°E`, the ship's own velocity is `(100/3)⟨sin 20°, -cos 20°⟩ - 5⟨sin 60°, cos 60°⟩`: eastward `N = (100/3) sin 20° - 5 sin 60°`, southward `D = (100/3) cos 20° + 5 cos 60°`. Its speed `√(N² + D²)` is `34.5 < v < 35.5` (about `35`) and the heading `S x E` has `x = arctan (N/D)` between `11.75°` and `11.85°` (about `11.8°`). -/
@[kb "stitzzeager2013" "Exercise 11.8.55, p. 1041"]
theorem exer_11_8_55 :
    ((34.5 : ℝ) < √((100 / 3 * sin (20 * π / 180) - 5 * sin (60 * π / 180)) ^ 2 + (100 / 3 * cos (20 * π / 180) + 5 * cos (60 * π / 180)) ^ 2) ∧ √((100 / 3 * sin (20 * π / 180) - 5 * sin (60 * π / 180)) ^ 2 + (100 / 3 * cos (20 * π / 180) + 5 * cos (60 * π / 180)) ^ 2) < 35.5) ∧
      ((11.75 : ℝ) < arctan ((100 / 3 * sin (20 * π / 180) - 5 * sin (60 * π / 180)) / (100 / 3 * cos (20 * π / 180) + 5 * cos (60 * π / 180))) * 180 / π ∧ arctan ((100 / 3 * sin (20 * π / 180) - 5 * sin (60 * π / 180)) / (100 / 3 * cos (20 * π / 180) + 5 * cos (60 * π / 180))) * 180 / π < 11.85) := by
  obtain ⟨s1l, s1u⟩ := num10_sd 20 0.342020070 0.342020184 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨s2l, s2u⟩ := num10_sd 60 0.866025185 0.866025571 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c3l, c3u⟩ := num10_cd 20 0.939692607 0.939692646 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c4l, c4u⟩ := num10_cd 60 0.499999899 0.500000189 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨s5l, s5u⟩ := num10_sd 11.75 0.203641708 0.203641775 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c6l, c6u⟩ := num10_cd 11.75 0.979045467 0.979045482 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨s7l, s7u⟩ := num10_sd 11.85 0.205350153 0.205350221 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c8l, c8u⟩ := num10_cd 11.85 0.978688554 0.978688569 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = 100 / 3 * sin (20 * π / 180) - 5 * sin (60 * π / 180) := ⟨_, rfl⟩
  obtain ⟨Dn, hD⟩ : ∃ Dn : ℝ, Dn = 100 / 3 * cos (20 * π / 180) + 5 * cos (60 * π / 180) := ⟨_, rfl⟩
  rw [← hN, ← hD]
  have hNb : 7.0705411 < N ∧ N < 7.0705469 := by rw [hN]; constructor <;> linarith
  have hDb : 33.8230863 < Dn ∧ Dn < 33.8230892 := by rw [hD]; constructor <;> linarith
  obtain ⟨hN1, hN2⟩ := hNb
  obtain ⟨hD1, hD2⟩ := hDb
  have hDp : 0 < Dn := by linarith
  constructor
  · have h1 : (34.500000000 : ℝ) < √(N ^ 2 + Dn ^ 2) := by
      rw [Real.lt_sqrt (by norm_num)]
      nlinarith [sq_nonneg (N - 7.070544), sq_nonneg (Dn - 33.823087)]
    have h2 : √(N ^ 2 + Dn ^ 2) < (35.500000000 : ℝ) := by
      rw [Real.sqrt_lt' (by norm_num)]
      nlinarith [mul_nonneg (sub_nonneg.2 hN1.le) (sub_nonneg.2 hN2.le), mul_nonneg (sub_nonneg.2 hD1.le) (sub_nonneg.2 hD2.le)]
    constructor <;> linarith
  · have ht1 : (0.2090448 : ℝ) < N / Dn := by rw [lt_div_iff₀ hDp]; linarith
    have ht2 : N / Dn < (0.2090450 : ℝ) := by rw [div_lt_iff₀ hDp]; linarith
    have hca : 0 < cos (11.75 * π / 180) := by linarith
    have hcb : 0 < cos (11.85 * π / 180) := by linarith
    have := num10_arctan_deg (t := N / Dn) (a := 11.75) (b := 11.85) (by norm_num) (by norm_num) (by norm_num)
      (by nlinarith [mul_pos (sub_pos.2 ht1) hca]) (by nlinarith [mul_pos (sub_pos.2 ht2) hcb])
    exact this

set_option maxHeartbeats 1600000 in
/-- Stitz-Zeager Exercise 11.8.56: to fly `96` mph at `N8.2°E` over the ground in a south-east wind of `25` mph (velocity `25⟨-1, 1⟩/√2`), the plane's own velocity has eastward part `N = 96 sin 8.2° + 25√2/2` and northward part `D = 96 cos 8.2° - 25√2/2`. Its speed `√(N² + D²)` is `83.455 < v < 83.465` (about `83.46`) and the heading `N x E` has `x = arctan (N/D)` between `22.05°` and `22.15°` (about `22.1°`). -/
@[kb "stitzzeager2013" "Exercise 11.8.56, p. 1041"]
theorem exer_11_8_56 :
    ((83.455 : ℝ) < √((96 * sin (8.2 * π / 180) + 25 * √2 / 2) ^ 2 + (96 * cos (8.2 * π / 180) - 25 * √2 / 2) ^ 2) ∧ √((96 * sin (8.2 * π / 180) + 25 * √2 / 2) ^ 2 + (96 * cos (8.2 * π / 180) - 25 * √2 / 2) ^ 2) < 83.465) ∧
      ((22.05 : ℝ) < arctan ((96 * sin (8.2 * π / 180) + 25 * √2 / 2) / (96 * cos (8.2 * π / 180) - 25 * √2 / 2)) * 180 / π ∧ arctan ((96 * sin (8.2 * π / 180) + 25 * √2 / 2) / (96 * cos (8.2 * π / 180) - 25 * √2 / 2)) * 180 / π < 22.15) := by
  obtain ⟨s1l, s1u⟩ := num10_sd 8.2 0.142628903 0.142628950 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c2l, c2u⟩ := num10_cd 8.2 0.989776228 0.989776236 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨s3l, s3u⟩ := num10_sd 22.05 0.375415491 0.375415617 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c4l, c4u⟩ := num10_cd 22.05 0.926856579 0.926856626 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨s5l, s5u⟩ := num10_sd 22.15 0.377032588 0.377032715 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c6l, c6u⟩ := num10_cd 22.15 0.926199944 0.926199991 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  have q2l : (1.4142135 : ℝ) < √2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have q2u : √2 < (1.4142136 : ℝ) := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = 96 * sin (8.2 * π / 180) + 25 * √2 / 2 := ⟨_, rfl⟩
  obtain ⟨Dn, hD⟩ : ∃ Dn : ℝ, Dn = 96 * cos (8.2 * π / 180) - 25 * √2 / 2 := ⟨_, rfl⟩
  rw [← hN, ← hD]
  have hNb : 31.3700434 < N ∧ N < 31.3700492 := by rw [hN]; constructor <;> linarith
  have hDb : 77.3408478 < Dn ∧ Dn < 77.3408500 := by rw [hD]; constructor <;> linarith
  obtain ⟨hN1, hN2⟩ := hNb
  obtain ⟨hD1, hD2⟩ := hDb
  have hDp : 0 < Dn := by linarith
  constructor
  · have h1 : (83.455000000 : ℝ) < √(N ^ 2 + Dn ^ 2) := by
      rw [Real.lt_sqrt (by norm_num)]
      nlinarith [sq_nonneg (N - 31.370046), sq_nonneg (Dn - 77.340848)]
    have h2 : √(N ^ 2 + Dn ^ 2) < (83.465000000 : ℝ) := by
      rw [Real.sqrt_lt' (by norm_num)]
      nlinarith [mul_nonneg (sub_nonneg.2 hN1.le) (sub_nonneg.2 hN2.le), mul_nonneg (sub_nonneg.2 hD1.le) (sub_nonneg.2 hD2.le)]
    constructor <;> linarith
  · have ht1 : (0.4056076 : ℝ) < N / Dn := by rw [lt_div_iff₀ hDp]; linarith
    have ht2 : N / Dn < (0.4056078 : ℝ) := by rw [div_lt_iff₀ hDp]; linarith
    have hca : 0 < cos (22.05 * π / 180) := by linarith
    have hcb : 0 < cos (22.15 * π / 180) := by linarith
    have := num10_arctan_deg (t := N / Dn) (a := 22.05) (b := 22.15) (by norm_num) (by norm_num) (by norm_num)
      (by nlinarith [mul_pos (sub_pos.2 ht1) hca]) (by nlinarith [mul_pos (sub_pos.2 ht2) hcb])
    exact this

set_option maxHeartbeats 1600000 in
/-- Stitz-Zeager Exercise 11.8.57: after half an hour the ship should be `25` miles at `N37°W` but is `30` miles at `N40°W`; the displacement has westward part `N = 30 sin 40° - 25 sin 37°` and northward part `D = 30 cos 40° - 25 cos 37°`, so the current has speed `2√(N² + D²)`, between `9.5` and `10.5` (about `10`) mph, and bearing `N x W` with `x = arctan (N/D)` between `54.55°` and `54.65°` (about `54.6°`). -/
@[kb "stitzzeager2013" "Exercise 11.8.57, p. 1041"]
theorem exer_11_8_57 :
    ((9.5 : ℝ) < 2 * √((30 * sin (40 * π / 180) - 25 * sin (37 * π / 180)) ^ 2 + (30 * cos (40 * π / 180) - 25 * cos (37 * π / 180)) ^ 2) ∧ 2 * √((30 * sin (40 * π / 180) - 25 * sin (37 * π / 180)) ^ 2 + (30 * cos (40 * π / 180) - 25 * cos (37 * π / 180)) ^ 2) < 10.5) ∧
      ((54.55 : ℝ) < arctan ((30 * sin (40 * π / 180) - 25 * sin (37 * π / 180)) / (30 * cos (40 * π / 180) - 25 * cos (37 * π / 180))) * 180 / π ∧ arctan ((30 * sin (40 * π / 180) - 25 * sin (37 * π / 180)) / (30 * cos (40 * π / 180) - 25 * cos (37 * π / 180))) * 180 / π < 54.65) := by
  obtain ⟨s1l, s1u⟩ := num10_sd 40 0.642787464 0.642787704 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨s2l, s2u⟩ := num10_sd 37 0.601814888 0.601815108 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c3l, c3u⟩ := num10_cd 40 0.766044393 0.766044537 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c4l, c4u⟩ := num10_cd 37 0.798635467 0.798635591 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨s5l, s5u⟩ := num10_sd 54.55 0.814621768 0.814622112 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c6l, c6u⟩ := num10_cd 54.55 0.579992199 0.579992447 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨s7l, s7u⟩ := num10_sd 54.65 0.815632804 0.815633149 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c8l, c8u⟩ := num10_cd 54.65 0.578569532 0.578569781 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = 30 * sin (40 * π / 180) - 25 * sin (37 * π / 180) := ⟨_, rfl⟩
  obtain ⟨Dn, hD⟩ : ∃ Dn : ℝ, Dn = 30 * cos (40 * π / 180) - 25 * cos (37 * π / 180) := ⟨_, rfl⟩
  rw [← hN, ← hD]
  have hNb : 4.2382462 < N ∧ N < 4.2382590 := by rw [hN]; constructor <;> linarith
  have hDb : 3.0154420 < Dn ∧ Dn < 3.0154495 := by rw [hD]; constructor <;> linarith
  obtain ⟨hN1, hN2⟩ := hNb
  obtain ⟨hD1, hD2⟩ := hDb
  have hDp : 0 < Dn := by linarith
  constructor
  · have h1 : (4.750000000 : ℝ) < √(N ^ 2 + Dn ^ 2) := by
      rw [Real.lt_sqrt (by norm_num)]
      nlinarith [sq_nonneg (N - 4.238252), sq_nonneg (Dn - 3.015445)]
    have h2 : √(N ^ 2 + Dn ^ 2) < (5.250000000 : ℝ) := by
      rw [Real.sqrt_lt' (by norm_num)]
      nlinarith [mul_nonneg (sub_nonneg.2 hN1.le) (sub_nonneg.2 hN2.le), mul_nonneg (sub_nonneg.2 hD1.le) (sub_nonneg.2 hD2.le)]
    constructor <;> linarith
  · have ht1 : (1.4055106 : ℝ) < N / Dn := by rw [lt_div_iff₀ hDp]; linarith
    have ht2 : N / Dn < (1.4055183 : ℝ) := by rw [div_lt_iff₀ hDp]; linarith
    have hca : 0 < cos (54.55 * π / 180) := by linarith
    have hcb : 0 < cos (54.65 * π / 180) := by linarith
    have := num10_arctan_deg (t := N / Dn) (a := 54.55) (b := 54.65) (by norm_num) (by norm_num) (by norm_num)
      (by nlinarith [mul_pos (sub_pos.2 ht1) hca]) (by nlinarith [mul_pos (sub_pos.2 ht2) hcb])
    exact this

set_option maxHeartbeats 1600000 in
/-- Stitz-Zeager Exercise 11.8.62: the three forces `100` (`N80°W`), `40` (due west) and `160` (`S80°W`) have
resultant with westward part `W = 260 sin 80° + 40` and southward part `S = 60 cos 80°`, so its magnitude `√(W² + S²)`
is `295.5 < F < 296.5` (about `296`, under `300`, so the couch does not move) and `S > 0` (it drifts south). -/
@[kb "stitzzeager2013" "Exercise 11.8.62, p. 1042"]
theorem exer_11_8_62 :
    (295.5 : ℝ) < √((260 * sin (80 * π / 180) + 40) ^ 2 + (60 * cos (80 * π / 180)) ^ 2) ∧
      √((260 * sin (80 * π / 180) + 40) ^ 2 + (60 * cos (80 * π / 180)) ^ 2) < 296.5 ∧
      0 < 60 * cos (80 * π / 180) := by
  obtain ⟨sl, su⟩ := num10_sd 80 0.984807466 0.984808017 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨cl, cu⟩ := num10_cd 80 0.173648026 0.173648464 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = 260 * sin (80 * π / 180) + 40 := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = 60 * cos (80 * π / 180) := ⟨_, rfl⟩
  rw [← hW, ← hS]
  have hW1 : 296.0499 < W := by rw [hW]; linarith
  have hW2 : W < 296.0501 := by rw [hW]; linarith
  have hS1 : 10.4188 < S := by rw [hS]; linarith
  have hS2 : S < 10.4190 := by rw [hS]; linarith
  refine ⟨?_, ?_, by linarith⟩
  · rw [Real.lt_sqrt (by norm_num)]
    nlinarith [sq_nonneg (W - 296.05), sq_nonneg (S - 10.4189)]
  · rw [Real.sqrt_lt' (by norm_num)]
    nlinarith [mul_nonneg (sub_nonneg.2 hW1.le) (sub_nonneg.2 hW2.le), mul_nonneg (sub_nonneg.2 hS1.le) (sub_nonneg.2 hS2.le)]

end UndergradKB.Precalculus.Course
