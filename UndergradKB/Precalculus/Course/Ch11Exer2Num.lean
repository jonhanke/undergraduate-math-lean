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
/-- Stitz-Zeager Exercise 11.2.30: the lodge is `d = 2 sin 60° / sin 35°` miles from the hiker (triangle angles
`60°`, `85°`, `35°`, law of sines); the book's `3.02` is `3.015 < d < 3.025`. -/
@[kb "stitzzeager2013" "Exercise 11.2.30, p. 918"]
theorem exer_11_2_30 :
    (3.015 : ℝ) < 2 * sin (π / 3) / sin (7 * π / 36) ∧ 2 * sin (π / 3) / sin (7 * π / 36) < 3.025 := by
  have h3 : sin (π / 3) = √3 / 2 := Real.sin_pi_div_three
  have s3l : 1.7320 < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have s3u : √3 < 1.7321 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have e : 7 * π / 36 = 35 * π / 180 := by ring
  obtain ⟨a, b⟩ := num10_sd 35 0.5735 0.5737 (by norm_num) (by norm_num) (by norm_num [nBaseOk, nOk, nIt, nStep, nBase])
    (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  rw [e, h3]
  have hpos : 0 < sin (35 * π / 180) := by linarith
  constructor
  · rw [lt_div_iff₀ hpos]; nlinarith
  · rw [div_lt_iff₀ hpos]; nlinarith

/-- Stitz-Zeager Exercise 11.3.21 (bearing part): with `d` the distance of Exercise 11.3.20 (law of cosines at the
`103.3°` angle), the angle `β` at Bigfoot Falls satisfies `cos β = (207² + d² - 192²)/(2·207·d)`, and the bearing
`N θ W` from Bigfoot Falls to Cliffs of Insanity Point has `θ = 68.5° - β`. The book prints `31.8°`, but `θ` is
about `31.854°`, so the correct rounding is `31.9°`: `31.85 < θ < 31.95`. -/
@[kb "stitzzeager2013" "Exercise 11.3.21, p. 928"]
theorem exer_11_3_21 :
    (31.85 : ℝ) < 68.5 - arccos ((207 ^ 2 + (√(192 ^ 2 + 207 ^ 2 - 2 * 192 * 207 * cos (103.3 * π / 180))) ^ 2 - 192 ^ 2) /
        (2 * 207 * √(192 ^ 2 + 207 ^ 2 - 2 * 192 * 207 * cos (103.3 * π / 180)))) * 180 / π ∧
      68.5 - arccos ((207 ^ 2 + (√(192 ^ 2 + 207 ^ 2 - 2 * 192 * 207 * cos (103.3 * π / 180))) ^ 2 - 192 ^ 2) /
        (2 * 207 * √(192 ^ 2 + 207 ^ 2 - 2 * 192 * 207 * cos (103.3 * π / 180)))) * 180 / π < 31.95 := by
  have hc : cos (103.3 * π / 180) = -sin (13.3 * π / 180) := by
    rw [show 103.3 * π / 180 = 13.3 * π / 180 + π / 2 by ring, cos_add_pi_div_two]
  obtain ⟨a, b⟩ := num10_sd 13.3 0.230049 0.230051 (by norm_num) (by norm_num) (by norm_num [nBaseOk, nOk, nIt, nStep, nBase])
    (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  rw [hc]
  set s := sin (13.3 * π / 180) with hs
  have hD0 : 0 ≤ (192 : ℝ) ^ 2 + 207 ^ 2 - 2 * 192 * 207 * -s := by nlinarith
  set d := √((192 : ℝ) ^ 2 + 207 ^ 2 - 2 * 192 * 207 * -s) with hd
  have hd2 : d ^ 2 = (192 : ℝ) ^ 2 + 207 ^ 2 - 2 * 192 * 207 * -s := sq_sqrt hD0
  have dl : 313.048 < d := by rw [hd, Real.lt_sqrt (by norm_num)]; nlinarith
  have du : d < 313.0485 := by rw [hd, Real.sqrt_lt' (by norm_num)]; nlinarith
  set q := (207 ^ 2 + d ^ 2 - 192 ^ 2) / (2 * 207 * d) with hq
  have hdp : 0 < 2 * 207 * d := by positivity
  have ql : 0.80231 < q := by rw [hq, lt_div_iff₀ hdp]; nlinarith
  have qu : q < 0.80236 := by rw [hq, div_lt_iff₀ hdp]; nlinarith
  obtain ⟨c1, c2⟩ := num10_cd 36.65 0.80229 0.80230 (by norm_num) (by norm_num) (by norm_num [nBaseOk, nOk, nIt, nStep, nBase])
    (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c3, c4⟩ := num10_cd 36.55 0.80333 0.80334 (by norm_num) (by norm_num) (by norm_num [nBaseOk, nOk, nIt, nStep, nBase])
    (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  have := num10_arccos_deg (q := q) (a := 36.55) (b := 36.65) (by norm_num) (by norm_num) (by norm_num)
    (by linarith) (by linarith)
  constructor <;> linarith [this.1, this.2]

/-- Stitz-Zeager Exercise 11.3.22 (bearing part): with `d` the distance from the lodge (law of cosines at `117°`),
the angle `β` at the end of the hike has `cos β = (3² + d² - 1.5²)/(2·3·d)`, and the bearing back to the lodge is
`N θ E` with `θ = 17° + β`; the book's `37°` is `36.5 < θ < 37.5`. -/
@[kb "stitzzeager2013" "Exercise 11.3.22, p. 929"]
theorem exer_11_3_22_bearing :
    (36.5 : ℝ) < 17 + arccos ((3 ^ 2 + (√(1.5 ^ 2 + 3 ^ 2 - 2 * 1.5 * 3 * cos (117 * π / 180))) ^ 2 - 1.5 ^ 2) /
        (2 * 3 * √(1.5 ^ 2 + 3 ^ 2 - 2 * 1.5 * 3 * cos (117 * π / 180)))) * 180 / π ∧
      17 + arccos ((3 ^ 2 + (√(1.5 ^ 2 + 3 ^ 2 - 2 * 1.5 * 3 * cos (117 * π / 180))) ^ 2 - 1.5 ^ 2) /
        (2 * 3 * √(1.5 ^ 2 + 3 ^ 2 - 2 * 1.5 * 3 * cos (117 * π / 180)))) * 180 / π < 37.5 := by
  obtain ⟨a, b⟩ := num10_cd 117 (-0.45400) (-0.45399) (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  set c := cos (117 * π / 180) with hc
  have hD0 : 0 ≤ (1.5 : ℝ) ^ 2 + 3 ^ 2 - 2 * 1.5 * 3 * c := by nlinarith
  set d := √((1.5 : ℝ) ^ 2 + 3 ^ 2 - 2 * 1.5 * 3 * c) with hd
  have hd2 : d ^ 2 = (1.5 : ℝ) ^ 2 + 3 ^ 2 - 2 * 1.5 * 3 * c := sq_sqrt hD0
  have dl : 3.916 < d := by rw [hd, Real.lt_sqrt (by norm_num)]; nlinarith
  have du : d < 3.9162 := by rw [hd, Real.sqrt_lt' (by norm_num)]; nlinarith
  set q := (3 ^ 2 + d ^ 2 - 1.5 ^ 2) / (2 * 3 * d) with hq
  have hdp : 0 < 2 * 3 * d := by positivity
  have ql : 0.9399 < q := by rw [hq, lt_div_iff₀ hdp]; nlinarith
  have qu : q < 0.9400 := by rw [hq, div_lt_iff₀ hdp]; nlinarith
  obtain ⟨c1, c2⟩ := num10_cd 20.5 0.9366 0.9367 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c3, c4⟩ := num10_cd 19.5 0.9426 0.9427 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  have := num10_arccos_deg (q := q) (a := 19.5) (b := 20.5) (by norm_num) (by norm_num) (by norm_num)
    (by linarith) (by linarith)
  constructor <;> linarith [this.1, this.2]

/-- Stitz-Zeager Exercise 11.3.23 (bearing part): with `d` the distance from port (law of cosines at `64°`), the
angle `β` at the end of the second leg has `cos β = (2² + d² - 5²)/(2·2·d)`, and the bearing to port is `S x W` with
`x = 139° - β`; the book's `47°` is `46.5 < x < 47.5`. -/
@[kb "stitzzeager2013" "Exercise 11.3.23, p. 929"]
theorem exer_11_3_23_bearing :
    (46.5 : ℝ) < 139 - arccos ((2 ^ 2 + (√(5 ^ 2 + 2 ^ 2 - 2 * 5 * 2 * cos (64 * π / 180))) ^ 2 - 5 ^ 2) /
        (2 * 2 * √(5 ^ 2 + 2 ^ 2 - 2 * 5 * 2 * cos (64 * π / 180)))) * 180 / π ∧
      139 - arccos ((2 ^ 2 + (√(5 ^ 2 + 2 ^ 2 - 2 * 5 * 2 * cos (64 * π / 180))) ^ 2 - 5 ^ 2) /
        (2 * 2 * √(5 ^ 2 + 2 ^ 2 - 2 * 5 * 2 * cos (64 * π / 180)))) * 180 / π < 47.5 := by
  obtain ⟨a, b⟩ := num10_cd 64 0.43837 0.43838 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  set c := cos (64 * π / 180) with hc
  have hD0 : 0 ≤ (5 : ℝ) ^ 2 + 2 ^ 2 - 2 * 5 * 2 * c := by nlinarith
  set d := √((5 : ℝ) ^ 2 + 2 ^ 2 - 2 * 5 * 2 * c) with hd
  have hd2 : d ^ 2 = (5 : ℝ) ^ 2 + 2 ^ 2 - 2 * 5 * 2 * c := sq_sqrt hD0
  have dl : 4.498 < d := by rw [hd, Real.lt_sqrt (by norm_num)]; nlinarith
  have du : d < 4.4981 := by rw [hd, Real.sqrt_lt' (by norm_num)]; nlinarith
  set q := (2 ^ 2 + d ^ 2 - 5 ^ 2) / (2 * 2 * d) with hq
  have hdp : 0 < 2 * 2 * d := by positivity
  have ql : -0.0430 < q := by rw [hq, lt_div_iff₀ hdp]; nlinarith
  have qu : q < -0.0420 := by rw [hq, div_lt_iff₀ hdp]; nlinarith
  obtain ⟨c1, c2⟩ := num10_cd 92.5 (-0.04363) (-0.04361) (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c3, c4⟩ := num10_cd 91.5 (-0.02618) (-0.02617) (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  have := num10_arccos_deg (q := q) (a := 91.5) (b := 92.5) (by norm_num) (by norm_num) (by norm_num)
    (by linarith) (by linarith)
  constructor <;> linarith [this.1, this.2]

/-- Stitz-Zeager Exercise 11.3.24 (bearing part): with `d` the distance from the island (law of cosines at `38°`),
the angle `β` at the ship has `cos β = (100² + d² - 300²)/(2·100·d)`, and the course to the island is `N θ E` with
`θ = β - 110°`; the book's `16.4°` is `16.35 < θ < 16.45`. -/
@[kb "stitzzeager2013" "Exercise 11.3.24, p. 929"]
theorem exer_11_3_24_bearing :
    (16.35 : ℝ) < arccos ((100 ^ 2 + (√(300 ^ 2 + 100 ^ 2 - 2 * 300 * 100 * cos (38 * π / 180))) ^ 2 - 300 ^ 2) /
        (2 * 100 * √(300 ^ 2 + 100 ^ 2 - 2 * 300 * 100 * cos (38 * π / 180)))) * 180 / π - 110 ∧
      arccos ((100 ^ 2 + (√(300 ^ 2 + 100 ^ 2 - 2 * 300 * 100 * cos (38 * π / 180))) ^ 2 - 300 ^ 2) /
        (2 * 100 * √(300 ^ 2 + 100 ^ 2 - 2 * 300 * 100 * cos (38 * π / 180)))) * 180 / π - 110 < 16.45 := by
  obtain ⟨a, b⟩ := num10_cd 38 0.7880107 0.7880109 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  set c := cos (38 * π / 180) with hc
  have hD0 : 0 ≤ (300 : ℝ) ^ 2 + 100 ^ 2 - 2 * 300 * 100 * c := by nlinarith
  set d := √((300 : ℝ) ^ 2 + 100 ^ 2 - 2 * 300 * 100 * c) with hd
  have hd2 : d ^ 2 = (300 : ℝ) ^ 2 + 100 ^ 2 - 2 * 300 * 100 * c := sq_sqrt hD0
  have dl : 229.6069 < d := by rw [hd, Real.lt_sqrt (by norm_num)]; nlinarith
  have du : d < 229.6071 := by rw [hd, Real.sqrt_lt' (by norm_num)]; nlinarith
  set q := (100 ^ 2 + d ^ 2 - 300 ^ 2) / (2 * 100 * d) with hq
  have hdp : 0 < 2 * 100 * d := by positivity
  have ql : -0.59411 < q := by rw [hq, lt_div_iff₀ hdp]; nlinarith
  have qu : q < -0.59403 := by rw [hq, div_lt_iff₀ hdp]; nlinarith
  obtain ⟨c1, c2⟩ := num10_cd 126.45 (-0.59413) (-0.59411) (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c3, c4⟩ := num10_cd 126.35 (-0.59273) (-0.59271) (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  have := num10_arccos_deg (q := q) (a := 126.35) (b := 126.45) (by norm_num) (by norm_num) (by norm_num)
    (by linarith) (by linarith)
  constructor <;> linarith [this.1, this.2]

/-- Stitz-Zeager Exercise 11.2.21, triangle of Exercise 1 (`α = 13°`, `β = 17°`, `a = 5`, `γ = 150°`): the area
`½ a b sin γ` with `b = 5 sin 17°/sin 13°` is `8.05 < A < 8.15` (about `8.1`). -/
@[kb "stitzzeager2013" "Exercise 11.2.21, p. 916"]
theorem exer_11_2_21 :
    (8.05 : ℝ) < 1 / 2 * 5 * (5 * sin (17 * π / 180) / sin (13 * π / 180)) * sin (5 * π / 6) ∧
      1 / 2 * 5 * (5 * sin (17 * π / 180) / sin (13 * π / 180)) * sin (5 * π / 6) < 8.15 := by
  have h6 : sin (5 * π / 6) = 1 / 2 := by
    rw [show 5 * π / 6 = π - π / 6 by ring, sin_pi_sub, sin_pi_div_six]
  obtain ⟨a, b⟩ := num10_sd 17 0.29237 0.29238 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c, d⟩ := num10_sd 13 0.22495 0.22496 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  have hp : 0 < sin (13 * π / 180) := by linarith
  rw [h6]
  constructor
  · have : 1 / 2 * 5 * (5 * sin (17 * π / 180) / sin (13 * π / 180)) * (1 / 2) =
        25 / 4 * sin (17 * π / 180) / sin (13 * π / 180) := by ring
    rw [this, lt_div_iff₀ hp]; nlinarith
  · have : 1 / 2 * 5 * (5 * sin (17 * π / 180) / sin (13 * π / 180)) * (1 / 2) =
        25 / 4 * sin (17 * π / 180) / sin (13 * π / 180) := by ring
    rw [this, div_lt_iff₀ hp]; nlinarith

/-- Stitz-Zeager Exercise 11.2.21, triangle of Exercise 12 (`α = γ = 53°`, `c = 28.01`, so `a = c`, `β = 74°`): the
area `½ a c sin β` is `377.05 < A < 377.15` (about `377.1`). -/
@[kb "stitzzeager2013" "Exercise 11.2.21, p. 916"]
theorem exer_11_2_21_t12 :
    (377.05 : ℝ) < 1 / 2 * 28.01 * 28.01 * sin (74 * π / 180) ∧
      1 / 2 * 28.01 * 28.01 * sin (74 * π / 180) < 377.15 := by
  obtain ⟨a, b⟩ := num10_sd 74 0.96126 0.96127 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  constructor <;> nlinarith

/-- Stitz-Zeager Exercise 11.2.21, triangle of Exercise 20 (`α = 50°`, `a = 25`, `b = 12.5`): with
`β = arcsin (b sin α / a)` and `γ = π - α - β`, the area `½ a b sin γ` is `148.5 < A < 149.5` (about `149`). -/
@[kb "stitzzeager2013" "Exercise 11.2.21, p. 916"]
theorem exer_11_2_21_t20 :
    (148.5 : ℝ) < 1 / 2 * 25 * 12.5 *
        sin (π - 50 * π / 180 - arcsin (12.5 * sin (50 * π / 180) / 25)) ∧
      1 / 2 * 25 * 12.5 * sin (π - 50 * π / 180 - arcsin (12.5 * sin (50 * π / 180) / 25)) < 149.5 := by
  obtain ⟨a, b⟩ := num10_sd 50 0.76604 0.76605 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c, d⟩ := num10_cd 50 0.64278 0.64279 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  set s := sin (50 * π / 180) with hs
  set k := cos (50 * π / 180) with hk
  have e : 12.5 * s / 25 = s / 2 := by ring
  have hb1 : -1 ≤ s / 2 := by linarith
  have hb2 : s / 2 ≤ 1 := by linarith
  have hsin : sin (arcsin (12.5 * s / 25)) = s / 2 := by rw [e]; exact sin_arcsin hb1 hb2
  have hcos : cos (arcsin (12.5 * s / 25)) = √(1 - (s / 2) ^ 2) := by rw [e]; exact cos_arcsin _
  have hg : sin (π - 50 * π / 180 - arcsin (12.5 * s / 25)) = s * √(1 - (s / 2) ^ 2) + k * (s / 2) := by
    rw [show π - 50 * π / 180 - arcsin (12.5 * s / 25) = π - (50 * π / 180 + arcsin (12.5 * s / 25)) by ring,
      sin_pi_sub, sin_add, hsin, hcos]
  have r1 : 0.9237 < √(1 - (s / 2) ^ 2) := by rw [Real.lt_sqrt (by norm_num)]; nlinarith
  have r2 : √(1 - (s / 2) ^ 2) < 0.9238 := by rw [Real.sqrt_lt' (by norm_num)]; nlinarith
  rw [hg]
  constructor <;> nlinarith

/-- Stitz-Zeager Exercise 11.8.26: the vector of magnitude `392` at angle `117°` has components
`⟨392 cos 117°, 392 sin 117°⟩`, which the book rounds to `⟨-177.96, 349.27⟩`: each component lies within `0.005` of it. -/
@[kb "stitzzeager2013" "Exercise 11.8.26, p. 1040"]
theorem exer_11_8_26 :
    ((-177.965 : ℝ) < 392 * cos (117 * π / 180) ∧ 392 * cos (117 * π / 180) < -177.955) ∧
      ((349.265 : ℝ) < 392 * sin (117 * π / 180) ∧ 392 * sin (117 * π / 180) < 349.275) := by
  obtain ⟨a, b⟩ := num10_cd 117 (-0.453990701) (-0.453990121) (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c, d⟩ := num10_sd 117 0.891006137 0.891007001 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  constructor <;> constructor <;> linarith

/-- Stitz-Zeager Exercise 11.8.27: the vector of magnitude `63.92` at angle `78.3°` has components
`⟨63.92 cos 78.3°, 63.92 sin 78.3°⟩`, which the book rounds to `⟨12.96, 62.59⟩`: each component lies within `0.005` of it. -/
@[kb "stitzzeager2013" "Exercise 11.8.27, p. 1040"]
theorem exer_11_8_27 :
    ((12.955 : ℝ) < 63.92 * cos (78.3 * π / 180) ∧ 63.92 * cos (78.3 * π / 180) < 12.965) ∧
      ((62.585 : ℝ) < 63.92 * sin (78.3 * π / 180) ∧ 63.92 * sin (78.3 * π / 180) < 62.595) := by
  obtain ⟨a, b⟩ := num10_cd 78.3 0.202787147 0.202787574 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c, d⟩ := num10_sd 78.3 0.979222529 0.979223065 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  constructor <;> constructor <;> linarith

/-- Stitz-Zeager Exercise 11.8.28: the vector of magnitude `5280` at angle `12°` has components
`⟨5280 cos 12°, 5280 sin 12°⟩`, which the book rounds to `⟨5164.62, 1097.77⟩`: each component lies within `0.005` of it. -/
@[kb "stitzzeager2013" "Exercise 11.8.28, p. 1040"]
theorem exer_11_8_28 :
    ((5164.615 : ℝ) < 5280 * cos (12 * π / 180) ∧ 5280 * cos (12 * π / 180) < 5164.625) ∧
      ((1097.765 : ℝ) < 5280 * sin (12 * π / 180) ∧ 5280 * sin (12 * π / 180) < 1097.775) := by
  obtain ⟨a, b⟩ := num10_cd 12 0.978147595 0.978147610 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c, d⟩ := num10_sd 12 0.207911647 0.207911715 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  constructor <;> constructor <;> linarith

/-- Stitz-Zeager Exercise 11.8.29: the vector of magnitude `450` at angle `210.75°` has components
`⟨450 cos 210.75°, 450 sin 210.75°⟩`, which the book rounds to `⟨-386.73, -230.08⟩`: each component lies within `0.005` of it. -/
@[kb "stitzzeager2013" "Exercise 11.8.29, p. 1040"]
theorem exer_11_8_29 :
    ((-386.735 : ℝ) < 450 * cos (210.75 * π / 180) ∧ 450 * cos (210.75 * π / 180) < -386.725) ∧
      ((-230.085 : ℝ) < 450 * sin (210.75 * π / 180) ∧ 450 * sin (210.75 * π / 180) < -230.075) := by
  rw [show 210.75 * π / 180 = 30.75 * π / 180 + π by ring, cos_add_pi, sin_add_pi]
  obtain ⟨a, b⟩ := num10_cd 30.75 0.859406381 0.859406469 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c, d⟩ := num10_sd 30.75 0.511292974 0.511293153 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  constructor <;> constructor <;> linarith

/-- Stitz-Zeager Exercise 11.8.30: the vector of magnitude `168.7` at angle `252°` has components
`⟨168.7 cos 252°, 168.7 sin 252°⟩`, which the book rounds to `⟨-52.13, -160.44⟩`: each component lies within `0.005` of it. -/
@[kb "stitzzeager2013" "Exercise 11.8.30, p. 1040"]
theorem exer_11_8_30 :
    ((-52.135 : ℝ) < 168.7 * cos (252 * π / 180) ∧ 168.7 * cos (252 * π / 180) < -52.125) ∧
      ((-160.445 : ℝ) < 168.7 * sin (252 * π / 180) ∧ 168.7 * sin (252 * π / 180) < -160.435) := by
  rw [show 252 * π / 180 = 72 * π / 180 + π by ring, cos_add_pi, sin_add_pi]
  obtain ⟨a, b⟩ := num10_cd 72 0.309016862 0.309017244 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c, d⟩ := num10_sd 72 0.951056256 0.951056739 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  constructor <;> constructor <;> linarith

/-- Stitz-Zeager Exercise 11.8.31: the vector of magnitude `26` at angle `304.5°` has components
`⟨26 cos 304.5°, 26 sin 304.5°⟩`, which the book rounds to `⟨14.73, -21.43⟩`: each component lies within `0.005` of it. -/
@[kb "stitzzeager2013" "Exercise 11.8.31, p. 1040"]
theorem exer_11_8_31 :
    ((14.725 : ℝ) < 26 * cos (304.5 * π / 180) ∧ 26 * cos (304.5 * π / 180) < 14.735) ∧
      ((-21.435 : ℝ) < 26 * sin (304.5 * π / 180) ∧ 26 * sin (304.5 * π / 180) < -21.425) := by
  rw [show 304.5 * π / 180 = -(55.5 * π / 180) + 2 * π by ring, cos_add_two_pi, sin_add_two_pi, cos_neg, sin_neg]
  obtain ⟨a, b⟩ := num10_cd 55.5 0.566406148 0.566406404 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  obtain ⟨c, d⟩ := num10_sd 55.5 0.824125986 0.824126337 (by norm_num) (by norm_num)
    (by norm_num [nBaseOk, nOk, nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase]) (by norm_num [nIt, nStep, nBase])
  constructor <;> constructor <;> linarith

end UndergradKB.Precalculus.Course
