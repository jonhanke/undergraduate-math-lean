import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 11 (Stitz-Zeager): exercises with the book's answers (wave 8), Section 11.10 (hammer throw) -/

namespace UndergradKB.Precalculus.Course

open Real

/-- Numerical bounds for `sin 42°` and `cos 42°` (from `42° = 45° - 3°` and the Taylor bounds at `3°`). -/
theorem ch11e3d_trig42 : (0.6691 : ℝ) < sin (42 * π / 180) ∧ sin (42 * π / 180) < 0.6692 ∧
    (0.7431 : ℝ) < cos (42 * π / 180) ∧ cos (42 * π / 180) < 0.7432 := by
  have hp1 := Real.pi_gt_d4
  have hp2 := Real.pi_lt_d4
  have hd1 : (0.05235 : ℝ) < π / 60 := by linarith
  have hd2 : π / 60 < (0.05236 : ℝ) := by linarith
  have hdp : (0 : ℝ) < π / 60 := by linarith
  set d := π / 60 with hd
  have e1 : 42 * π / 180 = π / 4 - d := by rw [hd]; ring
  have hs := Real.sin_bound (x := d) (by rw [abs_of_pos hdp]; linarith)
  have hc := Real.cos_bound (x := d) (by rw [abs_of_pos hdp]; linarith)
  rw [abs_of_pos hdp] at hs hc
  have hd4 : d ^ 4 < (0.05236 : ℝ) ^ 4 := pow_lt_pow_left₀ hd2 hdp.le (by norm_num)
  have hd3a : d ^ 3 < (0.05236 : ℝ) ^ 3 := pow_lt_pow_left₀ hd2 hdp.le (by norm_num)
  have hd3b : (0.05235 : ℝ) ^ 3 < d ^ 3 := pow_lt_pow_left₀ hd1 (by norm_num) (by norm_num)
  have hd2a : d ^ 2 < (0.05236 : ℝ) ^ 2 := pow_lt_pow_left₀ hd2 hdp.le (by norm_num)
  have hd2b : (0.05235 : ℝ) ^ 2 < d ^ 2 := pow_lt_pow_left₀ hd1 (by norm_num) (by norm_num)
  norm_num at hd4 hd3a hd3b hd2a hd2b
  have hsl := (abs_le.mp hs).1
  have hsu := (abs_le.mp hs).2
  have hcl := (abs_le.mp hc).1
  have hcu := (abs_le.mp hc).2
  have sd1 : (0.05232 : ℝ) < sin d := by nlinarith
  have sd2 : sin d < (0.05234 : ℝ) := by nlinarith
  have cd1 : (0.99862 : ℝ) < cos d := by nlinarith
  have cd2 : cos d < (0.99863 : ℝ) := by nlinarith
  have q1 : (0.707105 : ℝ) < √2 / 2 := by
    have : (1.41421 : ℝ) < √2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
    linarith
  have q2 : √2 / 2 < (0.70711 : ℝ) := by
    have : √2 < (1.41422 : ℝ) := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    linarith
  rw [e1, Real.sin_sub, Real.cos_sub, Real.sin_pi_div_four, Real.cos_pi_div_four]
  have m1 := mul_lt_mul'' q1 (show (0.94628 : ℝ) < cos d - sin d by linarith) (by norm_num)
    (by norm_num)
  have m2 := mul_lt_mul'' q2 (show cos d - sin d < (0.94631 : ℝ) by linarith) (by linarith)
    (by linarith)
  have m3 := mul_lt_mul'' q1 (show (1.05094 : ℝ) < cos d + sin d by linarith) (by norm_num)
    (by norm_num)
  have m4 := mul_lt_mul'' q2 (show cos d + sin d < (1.05097 : ℝ) by linarith) (by linarith)
    (by linarith)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- Stitz-Zeager Exercise 11.10.43: the hammer, released `6` ft up at `42°` with speed `33` ft/s
(`x = 33 cos 42° t`, `y = -16 t² + 33 sin 42° t + 6`), has exactly one landing time `t ≥ 0` with `y = 0`,
it lies in `(1.605, 1.615)` seconds (the book: about `1.61`), and the landing distance is
between `39.3` and `39.7` feet (the book: about `39.48`). -/
@[kb "stitzzeager2013" "Exercise 11.10.43, p. 1073"]
theorem exer_11_10_43 :
    ∃ t : ℝ, (0 ≤ t ∧ -16 * t ^ 2 + 33 * sin (42 * π / 180) * t + 6 = 0) ∧
      (∀ u : ℝ, 0 ≤ u → -16 * u ^ 2 + 33 * sin (42 * π / 180) * u + 6 = 0 → u = t) ∧
      (1.605 : ℝ) < t ∧ t < 1.615 ∧
      (39.3 : ℝ) < 33 * cos (42 * π / 180) * t ∧ 33 * cos (42 * π / 180) * t < 39.7 := by
  obtain ⟨s1, s2, c1, c2⟩ := ch11e3d_trig42
  set s := sin (42 * π / 180) with hs
  set c := cos (42 * π / 180) with hc
  have hD : (0 : ℝ) ≤ (33 * s) ^ 2 + 384 := by positivity
  set r := √((33 * s) ^ 2 + 384) with hr
  have hr2 : r ^ 2 = (33 * s) ^ 2 + 384 := Real.sq_sqrt hD
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrS : 33 * s < r := by
    by_contra h
    replace h := not_lt.mp h
    nlinarith
  have hr_lo : (29.52 : ℝ) < r := by
    by_contra h
    replace h := not_lt.mp h
    nlinarith
  have hr_hi : r < (29.525 : ℝ) := by
    by_contra h
    replace h := not_lt.mp h
    nlinarith
  have ht1 : (1.605 : ℝ) < (33 * s + r) / 32 := by linarith
  have ht2 : (33 * s + r) / 32 < (1.615 : ℝ) := by linarith
  refine ⟨(33 * s + r) / 32, ⟨by linarith, ?_⟩, ?_, ht1, ht2, ?_, ?_⟩
  · linear_combination (-1 / 64 : ℝ) * hr2
  · intro u hu he
    have hprod : (u - (33 * s + r) / 32) * (u - (33 * s - r) / 32) = 0 := by
      linear_combination (-1 / 16 : ℝ) * he + (-1 / 1024 : ℝ) * hr2
    rcases mul_eq_zero.mp hprod with h | h
    · linarith
    · exfalso; linarith
  · nlinarith
  · nlinarith

end UndergradKB.Precalculus.Course
