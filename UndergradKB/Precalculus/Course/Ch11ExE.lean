import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Real.Pi.Bounds
import UndergradKB.Precalculus.Course.Ch11ExC

/-! # Course layer, Chapter 11 (Stitz-Zeager): the rounded bearing of Example 11.8.1 (wave 7)

Wave 5 stated the true speed of Example 11.8.1 (`ex_11_8_1`: between 183.5 and 184.5 miles per hour); the rounded
true bearing `N51°E` needs cosine bounds at angles that are not special, which come here from Mathlib's
`Real.cos_bound` (`|cos x - (1 - x²/2)| ≤ |x|⁴ · 5/96` for `|x| ≤ 1`) and the bounds on `π`.
-/

namespace UndergradKB.Precalculus.Course

open Real

/-- `cos x` is within `|x|⁴ · 5/96` of `1 - x²/2` for `|x| ≤ 1`, as two inequalities. -/
lemma cos_two_sided {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    1 - x ^ 2 / 2 - x ^ 4 * (5 / 96) ≤ cos x ∧ cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 * (5 / 96) := by
  have hb := Real.cos_bound (x := x) (by rw [abs_of_nonneg h0]; exact h1)
  rw [abs_of_nonneg h0] at hb
  constructor <;> linarith [(abs_le.1 hb).1, (abs_le.1 hb).2]

/-- Stitz-Zeager Example 11.8.1, the true bearing: with `c = √(175² + 35² - 2·175·35 cos 100°)` the true speed, the
angle `α = arccos((c² + 29400)/(350 c))` between the plane's heading and its true course (Law of Cosines) lies
between `10.5°` and `11.5°`, so the true bearing `N(40° + α)E` rounds to `N51°E`. -/
@[kb "stitzzeager2013" "Example 11.8.1, p. 1025"]
theorem ex_11_8_1_bearing :
    (50.5 : ℝ) < 40 + arccos (((√(31850 - 12250 * cos (5 * π / 9))) ^ 2 + 29400) /
        (350 * √(31850 - 12250 * cos (5 * π / 9)))) * 180 / π ∧
      40 + arccos (((√(31850 - 12250 * cos (5 * π / 9))) ^ 2 + 29400) /
        (350 * √(31850 - 12250 * cos (5 * π / 9)))) * 180 / π < 51.5 := by
  obtain ⟨-, hlo, hhi, -⟩ := ex_11_8_1
  set s := 31850 - 12250 * cos (5 * π / 9) with hs
  have hs0 : 0 ≤ s := by nlinarith
  set c := √s with hc
  have hc2 : c ^ 2 = s := sq_sqrt hs0
  have hc0 : 0 ≤ c := sqrt_nonneg s
  have hclo : 183.5 < c := by nlinarith
  have hchi : c < 184.5 := by nlinarith
  set q := (c ^ 2 + 29400) / (350 * c) with hq
  have hcpos : 0 < 350 * c := by linarith
  -- the cosine of the course angle lies strictly between the cosines of `11.5°` and `10.5°`
  have hqlo : 0.97995 < q := by
    rw [hq, lt_div_iff₀ hcpos]; nlinarith
  have hqhi : q < 0.98314 := by
    rw [hq, div_lt_iff₀ hcpos]; nlinarith
  have p1 := pi_gt_d6
  have p2 := pi_lt_d6
  have hp : 0 < π := pi_pos
  set a := 10.5 * π / 180 with ha
  set b := 11.5 * π / 180 with hb
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have ha1 : a ≤ 1 := by rw [ha]; nlinarith
  have hb1 : b ≤ 1 := by rw [hb]; nlinarith
  have hcosa : 0.98314 ≤ cos a := by
    have h := (cos_two_sided ha0 ha1).1
    have hal : 0.1832595 < a := by rw [ha]; nlinarith
    have hau : a < 0.1832596 := by rw [ha]; nlinarith
    nlinarith [pow_le_pow_left₀ ha0 hau.le 4]
  have hcosb : cos b ≤ 0.97995 := by
    have h := (cos_two_sided hb0 hb1).2
    have hbl : 0.2007128 < b := by rw [hb]; nlinarith
    have hbu : b < 0.2007130 := by rw [hb]; nlinarith
    nlinarith [pow_le_pow_left₀ hb0 hbu.le 4]
  have hq1 : q ≤ 1 := by linarith
  have hqm : -1 ≤ q := by linarith
  have hapi : a ≤ π := by linarith
  have hbpi : b ≤ π := by linarith
  -- `arccos` is strictly decreasing on `[-1, 1]`
  have hlt1 : arccos q < b := by
    have := strictAntiOn_arccos ⟨by linarith [neg_one_le_cos b], by linarith⟩ ⟨hqm, hq1⟩
      (lt_of_le_of_lt hcosb hqlo)
    rwa [arccos_cos hb0 hbpi] at this
  have hlt2 : a < arccos q := by
    have := strictAntiOn_arccos ⟨hqm, hq1⟩ ⟨by linarith, cos_le_one a⟩ (lt_of_lt_of_le hqhi hcosa)
    rwa [arccos_cos ha0 hapi] at this
  constructor
  · have : 10.5 < arccos q * 180 / π := by
      rw [lt_div_iff₀ hp]; rw [ha] at hlt2; linarith
    linarith
  · have : arccos q * 180 / π < 11.5 := by
      rw [div_lt_iff₀ hp]; rw [hb] at hlt1; linarith
    linarith

end UndergradKB.Precalculus.Course
