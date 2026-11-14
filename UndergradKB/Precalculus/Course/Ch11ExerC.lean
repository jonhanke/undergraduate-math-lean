import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Real.Pi.Bounds
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 11 (Stitz-Zeager): exercises with the book's answers

Section 11.3 (law of cosines). A triangle with angles `α β γ` opposite the sides `a b c` is encoded by
`CosTri`: positive sides, angles in `(0, π)`, and the three laws of cosines. -/

namespace UndergradKB.Precalculus.Course

open Real Set

/-- A triangle with sides `a b c` opposite the angles `α β γ`: positive sides, angles in `(0, π)`, and
`a² = b² + c² - 2bc cos α` together with its two cyclic versions. -/
def CosTri (α β γ a b c : ℝ) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < c ∧ (0 < α ∧ α < π) ∧ (0 < β ∧ β < π) ∧ (0 < γ ∧ γ < π) ∧
    a ^ 2 = b ^ 2 + c ^ 2 - 2 * b * c * cos α ∧ b ^ 2 = a ^ 2 + c ^ 2 - 2 * a * c * cos β ∧
    c ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b * cos γ

/-! ## Helpers -/

private theorem x11c_arccos_iff {α t : ℝ} (h1 : -1 < t) (h2 : t < 1) :
    (0 < α ∧ α < π ∧ cos α = t) ↔ α = arccos t := by
  constructor
  · rintro ⟨h0, h1', h⟩
    rw [← h, arccos_cos h0.le h1'.le]
  · rintro rfl
    exact ⟨arccos_pos.mpr h2, arccos_lt_pi.mpr h1, cos_arccos h1.le h2.le⟩

private theorem x11c_sss {α β γ a b c tα tβ tγ : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : b ^ 2 + c ^ 2 - a ^ 2 = 2 * b * c * tα) (h2 : a ^ 2 + c ^ 2 - b ^ 2 = 2 * a * c * tβ)
    (h3 : a ^ 2 + b ^ 2 - c ^ 2 = 2 * a * b * tγ)
    (t1 : -1 < tα) (t1' : tα < 1) (t2 : -1 < tβ) (t2' : tβ < 1) (t3 : -1 < tγ) (t3' : tγ < 1) :
    CosTri α β γ a b c ↔ α = arccos tα ∧ β = arccos tβ ∧ γ = arccos tγ := by
  have e1 : 2 * b * c ≠ 0 := by positivity
  have e2 : 2 * a * c ≠ 0 := by positivity
  have e3 : 2 * a * b ≠ 0 := by positivity
  constructor
  · rintro ⟨-, -, -, ⟨a0, a1⟩, ⟨b0, b1⟩, ⟨c0, c1⟩, k1, k2, k3⟩
    refine ⟨(x11c_arccos_iff t1 t1').mp ⟨a0, a1, ?_⟩, (x11c_arccos_iff t2 t2').mp ⟨b0, b1, ?_⟩,
      (x11c_arccos_iff t3 t3').mp ⟨c0, c1, ?_⟩⟩
    · apply mul_left_cancel₀ e1; linarith
    · apply mul_left_cancel₀ e2; linarith
    · apply mul_left_cancel₀ e3; linarith
  · rintro ⟨r1, r2, r3⟩
    obtain ⟨a0, a1, ca⟩ := (x11c_arccos_iff t1 t1').mpr r1
    obtain ⟨b0, b1, cb⟩ := (x11c_arccos_iff t2 t2').mpr r2
    obtain ⟨c0, c1, cc⟩ := (x11c_arccos_iff t3 t3').mpr r3
    refine ⟨ha, hb, hc, ⟨a0, a1⟩, ⟨b0, b1⟩, ⟨c0, c1⟩, ?_, ?_, ?_⟩
    · rw [ca]; linarith
    · rw [cb]; linarith
    · rw [cc]; linarith

private theorem x11c_sin27 : 0.4537 < sin (27 * π / 180) ∧ sin (27 * π / 180) < 0.4548 := by
  have h1 := pi_gt_d2
  have h2 := pi_lt_d2
  have e : sin (27 * π / 180) = sin (π / 6) * cos (π / 60) - cos (π / 6) * sin (π / 60) := by
    rw [← sin_sub]; congr 1; ring
  rw [e, sin_pi_div_six, cos_pi_div_six]
  have hy : 0 < π / 60 := by positivity
  have hs := sin_lt hy
  have hs2 := sin_gt_sub_cube hy
  have hc := one_sub_sq_div_two_le_cos (x := π / 60)
  have hcl := cos_le_one (π / 60)
  have h3a : (1.732 : ℝ) < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h3b : √3 < 1.7321 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hp : 0 < sin (π / 60) := sin_pos_of_pos_of_lt_pi hy (by linarith)
  constructor
  · nlinarith [mul_pos hy hy, mul_pos (mul_pos hy hy) hy]
  · nlinarith [mul_pos hy hy, mul_pos (mul_pos hy hy) hy]

/-! ## Section 11.3 -/

/-- Stitz-Zeager Exercise 11.3.4: `a = 3`, `b = 4`, `γ = 90°` gives `c = 5`, `α = arccos (4/5)`
(about `36.87°`), `β = arccos (3/5)` (about `53.13°`). -/
@[kb "stitzzeager2013" "Exercise 11.3.4, p. 928"]
theorem exer_11_3_4 (α β c : ℝ) :
    CosTri α β (π / 2) 3 4 c ↔ c = 5 ∧ α = arccos (4 / 5) ∧ β = arccos (3 / 5) := by
  constructor
  · intro h
    have hc : c = 5 := by
      obtain ⟨-, -, hc0, -, -, -, -, -, k3⟩ := id h
      rw [cos_pi_div_two] at k3
      nlinarith
    subst hc
    obtain ⟨r1, r2, -⟩ := (x11c_sss (tα := 4 / 5) (tβ := 3 / 5) (tγ := 0) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)).mp h
    exact ⟨rfl, r1, r2⟩
  · rintro ⟨rfl, r1, r2⟩
    exact (x11c_sss (tα := 4 / 5) (tβ := 3 / 5) (tγ := 0) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)).mpr ⟨r1, r2, arccos_zero.symm⟩

/-- Stitz-Zeager Exercise 11.3.5: `α = 120°`, `b = 3`, `c = 4`: the side `a` satisfies the law of cosines
exactly when `a = √37`. -/
@[kb "stitzzeager2013" "Exercise 11.3.5, p. 928"]
theorem exer_11_3_5 (a : ℝ) (ha : 0 < a) :
    a ^ 2 = 3 ^ 2 + 4 ^ 2 - 2 * 3 * 4 * cos (2 * π / 3) ↔ a = √37 := by
  have hc : cos (2 * π / 3) = -1 / 2 := by
    rw [show 2 * π / 3 = π - π / 3 by ring, cos_pi_sub, cos_pi_div_three]; norm_num
  rw [hc]
  constructor
  · intro h
    have : a ^ 2 = 37 := by linarith
    rw [← this, Real.sqrt_sq ha.le]
  · rintro rfl
    rw [Real.sq_sqrt (by norm_num)]; norm_num

/-- Stitz-Zeager Exercise 11.3.6: the triangle with sides `7, 10, 13` has angles `arccos (11/13)`,
`arccos (59/91)`, `arccos (-1/7)` (about `32.31°`, `49.58°`, `98.21°`). -/
@[kb "stitzzeager2013" "Exercise 11.3.6, p. 928"]
theorem exer_11_3_6 (α β γ : ℝ) :
    CosTri α β γ 7 10 13 ↔ α = arccos (11 / 13) ∧ β = arccos (59 / 91) ∧ γ = arccos (-1 / 7) :=
  x11c_sss (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Stitz-Zeager Exercise 11.3.7: sides `1, 2, 5` do not form a triangle. -/
@[kb "stitzzeager2013" "Exercise 11.3.7, p. 928"]
theorem exer_11_3_7 : ¬ ∃ α β γ : ℝ, CosTri α β γ 1 2 5 := by
  rintro ⟨α, β, γ, -, -, -, -, -, -, k1, -, -⟩
  nlinarith [cos_le_one α]

/-- Stitz-Zeager Exercise 11.3.8: the triangle with sides `300, 302, 48` has angles `arccos (877/7248)`,
`arccos (11/288)`, `arccos (1789/1812)` (about `83.05°`, `87.81°`, `9.14°`). -/
@[kb "stitzzeager2013" "Exercise 11.3.8, p. 928"]
theorem exer_11_3_8 (α β γ : ℝ) :
    CosTri α β γ 300 302 48 ↔ α = arccos (877 / 7248) ∧ β = arccos (11 / 288) ∧
      γ = arccos (1789 / 1812) :=
  x11c_sss (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Stitz-Zeager Exercise 11.3.9: the triangle with sides `5, 5, 5` is equiangular, all angles `60°`. -/
@[kb "stitzzeager2013" "Exercise 11.3.9, p. 928"]
theorem exer_11_3_9 (α β γ : ℝ) : CosTri α β γ 5 5 5 ↔ α = π / 3 ∧ β = π / 3 ∧ γ = π / 3 := by
  have h : arccos (1 / 2 : ℝ) = π / 3 := by
    rw [← cos_pi_div_three, arccos_cos (by positivity) (by linarith [pi_pos])]
  rw [x11c_sss (tα := 1 / 2) (tβ := 1 / 2) (tγ := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num), h]

/-- Stitz-Zeager Exercise 11.3.10: the triangle with sides `5, 12, 13` is right, with `γ = 90°`,
`α = arccos (12/13)` (about `22.62°`) and `β = arccos (5/13)` (about `67.38°`). -/
@[kb "stitzzeager2013" "Exercise 11.3.10, p. 928"]
theorem exer_11_3_10 (α β γ : ℝ) :
    CosTri α β γ 5 12 13 ↔ α = arccos (12 / 13) ∧ β = arccos (5 / 13) ∧ γ = π / 2 := by
  rw [← arccos_zero]
  exact x11c_sss (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Stitz-Zeager Exercise 11.3.12: the triangle with sides `37, 45, 26` has angles `arccos (37/65)`,
`arccos (5/481)`, `arccos (151/185)` (about `55.30°`, `89.40°`, `35.30°`). -/
@[kb "stitzzeager2013" "Exercise 11.3.12, p. 928"]
theorem exer_11_3_12 (α β γ : ℝ) :
    CosTri α β γ 37 45 26 ↔ α = arccos (37 / 65) ∧ β = arccos (5 / 481) ∧
      γ = arccos (151 / 185) :=
  x11c_sss (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Stitz-Zeager Exercise 11.3.11: with `a = 18`, `α = 63°`, `b = 20` the law of cosines
`c² - 2 (20 cos 63°) c + 76 = 0` has exactly two positive solutions `k ± √(k² - 76)`, `k = 20 cos 63°`:
two triangles (`c ≈ 6.54` and `c ≈ 11.62`). -/
@[kb "stitzzeager2013" "Exercise 11.3.11, p. 928"]
theorem exer_11_3_11 (k : ℝ) (hk : k = 20 * cos (63 * π / 180)) :
    {c : ℝ | 0 < c ∧ 18 ^ 2 = 20 ^ 2 + c ^ 2 - 2 * 20 * c * cos (63 * π / 180)} =
        {k - √(k ^ 2 - 76), k + √(k ^ 2 - 76)} ∧
      0 < k - √(k ^ 2 - 76) ∧ k - √(k ^ 2 - 76) < k + √(k ^ 2 - 76) := by
  have hc : cos (63 * π / 180) = sin (27 * π / 180) := by
    rw [← cos_pi_div_two_sub]; congr 1; ring
  obtain ⟨s1, s2⟩ := x11c_sin27
  subst hk
  rw [hc]
  generalize sin (27 * π / 180) = s at s1 s2 ⊢
  have hD : 0 < (20 * s) ^ 2 - 76 := by nlinarith
  have hs := Real.sq_sqrt hD.le
  have hs0 := Real.sqrt_pos.2 hD
  have hlt : √((20 * s) ^ 2 - 76) < 20 * s := by nlinarith
  refine ⟨?_, by linarith, by linarith⟩
  ext c
  simp only [Set.mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨hc0, h⟩
    have : (c - 20 * s) ^ 2 = √((20 * s) ^ 2 - 76) ^ 2 := by rw [hs]; nlinarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 this with h3 | h3
    · right; linarith
    · left; linarith
  · rintro (rfl | rfl)
    · refine ⟨by linarith, ?_⟩
      nlinarith
    · refine ⟨by linarith, ?_⟩
      nlinarith

/-- Stitz-Zeager Exercise 11.3.13: with `a = 16`, `α = 63°`, `b = 20` the law of cosines
`c² - 2 (20 cos 63°) c + 144 = 0` has no positive solution, so there is no triangle. -/
@[kb "stitzzeager2013" "Exercise 11.3.13, p. 928"]
theorem exer_11_3_13 :
    {c : ℝ | 0 < c ∧ 16 ^ 2 = 20 ^ 2 + c ^ 2 - 2 * 20 * c * cos (63 * π / 180)} = ∅ := by
  have hc : cos (63 * π / 180) = sin (27 * π / 180) := by
    rw [← cos_pi_div_two_sub]; congr 1; ring
  obtain ⟨s1, s2⟩ := x11c_sin27
  ext c
  simp only [Set.mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
  intro hc0 h
  rw [hc] at h
  nlinarith [sq_nonneg (c - 20 * sin (27 * π / 180))]

/-- Stitz-Zeager Exercise 11.3.14: with `a = 22`, `α = 63°`, `b = 20` the law of cosines
`c² - 2 (20 cos 63°) c - 84 = 0` has exactly one positive solution `k + √(k² + 84)`, `k = 20 cos 63°`
(about `21.98`). -/
@[kb "stitzzeager2013" "Exercise 11.3.14, p. 928"]
theorem exer_11_3_14 (k : ℝ) (hk : k = 20 * cos (63 * π / 180)) :
    {c : ℝ | 0 < c ∧ 22 ^ 2 = 20 ^ 2 + c ^ 2 - 2 * 20 * c * cos (63 * π / 180)} =
      {k + √(k ^ 2 + 84)} := by
  have hc : cos (63 * π / 180) = sin (27 * π / 180) := by
    rw [← cos_pi_div_two_sub]; congr 1; ring
  obtain ⟨s1, s2⟩ := x11c_sin27
  subst hk
  rw [hc]
  generalize sin (27 * π / 180) = s at s1 s2 ⊢
  have hD : 0 < (20 * s) ^ 2 + 84 := by positivity
  have hs := Real.sq_sqrt hD.le
  have hs0 := Real.sqrt_pos.2 hD
  have hgt : 20 * s < √((20 * s) ^ 2 + 84) := by nlinarith
  ext c
  simp only [Set.mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨hc0, h⟩
    have h' : (c - 20 * s) ^ 2 = √((20 * s) ^ 2 + 84) ^ 2 := by rw [hs]; nlinarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h' with h3 | h3
    · linarith
    · exfalso; linarith
  · rintro rfl
    refine ⟨by linarith, ?_⟩
    nlinarith

/-- Stitz-Zeager Exercise 11.3.17: Heron's formula gives the areas `√1200 = 20√3` (sides `7, 10, 13`),
`√51764375` (sides `300, 302, 48`, about `7194.75`) and `30` (sides `5, 12, 13`). -/
@[kb "stitzzeager2013" "Exercise 11.3.17, p. 928"]
theorem exer_11_3_17 :
    √(15 * (15 - 7) * (15 - 10) * (15 - 13)) = 20 * √3 ∧
      √(325 * (325 - 300) * (325 - 302) * (325 - 48)) = √51764375 ∧
      7194.7 < √51764375 ∧ √51764375 < 7194.8 ∧
      √(15 * (15 - 5) * (15 - 12) * (15 - 13)) = 30 := by
  refine ⟨?_, by norm_num, ?_, ?_, ?_⟩
  · rw [show (15 * (15 - 7) * (15 - 10) * (15 - 13) : ℝ) = 20 ^ 2 * 3 by norm_num,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num
  · rw [show (15 * (15 - 5) * (15 - 12) * (15 - 13) : ℝ) = 30 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- Stitz-Zeager Exercise 11.3.18: at four o'clock the clock hands (`4` and `5.5` inches) make `120°`, so
the distance `d` between their ends satisfies `d² = 4² + 5.5² - 2·4·5.5 cos 120°`, i.e. `d = √273/2`,
about `8.26` inches. -/
@[kb "stitzzeager2013" "Exercise 11.3.18, p. 928"]
theorem exer_11_3_18 (d : ℝ) (hd : 0 < d) :
    d ^ 2 = 4 ^ 2 + 5.5 ^ 2 - 2 * 4 * 5.5 * cos (2 * π / 3) ↔
      d = √273 / 2 ∧ 8.25 < d ∧ d < 8.27 := by
  have hc : cos (2 * π / 3) = -1 / 2 := by
    rw [show 2 * π / 3 = π - π / 3 by ring, cos_pi_sub, cos_pi_div_three]; norm_num
  have h273 : √273 / 2 = √68.25 := by
    rw [show (68.25 : ℝ) = 273 / 4 by norm_num, Real.sqrt_div (by norm_num)]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 273 by norm_num)
  have hs0 : 0 < √273 := by positivity
  rw [hc]
  constructor
  · intro h
    have hd' : d = √273 / 2 := by
      have : d ^ 2 = (√273 / 2) ^ 2 := by rw [div_pow, hs]; linarith
      exact (sq_eq_sq₀ hd.le (by positivity)).mp this
    refine ⟨hd', ?_, ?_⟩ <;> rw [hd'] <;> nlinarith
  · rintro ⟨rfl, -, -⟩
    rw [div_pow, hs]; norm_num

/-- Stitz-Zeager Exercise 11.3.19: crater diameter `d` with sight lines `4` and `2` miles at `117°`:
`d² = 4² + 2² - 2·4·2 cos 117°` gives `5.22` (to hundredths): `5.215 < d < 5.225`. -/
@[kb "stitzzeager2013" "Exercise 11.3.19, p. 928"]
theorem exer_11_3_19 (d : ℝ) (hd : 0 < d) :
    d ^ 2 = 4 ^ 2 + 2 ^ 2 - 2 * 4 * 2 * cos (117 * π / 180) →
      5.215 < d ∧ d < 5.225 := by
  intro h
  obtain ⟨s1, s2⟩ := x11c_sin27
  have hc : cos (117 * π / 180) = -sin (27 * π / 180) := by
    rw [show 117 * π / 180 = 27 * π / 180 + π / 2 by ring, cos_add_pi_div_two]
  rw [hc] at h
  constructor <;> nlinarith

/-- Stitz-Zeager Exercise 11.3.20: the helicopter legs `192` (bearing `N8.2°E`) and `207` (bearing
`S68.5°E`) differ by `103.3°`, so the distance `d` between the points satisfies
`d² = 192² + 207² - 2·192·207 cos 103.3°` and `312.5 < d < 313.5` (about `313` miles). -/
@[kb "stitzzeager2013" "Exercise 11.3.20, p. 928"]
theorem exer_11_3_20 (d : ℝ) (hd : 0 < d) :
    d ^ 2 = 192 ^ 2 + 207 ^ 2 - 2 * 192 * 207 * cos (103.3 * π / 180) →
      312.5 < d ∧ d < 313.5 := by
  intro h
  have h1 := pi_gt_d2
  have h2 := pi_lt_d2
  have hx : 0 < 13.3 * π / 180 := by positivity
  have hs := sin_lt hx
  have hs2 := sin_gt_sub_cube hx
  have hc : cos (103.3 * π / 180) = -sin (13.3 * π / 180) := by
    rw [show 103.3 * π / 180 = 13.3 * π / 180 + π / 2 by ring, cos_add_pi_div_two]
  rw [hc] at h
  constructor <;> nlinarith [mul_pos hx hx, mul_pos (mul_pos hx hx) hx]

/-- Stitz-Zeager Exercise 11.3.22: the naturalist's legs `1.5` (`S80°W`) and `3` (`S17°W`) meet at the
interior angle `117°`, so her distance `d` from the lodge satisfies `d² = 1.5² + 3² - 2·1.5·3 cos 117°`
and `3.915 < d < 3.925` (about `3.92` miles). -/
@[kb "stitzzeager2013" "Exercise 11.3.22, p. 929"]
theorem exer_11_3_22 (d : ℝ) (hd : 0 < d) :
    d ^ 2 = 1.5 ^ 2 + 3 ^ 2 - 2 * 1.5 * 3 * cos (117 * π / 180) →
      3.915 < d ∧ d < 3.925 := by
  intro h
  obtain ⟨s1, s2⟩ := x11c_sin27
  have hc : cos (117 * π / 180) = -sin (27 * π / 180) := by
    rw [show 117 * π / 180 = 27 * π / 180 + π / 2 by ring, cos_add_pi_div_two]
  rw [hc] at h
  constructor <;> nlinarith

end UndergradKB.Precalculus.Course
