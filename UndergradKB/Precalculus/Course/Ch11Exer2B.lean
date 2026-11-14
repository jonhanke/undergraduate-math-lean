import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Real.Pi.Bounds
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.Course.Ch11ExerB
import UndergradKB.Precalculus.Course.Ch11ExerC

/-! # Course layer, Chapter 11 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 11.3

Triangles are encoded with `CosTri` (from `Ch11ExerC`) and `SineTri` (from `Ch11ExerB`). -/

namespace UndergradKB.Precalculus.Course

open Real

/-! ## Helpers -/

private theorem w3_arccos_iff {α t : ℝ} (h1 : -1 < t) (h2 : t < 1) :
    (0 < α ∧ α < π ∧ cos α = t) ↔ α = arccos t := by
  constructor
  · rintro ⟨h0, h1', h⟩
    rw [← h, arccos_cos h0.le h1'.le]
  · rintro rfl
    exact ⟨arccos_pos.mpr h2, arccos_lt_pi.mpr h1, cos_arccos h1.le h2.le⟩

private theorem w3_sss {α β γ a b c tα tβ tγ : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : b ^ 2 + c ^ 2 - a ^ 2 = 2 * b * c * tα) (h2 : a ^ 2 + c ^ 2 - b ^ 2 = 2 * a * c * tβ)
    (h3 : a ^ 2 + b ^ 2 - c ^ 2 = 2 * a * b * tγ)
    (t1 : -1 < tα) (t1' : tα < 1) (t2 : -1 < tβ) (t2' : tβ < 1) (t3 : -1 < tγ) (t3' : tγ < 1) :
    CosTri α β γ a b c ↔ α = arccos tα ∧ β = arccos tβ ∧ γ = arccos tγ := by
  have e1 : 2 * b * c ≠ 0 := by positivity
  have e2 : 2 * a * c ≠ 0 := by positivity
  have e3 : 2 * a * b ≠ 0 := by positivity
  constructor
  · rintro ⟨-, -, -, ⟨a0, a1⟩, ⟨b0, b1⟩, ⟨c0, c1⟩, k1, k2, k3⟩
    refine ⟨(w3_arccos_iff t1 t1').mp ⟨a0, a1, ?_⟩, (w3_arccos_iff t2 t2').mp ⟨b0, b1, ?_⟩,
      (w3_arccos_iff t3 t3').mp ⟨c0, c1, ?_⟩⟩
    · apply mul_left_cancel₀ e1; linarith
    · apply mul_left_cancel₀ e2; linarith
    · apply mul_left_cancel₀ e3; linarith
  · rintro ⟨r1, r2, r3⟩
    obtain ⟨a0, a1, ca⟩ := (w3_arccos_iff t1 t1').mpr r1
    obtain ⟨b0, b1, cb⟩ := (w3_arccos_iff t2 t2').mpr r2
    obtain ⟨c0, c1, cc⟩ := (w3_arccos_iff t3 t3').mpr r3
    refine ⟨ha, hb, hc, ⟨a0, a1⟩, ⟨b0, b1⟩, ⟨c0, c1⟩, ?_, ?_, ?_⟩
    · rw [ca]; linarith
    · rw [cb]; linarith
    · rw [cc]; linarith

private theorem w3_rot {α β γ a b c : ℝ} : CosTri α β γ a b c ↔ CosTri β γ α b c a := by
  constructor
  · rintro ⟨ha, hb, hc, hα, hβ, hγ, k1, k2, k3⟩
    exact ⟨hb, hc, ha, hβ, hγ, hα, by linarith, by linarith, by linarith⟩
  · rintro ⟨ha, hb, hc, hα, hβ, hγ, k1, k2, k3⟩
    exact ⟨hc, ha, hb, hγ, hα, hβ, by linarith, by linarith, by linarith⟩

private theorem w3_cos_bd {α : ℝ} (h0 : 0 < α) (h1 : α < π) : -1 < cos α ∧ cos α < 1 := by
  constructor
  · rw [← cos_pi]; exact cos_lt_cos_of_nonneg_of_le_pi h0.le le_rfl h1
  · rw [← cos_zero]; exact cos_lt_cos_of_nonneg_of_le_pi le_rfl h1.le h0

private theorem w3_ineq {α a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : cos α < 1) (h2 : -1 < cos α) (k : a ^ 2 = b ^ 2 + c ^ 2 - 2 * b * c * cos α) :
    a < b + c ∧ b < a + c ∧ c < a + b := by
  have hbc := mul_pos hb hc
  have e1 : a ^ 2 < (b + c) ^ 2 := by nlinarith [mul_pos hbc (show 0 < 1 + cos α by linarith)]
  have e2 : (b - c) ^ 2 < a ^ 2 := by nlinarith [mul_pos hbc (show 0 < 1 - cos α by linarith)]
  have f1 := abs_lt.mp (abs_lt_of_sq_lt_sq e1 (by positivity))
  have f2 := abs_lt.mp (abs_lt_of_sq_lt_sq e2 ha.le)
  refine ⟨f1.2, by linarith [f2.2], by linarith [f2.1]⟩

private theorem w3_tb {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (t1 : a < b + c) (t2 : b < a + c) (t3 : c < a + b) :
    -1 < (a ^ 2 + c ^ 2 - b ^ 2) / (2 * a * c) ∧ (a ^ 2 + c ^ 2 - b ^ 2) / (2 * a * c) < 1 := by
  have hp : 0 < 2 * a * c := by positivity
  constructor
  · rw [lt_div_iff₀ hp]
    nlinarith [mul_pos (show 0 < a + c - b by linarith) (show 0 < a + c + b by linarith)]
  · rw [div_lt_one hp]
    nlinarith [mul_pos (show 0 < b - a + c by linarith) (show 0 < b + a - c by linarith)]

/-- Side-angle-side: the angle `α` and its adjacent sides `b, c` determine the triangle. -/
private theorem w3_sas {α β γ a b c : ℝ} (hb : 0 < b) (hc : 0 < c) (hα0 : 0 < α) (hαπ : α < π) :
    CosTri α β γ a b c ↔ a = √(b ^ 2 + c ^ 2 - 2 * b * c * cos α) ∧
      β = arccos ((a ^ 2 + c ^ 2 - b ^ 2) / (2 * a * c)) ∧
      γ = arccos ((a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b)) := by
  obtain ⟨hc2, hc1⟩ := w3_cos_bd hα0 hαπ
  have hbc := mul_pos hb hc
  have hpos : 0 < b ^ 2 + c ^ 2 - 2 * b * c * cos α := by
    nlinarith [mul_pos hbc (show 0 < 1 - cos α by linarith), sq_nonneg (b - c)]
  constructor
  · intro h
    obtain ⟨ha, -, -, -, -, -, k1, -, -⟩ := id h
    have hae : a = √(b ^ 2 + c ^ 2 - 2 * b * c * cos α) := by rw [← k1, Real.sqrt_sq ha.le]
    obtain ⟨t1, t2, t3⟩ := w3_ineq ha hb hc hc1 hc2 k1
    obtain ⟨u1, u2⟩ := w3_tb ha hb hc t1 t2 t3
    obtain ⟨v1, v2⟩ := w3_tb ha hc hb (by linarith) t3 t2
    obtain ⟨-, r2, r3⟩ := (w3_sss (tα := cos α) (tβ := (a ^ 2 + c ^ 2 - b ^ 2) / (2 * a * c))
      (tγ := (a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b)) ha hb hc (by linarith)
      (by field_simp) (by field_simp) hc2 hc1 u1 u2 v1 v2).mp h
    exact ⟨hae, r2, r3⟩
  · rintro ⟨hae, r2, r3⟩
    have ha : 0 < a := by rw [hae]; exact Real.sqrt_pos.mpr hpos
    have k1 : a ^ 2 = b ^ 2 + c ^ 2 - 2 * b * c * cos α := by rw [hae, Real.sq_sqrt hpos.le]
    obtain ⟨t1, t2, t3⟩ := w3_ineq ha hb hc hc1 hc2 k1
    obtain ⟨u1, u2⟩ := w3_tb ha hb hc t1 t2 t3
    obtain ⟨v1, v2⟩ := w3_tb ha hc hb (by linarith) t3 t2
    exact (w3_sss (tα := cos α) (tβ := (a ^ 2 + c ^ 2 - b ^ 2) / (2 * a * c))
      (tγ := (a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b)) ha hb hc (by linarith)
      (by field_simp) (by field_simp) hc2 hc1 u1 u2 v1 v2).mpr
      ⟨(arccos_cos hα0.le hαπ.le).symm, r2, r3⟩

private theorem w3_tri_c {α β γ a b c : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hs : α + β + γ = π) (hc : 0 < c) :
    SineTri α β γ a b c ↔ a = c * sin α / sin γ ∧ b = c * sin β / sin γ := by
  have sα : 0 < sin α := sin_pos_of_pos_of_lt_pi hα (by linarith)
  have sβ : 0 < sin β := sin_pos_of_pos_of_lt_pi hβ (by linarith)
  have sγ : 0 < sin γ := sin_pos_of_pos_of_lt_pi hγ (by linarith)
  constructor
  · rintro ⟨-, -, -, -, -, -, -, h1, h2⟩
    rw [div_eq_div_iff sα.ne' sβ.ne'] at h1
    rw [div_eq_div_iff sβ.ne' sγ.ne'] at h2
    refine ⟨?_, by rw [eq_div_iff sγ.ne']; linarith⟩
    rw [eq_div_iff sγ.ne']
    apply mul_right_cancel₀ sβ.ne'
    linear_combination sin γ * h1 + sin α * h2
  · rintro ⟨ha, hb⟩
    refine ⟨hα, hβ, hγ, hs, by rw [ha]; positivity, by rw [hb]; positivity, hc, ?_, ?_⟩
    · rw [ha, hb]; field_simp
    · rw [hb]; field_simp

private theorem w3_sin_iv (x l u : ℝ) (hl : 0 ≤ l) (hlx : l ≤ x) (hxu : x ≤ u) (hu : u ≤ 1) :
    l - u ^ 3 / 6 - u ^ 5 / 100 ≤ sin x ∧ sin x ≤ u - l ^ 3 / 6 + u ^ 5 / 100 := by
  have h0 : 0 ≤ x := le_trans hl hlx
  have := Real.sin_bound (x := x) (by rw [abs_of_nonneg h0]; exact le_trans hxu hu)
  rw [abs_of_nonneg h0] at this
  have h5 : x ^ 5 ≤ u ^ 5 := pow_le_pow_left₀ h0 hxu 5
  have h3 : x ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ h0 hxu 3
  have h3' : l ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ hl hlx 3
  have := abs_le.mp this
  constructor <;> linarith [this.1, this.2]

/-! ## Section 11.3 -/

/-- Stitz-Zeager Exercise 11.3.1: `a = 7`, `b = 12`, `γ = 59.3°` gives `c = √(7² + 12² - 2·7·12 cos γ)` (about
`10.36`), and `α`, `β` are the arccosines of `(c² + 12² - 7²)/(2·12 c)` and `(c² + 7² - 12²)/(2·7 c)`
(about `35.54°` and `85.16°`). -/
@[kb "stitzzeager2013" "Exercise 11.3.1, p. 928"]
theorem exer_11_3_1 (α β c : ℝ) :
    CosTri α β (59.3 * π / 180) 7 12 c ↔
      c = √(7 ^ 2 + 12 ^ 2 - 2 * 7 * 12 * cos (59.3 * π / 180)) ∧
      α = arccos ((c ^ 2 + 12 ^ 2 - 7 ^ 2) / (2 * c * 12)) ∧
      β = arccos ((c ^ 2 + 7 ^ 2 - 12 ^ 2) / (2 * c * 7)) := by
  have hpi := pi_pos
  rw [w3_rot, w3_rot]
  exact w3_sas (by norm_num) (by norm_num) (by positivity) (by linarith)

/-- Stitz-Zeager Exercise 11.3.2: `α = 104°`, `b = 25`, `c = 37` gives `a = √(25² + 37² - 2·25·37 cos α)`
(about `49.41`), `β = arccos ((a² + 37² - 25²)/(2·37 a))` (about `29.40°`) and `γ = arccos ((a² + 25² -
37²)/(2·25 a))` (about `46.60°`). -/
@[kb "stitzzeager2013" "Exercise 11.3.2, p. 928"]
theorem exer_11_3_2 (a β γ : ℝ) :
    CosTri (104 * π / 180) β γ a 25 37 ↔
      a = √(25 ^ 2 + 37 ^ 2 - 2 * 25 * 37 * cos (104 * π / 180)) ∧
      β = arccos ((a ^ 2 + 37 ^ 2 - 25 ^ 2) / (2 * a * 37)) ∧
      γ = arccos ((a ^ 2 + 25 ^ 2 - 37 ^ 2) / (2 * a * 25)) := by
  have hpi := pi_pos
  exact w3_sas (by norm_num) (by norm_num) (by positivity) (by linarith)

/-- Stitz-Zeager Exercise 11.3.3: `a = c = 153`, `β = 8.2°` gives the isosceles triangle with
`b = √(2·153² - 2·153² cos β)` (about `21.88`) and `α = γ = arccos (b/306)` (about `85.90°`). -/
@[kb "stitzzeager2013" "Exercise 11.3.3, p. 928"]
theorem exer_11_3_3 (α γ b : ℝ) :
    CosTri α (8.2 * π / 180) γ 153 b 153 ↔
      b = √(153 ^ 2 + 153 ^ 2 - 2 * 153 * 153 * cos (8.2 * π / 180)) ∧
      γ = arccos ((b ^ 2 + 153 ^ 2 - 153 ^ 2) / (2 * b * 153)) ∧
      α = arccos ((b ^ 2 + 153 ^ 2 - 153 ^ 2) / (2 * b * 153)) := by
  have hpi := pi_pos
  rw [w3_rot]
  exact w3_sas (by norm_num) (by norm_num) (by positivity) (by linarith)

/-- Stitz-Zeager Exercise 11.3.15: `α = 42°`, `b = 117`, `c = 88` gives `a = √(117² + 88² - 2·117·88 cos α)`
(about `78.30`), `β = arccos ((a² + 88² - 117²)/(2·88 a))` (about `89.23°`) and `γ = arccos ((a² + 117² -
88²)/(2·117 a))` (about `48.77°`). -/
@[kb "stitzzeager2013" "Exercise 11.3.15, p. 928"]
theorem exer_11_3_15 (a β γ : ℝ) :
    CosTri (42 * π / 180) β γ a 117 88 ↔
      a = √(117 ^ 2 + 88 ^ 2 - 2 * 117 * 88 * cos (42 * π / 180)) ∧
      β = arccos ((a ^ 2 + 88 ^ 2 - 117 ^ 2) / (2 * a * 88)) ∧
      γ = arccos ((a ^ 2 + 117 ^ 2 - 88 ^ 2) / (2 * a * 117)) := by
  have hpi := pi_pos
  exact w3_sas (by norm_num) (by norm_num) (by positivity) (by linarith)

/-- Stitz-Zeager Exercise 11.3.16: `β = 7°`, `γ = 170°`, `c = 98.6` gives `α = 3°`,
`a = 98.6 sin 3°/sin 170°` (about `29.72`) and `b = 98.6 sin 7°/sin 170°` (about `69.2`). -/
@[kb "stitzzeager2013" "Exercise 11.3.16, p. 928"]
theorem exer_11_3_16 (α a b : ℝ) :
    SineTri α (7 * π / 180) (170 * π / 180) a b 98.6 ↔ α = 3 * π / 180 ∧
      a = 98.6 * sin (3 * π / 180) / sin (170 * π / 180) ∧
      b = 98.6 * sin (7 * π / 180) / sin (170 * π / 180) := by
  have hpi := pi_pos
  constructor
  · intro h
    have hα : α = 3 * π / 180 := by have := h.2.2.2.1; linarith
    subst hα
    exact ⟨rfl, (w3_tri_c (by positivity) (by positivity) (by positivity) (by ring) (by norm_num)).mp h⟩
  · rintro ⟨rfl, h⟩
    exact (w3_tri_c (by positivity) (by positivity) (by positivity) (by ring) (by norm_num)).mpr h

/-- Stitz-Zeager Exercise 11.3.23: the ship's legs `5` (`N23°E`) and `2` (`S41°E`) meet at the interior angle
`64°`, so its distance `d` from port satisfies `d² = 5² + 2² - 2·5·2 cos 64°`, and `4.49 < d < 4.51`
(about `4.50` miles). -/
@[kb "stitzzeager2013" "Exercise 11.3.23, p. 929"]
theorem exer_11_3_23 (d : ℝ) (hd : 0 < d) :
    d ^ 2 = 5 ^ 2 + 2 ^ 2 - 2 * 5 * 2 * cos (64 * π / 180) ↔
      d = √(5 ^ 2 + 2 ^ 2 - 2 * 5 * 2 * cos (64 * π / 180)) ∧ 4.49 < d ∧ d < 4.51 := by
  have h1 := pi_gt_d2
  have h2 := pi_lt_d2
  have hc : cos (64 * π / 180) = sin (26 * π / 180) := by
    rw [← cos_pi_div_two_sub]; congr 1; ring
  obtain ⟨s1, s2⟩ := w3_sin_iv (26 * π / 180) 0.4535 0.455 (by norm_num) (by nlinarith)
    (by nlinarith) (by norm_num)
  rw [hc]
  have hpos : 0 < (5:ℝ) ^ 2 + 2 ^ 2 - 2 * 5 * 2 * sin (26 * π / 180) := by nlinarith
  constructor
  · intro h
    have hd' : d = √(5 ^ 2 + 2 ^ 2 - 2 * 5 * 2 * sin (26 * π / 180)) := by
      rw [← h, Real.sqrt_sq hd.le]
    refine ⟨hd', ?_, ?_⟩ <;> nlinarith
  · rintro ⟨hd', -, -⟩
    rw [hd', Real.sq_sqrt hpos.le]

/-- Stitz-Zeager Exercise 11.3.24: the ship's legs `300` (to the island) and `100` (the drift) meet at `38°`
at the harbor, so its distance `d` from the island satisfies `d² = 300² + 100² - 2·300·100 cos 38°`
(about `229.61` miles). -/
@[kb "stitzzeager2013" "Exercise 11.3.24, p. 929"]
theorem exer_11_3_24 (d : ℝ) (hd : 0 < d) :
    d ^ 2 = 300 ^ 2 + 100 ^ 2 - 2 * 300 * 100 * cos (38 * π / 180) ↔
      d = √(300 ^ 2 + 100 ^ 2 - 2 * 300 * 100 * cos (38 * π / 180)) := by
  have hpi := pi_pos
  have h := w3_cos_bd (α := 38 * π / 180) (by positivity) (by linarith)
  have hpos : 0 < (300:ℝ) ^ 2 + 100 ^ 2 - 2 * 300 * 100 * cos (38 * π / 180) := by nlinarith [h.2]
  constructor
  · intro h'
    rw [← h', Real.sqrt_sq hd.le]
  · intro h'
    rw [h', Real.sq_sqrt hpos.le]

/-- Stitz-Zeager Exercise 11.3.25: the lines of sight to the fires have lengths `300/sin 2.5°` and
`300/sin 1.3°` and meet at `117°`, so the distance `d` between the fires satisfies the law of cosines
(about `17456` feet). -/
@[kb "stitzzeager2013" "Exercise 11.3.25, p. 929"]
theorem exer_11_3_25 (d : ℝ) (hd : 0 < d) :
    d ^ 2 = (300 / sin (2.5 * π / 180)) ^ 2 + (300 / sin (1.3 * π / 180)) ^ 2 -
        2 * (300 / sin (2.5 * π / 180)) * (300 / sin (1.3 * π / 180)) * cos (117 * π / 180) ↔
      d = √((300 / sin (2.5 * π / 180)) ^ 2 + (300 / sin (1.3 * π / 180)) ^ 2 -
        2 * (300 / sin (2.5 * π / 180)) * (300 / sin (1.3 * π / 180)) * cos (117 * π / 180)) := by
  have hpi := pi_pos
  have s1 : 0 < sin (2.5 * π / 180) := sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)
  have s2 : 0 < sin (1.3 * π / 180) := sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)
  have h := w3_cos_bd (α := 117 * π / 180) (by positivity) (by linarith)
  have p1 : 0 < 300 / sin (2.5 * π / 180) := by positivity
  have p2 : 0 < 300 / sin (1.3 * π / 180) := by positivity
  have hpos : 0 < (300 / sin (2.5 * π / 180)) ^ 2 + (300 / sin (1.3 * π / 180)) ^ 2 -
        2 * (300 / sin (2.5 * π / 180)) * (300 / sin (1.3 * π / 180)) * cos (117 * π / 180) := by
    nlinarith [mul_pos p1 p2, sq_nonneg (300 / sin (2.5 * π / 180) - 300 / sin (1.3 * π / 180)),
      mul_pos (mul_pos p1 p2) (show 0 < 1 - cos (117 * π / 180) by linarith [h.2])]
  constructor
  · intro h'
    rw [← h', Real.sqrt_sq hd.le]
  · intro h'
    rw [h', Real.sq_sqrt hpos.le]

end UndergradKB.Precalculus.Course
