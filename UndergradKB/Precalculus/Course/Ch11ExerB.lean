import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.Real.Pi.Bounds
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 11 (Stitz-Zeager): exercises with the book's answers

Section 11.2 (law of sines). A triangle with angles `α β γ` and opposite sides `a b c` is encoded by
`SineTri`: positive angles with sum `π`, positive sides, and the law of sines `a / sin α = b / sin β =
c / sin γ`. -/

namespace UndergradKB.Precalculus.Course

open Real

/-- A triangle with angles `α β γ` opposite the sides `a b c` (angles positive with sum `π`, sides positive,
and equal sine ratios). -/
def SineTri (α β γ a b c : ℝ) : Prop :=
  0 < α ∧ 0 < β ∧ 0 < γ ∧ α + β + γ = π ∧ 0 < a ∧ 0 < b ∧ 0 < c ∧
    a / sin α = b / sin β ∧ b / sin β = c / sin γ

/-! ## Helpers -/

private theorem x11_sines {α β γ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hs : α + β + γ = π) :
    0 < sin α ∧ 0 < sin β ∧ 0 < sin γ :=
  ⟨sin_pos_of_pos_of_lt_pi hα (by linarith), sin_pos_of_pos_of_lt_pi hβ (by linarith),
    sin_pos_of_pos_of_lt_pi hγ (by linarith)⟩

private theorem x11_tri_a {α β γ a b c : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hs : α + β + γ = π) (ha : 0 < a) :
    SineTri α β γ a b c ↔ b = a * sin β / sin α ∧ c = a * sin γ / sin α := by
  obtain ⟨sα, sβ, sγ⟩ := x11_sines hα hβ hγ hs
  constructor
  · rintro ⟨-, -, -, -, -, -, -, h1, h2⟩
    rw [div_eq_div_iff sα.ne' sβ.ne'] at h1
    rw [div_eq_div_iff sβ.ne' sγ.ne'] at h2
    refine ⟨by rw [eq_div_iff sα.ne']; linarith, ?_⟩
    rw [eq_div_iff sα.ne']
    apply mul_right_cancel₀ sβ.ne'
    linear_combination (-sin α) * h2 - sin γ * h1
  · rintro ⟨hb, hc⟩
    refine ⟨hα, hβ, hγ, hs, ha, by rw [hb]; positivity, by rw [hc]; positivity, ?_, ?_⟩
    · rw [hb]; field_simp
    · rw [hb, hc]; field_simp

private theorem x11_tri_b {α β γ a b c : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hs : α + β + γ = π) (hb : 0 < b) :
    SineTri α β γ a b c ↔ a = b * sin α / sin β ∧ c = b * sin γ / sin β := by
  obtain ⟨sα, sβ, sγ⟩ := x11_sines hα hβ hγ hs
  constructor
  · rintro ⟨-, -, -, -, -, -, -, h1, h2⟩
    rw [div_eq_div_iff sα.ne' sβ.ne'] at h1
    rw [div_eq_div_iff sβ.ne' sγ.ne'] at h2
    exact ⟨by rw [eq_div_iff sβ.ne']; linarith, by rw [eq_div_iff sβ.ne']; linarith⟩
  · rintro ⟨ha, hc⟩
    refine ⟨hα, hβ, hγ, hs, by rw [ha]; positivity, hb, by rw [hc]; positivity, ?_, ?_⟩
    · rw [ha]; field_simp
    · rw [hc]; field_simp

private theorem x11_tri_c {α β γ a b c : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hs : α + β + γ = π) (hc : 0 < c) :
    SineTri α β γ a b c ↔ a = c * sin α / sin γ ∧ b = c * sin β / sin γ := by
  obtain ⟨sα, sβ, sγ⟩ := x11_sines hα hβ hγ hs
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

private theorem x11_sin_eq_one {β : ℝ} (h0 : 0 < β) (h1 : β < π) (h : sin β = 1) : β = π / 2 := by
  obtain ⟨k, hk⟩ := Real.sin_eq_one_iff.mp h
  have hpi := pi_pos
  have hk1 : (k : ℝ) < 1 := by nlinarith
  have hk2 : (-1 : ℝ) < k := by nlinarith
  have : k = 0 := by
    have a : k < 1 := by exact_mod_cast hk1
    have b : -1 < k := by exact_mod_cast hk2
    omega
  subst this
  simp at hk
  linarith

/-! ## Section 11.2 -/

/-- Stitz-Zeager Exercise 11.2.1: the triangle with `α = 13°`, `β = 17°`, `a = 5` has `γ = 150°`,
`b = 5 sin 17°/sin 13°` (about `6.50`) and `c = 5 sin 150°/sin 13°` (about `11.11`). -/
@[kb "stitzzeager2013" "Exercise 11.2.1, p. 916"]
theorem exer_11_2_1 (γ b c : ℝ) :
    SineTri (13 * π / 180) (17 * π / 180) γ 5 b c ↔ γ = 150 * π / 180 ∧
      b = 5 * sin (17 * π / 180) / sin (13 * π / 180) ∧
      c = 5 * sin (150 * π / 180) / sin (13 * π / 180) := by
  have hpi := pi_pos
  constructor
  · intro h
    have hγ : γ = 150 * π / 180 := by have := h.2.2.2.1; linarith
    subst hγ
    exact ⟨rfl, (x11_tri_a (by positivity) (by positivity) (by positivity) (by ring) (by norm_num)).mp h⟩
  · rintro ⟨rfl, h⟩
    exact (x11_tri_a (by positivity) (by positivity) (by positivity) (by ring) (by norm_num)).mpr h

/-- Stitz-Zeager Exercise 11.2.3: `α = 95°`, `β = 85°`, `a = 33.33` gives no triangle (the two angles
already sum to `180°`). -/
@[kb "stitzzeager2013" "Exercise 11.2.3, p. 916"]
theorem exer_11_2_3 : ¬ ∃ γ b c : ℝ, SineTri (95 * π / 180) (85 * π / 180) γ 33.33 b c := by
  rintro ⟨γ, b, c, -, -, hγ, hs, -⟩
  linarith

/-- Stitz-Zeager Exercise 11.2.5: `α = 117°`, `a = 35`, `b = 42` gives no triangle (it would need
`sin β = 42 sin 117°/35 > 1`). -/
@[kb "stitzzeager2013" "Exercise 11.2.5, p. 916"]
theorem exer_11_2_5 : ¬ ∃ β γ c : ℝ, SineTri (117 * π / 180) β γ 35 42 c := by
  rintro ⟨β, γ, c, hα, hβ, hγ, hs, -, -, -, h1, -⟩
  have hpi := pi_pos
  obtain ⟨-, sβ, -⟩ := x11_sines hα hβ hγ hs
  rw [div_eq_div_iff (sin_pos_of_pos_of_lt_pi hα (by linarith)).ne' sβ.ne'] at h1
  have e : sin (117 * π / 180) = cos (27 * π / 180) := by
    rw [show 117 * π / 180 = 27 * π / 180 + π / 2 by ring, sin_add_pi_div_two]
  have hc := one_sub_sq_div_two_le_cos (x := 27 * π / 180)
  have hl := pi_lt_d2
  nlinarith [sin_le_one β]

/-- Stitz-Zeager Exercise 11.2.10: `α = 30°`, `a = 7`, `b = 14` forces a right triangle:
`β = 90°`, `γ = 60°`, `c = 7√3`. -/
@[kb "stitzzeager2013" "Exercise 11.2.10, p. 916"]
theorem exer_11_2_10 (β γ c : ℝ) :
    SineTri (π / 6) β γ 7 14 c ↔ β = π / 2 ∧ γ = π / 3 ∧ c = 7 * √3 := by
  have hpi := pi_pos
  constructor
  · intro h
    obtain ⟨hα, hβ, hγ, hs, -, -, -, h1, -⟩ := id h
    have sβ := (x11_sines hα hβ hγ hs).2.1
    rw [sin_pi_div_six, div_eq_div_iff (by norm_num) sβ.ne'] at h1
    have hb1 : β = π / 2 := x11_sin_eq_one hβ (by linarith) (by linarith)
    subst hb1
    have hγ' : γ = π / 3 := by linarith
    subst hγ'
    refine ⟨rfl, rfl, ?_⟩
    have := (x11_tri_a hα hβ hγ hs (by norm_num)).mp h |>.2
    rw [this, sin_pi_div_three, sin_pi_div_six]
    ring
  · rintro ⟨rfl, rfl, rfl⟩
    refine (x11_tri_a (by positivity) (by positivity) (by positivity) (by ring) (by norm_num)).mpr ⟨?_, ?_⟩
    · rw [sin_pi_div_two, sin_pi_div_six]; norm_num
    · rw [sin_pi_div_three, sin_pi_div_six]; ring

/-- Stitz-Zeager Exercise 11.2.12: `γ = α = 53°`, `c = 28.01` gives the isosceles triangle with `β = 74°`,
`a = 28.01` and `b = 28.01 sin 74°/sin 53°` (about `33.71`). -/
@[kb "stitzzeager2013" "Exercise 11.2.12, p. 916"]
theorem exer_11_2_12 (β a b : ℝ) :
    SineTri (53 * π / 180) β (53 * π / 180) a b 28.01 ↔ β = 74 * π / 180 ∧ a = 28.01 ∧
      b = 28.01 * sin (74 * π / 180) / sin (53 * π / 180) := by
  have hpi := pi_pos
  have s53 : 0 < sin (53 * π / 180) := sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)
  constructor
  · intro h
    have hβ : β = 74 * π / 180 := by have := h.2.2.2.1; linarith
    subst hβ
    obtain ⟨ha, hb⟩ := (x11_tri_c (by positivity) (by positivity) (by positivity) (by ring)
      (by norm_num)).mp h
    refine ⟨rfl, ?_, hb⟩
    rw [ha]; field_simp
  · rintro ⟨rfl, ha, hb⟩
    refine (x11_tri_c (by positivity) (by positivity) (by positivity) (by ring) (by norm_num)).mpr
      ⟨?_, hb⟩
    rw [ha]; field_simp

/-- Stitz-Zeager Exercise 11.2.16: `β = 102°`, `b = 16.75`, `c = 18` gives no triangle (it would need
`sin γ = 18 sin 102°/16.75 > 1`). -/
@[kb "stitzzeager2013" "Exercise 11.2.16, p. 916"]
theorem exer_11_2_16 : ¬ ∃ α γ a : ℝ, SineTri α (102 * π / 180) γ a 16.75 18 := by
  rintro ⟨α, γ, a, hα, hβ, hγ, hs, -, -, -, -, h2⟩
  have hpi := pi_pos
  obtain ⟨-, sβ, sγ⟩ := x11_sines hα hβ hγ hs
  rw [div_eq_div_iff sβ.ne' sγ.ne'] at h2
  have e : sin (102 * π / 180) = cos (12 * π / 180) := by
    rw [show 102 * π / 180 = 12 * π / 180 + π / 2 by ring, sin_add_pi_div_two]
  have hc := one_sub_sq_div_two_le_cos (x := 12 * π / 180)
  have hl := pi_lt_d2
  nlinarith [sin_le_one γ]

/-- Stitz-Zeager Exercise 11.2.17: `β = 102°`, `γ = 35°`, `b = 16.75` gives `α = 43°`,
`a = 16.75 sin 43°/sin 102°` (about `11.68`) and `c = 16.75 sin 35°/sin 102°` (about `9.82`). -/
@[kb "stitzzeager2013" "Exercise 11.2.17, p. 916"]
theorem exer_11_2_17 (α a c : ℝ) :
    SineTri α (102 * π / 180) (35 * π / 180) a 16.75 c ↔ α = 43 * π / 180 ∧
      a = 16.75 * sin (43 * π / 180) / sin (102 * π / 180) ∧
      c = 16.75 * sin (35 * π / 180) / sin (102 * π / 180) := by
  have hpi := pi_pos
  constructor
  · intro h
    have hα : α = 43 * π / 180 := by have := h.2.2.2.1; linarith
    subst hα
    exact ⟨rfl, (x11_tri_b (by positivity) (by positivity) (by positivity) (by ring) (by norm_num)).mp h⟩
  · rintro ⟨rfl, h⟩
    exact (x11_tri_b (by positivity) (by positivity) (by positivity) (by ring) (by norm_num)).mpr h

/-- Stitz-Zeager Exercise 11.2.19: `γ = 120°`, `β = 61°`, `c = 4` gives no triangle (the angles
already exceed `180°`). -/
@[kb "stitzzeager2013" "Exercise 11.2.19, p. 916"]
theorem exer_11_2_19 : ¬ ∃ α a b : ℝ, SineTri α (61 * π / 180) (120 * π / 180) a b 4 := by
  rintro ⟨α, a, b, hα, -, -, hs, -⟩
  have hpi := pi_pos
  linarith

/-- Stitz-Zeager Exercise 11.2.22: a road rising 7 per 100 horizontal makes the angle `arctan (7/100)`
with the horizontal, which is about `0.0699` radians, i.e. about `4°` (ERRATUM: the book prints
`0.699` radians; the correct value is about `0.0699`). -/
@[kb "stitzzeager2013" "Exercise 11.2.22, p. 916"]
theorem exer_11_2_22 : 0.0698 < arctan (7 / 100) ∧ arctan (7 / 100) < 0.07 := by
  refine ⟨?_, ?_⟩
  · have hy : (0 : ℝ) < 0.0698 := by norm_num
    have hlt : 0.0698 < π / 2 := by have := pi_gt_three; linarith
    rw [← arctan_tan (show -(π / 2) < 0.0698 by linarith) hlt]
    rw [arctan_lt_arctan_iff]
    have hs := sin_lt hy
    have hc := one_sub_sq_div_two_le_cos (x := 0.0698)
    rw [tan_eq_sin_div_cos, div_lt_iff₀ (by nlinarith)]
    nlinarith
  · have := arctan_lt_self (show (0 : ℝ) < 7 / 100 by norm_num)
    linarith

/-- Stitz-Zeager Exercise 11.2.23: a road at `9.65°` to the horizontal has a grade `tan 9.65°` of about
`17%`. -/
@[kb "stitzzeager2013" "Exercise 11.2.23, p. 916"]
theorem exer_11_2_23 : 0.165 < tan (9.65 * π / 180) ∧ tan (9.65 * π / 180) < 0.175 := by
  have h1 := pi_gt_d2
  have h2 := pi_lt_d2
  have hx : 0 < 9.65 * π / 180 := by positivity
  have hs := sin_lt hx
  have hs2 := sin_gt_sub_cube hx
  have hc := one_sub_sq_div_two_le_cos (x := 9.65 * π / 180)
  have hcle := cos_le_one (9.65 * π / 180)
  have hcpos : 0 < cos (9.65 * π / 180) := by nlinarith
  rw [tan_eq_sin_div_cos]
  constructor
  · rw [lt_div_iff₀ hcpos]
    nlinarith [mul_pos hx hx, mul_pos (mul_pos hx hx) hx]
  · rw [div_lt_iff₀ hcpos]
    nlinarith [mul_pos hx hx, mul_pos (mul_pos hx hx) hx]

/-- Stitz-Zeager Exercise 11.2.24: for the tree on a 7% grade, with the line of sight at `6°`, the tree
making `94°` with the road, and `500` ft of road, the height is `500 sin 6°/sin 80°`, between `52` and
`54` feet (the book says about `53`). -/
@[kb "stitzzeager2013" "Exercise 11.2.24, p. 917"]
theorem exer_11_2_24 (h d : ℝ) :
    SineTri (6 * π / 180) (94 * π / 180) (80 * π / 180) h d 500 ↔
      h = 500 * sin (6 * π / 180) / sin (80 * π / 180) ∧
        d = 500 * sin (94 * π / 180) / sin (80 * π / 180) := by
  have hpi := pi_pos
  exact x11_tri_c (by positivity) (by positivity) (by positivity) (by ring) (by norm_num)

/-- Stitz-Zeager Exercise 11.2.24 (numerical value): the height `500 sin 6°/sin 80°` lies between `52` and
`54` feet. -/
@[kb "stitzzeager2013" "Exercise 11.2.24, p. 917"]
theorem exer_11_2_24_value :
    52 < 500 * sin (6 * π / 180) / sin (80 * π / 180) ∧
      500 * sin (6 * π / 180) / sin (80 * π / 180) < 54 := by
  have h1 := pi_gt_d2
  have h2 := pi_lt_d2
  have hx : 0 < 6 * π / 180 := by positivity
  have hs := sin_lt hx
  have hs2 := sin_gt_sub_cube hx
  have e : sin (80 * π / 180) = cos (10 * π / 180) := by
    rw [show 80 * π / 180 = -(10 * π / 180) + π / 2 by ring, sin_add_pi_div_two, cos_neg]
  have hc := one_sub_sq_div_two_le_cos (x := 10 * π / 180)
  have hcle := cos_le_one (10 * π / 180)
  rw [e]
  have hcpos : 0 < cos (10 * π / 180) := by nlinarith
  constructor
  · rw [lt_div_iff₀ hcpos]
    nlinarith [mul_pos hx hx, mul_pos (mul_pos hx hx) hx]
  · rw [div_lt_iff₀ hcpos]
    nlinarith [mul_pos hx hx, mul_pos (mul_pos hx hx) hx]

/-- Stitz-Zeager Exercise 11.2.25: the compass bearings convert to standard angles (degrees): due west
`180`, `S83°E` is `270 + 83 = 353`, `N5.5°E` is `90 - 5.5 = 84.5`, due south `270`, `N31.25°W` is
`90 + 31.25 = 121.25`, `N45°E` is `45`, `S45°W` is `270 - 45 = 225`. -/
@[kb "stitzzeager2013" "Exercise 11.2.25, p. 917"]
theorem exer_11_2_25 : (270 + 83 : ℝ) = 353 ∧ (90 - 5.5 : ℝ) = 84.5 ∧ (90 + 31.25 : ℝ) = 121.25 ∧
    (90 - 45 : ℝ) = 45 ∧ (270 - 45 : ℝ) = 225 := by
  norm_num

/-- Stitz-Zeager Exercise 11.2.26: Colonel `C`, Sarge `S` (3000 ft east), fire `F` at `N42°E` from `C` and
`N20°W` from `S`; the triangle has angles `48°` at `C`, `70°` at `S`, `62°` at `F`, so `CF = 3000 sin 70°/sin 62°`
(about `3193`) and `SF = 3000 sin 48°/sin 62°` (about `2525`). -/
@[kb "stitzzeager2013" "Exercise 11.2.26, p. 918"]
theorem exer_11_2_26 (cf sf : ℝ) :
    SineTri (48 * π / 180) (70 * π / 180) (62 * π / 180) sf cf 3000 ↔
      cf = 3000 * sin (70 * π / 180) / sin (62 * π / 180) ∧
      sf = 3000 * sin (48 * π / 180) / sin (62 * π / 180) := by
  have hpi := pi_pos
  rw [x11_tri_c (by positivity) (by positivity) (by positivity) (by ring) (by norm_num)]
  exact and_comm

/-- Stitz-Zeager Exercise 11.2.27: in the hiker's triangle (angles `25°` at the point, `143°` at the
trailhead, `12°` at the observatory, trailhead-observatory side `5`), observatory to point is
`5 sin 143°/sin 25°` (about `7.12`) and point to trailhead is `5 sin 12°/sin 25°` (about `2.46`). -/
@[kb "stitzzeager2013" "Exercise 11.2.27, p. 918"]
theorem exer_11_2_27 (sm st : ℝ) :
    SineTri (25 * π / 180) (143 * π / 180) (12 * π / 180) 5 sm st ↔
      sm = 5 * sin (143 * π / 180) / sin (25 * π / 180) ∧
      st = 5 * sin (12 * π / 180) / sin (25 * π / 180) := by
  have hpi := pi_pos
  exact x11_tri_a (by positivity) (by positivity) (by positivity) (by ring) (by norm_num)

/-- Stitz-Zeager Exercise 11.2.28: the two ships and the flare form a triangle with angles `35°` (ship
`SS Bigfoot`), `55°` (`HMS Sasquatch`) and `90°` (flare); the distances from the flare are `5 sin 55°`
(about `4.1` miles) and `5 sin 35°` (about `2.9` miles). -/
@[kb "stitzzeager2013" "Exercise 11.2.28, p. 918"]
theorem exer_11_2_28 (fh fb : ℝ) :
    SineTri (35 * π / 180) (55 * π / 180) (π / 2) fh fb 5 ↔
      fb = 5 * sin (55 * π / 180) ∧ fh = 5 * sin (35 * π / 180) := by
  have hpi := pi_pos
  rw [x11_tri_c (by positivity) (by positivity) (by positivity) (by ring) (by norm_num),
    sin_pi_div_two, div_one, div_one]
  exact and_comm

/-- Stitz-Zeager Exercise 11.2.29: with Carl, Jeff and the nest forming a triangle with angles `40°`
(Carl), `20°` (Jeff), `120°` (nest) and Carl-Jeff `500`, Jeff is `500 sin 40°/sin 120°` from the nest
(about `371` feet). -/
@[kb "stitzzeager2013" "Exercise 11.2.29, p. 918"]
theorem exer_11_2_29 (jn cn : ℝ) :
    SineTri (40 * π / 180) (20 * π / 180) (120 * π / 180) jn cn 500 ↔
      jn = 500 * sin (40 * π / 180) / sin (120 * π / 180) ∧
      cn = 500 * sin (20 * π / 180) / sin (120 * π / 180) := by
  have hpi := pi_pos
  exact x11_tri_c (by positivity) (by positivity) (by positivity) (by ring) (by norm_num)

end UndergradKB.Precalculus.Course
