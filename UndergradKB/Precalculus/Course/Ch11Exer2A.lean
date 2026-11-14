import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.Real.Pi.Bounds
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.Course.Ch11ExerB

/-! # Course layer, Chapter 11 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 11.2

Triangles are encoded with `SineTri` (from `Ch11ExerB`): positive angles with sum `π`, positive sides and the
law of sines. -/

namespace UndergradKB.Precalculus.Course

open Real

/-! ## Helpers -/

private theorem w2_sines {α β γ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hs : α + β + γ = π) :
    0 < sin α ∧ 0 < sin β ∧ 0 < sin γ :=
  ⟨sin_pos_of_pos_of_lt_pi hα (by linarith), sin_pos_of_pos_of_lt_pi hβ (by linarith),
    sin_pos_of_pos_of_lt_pi hγ (by linarith)⟩

private theorem w2_tri_a {α β γ a b c : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hs : α + β + γ = π) (ha : 0 < a) :
    SineTri α β γ a b c ↔ b = a * sin β / sin α ∧ c = a * sin γ / sin α := by
  obtain ⟨sα, sβ, sγ⟩ := w2_sines hα hβ hγ hs
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

private theorem w2_tri_b {α β γ a b c : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hs : α + β + γ = π) (hb : 0 < b) :
    SineTri α β γ a b c ↔ a = b * sin α / sin β ∧ c = b * sin γ / sin β := by
  obtain ⟨sα, sβ, sγ⟩ := w2_sines hα hβ hγ hs
  constructor
  · rintro ⟨-, -, -, -, -, -, -, h1, h2⟩
    rw [div_eq_div_iff sα.ne' sβ.ne'] at h1
    rw [div_eq_div_iff sβ.ne' sγ.ne'] at h2
    exact ⟨by rw [eq_div_iff sβ.ne']; linarith, by rw [eq_div_iff sβ.ne']; linarith⟩
  · rintro ⟨ha, hc⟩
    refine ⟨hα, hβ, hγ, hs, by rw [ha]; positivity, hb, by rw [hc]; positivity, ?_, ?_⟩
    · rw [ha]; field_simp
    · rw [hc]; field_simp

private theorem w2_tri_c {α β γ a b c : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hs : α + β + γ = π) (hc : 0 < c) :
    SineTri α β γ a b c ↔ a = c * sin α / sin γ ∧ b = c * sin β / sin γ := by
  obtain ⟨sα, sβ, sγ⟩ := w2_sines hα hβ hγ hs
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

private theorem w2_swap_ab {α β γ a b c : ℝ} :
    SineTri α β γ a b c ↔ SineTri β α γ b a c := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    exact ⟨h2, h1, h3, by linarith, h6, h5, h7, h8.symm, h8.trans h9⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    exact ⟨h2, h1, h3, by linarith, h6, h5, h7, h8.symm, h8.trans h9⟩

private theorem w2_swap_ac {α β γ a b c : ℝ} :
    SineTri α β γ a b c ↔ SineTri γ β α c b a := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    exact ⟨h3, h2, h1, by linarith, h7, h6, h5, h9.symm, h8.symm⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    exact ⟨h3, h2, h1, by linarith, h7, h6, h5, h9.symm, h8.symm⟩

private theorem w2_swap_bc {α β γ a b c : ℝ} :
    SineTri α β γ a b c ↔ SineTri α γ β a c b := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    exact ⟨h1, h3, h2, by linarith, h5, h7, h6, h8.trans h9, h9.symm⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    exact ⟨h1, h3, h2, by linarith, h5, h7, h6, h8.trans h9, h9.symm⟩

/-- SSA with a shorter side opposite the unknown angle: exactly one triangle. -/
private theorem w2_ssa_one {α β γ a b c : ℝ} (hα : 0 < α) (hαπ : α < π) (ha : 0 < a) (hb : 0 < b)
    (hba : b < a) :
    SineTri α β γ a b c ↔ β = arcsin (b * sin α / a) ∧ γ = π - α - β ∧ c = a * sin γ / sin α := by
  have sα : 0 < sin α := sin_pos_of_pos_of_lt_pi hα hαπ
  have hk0 : 0 < b * sin α / a := by positivity
  have hk1 : b * sin α / a < sin α := by
    rw [div_lt_iff₀ ha]; nlinarith
  have hk2 : b * sin α / a < 1 := lt_of_lt_of_le hk1 (sin_le_one α)
  have hpi := pi_pos
  constructor
  · intro h
    obtain ⟨-, hβ, hγ, hs, -, -, -, h1, -⟩ := id h
    have hγe : γ = π - α - β := by linarith
    have sβ : 0 < sin β := sin_pos_of_pos_of_lt_pi hβ (by linarith)
    rw [div_eq_div_iff sα.ne' sβ.ne'] at h1
    have hsin : sin β = b * sin α / a := by rw [eq_div_iff ha.ne']; linarith
    have hβ2 : β ≤ π / 2 := by
      by_contra hc
      push_neg at hc
      have := sin_lt_sin_of_lt_of_le_pi_div_two (x := α) (y := π - β) (by linarith) (by linarith)
        (by linarith)
      rw [sin_pi_sub] at this
      linarith
    refine ⟨?_, hγe, ?_⟩
    · rw [← hsin]; exact (arcsin_sin (by linarith) hβ2).symm
    · exact ((w2_tri_a hα hβ hγ hs ha).mp h).2
  · rintro ⟨hβe, hγe, hce⟩
    have hsinβ : sin β = b * sin α / a := by
      rw [hβe]; exact sin_arcsin (by linarith) (by linarith)
    have hβ0 : 0 < β := by rw [hβe]; exact arcsin_pos.mpr hk0
    have hβ2 : β < π / 2 := by rw [hβe]; exact arcsin_lt_pi_div_two.mpr hk2
    have hαβ : α + β < π := by
      by_contra hc
      push_neg at hc
      have := sin_le_sin_of_le_of_le_pi_div_two (x := π - α) (y := β) (by linarith) (by linarith)
        (by linarith)
      rw [sin_pi_sub] at this
      linarith
    have hγ0 : 0 < γ := by linarith
    refine (w2_tri_a hα hβ0 hγ0 (by linarith) ha).mpr ⟨?_, hce⟩
    rw [hsinβ]; field_simp

/-- SSA with a longer side opposite the unknown angle and an acute known angle: two triangles when the
sine is at most one (here strictly below one). -/
private theorem w2_ssa_two {α β γ a b c : ℝ} (hα : 0 < α) (hαπ : α < π / 2) (ha : 0 < a) (hb : 0 < b)
    (hab : a < b) (hk : b * sin α / a < 1) :
    SineTri α β γ a b c ↔ (β = arcsin (b * sin α / a) ∨ β = π - arcsin (b * sin α / a)) ∧
      γ = π - α - β ∧ c = a * sin γ / sin α := by
  have hpi := pi_pos
  have sα : 0 < sin α := sin_pos_of_pos_of_lt_pi hα (by linarith)
  have hk0 : 0 < b * sin α / a := by positivity
  have hk1 : sin α < b * sin α / a := by
    rw [lt_div_iff₀ ha]; nlinarith
  have hA : α < arcsin (b * sin α / a) := by
    have := arcsin_lt_arcsin (x := sin α) (by linarith [sin_pos_of_pos_of_lt_pi hα (by linarith : α < π)])
      hk1 hk.le
    rwa [arcsin_sin (by linarith) (by linarith)] at this
  have hA2 : arcsin (b * sin α / a) < π / 2 := arcsin_lt_pi_div_two.mpr hk
  have hA0 : 0 < arcsin (b * sin α / a) := arcsin_pos.mpr hk0
  have hsA : sin (arcsin (b * sin α / a)) = b * sin α / a := sin_arcsin (by linarith) hk.le
  constructor
  · intro h
    obtain ⟨-, hβ, hγ, hs, -, -, -, h1, -⟩ := id h
    have hγe : γ = π - α - β := by linarith
    have sβ : 0 < sin β := sin_pos_of_pos_of_lt_pi hβ (by linarith)
    rw [div_eq_div_iff sα.ne' sβ.ne'] at h1
    have hsin : sin β = b * sin α / a := by rw [eq_div_iff ha.ne']; linarith
    refine ⟨?_, hγe, ((w2_tri_a hα hβ hγ hs ha).mp h).2⟩
    rcases le_or_gt β (π / 2) with hc | hc
    · left; rw [← hsin]; exact (arcsin_sin (by linarith) hc).symm
    · right
      have : arcsin (sin (π - β)) = π - β := arcsin_sin (by linarith) (by linarith)
      rw [sin_pi_sub, hsin] at this
      linarith
  · rintro ⟨hβe, hγe, hce⟩
    have hβ0 : 0 < β ∧ α + β < π ∧ sin β = b * sin α / a := by
      rcases hβe with h | h
      · subst h; exact ⟨hA0, by linarith, hsA⟩
      · subst h; exact ⟨by linarith, by linarith, by rw [sin_pi_sub]; exact hsA⟩
    obtain ⟨hβ0, hαβ, hsinβ⟩ := hβ0
    have hγ0 : 0 < γ := by linarith
    refine (w2_tri_a hα hβ0 hγ0 (by linarith) ha).mpr ⟨?_, hce⟩
    rw [hsinβ]; field_simp

/-- SSA with the sine ratio above one: no triangle. -/
private theorem w2_ssa_none {α a b : ℝ} (ha : 0 < a) (hk : 1 < b * sin α / a) :
    ¬ ∃ β γ c : ℝ, SineTri α β γ a b c := by
  rintro ⟨β, γ, c, hα, hβ, hγ, hs, -, -, -, h1, -⟩
  have hpi := pi_pos
  obtain ⟨sα, sβ, -⟩ := w2_sines hα hβ hγ hs
  rw [div_eq_div_iff sα.ne' sβ.ne'] at h1
  rw [lt_div_iff₀ ha] at hk
  nlinarith [sin_le_one β]

private theorem w2_cos_le (y : ℝ) (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    cos y ≤ 1 - y ^ 2 / 2 + y ^ 4 * (5 / 96) := by
  have := Real.cos_bound (x := y) (by rw [abs_of_nonneg h0]; exact h1)
  rw [abs_of_nonneg h0] at this
  have := (abs_le.mp this).2
  linarith

/-! ## Section 11.2 -/

/-- Stitz-Zeager Exercise 11.2.2: `α = 73.2°`, `β = 54.1°`, `a = 117` gives `γ = 52.7°`,
`b = 117 sin 54.1°/sin 73.2°` (about `99.00`) and `c = 117 sin 52.7°/sin 73.2°` (about `97.22`). -/
@[kb "stitzzeager2013" "Exercise 11.2.2, p. 916"]
theorem exer_11_2_2 (γ b c : ℝ) :
    SineTri (73.2 * π / 180) (54.1 * π / 180) γ 117 b c ↔ γ = 52.7 * π / 180 ∧
      b = 117 * sin (54.1 * π / 180) / sin (73.2 * π / 180) ∧
      c = 117 * sin (52.7 * π / 180) / sin (73.2 * π / 180) := by
  have hpi := pi_pos
  constructor
  · intro h
    have hγ : γ = 52.7 * π / 180 := by have := h.2.2.2.1; linarith
    subst hγ
    exact ⟨rfl, (w2_tri_a (by positivity) (by positivity) (by positivity) (by ring) (by norm_num)).mp h⟩
  · rintro ⟨rfl, h⟩
    exact (w2_tri_a (by positivity) (by positivity) (by positivity) (by ring) (by norm_num)).mpr h

/-- Stitz-Zeager Exercise 11.2.4: `α = 95°`, `β = 62°`, `a = 33.33` gives `γ = 23°`,
`b = 33.33 sin 62°/sin 95°` (about `29.54`) and `c = 33.33 sin 23°/sin 95°` (about `13.07`). -/
@[kb "stitzzeager2013" "Exercise 11.2.4, p. 916"]
theorem exer_11_2_4 (γ b c : ℝ) :
    SineTri (95 * π / 180) (62 * π / 180) γ 33.33 b c ↔ γ = 23 * π / 180 ∧
      b = 33.33 * sin (62 * π / 180) / sin (95 * π / 180) ∧
      c = 33.33 * sin (23 * π / 180) / sin (95 * π / 180) := by
  have hpi := pi_pos
  constructor
  · intro h
    have hγ : γ = 23 * π / 180 := by have := h.2.2.2.1; linarith
    subst hγ
    exact ⟨rfl, (w2_tri_a (by positivity) (by positivity) (by positivity) (by ring) (by norm_num)).mp h⟩
  · rintro ⟨rfl, h⟩
    exact (w2_tri_a (by positivity) (by positivity) (by positivity) (by ring) (by norm_num)).mpr h

/-- Stitz-Zeager Exercise 11.2.18: `β = 29.13°`, `γ = 83.95°`, `b = 314.15` gives `α = 66.92°`,
`a = 314.15 sin 66.92°/sin 29.13°` (about `593.69`) and `c = 314.15 sin 83.95°/sin 29.13°` (about `641.75`). -/
@[kb "stitzzeager2013" "Exercise 11.2.18, p. 916"]
theorem exer_11_2_18 (α a c : ℝ) :
    SineTri α (29.13 * π / 180) (83.95 * π / 180) a 314.15 c ↔ α = 66.92 * π / 180 ∧
      a = 314.15 * sin (66.92 * π / 180) / sin (29.13 * π / 180) ∧
      c = 314.15 * sin (83.95 * π / 180) / sin (29.13 * π / 180) := by
  have hpi := pi_pos
  constructor
  · intro h
    have hα : α = 66.92 * π / 180 := by have := h.2.2.2.1; linarith
    subst hα
    exact ⟨rfl, (w2_tri_b (by positivity) (by positivity) (by positivity) (by ring) (by norm_num)).mp h⟩
  · rintro ⟨rfl, h⟩
    exact (w2_tri_b (by positivity) (by positivity) (by positivity) (by ring) (by norm_num)).mpr h

/-- Stitz-Zeager Exercise 11.2.6: `α = 117°`, `a = 45`, `b = 42` gives one triangle:
`β = arcsin (42 sin 117°/45)` (about `56.3°`), `γ = π - α - β`, `c = 45 sin γ/sin 117°` (about `5.89`). -/
@[kb "stitzzeager2013" "Exercise 11.2.6, p. 916"]
theorem exer_11_2_6 (β γ c : ℝ) :
    SineTri (117 * π / 180) β γ 45 42 c ↔ β = arcsin (42 * sin (117 * π / 180) / 45) ∧
      γ = π - 117 * π / 180 - β ∧ c = 45 * sin γ / sin (117 * π / 180) := by
  have hpi := pi_pos
  exact w2_ssa_one (by positivity) (by linarith) (by norm_num) (by norm_num) (by norm_num)

/-- Stitz-Zeager Exercise 11.2.11: `α = 42°`, `a = 39`, `b = 23.5` gives one triangle:
`β = arcsin (23.5 sin 42°/39)` (about `23.78°`), `γ = π - α - β`, `c = 39 sin γ/sin 42°` (about `53.15`). -/
@[kb "stitzzeager2013" "Exercise 11.2.11, p. 916"]
theorem exer_11_2_11 (β γ c : ℝ) :
    SineTri (42 * π / 180) β γ 39 23.5 c ↔ β = arcsin (23.5 * sin (42 * π / 180) / 39) ∧
      γ = π - 42 * π / 180 - β ∧ c = 39 * sin γ / sin (42 * π / 180) := by
  have hpi := pi_pos
  exact w2_ssa_one (by positivity) (by linarith) (by norm_num) (by norm_num) (by norm_num)

/-- Stitz-Zeager Exercise 11.2.20: `α = 50°`, `a = 25`, `b = 12.5` gives one triangle:
`β = arcsin (12.5 sin 50°/25)` (about `22.52°`), `γ = π - α - β`, `c = 25 sin γ/sin 50°` (about `31.13`). -/
@[kb "stitzzeager2013" "Exercise 11.2.20, p. 916"]
theorem exer_11_2_20 (β γ c : ℝ) :
    SineTri (50 * π / 180) β γ 25 12.5 c ↔ β = arcsin (12.5 * sin (50 * π / 180) / 25) ∧
      γ = π - 50 * π / 180 - β ∧ c = 25 * sin γ / sin (50 * π / 180) := by
  have hpi := pi_pos
  exact w2_ssa_one (by positivity) (by linarith) (by norm_num) (by norm_num) (by norm_num)

/-- Stitz-Zeager Exercise 11.2.15: `β = 102°`, `b = 16.75`, `c = 13` gives one triangle:
`γ = arcsin (13 sin 102°/16.75)` (about `49.39°`), `α = π - β - γ`, `a = 16.75 sin α/sin 102°`
(about `8.20`). -/
@[kb "stitzzeager2013" "Exercise 11.2.15, p. 916"]
theorem exer_11_2_15 (α γ a : ℝ) :
    SineTri α (102 * π / 180) γ a 16.75 13 ↔ γ = arcsin (13 * sin (102 * π / 180) / 16.75) ∧
      α = π - 102 * π / 180 - γ ∧ a = 16.75 * sin α / sin (102 * π / 180) := by
  have hpi := pi_pos
  rw [w2_swap_bc, w2_swap_ac]
  exact w2_ssa_one (by positivity) (by linarith) (by norm_num) (by norm_num) (by norm_num)

private theorem w2_cos_lt (y l u : ℝ) (hl : 0 ≤ l) (hly : l ≤ y) (hyu : y ≤ u) (hu : u ≤ 1) :
    cos y ≤ 1 - l ^ 2 / 2 + u ^ 4 * (5 / 96) := by
  have h0 : 0 ≤ y := le_trans hl hly
  have := w2_cos_le y h0 (le_trans hyu hu)
  have h2 : l ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hl hly 2
  have h4 : y ^ 4 ≤ u ^ 4 := pow_le_pow_left₀ h0 hyu 4
  nlinarith

/-- Stitz-Zeager Exercise 11.2.7: `α = 68.7°`, `a = 88`, `b = 92` gives two triangles: `β` is
`arcsin (92 sin 68.7°/88)` (about `76.9°`) or its supplement (about `103.1°`), with `γ = π - α - β` and
`c = 88 sin γ/sin 68.7°` (about `53.36` or `13.47`). -/
@[kb "stitzzeager2013" "Exercise 11.2.7, p. 916"]
theorem exer_11_2_7 (β γ c : ℝ) :
    SineTri (68.7 * π / 180) β γ 88 92 c ↔
      (β = arcsin (92 * sin (68.7 * π / 180) / 88) ∨ β = π - arcsin (92 * sin (68.7 * π / 180) / 88)) ∧
      γ = π - 68.7 * π / 180 - β ∧ c = 88 * sin γ / sin (68.7 * π / 180) := by
  have h1 := pi_gt_d2
  have h2 := pi_lt_d4
  have hs : sin (68.7 * π / 180) = cos (21.3 * π / 180) := by
    rw [← sin_pi_div_two_sub]; congr 1; ring
  have hc := w2_cos_lt (21.3 * π / 180) 0.37 0.38 (by norm_num) (by nlinarith) (by nlinarith) (by norm_num)
  apply w2_ssa_two (by positivity) (by linarith) (by norm_num) (by norm_num) (by norm_num)
  rw [hs, div_lt_one (by norm_num)]
  nlinarith

/-- Stitz-Zeager Exercise 11.2.8: `α = 42°`, `a = 17`, `b = 23.5` gives two triangles: `β` is
`arcsin (23.5 sin 42°/17)` (about `67.66°`) or its supplement (about `112.34°`), with `γ = π - α - β` and
`c = 17 sin γ/sin 42°` (about `23.93` or `11.00`). -/
@[kb "stitzzeager2013" "Exercise 11.2.8, p. 916"]
theorem exer_11_2_8 (β γ c : ℝ) :
    SineTri (42 * π / 180) β γ 17 23.5 c ↔
      (β = arcsin (23.5 * sin (42 * π / 180) / 17) ∨ β = π - arcsin (23.5 * sin (42 * π / 180) / 17)) ∧
      γ = π - 42 * π / 180 - β ∧ c = 17 * sin γ / sin (42 * π / 180) := by
  have hpi := pi_pos
  have hs : sin (42 * π / 180) ≤ √2 / 2 := by
    rw [← sin_pi_div_four]
    exact sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
  have h2 : √2 < 1.4468 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  apply w2_ssa_two (by positivity) (by linarith) (by norm_num) (by norm_num) (by norm_num)
  rw [div_lt_one (by norm_num)]
  nlinarith

/-- Stitz-Zeager Exercise 11.2.13: `α = 6°`, `a = 57`, `b = 100` gives two triangles: `β` is
`arcsin (100 sin 6°/57)` (about `169.43°` is the supplement, `10.57°` the acute value), with `γ = π - α - β`
and `c = 57 sin γ/sin 6°` (about `155.51` or `43.45`). -/
@[kb "stitzzeager2013" "Exercise 11.2.13, p. 916"]
theorem exer_11_2_13 (β γ c : ℝ) :
    SineTri (6 * π / 180) β γ 57 100 c ↔
      (β = arcsin (100 * sin (6 * π / 180) / 57) ∨ β = π - arcsin (100 * sin (6 * π / 180) / 57)) ∧
      γ = π - 6 * π / 180 - β ∧ c = 57 * sin γ / sin (6 * π / 180) := by
  have hpi := pi_pos
  have h2 := pi_lt_d2
  have hs : sin (6 * π / 180) ≤ 6 * π / 180 := sin_le (by positivity)
  apply w2_ssa_two (by positivity) (by linarith) (by norm_num) (by norm_num) (by norm_num)
  rw [div_lt_one (by norm_num)]
  nlinarith

/-- Stitz-Zeager Exercise 11.2.14: `γ = 74.6°`, `c = 3`, `a = 3.05` gives two triangles: `α` is
`arcsin (3.05 sin 74.6°/3)` (about `78.59°`) or its supplement (about `101.41°`), with `β = π - γ - α` and
`b = 3 sin β/sin 74.6°` (about `1.40` or `0.217`). -/
@[kb "stitzzeager2013" "Exercise 11.2.14, p. 916"]
theorem exer_11_2_14 (α β b : ℝ) :
    SineTri α β (74.6 * π / 180) 3.05 b 3 ↔
      (α = arcsin (3.05 * sin (74.6 * π / 180) / 3) ∨ α = π - arcsin (3.05 * sin (74.6 * π / 180) / 3)) ∧
      β = π - 74.6 * π / 180 - α ∧ b = 3 * sin β / sin (74.6 * π / 180) := by
  have h1 := pi_gt_d2
  have h2 := pi_lt_d4
  have hs : sin (74.6 * π / 180) = cos (15.4 * π / 180) := by
    rw [← sin_pi_div_two_sub]; congr 1; ring
  have hc := w2_cos_lt (15.4 * π / 180) 0.26 0.27 (by norm_num) (by nlinarith) (by nlinarith) (by norm_num)
  rw [w2_swap_ab, w2_swap_ac]
  apply w2_ssa_two (by positivity) (by linarith) (by norm_num) (by norm_num) (by norm_num)
  rw [hs, div_lt_one (by norm_num)]
  nlinarith

/-- Stitz-Zeager Exercise 11.2.9: `α = 68.7°`, `a = 70`, `b = 90` gives no triangle (it would need
`sin β = 90 sin 68.7°/70 > 1`). -/
@[kb "stitzzeager2013" "Exercise 11.2.9, p. 916"]
theorem exer_11_2_9 : ¬ ∃ β γ c : ℝ, SineTri (68.7 * π / 180) β γ 70 90 c := by
  have hpi := pi_pos
  have hs : √3 / 2 ≤ sin (68.7 * π / 180) := by
    rw [← sin_pi_div_three]
    exact sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
  have h3 : 1.7 < √3 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  apply w2_ssa_none (by norm_num)
  rw [lt_div_iff₀ (by norm_num)]
  nlinarith

/-- Stitz-Zeager Exercise 11.2.31: tower `A` sees the ship at `N70°E`; tower `B` is 50 miles from `A` at
`S80°E` and sees the ship at `N25°W`. The triangle has angles `30°` at `A`, `55°` at `B`, `95°` at the ship, so
the ship is `50 sin 30°/sin 95°` (about `25.1` miles) from `B`. -/
@[kb "stitzzeager2013" "Exercise 11.2.31, p. 906"]
theorem exer_11_2_31 (bs as : ℝ) :
    SineTri (30 * π / 180) (55 * π / 180) (95 * π / 180) bs as 50 ↔
      bs = 50 * sin (30 * π / 180) / sin (95 * π / 180) ∧
      as = 50 * sin (55 * π / 180) / sin (95 * π / 180) := by
  have hpi := pi_pos
  exact w2_tri_c (by positivity) (by positivity) (by positivity) (by ring) (by norm_num)

/-- Stitz-Zeager Exercise 11.2.32: the UFO triangle has angles `75°`, `50°`, `55°` over a base of `2` miles
(`10560` ft); the UFO height is `10560 sin 50° sin 75°/sin 55°` feet (about `9539`). -/
@[kb "stitzzeager2013" "Exercise 11.2.32, p. 906"]
theorem exer_11_2_32 (yu su h : ℝ) :
    (SineTri (75 * π / 180) (50 * π / 180) (55 * π / 180) yu su 10560 ∧ h = su * sin (75 * π / 180)) ↔
      yu = 10560 * sin (75 * π / 180) / sin (55 * π / 180) ∧
      su = 10560 * sin (50 * π / 180) / sin (55 * π / 180) ∧
      h = 10560 * sin (50 * π / 180) * sin (75 * π / 180) / sin (55 * π / 180) := by
  have hpi := pi_pos
  rw [w2_tri_c (by positivity) (by positivity) (by positivity) (by ring) (by norm_num)]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, by rw [h3, h2]; ring⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, by rw [h3, h2]; ring⟩

/-- Stitz-Zeager Exercise 11.2.33: the gargoyle triangle has angles `35°` (upper observer), `70°` (lower
observer, `45` ft below), `75°` (gargoyle); the distances are `45 sin 70°/sin 75°` (about `44`) and
`45 sin 35°/sin 75°` (about `27`), and the horizontal distance is `45 sin 70° sin 35°/sin 75°` (about `25`). -/
@[kb "stitzzeager2013" "Exercise 11.2.33, p. 907"]
theorem exer_11_2_33 (lo up h : ℝ) :
    (SineTri (35 * π / 180) (70 * π / 180) (75 * π / 180) lo up 45 ∧ h = up * sin (35 * π / 180)) ↔
      up = 45 * sin (70 * π / 180) / sin (75 * π / 180) ∧
      lo = 45 * sin (35 * π / 180) / sin (75 * π / 180) ∧
      h = 45 * sin (70 * π / 180) * sin (35 * π / 180) / sin (75 * π / 180) := by
  have hpi := pi_pos
  rw [w2_tri_c (by positivity) (by positivity) (by positivity) (by ring) (by norm_num)]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h2, h1, by rw [h3, h2]; ring⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h2, h1⟩, by rw [h3, h1]; ring⟩

/-- Stitz-Zeager Exercise 11.2.34: the law of sines holds in a right triangle with legs `a`, `b`,
hypotenuse `c`, where `sin α = a/c`, `sin β = b/c`, and the right angle has sine `1`. -/
@[kb "stitzzeager2013" "Exercise 11.2.34, p. 907"]
theorem exer_11_2_34 (a b c α β : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hsa : sin α = a / c)
    (hsb : sin β = b / c) :
    a / sin α = b / sin β ∧ b / sin β = c / sin (π / 2) := by
  rw [hsa, hsb, sin_pi_div_two]
  refine ⟨?_, ?_⟩ <;> field_simp

end UndergradKB.Precalculus.Course
