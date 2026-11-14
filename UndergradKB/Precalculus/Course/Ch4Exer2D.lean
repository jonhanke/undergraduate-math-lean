import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.Rational

/-! # Course layer, Chapter 4 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 4.3,
applications and variation -/

namespace UndergradKB.Precalculus.Course

/-- A cylindrical can of volume `V = 2π r₀³` has least surface area `2πr² + 2V/r` at `r = r₀`. -/
private lemma w7z_can (V r0 r : ℝ) (hr0 : 0 < r0) (hr : 0 < r) (hV : V = 2 * Real.pi * r0 ^ 3) :
    2 * Real.pi * r0 ^ 2 + 2 * V / r0 ≤ 2 * Real.pi * r ^ 2 + 2 * V / r := by
  rw [hV, ← sub_nonneg]
  have hpi := Real.pi_pos
  have : (2 * Real.pi * r ^ 2 + 2 * (2 * Real.pi * r0 ^ 3) / r) -
      (2 * Real.pi * r0 ^ 2 + 2 * (2 * Real.pi * r0 ^ 3) / r0) =
      2 * Real.pi * (r - r0) ^ 2 * (r + 2 * r0) / r := by
    field_simp
    ring
  rw [this]
  positivity

/-- For `V > 0` there is `r₀ > 0` with `V = 2π r₀³`. -/
private lemma w7z_root (V : ℝ) (hV : 0 < V) : ∃ r0 : ℝ, 0 < r0 ∧ V = 2 * Real.pi * r0 ^ 3 := by
  have hpi := Real.pi_pos
  refine ⟨(V / (2 * Real.pi)) ^ (((3 : ℕ) : ℝ)⁻¹), Real.rpow_pos_of_pos (by positivity) _, ?_⟩
  have := Real.rpow_inv_natCast_pow (x := V / (2 * Real.pi)) (n := 3) (by positivity) (by norm_num)
  rw [this]
  field_simp

/-- Stitz-Zeager Exercise 4.3.26: for `C(x) = .03x³ - 4.5x² + 225x + 250` the average cost `C(x)/x` over whole
numbers of systems `x ≥ 1` is least at `x = 76`, where it is about `59.57`; at `x = 75` it is about `59.58`. -/
@[kb "stitzzeager2013" "Exercise 4.3.26, p. 366"]
theorem exer_4_3_26 (C : ℝ → ℝ) (hC : ∀ x, C x = 3 / 100 * x ^ 3 - 9 / 2 * x ^ 2 + 225 * x + 250) :
    (∀ n : ℕ, 1 ≤ n → C 76 / 76 ≤ C n / n) ∧ 59.56 < C 76 / 76 ∧ C 76 / 76 < 59.58 ∧
      59.58 < C 75 / 75 ∧ C 75 / 75 < 59.59 := by
  refine ⟨fun n hn => ?_, by rw [hC]; norm_num, by rw [hC]; norm_num, by rw [hC]; norm_num,
    by rw [hC]; norm_num⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_div_iff₀ (by norm_num) hn0]
  have key : C n * 76 - C 76 * n = ((n : ℝ) - 76) * (57 / 25 * (n : ℝ) ^ 2 - 4218 / 25 * n - 250) := by
    rw [hC, hC]; ring
  rcases le_or_gt (n : ℝ) 75 with h | h
  · have hq : 57 / 25 * (n : ℝ) ^ 2 - 4218 / 25 * n - 250 < 0 := by nlinarith
    nlinarith
  · have h76 : (76 : ℝ) ≤ n := by
      have : (75 : ℕ) < n := by exact_mod_cast h
      exact_mod_cast this
    have hq : 0 < 57 / 25 * (n : ℝ) ^ 2 - 4218 / 25 * n - 250 := by nlinarith
    nlinarith

/-- Stitz-Zeager Exercise 4.3.27: an open-top box with square base of side `x` and volume `500` has surface area
`x² + 4x(500/x²) = x² + 2000/x`, which is at least `300` with equality exactly at `x = 10` (then the height is
`500/10² = 5`). -/
@[kb "stitzzeager2013" "Exercise 4.3.27, p. 366"]
theorem exer_4_3_27 :
    (∀ x : ℝ, 0 < x → 300 ≤ x ^ 2 + 4 * x * (500 / x ^ 2)) ∧
    (∀ x : ℝ, 0 < x → (x ^ 2 + 4 * x * (500 / x ^ 2) = 300 ↔ x = 10)) ∧ (500 : ℝ) / 10 ^ 2 = 5 := by
  have key : ∀ x : ℝ, 0 < x → x ^ 2 + 4 * x * (500 / x ^ 2) - 300 = (x - 10) ^ 2 * (x + 20) / x := by
    intro x hx
    field_simp
    ring
  refine ⟨fun x hx => ?_, fun x hx => ?_, by norm_num⟩
  · have := key x hx
    have h2 : 0 ≤ (x - 10) ^ 2 * (x + 20) / x := by positivity
    linarith
  · constructor
    · intro h
      have := key x hx
      have h2 : (x - 10) ^ 2 * (x + 20) / x = 0 := by linarith
      rw [div_eq_zero_iff] at h2
      rcases h2 with h2 | h2
      · rcases mul_eq_zero.mp h2 with h3 | h3
        · have := pow_eq_zero_iff (two_ne_zero) |>.mp h3; linarith
        · linarith
      · linarith
    · rintro rfl; norm_num

/-- Stitz-Zeager Exercise 4.3.29: a garden of area `100` against a house wall, with sides `x` (along the wall) and
`y = 100/x`, needs fencing `x + 2y = x + 200/x ≥ 20√2 ≈ 28.28`, with equality exactly for `x = 10√2 ≈ 14.14`,
`y = 5√2 ≈ 7.07`. -/
@[kb "stitzzeager2013" "Exercise 4.3.29, p. 366"]
theorem exer_4_3_29 :
    (∀ x : ℝ, 0 < x → 20 * Real.sqrt 2 ≤ x + 2 * (100 / x)) ∧
    (∀ x : ℝ, 0 < x → (x + 2 * (100 / x) = 20 * Real.sqrt 2 ↔ x = 10 * Real.sqrt 2)) ∧
    100 / (10 * Real.sqrt 2) = 5 * Real.sqrt 2 ∧
    28.28 < 20 * Real.sqrt 2 ∧ 20 * Real.sqrt 2 < 28.29 ∧
    14.14 < 10 * Real.sqrt 2 ∧ 10 * Real.sqrt 2 < 14.15 ∧
    7.07 < 5 * Real.sqrt 2 ∧ 5 * Real.sqrt 2 < 7.08 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hlo : (1.414 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hhi : Real.sqrt 2 < 1.4143 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have key : ∀ x : ℝ, 0 < x → x + 2 * (100 / x) - 20 * Real.sqrt 2 = (x - 10 * Real.sqrt 2) ^ 2 / x := by
    intro x hx
    field_simp
    linear_combination (-100) * hs
  refine ⟨fun x hx => ?_, fun x hx => ?_, ?_, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith⟩
  · have := key x hx
    have h2 : 0 ≤ (x - 10 * Real.sqrt 2) ^ 2 / x := by positivity
    linarith
  · constructor
    · intro h
      have := key x hx
      have h2 : (x - 10 * Real.sqrt 2) ^ 2 / x = 0 := by linarith
      rw [div_eq_zero_iff] at h2
      rcases h2 with h2 | h2
      · have := pow_eq_zero_iff (two_ne_zero) |>.mp h2; linarith
      · linarith
    · rintro rfl
      have := key (10 * Real.sqrt 2) (by positivity)
      rw [sub_self] at this
      simp at this
      linarith
  · field_simp
    nlinarith

/-- Stitz-Zeager Exercise 4.3.30: a can of volume `33.6` with radius `r` and height `h` has `V = πr²h`,
`S = 2πr² + 2πrh`, hence `S = 2πr² + 67.2/r` for `r > 0`; the surface area is least at `r₀` with `2πr₀³ = 33.6`,
`1.748 < r₀ < 1.749` (the book: `r ≈ 1.749`), where the height is `h = 2r₀` (`3.496 < h < 3.498`). -/
@[kb "stitzzeager2013" "Exercise 4.3.30, p. 366"]
theorem exer_4_3_30 :
    (∀ r h : ℝ, 0 < r → Real.pi * r ^ 2 * h = 33.6 →
      2 * Real.pi * r ^ 2 + 2 * Real.pi * r * h = 2 * Real.pi * r ^ 2 + 67.2 / r) ∧
    ∃ r0 : ℝ, 0 < r0 ∧ 2 * Real.pi * r0 ^ 3 = 33.6 ∧ 1.748 < r0 ∧ r0 < 1.749 ∧
      Real.pi * r0 ^ 2 * (2 * r0) = 33.6 ∧
      ∀ r : ℝ, 0 < r → 2 * Real.pi * r0 ^ 2 + 67.2 / r0 ≤ 2 * Real.pi * r ^ 2 + 67.2 / r := by
  refine ⟨fun r h hr hV => ?_, ?_⟩
  · have hpi := Real.pi_pos
    have : 2 * Real.pi * r * h = 67.2 / r := by
      field_simp
      nlinarith
    rw [this]
  · obtain ⟨r0, hr0, hV⟩ := w7z_root 33.6 (by norm_num)
    have h3 := Real.pi_gt_d4
    have h4 := Real.pi_lt_d4
    refine ⟨r0, hr0, hV.symm, ?_, ?_, by nlinarith, fun r hr => ?_⟩
    · refine lt_of_not_ge fun hc => ?_
      have h5 : r0 ^ 3 ≤ 1.748 ^ 3 := pow_le_pow_left₀ hr0.le hc 3
      nlinarith [Real.pi_pos, mul_le_mul h4.le h5 (by positivity) (by norm_num)]
    · refine lt_of_not_ge fun hc => ?_
      have h5 : 1.749 ^ 3 ≤ r0 ^ 3 := pow_le_pow_left₀ (by norm_num) hc 3
      nlinarith [Real.pi_pos, mul_le_mul h3.le h5 (by norm_num) (by positivity)]
    · have := w7z_can 33.6 r0 r hr0 hr hV
      have e : 2 * (33.6 : ℝ) = 67.2 := by norm_num
      rw [e] at this
      exact this

/-- Stitz-Zeager Exercise 4.3.31: a drum of volume `7.35` has surface area `2πr² + 2(7.35)/r`; it is least at `r₀`
with `2πr₀³ = 7.35`, where `1.053 < r₀ < 1.054`, the height is `h = 2r₀` (`2.106 < h < 2.108`; the book's `2.12`
comes from using the rounded radius `1.05`) and the minimum surface area is `6πr₀²` (between `20.90` and `20.95`). -/
@[kb "stitzzeager2013" "Exercise 4.3.31, p. 367"]
theorem exer_4_3_31 :
    ∃ r0 : ℝ, 0 < r0 ∧ 2 * Real.pi * r0 ^ 3 = 7.35 ∧ 1.053 < r0 ∧ r0 < 1.054 ∧
      Real.pi * r0 ^ 2 * (2 * r0) = 7.35 ∧ 2.106 < 2 * r0 ∧ 2 * r0 < 2.108 ∧
      2 * Real.pi * r0 ^ 2 + 2 * 7.35 / r0 = 6 * Real.pi * r0 ^ 2 ∧
      20.90 < 6 * Real.pi * r0 ^ 2 ∧ 6 * Real.pi * r0 ^ 2 < 20.95 ∧
      ∀ r : ℝ, 0 < r → 2 * Real.pi * r0 ^ 2 + 2 * 7.35 / r0 ≤ 2 * Real.pi * r ^ 2 + 2 * 7.35 / r := by
  obtain ⟨r0, hr0, hV⟩ := w7z_root 7.35 (by norm_num)
  have h3 := Real.pi_gt_d4
  have h4 := Real.pi_lt_d4
  have hlo : 1.053 < r0 := by
    refine lt_of_not_ge fun hc => ?_
    have h5 : r0 ^ 3 ≤ 1.053 ^ 3 := pow_le_pow_left₀ hr0.le hc 3
    nlinarith [Real.pi_pos, mul_le_mul h4.le h5 (by positivity) (by norm_num)]
  have hhi : r0 < 1.054 := by
    refine lt_of_not_ge fun hc => ?_
    have h5 : 1.054 ^ 3 ≤ r0 ^ 3 := pow_le_pow_left₀ (by norm_num) hc 3
    nlinarith [Real.pi_pos, mul_le_mul h3.le h5 (by norm_num) (by positivity)]
  refine ⟨r0, hr0, hV.symm, hlo, hhi, by nlinarith, by linarith, by linarith, ?_, ?_, ?_,
    fun r hr => w7z_can 7.35 r0 r hr0 hr hV⟩
  · rw [hV]; field_simp; ring
  · have h6 : 1.053 ^ 2 < r0 ^ 2 := by nlinarith
    nlinarith [Real.pi_pos]
  · have h6 : r0 ^ 2 < 1.054 ^ 2 := by nlinarith
    nlinarith [Real.pi_pos]

/-! ### Variation -/

/-- Stitz-Zeager Exercise 4.3.33: `T` directly proportional to `V` means `T = kV` for a constant `k`. -/
@[kb "stitzzeager2013" "Exercise 4.3.33, p. 367"]
theorem exer_4_3_33 (T V : ℝ → ℝ) :
    UndergradKB.Precalculus.VariesDirectly T V ↔ ∃ k : ℝ, ∀ t, T t = k * V t := Iff.rfl

/-- Stitz-Zeager Exercise 4.3.34: `f` inversely proportional to `λ` means `f = k/λ` for a constant `k`. -/
@[kb "stitzzeager2013" "Exercise 4.3.34, p. 367"]
theorem exer_4_3_34 (f lam : ℝ → ℝ) :
    UndergradKB.Precalculus.VariesInversely f lam ↔ ∃ k : ℝ, ∀ t, f t = k / lam t := Iff.rfl

/-- Stitz-Zeager Exercise 4.3.35: `d` directly proportional to `m` and inversely proportional to `V` means
`d = km/V` for a constant `k`. -/
@[kb "stitzzeager2013" "Exercise 4.3.35, p. 367"]
theorem exer_4_3_35 (d m V : ℝ → ℝ) :
    UndergradKB.Precalculus.VariesDirectly d (fun t => m t / V t) ↔
      ∃ k : ℝ, ∀ t, d t = k * m t / V t := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, fun t => by rw [hk t, mul_div_assoc]⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, fun t => by rw [hk t, mul_div_assoc]⟩

/-- Stitz-Zeager Exercise 4.3.36: `P²` directly proportional to `a³` means `P² = k a³` for a constant `k`. -/
@[kb "stitzzeager2013" "Exercise 4.3.36, p. 367"]
theorem exer_4_3_36 (P a : ℝ → ℝ) :
    UndergradKB.Precalculus.VariesDirectly (fun t => P t ^ 2) (fun t => a t ^ 3) ↔
      ∃ k : ℝ, ∀ t, P t ^ 2 = k * a t ^ 3 := Iff.rfl

/-- Stitz-Zeager Exercise 4.3.38: `F` varying directly with the product `qQ` and inversely with `r²` means
`F = kqQ/r²` for a constant `k` (when `r ≠ 0`). -/
@[kb "stitzzeager2013" "Exercise 4.3.38, p. 367"]
theorem exer_4_3_38 (F q Q r : ℝ → ℝ) (hr : ∀ t, r t ≠ 0) :
    UndergradKB.Precalculus.VariesJointly (fun t => F t * r t ^ 2) q Q ↔
      ∃ k : ℝ, ∀ t, F t = k * q t * Q t / r t ^ 2 := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, fun t => ?_⟩
    have := hk t
    have h2 : r t ^ 2 ≠ 0 := pow_ne_zero 2 (hr t)
    rw [eq_div_iff h2]
    exact this
  · rintro ⟨k, hk⟩
    refine ⟨k, fun t => ?_⟩
    have h2 : r t ^ 2 ≠ 0 := pow_ne_zero 2 (hr t)
    show F t * r t ^ 2 = k * q t * Q t
    rw [hk t, div_mul_cancel₀ _ h2]

end UndergradKB.Precalculus.Course
