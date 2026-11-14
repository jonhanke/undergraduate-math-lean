import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Interval.Set.Basic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 5 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 5.3 (applications) -/

namespace UndergradKB.Precalculus.Course

open Set

/-- A number `t` with `t ^ n = c`, `lo ^ n < c < hi ^ n` (all bounds nonnegative) lies strictly between `lo`, `hi`. -/
private theorem x5w7h_bound {t c lo hi : ℝ} {n : ℕ} (hn : n ≠ 0) (hlo : 0 ≤ lo) (hhi : 0 ≤ hi)
    (ht : 0 ≤ t) (h : t ^ n = c) (h1 : lo ^ n < c) (h2 : c < hi ^ n) : lo < t ∧ t < hi := by
  constructor
  · by_contra hc
    have := pow_le_pow_left₀ ht (not_lt.1 hc) n
    rw [h] at this; linarith
  · by_contra hc
    have := pow_le_pow_left₀ hhi (not_lt.1 hc) n
    rw [h] at this; linarith

private theorem x5w7h_pow16 {V : ℝ} (hV : 0 ≤ V) : (V ^ (0.16 : ℝ)) ^ (25 : ℕ) = V ^ (4 : ℕ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hV,
    show (0.16 : ℝ) * ((25 : ℕ) : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

private theorem x5w7h_pow16' {t : ℝ} (ht : 0 < t) : (t ^ (25 / 4 : ℝ)) ^ (0.16 : ℝ) = t := by
  rw [← Real.rpow_mul ht.le, show (25 / 4 : ℝ) * 0.16 = 1 by norm_num, Real.rpow_one]

/-- The National Weather Service wind chill formula `W = 35.74 + 0.6215 T - 35.75 V^0.16 + 0.4275 T V^0.16`. -/
noncomputable def ch5W7WindChill (T V : ℝ) : ℝ :=
  35.74 + 0.6215 * T - 35.75 * V ^ (0.16 : ℝ) + 0.4275 * T * V ^ (0.16 : ℝ)

/-- Stitz-Zeager Exercise 5.3.36: with cost `C(x) = 15x + 20√(100 + (30-x)²)` for `0 ≤ x ≤ 30`, the minimum
cost is about `582.29`, attained near `x = 18.66`: `C ≥ 582.28` on `[0, 30]` and `C(18.66) < 582.3`. -/
@[kb "stitzzeager2013" "Exercise 5.3.36, p. 420"]
theorem exer_5_3_36 (C : ℝ → ℝ) (hC : C = fun x => 15 * x + 20 * Real.sqrt (100 + (30 - x) ^ 2)) :
    (∀ x ∈ Icc (0 : ℝ) 30, 582.28 ≤ C x) ∧ C 18.66 < 582.3 := by
  subst hC
  constructor
  · intro x _
    simp only
    have hs := Real.sq_sqrt (show 0 ≤ 100 + (30 - x) ^ 2 by positivity)
    have hs0 := Real.sqrt_nonneg (100 + (30 - x) ^ 2)
    by_contra hc
    push Not at hc
    have h1 : 20 * Real.sqrt (100 + (30 - x) ^ 2) < 582.28 - 15 * x := by linarith
    have h2 := pow_lt_pow_left₀ h1 (by positivity) (two_ne_zero)
    nlinarith [sq_nonneg (x - 18.66)]
  · simp only
    have hs0 := Real.sqrt_nonneg (100 + (30 - 18.66) ^ 2)
    have : Real.sqrt (100 + (30 - 18.66) ^ 2) < 15.12 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    linarith

/-- Stitz-Zeager Exercise 5.3.37 (a), (b): for a cone of volume `100` and base radius `r > 0`, the height is
`h = 300/(πr²)`, and then the surface area `πr√(r²+h²)` equals `√(π²r⁶ + 90000)/r`. -/
@[kb "stitzzeager2013" "Exercise 5.3.37, p. 420"]
theorem exer_5_3_37 :
    (∀ r h : ℝ, 0 < r → (1 / 3 * Real.pi * r ^ 2 * h = 100 ↔ h = 300 / (Real.pi * r ^ 2))) ∧
    ∀ r : ℝ, 0 < r → Real.pi * r * Real.sqrt (r ^ 2 + (300 / (Real.pi * r ^ 2)) ^ 2) =
      Real.sqrt (Real.pi ^ 2 * r ^ 6 + 90000) / r := by
  have hpi := Real.pi_pos
  constructor
  · intro r h hr
    have hne : Real.pi * r ^ 2 ≠ 0 := by positivity
    rw [eq_div_iff hne]
    constructor <;> intro hh <;> linarith
  · intro r hr
    rw [eq_div_iff hr.ne']
    have hne : Real.pi * r ^ 2 ≠ 0 := by positivity
    have e : (Real.pi * r ^ 2) ^ 2 * (r ^ 2 + (300 / (Real.pi * r ^ 2)) ^ 2) =
        Real.pi ^ 2 * r ^ 6 + 90000 := by
      field_simp
      norm_num
    rw [← e, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    ring

/-- Stitz-Zeager Exercise 5.3.38 (a): at `42` degrees and wind speed `7` the wind chill is about `37.55`
degrees (it lies in `[37.545, 37.555)`). -/
@[kb "stitzzeager2013" "Exercise 5.3.38, p. 420"]
theorem exer_5_3_38_a : 37.545 ≤ ch5W7WindChill 42 7 ∧ ch5W7WindChill 42 7 < 37.555 := by
  have h := x5w7h_pow16 (V := 7) (by norm_num)
  have hb := x5w7h_bound (t := (7 : ℝ) ^ (0.16 : ℝ)) (c := 2401) (lo := 1.3651) (hi := 1.3653) (n := 25)
    (by norm_num) (by norm_num) (by norm_num) (by positivity) (by rw [h]; norm_num) (by norm_num)
    (by norm_num)
  unfold ch5W7WindChill
  constructor <;> nlinarith [hb.1, hb.2]

/-- Stitz-Zeager Exercise 5.3.38 (b): at `37` degrees, the wind chill is `30` for exactly one wind speed `V > 0`,
and it lies in `(9.835, 9.845)` (about `9.84` mph). -/
@[kb "stitzzeager2013" "Exercise 5.3.38, p. 420"]
theorem exer_5_3_38_b :
    (∃ V : ℝ, 0 < V ∧ ch5W7WindChill 37 V = 30) ∧
    ∀ V : ℝ, 0 < V → ch5W7WindChill 37 V = 30 → 9.835 < V ∧ V < 9.845 := by
  constructor
  · have ht : (0 : ℝ) < 28.7355 / 19.9325 := by norm_num
    refine ⟨(28.7355 / 19.9325 : ℝ) ^ (25 / 4 : ℝ), Real.rpow_pos_of_pos ht _, ?_⟩
    unfold ch5W7WindChill
    rw [x5w7h_pow16' ht]
    norm_num
  · intro V hV h
    unfold ch5W7WindChill at h
    have ht : V ^ (0.16 : ℝ) = 28.7355 / 19.9325 := by
      rw [eq_div_iff (by norm_num)]; linarith
    have h25 := x5w7h_pow16 (V := V) hV.le
    rw [ht] at h25
    exact x5w7h_bound (t := V) (c := (28.7355 / 19.9325 : ℝ) ^ 25) (lo := 9.835) (hi := 9.845) (n := 4)
      (by norm_num) (by norm_num) (by norm_num) hV.le h25.symm (by norm_num) (by norm_num)

/-- Stitz-Zeager Exercise 5.3.39 (b): at air temperature `28` the wind chill is `0` for exactly one wind speed
`V > 0`, about `152.29` mph (it lies in `(152.28, 152.30)`). -/
@[kb "stitzzeager2013" "Exercise 5.3.39, p. 420"]
theorem exer_5_3_39_b :
    (∃ V : ℝ, 0 < V ∧ ch5W7WindChill 28 V = 0) ∧
    ∀ V : ℝ, 0 < V → ch5W7WindChill 28 V = 0 → 152.28 < V ∧ V < 152.30 := by
  constructor
  · have ht : (0 : ℝ) < 53.142 / 23.78 := by norm_num
    refine ⟨(53.142 / 23.78 : ℝ) ^ (25 / 4 : ℝ), Real.rpow_pos_of_pos ht _, ?_⟩
    unfold ch5W7WindChill
    rw [x5w7h_pow16' ht]
    norm_num
  · intro V hV h
    unfold ch5W7WindChill at h
    have ht : V ^ (0.16 : ℝ) = 53.142 / 23.78 := by
      rw [eq_div_iff (by norm_num)]; linarith
    have h25 := x5w7h_pow16 (V := V) hV.le
    rw [ht] at h25
    exact x5w7h_bound (t := V) (c := (53.142 / 23.78 : ℝ) ^ 25) (lo := 152.28) (hi := 152.30) (n := 4)
      (by norm_num) (by norm_num) (by norm_num) hV.le h25.symm (by norm_num) (by norm_num)

end UndergradKB.Precalculus.Course
