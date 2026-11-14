import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Interval.Set.Basic
import UndergradKB.Precalculus.Radicals
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 5 (Stitz-Zeager): exercises with the book's answers (wave 8), Sections 5.2, 5.3 -/

namespace UndergradKB.Precalculus.Course

open Set

/-! ## Section 5.2: inverse functions -/

/-- Stitz-Zeager Exercise 5.2.21: for `a ≠ 0`, the inverse of `f(x) = a x + b` is `f⁻¹(y) = (y - b)/a`. -/
@[kb "stitzzeager2013" "Exercise 5.2.21, p. 406"]
theorem exer_5_2_21 (a b : ℝ) (ha : a ≠ 0) :
    (∀ x : ℝ, (a * x + b - b) / a = x) ∧ ∀ y : ℝ, a * ((y - b) / a) + b = y := by
  refine ⟨fun x => ?_, fun y => ?_⟩
  · field_simp; ring
  · field_simp; ring

/-- Stitz-Zeager Exercise 5.2.22: for `a ≠ 0`, the inverse of `f(x) = a √(x - h) + k` (`x ≥ h`) is
`f⁻¹(y) = ((y - k)/a)² + h`, defined on those `y` with `(y - k)/a ≥ 0`. -/
@[kb "stitzzeager2013" "Exercise 5.2.22, p. 406"]
theorem exer_5_2_22 (a h k : ℝ) (ha : a ≠ 0) :
    (∀ x : ℝ, h ≤ x → ((a * Real.sqrt (x - h) + k - k) / a) ^ 2 + h = x) ∧
    ∀ y : ℝ, 0 ≤ (y - k) / a → a * Real.sqrt (((y - k) / a) ^ 2 + h - h) + k = y := by
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · rw [show a * Real.sqrt (x - h) + k - k = a * Real.sqrt (x - h) by ring, mul_div_cancel_left₀ _ ha,
      Real.sq_sqrt (by linarith)]
    ring
  · rw [show ((y - k) / a) ^ 2 + h - h = ((y - k) / a) ^ 2 by ring, Real.sqrt_sq hy]
    field_simp; ring

/-- Stitz-Zeager Exercise 5.2.23: for `a ≠ 0`, the inverse of `f(x) = a x² + b x + c` on `x ≥ -b/(2a)` is
`f⁻¹(y) = -b/(2a) + √((y - c)/a + b²/(4a²))`. -/
@[kb "stitzzeager2013" "Exercise 5.2.23, p. 406"]
theorem exer_5_2_23 (a b c : ℝ) (ha : a ≠ 0) :
    (∀ x : ℝ, -b / (2 * a) ≤ x →
      -b / (2 * a) + Real.sqrt ((a * x ^ 2 + b * x + c - c) / a + b ^ 2 / (4 * a ^ 2)) = x) ∧
    ∀ y : ℝ, 0 ≤ (y - c) / a + b ^ 2 / (4 * a ^ 2) →
      a * (-b / (2 * a) + Real.sqrt ((y - c) / a + b ^ 2 / (4 * a ^ 2))) ^ 2 +
        b * (-b / (2 * a) + Real.sqrt ((y - c) / a + b ^ 2 / (4 * a ^ 2))) + c = y := by
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · have h1 : (a * x ^ 2 + b * x + c - c) / a + b ^ 2 / (4 * a ^ 2) = (x + b / (2 * a)) ^ 2 := by
      field_simp; ring
    have h2 : 0 ≤ x + b / (2 * a) := by
      have : -b / (2 * a) = -(b / (2 * a)) := by ring
      linarith
    rw [h1, Real.sqrt_sq h2]
    have : -b / (2 * a) = -(b / (2 * a)) := by ring
    linarith
  · set s := Real.sqrt ((y - c) / a + b ^ 2 / (4 * a ^ 2)) with hs
    have hs2 : s ^ 2 = (y - c) / a + b ^ 2 / (4 * a ^ 2) := Real.sq_sqrt hy
    have hD : a * s ^ 2 = y - c + b ^ 2 / (4 * a) := by
      rw [hs2]; field_simp
    have : a * (-b / (2 * a) + s) ^ 2 + b * (-b / (2 * a) + s) + c = a * s ^ 2 - b ^ 2 / (4 * a) + c := by
      field_simp; ring
    rw [this, hD]; ring

/-- Stitz-Zeager Exercise 5.2.24: if `ad - bc ≠ 0`, the inverse of `f(x) = (ax + b)/(cx + d)` is
`f⁻¹(y) = (d y - b)/(-c y + a)`, checked both ways on the points where the denominators are nonzero. -/
@[kb "stitzzeager2013" "Exercise 5.2.24, p. 406"]
theorem exer_5_2_24 (a b c d : ℝ) (h : a * d - b * c ≠ 0) :
    (∀ x : ℝ, c * x + d ≠ 0 →
      (d * ((a * x + b) / (c * x + d)) - b) / (-c * ((a * x + b) / (c * x + d)) + a) = x) ∧
    ∀ y : ℝ, -c * y + a ≠ 0 →
      (a * ((d * y - b) / (-c * y + a)) + b) / (c * ((d * y - b) / (-c * y + a)) + d) = y := by
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · have hu : (a * x + b) / (c * x + d) * (c * x + d) = a * x + b := div_mul_cancel₀ _ hx
    have e1 : d * ((a * x + b) / (c * x + d)) - b = (a * d - b * c) * x / (c * x + d) := by
      rw [eq_div_iff hx]; linear_combination d * hu
    have e2 : -c * ((a * x + b) / (c * x + d)) + a = (a * d - b * c) / (c * x + d) := by
      rw [eq_div_iff hx]; linear_combination (-c) * hu
    rw [e1, e2, div_div_div_cancel_right₀ hx]
    field_simp
  · have hv : (d * y - b) / (-c * y + a) * (-c * y + a) = d * y - b := div_mul_cancel₀ _ hy
    have e1 : a * ((d * y - b) / (-c * y + a)) + b = (a * d - b * c) * y / (-c * y + a) := by
      rw [eq_div_iff hy]; linear_combination a * hv
    have e2 : c * ((d * y - b) / (-c * y + a)) + d = (a * d - b * c) / (-c * y + a) := by
      rw [eq_div_iff hy]; linear_combination c * hv
    rw [e1, e2, div_div_div_cancel_right₀ hy]
    field_simp

/-- Stitz-Zeager Exercise 5.2.26: the Fahrenheit conversion `C(F) = (5/9)(F - 32)` and the Celsius to Fahrenheit
conversion `F(C) = (9/5) C + 32` are inverse to each other. -/
@[kb "stitzzeager2013" "Exercise 5.2.26, p. 407"]
theorem exer_5_2_26 :
    (∀ c : ℝ, (5 / 9) * ((9 / 5 * c + 32) - 32) = c) ∧ ∀ f : ℝ, 9 / 5 * ((5 / 9) * (f - 32)) + 32 = f := by
  refine ⟨fun c => ?_, fun f => ?_⟩ <;> ring

/-- Stitz-Zeager Exercise 5.2.29: a function that is strictly increasing, or strictly decreasing, on all of
its domain is one-to-one. -/
@[kb "stitzzeager2013" "Exercise 5.2.29, p. 407"]
theorem exer_5_2_29 (f : ℝ → ℝ) (h : StrictMono f ∨ StrictAnti f) : Function.Injective f := by
  rcases h with h | h
  · exact h.injective
  · exact h.injective

/-- Stitz-Zeager Exercise 5.2.33: for `f(x) = (ax + b)/(cx + d)` the condition is `ad - bc ≠ 0`: then `f` is
one-to-one on its domain, while for `ad - bc = 0` it takes the same value at all points of its domain. -/
@[kb "stitzzeager2013" "Exercise 5.2.33, p. 407"]
theorem exer_5_2_33 (a b c d : ℝ) :
    (a * d - b * c ≠ 0 → ∀ x y : ℝ, c * x + d ≠ 0 → c * y + d ≠ 0 →
      (a * x + b) / (c * x + d) = (a * y + b) / (c * y + d) → x = y) ∧
    (a * d - b * c = 0 → ∀ x y : ℝ, c * x + d ≠ 0 → c * y + d ≠ 0 →
      (a * x + b) / (c * x + d) = (a * y + b) / (c * y + d)) := by
  constructor
  · intro h x y hx hy hxy
    rw [div_eq_div_iff hx hy] at hxy
    have : (x - y) * (a * d - b * c) = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · linarith
    · exact absurd h1 h
  · intro h x y hx hy
    rw [div_eq_div_iff hx hy]
    have : (x - y) * (a * d - b * c) = 0 := by rw [h]; ring
    linarith

/-- Stitz-Zeager Exercise 5.2.28: `f(x) = 2x/(x² - 1)` is one-to-one on `(-1, 1)`, and for `x ≠ 0` in that interval
`x = (1 - √(1 + f(x)²))/f(x)` (the inverse formula; it has no meaning at `x = 0` where `f(0) = 0`). -/
@[kb "stitzzeager2013" "Exercise 5.2.28, p. 407"]
theorem exer_5_2_28 (f : ℝ → ℝ) (hf : f = fun x => 2 * x / (x ^ 2 - 1)) :
    InjOn f (Ioo (-1) 1) ∧
    (∀ x ∈ Ioo (-1 : ℝ) 1, x ≠ 0 → (1 - Real.sqrt (1 + (f x) ^ 2)) / f x = x) ∧ f 0 = 0 := by
  subst hf
  refine ⟨?_, ?_, by norm_num⟩
  · intro x hx y hy h
    simp only at h
    have hx1 : x ^ 2 - 1 ≠ 0 := by nlinarith [hx.1, hx.2]
    have hy1 : y ^ 2 - 1 ≠ 0 := by nlinarith [hy.1, hy.2]
    rw [div_eq_div_iff hx1 hy1] at h
    have h2 : (y - x) * (x * y + 1) = 0 := by linarith
    rcases mul_eq_zero.1 h2 with h3 | h3
    · linarith
    · nlinarith [hx.1, hx.2, hy.1, hy.2]
  · intro x hx hx0
    simp only
    have hd : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    have hne : x ^ 2 - 1 ≠ 0 := by intro h; linarith
    have e : 1 + (2 * x / (x ^ 2 - 1)) ^ 2 = ((x ^ 2 + 1) / (1 - x ^ 2)) ^ 2 := by
      field_simp; ring
    rw [e, Real.sqrt_sq (by positivity)]
    have : 2 * x / (x ^ 2 - 1) ≠ 0 := div_ne_zero (by simpa using hx0) hne
    rw [div_eq_iff this]
    field_simp
    ring

/-- Stitz-Zeager Exercise 5.2.32: a function is its own inverse (`f(f(x)) = x`) exactly when its graph is
symmetric about the line `y = x`: `(x, y)` on the graph implies `(y, x)` on the graph. -/
@[kb "stitzzeager2013" "Exercise 5.2.32, p. 407"]
theorem exer_5_2_32 (f : ℝ → ℝ) : (∀ x, f (f x) = x) ↔ ∀ x y, y = f x → x = f y := by
  constructor
  · intro h x y hy; rw [hy, h]
  · intro h x; exact (h x (f x) rfl).symm

/-! ## Section 5.3: other algebraic functions -/

/-- Stitz-Zeager Exercise 5.3.45: the quotient rule for radicals, `ⁿ√(x/y) = ⁿ√x / ⁿ√y` (`y ≠ 0`), for odd `n`
or non-negative radicands. -/
@[kb "stitzzeager2013" "Exercise 5.3.45, p. 422"]
theorem exer_5_3_45 {n : ℕ} (hn : n ≠ 0) {x y : ℝ} (hy : y ≠ 0) (h : Odd n ∨ (0 ≤ x ∧ 0 ≤ y)) :
    principalRoot n (x / y) = principalRoot n x / principalRoot n y :=
  principalRoot_div hn hy h

/-- Stitz-Zeager Exercise 5.3.46: `(x^(3/2))^(2/3) = x` for `x ≥ 0`. -/
@[kb "stitzzeager2013" "Exercise 5.3.46, p. 422"]
theorem exer_5_3_46 (x : ℝ) (hx : 0 ≤ x) : (x ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) = x := by
  rw [← Real.rpow_mul hx, show (3 / 2 : ℝ) * (2 / 3) = 1 by norm_num, Real.rpow_one]

/-- Stitz-Zeager Exercise 5.3.47: a real cube root of 2 is a zero of `x³ - 2`, which has no rational zero, hence
it is irrational. -/
@[kb "stitzzeager2013" "Exercise 5.3.47, p. 422"]
theorem exer_5_3_47 (r : ℝ) (hr : r ^ 3 = 2) : Irrational r := by
  refine irrational_nrt_of_notint_nrt 3 2 (by rw [hr]; norm_num) ?_ (by norm_num)
  rintro ⟨y, rfl⟩
  have h : (y : ℝ) ^ 3 = 2 := hr
  have h' : y ^ 3 = 2 := by exact_mod_cast h
  have h1 : y ≤ 1 ∨ 2 ≤ y := by omega
  rcases h1 with h1 | h1
  · nlinarith [sq_nonneg y, sq_nonneg (y - 1), sq_nonneg (y + 1)]
  · nlinarith [sq_nonneg y]

/-- Stitz-Zeager Exercise 5.3.48: for naturals `c ≥ 2`, `n ≥ 2` with `c` not an `n`-th power of a natural number,
every real `n`-th root of `c` is irrational. -/
@[kb "stitzzeager2013" "Exercise 5.3.48, p. 422"]
theorem exer_5_3_48 (n c : ℕ) (hn : 2 ≤ n) (hc : 2 ≤ c) (hp : ¬ ∃ p : ℕ, c = p ^ n)
    (r : ℝ) (hr : r ^ n = c) : Irrational r := by
  refine irrational_nrt_of_notint_nrt n (c : ℤ) (by rw [hr]; norm_cast) ?_ (by omega)
  rintro ⟨y, rfl⟩
  apply hp
  refine ⟨y.natAbs, ?_⟩
  have h : y ^ n = (c : ℤ) := by exact_mod_cast hr
  have := congrArg Int.natAbs h
  rw [Int.natAbs_pow] at this
  simpa using this.symm

end UndergradKB.Precalculus.Course
