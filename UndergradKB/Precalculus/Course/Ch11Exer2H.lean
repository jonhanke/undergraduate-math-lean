import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Sqrt
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 11 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 11.7 (part 3)

Roots of complex numbers and complex conjugation. We write `⟨x, y⟩` for `x + y i`. -/

namespace UndergradKB.Precalculus.Course

open Real Set

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-! ## Helpers -/

private theorem w7h_s (n : ℕ) (hn : 0 < n) : √(n : ℝ) * √(n : ℝ) = n :=
  Real.mul_self_sqrt (by positivity)

private theorem w7h_sq {a z : ℂ} (h : a ^ 2 = z) (w : ℂ) : w ^ 2 = z ↔ w = a ∨ w = -a := by
  rw [← h]; exact sq_eq_sq_iff_eq_or_eq_neg

/-- The cube roots of `c³` are `c`, `c ω`, `c ω²`, where `ω = -1/2 + (√3/2) i`. -/
private theorem w7h_cube {c z a b : ℂ} (hc : c ^ 3 = z)
    (ha : c * (⟨-(1 / 2), √3 / 2⟩ : ℂ) = a) (hb : c * (⟨-(1 / 2), -(√3 / 2)⟩ : ℂ) = b) (w : ℂ) :
    w ^ 3 = z ↔ w = c ∨ w = a ∨ w = b := by
  have h3 := w7h_s 3 (by norm_num)
  push_cast at h3
  have hsum : (⟨-(1 / 2), √3 / 2⟩ : ℂ) + ⟨-(1 / 2), -(√3 / 2)⟩ = -1 := by
    apply Complex.ext <;> simp <;> norm_num
  have hprod : (⟨-(1 / 2), √3 / 2⟩ : ℂ) * ⟨-(1 / 2), -(√3 / 2)⟩ = 1 := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> nlinarith
  rw [← ha, ← hb, ← hc]
  set ω : ℂ := ⟨-(1 / 2), √3 / 2⟩
  set ω2 : ℂ := ⟨-(1 / 2), -(√3 / 2)⟩
  have fac : w ^ 3 - c ^ 3 = (w - c) * (w - c * ω) * (w - c * ω2) := by
    linear_combination (c * w ^ 2 - c ^ 2 * w) * hsum + (c ^ 3 - c ^ 2 * w) * hprod
  constructor
  · intro h
    have : (w - c) * (w - c * ω) * (w - c * ω2) = 0 := by rw [← fac, h]; ring
    rcases mul_eq_zero.mp this with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · left; exact sub_eq_zero.mp h2
      · right; left; exact sub_eq_zero.mp h2
    · right; right; exact sub_eq_zero.mp h1
  · intro h
    have : w ^ 3 - c ^ 3 = 0 := by
      rw [fac]
      rcases h with h | h | h <;> rw [h] <;> ring
    exact sub_eq_zero.mp this

/-! ## Section 11.7: roots -/

/-- Stitz-Zeager Exercise 11.7.66: the two square roots of `-25i` are `-5√2/2 + (5√2/2) i` and
`5√2/2 - (5√2/2) i`. -/
@[kb "stitzzeager2013" "Exercise 11.7.66, p. 1017"]
theorem exer_11_7_66 (w : ℂ) :
    w ^ 2 = ⟨0, -25⟩ ↔ w = ⟨-(5 * √2 / 2), 5 * √2 / 2⟩ ∨ w = ⟨5 * √2 / 2, -(5 * √2 / 2)⟩ := by
  have h2 := w7h_s 2 (by norm_num)
  push_cast at h2
  have ha : (⟨-(5 * √2 / 2), 5 * √2 / 2⟩ : ℂ) ^ 2 = ⟨0, -25⟩ := by
    apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im] <;> nlinarith
  have hb : (⟨5 * √2 / 2, -(5 * √2 / 2)⟩ : ℂ) = -⟨-(5 * √2 / 2), 5 * √2 / 2⟩ := by
    apply Complex.ext <;> simp
  rw [hb]
  exact w7h_sq ha w

/-- Stitz-Zeager Exercise 11.7.67: the two square roots of `1 + √3 i` are `√6/2 + (√2/2) i` and
`-√6/2 - (√2/2) i`. -/
@[kb "stitzzeager2013" "Exercise 11.7.67, p. 1017"]
theorem exer_11_7_67 (w : ℂ) :
    w ^ 2 = ⟨1, √3⟩ ↔ w = ⟨√6 / 2, √2 / 2⟩ ∨ w = ⟨-(√6 / 2), -(√2 / 2)⟩ := by
  have h2 := w7h_s 2 (by norm_num)
  push_cast at h2
  have h6 : √6 = √2 * √3 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have h3 := w7h_s 3 (by norm_num)
  push_cast at h3
  have ha : (⟨√6 / 2, √2 / 2⟩ : ℂ) ^ 2 = ⟨1, √3⟩ := by
    apply Complex.ext
    · simp [pow_two, Complex.mul_re, Complex.mul_im, h6]
      linear_combination ((√3 * √3) / 4 - 1 / 4) * h2 + (1 / 2) * h3
    · simp [pow_two, Complex.mul_re, Complex.mul_im, h6]
      linear_combination (√3 / 2) * h2
  have hb : (⟨-(√6 / 2), -(√2 / 2)⟩ : ℂ) = -⟨√6 / 2, √2 / 2⟩ := by
    apply Complex.ext <;> simp
  rw [hb]
  exact w7h_sq ha w

/-- Stitz-Zeager Exercise 11.7.68: the two square roots of `5/2 - (5√3/2) i` are `-√15/2 + (√5/2) i` and
`√15/2 - (√5/2) i`. -/
@[kb "stitzzeager2013" "Exercise 11.7.68, p. 1017"]
theorem exer_11_7_68 (w : ℂ) :
    w ^ 2 = ⟨5 / 2, -(5 * √3 / 2)⟩ ↔
      w = ⟨-(√15 / 2), √5 / 2⟩ ∨ w = ⟨√15 / 2, -(√5 / 2)⟩ := by
  have h5 := w7h_s 5 (by norm_num)
  have h3 := w7h_s 3 (by norm_num)
  push_cast at h5 h3
  have h15 : √15 = √5 * √3 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have ha : (⟨-(√15 / 2), √5 / 2⟩ : ℂ) ^ 2 = ⟨5 / 2, -(5 * √3 / 2)⟩ := by
    apply Complex.ext
    · simp [pow_two, Complex.mul_re, Complex.mul_im, h15]
      linear_combination ((√3 * √3) / 4 - 1 / 4) * h5 + (5 / 4) * h3
    · simp [pow_two, Complex.mul_re, Complex.mul_im, h15]
      linear_combination (-(√3 / 2)) * h5
  have hb : (⟨√15 / 2, -(√5 / 2)⟩ : ℂ) = -⟨-(√15 / 2), √5 / 2⟩ := by
    apply Complex.ext <;> simp
  rw [hb]
  exact w7h_sq ha w

/-- Stitz-Zeager Exercise 11.7.70: the three cube roots of `-125` are `5/2 + (5√3/2) i`, `-5`,
`5/2 - (5√3/2) i`. -/
@[kb "stitzzeager2013" "Exercise 11.7.70, p. 1017"]
theorem exer_11_7_70 (w : ℂ) :
    w ^ 3 = -125 ↔ w = -5 ∨ w = ⟨5 / 2, -(5 * √3 / 2)⟩ ∨ w = ⟨5 / 2, 5 * √3 / 2⟩ := by
  refine w7h_cube (by norm_num) ?_ ?_ w
  · apply Complex.ext <;> simp <;> ring
  · apply Complex.ext <;> simp <;> ring

/-- Stitz-Zeager Exercise 11.7.71: the three cube roots of `i` are `√3/2 + i/2`, `-√3/2 + i/2`, `-i`. -/
@[kb "stitzzeager2013" "Exercise 11.7.71, p. 1017"]
theorem exer_11_7_71 (w : ℂ) :
    w ^ 3 = Complex.I ↔ w = -Complex.I ∨ w = ⟨√3 / 2, 1 / 2⟩ ∨ w = ⟨-(√3 / 2), 1 / 2⟩ := by
  refine w7h_cube (by linear_combination (-Complex.I) * Complex.I_sq) ?_ ?_ w
  · apply Complex.ext <;> simp <;> ring
  · apply Complex.ext <;> simp <;> ring

/-- Stitz-Zeager Exercise 11.7.72: the three cube roots of `-8i` are `2i`, `-√3 - i`, `√3 - i`. -/
@[kb "stitzzeager2013" "Exercise 11.7.72, p. 1017"]
theorem exer_11_7_72 (w : ℂ) :
    w ^ 3 = ⟨0, -8⟩ ↔ w = 2 * Complex.I ∨ w = ⟨-√3, -1⟩ ∨ w = ⟨√3, -1⟩ := by
  refine w7h_cube ?_ ?_ ?_ w
  · apply Complex.ext <;> simp [pow_succ, Complex.mul_re, Complex.mul_im] <;> norm_num
  · apply Complex.ext <;> simp <;> ring
  · apply Complex.ext <;> simp <;> ring

/-- Stitz-Zeager Exercise 11.7.74: the four fourth roots of `-81` are `(3√2/2)(±1 ± i)`. -/
@[kb "stitzzeager2013" "Exercise 11.7.74, p. 1017"]
theorem exer_11_7_74 (w : ℂ) :
    w ^ 4 = -81 ↔ w = ⟨3 * √2 / 2, 3 * √2 / 2⟩ ∨ w = ⟨-(3 * √2 / 2), 3 * √2 / 2⟩ ∨
      w = ⟨-(3 * √2 / 2), -(3 * √2 / 2)⟩ ∨ w = ⟨3 * √2 / 2, -(3 * √2 / 2)⟩ := by
  have h2 := w7h_s 2 (by norm_num)
  push_cast at h2
  have h1 : (⟨3 * √2 / 2, 3 * √2 / 2⟩ : ℂ) ^ 2 = 9 * Complex.I := by
    apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im] <;> nlinarith
  have h3 : (⟨3 * √2 / 2, -(3 * √2 / 2)⟩ : ℂ) ^ 2 = -(9 * Complex.I) := by
    apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im] <;> nlinarith
  have e1 : (⟨-(3 * √2 / 2), -(3 * √2 / 2)⟩ : ℂ) = -⟨3 * √2 / 2, 3 * √2 / 2⟩ := by
    apply Complex.ext <;> simp
  have e2 : (⟨-(3 * √2 / 2), 3 * √2 / 2⟩ : ℂ) = -⟨3 * √2 / 2, -(3 * √2 / 2)⟩ := by
    apply Complex.ext <;> simp
  have hI : (9 * Complex.I) ^ 2 = -81 := by linear_combination 81 * Complex.I_sq
  have key : w ^ 4 = -81 ↔ w ^ 2 = 9 * Complex.I ∨ w ^ 2 = -(9 * Complex.I) := by
    rw [show w ^ 4 = (w ^ 2) ^ 2 by ring, ← hI]
    exact sq_eq_sq_iff_eq_or_eq_neg
  rw [key, w7h_sq h1 w, w7h_sq h3 w, ← e1, ← e2]
  tauto

/-- Stitz-Zeager Exercise 11.7.75: the six sixth roots of `64` are `2`, `1 + √3 i`, `-1 + √3 i`, `-2`,
`-1 - √3 i`, `1 - √3 i`. -/
@[kb "stitzzeager2013" "Exercise 11.7.75, p. 1017"]
theorem exer_11_7_75 (w : ℂ) :
    w ^ 6 = 64 ↔ w = 2 ∨ w = ⟨1, √3⟩ ∨ w = ⟨-1, √3⟩ ∨ w = -2 ∨ w = ⟨-1, -√3⟩ ∨ w = ⟨1, -√3⟩ := by
  have h3 := w7h_s 3 (by norm_num)
  push_cast at h3
  have h1 : (⟨1, √3⟩ : ℂ) ^ 2 = ⟨-2, 2 * √3⟩ := by
    apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im] <;> nlinarith [h3]
  have h2 : (⟨1, -√3⟩ : ℂ) ^ 2 = ⟨-2, -(2 * √3)⟩ := by
    apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im] <;> nlinarith [h3]
  have e1 : (⟨-1, -√3⟩ : ℂ) = -⟨1, √3⟩ := by apply Complex.ext <;> simp
  have e2 : (⟨-1, √3⟩ : ℂ) = -⟨1, -√3⟩ := by apply Complex.ext <;> simp
  have hc := w7h_cube (c := 4) (z := 64) (a := ⟨-2, 2 * √3⟩) (b := ⟨-2, -(2 * √3)⟩) (by norm_num)
    (by apply Complex.ext <;> simp <;> ring) (by apply Complex.ext <;> simp <;> ring) (w ^ 2)
  rw [show w ^ 6 = (w ^ 2) ^ 3 by ring, hc, w7h_sq (a := 2) (by norm_num) w, w7h_sq h1 w, w7h_sq h2 w,
    ← e1, ← e2]
  constructor
  · rintro ((h | h) | (h | h) | (h | h))
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · exact Or.inr (Or.inr (Or.inl h))
  · rintro (h | h | h | h | h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inl (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))

/-- Stitz-Zeager Exercise 11.7.76: the six sixth roots of `-729` are `3√3/2 + 3i/2`, `3i`, `-3√3/2 + 3i/2`,
`-3√3/2 - 3i/2`, `-3i`, `3√3/2 - 3i/2`. -/
@[kb "stitzzeager2013" "Exercise 11.7.76, p. 1017"]
theorem exer_11_7_76 (w : ℂ) :
    w ^ 6 = -729 ↔ w = ⟨3 * √3 / 2, 3 / 2⟩ ∨ w = 3 * Complex.I ∨ w = ⟨-(3 * √3 / 2), 3 / 2⟩ ∨
      w = ⟨-(3 * √3 / 2), -(3 / 2)⟩ ∨ w = -(3 * Complex.I) ∨ w = ⟨3 * √3 / 2, -(3 / 2)⟩ := by
  have h3 := w7h_s 3 (by norm_num)
  push_cast at h3
  have h1 : (⟨3 * √3 / 2, 3 / 2⟩ : ℂ) ^ 2 = ⟨9 / 2, 9 * √3 / 2⟩ := by
    apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im] <;> nlinarith [h3]
  have h2 : (⟨3 * √3 / 2, -(3 / 2)⟩ : ℂ) ^ 2 = ⟨9 / 2, -(9 * √3 / 2)⟩ := by
    apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im] <;> nlinarith [h3]
  have h0 : (3 * Complex.I) ^ 2 = -9 := by linear_combination 9 * Complex.I_sq
  have e1 : (⟨-(3 * √3 / 2), -(3 / 2)⟩ : ℂ) = -⟨3 * √3 / 2, 3 / 2⟩ := by apply Complex.ext <;> simp
  have e2 : (⟨-(3 * √3 / 2), 3 / 2⟩ : ℂ) = -⟨3 * √3 / 2, -(3 / 2)⟩ := by apply Complex.ext <;> simp
  have hc := w7h_cube (c := -9) (z := -729) (a := ⟨9 / 2, -(9 * √3 / 2)⟩) (b := ⟨9 / 2, 9 * √3 / 2⟩)
    (by norm_num) (by apply Complex.ext <;> simp <;> ring) (by apply Complex.ext <;> simp <;> ring) (w ^ 2)
  rw [show w ^ 6 = (w ^ 2) ^ 3 by ring, hc, w7h_sq h0 w, w7h_sq h2 w, w7h_sq h1 w, ← e1, ← e2]
  constructor
  · rintro ((h | h) | (h | h) | (h | h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rintro (h | h | h | h | h | h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl (Or.inr h))
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inl (Or.inl h))

/-- Stitz-Zeager Exercise 11.7.80: for `w ≠ 0`, `|1/w| = 1/|w|`. -/
@[kb "stitzzeager2013" "Exercise 11.7.80, p. 1018"]
theorem exer_11_7_80 (w : ℂ) (_hw : w ≠ 0) : ‖1 / w‖ = 1 / ‖w‖ := by
  simp [norm_inv]

/-- Stitz-Zeager Exercise 11.7.81(a): `|z̄| = |z|`. -/
@[kb "stitzzeager2013" "Exercise 11.7.81a, p. 1018"]
theorem exer_11_7_81_a (z : ℂ) : ‖(starRingEnd ℂ) z‖ = ‖z‖ := by
  simp

/-- Stitz-Zeager Exercise 11.7.81(b): `|z| = √(z z̄)` (the product `z z̄` is the real number `|z|²`). -/
@[kb "stitzzeager2013" "Exercise 11.7.81b, p. 1018"]
theorem exer_11_7_81_b (z : ℂ) : ‖z‖ = √(z * (starRingEnd ℂ) z).re := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re,
    Real.sqrt_sq (norm_nonneg _)]

/-- Stitz-Zeager Exercise 11.7.81(c): `Re z = (z + z̄)/2` and `Im z = (z - z̄)/(2i)`. -/
@[kb "stitzzeager2013" "Exercise 11.7.81c, p. 1018"]
theorem exer_11_7_81_c (z : ℂ) :
    (z.re : ℂ) = (z + (starRingEnd ℂ) z) / 2 ∧ (z.im : ℂ) = (z - (starRingEnd ℂ) z) / (2 * Complex.I) := by
  constructor
  · rw [Complex.add_conj]; push_cast; ring
  · rw [Complex.sub_conj]; push_cast
    field_simp

/-- Stitz-Zeager Exercise 11.7.81(d): if `θ` is an argument of `z` (that is, `z = |z| cis θ`) then `-θ` is an
argument of `z̄`. -/
@[kb "stitzzeager2013" "Exercise 11.7.81d, p. 1018"]
theorem exer_11_7_81_d (z : ℂ) (θ : ℝ) (h : z = (‖z‖ : ℂ) * Complex.exp (↑θ * Complex.I)) :
    (starRingEnd ℂ) z = (‖(starRingEnd ℂ) z‖ : ℂ) * Complex.exp (↑(-θ) * Complex.I) := by
  obtain ⟨r, hr⟩ : ∃ r, r = ‖z‖ := ⟨_, rfl⟩
  have hn : ‖(starRingEnd ℂ) z‖ = r := by rw [hr]; simp
  rw [← hr] at h
  rw [hn]
  clear hr hn
  subst h
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp [map_mul, Complex.conj_ofReal, Complex.conj_I]

/-- Stitz-Zeager Exercise 11.7.81(e): it is not always true that `Arg z̄ = -Arg z` (for `z = -1` both
principal arguments equal `π`). -/
@[kb "stitzzeager2013" "Exercise 11.7.81e, p. 1018"]
theorem exer_11_7_81_e : ¬ ∀ z : ℂ, Complex.arg ((starRingEnd ℂ) z) = -Complex.arg z := by
  intro h
  have h1 := h (-1)
  have e : (starRingEnd ℂ) (-1 : ℂ) = -1 := by simp
  rw [e, Complex.arg_neg_one] at h1
  linarith [pi_pos]

/-- Stitz-Zeager Exercise 11.7.82(a): `1` is an `n`th root of unity. -/
@[kb "stitzzeager2013" "Exercise 11.7.82a, p. 1018"]
theorem exer_11_7_82_a (n : ℕ) : (1 : ℂ) ^ n = 1 := one_pow n

/-- Stitz-Zeager Exercise 11.7.82(b): the product of two `n`th roots of unity is an `n`th root of unity. -/
@[kb "stitzzeager2013" "Exercise 11.7.82b, p. 1018"]
theorem exer_11_7_82_b (n : ℕ) (u v : ℂ) (hu : u ^ n = 1) (hv : v ^ n = 1) : (u * v) ^ n = 1 := by
  rw [mul_pow, hu, hv, one_mul]

/-- Stitz-Zeager Exercise 11.7.82(c): if `cis θ` is an `n`th root of unity, so is `cis (2π - θ)`, and the
two multiply to `1`. -/
@[kb "stitzzeager2013" "Exercise 11.7.82c, p. 1018"]
theorem exer_11_7_82_c (n : ℕ) (θ : ℝ) (h : Complex.exp (↑θ * Complex.I) ^ n = 1) :
    Complex.exp (↑(2 * π - θ) * Complex.I) ^ n = 1 ∧
      Complex.exp (↑θ * Complex.I) * Complex.exp (↑(2 * π - θ) * Complex.I) = 1 := by
  have e : Complex.exp (↑(2 * π - θ) * Complex.I) = (Complex.exp (↑θ * Complex.I))⁻¹ := by
    rw [← Complex.exp_neg, Complex.exp_eq_exp_iff_exists_int]
    exact ⟨1, by push_cast; ring⟩
  rw [e]
  refine ⟨by rw [inv_pow, h, inv_one], ?_⟩
  exact mul_inv_cancel₀ (Complex.exp_ne_zero _)

end UndergradKB.Precalculus.Course
