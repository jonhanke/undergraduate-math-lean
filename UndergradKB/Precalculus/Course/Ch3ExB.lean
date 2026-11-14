import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.IntervalCases
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.DescartesParity
import UndergradKB.Precalculus.Course.Ch3Ex

/-! # Course layer, Chapter 3 (Stitz-Zeager): worked examples, wave 5 -/

namespace UndergradKB.Precalculus.Course

open Set Polynomial

/-- If `q(a) ≠ 0` and `f = q * (X - a)^n`, then `a` is a zero of `f` of multiplicity exactly `n`. -/
private theorem rm_of_factor {K : Type*} [Field K] (f q : K[X]) (a : K) (n : ℕ)
    (hf : f = q * (X - C a) ^ n) (hq : q.eval a ≠ 0) : f.rootMultiplicity a = n := by
  have hq0 : q ≠ 0 := fun h => hq (by simp [h])
  rw [hf, rootMultiplicity_mul_X_sub_C_pow hq0,
    rootMultiplicity_eq_zero (by simpa [IsRoot] using hq)]
  simp

/-! ## Section 3.3 -/

/-- Stitz-Zeager Example 3.3.2: every rational zero of `f(x) = 2x⁴ + 4x³ - x² - 6x - 3` lies in the list
`±1/2, ±1, ±3/2, ±3` given by the Rational Zeros Theorem (numerators dividing `3`, denominators dividing `2`). -/
@[kb "stitzzeager2013" "Example 3.3.2, p. 282"]
theorem ex_3_3_2_rational_zero_candidates (q : ℚ)
    (hq : 2 * q ^ 4 + 4 * q ^ 3 - q ^ 2 - 6 * q - 3 = 0) :
    q ∈ ({1 / 2, -1 / 2, 1, -1, 3 / 2, -3 / 2, 3, -3} : Finset ℚ) := by
  obtain ⟨n, d, hd, hcop, rfl⟩ : ∃ n d : ℤ, 0 < d ∧ IsCoprime n d ∧ q = n / d :=
    ⟨q.num, q.den, by exact_mod_cast q.den_pos, Rat.isCoprime_num_den q, by simp [Rat.num_div_den]⟩
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have e : 2 * n ^ 4 + 4 * n ^ 3 * d - n ^ 2 * d ^ 2 - 6 * n * d ^ 3 - 3 * d ^ 4 = 0 := by
    have : ((2 * n ^ 4 + 4 * n ^ 3 * d - n ^ 2 * d ^ 2 - 6 * n * d ^ 3 - 3 * d ^ 4 : ℤ) : ℚ) = 0 := by
      push_cast
      field_simp at hq
      linarith
    exact_mod_cast this
  have h1 : d ∣ 2 * n ^ 4 :=
    ⟨-(4 * n ^ 3 - n ^ 2 * d - 6 * n * d ^ 2 - 3 * d ^ 3), by linear_combination e⟩
  have h2 : n ∣ 3 * d ^ 4 :=
    ⟨2 * n ^ 3 + 4 * n ^ 2 * d - n * d ^ 2 - 6 * d ^ 3, by linear_combination -e⟩
  have h1' : d ∣ 2 := (hcop.symm.pow_right (n := 4)).dvd_of_dvd_mul_right h1
  have h2' : n ∣ 3 := (hcop.pow_right (n := 4)).dvd_of_dvd_mul_right h2
  have hd2 : d ≤ 2 := Int.le_of_dvd (by norm_num) h1'
  have hn3 : n ≤ 3 := Int.le_of_dvd (by norm_num) h2'
  have hn3' : -n ≤ 3 := Int.le_of_dvd (by norm_num) ((neg_dvd).2 h2')
  have hd1 : 1 ≤ d := hd
  have hmem : ∀ x : ℚ, x ∈ ({1 / 2, -1 / 2, 1, -1, 3 / 2, -3 / 2, 3, -3} : Finset ℚ) ↔
      x = 1 / 2 ∨ x = -1 / 2 ∨ x = 1 ∨ x = -1 ∨ x = 3 / 2 ∨ x = -3 / 2 ∨ x = 3 ∨ x = -3 := by
    intro x; simp
  rw [hmem]
  have hn : -3 ≤ n := by omega
  interval_cases n <;> interval_cases d <;> first | (norm_num at e; done) | norm_num

/-- Stitz-Zeager Example 3.3.5: `f(x) = 2x⁴ + 4x³ - x² - 6x - 3` has `1` sign variation, and
`f(-x) = 2x⁴ - 4x³ - x² + 6x - 3` has `3`; hence, with multiplicity, `f` has exactly one positive zero and either
`3` or `1` negative zeros. -/
@[kb "stitzzeager2013" "Example 3.3.5, p. 286"]
theorem ex_3_3_5_descartes :
    (2 * X ^ 4 + 4 * X ^ 3 - X ^ 2 - 6 * X - 3 : ℝ[X]).signVariations = 1 ∧
      (2 * X ^ 4 + 4 * X ^ 3 - X ^ 2 - 6 * X - 3 : ℝ[X]).comp (-X) =
        2 * X ^ 4 - 4 * X ^ 3 - X ^ 2 + 6 * X - 3 ∧
      (2 * X ^ 4 - 4 * X ^ 3 - X ^ 2 + 6 * X - 3 : ℝ[X]).signVariations = 3 ∧
      (2 * X ^ 4 + 4 * X ^ 3 - X ^ 2 - 6 * X - 3 : ℝ[X]).roots.countP (0 < ·) = 1 ∧
      ((2 * X ^ 4 + 4 * X ^ 3 - X ^ 2 - 6 * X - 3 : ℝ[X]).roots.countP (· < 0) = 3 ∨
        (2 * X ^ 4 + 4 * X ^ 3 - X ^ 2 - 6 * X - 3 : ℝ[X]).roots.countP (· < 0) = 1) := by
  set f : ℝ[X] := 2 * X ^ 4 + 4 * X ^ 3 - X ^ 2 - 6 * X - 3 with hf
  have hf0 : f ≠ 0 := by
    intro h
    have := congrArg (fun p => p.eval 0) h
    simp [hf] at this
  have hcomp : f.comp (-X) = 2 * X ^ 4 - 4 * X ^ 3 - X ^ 2 + 6 * X - 3 := by
    simp [hf]; ring
  have hsv : f.signVariations = 1 := by
    have hdeg : f.degree = 4 := by rw [hf]; compute_degree!
    have c0 : f.coeff 0 = -3 := by simp [hf, coeff_X, coeff_X_pow]
    have c1 : f.coeff 1 = -6 := by simp [hf, coeff_X, coeff_X_pow]
    have c2 : f.coeff 2 = -1 := by simp [hf, coeff_X, coeff_X_pow]
    have c3 : f.coeff 3 = 4 := by simp [hf, coeff_X, coeff_X_pow]
    have c4 : f.coeff 4 = 2 := by simp [hf, coeff_X, coeff_X_pow]
    simp only [Polynomial.signVariations, Polynomial.coeffList, hdeg]
    simp only [show (4 : WithBot ℕ).succ = 5 from rfl]
    simp [List.range_succ, c0, c1, c2, c3, c4]
    rw [List.signVariations_congr (l₂ := ([2, 4, -1, -6, -3] : List ℤ)) (by norm_num [sign_apply])]
    decide
  have hsv' : (2 * X ^ 4 - 4 * X ^ 3 - X ^ 2 + 6 * X - 3 : ℝ[X]).signVariations = 3 := by
    set g : ℝ[X] := 2 * X ^ 4 - 4 * X ^ 3 - X ^ 2 + 6 * X - 3 with hg
    have hdeg : g.degree = 4 := by rw [hg]; compute_degree!
    have c0 : g.coeff 0 = -3 := by simp [hg, coeff_X, coeff_X_pow]
    have c1 : g.coeff 1 = 6 := by simp [hg, coeff_X, coeff_X_pow]
    have c2 : g.coeff 2 = -1 := by simp [hg, coeff_X, coeff_X_pow]
    have c3 : g.coeff 3 = -4 := by simp [hg, coeff_X, coeff_X_pow]
    have c4 : g.coeff 4 = 2 := by simp [hg, coeff_X, coeff_X_pow]
    simp only [Polynomial.signVariations, Polynomial.coeffList, hdeg]
    simp only [show (4 : WithBot ℕ).succ = 5 from rfl]
    simp [List.range_succ, c0, c1, c2, c3, c4]
    rw [List.signVariations_congr (l₂ := ([2, -4, -1, 6, -3] : List ℤ)) (by norm_num [sign_apply])]
    decide
  refine ⟨hsv, hcomp, hsv', ?_, ?_⟩
  · obtain ⟨k, hk⟩ := descartes_rule_of_signs f hf0
    omega
  · obtain ⟨k, hk⟩ := descartes_rule_of_signs_neg f hf0
    rw [hcomp, hsv'] at hk
    omega

/-! ## Section 3.4 -/

/-- The nonreal zeros `(1 ± i√3)/2` of the quadratic `x² - x + 1`. -/
private theorem quad_pair_mul (x : ℂ) :
    (x - (1 + Complex.I * Real.sqrt 3) / 2) * (x - (1 - Complex.I * Real.sqrt 3) / 2) =
      x ^ 2 - x + 1 := by
  have h3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination (-(1 : ℂ) / 4) * (Real.sqrt 3 : ℂ) ^ 2 * hI + (-(1 : ℂ) / 4 * (-1)) * h3

/-- Stitz-Zeager Example 3.4.2(1): over `ℂ`, the polynomial `12x⁵ - 20x⁴ + 19x³ - 6x² - 2x + 1` has the zero `1/2`
with multiplicity `2` and the zeros `-1/3`, `(1 + i√3)/2`, `(1 - i√3)/2` each with multiplicity `1` (together `5`). -/
@[kb "stitzzeager2013" "Example 3.4.2, p. 302"]
theorem ex_3_4_2_a_multiplicities :
    let F : ℂ[X] := 12 * X ^ 5 - 20 * X ^ 4 + 19 * X ^ 3 - 6 * X ^ 2 - 2 * X + 1
    F.rootMultiplicity (1 / 2) = 2 ∧ F.rootMultiplicity (-1 / 3) = 1 ∧
      F.rootMultiplicity ((1 + Complex.I * Real.sqrt 3) / 2) = 1 ∧
      F.rootMultiplicity ((1 - Complex.I * Real.sqrt 3) / 2) = 1 ∧
      2 + 1 + 1 + 1 = F.natDegree := by
  intro F
  set a₁ : ℂ := (1 + Complex.I * Real.sqrt 3) / 2 with ha₁
  set a₂ : ℂ := (1 - Complex.I * Real.sqrt 3) / 2 with ha₂
  have hfac : ∀ x : ℂ, F.eval x = 12 * (x - 1 / 2) ^ 2 * (x + 1 / 3) * (x - a₁) * (x - a₂) := by
    intro x
    have := (ex_3_4_2_factorizations).2 x
    simpa [F] using this
  have hs3 : (Real.sqrt 3 : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have hs3' : (Real.sqrt 3 : ℂ) ≠ 0 := by exact_mod_cast hs3
  have hpoly : F = (12 * (X - C (1 / 2)) ^ 2 * (X + C (1 / 3)) * (X - C a₁) * (X - C a₂) : ℂ[X]) := by
    apply Polynomial.funext
    intro x
    rw [hfac]; simp
  have h12 : (1 / 2 : ℂ) - a₁ ≠ 0 := by
    rw [ha₁]; intro h
    apply hs3'
    have : Complex.I * (Real.sqrt 3 : ℂ) = 0 := by linear_combination -2 * h
    simp at this
  have hC : C (-1 / 3 : ℂ) = - C (1 / 3) := by rw [← C_neg]; norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine rm_of_factor F (12 * (X + C (1 / 3)) * (X - C a₁) * (X - C a₂)) (1 / 2) 2
      (by rw [hpoly]; ring) ?_
    simp only [eval_mul, eval_ofNat, eval_add, eval_X, eval_sub, eval_C]
    have h1 : (1 / 2 : ℂ) - a₁ ≠ 0 := h12
    have h2 : (1 / 2 : ℂ) - a₂ ≠ 0 := by
      rw [ha₂]; intro h
      apply hs3'
      have : Complex.I * (Real.sqrt 3 : ℂ) = 0 := by linear_combination 2 * h
      simp at this
    have h3 : (1 / 2 : ℂ) + 1 / 3 ≠ 0 := by norm_num
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) h3) h1) h2
  · refine rm_of_factor F (12 * (X - C (1 / 2)) ^ 2 * (X - C a₁) * (X - C a₂)) (-1 / 3) 1
      (by rw [hpoly, hC]; ring) ?_
    simp only [eval_mul, eval_ofNat, eval_pow, eval_sub, eval_X, eval_C]
    have h1 : (-1 / 3 : ℂ) - 1 / 2 ≠ 0 := by norm_num
    have h2 : (-1 / 3 : ℂ) - a₁ ≠ 0 := by
      rw [ha₁]; intro h
      have h' := congrArg Complex.re h
      simp at h'
      linarith
    have h3 : (-1 / 3 : ℂ) - a₂ ≠ 0 := by
      rw [ha₂]; intro h
      have h' := congrArg Complex.re h
      simp at h'
      linarith
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ h1)) h2) h3
  · refine rm_of_factor F (12 * (X - C (1 / 2)) ^ 2 * (X + C (1 / 3)) * (X - C a₂)) a₁ 1
      (by rw [hpoly]; ring) ?_
    simp only [eval_mul, eval_ofNat, eval_pow, eval_sub, eval_add, eval_X, eval_C]
    have h1 : a₁ - 1 / 2 ≠ 0 := fun h => h12 (by linear_combination -h)
    have h2 : a₁ + 1 / 3 ≠ 0 := by
      rw [ha₁]; intro h
      have h' := congrArg Complex.re h
      simp at h'
      linarith
    have h3 : a₁ - a₂ ≠ 0 := by
      rw [ha₁, ha₂]; intro h
      apply hs3'
      have : Complex.I * (Real.sqrt 3 : ℂ) = 0 := by linear_combination h
      simp at this
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ h1)) h2) h3
  · refine rm_of_factor F (12 * (X - C (1 / 2)) ^ 2 * (X + C (1 / 3)) * (X - C a₁)) a₂ 1
      (by rw [hpoly]; ring) ?_
    simp only [eval_mul, eval_ofNat, eval_pow, eval_sub, eval_add, eval_X, eval_C]
    have h1 : a₂ - 1 / 2 ≠ 0 := by
      rw [ha₂]; intro h
      apply hs3'
      have : Complex.I * (Real.sqrt 3 : ℂ) = 0 := by linear_combination -2 * h
      simp at this
    have h2 : a₂ + 1 / 3 ≠ 0 := by
      rw [ha₂]; intro h
      have h' := congrArg Complex.re h
      simp at h'
      linarith
    have h3 : a₂ - a₁ ≠ 0 := by
      rw [ha₁, ha₂]; intro h
      apply hs3'
      have : Complex.I * (Real.sqrt 3 : ℂ) = 0 := by linear_combination -h
      simp at this
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ h1)) h2) h3
  · have : F.natDegree = 5 := by
      simp only [F]; compute_degree!
    omega

/-- Stitz-Zeager Example 3.4.3(2): the complex zeros of `x⁴ + 64` are exactly `2 + 2i`, `2 - 2i`, `-2 + 2i`,
`-2 - 2i`, and each has multiplicity `1`. -/
@[kb "stitzzeager2013" "Example 3.4.3, p. 304"]
theorem ex_3_4_3_b_all_zeros :
    (∀ z : ℂ, z ^ 4 + 64 = 0 ↔
        z = 2 + 2 * Complex.I ∨ z = 2 - 2 * Complex.I ∨ z = -2 + 2 * Complex.I ∨
          z = -2 - 2 * Complex.I) ∧
      ((X ^ 4 + 64 : ℂ[X]).rootMultiplicity (2 + 2 * Complex.I) = 1 ∧
        (X ^ 4 + 64 : ℂ[X]).rootMultiplicity (2 - 2 * Complex.I) = 1 ∧
        (X ^ 4 + 64 : ℂ[X]).rootMultiplicity (-2 + 2 * Complex.I) = 1 ∧
        (X ^ 4 + 64 : ℂ[X]).rootMultiplicity (-2 - 2 * Complex.I) = 1) := by
  have hf : ∀ z : ℂ, z ^ 4 + 64 = (z - (2 - 2 * Complex.I)) * (z - (2 + 2 * Complex.I)) *
      (z - (-2 + 2 * Complex.I)) * (z - (-2 - 2 * Complex.I)) := fun z =>
    (ex_3_4_3_x4_plus_64).2.2 z
  have hpoly : (X ^ 4 + 64 : ℂ[X]) = (X - C (2 - 2 * Complex.I)) * (X - C (2 + 2 * Complex.I)) *
      (X - C (-2 + 2 * Complex.I)) * (X - C (-2 - 2 * Complex.I)) := by
    apply Polynomial.funext
    intro x
    simp only [eval_add, eval_pow, eval_X, eval_ofNat, eval_mul, eval_sub, eval_C]
    exact hf x
  refine ⟨fun z => ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf z]
    simp only [mul_eq_zero, sub_eq_zero]
    tauto
  · refine rm_of_factor _ ((X - C (2 - 2 * Complex.I)) * (X - C (-2 + 2 * Complex.I)) *
      (X - C (-2 - 2 * Complex.I))) _ 1 (by rw [hpoly]; ring) ?_
    simp [Complex.ext_iff, sub_eq_zero]
    norm_num
  · refine rm_of_factor _ ((X - C (2 + 2 * Complex.I)) * (X - C (-2 + 2 * Complex.I)) *
      (X - C (-2 - 2 * Complex.I))) _ 1 (by rw [hpoly]; ring) ?_
    simp [Complex.ext_iff, sub_eq_zero]
    norm_num
  · refine rm_of_factor _ ((X - C (2 - 2 * Complex.I)) * (X - C (2 + 2 * Complex.I)) *
      (X - C (-2 - 2 * Complex.I))) _ 1 (by rw [hpoly]; ring) ?_
    simp [Complex.ext_iff, sub_eq_zero]
    norm_num
  · refine rm_of_factor _ ((X - C (2 - 2 * Complex.I)) * (X - C (2 + 2 * Complex.I)) *
      (X - C (-2 + 2 * Complex.I))) _ 1 (by rw [hpoly]; ring) ?_
    simp [Complex.ext_iff, sub_eq_zero]
    norm_num

end UndergradKB.Precalculus.Course
