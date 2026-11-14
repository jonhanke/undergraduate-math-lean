import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.IntervalCases
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.DescartesParity

/-! # Course layer, Chapter 3 (Stitz-Zeager): exercises with the book's answers (wave 8), Section 3.3 -/

namespace UndergradKB.Precalculus.Course

open Set Polynomial

set_option linter.unusedSimpArgs false

/-- Stitz-Zeager Exercise 3.3.1 (Descartes' Rule of Signs): `f(x) = x ^ 3 - 2 * x ^ 2 - 5 * x + 6` has `2` sign variation(s) and
`f(-x)` has `1`; the book's counts of positive and negative zeros (with multiplicity) follow. -/
@[kb "stitzzeager2013" "Exercise 3.3.1, p. 292"]
theorem exer_3_3_1_descartes :
    (X ^ 3 - 2 * X ^ 2 - 5 * X + 6 : ℝ[X]).signVariations = 2 ∧
      (X ^ 3 - 2 * X ^ 2 - 5 * X + 6 : ℝ[X]).comp (-X) = -X ^ 3 - 2 * X ^ 2 + 5 * X + 6 ∧
      (-X ^ 3 - 2 * X ^ 2 + 5 * X + 6 : ℝ[X]).signVariations = 1 ∧
      ((X ^ 3 - 2 * X ^ 2 - 5 * X + 6 : ℝ[X]).roots.countP (0 < ·) = 2 ∨ (X ^ 3 - 2 * X ^ 2 - 5 * X + 6 : ℝ[X]).roots.countP (0 < ·) = 0) ∧
      ((X ^ 3 - 2 * X ^ 2 - 5 * X + 6 : ℝ[X]).roots.countP (· < 0) = 1) := by
  set f : ℝ[X] := X ^ 3 - 2 * X ^ 2 - 5 * X + 6 with hf
  have hf0 : f ≠ 0 := by
    intro h
    have := congrArg (fun p => p.eval 0) h
    simp [hf] at this
  have hcomp : f.comp (-X) = -X ^ 3 - 2 * X ^ 2 + 5 * X + 6 := by
    simp [hf]; ring
  have hsv : f.signVariations = 2 := by
    have hdeg : f.degree = 3 := by rw [hf]; compute_degree!
    have c0 : f.coeff 0 = 6 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c1 : f.coeff 1 = -5 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c2 : f.coeff 2 = -2 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c3 : f.coeff 3 = 1 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    simp only [Polynomial.signVariations, Polynomial.coeffList, hdeg]
    simp only [show (3 : WithBot ℕ).succ = 4 from rfl]
    simp [List.range_succ, c0, c1, c2, c3]
    rw [List.signVariations_congr (l₂ := ([1, -2, -5, 6] : List ℤ)) (by norm_num [sign_apply])]
    decide
  have hsv' : (-X ^ 3 - 2 * X ^ 2 + 5 * X + 6 : ℝ[X]).signVariations = 1 := by
    set g : ℝ[X] := -X ^ 3 - 2 * X ^ 2 + 5 * X + 6 with hg
    have hdeg : g.degree = 3 := by rw [hg]; compute_degree!
    have c0 : g.coeff 0 = 6 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c1 : g.coeff 1 = 5 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c2 : g.coeff 2 = -2 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c3 : g.coeff 3 = -1 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    simp only [Polynomial.signVariations, Polynomial.coeffList, hdeg]
    simp only [show (3 : WithBot ℕ).succ = 4 from rfl]
    simp [List.range_succ, c0, c1, c2, c3]
    rw [List.signVariations_congr (l₂ := ([-1, -2, 5, 6] : List ℤ)) (by norm_num [sign_apply])]
    decide
  refine ⟨hsv, hcomp, hsv', ?_, ?_⟩
  · obtain ⟨k, hk⟩ := descartes_rule_of_signs f hf0
    omega
  · obtain ⟨k, hk⟩ := descartes_rule_of_signs_neg f hf0
    rw [hcomp, hsv'] at hk
    omega

/-- Stitz-Zeager Exercise 3.3.2 (Descartes' Rule of Signs): `f(x) = x ^ 4 + 2 * x ^ 3 - 12 * x ^ 2 - 40 * x - 32` has `1` sign variation(s) and
`f(-x)` has `3`; the book's counts of positive and negative zeros (with multiplicity) follow. -/
@[kb "stitzzeager2013" "Exercise 3.3.2, p. 292"]
theorem exer_3_3_2_descartes :
    (X ^ 4 + 2 * X ^ 3 - 12 * X ^ 2 - 40 * X - 32 : ℝ[X]).signVariations = 1 ∧
      (X ^ 4 + 2 * X ^ 3 - 12 * X ^ 2 - 40 * X - 32 : ℝ[X]).comp (-X) = X ^ 4 - 2 * X ^ 3 - 12 * X ^ 2 + 40 * X - 32 ∧
      (X ^ 4 - 2 * X ^ 3 - 12 * X ^ 2 + 40 * X - 32 : ℝ[X]).signVariations = 3 ∧
      ((X ^ 4 + 2 * X ^ 3 - 12 * X ^ 2 - 40 * X - 32 : ℝ[X]).roots.countP (0 < ·) = 1) ∧
      ((X ^ 4 + 2 * X ^ 3 - 12 * X ^ 2 - 40 * X - 32 : ℝ[X]).roots.countP (· < 0) = 3 ∨ (X ^ 4 + 2 * X ^ 3 - 12 * X ^ 2 - 40 * X - 32 : ℝ[X]).roots.countP (· < 0) = 1) := by
  set f : ℝ[X] := X ^ 4 + 2 * X ^ 3 - 12 * X ^ 2 - 40 * X - 32 with hf
  have hf0 : f ≠ 0 := by
    intro h
    have := congrArg (fun p => p.eval 0) h
    simp [hf] at this
  have hcomp : f.comp (-X) = X ^ 4 - 2 * X ^ 3 - 12 * X ^ 2 + 40 * X - 32 := by
    simp [hf]; ring
  have hsv : f.signVariations = 1 := by
    have hdeg : f.degree = 4 := by rw [hf]; compute_degree!
    have c0 : f.coeff 0 = -32 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c1 : f.coeff 1 = -40 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c2 : f.coeff 2 = -12 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c3 : f.coeff 3 = 2 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c4 : f.coeff 4 = 1 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    simp only [Polynomial.signVariations, Polynomial.coeffList, hdeg]
    simp only [show (4 : WithBot ℕ).succ = 5 from rfl]
    simp [List.range_succ, c0, c1, c2, c3, c4]
    rw [List.signVariations_congr (l₂ := ([1, 2, -12, -40, -32] : List ℤ)) (by norm_num [sign_apply])]
    decide
  have hsv' : (X ^ 4 - 2 * X ^ 3 - 12 * X ^ 2 + 40 * X - 32 : ℝ[X]).signVariations = 3 := by
    set g : ℝ[X] := X ^ 4 - 2 * X ^ 3 - 12 * X ^ 2 + 40 * X - 32 with hg
    have hdeg : g.degree = 4 := by rw [hg]; compute_degree!
    have c0 : g.coeff 0 = -32 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c1 : g.coeff 1 = 40 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c2 : g.coeff 2 = -12 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c3 : g.coeff 3 = -2 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c4 : g.coeff 4 = 1 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    simp only [Polynomial.signVariations, Polynomial.coeffList, hdeg]
    simp only [show (4 : WithBot ℕ).succ = 5 from rfl]
    simp [List.range_succ, c0, c1, c2, c3, c4]
    rw [List.signVariations_congr (l₂ := ([1, -2, -12, 40, -32] : List ℤ)) (by norm_num [sign_apply])]
    decide
  refine ⟨hsv, hcomp, hsv', ?_, ?_⟩
  · obtain ⟨k, hk⟩ := descartes_rule_of_signs f hf0
    omega
  · obtain ⟨k, hk⟩ := descartes_rule_of_signs_neg f hf0
    rw [hcomp, hsv'] at hk
    omega

/-- Stitz-Zeager Exercise 3.3.3 (Descartes' Rule of Signs): `f(x) = x ^ 4 - 9 * x ^ 2 - 4 * x + 12` has `2` sign variation(s) and
`f(-x)` has `2`; the book's counts of positive and negative zeros (with multiplicity) follow. -/
@[kb "stitzzeager2013" "Exercise 3.3.3, p. 292"]
theorem exer_3_3_3_descartes :
    (X ^ 4 - 9 * X ^ 2 - 4 * X + 12 : ℝ[X]).signVariations = 2 ∧
      (X ^ 4 - 9 * X ^ 2 - 4 * X + 12 : ℝ[X]).comp (-X) = X ^ 4 - 9 * X ^ 2 + 4 * X + 12 ∧
      (X ^ 4 - 9 * X ^ 2 + 4 * X + 12 : ℝ[X]).signVariations = 2 ∧
      ((X ^ 4 - 9 * X ^ 2 - 4 * X + 12 : ℝ[X]).roots.countP (0 < ·) = 2 ∨ (X ^ 4 - 9 * X ^ 2 - 4 * X + 12 : ℝ[X]).roots.countP (0 < ·) = 0) ∧
      ((X ^ 4 - 9 * X ^ 2 - 4 * X + 12 : ℝ[X]).roots.countP (· < 0) = 2 ∨ (X ^ 4 - 9 * X ^ 2 - 4 * X + 12 : ℝ[X]).roots.countP (· < 0) = 0) := by
  set f : ℝ[X] := X ^ 4 - 9 * X ^ 2 - 4 * X + 12 with hf
  have hf0 : f ≠ 0 := by
    intro h
    have := congrArg (fun p => p.eval 0) h
    simp [hf] at this
  have hcomp : f.comp (-X) = X ^ 4 - 9 * X ^ 2 + 4 * X + 12 := by
    simp [hf]; ring
  have hsv : f.signVariations = 2 := by
    have hdeg : f.degree = 4 := by rw [hf]; compute_degree!
    have c0 : f.coeff 0 = 12 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c1 : f.coeff 1 = -4 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c2 : f.coeff 2 = -9 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c3 : f.coeff 3 = 0 := by
      have h12 : (12 : ℝ[X]).coeff 3 = 0 := coeff_ofNat_succ 12 2
      rw [hf, coeff_add, coeff_sub, coeff_sub, h12]
      simp [coeff_X, coeff_X_pow]
    have c4 : f.coeff 4 = 1 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    simp only [Polynomial.signVariations, Polynomial.coeffList, hdeg]
    simp only [show (4 : WithBot ℕ).succ = 5 from rfl]
    simp [List.range_succ, c0, c1, c2, c3, c4]
    rw [List.signVariations_congr (l₂ := ([1, -9, -4, 12] : List ℤ)) (by norm_num [sign_apply])]
    decide
  have hsv' : (X ^ 4 - 9 * X ^ 2 + 4 * X + 12 : ℝ[X]).signVariations = 2 := by
    set g : ℝ[X] := X ^ 4 - 9 * X ^ 2 + 4 * X + 12 with hg
    have hdeg : g.degree = 4 := by rw [hg]; compute_degree!
    have c0 : g.coeff 0 = 12 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c1 : g.coeff 1 = 4 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c2 : g.coeff 2 = -9 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c3 : g.coeff 3 = 0 := by
      have h12 : (12 : ℝ[X]).coeff 3 = 0 := coeff_ofNat_succ 12 2
      rw [hg, coeff_add, coeff_add, coeff_sub, h12]
      simp [coeff_X, coeff_X_pow]
    have c4 : g.coeff 4 = 1 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    simp only [Polynomial.signVariations, Polynomial.coeffList, hdeg]
    simp only [show (4 : WithBot ℕ).succ = 5 from rfl]
    simp [List.range_succ, c0, c1, c2, c3, c4]
    rw [List.signVariations_congr (l₂ := ([1, -9, 4, 12] : List ℤ)) (by norm_num [sign_apply])]
    decide
  refine ⟨hsv, hcomp, hsv', ?_, ?_⟩
  · obtain ⟨k, hk⟩ := descartes_rule_of_signs f hf0
    omega
  · obtain ⟨k, hk⟩ := descartes_rule_of_signs_neg f hf0
    rw [hcomp, hsv'] at hk
    omega

/-- Stitz-Zeager Exercise 3.3.4 (Descartes' Rule of Signs): `f(x) = x ^ 3 + 4 * x ^ 2 - 11 * x + 6` has `2` sign variation(s) and
`f(-x)` has `1`; the book's counts of positive and negative zeros (with multiplicity) follow. -/
@[kb "stitzzeager2013" "Exercise 3.3.4, p. 292"]
theorem exer_3_3_4_descartes :
    (X ^ 3 + 4 * X ^ 2 - 11 * X + 6 : ℝ[X]).signVariations = 2 ∧
      (X ^ 3 + 4 * X ^ 2 - 11 * X + 6 : ℝ[X]).comp (-X) = -X ^ 3 + 4 * X ^ 2 + 11 * X + 6 ∧
      (-X ^ 3 + 4 * X ^ 2 + 11 * X + 6 : ℝ[X]).signVariations = 1 ∧
      ((X ^ 3 + 4 * X ^ 2 - 11 * X + 6 : ℝ[X]).roots.countP (0 < ·) = 2 ∨ (X ^ 3 + 4 * X ^ 2 - 11 * X + 6 : ℝ[X]).roots.countP (0 < ·) = 0) ∧
      ((X ^ 3 + 4 * X ^ 2 - 11 * X + 6 : ℝ[X]).roots.countP (· < 0) = 1) := by
  set f : ℝ[X] := X ^ 3 + 4 * X ^ 2 - 11 * X + 6 with hf
  have hf0 : f ≠ 0 := by
    intro h
    have := congrArg (fun p => p.eval 0) h
    simp [hf] at this
  have hcomp : f.comp (-X) = -X ^ 3 + 4 * X ^ 2 + 11 * X + 6 := by
    simp [hf]; ring
  have hsv : f.signVariations = 2 := by
    have hdeg : f.degree = 3 := by rw [hf]; compute_degree!
    have c0 : f.coeff 0 = 6 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c1 : f.coeff 1 = -11 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c2 : f.coeff 2 = 4 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c3 : f.coeff 3 = 1 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    simp only [Polynomial.signVariations, Polynomial.coeffList, hdeg]
    simp only [show (3 : WithBot ℕ).succ = 4 from rfl]
    simp [List.range_succ, c0, c1, c2, c3]
    rw [List.signVariations_congr (l₂ := ([1, 4, -11, 6] : List ℤ)) (by norm_num [sign_apply])]
    decide
  have hsv' : (-X ^ 3 + 4 * X ^ 2 + 11 * X + 6 : ℝ[X]).signVariations = 1 := by
    set g : ℝ[X] := -X ^ 3 + 4 * X ^ 2 + 11 * X + 6 with hg
    have hdeg : g.degree = 3 := by rw [hg]; compute_degree!
    have c0 : g.coeff 0 = 6 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c1 : g.coeff 1 = 11 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c2 : g.coeff 2 = 4 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c3 : g.coeff 3 = -1 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    simp only [Polynomial.signVariations, Polynomial.coeffList, hdeg]
    simp only [show (3 : WithBot ℕ).succ = 4 from rfl]
    simp [List.range_succ, c0, c1, c2, c3]
    rw [List.signVariations_congr (l₂ := ([-1, 4, 11, 6] : List ℤ)) (by norm_num [sign_apply])]
    decide
  refine ⟨hsv, hcomp, hsv', ?_, ?_⟩
  · obtain ⟨k, hk⟩ := descartes_rule_of_signs f hf0
    omega
  · obtain ⟨k, hk⟩ := descartes_rule_of_signs_neg f hf0
    rw [hcomp, hsv'] at hk
    omega

/-- Stitz-Zeager Exercise 3.3.5 (Descartes' Rule of Signs): `f(x) = x ^ 3 - 7 * x ^ 2 + x - 7` has `3` sign variation(s) and
`f(-x)` has `0`; the book's counts of positive and negative zeros (with multiplicity) follow. -/
@[kb "stitzzeager2013" "Exercise 3.3.5, p. 292"]
theorem exer_3_3_5_descartes :
    (X ^ 3 - 7 * X ^ 2 + X - 7 : ℝ[X]).signVariations = 3 ∧
      (X ^ 3 - 7 * X ^ 2 + X - 7 : ℝ[X]).comp (-X) = -X ^ 3 - 7 * X ^ 2 - X - 7 ∧
      (-X ^ 3 - 7 * X ^ 2 - X - 7 : ℝ[X]).signVariations = 0 ∧
      ((X ^ 3 - 7 * X ^ 2 + X - 7 : ℝ[X]).roots.countP (0 < ·) = 3 ∨ (X ^ 3 - 7 * X ^ 2 + X - 7 : ℝ[X]).roots.countP (0 < ·) = 1) ∧
      ((X ^ 3 - 7 * X ^ 2 + X - 7 : ℝ[X]).roots.countP (· < 0) = 0) := by
  set f : ℝ[X] := X ^ 3 - 7 * X ^ 2 + X - 7 with hf
  have hf0 : f ≠ 0 := by
    intro h
    have := congrArg (fun p => p.eval 0) h
    simp [hf] at this
  have hcomp : f.comp (-X) = -X ^ 3 - 7 * X ^ 2 - X - 7 := by
    simp [hf]; ring
  have hsv : f.signVariations = 3 := by
    have hdeg : f.degree = 3 := by rw [hf]; compute_degree!
    have c0 : f.coeff 0 = -7 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c1 : f.coeff 1 = 1 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c2 : f.coeff 2 = -7 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c3 : f.coeff 3 = 1 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    simp only [Polynomial.signVariations, Polynomial.coeffList, hdeg]
    simp only [show (3 : WithBot ℕ).succ = 4 from rfl]
    simp [List.range_succ, c0, c1, c2, c3]
    rw [List.signVariations_congr (l₂ := ([1, -7, 1, -7] : List ℤ)) (by norm_num [sign_apply])]
    decide
  have hsv' : (-X ^ 3 - 7 * X ^ 2 - X - 7 : ℝ[X]).signVariations = 0 := by
    set g : ℝ[X] := -X ^ 3 - 7 * X ^ 2 - X - 7 with hg
    have hdeg : g.degree = 3 := by rw [hg]; compute_degree!
    have c0 : g.coeff 0 = -7 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c1 : g.coeff 1 = -1 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c2 : g.coeff 2 = -7 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c3 : g.coeff 3 = -1 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    simp only [Polynomial.signVariations, Polynomial.coeffList, hdeg]
    simp only [show (3 : WithBot ℕ).succ = 4 from rfl]
    simp [List.range_succ, c0, c1, c2, c3]
    rw [List.signVariations_congr (l₂ := ([-1, -7, -1, -7] : List ℤ)) (by norm_num [sign_apply])]
    decide
  refine ⟨hsv, hcomp, hsv', ?_, ?_⟩
  · obtain ⟨k, hk⟩ := descartes_rule_of_signs f hf0
    omega
  · obtain ⟨k, hk⟩ := descartes_rule_of_signs_neg f hf0
    rw [hcomp, hsv'] at hk
    omega

/-- Stitz-Zeager Exercise 3.3.6 (Descartes' Rule of Signs): `f(x) = -2 * x ^ 3 + 19 * x ^ 2 - 49 * x + 20` has `3` sign variation(s) and
`f(-x)` has `0`; the book's counts of positive and negative zeros (with multiplicity) follow. -/
@[kb "stitzzeager2013" "Exercise 3.3.6, p. 292"]
theorem exer_3_3_6_descartes :
    (-2 * X ^ 3 + 19 * X ^ 2 - 49 * X + 20 : ℝ[X]).signVariations = 3 ∧
      (-2 * X ^ 3 + 19 * X ^ 2 - 49 * X + 20 : ℝ[X]).comp (-X) = 2 * X ^ 3 + 19 * X ^ 2 + 49 * X + 20 ∧
      (2 * X ^ 3 + 19 * X ^ 2 + 49 * X + 20 : ℝ[X]).signVariations = 0 ∧
      ((-2 * X ^ 3 + 19 * X ^ 2 - 49 * X + 20 : ℝ[X]).roots.countP (0 < ·) = 3 ∨ (-2 * X ^ 3 + 19 * X ^ 2 - 49 * X + 20 : ℝ[X]).roots.countP (0 < ·) = 1) ∧
      ((-2 * X ^ 3 + 19 * X ^ 2 - 49 * X + 20 : ℝ[X]).roots.countP (· < 0) = 0) := by
  set f : ℝ[X] := -2 * X ^ 3 + 19 * X ^ 2 - 49 * X + 20 with hf
  have hf0 : f ≠ 0 := by
    intro h
    have := congrArg (fun p => p.eval 0) h
    simp [hf] at this
  have hcomp : f.comp (-X) = 2 * X ^ 3 + 19 * X ^ 2 + 49 * X + 20 := by
    simp [hf]; ring
  have hsv : f.signVariations = 3 := by
    have hdeg : f.degree = 3 := by rw [hf]; compute_degree!
    have c0 : f.coeff 0 = 20 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c1 : f.coeff 1 = -49 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c2 : f.coeff 2 = 19 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c3 : f.coeff 3 = -2 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    simp only [Polynomial.signVariations, Polynomial.coeffList, hdeg]
    simp only [show (3 : WithBot ℕ).succ = 4 from rfl]
    simp [List.range_succ, c0, c1, c2, c3]
    rw [List.signVariations_congr (l₂ := ([-2, 19, -49, 20] : List ℤ)) (by norm_num [sign_apply])]
    decide
  have hsv' : (2 * X ^ 3 + 19 * X ^ 2 + 49 * X + 20 : ℝ[X]).signVariations = 0 := by
    set g : ℝ[X] := 2 * X ^ 3 + 19 * X ^ 2 + 49 * X + 20 with hg
    have hdeg : g.degree = 3 := by rw [hg]; compute_degree!
    have c0 : g.coeff 0 = 20 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c1 : g.coeff 1 = 49 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c2 : g.coeff 2 = 19 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c3 : g.coeff 3 = 2 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    simp only [Polynomial.signVariations, Polynomial.coeffList, hdeg]
    simp only [show (3 : WithBot ℕ).succ = 4 from rfl]
    simp [List.range_succ, c0, c1, c2, c3]
    rw [List.signVariations_congr (l₂ := ([2, 19, 49, 20] : List ℤ)) (by norm_num [sign_apply])]
    decide
  refine ⟨hsv, hcomp, hsv', ?_, ?_⟩
  · obtain ⟨k, hk⟩ := descartes_rule_of_signs f hf0
    omega
  · obtain ⟨k, hk⟩ := descartes_rule_of_signs_neg f hf0
    rw [hcomp, hsv'] at hk
    omega

/-- Stitz-Zeager Exercise 3.3.7 (Descartes' Rule of Signs): `f(x) = -17 * x ^ 3 + 5 * x ^ 2 + 34 * x - 10` has `2` sign variation(s) and
`f(-x)` has `1`; the book's counts of positive and negative zeros (with multiplicity) follow. -/
@[kb "stitzzeager2013" "Exercise 3.3.7, p. 292"]
theorem exer_3_3_7_descartes :
    (-17 * X ^ 3 + 5 * X ^ 2 + 34 * X - 10 : ℝ[X]).signVariations = 2 ∧
      (-17 * X ^ 3 + 5 * X ^ 2 + 34 * X - 10 : ℝ[X]).comp (-X) = 17 * X ^ 3 + 5 * X ^ 2 - 34 * X - 10 ∧
      (17 * X ^ 3 + 5 * X ^ 2 - 34 * X - 10 : ℝ[X]).signVariations = 1 ∧
      ((-17 * X ^ 3 + 5 * X ^ 2 + 34 * X - 10 : ℝ[X]).roots.countP (0 < ·) = 2 ∨ (-17 * X ^ 3 + 5 * X ^ 2 + 34 * X - 10 : ℝ[X]).roots.countP (0 < ·) = 0) ∧
      ((-17 * X ^ 3 + 5 * X ^ 2 + 34 * X - 10 : ℝ[X]).roots.countP (· < 0) = 1) := by
  set f : ℝ[X] := -17 * X ^ 3 + 5 * X ^ 2 + 34 * X - 10 with hf
  have hf0 : f ≠ 0 := by
    intro h
    have := congrArg (fun p => p.eval 0) h
    simp [hf] at this
  have hcomp : f.comp (-X) = 17 * X ^ 3 + 5 * X ^ 2 - 34 * X - 10 := by
    simp [hf]; ring
  have hsv : f.signVariations = 2 := by
    have hdeg : f.degree = 3 := by rw [hf]; compute_degree!
    have c0 : f.coeff 0 = -10 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c1 : f.coeff 1 = 34 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c2 : f.coeff 2 = 5 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c3 : f.coeff 3 = -17 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    simp only [Polynomial.signVariations, Polynomial.coeffList, hdeg]
    simp only [show (3 : WithBot ℕ).succ = 4 from rfl]
    simp [List.range_succ, c0, c1, c2, c3]
    rw [List.signVariations_congr (l₂ := ([-17, 5, 34, -10] : List ℤ)) (by norm_num [sign_apply])]
    decide
  have hsv' : (17 * X ^ 3 + 5 * X ^ 2 - 34 * X - 10 : ℝ[X]).signVariations = 1 := by
    set g : ℝ[X] := 17 * X ^ 3 + 5 * X ^ 2 - 34 * X - 10 with hg
    have hdeg : g.degree = 3 := by rw [hg]; compute_degree!
    have c0 : g.coeff 0 = -10 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c1 : g.coeff 1 = -34 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c2 : g.coeff 2 = 5 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c3 : g.coeff 3 = 17 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    simp only [Polynomial.signVariations, Polynomial.coeffList, hdeg]
    simp only [show (3 : WithBot ℕ).succ = 4 from rfl]
    simp [List.range_succ, c0, c1, c2, c3]
    rw [List.signVariations_congr (l₂ := ([17, 5, -34, -10] : List ℤ)) (by norm_num [sign_apply])]
    decide
  refine ⟨hsv, hcomp, hsv', ?_, ?_⟩
  · obtain ⟨k, hk⟩ := descartes_rule_of_signs f hf0
    omega
  · obtain ⟨k, hk⟩ := descartes_rule_of_signs_neg f hf0
    rw [hcomp, hsv'] at hk
    omega

/-- Stitz-Zeager Exercise 3.3.8 (Descartes' Rule of Signs): `f(x) = 36 * x ^ 4 - 12 * x ^ 3 - 11 * x ^ 2 + 2 * x + 1` has `2` sign variation(s) and
`f(-x)` has `2`; the book's counts of positive and negative zeros (with multiplicity) follow. -/
@[kb "stitzzeager2013" "Exercise 3.3.8, p. 292"]
theorem exer_3_3_8_descartes :
    (36 * X ^ 4 - 12 * X ^ 3 - 11 * X ^ 2 + 2 * X + 1 : ℝ[X]).signVariations = 2 ∧
      (36 * X ^ 4 - 12 * X ^ 3 - 11 * X ^ 2 + 2 * X + 1 : ℝ[X]).comp (-X) = 36 * X ^ 4 + 12 * X ^ 3 - 11 * X ^ 2 - 2 * X + 1 ∧
      (36 * X ^ 4 + 12 * X ^ 3 - 11 * X ^ 2 - 2 * X + 1 : ℝ[X]).signVariations = 2 ∧
      ((36 * X ^ 4 - 12 * X ^ 3 - 11 * X ^ 2 + 2 * X + 1 : ℝ[X]).roots.countP (0 < ·) = 2 ∨ (36 * X ^ 4 - 12 * X ^ 3 - 11 * X ^ 2 + 2 * X + 1 : ℝ[X]).roots.countP (0 < ·) = 0) ∧
      ((36 * X ^ 4 - 12 * X ^ 3 - 11 * X ^ 2 + 2 * X + 1 : ℝ[X]).roots.countP (· < 0) = 2 ∨ (36 * X ^ 4 - 12 * X ^ 3 - 11 * X ^ 2 + 2 * X + 1 : ℝ[X]).roots.countP (· < 0) = 0) := by
  set f : ℝ[X] := 36 * X ^ 4 - 12 * X ^ 3 - 11 * X ^ 2 + 2 * X + 1 with hf
  have hf0 : f ≠ 0 := by
    intro h
    have := congrArg (fun p => p.eval 0) h
    simp [hf] at this
  have hcomp : f.comp (-X) = 36 * X ^ 4 + 12 * X ^ 3 - 11 * X ^ 2 - 2 * X + 1 := by
    simp [hf]; ring
  have hsv : f.signVariations = 2 := by
    have hdeg : f.degree = 4 := by rw [hf]; compute_degree!
    have c0 : f.coeff 0 = 1 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c1 : f.coeff 1 = 2 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c2 : f.coeff 2 = -11 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c3 : f.coeff 3 = -12 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c4 : f.coeff 4 = 36 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    simp only [Polynomial.signVariations, Polynomial.coeffList, hdeg]
    simp only [show (4 : WithBot ℕ).succ = 5 from rfl]
    simp [List.range_succ, c0, c1, c2, c3, c4]
    rw [List.signVariations_congr (l₂ := ([36, -12, -11, 2, 1] : List ℤ)) (by norm_num [sign_apply])]
    decide
  have hsv' : (36 * X ^ 4 + 12 * X ^ 3 - 11 * X ^ 2 - 2 * X + 1 : ℝ[X]).signVariations = 2 := by
    set g : ℝ[X] := 36 * X ^ 4 + 12 * X ^ 3 - 11 * X ^ 2 - 2 * X + 1 with hg
    have hdeg : g.degree = 4 := by rw [hg]; compute_degree!
    have c0 : g.coeff 0 = 1 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c1 : g.coeff 1 = -2 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c2 : g.coeff 2 = -11 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c3 : g.coeff 3 = 12 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c4 : g.coeff 4 = 36 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    simp only [Polynomial.signVariations, Polynomial.coeffList, hdeg]
    simp only [show (4 : WithBot ℕ).succ = 5 from rfl]
    simp [List.range_succ, c0, c1, c2, c3, c4]
    rw [List.signVariations_congr (l₂ := ([36, 12, -11, -2, 1] : List ℤ)) (by norm_num [sign_apply])]
    decide
  refine ⟨hsv, hcomp, hsv', ?_, ?_⟩
  · obtain ⟨k, hk⟩ := descartes_rule_of_signs f hf0
    omega
  · obtain ⟨k, hk⟩ := descartes_rule_of_signs_neg f hf0
    rw [hcomp, hsv'] at hk
    omega

/-- Stitz-Zeager Exercise 3.3.9 (Descartes' Rule of Signs): `f(x) = 3 * x ^ 3 + 3 * x ^ 2 - 11 * x - 10` has `1` sign variation(s) and
`f(-x)` has `2`; the book's counts of positive and negative zeros (with multiplicity) follow. -/
@[kb "stitzzeager2013" "Exercise 3.3.9, p. 292"]
theorem exer_3_3_9_descartes :
    (3 * X ^ 3 + 3 * X ^ 2 - 11 * X - 10 : ℝ[X]).signVariations = 1 ∧
      (3 * X ^ 3 + 3 * X ^ 2 - 11 * X - 10 : ℝ[X]).comp (-X) = -3 * X ^ 3 + 3 * X ^ 2 + 11 * X - 10 ∧
      (-3 * X ^ 3 + 3 * X ^ 2 + 11 * X - 10 : ℝ[X]).signVariations = 2 ∧
      ((3 * X ^ 3 + 3 * X ^ 2 - 11 * X - 10 : ℝ[X]).roots.countP (0 < ·) = 1) ∧
      ((3 * X ^ 3 + 3 * X ^ 2 - 11 * X - 10 : ℝ[X]).roots.countP (· < 0) = 2 ∨ (3 * X ^ 3 + 3 * X ^ 2 - 11 * X - 10 : ℝ[X]).roots.countP (· < 0) = 0) := by
  set f : ℝ[X] := 3 * X ^ 3 + 3 * X ^ 2 - 11 * X - 10 with hf
  have hf0 : f ≠ 0 := by
    intro h
    have := congrArg (fun p => p.eval 0) h
    simp [hf] at this
  have hcomp : f.comp (-X) = -3 * X ^ 3 + 3 * X ^ 2 + 11 * X - 10 := by
    simp [hf]; ring
  have hsv : f.signVariations = 1 := by
    have hdeg : f.degree = 3 := by rw [hf]; compute_degree!
    have c0 : f.coeff 0 = -10 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c1 : f.coeff 1 = -11 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c2 : f.coeff 2 = 3 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c3 : f.coeff 3 = 3 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    simp only [Polynomial.signVariations, Polynomial.coeffList, hdeg]
    simp only [show (3 : WithBot ℕ).succ = 4 from rfl]
    simp [List.range_succ, c0, c1, c2, c3]
    rw [List.signVariations_congr (l₂ := ([3, 3, -11, -10] : List ℤ)) (by norm_num [sign_apply])]
    decide
  have hsv' : (-3 * X ^ 3 + 3 * X ^ 2 + 11 * X - 10 : ℝ[X]).signVariations = 2 := by
    set g : ℝ[X] := -3 * X ^ 3 + 3 * X ^ 2 + 11 * X - 10 with hg
    have hdeg : g.degree = 3 := by rw [hg]; compute_degree!
    have c0 : g.coeff 0 = -10 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c1 : g.coeff 1 = 11 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c2 : g.coeff 2 = 3 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c3 : g.coeff 3 = -3 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    simp only [Polynomial.signVariations, Polynomial.coeffList, hdeg]
    simp only [show (3 : WithBot ℕ).succ = 4 from rfl]
    simp [List.range_succ, c0, c1, c2, c3]
    rw [List.signVariations_congr (l₂ := ([-3, 3, 11, -10] : List ℤ)) (by norm_num [sign_apply])]
    decide
  refine ⟨hsv, hcomp, hsv', ?_, ?_⟩
  · obtain ⟨k, hk⟩ := descartes_rule_of_signs f hf0
    omega
  · obtain ⟨k, hk⟩ := descartes_rule_of_signs_neg f hf0
    rw [hcomp, hsv'] at hk
    omega

/-- Stitz-Zeager Exercise 3.3.10 (Descartes' Rule of Signs): `f(x) = 2 * x ^ 4 + x ^ 3 - 7 * x ^ 2 - 3 * x + 3` has `2` sign variation(s) and
`f(-x)` has `2`; the book's counts of positive and negative zeros (with multiplicity) follow. -/
@[kb "stitzzeager2013" "Exercise 3.3.10, p. 292"]
theorem exer_3_3_10_descartes :
    (2 * X ^ 4 + X ^ 3 - 7 * X ^ 2 - 3 * X + 3 : ℝ[X]).signVariations = 2 ∧
      (2 * X ^ 4 + X ^ 3 - 7 * X ^ 2 - 3 * X + 3 : ℝ[X]).comp (-X) = 2 * X ^ 4 - X ^ 3 - 7 * X ^ 2 + 3 * X + 3 ∧
      (2 * X ^ 4 - X ^ 3 - 7 * X ^ 2 + 3 * X + 3 : ℝ[X]).signVariations = 2 ∧
      ((2 * X ^ 4 + X ^ 3 - 7 * X ^ 2 - 3 * X + 3 : ℝ[X]).roots.countP (0 < ·) = 2 ∨ (2 * X ^ 4 + X ^ 3 - 7 * X ^ 2 - 3 * X + 3 : ℝ[X]).roots.countP (0 < ·) = 0) ∧
      ((2 * X ^ 4 + X ^ 3 - 7 * X ^ 2 - 3 * X + 3 : ℝ[X]).roots.countP (· < 0) = 2 ∨ (2 * X ^ 4 + X ^ 3 - 7 * X ^ 2 - 3 * X + 3 : ℝ[X]).roots.countP (· < 0) = 0) := by
  set f : ℝ[X] := 2 * X ^ 4 + X ^ 3 - 7 * X ^ 2 - 3 * X + 3 with hf
  have hf0 : f ≠ 0 := by
    intro h
    have := congrArg (fun p => p.eval 0) h
    simp [hf] at this
  have hcomp : f.comp (-X) = 2 * X ^ 4 - X ^ 3 - 7 * X ^ 2 + 3 * X + 3 := by
    simp [hf]; ring
  have hsv : f.signVariations = 2 := by
    have hdeg : f.degree = 4 := by rw [hf]; compute_degree!
    have c0 : f.coeff 0 = 3 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c1 : f.coeff 1 = -3 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c2 : f.coeff 2 = -7 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c3 : f.coeff 3 = 1 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c4 : f.coeff 4 = 2 := by simp [hf, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    simp only [Polynomial.signVariations, Polynomial.coeffList, hdeg]
    simp only [show (4 : WithBot ℕ).succ = 5 from rfl]
    simp [List.range_succ, c0, c1, c2, c3, c4]
    rw [List.signVariations_congr (l₂ := ([2, 1, -7, -3, 3] : List ℤ)) (by norm_num [sign_apply])]
    decide
  have hsv' : (2 * X ^ 4 - X ^ 3 - 7 * X ^ 2 + 3 * X + 3 : ℝ[X]).signVariations = 2 := by
    set g : ℝ[X] := 2 * X ^ 4 - X ^ 3 - 7 * X ^ 2 + 3 * X + 3 with hg
    have hdeg : g.degree = 4 := by rw [hg]; compute_degree!
    have c0 : g.coeff 0 = 3 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c1 : g.coeff 1 = 3 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c2 : g.coeff 2 = -7 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c3 : g.coeff 3 = -1 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    have c4 : g.coeff 4 = 2 := by simp [hg, coeff_X, coeff_X_pow, coeff_one, coeff_ofNat_succ]
    simp only [Polynomial.signVariations, Polynomial.coeffList, hdeg]
    simp only [show (4 : WithBot ℕ).succ = 5 from rfl]
    simp [List.range_succ, c0, c1, c2, c3, c4]
    rw [List.signVariations_congr (l₂ := ([2, -1, -7, 3, 3] : List ℤ)) (by norm_num [sign_apply])]
    decide
  refine ⟨hsv, hcomp, hsv', ?_, ?_⟩
  · obtain ⟨k, hk⟩ := descartes_rule_of_signs f hf0
    omega
  · obtain ⟨k, hk⟩ := descartes_rule_of_signs_neg f hf0
    rw [hcomp, hsv'] at hk
    omega
