import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Topology.Order.LocalExtr
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 1 (Stitz-Zeager): exercises with the book's answers (wave 8), Sections 1.4 and 1.6 -/

namespace UndergradKB.Precalculus.Course

open Set Filter Topology

/-! ## Section 1.4 -/

/-- Stitz-Zeager Exercise 1.4.37: the polynomial `x⁴ - 13x³ + 56x² - 19` is defined for every real `x`,
so its implied domain is `(-∞, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 1.4.37, p. 77"]
theorem exer_1_4_37 :
    {x : ℝ | ∃ y : ℝ, y = x ^ 4 - 13 * x ^ 3 + 56 * x ^ 2 - 19} = univ := by
  ext x; simp only [mem_ofPred_eq, mem_univ, iff_true]; exact ⟨_, rfl⟩

/-- Stitz-Zeager Exercise 1.4.38: the polynomial `x² + 4` has implied domain `(-∞, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 1.4.38, p. 77"]
theorem exer_1_4_38 : {x : ℝ | ∃ y : ℝ, y = x ^ 2 + 4} = univ := by
  ext x; simp only [mem_ofPred_eq, mem_univ, iff_true]; exact ⟨_, rfl⟩

/-! ## Section 1.6 -/

private lemma ch1e3a_strictMono_noExt (f : ℝ → ℝ) (hf : StrictMono f) :
    (∀ c, ¬ IsLocalMin f c) ∧ (∀ c, ¬ IsLocalMax f c) ∧
      (∀ c, ¬ IsMinOn f univ c) ∧ (∀ c, ¬ IsMaxOn f univ c) := by
  have hmin : ∀ c, ¬ IsLocalMin f c := by
    intro c h
    have h1 : ∀ᶠ y in 𝓝[<] c, f c ≤ f y := nhdsWithin_le_nhds h
    obtain ⟨y, hy, hyc⟩ := (h1.and eventually_mem_nhdsWithin).exists
    exact absurd hy (not_le.mpr (hf hyc))
  have hmax : ∀ c, ¬ IsLocalMax f c := by
    intro c h
    have h1 : ∀ᶠ y in 𝓝[>] c, f y ≤ f c := nhdsWithin_le_nhds h
    obtain ⟨y, hy, hyc⟩ := (h1.and eventually_mem_nhdsWithin).exists
    exact absurd hy (not_le.mpr (hf hyc))
  refine ⟨hmin, hmax, fun c h => hmin c (h.isLocalMin univ_mem), fun c h => hmax c (h.isLocalMax univ_mem)⟩

private lemma ch1e3a_strictAnti_noExt (f : ℝ → ℝ) (hf : StrictAnti f) :
    (∀ c, ¬ IsLocalMin f c) ∧ (∀ c, ¬ IsLocalMax f c) ∧
      (∀ c, ¬ IsMinOn f univ c) ∧ (∀ c, ¬ IsMaxOn f univ c) := by
  have hmin : ∀ c, ¬ IsLocalMin f c := by
    intro c h
    have h1 : ∀ᶠ y in 𝓝[>] c, f c ≤ f y := nhdsWithin_le_nhds h
    obtain ⟨y, hy, hyc⟩ := (h1.and eventually_mem_nhdsWithin).exists
    exact absurd hy (not_le.mpr (hf hyc))
  have hmax : ∀ c, ¬ IsLocalMax f c := by
    intro c h
    have h1 : ∀ᶠ y in 𝓝[<] c, f y ≤ f c := nhdsWithin_le_nhds h
    obtain ⟨y, hy, hyc⟩ := (h1.and eventually_mem_nhdsWithin).exists
    exact absurd hy (not_le.mpr (hf hyc))
  refine ⟨hmin, hmax, fun c h => hmin c (h.isLocalMin univ_mem), fun c h => hmax c (h.isLocalMax univ_mem)⟩

/-- Stitz-Zeager Exercise 1.6.94: `f(x) = x³ + x - 12` is strictly increasing, so it has no local and no absolute
extremum. -/
@[kb "stitzzeager2013" "Exercise 1.6.94, p. 123"]
theorem exer_1_6_94 (f : ℝ → ℝ) (hf : ∀ x, f x = x ^ 3 + x - 12) :
    (∀ c, ¬ IsLocalMin f c) ∧ (∀ c, ¬ IsLocalMax f c) ∧
      (∀ c, ¬ IsMinOn f univ c) ∧ (∀ c, ¬ IsMaxOn f univ c) := by
  apply ch1e3a_strictMono_noExt
  intro a b hab
  rw [hf, hf]
  have h1 : 0 < b - a := sub_pos.mpr hab
  nlinarith [sq_nonneg (a + b), sq_nonneg a, sq_nonneg b, mul_pos h1 h1, mul_nonneg h1.le (sq_nonneg (a + b)),
    mul_nonneg h1.le (sq_nonneg a), mul_nonneg h1.le (sq_nonneg b)]

/-- Stitz-Zeager Exercise 1.6.95: `f(x) = -5x + 2` is strictly decreasing, so it has no local and no absolute
extremum. -/
@[kb "stitzzeager2013" "Exercise 1.6.95, p. 123"]
theorem exer_1_6_95 (f : ℝ → ℝ) (hf : ∀ x, f x = -5 * x + 2) :
    (∀ c, ¬ IsLocalMin f c) ∧ (∀ c, ¬ IsLocalMax f c) ∧
      (∀ c, ¬ IsMinOn f univ c) ∧ (∀ c, ¬ IsMaxOn f univ c) := by
  apply ch1e3a_strictAnti_noExt
  intro a b hab
  rw [hf, hf]
  linarith

end UndergradKB.Precalculus.Course
