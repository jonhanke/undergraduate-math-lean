import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Data.Int.Interval
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 10 (Stitz-Zeager): exercises with the book's answers (wave 8), Sections 10.5 and 10.7
(former too-hard items) -/

namespace UndergradKB.Precalculus.Course

open Real Filter Topology

/-- The inverses of `c + 2πn` (`c > 0`) tend to `0` through nonzero values. -/
theorem ch10e3e_seq (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => (c + 2 * π * (n : ℝ))⁻¹) atTop (nhdsWithin 0 {0}ᶜ) := by
  have h : Tendsto (fun n : ℕ => c + 2 * π * (n : ℝ)) atTop atTop :=
    Filter.tendsto_atTop_add_const_left _ _
      (Filter.Tendsto.const_mul_atTop (by positivity) tendsto_natCast_atTop_atTop)
  refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_inv_atTop_zero.comp h, ?_⟩
  refine Filter.Eventually.of_forall (fun n => ?_)
  have : 0 < c + 2 * π * (n : ℝ) := by positivity
  exact inv_ne_zero this.ne'

/-- Stitz-Zeager Exercise 10.5.47: `sin(1/x)` has no limit as `x → 0`. -/
@[kb "stitzzeager2013" "Exercise 10.5.47, p. 822"]
theorem exer_10_5_47 :
    ¬ ∃ L : ℝ, Tendsto (fun x : ℝ => sin (1 / x)) (nhdsWithin 0 {0}ᶜ) (nhds L) := by
  rintro ⟨L, hL⟩
  have hp := Real.pi_pos
  have h1 := hL.comp (ch10e3e_seq (π / 2) (by positivity))
  have h2 := hL.comp (ch10e3e_seq π hp)
  have e1 : (fun x : ℝ => sin (1 / x)) ∘ (fun n : ℕ => (π / 2 + 2 * π * (n : ℝ))⁻¹) =
      fun _ => (1 : ℝ) := by
    funext n
    simp only [Function.comp, one_div, inv_inv]
    rw [show π / 2 + 2 * π * (n : ℝ) = π / 2 + (n : ℝ) * (2 * π) by ring,
      Real.sin_add_nat_mul_two_pi, Real.sin_pi_div_two]
  have e2 : (fun x : ℝ => sin (1 / x)) ∘ (fun n : ℕ => (π + 2 * π * (n : ℝ))⁻¹) =
      fun _ => (0 : ℝ) := by
    funext n
    simp only [Function.comp, one_div, inv_inv]
    rw [show π + 2 * π * (n : ℝ) = π + (n : ℝ) * (2 * π) by ring,
      Real.sin_add_nat_mul_two_pi, Real.sin_pi]
  rw [e1] at h1
  rw [e2] at h2
  have a := tendsto_nhds_unique h1 tendsto_const_nhds
  have b := tendsto_nhds_unique h2 tendsto_const_nhds
  linarith

/-- Solutions of `c ∈ (0, 2π)`-shifted equations: the integer parameter lies in `[0, n)`. -/
theorem ch10e3e_range (n : ℕ) (x c : ℝ) (k : ℤ) (hc0 : 0 < c) (hc1 : c < 2 * π)
    (h0 : 0 ≤ (n : ℝ) * x) (h2 : (n : ℝ) * x < 2 * π * n) (hk : (n : ℝ) * x = 2 * k * π + c) :
    0 ≤ k ∧ k < n := by
  have hp := Real.pi_pos
  constructor
  · by_contra h
    have h' : k ≤ -1 := by omega
    have h'' : (k : ℝ) ≤ -1 := by exact_mod_cast h'
    nlinarith
  · by_contra h
    have h' : (n : ℤ) ≤ k := by omega
    have h'' : (n : ℝ) ≤ k := by exact_mod_cast h'
    nlinarith

/-- The solutions of `sin(n x) = 1/2` in `[0, 2π)` form an explicit finite set. -/
theorem ch10e3e_set (n : ℕ) (hn : 0 < n) :
    {x : ℝ | 0 ≤ x ∧ x < 2 * π ∧ sin ((n : ℝ) * x) = 1 / 2} =
      ↑((Finset.Ico (0 : ℤ) n).image (fun k : ℤ => (π / 6 + 2 * π * k) / n) ∪
        (Finset.Ico (0 : ℤ) n).image (fun k : ℤ => (5 * π / 6 + 2 * π * k) / n)) := by
  have hp := Real.pi_pos
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := hnp.ne'
  ext x
  simp only [Set.mem_setOf_eq, Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image,
    Finset.mem_coe, Finset.mem_Ico]
  constructor
  · rintro ⟨h0, h2, hs⟩
    have hnx0 : 0 ≤ (n : ℝ) * x := mul_nonneg hnp.le h0
    have hnx2 : (n : ℝ) * x < 2 * π * n := by nlinarith
    have hs' : sin (π / 6) = sin ((n : ℝ) * x) := by rw [Real.sin_pi_div_six]; exact hs.symm
    obtain ⟨k, hk | hk⟩ := Real.sin_eq_sin_iff.mp hs'
    · obtain ⟨a, b⟩ := ch10e3e_range n x (π / 6) k (by positivity) (by linarith) hnx0 hnx2 hk
      left
      refine ⟨k, ⟨a, b⟩, ?_⟩
      field_simp
      linarith
    · have hk' : (n : ℝ) * x = 2 * k * π + 5 * π / 6 := by linarith
      obtain ⟨a, b⟩ := ch10e3e_range n x (5 * π / 6) k (by positivity) (by linarith) hnx0 hnx2 hk'
      right
      refine ⟨k, ⟨a, b⟩, ?_⟩
      field_simp
      linarith
  · rintro (⟨k, ⟨a, b⟩, rfl⟩ | ⟨k, ⟨a, b⟩, rfl⟩)
    · have hk0 : (0 : ℝ) ≤ k := by exact_mod_cast a
      have hk1 : (k : ℝ) + 1 ≤ n := by exact_mod_cast b
      refine ⟨by positivity, ?_, ?_⟩
      · rw [div_lt_iff₀ hnp]; nlinarith
      · have e : (n : ℝ) * ((π / 6 + 2 * π * k) / n) = π / 6 + (k : ℤ) * (2 * π) := by
          field_simp
        rw [e, Real.sin_add_int_mul_two_pi, Real.sin_pi_div_six]
    · have hk0 : (0 : ℝ) ≤ k := by exact_mod_cast a
      have hk1 : (k : ℝ) + 1 ≤ n := by exact_mod_cast b
      refine ⟨by positivity, ?_, ?_⟩
      · rw [div_lt_iff₀ hnp]; nlinarith
      · have e : (n : ℝ) * ((5 * π / 6 + 2 * π * k) / n) = 5 * π / 6 + (k : ℤ) * (2 * π) := by
          field_simp
        rw [e, Real.sin_add_int_mul_two_pi, show 5 * π / 6 = π - π / 6 by ring, Real.sin_pi_sub,
          Real.sin_pi_div_six]

/-- Stitz-Zeager Exercise 10.7.108: for `n ≥ 1` the equation `sin(n x) = 1/2` has exactly `2n` solutions
in `[0, 2π)`: they are `(π/6 + 2πk)/n` and `(5π/6 + 2πk)/n`, `0 ≤ k < n`. -/
@[kb "stitzzeager2013" "Exercise 10.7.108, p. 888"]
theorem exer_10_7_108 (n : ℕ) (hn : 0 < n) :
    {x : ℝ | 0 ≤ x ∧ x < 2 * π ∧ sin ((n : ℝ) * x) = 1 / 2} =
      ↑((Finset.Ico (0 : ℤ) n).image (fun k : ℤ => (π / 6 + 2 * π * k) / n) ∪
        (Finset.Ico (0 : ℤ) n).image (fun k : ℤ => (5 * π / 6 + 2 * π * k) / n)) ∧
    {x : ℝ | 0 ≤ x ∧ x < 2 * π ∧ sin ((n : ℝ) * x) = 1 / 2}.ncard = 2 * n := by
  refine ⟨ch10e3e_set n hn, ?_⟩
  rw [ch10e3e_set n hn, Set.ncard_coe_finset]
  have hp := Real.pi_pos
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := hnp.ne'
  have inj1 : Function.Injective (fun k : ℤ => (π / 6 + 2 * π * k) / n) := by
    intro a b h
    have h' := (div_left_inj' hnne).mp h
    have h'' : 2 * π * (a : ℝ) = 2 * π * b := by linarith
    exact_mod_cast mul_left_cancel₀ (by positivity : 2 * π ≠ 0) h''
  have inj2 : Function.Injective (fun k : ℤ => (5 * π / 6 + 2 * π * k) / n) := by
    intro a b h
    have h' := (div_left_inj' hnne).mp h
    have h'' : 2 * π * (a : ℝ) = 2 * π * b := by linarith
    exact_mod_cast mul_left_cancel₀ (by positivity : 2 * π ≠ 0) h''
  have hdisj : Disjoint ((Finset.Ico (0 : ℤ) n).image (fun k : ℤ => (π / 6 + 2 * π * k) / n))
      ((Finset.Ico (0 : ℤ) n).image (fun k : ℤ => (5 * π / 6 + 2 * π * k) / n)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_image] at hx hx'
    obtain ⟨a, _, rfl⟩ := hx
    obtain ⟨b, _, hb⟩ := hx'
    have h' := (div_left_inj' hnne).mp hb
    have h3 : π * (3 * (a : ℝ) - 3 * b) = π * 1 := by linarith
    have h4 := mul_left_cancel₀ hp.ne' h3
    have h5 : (3 * a - 3 * b : ℤ) = 1 := by exact_mod_cast h4
    omega
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ inj1,
    Finset.card_image_of_injective _ inj2]
  simp
  ring

end UndergradKB.Precalculus.Course
