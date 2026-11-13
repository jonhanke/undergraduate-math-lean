import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Insert
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import UndergradKB.Common

/-!
# Course layer: Hammack, Book of Proof, Chapter 12, worked examples
-/

namespace UndergradKB.Foundations.Course

/-- Hammack Example 12.3: the range of `(m, n) ↦ 6m - 9n` on `ℤ × ℤ` is the set of multiples of 3. -/
@[kb "hammack2018" "Example 12.3, p. 239"]
theorem hammack_ex_12_3_range_multiples_of_three :
    Set.range (fun p : ℤ × ℤ => 6 * p.1 - 9 * p.2) = {x : ℤ | 3 ∣ x} := by
  ext x
  constructor
  · rintro ⟨⟨m, n⟩, rfl⟩
    simp only [Set.mem_ofPred_eq]
    omega
  · intro hx
    obtain ⟨k, hk⟩ := hx
    exact ⟨(-k, -k), by simp only; omega⟩

/-- Hammack Example 12.4: `x ↦ 1/x + 1` is injective on the nonzero reals but does not hit every real
(it misses 1). -/
@[kb "hammack2018" "Example 12.4, p. 243"]
theorem hammack_ex_12_4_injective_not_surjective :
    Set.InjOn (fun x : ℝ => 1 / x + 1) {0}ᶜ ∧ ¬ Set.SurjOn (fun x : ℝ => 1 / x + 1) {0}ᶜ Set.univ := by
  constructor
  · intro a _ b _ h
    simp only [one_div, add_left_inj, inv_inj] at h
    exact h
  · intro h
    obtain ⟨x, hx, hx1⟩ := h (Set.mem_univ (1 : ℝ))
    have hx0 : x ≠ 0 := hx
    simp [hx0] at hx1

/-- Hammack Example 12.5: restricting the codomain to the reals other than 1, `x ↦ 1/x + 1` is a bijection from
the nonzero reals. -/
@[kb "hammack2018" "Example 12.5, p. 243"]
theorem hammack_ex_12_5_bijective :
    Set.BijOn (fun x : ℝ => 1 / x + 1) {0}ᶜ {1}ᶜ := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hx0 : x ≠ 0 := hx
    simp [hx0]
  · intro a _ b _ h
    simp only [one_div, add_left_inj, inv_inj] at h
    exact h
  · intro b hb
    have hb1 : b - 1 ≠ 0 := sub_ne_zero.mpr hb
    refine ⟨1 / (b - 1), by simpa using hb1, ?_⟩
    simp only [one_div, inv_inv]
    ring

/-- Hammack Example 12.6: `(m, n) ↦ (m + n, m + 2n)` is a bijection of `ℤ × ℤ`. -/
@[kb "hammack2018" "Example 12.6, p. 243"]
theorem hammack_ex_12_6_bijective :
    Function.Bijective (fun p : ℤ × ℤ => (p.1 + p.2, p.1 + 2 * p.2)) := by
  constructor
  · rintro ⟨m, n⟩ ⟨k, l⟩ h
    simp only [Prod.mk.injEq] at h ⊢
    omega
  · rintro ⟨b, c⟩
    exact ⟨(2 * b - c, c - b), by simp only [Prod.mk.injEq]; omega⟩

/-- Hammack Example 12.7: `(m, n) ↦ m / (|n| + 1)` into `ℚ` is not injective but is surjective. -/
@[kb "hammack2018" "Example 12.7, p. 243"]
theorem hammack_ex_12_7_not_injective_surjective :
    ¬ Function.Injective (fun p : ℤ × ℤ => (p.1 : ℚ) / (|(p.2 : ℚ)| + 1)) ∧
      Function.Surjective (fun p : ℤ × ℤ => (p.1 : ℚ) / (|(p.2 : ℚ)| + 1)) := by
  constructor
  · intro h
    have := @h (1, 2) (1, -2) (by norm_num)
    simp at this
  · intro b
    refine ⟨(b.num, (b.den : ℤ) - 1), ?_⟩
    have hd : (1 : ℚ) ≤ (b.den : ℚ) := by exact_mod_cast b.den_pos
    have : |(((b.den : ℤ) - 1 : ℤ) : ℚ)| + 1 = (b.den : ℚ) := by
      push_cast
      rw [abs_of_nonneg (by linarith)]
      ring
    simp only
    rw [this]
    exact Rat.num_div_den b

/-- Hammack Example 12.8: with `f = {(a,0),(b,1),(c,0)}` and `g = {(0,3),(1,1)}`, the composition `g ∘ f`
sends `a, b, c` to `3, 1, 3` (indices `0, 1, 2`). -/
@[kb "hammack2018" "Example 12.8, p. 248"]
theorem hammack_ex_12_8_composition :
    (![3, 1] : Fin 2 → ℕ) ∘ (![0, 1, 0] : Fin 3 → Fin 2) = ![3, 1, 3] := by
  decide

/-- Hammack Example 12.10: with `f x = x^2 + x` and `g x = x + 1`, `g ∘ f` is `x^2 + x + 1`, `f ∘ g` is
`x^2 + 3x + 2`, and the two compositions differ. -/
@[kb "hammack2018" "Example 12.10, p. 248"]
theorem hammack_ex_12_10_composition_not_commutative :
    (∀ x : ℝ, ((fun x : ℝ => x + 1) ∘ (fun x : ℝ => x ^ 2 + x)) x = x ^ 2 + x + 1) ∧
    (∀ x : ℝ, ((fun x : ℝ => x ^ 2 + x) ∘ (fun x : ℝ => x + 1)) x = x ^ 2 + 3 * x + 2) ∧
    (fun x : ℝ => x + 1) ∘ (fun x : ℝ => x ^ 2 + x) ≠ (fun x : ℝ => x ^ 2 + x) ∘ (fun x : ℝ => x + 1) := by
  refine ⟨fun x => rfl, fun x => by simp only [Function.comp]; ring, ?_⟩
  intro h
  have := congrFun h 0
  norm_num [Function.comp] at this

/-- Hammack Example 12.11: `x ↦ x^3 + 1` is a bijection of `ℝ`; each `y` has exactly one preimage, namely the
real cube root of `y - 1`. -/
@[kb "hammack2018" "Example 12.11, p. 252"]
theorem hammack_ex_12_11_cube_plus_one_bijective :
    ∀ y : ℝ, ∃! x : ℝ, x ^ 3 + 1 = y := by
  intro y
  have hcube : ∀ t : ℝ, 0 ≤ t → ((t ^ ((3 : ℕ)⁻¹ : ℝ)) ^ 3 = t) := fun t ht =>
    Real.rpow_inv_natCast_pow ht (by norm_num)
  refine ⟨if 0 ≤ y - 1 then (y - 1) ^ ((3 : ℕ)⁻¹ : ℝ) else -((1 - y) ^ ((3 : ℕ)⁻¹ : ℝ)), ?_, ?_⟩
  · by_cases h : 0 ≤ y - 1
    · simp only [h, ite_true]
      rw [hcube _ h]; ring
    · simp only [h, ite_false]
      have h' : 0 ≤ 1 - y := by linarith
      have := hcube _ h'
      calc (-((1 - y) ^ ((3 : ℕ)⁻¹ : ℝ))) ^ 3 + 1
          = -(((1 - y) ^ ((3 : ℕ)⁻¹ : ℝ)) ^ 3) + 1 := by ring
        _ = y := by rw [this]; ring
  · intro z hz
    have hodd : Odd 3 := by decide
    have key : ∀ a b : ℝ, a ^ 3 = b ^ 3 → a = b := fun a b hab =>
      (Odd.strictMono_pow hodd).injective hab
    by_cases h : 0 ≤ y - 1
    · simp only [h, ite_true]
      apply key
      rw [hcube _ h]; linarith
    · simp only [h, ite_false]
      have h' : 0 ≤ 1 - y := by linarith
      have := hcube _ h'
      apply key
      calc z ^ 3 = y - 1 := by linarith
        _ = -(((1 - y) ^ ((3 : ℕ)⁻¹ : ℝ)) ^ 3) := by rw [this]; ring
        _ = (-((1 - y) ^ ((3 : ℕ)⁻¹ : ℝ))) ^ 3 := by ring

/-- Hammack Example 12.12: the inverse of `g(m, n) = (m + n, m + 2n)` on `ℤ × ℤ` is
`(m, n) ↦ (2m - n, n - m)`. -/
@[kb "hammack2018" "Example 12.12, p. 253"]
theorem hammack_ex_12_12_inverse :
    Function.LeftInverse (fun p : ℤ × ℤ => (2 * p.1 - p.2, p.2 - p.1))
        (fun p : ℤ × ℤ => (p.1 + p.2, p.1 + 2 * p.2)) ∧
    Function.RightInverse (fun p : ℤ × ℤ => (2 * p.1 - p.2, p.2 - p.1))
        (fun p : ℤ × ℤ => (p.1 + p.2, p.1 + 2 * p.2)) := by
  constructor
  · rintro ⟨m, n⟩
    simp only [Prod.mk.injEq]
    omega
  · rintro ⟨m, n⟩
    simp only [Prod.mk.injEq]
    omega

/-- Hammack Example 12.13: for the 8-element function with values `4, 8, 8, 1, 2, 4, 6, 4` (on `s, ..., z`
encoded `0, ..., 7`), the preimage of `{4}` is `{s, x, z}`, the image of `{s, t, u, z}` is `{8, 4}`, and
nothing maps to 9. -/
@[kb "hammack2018" "Example 12.13, p. 254"]
theorem hammack_ex_12_13_image_preimage :
    let f : Fin 8 → ℕ := ![4, 8, 8, 1, 2, 4, 6, 4]
    f ⁻¹' {4} = {0, 5, 7} ∧ f '' {0, 1, 2, 7} = {8, 4} ∧ f ⁻¹' {9} = ∅ := by
  intro f
  refine ⟨?_, ?_, ?_⟩
  · ext x
    fin_cases x <;> simp [f]
  · ext y
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases hx with rfl | rfl | rfl | rfl <;> simp [f]
    · rintro (rfl | rfl)
      · exact ⟨1, by simp, by simp [f]⟩
      · exact ⟨0, by simp, by simp [f]⟩
  · ext x
    fin_cases x <;> simp [f]

end UndergradKB.Foundations.Course
