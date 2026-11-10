import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import UndergradKB.Common.Attr

/-! # Solving trigonometric equations (Corral §6.1; OpenStax §9.5)

General solutions of `sin x = a`, `cos x = a`, `tan x = a` through the inverse functions, and the rescaling
rule for equations `f (k x) = a` on `[0, 2π)`. Mathlib has the characterisations `Real.sin_eq_sin_iff` and
`Real.cos_eq_cos_iff`; the forms below are the ones the books use.
-/

namespace UndergradKB.Trigonometry

open Real Set

/-- **Solutions of `sin x = a`**: for `-1 ≤ a ≤ 1`, `sin x = a` exactly when `x = arcsin a + 2kπ` or
`x = π - arcsin a + 2kπ` for some integer `k`. (TR-172) -/
@[kb "openstaxalgtrig2e" "§9.5 (general solutions of sin x = a), p. 857"]
theorem sin_eq_iff {a x : ℝ} (ha₁ : -1 ≤ a) (ha₂ : a ≤ 1) :
    sin x = a ↔ ∃ k : ℤ, x = arcsin a + 2 * k * π ∨ x = π - arcsin a + 2 * k * π := by
  have h : sin x = a ↔ sin (arcsin a) = sin x := by rw [sin_arcsin ha₁ ha₂, eq_comm]
  rw [h, sin_eq_sin_iff]
  refine exists_congr fun k => or_congr ?_ ?_ <;> constructor <;> intro h <;> linarith

/-- **Solutions of `cos x = a`**: for `-1 ≤ a ≤ 1`, `cos x = a` exactly when `x = ± arccos a + 2kπ` for some
integer `k`. (TR-173) -/
@[kb "openstaxalgtrig2e" "§9.5 (general solutions of cos x = a), p. 857"]
theorem cos_eq_iff {a x : ℝ} (ha₁ : -1 ≤ a) (ha₂ : a ≤ 1) :
    cos x = a ↔ ∃ k : ℤ, x = arccos a + 2 * k * π ∨ x = -arccos a + 2 * k * π := by
  have h : cos x = a ↔ cos (arccos a) = cos x := by rw [cos_arccos ha₁ ha₂, eq_comm]
  rw [h, cos_eq_cos_iff]
  refine exists_congr fun k => or_congr ?_ ?_ <;> constructor <;> intro h <;> linarith

/-- **Solutions of `tan x = a`**: for `x` in the domain of the tangent (`cos x ≠ 0`), `tan x = a` exactly when
`x = arctan a + kπ` for some integer `k`. (TR-174) -/
@[kb "openstaxalgtrig2e" "§9.5 (general solutions of tan x = a), p. 858"]
theorem tan_eq_iff {a x : ℝ} (hc : cos x ≠ 0) :
    tan x = a ↔ ∃ k : ℤ, x = arctan a + k * π := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ : ∃ n : ℤ, x - n * π ∈ Ioc (-(π / 2)) (π / 2) := by
      refine ⟨toIocDiv pi_pos (-(π / 2)) x, ?_⟩
      have := toIocMod_mem_Ioc pi_pos (-(π / 2)) x
      rw [← self_sub_toIocDiv_zsmul, zsmul_eq_mul] at this
      convert this using 2
      ring
    have hne : x - n * π ≠ π / 2 := by
      intro e
      apply hc
      rw [cos_eq_zero_iff]
      exact ⟨n, by linear_combination e⟩
    have htan : tan (x - n * π) = a := by
      rw [← h]
      exact (tan_periodic.int_mul n).sub_eq x
    have := arctan_tan (x := x - n * π) hn.1 (lt_of_le_of_ne hn.2 hne)
    rw [htan] at this
    exact ⟨n, by linarith⟩
  · rintro ⟨k, rfl⟩
    rw [(tan_periodic.int_mul k) (arctan a), tan_arctan]

/-- **Equations with a multiple angle**: the solutions in `[0, 2π)` of `f (k x) = a` (for `k > 0`) are the
solutions `u` in `[0, 2kπ)` of `f u = a`, divided by `k`. (TR-175) -/
@[kb "openstaxalgtrig2e" "§9.5 (equations with multiple angles), p. 867"]
theorem solutions_mul_angle (f : ℝ → ℝ) (a : ℝ) {k : ℝ} (hk : 0 < k) :
    {x | x ∈ Ico 0 (2 * π) ∧ f (k * x) = a} =
      (fun u => u / k) '' {u | u ∈ Ico 0 (2 * k * π) ∧ f u = a} := by
  ext x
  simp only [mem_ofPred_eq, mem_image, mem_Ico]
  constructor
  · rintro ⟨⟨h0, h1⟩, hf⟩
    exact ⟨k * x, ⟨⟨mul_nonneg hk.le h0, by nlinarith⟩, hf⟩, by field_simp⟩
  · rintro ⟨u, ⟨⟨h0, h1⟩, hf⟩, rfl⟩
    refine ⟨⟨div_nonneg h0 hk.le, ?_⟩, by rwa [mul_div_cancel₀ _ hk.ne']⟩
    rw [div_lt_iff₀ hk]
    linarith

/-- **General solution from one solution**: if `f` has period `p` and `f x = a`, then `f (x + k p) = a` for
every integer `k` (Corral §6.1: adding multiples of the period to one solution gives infinitely many).
(TR-165) -/
@[kb "corraltrig" "Box §6.1, p. 137"]
theorem periodic_solutions {f : ℝ → ℝ} {p a x : ℝ} (hf : Function.Periodic f p) (hx : f x = a)
    (k : ℤ) : f (x + k * p) = a := by
  rw [hf.int_mul k x, hx]

end UndergradKB.Trigonometry
