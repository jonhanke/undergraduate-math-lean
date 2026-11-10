import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.ToIntervalMod
import UndergradKB.Common.Attr

/-! # Coterminal angles (Corral §1.4; OpenStax §7.1)

Angles that differ by a whole number of turns are coterminal (they have the same terminal side, hence the
same trigonometric values), and every angle is coterminal with exactly one angle in `[0, 2π)` (in degrees,
`[0°, 360°)`). Mathlib identifies such angles in `Real.Angle`; here are the books' statements.
-/

namespace UndergradKB.Trigonometry

open Real Set

/-- **Coterminal angles have the same values**: `θ` and `θ + 2πk` have the same sine and cosine (and the same
point on the unit circle) for every integer `k`. (TR-006) -/
@[kb "corraltrig" "Def §1.4 (coterminal angles), p. 37"]
theorem sin_cos_add_int_mul_two_pi (θ : ℝ) (k : ℤ) :
    sin (θ + k * (2 * π)) = sin θ ∧ cos (θ + k * (2 * π)) = cos θ :=
  ⟨sin_periodic.int_mul k θ, cos_periodic.int_mul k θ⟩

/-- **The coterminal angle in `[0, 2π)`**: every angle `θ` is coterminal with exactly one angle `φ` with
`0 ≤ φ < 2π`. (TR-010) -/
@[kb "openstaxalgtrig2e" "§7.1 Finding coterminal angles, p. 687"]
theorem existsUnique_coterminal_Ico (θ : ℝ) :
    ∃! φ, φ ∈ Ico 0 (2 * π) ∧ ∃ k : ℤ, φ = θ + k * (2 * π) := by
  have h2π : 0 < 2 * π := by positivity
  refine ⟨toIcoMod h2π 0 θ, ⟨by simpa using toIcoMod_mem_Ico h2π 0 θ, -toIcoDiv h2π 0 θ, ?_⟩, ?_⟩
  · rw [← self_sub_toIcoDiv_zsmul, zsmul_eq_mul]; push_cast; ring
  · rintro φ ⟨hφ, k, rfl⟩
    have hmem : θ + k * (2 * π) ∈ Ico 0 (0 + 2 * π) := by simpa using hφ
    exact ((toIcoMod_eq_iff h2π).2 ⟨hmem, -k, by rw [zsmul_eq_mul]; push_cast; ring⟩).symm

/-- The degree form: every angle of `x` degrees is coterminal with exactly one angle in `[0°, 360°)`. (TR-010) -/
theorem existsUnique_coterminal_Ico_deg (x : ℝ) :
    ∃! y, y ∈ Ico (0 : ℝ) 360 ∧ ∃ k : ℤ, y = x + k * 360 := by
  have h : (0 : ℝ) < 360 := by norm_num
  refine ⟨toIcoMod h 0 x, ⟨by simpa using toIcoMod_mem_Ico h 0 x, -toIcoDiv h 0 x, ?_⟩, ?_⟩
  · rw [← self_sub_toIcoDiv_zsmul, zsmul_eq_mul]; push_cast; ring
  · rintro y ⟨hy, k, rfl⟩
    have hmem : x + k * 360 ∈ Ico 0 (0 + 360) := by simpa using hy
    exact ((toIcoMod_eq_iff h).2 ⟨hmem, -k, by rw [zsmul_eq_mul]; push_cast; ring⟩).symm

end UndergradKB.Trigonometry
