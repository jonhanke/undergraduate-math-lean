import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import UndergradKB.Common.Attr

/-! # Trace of an operator (Axler, section 8C)

Rows LA-504 and LA-507.  `K` is an arbitrary field (Axler: `ℂ` for 8.54, `ℝ`/`ℂ` for 8.57).
-/

open Module

namespace UndergradKB.LinearAlgebra

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The trace of an operator on a nonzero finite-dimensional space is the negative of the coefficient
of `z ^ (n - 1)` in its characteristic polynomial, `n = dim V`. -/
@[kb "axler2024" "8.54, p. 346"]
theorem axler_8_54 [Nontrivial V] (T : V →ₗ[K] V) :
    LinearMap.trace K V T = -(LinearMap.charpoly T).coeff (finrank K V - 1) := by
  classical
  let b := Module.finBasis K V
  have hpos : 0 < finrank K V := Module.finrank_pos
  have : Nonempty (Fin (finrank K V)) := ⟨⟨0, hpos⟩⟩
  rw [LinearMap.trace_eq_matrix_trace K b, ← LinearMap.charpoly_toMatrix T b,
    Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin]

/-- No operators `S`, `T` on a nonzero finite-dimensional space over a field of characteristic `0`
satisfy `S T - T S = I`. -/
@[kb "axler2024" "8.57, p. 348"]
theorem axler_8_57 [CharZero K] [Nontrivial V] (S T : V →ₗ[K] V) : S * T - T * S ≠ 1 := by
  intro h
  have h1 := congrArg (LinearMap.trace K V) h
  rw [map_sub, LinearMap.trace_mul_comm K S T, sub_self, LinearMap.trace_one] at h1
  have hpos : 0 < finrank K V := Module.finrank_pos
  have : (finrank K V : K) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  exact this h1.symm

end UndergradKB.LinearAlgebra
