import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import UndergradKB.Common.Attr

/-! # Dimensions of spaces of multilinear forms and of tensor products (Axler, chapter 9)

Rows LA-511, LA-589, LA-599, LA-601.  `K` is an arbitrary field (Axler: `ℝ` or `ℂ`).
-/

open Module
open scoped TensorProduct

namespace UndergradKB.LinearAlgebra

variable {K : Type*} [Field K]

/-- The dimension of the space of bilinear forms on `V` is the square of `dim V`. -/
@[kb "axler2024" "9.5, p. 353"]
theorem axler_9_5 {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] :
    finrank K (LinearMap.BilinForm K V) = finrank K V ^ 2 := by
  show finrank K (V →ₗ[K] V →ₗ[K] K) = _
  rw [Module.finrank_linearMap, Module.finrank_linearMap_self, sq]

/-- The dimension of the space `B(V, W)` of bilinear functionals on `V × W` is `dim V * dim W`. -/
@[kb "axler2024" "9.70, p. 389"]
theorem axler_9_70 {V W : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] :
    finrank K (V →ₗ[K] W →ₗ[K] K) = finrank K V * finrank K W := by
  rw [Module.finrank_linearMap, Module.finrank_linearMap_self]

section PiTensor

variable {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
  [∀ i, FiniteDimensional K (V i)]

/-- The dimension of `V₁ ⊗ ⋯ ⊗ Vₘ` is the product of the dimensions of the `Vₖ`
(stated for any finite index type). -/
@[kb "axler2024" "9.89, p. 397"]
theorem axler_9_89 : finrank K (⨂[K] i, V i) = ∏ i, finrank K (V i) := by
  classical
  have b := Basis.piTensorProduct (fun i => Module.finBasis K (V i))
  rw [Module.finrank_eq_card_basis b, Fintype.card_pi]
  simp

/-- The dimension of the space of `m`-linear forms on `V₁ × ⋯ × Vₘ` is the product of the dimensions
(stated for any finite index type). -/
@[kb "axler2024" "9.87, p. 396"]
theorem axler_9_87 : finrank K (MultilinearMap K V K) = ∏ i, finrank K (V i) := by
  classical
  have : Module.Finite K (⨂[K] i, V i) :=
    Module.Finite.of_basis (Basis.piTensorProduct (fun i => Module.finBasis K (V i)))
  rw [(PiTensorProduct.lift (R := K) (s := V) (E := K)).finrank_eq,
    Module.finrank_linearMap_self, axler_9_89]

end PiTensor

end UndergradKB.LinearAlgebra
