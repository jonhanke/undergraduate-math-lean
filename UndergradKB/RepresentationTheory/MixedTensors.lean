import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.TensorPower.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import UndergradKB.Common.Attr

/-! # Tensors of type (m, n) (Etingof et al., §1.10)

The space of tensors of type `(m, n)` on a vector space `V` is `V^{⊗n} ⊗ (V*)^{⊗m}`. Given a basis `v_i` of a
finite-dimensional `V` with dual basis `v_i*`, the products `v_{i_1} ⊗ ... ⊗ v_{i_n} ⊗ v_{j_1}* ⊗ ... ⊗ v_{j_m}*`
form a basis, so the space has dimension `(dim V)^(n+m)`. Small bridging definition: Mathlib has the tensor powers
but no name for the mixed space.
-/

namespace UndergradKB.RepresentationTheory

open TensorProduct

variable (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V]

/-- Tensors of type `(m, n)` on `V`: `n` copies of `V` tensored with `m` copies of the dual space. -/
@[kb "etingof2011" "§1.10, p. 17"]
abbrev MixedTensor (m n : ℕ) : Type _ :=
  (⨂[k]^n V) ⊗[k] (⨂[k]^m (Module.Dual k V))

variable {k V} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The basis of `MixedTensor k V m n` built from a basis of `V` and its dual basis. -/
noncomputable def mixedTensorBasis (b : Module.Basis ι k V) (m n : ℕ) :
    Module.Basis ((Fin n → ι) × (Fin m → ι)) k (MixedTensor k V m n) :=
  (Basis.piTensorProduct fun _ => b).tensorProduct
    (Basis.piTensorProduct fun _ => b.dualBasis)

/-- The basis vectors are the elementary tensors `v_{i_1} ⊗ ... ⊗ v_{i_n} ⊗ v_{j_1}* ⊗ ... ⊗ v_{j_m}*`. -/
@[kb "etingof2011" "§1.10, p. 17"]
theorem mixedTensorBasis_apply (b : Module.Basis ι k V) (m n : ℕ) (p : Fin n → ι) (q : Fin m → ι) :
    mixedTensorBasis b m n (p, q) =
      (PiTensorProduct.tprod k fun i => b (p i)) ⊗ₜ (PiTensorProduct.tprod k fun j => b.dualBasis (q j)) := by
  simp only [mixedTensorBasis, Module.Basis.tensorProduct_apply, Basis.piTensorProduct_apply]

/-- The space of tensors of type `(m, n)` on an `N`-dimensional space has dimension `N^(n+m)`. -/
@[kb "etingof2011" "§1.10, p. 17"]
theorem finrank_mixedTensor [FiniteDimensional k V] (m n : ℕ) :
    Module.finrank k (MixedTensor k V m n) = Module.finrank k V ^ (n + m) := by
  let b := Module.finBasis k V
  rw [Module.finrank_eq_card_basis (mixedTensorBasis b m n)]
  simp [Fintype.card_prod, pow_add]

end UndergradKB.RepresentationTheory
