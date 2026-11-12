import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Algebra.Bilinear
import UndergradKB.Common.Attr

/-! # Characters of representations of an algebra (Etingof et al., §2.6)

For a finite-dimensional representation `V` of an algebra `A` (an `A`-module, finite-dimensional over `k`), the
character is the linear function `χ_V(a) = tr(a acting on V)`. It vanishes on commutators `ab - ba`, so it factors
through `A / [A, A]`.
-/

namespace UndergradKB.RepresentationTheory

open Module

variable (k : Type*) {A V : Type*} [Field k] [Ring A] [Algebra k A] [AddCommGroup V] [Module A V] [Module k V]
  [IsScalarTower k A V]

/-- **Etingof et al., §2.6**: the character of a representation of an algebra, `a ↦ tr(a acting on V)`, as a
`k`-linear function on `A`. -/
@[kb "etingof2011" "§2.6, p. 27"]
noncomputable def algebraCharacter : A →ₗ[k] k :=
  LinearMap.trace k V ∘ₗ (Algebra.lsmul k k V).toLinearMap

theorem algebraCharacter_apply (a : A) :
    algebraCharacter k (V := V) a = LinearMap.trace k V (Algebra.lsmul k k V a) := rfl

/-- **Etingof et al., §2.6**: the character of a representation of an algebra vanishes on commutators. -/
@[kb "etingof2011" "§2.6, p. 27"]
theorem algebraCharacter_commutator (a b : A) : algebraCharacter k (V := V) (a * b - b * a) = 0 := by
  rw [algebraCharacter_apply, map_sub, map_mul, map_mul, map_sub, LinearMap.trace_mul_comm, sub_self]

end UndergradKB.RepresentationTheory
