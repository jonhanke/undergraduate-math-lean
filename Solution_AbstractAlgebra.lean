/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import UndergradKB.AbstractAlgebra.Constructible
import UndergradKB.AbstractAlgebra.PiTranscendental
import UndergradKB.AbstractAlgebra.Galois
import UndergradKB.AbstractAlgebra.MatrixGroups2
import UndergradKB.AbstractAlgebra.FiniteSymmetry
import UndergradKB.AbstractAlgebra.CyclicCodes

/-!
# Proofs of the abstract algebra headline statements (Judson and Beezer)

Each statement of `Challenge_AbstractAlgebra.lean` is proved here from the library. `lake comparator` (configured
by `comparator/AbstractAlgebra.json`) checks that each statement here is exactly the one in
`Challenge_AbstractAlgebra.lean` and that the proofs use only the standard axioms `propext`, `Classical.choice`
and `Quot.sound`.
-/

namespace UndergradKB.Headlines.AbstractAlgebra

theorem transcendental_pi : Transcendental ℚ Real.pi :=
  UndergradKB.AbstractAlgebra.transcendental_pi

theorem constructible_iff_sqrt_tower (x : ℝ) :
    UndergradKB.AbstractAlgebra.Constructible x ↔
      ∃ F, UndergradKB.AbstractAlgebra.SqrtTower F ∧ x ∈ F :=
  UndergradKB.AbstractAlgebra.constructible_iff_tower x

theorem not_constructible_cbrt_two :
    ¬ UndergradKB.AbstractAlgebra.Constructible ((2 : ℝ) ^ ((1 : ℝ) / 3)) :=
  UndergradKB.AbstractAlgebra.not_constructible_cbrt_two

theorem not_constructible_cos_pi_div_nine :
    ¬ UndergradKB.AbstractAlgebra.Constructible (Real.cos (Real.pi / 9)) :=
  UndergradKB.AbstractAlgebra.not_constructible_cos_twenty_degrees

theorem not_constructible_sqrt_pi :
    ¬ UndergradKB.AbstractAlgebra.Constructible (Real.sqrt Real.pi) :=
  UndergradKB.AbstractAlgebra.not_constructible_sqrt_pi

theorem quintic_not_solvable_by_radicals :
    ¬ UndergradKB.AbstractAlgebra.SolvableByRadicals ℚ UndergradKB.AbstractAlgebra.Quintic.quintic :=
  UndergradKB.AbstractAlgebra.Quintic.quintic_not_solvableByRadicals

theorem crystallographic_restriction {V : Type*} [AddCommGroup V] [Module ℝ V]
    (hV : Module.finrank ℝ V = 2) {x y : V}
    (hxy : LinearIndependent ℝ ![x, y]) (T : V →ₗ[ℝ] V)
    (hT : ∀ v ∈ UndergradKB.AbstractAlgebra.lattice2 x y, T v ∈ UndergradKB.AbstractAlgebra.lattice2 x y)
    (m : ℕ) (hm : m ≠ 0) (hTm : T ^ m = 1) :
    orderOf T = 1 ∨ orderOf T = 2 ∨ orderOf T = 3 ∨ orderOf T = 4 ∨ orderOf T = 6 :=
  UndergradKB.AbstractAlgebra.crystallographic_restriction hV hxy T hT m hm hTm

theorem finite_subgroup_orthogonal_two (G : Subgroup (Matrix.orthogonalGroup (Fin 2) ℝ)) [Finite G] :
    ∃ n : ℕ, n = Nat.card (UndergradKB.AbstractAlgebra.rotationPart G) ∧ 0 < n ∧
      (Nonempty (G ≃* Multiplicative (ZMod n)) ∨ Nonempty (G ≃* DihedralGroup n)) :=
  UndergradKB.AbstractAlgebra.finite_subgroup_orthogonal_two G

open Polynomial in
theorem bch_bound {F : Type*} [Field F] {n : ℕ} {E : Type*} [Field E] [Algebra F E] [DecidableEq F] [NeZero n]
    {ω : E} (hω : IsPrimitiveRoot ω n) (a s : ℕ) {g : F[X]}
    (hg : ∀ k < s, aeval (ω ^ (a + k)) g = 0) {w : Fin n → F}
    (hw : w ∈ UndergradKB.AbstractAlgebra.CyclicCodes.cyclicCodeOf n g)
    (hw0 : w ≠ 0) : s + 1 ≤ hammingNorm w :=
  UndergradKB.AbstractAlgebra.CyclicCodes.bch_bound hω a s hg hw hw0

end UndergradKB.Headlines.AbstractAlgebra
