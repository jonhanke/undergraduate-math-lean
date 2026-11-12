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
# Headline statements of undergraduate-math-lean 0.2.0: abstract algebra (Judson and Beezer)

The main results of this topic that Mathlib and Tau Ceti lack, one theorem each, with every proof a deliberate
`sorry`: to check what is claimed, read this file. They are: the number π is transcendental over the rationals;
a real number is constructible with straightedge and compass exactly when it lies in a tower of square-root
extensions of the rationals; the three classical impossibilities (doubling the cube, trisecting a 60 degree
angle, squaring the circle); an explicit quintic polynomial that is not solvable by radicals; and, new in 0.2.0,
the crystallographic restriction, the finite subgroups of `O(2)`, and the BCH bound for cyclic codes.
`Solution_AbstractAlgebra.lean` proves the same statements from the library, and `lake comparator` (configured by
`comparator/AbstractAlgebra.json`) checks that each proved statement is exactly the one here and uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Each statement is the library's statement, copied. The statements were not yet reviewed by a human (see the
README).

## Definitions used

Besides Mathlib, the statements use these definitions of the library; a reader checking a statement should check
these too:

* `UndergradKB.AbstractAlgebra.ConstructiblePt`: the points of the complex plane that can be built from `0` and
  `1` with straightedge and compass (new points are intersections of two lines, of a line and a circle, or of two
  circles).
* `UndergradKB.AbstractAlgebra.Constructible`: a real number `x` is constructible when the point `x` of the real
  axis is.
* `UndergradKB.AbstractAlgebra.SqrtTower`: the intermediate fields of the rationals inside the reals that are
  built from the rationals by repeatedly adjoining the square root of an element of the field built so far.
* `UndergradKB.AbstractAlgebra.SolvableByRadicals`: a polynomial is solvable by radicals when every root in its
  splitting field lies in Mathlib's `solvableByRad`, the smallest subfield closed under taking roots of any order.
* `UndergradKB.AbstractAlgebra.Quintic.quintic`: the rational polynomial `x^5 - 6x^3 - 27x - 3`.
* `UndergradKB.AbstractAlgebra.lattice2 x y`: the integer span of `x` and `y`.
* `UndergradKB.AbstractAlgebra.rotationPart G`: the elements of `G` of determinant 1 (the rotations).
* `UndergradKB.AbstractAlgebra.CyclicCodes.cyclicCodeOf n g`: the words `w : Fin n → F` whose polynomial
  `∑ i, w i X^i` is divisible by `g`.
-/

namespace UndergradKB.Headlines.AbstractAlgebra

/-- **The number π is transcendental** (Lindemann; used in Judson and Beezer, Section 21.3.2, p. 298): π is not
a root of any nonzero polynomial with rational coefficients. Mathlib has only the analytic part of the
Lindemann–Weierstrass theorem (`LindemannWeierstrass.exp_polynomial_approx`). Tau Ceti proves the
Lindemann–Weierstrass theorem (`algebraicIndependent_exp`), which implies this, but does not state it; the proof
here is independent of Tau Ceti. -/
theorem transcendental_pi : Transcendental ℚ Real.pi := by
  sorry

/-- **Constructible numbers are the square-root towers** (Judson and Beezer, Theorem 21.3.7, p. 297): a real
number is constructible with straightedge and compass exactly when it lies in the top field of a tower
`ℚ = F₀ ⊂ ⋯ ⊂ F_k` with `F_{i+1} = F_i(√α_i)` and `α_i ∈ F_i`. Neither Mathlib nor Tau Ceti has a theory of
constructible numbers. -/
theorem constructible_iff_sqrt_tower (x : ℝ) :
    UndergradKB.AbstractAlgebra.Constructible x ↔
      ∃ F, UndergradKB.AbstractAlgebra.SqrtTower F ∧ x ∈ F := by
  sorry

/-- **Doubling the cube is impossible** (Judson and Beezer, Section 21.3.2, p. 298): the real number `∛2` is not
constructible with straightedge and compass. Neither Mathlib nor Tau Ceti has a theory of constructible
numbers. -/
theorem not_constructible_cbrt_two :
    ¬ UndergradKB.AbstractAlgebra.Constructible ((2 : ℝ) ^ ((1 : ℝ) / 3)) := by
  sorry

/-- **Trisecting a 60 degree angle is impossible** (Judson and Beezer, Section 21.3.3, p. 298): `cos (π / 9)`,
the cosine of 20 degrees, is not constructible with straightedge and compass, so the constructible angle of 60
degrees cannot be trisected. Neither Mathlib nor Tau Ceti has a theory of constructible numbers. -/
theorem not_constructible_cos_pi_div_nine :
    ¬ UndergradKB.AbstractAlgebra.Constructible (Real.cos (Real.pi / 9)) := by
  sorry

/-- **Squaring the circle is impossible** (Judson and Beezer, Section 21.3.2, p. 298): `√π`, the side of a
square with the area of the unit circle, is not constructible with straightedge and compass. Neither Mathlib nor
Tau Ceti has a theory of constructible numbers. -/
theorem not_constructible_sqrt_pi :
    ¬ UndergradKB.AbstractAlgebra.Constructible (Real.sqrt Real.pi) := by
  sorry

/-- **An explicit quintic that is not solvable by radicals** (Judson and Beezer, Example 23.3.7, p. 331): the
polynomial `x^5 - 6x^3 - 27x - 3` over the rationals is not solvable by radicals. Mathlib proves one direction
of the criterion (`isSolvable_gal_of_irreducible`) and a prime-degree criterion for the Galois group
(`galActionHom_bijective_of_prime_degree`), but gives no explicit polynomial. Tau Ceti's
`FieldTheory/GaloisGroups/Quintic.lean` is about groups only and not about `solvableByRad`. -/
theorem quintic_not_solvable_by_radicals :
    ¬ UndergradKB.AbstractAlgebra.SolvableByRadicals ℚ UndergradKB.AbstractAlgebra.Quintic.quintic := by
  sorry

/-- **The crystallographic restriction** (Judson and Beezer, Theorem 12.2.9; new in 0.2.0): a linear map of finite
order of a real plane that maps a lattice (the integer span of two independent vectors) into itself has order 1, 2,
3, 4 or 6. Related: neither Mathlib nor Tau Ceti has it (their "crystallographic" results are about root
systems). -/
theorem crystallographic_restriction {V : Type*} [AddCommGroup V] [Module ℝ V]
    (hV : Module.finrank ℝ V = 2) {x y : V}
    (hxy : LinearIndependent ℝ ![x, y]) (T : V →ₗ[ℝ] V)
    (hT : ∀ v ∈ UndergradKB.AbstractAlgebra.lattice2 x y, T v ∈ UndergradKB.AbstractAlgebra.lattice2 x y)
    (m : ℕ) (hm : m ≠ 0) (hTm : T ^ m = 1) :
    orderOf T = 1 ∨ orderOf T = 2 ∨ orderOf T = 3 ∨ orderOf T = 4 ∨ orderOf T = 6 := by
  sorry

/-- **Finite groups of plane symmetries** (Judson and Beezer, Theorem 12.2.4; new in 0.2.0): a finite subgroup of
the orthogonal group `O(2)` is cyclic or dihedral of order determined by its number `n ≥ 1` of rotations. Related:
Mathlib describes the elements of `SO(2)`; neither Mathlib nor Tau Ceti classifies the finite subgroups of
`O(2)`. -/
theorem finite_subgroup_orthogonal_two (G : Subgroup (Matrix.orthogonalGroup (Fin 2) ℝ)) [Finite G] :
    ∃ n : ℕ, n = Nat.card (UndergradKB.AbstractAlgebra.rotationPart G) ∧ 0 < n ∧
      (Nonempty (G ≃* Multiplicative (ZMod n)) ∨ Nonempty (G ≃* DihedralGroup n)) := by
  sorry

open Polynomial in
/-- **The BCH bound** (Judson and Beezer, Theorem 22.2.8; new in 0.2.0): if the generator polynomial `g` of a
cyclic code of length `n` over a field `F` vanishes at `s` consecutive powers `ω^a, …, ω^(a+s-1)` of a primitive
`n`-th root of unity `ω` (in an extension field `E`), every nonzero code word has at least `s + 1` nonzero
entries. Related: Mathlib and Tau Ceti have Hamming distance and some codes, but no cyclic codes and no BCH
bound. -/
theorem bch_bound {F : Type*} [Field F] {n : ℕ} {E : Type*} [Field E] [Algebra F E] [DecidableEq F] [NeZero n]
    {ω : E} (hω : IsPrimitiveRoot ω n) (a s : ℕ) {g : F[X]}
    (hg : ∀ k < s, aeval (ω ^ (a + k)) g = 0) {w : Fin n → F}
    (hw : w ∈ UndergradKB.AbstractAlgebra.CyclicCodes.cyclicCodeOf n g)
    (hw0 : w ≠ 0) : s + 1 ≤ hammingNorm w := by
  sorry

end UndergradKB.Headlines.AbstractAlgebra
