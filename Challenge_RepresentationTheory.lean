/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import UndergradKB.RepresentationTheory.GroupDeterminant
import UndergradKB.RepresentationTheory.AlgebrasChapter2b
import UndergradKB.RepresentationTheory.PeterWeyl
import UndergradKB.RepresentationTheory.PolynomialRepsSum
import UndergradKB.RepresentationTheory.McKayClassification

/-!
# Headline statements of undergraduate-math-lean 0.2.1: representation theory (Etingof et al.)

The main results of this topic that Mathlib and Tau Ceti lack, one theorem each, with every proof a deliberate
`sorry`: Frobenius's factorization of the group determinant, and Dixmier's lemma (Schur's lemma for irreducible
representations of countable dimension). Version 0.2.1 adds the Peter–Weyl theorem for `GL_N(ℂ)` (the ring of
rational functions is `⨁_λ L_λ^* ⊗ L_λ`), the classification of the rational representations of `GL_N(ℂ)` (every
irreducible one is some `L_λ`, the `L_λ` are pairwise non-isomorphic, and every rational representation is a direct
sum of them), and the McKay graph of a finite subgroup of `SU(2)` being an affine Dynkin diagram (the graph half of the
McKay correspondence). Most named theorems of the book (Burnside's `pᵃqᵇ` theorem, Frobenius
reciprocity and divisibility, Gabriel's theorem, Schur–Weyl duality, the hook length formula, the Frobenius character
formula) are proved here too but are not headlines: Tau Ceti has them. To check what is claimed, read this file.
`Solution_RepresentationTheory.lean` proves the same statements from the library, and `lake comparator` (configured
by `comparator/RepresentationTheory.json`) checks that each proved statement is exactly the one here and uses only
the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Each statement is the library's statement, copied. The statements were not yet reviewed by a human (see the README).

## Definitions used

Besides Mathlib, the statements use these definitions of the library (namespace `UndergradKB.RepresentationTheory`);
a reader checking a statement should check these too:

* `IrrRep ℂ G`: a finite-dimensional irreducible complex representation of `G`, bundled with its space `V` and its
  action `ρ` (Mathlib's `Representation` and `IsIrreducible`).
* `groupMatrix G R`: the matrix indexed by `G × G` whose `(g, h)` entry is the variable `x_{gh}` of the polynomial
  ring `MvPolynomial G R`; `groupDeterminant G R` is its determinant (Etingof et al., Definition 4.6).
* `groupPoly ρ`: the polynomial `det (∑_g x_g ρ(g))` in the variables `x_g`, computed in a basis of `V`.
* `ratFunctions N ℂ`: the algebra of functions `GL_N(ℂ) → ℂ` that are polynomials in the matrix entries and `1 / det`.
* `IsRationalRep ρ` (for `ρ` a representation of `GL_N(ℂ)`): all coefficient functions `g ↦ φ(ρ g v)` lie in
  `ratFunctions N ℂ`; for finite-dimensional spaces, the matrix entries are polynomials in the entries of `g` and
  `1 / det g` (Etingof et al., Definition 4.65).
* `IsIrredRep ρ`: the space is nonzero and its only `ρ`-invariant subspaces are `0` and everything.
* `DiagramsOfSize n`: Young diagrams with `n` boxes. `glIrrep ν a`, for a diagram `ν` with at most `N` rows and
  `a : ℤ`, is the representation `L_ν ⊗ det^a` of `GL_N(ℂ)` (`L_ν` the Schur functor of `ν`, built from the Specht
  module of `ν` and the tensor power of `ℂ^N`), the book's `L_λ` for `λ_j = ν_j + a`. `highestWeight N ν a` is the
  sequence `(ν_j + a)_{j<N}`. Here the highest weight is only the name of this indexing: the weights of the torus are
  not formalised (see Known restrictions in the README).
* `HighestWeights N`: the antitone sequences `λ : Fin N → ℤ`. `LCarrier λ` is the space and `Lrep λ` the action of a
  fixed model `L_λ` of `glIrrep ν a` with `highestWeight N ν a = λ` (chosen by `Classical.choice`).
* `mckay ρ i j`: the McKay matrix entry `(χ_ρ χ_i, χ_j)`, the multiplicity of the irreducible `V_j` in `ρ ⊗ V_i`,
  for irreducible characters `i`, `j` (`irrChars ℂ G` is the set of characters of irreducible representations of `G`).
  `natRep G` is the natural 2-dimensional representation of a subgroup `G` of `SU(2)`.
* `affineCycle k`, `affineD k`, `affineE6`, `affineE7` and `graphOfCartan (CartanMatrix.E 9)`: the affine Dynkin
  diagrams `Ã_{k+2}` (a cycle on `k + 3` vertices), `D̃_{k+4}` (on `k + 5` vertices), `Ẽ_6`, `Ẽ_7` and `Ẽ_8`, as simple
  graphs (`graphOfCartan M` joins `i ≠ j` when `M i j = M j i = -1`; `CartanMatrix.E 9` is Mathlib's Cartan matrix of
  `E_9 = Ẽ_8`).
-/

namespace UndergradKB.Headlines.RepresentationTheory

open Module Representation MvPolynomial UndergradKB.RepresentationTheory UndergradKB.RepresentationTheory.Roots
open scoped TensorProduct DirectSum

/-- **Frobenius's factorization of the group determinant** (Etingof et al. Theorem 4.7): for a finite group `G` and
a list `X` of its irreducible complex representations, one of each isomorphism class, the group determinant is
`ε ∏ᵢ Pᵢ ^ dim Vᵢ` with `Pᵢ = det (∑_g x_g ρᵢ(g))`, the `Pᵢ` are irreducible polynomials, and two of them are
proportional only if they are equal. Here `ε` is the sign of the permutation `g ↦ g⁻¹` of `G`: the matrix `(x_{gh})`
is the matrix of the regular representation only after reordering its columns by `h ↦ h⁻¹`, a sign the book omits.
Related: neither Mathlib nor Tau Ceti has the group determinant. -/
theorem groupDeterminant_factorization {G : Type*} [Group G] [Fintype G] [DecidableEq G] {ι : Type*} [Fintype ι]
    (X : ι → IrrRep ℂ G)
    (hinj : ∀ i j, Nonempty (Representation.Equiv (X i).ρ (X j).ρ) → i = j)
    (hsurj : ∀ Y : IrrRep ℂ G, ∃ i, Nonempty (Representation.Equiv Y.ρ (X i).ρ)) :
    groupDeterminant G ℂ = C (((Equiv.Perm.sign (Equiv.inv G) : ℤˣ) : ℤ) : ℂ) *
        ∏ i, groupPoly (X i).ρ ^ finrank ℂ (X i).V ∧
      (∀ i, Irreducible (groupPoly (X i).ρ)) ∧
      (∀ i j (c : ℂ), groupPoly (X i).ρ = C c * groupPoly (X j).ρ → i = j) := by
  sorry

/-- **Dixmier's lemma** (Etingof et al. Problem 1.23): every endomorphism of an irreducible representation of a
complex algebra on a space of countable dimension is a scalar. Related: Mathlib and Tau Ceti have Schur's lemma for
finite-dimensional (or compact) settings only. -/
theorem dixmier_lemma {A : Type*} {V : Type*} [Ring A] [Algebra ℂ A]
    [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V] [IsSimpleModule A V]
    (hV : Module.rank ℂ V ≤ Cardinal.aleph0) (φ : Module.End A V) :
    ∃ c : ℂ, φ = algebraMap ℂ (Module.End A V) c := by
  sorry

/-- **Peter–Weyl theorem for `GL_N(ℂ)`** (Etingof et al. Theorem 4.66 (ii)): the algebra of rational functions on
`GL_N(ℂ)` (polynomials in the matrix entries and `1 / det`) is isomorphic, as a vector space, to `⨁_λ L_λ^* ⊗ L_λ`,
the sum over all highest weights `λ`, by the map sending `f ⊗ v` in the summand of `λ` to the matrix coefficient
`x ↦ f (ρ_λ x v)`. The book's `GL_N × GL_N`-equivariance is not part of this statement; it follows from the formula
for the map. The summands use fixed models `L_λ` (`Lrep`) of the irreducible rational representations; the highest
weight is only an indexing (see Known restrictions in the README), and the spaces `L_λ` live in `Type`
(see Known restrictions in the README). Stated as the existence of the isomorphism with this formula (the library constructs it as a
definition). Related: Mathlib has no Peter–Weyl theorem; Tau Ceti has the analytic Peter–Weyl theorem for compact
groups (`L²`) and the span of the matrix coefficients of the regular comodule, but not this decomposition of the
coordinate ring of `GL_N`. -/
theorem peter_weyl_gl {N : ℕ} :
    ∃ e : (⨁ lam : HighestWeights N, Module.Dual ℂ (LCarrier lam) ⊗[ℂ] LCarrier lam) ≃ₗ[ℂ]
        (ratFunctions N ℂ).toSubmodule,
      ∀ (lam : HighestWeights N) (f : Module.Dual ℂ (LCarrier lam)) (v : LCarrier lam) (x : GL (Fin N) ℂ),
        (e (DirectSum.lof ℂ _ (fun lam => Module.Dual ℂ (LCarrier lam) ⊗[ℂ] LCarrier lam) lam (f ⊗ₜ v)) :
          GL (Fin N) ℂ → ℂ) x = f (Lrep lam x v) := by
  sorry

/-- **Every irreducible rational representation of `GL_N(ℂ)` is some `L_λ`** (Etingof et al. Theorem 4.66 (i)): a
finite-dimensional irreducible rational representation of `GL_N(ℂ)` is isomorphic to `L_ν ⊗ det^a` for a Young
diagram `ν` with at most `N` rows and an integer `a`, i.e. to the representation `L_λ` with highest weight
`λ_j = ν_j + a`. The space is in `Type` (see Known restrictions in the README), and the highest weight is only an indexing
(see Known restrictions in the README). Related: Mathlib has nothing; Tau Ceti has the complete reducibility of rational representations of
`GL_n` (linear reductivity) and the classification of the irreducible modules of the Lie algebra `gl_N` by dominant
weights, but not this classification of the representations of the group by `ν` and `a`. -/
theorem rational_irrep_is_glIrrep {N : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    {ρ : Representation ℂ (GL (Fin N) ℂ) W} (hρ : IsRationalRep ρ) (hirr : IsIrredRep ρ) :
    ∃ (n : ℕ) (ν : DiagramsOfSize n) (a : ℤ), ν.1.colLen 0 ≤ N ∧
      Nonempty (Representation.Equiv ρ (glIrrep (N := N) ν a)) := by
  sorry

/-- **The irreducible rational representations of `GL_N(ℂ)` are pairwise non-isomorphic** (Etingof et al. Definition
4.65 and Theorem 4.66 (i)): for diagrams `ν`, `μ` with at most `N` rows, `L_ν ⊗ det^a ≅ L_μ ⊗ det^b` if and only if
they have the same highest weight, `ν_j + a = μ_j + b` for all `j`. The highest weight is only an indexing
(see Known restrictions in the README). Related: see the classification above; neither Mathlib nor Tau Ceti has the group-level statement. -/
theorem glIrrep_iso_iff {N n m : ℕ} (ν : DiagramsOfSize n) (μ : DiagramsOfSize m)
    (hν : ν.1.colLen 0 ≤ N) (hμ : μ.1.colLen 0 ≤ N) (a b : ℤ) :
    Nonempty (Representation.Equiv (glIrrep (N := N) ν a) (glIrrep (N := N) μ b)) ↔
      highestWeight N ν a = highestWeight N μ b := by
  sorry

/-- **Complete reducibility of rational representations of `GL_N(ℂ)` into the `L_λ`** (Etingof et al. Theorem 4.66
(i)): a finite-dimensional rational representation of `GL_N(ℂ)` is the internal direct sum of finitely many invariant
subspaces, each isomorphic to some `L_ν ⊗ det^a` (`ν` a diagram with at most `N` rows, `a : ℤ`). The space is in
`Type` (see Known restrictions in the README), and the highest weight is only an indexing (see Known restrictions in the README). Related: Tau Ceti has
complete reducibility of rational representations of `GL_n` in characteristic `0` as comodules, without listing the
constituents; Mathlib has nothing. -/
theorem rational_rep_decomposition {N : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    {ρ : Representation ℂ (GL (Fin N) ℂ) W} (hρ : IsRationalRep ρ) :
    ∃ (s : Finset (Submodule ℂ W)) (h : ∀ U ∈ s, ∀ g, ∀ w ∈ U, ρ g w ∈ U),
      DirectSum.IsInternal (fun U : s => (U : Submodule ℂ W)) ∧
      ∀ U (hU : U ∈ s), ∃ (n : ℕ) (ν : DiagramsOfSize n) (a : ℤ), ν.1.colLen 0 ≤ N ∧
        Nonempty (Representation.Equiv (⟨U, fun g _ hw => h U hU g _ hw⟩ : Subrepresentation ρ).toRepresentation
          (glIrrep (N := N) ν a)) := by
  sorry

open scoped Classical in
/-- **The McKay graph of a finite subgroup of `SU(2)` is an affine Dynkin diagram** (Etingof et al. Problem 5.5 (c)):
let `G ≠ 1` be a finite subgroup of `SU(2)`, `V` its natural 2-dimensional representation, and `r_ij` the
multiplicity of the irreducible `V_j` in `V ⊗ V_i` (the McKay matrix). Then either two vertices are joined by a double
edge and they are all the irreducible representations (`Ã_1`), or all `r_ij` are `0` or `1` and the graph with
adjacency `r_ij = 1`, on the irreducible representations numbered by `Fin N`, is isomorphic to a cycle `Ã_k`, to
`D̃_k`, or to `Ẽ_6`, `Ẽ_7` or `Ẽ_8`. This is the graph half of the McKay correspondence: the converse (every affine
ADE diagram occurs, for the corresponding binary polyhedral group) and the classification of the finite subgroups of
`SU(2)` are not part of it. Related: neither Mathlib nor Tau Ceti has a theorem on McKay graphs (Tau Ceti mentions
them only in comments); Tau Ceti has an equivalent recognition of the affine Dynkin diagrams, but the library's proof
uses its own classification of them. -/
theorem mckay_affine_classification (G : Subgroup (Matrix.specialUnitaryGroup (Fin 2) ℂ)) [Fintype G]
    [Invertible (Nat.card G : ℂ)] (hG : G ≠ ⊥) :
    (∃ i j : irrChars ℂ G, i ≠ j ∧ mckay (natRep G) i j = 2 ∧ ∀ k, k = i ∨ k = j) ∨
    ∃ (N : ℕ) (e : irrChars ℂ G ≃ Fin N) (M : SimpleGraph (Fin N)),
      (∀ i j, mckay (natRep G) i j = 0 ∨ mckay (natRep G) i j = 1) ∧
      (∀ i j, M.Adj (e i) (e j) ↔ mckay (natRep G) i j = 1) ∧
      ((∃ k, Nonempty (affineCycle k ≃g M)) ∨ (∃ k, Nonempty (affineD k ≃g M)) ∨
        Nonempty (affineE6 ≃g M) ∨ Nonempty (affineE7 ≃g M) ∨
        Nonempty (graphOfCartan (CartanMatrix.E 9) ≃g M)) := by
  sorry

end UndergradKB.Headlines.RepresentationTheory
