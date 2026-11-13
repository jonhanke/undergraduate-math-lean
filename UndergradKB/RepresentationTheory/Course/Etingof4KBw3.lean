import UndergradKB.RepresentationTheory.PeterWeyl
import UndergradKB.Common.Attr

/-!
# Etingof et al., Introduction to Representation Theory: Section 4.22 (polynomial representations of `GL(V)`)

Thin theorems in the book's terms for Definition 4.65 and Theorem 4.66, tagged with the source key `etingof2011`
and the locator of the item in the book.  The book's "polynomial" representations (matrix coefficients in
`k[g_ij][1/det g]`) are `IsRationalRep` here; `glIrrep ν a = L_ν ⊗ det^a` is the book's `L_λ` with
`λ_j = ν_j + a` (`highestWeight`).
-/

namespace UndergradKB.RepresentationTheory.Course

open UndergradKB.RepresentationTheory
open scoped TensorProduct DirectSum

variable {N : ℕ}

/-- Etingof et al., Definition 4.65: every non-increasing sequence `λ_1 ≥ ⋯ ≥ λ_N` of integers is the highest
weight of some `L_ν ⊗ det^a`. -/
@[kb "etingof2011" "Definition 4.65, p. 67"]
theorem etingof_4_65_a (lam : Fin N → ℤ) (hlam : Antitone lam) :
    ∃ (n : ℕ) (ν : DiagramsOfSize n) (a : ℤ), ν.1.colLen 0 ≤ N ∧ highestWeight N ν a = lam :=
  exists_highestWeight_eq lam hlam

/-- Etingof et al., Definition 4.65: `L_λ` is an irreducible representation of `GL_N(ℂ)` with matrix coefficients
in `ℂ[g_ij][1/det g]`. -/
@[kb "etingof2011" "Definition 4.65, p. 67"]
theorem etingof_4_65_b {n : ℕ} (ν : DiagramsOfSize n) (hν : ν.1.colLen 0 ≤ N) (a : ℤ) :
    IsRationalRep (glIrrep (N := N) ν a) ∧ IsIrredRep (glIrrep (N := N) ν a) :=
  ⟨isRationalRep_glIrrep ν a, isIrredRep_glIrrep ν hν a⟩

/-- Etingof et al., Definition 4.65 and Theorem 4.66 (i): the `L_λ` are determined up to isomorphism by their
highest weight, and different highest weights give non-isomorphic representations. -/
@[kb "etingof2011" "Theorem 4.66, p. 67"]
theorem etingof_4_66_a {n m : ℕ} (ν : DiagramsOfSize n) (μ : DiagramsOfSize m)
    (hν : ν.1.colLen 0 ≤ N) (hμ : μ.1.colLen 0 ≤ N) (a b : ℤ) :
    Nonempty (Representation.Equiv (glIrrep (N := N) ν a) (glIrrep (N := N) μ b)) ↔
      highestWeight N ν a = highestWeight N μ b :=
  glIrrep_equiv_iff ν μ hν hμ a b

/-- Etingof et al., Theorem 4.66 (i): a finite-dimensional polynomial (rational) representation of `GL_N(ℂ)` is
completely reducible. -/
@[kb "etingof2011" "Theorem 4.66, p. 67"]
theorem etingof_4_66_b {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    {ρ : Representation ℂ (GL (Fin N) ℂ) W} (hρ : IsRationalRep ρ) (U : Submodule ℂ W)
    (hU : ∀ g, ∀ w ∈ U, ρ g w ∈ U) : ∃ U' : Submodule ℂ W, (∀ g, ∀ w ∈ U', ρ g w ∈ U') ∧ IsCompl U U' :=
  hρ.exists_isCompl U hU

/-- Etingof et al., Theorem 4.66 (i): every irreducible finite-dimensional polynomial (rational) representation of
`GL_N(ℂ)` is isomorphic to some `L_λ`. -/
@[kb "etingof2011" "Theorem 4.66, p. 67"]
theorem etingof_4_66_c {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    {ρ : Representation ℂ (GL (Fin N) ℂ) W} (hρ : IsRationalRep ρ) (hirr : IsIrredRep ρ) :
    ∃ (n : ℕ) (ν : DiagramsOfSize n) (a : ℤ), ν.1.colLen 0 ≤ N ∧
      Nonempty (Representation.Equiv ρ (glIrrep (N := N) ν a)) :=
  hρ.exists_equiv_glIrrep hirr

/-- Etingof et al., Theorem 4.66 (i): a finite-dimensional polynomial (rational) representation of `GL_N(ℂ)` is a
direct sum of invariant subspaces, each isomorphic to some `L_λ`. -/
@[kb "etingof2011" "Theorem 4.66, p. 67"]
theorem etingof_4_66_d {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    {ρ : Representation ℂ (GL (Fin N) ℂ) W} (hρ : IsRationalRep ρ) :
    ∃ (s : Finset (Submodule ℂ W)) (h : ∀ U ∈ s, ∀ g, ∀ w ∈ U, ρ g w ∈ U),
      DirectSum.IsInternal (fun U : s => (U : Submodule ℂ W)) ∧
      ∀ U (hU : U ∈ s), ∃ (n : ℕ) (ν : DiagramsOfSize n) (a : ℤ), ν.1.colLen 0 ≤ N ∧
        Nonempty (Representation.Equiv (⟨U, fun g _ hw => h U hU g _ hw⟩ : Subrepresentation ρ).toRepresentation
          (glIrrep (N := N) ν a)) :=
  hρ.exists_isInternal_glIrrep

/-- Etingof et al., Theorem 4.66 (ii) (Peter-Weyl for `GL(V)`): the algebra of polynomial functions on `GL_N(ℂ)`
(polynomials in `g_ij` and `1 / det g`) is `⨁_λ L_λ^* ⊗ L_λ`, by matrix coefficients `f ⊗ v ↦ (x ↦ f(ρ_λ(x) v))`. -/
@[kb "etingof2011" "Theorem 4.66, p. 67"]
theorem etingof_4_66_e (lam : HighestWeights N) (f : Module.Dual ℂ (LCarrier lam)) (v : LCarrier lam)
    (x : GL (Fin N) ℂ) :
    (peterWeyl (DirectSum.lof ℂ _ (fun lam => Module.Dual ℂ (LCarrier lam) ⊗[ℂ] LCarrier lam) lam (f ⊗ₜ v)) :
      GL (Fin N) ℂ → ℂ) x = f (Lrep lam x v) :=
  peterWeyl_apply_tmul lam f v x

/-- Etingof et al., Theorem 4.66 (ii): the decomposition is compatible with the action of `GL(V) × GL(V)`,
`(g, h)` acting by `φ ↦ (x ↦ φ(g⁻¹ x h))` on functions and by `A ↦ ρ(h) A ρ(g)⁻¹` on `End(L_λ) = L_λ^* ⊗ L_λ`. -/
@[kb "etingof2011" "Theorem 4.66, p. 67"]
theorem etingof_4_66_f (lam : HighestWeights N) (g h : GL (Fin N) ℂ) (A : Module.End ℂ (LCarrier lam))
    (x : GL (Fin N) ℂ) :
    matCoeff lam (Lrep lam h * A * Lrep lam g⁻¹) x = matCoeff lam A (g⁻¹ * x * h) :=
  matCoeff_act lam g h A x

end UndergradKB.RepresentationTheory.Course
