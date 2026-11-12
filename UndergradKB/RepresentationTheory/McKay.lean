import Mathlib.RepresentationTheory.Character
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.ToLin
import UndergradKB.RepresentationTheory.ComplexCharacters
import UndergradKB.Common.Attr

/-! # The McKay graph of a representation (Etingof et al., Problem 5.5)

For a finite group `G` and a finite-dimensional complex representation `ρ` (the book takes the natural
2-dimensional representation `V` of a finite subgroup of `SU(2)`), the McKay matrix has entries
`r_ij = (χ_V χ_i, χ_j)`, the multiplicity of the irreducible `V_j` in `V ⊗ V_i`.

Proved here:
* `mckay_symm`: if the character of `ρ` is real valued then `r_ij = r_ji`;
* `exists_natCast_mckay`: each `r_ij` is a natural number (a dimension of a space of intertwiners);
* `sum_mckay_mul_dim`: `∑_j r_ij dim V_j = dim V · dim V_i`, so for a 2-dimensional `ρ` the dimension vector
  is a kernel vector of `2 I - R`;
* `mckay_self_eq_zero`: if a central element acts on `ρ` as `-1`, then `r_ii = 0` (no loops);
* for a subgroup of `SU(2)` the natural representation is real (`natRep_character_inv`) and is 2-dimensional.

Connectedness of the graph is in `McKayConnected.lean`. Not proved: the identification of the connected graphs with a positive kernel vector of `2 I - R` as the affine
Dynkin graphs (the classification in `DynkinClassification` covers only simple graphs; the McKay graph is in
general a multigraph, and this needs the classification of multigraphs with that property).
-/

namespace UndergradKB.RepresentationTheory

open Representation Module

set_option linter.unusedSectionVars false

section General

variable {G V : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)

/-- The McKay matrix entry `r_ij = (χ_ρ χ_i, χ_j)` for irreducible characters `i`, `j`: the multiplicity of the
irreducible `V_j` in `ρ ⊗ V_i`. -/
noncomputable def mckay (i j : irrChars ℂ G) : ℂ :=
  pairing (ρ.character * (i : G → ℂ)) (j : G → ℂ)

/-- **Etingof et al., Problem 5.5**: symmetry `r_ij = r_ji` of the McKay matrix when the character of `ρ` is
real valued. -/
@[kb "etingof2011" "Problem 5.5, p. 80"]
theorem mckay_symm (hreal : ∀ g, ρ.character g⁻¹ = ρ.character g) (i j : irrChars ℂ G) :
    mckay ρ i j = mckay ρ j i := by
  unfold mckay
  simp only [pairing_apply, Pi.mul_apply]
  congr 1
  refine Fintype.sum_equiv (Equiv.inv G) _ _ fun g ↦ ?_
  simp only [Equiv.inv_apply, inv_inv, hreal]
  ring

/-- **Etingof et al., Problem 5.5**: the entries of the McKay matrix are natural numbers. -/
@[kb "etingof2011" "Problem 5.5, p. 80"]
theorem exists_natCast_mckay (i j : irrChars ℂ G) : ∃ n : ℕ, mckay ρ i j = n := by
  obtain ⟨X, hX⟩ := i.2
  obtain ⟨Y, hY⟩ := j.2
  have hX' : (i : G → ℂ) = X.ρ.character := hX.symm
  have hY' : (j : G → ℂ) = Y.ρ.character := hY.symm
  have h := hermitianPairing_character_eq_finrank (tprod ρ X.ρ) Y.ρ
  refine ⟨finrank ℂ (IntertwiningMap Y.ρ (tprod ρ X.ρ)), ?_⟩
  rw [← h, hermitianPairing_character, mckay, hX', hY', char_tensor]

/-- The product of `χ_ρ` with an irreducible character is a class function. -/
theorem mul_irrChars_mem_classFunctions (i : irrChars ℂ G) :
    ρ.character * (i : G → ℂ) ∈ classFunctions ℂ G := by
  obtain ⟨X, hX⟩ := i.2
  have hX' : (i : G → ℂ) = X.ρ.character := hX.symm
  rw [hX', ← char_tensor]
  exact character_mem_classFunctions _

/-- Expansion of `χ_ρ χ_i` in the irreducible characters, with the McKay matrix as coefficients. -/
theorem mul_irrChars_eq_sum (i : irrChars ℂ G) :
    ρ.character * (i : G → ℂ) = ∑ j : irrChars ℂ G, mckay ρ i j • (j : G → ℂ) :=
  eq_sum_pairing_smul (mul_irrChars_mem_classFunctions ρ i)

/-- **Etingof et al., Problem 5.5**: evaluating at the identity, `∑_j r_ij dim V_j = dim ρ · dim V_i`. -/
@[kb "etingof2011" "Problem 5.5, p. 80"]
theorem sum_mckay_mul_dim (i : irrChars ℂ G) :
    ∑ j : irrChars ℂ G, mckay ρ i j * (j : G → ℂ) 1 = (finrank ℂ V : ℂ) * (i : G → ℂ) 1 := by
  have h := congrFun (mul_irrChars_eq_sum ρ i) 1
  simpa [Finset.sum_apply, char_one] using h.symm

/-- **Etingof et al., Problem 5.5**: if a central element `z` acts on `ρ` as `-1`, the McKay graph has no loops. -/
@[kb "etingof2011" "Problem 5.5, p. 80"]
theorem mckay_self_eq_zero {z : G} (hz : ∀ g, z * g = g * z) (hρ : ρ z = -LinearMap.id)
    (i : irrChars ℂ G) : mckay ρ i i = 0 := by
  obtain ⟨X, hX⟩ := i.2
  have hX' : (i : G → ℂ) = X.ρ.character := hX.symm
  have hz' : ∀ g, z⁻¹ * g = g * z⁻¹ := fun g ↦ by
    simpa using (congrArg (·⁻¹) (hz g⁻¹)).symm
  have key : ∀ w : G, (∀ g, w * g = g * w) → ∃ c : ℂ, ∀ h, X.ρ.character (w * h) = c * X.ρ.character h := by
    intro w hw
    obtain ⟨c, hc⟩ := exists_eq_smul_id_of_commute (ρ := X.ρ) (X.ρ w) fun g ↦ by
      rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul, hw]
    refine ⟨c, fun h ↦ ?_⟩
    simp only [Representation.character, map_mul, hc, Module.End.mul_eq_comp, LinearMap.smul_comp,
      LinearMap.id_comp, map_smul, smul_eq_mul]
  obtain ⟨c, hc⟩ := key z hz
  obtain ⟨c', hc'⟩ := key z⁻¹ hz'
  have hcc : ∀ h, c' * (c * X.ρ.character h) = X.ρ.character h := fun h ↦ by
    rw [← hc, ← hc', ← mul_assoc, inv_mul_cancel, one_mul]
  have hV : ∀ h, ρ.character (z * h) = - ρ.character h := fun h ↦ by
    simp only [Representation.character, map_mul, hρ, Module.End.mul_eq_comp, LinearMap.neg_comp,
      LinearMap.id_comp, map_neg]
  unfold mckay
  rw [pairing_apply, hX']
  simp only [Pi.mul_apply]
  have hS : ∑ g : G, ρ.character g * X.ρ.character g * X.ρ.character g⁻¹ = 0 := by
    have h1 : ∑ g : G, ρ.character g * X.ρ.character g * X.ρ.character g⁻¹
        = ∑ g : G, ρ.character (z * g) * X.ρ.character (z * g) * X.ρ.character (z * g)⁻¹ :=
      (Fintype.sum_equiv (Equiv.mulLeft z) _ _ fun g ↦ rfl).symm
    have h2 : ∀ g : G, ρ.character (z * g) * X.ρ.character (z * g) * X.ρ.character (z * g)⁻¹
        = - (ρ.character g * X.ρ.character g * X.ρ.character g⁻¹) := fun g ↦ by
      have : (z * g)⁻¹ = z⁻¹ * g⁻¹ := by rw [mul_inv_rev, ← hz' g⁻¹]
      rw [this, hV, hc, hc']
      have := hcc g
      calc _ = -(ρ.character g * (c' * (c * X.ρ.character g)) * X.ρ.character g⁻¹) := by ring
        _ = _ := by rw [this]
    simp only [h2, Finset.sum_neg_distrib] at h1
    linear_combination (1 / 2 : ℂ) * h1
  rw [hS, mul_zero]

end General

/-! ### Subgroups of `SU(2)` -/

section SU2

variable (G : Subgroup (Matrix.specialUnitaryGroup (Fin 2) ℂ))

/-- The natural 2-dimensional representation of a subgroup of `SU(2)`. -/
noncomputable def natRep : Representation ℂ G (Fin 2 → ℂ) where
  toFun g := Matrix.toLin' (g.1.1 : Matrix (Fin 2) (Fin 2) ℂ)
  map_one' := by
    show Matrix.toLin' (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1
    exact Matrix.toLin'_one
  map_mul' a b := by
    show Matrix.toLin' (a.1.1 * b.1.1) = _
    rw [Matrix.toLin'_mul]
    rfl

theorem natRep_character (g : G) : (natRep G).character g = (g.1.1 : Matrix (Fin 2) (Fin 2) ℂ).trace := by
  show LinearMap.trace ℂ _ (Matrix.toLin' _) = _
  rw [Matrix.toLin_eq_toLin' |>.symm, Matrix.trace_toLin_eq]

/-- For a `2 × 2` matrix of determinant one that is unitary, the inverse is the adjugate and the conjugate
transpose, so inversion preserves the trace. -/
theorem natRep_character_inv (g : G) : (natRep G).character g⁻¹ = (natRep G).character g := by
  rw [natRep_character, natRep_character]
  have hg := g.1.2
  have h1 : (g.1.1 : Matrix (Fin 2) (Fin 2) ℂ) * star g.1.1 = 1 := hg.1.2
  have hdet : (g.1.1 : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := hg.2
  have h2 : (g.1.1 : Matrix (Fin 2) (Fin 2) ℂ).adjugate * g.1.1 = 1 := by
    rw [Matrix.adjugate_mul, hdet, one_smul]
  have h3 : (g.1.1 : Matrix (Fin 2) (Fin 2) ℂ).adjugate = star g.1.1 := by
    calc _ = (g.1.1 : Matrix (Fin 2) (Fin 2) ℂ).adjugate * (g.1.1 * star g.1.1) := by rw [h1, Matrix.mul_one]
      _ = star g.1.1 := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have h4 : ((g⁻¹ : G).1.1 : Matrix (Fin 2) (Fin 2) ℂ) = (g.1.1 : Matrix (Fin 2) (Fin 2) ℂ).adjugate := by
    rw [h3]; rfl
  rw [h4, Matrix.adjugate_fin_two]
  simp [Matrix.trace_fin_two, add_comm]

/-- The natural representation of a subgroup of `SU(2)` has dimension two. -/
theorem finrank_natRep : finrank ℂ (Fin 2 → ℂ) = 2 := by simp

/-- **Etingof et al., Problem 5.5**: for a finite subgroup `G` of `SU(2)` and the natural 2-dimensional
representation `V`, the McKay matrix is symmetric. -/
@[kb "etingof2011" "Problem 5.5, p. 80"]
theorem mckay_natRep_symm [Fintype G] [Invertible (Nat.card G : ℂ)] (i j : irrChars ℂ G) :
    mckay (natRep G) i j = mckay (natRep G) j i :=
  mckay_symm _ (natRep_character_inv G) i j

/-- **Etingof et al., Problem 5.5**: for a finite subgroup of `SU(2)` containing `-1`, the McKay graph of the
natural representation has no loops. -/
@[kb "etingof2011" "Problem 5.5, p. 80"]
theorem mckay_natRep_self_eq_zero [Fintype G] [Invertible (Nat.card G : ℂ)] (z : G)
    (hz : (z.1.1 : Matrix (Fin 2) (Fin 2) ℂ) = -1) (i : irrChars ℂ G) : mckay (natRep G) i i = 0 := by
  refine mckay_self_eq_zero (natRep G) (z := z) (fun g ↦ ?_) ?_ i
  · refine Subtype.ext (Subtype.ext ?_)
    show z.1.1 * g.1.1 = g.1.1 * z.1.1
    rw [hz]; simp
  · show Matrix.toLin' (z.1.1 : Matrix (Fin 2) (Fin 2) ℂ) = _
    rw [hz]
    ext v i
    simp

end SU2

end UndergradKB.RepresentationTheory
