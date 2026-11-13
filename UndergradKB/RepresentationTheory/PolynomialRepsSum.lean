import Mathlib.Algebra.DirectSum.Module
import Mathlib.Order.SupIndep
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.PolynomialRepsClassify

/-! # A rational representation of `GL_N(ℂ)` is a direct sum of `L_λ` (Etingof et al., Theorem 4.66 (i))

`IsRationalRep.exists_isInternal_glIrrep`: a finite-dimensional rational representation `W` of `GL_N(ℂ)` is the
internal direct sum of finitely many invariant subspaces, each isomorphic (as a representation) to some
`L_λ = L_ν ⊗ det^a`.  The `L_λ` for different highest weights are pairwise non-isomorphic (`glIrrep_equiv_iff`).

The proof splits off a minimal nonzero invariant subspace (irreducible) and an invariant complement
(`IsRationalRep.exists_isCompl`), and inducts on the dimension.
-/

namespace UndergradKB.RepresentationTheory

variable {N : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  {ρ : Representation ℂ (GL (Fin N) ℂ) W}

/-- `U` is invariant. -/
def IsInvariant (ρ : Representation ℂ (GL (Fin N) ℂ) W) (U : Submodule ℂ W) : Prop := ∀ g, ∀ w ∈ U, ρ g w ∈ U

/-- `U` is a minimal nonzero invariant subspace. -/
def IsMinInvariant (ρ : Representation ℂ (GL (Fin N) ℂ) W) (U : Submodule ℂ W) : Prop :=
  IsInvariant ρ U ∧ U ≠ ⊥ ∧ ∀ V, IsInvariant ρ V → V ≤ U → V = ⊥ ∨ V = U

theorem exists_isMinInvariant_le {S : Submodule ℂ W} (hS : IsInvariant ρ S) (hS0 : S ≠ ⊥) :
    ∃ U, IsMinInvariant ρ U ∧ U ≤ S := by
  classical
  have hex : ∃ d, ∃ V : Submodule ℂ W, IsInvariant ρ V ∧ V ≠ ⊥ ∧ V ≤ S ∧ Module.finrank ℂ V = d :=
    ⟨_, S, hS, hS0, le_rfl, rfl⟩
  obtain ⟨V, hV, hV0, hVS, hVd⟩ := Nat.find_spec hex
  refine ⟨V, ⟨hV, hV0, fun V' hV' hle => ?_⟩, hVS⟩
  by_cases h0 : V' = ⊥
  · exact Or.inl h0
  right
  have hmin := Nat.find_min' hex ⟨V', hV', h0, hle.trans hVS, rfl⟩
  rw [← hVd] at hmin
  exact Submodule.eq_of_le_of_finrank_le hle hmin

/-- The restriction of `ρ` to a minimal invariant subspace is irreducible. -/
theorem IsMinInvariant.isIrredRep {U : Submodule ℂ W} (hU : IsMinInvariant ρ U) :
    IsIrredRep (⟨U, fun g _ hw => hU.1 g _ hw⟩ : Subrepresentation ρ).toRepresentation := by
  obtain ⟨hinv, hne, hmin⟩ := hU
  refine ⟨(Submodule.nontrivial_iff_ne_bot).2 hne, fun V hV => ?_⟩
  have hV' : IsInvariant ρ (V.map U.subtype) := by
    rintro g _ ⟨v, hv, rfl⟩
    exact ⟨_, hV g v hv, rfl⟩
  rcases hmin _ hV' (Submodule.map_subtype_le U V) with h | h
  · left
    exact Submodule.map_injective_of_injective U.injective_subtype (by rw [h, Submodule.map_bot])
  · right
    apply Submodule.map_injective_of_injective U.injective_subtype
    rw [h, Submodule.map_top, Submodule.range_subtype]

theorem exists_finset_decomp (hρ : IsRationalRep ρ) :
    ∀ k : ℕ, ∀ S : Submodule ℂ W, IsInvariant ρ S → Module.finrank ℂ S ≤ k →
      ∃ s : Finset (Submodule ℂ W), (∀ U ∈ s, IsMinInvariant ρ U) ∧ s.SupIndep id ∧ s.sup id = S := by
  classical
  intro k
  induction k with
  | zero =>
    intro S _ hk
    have : S = ⊥ := Submodule.finrank_eq_zero.1 (Nat.le_zero.1 hk)
    exact ⟨∅, by simp, Finset.supIndep_empty _, by simp [this]⟩
  | succ k ih =>
    intro S hS hk
    by_cases hS0 : S = ⊥
    · exact ⟨∅, by simp, Finset.supIndep_empty _, by simp [hS0]⟩
    obtain ⟨V, hV, hVS⟩ := exists_isMinInvariant_le hS hS0
    obtain ⟨C, hC, hVC⟩ := hρ.exists_isCompl V hV.1
    have hS' : IsInvariant ρ (S ⊓ C) := fun g w hw => ⟨hS g w hw.1, hC g w hw.2⟩
    have hlt : S ⊓ C < S := by
      refine lt_of_le_of_ne inf_le_left fun h => hV.2.1 ?_
      have : V ≤ C := (hVS.trans h.symm.le).trans inf_le_right
      exact disjoint_self.1 (hVC.disjoint.mono_right this)
    have hk' : Module.finrank ℂ (S ⊓ C : Submodule ℂ W) ≤ k := by
      have := Submodule.finrank_lt_finrank_of_lt hlt
      omega
    obtain ⟨s, hs, hind, hsup⟩ := ih (S ⊓ C) hS' hk'
    refine ⟨insert V s, ?_, ?_, ?_⟩
    · intro U hU
      rcases Finset.mem_insert.1 hU with rfl | hU
      · exact hV
      · exact hs U hU
    · refine hind.insert ?_
      rw [hsup]
      exact hVC.disjoint.mono_right inf_le_right
    · rw [Finset.sup_insert, hsup, id]
      rw [inf_comm S C, ← sup_inf_assoc_of_le C hVS, hVC.codisjoint.eq_top, top_inf_eq]

/-- **Etingof et al., Theorem 4.66 (i).**  A finite-dimensional rational representation of `GL_N(ℂ)` is the internal
direct sum of finitely many invariant subspaces, each isomorphic to some `L_λ = L_ν ⊗ det^a` (`ν` a diagram with at
most `N` rows); the `L_λ` with different highest weights are pairwise non-isomorphic (`glIrrep_equiv_iff`). -/
@[kb "etingof2011" "Theorem 4.66, p. 67"]
theorem IsRationalRep.exists_isInternal_glIrrep (hρ : IsRationalRep ρ) :
    ∃ (s : Finset (Submodule ℂ W)) (h : ∀ U ∈ s, ∀ g, ∀ w ∈ U, ρ g w ∈ U),
      DirectSum.IsInternal (fun U : s => (U : Submodule ℂ W)) ∧
      ∀ U (hU : U ∈ s), ∃ (n : ℕ) (ν : DiagramsOfSize n) (a : ℤ), ν.1.colLen 0 ≤ N ∧
        Nonempty (Representation.Equiv (⟨U, fun g _ hw => h U hU g _ hw⟩ : Subrepresentation ρ).toRepresentation
          (glIrrep (N := N) ν a)) := by
  classical
  obtain ⟨s, hs, hind, hsup⟩ := exists_finset_decomp hρ _ ⊤ (fun _ _ _ => trivial) le_rfl
  refine ⟨s, fun U hU => (hs U hU).1, ?_, fun U hU => ?_⟩
  · apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · exact hind.independent
    · rw [← hsup, Finset.sup_eq_iSup, iSup_subtype']
      rfl
  · have hirr := (hs U hU).isIrredRep
    have hrat : IsRationalRep (⟨U, fun g _ hw => (hs U hU).1 g _ hw⟩ : Subrepresentation ρ).toRepresentation :=
      IsSRep.of_injective U.subtype U.injective_subtype (fun _ _ => rfl) hρ
    exact hrat.exists_equiv_glIrrep hirr

end UndergradKB.RepresentationTheory
