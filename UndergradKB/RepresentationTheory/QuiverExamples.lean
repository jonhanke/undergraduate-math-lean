import UndergradKB.RepresentationTheory.Quiver
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import UndergradKB.Common.Attr

/-! # Example 5.8: representations of the quiver `A₂` (Etingof et al., §5.1)

The quiver `A₂` has two vertices `src`, `tgt` and one arrow `src ⟶ tgt`. We build the representation attached to a
linear map `f : U → W`, show that three standard ones (`k → 0`, `k → k` with the identity, `0 → k`) are
indecomposable, and that they are pairwise non-isomorphic (they have different dimension vectors).
The classification statement (every indecomposable finite-dimensional representation is isomorphic to one of these)
is not proved here.
-/

namespace UndergradKB.RepresentationTheory

universe u

/-- The two vertices of `A₂`. -/
inductive A2V : Type
  | src
  | tgt

/-- The single arrow of `A₂`, from `src` to `tgt`. -/
inductive A2Arrow : A2V → A2V → Type
  | arr : A2Arrow A2V.src A2V.tgt

instance : Quiver.{0} A2V := ⟨A2Arrow⟩

/-- The spaces of the representation attached to `U → W`. -/
def A2obj (U W : Type u) : A2V → Type u
  | A2V.src => U
  | A2V.tgt => W

section

variable (U W : Type u) (k : Type u) [Field k] [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]

instance (i : A2V) : AddCommGroup (A2obj U W i) := by
  cases i
  · exact inferInstanceAs (AddCommGroup U)
  · exact inferInstanceAs (AddCommGroup W)

instance (i : A2V) : Module k (A2obj U W i) := by
  cases i
  · exact inferInstanceAs (Module k U)
  · exact inferInstanceAs (Module k W)

end

variable {k : Type u} [Field k] {U W : Type u} [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]

/-- The representation of `A₂` given by a linear map `f : U → W`. -/
def A2Rep (f : U →ₗ[k] W) : QRep k A2V where
  obj := A2obj U W
  map := by
    intro i j a
    cases a
    exact f

theorem A2Rep_dimVec_src (f : U →ₗ[k] W) : (A2Rep f).dimVec A2V.src = Module.finrank k U := rfl

theorem A2Rep_dimVec_tgt (f : U →ₗ[k] W) : (A2Rep f).dimVec A2V.tgt = Module.finrank k W := rfl

/-- A one-dimensional-or-zero space condition used to organise the proofs. -/
private def OneOrZero (k : Type u) [Field k] (M : Type u) [AddCommGroup M] [Module k M] : Prop :=
  Subsingleton M ∨ ∃ v : M, v ≠ 0 ∧ ∀ w, ∃ r : k, r • v = w

private theorem compl_cases {M : Type u} [AddCommGroup M] [Module k M] (h : OneOrZero k M)
    {S T : Submodule k M} (hST : IsCompl S T) : S = ⊥ ∨ T = ⊥ := by
  rcases h with h | h
  · exact Or.inl (Subsingleton.elim _ _)
  · exact rank_one_isCompl h hST

private theorem a2_eq_bot {f : U →ₗ[k] W} (S : QRep.Subrep (A2Rep f))
    (h1 : S.carrier A2V.src = ⊥) (h2 : S.carrier A2V.tgt = ⊥) : S = ⊥ := by
  apply QRep.Subrep.ext
  intro i
  cases i
  · exact h1
  · exact h2

private theorem a2_mixed {f : U →ₗ[k] W} (hf : Function.Injective f) [Nontrivial U]
    (S T : QRep.Subrep (A2Rep f)) (hST : IsCompl (S.carrier A2V.src) (T.carrier A2V.src))
    (hS : S.carrier A2V.src = ⊥) (hT : T.carrier A2V.tgt = ⊥) : False := by
  have hTtop : T.carrier A2V.src = ⊤ := by
    have := hST.sup_eq_top
    rwa [hS, bot_sup_eq] at this
  obtain ⟨u, hu⟩ := exists_ne (0 : U)
  have hmem : (A2Rep f).map (show A2V.src ⟶ A2V.tgt from A2Arrow.arr) u ∈ T.carrier A2V.tgt :=
    T.map_mem (show A2V.src ⟶ A2V.tgt from A2Arrow.arr) (x := u) (by rw [hTtop]; trivial)
  rw [hT, Submodule.mem_bot] at hmem
  have hmem' : f u = 0 := hmem
  exact hu (hf (by rw [hmem', map_zero]))

private theorem a2_mixed' {f : U →ₗ[k] W} (hf : Nontrivial U → Nontrivial W → Function.Injective f)
    (S T : QRep.Subrep (A2Rep f)) (hST : IsCompl (S.carrier A2V.src) (T.carrier A2V.src))
    (hS : S.carrier A2V.src = ⊥) (hT : T.carrier A2V.tgt = ⊥) : S = ⊥ ∨ T = ⊥ := by
  by_cases hUs : Subsingleton U
  · right
    refine a2_eq_bot T ?_ hT
    exact (Submodule.eq_bot_iff _).2 fun x _ => Subsingleton.elim (α := U) _ _
  by_cases hWs : Subsingleton W
  · left
    refine a2_eq_bot S hS ?_
    exact (Submodule.eq_bot_iff _).2 fun x _ => Subsingleton.elim (α := W) _ _
  rw [not_subsingleton_iff_nontrivial] at hUs hWs
  exact (a2_mixed (hf hUs hWs) S T hST hS hT).elim

private theorem a2_isIndecomposable (f : U →ₗ[k] W) (hU : OneOrZero k U) (hW : OneOrZero k W)
    (hnt : Nontrivial U ∨ Nontrivial W) (hf : Nontrivial U → Nontrivial W → Function.Injective f) :
    (A2Rep f).IsIndecomposable := by
  refine ⟨?_, ?_⟩
  · intro h
    rcases hnt with hn | hn
    · have h' : (⊥ : Submodule k U) = ⊤ := congrArg (fun S : QRep.Subrep (A2Rep f) => S.carrier A2V.src) h
      exact bot_ne_top h'
    · have h' : (⊥ : Submodule k W) = ⊤ := congrArg (fun S : QRep.Subrep (A2Rep f) => S.carrier A2V.tgt) h
      exact bot_ne_top h'
  · intro S T hST
    have hs := compl_cases hU (hST A2V.src)
    have ht := compl_cases hW (hST A2V.tgt)
    rcases hs with hs | hs <;> rcases ht with ht | ht
    · exact Or.inl (a2_eq_bot S hs ht)
    · exact a2_mixed' hf S T (hST A2V.src) hs ht
    · exact (a2_mixed' hf T S (hST A2V.src).symm hs ht).symm
    · exact Or.inr (a2_eq_bot T hs ht)

private theorem oneOrZero_self : OneOrZero k k :=
  Or.inr ⟨1, one_ne_zero, fun w => ⟨w, by simp⟩⟩

private theorem oneOrZero_punit : OneOrZero k PUnit.{u + 1} :=
  Or.inl inferInstance

/-- The representation `k → 0` of `A₂`. -/
def A2Rep.kToZero (k : Type u) [Field k] : QRep k A2V := A2Rep (0 : k →ₗ[k] PUnit.{u + 1})

/-- The representation `k → k` of `A₂` given by the identity. -/
def A2Rep.kToK (k : Type u) [Field k] : QRep k A2V := A2Rep (LinearMap.id : k →ₗ[k] k)

/-- The representation `0 → k` of `A₂`. -/
def A2Rep.zeroToK (k : Type u) [Field k] : QRep k A2V := A2Rep (0 : PUnit.{u + 1} →ₗ[k] k)

/-- **Example 5.8** (part): the representation `k → 0` of `A₂` is indecomposable. -/
@[kb "etingof2011" "Example 5.8, p. 81"]
theorem A2Rep.kToZero_isIndecomposable (k : Type u) [Field k] : (A2Rep.kToZero k).IsIndecomposable :=
  a2_isIndecomposable _ oneOrZero_self oneOrZero_punit (Or.inl inferInstance)
    (fun _ h => (not_nontrivial_iff_subsingleton.mpr inferInstance h).elim)

/-- **Example 5.8** (part): the representation `k → k` (identity) of `A₂` is indecomposable. -/
@[kb "etingof2011" "Example 5.8, p. 81"]
theorem A2Rep.kToK_isIndecomposable (k : Type u) [Field k] : (A2Rep.kToK k).IsIndecomposable :=
  a2_isIndecomposable _ oneOrZero_self oneOrZero_self (Or.inl inferInstance) (fun _ _ => fun _ _ h => h)

/-- **Example 5.8** (part): the representation `0 → k` of `A₂` is indecomposable. -/
@[kb "etingof2011" "Example 5.8, p. 81"]
theorem A2Rep.zeroToK_isIndecomposable (k : Type u) [Field k] : (A2Rep.zeroToK k).IsIndecomposable :=
  a2_isIndecomposable _ oneOrZero_punit oneOrZero_self (Or.inr inferInstance)
    (fun h => (not_nontrivial_iff_subsingleton.mpr inferInstance h).elim)

/-- **Example 5.8** (part): the dimension vectors of the three representations are `(1,0)`, `(1,1)`, `(0,1)`. -/
theorem A2Rep.dimVec_kToZero (k : Type u) [Field k] :
    (A2Rep.kToZero k).dimVec A2V.src = 1 ∧ (A2Rep.kToZero k).dimVec A2V.tgt = 0 :=
  ⟨Module.finrank_self k, Module.finrank_zero_of_subsingleton (R := k) (M := PUnit.{u + 1})⟩

theorem A2Rep.dimVec_kToK (k : Type u) [Field k] :
    (A2Rep.kToK k).dimVec A2V.src = 1 ∧ (A2Rep.kToK k).dimVec A2V.tgt = 1 :=
  ⟨Module.finrank_self k, Module.finrank_self k⟩

theorem A2Rep.dimVec_zeroToK (k : Type u) [Field k] :
    (A2Rep.zeroToK k).dimVec A2V.src = 0 ∧ (A2Rep.zeroToK k).dimVec A2V.tgt = 1 :=
  ⟨Module.finrank_zero_of_subsingleton (R := k) (M := PUnit.{u + 1}), Module.finrank_self k⟩

/-- **Example 5.8** (part): the three representations are pairwise non-isomorphic. -/
@[kb "etingof2011" "Example 5.8, p. 81"]
theorem A2Rep.pairwise_not_isomorphic (k : Type u) [Field k] :
    ¬ QRep.Isomorphic (A2Rep.kToZero k) (A2Rep.kToK k) ∧
    ¬ QRep.Isomorphic (A2Rep.kToZero k) (A2Rep.zeroToK k) ∧
    ¬ QRep.Isomorphic (A2Rep.kToK k) (A2Rep.zeroToK k) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := (A2Rep.dimVec_kToZero k).2.symm.trans ((congrFun h.dimVec_eq A2V.tgt).trans (A2Rep.dimVec_kToK k).2)
    omega
  · have := (A2Rep.dimVec_kToZero k).1.symm.trans ((congrFun h.dimVec_eq A2V.src).trans (A2Rep.dimVec_zeroToK k).1)
    omega
  · have := (A2Rep.dimVec_kToK k).1.symm.trans ((congrFun h.dimVec_eq A2V.src).trans (A2Rep.dimVec_zeroToK k).1)
    omega

end UndergradKB.RepresentationTheory
