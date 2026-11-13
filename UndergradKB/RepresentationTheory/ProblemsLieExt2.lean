import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.NatCard
import UndergradKB.Common.Attr

/-! # Problem 2.22(b) (Etingof et al.)

A representation of the algebra `B = k⟨x_1, ..., x_n⟩ / (x_i x_j)` is the same as operators `X_1, ..., X_n` on a
space `V` with `X_i X_j = 0` for all `i, j`; we work in this operator form.  For `n ≥ 2` the family
`X_1 = E_{12}`, `X_2 = λ E_{12}`, `X_i = 0` (`i ≥ 3`) on `k^2` gives indecomposable representations, pairwise
non-isomorphic for different `λ`; over an infinite field there are therefore infinitely many isomorphism
classes.  The classification of 2-dimensional representations of `k[x_1, ..., x_n]` is not formalized.
-/

namespace UndergradKB.RepresentationTheory

section Ext22b

variable {k : Type*} [Field k] {n : ℕ} {V V' V'' : Type*} [AddCommGroup V] [Module k V]
  [AddCommGroup V'] [Module k V'] [AddCommGroup V''] [Module k V'']

/-- A representation of `k⟨x_1, ..., x_n⟩ / (x_i x_j)` in operator form: operators with `X_i X_j = 0`. -/
def IsZeroProdRep (X : Fin n → Module.End k V) : Prop := ∀ i j, X i * X j = 0

/-- A subspace invariant under all the operators. -/
def IsInvFam (X : Fin n → Module.End k V) (U : Submodule k V) : Prop := ∀ i, U.map (X i) ≤ U

/-- Indecomposable: nonzero and not a direct sum of two nonzero invariant subspaces. -/
def IsIndecomposableRep (X : Fin n → Module.End k V) : Prop :=
  Nontrivial V ∧ ∀ U₁ U₂ : Submodule k V, IsInvFam X U₁ → IsInvFam X U₂ → IsCompl U₁ U₂ →
    U₁ = ⊥ ∨ U₂ = ⊥

/-- Isomorphism of representations in operator form. -/
def RepIso (X : Fin n → Module.End k V) (X' : Fin n → Module.End k V') : Prop :=
  ∃ T : V ≃ₗ[k] V', ∀ i v, T (X i v) = X' i (T v)

theorem RepIso.refl (X : Fin n → Module.End k V) : RepIso X X := ⟨LinearEquiv.refl k V, fun _ _ => rfl⟩

theorem RepIso.symm {X : Fin n → Module.End k V} {X' : Fin n → Module.End k V'} (h : RepIso X X') :
    RepIso X' X := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T.symm, fun i v => ?_⟩
  apply T.injective
  rw [hT, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem RepIso.trans {X : Fin n → Module.End k V} {X' : Fin n → Module.End k V'}
    {X'' : Fin n → Module.End k V''} (h : RepIso X X') (h' : RepIso X' X'') : RepIso X X'' := by
  obtain ⟨T, hT⟩ := h
  obtain ⟨S, hS⟩ := h'
  exact ⟨T.trans S, fun i v => by simp [hT, hS]⟩

variable (k) in
/-- The nilpotent `E_{12} : e_2 ↦ e_1` on `k^2`. -/
noncomputable def nilE : Module.End k (Fin 2 → k) :=
  (LinearMap.single k (fun _ : Fin 2 => k) 0) ∘ₗ LinearMap.proj 1

theorem nilE_apply (f : Fin 2 → k) : nilE k f = Pi.single 0 (f 1) := by simp [nilE]

/-- The coefficient of `E_{12}` in `X_i`: `1, λ, 0, 0, ...`. -/
def famCoef (l : k) (i : Fin n) : k := if i.val = 0 then 1 else if i.val = 1 then l else 0

/-- The family `X_1 = E_{12}`, `X_2 = λ E_{12}`, `X_i = 0` for `i ≥ 3` on `k^2`. -/
noncomputable def nilFam (n : ℕ) (l : k) : Fin n → Module.End k (Fin 2 → k) :=
  fun i => famCoef l i • nilE k

theorem nilFam_isZeroProdRep (l : k) : IsZeroProdRep (nilFam n l) := by
  intro i j
  refine LinearMap.ext fun f => ?_
  simp [nilFam, nilE_apply]

theorem nilFam_zero (hn : 2 ≤ n) (l : k) (f : Fin 2 → k) :
    nilFam n l ⟨0, by omega⟩ f = nilE k f := by
  simp [nilFam, famCoef]

theorem nilFam_one (hn : 2 ≤ n) (l : k) (f : Fin 2 → k) :
    nilFam n l ⟨1, by omega⟩ f = l • nilE k f := by
  simp [nilFam, famCoef]

/-- Every nonzero invariant subspace contains `e_1`. -/
theorem single_mem_of_inv (hn : 2 ≤ n) (l : k) (U : Submodule k (Fin 2 → k))
    (hU : IsInvFam (nilFam n l) U) (hne : U ≠ ⊥) : (Pi.single 0 1 : Fin 2 → k) ∈ U := by
  obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  by_cases h1 : u 1 = 0
  · have h0 : u 0 ≠ 0 := by
      intro h
      apply hu0
      funext j
      fin_cases j <;> simp [h, h1]
    have : u = u 0 • (Pi.single 0 1 : Fin 2 → k) := by
      funext j
      fin_cases j <;> simp [h1]
    have h2 := U.smul_mem (u 0)⁻¹ huU
    have h3 : (u 0)⁻¹ • u = (Pi.single 0 1 : Fin 2 → k) := by
      funext j; fin_cases j <;> simp [h1, h0]
    rwa [h3] at h2
  · have hm : nilFam n l ⟨0, by omega⟩ u ∈ U := hU ⟨0, by omega⟩ ⟨u, huU, rfl⟩
    rw [nilFam_zero hn, nilE_apply] at hm
    have : (Pi.single 0 (u 1) : Fin 2 → k) = u 1 • (Pi.single 0 1 : Fin 2 → k) := by
      funext j; fin_cases j <;> simp
    rw [this] at hm
    have h2 := U.smul_mem (u 1)⁻¹ hm
    rwa [smul_smul, inv_mul_cancel₀ h1, one_smul] at h2

/-- Each member of the family is an indecomposable representation. -/
@[kb "etingof2011" "Problem 2.22, p. 30"]
theorem nilFam_indecomposable (hn : 2 ≤ n) (l : k) : IsIndecomposableRep (nilFam n l) := by
  refine ⟨inferInstance, fun U₁ U₂ h₁ h₂ hc => ?_⟩
  by_contra hcon
  push Not at hcon
  have a1 := single_mem_of_inv hn l U₁ h₁ hcon.1
  have a2 := single_mem_of_inv hn l U₂ h₂ hcon.2
  have : (Pi.single 0 1 : Fin 2 → k) ∈ U₁ ⊓ U₂ := ⟨a1, a2⟩
  rw [hc.inf_eq_bot, Submodule.mem_bot] at this
  have := congr_fun this 0
  simp at this

/-- Members of the family with different parameters are not isomorphic. -/
@[kb "etingof2011" "Problem 2.22, p. 30"]
theorem nilFam_iso_imp_eq (hn : 2 ≤ n) {l m : k} (h : RepIso (nilFam n l) (nilFam n m)) : l = m := by
  obtain ⟨T, hT⟩ := h
  have h0 := fun v => hT ⟨0, by omega⟩ v
  have h1 := fun v => hT ⟨1, by omega⟩ v
  simp only [nilFam_zero hn, nilFam_one hn] at h0 h1
  have e : nilE k (Pi.single 1 1 : Fin 2 → k) = Pi.single 0 1 := by simp [nilE_apply]
  have key := h1 (Pi.single 1 1)
  rw [map_smul, ← h0] at key
  -- key : l • T e₁ = m • T e₁
  have hne : T (Pi.single 0 1 : Fin 2 → k) ≠ 0 := by
    intro h
    have := T.injective (h.trans (map_zero T).symm)
    have := congr_fun this 0
    simp at this
  rw [e] at key
  by_contra hlm
  have : (l - m) • T (Pi.single 0 1 : Fin 2 → k) = 0 := by rw [sub_smul, key, sub_self]
  exact hne ((smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hlm))

/-- **Etingof et al., Problem 2.22(b)**: for `n ≥ 2` and an infinite field, the algebra
`k⟨x_1, ..., x_n⟩/(x_i x_j)` (representations = operators with `X_i X_j = 0`) has infinitely many pairwise
non-isomorphic indecomposable representations: the representations `nilFam n l` are indecomposable, and any
finite set of representations on `k^2` misses some `nilFam n l`. -/
@[kb "etingof2011" "Problem 2.22, p. 30"]
theorem infinitely_many_indecomposable [Infinite k] (hn : 2 ≤ n)
    (S : Finset (Fin n → Module.End k (Fin 2 → k))) :
    ∃ l : k, IsZeroProdRep (nilFam n l) ∧ IsIndecomposableRep (nilFam n l) ∧
      ∀ s ∈ S, ¬ RepIso (nilFam n l) s := by
  classical
  by_contra hcon
  push Not at hcon
  have : ∀ l : k, ∃ s : S, RepIso (nilFam n l) s.1 := fun l => by
    obtain ⟨s, hs, hi⟩ := hcon l (nilFam_isZeroProdRep l) (nilFam_indecomposable hn l)
    exact ⟨⟨s, hs⟩, hi⟩
  choose g hg using this
  have hinj : Function.Injective g := by
    intro l m hlm
    exact nilFam_iso_imp_eq hn ((hg l).trans (hlm ▸ (hg m).symm))
  exact not_injective_infinite_finite g hinj

end Ext22b

end UndergradKB.RepresentationTheory
