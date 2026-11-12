import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.SimpleModule.Basic
import UndergradKB.Common.Attr

/-! # Basic notions of representation theory (Etingof et al., Chapter 1)

* Problem 1.20: a nonzero finite-dimensional representation has an irreducible subrepresentation.
* Definition 1.15: indecomposable representations; irreducible implies indecomposable, and the converse
  holds when the characteristic of the field does not divide the order of a finite group (Maschke).
* Section 1.7: faithful representations; the regular representation of a group is faithful.
-/

namespace UndergradKB.RepresentationTheory

open Representation

section Irreducible

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]

/-- The image in `V` of a subrepresentation of a subrepresentation `W`, as a subrepresentation of `V`. -/
private def mapSub {ρ : Representation k G V} (W : Subrepresentation ρ)
    (σ : Subrepresentation W.toRepresentation) : Subrepresentation ρ where
  toSubmodule := σ.toSubmodule.map W.toSubmodule.subtype
  apply_mem_toSubmodule g v := by
    rintro ⟨x, hx, rfl⟩
    exact ⟨W.toRepresentation g x, σ.apply_mem_toSubmodule g hx, rfl⟩

/-- **Etingof et al., Problem 1.20**: every nonzero finite-dimensional representation of a group has
an irreducible subrepresentation. -/
@[kb "etingof2011" "Problem 1.20, p. 10"]
theorem exists_irreducible_subrepresentation (ρ : Representation k G V) [FiniteDimensional k V]
    [Nontrivial V] : ∃ W : Subrepresentation ρ, IsIrreducible W.toRepresentation := by
  classical
  have hne : (⊤ : Subrepresentation ρ) ∈ {W : Subrepresentation ρ | W ≠ ⊥} := by
    intro h
    have := congrArg Subrepresentation.toSubmodule h
    exact top_ne_bot (α := Submodule k V) this
  obtain ⟨W, hW, hmin⟩ := (InvImage.wf (fun W : Subrepresentation ρ => Module.finrank k W.toSubmodule)
    wellFounded_lt).has_min _ ⟨_, hne⟩
  have hW' : W.toSubmodule ≠ ⊥ := fun h => hW (Subrepresentation.toSubmodule_injective h)
  have : Nontrivial W.toSubmodule := Submodule.nontrivial_iff_ne_bot.2 hW'
  have hinj := Submodule.map_injective_of_injective (R := k) W.toSubmodule.injective_subtype
  refine ⟨W, ?_⟩
  have : Nontrivial (Subrepresentation W.toRepresentation) :=
    ⟨⊥, ⊤, fun h => bot_ne_top (α := Submodule k W.toSubmodule)
      (congrArg Subrepresentation.toSubmodule h)⟩
  refine ⟨fun σ => ?_⟩
  have hle : (mapSub W σ).toSubmodule ≤ W.toSubmodule := Submodule.map_subtype_le _ _
  by_cases h0 : mapSub W σ = ⊥
  · left
    apply Subrepresentation.toSubmodule_injective
    apply hinj
    have h1 : (mapSub W σ).toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule h0
    show _ = Submodule.map W.toSubmodule.subtype ⊥
    rw [Submodule.map_bot]
    exact h1
  · right
    have hfr := hmin (mapSub W σ) h0
    have heq : (mapSub W σ).toSubmodule = W.toSubmodule :=
      Submodule.eq_of_le_of_finrank_le hle (not_lt.1 hfr)
    apply Subrepresentation.toSubmodule_injective
    apply hinj
    show _ = Submodule.map W.toSubmodule.subtype ⊤
    rw [Submodule.map_subtype_top]
    exact heq

/-- Module version of Problem 1.20: a nonzero module over a `k`-algebra `A` which is finite-dimensional
over `k` has a simple submodule. -/
@[kb "etingof2011" "Problem 1.20, p. 10"]
theorem exists_isSimpleModule_submodule (A M : Type*) [Ring A] [Algebra k A] [AddCommGroup M]
    [Module A M] [Module k M] [IsScalarTower k A M] [FiniteDimensional k M] [Nontrivial M] :
    ∃ N : Submodule A M, IsSimpleModule A N := by
  have : IsArtinian A M := isArtinian_of_tower k inferInstance
  rcases IsAtomic.eq_bot_or_exists_atom_le (⊤ : Submodule A M) with h | ⟨N, hN, -⟩
  · exact absurd h top_ne_bot
  · exact ⟨N, isSimpleModule_iff_isAtom.2 hN⟩

/-- **Etingof et al., Definition 1.15** (in the form used here): a representation is indecomposable
if it is nonzero and cannot be written as an internal direct sum of two nonzero subrepresentations,
i.e. whenever two subrepresentations are complements of each other, one of them is zero. -/
def IsIndecomposable (ρ : Representation k G V) : Prop :=
  Nontrivial V ∧ ∀ W₁ W₂ : Subrepresentation ρ, IsCompl W₁ W₂ → W₁ = ⊥ ∨ W₂ = ⊥

/-- An irreducible representation is indecomposable (Definition 1.15). -/
@[kb "etingof2011" "Definition 1.15, p. 8"]
theorem IsIndecomposable.of_isIrreducible (ρ : Representation k G V) [IsIrreducible ρ] :
    IsIndecomposable ρ := by
  refine ⟨?_, ?_⟩
  · by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    obtain ⟨a, b, hab⟩ := exists_pair_ne (Subrepresentation ρ)
    exact hab (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
  · intro W₁ W₂ h
    rcases eq_bot_or_eq_top W₁ with h1 | h1
    · exact Or.inl h1
    · right
      have := h.disjoint
      rwa [h1, top_disjoint] at this

end Irreducible

section Maschke

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- Over a field whose characteristic does not divide the order of the finite group `G`, an
indecomposable representation is irreducible (Maschke's theorem; Definition 1.15 and §3.2). -/
@[kb "etingof2011" "Definition 1.15, p. 8"]
theorem IsIndecomposable.isIrreducible [Finite G] (hG : (Nat.card G : k) ≠ 0)
    {ρ : Representation k G V} (h : IsIndecomposable ρ) : IsIrreducible ρ := by
  have : NeZero (Nat.card G : k) := ⟨hG⟩
  obtain ⟨hnt, hind⟩ := h
  have : Nontrivial (Subrepresentation ρ) :=
    ⟨⊥, ⊤, fun h => bot_ne_top (α := Submodule k V) (congrArg Subrepresentation.toSubmodule h)⟩
  refine ⟨fun σ => ?_⟩
  obtain ⟨q, hq⟩ := MonoidAlgebra.Submodule.exists_isCompl (k := k) (G := G)
    (V := ρ.asModule) (Subrepresentation.asSubmodule σ)
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  have hq' : IsCompl (e σ) (e (e.symm q)) := by
    rw [OrderIso.apply_symm_apply]
    exact hq
  have hc : IsCompl σ (e.symm q) := e.isCompl_iff.2 hq'
  rcases hind σ _ hc with h | h
  · exact Or.inl h
  · right
    have := hc.codisjoint
    rwa [h, codisjoint_bot] at this

end Maschke

section Faithful

variable {k G V : Type*} [Semiring k] [Monoid G] [AddCommMonoid V] [Module k V]

/-- A representation is faithful if the homomorphism `G → End V` is injective (§1.7). -/
def IsFaithful (ρ : Representation k G V) : Prop := Function.Injective ρ

/-- The left regular representation of a group on `k[G]` is faithful (§1.7), when `k` is nontrivial. -/
@[kb "etingof2011" "§1.7, p. 12"]
theorem isFaithful_ofMulAction_self [Nontrivial k] : IsFaithful (Representation.ofMulAction k G G) := by
  intro g h hgh
  have := LinearMap.congr_fun hgh (MonoidAlgebra.single 1 1)
  simp only [Representation.ofMulAction_single, smul_eq_mul, mul_one] at this
  exact (MonoidAlgebra.single_left_inj one_ne_zero).1 this

end Faithful

end UndergradKB.RepresentationTheory
