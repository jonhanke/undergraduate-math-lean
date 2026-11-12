import Mathlib.Order.JordanHolder
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Nilpotent.Basic
import UndergradKB.Common.Attr

/-! # Jordan-Holder and Fitting's lemma for modules (Etingof et al., Theorem 2.18, Lemma 2.20)

* Two filtrations of a module by submodules with simple successive quotients, running from `0` to the
  whole module, have the same length, and their successive quotients agree up to a permutation
  and isomorphism.  This is Mathlib's Jordan-Holder theorem for the (modular) lattice of submodules,
  translated to the "simple quotient" formulation.
* An endomorphism of a Noetherian indecomposable module is a unit or nilpotent, and a sum of two
  nilpotent endomorphisms of such a module is nilpotent.
-/

universe u v

namespace UndergradKB.RepresentationTheory

open Module

section JordanHolder

variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]

/-- A filtration `0 = F 0 ⊆ F 1 ⊆ ... ⊆ F n = M` of `M` by submodules whose successive quotients
`F (i+1) / F i` are simple modules. -/
structure SimpleFiltration (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M] where
  /-- the number of steps -/
  length : ℕ
  /-- the submodules in the chain -/
  toFun : Fin (length + 1) → Submodule R M
  head_eq : toFun 0 = ⊥
  last_eq : toFun (Fin.last length) = ⊤
  le_succ : ∀ i : Fin length, toFun i.castSucc ≤ toFun i.succ
  simple : ∀ i : Fin length, IsSimpleModule R (toFun i.succ ⧸ (toFun i.castSucc).comap (toFun i.succ).subtype)

namespace SimpleFiltration

/-- The `i`-th successive quotient of a simple filtration. -/
abbrev quotient (F : SimpleFiltration R M) (i : Fin F.length) : Type v :=
  F.toFun i.succ ⧸ (F.toFun i.castSucc).comap (F.toFun i.succ).subtype

/-- A simple filtration is a composition series of the lattice of submodules. -/
def toCompositionSeries (F : SimpleFiltration R M) : CompositionSeries (Submodule R M) where
  length := F.length
  toFun := F.toFun
  step i := (covBy_iff_quot_is_simple (F.le_succ i)).2 (F.simple i)

@[simp] lemma toCompositionSeries_length (F : SimpleFiltration R M) :
    F.toCompositionSeries.length = F.length := rfl

lemma toCompositionSeries_head (F : SimpleFiltration R M) : F.toCompositionSeries.head = ⊥ :=
  F.head_eq

lemma toCompositionSeries_last (F : SimpleFiltration R M) : F.toCompositionSeries.last = ⊤ :=
  F.last_eq

end SimpleFiltration

/-- **Jordan-Holder.**  Any two filtrations of `M` with simple successive quotients have the same
length, and there is a bijection between their steps matching the successive quotients up to
isomorphism. -/
@[kb "etingof2011" "Theorem 2.18, p. 28"]
theorem SimpleFiltration.jordan_holder (F G : SimpleFiltration R M) :
    F.length = G.length ∧
      ∃ σ : Fin F.length ≃ Fin G.length, ∀ i, Nonempty (F.quotient i ≃ₗ[R] G.quotient (σ i)) := by
  have hE := CompositionSeries.jordan_holder F.toCompositionSeries G.toCompositionSeries
    (F.toCompositionSeries_head.trans G.toCompositionSeries_head.symm)
    (F.toCompositionSeries_last.trans G.toCompositionSeries_last.symm)
  refine ⟨hE.length_eq, ?_⟩
  obtain ⟨σ, hσ⟩ := hE
  exact ⟨σ, fun i => ⟨(JordanHolderLattice.Iso.linearEquiv (hσ i))⟩⟩

/-- The common length of simple filtrations is the length of the module. -/
theorem SimpleFiltration.length_eq_moduleLength (F : SimpleFiltration R M) :
    (F.length : ℕ∞) = Module.length R M := by
  have := Module.length_compositionSeries F.toCompositionSeries F.toCompositionSeries_head
    F.toCompositionSeries_last
  rw [← this]
  rfl

end JordanHolder

section Fitting

variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]

/-- A module is indecomposable if it is nonzero and is not the internal direct sum of two nonzero
submodules. -/
def IsIndecomposableModule (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M] : Prop :=
  Nontrivial M ∧ ∀ p q : Submodule R M, IsCompl p q → p = ⊥ ∨ q = ⊥

/-- **Fitting's lemma.**  Every endomorphism of an indecomposable Noetherian module is invertible or
nilpotent. -/
@[kb "etingof2011" "Lemma 2.20, p. 29"]
theorem isUnit_or_isNilpotent_of_indecomposable [IsNoetherian R M] [IsArtinian R M]
    (hM : IsIndecomposableModule R M) (f : Module.End R M) : IsUnit f ∨ IsNilpotent f := by
  obtain ⟨n, hn⟩ := (Filter.eventually_atTop.1 f.eventually_isCompl_ker_pow_range_pow)
  have h := hn (n + 1) (Nat.le_succ n)
  rcases hM.2 _ _ h with h0 | h0
  · left
    have hsurj : LinearMap.range (f ^ (n + 1)) = ⊤ := by
      have h2 := h.2
      rw [h0] at h2
      exact codisjoint_bot.1 h2.symm
    rw [Module.End.isUnit_iff]
    constructor
    · intro x y hxy
      have hx : x - y ∈ LinearMap.ker (f ^ (n + 1)) := by
        rw [LinearMap.mem_ker, pow_succ, mul_apply_eq_comp, map_sub, hxy, sub_self,
          map_zero]
      rw [h0, Submodule.mem_bot] at hx
      exact sub_eq_zero.1 hx
    · intro y
      have hy : y ∈ LinearMap.range (f ^ (n + 1)) := by rw [hsurj]; trivial
      obtain ⟨x, hx⟩ := hy
      refine ⟨(f ^ n) x, ?_⟩
      rw [← hx, pow_succ', mul_apply_eq_comp]
  · right
    exact ⟨n + 1, LinearMap.range_eq_bot.1 h0⟩

/-- Sums of nilpotent endomorphisms of an indecomposable Noetherian module are nilpotent. -/
@[kb "etingof2011" "Lemma 2.20, p. 29"]
theorem isNilpotent_add_of_indecomposable [IsNoetherian R M] [IsArtinian R M]
    (hM : IsIndecomposableModule R M) {f g : Module.End R M}
    (hf : IsNilpotent f) (hg : IsNilpotent g) : IsNilpotent (f + g) := by
  have := hM.1
  have : Nontrivial (Module.End R M) := inferInstance
  by_contra hfg
  obtain ⟨u, hu⟩ := (isUnit_or_isNilpotent_of_indecomposable hM (f + g)).resolve_right hfg
  -- `a = u⁻¹ f` and `b = u⁻¹ g` sum to `1`
  set a : Module.End R M := ↑u⁻¹ * f with ha
  set b : Module.End R M := ↑u⁻¹ * g with hb
  have hab : a + b = 1 := by
    rw [ha, hb, ← mul_add, ← hu, Units.inv_mul]
  have hnu : ∀ x : Module.End R M, IsNilpotent x → ¬ IsUnit (↑u⁻¹ * x) := by
    intro x hx hux
    have : IsUnit x := by
      have := (u.isUnit.mul hux)
      simpa [← mul_assoc] using this
    exact this.not_isNilpotent hx
  have ha' : IsNilpotent a :=
    (isUnit_or_isNilpotent_of_indecomposable hM a).resolve_left (hnu f hf)
  have hb1 : b = 1 - a := by rw [← hab]; abel
  have hbu : IsUnit b := by rw [hb1]; exact ha'.isUnit_one_sub
  exact hnu g hg hbu

end Fitting

end UndergradKB.RepresentationTheory
