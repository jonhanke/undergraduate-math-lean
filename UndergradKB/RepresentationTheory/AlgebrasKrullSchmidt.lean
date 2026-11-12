import Mathlib.RingTheory.Length
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Logic.Equiv.Option
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Artinian.Module
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.JordanHolderFitting

/-! # The Krull-Schmidt theorem (Etingof et al., Theorem 2.19)

A module of finite length (Noetherian and Artinian, e.g. a finite-dimensional representation) is isomorphic to a
finite product of indecomposable modules, and the factors are unique up to isomorphism and permutation.

Existence is an induction on the length.  Uniqueness is the exchange argument: if `Π Nᵢ ≅ Π N'ⱼ` with all factors
indecomposable, Fitting's lemma applied to the endomorphism ring of `N_{i₀}` produces an index `j₀` with
`N_{i₀} ≅ N'_{j₀}` such that the images of `N_{i₀}` and the kernel of the projection to `N'_{j₀}` are complementary;
comparing complements gives `Π_{i ≠ i₀} Nᵢ ≅ Π_{j ≠ j₀} N'ⱼ`, and one inducts on the number of factors.
-/

universe u v w

namespace UndergradKB.RepresentationTheory

open Module

section Complements

variable {R : Type u} [Ring R]

/-- If `π ∘ φ` is bijective, then the range of `φ` and the kernel of `π` are complementary submodules. -/
theorem isCompl_range_ker_of_bijective_comp {Q M N : Type*} [AddCommGroup Q] [Module R Q] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (φ : Q →ₗ[R] M) (π : M →ₗ[R] N)
    (h : Function.Bijective (π ∘ₗ φ)) : IsCompl (LinearMap.range φ) (LinearMap.ker π) := by
  constructor
  · rw [disjoint_iff, Submodule.eq_bot_iff]
    rintro y ⟨⟨x, rfl⟩, hy⟩
    have hx : x = 0 := h.1 (by simpa using hy)
    simp [hx]
  · rw [codisjoint_iff, eq_top_iff]
    intro y _
    obtain ⟨x, hx⟩ := h.2 (π y)
    rw [Submodule.mem_sup]
    refine ⟨φ x, ⟨x, rfl⟩, y - φ x, ?_, by abel⟩
    rw [LinearMap.mem_ker, map_sub]
    have : π (φ x) = π y := hx
    rw [this, sub_self]

/-- If `b ∘ a` is bijective and `Y` is indecomposable, with `X` nonzero, then both `a : X → Y` and `b : Y → X`
are bijective. -/
theorem bijective_of_bijective_comp_of_indecomposable {X Y : Type*} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] [Nontrivial X] (hY : IsIndecomposableModule R Y) (a : X →ₗ[R] Y)
    (b : Y →ₗ[R] X) (h : Function.Bijective (b ∘ₗ a)) : Function.Bijective a ∧ Function.Bijective b := by
  have hc := isCompl_range_ker_of_bijective_comp a b h
  rcases hY.2 _ _ hc with h0 | h0
  · exfalso
    obtain ⟨x, hx⟩ := exists_ne (0 : X)
    have ha : a x = 0 := by
      have : a x ∈ LinearMap.range a := ⟨x, rfl⟩
      rw [h0] at this
      exact this
    exact hx (h.1 (by simp [ha]))
  · have hbi : Function.Injective b := LinearMap.ker_eq_bot.1 h0
    have hbs : Function.Surjective b := fun x => by
      obtain ⟨x', hx'⟩ := h.2 x
      exact ⟨a x', hx'⟩
    refine ⟨⟨(show Function.Injective (b ∘ a) from h.1).of_comp, fun y => ?_⟩, ⟨hbi, hbs⟩⟩
    obtain ⟨x', hx'⟩ := h.2 (b y)
    exact ⟨x', hbi hx'⟩

end Complements

section Exchange

variable {R : Type u} [Ring R]

/-- A kernel of a coordinate projection of a product is the product of the other factors. -/
def kerProjEquiv {κ : Type*} [DecidableEq κ] {N : κ → Type*} [∀ j, AddCommGroup (N j)]
    [∀ j, Module R (N j)] (j0 : κ) :
    LinearMap.ker (LinearMap.proj j0 : (Π j, N j) →ₗ[R] N j0) ≃ₗ[R] Π j : {j // j ≠ j0}, N j where
  toFun x := fun j => x.1 j.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun z := ⟨fun j => if h : j = j0 then 0 else z ⟨j, h⟩, by
    rw [LinearMap.mem_ker]
    simp⟩
  left_inv x := by
    apply Subtype.ext
    funext j
    by_cases h : j = j0
    · subst h
      have := LinearMap.mem_ker.1 x.2
      simp only [LinearMap.proj_apply] at this
      simp [this]
    · simp [h]
  right_inv z := by
    funext j
    simp [j.2]

/-- Fitting's lemma gives a summand: if `ψ ∘ φ = id` for `φ : X → Π Yⱼ` with `X` indecomposable of finite length,
then for some `j` the endomorphism `ψ ∘ single j ∘ proj j ∘ φ` of `X` is a unit. -/
theorem exists_isUnit_of_split {X : Type*} [AddCommGroup X] [Module R X] [IsNoetherian R X]
    [IsArtinian R X] (hX : IsIndecomposableModule R X) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Y : ι → Type*} [∀ j, AddCommGroup (Y j)] [∀ j, Module R (Y j)] (φ : X →ₗ[R] Π j, Y j)
    (ψ : (Π j, Y j) →ₗ[R] X) (h : ψ ∘ₗ φ = LinearMap.id) :
    ∃ j, IsUnit ((ψ ∘ₗ LinearMap.single R Y j) ∘ₗ (LinearMap.proj j ∘ₗ φ) : Module.End R X) := by
  by_contra hcon
  push Not at hcon
  have hnil : ∀ j, IsNilpotent ((ψ ∘ₗ LinearMap.single R Y j) ∘ₗ (LinearMap.proj j ∘ₗ φ) : Module.End R X) :=
    fun j => (isUnit_or_isNilpotent_of_indecomposable hX _).resolve_left (hcon j)
  have hsum := Finset.sum_induction (s := Finset.univ) _ (fun f : Module.End R X => IsNilpotent f)
    (fun a b ha hb => isNilpotent_add_of_indecomposable hX ha hb) IsNilpotent.zero
    (fun j _ => hnil j)
  have hone : ∑ j, ((ψ ∘ₗ LinearMap.single R Y j) ∘ₗ (LinearMap.proj j ∘ₗ φ) : Module.End R X) = 1 := by
    ext x
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, one_apply_eq_self]
    rw [← map_sum]
    have : ∑ j, LinearMap.single R Y j (φ x j) = φ x := by
      funext i
      simp [Finset.sum_apply]
    rw [this]
    exact LinearMap.congr_fun h x
  rw [hone] at hsum
  have := hX.1
  obtain ⟨n, hn⟩ := hsum
  rw [one_pow] at hn
  exact one_ne_zero hn

/-- The exchange step of the Krull-Schmidt theorem: if `Π Nᵢ ≅ Π N'ⱼ` with all factors indecomposable and `N_{i₀}`
of finite length, then some `N'_{j₀}` is isomorphic to `N_{i₀}` and the remaining products are isomorphic. -/
theorem exists_exchange {ι : Type*} {κ : Type*} [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {N : ι → Type*} {N' : κ → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    [∀ j, AddCommGroup (N' j)] [∀ j, Module R (N' j)] (i0 : ι) [IsNoetherian R (N i0)]
    [IsArtinian R (N i0)] (hX : IsIndecomposableModule R (N i0)) (hY : ∀ j, IsIndecomposableModule R (N' j))
    (e : (Π i, N i) ≃ₗ[R] Π j, N' j) :
    ∃ j0, Nonempty (N i0 ≃ₗ[R] N' j0) ∧
      Nonempty ((Π i : {i // i ≠ i0}, N i) ≃ₗ[R] Π j : {j // j ≠ j0}, N' j) := by
  let φ : N i0 →ₗ[R] Π j, N' j := e.toLinearMap ∘ₗ LinearMap.single R N i0
  let ψ : (Π j, N' j) →ₗ[R] N i0 := LinearMap.proj i0 ∘ₗ e.symm.toLinearMap
  have hψφ : ψ ∘ₗ φ = LinearMap.id := by
    ext x
    simp [ψ, φ]
  obtain ⟨j0, hu⟩ := exists_isUnit_of_split hX φ ψ hψφ
  have hbij : Function.Bijective ((ψ ∘ₗ LinearMap.single R N' j0) ∘ₗ (LinearMap.proj j0 ∘ₗ φ)) :=
    (Module.End.isUnit_iff _).1 hu
  have : Nontrivial (N i0) := hX.1
  obtain ⟨ha, -⟩ := bijective_of_bijective_comp_of_indecomposable (hY j0) (LinearMap.proj j0 ∘ₗ φ)
    (ψ ∘ₗ LinearMap.single R N' j0) hbij
  refine ⟨j0, ⟨LinearEquiv.ofBijective _ ha⟩, ⟨?_⟩⟩
  let K : Submodule R (Π i, N i) := LinearMap.ker (LinearMap.proj i0 : (Π i, N i) →ₗ[R] N i0)
  have hid : (LinearMap.proj i0 ∘ₗ LinearMap.single R N i0 : N i0 →ₗ[R] N i0) = LinearMap.id := by
    ext x
    simp
  have h1 : IsCompl (LinearMap.range (LinearMap.single R N i0)) K :=
    isCompl_range_ker_of_bijective_comp _ _ (by rw [hid]; exact Function.bijective_id)
  have h1' := Submodule.isCompl_map e h1
  have h2 := isCompl_range_ker_of_bijective_comp φ (LinearMap.proj j0) ha
  have hrange : LinearMap.range φ = (LinearMap.range (LinearMap.single R N i0)).map e.toLinearMap :=
    LinearMap.range_comp _ _
  rw [hrange] at h2
  let eC : (K.map e.toLinearMap) ≃ₗ[R] LinearMap.ker (LinearMap.proj j0 : (Π j, N' j) →ₗ[R] N' j0) :=
    ((Submodule.quotientEquivOfIsCompl _ _ h1').symm).trans (Submodule.quotientEquivOfIsCompl _ _ h2)
  exact (kerProjEquiv i0).symm.trans ((LinearEquiv.submoduleMap e K).trans (eC.trans (kerProjEquiv j0)))

end Exchange

section Uniqueness

variable {R : Type u} [Ring R]

/-- **Etingof et al., Theorem 2.19 (uniqueness)**: if a module is isomorphic to a finite product of indecomposable
modules of finite length in two ways, then there is a bijection of the index sets matching the factors up to
isomorphism. -/
@[kb "etingof2011" "Theorem 2.19, p. 29"]
theorem krullSchmidt_unique : ∀ (n : ℕ) {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] {N : ι → Type*} {N' : κ → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    [∀ j, AddCommGroup (N' j)] [∀ j, Module R (N' j)] [∀ i, IsNoetherian R (N i)] [∀ i, IsArtinian R (N i)],
    Fintype.card ι = n → (∀ i, IsIndecomposableModule R (N i)) → (∀ j, IsIndecomposableModule R (N' j)) →
    ((Π i, N i) ≃ₗ[R] Π j, N' j) → ∃ σ : ι ≃ κ, ∀ i, Nonempty (N i ≃ₗ[R] N' (σ i)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ι κ _ _ _ _ N N' _ _ _ _ _ _ hn hN hN' e
    by_cases hι : IsEmpty ι
    · have hκ : IsEmpty κ := by
        refine ⟨fun j => ?_⟩
        have : Nontrivial (N' j) := (hN' j).1
        obtain ⟨y, hy⟩ := exists_ne (0 : N' j)
        have hsub : Subsingleton (Π j, N' j) := e.symm.injective.subsingleton
        exact hy (by simpa using congrFun (Subsingleton.elim (Pi.single j y : Π j, N' j) 0) j)
      exact ⟨Equiv.equivOfIsEmpty ι κ, fun i => (hι.false i).elim⟩
    · obtain ⟨i0⟩ := not_isEmpty_iff.1 hι
      obtain ⟨j0, ⟨e0⟩, ⟨F⟩⟩ := exists_exchange i0 (hN i0) hN' e
      have hlt : Fintype.card {i // i ≠ i0} < n :=
        hn ▸ Fintype.card_subtype_lt (p := fun i => i ≠ i0) (x := i0) (by simp)
      obtain ⟨σ', hσ'⟩ := ih _ hlt rfl (fun i => hN i.1) (fun j => hN' j.1) F
      let σ : ι ≃ κ := (Equiv.optionSubtypeNe i0).symm.trans
        ((Equiv.optionCongr σ').trans (Equiv.optionSubtypeNe j0))
      have h0 : σ i0 = j0 := by simp [σ]
      have h1 : ∀ (i : ι) (h : i ≠ i0), σ i = (σ' ⟨i, h⟩).1 := by
        intro i h
        simp [σ, h]
      refine ⟨σ, fun i => ?_⟩
      by_cases h : i = i0
      · rw [h, h0]
        exact ⟨e0⟩
      · rw [h1 i h]
        exact hσ' ⟨i, h⟩

end Uniqueness

section Existence

variable {R : Type u} [Ring R]

private theorem exists_decomposition_aux : ∀ (n : ℕ) (M : Type v) [AddCommGroup M] [Module R M]
    [IsNoetherian R M] [IsArtinian R M], Module.length R M = n →
    ∃ (ι : Type) (_ : Fintype ι) (N : ι → Type v) (_ : ∀ i, AddCommGroup (N i)) (_ : ∀ i, Module R (N i)),
      (∀ i, IsIndecomposableModule R (N i)) ∧ Nonempty (M ≃ₗ[R] Π i, N i) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro M _ _ _ _ hn
    by_cases hM : Subsingleton M
    · exact ⟨Fin 0, inferInstance, fun _ => M, fun _ => inferInstance, fun _ => inferInstance,
        fun i => i.elim0, ⟨LinearEquiv.ofSubsingleton _ _⟩⟩
    · have hnt : Nontrivial M := not_subsingleton_iff_nontrivial.1 hM
      by_cases hind : IsIndecomposableModule R M
      · exact ⟨Unit, inferInstance, fun _ => M, fun _ => inferInstance, fun _ => inferInstance,
          fun _ => hind, ⟨(LinearEquiv.piUnique R (fun _ : Unit => M)).symm⟩⟩
      · obtain ⟨p, q, hpq, hp, hq⟩ : ∃ p q : Submodule R M, IsCompl p q ∧ p ≠ ⊥ ∧ q ≠ ⊥ := by
          by_contra hcon
          apply hind
          refine ⟨hnt, fun p q hpq => ?_⟩
          by_contra h
          push Not at h
          exact hcon ⟨p, q, hpq, h.1, h.2⟩
        let e : (p × q) ≃ₗ[R] M := Submodule.prodEquivOfIsCompl p q hpq
        have hlen : Module.length R M = Module.length R p + Module.length R q := by
          rw [← e.length_eq, Module.length_prod]
        have hpne : Nontrivial p := Submodule.nontrivial_iff_ne_bot.2 hp
        have hqne : Nontrivial q := Submodule.nontrivial_iff_ne_bot.2 hq
        obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 (Module.length_ne_top (R := R) (M := p))
        obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.1 (Module.length_ne_top (R := R) (M := q))
        have hapos : 0 < a := by
          have := Module.length_pos (R := R) (M := p)
          rw [← ha] at this
          exact_mod_cast this
        have hbpos : 0 < b := by
          have := Module.length_pos (R := R) (M := q)
          rw [← hb] at this
          exact_mod_cast this
        have hab : a + b = n := by
          have h : ((a + b : ℕ) : ℕ∞) = (n : ℕ∞) := by rw [Nat.cast_add, ha, hb, ← hlen, hn]
          exact_mod_cast h
        obtain ⟨ι1, f1, N1, A1, M1, h1, ⟨e1⟩⟩ := ih a (by omega) p ha.symm
        obtain ⟨ι2, f2, N2, A2, M2, h2, ⟨e2⟩⟩ := ih b (by omega) q hb.symm
        let iA : ∀ i, AddCommGroup (Sum.elim N1 N2 i) := fun i =>
          Sum.rec (motive := fun i => AddCommGroup (Sum.elim N1 N2 i)) (fun a => A1 a)
            (fun b => A2 b) i
        let iM : ∀ i, Module R (Sum.elim N1 N2 i) := fun i =>
          Sum.rec (motive := fun i => Module R (Sum.elim N1 N2 i)) (fun a => M1 a)
            (fun b => M2 b) i
        refine ⟨ι1 ⊕ ι2, inferInstance, Sum.elim N1 N2, iA, iM, ?_, ⟨?_⟩⟩
        · rintro (i | i)
          · exact h1 i
          · exact h2 i
        · exact e.symm.trans ((e1.prodCongr e2).trans (LinearEquiv.sumPiEquivProdPi R ι1 ι2 (Sum.elim N1 N2)).symm)

/-- **Etingof et al., Theorem 2.19 (existence)**: a module of finite length is isomorphic to a finite product of
indecomposable modules. -/
@[kb "etingof2011" "Theorem 2.19, p. 29"]
theorem exists_indecomposable_decomposition (M : Type v) [AddCommGroup M] [Module R M] [IsNoetherian R M]
    [IsArtinian R M] :
    ∃ (ι : Type) (_ : Fintype ι) (N : ι → Type v) (_ : ∀ i, AddCommGroup (N i)) (_ : ∀ i, Module R (N i)),
      (∀ i, IsIndecomposableModule R (N i)) ∧ Nonempty (M ≃ₗ[R] Π i, N i) := by
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 (Module.length_ne_top (R := R) (M := M))
  exact exists_decomposition_aux a M ha.symm

/-- **Etingof et al., Theorem 2.19 (uniqueness, unquantified form)**: two decompositions of a module into finite
products of indecomposable modules of finite length agree up to a bijection of the index sets and isomorphisms of
the factors. -/
@[kb "etingof2011" "Theorem 2.19, p. 29"]
theorem krullSchmidt_unique' {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ] {N : ι → Type*}
    {N' : κ → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)] [∀ j, AddCommGroup (N' j)]
    [∀ j, Module R (N' j)] [∀ i, IsNoetherian R (N i)] [∀ i, IsArtinian R (N i)]
    (hN : ∀ i, IsIndecomposableModule R (N i)) (hN' : ∀ j, IsIndecomposableModule R (N' j))
    (e : (Π i, N i) ≃ₗ[R] Π j, N' j) : ∃ σ : ι ≃ κ, ∀ i, Nonempty (N i ≃ₗ[R] N' (σ i)) := by
  classical
  exact krullSchmidt_unique _ rfl hN hN' e

/-- **Etingof et al., Theorem 2.19 (existence, finite-dimensional representations)**: a finite-dimensional
representation of an algebra `A` over a field `k` is a finite product of indecomposable representations. -/
@[kb "etingof2011" "Theorem 2.19, p. 29"]
theorem exists_indecomposable_decomposition_of_finiteDimensional {k A : Type*} [Field k] [Ring A]
    [Algebra k A] (V : Type v) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [FiniteDimensional k V] :
    ∃ (ι : Type) (_ : Fintype ι) (N : ι → Type v) (_ : ∀ i, AddCommGroup (N i)) (_ : ∀ i, Module A (N i)),
      (∀ i, IsIndecomposableModule A (N i)) ∧ Nonempty (V ≃ₗ[A] Π i, N i) := by
  have : IsNoetherian A V := isNoetherian_of_tower k inferInstance
  have : IsArtinian A V := isArtinian_of_tower k inferInstance
  exact exists_indecomposable_decomposition V

end Existence

end UndergradKB.RepresentationTheory
