import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.DoubleCentralizer
import UndergradKB.RepresentationTheory.TensorProductAlgebras

/-! # Isotypic decomposition of semisimple modules (Etingof et al., Definition 2.1 example, Theorems 4.54, 2.26)

Over an algebraically closed field `k`, a finite-dimensional semisimple module `V` over a `k`-algebra `A` is
isomorphic, as an `A`-module, to `⨁ᵢ Xᵢ ⊗ Hom_A(Xᵢ, V)`, where `(Xᵢ)` is any finite family of pairwise
non-isomorphic finite-dimensional simple modules containing every simple summand of `V`, and `A` acts on the
factors `Xᵢ` (`isotypicDecomposition`).  The factor order is `Xᵢ ⊗ Hom_A(Xᵢ, V)` so that Mathlib's left-factor
module structure on a tensor product gives the `A`-action.

Consequences: part (c) of the double centralizer theorem (the commutant acts on `Hom_A(Xᵢ, E)` by
post-composition, these modules are simple, and the decomposition is compatible with the commutant), and
part (ii) of Theorem 2.26: every finite-dimensional simple `A ⊗ B`-module is `V ⊗ W` with `V`, `W` simple
(`exists_linearEquiv_tensor_of_isSimpleModule`), and `V`, `W` are unique up to isomorphism
(`linearEquiv_of_tensor_linearEquiv`).
-/

namespace UndergradKB.RepresentationTheory
open scoped TensorProduct

section Eval
variable (k : Type*) {A : Type*} [Field k] [Ring A] [Algebra k A]
  (X V : Type*) [AddCommGroup X] [Module k X] [Module A X] [IsScalarTower k A X]
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]

/-- The evaluation map `X ⊗ Hom_A(X, V) → V`, `x ⊗ f ↦ f x`; it is `A`-linear for the action on `X`. -/
noncomputable def evalHom : X ⊗[k] (X →ₗ[A] V) →ₗ[A] V :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun x =>
        { toFun := fun f => f x
          map_add' := fun f g => by simp
          map_smul' := fun c f => by simp }
      map_add' := fun x y => by ext f; simp
      map_smul' := fun a x => by ext f; simp }

variable {k X V} in
@[simp] theorem evalHom_tmul (x : X) (f : X →ₗ[A] V) : evalHom k X V (x ⊗ₜ[k] f) = f x := by
  simp [evalHom]

end Eval

section Key
variable {k : Type*} {A : Type*} [Field k] [Ring A] [Algebra k A]
  {X V : Type*} [AddCommGroup X] [Module k X] [Module A X] [IsScalarTower k A X]
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]

/-- Every element of `X ⊗ H` has the form `∑ xᵢ ⊗ bᵢ` for a given finite basis `b` of `H`. -/
theorem exists_eq_sum_tmul_basis {H : Type*} [AddCommGroup H] [Module k H] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι k H) (x : X ⊗[k] H) : ∃ y : ι → X, x = ∑ i, y i ⊗ₜ[k] b i := by
  induction x using TensorProduct.inductionOn with
  | tmul v w =>
    refine ⟨fun i => b.repr w i • v, ?_⟩
    conv_lhs => rw [← b.sum_repr w]
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  | add x y hx hy =>
    obtain ⟨w1, rfl⟩ := hx
    obtain ⟨w2, rfl⟩ := hy
    exact ⟨w1 + w2, by simp [TensorProduct.add_tmul, Finset.sum_add_distrib]⟩

variable (k) in
/-- Schur's lemma over an algebraically closed field. -/
theorem exists_end_eq_smul [IsAlgClosed k] [IsSimpleModule A X] [FiniteDimensional k X]
    (φ : X →ₗ[A] X) : ∃ c : k, ∀ x, φ x = c • x := by
  obtain ⟨c, hc⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := A) (V := X) k).2 φ
  exact ⟨c, fun x => by rw [← hc, Module.algebraMap_end_apply]⟩

/-- For a nonzero map `f` from a simple module into a semisimple module there is `g` with `g ∘ f ≠ 0`. -/
theorem exists_comp_ne_zero [IsSimpleModule A X] [IsSemisimpleModule A V] (f : X →ₗ[A] V)
    (hf : f ≠ 0) : ∃ g : V →ₗ[A] X, g ∘ₗ f ≠ 0 := by
  obtain ⟨g, hg⟩ := IsSemisimpleModule.extension_property f (LinearMap.injective_of_ne_zero hf)
    (LinearMap.id : X →ₗ[A] X)
  refine ⟨g, ?_⟩
  rw [hg]
  have := IsSimpleModule.nontrivial A X
  intro h
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  exact hx (by simpa using congr($h x))

end Key

section Injective
variable (k : Type*) {A : Type*} [Field k] [Ring A] [Algebra k A] [IsAlgClosed k]
  {X V : Type*} [AddCommGroup X] [Module k X] [Module A X] [IsScalarTower k A X]
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [IsSimpleModule A X] [FiniteDimensional k X] [IsSemisimpleModule A V]

/-- Key independence step: if `b` is a `k`-basis of `Hom_A(X, V)` for a simple `X` and a combination
`∑ yᵢ ⊗ bᵢ` is killed by every `A`-linear map `V → X` after evaluation, then all `yᵢ` vanish. -/
theorem eq_zero_of_forall_comp_evalHom {ι : Type*} [Fintype ι] (b : Module.Basis ι k (X →ₗ[A] V))
    (y : ι → X)
    (h : ∀ g : V →ₗ[A] X, g (evalHom k X V (∑ i, y i ⊗ₜ[k] b i)) = 0) : ∀ i, y i = 0 := by
  classical
  let e := LinearEquiv.ofBijective (Algebra.linearMap k (Module.End A X))
    (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := A) (V := X) k)
  have he : ∀ (φ : X →ₗ[A] X) (x : X), φ x = e.symm φ • x := by
    intro φ x
    calc φ x = e (e.symm φ) x := by rw [e.apply_symm_apply]
      _ = e.symm φ • x := Module.algebraMap_end_apply (R := k) (S := A) (M := X) (a := e.symm φ) (m := x)
  let Θ : (V →ₗ[A] X) → (X →ₗ[A] V) →ₗ[k] k := fun g =>
    e.symm.toLinearMap ∘ₗ
      { toFun := fun f => g ∘ₗ f
        map_add' := fun f f' => LinearMap.comp_add _ _ _
        map_smul' := fun c f => by ext x; simp }
  have hΘ : ∀ g f, Θ g f = e.symm (g ∘ₗ f) := fun g f => rfl
  let Ψ : (V →ₗ[A] X) →ₗ[k] (ι → k) :=
    { toFun := fun g l => Θ g (b l)
      map_add' := fun g g' => by
        ext l; simp [hΘ, LinearMap.add_comp]
      map_smul' := fun c g => by
        ext l; simp [hΘ, LinearMap.smul_comp] }
  have hrange : LinearMap.range Ψ = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne)
      inferInstance
    have hφΨ : ∀ g, φ (Ψ g) = 0 := by
      intro g
      have : φ (Ψ g) ∈ (LinearMap.range Ψ).map φ := ⟨Ψ g, ⟨g, rfl⟩, rfl⟩
      rw [hφ] at this
      simpa using this
    let a : ι → k := fun l => φ (fun j => if l = j then 1 else 0)
    let f : X →ₗ[A] V := ∑ l, a l • b l
    have hf : f = 0 := by
      by_contra hf0
      obtain ⟨g, hg⟩ := exists_comp_ne_zero f hf0
      apply hg
      have h1 : Θ g f = φ (Ψ g) := by
        rw [φ.pi_apply_eq_sum_univ (Ψ g)]
        simp only [f, map_sum, map_smul, smul_eq_mul, Ψ, LinearMap.coe_mk, AddHom.coe_mk, a]
        refine Finset.sum_congr rfl fun l _ => ?_
        exact mul_comm _ _
      rw [hφΨ, hΘ] at h1
      simpa using h1
    apply hφ0
    have ha : ∀ l, a l = 0 :=
      Fintype.linearIndependent_iff.1 b.linearIndependent a hf
    refine LinearMap.ext fun v => ?_
    rw [φ.pi_apply_eq_sum_univ v]
    exact Finset.sum_eq_zero fun l _ => by rw [show (φ fun j => if l = j then 1 else 0) = 0 from ha l]; simp
  intro i0
  obtain ⟨g, hg⟩ : ∃ g, Ψ g = Pi.single i0 1 := by
    have : (Pi.single i0 1 : ι → k) ∈ LinearMap.range Ψ := by rw [hrange]; trivial
    exact this
  have := h g
  simp only [map_sum, evalHom_tmul] at this
  have h2 : ∀ i, g (b i (y i)) = Ψ g i • y i := fun i => he (g ∘ₗ b i) (y i)
  simp only [h2, hg] at this
  simpa [Pi.single_apply] using this

end Injective

section Family
variable (k : Type*) {A : Type*} [Field k] [Ring A] [Algebra k A]
  {V : Type*} [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  {ι : Type*} [Fintype ι] (X : ι → Type*) [∀ i, AddCommGroup (X i)] [∀ i, Module k (X i)]
  [∀ i, Module A (X i)] [∀ i, IsScalarTower k A (X i)]

/-- The evaluation map from the direct sum of the spaces `X i ⊗ Hom_A(X i, V)` to `V`. -/
noncomputable def isotypicEval : (Π i, X i ⊗[k] (X i →ₗ[A] V)) →ₗ[A] V :=
  ∑ i, (evalHom k (X i) V).comp (LinearMap.proj i)

variable {k X} in
/-- Evaluation of `isotypicEval` as a sum. -/
theorem isotypicEval_apply (z : Π i, X i ⊗[k] (X i →ₗ[A] V)) :
    isotypicEval k X z = ∑ i, evalHom k (X i) V (z i) := by
  simp [isotypicEval, LinearMap.sum_apply]

variable {k X} in
/-- Evaluation on a single summand. -/
theorem isotypicEval_single [DecidableEq ι] (i : ι) (w : X i ⊗[k] (X i →ₗ[A] V)) :
    isotypicEval k X (Pi.single i w) = evalHom k (X i) V w := by
  rw [isotypicEval_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

/-- `Hom_A(X, V)` is finite-dimensional over `k` when `X` and `V` are. -/
theorem finiteDimensional_hom {X V : Type*} [AddCommGroup X] [Module k X] [Module A X]
    [IsScalarTower k A X] [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [FiniteDimensional k X] [FiniteDimensional k V] : FiniteDimensional k (X →ₗ[A] V) :=
  Module.Finite.of_injective (LinearMap.restrictScalarsₗ k A X V k)
    (LinearMap.restrictScalars_injective _)

variable [IsAlgClosed k] [∀ i, IsSimpleModule A (X i)] [∀ i, FiniteDimensional k (X i)]
  [IsSemisimpleModule A V] [FiniteDimensional k V]

omit [Fintype ι] [IsAlgClosed k] [∀ i, FiniteDimensional k (X i)] [IsSemisimpleModule A V]
  [FiniteDimensional k V] in
/-- Maps from a simple module to a non-isomorphic simple module vanish. -/
theorem comp_evalHom_eq_zero {i j : ι} (hij : IsEmpty (X i ≃ₗ[A] X j)) (g : V →ₗ[A] X j)
    (w : X i ⊗[k] (X i →ₗ[A] V)) : g (evalHom k (X i) V w) = 0 := by
  induction w using TensorProduct.inductionOn with
  | tmul x f =>
    rw [evalHom_tmul]
    change (g ∘ₗ f) x = 0
    rcases LinearMap.bijective_or_eq_zero (g ∘ₗ f) with h | h
    · exact (hij.false (LinearEquiv.ofBijective _ h)).elim
    · simp [h]
  | add w w' hw hw' => simp [hw, hw']

/-- Injectivity of the evaluation map. -/
theorem isotypicEval_injective (hX : ∀ i j, i ≠ j → IsEmpty (X i ≃ₗ[A] X j)) :
    Function.Injective (isotypicEval k (A := A) (V := V) X) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  funext j
  have _ : FiniteDimensional k (X j →ₗ[A] V) := finiteDimensional_hom k
  let b := Module.finBasis k (X j →ₗ[A] V)
  obtain ⟨y, hy⟩ := exists_eq_sum_tmul_basis b (z j)
  have hg : ∀ g : V →ₗ[A] X j, g (evalHom k (X j) V (z j)) = 0 := by
    intro g
    have h1 := congr(g $hz)
    rw [map_zero, isotypicEval_apply, map_sum, Finset.sum_eq_single j] at h1
    · exact h1
    · intro i _ hij
      exact comp_evalHom_eq_zero k X (hX i j hij) g _
    · simp
  rw [hy] at hg
  have := eq_zero_of_forall_comp_evalHom k b y hg
  rw [hy]
  simp [this]

omit [IsAlgClosed k] [∀ i, IsSimpleModule A (X i)] [∀ i, FiniteDimensional k (X i)]
  [FiniteDimensional k V] in
/-- Surjectivity of the evaluation map. -/
theorem isotypicEval_surjective
    (hcov : ∀ S : Submodule A V, IsSimpleModule A S → ∃ i, Nonempty (X i ≃ₗ[A] S)) :
    Function.Surjective (isotypicEval k (A := A) (V := V) X) := by
  classical
  rw [← LinearMap.range_eq_top, ← top_le_iff, ← IsSemisimpleModule.sSup_simples_eq_top (R := A) (M := V)]
  refine sSup_le fun S hS => ?_
  obtain ⟨i, ⟨e⟩⟩ := hcov S hS
  intro s hs
  refine ⟨Pi.single i (e.symm ⟨s, hs⟩ ⊗ₜ[k] (S.subtype ∘ₗ e.toLinearMap)), ?_⟩
  rw [isotypicEval_single, evalHom_tmul]
  simp

/-- **Isotypic decomposition** (Etingof et al., Definition 2.1 example, p. 23).  Over an algebraically closed
field, a finite-dimensional semisimple `A`-module `V` is the direct sum of the modules `Xᵢ ⊗ Hom_A(Xᵢ, V)`,
where `(Xᵢ)` is a finite family of pairwise non-isomorphic finite-dimensional simple modules such that every
simple submodule of `V` is isomorphic to some `Xᵢ`, and `A` acts through the factor `Xᵢ`. -/
@[kb "etingof2011" "Definition 2.1 example, p. 23"]
noncomputable def isotypicDecomposition (hX : ∀ i j, i ≠ j → IsEmpty (X i ≃ₗ[A] X j))
    (hcov : ∀ S : Submodule A V, IsSimpleModule A S → ∃ i, Nonempty (X i ≃ₗ[A] S)) :
    (Π i, X i ⊗[k] (X i →ₗ[A] V)) ≃ₗ[A] V :=
  LinearEquiv.ofBijective (isotypicEval k X)
    ⟨isotypicEval_injective k X hX, isotypicEval_surjective k X hcov⟩

end Family

section DoubleCentralizerDecomposition

variable {k : Type*} [Field k] {E : Type*} [AddCommGroup E] [Module k E]
  (A : Subalgebra k (Module.End k E))

/-- Post-composition with an element of the commutant `B` of `A`, as a map `Hom_A(X, E) → Hom_A(X, E)`. -/
noncomputable def commutantComp {X : Type*} [AddCommGroup X] [Module A X] (b : commutant A)
    (f : X →ₗ[A] E) : X →ₗ[A] E :=
  commutantToEnd A b ∘ₗ f

theorem commutantComp_apply {X : Type*} [AddCommGroup X] [Module A X] (b : commutant A)
    (f : X →ₗ[A] E) (x : X) : commutantComp A b f x = b.1 (f x) := rfl

/-- The commutant `B` of `A` acts on `Hom_A(X, E)` by post-composition. -/
@[instance_reducible] noncomputable def homCommutantModule (X : Type*) [AddCommGroup X] [Module A X] :
    Module (commutant A) (X →ₗ[A] E) :=
  Module.compHom _ (commutantToEnd A).toRingHom

/-- **Etingof et al., Theorem 4.54 (c), simplicity part.**  For a semisimple subalgebra `A` of `End E` with
commutant `B`, and a simple `A`-module `X` occurring in `E`, the space `Hom_A(X, E)` is a simple `B`-module. -/
@[kb "etingof2011" "Theorem 4.54, p. 64"]
theorem isSimpleModule_homCommutant [IsSemisimpleModule A E] (X : Type*) [AddCommGroup X] [Module A X]
    [IsSimpleModule A X] [Nontrivial (X →ₗ[A] E)] :
    @IsSimpleModule (commutant A) _ (X →ₗ[A] E) _ (homCommutantModule A X) := by
  let _ := homCommutantModule A X
  rw [isSimpleModule_iff_toSpanSingleton_surjective]
  refine ⟨inferInstance, fun f hf f' => ?_⟩
  obtain ⟨h, hh⟩ := IsSemisimpleModule.extension_property f (LinearMap.injective_of_ne_zero hf) f'
  refine ⟨(commutantEquivEnd A).symm h, ?_⟩
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.toSpanSingleton_apply]
  have : (commutantToEnd A ((commutantEquivEnd A).symm h)) = h := (commutantEquivEnd A).apply_symm_apply h
  change (commutantToEnd A ((commutantEquivEnd A).symm h)) (f x) = f' x
  rw [this, ← hh]
  rfl

/-- **Etingof et al., Theorem 4.54 (c), compatibility part.**  The decomposition
`E ≅ ⨁ Xᵢ ⊗ Hom_A(Xᵢ, E)` is compatible with the commutant: an element `b` of the commutant acts on the summand
`x ⊗ f` as `x ⊗ (b ∘ f)`. -/
@[kb "etingof2011" "Theorem 4.54, p. 64"]
theorem commutant_isotypicEval_single {ι : Type*} [Fintype ι] [DecidableEq ι] (X : ι → Type*)
    [∀ i, AddCommGroup (X i)] [∀ i, Module k (X i)] [∀ i, Module A (X i)] [∀ i, IsScalarTower k A (X i)]
    (b : commutant A) (i : ι) (x : X i) (f : X i →ₗ[A] E) :
    b.1 (isotypicEval k X (Pi.single i (x ⊗ₜ[k] f))) =
      isotypicEval k X (Pi.single i (x ⊗ₜ[k] (commutantComp A b f))) := by
  rw [isotypicEval_single, isotypicEval_single, evalHom_tmul, evalHom_tmul, commutantComp_apply]

end DoubleCentralizerDecomposition

section Theorem226

/-- A nonzero Artinian module has a simple submodule. -/
theorem exists_simple_submodule_of_artinian {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [Nontrivial M] [IsArtinian R M] : ∃ N : Submodule R M, IsSimpleModule R N := by
  rcases eq_bot_or_exists_atom_le (⊤ : Submodule R M) with h | ⟨a, ha, -⟩
  · obtain ⟨x, hx⟩ := exists_ne (0 : M)
    have hx' : x ∈ (⊤ : Submodule R M) := trivial
    rw [h] at hx'
    exact absurd ((Submodule.mem_bot R).1 hx') hx
  · exact ⟨a, (isSimpleModule_iff_isAtom).2 ha⟩

variable (k : Type*) [Field k] [IsAlgClosed k] (A B M : Type*) [Ring A] [Algebra k A] [Ring B]
  [Algebra k B] [AddCommGroup M] [Module k M] [Module A M] [Module B M] [Module (A ⊗[k] B) M]
  [IsScalarTower k A M] [IsScalarTower k B M] [SMulCommClass A B M]

attribute [local instance] tensorModule

/-- **Etingof et al., Theorem 2.26 (ii), existence.**  Let `M` be a finite-dimensional simple
`A ⊗ B`-module over an algebraically closed field, whose restrictions to `A` and `B` are the given module
structures (`h`).  Then `M ≅ V ⊗ W` as `A ⊗ B`-modules, where `V` is a simple `A`-submodule of `M` and `W` is a
simple `B`-submodule of `Hom_A(V, M)` (with `B` acting by post-composition). -/
@[kb "etingof2011" "Theorem 2.26, p. 31"]
theorem exists_linearEquiv_tensor_of_isSimpleModule [IsSimpleModule (A ⊗[k] B) M]
    [FiniteDimensional k M] (h : ∀ (a : A) (b : B) (m : M), (a ⊗ₜ[k] b) • m = a • b • m) :
    ∃ (V : Submodule A M) (W : Submodule B (V →ₗ[A] M)), IsSimpleModule A V ∧ IsSimpleModule B W ∧
      Nonempty ((V ⊗[k] W) ≃ₗ[A ⊗[k] B] M) := by
  have : Nontrivial M := IsSimpleModule.nontrivial (A ⊗[k] B) M
  have : IsArtinian k M := inferInstance
  have : IsArtinian A M := isArtinian_of_tower k this
  obtain ⟨V, hV⟩ := exists_simple_submodule_of_artinian (R := A) (M := M)
  have : FiniteDimensional k V :=
    Module.Finite.of_injective (V.subtype.restrictScalars k) Subtype.val_injective
  have : FiniteDimensional k (V →ₗ[A] M) := finiteDimensional_hom k
  have : Nontrivial (V →ₗ[A] M) := ⟨⟨V.subtype, 0, fun h0 => by
    have := IsSimpleModule.nontrivial A V
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    exact hx (Subtype.ext (by simpa using congr($h0 x)))⟩⟩
  have : IsArtinian k (V →ₗ[A] M) := inferInstance
  have : IsArtinian B (V →ₗ[A] M) := isArtinian_of_tower k this
  obtain ⟨W, hW⟩ := exists_simple_submodule_of_artinian (R := B) (M := V →ₗ[A] M)
  refine ⟨V, W, hV, hW, ?_⟩
  let Φ0 : V ⊗[k] W →ₗ[k] M :=
    TensorProduct.lift
      { toFun := fun v =>
          { toFun := fun w => (w : V →ₗ[A] M) v
            map_add' := fun w w' => by simp
            map_smul' := fun c w => by simp }
        map_add' := fun v v' => by ext w; simp
        map_smul' := fun c v => by ext w; simp }
  have hΦ0 : ∀ (v : V) (w : W), Φ0 (v ⊗ₜ[k] w) = (w : V →ₗ[A] M) v := fun v w => by simp [Φ0]
  have : SMulCommClass B A M := SMulCommClass.symm A B M
  have hsm : ∀ (r : A ⊗[k] B) (z : V ⊗[k] W), Φ0 (r • z) = r • Φ0 z := by
    intro r z
    induction r using TensorProduct.inductionOn with
    | tmul a b =>
      induction z using TensorProduct.inductionOn with
      | tmul v w =>
        rw [tensorModule_tmul_smul_tmul, hΦ0, hΦ0, h, Submodule.coe_smul, LinearMap.smul_apply,
          map_smul, smul_comm]
      | add z1 z2 h1 h2 => rw [smul_add, map_add, map_add, h1, h2, smul_add]
    | add r1 r2 h1 h2 => rw [add_smul, map_add, h1, h2, add_smul]
  let Φ : V ⊗[k] W →ₗ[A ⊗[k] B] M :=
    { toFun := Φ0
      map_add' := Φ0.map_add
      map_smul' := fun r z => hsm r z }
  have hΦ : ∀ (v : V) (w : W), Φ (v ⊗ₜ[k] w) = (w : V →ₗ[A] M) v := hΦ0
  have : IsSimpleModule (A ⊗[k] B) (V ⊗[k] W) := isSimpleModule_tensorModule k
  have hne : Φ ≠ 0 := by
    have := IsSimpleModule.nontrivial B W
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    have hw' : (w : V →ₗ[A] M) ≠ 0 := fun h0 => hw (Subtype.ext h0)
    obtain ⟨v, hv⟩ : ∃ v, (w : V →ₗ[A] M) v ≠ 0 := by
      by_contra hcon
      exact hw' (LinearMap.ext fun x => by_contra fun hx => hcon ⟨x, hx⟩)
    intro h0
    apply hv
    rw [← hΦ, h0]
    rfl
  exact ⟨LinearEquiv.ofBijective Φ
    ⟨LinearMap.injective_of_ne_zero hne, LinearMap.surjective_of_ne_zero hne⟩⟩

end Theorem226

section Theorem226Unique

/-- A pure tensor of nonzero vectors over a field is nonzero. -/
theorem tmul_ne_zero_of_ne_zero {k V W : Type*} [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] {v : V} {w : W} (hv : v ≠ 0) (hw : w ≠ 0) :
    v ⊗ₜ[k] w ≠ 0 := by
  obtain ⟨φ, hφ⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.toSpanSingleton k V v)
    (LinearMap.ker_eq_bot.2 (smul_left_injective k hv))
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.toSpanSingleton k W w)
    (LinearMap.ker_eq_bot.2 (smul_left_injective k hw))
  have h1 : φ v = 1 := by simpa using congr($hφ 1)
  have h2 : ψ w = 1 := by simpa using congr($hψ 1)
  intro h0
  have := congr(TensorProduct.lift ((LinearMap.mul k k).compl₁₂ φ ψ) $h0)
  simp [h1, h2] at this

variable (k : Type*) [Field k] (A B : Type*) [Ring A] [Algebra k A] [Ring B] [Algebra k B]
  {V V' W W' : Type*} [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [AddCommGroup V'] [Module k V'] [Module A V'] [IsScalarTower k A V']
  [AddCommGroup W] [Module k W] [Module B W] [IsScalarTower k B W]
  [AddCommGroup W'] [Module k W'] [Module B W'] [IsScalarTower k B W']
  [IsSimpleModule A V] [IsSimpleModule A V'] [IsSimpleModule B W] [IsSimpleModule B W']
  [FiniteDimensional k V'] [FiniteDimensional k W']

attribute [local instance] tensorModule

/-- **Etingof et al., Theorem 2.26 (ii), uniqueness.**  If `V ⊗ W` and `V' ⊗ W'` are isomorphic as
`A ⊗ B`-modules, for simple modules `V, V'` over `A` and `W, W'` over `B` (the primed ones finite-dimensional),
then `V ≅ V'` as `A`-modules and `W ≅ W'` as `B`-modules. -/
@[kb "etingof2011" "Theorem 2.26, p. 31"]
theorem linearEquiv_of_tensor_linearEquiv (θ : (V ⊗[k] W) ≃ₗ[A ⊗[k] B] (V' ⊗[k] W')) :
    Nonempty (V ≃ₗ[A] V') ∧ Nonempty (W ≃ₗ[B] W') := by
  have : Nontrivial V := IsSimpleModule.nontrivial A V
  have : Nontrivial W := IsSimpleModule.nontrivial B W
  obtain ⟨v0, hv0⟩ := exists_ne (0 : V)
  obtain ⟨w0, hw0⟩ := exists_ne (0 : W)
  have hz : θ (v0 ⊗ₜ[k] w0) ≠ 0 := fun h =>
    tmul_ne_zero_of_ne_zero hv0 hw0 (θ.injective (by rw [h, map_zero]))
  constructor
  · let b' := Module.finBasis k W'
    obtain ⟨y, hy⟩ := exists_eq_sum_tmul_basis (X := V') b' (θ (v0 ⊗ₜ[k] w0))
    obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
      by_contra hcon
      apply hz
      rw [hy]
      exact Finset.sum_eq_zero fun j _ => by
        rw [show y j = 0 from by_contra fun hj => hcon ⟨j, hj⟩, TensorProduct.zero_tmul]
    let gk : V' ⊗[k] W' →ₗ[k] V' :=
      (TensorProduct.rid k V').toLinearMap ∘ₗ LinearMap.lTensor V' (b'.coord i)
    have hgk : ∀ (v' : V') (w' : W'), gk (v' ⊗ₜ[k] w') = b'.coord i w' • v' := by
      intro v' w'; simp [gk]
    have hgA : ∀ (a : A) (z : V' ⊗[k] W'), gk ((a ⊗ₜ[k] (1 : B)) • z) = a • gk z := by
      intro a z
      induction z using TensorProduct.inductionOn with
      | tmul v' w' =>
        rw [tensorModule_tmul_smul_tmul, one_smul, hgk, hgk, smul_comm]
      | add z1 z2 h1 h2 => rw [smul_add, map_add, h1, h2, map_add, smul_add]
    let g : V →ₗ[A] V' :=
      { toFun := fun v => gk (θ (v ⊗ₜ[k] w0))
        map_add' := fun v v' => by simp [TensorProduct.add_tmul]
        map_smul' := fun a v => by
          have : (a • v) ⊗ₜ[k] w0 = (a ⊗ₜ[k] (1 : B)) • (v ⊗ₜ[k] w0) := by
            rw [tensorModule_tmul_smul_tmul, one_smul]
          simp only [RingHom.id_apply]
          rw [this, LinearEquiv.map_smul, hgA] }
    have hg : g ≠ 0 := by
      intro h0
      have h1 : g v0 = y i := by
        change gk (θ (v0 ⊗ₜ[k] w0)) = y i
        rw [hy, map_sum]
        simp only [hgk]
        rw [Finset.sum_eq_single i]
        · simp [b']
        · intro j _ hj
          simp [b', Module.Basis.coord_apply, hj]
        · simp
      exact hi (by rw [← h1, h0]; rfl)
    exact ⟨LinearEquiv.ofBijective g (LinearMap.bijective_of_ne_zero hg)⟩
  · let e := Module.finBasis k V'
    obtain ⟨y, hy⟩ := exists_eq_sum_basis_tmul (W := W') e (θ (v0 ⊗ₜ[k] w0))
    obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
      by_contra hcon
      apply hz
      rw [hy]
      exact Finset.sum_eq_zero fun j _ => by
        rw [show y j = 0 from by_contra fun hj => hcon ⟨j, hj⟩, TensorProduct.tmul_zero]
    let gk : V' ⊗[k] W' →ₗ[k] W' :=
      (TensorProduct.lid k W').toLinearMap ∘ₗ LinearMap.rTensor W' (e.coord i)
    have hgk : ∀ (v' : V') (w' : W'), gk (v' ⊗ₜ[k] w') = e.coord i v' • w' := by
      intro v' w'; simp [gk]
    have hgB : ∀ (b : B) (z : V' ⊗[k] W'), gk (((1 : A) ⊗ₜ[k] b) • z) = b • gk z := by
      intro b z
      induction z using TensorProduct.inductionOn with
      | tmul v' w' =>
        rw [tensorModule_tmul_smul_tmul, one_smul, hgk, hgk, smul_comm]
      | add z1 z2 h1 h2 => rw [smul_add, map_add, h1, h2, map_add, smul_add]
    let g : W →ₗ[B] W' :=
      { toFun := fun w => gk (θ (v0 ⊗ₜ[k] w))
        map_add' := fun w w' => by simp [TensorProduct.tmul_add]
        map_smul' := fun b w => by
          have : v0 ⊗ₜ[k] (b • w) = ((1 : A) ⊗ₜ[k] b) • (v0 ⊗ₜ[k] w) := by
            rw [tensorModule_tmul_smul_tmul, one_smul]
          simp only [RingHom.id_apply]
          rw [this, LinearEquiv.map_smul, hgB] }
    have hg : g ≠ 0 := by
      intro h0
      have h1 : g w0 = y i := by
        change gk (θ (v0 ⊗ₜ[k] w0)) = y i
        rw [hy, map_sum]
        simp only [hgk]
        rw [Finset.sum_eq_single i]
        · simp [e]
        · intro j _ hj
          simp [e, Module.Basis.coord_apply, hj]
        · simp
      exact hi (by rw [← h1, h0]; rfl)
    exact ⟨LinearEquiv.ofBijective g (LinearMap.bijective_of_ne_zero hg)⟩

end Theorem226Unique

end UndergradKB.RepresentationTheory
