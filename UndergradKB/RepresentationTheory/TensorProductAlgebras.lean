import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.AlgebrasChapter2

/-! # Tensor products of modules over tensor products of algebras (Etingof et al., Theorem 2.26)

For modules `V` over `A` and `W` over `B` (algebras over a field `k`), the tensor product `V ⊗ W` is a module
over `A ⊗ B`, with `(a ⊗ b) (v ⊗ w) = a v ⊗ b w`.  We define this module structure through the algebra map
`A ⊗ B → End V ⊗ End W → End (V ⊗ W)` and prove part (i) of the theorem: if `k` is algebraically closed, `V` is
finite-dimensional and both `V`, `W` are simple, then `V ⊗ W` is a simple `A ⊗ B`-module.

Part (ii) (every simple finite-dimensional `A ⊗ B`-module arises this way, uniquely) is not formalized.
-/

namespace UndergradKB.RepresentationTheory

open scoped TensorProduct

section

variable (k A B V W : Type*) [Field k] [Ring A] [Algebra k A] [Ring B] [Algebra k B]
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [AddCommGroup W] [Module k W] [Module B W] [IsScalarTower k B W]

/-- The action of `A ⊗ B` on `V ⊗ W` as an algebra map to `End_k (V ⊗ W)`. -/
noncomputable def tensorAction : A ⊗[k] B →ₐ[k] Module.End k (V ⊗[k] W) :=
  (Module.endTensorEndAlgHom (R := k) (S := k) (A := k) (M := V) (N := W)).comp
    (Algebra.TensorProduct.map (Algebra.lsmul k k V) (Algebra.lsmul k k W))

theorem tensorAction_tmul (a : A) (b : B) (v : V) (w : W) :
    tensorAction k A B V W (a ⊗ₜ b) (v ⊗ₜ w) = (a • v) ⊗ₜ (b • w) := by
  simp [tensorAction, Module.endTensorEndAlgHom_apply]

/-- The `A ⊗ B`-module structure on `V ⊗ W`. -/
@[instance_reducible] noncomputable def tensorModule : Module (A ⊗[k] B) (V ⊗[k] W) :=
  Module.compHom _ (tensorAction k A B V W).toRingHom

attribute [local instance] tensorModule in
theorem tensorModule_tmul_smul_tmul (a : A) (b : B) (v : V) (w : W) :
    (a ⊗ₜ[k] b) • (v ⊗ₜ[k] w) = (a • v) ⊗ₜ[k] (b • w) :=
  tensorAction_tmul k A B V W a b v w

variable {k V} in
/-- Every element of `V ⊗ W` is `∑ eᵢ ⊗ wᵢ` for a given basis `e` of `V`. -/
theorem exists_eq_sum_basis_tmul {ι : Type*} [Fintype ι] (e : Module.Basis ι k V) (x : V ⊗[k] W) :
    ∃ w : ι → W, x = ∑ i, e i ⊗ₜ[k] w i := by
  induction x using TensorProduct.inductionOn with
  | tmul v w =>
    refine ⟨fun i => e.repr v i • w, ?_⟩
    conv_lhs => rw [← e.sum_repr v]
    rw [TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.smul_tmul]
  | add x y hx hy =>
    obtain ⟨w1, rfl⟩ := hx
    obtain ⟨w2, rfl⟩ := hy
    exact ⟨w1 + w2, by simp [TensorProduct.tmul_add, Finset.sum_add_distrib]⟩

end

section

variable (k : Type*) {A B V W : Type*} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [Ring B]
  [Algebra k B] [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [AddCommGroup W] [Module k W] [Module B W] [IsScalarTower k B W]
  [IsSimpleModule A V] [IsSimpleModule B W] [FiniteDimensional k V]

/-- **Etingof et al., Theorem 2.26 (i)**: over an algebraically closed field, the tensor product of a
finite-dimensional simple `A`-module `V` and a simple `B`-module `W` is a simple module over `A ⊗ B`
(here `W` is not even required to be finite-dimensional). -/
@[kb "etingof2011" "Theorem 2.26, p. 31"]
theorem isSimpleModule_tensorModule :
    @IsSimpleModule (A ⊗[k] B) _ (V ⊗[k] W) _ (tensorModule k A B V W) := by
  let _ := tensorModule k A B V W
  have : Nontrivial V := IsSimpleModule.nontrivial A V
  have : Nontrivial W := IsSimpleModule.nontrivial B W
  obtain ⟨w0, hw0⟩ := exists_ne (0 : W)
  have : Nontrivial (V ⊗[k] W) :=
    TensorProduct.nontrivial_of_linearMap_injective_of_flat_left k V W (LinearMap.toSpanSingleton k W w0)
      (smul_left_injective k hw0)
  rw [isSimpleModule_iff_toSpanSingleton_surjective]
  refine ⟨inferInstance, fun x hx y => ?_⟩
  -- expand `x` in a basis of `V`
  let e := Module.finBasis k V
  obtain ⟨w, hw⟩ := exists_eq_sum_basis_tmul (W := W) e x
  have hj : ∃ j, w j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hx (by simp [hw, h])
  obtain ⟨j, hj⟩ := hj
  classical
  -- project onto the `j`-th summand
  obtain ⟨a, ha⟩ := exists_smul_eq_of_linearIndependent (k := k) (A := A) (V := V) e e.linearIndependent
    (fun i => if i = j then e j else 0)
  have h1 : (a ⊗ₜ[k] (1 : B)) • x = e j ⊗ₜ[k] w j := by
    rw [hw, Finset.smul_sum]
    rw [Finset.sum_eq_single j]
    · rw [tensorModule_tmul_smul_tmul, ha]
      simp
    · intro i _ hij
      rw [tensorModule_tmul_smul_tmul, ha]
      simp [hij]
    · simp
  have hej : e j ≠ 0 := e.ne_zero j
  -- reach every pure tensor from `e j ⊗ w j`
  have h2 : ∀ (v : V) (w' : W), ∃ r : A ⊗[k] B, r • (e j ⊗ₜ[k] w j) = v ⊗ₜ[k] w' := by
    intro v w'
    obtain ⟨a', ha'⟩ := IsSimpleModule.toSpanSingleton_surjective (R := A) hej v
    obtain ⟨b', hb'⟩ := IsSimpleModule.toSpanSingleton_surjective (R := B) hj w'
    refine ⟨a' ⊗ₜ b', ?_⟩
    rw [tensorModule_tmul_smul_tmul]
    exact congrArg₂ _ ha' hb'
  have h3 : ∀ z : V ⊗[k] W, ∃ r : A ⊗[k] B, r • (e j ⊗ₜ[k] w j) = z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul v w' => exact h2 v w'
    | add z1 z2 h1' h2' =>
      obtain ⟨r1, hr1⟩ := h1'
      obtain ⟨r2, hr2⟩ := h2'
      exact ⟨r1 + r2, by rw [add_smul, hr1, hr2]⟩
  obtain ⟨r, hr⟩ := h3 y
  refine ⟨r * (a ⊗ₜ[k] (1 : B)), ?_⟩
  simp only [LinearMap.toSpanSingleton_apply]
  rw [mul_smul, h1, hr]

end

end UndergradKB.RepresentationTheory
