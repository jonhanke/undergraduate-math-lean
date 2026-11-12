import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.Algebra.Group.Equiv.Basic
import UndergradKB.Common.Attr

/-! # Schur functors (Etingof et al., Example 6.5(8))

The symmetric group `S_n = Equiv.Perm (Fin n)` acts on the tensor power `V^{⊗n}` by permuting the tensor factors.
For a representation `π` of `S_n`, the space of `S_n`-equivariant maps `π → V^{⊗n}` is functorial in the linear
map `V → W` (applying the `n`-th tensor power of the map), which is the Schur functor attached to `π`.

Not formalized here: the labelling of the irreducible `π` by Young diagrams.
-/

namespace UndergradKB.RepresentationTheory

open PiTensorProduct
open scoped TensorProduct

section SchurFunctors

variable (k : Type*) [CommSemiring k] (n : ℕ) (V : Type*) [AddCommMonoid V] [Module k V]

/-- The action of the symmetric group `S_n` on the tensor power `V^{⊗n}` by permuting the tensor factors. -/
@[kb "etingof2011" "Example 6.5(8), p. 100"]
noncomputable def tensorPowerPermRep : Representation k (Equiv.Perm (Fin n)) (⨂[k] _ : Fin n, V) where
  toFun σ := (reindex k (fun _ : Fin n => V) σ).toLinearMap
  map_one' := by
    refine LinearMap.ext fun x => ?_
    exact congr($(reindex_refl (R := k) (s := fun _ : Fin n => V)) x)
  map_mul' σ τ := by
    refine LinearMap.ext fun x => ?_
    exact (reindex_reindex (R := k) (s := fun _ : Fin n => V) τ σ x).symm

variable {k n V}

/-- A permutation sends a pure tensor to the pure tensor with permuted factors. -/
@[kb "etingof2011" "Example 6.5(8), p. 100"]
theorem tensorPowerPermRep_tprod (σ : Equiv.Perm (Fin n)) (f : Fin n → V) :
    tensorPowerPermRep k n V σ (tprod k f) = tprod k (fun i => f (σ⁻¹ i)) := by
  simp [tensorPowerPermRep, reindex_tprod]

/-- Each permutation acts through an invertible linear map, with inverse given by the inverse permutation. -/
@[kb "etingof2011" "Example 6.5(8), p. 100"]
theorem tensorPowerPermRep_inv_apply (σ : Equiv.Perm (Fin n)) (x : ⨂[k] _ : Fin n, V) :
    tensorPowerPermRep k n V σ⁻¹ (tensorPowerPermRep k n V σ x) = x := by
  change (tensorPowerPermRep k n V σ⁻¹ * tensorPowerPermRep k n V σ) x = x
  rw [← map_mul]
  simp

variable {W : Type*} [AddCommMonoid W] [Module k W]

/-- The `n`-th tensor power of a linear map `V → W`. -/
noncomputable def tensorPowerMap (n : ℕ) (f : V →ₗ[k] W) : (⨂[k] _ : Fin n, V) →ₗ[k] ⨂[k] _ : Fin n, W :=
  PiTensorProduct.map (fun _ => f)

/-- The tensor power of a linear map commutes with the permutation action. -/
@[kb "etingof2011" "Example 6.5(8), p. 100"]
theorem tensorPowerMap_perm (f : V →ₗ[k] W) (σ : Equiv.Perm (Fin n)) (x : ⨂[k] _ : Fin n, V) :
    tensorPowerMap n f (tensorPowerPermRep k n V σ x) = tensorPowerPermRep k n W σ (tensorPowerMap n f x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r g => simp [tensorPowerMap, tensorPowerPermRep_tprod]
  | add x y hx hy => simp [map_add, hx, hy]

@[simp] theorem tensorPowerMap_id : tensorPowerMap n (LinearMap.id : V →ₗ[k] V) = LinearMap.id := by
  simp [tensorPowerMap]

theorem tensorPowerMap_comp {U : Type*} [AddCommMonoid U] [Module k U] (g : W →ₗ[k] U) (f : V →ₗ[k] W) :
    tensorPowerMap n (g ∘ₗ f) = tensorPowerMap n g ∘ₗ tensorPowerMap n f := by
  ext x
  simp [tensorPowerMap, PiTensorProduct.map_comp]

variable {P : Type*} [AddCommMonoid P] [Module k P]

/-- The space `Hom_{S_n}(π, V^{⊗n})` of `S_n`-equivariant linear maps from a representation `π` of `S_n` to the
tensor power `V^{⊗n}`. -/
@[kb "etingof2011" "Example 6.5(8), p. 100"]
def schurHom (π : Representation k (Equiv.Perm (Fin n)) P) (V : Type*) [AddCommMonoid V] [Module k V] :
    Submodule k (P →ₗ[k] ⨂[k] _ : Fin n, V) where
  carrier := {φ | ∀ (σ : Equiv.Perm (Fin n)) (p : P), φ (π σ p) = tensorPowerPermRep k n V σ (φ p)}
  add_mem' := by
    intro a b ha hb σ p
    simp [ha σ p, hb σ p]
  zero_mem' := by
    intro σ p
    simp
  smul_mem' := by
    intro c a ha σ p
    simp [ha σ p]

/-- Membership in `schurHom` is the equivariance condition of Mathlib's intertwining maps. -/
theorem mem_schurHom_iff (π : Representation k (Equiv.Perm (Fin n)) P) (φ : P →ₗ[k] ⨂[k] _ : Fin n, V) :
    φ ∈ schurHom π V ↔ Representation.IsIntertwiningMap π (tensorPowerPermRep k n V) φ :=
  ⟨fun h => ⟨h⟩, fun h => h.isIntertwining⟩

/-- The Schur functor on morphisms: a linear map `f : V → W` induces a linear map
`Hom_{S_n}(π, V^{⊗n}) → Hom_{S_n}(π, W^{⊗n})` by composing with `f^{⊗n}`. -/
@[kb "etingof2011" "Example 6.5(8), p. 100"]
noncomputable def schurHomMap (π : Representation k (Equiv.Perm (Fin n)) P) (f : V →ₗ[k] W) :
    schurHom π V →ₗ[k] schurHom π W where
  toFun φ := ⟨tensorPowerMap n f ∘ₗ φ.1, by
    intro σ p
    simp [φ.2 σ p, tensorPowerMap_perm]⟩
  map_add' a b := by
    ext p
    simp
  map_smul' c a := by
    ext p
    simp

/-- The Schur functor preserves identities. -/
@[kb "etingof2011" "Example 6.5(8), p. 100"]
theorem schurHomMap_id (π : Representation k (Equiv.Perm (Fin n)) P) :
    schurHomMap π (LinearMap.id : V →ₗ[k] V) = LinearMap.id := by
  ext φ p
  simp [schurHomMap]

/-- The Schur functor preserves composition. -/
@[kb "etingof2011" "Example 6.5(8), p. 100"]
theorem schurHomMap_comp {U : Type*} [AddCommMonoid U] [Module k U]
    (π : Representation k (Equiv.Perm (Fin n)) P) (g : W →ₗ[k] U) (f : V →ₗ[k] W) :
    schurHomMap π (g ∘ₗ f) = schurHomMap π g ∘ₗ schurHomMap π f := by
  ext φ p
  simp [schurHomMap, tensorPowerMap_comp]

end SchurFunctors

end UndergradKB.RepresentationTheory
