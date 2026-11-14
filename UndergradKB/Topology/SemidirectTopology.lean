import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Constructions
import UndergradKB.Common.Attr

/-! # Topological semidirect products (Morris, Exercises A5.5 #6, row TP-537)

Mathlib has the semidirect product of groups `N ⋊[φ] G` (`SemidirectProduct`), with no topology.
Following the book we give it the product topology of `N × G` (a small bridging instance: the
topology induced by `x ↦ (x.left, x.right)`), and prove that when the action `(n, g) ↦ φ g n` is
continuous, each `φ g` is a homeomorphism and `N ⋊[φ] G` is a topological group.
-/

open Topology

namespace UndergradKB.Topology

variable {N G : Type*} [Group N] [Group G] [TopologicalSpace N] [TopologicalSpace G]
  {φ : G →* MulAut N}

/-- The product topology on the semidirect product (bridging instance: Mathlib has none). -/
instance semidirectProductTopology : TopologicalSpace (N ⋊[φ] G) :=
  TopologicalSpace.induced (fun x => (x.left, x.right)) inferInstance

theorem continuous_semidirect_iff {X : Type*} [TopologicalSpace X] {f : X → N ⋊[φ] G} :
    Continuous f ↔ Continuous (fun x => (f x).left) ∧ Continuous (fun x => (f x).right) := by
  rw [continuous_induced_rng, continuous_prodMk]
  rfl

theorem continuous_semidirect_left : Continuous fun x : N ⋊[φ] G => x.left :=
  (continuous_semidirect_iff.1 continuous_id).1

theorem continuous_semidirect_right : Continuous fun x : N ⋊[φ] G => x.right :=
  (continuous_semidirect_iff.1 continuous_id).2

/-- The semidirect product is homeomorphic to `N × G` (the book's description: the set `N × G`
with the product topology). -/
def semidirectHomeomorphProd : (N ⋊[φ] G) ≃ₜ N × G where
  toFun x := (x.left, x.right)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_semidirect_left.prodMk continuous_semidirect_right
  continuous_invFun := continuous_semidirect_iff.2 ⟨continuous_fst, continuous_snd⟩

/-- Morris, Exercises A5.5 #6 (i) (TP-537).  If the action `(n, g) ↦ φ g n` is continuous, each
automorphism `φ g` is a homeomorphism of `N`. -/
@[kb "morris2024" "Exercises A5.5 #6(i), p. 537"]
def actionHomeomorph (hφ : Continuous fun p : N × G => φ p.2 p.1) (g : G) : N ≃ₜ N where
  toEquiv := (φ g).toEquiv
  continuous_toFun := hφ.comp (continuous_id.prodMk continuous_const)
  continuous_invFun := by
    have : (φ g).toEquiv.invFun = fun n => φ g⁻¹ n := by
      funext n
      rw [map_inv]
      rfl
    show Continuous (φ g).toEquiv.invFun
    rw [this]
    exact hφ.comp (continuous_id.prodMk continuous_const)

/-- Morris, Exercises A5.5 #6 (ii) (TP-537).  With the product topology, the semidirect product
`N ⋊[φ] G` of topological groups is a topological group when the action `(n, g) ↦ φ g n` is
continuous. -/
@[kb "morris2024" "Exercises A5.5 #6(ii), p. 537"]
theorem isTopologicalGroup_semidirectProduct [IsTopologicalGroup N] [IsTopologicalGroup G]
    (hφ : Continuous fun p : N × G => φ p.2 p.1) : IsTopologicalGroup (N ⋊[φ] G) where
  continuous_mul := by
    rw [continuous_semidirect_iff]
    constructor
    · show Continuous fun p : (N ⋊[φ] G) × (N ⋊[φ] G) => p.1.left * φ p.1.right p.2.left
      exact (continuous_semidirect_left.comp continuous_fst).mul
        (hφ.comp ((continuous_semidirect_left.comp continuous_snd).prodMk
          (continuous_semidirect_right.comp continuous_fst)))
    · show Continuous fun p : (N ⋊[φ] G) × (N ⋊[φ] G) => p.1.right * p.2.right
      exact (continuous_semidirect_right.comp continuous_fst).mul
        (continuous_semidirect_right.comp continuous_snd)
  continuous_inv := by
    rw [continuous_semidirect_iff]
    constructor
    · show Continuous fun x : N ⋊[φ] G => φ x.right⁻¹ x.left⁻¹
      exact hφ.comp (continuous_semidirect_left.inv.prodMk continuous_semidirect_right.inv)
    · show Continuous fun x : N ⋊[φ] G => x.right⁻¹
      exact continuous_semidirect_right.inv

end UndergradKB.Topology
