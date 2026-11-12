import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Topology.Algebra.Group.CompactOpen
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import UndergradKB.Common.Attr

/-!
# The dual group of an abstract abelian group

For an abelian group `A` (no topology), `AbstractDual A` is the group of *all* homomorphisms
`A → Circle`, topologised as a subspace of the product `Circle^A` (pointwise convergence).  It is a
compact abelian group, and for `A` carrying the discrete topology it is the same as Mathlib's
`PontryaginDual A` (compact-open topology on continuous homomorphisms), since on a discrete space the
compact-open and pointwise topologies agree.
-/

open Topology Set

namespace UndergradKB.Topology

universe u

noncomputable section

/-- Morris, Topology Without Tears, Definition A5.0.13 (TP-487). The dual group `Hom(A, T)` of an
abelian group `A`: all group homomorphisms into the circle, with the subspace topology from the
product `Circle^A`. -/
@[kb "morris2024" "Definition A5.0.13, p. 503"]
def AbstractDual (A : Type u) [CommGroup A] : Type u := A →* Circle

namespace AbstractDual

variable {A : Type u} [CommGroup A]

instance : CommGroup (AbstractDual A) := inferInstanceAs (CommGroup (A →* Circle))

/-- A homomorphism viewed as a point of the product `Circle^A`. -/
def coeFn (f : AbstractDual A) : A → Circle := fun a => (show A →* Circle from f) a

/-- The subspace topology from `Circle^A`. -/
instance : TopologicalSpace (AbstractDual A) :=
  TopologicalSpace.induced coeFn inferInstance

theorem isInducing_coeFn : IsInducing (coeFn : AbstractDual A → A → Circle) := ⟨rfl⟩

theorem coeFn_injective : Function.Injective (coeFn : AbstractDual A → A → Circle) :=
  fun f g h => MonoidHom.ext (congrFun h)

theorem isEmbedding_coeFn : IsEmbedding (coeFn : AbstractDual A → A → Circle) :=
  ⟨isInducing_coeFn, coeFn_injective⟩

theorem range_coeFn :
    range (coeFn : AbstractDual A → A → Circle) =
      ⋂ a, ⋂ b, {g : A → Circle | g (a * b) = g a * g b} := by
  ext g
  simp only [mem_range, mem_iInter, mem_setOf_eq]
  constructor
  · rintro ⟨f, rfl⟩ a b
    exact map_mul (show A →* Circle from f) a b
  · intro h
    exact ⟨(MonoidHom.mk' g h : A →* Circle), rfl⟩

/-- The dual of an abelian group is a closed subset of `Circle^A`. -/
theorem isClosedEmbedding_coeFn : IsClosedEmbedding (coeFn : AbstractDual A → A → Circle) where
  toIsEmbedding := isEmbedding_coeFn
  isClosed_range := by
    rw [range_coeFn]
    exact isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_eq (continuous_apply _) ((continuous_apply a).mul (continuous_apply b))

/-- The coercion to `Circle^A` as a group homomorphism. -/
def coeHom : AbstractDual A →* (A → Circle) where
  toFun := coeFn
  map_one' := rfl
  map_mul' _ _ := rfl

instance : IsTopologicalGroup (AbstractDual A) :=
  IsInducing.isTopologicalGroup (coeHom : AbstractDual A →* (A → Circle)) isInducing_coeFn

instance : T2Space (AbstractDual A) := isEmbedding_coeFn.t2Space

instance : CompactSpace (AbstractDual A) := isClosedEmbedding_coeFn.compactSpace

end AbstractDual

/-- Morris, Topology Without Tears, Proposition A5.0.14 (TP-488). The dual group of any abelian
group is a compact Hausdorff abelian topological group. -/
@[kb "morris2024" "Proposition A5.0.14, p. 503"]
theorem abstractDual_compact_abelian_group (A : Type u) [CommGroup A] :
    CompactSpace (AbstractDual A) ∧ T2Space (AbstractDual A) ∧
      IsTopologicalGroup (AbstractDual A) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

section Identification

variable (A : Type u) [CommGroup A] [TopologicalSpace A] [DiscreteTopology A]

/-- The dual of the abstract group is the group of continuous homomorphisms of the discrete group:
the multiplicative equivalence underlying `dualContinuousMulEquiv`. -/
def dualMulEquiv : AbstractDual A ≃* PontryaginDual A where
  toFun f := (⟨(show A →* Circle from f), continuous_of_discreteTopology⟩ : A →ₜ* Circle)
  invFun ψ := (ψ.toMonoidHom : A →* Circle)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem isInducing_pontryaginCoe :
    IsInducing (fun ψ : PontryaginDual A => (⇑(ψ : A →ₜ* Circle) : A → Circle)) :=
  (ContinuousMonoidHom.isClosedEmbedding_coe (A := A) (B := Circle)).isEmbedding.isInducing

/-- Morris, Topology Without Tears, Definition A5.0.13 (TP-487). For an abelian group `A` with the
discrete topology, the dual group with the pointwise topology is isomorphic, as a topological group,
to Mathlib's Pontryagin dual (continuous homomorphisms with the compact-open topology). -/
@[kb "morris2024" "Definition A5.0.13, p. 503"]
def dualContinuousMulEquiv : AbstractDual A ≃ₜ* PontryaginDual A where
  toMulEquiv := dualMulEquiv A
  continuous_toFun := by
    rw [(isInducing_pontryaginCoe A).continuous_iff]
    exact AbstractDual.isInducing_coeFn.continuous
  continuous_invFun := by
    rw [AbstractDual.isInducing_coeFn.continuous_iff]
    exact (isInducing_pontryaginCoe A).continuous

end Identification

/-- Morris, Topology Without Tears, Theorem A5.7.9 (TP-570), the half for discrete groups: the
Pontryagin dual of a discrete abelian group is compact. -/
@[kb "morris2024" "Theorem A5.7.9, p. 561"]
theorem compactSpace_pontryaginDual_of_discrete (A : Type u) [CommGroup A] [TopologicalSpace A]
    [DiscreteTopology A] : CompactSpace (PontryaginDual A) :=
  inferInstance

end

end UndergradKB.Topology
