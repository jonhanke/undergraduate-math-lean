import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import UndergradKB.Topology.TopGroups
import UndergradKB.Topology.Characters
import UndergradKB.Topology.GroupsMore
import UndergradKB.Topology.DualityDiscrete
import UndergradKB.Common.Attr

/-!
# Dual of a product, of quotients and of subgroups (Morris, Appendix 5, A5.9 and A5.11)

* extension of characters from a subgroup of an abelian group (divisibility of the circle);
* `f*` is onto when `f` is open and injective (A5.9.5);
* duals of quotients and of subgroups (A5.9.6, A5.9.7);
* the dual of a product of compact groups is the restricted direct product of the duals (A5.11.8).
-/

open Set Topology Function

namespace UndergradKB.Topology

noncomputable section

/-! ### Extension of characters -/

theorem circle_exists_pow_eq (n : ℕ) (hn : 0 < n) (w : Circle) : ∃ x : Circle, x ^ n = w := by
  refine ⟨Circle.exp (Complex.arg (w : ℂ) / n), ?_⟩
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [← Circle.exp_natCast_mul]
  have : (n : ℝ) * (Complex.arg (w : ℂ) / n) = Complex.arg (w : ℂ) := by field_simp
  rw [this]
  exact Circle.exp_arg w

/-- The circle is a divisible group (additive form). -/
theorem isDivisibleGroup_additive_circle : IsDivisibleGroup (Additive Circle) := by
  intro n hn d
  obtain ⟨x, hx⟩ := circle_exists_pow_eq n hn (Additive.toMul d)
  refine ⟨Additive.ofMul x, ?_⟩
  rw [← ofMul_pow, hx]
  rfl

/-- A character of a subgroup of an abelian group extends to a character of the group. -/
theorem exists_monoidHom_circle_extension {B : Type*} [CommGroup B] (H : Subgroup B)
    (φ : H →* Circle) : ∃ Φ : B →* Circle, ∀ h : H, Φ h = φ h := by
  let H' : AddSubgroup (Additive B) := Subgroup.toAddSubgroup H
  let φ' : H' →+ Additive Circle :=
    { toFun := fun h => Additive.ofMul (φ ⟨Additive.toMul h.1, h.2⟩)
      map_zero' := congrArg Additive.ofMul (map_one φ)
      map_add' := fun a b => congrArg Additive.ofMul
        (map_mul φ ⟨Additive.toMul a.1, a.2⟩ ⟨Additive.toMul b.1, b.2⟩) }
  obtain ⟨Ψ, hΨ⟩ := exists_addMonoidHom_extension isDivisibleGroup_additive_circle H' φ'
  refine ⟨{ toFun := fun b => Additive.toMul (Ψ (Additive.ofMul b))
            map_one' := by simp
            map_mul' := fun a b => by simp [ofMul_mul] }, fun h => ?_⟩
  exact congrArg Additive.toMul (hΨ ⟨Additive.ofMul (h : B), h.2⟩)

/-! ### TP-576: `f*` is onto for an open injective `f` -/

section Surj

variable {A B : Type*} [CommGroup A] [CommGroup B] [TopologicalSpace A] [TopologicalSpace B]
  [IsTopologicalGroup A] [IsTopologicalGroup B]

/-- Morris, Topology Without Tears, Proposition A5.9.5 (TP-576), last part. If a continuous
homomorphism `f : A → B` is open and one-one, then `f* : B* → A*`, `f* γ = γ ∘ f`, is onto. (The
book states it for LCA-groups; the proof only needs topological abelian groups.) -/
@[kb "morris2024" "Proposition A5.9.5, p. 568"]
theorem PontryaginDual_map_surjective_of_isOpenMap_of_injective (f : A →ₜ* B)
    (hinj : Injective f) (hopen : IsOpenMap f) : Surjective (PontryaginDual.map f) := by
  intro δ
  have hemb : IsOpenEmbedding f :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap f.continuous_toFun hinj hopen
  let e : A ≃* (f : A →* B).range := MonoidHom.ofInjective (f := (f : A →* B)) hinj
  let φ : (f : A →* B).range →* Circle := (δ : A →* Circle).comp e.symm.toMonoidHom
  obtain ⟨Φ, hΦ⟩ := exists_monoidHom_circle_extension _ φ
  have hΦf : ∀ a, Φ (f a) = δ a := by
    intro a
    have := hΦ (e a)
    have h1 : ((e a : (f : A →* B).range) : B) = f a := rfl
    rw [h1] at this
    rw [this]
    simp [φ]
  have hcont : Continuous Φ := by
    refine continuous_of_continuousAt_one Φ ?_
    have h1 : ContinuousAt (Φ ∘ f) 1 := by
      have : (Φ ∘ f) = δ := funext hΦf
      rw [this]
      exact δ.continuous_toFun.continuousAt
    have h2 := hemb.continuousAt_iff.1 h1
    rwa [map_one] at h2
  exact ⟨⟨Φ, hcont⟩, PontryaginDual.ext fun a => hΦf a⟩

end Surj

/-! ### TP-577: duals of quotients and of subgroups -/

section QuotSub

/-- Morris, Topology Without Tears, Corollary A5.9.6 (TP-577), compact case. If `B` is a quotient
of `A` (a continuous surjective homomorphism `f`) and both are compact, then `f* : B* → A*` is an
injective continuous homomorphism and a topological embedding (both duals are discrete), so `B*` is
topologically isomorphic to a subgroup of `A*`. -/
@[kb "morris2024" "Corollary A5.9.6, p. 568"]
theorem PontryaginDual_map_isEmbedding_of_surjective_compact {A B : Type*} [Monoid A] [Monoid B]
    [TopologicalSpace A] [TopologicalSpace B] [CompactSpace A] [CompactSpace B] (f : A →ₜ* B)
    (hf : Surjective f) : Injective (PontryaginDual.map f) ∧ IsEmbedding (PontryaginDual.map f) := by
  have hinj := PontryaginDual_map_injective_of_surjective f hf
  refine ⟨hinj, ⟨?_⟩, hinj⟩
  have h1 : instTopologicalSpacePontryaginDual B = ⊥ := DiscreteTopology.eq_bot
  refine h1.trans (eq_bot_of_singletons_open (t := TopologicalSpace.induced
    (⇑(PontryaginDual.map f)) (instTopologicalSpacePontryaginDual A)) fun b => ?_).symm
  refine isOpen_induced_iff.2 ⟨{PontryaginDual.map f b}, isOpen_discrete _, ?_⟩
  ext x
  simp [hinj.eq_iff]

/-- Morris, Topology Without Tears, Corollary A5.9.6 (TP-577), discrete case. If `B` is a quotient
of `A` (a surjective homomorphism of discrete groups), then `f* : B* → A*` is an injective
continuous homomorphism and a (closed) topological embedding, so `B*` is topologically isomorphic
to a closed subgroup of `A*`. -/
@[kb "morris2024" "Corollary A5.9.6, p. 568"]
theorem PontryaginDual_map_isClosedEmbedding_of_surjective_discrete {A B : Type*} [CommGroup A]
    [CommGroup B] [TopologicalSpace A] [TopologicalSpace B] [DiscreteTopology A]
    [DiscreteTopology B] (f : A →ₜ* B) (hf : Surjective f) :
    Injective (PontryaginDual.map f) ∧ IsClosedEmbedding (PontryaginDual.map f) := by
  have hinj := PontryaginDual_map_injective_of_surjective f hf
  exact ⟨hinj, (map_continuous (PontryaginDual.map f)).isClosedEmbedding hinj⟩

/-- The inclusion of a subgroup as a continuous homomorphism. -/
def subgroupInclusion {B : Type*} [CommGroup B] [TopologicalSpace B] (A : Subgroup B) :
    A →ₜ* B :=
  ⟨A.subtype, continuous_subtype_val⟩

/-- Morris, Topology Without Tears, Corollary A5.9.7 (TP-577). If `A` is a subgroup of a discrete
abelian group `B`, then restriction of characters `B* → A*` is a continuous surjective homomorphism
and a quotient map of topological spaces, so `A*` is a quotient group of `B*` (topologically, as
both are compact Hausdorff). -/
@[kb "morris2024" "Corollary A5.9.7, p. 569"]
theorem PontryaginDual_map_isQuotientMap_subgroup_discrete {B : Type*} [CommGroup B]
    [TopologicalSpace B] [DiscreteTopology B] (A : Subgroup B) :
    Surjective (PontryaginDual.map (subgroupInclusion A)) ∧
      IsQuotientMap (PontryaginDual.map (subgroupInclusion A)) := by
  have hsurj : Surjective (PontryaginDual.map (subgroupInclusion A)) :=
    PontryaginDual_map_surjective_of_isOpenMap_of_injective (subgroupInclusion A)
      A.subtype_injective (fun s _ => isOpen_discrete _)
  exact ⟨hsurj, (map_continuous (PontryaginDual.map (subgroupInclusion A))).isClosedMap.isQuotientMap
    (map_continuous (PontryaginDual.map (subgroupInclusion A))) hsurj⟩

end QuotSub

end

end UndergradKB.Topology
