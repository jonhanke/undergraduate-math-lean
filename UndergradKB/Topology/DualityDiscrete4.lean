import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Topology.Compactness.Compact
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import UndergradKB.Topology.TopGroups
import UndergradKB.Topology.Characters
import UndergradKB.Topology.GroupsMore
import UndergradKB.Topology.DualityDiscrete
import UndergradKB.Common.Attr

/-!
# The dual of a product of compact groups (Morris, Appendix 5, Theorem A5.11.8)

The dual of a product of compact Hausdorff abelian groups is, as an abstract group, the restricted
direct product of the duals.  The only input that is not proved here is that the continuous
characters of each factor separate its points (the book gets it from the Peter-Weyl theorem); it
is a hypothesis `hsep`, and it holds for instance for the dual of a discrete group.
-/

open Set Topology Function

universe u

namespace UndergradKB.Topology

noncomputable section

section DualProd

variable {ι : Type*} (K : ι → Type*) [∀ i, CommGroup (K i)] [∀ i, TopologicalSpace (K i)]

theorem dualProd_support_finite
    (γ : restrictedDirectProduct (fun i => PontryaginDual (K i))) (g : ∀ i, K i) :
    (mulSupport fun i => (γ.1 i) (g i)) ⊆ ↑((mem_restrictedDirectProduct_iff _ γ.1).1 γ.2).toFinset := by
  intro i hi
  simp only [Finite.coe_toFinset, Set.mem_ofPred_eq]
  intro h
  apply hi
  simp [h]

/-- The character `g ↦ ∏ᵢ γᵢ(gᵢ)` of the product, for a finitely supported family `γ` of
characters. -/
def dualProdChar (γ : restrictedDirectProduct (fun i => PontryaginDual (K i))) :
    PontryaginDual (∀ i, K i) where
  toFun g := ∏ᶠ i, (γ.1 i) (g i)
  map_one' := by simp
  map_mul' g h := by
    have hs := dualProd_support_finite K γ
    have h1 : (mulSupport fun i => (γ.1 i) (g i)).Finite := (Finset.finite_toSet _).subset (hs g)
    have h2 : (mulSupport fun i => (γ.1 i) (h i)).Finite := (Finset.finite_toSet _).subset (hs h)
    simp only [Pi.mul_apply, map_mul]
    exact finprod_mul_distrib h1 h2
  continuous_toFun := by
    have hs := dualProd_support_finite K γ
    have : (fun g : ∀ i, K i => ∏ᶠ i, (γ.1 i) (g i)) =
        fun g => ∏ i ∈ ((mem_restrictedDirectProduct_iff _ γ.1).1 γ.2).toFinset, (γ.1 i) (g i) :=
      funext fun g => finprod_eq_prod_of_mulSupport_subset _ (hs g)
    show Continuous (fun g : ∀ i, K i => ∏ᶠ i, (γ.1 i) (g i))
    rw [this]
    exact continuous_finsetProd _ fun i _ => (map_continuous (γ.1 i)).comp (continuous_apply i)

theorem dualProdChar_apply (γ : restrictedDirectProduct (fun i => PontryaginDual (K i)))
    (g : ∀ i, K i) : dualProdChar K γ g = ∏ᶠ i, (γ.1 i) (g i) := rfl

/-- The map from finitely supported families of characters to characters of the product. -/
def dualProdHom : restrictedDirectProduct (fun i => PontryaginDual (K i)) →*
    PontryaginDual (∀ i, K i) where
  toFun := dualProdChar K
  map_one' := PontryaginDual.ext fun g => by simp [dualProdChar_apply]
  map_mul' γ δ := PontryaginDual.ext fun g => by
    have hs := dualProd_support_finite K
    have h1 : (mulSupport fun i => (γ.1 i) (g i)).Finite :=
      (Finset.finite_toSet _).subset (hs γ g)
    have h2 : (mulSupport fun i => (δ.1 i) (g i)).Finite :=
      (Finset.finite_toSet _).subset (hs δ g)
    show dualProdChar K (γ * δ) g = (dualProdChar K γ * dualProdChar K δ) g
    rw [dualProdChar_apply]
    show (∏ᶠ i, ((γ.1 i) * (δ.1 i)) (g i)) = (dualProdChar K γ g) * (dualProdChar K δ g)
    simp only [dualProdChar_apply]
    rw [← finprod_mul_distrib h1 h2]
    rfl

theorem dualProdChar_mulSingle [DecidableEq ι]
    (γ : restrictedDirectProduct (fun i => PontryaginDual (K i))) (i : ι) (x : K i) :
    dualProdChar K γ (Pi.mulSingle i x) = (γ.1 i) x := by
  rw [dualProdChar_apply, finprod_eq_single _ i]
  · simp
  · intro j hj
    simp [Pi.mulSingle_eq_of_ne hj]

theorem dualProdHom_injective : Injective (dualProdHom K) := by
  classical
  intro γ δ h
  refine Subtype.ext (funext fun i => PontryaginDual.ext fun x => ?_)
  have := DFunLike.congr_fun h (Pi.mulSingle i x)
  have e1 : dualProdHom K γ (Pi.mulSingle i x) = (γ.1 i) x := dualProdChar_mulSingle K γ i x
  have e2 : dualProdHom K δ (Pi.mulSingle i x) = (δ.1 i) x := dualProdChar_mulSingle K δ i x
  rw [e1, e2] at this
  exact this

variable [∀ i, IsTopologicalGroup (K i)] [∀ i, CompactSpace (K i)] [∀ i, T2Space (K i)]

/-- Morris, Topology Without Tears, Theorem A5.11.8 (TP-591). The dual group of a product of
compact Hausdorff abelian groups `Kᵢ` is algebraically isomorphic to the restricted direct product
of the dual groups, via `γ ↦ (g ↦ ∏ᵢ γᵢ(gᵢ))`. Hypothesis: the continuous characters of each
factor separate its points (for compact Hausdorff abelian groups this is the Peter-Weyl theorem,
not proved here). -/
@[kb "morris2024" "Theorem A5.11.8, p. 578"]
theorem dualProdHom_surjective
    (hsep : ∀ i, ∀ x y : K i, x ≠ y → ∃ χ : PontryaginDual (K i), χ x ≠ χ y) :
    Surjective (dualProdHom K) := by
  classical
  let S : Subgroup (PontryaginDual (∀ i, K i)) := (dualProdHom K).range
  have hS : S = ⊤ := by
    refine subgroup_dual_eq_top_of_separatesPoints S fun x y hxy => ?_
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hxy
    obtain ⟨χ, hχ⟩ := hsep i _ _ hi
    let γ : restrictedDirectProduct (fun i => PontryaginDual (K i)) :=
      ⟨Pi.mulSingle i χ, (Set.finite_singleton i).subset fun j hj => by
        by_contra hji
        exact hj (Pi.mulSingle_eq_of_ne (by simpa using hji) _)⟩
    refine ⟨dualProdHom K γ, ⟨γ, rfl⟩, ?_⟩
    rw [show dualProdHom K γ x = ∏ᶠ j, (γ.1 j) (x j) from rfl,
      show dualProdHom K γ y = ∏ᶠ j, (γ.1 j) (y j) from rfl,
      finprod_eq_single _ i (fun j hj => by simp [γ, Pi.mulSingle_eq_of_ne hj]),
      finprod_eq_single _ i (fun j hj => by simp [γ, Pi.mulSingle_eq_of_ne hj])]
    simpa [γ] using hχ
  intro z
  have : z ∈ S := by rw [hS]; trivial
  obtain ⟨g, hg⟩ := this
  exact ⟨g, hg⟩

/-- Morris, Topology Without Tears, Theorem A5.11.8 (TP-591), as a group isomorphism. -/
@[kb "morris2024" "Theorem A5.11.8, p. 578"]
def dualProdEquiv
    (hsep : ∀ i, ∀ x y : K i, x ≠ y → ∃ χ : PontryaginDual (K i), χ x ≠ χ y) :
    restrictedDirectProduct (fun i => PontryaginDual (K i)) ≃* PontryaginDual (∀ i, K i) :=
  MulEquiv.ofBijective (dualProdHom K) ⟨dualProdHom_injective K, dualProdHom_surjective K hsep⟩

/-- Morris, Topology Without Tears, Theorem A5.11.8 (TP-591), first half. Every continuous
character of a product of compact Hausdorff abelian groups (whose characters separate points) is
trivial on all but finitely many factors. -/
@[kb "morris2024" "Theorem A5.11.8, p. 578"]
theorem dualProd_finite_support
    (hsep : ∀ i, ∀ x y : K i, x ≠ y → ∃ χ : PontryaginDual (K i), χ x ≠ χ y)
    [DecidableEq ι] (χ : PontryaginDual (∀ i, K i)) :
    {i | ∃ x : K i, χ (Pi.mulSingle i x) ≠ 1}.Finite := by
  obtain ⟨γ, rfl⟩ := dualProdHom_surjective K hsep χ
  refine ((mem_restrictedDirectProduct_iff _ γ.1).1 γ.2).subset ?_
  rintro i ⟨x, hx⟩ h
  apply hx
  have : dualProdHom K γ (Pi.mulSingle i x) = (γ.1 i) x := dualProdChar_mulSingle K γ i x
  rw [this, h]
  rfl

end DualProd

section DualOfDiscrete

/-- Morris, Topology Without Tears, Theorem A5.11.8 (TP-591), unconditional case: for the duals
`Kᵢ = Dᵢ*` of discrete abelian groups (which are compact Hausdorff abelian groups whose characters
separate points), the dual of `∏ Dᵢ*` is the restricted direct product of the `Dᵢ**`. -/
@[kb "morris2024" "Theorem A5.11.8, p. 578"]
def dualProdEquivOfDualDiscrete {ι : Type*} (D : ι → Type*) [∀ i, CommGroup (D i)]
    [∀ i, TopologicalSpace (D i)] [∀ i, DiscreteTopology (D i)] :
    restrictedDirectProduct (fun i => PontryaginDual (PontryaginDual (D i))) ≃*
      PontryaginDual (∀ i, PontryaginDual (D i)) :=
  dualProdEquiv (fun i => PontryaginDual (D i)) fun i χ χ' hne => by
    obtain ⟨d, hd⟩ : ∃ d, χ d ≠ χ' d := by
      by_contra h
      push Not at h
      exact hne (PontryaginDual.ext h)
    exact ⟨evalAtPoint (D i) d, hd⟩

end DualOfDiscrete

/-! ### TP-593: the elementary case of bounded exponent -/

/-- Morris, Topology Without Tears, Theorem A5.11.11 (TP-593), prime exponent. An abelian group in
which every element has order dividing a prime `p` (no finiteness assumption) is isomorphic to a
restricted direct product (finitely supported functions) of copies of the cyclic group `Z(p)`: it is a
vector space over `ZMod p`. -/
@[kb "morris2024" "Theorem A5.11.11, p. 580"]
theorem exists_addEquiv_finsupp_zmod_of_prime_exponent (p : ℕ) [Fact p.Prime] (G : Type u)
    [AddCommGroup G] (h : ∀ g : G, p • g = 0) :
    ∃ ι : Type u, Nonempty (G ≃+ (ι →₀ ZMod p)) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : Module (ZMod p) G := AddCommGroup.zmodModule h
  let b := Module.Basis.ofVectorSpace (ZMod p) G
  exact ⟨_, ⟨b.repr.toAddEquiv⟩⟩

end

end UndergradKB.Topology
