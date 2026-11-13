import UndergradKB.Topology.PeterWeylAbelian2
import UndergradKB.Topology.DualityDiscrete2
import UndergradKB.Topology.DualityDiscrete
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import UndergradKB.Common.Attr

/-!
# Characters and duality for compact abelian groups (Appendix 5 of Morris)

From `PeterWeyl.exists_char_ne_one_of_measure` (the characters of a compact Hausdorff abelian group
separate points, proved by the spectral theorem for compact self-adjoint operators on `L²`):

* Corollary A5.10.2 (TP-581) and Corollary A5.10.3 (TP-582): enough characters; a compact Hausdorff
  abelian group is a closed subgroup of a power of the circle;
* separation of a point from a closed subgroup by a character (used for Propositions A5.11.1,
  A5.14.2 and Theorem A5.12.4);
* Proposition A5.11.1 (TP-584): in a discrete abelian group, a subgroup of the dual separating points
  is dense;
* Theorem A5.11.2 (TP-585): Pontryagin-van Kampen duality for compact Hausdorff abelian groups;
* Corollary A5.11.4 (TP-587): characters of a compact subgroup extend;
* Theorem A5.12.4 (TP-597): monothetic compact groups;
* Proposition A5.14.2 (TP-618), compact case: the annihilator of the annihilator of a closed
  subgroup is the subgroup.
-/

open Topology Set MeasureTheory

set_option linter.unusedSectionVars false

universe u

namespace UndergradKB.Topology

section Compact

variable {K : Type u} [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [T2Space K]

/-- A nontrivial element of a compact Hausdorff abelian group is moved by some character. -/
theorem exists_char_ne_one_of_compact {g : K} (hg : g ≠ 1) : ∃ χ : PontryaginDual K, χ g ≠ 1 := by
  borelize K
  exact PeterWeyl.exists_char_ne_one_of_measure Measure.haar hg

/-- Morris, Topology Without Tears, Corollary A5.10.2 (TP-581). A compact Hausdorff abelian group has
enough continuous characters to separate its points. -/
@[kb "morris2024" "Corollary A5.10.2, p. 572"]
theorem characters_separate_points_of_compact {x y : K} (hxy : x ≠ y) :
    ∃ χ : PontryaginDual K, χ x ≠ χ y := by
  obtain ⟨χ, hχ⟩ := exists_char_ne_one_of_compact (g := x * y⁻¹)
    (fun h => hxy (mul_inv_eq_one.1 h))
  refine ⟨χ, fun h => hχ ?_⟩
  rw [map_mul, map_inv, h, mul_inv_cancel]

/-- The map of `K` into the product of circles indexed by its characters. -/
noncomputable def evalChars' (K : Type*) [CommGroup K] [TopologicalSpace K] :
    K →* (PontryaginDual K → Circle) where
  toFun x χ := χ x
  map_one' := by funext χ; exact map_one χ
  map_mul' x y := by funext χ; exact map_mul χ x y

/-- Morris, Topology Without Tears, Corollary A5.10.3 (TP-582). A compact Hausdorff abelian group is
topologically isomorphic to a closed subgroup of a product of copies of the circle: the evaluation map
into `Circle ^ (dual group)` is a closed embedding (and a homomorphism). -/
@[kb "morris2024" "Corollary A5.10.3, p. 573"]
theorem isClosedEmbedding_evalChars' : IsClosedEmbedding (evalChars' K) := by
  refine Continuous.isClosedEmbedding (continuous_pi fun χ => χ.continuous) ?_
  intro x y hxy
  by_contra hne
  obtain ⟨χ, hχ⟩ := characters_separate_points_of_compact hne
  exact hχ (congrFun hxy χ)

/-- Morris, Topology Without Tears, Corollary A5.10.3 (TP-582), existence form. -/
@[kb "morris2024" "Corollary A5.10.3, p. 573"]
theorem exists_isClosedEmbedding_circle_pow :
    ∃ (ι : Type u) (f : K →* (ι → Circle)), IsClosedEmbedding f :=
  ⟨_, evalChars' K, isClosedEmbedding_evalChars'⟩

/-- A point outside a closed subgroup of a compact Hausdorff abelian group is separated from it by a
character trivial on the subgroup. -/
theorem exists_char_trivial_on_ne (H : Subgroup K) (hH : IsClosed (H : Set K)) {x : K}
    (hx : x ∉ H) : ∃ χ : PontryaginDual K, (∀ h ∈ H, χ h = 1) ∧ χ x ≠ 1 := by
  have : IsClosed (H : Set K) := hH
  have hmk : (QuotientGroup.mk x : K ⧸ H) ≠ 1 := by
    rwa [Ne, QuotientGroup.eq_one_iff]
  obtain ⟨ψ, hψ⟩ := exists_char_ne_one_of_compact hmk
  let q : K →ₜ* K ⧸ H := ⟨QuotientGroup.mk' H, continuous_quot_mk⟩
  refine ⟨ψ.comp q, fun h hh => ?_, hψ⟩
  show ψ (QuotientGroup.mk h) = 1
  rw [(QuotientGroup.eq_one_iff h).2 hh, map_one]

/-- The annihilator in the dual of a set of elements. -/
def annihilator (S : Set K) : Set (PontryaginDual K) := {χ | ∀ x ∈ S, χ x = 1}

/-- The annihilator in the group of a set of characters. -/
def coannihilator (T : Set (PontryaginDual K)) : Set K := {x | ∀ χ ∈ T, χ x = 1}

/-- Morris, Topology Without Tears, Proposition A5.14.2 (TP-618), for compact Hausdorff abelian
groups: the annihilator of the annihilator of a closed subgroup `H` is `H`. -/
@[kb "morris2024" "Proposition A5.14.2, p. 603"]
theorem coannihilator_annihilator (H : Subgroup K) (hH : IsClosed (H : Set K)) :
    coannihilator (annihilator (H : Set K)) = H := by
  ext x
  constructor
  · intro hx
    by_contra hxH
    obtain ⟨χ, hχH, hχx⟩ := exists_char_trivial_on_ne H hH hxH
    exact hχx (hx χ hχH)
  · intro hx χ hχ
    exact hχ x hx

end Compact

section DiscreteDense

variable {D : Type*} [CommGroup D] [TopologicalSpace D] [DiscreteTopology D]

/-- Morris, Topology Without Tears, Proposition A5.11.1 (TP-584). In a discrete abelian group, a
subgroup of the dual group that separates points is dense in the dual. -/
@[kb "morris2024" "Proposition A5.11.1, p. 575"]
theorem dense_of_separatesPoints_discrete (S : Subgroup (PontryaginDual D))
    (hS : ∀ x y : D, x ≠ y → ∃ χ ∈ S, χ x ≠ χ y) : Dense (S : Set (PontryaginDual D)) := by
  have : IsTopologicalGroup D := ⟨⟩
  let H := S.topologicalClosure
  have hHc : IsClosed (H : Set (PontryaginDual D)) := S.isClosed_topologicalClosure
  rw [dense_iff_closure_eq]
  by_contra hne
  obtain ⟨Φ, hΦ⟩ : ∃ Φ, Φ ∉ closure (S : Set (PontryaginDual D)) := by
    by_contra h
    push Not at h
    exact hne (eq_univ_of_forall h)
  have hΦH : Φ ∉ H := by rwa [← SetLike.mem_coe, Subgroup.topologicalClosure_coe]
  obtain ⟨Ψ, hΨH, hΨΦ⟩ := exists_char_trivial_on_ne H hHc hΦH
  obtain ⟨d, hd⟩ := toDualDual_surjective D Ψ
  have hd1 : d ≠ 1 := by
    rintro rfl
    apply hΨΦ
    rw [← hd, map_one]
    rfl
  obtain ⟨χ, hχS, hχ⟩ := hS d 1 hd1
  apply hχ
  have h1 : Ψ χ = 1 := hΨH χ (S.le_topologicalClosure hχS)
  rw [← hd] at h1
  rw [map_one]
  exact h1

end DiscreteDense

end UndergradKB.Topology
