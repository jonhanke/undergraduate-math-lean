import UndergradKB.Topology.LCASeparation
import UndergradKB.Topology.DualityCompact2
import UndergradKB.Topology.GroupsMore2
import UndergradKB.Common.Attr

/-!
# Wave 2: consequences of enough characters for locally compact abelian groups (Morris, Appendix 5)

* Proposition A5.14.2 (TP-618) for closed subgroups of locally compact Hausdorff abelian groups;
* the Bohr compactification (TP-611): `bohrMap` is injective for locally compact Hausdorff abelian groups
  and has dense image for every abelian topological group;
* Corollaries A5.11.4 and A5.11.5 (TP-587, TP-588) without the separation hypothesis.
-/

open Set

universe u

namespace UndergradKB.Topology

namespace LCA

section Annihilators

variable {G : Type u} [CommGroup G] [TopologicalSpace G]

/-- The annihilator in the dual group of a set of elements. -/
def annihilator (S : Set G) : Set (PontryaginDual G) := {χ | ∀ x ∈ S, χ x = 1}

/-- The annihilator in the group of a set of characters. -/
def coannihilator (T : Set (PontryaginDual G)) : Set G := {x | ∀ χ ∈ T, χ x = 1}

end Annihilators

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G]

/-- Morris, Topology Without Tears, Proposition A5.14.2 (TP-618). In a locally compact Hausdorff
abelian group the annihilator of the annihilator of a closed subgroup `H` is `H`. -/
@[kb "morris2024" "Proposition A5.14.2, p. 603"]
theorem coannihilator_annihilator (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    coannihilator (annihilator (H : Set G)) = H := by
  ext x
  constructor
  · intro hx
    by_contra hxH
    obtain ⟨χ, hχH, hχx⟩ := exists_char_trivial_on_ne_of_LCA H hH hxH
    exact hχx (hx χ hχH)
  · intro hx χ hχ
    exact hχ x hx

end LCA

/-- Morris, Topology Without Tears, Exercises A5.13 #6 (TP-611). For a locally compact Hausdorff
abelian group the canonical map `G → bG` into the Bohr compactification is injective. -/
@[kb "morris2024" "Exercises A5.13, p. 600"]
theorem injective_bohrMap_of_LCA (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] : Function.Injective (bohrMap G) :=
  (injective_bohrMap_iff G).2 fun _ _ hgh => LCA.characters_separate_points_of_LCA hgh

/-- Morris, Topology Without Tears, Exercises A5.13 #6 (TP-611). For every abelian topological group
`G`, the image of `G` in its Bohr compactification is dense (the image is a subgroup of the dual of the
discrete group `Γ_d` and separates the points of `Γ_d`). -/
@[kb "morris2024" "Exercises A5.13, p. 600"]
theorem dense_range_bohrMap (G : Type u) [CommGroup G] [TopologicalSpace G] :
    Dense (range (bohrMap G)) := by
  let S : Subgroup (BohrCompactification G) := (bohrMap G).toMonoidHom.range
  have hS : ∀ x y : WithDiscreteTopology (PontryaginDual G), x ≠ y → ∃ χ ∈ S, χ x ≠ χ y := by
    intro x y hxy
    have : ∃ g : G, (ofDiscreteDual G x) g ≠ (ofDiscreteDual G y) g := by
      by_contra hc
      push Not at hc
      exact hxy (PontryaginDual.ext hc)
    obtain ⟨g, hg⟩ := this
    exact ⟨bohrMap G g, ⟨g, rfl⟩, hg⟩
  exact dense_of_separatesPoints_discrete S hS

/-- Morris, Topology Without Tears, Corollary A5.11.4 (TP-587). In a locally compact Hausdorff abelian
group every character of a compact subgroup extends to the group. -/
@[kb "morris2024" "Corollary A5.11.4, p. 576"]
theorem exists_extend_char_of_compact_subgroup_LCA {B : Type u} [CommGroup B] [TopologicalSpace B]
    [IsTopologicalGroup B] [T2Space B] [LocallyCompactSpace B]
    (K : Subgroup B) (hK : IsCompact (K : Set B)) (ψ : PontryaginDual K) :
    ∃ χ : PontryaginDual B, ∀ k : K, χ k = ψ k :=
  exists_extend_char_of_compact_subgroup (fun _ _ hxy => LCA.characters_separate_points_of_LCA hxy)
    K hK ψ

/-- Morris, Topology Without Tears, Corollary A5.11.5 (TP-588). A continuous one-one homomorphism `f` of
a compact Hausdorff abelian group `A` into a locally compact Hausdorff abelian group `B` has onto dual map
`f* : B* → A*`, which is a quotient map onto the discrete group `A*`. -/
@[kb "morris2024" "Corollary A5.11.5, p. 576"]
theorem PontryaginDual_map_surjective_isQuotientMap_of_injective_LCA {A B : Type*} [CommGroup A]
    [TopologicalSpace A] [IsTopologicalGroup A] [CompactSpace A] [T2Space A] [CommGroup B]
    [TopologicalSpace B] [IsTopologicalGroup B] [T2Space B] [LocallyCompactSpace B] (f : A →ₜ* B)
    (hf : Function.Injective f) :
    Function.Surjective (PontryaginDual.map f) ∧ Topology.IsQuotientMap (PontryaginDual.map f) :=
  PontryaginDual_map_surjective_isQuotientMap_of_injective_compact f hf
    fun _ _ hxy => LCA.characters_separate_points_of_LCA hxy

end UndergradKB.Topology
