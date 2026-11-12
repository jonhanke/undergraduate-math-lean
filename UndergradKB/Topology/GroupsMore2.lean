import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import UndergradKB.Topology.TopGroups
import UndergradKB.Topology.Characters
import UndergradKB.Common.Attr

/-!
# More on topological groups, part 2 (Morris, Topology Without Tears, Appendix 5)

Splitting off an open divisible subgroup, inverse limits, open compactly generated subgroups, and
the Bohr compactification as a definition.
-/

open Set Filter Topology Pointwise

universe u v

namespace UndergradKB.Topology

/-! ### TP-530: an open divisible subgroup splits off -/

section Split

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]

/-- Morris, Topology Without Tears, Proposition A5.3.8 (TP-530). If `H` is an open divisible
subgroup of an abelian topological group `G`, then `G` is topologically isomorphic to
`H × G ⧸ H` (the second factor is discrete); the isomorphism is `g ↦ (r g, g + H)` for a
retraction `r : G → H`. -/
@[kb "morris2024" "Proposition A5.3.8, p. 532"]
theorem exists_continuousAddEquiv_prod_quotient (H : AddSubgroup G) (hH : IsOpen (H : Set G))
    (hdiv : IsDivisibleGroup H) :
    ∃ e : G ≃ₜ+ (H × (G ⧸ H)), ∀ g : G, (e g).2 = QuotientAddGroup.mk g := by
  obtain ⟨r, hr⟩ := exists_addMonoidHom_extension hdiv H (AddMonoidHom.id H)
  have hr' : ∀ h : H, r h = h := fun h => by simpa using hr h
  have rcont : Continuous r := by
    refine continuous_of_continuousAt_zero r ?_
    have hc : ContinuousOn r (H : Set G) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have : (H : Set G).domRestrict r = id := by
        funext h; exact hr' h
      rw [this]; exact continuous_id
    exact hc.continuousAt (hH.mem_nhds H.zero_mem)
  have : DiscreteTopology (G ⧸ H) := QuotientAddGroup.discreteTopology hH
  let φ : G →+ G := AddMonoidHom.id G - H.subtype.comp r
  have hφ : ∀ x ∈ H, φ x = 0 := by
    intro x hx
    have := hr' ⟨x, hx⟩
    simp [φ, this]
  let s : G ⧸ H →+ G := QuotientAddGroup.lift H φ hφ
  have hs : ∀ g : G, s (QuotientAddGroup.mk g) = g - r g := fun g => rfl
  let e : G ≃+ (H × (G ⧸ H)) :=
    { toFun := fun g => (r g, QuotientAddGroup.mk g)
      invFun := fun p => (p.1 : G) + s p.2
      left_inv := fun g => by simp [hs]
      right_inv := by
        rintro ⟨h, q⟩
        obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective q
        refine Prod.ext ?_ ?_
        · show r ((h : G) + (g - r g)) = h
          rw [map_add, map_sub, hr' h, hr' (r g)]
          abel
        · show QuotientAddGroup.mk ((h : G) + (g - r g)) = QuotientAddGroup.mk g
          rw [QuotientAddGroup.eq]
          have : -((h : G) + (g - r g)) + g = -(h : G) + (r g : G) := by abel
          rw [this]
          exact H.add_mem (H.neg_mem h.2) (r g).2
      map_add' := fun a b => by
        ext <;> simp }
  refine ⟨{ toAddEquiv := e, continuous_toFun := ?_, continuous_invFun := ?_ }, fun g => rfl⟩
  · exact rcont.prodMk QuotientAddGroup.continuous_mk
  · show Continuous (fun p : H × (G ⧸ H) => (p.1 : G) + s p.2)
    exact (continuous_subtype_val.comp continuous_fst).add
      ((continuous_of_discreteTopology (f := s)).comp continuous_snd)

end Split

/-! ### TP-533: inverse limits -/

section InverseLimit

variable {ι : Type*} [Preorder ι] (G : ι → Type*) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]

/-- Morris, Topology Without Tears, §A5.4 (TP-533). Data of an inverse (projective) mapping system
of topological groups over a directed set: open continuous homomorphisms `f h : G j → G i` for
`i ≤ j`, compatible with composition. -/
structure IsInverseSystem (f : ∀ {i j : ι}, i ≤ j → (G j →ₜ* G i)) : Prop where
  directed : IsDirected ι (· ≤ ·)
  map_refl : ∀ (i : ι) (x : G i), f (le_refl i) x = x
  map_comp : ∀ {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k) (x : G k),
    f (hij.trans hjk) x = f hij (f hjk x)
  isOpenMap : ∀ {i j : ι} (h : i ≤ j), IsOpenMap (f h)

/-- Morris, Topology Without Tears, §A5.4 (TP-533). The inverse (projective) limit of a system:
the subgroup of the product of the elements `x` with `f h (x j) = x i` whenever `i ≤ j`. -/
def inverseLimit (f : ∀ {i j : ι}, i ≤ j → (G j →ₜ* G i)) : Subgroup (∀ i, G i) where
  carrier := {x | ∀ {i j : ι} (h : i ≤ j), f h (x j) = x i}
  one_mem' := fun h => map_one (f h)
  mul_mem' := fun ha hb i j h => by
    simp only [Pi.mul_apply, map_mul, ha h, hb h]
  inv_mem' := fun ha i j h => by
    simp only [Pi.inv_apply, map_inv, ha h]

/-- Morris, Topology Without Tears, Exercises A5.4 #6 (TP-533). The inverse limit of a system of
Hausdorff topological groups is a closed subgroup of the product. -/
@[kb "morris2024" "Exercises A5.4, p. 535"]
theorem isClosed_inverseLimit [∀ i, T2Space (G i)] (f : ∀ {i j : ι}, i ≤ j → (G j →ₜ* G i)) :
    IsClosed (inverseLimit G f : Set (∀ i, G i)) := by
  have : (inverseLimit G f : Set (∀ i, G i)) =
      ⋂ (i : ι) (j : ι) (h : i ≤ j), {x | f h (x j) = x i} := by
    ext x
    simp only [Set.mem_iInter]
    exact ⟨fun hx i j h => hx h, fun hx i j h => hx i j h⟩
  rw [this]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun h => ?_
  exact isClosed_eq ((map_continuous (f h)).comp (continuous_apply j)) (continuous_apply i)

end InverseLimit

/-! ### TP-601, TP-627: open compactly generated subgroups -/

section OpenCG

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- Morris, Topology Without Tears, Proposition A5.15.3 (TP-627). In a locally compact group every
compact subset lies in an open and closed compactly generated subgroup. -/
@[kb "morris2024" "Proposition A5.15.3, p. 609"]
theorem exists_isOpen_isClosed_isCompactlyGenerated_subgroup {K : Set G} (hK : IsCompact K) :
    ∃ H : Subgroup G, K ⊆ H ∧ IsOpen (H : Set G) ∧ IsClosed (H : Set G) ∧
      IsCompactlyGeneratedGroup H := by
  obtain ⟨V, hVc, hV⟩ := exists_compact_mem_nhds (1 : G)
  have hL : K ∪ V ∈ 𝓝 (1 : G) := Filter.mem_of_superset hV Set.subset_union_right
  have hopen := isOpen_closure_of_mem_nhds_one hL
  refine ⟨Subgroup.closure (K ∪ V), fun x hx => Subgroup.subset_closure (Or.inl hx), hopen,
    Subgroup.isClosed_of_isOpen _ hopen, ⟨Subtype.val ⁻¹' (K ∪ V), ?_,
    Subgroup.closure_closure_coe_preimage⟩⟩
  have himg : Subtype.val '' (Subtype.val ⁻¹' (K ∪ V) : Set (Subgroup.closure (K ∪ V))) = K ∪ V := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, Subgroup.subset_closure hx⟩, hx, rfl⟩
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, himg]
  exact hK.union hVc

/-- Morris, Topology Without Tears, Corollary A5.12.8 (TP-601). Every locally compact group has an
open (and closed) compactly generated subgroup. -/
@[kb "morris2024" "Corollary A5.12.8, p. 585"]
theorem exists_isOpen_isCompactlyGenerated_subgroup :
    ∃ H : Subgroup G, IsOpen (H : Set G) ∧ IsCompactlyGeneratedGroup H := by
  obtain ⟨H, -, ho, -, hc⟩ := exists_isOpen_isClosed_isCompactlyGenerated_subgroup
    (isCompact_empty : IsCompact (∅ : Set G))
  exact ⟨H, ho, hc⟩

end OpenCG

/-! ### TP-611: the Bohr compactification -/

section Bohr

/-- A copy of a type carrying the discrete topology (used to form `(Γ_d)*`). -/
def WithDiscreteTopology (X : Type*) : Type _ := X

instance (X : Type*) [CommGroup X] : CommGroup (WithDiscreteTopology X) :=
  inferInstanceAs (CommGroup X)

instance (X : Type*) : TopologicalSpace (WithDiscreteTopology X) := ⊥

instance (X : Type*) : DiscreteTopology (WithDiscreteTopology X) := ⟨rfl⟩

/-- Morris, Topology Without Tears, Exercises A5.13 #6 (TP-611). The Bohr compactification of an
abelian topological group `G`: the dual of the dual group `Γ` of `G` taken with the discrete
topology. -/
abbrev BohrCompactification (G : Type*) [CommGroup G] [TopologicalSpace G] : Type _ :=
  PontryaginDual (WithDiscreteTopology (PontryaginDual G))

variable (G : Type*) [CommGroup G] [TopologicalSpace G]

/-- A character of `G`, viewed as an element of the discrete copy of the dual group. -/
def toDiscreteDual (γ : PontryaginDual G) : WithDiscreteTopology (PontryaginDual G) := γ

/-- A point of the discrete copy of the dual group, viewed as a character of `G`. -/
def ofDiscreteDual (γ : WithDiscreteTopology (PontryaginDual G)) : PontryaginDual G := γ

/-- Morris, Topology Without Tears, Exercises A5.13 #6 (TP-611). The Bohr compactification is a
compact Hausdorff topological group. -/
@[kb "morris2024" "Exercises A5.13, p. 600"]
theorem bohr_compact_t2_topologicalGroup :
    CompactSpace (BohrCompactification G) ∧ T2Space (BohrCompactification G) ∧
      IsTopologicalGroup (BohrCompactification G) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- The canonical homomorphism `G → bG`, `β g γ = γ g`. -/
noncomputable def bohrMap : G →ₜ* BohrCompactification G where
  toFun g :=
    ({ toFun := fun γ => (ofDiscreteDual G γ) g
       map_one' := rfl
       map_mul' := fun _ _ => rfl
       continuous_toFun := continuous_of_discreteTopology } :
      WithDiscreteTopology (PontryaginDual G) →ₜ* Circle)
  map_one' := PontryaginDual.ext fun γ => map_one (ofDiscreteDual G γ)
  map_mul' g h := PontryaginDual.ext fun γ => map_mul (ofDiscreteDual G γ) g h
  continuous_toFun := by
    refine ContinuousMonoidHom.continuous_of_continuous_uncurry _ ?_
    refine continuous_prod_of_discrete_right.2 fun γ => ?_
    exact map_continuous (ofDiscreteDual G γ)

/-- Morris, Topology Without Tears, Exercises A5.13 #6 (TP-611). The canonical map `G → bG` is a
continuous homomorphism, and it is injective iff the characters of `G` separate points. -/
@[kb "morris2024" "Exercises A5.13, p. 600"]
theorem injective_bohrMap_iff :
    Function.Injective (bohrMap G) ↔
      ∀ g h : G, g ≠ h → ∃ γ : PontryaginDual G, γ g ≠ γ h := by
  constructor
  · intro hinj g h hgh
    by_contra hc
    push Not at hc
    exact hgh (hinj (PontryaginDual.ext fun γ => hc (ofDiscreteDual G γ)))
  · intro hsep g h he
    by_contra hne
    obtain ⟨γ, hγ⟩ := hsep g h hne
    exact hγ (DFunLike.congr_fun he (toDiscreteDual G γ))

end Bohr

end UndergradKB.Topology
