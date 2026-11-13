import Mathlib.RingTheory.IntegralDomain
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Analysis.Complex.Circle
import UndergradKB.Topology.GroupsBounded3
import UndergradKB.Topology.GroupsMore2
import UndergradKB.Topology.DualityDiscrete2
import UndergradKB.Topology.DualityDiscrete4
import UndergradKB.Topology.DualityCompact3
import UndergradKB.Topology.ClassicalDuals
import UndergradKB.Topology.DualityPlumbing
import UndergradKB.Common.Attr

/-!
# Compact abelian torsion groups are products of finite cyclic groups

Morris, *Topology Without Tears* (2024), Theorem A5.11.12 (`morris2024`).  With the bounded exponent and the
structure `G^ ≃ ⨁ Z(mᵢ)` of the dual of `GroupsBounded3`: the dual `G^` is discrete, so it is topologically
isomorphic to the dual of the compact group `Q = ∏ (Z(mᵢ))^` (dual of the restricted direct sum), and
duality for the compact groups `G` and `Q` gives `G ≃ₜ Q`; the dual of a finite cyclic group is cyclic.
-/

universe u

open Function Set Topology

namespace UndergradKB.Topology

/-- The dual of a finite cyclic discrete group is cyclic: a character is determined by its value at a
generator, which is a root of unity, and finite subgroups of `ℂˣ` are cyclic. -/
theorem isCyclic_dual_of_isCyclic {A : Type*} [CommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [Finite A] [hA : IsCyclic A] : IsCyclic (PontryaginDual A) := by
  obtain ⟨g, hg⟩ := hA.exists_generator
  let ev : PontryaginDual A →* Circle :=
    { toFun := fun χ => χ g
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hev : Injective ev := by
    intro χ ψ h
    apply PontryaginDual.ext
    intro a
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
    have : χ g = ψ g := h
    show χ (g ^ k) = ψ (g ^ k)
    rw [map_zpow, map_zpow, this]
  exact isCyclic_of_injective_ringHom (Circle.coeHom.comp ev) (Circle.coe_injective.comp hev)

/-- A multiplicative equivalence of restricted direct products from coordinatewise ones. -/
noncomputable def restrictedDirectProduct_congr {ι : Type*} {X Y : ι → Type*} [∀ i, CommGroup (X i)]
    [∀ i, CommGroup (Y i)] (e : ∀ i, X i ≃* Y i) :
    restrictedDirectProduct X ≃* restrictedDirectProduct Y where
  toFun x := ⟨fun i => e i (x.1 i), x.2.subset fun i hi h => hi (by simp [h])⟩
  invFun y := ⟨fun i => (e i).symm (y.1 i), y.2.subset fun i hi h => hi (by simp [h])⟩
  left_inv x := Subtype.ext (funext fun i => (e i).symm_apply_apply _)
  right_inv y := Subtype.ext (funext fun i => (e i).apply_symm_apply _)
  map_mul' x y := Subtype.ext (funext fun i => map_mul (e i) _ _)

/-- The restricted direct product of the cyclic groups is the direct sum. -/
noncomputable def mulEquivRestrictedDirectProduct {ι : Type*} (m : ι → ℕ) :
    Multiplicative (DirectSum ι (fun i => ZMod (m i))) ≃*
      restrictedDirectProduct (fun i => Multiplicative (ZMod (m i))) := by
  classical
  have hfin : ∀ d : Multiplicative (DirectSum ι (fun i => ZMod (m i))),
      (fun i => Multiplicative.ofAdd ((Multiplicative.toAdd d) i)) ∈
        restrictedDirectProduct (fun i => Multiplicative (ZMod (m i))) := by
    intro d
    refine (DFinsupp.support (Multiplicative.toAdd d)).finite_toSet.subset fun i hi => ?_
    simp only [Finset.mem_coe, DFinsupp.mem_support_toFun]
    intro h
    exact hi (by simp [h])
  let f : Multiplicative (DirectSum ι (fun i => ZMod (m i))) →*
      restrictedDirectProduct (fun i => Multiplicative (ZMod (m i))) :=
    { toFun := fun d => ⟨fun i => Multiplicative.ofAdd ((Multiplicative.toAdd d) i), hfin d⟩
      map_one' := Subtype.ext (by funext i; rfl)
      map_mul' := fun a b => Subtype.ext (by funext i; rfl) }
  refine MulEquiv.ofBijective f ⟨?_, ?_⟩
  · intro a b hab
    have := congrArg (fun z => z.1) hab
    apply Multiplicative.toAdd.injective
    ext i
    exact congrFun this i
  · rintro ⟨g, hg⟩
    have hsupp : {i | Multiplicative.toAdd (g i) ≠ 0}.Finite :=
      hg.subset fun i hi => fun h => hi (by simp [h])
    refine ⟨Multiplicative.ofAdd
      (DFinsupp.mk hsupp.toFinset (fun i => Multiplicative.toAdd (g i.1))), ?_⟩
    apply Subtype.ext
    funext i
    simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, DFinsupp.mk_apply]
    by_cases hi : i ∈ hsupp.toFinset
    · simp only [hi, ↓reduceDIte]; rfl
    · simp only [hi, ↓reduceDIte]
      have : ¬ Multiplicative.toAdd (g i) ≠ 0 := by simpa using hi
      push Not at this
      exact (congrArg Multiplicative.ofAdd this).symm

/-- Morris, Topology Without Tears, Theorem A5.11.12 (TP-594). A compact Hausdorff abelian torsion group is
topologically isomorphic to a product of finite cyclic groups (with the discrete topology), and only finitely
many distinct orders occur. -/
@[kb "morris2024" "Theorem A5.11.12, p. 580"]
theorem compact_torsion_equiv_pi_cyclic {G : Type u} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] (h : ∀ g : G, IsOfFinOrder g) :
    ∃ (ι : Type u) (k : ι → ℕ), (∀ i, 0 < k i) ∧ (Set.range k).Finite ∧
      Nonempty (G ≃ₜ* ∀ i, WithDiscreteTopology (Multiplicative (ZMod (k i)))) := by
  classical
  obtain ⟨N, hN, hGN⟩ := exists_pow_eq_one_of_compact_torsion h
  obtain ⟨ι, m, hm, ⟨eD⟩⟩ := exists_mulEquiv_directSum_dual_of_compact_torsion h
  have hne : ∀ i, NeZero (m i) := fun i => ⟨(hm i).ne'⟩
  let C : ι → Type := fun i => WithDiscreteTopology (Multiplicative (ZMod (m i)))
  have hfin : ∀ i, Finite (C i) := fun i =>
    have := hne i
    inferInstanceAs (Finite (Multiplicative (ZMod (m i))))
  have hcomp : ∀ i, CompactSpace (C i) := fun i => have := hfin i; inferInstance
  have htg : ∀ i, IsTopologicalGroup (C i) := fun i => inferInstance
  -- the isomorphism `G^ ≃ (∏ (C i)^)^`, a topological one since both groups are discrete
  let Q := ∀ i, PontryaginDual (C i)
  have hdual : ∀ i, DualityHolds (C i) := fun i => dualityHolds_of_discrete (C i)
  choose eC heC using hdual
  let e1 : PontryaginDual G ≃* restrictedDirectProduct C :=
    eD.trans (mulEquivRestrictedDirectProduct m)
  let e2 : restrictedDirectProduct C ≃*
      restrictedDirectProduct (fun i => PontryaginDual (PontryaginDual (C i))) :=
    restrictedDirectProduct_congr (fun i => (eC i).toMulEquiv)
  let e3 := dualProdEquivOfDualDiscrete C
  let eDQ : PontryaginDual G ≃* PontryaginDual Q := e1.trans (e2.trans e3)
  let cme : PontryaginDual G ≃ₜ* PontryaginDual Q :=
    { toMulEquiv := eDQ
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  obtain ⟨eG, -⟩ := (dualityHolds_of_compact (K := G))
  obtain ⟨eQ, -⟩ := (dualityHolds_of_compact (K := Q))
  let eGQ : G ≃ₜ* Q := (eG.trans (dualCongr cme)).trans eQ.symm
  -- the duals of the cyclic groups are cyclic
  have hcyc : ∀ i, IsCyclic (PontryaginDual (C i)) := fun i => by
    have := hfin i
    have : IsCyclic (C i) := inferInstanceAs (IsCyclic (Multiplicative (ZMod (m i))))
    exact isCyclic_dual_of_isCyclic
  have hfin' : ∀ i, Finite (PontryaginDual (C i)) := fun i => by
    have := hfin i
    infer_instance
  let k : ι → ℕ := fun i => Nat.card (PontryaginDual (C i))
  let eP : ∀ i, Multiplicative (ZMod (k i)) ≃* PontryaginDual (C i) := fun i =>
    zmodCyclicMulEquiv (hcyc i)
  let W : ι → Type := fun i => WithDiscreteTopology (Multiplicative (ZMod (k i)))
  let F : ∀ i, PontryaginDual (C i) ≃ₜ* W i := fun i =>
    { toMulEquiv := (eP i).symm
      continuous_toFun := by
        have := hfin i
        exact continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  let eQW : Q ≃ₜ* ∀ i, W i :=
    { toMulEquiv := MulEquiv.piCongrRight (fun i => (F i).toMulEquiv)
      continuous_toFun := continuous_pi fun i => (F i).continuous.comp (continuous_apply i)
      continuous_invFun := continuous_pi fun i =>
        (F i).symm.continuous.comp (continuous_apply i) }
  let eGW : G ≃ₜ* ∀ i, W i := eGQ.trans eQW
  have hkpos : ∀ i, 0 < k i := fun i => by
    have := hfin' i
    exact Nat.card_pos
  refine ⟨ι, k, hkpos, ?_, ⟨eGW⟩⟩
  -- finitely many orders: each divides the exponent `N`
  refine (Nat.divisors N).finite_toSet.subset ?_
  rintro _ ⟨i, rfl⟩
  have hx : (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod (k i))) : ∀ j, W j) ^ N = 1 := by
    have := hGN (eGW.symm (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod (k i)))))
    have h2 := congrArg eGW this
    rw [map_pow, ContinuousMulEquiv.apply_symm_apply, map_one eGW] at h2
    exact h2
  have h3 : (Multiplicative.ofAdd (1 : ZMod (k i))) ^ N = 1 := by
    have := congrFun hx i
    have e : (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod (k i))) : ∀ j, W j) i =
        Multiplicative.ofAdd 1 := Pi.mulSingle_eq_same i _
    have e2 : ((Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod (k i))) : ∀ j, W j) ^ N) i =
        (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod (k i))) : ∀ j, W j) i ^ N := rfl
    rw [e2, e] at this
    exact this
  have h4 : ((N : ZMod (k i))) = 0 := by
    have h6 : Multiplicative.ofAdd (N • (1 : ZMod (k i))) = Multiplicative.ofAdd 0 := by
      rw [ofAdd_nsmul]; simpa using h3
    simpa using Multiplicative.ofAdd.injective h6
  have h5 := (ZMod.natCast_eq_zero_iff N (k i)).mp h4
  exact Finset.mem_coe.mpr (Nat.mem_divisors.mpr ⟨h5, hN.ne'⟩)

end UndergradKB.Topology
