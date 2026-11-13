import UndergradKB.Topology.GroupsMore
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Quotient
import UndergradKB.Common.Attr

/-!
# Local isomorphism of a group with `ℝⁿ` (for Morris, Proposition A5.12.10)

If a topological group `Q` has a discrete subgroup `D'` with `Q / D'` topologically isomorphic to
`Tⁿ × F`, `F` discrete, then `Q` is locally isomorphic to `ℝⁿ` (in the sense of
`LocallyIsomorphic`).
-/

open Topology Set Filter Real

set_option linter.unusedSectionVars false

namespace UndergradKB.Topology

/-- An open-on-subsets injective continuous map restricts to a homeomorphism of an open set onto its
image. -/
theorem exists_homeomorph_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (g : X → Y)
    (hg : Continuous g) (S : Set X) (hS : IsOpen S) (hinj : InjOn g S)
    (hopen : ∀ T, T ⊆ S → IsOpen T → IsOpen (g '' T)) :
    ∃ e : S ≃ₜ g '' S, ∀ x : S, ((e x : g '' S) : Y) = g x := by
  let e0 : S ≃ g '' S := Equiv.Set.imageOfInjOn g S hinj
  have hc : Continuous e0 := Continuous.subtype_mk (hg.comp continuous_subtype_val) _
  have ho : IsOpenMap e0 := by
    intro O hO
    obtain ⟨O', hO', rfl⟩ := isOpen_induced_iff.1 hO
    refine isOpen_induced_iff.2 ⟨g '' (O' ∩ S), hopen _ inter_subset_right (hO'.inter hS), ?_⟩
    ext ⟨y, hy⟩
    constructor
    · rintro ⟨x, hxO, hxy⟩
      exact ⟨⟨x, hxO.2⟩, hxO.1, Subtype.ext hxy⟩
    · rintro ⟨x, hxO, hxy⟩
      exact ⟨x, ⟨hxO, x.2⟩, congrArg Subtype.val hxy⟩
  exact ⟨e0.toHomeomorphOfContinuousOpen hc ho, fun x => rfl⟩

/-- Lifting a local isomorphism through a continuous open homomorphism that is injective near `1`. -/
theorem locallyIsomorphic_of_lift {A Q R : Type*} [Group A] [Group Q] [Group R]
    [TopologicalSpace A] [TopologicalSpace Q] [TopologicalSpace R] [IsTopologicalGroup Q]
    (p : Q →* R) (hpc : Continuous p) (hpo : IsOpenMap p) (ρ : A →* R) (hρc : Continuous ρ)
    (N : Set A) (hNo : IsOpen N) (h1N : (1 : A) ∈ N) (hρinj : InjOn ρ N)
    (hρopen : ∀ S, S ⊆ N → IsOpen S → IsOpen (ρ '' S))
    (W1 : Set Q) (hW1o : IsOpen W1) (h1W1 : (1 : Q) ∈ W1) (hpinj : InjOn p W1) :
    LocallyIsomorphic A Q := by
  obtain ⟨V, hV, hVW⟩ := exists_nhds_one_split (hW1o.mem_nhds h1W1)
  let W0 : Set Q := interior V ∩ W1
  have hW0o : IsOpen W0 := isOpen_interior.inter hW1o
  have h1W0 : (1 : Q) ∈ W0 := ⟨mem_interior_iff_mem_nhds.2 hV, h1W1⟩
  have hW0W1 : W0 ⊆ W1 := inter_subset_right
  have hW0mul : ∀ a ∈ W0, ∀ b ∈ W0, a * b ∈ W1 := fun a ha b hb =>
    hVW a (interior_subset ha.1) b (interior_subset hb.1)
  let Vs : Set A := N ∩ ρ ⁻¹' (p '' W0)
  have hVso : IsOpen Vs := hNo.inter ((hpo _ hW0o).preimage hρc)
  have h1Vs : (1 : A) ∈ Vs := ⟨h1N, ⟨1, h1W0, by rw [map_one, map_one]⟩⟩
  let Us : Set Q := W0 ∩ p ⁻¹' (ρ '' Vs)
  have hρVs : IsOpen (ρ '' Vs) := hρopen _ inter_subset_left hVso
  have hUso : IsOpen Us := hW0o.inter (hρVs.preimage hpc)
  have h1Us : (1 : Q) ∈ Us := ⟨h1W0, ⟨1, h1Vs, by rw [map_one, map_one]⟩⟩
  obtain ⟨e1, he1⟩ := exists_homeomorph_image ρ hρc Vs hVso (hρinj.mono inter_subset_left)
    (fun T hT hTo => hρopen T (hT.trans inter_subset_left) hTo)
  obtain ⟨e2, he2⟩ := exists_homeomorph_image p hpc Us hUso
    (hpinj.mono (inter_subset_left.trans hW0W1)) (fun T _ hTo => hpo T hTo)
  have hEq : p '' Us = ρ '' Vs := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu.2
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨w, hw, hwx⟩ := hx.2
      exact ⟨w, ⟨hw, ⟨x, hx, hwx.symm⟩⟩, hwx⟩
  let f : Vs ≃ₜ Us := e1.trans ((Homeomorph.setCongr hEq.symm).trans e2.symm)
  have hkey : ∀ x : Vs, p ((f x : Us) : Q) = ρ (x : A) := by
    intro x
    have h1 : ((e2 (e2.symm (Homeomorph.setCongr hEq.symm (e1 x))) : p '' Us) : R) =
        ((Homeomorph.setCongr hEq.symm (e1 x) : p '' Us) : R) := by
      rw [e2.apply_symm_apply]
    rw [he2] at h1
    exact h1.trans (he1 x)
  refine ⟨Vs, Us, f, hVso.mem_nhds h1Vs, hUso.mem_nhds h1Us, ?_⟩
  intro x y hxy
  have ha : ((f x : Us) : Q) ∈ W0 := (f x).2.1
  have hb : ((f y : Us) : Q) ∈ W0 := (f y).2.1
  have hc : ((f ⟨(x : A) * y, hxy⟩ : Us) : Q) ∈ W0 := (f ⟨(x : A) * y, hxy⟩).2.1
  apply hpinj (hW0W1 hc) (hW0mul _ ha _ hb)
  calc p ((f ⟨(x : A) * y, hxy⟩ : Us) : Q) = ρ ((x : A) * y) := hkey ⟨(x : A) * y, hxy⟩
    _ = ρ x * ρ y := map_mul ρ _ _
    _ = p ((f x : Us) : Q) * p ((f y : Us) : Q) := by rw [hkey x, hkey y]
    _ = p (((f x : Us) : Q) * ((f y : Us) : Q)) := (map_mul p _ _).symm

/-- If `Q` has a discrete subgroup `D'` with `Q / D' ≃ₜ* Tⁿ × F` (`F` discrete), then `Q` is locally
isomorphic to `ℝⁿ` (Morris, Exercises A5.5 #7 and Proposition A5.5.23, used in the proof of
Proposition A5.12.10). -/
theorem locallyIsomorphic_real_pow_of_discrete_quotient_torus (n : ℕ) {Q : Type*} [CommGroup Q]
    [TopologicalSpace Q] [IsTopologicalGroup Q] (D' : Subgroup Q) [DiscreteTopology D']
    {F : Type*} [CommGroup F] [TopologicalSpace F] [DiscreteTopology F]
    (T : (Q ⧸ D') ≃ₜ* (Fin n → Circle) × F) :
    LocallyIsomorphic (Multiplicative (Fin n → ℝ)) Q := by
  classical
  -- a neighbourhood on which the quotient map is injective
  obtain ⟨O, hOo, hO⟩ := isOpen_induced_iff.1 (isOpen_discrete ({1} : Set D'))
  have h1O : (1 : Q) ∈ O := by
    have : (1 : D') ∈ ((↑) : D' → Q) ⁻¹' O := by rw [hO]; rfl
    exact this
  have hDO : ∀ d ∈ D', d ∈ O → d = 1 := by
    intro d hd hdO
    have : (⟨d, hd⟩ : D') ∈ ((↑) : D' → Q) ⁻¹' O := hdO
    rw [hO, Set.mem_singleton_iff] at this
    exact congrArg Subtype.val this
  obtain ⟨V, hV, hVO⟩ := exists_nhds_one_split (hOo.mem_nhds h1O)
  have hW1n : V ∩ V⁻¹ ∈ 𝓝 (1 : Q) := inter_mem hV (inv_mem_nhds_one Q hV)
  have hW1inj : InjOn (QuotientGroup.mk' D') (interior (V ∩ V⁻¹)) := by
    intro a ha b hb hab
    have hmem : a⁻¹ * b ∈ D' := QuotientGroup.eq.1 hab
    have ha' : a⁻¹ ∈ V := (interior_subset ha).2
    have hb' : b ∈ V := (interior_subset hb).1
    have : a⁻¹ * b = 1 := hDO _ hmem (hVO _ ha' _ hb')
    exact inv_mul_eq_one.1 this
  -- the exponential map
  let expHom : Multiplicative (Fin n → ℝ) →* (Fin n → Circle) :=
    { toFun := fun x i => Circle.exp (2 * Real.pi * Multiplicative.toAdd x i)
      map_one' := by funext i; simp
      map_mul' := fun x y => by funext i; simp [mul_add, Circle.exp_add] }
  have hexp1 : IsOpenMap (fun t : ℝ => Circle.exp (2 * Real.pi * t)) :=
    isLocalHomeomorph_circleExp.isOpenMap.comp
      (Homeomorph.mulLeft₀ (2 * Real.pi) (by positivity)).isOpenMap
  have hexpo : IsOpenMap expHom := by
    show IsOpenMap (Pi.map fun _ : Fin n => fun t : ℝ => Circle.exp (2 * Real.pi * t))
    refine IsOpenMap.piMap (fun _ => hexp1) (Filter.Eventually.of_forall fun _ z => ?_)
    obtain ⟨s, hs⟩ := Circle.exp_surjective z
    exact ⟨s / (2 * Real.pi), by
      show Circle.exp (2 * Real.pi * (s / (2 * Real.pi))) = z
      rw [mul_div_cancel₀ _ (by positivity), hs]⟩
  have hexpc : Continuous expHom := by
    show Continuous (fun x : Fin n → ℝ => fun i => Circle.exp (2 * Real.pi * x i))
    exact continuous_pi fun i => Circle.exp.continuous.comp
      (continuous_const.mul (continuous_apply i))
  have hι : IsOpenMap (fun z : Fin n → Circle => (z, (1 : F))) := by
    intro U hU
    have : (fun z : Fin n → Circle => (z, (1 : F))) '' U = U ×ˢ ({1} : Set F) := by
      ext ⟨z, f⟩
      simp [eq_comm]
    rw [this]
    exact hU.prod (isOpen_discrete _)
  let ρ : Multiplicative (Fin n → ℝ) →* Q ⧸ D' :=
    T.symm.toMulEquiv.toMonoidHom.comp ((MonoidHom.inl _ F).comp expHom)
  have hρc : Continuous ρ :=
    T.symm.continuous.comp ((continuous_id.prodMk continuous_const).comp hexpc)
  have hρo : IsOpenMap ρ := (T.symm.toHomeomorph.isOpenMap).comp (hι.comp hexpo)
  have hNo : IsOpen (Set.pi (Set.univ : Set (Fin n)) fun _ => Ioo (-(1 / 2 : ℝ)) (1 / 2)) :=
    isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo
  have hρinj : InjOn ρ (Set.pi (Set.univ : Set (Fin n)) fun _ => Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro x hx y hy hxy
    have h1 : expHom x = expHom y := by
      have := T.symm.injective hxy
      exact (Prod.mk.inj this).1
    funext i
    have hi := congrFun h1 i
    have hxi : -(1 / 2 : ℝ) < Multiplicative.toAdd x i ∧ Multiplicative.toAdd x i < 1 / 2 :=
      hx i (mem_univ i)
    have hyi : -(1 / 2 : ℝ) < Multiplicative.toAdd y i ∧ Multiplicative.toAdd y i < 1 / 2 :=
      hy i (mem_univ i)
    have hinj := Circle.exp_injOn_of_forall_sub_mem_Ioo (s := Ioo (-Real.pi) Real.pi) (by
      intro u hu v hv
      constructor <;> linarith [hu.1, hu.2, hv.1, hv.2, Real.pi_pos])
    have hpi := Real.pi_pos
    have hxm : 2 * Real.pi * Multiplicative.toAdd x i ∈ Ioo (-Real.pi) Real.pi :=
      ⟨by nlinarith [hxi.1], by nlinarith [hxi.2]⟩
    have hym : 2 * Real.pi * Multiplicative.toAdd y i ∈ Ioo (-Real.pi) Real.pi :=
      ⟨by nlinarith [hyi.1], by nlinarith [hyi.2]⟩
    have := hinj hxm hym hi
    exact mul_left_cancel₀ (by positivity) this
  exact locallyIsomorphic_of_lift (QuotientGroup.mk' D') QuotientGroup.continuous_mk
    QuotientGroup.isOpenMap_coe ρ hρc
    (Set.pi (Set.univ : Set (Fin n)) fun _ => Ioo (-(1 / 2 : ℝ)) (1 / 2)) hNo
    (fun i _ => (⟨by norm_num, by norm_num⟩ : (0 : ℝ) ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2))) hρinj (fun S _ hS => hρo S hS)
    (interior (V ∩ V⁻¹)) isOpen_interior (mem_interior_iff_mem_nhds.2 hW1n) hW1inj

end UndergradKB.Topology
