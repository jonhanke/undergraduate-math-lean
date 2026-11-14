import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.SetTheory.Cardinal.Arithmetic
import UndergradKB.Topology.CantorBrouwer
import UndergradKB.Common.Attr

/-! # Infinite profinite groups are Cantor cubes (Morris, Theorem A5.0.23, all weights)

* `nonempty_homeomorph_cantorCube_of_group` (Morris, Theorem A5.0.23, TP-496): the underlying space
  of an infinite, totally disconnected, compact (Hausdorff) group is homeomorphic to a Cantor cube
  `{0,1}^κ` for some infinite index set `κ`.  Wave 4 proved the metrizable case
  (`nonempty_homeomorph_cantor_of_group`); this file removes that restriction.

Proof (elementary, no continuous sections are needed).  Well-order the open normal subgroups
`U α` and put `N α = ⋂_{β < α} U β`.  For each `α` choose a representative `ρ α g` of the coset of
`g` modulo the open subgroup `N α ⊔ U α`, and send `g` to the coset of `(ρ α g)⁻¹ g` modulo `U α`;
this lies in the image `R α` of `N α` in `G ⧸ U α`.  The map `g ↦ (Ψ α g)_α` is a continuous
bijection `G → ∏_α R α` (injective by transfinite induction; surjective by compactness and
transfinite induction), hence a homeomorphism.  The factors are finite and discrete.  Dropping the
one-point factors and grouping the remaining (infinitely many) indices into countably infinite
blocks, each block is a countable product of finite discrete spaces with at least two points, which is
the Cantor space `ℕ → Bool` by Brouwer's theorem.
-/

open Set Filter Topology TopologicalSpace

namespace UndergradKB.Topology
namespace CantorCube

set_option linter.unusedSectionVars false

section Core

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {ι : Type*} (r : ι → ι → Prop) (U : ι → Subgroup G)

/-- `N α = ⋂_{β < α} U β`. -/
def N (α : ι) : Subgroup G := ⨅ (β : ι) (_ : r β α), U β

theorem mem_N {α : ι} {x : G} : x ∈ N r U α ↔ ∀ β, r β α → x ∈ U β := by
  simp [N, Subgroup.mem_iInf]

/-- The open subgroup `N α ⊔ U α`. -/
def V (α : ι) : Subgroup G := U α ⊔ N r U α

/-- A chosen representative of the coset `g (N α ⊔ U α)`. -/
noncomputable def ρ (α : ι) (g : G) : G := (QuotientGroup.mk g : G ⧸ V r U α).out

/-- The `α`-th coordinate: the coset of `(ρ α g)⁻¹ g` modulo `U α`. -/
noncomputable def Ψ (α : ι) (g : G) : G ⧸ U α := QuotientGroup.mk ((ρ r U α g)⁻¹ * g)

/-- The image of `N α` in `G ⧸ U α`. -/
def R (α : ι) : Set (G ⧸ U α) := QuotientGroup.mk '' (N r U α : Set G)

variable {r U}

theorem ρ_spec (α : ι) (g : G) : (ρ r U α g)⁻¹ * g ∈ V r U α := by
  have := Quotient.out_eq (QuotientGroup.mk g : G ⧸ V r U α)
  exact QuotientGroup.eq.1 this

theorem ρ_eq {α : ι} {x y : G} (h : x⁻¹ * y ∈ V r U α) : ρ r U α x = ρ r U α y := by
  unfold ρ
  rw [show (QuotientGroup.mk x : G ⧸ V r U α) = QuotientGroup.mk y from QuotientGroup.eq.2 h]

theorem Ψ_eq_of_mem_U {α : ι} {x y : G} (h : x⁻¹ * y ∈ U α) : Ψ r U α x = Ψ r U α y := by
  have hρ : ρ r U α x = ρ r U α y := ρ_eq (le_sup_left (a := U α) h)
  unfold Ψ
  rw [hρ, QuotientGroup.eq]
  simpa [mul_assoc] using h

theorem mem_U_of_Ψ_eq {α : ι} {x y : G} (hN : x⁻¹ * y ∈ N r U α) (h : Ψ r U α x = Ψ r U α y) :
    x⁻¹ * y ∈ U α := by
  have hρ : ρ r U α x = ρ r U α y := ρ_eq (le_sup_right (a := U α) hN)
  unfold Ψ at h
  rw [hρ, QuotientGroup.eq] at h
  simpa [mul_assoc] using h

variable (hUn : ∀ i, (U i).Normal) (hUo : ∀ i, IsOpen (U i : Set G))
include hUn

theorem N_normal (α : ι) : (N r U α).Normal := by
  unfold N
  exact Subgroup.normal_iInf_normal fun β => Subgroup.normal_iInf_normal fun _ => hUn β

theorem Ψ_mem_R (α : ι) (g : G) : Ψ r U α g ∈ R r U α := by
  have := N_normal (r := r) hUn α
  have h := ρ_spec (r := r) (U := U) α g
  unfold V at h
  rw [← SetLike.mem_coe, Subgroup.mul_normal] at h
  obtain ⟨u, hu, a, ha, hua⟩ := h
  -- `(ρ g)⁻¹ g = u a`; the coset of `u a` modulo `U` is that of `u a u⁻¹ ∈ N`.
  refine ⟨u * a * u⁻¹, this.conj_mem a ha u, ?_⟩
  unfold Ψ
  rw [← hua, QuotientGroup.eq]
  simpa [mul_assoc] using hu

/-- Moving inside a coset of `N α` to any prescribed value of the `α`-th coordinate. -/
theorem exists_mul_Ψ_eq (α : ι) (x : G) {q : G ⧸ U α} (hq : q ∈ R r U α) :
    ∃ m ∈ N r U α, Ψ r U α (x * m) = q := by
  have hNn := N_normal (r := r) hUn α
  obtain ⟨n, hn, rfl⟩ := hq
  have h := ρ_spec (r := r) (U := U) α x
  unfold V at h
  rw [← SetLike.mem_coe, Subgroup.mul_normal] at h
  obtain ⟨u, hu, a, ha, hua⟩ := h
  refine ⟨a⁻¹ * (u⁻¹ * n * u), (N r U α).mul_mem ((N r U α).inv_mem ha) ?_, ?_⟩
  · simpa using hNn.conj_mem n hn u⁻¹
  · have hρ : ρ r U α (x * (a⁻¹ * (u⁻¹ * n * u))) = ρ r U α x := by
      refine (ρ_eq ?_).symm
      have : x⁻¹ * (x * (a⁻¹ * (u⁻¹ * n * u))) = a⁻¹ * (u⁻¹ * n * u) := by group
      rw [this]
      exact le_sup_right (a := U α) ((N r U α).mul_mem ((N r U α).inv_mem ha)
        (by simpa using hNn.conj_mem n hn u⁻¹))
    unfold Ψ
    rw [hρ, QuotientGroup.eq]
    have e : (ρ r U α x)⁻¹ * (x * (a⁻¹ * (u⁻¹ * n * u))) = n * u := by
      rw [← mul_assoc, ← hua]; group
    rw [e]
    simpa using hu

omit hUn in
include hUo in
theorem continuous_Ψ (α : ι) : Continuous (Ψ r U α) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hmem : {y : G | x⁻¹ * y ∈ U α} ∈ 𝓝 x :=
    ((hUo α).preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)
  have : (fun _ => Ψ r U α x) =ᶠ[𝓝 x] Ψ r U α := by
    filter_upwards [hmem] with y hy
    exact Ψ_eq_of_mem_U hy
  exact continuousAt_const.congr this

/-! ### The coordinate map is a homeomorphism onto `∏_α R α` -/

variable [IsWellOrder ι r]

omit hUn in
theorem mem_N_of_Ψ_eq {x y : G} (h : ∀ α, Ψ r U α x = Ψ r U α y) (α : ι) :
    x⁻¹ * y ∈ N r U α := by
  induction α using (IsWellOrder.wf (r := r)).induction with | _ α ih => ?_
  rw [mem_N]
  intro β hβ
  exact mem_U_of_Ψ_eq (ih β hβ) (h β)

/-- The coordinate map `G → ∏_α R α`. -/
noncomputable def Φ (g : G) : ∀ α, R r U α := fun α => ⟨Ψ r U α g, Ψ_mem_R hUn α g⟩

omit hUn in
theorem K_anti {f : ∀ α, G ⧸ U α} {β γ : ι} (hβγ : r β γ) :
    {x : G | ∀ δ, (r δ γ ∨ δ = γ) → Ψ r U δ x = f δ} ⊆
      {x : G | ∀ δ, (r δ β ∨ δ = β) → Ψ r U δ x = f δ} := by
  intro x hx δ hδ
  rcases hδ with hδ | rfl
  · exact hx δ (Or.inl (_root_.trans hδ hβγ))
  · exact hx δ (Or.inl hβγ)

omit hUn in
include hUo in
theorem nonempty_biInter_K [CompactSpace G] {f : ∀ α, G ⧸ U α} (T : Set ι)
    (hT : ∀ β ∈ T, {x : G | ∀ δ, (r δ β ∨ δ = β) → Ψ r U δ x = f δ}.Nonempty) :
    (⋂ β ∈ T, {x : G | ∀ δ, (r δ β ∨ δ = β) → Ψ r U δ x = f δ}).Nonempty := by
  have hd : ∀ α, DiscreteTopology (G ⧸ U α) := fun α => QuotientGroup.discreteTopology (hUo α)
  rcases T.eq_empty_or_nonempty with rfl | hne
  · simp
  have : Nonempty T := hne.to_subtype
  rw [biInter_eq_iInter]
  have hcl : ∀ β : T, IsClosed {x : G | ∀ δ, (r δ β ∨ δ = β) → Ψ r U δ x = f δ} := by
    intro β
    have : {x : G | ∀ δ, (r δ β ∨ δ = β) → Ψ r U δ x = f δ} =
        ⋂ δ, ⋂ (_ : r δ β ∨ δ = β), {x : G | Ψ r U δ x = f δ} := by
      ext x; simp
    rw [this]
    exact isClosed_iInter fun δ => isClosed_iInter fun _ =>
      isClosed_eq (continuous_Ψ hUo δ) continuous_const
  refine IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _ ?_
    (fun β => hT β β.2) (fun β => (hcl β).isCompact) hcl
  intro a b
  rcases trichotomous_of r a.1 b.1 with h | h | h
  · exact ⟨b, K_anti h, le_rfl⟩
  · exact ⟨a, le_rfl, by rw [Subtype.ext h]⟩
  · exact ⟨a, le_rfl, K_anti h⟩

include hUo in
theorem Φ_surjective [CompactSpace G] : Function.Surjective (Φ (r := r) hUn) := by
  intro f
  let f' : ∀ α, G ⧸ U α := fun α => (f α : G ⧸ U α)
  have key : ∀ α, {x : G | ∀ δ, (r δ α ∨ δ = α) → Ψ r U δ x = f' δ}.Nonempty := by
    intro α
    induction α using (IsWellOrder.wf (r := r)).induction with | _ α ih => ?_
    obtain ⟨x, hx⟩ := nonempty_biInter_K hUo {β | r β α} ih
    rw [mem_iInter₂] at hx
    obtain ⟨m, hm, hΨ⟩ := exists_mul_Ψ_eq hUn α x (f α).2
    refine ⟨x * m, fun γ hγ => ?_⟩
    rcases hγ with hγ | rfl
    · rw [← Ψ_eq_of_mem_U (show x⁻¹ * (x * m) ∈ U γ by simpa using (mem_N r U).1 hm γ hγ)]
      exact hx γ hγ γ (Or.inr rfl)
    · exact hΨ
  obtain ⟨x, hx⟩ := nonempty_biInter_K hUo univ fun β _ => key β
  rw [mem_iInter₂] at hx
  exact ⟨x, funext fun α => Subtype.ext (hx α (mem_univ α) α (Or.inr rfl))⟩

omit hUo in
theorem Φ_injective (hsep : ∀ x : G, x ≠ 1 → ∃ i, x ∉ U i) :
    Function.Injective (Φ (r := r) hUn) := by
  intro x y hxy
  have h : ∀ α, Ψ r U α x = Ψ r U α y := fun α => congrArg Subtype.val (congrFun hxy α)
  by_contra hne
  have hne' : x⁻¹ * y ≠ 1 := by
    intro e
    exact hne (inv_mul_eq_one.1 e)
  obtain ⟨i, hi⟩ := hsep _ hne'
  exact hi (mem_U_of_Ψ_eq (mem_N_of_Ψ_eq h i) (h i))

include hUo in
/-- The coordinate map is a homeomorphism `G ≃ₜ ∏_α R α`. -/
theorem nonempty_homeomorph_pi [CompactSpace G] (hsep : ∀ x : G, x ≠ 1 → ∃ i, x ∉ U i) :
    Nonempty (G ≃ₜ ∀ α, R r U α) := by
  have hd : ∀ α, DiscreteTopology (G ⧸ U α) := fun α => QuotientGroup.discreteTopology (hUo α)
  have hc : Continuous (Φ (r := r) hUn) :=
    continuous_pi fun α => (continuous_Ψ hUo α).subtype_mk _
  exact ⟨hc.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ ⟨Φ_injective hUn hsep, Φ_surjective hUn hUo⟩)⟩

end Core

/-! ### Infinite products of finite discrete spaces are Cantor cubes -/

section Product

universe u v

variable {ι : Type u} (R : ι → Type v) [∀ i, TopologicalSpace (R i)] [∀ i, DiscreteTopology (R i)]
  [∀ i, Finite (R i)]

/-- A countable product of finite discrete spaces, each with at least two points, has no
isolated point. -/
theorem not_isOpen_singleton_pi (Y : ℕ → Type v) [∀ n, TopologicalSpace (Y n)]
    [∀ n, Nontrivial (Y n)] (x : ∀ n, Y n) : ¬ IsOpen ({x} : Set (∀ n, Y n)) := by
  intro ho
  let v : ∀ k, Y k := fun k => (exists_ne (x k)).choose
  let y : ℕ → ∀ n, Y n := fun k => Function.update x k (v k)
  have hy : Tendsto y atTop (𝓝 x) := by
    rw [tendsto_pi_nhds]
    intro n
    refine tendsto_atTop_of_eventually_const (i₀ := n + 1) fun k hk => ?_
    simp only [y]
    rw [Function.update_of_ne (by omega)]
  obtain ⟨k, hk⟩ := (hy.eventually (ho.mem_nhds rfl)).exists
  have := congrFun (hk : y k = x) k
  simp only [y, Function.update_self] at this
  exact (exists_ne (x k)).choose_spec this

/-- **Products of finite discrete spaces.**  An infinite product of nonempty finite discrete spaces
is homeomorphic to a Cantor cube `{0,1}^κ` with `κ` infinite. -/
theorem exists_homeomorph_cantorCube_pi [∀ i, Nonempty (R i)] [Infinite (∀ i, R i)] :
    ∃ κ : Type u, Infinite κ ∧ Nonempty ((∀ i, R i) ≃ₜ (κ → Bool)) := by
  classical
  let J := {i : ι // Nontrivial (R i)}
  -- drop the one-point factors
  let res : (∀ i, R i) → ∀ j : J, R j.1 := fun f j => f j.1
  have hres_inj : Function.Injective res := by
    intro f g hfg
    funext i
    by_cases hi : Nontrivial (R i)
    · exact congrFun hfg ⟨i, hi⟩
    · have : Subsingleton (R i) := not_nontrivial_iff_subsingleton.1 hi
      exact Subsingleton.elim _ _
  have hres_surj : Function.Surjective res := by
    intro h
    refine ⟨fun i => if hi : Nontrivial (R i) then h ⟨i, hi⟩ else Classical.arbitrary _, ?_⟩
    funext j
    simp only [res]
    split_ifs with hi
    · rfl
    · exact absurd j.2 hi
  have h1 : (∀ i, R i) ≃ₜ ∀ j : J, R j.1 :=
    (continuous_pi fun j => continuous_apply j.1).homeoOfEquivCompactToT2
      (f := Equiv.ofBijective res ⟨hres_inj, hres_surj⟩)
  have hJ : Infinite J := by
    by_contra hfin
    rw [not_infinite_iff_finite] at hfin
    have : Finite (∀ j : J, R j.1) := Pi.finite
    have := Finite.of_equiv _ h1.toEquiv.symm
    exact not_finite (∀ i, R i)
  -- group the coordinates into countably infinite blocks
  have hcard : Cardinal.mk (J × ℕ) = Cardinal.mk J := by
    rw [Cardinal.mk_prod, Cardinal.lift_uzero, Cardinal.mk_nat, Cardinal.lift_aleph0]
    exact Cardinal.mul_aleph0_eq (Cardinal.infinite_iff.1 hJ)
  obtain ⟨e⟩ := Cardinal.eq.1 hcard
  have h2 : (∀ j : J, R j.1) ≃ₜ ∀ p : J × ℕ, R (e p).1 :=
    (Homeomorph.piCongrLeft (Y := fun j : J => R j.1) e).symm
  let cur : (∀ p : J × ℕ, R (e p).1) ≃ ∀ j : J, ∀ n : ℕ, R (e (j, n)).1 :=
    { toFun := fun f j n => f (j, n)
      invFun := fun g p => g p.1 p.2
      left_inv := fun f => rfl
      right_inv := fun g => rfl }
  have h3 : (∀ p : J × ℕ, R (e p).1) ≃ₜ ∀ j : J, ∀ n : ℕ, R (e (j, n)).1 :=
    (continuous_pi fun j => continuous_pi fun n => continuous_apply (j, n)).homeoOfEquivCompactToT2
      (f := cur)
  have hblock : ∀ j : J, Nonempty ((∀ n : ℕ, R (e (j, n)).1) ≃ₜ (ℕ → Bool)) := by
    intro j
    have : ∀ n, Nontrivial (R (e (j, n)).1) := fun n => (e (j, n)).2
    exact CantorBrouwer.nonempty_homeomorph_cantor_of_perfect (not_isOpen_singleton_pi _)
  have h4 : (∀ j : J, ∀ n : ℕ, R (e (j, n)).1) ≃ₜ ∀ _ : J, ℕ → Bool :=
    Homeomorph.piCongrRight fun j => (hblock j).some
  let unc : (∀ _ : J, ℕ → Bool) ≃ (J × ℕ → Bool) :=
    { toFun := fun g p => g p.1 p.2
      invFun := fun f j n => f (j, n)
      left_inv := fun g => rfl
      right_inv := fun f => rfl }
  have h5 : (∀ _ : J, ℕ → Bool) ≃ₜ (J × ℕ → Bool) :=
    (continuous_pi fun p => (continuous_apply p.2).comp (continuous_apply p.1)).homeoOfEquivCompactToT2
      (f := unc)
  have h6 : (J × ℕ → Bool) ≃ₜ (J → Bool) := Homeomorph.piCongrLeft (Y := fun _ : J => Bool) e
  exact ⟨J, hJ, ⟨h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))⟩⟩

end Product

end CantorCube

open CantorCube

universe u

/-- **Morris, Theorem A5.0.23 (TP-496).**  The underlying topological space of every infinite,
totally disconnected, compact (Hausdorff) group is a Cantor cube: it is homeomorphic to `{0,1}^κ`
for some infinite set `κ`.  (Index the open normal subgroups by a well-order, read off the cosets
coordinate by coordinate, and regroup the finite factors into Cantor-space blocks.) -/
@[kb "morris2024" "Theorem A5.0.23, p. 509"]
theorem nonempty_homeomorph_cantorCube_of_group {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [Infinite G] :
    ∃ κ : Type u, Infinite κ ∧ Nonempty (G ≃ₜ (κ → Bool)) := by
  classical
  let U : OpenNormalSubgroup G → Subgroup G := fun i => i.toSubgroup
  have hUn : ∀ i, (U i).Normal := fun i => i.isNormal'
  have hUo : ∀ i, IsOpen (U i : Set G) := fun i => i.isOpen'
  have hsep : ∀ x : G, x ≠ 1 → ∃ i, x ∉ U i := by
    intro x hx
    obtain ⟨W, hW, h1, hxW⟩ := exists_isClopen_of_totally_separated (Ne.symm hx)
    obtain ⟨H, hH⟩ := IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one hW h1
    exact ⟨H, fun h => hxW (hH h)⟩
  obtain ⟨h⟩ := nonempty_homeomorph_pi (r := WellOrderingRel) hUn hUo hsep
  have hd : ∀ α, DiscreteTopology (G ⧸ U α) := fun α => QuotientGroup.discreteTopology (hUo α)
  have hf : ∀ α, Finite (G ⧸ U α) := fun α => Subgroup.quotient_finite_of_isOpen _ (hUo α)
  have hne : ∀ α, Nonempty (R WellOrderingRel U α) :=
    fun α => ⟨⟨QuotientGroup.mk 1, 1, (N WellOrderingRel U α).one_mem, rfl⟩⟩
  have : Infinite (∀ α, R WellOrderingRel U α) := Infinite.of_injective h h.injective
  obtain ⟨κ, hκ, ⟨h'⟩⟩ := exists_homeomorph_cantorCube_pi (fun α => R WellOrderingRel U α)
  exact ⟨κ, hκ, ⟨h.trans h'⟩⟩

end UndergradKB.Topology
