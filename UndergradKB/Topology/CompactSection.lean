import UndergradKB.Topology.IdentityComponentProduct
import UndergradKB.Topology.PeterWeylGeneral2
import UndergradKB.Topology.CantorCube
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Order.Zorn
import UndergradKB.Common.Attr

/-! # A compact group is homeomorphic to `G₀ × G/G₀`, all compact groups (Morris, Theorem A5.0.26)

Wave 4 proved Theorem A5.0.26 for compact metrizable groups (`IdentityComponentProduct.lean`), by a
continuous cross-section of `G → G/G₀` obtained from zero-dimensional selection, which needs a metric
on `G`.  Here the cross-section is built for every compact Hausdorff group.

* `Selection.exists_continuous_selection`: (zero-dimensional selection for set-valued maps) a lower
  semicontinuous map `Φ` with nonempty closed values from a compact Hausdorff totally disconnected
  space into a compact metric space has a continuous selection.
* `continuous_mk_of_map`: a map into a coset space `G ⧸ A` of a compact group is continuous as soon
  as its composite with a continuous map `ψ` whose fibres are the cosets of `A` is continuous.
* `exists_continuous_section_of_totallyDisconnected`: if `H` is a closed subgroup of a compact
  Hausdorff group `G` with `G ⧸ H` totally disconnected, then `G → G ⧸ H` has a continuous section.
  Partial sections `(N, s)` (a closed subgroup `N` and a choice `s q ∈ q` continuous modulo `N`) are
  ordered by refinement; chains have upper bounds by compactness; by Zorn's lemma there is a maximal
  one, and `N = 1` because a nontrivial `N` can be cut down by the kernel of a finite-dimensional
  unitary representation not trivial on `N` (Peter-Weyl, Theorem A5.10.1), the new coordinate being
  chosen by zero-dimensional selection in the metric space of matrices.
* `nonempty_homeomorph_identityComponent_prod_of_compact`: Theorem A5.0.26 in the book's generality.
* `exists_homeomorph_identityComponent_prod_cantorCube`: with Theorem A5.0.23, if `G/G₀` is infinite
  then `G` is homeomorphic to `G₀ × {0,1}^κ` for an infinite set `κ`.
-/

open Set Filter Topology TopologicalSpace Metric

universe u

namespace UndergradKB.Topology
namespace Selection

variable {X Q : Type*} [MetricSpace X] [TopologicalSpace Q] [CompactSpace Q] [T2Space Q]
  [TotallyDisconnectedSpace Q]

/-- One refinement step of locally constant approximate selections of a lower semicontinuous
set-valued map. -/
theorem refine_step_setValued {Φ : Q → Set X}
    (hΦ : ∀ U : Set X, IsOpen U → IsOpen {q | (Φ q ∩ U).Nonempty}) {ε ε' : ℝ} (hε' : 0 < ε')
    (f : Q → X) (hf : IsLocallyConstant f) (hfib : ∀ q, ∃ x ∈ Φ q, dist (f q) x < ε) :
    ∃ f' : Q → X, IsLocallyConstant f' ∧ (∀ q, dist (f q) (f' q) < ε) ∧
      ∀ q, ∃ x ∈ Φ q, dist (f' q) x < ε' := by
  classical
  choose xq hxq using hfib
  let O : Q → Set Q := fun q => f ⁻¹' {f q} ∩ {q' | (Φ q' ∩ ball (xq q) ε').Nonempty}
  have hO : ∀ q, IsOpen (O q) := fun q =>
    (hf.isOpen_fiber (f q)).inter (hΦ _ isOpen_ball)
  have hqO : ∀ q, q ∈ O q := fun q =>
    ⟨rfl, xq q, (hxq q).1, mem_ball_self hε'⟩
  have hbasis := isTopologicalBasis_isClopen (X := Q)
  choose C hCcl hqC hCO using fun q => hbasis.exists_subset_of_mem_open (hqO q) (hO q)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover C (fun q => (hCcl q).isOpen)
    (fun q _ => mem_iUnion.2 ⟨q, hqC q⟩)
  let L := t.toList
  have hcov : ∀ q, ∃ a ∈ L, q ∈ C a := by
    intro q
    obtain ⟨a, ha, hqa⟩ := mem_iUnion₂.1 (ht (mem_univ q))
    exact ⟨a, Finset.mem_toList.2 ha, hqa⟩
  let pick : Q → Q := fun q => (sel C L q).getD q
  have hpick : ∀ q, q ∈ C (pick q) := by
    intro q
    obtain ⟨a, ha⟩ := sel_isSome C L q (hcov q)
    simp only [pick, ha, Option.getD_some]
    exact (sel_spec C L q a ha).2
  refine ⟨fun q => xq (pick q), ?_, fun q => ?_, fun q => ?_⟩
  · have : IsLocallyConstant fun q => (sel C L q).getD q := by
      rw [IsLocallyConstant.iff_eventually_eq]
      intro q
      have hev := (sel_isLocallyConstant C hCcl L).eventually_eq q
      obtain ⟨a, ha⟩ := sel_isSome C L q (hcov q)
      filter_upwards [hev] with q' hq'
      rw [hq', ha]
      rfl
    exact this.comp xq
  · have h1 := hCO _ (hpick q)
    have h2 : f q = f (pick q) := h1.1
    rw [h2]
    exact (hxq (pick q)).2
  · obtain ⟨-, y, hy, hyb⟩ := hCO _ (hpick q)
    exact ⟨y, hy, by rw [dist_comm]; exact hyb⟩

/-- **Zero-dimensional selection for set-valued maps.**  A lower semicontinuous map `Φ` with
nonempty closed values from a compact Hausdorff totally disconnected space into a compact metric
space has a continuous selection. -/
theorem exists_continuous_selection [CompactSpace X] {Φ : Q → Set X} (hne : ∀ q, (Φ q).Nonempty)
    (hcl : ∀ q, IsClosed (Φ q)) (hΦ : ∀ U : Set X, IsOpen U → IsOpen {q | (Φ q ∩ U).Nonempty}) :
    ∃ t : Q → X, Continuous t ∧ ∀ q, t q ∈ Φ q := by
  classical
  by_cases hX : Nonempty X
  swap
  · have hQ : IsEmpty Q := ⟨fun q => hX ⟨(hne q).some⟩⟩
    exact ⟨fun q => (hQ.false q).elim, continuous_of_discreteTopology, fun q => (hQ.false q).elim⟩
  obtain ⟨x0⟩ := hX
  obtain ⟨R, hR⟩ := isCompact_univ.isBounded.subset_closedBall x0
  set C : ℝ := 2 * (max R 0 + 1) with hC
  have hCpos : 0 < C := by positivity
  let ε : ℕ → ℝ := fun n => C / 2 / 2 ^ n
  have hεpos : ∀ n, 0 < ε n := fun n => by positivity
  let P : ℕ → (Q → X) → Prop := fun n f =>
    IsLocallyConstant f ∧ ∀ q, ∃ x ∈ Φ q, dist (f q) x < ε n
  have hstep : ∀ n (f : {f // P n f}), ∃ f' : {f' // P (n + 1) f'},
      ∀ q, dist (f.1 q) (f'.1 q) < ε n := by
    rintro n ⟨f, hf1, hf2⟩
    obtain ⟨f', h1, h2, h3⟩ := refine_step_setValued hΦ (hεpos (n + 1)) f hf1 hf2
    exact ⟨⟨f', h1, h3⟩, h2⟩
  choose step hstep using hstep
  have h0 : P 0 fun _ => x0 := by
    refine ⟨IsLocallyConstant.const x0, fun q => ?_⟩
    obtain ⟨x, hx⟩ := hne q
    refine ⟨x, hx, ?_⟩
    have := hR (mem_univ x)
    rw [mem_closedBall, dist_comm] at this
    simp only [ε, pow_zero, div_one, hC]
    linarith [le_max_left R 0]
  let seq : (n : ℕ) → {f // P n f} := fun n =>
    Nat.rec (motive := fun n => {f // P n f}) ⟨_, h0⟩ (fun n f => step n f) n
  let F : ℕ → Q → X := fun n => (seq n).1
  have hF : ∀ n q, dist (F n q) (F (n + 1) q) ≤ C / 2 / 2 ^ n := fun n q =>
    (hstep n (seq n) q).le
  have hcs : ∀ q, CauchySeq fun n => F n q := fun q =>
    cauchySeq_of_le_geometric_two (fun n => hF n q)
  have : CompleteSpace X := complete_of_compact
  choose s hs' using fun q => cauchySeq_tendsto_of_complete (hcs q)
  have hbound : ∀ n q, dist (F n q) (s q) ≤ C / 2 ^ n := fun n q =>
    dist_le_of_le_geometric_two_of_tendsto (fun n => hF n q) (hs' q) n
  have hpow : Tendsto (fun n : ℕ => C / 2 ^ n) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)).const_mul C
    simpa [div_eq_mul_inv] using this
  have hunif : TendstoUniformly F s atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro r hr
    filter_upwards [hpow.eventually (gt_mem_nhds hr)] with n hn q
    rw [dist_comm]
    exact lt_of_le_of_lt (hbound n q) hn
  refine ⟨s, hunif.continuous (Eventually.of_forall fun n => (seq n).2.1.continuous).frequently,
    fun q => ?_⟩
  choose g hg using fun n => (seq n).2.2 q
  have hgt : Tendsto g atTop (𝓝 (s q)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have h2 : Tendsto (fun n : ℕ => C / 2 / 2 ^ n + C / 2 ^ n) atTop (𝓝 0) := by
      have h3 : Tendsto (fun n : ℕ => C / 2 / 2 ^ n) atTop (𝓝 0) := by
        have := hpow.div_const 2
        simp only [zero_div] at this
        refine this.congr fun n => ?_
        ring
      simpa using h3.add hpow
    refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) h2
    calc dist (g n) (s q) ≤ dist (g n) (F n q) + dist (F n q) (s q) := dist_triangle _ _ _
      _ ≤ C / 2 / 2 ^ n + C / 2 ^ n := by
        rw [dist_comm]
        exact add_le_add (hg n).2.le (hbound n q)
  exact (hcl q).mem_of_tendsto hgt (Eventually.of_forall fun n => (hg n).1)

end Selection

open Selection

section Sections

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

omit [IsTopologicalGroup G] in
/-- A map into a coset space `G ⧸ A` of a compact group is continuous as soon as its composite
with a continuous map `ψ`, whose fibres are exactly the cosets of `A`, is continuous. -/
theorem continuous_mk_of_map {X Q : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Q]
    (A : Subgroup G) (ψ : G → X) (hψ : Continuous ψ) (hA : ∀ x y, ψ x = ψ y ↔ x⁻¹ * y ∈ A)
    {f : Q → G} (hf : Continuous (ψ ∘ f)) : Continuous fun q => (f q : G ⧸ A) := by
  let ψ' : G ⧸ A → X := Quotient.lift ψ fun a b h => (hA a b).2 (QuotientGroup.leftRel_apply.1 h)
  have hc : Continuous ψ' := hψ.quotient_lift _
  have hinj : Function.Injective ψ' := by
    intro a b
    induction a using QuotientGroup.induction_on
    induction b using QuotientGroup.induction_on
    intro h
    exact QuotientGroup.eq.2 ((hA _ _).1 h)
  exact (hc.isClosedEmbedding hinj).isInducing.continuous_iff.2 hf

variable [T2Space G] (H : Subgroup G) [IsClosed (H : Set G)]

/-- A partial cross-section of `G → G ⧸ H`: a choice `s q ∈ q` of a point in each coset, which is
continuous modulo the closed subgroup `N`. -/
structure PartialSection where
  /-- The subgroup modulo which the choice is continuous. -/
  N : Subgroup G
  closed : IsClosed (N : Set G)
  /-- The choice of a point in each coset. -/
  s : G ⧸ H → G
  mem : ∀ q, (s q : G ⧸ H) = q
  cont : Continuous fun q => (s q : G ⧸ N)

namespace PartialSection

variable {H}

/-- Refinement: `b` refines `a` if `b.N ≤ a.N` and `b` agrees with `a` modulo `a.N`. -/
instance : Preorder (PartialSection H) where
  le a b := b.N ≤ a.N ∧ ∀ q, (a.s q)⁻¹ * b.s q ∈ a.N
  le_refl a := ⟨le_rfl, fun q => by simp [one_mem]⟩
  le_trans a b c hab hbc := ⟨hbc.1.trans hab.1, fun q => by
    have := mul_mem (hab.2 q) (hab.1 (hbc.2 q))
    simpa [mul_assoc] using this⟩

omit [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [IsClosed (H : Set G)] in
theorem le_def {a b : PartialSection H} :
    a ≤ b ↔ b.N ≤ a.N ∧ ∀ q, (a.s q)⁻¹ * b.s q ∈ a.N := Iff.rfl

omit [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [IsClosed (H : Set G)] in
/-- A finite part of a chain has a largest element. -/
theorem exists_max_of_chain {c : Set (PartialSection H)} (hc : IsChain (· ≤ ·) c)
    (u : Finset c) (hu : u.Nonempty) : ∃ j ∈ u, ∀ i ∈ u, i.1 ≤ j.1 := by
  classical
  induction u using Finset.induction_on with
  | empty => simp at hu
  | insert a u ha ih =>
    rcases u.eq_empty_or_nonempty with rfl | hu'
    · refine ⟨a, by simp, fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact le_rfl
      · simp at hi
    · obtain ⟨j, hj, hjmax⟩ := ih hu'
      rcases hc.total a.2 j.2 with h | h
      · refine ⟨j, Finset.mem_insert_of_mem hj, fun i hi => ?_⟩
        rcases Finset.mem_insert.1 hi with rfl | hi
        exacts [h, hjmax i hi]
      · refine ⟨a, Finset.mem_insert_self _ _, fun i hi => ?_⟩
        rcases Finset.mem_insert.1 hi with rfl | hi
        exacts [le_rfl, (hjmax i hi).trans h]

omit [T2Space G] in
/-- Chains of partial sections are bounded above (compactness). -/
theorem bddAbove (c : Set (PartialSection H)) (hc : IsChain (· ≤ ·) c) : BddAbove c := by
  classical
  let N : Subgroup G := ⨅ i : c, i.1.N
  have hNc : IsClosed (N : Set G) := by
    simp only [N, Subgroup.coe_iInf]
    exact isClosed_iInter fun i => i.1.closed
  have hne : ∀ q : G ⧸ H,
      ({x : G | (x : G ⧸ H) = q} ∩ ⋂ i : c, {x | (i.1.s q)⁻¹ * x ∈ i.1.N}).Nonempty := by
    intro q
    have hT : T2Space (G ⧸ H) := inferInstance
    refine IsCompact.inter_iInter_nonempty ?_ _ (fun i => i.1.closed.preimage
      (continuous_const.mul continuous_id)) fun u => ?_
    · exact ((isClosed_singleton (x := q)).preimage QuotientGroup.continuous_mk).isCompact
    · rcases u.eq_empty_or_nonempty with rfl | hu
      · exact ⟨(q.out : G), by simp⟩
      · obtain ⟨j, -, hjmax⟩ := exists_max_of_chain hc u hu
        refine ⟨j.1.s q, j.1.mem q, ?_⟩
        simp only [mem_iInter]
        exact fun i hi => (hjmax i hi).2 q
  choose s hs using hne
  have hsH : ∀ q, (s q : G ⧸ H) = q := fun q => (hs q).1
  have hsi : ∀ q (i : c), (i.1.s q)⁻¹ * s q ∈ i.1.N := fun q i => mem_iInter.1 (hs q).2 i
  have : ∀ i : c, T2Space (G ⧸ i.1.N) := fun i => by
    have := i.1.closed
    infer_instance
  have hcont : Continuous fun q => (s q : G ⧸ N) := by
    refine continuous_mk_of_map N (fun x (i : c) => (x : G ⧸ i.1.N))
      (continuous_pi fun i => QuotientGroup.continuous_mk) (fun x y => ?_) ?_
    · simp only [funext_iff, QuotientGroup.eq, N, Subgroup.mem_iInf]
    · refine continuous_pi fun i => (i.1.cont).congr fun q => ?_
      exact QuotientGroup.eq.2 (hsi q i)
  refine ⟨⟨N, hNc, s, hsH, hcont⟩, fun a ha => ?_⟩
  exact ⟨iInf_le (fun i : c => i.1.N) ⟨a, ha⟩, fun q => hsi q ⟨a, ha⟩⟩

/-- The initial partial section, continuous modulo `G` itself. -/
noncomputable def top : PartialSection H where
  N := ⊤
  closed := by simp
  s q := q.out
  mem q := QuotientGroup.out_eq' q
  cont := by
    have := QuotientGroup.subsingleton_quotient_top (G := G)
    exact continuous_of_const fun _ _ => Subsingleton.elim _ _

/-- A partial section that is continuous modulo a nontrivial `N` can be refined, cutting `N` down
by the kernel of a finite-dimensional unitary representation that is nontrivial on a given
`g ∈ N` (Peter-Weyl), the new coordinate chosen by zero-dimensional selection. -/
theorem exists_le_not_mem [TotallyDisconnectedSpace (G ⧸ H)] (a : PartialSection H) {g : G}
    (hg1 : g ≠ 1) : ∃ b : PartialSection H, a ≤ b ∧ g ∉ b.N := by
  classical
  obtain ⟨n, π, hπc, hπg⟩ := exists_unitaryMatrixRep_ne_one hg1
  let ψ0 : G → (Fin n → Fin n → ℂ) := fun x i j => (π x : Matrix (Fin n) (Fin n) ℂ) i j
  have hψ0c : Continuous ψ0 := continuous_pi fun i => continuous_pi fun j =>
    (continuous_subtype_val.comp hπc).matrix_elem i j
  let X := Set.range ψ0
  have : CompactSpace X := isCompact_iff_compactSpace.1 (isCompact_range hψ0c)
  let ψ : G → X := fun x => ⟨ψ0 x, x, rfl⟩
  have hψc : Continuous ψ := hψ0c.subtype_mk _
  have hψ : ∀ x y, ψ x = ψ y ↔ x⁻¹ * y ∈ π.ker := by
    intro x y
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one, Subtype.ext_iff]
    constructor
    · intro h
      apply Subtype.ext
      ext i j
      exact congrFun (congrFun h i) j
    · intro h
      simp only [ψ, ψ0, h]
  have := a.closed
  let K : Subgroup G := H ⊓ a.N
  have hK : ∀ x y : G, ((x : G ⧸ H), (x : G ⧸ a.N)) = ((y : G ⧸ H), (y : G ⧸ a.N)) ↔
      x⁻¹ * y ∈ K := by
    intro x y
    simp only [Prod.mk.injEq, QuotientGroup.eq, K, Subgroup.mem_inf]
  have hKc : Continuous fun q => (a.s q : G ⧸ K) := by
    refine continuous_mk_of_map K _ (QuotientGroup.continuous_mk.prodMk QuotientGroup.continuous_mk) hK ?_
    exact (continuous_id.congr fun q => (a.mem q).symm).prodMk a.cont
  have hKcl : IsClosed (K : Set G) := by
    simp only [K, Subgroup.coe_inf]
    exact (inferInstance : IsClosed (H : Set G)).inter a.closed
  let Φ : G ⧸ H → Set X := fun q => ψ '' {x | (a.s q)⁻¹ * x ∈ K}
  have hΦne : ∀ q, (Φ q).Nonempty := fun q => ⟨ψ (a.s q), a.s q, by simp [one_mem], rfl⟩
  have hΦcl : ∀ q, IsClosed (Φ q) := fun q =>
    ((hKcl.preimage (continuous_const.mul continuous_id)).isCompact.image hψc).isClosed
  have hΦ : ∀ U : Set X, IsOpen U → IsOpen {q | (Φ q ∩ U).Nonempty} := by
    intro U hU
    have hV : IsOpen ((QuotientGroup.mk : G → G ⧸ K) '' (ψ ⁻¹' U)) :=
      QuotientGroup.isOpenMap_coe _ (hU.preimage hψc)
    convert hV.preimage hKc using 1
    ext q
    simp only [mem_ofPred_eq, mem_preimage, mem_image, Φ]
    constructor
    · rintro ⟨-, ⟨x, hx, rfl⟩, hxU⟩
      exact ⟨x, hxU, (QuotientGroup.eq.2 hx).symm⟩
    · rintro ⟨x, hxU, hx⟩
      exact ⟨ψ x, ⟨x, QuotientGroup.eq.1 hx.symm, rfl⟩, hxU⟩
  obtain ⟨t, htc, ht⟩ := exists_continuous_selection hΦne hΦcl hΦ
  choose x hxK hxt using fun q => ht q
  have hxH : ∀ q, (x q : G ⧸ H) = q := fun q =>
    (QuotientGroup.eq.2 (Subgroup.mem_inf.1 (hxK q)).1).symm.trans (a.mem q)
  have hxN : ∀ q, (a.s q)⁻¹ * x q ∈ a.N := fun q => (Subgroup.mem_inf.1 (hxK q)).2
  let N' : Subgroup G := a.N ⊓ π.ker
  have hN'c : IsClosed (N' : Set G) := by
    simp only [N', Subgroup.coe_inf, MonoidHom.coe_ker]
    exact a.closed.inter (isClosed_singleton.preimage hπc)
  have hN' : ∀ x y : G, ((x : G ⧸ a.N), ψ x) = ((y : G ⧸ a.N), ψ y) ↔ x⁻¹ * y ∈ N' := by
    intro x y
    simp only [Prod.mk.injEq, QuotientGroup.eq, N', Subgroup.mem_inf, hψ]
  have hcont : Continuous fun q => (x q : G ⧸ N') := by
    refine continuous_mk_of_map N' _ (QuotientGroup.continuous_mk.prodMk hψc) hN' ?_
    refine (a.cont.congr fun q => QuotientGroup.eq.2 (hxN q)).prodMk (htc.congr fun q => ?_)
    exact (hxt q).symm
  refine ⟨⟨N', hN'c, x, hxH, hcont⟩, ⟨inf_le_left, hxN⟩, fun hg => hπg ?_⟩
  exact (Subgroup.mem_inf.1 hg).2

end PartialSection

/-- **Cross-sections of compact groups.**  If `H` is a closed subgroup of a compact Hausdorff group
`G` and `G ⧸ H` is totally disconnected, then the quotient map `G → G ⧸ H` has a continuous
section. -/
theorem exists_continuous_section_of_totallyDisconnected [TotallyDisconnectedSpace (G ⧸ H)] :
    ∃ s : G ⧸ H → G, Continuous s ∧ ∀ q, (s q : G ⧸ H) = q := by
  classical
  obtain ⟨m, hm⟩ := zorn_le (α := PartialSection H) PartialSection.bddAbove
  have hbot : ∀ g ∈ m.N, g = 1 := by
    intro g hg
    by_contra hg1
    obtain ⟨b, hmb, hgb⟩ := m.exists_le_not_mem hg1
    exact hgb ((hm hmb).1 hg)
  have := m.closed
  have hT : T2Space (G ⧸ m.N) := inferInstance
  have hinj : Function.Injective (QuotientGroup.mk : G → G ⧸ m.N) := by
    intro x y h
    have := hbot _ (QuotientGroup.eq.1 h)
    rw [inv_mul_eq_one] at this
    exact this
  have he := QuotientGroup.continuous_mk.isClosedEmbedding hinj
  exact ⟨m.s, he.isInducing.continuous_iff.2 m.cont, m.mem⟩

end Sections

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **Morris, Theorem A5.0.26 (TP-498).**  A compact (Hausdorff) group `G` is homeomorphic to the
product `G₀ × G/G₀` of its identity component and the quotient by it. -/
@[kb "morris2024" "Theorem A5.0.26, p. 510"]
theorem nonempty_homeomorph_identityComponent_prod_of_compact [CompactSpace G] [T2Space G] :
    have := normal_connectedComponentOfOne G
    Nonempty (G ≃ₜ (Subgroup.connectedComponentOfOne G) ×
      (G ⧸ Subgroup.connectedComponentOfOne G)) := by
  have := normal_connectedComponentOfOne G
  set N := Subgroup.connectedComponentOfOne G
  have : IsClosed (N : Set G) := isClosed_connectedComponentOfOne G
  have : TotallyDisconnectedSpace (G ⧸ N) :=
    totallyDisconnectedSpace_quotient_connectedComponentOfOne G
  obtain ⟨s, hsc, hs⟩ := exists_continuous_section_of_totallyDisconnected N
  have hmem : ∀ g : G, (s (g : G ⧸ N))⁻¹ * g ∈ N := fun g =>
    QuotientGroup.eq.1 (hs (g : G ⧸ N))
  refine ⟨{
    toFun := fun g => (⟨(s (g : G ⧸ N))⁻¹ * g, hmem g⟩, (g : G ⧸ N))
    invFun := fun p => s p.2 * p.1
    left_inv := fun g => by simp
    right_inv := fun p => by
      obtain ⟨⟨h, hh⟩, q⟩ := p
      have hq : ((s q * h : G) : G ⧸ N) = q := by
        rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff h).2 hh, mul_one, hs]
      simp only [hq, Prod.mk.injEq, and_true]
      ext
      simp
    continuous_toFun := by
      refine Continuous.prodMk (Continuous.subtype_mk ?_ _) QuotientGroup.continuous_mk
      exact (hsc.comp QuotientGroup.continuous_mk).inv.mul continuous_id
    continuous_invFun :=
      (hsc.comp continuous_snd).mul (continuous_subtype_val.comp continuous_fst) }⟩

/-- Theorem A5.0.26 combined with Theorem A5.0.23 (all weights): a compact group with infinitely
many components is homeomorphic to `G₀ × {0,1}^κ` for an infinite set `κ`. -/
@[kb "morris2024" "Theorem A5.0.26, p. 510"]
theorem exists_homeomorph_identityComponent_prod_cantorCube {G : Type u} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [Infinite (G ⧸ Subgroup.connectedComponentOfOne G)] :
    ∃ κ : Type u, Infinite κ ∧
      Nonempty (G ≃ₜ (Subgroup.connectedComponentOfOne G) × (κ → Bool)) := by
  have := normal_connectedComponentOfOne G
  set N := Subgroup.connectedComponentOfOne G
  have : IsClosed (N : Set G) := isClosed_connectedComponentOfOne G
  have : TotallyDisconnectedSpace (G ⧸ N) :=
    totallyDisconnectedSpace_quotient_connectedComponentOfOne G
  obtain ⟨e⟩ := nonempty_homeomorph_identityComponent_prod_of_compact G
  obtain ⟨κ, hκ, ⟨e'⟩⟩ := nonempty_homeomorph_cantorCube_of_group (G := G ⧸ N)
  exact ⟨κ, hκ, ⟨e.trans (Homeomorph.prodCongr (Homeomorph.refl _) e')⟩⟩

end UndergradKB.Topology
