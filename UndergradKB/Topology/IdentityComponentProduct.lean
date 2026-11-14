import UndergradKB.Topology.IdentityComponent
import UndergradKB.Topology.CantorBrouwer
import Mathlib.Topology.InductiveDimension.Classes
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Metrizable.Uniformity
import UndergradKB.Common.Attr

/-! # A compact group is homeomorphic to `G₀ × G/G₀` (Morris, Theorem A5.0.26, TP-498)

Proved here for compact metrizable groups.

* `exists_continuous_section`: (zero-dimensional selection) a continuous open surjection `π` from a
  compact metric space onto a compact Hausdorff totally disconnected space has a continuous section.
  Locally constant approximate sections `sₙ` (every fibre passes within `εₙ` of `sₙ q`) are refined
  over finite clopen covers; they converge uniformly to a section.
* `nonempty_homeomorph_identityComponent_prod`: a compact metrizable group `G` is homeomorphic to
  `G₀ × G/G₀`, via `(h, q) ↦ s q * h`.
* `nonempty_homeomorph_identityComponent_prod_cantor`: if moreover `G/G₀` is infinite, then `G` is
  homeomorphic to `G₀ × {0,1}^ℵ₀` (combining with Brouwer's theorem, Theorem A5.0.23).
-/

open Set Filter Topology TopologicalSpace Metric

namespace UndergradKB.Topology
namespace Selection

variable {G Q : Type*} [MetricSpace G] [TopologicalSpace Q]

/-- First index of a list of sets containing a point. -/
noncomputable def sel (C : Q → Set Q) : List Q → Q → Option Q
  | [], _ => none
  | a :: l, q => open Classical in if q ∈ C a then some a else sel C l q

omit [MetricSpace G] [TopologicalSpace Q] in
theorem sel_spec (C : Q → Set Q) (l : List Q) (q a : Q) (h : sel C l q = some a) :
    a ∈ l ∧ q ∈ C a := by
  induction l with
  | nil => simp [sel] at h
  | cons b l ih =>
    by_cases hb : q ∈ C b
    · simp only [sel, hb, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨List.mem_cons_self, hb⟩
    · simp only [sel, hb, ↓reduceIte] at h
      exact ⟨List.mem_cons_of_mem _ (ih h).1, (ih h).2⟩

omit [MetricSpace G] [TopologicalSpace Q] in
theorem sel_isSome (C : Q → Set Q) (l : List Q) (q : Q) (h : ∃ a ∈ l, q ∈ C a) :
    ∃ a, sel C l q = some a := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    by_cases hb : q ∈ C b
    · exact ⟨b, by simp [sel, hb]⟩
    · simp only [sel, hb, ↓reduceIte]
      apply ih
      obtain ⟨a, ha, hqa⟩ := h
      rcases List.mem_cons.1 ha with rfl | ha
      · exact absurd hqa hb
      · exact ⟨a, ha, hqa⟩

omit [MetricSpace G] in
theorem sel_isLocallyConstant (C : Q → Set Q) (hC : ∀ a, IsClopen (C a)) (l : List Q) :
    IsLocallyConstant (sel C l) := by
  induction l with
  | nil => exact IsLocallyConstant.const none
  | cons b l ih =>
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro o
    have : sel C (b :: l) ⁻¹' {o} =
        (C b ∩ {_q | some b = o}) ∪ ((C b)ᶜ ∩ sel C l ⁻¹' {o}) := by
      ext q
      by_cases hq : q ∈ C b <;> simp [sel, hq]
    rw [this]
    refine ((hC b).isOpen.inter ?_).union ((hC b).compl.isOpen.inter (ih.isOpen_fiber o))
    by_cases h : some b = o
    · simp [h]
    · simp [h]

variable [CompactSpace Q] [T2Space Q] [TotallyDisconnectedSpace Q] {π : G → Q}

/-- One refinement step of locally constant approximate sections. -/
theorem refine_step (ho : IsOpenMap π) {ε ε' : ℝ} (hε' : 0 < ε') (f : Q → G)
    (hf : IsLocallyConstant f) (hfib : ∀ q, ∃ g, dist (f q) g < ε ∧ π g = q) :
    ∃ f' : Q → G, IsLocallyConstant f' ∧ (∀ q, dist (f q) (f' q) < ε) ∧
      ∀ q, ∃ g, dist (f' q) g < ε' ∧ π g = q := by
  classical
  choose gq hgq using hfib
  let O : Q → Set Q := fun q => f ⁻¹' {f q} ∩ π '' ball (gq q) ε'
  have hO : ∀ q, IsOpen (O q) := fun q =>
    (hf.isOpen_fiber (f q)).inter (ho _ isOpen_ball)
  have hqO : ∀ q, q ∈ O q := fun q =>
    ⟨rfl, gq q, mem_ball_self hε', (hgq q).2⟩
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
  refine ⟨fun q => gq (pick q), ?_, fun q => ?_, fun q => ?_⟩
  · have : IsLocallyConstant fun q => (sel C L q).getD q := by
      rw [IsLocallyConstant.iff_eventually_eq]
      intro q
      have hev := (sel_isLocallyConstant C hCcl L).eventually_eq q
      obtain ⟨a, ha⟩ := sel_isSome C L q (hcov q)
      filter_upwards [hev] with q' hq'
      rw [hq', ha]
      rfl
    exact this.comp gq
  · have h1 := hCO _ (hpick q)
    have h2 : f q = f (pick q) := h1.1
    rw [h2]
    exact (hgq (pick q)).1
  · obtain ⟨-, g, hg, hπ⟩ := hCO _ (hpick q)
    exact ⟨g, by rw [dist_comm]; exact hg, hπ⟩

/-- **Zero-dimensional selection.**  A continuous open surjection from a compact metric space onto
a compact Hausdorff totally disconnected space has a continuous section. -/
theorem exists_continuous_section [CompactSpace G] (hc : Continuous π) (ho : IsOpenMap π)
    (hs : Function.Surjective π) : ∃ s : Q → G, Continuous s ∧ ∀ q, π (s q) = q := by
  classical
  by_cases hG : Nonempty G
  swap
  · have hQ : IsEmpty Q := ⟨fun q => hG ⟨(hs q).choose⟩⟩
    exact ⟨fun q => (hQ.false q).elim, continuous_of_discreteTopology, fun q => (hQ.false q).elim⟩
  obtain ⟨g0⟩ := hG
  obtain ⟨R, hR⟩ := isCompact_univ.isBounded.subset_closedBall g0
  set C : ℝ := 2 * (max R 0 + 1) with hC
  have hCpos : 0 < C := by positivity
  let ε : ℕ → ℝ := fun n => C / 2 / 2 ^ n
  have hεpos : ∀ n, 0 < ε n := fun n => by positivity
  let P : ℕ → (Q → G) → Prop := fun n f =>
    IsLocallyConstant f ∧ ∀ q, ∃ g, dist (f q) g < ε n ∧ π g = q
  have hstep : ∀ n (f : {f // P n f}), ∃ f' : {f' // P (n + 1) f'},
      ∀ q, dist (f.1 q) (f'.1 q) < ε n := by
    rintro n ⟨f, hf1, hf2⟩
    obtain ⟨f', h1, h2, h3⟩ := refine_step ho (hεpos (n + 1)) f hf1 hf2
    exact ⟨⟨f', h1, h3⟩, h2⟩
  choose step hstep using hstep
  have h0 : P 0 fun _ => g0 := by
    refine ⟨IsLocallyConstant.const g0, fun q => ?_⟩
    obtain ⟨g, rfl⟩ := hs q
    refine ⟨g, ?_, rfl⟩
    have := hR (mem_univ g)
    rw [mem_closedBall, dist_comm] at this
    simp only [ε, pow_zero, div_one, hC]
    linarith [le_max_left R 0]
  let seq : (n : ℕ) → {f // P n f} := fun n =>
    Nat.rec (motive := fun n => {f // P n f}) ⟨_, h0⟩ (fun n f => step n f) n
  let F : ℕ → Q → G := fun n => (seq n).1
  have hF : ∀ n q, dist (F n q) (F (n + 1) q) ≤ C / 2 / 2 ^ n := fun n q =>
    (hstep n (seq n) q).le
  have hcs : ∀ q, CauchySeq fun n => F n q := fun q =>
    cauchySeq_of_le_geometric_two (fun n => hF n q)
  have : CompleteSpace G := complete_of_compact
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
  refine ⟨s, hunif.continuous (Eventually.of_forall fun n => (seq n).2.1.continuous).frequently, fun q => ?_⟩
  -- the section lands in the fibre
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
        exact add_le_add (hg n).1.le (hbound n q)
  have hcl : IsClosed (π ⁻¹' {q}) := isClosed_singleton.preimage hc
  exact hcl.mem_of_tendsto hgt (Eventually.of_forall fun n => (hg n).2)

end Selection

open Selection

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **Morris, Theorem A5.0.26 (TP-498), metrizable case.**  A compact metrizable group `G` is
homeomorphic to the product `G₀ × G/G₀` of its identity component and the quotient by it.  (The
book's theorem covers all compact groups; the non-metrizable case is not proved here.) -/
@[kb "morris2024" "Theorem A5.0.26, p. 510"]
theorem nonempty_homeomorph_identityComponent_prod [CompactSpace G] [MetrizableSpace G] :
    have := normal_connectedComponentOfOne G
    Nonempty (G ≃ₜ (Subgroup.connectedComponentOfOne G) ×
      (G ⧸ Subgroup.connectedComponentOfOne G)) := by
  have := normal_connectedComponentOfOne G
  let _ := metrizableSpaceMetric G
  set N := Subgroup.connectedComponentOfOne G
  have : IsClosed (N : Set G) := isClosed_connectedComponentOfOne G
  have : TotallyDisconnectedSpace (G ⧸ N) := totallyDisconnectedSpace_quotient_connectedComponentOfOne G
  obtain ⟨s, hsc, hs⟩ := exists_continuous_section (π := (QuotientGroup.mk : G → G ⧸ N))
    continuous_quotient_mk' QuotientGroup.isOpenMap_coe QuotientGroup.mk_surjective
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
      refine Continuous.prodMk (Continuous.subtype_mk ?_ _) continuous_quotient_mk'
      exact (hsc.comp continuous_quotient_mk').inv.mul continuous_id
    continuous_invFun := (hsc.comp continuous_snd).mul (continuous_subtype_val.comp continuous_fst) }⟩

/-- Theorem A5.0.26 combined with Theorem A5.0.23: a compact metrizable group with infinitely many
components is homeomorphic to `G₀ × {0,1}^ℵ₀`. -/
@[kb "morris2024" "Theorem A5.0.26, p. 510"]
theorem nonempty_homeomorph_identityComponent_prod_cantor [CompactSpace G] [MetrizableSpace G]
    [Infinite (G ⧸ Subgroup.connectedComponentOfOne G)] :
    Nonempty (G ≃ₜ (Subgroup.connectedComponentOfOne G) × (ℕ → Bool)) := by
  have := normal_connectedComponentOfOne G
  let _ := metrizableSpaceMetric G
  set N := Subgroup.connectedComponentOfOne G
  have : IsClosed (N : Set G) := isClosed_connectedComponentOfOne G
  have : TotallyDisconnectedSpace (G ⧸ N) := totallyDisconnectedSpace_quotient_connectedComponentOfOne G
  obtain ⟨e⟩ := nonempty_homeomorph_identityComponent_prod G
  have : SecondCountableTopology (G ⧸ N) := inferInstance
  obtain ⟨e'⟩ := CantorBrouwer.nonempty_homeomorph_cantor_of_perfect (X := G ⧸ N)
    not_isOpen_singleton_of_infinite_compact_group
  exact ⟨e.trans (Homeomorph.prodCongr (Homeomorph.refl _) e')⟩

end UndergradKB.Topology
