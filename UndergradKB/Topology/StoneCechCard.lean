import Mathlib.Topology.Compactification.StoneCech
import Mathlib.Topology.Bases
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UnitInterval
import Mathlib.Order.Filter.Ultrafilter.Cardinality
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Bounded
import UndergradKB.Common.Attr

/-!
# Cardinality of the Stone-Cech compactification (Morris, Topology Without Tears, §10.4)
-/

open scoped Topology

namespace UndergradKB.Topology

open Set Filter

namespace StoneCechCard

/-- The map from ultrafilters on `X` onto the Stone-Cech compactification of `X`. -/
noncomputable def ofUltrafilter {X : Type*} [TopologicalSpace X] (F : Ultrafilter X) : StoneCech X :=
  T2Quotient.mk (Quot.mk _ F : PreStoneCech X)

theorem surjective_ofUltrafilter {X : Type*} [TopologicalSpace X] :
    Function.Surjective (ofUltrafilter (X := X)) := by
  intro y
  obtain ⟨p, hp⟩ := T2Quotient.surjective_mk (X := PreStoneCech X) y
  obtain ⟨F, hF⟩ := Quot.mk_surjective p
  exact ⟨F, by rw [← hp, ← hF]; rfl⟩

/-- Morris, Topology Without Tears, Proposition 10.4.15 (TP-324). For a separable space `X`, the
Stone-Cech compactification of `X` has cardinality at most that of the one of `ℕ`. -/
@[kb "morris2024" "Proposition 10.4.15, p. 334"]
theorem card_stoneCech_le_of_separable {X : Type} [TopologicalSpace X]
    [TopologicalSpace.SeparableSpace X] :
    Cardinal.mk (StoneCech X) ≤ Cardinal.mk (StoneCech ℕ) := by
  rcases isEmpty_or_nonempty X with hX | hX
  · have : IsEmpty (Ultrafilter X) := ⟨fun F => hX.false (Filter.nonempty_of_mem F.univ_mem).some⟩
    have : IsEmpty (StoneCech X) := ⟨fun y => by
      obtain ⟨F, -⟩ := surjective_ofUltrafilter y
      exact this.false F⟩
    simp
  · obtain ⟨s, hs⟩ := TopologicalSpace.exists_dense_seq X
    have hg : Continuous ((stoneCechUnit : X → StoneCech X) ∘ s) :=
      continuous_stoneCechUnit.comp continuous_of_discreteTopology
    have hΦ := continuous_stoneCechExtend hg
    have hd : Dense (range (stoneCechExtend hg)) := by
      refine (denseRange_stoneCechUnit.comp hs continuous_stoneCechUnit).mono ?_
      rintro _ ⟨n, rfl⟩
      exact ⟨stoneCechUnit n, stoneCechExtend_stoneCechUnit hg n⟩
    have hsurj : Function.Surjective (stoneCechExtend hg) := by
      have := hd.closure_eq
      rw [(isCompact_range hΦ).isClosed.closure_eq] at this
      exact range_eq_univ.1 this
    exact Cardinal.mk_le_of_surjective hsurj

theorem card_stoneCech_nat_le : Cardinal.mk (StoneCech ℕ) ≤ 2 ^ Cardinal.continuum := by
  have h1 : Cardinal.mk (Ultrafilter ℕ) = 2 ^ (2 ^ Cardinal.mk ℕ : Cardinal) :=
    Cardinal.mk_ultrafilter_of_infinite
  rw [Cardinal.mk_nat, Cardinal.two_power_aleph0] at h1
  exact h1 ▸ Cardinal.mk_le_of_surjective surjective_ofUltrafilter

/-- Ultrafilters on `ℕ` inject into the Stone-Cech compactification of a normal space containing a
sequence of distinct points all of whose subsets are closed. -/
theorem card_ultrafilter_nat_le {X : Type} [TopologicalSpace X] [NormalSpace X] {x : ℕ → X}
    (hinj : Function.Injective x) (hcl : ∀ T ⊆ range x, IsClosed T) :
    Cardinal.mk (Ultrafilter ℕ) ≤ Cardinal.mk (StoneCech X) := by
  have hex : ∀ p : Ultrafilter ℕ, ∃ y : StoneCech X,
      ((p.map (stoneCechUnit ∘ x) : Ultrafilter (StoneCech X)) : Filter (StoneCech X)) ≤ 𝓝 y :=
    fun p => by
      obtain ⟨y, -, hy⟩ := isCompact_univ.ultrafilter_le_nhds
        (p.map (stoneCechUnit ∘ x) : Ultrafilter (StoneCech X)) (by simp)
      exact ⟨y, hy⟩
  choose g hg using hex
  refine Cardinal.mk_le_of_injective (f := g) fun p q hpq => ?_
  refine Ultrafilter.eq_of_le (Filter.le_def.2 fun S hS => ?_)
  by_contra hSp
  have hSc : Sᶜ ∈ p := Ultrafilter.compl_mem_iff_notMem.2 hSp
  obtain ⟨f, hf0, hf1, hf⟩ := exists_continuous_zero_one_of_isClosed
    (hcl (x '' Sᶜ) (image_subset_range _ _)) (hcl (x '' S) (image_subset_range _ _))
    (by rw [Set.disjoint_image_iff hinj]; exact disjoint_compl_left)
  let f' : X → unitInterval := fun y => ⟨f y, hf y⟩
  have hf' : Continuous f' := by fun_prop
  have hF := continuous_stoneCechExtend hf'
  have key : ∀ n, stoneCechExtend hf' (stoneCechUnit (x n)) = f' (x n) :=
    fun n => stoneCechExtend_stoneCechUnit hf' (x n)
  have t1 : Tendsto (fun n => stoneCechExtend hf' (stoneCechUnit (x n))) (p : Filter ℕ)
      (𝓝 (stoneCechExtend hf' (g p))) :=
    (hF.tendsto (g p)).comp (by have := hg p; rw [Ultrafilter.coe_map] at this; exact this)
  have t2 : Tendsto (fun n => stoneCechExtend hf' (stoneCechUnit (x n))) (p : Filter ℕ)
      (𝓝 (0 : unitInterval)) := by
    refine tendsto_const_nhds.congr' (Filter.mem_of_superset hSc fun n hn => ?_)
    simp only [key, f']
    exact Subtype.ext (hf0 ⟨n, hn, rfl⟩).symm
  have t3 : Tendsto (fun n => stoneCechExtend hf' (stoneCechUnit (x n))) (q : Filter ℕ)
      (𝓝 (stoneCechExtend hf' (g q))) :=
    (hF.tendsto (g q)).comp (by have := hg q; rw [Ultrafilter.coe_map] at this; exact this)
  have t4 : Tendsto (fun n => stoneCechExtend hf' (stoneCechUnit (x n))) (q : Filter ℕ)
      (𝓝 (1 : unitInterval)) := by
    refine tendsto_const_nhds.congr' (Filter.mem_of_superset hS fun n hn => ?_)
    simp only [key, f']
    exact Subtype.ext (hf1 ⟨n, hn, rfl⟩).symm
  have e1 := tendsto_nhds_unique t1 t2
  have e2 := tendsto_nhds_unique t3 t4
  rw [hpq] at e1
  have : (0 : unitInterval) = 1 := e1.symm.trans e2
  exact zero_ne_one this

/-- The extension to `βℕ` of a sequence of distinct points all of whose subsets are closed in a
normal space is a topological embedding `βℕ → βX`. -/
theorem isEmbedding_stoneCechExtend_seq {X : Type} [TopologicalSpace X] [NormalSpace X]
    {x : ℕ → X} (hinj : Function.Injective x) (hcl : ∀ T ⊆ range x, IsClosed T) :
    ∃ Φ : StoneCech ℕ → StoneCech X, Topology.IsEmbedding Φ ∧
      ∀ n, Φ (stoneCechUnit n) = stoneCechUnit (x n) := by
  have hg : Continuous ((stoneCechUnit : X → StoneCech X) ∘ x) :=
    continuous_stoneCechUnit.comp continuous_of_discreteTopology
  have hΦ := continuous_stoneCechExtend hg
  have hΦu : ∀ n, stoneCechExtend hg (stoneCechUnit n) = stoneCechUnit (x n) :=
    fun n => stoneCechExtend_stoneCechUnit hg n
  have hce : Topology.IsClosedEmbedding x :=
    Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap continuous_of_discreteTopology
      hinj fun S _ => hcl _ (image_subset_range _ _)
  have hinjΦ : Function.Injective (stoneCechExtend hg) := by
    intro a b hab
    by_contra hne
    obtain ⟨h, ha, hb, hh⟩ := exists_continuous_zero_one_of_isClosed
      (isClosed_singleton (x := a)) (isClosed_singleton (x := b)) (disjoint_singleton.2 hne)
    have ha0 : h a = 0 := ha rfl
    have hb1 : h b = 1 := hb rfl
    let hn : C(ℕ, ℝ) := ⟨fun n => h (stoneCechUnit n), by fun_prop⟩
    obtain ⟨G, hGt, hGe⟩ := ContinuousMap.exists_extension_forall_mem_of_isClosedEmbedding hn
      (t := Icc (0 : ℝ) 1) (fun n => hh _) ⟨0, by simp⟩ hce
    let G' : X → unitInterval := fun y => ⟨G y, hGt y⟩
    have hG' : Continuous G' := by fun_prop
    have hF := continuous_stoneCechExtend hG'
    have hcomp : (fun w => ((stoneCechExtend hG' (stoneCechExtend hg w) : unitInterval) : ℝ)) =
        fun w => h w := by
      refine Continuous.ext_on denseRange_stoneCechUnit (by fun_prop) h.continuous ?_
      rintro _ ⟨n, rfl⟩
      simp only [hΦu, stoneCechExtend_stoneCechUnit hG']
      exact congr_fun hGe n
    have e1 := congr_fun hcomp a
    have e2 := congr_fun hcomp b
    simp only [hab] at e1
    rw [e1, ha0, hb1] at e2
    exact zero_ne_one e2
  exact ⟨stoneCechExtend hg, (hΦ.isClosedEmbedding hinjΦ).isEmbedding, hΦu⟩

/-- An unbounded metric space contains a sequence of distinct points all of whose subsets are
closed (a closed discrete copy of `ℕ`). -/
theorem exists_closed_discrete_seq {Y : Type*} [MetricSpace Y]
    (hY : ¬ Bornology.IsBounded (univ : Set Y)) :
    ∃ x : ℕ → Y, Function.Injective x ∧ ∀ T ⊆ range x, IsClosed T := by
  obtain ⟨y0⟩ : Nonempty Y := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hY (by simp [Set.univ_eq_empty_iff.2 h])
  have hfar : ∀ r : ℝ, ∃ y : Y, r < dist y y0 := by
    intro r
    by_contra h
    push Not at h
    exact hY ((Metric.isBounded_closedBall (x := y0) (r := r)).subset fun y _ => by
      simpa using h y)
  choose f hf using hfar
  let x : ℕ → Y := fun n => Nat.rec (f 0) (fun _ y => f (dist y y0 + 1)) n
  have hxs : ∀ n, x (n + 1) = f (dist (x n) y0 + 1) := fun n => rfl
  have hstep : ∀ n, dist (x n) y0 + 1 < dist (x (n + 1)) y0 := fun n => by
    rw [hxs]; exact hf _
  have hge : ∀ n : ℕ, (n : ℝ) ≤ dist (x n) y0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => push_cast; linarith [hstep n]
  have hmono : StrictMono fun n => dist (x n) y0 :=
    strictMono_nat_of_lt_succ fun n => by linarith [hstep n]
  refine ⟨x, fun m n h => hmono.injective (by simp only [h]), fun T hT => ?_⟩
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro y hy
  let N : Set ℕ := {n | dist (x n) y0 ≤ dist y y0 + 1}
  have hN : N.Finite := (Set.finite_Iic ⌈dist y y0 + 1⌉₊).subset fun n hn => by
    have h1 : (n : ℝ) ≤ dist y y0 + 1 := (hge n).trans hn
    exact Nat.cast_le.1 (h1.trans (Nat.le_ceil _))
  let F : Set Y := T ∩ x '' N
  have hF : F.Finite := (hN.image x).subset inter_subset_right
  have hyF : y ∉ F := fun h => hy h.1
  refine Filter.mem_of_superset (Filter.inter_mem (Metric.ball_mem_nhds y one_pos)
    (hF.isClosed.isOpen_compl.mem_nhds hyF)) ?_
  rintro z ⟨hz1, hz2⟩ hzT
  obtain ⟨n, rfl⟩ := hT hzT
  refine hz2 ⟨hzT, n, ?_, rfl⟩
  have := dist_triangle (x n) y y0
  rw [Metric.mem_ball] at hz1
  show dist (x n) y0 ≤ dist y y0 + 1
  linarith [dist_comm y (x n)]

theorem mk_euclideanSpace_le (n : ℕ) : Cardinal.mk (EuclideanSpace ℝ (Fin n)) ≤ Cardinal.continuum := by
  rw [Cardinal.mk_congr (WithLp.equiv 2 (Fin n → ℝ)), Cardinal.mk_arrow]
  simp only [Cardinal.mk_real, Cardinal.lift_continuum, Cardinal.mk_fintype, Fintype.card_fin,
    Cardinal.lift_natCast]
  exact Cardinal.power_nat_le Cardinal.aleph0_le_continuum

/-- Morris, Topology Without Tears, Proposition 10.4.18 (TP-326). For an unbounded subset `X` of
Euclidean space `ℝⁿ`, the Stone-Cech compactification `βX` contains a copy of `βℕ` (a topological
embedding extending the inclusion of a closed discrete sequence) and has cardinality `2 ^ 𝔠`. -/
@[kb "morris2024" "Proposition 10.4.18, p. 335"]
theorem stoneCech_of_unbounded {n : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))}
    (hX : ¬ Bornology.IsBounded X) :
    (∃ Φ : StoneCech ℕ → StoneCech X, Topology.IsEmbedding Φ) ∧
      Cardinal.mk (StoneCech X) = 2 ^ Cardinal.continuum := by
  have hY : ¬ Bornology.IsBounded (univ : Set X) := by
    intro h
    apply hX
    have h2 := Bornology.isBounded_induced.1 h
    rwa [image_univ, Subtype.range_coe] at h2
  obtain ⟨x, hinj, hcl⟩ := exists_closed_discrete_seq hY
  refine ⟨?_, le_antisymm ?_ ?_⟩
  · obtain ⟨Φ, hΦ, -⟩ := isEmbedding_stoneCechExtend_seq hinj hcl
    exact ⟨Φ, hΦ⟩
  · exact card_stoneCech_le_of_separable.trans card_stoneCech_nat_le
  · have h1 : Cardinal.mk (Ultrafilter ℕ) = 2 ^ (2 ^ Cardinal.mk ℕ : Cardinal) :=
      Cardinal.mk_ultrafilter_of_infinite
    rw [Cardinal.mk_nat, Cardinal.two_power_aleph0] at h1
    exact h1 ▸ card_ultrafilter_nat_le hinj hcl

/-- Morris, Topology Without Tears, Corollary 10.4.19 (TP-327). A closed subspace of `ℝⁿ` is compact
iff its Stone-Cech compactification does not have cardinality `2 ^ 𝔠`. -/
@[kb "morris2024" "Corollary 10.4.19, p. 335"]
theorem isCompact_iff_card_stoneCech_ne {n : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))}
    (hX : IsClosed X) : IsCompact X ↔ Cardinal.mk (StoneCech X) ≠ 2 ^ Cardinal.continuum := by
  constructor
  · intro hc heq
    have : CompactSpace X := isCompact_iff_compactSpace.1 hc
    have h1 : Cardinal.mk (StoneCech X) ≤ Cardinal.mk X := by
      refine Cardinal.mk_le_of_surjective (f := (stoneCechUnit : X → StoneCech X)) ?_
      have hd := (denseRange_stoneCechUnit (α := X)).closure_eq
      rw [(isCompact_range continuous_stoneCechUnit).isClosed.closure_eq] at hd
      exact range_eq_univ.1 hd
    have h2 : Cardinal.mk X ≤ Cardinal.continuum := (Cardinal.mk_set_le X).trans (mk_euclideanSpace_le n)
    exact absurd (heq ▸ h1.trans h2) (not_le_of_gt (Cardinal.cantor _))
  · intro hne
    by_contra hnc
    refine hne (stoneCech_of_unbounded fun hb => hnc ?_).2
    exact Metric.isCompact_of_isClosed_isBounded hX hb

end StoneCechCard

end UndergradKB.Topology
