import UndergradKB.Topology.HahnMazurkiewiczPaths
import UndergradKB.Topology.ConesSpheres
import Mathlib.Topology.MetricSpace.HausdorffAlexandroff
import Mathlib.Topology.Instances.CantorSet
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Metrizable.Uniformity
import UndergradKB.Common.Attr

/-! # The Hahn-Mazurkiewicz theorem (Morris, Theorem 9.5.12, TP-235)

A Hausdorff space is a continuous image of `[0,1]` if and only if it is compact, connected, locally
connected and metrizable. The "only if" direction is
`compact_connected_locallyConnected_metrizable_of_continuous_surjective_unitInterval`
(`ConesSpheres.lean`); this file proves the "if" direction.

Route: put a metric on `X`. By `HMPaths.exists_path_of_dist_lt`, `X` is uniformly locally path
connected. By the Hausdorff-Alexandroff theorem (Mathlib) `X` is a continuous image of the Cantor
set `K ⊆ [0,1]`. A continuous map on a closed set `K ⊆ [0,1]` containing `0` and `1` extends to
`[0,1]`: on each gap `(a, b)` of `K` follow a path from `f a` to `f b` of nearly minimal radius;
small gaps get small paths, which gives continuity at the points of `K`.
-/

open Set Filter Topology Metric

namespace UndergradKB.Topology
namespace HMExt

variable {X : Type*} [MetricSpace X]

/-! ### Paths of nearly minimal radius -/

/-- The infimum of the radii (measured from the starting point) of paths from `u` to `v`. -/
noncomputable def pathRad (u v : X) : ℝ := sInf {r | ∃ γ : Path u v, ∀ t, dist u (γ t) ≤ r}

theorem pathRad_nonneg (u v : X) : 0 ≤ pathRad u v := by
  apply Real.sInf_nonneg
  rintro r ⟨γ, hγ⟩
  exact le_trans dist_nonneg (hγ 0)

theorem exists_good_path [PathConnectedSpace X] (u v : X) :
    ∃ γ : Path u v, ∀ t, dist u (γ t) ≤ pathRad u v + dist u v := by
  by_cases h : u = v
  · subst h
    refine ⟨Path.refl u, fun t => ?_⟩
    simp only [Path.refl_apply, dist_self, add_zero]
    exact pathRad_nonneg u u
  · have hne : {r | ∃ γ : Path u v, ∀ t, dist u (γ t) ≤ r}.Nonempty := by
      let γ := PathConnectedSpace.somePath u v
      obtain ⟨r, hr⟩ := (isCompact_range γ.continuous).isBounded.subset_closedBall u
      refine ⟨r, γ, fun t => ?_⟩
      have := hr (mem_range_self t)
      rw [mem_closedBall, dist_comm] at this
      exact this
    obtain ⟨a, ⟨γ, hγ⟩, ha⟩ := Real.lt_sInf_add_pos hne (dist_pos.2 h)
    exact ⟨γ, fun t => (hγ t).trans ha.le⟩

/-- A chosen path of nearly minimal radius. -/
noncomputable def bestPath [PathConnectedSpace X] (u v : X) : Path u v :=
  (exists_good_path u v).choose

/-- If nearby points are joined by small paths, the chosen paths between nearby points are small. -/
theorem bestPath_small [PathConnectedSpace X]
    (hP : ∀ ε > 0, ∃ δ > 0, ∀ x y : X, dist x y < δ → ∃ γ : Path x y, ∀ t, dist x (γ t) ≤ ε)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ u v : X, dist u v < δ → ∀ s : ℝ, dist u ((bestPath u v).extend s) < ε := by
  obtain ⟨δ, hδ, h⟩ := hP (ε / 2) (half_pos hε)
  refine ⟨min δ (ε / 2), lt_min hδ (half_pos hε), fun u v huv s => ?_⟩
  obtain ⟨γ, hγ⟩ := h u v (lt_of_lt_of_le huv (min_le_left _ _))
  have hrad : pathRad u v ≤ ε / 2 := by
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro r ⟨γ', hγ'⟩
      exact le_trans dist_nonneg (hγ' 0)
    · exact ⟨γ, hγ⟩
  have h1 := (exists_good_path u v).choose_spec (projIcc 0 1 zero_le_one s)
  have h2 : dist u v < ε / 2 := lt_of_lt_of_le huv (min_le_right _ _)
  change dist u ((exists_good_path u v).choose (projIcc 0 1 zero_le_one s)) < ε
  linarith

/-! ### Gaps of a closed subset of `[0,1]` -/

section Gaps

variable {K : Set ℝ} (hK : IsClosed K) (hK01 : K ⊆ Icc 0 1) (h0 : (0 : ℝ) ∈ K) (h1 : (1 : ℝ) ∈ K)

/-- The largest point of `K` below `y`. -/
noncomputable def lo (K : Set ℝ) (y : ℝ) : ℝ := sSup (K ∩ Iic y)

/-- The smallest point of `K` above `y`. -/
noncomputable def hi (K : Set ℝ) (y : ℝ) : ℝ := sInf (K ∩ Ici y)

include hK h0 in
theorem lo_mem {y : ℝ} (hy : 0 ≤ y) : lo K y ∈ K ∧ lo K y ≤ y :=
  (hK.inter isClosed_Iic).csSup_mem ⟨0, h0, hy⟩ ⟨y, fun _ h => h.2⟩

include hK h1 in
theorem hi_mem {y : ℝ} (hy : y ≤ 1) : hi K y ∈ K ∧ y ≤ hi K y :=
  (hK.inter isClosed_Ici).csInf_mem ⟨1, h1, hy⟩ ⟨y, fun _ h => h.2⟩

theorem le_lo {y c : ℝ} (hc : c ∈ K) (hcy : c ≤ y) : c ≤ lo K y :=
  le_csSup ⟨y, fun _ h => h.2⟩ ⟨hc, hcy⟩

theorem hi_le {y c : ℝ} (hc : c ∈ K) (hcy : y ≤ c) : hi K y ≤ c :=
  csInf_le ⟨y, fun _ h => h.2⟩ ⟨hc, hcy⟩

include hK hK01 h0 h1 in
/-- Points of a gap: the gap is `(lo, hi)`, and every point of `(lo, hi)` has the same gap. -/
theorem gap_const {y y' : ℝ} (hy : y ∈ Icc (0 : ℝ) 1)
    (hy' : y' ∈ Ioo (lo K y) (hi K y)) :
    y' ∉ K ∧ lo K y' = lo K y ∧ hi K y' = hi K y := by
  have hl := lo_mem hK h0 hy.1
  have hh := hi_mem hK h1 hy.2
  have hy'0 : 0 ≤ y' := le_trans (hK01 hl.1).1 hy'.1.le
  have hy'1 : y' ≤ 1 := le_trans hy'.2.le (hK01 hh.1).2
  have notin : ∀ c ∈ K, c ≤ lo K y ∨ hi K y ≤ c := by
    intro c hc
    rcases le_total c y with h | h
    · exact Or.inl (le_lo hc h)
    · exact Or.inr (hi_le hc h)
  have hy'K : y' ∉ K := fun h => by
    rcases notin y' h with h' | h' <;> linarith [hy'.1, hy'.2]
  have hl' := lo_mem hK h0 hy'0
  have hh' := hi_mem hK h1 hy'1
  refine ⟨hy'K, le_antisymm ?_ (le_lo hl.1 hy'.1.le), le_antisymm (hi_le hh.1 hy'.2.le) ?_⟩
  · rcases notin _ hl'.1 with h | h
    · exact h
    · linarith [hy'.2]
  · rcases notin _ hh'.1 with h | h
    · linarith [hy'.1]
    · exact h

include hK h0 h1 in
theorem lo_lt_of_not_mem {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) (hyK : y ∉ K) :
    lo K y < y ∧ y < hi K y := by
  have hl := lo_mem hK h0 hy.1
  have hh := hi_mem hK h1 hy.2
  exact ⟨lt_of_le_of_ne hl.2 fun h => hyK (h ▸ hl.1),
    lt_of_le_of_ne hh.2 fun h => hyK (h.symm ▸ hh.1)⟩

omit hK hK01 h0 h1 in
theorem abs_sub_le_of_between {y c y' : ℝ} (hm : min y c ≤ y') (hM : y' ≤ max y c) :
    |y' - y| ≤ |c - y| := by
  rcases le_total y c with h | h
  · rw [min_eq_left h] at hm
    rw [max_eq_right h] at hM
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · rw [min_eq_right h] at hm
    rw [max_eq_left h] at hM
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith

end Gaps

/-! ### The extension -/

section Extension

variable [PathConnectedSpace X] (K : Set ℝ) (f : ℝ → X)

/-- The extension of `f` from `K` to `[0,1]`: on a gap `(a, b)` follow the chosen path from `f a`
to `f b`, linearly reparametrised. -/
noncomputable def extend (y : ℝ) : X :=
  open Classical in
  if y ∈ K then f y
  else (bestPath (f (lo K y)) (f (hi K y))).extend ((y - lo K y) / (hi K y - lo K y))

variable {K f}

theorem extend_of_mem {y : ℝ} (hy : y ∈ K) : extend K f y = f y := by
  simp [extend, hy]

theorem extend_of_not_mem {y : ℝ} (hy : y ∉ K) : extend K f y =
    (bestPath (f (lo K y)) (f (hi K y))).extend ((y - lo K y) / (hi K y - lo K y)) := by
  simp [extend, hy]

variable (hK : IsClosed K) (hK01 : K ⊆ Icc 0 1) (h0 : (0 : ℝ) ∈ K) (h1 : (1 : ℝ) ∈ K)
  (hf : ContinuousOn f K)
  (hP : ∀ ε > 0, ∃ δ > 0, ∀ x y : X, dist x y < δ → ∃ γ : Path x y, ∀ t, dist x (γ t) ≤ ε)

include hK hK01 h0 h1 in
theorem continuousAt_extend_of_not_mem {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) (hyK : y ∉ K) :
    ContinuousAt (extend K f) y := by
  have hlt := lo_lt_of_not_mem hK h0 h1 hy hyK
  set a := lo K y
  set b := hi K y
  have hcont : Continuous fun s : ℝ => (bestPath (f a) (f b)).extend ((s - a) / (b - a)) :=
    (bestPath (f a) (f b)).continuous_extend.comp
      ((continuous_id.sub continuous_const).div_const _)
  refine (hcont.continuousAt (x := y)).congr ?_
  filter_upwards [Ioo_mem_nhds hlt.1 hlt.2] with y' hy'
  obtain ⟨hy'K, hl, hh⟩ := gap_const hK hK01 h0 h1 hy hy'
  rw [extend_of_not_mem hy'K, hl, hh]

include hK hK01 h0 h1 hf hP in
theorem continuousWithinAt_extend_of_mem {y : ℝ} (hyK : y ∈ K) :
    ContinuousWithinAt (extend K f) (Icc (0 : ℝ) 1) y := by
  have hy := hK01 hyK
  rw [ContinuousWithinAt, extend_of_mem hyK, Metric.tendsto_nhds]
  intro r hr
  rw [eventually_nhdsWithin_iff]
  obtain ⟨δ, hδ, hsmall⟩ := bestPath_small hP (half_pos hr)
  have hKc : IsCompact K := (isCompact_Icc.of_isClosed_subset hK hK01)
  obtain ⟨η, hη, hunif⟩ := Metric.uniformContinuousOn_iff.1
    (hKc.uniformContinuousOn_of_continuous hf) (min δ (r / 2)) (lt_min hδ (half_pos hr))
  -- the core estimate between two points of `K` at distance less than `η`
  have core : ∀ c ∈ K, |c - y| < η → ∀ y' ∈ Icc (0 : ℝ) 1, min y c ≤ y' → y' ≤ max y c →
      dist (extend K f y') (f y) < r := by
    intro c hc hcy y' hy' hm hM
    have hmK : min y c ∈ K := by rcases min_choice y c with h | h <;> rw [h] <;> assumption
    have hMK : max y c ∈ K := by rcases max_choice y c with h | h <;> rw [h] <;> assumption
    have hwidth : max y c - min y c = |c - y| := by
      rw [max_sub_min_eq_abs, abs_sub_comm]
    by_cases hy'K : y' ∈ K
    · rw [extend_of_mem hy'K]
      have : dist y' y < η := by
        rw [Real.dist_eq]
        exact lt_of_le_of_lt (abs_sub_le_of_between hm hM) hcy
      have := hunif y' hy'K y hyK this
      linarith [min_le_right δ (r / 2)]
    · have hl := lo_mem hK h0 hy'.1
      have hh := hi_mem hK h1 hy'.2
      have hl1 : min y c ≤ lo K y' := le_lo hmK hm
      have hh1 : hi K y' ≤ max y c := hi_le hMK hM
      have hab : dist (lo K y') (hi K y') < η := by
        rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [hl.2, hh.2])]
        linarith
      have hay : dist (lo K y') y < η := by
        rw [Real.dist_eq]
        exact lt_of_le_of_lt (abs_sub_le_of_between hl1 (by linarith [hl.2])) hcy
      have e1 := hunif _ hl.1 _ hh.1 hab
      have e2 := hunif _ hl.1 _ hyK hay
      have e3 := hsmall _ _ (lt_of_lt_of_le e1 (min_le_left _ _))
        ((y' - lo K y') / (hi K y' - lo K y'))
      rw [extend_of_not_mem hy'K]
      calc dist _ (f y) ≤ dist _ (f (lo K y')) + dist (f (lo K y')) (f y) := dist_triangle _ _ _
        _ < r / 2 + r / 2 := by
          rw [dist_comm]
          exact add_lt_add e3 (lt_of_lt_of_le e2 (min_le_right _ _))
        _ = r := by ring
  rw [← nhdsLE_sup_nhdsGE, Filter.eventually_sup]
  constructor
  · -- from the left
    by_cases hA : ∃ c ∈ K, y - η < c ∧ c < y
    · obtain ⟨c, hc, hc1, hc2⟩ := hA
      filter_upwards [Ioc_mem_nhdsLE hc2] with y' hy' hy'01
      refine core c hc ?_ y' hy'01 ?_ ?_
      · rw [abs_lt]; constructor <;> linarith
      · rw [min_eq_right hc2.le]; exact hy'.1.le
      · rw [max_eq_left hc2.le]; exact hy'.2
    · by_cases hy0 : 0 < y
      · set y'' := max (y - η / 2) 0 with hy''
        have hy''1 : y'' < y := max_lt (by linarith) hy0
        have hy''2 : y - η < y'' := lt_of_lt_of_le (by linarith) (le_max_left _ _)
        have hy''01 : y'' ∈ Icc (0 : ℝ) 1 := ⟨le_max_right _ _, by linarith [hy.2]⟩
        have hy''K : y'' ∉ K := fun h => hA ⟨y'', h, hy''2, hy''1⟩
        have hhi : hi K y'' = y := by
          refine le_antisymm (hi_le hyK hy''1.le) ?_
          have hh := hi_mem hK h1 hy''01.2
          by_contra hlt
          exact hA ⟨_, hh.1, by linarith [hh.2], lt_of_not_ge hlt⟩
        set a := lo K y''
        have hlt := lo_lt_of_not_mem hK h0 h1 hy''01 hy''K
        rw [hhi] at hlt
        have hcont : Continuous fun s : ℝ => (bestPath (f a) (f y)).extend ((s - a) / (y - a)) :=
          (bestPath (f a) (f y)).continuous_extend.comp
            ((continuous_id.sub continuous_const).div_const _)
        have hval : (bestPath (f a) (f y)).extend ((y - a) / (y - a)) = f y := by
          rw [div_self (by linarith [hlt.1, hlt.2])]; exact Path.extend_one _
        have hT := hcont.continuousAt (x := y)
        rw [ContinuousAt, hval, Metric.tendsto_nhds] at hT
        filter_upwards [Ioc_mem_nhdsLE (show a < y by linarith [hlt.1, hlt.2]),
          nhdsWithin_le_nhds (hT r hr)] with y' hy' hy'r _
        rcases eq_or_lt_of_le hy'.2 with h | h
        · rw [h, extend_of_mem hyK, dist_self]; exact hr
        · have hmem : y' ∈ Ioo (lo K y'') (hi K y'') := by rw [hhi]; exact ⟨hy'.1, h⟩
          obtain ⟨hy'K, hl, hh⟩ := gap_const hK hK01 h0 h1 hy''01 hmem
          rw [extend_of_not_mem hy'K, hl, hh, hhi]
          exact hy'r
      · filter_upwards [self_mem_nhdsWithin] with y' hy' hy'01
        have : y' = y := le_antisymm hy' (by linarith [hy'01.1])
        rw [this, extend_of_mem hyK, dist_self]; exact hr
  · -- from the right
    by_cases hA : ∃ c ∈ K, y < c ∧ c < y + η
    · obtain ⟨c, hc, hc1, hc2⟩ := hA
      filter_upwards [Ico_mem_nhdsGE hc1] with y' hy' hy'01
      refine core c hc ?_ y' hy'01 ?_ ?_
      · rw [abs_lt]; constructor <;> linarith
      · rw [min_eq_left hc1.le]; exact hy'.1
      · rw [max_eq_right hc1.le]; exact hy'.2.le
    · by_cases hy1 : y < 1
      · set y'' := min (y + η / 2) 1 with hy''
        have hy''1 : y < y'' := lt_min (by linarith) hy1
        have hy''2 : y'' < y + η := lt_of_le_of_lt (min_le_left _ _) (by linarith)
        have hy''01 : y'' ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hy.1], min_le_right _ _⟩
        have hy''K : y'' ∉ K := fun h => hA ⟨y'', h, hy''1, hy''2⟩
        have hlo : lo K y'' = y := by
          refine le_antisymm ?_ (le_lo hyK hy''1.le)
          have hl := lo_mem hK h0 hy''01.1
          by_contra hlt
          exact hA ⟨_, hl.1, lt_of_not_ge hlt, by linarith [hl.2]⟩
        set b := hi K y''
        have hlt := lo_lt_of_not_mem hK h0 h1 hy''01 hy''K
        rw [hlo] at hlt
        have hcont : Continuous fun s : ℝ => (bestPath (f y) (f b)).extend ((s - y) / (b - y)) :=
          (bestPath (f y) (f b)).continuous_extend.comp
            ((continuous_id.sub continuous_const).div_const _)
        have hval : (bestPath (f y) (f b)).extend ((y - y) / (b - y)) = f y := by
          rw [sub_self, zero_div]; exact Path.extend_zero _
        have hT := hcont.continuousAt (x := y)
        rw [ContinuousAt, hval, Metric.tendsto_nhds] at hT
        filter_upwards [Ico_mem_nhdsGE (show y < b by linarith [hlt.1, hlt.2]),
          nhdsWithin_le_nhds (hT r hr)] with y' hy' hy'r _
        rcases eq_or_lt_of_le hy'.1 with h | h
        · rw [← h, extend_of_mem hyK, dist_self]; exact hr
        · have hmem : y' ∈ Ioo (lo K y'') (hi K y'') := by rw [hlo]; exact ⟨h, hy'.2⟩
          obtain ⟨hy'K, hl, hh⟩ := gap_const hK hK01 h0 h1 hy''01 hmem
          rw [extend_of_not_mem hy'K, hl, hh, hlo]
          exact hy'r
      · filter_upwards [self_mem_nhdsWithin] with y' hy' hy'01
        have : y' = y := le_antisymm (by linarith [hy'01.2]) hy'
        rw [this, extend_of_mem hyK, dist_self]; exact hr

include hK hK01 h0 h1 hf hP in
/-- **Extension over the gaps.**  A continuous map on a closed subset `K` of `[0,1]` containing `0`
and `1`, with values in a uniformly locally path connected compact metric space, extends to a
continuous map on `[0,1]`. -/
theorem continuousOn_extend : ContinuousOn (extend K f) (Icc (0 : ℝ) 1) := by
  intro y hy
  by_cases hyK : y ∈ K
  · exact continuousWithinAt_extend_of_mem hK hK01 h0 h1 hf hP hyK
  · exact (continuousAt_extend_of_not_mem hK hK01 h0 h1 hy hyK).continuousWithinAt

end Extension

/-- `1` belongs to the Cantor set. -/
theorem one_mem_cantorSet : (1 : ℝ) ∈ cantorSet := by
  have : ∀ n, (1 : ℝ) ∈ preCantorSet n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [preCantorSet_succ]
      exact Or.inr ⟨1, ih, by norm_num⟩
  simpa [cantorSet] using this

end HMExt

/-- **Hahn-Mazurkiewicz theorem** (the "if" direction of Morris, Theorem 9.5.12, TP-235).  A
compact, connected, locally connected, metrizable Hausdorff space is a continuous image of the unit
interval `[0,1]`. -/
@[kb "morris2024" "Theorem 9.5.12, p. 253"]
theorem exists_continuous_surjective_unitInterval_of_peano {X : Type*} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [LocallyConnectedSpace X]
    [TopologicalSpace.MetrizableSpace X] :
    ∃ f : unitInterval → X, Continuous f ∧ Function.Surjective f := by
  classical
  let _ : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  have : LocallyPathConnectedSpace X := HMPaths.locallyPathConnectedSpace_of_compact_locallyConnected
  have : PathConnectedSpace X := PathConnectedSpace.of_locallyPathConnectedSpace
  have hP : ∀ ε > 0, ∃ δ > 0, ∀ x y : X, dist x y < δ → ∃ γ : Path x y, ∀ t, dist x (γ t) ≤ ε :=
    fun ε hε => HMPaths.exists_path_of_dist_lt hε
  obtain ⟨F, hFc, hFs⟩ := exists_nat_bool_continuous_surjective_of_compact X
  let e := cantorSetHomeomorphNatToBool
  let f0 : ℝ → X := fun t =>
    if h : t ∈ cantorSet then F (e ⟨t, h⟩) else F fun _ => false
  have hf0 : ContinuousOn f0 cantorSet := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : cantorSet.domRestrict f0 = F ∘ e := by
      funext t
      simp [f0, t.2]
    rw [this]
    exact hFc.comp e.continuous
  have hc := HMExt.continuousOn_extend isClosed_cantorSet cantorSet_subset_unitInterval
    zero_mem_cantorSet HMExt.one_mem_cantorSet hf0 hP
  refine ⟨fun t => HMExt.extend cantorSet f0 t,
    hc.comp_continuous continuous_subtype_val (fun t => t.2), fun x => ?_⟩
  obtain ⟨s, rfl⟩ := hFs x
  let t := e.symm s
  refine ⟨⟨t, cantorSet_subset_unitInterval t.2⟩, ?_⟩
  simp only
  rw [HMExt.extend_of_mem t.2]
  simp [f0, t.2, t]

/-- **Morris, Theorem 9.5.12 (Hahn-Mazurkiewicz), both directions.**  A Hausdorff space is a
continuous image of `[0,1]` if and only if it is compact, connected, locally connected and
metrizable. -/
@[kb "morris2024" "Theorem 9.5.12, p. 253"]
theorem exists_continuous_surjective_unitInterval_iff {X : Type*} [TopologicalSpace X]
    [T2Space X] :
    (∃ f : unitInterval → X, Continuous f ∧ Function.Surjective f) ↔
      CompactSpace X ∧ ConnectedSpace X ∧ LocallyConnectedSpace X ∧
        TopologicalSpace.MetrizableSpace X := by
  constructor
  · rintro ⟨f, hf, hs⟩
    exact compact_connected_locallyConnected_metrizable_of_continuous_surjective_unitInterval hf hs
  · rintro ⟨_, _, _, _⟩
    exact exists_continuous_surjective_unitInterval_of_peano

end UndergradKB.Topology
