import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Bases
import Mathlib.Topology.Connected.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import UndergradKB.Common.Attr

/-!
# `ε`-coverings and the first lemmas on Hausdorff measure

Morris, *Topology Without Tears* (2024), Appendix 4, Section A4.1 (`morris2024`): `ε`-coverings, countable
`ε`-coverings and separability, the quantities `H^s_ε` of Definition A4.1.4, Lemma A4.1.7, the reduction to
open coverings (Proposition A4.1.21) and the diameter lemma for connected sets (Lemma A4.1.22).

Diameters are `Metric.ediam` (values in `ℝ≥0∞`); for sets of diameter `< ε` this agrees with the real-valued
diameter (see `isEpsCovering_iff_bounded_diam_lt`). Coverings are `ℕ`-indexed families (a finite family is
padded with empty sets).
-/

open Set Function Filter
open scoped ENNReal NNReal Topology

namespace UndergradKB.Topology

section Covers

variable {X : Type*} [MetricSpace X]

/-- An *`ε`-covering* of `Y`: a family of sets covering `Y`, each of diameter `< ε`. -/
def IsEpsCovering {ι : Type*} (ε : ℝ) (Y : Set X) (U : ι → Set X) : Prop :=
  Y ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) < ENNReal.ofReal ε

/-- Morris, Topology Without Tears, Definition A4.1.2 (TP-457). In terms of the real-valued diameter: the
members of an `ε`-covering are bounded of diameter `< ε`. -/
@[kb "morris2024" "Definition A4.1.2, p. 472"]
theorem isEpsCovering_iff_bounded_diam_lt {ι : Type*} (ε : ℝ) (Y : Set X) (U : ι → Set X) :
    IsEpsCovering ε Y U ↔
      Y ⊆ ⋃ i, U i ∧ ∀ i, Bornology.IsBounded (U i) ∧ Metric.diam (U i) < ε := by
  unfold IsEpsCovering
  refine and_congr_right fun _ => forall_congr' fun i => ?_
  constructor
  · intro h
    have hne : Metric.ediam (U i) ≠ ⊤ := (h.trans ENNReal.ofReal_lt_top).ne
    exact ⟨Metric.isBounded_iff_ediam_ne_top.mpr hne, (ENNReal.lt_ofReal_iff_toReal_lt hne).mp h⟩
  · rintro ⟨hb, hd⟩
    have hne : Metric.ediam (U i) ≠ ⊤ := Metric.isBounded_iff_ediam_ne_top.mp hb
    exact (ENNReal.lt_ofReal_iff_toReal_lt hne).mpr hd

/-- Morris, Topology Without Tears, Proposition A4.1.3 (TP-458). A subset `Y` of a metric space has a
countable `ε`-covering for every `ε > 0` if and only if it is separable. -/
@[kb "morris2024" "Proposition A4.1.3, p. 472"]
theorem forall_exists_isEpsCovering_iff_isSeparable (Y : Set X) :
    (∀ ε > 0, ∃ U : ℕ → Set X, IsEpsCovering ε Y U) ↔ TopologicalSpace.IsSeparable Y := by
  constructor
  · intro h
    choose U hU using fun n : ℕ => h (1 / ((n : ℝ) + 1)) (by positivity)
    let t : Set X := ⋃ p : ℕ × ℕ, {y | ∃ h : (Y ∩ U p.1 p.2).Nonempty, y = h.some}
    have htc : t.Countable := by
      refine Set.countable_iUnion fun p => ?_
      refine Set.Subsingleton.countable ?_
      rintro y ⟨h1, rfl⟩ z ⟨h2, rfl⟩
      rfl
    refine ⟨t, htc, fun y hy => ?_⟩
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ((hU n).1 hy)
    have hne : (Y ∩ U n i).Nonempty := ⟨y, hy, hi⟩
    refine ⟨hne.some, Set.mem_iUnion.mpr ⟨(n, i), hne, rfl⟩, ?_⟩
    have hb : hne.some ∈ U n i := hne.some_mem.2
    have h1 : edist y hne.some ≤ Metric.ediam (U n i) := Metric.edist_le_ediam_of_mem hi hb
    have h2 := h1.trans_lt ((hU n).2 i)
    rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff (by positivity)] at h2
    exact h2.trans hn
  · rintro ⟨c, hc, hYc⟩ ε hε
    by_cases hce : c.Nonempty
    · obtain ⟨g, hg⟩ := hc.exists_eq_range hce
      refine ⟨fun i => Metric.ball (g i) (ε / 3), fun y hy => ?_, fun i => ?_⟩
      · have := hYc hy
        rw [hg, Metric.mem_closure_iff] at this
        obtain ⟨b, ⟨i, rfl⟩, hb⟩ := this (ε / 3) (by positivity)
        exact Set.mem_iUnion.mpr ⟨i, Metric.mem_ball.mpr hb⟩
      · have : Metric.ediam (Metric.ball (g i) (ε / 3)) ≤ ENNReal.ofReal (2 * (ε / 3)) := by
          rw [Metric.ediam_le_iff]
          intro x hx y hy
          rw [edist_dist]
          apply ENNReal.ofReal_le_ofReal
          have := Metric.mem_ball.mp hx
          have := Metric.mem_ball.mp hy
          have := dist_triangle_right x y (g i)
          linarith
        exact this.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith))
    · rw [Set.not_nonempty_iff_eq_empty] at hce
      subst hce
      refine ⟨fun _ => ∅, fun y hy => ?_, fun i => ?_⟩
      · have := hYc hy
        simp at this
      · simpa using hε

/-- Morris, Topology Without Tears, Proposition A4.1.3 (TP-458). The same statement with "separable" read
as `SeparableSpace` of the subspace `(Y, d₁)` with the induced metric. -/
@[kb "morris2024" "Proposition A4.1.3, p. 472"]
theorem forall_exists_isEpsCovering_iff_separableSpace (Y : Set X) :
    (∀ ε > 0, ∃ U : ℕ → Set X, IsEpsCovering ε Y U) ↔ TopologicalSpace.SeparableSpace Y := by
  rw [forall_exists_isEpsCovering_iff_isSeparable]
  exact ⟨fun h => h.separableSpace, fun h => TopologicalSpace.IsSeparable.of_subtype Y⟩

/-! ### The quantities `H^s_ε` -/

/-- Hausdorff's `H^s_ε(Y)`: the infimum of `∑ (diam U_i)^s` over countable `ε`-coverings `{U_i}` of `Y`. -/
noncomputable def hausdorffEps (s ε : ℝ) (Y : Set X) : ℝ≥0∞ :=
  ⨅ U : {U : ℕ → Set X // IsEpsCovering ε Y U}, ∑' i, Metric.ediam (U.1 i) ^ s

/-- The variant `O^s_ε(Y)` using only coverings by open sets. -/
noncomputable def hausdorffEpsOpen (s ε : ℝ) (Y : Set X) : ℝ≥0∞ :=
  ⨅ U : {U : ℕ → Set X // IsEpsCovering ε Y U ∧ ∀ i, IsOpen (U i)}, ∑' i, Metric.ediam (U.1 i) ^ s

/-- Morris, Topology Without Tears, Lemma A4.1.7 (i) (TP-460). For `0 < s < t` and `ε < 1`:
`H^t_ε ≤ H^s_ε`. -/
@[kb "morris2024" "Lemma A4.1.7, p. 474"]
theorem hausdorffEps_le_of_lt {s t ε : ℝ} (hst : s < t) (hε1 : ε < 1) (Y : Set X) : hausdorffEps t ε Y ≤ hausdorffEps s ε Y := by
  refine le_iInf fun U => (iInf_le _ U).trans ?_
  refine tsum_le_tsum fun i => ?_
  have hd : Metric.ediam (U.1 i) ≤ 1 :=
    (U.2.2 i).le.trans (ENNReal.ofReal_le_one.mpr hε1.le)
  exact ENNReal.rpow_le_rpow_of_exponent_ge hd hst.le

/-- Morris, Topology Without Tears, Lemma A4.1.7 (ii) (TP-460). For `0 < s < t` and `ε < 1`:
`H^t_ε ≤ ε^(t-s) H^s_ε`. -/
@[kb "morris2024" "Lemma A4.1.7, p. 474"]
theorem hausdorffEps_le_mul_of_lt {s t ε : ℝ} (hs : 0 < s) (hst : s < t) (hε : 0 < ε) (Y : Set X) :
    hausdorffEps t ε Y ≤ ENNReal.ofReal (ε ^ (t - s)) * hausdorffEps s ε Y := by
  have hc0 : ENNReal.ofReal (ε ^ (t - s)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hε _)).ne'
  unfold hausdorffEps
  rw [ENNReal.mul_iInf_of_ne hc0 ENNReal.ofReal_ne_top]
  refine le_iInf fun U => (iInf_le _ U).trans ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun i => ?_
  set d := Metric.ediam (U.1 i) with hd
  have hlt : d < ENNReal.ofReal ε := U.2.2 i
  by_cases h0 : d = 0
  · rw [h0, ENNReal.zero_rpow_of_pos (by linarith), ENNReal.zero_rpow_of_pos hs]; simp
  have htop : d ≠ ⊤ := (hlt.trans ENNReal.ofReal_lt_top).ne
  have : d ^ t = d ^ (t - s) * d ^ s := by
    rw [← ENNReal.rpow_add _ _ h0 htop]; congr 1; ring
  rw [this, ← ENNReal.ofReal_rpow_of_nonneg hε.le (by linarith)]
  exact mul_le_mul_left (ENNReal.rpow_le_rpow hlt.le (by linarith)) _

/-- Thickening a set slightly keeps the diameter below `ε` and changes `(diam)^s` by an arbitrarily small
amount. -/
private lemma exists_thickening_param {s ε : ℝ} (hs : 0 ≤ s) {d : ℝ≥0∞} (hd : d < ENNReal.ofReal ε)
    {η : ℝ≥0} (hη : 0 < η) :
    ∃ δ : ℝ≥0, 0 < δ ∧ d + 2 * δ < ENNReal.ofReal ε ∧ (d + 2 * δ) ^ s ≤ d ^ s + η := by
  have hdtop : d ≠ ⊤ := (hd.trans ENNReal.ofReal_lt_top).ne
  have hg : Continuous fun δ : ℝ≥0 => d + 2 * (δ : ℝ≥0∞) :=
    continuous_const.add ((ENNReal.continuous_const_mul (by simp)).comp ENNReal.continuous_coe)
  have hA : IsOpen {x : ℝ≥0∞ | x < ENNReal.ofReal ε} := isOpen_Iio
  have hB : IsOpen {x : ℝ≥0∞ | x ^ s < d ^ s + η} :=
    isOpen_lt (ENNReal.continuous_rpow_const.comp continuous_id) continuous_const
  have hdsne : d ^ s ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hs hdtop
  have h0 : (0 : ℝ≥0) ∈ (fun δ : ℝ≥0 => d + 2 * (δ : ℝ≥0∞)) ⁻¹' ({x | x < ENNReal.ofReal ε} ∩
      {x | x ^ s < d ^ s + η}) := by
    refine ⟨by simpa using hd, ?_⟩
    simpa using ENNReal.lt_add_right hdsne (by simpa using hη.ne')
  have hopen := ((hA.inter hB).preimage hg).mem_nhds h0
  obtain ⟨δ, hδ, hδ'⟩ := (Filter.eventually_of_mem hopen fun x hx => hx).exists_gt
  exact ⟨δ, hδ, hδ'.1, hδ'.2.le⟩

/-- Morris, Topology Without Tears, Proposition A4.1.21 (TP-471). For `s > 0`, the infimum defining `H^s_ε`
may be taken over coverings by open sets only: `O^s_ε(Y) = H^s_ε(Y)`. (The limit formula for `H^s` then
follows at once.) -/
@[kb "morris2024" "Proposition A4.1.21, p. 478"]
theorem hausdorffEpsOpen_eq {s ε : ℝ} (hs : 0 < s) (Y : Set X) :
    hausdorffEpsOpen s ε Y = hausdorffEps s ε Y := by
  apply le_antisymm
  · refine le_iInf fun U => ?_
    apply ENNReal.le_of_forall_pos_le_add
    intro η hη _
    obtain ⟨η', hη'pos, hη'sum⟩ := ENNReal.exists_pos_sum_of_countable (ε := (η : ℝ≥0∞))
      (by simpa using hη.ne') ℕ
    have hex : ∀ i, ∃ δ : ℝ≥0, 0 < δ ∧ Metric.ediam (U.1 i) + 2 * δ < ENNReal.ofReal ε ∧
        (Metric.ediam (U.1 i) + 2 * δ) ^ s ≤ Metric.ediam (U.1 i) ^ s + η' i :=
      fun i => exists_thickening_param hs.le (U.2.2 i) (hη'pos i)
    choose δ hδpos hδlt hδle using hex
    let O : ℕ → Set X := fun i => Metric.thickening (δ i : ℝ) (U.1 i)
    have hO : IsEpsCovering ε Y O ∧ ∀ i, IsOpen (O i) := by
      refine ⟨⟨?_, fun i => ?_⟩, fun i => Metric.isOpen_thickening⟩
      · intro y hy
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (U.2.1 hy)
        exact Set.mem_iUnion.mpr ⟨i, Metric.self_subset_thickening (by exact_mod_cast hδpos i) _ hi⟩
      · exact (Metric.ediam_thickening_le (δ i)).trans_lt (hδlt i)
    refine (iInf_le _ ⟨O, hO⟩).trans ?_
    calc ∑' i, Metric.ediam (O i) ^ s
        ≤ ∑' i, (Metric.ediam (U.1 i) ^ s + η' i) := by
          refine tsum_le_tsum fun i => ?_
          exact (ENNReal.rpow_le_rpow (Metric.ediam_thickening_le (δ i)) hs.le).trans (hδle i)
      _ = ∑' i, Metric.ediam (U.1 i) ^ s + ∑' i, (η' i : ℝ≥0∞) := tsum_add
      _ ≤ ∑' i, Metric.ediam (U.1 i) ^ s + η := add_le_add le_rfl hη'sum.le
  · refine le_iInf fun U => ?_
    exact iInf_le (fun V : {V : ℕ → Set X // IsEpsCovering ε Y V} => ∑' i, Metric.ediam (V.1 i) ^ s)
      ⟨U.1, U.2.1⟩

end Covers

/-! ### Connected sets -/

section Connected

variable {X : Type*} [MetricSpace X]

/-- Morris, Topology Without Tears, Lemma A4.1.22 (TP-472). If a (pre)connected set `Y` is covered by countably
many sets `U i` (for instance open sets), then `diam Y ≤ ∑ diam (U i)` (diameters in `ℝ≥0∞`). Neither
openness nor separability is needed. -/
@[kb "morris2024" "Lemma A4.1.22, p. 478"]
theorem ediam_le_tsum_ediam_of_isPreconnected {ι : Type*} [Countable ι] {Y : Set X}
    (hY : IsPreconnected Y) {U : ι → Set X} (hU : Y ⊆ ⋃ i, U i) :
    Metric.ediam Y ≤ ∑' i, Metric.ediam (U i) := by
  rw [Metric.ediam_le_iff]
  intro x hx y hy
  set g : X → ℝ := fun z => dist x z with hg
  have hgc : Continuous g := continuous_const.dist continuous_id
  have hgl : LipschitzWith 1 g := LipschitzWith.dist_right x
  have hconn : IsPreconnected (g '' Y) := hY.image g hgc.continuousOn
  have hsub : Icc 0 (dist x y) ⊆ g '' Y :=
    hconn.Icc_subset ⟨x, hx, by simp [hg]⟩ ⟨y, hy, rfl⟩
  have hcover : g '' Y ⊆ ⋃ i, g '' U i := by
    rw [← Set.image_iUnion]; exact Set.image_mono hU
  calc edist x y = MeasureTheory.volume (Icc 0 (dist x y)) := by
        rw [Real.volume_Icc, edist_dist]; simp
    _ ≤ MeasureTheory.volume (⋃ i, g '' U i) :=
        MeasureTheory.measure_mono (hsub.trans hcover)
    _ ≤ ∑' i, MeasureTheory.volume (g '' U i) := MeasureTheory.measure_iUnion_le _
    _ ≤ ∑' i, Metric.ediam (g '' U i) := tsum_le_tsum fun i => Real.volume_le_diam _
    _ ≤ ∑' i, Metric.ediam (U i) := by
        refine tsum_le_tsum fun i => ?_
        simpa using hgl.ediam_image_le (U i)

/-- Morris, Topology Without Tears, Lemma A4.1.22 (TP-472). The book's form: a connected set covered by open
sets `O i` has `diam Y ≤ ∑ diam (O i)`. -/
@[kb "morris2024" "Lemma A4.1.22, p. 478"]
theorem ediam_le_tsum_ediam_of_isConnected_isOpen {Y : Set X} (hY : IsConnected Y) {O : ℕ → Set X}
    (_hO : ∀ i, IsOpen (O i)) (hcov : Y ⊆ ⋃ i, O i) :
    Metric.ediam Y ≤ ∑' i, Metric.ediam (O i) :=
  ediam_le_tsum_ediam_of_isPreconnected hY.isPreconnected hcov

end Connected

end UndergradKB.Topology
