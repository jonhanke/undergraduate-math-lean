import UndergradKB.Topology.BanachEmbedding
import Mathlib.Topology.Instances.CantorSet
import Mathlib.Topology.MetricSpace.HausdorffAlexandroff
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.ContinuousMap.Compact
import UndergradKB.Common.Attr

/-!
# The Banach-Mazur theorem (Morris, Remark 12.2.31)

Every separable real Banach space embeds linearly isometrically into `C([0,1], ℝ)`.  Route: the weak-*
unit ball `K` of the dual is compact metrizable, so the Cantor set maps onto `K`
(Hausdorff-Alexandroff); composition gives a linear isometry `C(K) → C(Cantor set)`; and functions on
a closed subset `F ⊆ [0,1]` containing `0, 1` are extended linearly over the omitted intervals,
which gives a linear isometry `C(F) → C([0,1])`.
-/

open Set Metric Filter
open scoped _root_.Topology

namespace UndergradKB.Topology

/-! ### Gaps of a closed subset of `[0,1]` -/

/-- Left end of the gap of `F` around `t`: the largest point of `F` below `t`. -/
noncomputable def gapL (F : Set ℝ) (t : ℝ) : ℝ := sSup (F ∩ Iic t)

/-- Right end of the gap of `F` around `t`: the smallest point of `F` above `t`. -/
noncomputable def gapR (F : Set ℝ) (t : ℝ) : ℝ := sInf (F ∩ Ici t)

section Gap

variable {F : Set ℝ}

theorem gapL_mem (hF : IsClosed F) (h0 : 0 ∈ F) {t : ℝ} (ht : 0 ≤ t) :
    gapL F t ∈ F ∧ gapL F t ≤ t := by
  have hne : (F ∩ Iic t).Nonempty := ⟨0, h0, ht⟩
  have hbdd : BddAbove (F ∩ Iic t) := ⟨t, fun x hx => hx.2⟩
  have hcl : IsClosed (F ∩ Iic t) := hF.inter isClosed_Iic
  exact ⟨(hcl.csSup_mem hne hbdd).1, csSup_le hne (fun x hx => hx.2)⟩

theorem gapR_mem (hF : IsClosed F) (h1 : 1 ∈ F) {t : ℝ} (ht : t ≤ 1) :
    gapR F t ∈ F ∧ t ≤ gapR F t := by
  have hne : (F ∩ Ici t).Nonempty := ⟨1, h1, ht⟩
  have hbdd : BddBelow (F ∩ Ici t) := ⟨t, fun x hx => hx.2⟩
  have hcl : IsClosed (F ∩ Ici t) := hF.inter isClosed_Ici
  exact ⟨(hcl.csInf_mem hne hbdd).1, le_csInf hne (fun x hx => hx.2)⟩

theorem le_gapL {x t : ℝ} (hx : x ∈ F) (hxt : x ≤ t) : x ≤ gapL F t :=
  le_csSup ⟨t, fun y hy => hy.2⟩ ⟨hx, hxt⟩

theorem gapR_le {x t : ℝ} (hx : x ∈ F) (htx : t ≤ x) : gapR F t ≤ x :=
  csInf_le ⟨t, fun y hy => hy.2⟩ ⟨hx, htx⟩

theorem le_gapL_or_gapR_le {x t : ℝ} (hx : x ∈ F) : x ≤ gapL F t ∨ gapR F t ≤ x := by
  rcases le_total x t with h | h
  · exact Or.inl (le_gapL hx h)
  · exact Or.inr (gapR_le hx h)

theorem gapL_lt (hF : IsClosed F) (h0 : 0 ∈ F) {t : ℝ} (ht : 0 ≤ t) (htF : t ∉ F) :
    gapL F t < t :=
  lt_of_le_of_ne (gapL_mem hF h0 ht).2 (fun e => htF (e ▸ (gapL_mem hF h0 ht).1))

theorem lt_gapR (hF : IsClosed F) (h1 : 1 ∈ F) {t : ℝ} (ht : t ≤ 1) (htF : t ∉ F) :
    t < gapR F t :=
  lt_of_le_of_ne (gapR_mem hF h1 ht).2 (fun e => htF (e ▸ (gapR_mem hF h1 ht).1))

/-- Inside the gap around `t`, the gap ends are constant and the points are not in `F`. -/
theorem gap_local (hF : IsClosed F) (h0 : 0 ∈ F) (h1 : 1 ∈ F) {t t' : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (htF : t ∉ F) (h : t' ∈ Ioo (gapL F t) (gapR F t)) :
    t' ∉ F ∧ gapL F t' = gapL F t ∧ gapR F t' = gapR F t := by
  obtain ⟨huF, _⟩ := gapL_mem hF h0 ht0
  obtain ⟨hvF, _⟩ := gapR_mem hF h1 ht1
  refine ⟨fun hF' => ?_, ?_, ?_⟩
  · rcases le_gapL_or_gapR_le (t := t) hF' with h' | h'
    · exact absurd h.1 (not_lt.2 h')
    · exact absurd h.2 (not_lt.2 h')
  · refine IsGreatest.csSup_eq ⟨⟨huF, h.1.le⟩, ?_⟩
    rintro x ⟨hxF, hxt⟩
    rcases le_gapL_or_gapR_le (t := t) hxF with h' | h'
    · exact h'
    · exact absurd (lt_of_le_of_lt (h'.trans hxt) h.2) (lt_irrefl _)
  · refine IsLeast.csInf_eq ⟨⟨hvF, h.2.le⟩, ?_⟩
    rintro x ⟨hxF, hxt⟩
    rcases le_gapL_or_gapR_le (t := t) hxF with h' | h'
    · exact absurd (lt_of_lt_of_le h.1 (hxt.trans h')) (lt_irrefl _)
    · exact h'

end Gap

/-! ### Linear interpolation over the gaps -/

open Classical in
/-- Extension of `g` from `F` to `ℝ`: equal to `g` on `F`, and linear on each gap. -/
noncomputable def gapExt (F : Set ℝ) (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t ∈ F then g t
  else g (gapL F t) + (t - gapL F t) / (gapR F t - gapL F t) * (g (gapR F t) - g (gapL F t))

theorem gapExt_of_mem {F : Set ℝ} {g : ℝ → ℝ} {t : ℝ} (h : t ∈ F) : gapExt F g t = g t := by
  unfold gapExt; rw [if_pos h]

theorem gapExt_of_notMem {F : Set ℝ} {g : ℝ → ℝ} {t : ℝ} (h : t ∉ F) :
    gapExt F g t = g (gapL F t) + (t - gapL F t) / (gapR F t - gapL F t) *
      (g (gapR F t) - g (gapL F t)) := by
  unfold gapExt; rw [if_neg h]

/-- Algebra of one interpolation step. -/
theorem interp_close {A B C ε M l : ℝ} (hε : 0 < ε) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hAM : |A| ≤ M)
    (hBM : |B| ≤ M) (hA : |A - C| < ε) (hB : |B - C| < ε ∨ l * (2 * M) ≤ ε) :
    |A + l * (B - A) - C| < 2 * ε := by
  rcases hB with hB | hB
  · rw [abs_lt] at hA hB ⊢
    have e1 : (1 - l) * (A - C) ≤ (1 - l) * ε := mul_le_mul_of_nonneg_left hA.2.le (by linarith)
    have e2 : l * (B - C) ≤ l * ε := mul_le_mul_of_nonneg_left hB.2.le hl0
    have e3 : (1 - l) * (-ε) ≤ (1 - l) * (A - C) := mul_le_mul_of_nonneg_left hA.1.le (by linarith)
    have e4 : l * (-ε) ≤ l * (B - C) := mul_le_mul_of_nonneg_left hB.1.le hl0
    constructor <;> nlinarith
  · have hBA : |B - A| ≤ 2 * M := by
      calc |B - A| ≤ |B| + |A| := abs_sub _ _
        _ ≤ 2 * M := by linarith
    have : |A + l * (B - A) - C| ≤ |A - C| + l * (2 * M) := by
      calc |A + l * (B - A) - C| = |(A - C) + l * (B - A)| := by ring_nf
        _ ≤ |A - C| + |l * (B - A)| := abs_add_le _ _
        _ ≤ |A - C| + l * (2 * M) := by
          rw [abs_mul, abs_of_nonneg hl0]
          have := mul_le_mul_of_nonneg_left hBA hl0
          linarith
    linarith

section Continuity

variable {F : Set ℝ} {g : ℝ → ℝ} {M : ℝ}

/-- Right-hand estimate near a point `t0 ∈ F`. -/
theorem gapExt_right_est (hF : IsClosed F) (h0 : 0 ∈ F) (h1 : 1 ∈ F) (hM : ∀ x ∈ F, |g x| ≤ M)
    {t0 : ℝ} (ht0 : t0 ∈ F) {ε δ0 : ℝ} (hε : 0 < ε) (hδ0 : 0 < δ0)
    (hclose : ∀ x ∈ F, |x - t0| < δ0 → |g x - g t0| < ε) {t : ℝ} (ht0' : 0 ≤ t) (ht1 : t ≤ 1)
    (hlt : t0 < t) (hδ : t - t0 < δ0 / 2) (hsmall : 4 * M * (t - t0) ≤ ε * δ0) :
    |gapExt F g t - g t0| < 2 * ε := by
  by_cases htF : t ∈ F
  · rw [gapExt_of_mem htF]
    have := hclose t htF (by rw [abs_of_pos (by linarith)]; linarith)
    linarith
  rw [gapExt_of_notMem htF]
  obtain ⟨huF, hut⟩ := gapL_mem hF h0 ht0'
  obtain ⟨hvF, htv⟩ := gapR_mem hF h1 ht1
  have hu0 : t0 ≤ gapL F t := le_gapL ht0 hlt.le
  have hult : gapL F t < t := gapL_lt hF h0 ht0' htF
  have hltv : t < gapR F t := lt_gapR hF h1 ht1 htF
  set u := gapL F t
  set v := gapR F t
  have hvu : 0 < v - u := by linarith
  have hl0 : 0 ≤ (t - u) / (v - u) := div_nonneg (by linarith) hvu.le
  have hl1 : (t - u) / (v - u) ≤ 1 := (div_le_one hvu).2 (by linarith)
  have hA : |g u - g t0| < ε := hclose u huF (by rw [abs_of_nonneg (by linarith)]; linarith)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM t0 ht0)
  refine interp_close hε hl0 hl1 (hM u huF) (hM v hvF) hA ?_
  by_cases hv : v < t0 + δ0
  · left
    exact hclose v hvF (by rw [abs_of_nonneg (by linarith)]; linarith)
  · right
    push Not at hv
    have hvu2 : δ0 / 2 ≤ v - u := by linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ hvu]
    have h1' : 2 * M * (t - u) ≤ 2 * M * (t - t0) := by
      apply mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h2' : ε * (δ0 / 2) ≤ ε * (v - u) := mul_le_mul_of_nonneg_left hvu2 hε.le
    nlinarith

/-- Left-hand estimate near a point `t0 ∈ F`. -/
theorem gapExt_left_est (hF : IsClosed F) (h0 : 0 ∈ F) (h1 : 1 ∈ F) (hM : ∀ x ∈ F, |g x| ≤ M)
    {t0 : ℝ} (ht0 : t0 ∈ F) {ε δ0 : ℝ} (hε : 0 < ε) (hδ0 : 0 < δ0)
    (hclose : ∀ x ∈ F, |x - t0| < δ0 → |g x - g t0| < ε) {t : ℝ} (ht0' : 0 ≤ t) (ht1 : t ≤ 1)
    (hlt : t < t0) (hδ : t0 - t < δ0 / 2) (hsmall : 4 * M * (t0 - t) ≤ ε * δ0) :
    |gapExt F g t - g t0| < 2 * ε := by
  by_cases htF : t ∈ F
  · rw [gapExt_of_mem htF]
    have := hclose t htF (by rw [abs_of_neg (by linarith)]; linarith)
    linarith
  rw [gapExt_of_notMem htF]
  obtain ⟨huF, hut⟩ := gapL_mem hF h0 ht0'
  obtain ⟨hvF, htv⟩ := gapR_mem hF h1 ht1
  have hv0 : gapR F t ≤ t0 := gapR_le ht0 hlt.le
  have hult : gapL F t < t := gapL_lt hF h0 ht0' htF
  have hltv : t < gapR F t := lt_gapR hF h1 ht1 htF
  set u := gapL F t
  set v := gapR F t
  have hvu : 0 < v - u := by linarith
  have hl0 : 0 ≤ (v - t) / (v - u) := div_nonneg (by linarith) hvu.le
  have hl1 : (v - t) / (v - u) ≤ 1 := (div_le_one hvu).2 (by linarith)
  have hB : |g v - g t0| < ε := hclose v hvF (by rw [abs_of_nonpos (by linarith)]; linarith)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM t0 ht0)
  have e : g u + (t - u) / (v - u) * (g v - g u) = g v + (v - t) / (v - u) * (g u - g v) := by
    field_simp
    ring
  rw [e]
  refine interp_close hε hl0 hl1 (hM v hvF) (hM u huF) hB ?_
  by_cases hu : t0 - δ0 < u
  · left
    exact hclose u huF (by rw [abs_of_nonpos (by linarith)]; linarith)
  · right
    push Not at hu
    have hvu2 : δ0 / 2 ≤ v - u := by linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ hvu]
    have h1' : 2 * M * (v - t) ≤ 2 * M * (t0 - t) := by
      apply mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h2' : ε * (δ0 / 2) ≤ ε * (v - u) := mul_le_mul_of_nonneg_left hvu2 hε.le
    nlinarith

theorem small_aux {M d ε' δ0 : ℝ} (hM0 : 0 ≤ M) (hd : 0 ≤ d) (hdlt : d < ε' * δ0 / (4 * M + 1)) :
    4 * M * d ≤ ε' * δ0 := by
  have h := (lt_div_iff₀ (by positivity)).1 hdlt
  nlinarith

theorem continuousOn_gapExt (hF : IsClosed F) (h0 : 0 ∈ F) (h1 : 1 ∈ F) (hsub : F ⊆ Icc 0 1)
    (hg : ContinuousOn g F) (hM : ∀ x ∈ F, |g x| ≤ M) : ContinuousOn (gapExt F g) (Icc 0 1) := by
  intro t0 ht0
  by_cases ht0F : t0 ∈ F
  · rw [Metric.continuousWithinAt_iff]
    intro ε hε
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM t0 ht0F)
    obtain ⟨δ0, hδ0, hδ0'⟩ := Metric.continuousWithinAt_iff.1 (hg t0 ht0F) (ε / 3) (by positivity)
    have hclose : ∀ x ∈ F, |x - t0| < δ0 → |g x - g t0| < ε / 3 := by
      intro x hx hxd
      have := hδ0' hx (by rwa [Real.dist_eq])
      rwa [Real.dist_eq] at this
    have hδpos : 0 < min (δ0 / 2) (ε / 3 * δ0 / (4 * M + 1)) := by
      apply lt_min (by positivity); positivity
    refine ⟨_, hδpos, fun t ht hd => ?_⟩
    rw [Real.dist_eq] at hd
    rw [Real.dist_eq, gapExt_of_mem ht0F]
    have hd1 : |t - t0| < δ0 / 2 := hd.trans_le (min_le_left _ _)
    have hd2 : |t - t0| < ε / 3 * δ0 / (4 * M + 1) := hd.trans_le (min_le_right _ _)
    rcases lt_trichotomy t t0 with hlt | heq | hgt
    · have hd1' : t0 - t < δ0 / 2 := by rwa [abs_of_neg (by linarith), neg_sub] at hd1
      have hd2' : t0 - t < ε / 3 * δ0 / (4 * M + 1) := by
        rwa [abs_of_neg (by linarith), neg_sub] at hd2
      have := gapExt_left_est hF h0 h1 hM ht0F (by positivity : (0 : ℝ) < ε / 3) hδ0 hclose ht.1
        ht.2 hlt hd1' (small_aux hM0 (by linarith) hd2')
      linarith
    · subst heq; rw [gapExt_of_mem ht0F]; simpa using hε
    · have hd1' : t - t0 < δ0 / 2 := by rwa [abs_of_pos (by linarith)] at hd1
      have hd2' : t - t0 < ε / 3 * δ0 / (4 * M + 1) := by
        rwa [abs_of_pos (by linarith)] at hd2
      have := gapExt_right_est hF h0 h1 hM ht0F (by positivity : (0 : ℝ) < ε / 3) hδ0 hclose ht.1
        ht.2 hgt hd1' (small_aux hM0 (by linarith) hd2')
      linarith
  · have hlt := gapL_lt hF h0 ht0.1 ht0F
    have hgt := lt_gapR hF h1 ht0.2 ht0F
    set u0 := gapL F t0
    set v0 := gapR F t0
    have hev : gapExt F g =ᶠ[𝓝 t0] fun t => g u0 + (t - u0) / (v0 - u0) * (g v0 - g u0) := by
      filter_upwards [Ioo_mem_nhds hlt hgt] with t ht
      obtain ⟨h1', h2', h3'⟩ := gap_local hF h0 h1 ht0.1 ht0.2 ht0F ht
      rw [gapExt_of_notMem h1', h2', h3']
    have hcont : Continuous fun t : ℝ => g u0 + (t - u0) / (v0 - u0) * (g v0 - g u0) := by
      fun_prop
    exact (hcont.continuousAt.congr hev.symm).continuousWithinAt

end Continuity

/-! ### The linear isometry `C(F) → C([0,1])` -/

section Operator

variable (F : Set ℝ)

open Classical in
/-- A continuous function on `F`, extended by `0` outside `F`. -/
noncomputable def extByZero (f : C(F, ℝ)) (x : ℝ) : ℝ := if h : x ∈ F then f ⟨x, h⟩ else 0

variable {F}

theorem extByZero_continuousOn (f : C(F, ℝ)) : ContinuousOn (extByZero F f) F := by
  rw [continuousOn_iff_continuous_domRestrict]
  have : F.domRestrict (extByZero F f) = f := by
    ext x
    simp [Set.domRestrict, extByZero, x.2]
  rw [this]; exact f.continuous

theorem abs_extByZero_le [CompactSpace F] (f : C(F, ℝ)) {x : ℝ} (hx : x ∈ F) :
    |extByZero F f x| ≤ ‖f‖ := by
  simp only [extByZero, dif_pos hx]
  exact f.norm_coe_le_norm ⟨x, hx⟩

theorem gapExt_add (g1 g2 : ℝ → ℝ) (t : ℝ) :
    gapExt F (fun x => g1 x + g2 x) t = gapExt F g1 t + gapExt F g2 t := by
  by_cases h : t ∈ F
  · simp [gapExt_of_mem h]
  · simp only [gapExt_of_notMem h]; ring

theorem gapExt_smul (c : ℝ) (g : ℝ → ℝ) (t : ℝ) :
    gapExt F (fun x => c * g x) t = c * gapExt F g t := by
  by_cases h : t ∈ F
  · simp [gapExt_of_mem h]
  · simp only [gapExt_of_notMem h]; ring

variable (hF : IsClosed F) (h0 : 0 ∈ F) (h1 : 1 ∈ F) (hsub : F ⊆ Icc 0 1)
include hF h0 h1 hsub

/-- Linear extension of `f ∈ C(F)` over the gaps of `F`, as a continuous function on `[0,1]`. -/
noncomputable def gapExtCM [CompactSpace F] (f : C(F, ℝ)) : C(unitInterval, ℝ) :=
  ⟨fun t => gapExt F (extByZero F f) t,
    (continuousOn_gapExt hF h0 h1 hsub (extByZero_continuousOn f)
      (fun _ hx => abs_extByZero_le f hx)).domRestrict⟩

theorem gapExtCM_apply_mem [CompactSpace F] (f : C(F, ℝ)) {x : ℝ} (hx : x ∈ F) (hx' : x ∈ Icc (0 : ℝ) 1) :
    gapExtCM hF h0 h1 hsub f ⟨x, hx'⟩ = f ⟨x, hx⟩ := by
  show gapExt F (extByZero F f) x = _
  rw [gapExt_of_mem hx]; simp [extByZero, hx]

theorem abs_gapExt_le [CompactSpace F] (f : C(F, ℝ)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |gapExt F (extByZero F f) t| ≤ ‖f‖ := by
  by_cases htF : t ∈ F
  · rw [gapExt_of_mem htF]; exact abs_extByZero_le f htF
  · rw [gapExt_of_notMem htF]
    obtain ⟨huF, _⟩ := gapL_mem hF h0 ht.1
    obtain ⟨hvF, _⟩ := gapR_mem hF h1 ht.2
    have hult := gapL_lt hF h0 ht.1 htF
    have hltv := lt_gapR hF h1 ht.2 htF
    set u := gapL F t
    set v := gapR F t
    have hvu : 0 < v - u := by linarith
    have hl0 : 0 ≤ (t - u) / (v - u) := div_nonneg (by linarith) hvu.le
    have hl1 : (t - u) / (v - u) ≤ 1 := (div_le_one hvu).2 (by linarith)
    have hA := abs_le.1 (abs_extByZero_le f huF)
    have hB := abs_le.1 (abs_extByZero_le f hvF)
    set l := (t - u) / (v - u)
    rw [abs_le]
    constructor <;> nlinarith [hA.1, hA.2, hB.1, hB.2]

/-- The linear isometry `C(F, ℝ) → C([0,1], ℝ)` extending functions linearly over the gaps. -/
noncomputable def gapExtLI [CompactSpace F] : C(F, ℝ) →ₗᵢ[ℝ] C(unitInterval, ℝ) where
  toFun := gapExtCM hF h0 h1 hsub
  map_add' f1 f2 := by
    ext ⟨t, ht⟩
    show gapExt F (extByZero F (f1 + f2)) t = gapExt F (extByZero F f1) t + gapExt F (extByZero F f2) t
    rw [← gapExt_add]
    congr 1
    ext x
    by_cases hx : x ∈ F <;> simp [extByZero, hx]
  map_smul' c f := by
    ext ⟨t, ht⟩
    show gapExt F (extByZero F (c • f)) t = c * gapExt F (extByZero F f) t
    rw [← gapExt_smul]
    congr 1
    ext x
    by_cases hx : x ∈ F <;> simp [extByZero, hx]
  norm_map' f := by
    apply le_antisymm
    · refine (ContinuousMap.norm_le _ (norm_nonneg f)).2 fun t => ?_
      rw [Real.norm_eq_abs]
      exact abs_gapExt_le hF h0 h1 hsub f t.2
    · refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x => ?_
      have := (gapExtCM hF h0 h1 hsub f).norm_coe_le_norm ⟨x.1, hsub x.2⟩
      rwa [gapExtCM_apply_mem hF h0 h1 hsub f x.2 (hsub x.2)] at this

end Operator

/-! ### The theorem -/

theorem one_mem_cantorSet : (1 : ℝ) ∈ cantorSet := by
  refine Set.mem_iInter.mpr fun n => ?_
  induction n with
  | zero => simp [preCantorSet]
  | succ n ih => exact Or.inr ⟨1, ih, by norm_num⟩

/-- Precomposition with a continuous surjection is a linear isometry of the spaces of continuous
real functions on compact spaces. -/
noncomputable def compSurjLI {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X]
    [CompactSpace Y] (g : C(X, Y)) (hg : Function.Surjective g) : C(Y, ℝ) →ₗᵢ[ℝ] C(X, ℝ) where
  toFun f := f.comp g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' f := by
    apply le_antisymm
    · exact (ContinuousMap.norm_le _ (norm_nonneg f)).2 fun x => f.norm_coe_le_norm (g x)
    · refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun y => ?_
      obtain ⟨x, rfl⟩ := hg y
      exact (f.comp g).norm_coe_le_norm x

universe u

/-- If a normed space embeds linearly isometrically into `C(K, ℝ)` for a nonempty compact metrizable
space `K`, then it embeds linearly isometrically into `C([0,1], ℝ)`. -/
theorem exists_linearIsometry_unitInterval_of_embedding {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {K : Type u} [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace.MetrizableSpace K] [Nonempty K] (T : E →ₗᵢ[ℝ] C(K, ℝ)) :
    Nonempty (E →ₗᵢ[ℝ] C(unitInterval, ℝ)) := by
  letI : MetricSpace K := TopologicalSpace.metrizableSpaceMetric K
  obtain ⟨g, hg, hgs⟩ := exists_nat_bool_continuous_surjective_of_compact K
  haveI : CompactSpace cantorSet := isCompact_iff_compactSpace.1 isCompact_cantorSet
  let G : C(cantorSet, K) := ⟨g ∘ cantorSetHomeomorphNatToBool, hg.comp (Homeomorph.continuous _)⟩
  have hGs : Function.Surjective G := hgs.comp cantorSetHomeomorphNatToBool.surjective
  exact ⟨(gapExtLI isClosed_cantorSet zero_mem_cantorSet one_mem_cantorSet
    cantorSet_subset_unitInterval).comp ((compSurjLI G hGs).comp T)⟩

/-- Morris, Topology Without Tears, Remark 12.2.31 (TP-371), Banach-Mazur. Every separable real normed
space (in particular every separable real Banach space) is linearly isometric to a subspace of
`C([0,1], ℝ)`. -/
@[kb "morris2024" "Remark 12.2.31, p. 387"]
theorem banach_mazur (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace.SeparableSpace E] : Nonempty (E →ₗᵢ[ℝ] C(unitInterval, ℝ)) := by
  have : TopologicalSpace.MetrizableSpace (dualUnitBall E) :=
    WeakDual.metrizable_of_isCompact ℝ E (dualUnitBall E) (WeakDual.isCompact_closedBall 0 1)
  have : Nonempty (dualUnitBall E) := ⟨⟨0, by simp [dualUnitBall]⟩⟩
  exact exists_linearIsometry_unitInterval_of_embedding ⟨evalOnDualBall E, norm_evalOnDualBall E⟩

end UndergradKB.Topology
