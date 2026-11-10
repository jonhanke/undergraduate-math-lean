import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import UndergradKB.Common.Attr

/-! # Calculus: double and triple Riemann sums

OpenStax Calculus 3:§5.1 and §5.4: Riemann sums of a continuous function over a rectangle or a box, for the regular
grid with arbitrary tags, converge to the integral. The argument is dimension-free: a general lemma bounds the
error of a sum over a finite measurable partition, and uniform continuity on the compact box supplies the
oscillation bound. -/

namespace UndergradKB.Calculus

open Set Finset MeasureTheory Filter Topology ENNReal

/-- Error of a "cell sum": if `T` is a finite disjoint union of measurable cells `S k` and `f` varies by at most
`ε` on each cell from the tag `p k`, then `∑ f(p k) μ(S k)` is within `ε μ(T)` of `∫_T f`. -/
theorem cellSum_error_le {α ι : Type*} [MeasurableSpace α] {μ : Measure α} (s : Finset ι) (S : ι → Set α)
    (hS : ∀ k ∈ s, MeasurableSet (S k)) (hd : (s : Set ι).PairwiseDisjoint S) (f : α → ℝ) (p : ι → α)
    (hfin : μ (⋃ k ∈ s, S k) ≠ ∞) (hf : IntegrableOn f (⋃ k ∈ s, S k) μ) {ε : ℝ}
    (h : ∀ k ∈ s, ∀ x ∈ S k, |f x - f (p k)| ≤ ε) :
    |∑ k ∈ s, f (p k) * μ.real (S k) - ∫ x in ⋃ k ∈ s, S k, f x ∂μ| ≤ ε * μ.real (⋃ k ∈ s, S k) := by
  have hSfin : ∀ k ∈ s, μ (S k) ≠ ∞ := fun k hk =>
    ne_top_of_le_ne_top hfin (measure_mono (subset_biUnion_of_mem (u := S) hk))
  have hI : ∀ k ∈ s, IntegrableOn f (S k) μ := fun k hk =>
    hf.mono_set (subset_biUnion_of_mem (u := S) hk)
  rw [integral_biUnion_finset s hS hd hI, measureReal_biUnion_finset hd hS hSfin, mul_sum, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
  have e1 : f (p k) * μ.real (S k) = ∫ x in S k, f (p k) ∂μ := by
    rw [setIntegral_const, smul_eq_mul, mul_comm]
  rw [e1, ← integral_sub (integrableOn_const (hSfin k hk)) (hI k hk)]
  have := norm_setIntegral_le_of_norm_le_const (μ := μ) (s := S k) (f := fun x => f (p k) - f x) (C := ε)
    (lt_top_iff_ne_top.2 (hSfin k hk)) (fun x hx => by
      simpa [Real.norm_eq_abs, abs_sub_comm] using h k hk x hx)
  simpa [Real.norm_eq_abs, mul_comm] using this

/-- Point `i` of the regular partition of `[a,b]` into `n` equal pieces (local to this file). -/
noncomputable def gridPoint (a b : ℝ) (n i : ℕ) : ℝ := a + i * ((b - a) / n)

/-- The `i`-th cell `[x_i, x_{i+1})` of the regular partition (half-open, so that cells are disjoint). -/
noncomputable def gridCell (a b : ℝ) (n i : ℕ) : Set ℝ := Ico (gridPoint a b n i) (gridPoint a b n (i + 1))

theorem gridPoint_succ_sub (a b : ℝ) (n i : ℕ) : gridPoint a b n (i + 1) - gridPoint a b n i = (b - a) / n := by
  simp [gridPoint]; ring

theorem gridPoint_last {a b : ℝ} {n : ℕ} (hn : 0 < n) : gridPoint a b n n = b := by
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [gridPoint]; field_simp; ring

theorem gridPoint_mono {a b : ℝ} (hab : a ≤ b) (n : ℕ) : Monotone (gridPoint a b n) := by
  intro i j hij
  have : (i : ℝ) ≤ j := by exact_mod_cast hij
  have h0 : 0 ≤ (b - a) / n := by have := sub_nonneg.2 hab; positivity
  simp only [gridPoint]; nlinarith

theorem gridCell_disjoint {a b : ℝ} (hab : a ≤ b) (n : ℕ) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (gridCell a b n i) (gridCell a b n j) := by
  wlog h : i < j generalizing i j
  · exact (this hij.symm (lt_of_le_of_ne (not_lt.1 h) hij.symm)).symm
  rw [Set.disjoint_left]
  intro x hx hx'
  have := gridPoint_mono hab n (Nat.succ_le_of_lt h)
  exact absurd (hx.2.trans_le this) (not_lt.2 hx'.1)

theorem gridCell_volume (a b : ℝ) (n i : ℕ) (hn : 0 < n) (hab : a ≤ b) :
    volume.real (gridCell a b n i) = (b - a) / n := by
  have h0 : 0 ≤ (b - a) / n := by have := sub_nonneg.2 hab; positivity
  simp only [gridCell, measureReal_def, Real.volume_Ico, gridPoint_succ_sub]
  rw [ENNReal.toReal_ofReal h0]

theorem gridCell_volume_ne_top (a b : ℝ) (n i : ℕ) : volume (gridCell a b n i) ≠ ∞ := by
  simp [gridCell]

theorem mem_Ico_iff_exists_gridCell {a b : ℝ} (hab : a < b) {n : ℕ} (hn : 0 < n) (x : ℝ) :
    x ∈ Ico a b ↔ ∃ i < n, x ∈ gridCell a b n i := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hh : 0 < (b - a) / n := div_pos (sub_pos.2 hab) hn'
  constructor
  · intro hx
    have hx0 : 0 ≤ (x - a) / ((b - a) / n) := div_nonneg (sub_nonneg.2 hx.1) hh.le
    refine ⟨⌊(x - a) / ((b - a) / n)⌋₊, ?_, ?_, ?_⟩
    · have : (x - a) / ((b - a) / n) < n := by
        rw [div_lt_iff₀ hh]
        have : (b - a) / n * n = b - a := by field_simp
        nlinarith [hx.2]
      exact (Nat.floor_lt hx0).2 this
    · have := Nat.floor_le hx0
      rw [le_div_iff₀ hh] at this
      simp only [gridPoint]; linarith
    · have := Nat.lt_floor_add_one ((x - a) / ((b - a) / n))
      rw [div_lt_iff₀ hh] at this
      simp only [gridPoint]; push_cast; linarith
  · rintro ⟨i, hi, hx⟩
    have h1 := gridPoint_mono hab.le n (Nat.zero_le i)
    have h2 := gridPoint_mono hab.le n (Nat.succ_le_of_lt hi)
    rw [gridPoint_last hn] at h2
    have h0 : gridPoint a b n 0 = a := by simp [gridPoint]
    rw [h0] at h1
    exact ⟨h1.trans hx.1, hx.2.trans_le h2⟩

theorem iUnion_gridCell {a b : ℝ} (hab : a < b) {n : ℕ} (hn : 0 < n) :
    (⋃ i ∈ range n, gridCell a b n i) = Ico a b := by
  ext x
  simp only [mem_iUnion, Finset.mem_range, exists_prop]
  exact ((mem_Ico_iff_exists_gridCell hab hn x).symm)

theorem gridCell_sub_le {a b : ℝ} {n : ℕ} {i : ℕ} {x y : ℝ}
    (hx : x ∈ Icc (gridPoint a b n i) (gridPoint a b n (i + 1)))
    (hy : y ∈ Icc (gridPoint a b n i) (gridPoint a b n (i + 1))) : |x - y| ≤ (b - a) / n := by
  have := gridPoint_succ_sub a b n i
  rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem gridCell_subset_Icc {a b : ℝ} (hab : a ≤ b) {n : ℕ} (hn : 0 < n) {i : ℕ} (hi : i < n) :
    Icc (gridPoint a b n i) (gridPoint a b n (i + 1)) ⊆ Icc a b := by
  have h1 := gridPoint_mono hab n (Nat.zero_le i)
  have h2 := gridPoint_mono hab n (Nat.succ_le_of_lt hi)
  rw [gridPoint_last hn] at h2
  have h0 : gridPoint a b n 0 = a := by simp [gridPoint]
  rw [h0] at h1
  exact Icc_subset_Icc h1 h2

theorem Ico_prod_volume_real (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) :
    volume.real (Ico a b ×ˢ Ico c d) = (b - a) * (d - c) := by
  simp only [measureReal_def, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.2 hab), ENNReal.toReal_ofReal (sub_nonneg.2 hcd)]

/-- OpenStax Calculus 3:§5.1 (CA-553), quantitative form. If `f` varies by at most `ε` between points of `R = [a,b]×[c,d]`
that are within one grid width in each coordinate, every double Riemann sum on the regular `m × n` grid with arbitrary
tags is within `ε (b-a)(d-c)` of `∫_R f`. -/
theorem doubleSum_error_le {f : ℝ × ℝ → ℝ} {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hf : ContinuousOn f (Icc a b ×ˢ Icc c d)) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {ε : ℝ}
    (hε : ∀ p ∈ Icc a b ×ˢ Icc c d, ∀ q ∈ Icc a b ×ˢ Icc c d,
      |p.1 - q.1| ≤ (b - a) / m → |p.2 - q.2| ≤ (d - c) / n → |f p - f q| ≤ ε)
    (t : ℕ → ℕ → ℝ × ℝ)
    (ht : ∀ i < m, ∀ j < n, t i j ∈ Icc (gridPoint a b m i) (gridPoint a b m (i + 1)) ×ˢ
      Icc (gridPoint c d n j) (gridPoint c d n (j + 1))) :
    |∑ i ∈ range m, ∑ j ∈ range n, f (t i j) * (((b - a) / m) * ((d - c) / n)) -
      ∫ p in Icc a b ×ˢ Icc c d, f p| ≤ ε * ((b - a) * (d - c)) := by
  have hU : (⋃ k ∈ range m ×ˢ range n, gridCell a b m k.1 ×ˢ gridCell c d n k.2) = Ico a b ×ˢ Ico c d := by
    ext ⟨x, y⟩
    simp only [mem_iUnion, Finset.mem_product, Finset.mem_range, mem_prod, exists_prop, Prod.exists]
    constructor
    · rintro ⟨i, j, ⟨hi, hj⟩, hx, hy⟩
      exact ⟨(mem_Ico_iff_exists_gridCell hab hm x).2 ⟨i, hi, hx⟩,
        (mem_Ico_iff_exists_gridCell hcd hn y).2 ⟨j, hj, hy⟩⟩
    · rintro ⟨hx, hy⟩
      obtain ⟨i, hi, hx'⟩ := (mem_Ico_iff_exists_gridCell hab hm x).1 hx
      obtain ⟨j, hj, hy'⟩ := (mem_Ico_iff_exists_gridCell hcd hn y).1 hy
      exact ⟨i, j, ⟨hi, hj⟩, hx', hy'⟩
  have hfR : IntegrableOn f (Icc a b ×ˢ Icc c d) volume :=
    hf.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hfin : volume (⋃ k ∈ range m ×ˢ range n, gridCell a b m k.1 ×ˢ gridCell c d n k.2) ≠ ∞ := by
    rw [hU, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Ico]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hfint : IntegrableOn f (⋃ k ∈ range m ×ˢ range n, gridCell a b m k.1 ×ˢ gridCell c d n k.2) volume := by
    rw [hU]; exact hfR.mono_set (prod_mono Ico_subset_Icc_self Ico_subset_Icc_self)
  have key := cellSum_error_le (μ := volume) (Finset.range m ×ˢ Finset.range n)
    (fun k => gridCell a b m k.1 ×ˢ gridCell c d n k.2)
    (fun k _ => (measurableSet_Ico).prod (measurableSet_Ico))
    (by
      intro k _ k' _ hne
      by_cases h1 : k.1 = k'.1
      · have h2 : k.2 ≠ k'.2 := fun h2 => hne (Prod.ext h1 h2)
        simp only [Function.onFun]
        rw [h1]
        exact Disjoint.set_prod_right (gridCell_disjoint hcd.le n h2) _ _
      · exact Disjoint.set_prod_left (gridCell_disjoint hab.le m h1) _ _)
    f (fun k => t k.1 k.2) hfin hfint (ε := ε) (by
      intro k hk p hp
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hk
      have h1 := ht k.1 hk.1 k.2 hk.2
      have hp1 : p.1 ∈ Icc (gridPoint a b m k.1) (gridPoint a b m (k.1 + 1)) := Ico_subset_Icc_self hp.1
      have hp2 : p.2 ∈ Icc (gridPoint c d n k.2) (gridPoint c d n (k.2 + 1)) := Ico_subset_Icc_self hp.2
      exact hε p ⟨gridCell_subset_Icc hab.le hm hk.1 hp1, gridCell_subset_Icc hcd.le hn hk.2 hp2⟩ _
        ⟨gridCell_subset_Icc hab.le hm hk.1 h1.1, gridCell_subset_Icc hcd.le hn hk.2 h1.2⟩
        (gridCell_sub_le hp1 h1.1) (gridCell_sub_le hp2 h1.2))
  rw [hU] at key
  rw [Ico_prod_volume_real a b c d hab.le hcd.le] at key
  have e1 : ∑ k ∈ range m ×ˢ range n, f (t k.1 k.2) * volume.real (gridCell a b m k.1 ×ˢ gridCell c d n k.2) =
      ∑ i ∈ range m, ∑ j ∈ range n, f (t i j) * (((b - a) / m) * ((d - c) / n)) := by
    rw [Finset.sum_product]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    have : volume.real (gridCell a b m i ×ˢ gridCell c d n j) = ((b - a) / m) * ((d - c) / n) := by
      simp only [gridCell, measureReal_def, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico,
        gridPoint_succ_sub, ENNReal.toReal_mul]
      have h1 : 0 ≤ (b - a) / m := by have := sub_pos.2 hab; positivity
      have h2 : 0 ≤ (d - c) / n := by have := sub_pos.2 hcd; positivity
      rw [ENNReal.toReal_ofReal h1, ENNReal.toReal_ofReal h2]
    rw [this]
  have e2 : ∫ p in Ico a b ×ˢ Ico c d, f p = ∫ p in Icc a b ×ˢ Icc c d, f p :=
    setIntegral_congr_set (Measure.set_prod_ae_eq Ico_ae_eq_Icc Ico_ae_eq_Icc)
  rw [e1, e2] at key
  exact key

theorem div_le_of_lt_nat {L δ : ℝ} (hδ : 0 < δ) {N m : ℕ} (hN : L / δ < N) (hm : N < m) : L / m ≤ δ := by
  have hm' : (0 : ℝ) < m := by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have : (N : ℝ) < m := by exact_mod_cast hm
    linarith
  rw [div_le_iff₀ hm']
  have := (div_lt_iff₀ hδ).1 hN
  have : (N : ℝ) < m := by exact_mod_cast hm
  nlinarith

/-- OpenStax Calculus 3:§5.1 (CA-553). Double Riemann sums of a function continuous on `R = [a,b]×[c,d]`, over the
regular `m × n` grid with arbitrary tags `t m n i j` in the `(i,j)` subrectangle, tend to the double integral
`∫_R f` as `m, n → ∞`. -/
@[kb "openstaxcalculus2016" "3:Definition (double integral over a rectangle), p. 430"]
theorem tendsto_doubleSum {f : ℝ × ℝ → ℝ} {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hf : ContinuousOn f (Icc a b ×ˢ Icc c d))
    (t : ℕ → ℕ → ℕ → ℕ → ℝ × ℝ)
    (ht : ∀ m n, ∀ i < m, ∀ j < n, t m n i j ∈ Icc (gridPoint a b m i) (gridPoint a b m (i + 1)) ×ˢ
      Icc (gridPoint c d n j) (gridPoint c d n (j + 1))) :
    Tendsto (fun q : ℕ × ℕ => ∑ i ∈ range q.1, ∑ j ∈ range q.2,
        f (t q.1 q.2 i j) * (((b - a) / q.1) * ((d - c) / q.2)))
      (atTop ×ˢ atTop) (𝓝 (∫ p in Icc a b ×ˢ Icc c d, f p)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have huc := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hf
  rw [Metric.uniformContinuousOn_iff_le] at huc
  have hK : 0 < (b - a) * (d - c) + 1 := by
    have := mul_pos (sub_pos.2 hab) (sub_pos.2 hcd); linarith
  have hε' : 0 < ε / (2 * ((b - a) * (d - c) + 1)) := by positivity
  obtain ⟨δ, hδ, hδ'⟩ := huc _ hε'
  obtain ⟨N, hN⟩ := exists_nat_gt (max (b - a) (d - c) / δ)
  filter_upwards [(eventually_ge_atTop (N + 1)).prod_mk (eventually_ge_atTop (N + 1))] with q hq
  obtain ⟨hm, hn⟩ := hq
  have hm0 : 0 < q.1 := by omega
  have hn0 : 0 < q.2 := by omega
  have hNm : (max (b - a) (d - c)) / δ < (N : ℕ) := hN
  have h1 : (b - a) / q.1 ≤ δ := by
    refine div_le_of_lt_nat hδ ?_ (by omega : N < q.1)
    exact lt_of_le_of_lt (div_le_div_of_nonneg_right (le_max_left _ _) hδ.le) hN
  have h2 : (d - c) / q.2 ≤ δ := by
    refine div_le_of_lt_nat hδ ?_ (by omega : N < q.2)
    exact lt_of_le_of_lt (div_le_div_of_nonneg_right (le_max_right _ _) hδ.le) hN
  have := doubleSum_error_le hab hcd hf hm0 hn0 (ε := ε / (2 * ((b - a) * (d - c) + 1)))
    (fun p hp r hr e1 e2 => by
      have := hδ' p hp r hr (by
        rw [Prod.dist_eq]
        exact max_le (by rw [Real.dist_eq]; exact e1.trans h1) (by rw [Real.dist_eq]; exact e2.trans h2))
      simpa [Real.dist_eq] using this)
    (t q.1 q.2) (ht q.1 q.2)
  rw [Real.dist_eq]
  refine this.trans_lt ?_
  have hP := mul_pos (sub_pos.2 hab) (sub_pos.2 hcd)
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

/-- OpenStax Calculus 3:§5.1 (CA-553), iterated form: `∫_R f = ∫_a^b ∫_c^d f(x,y) dy dx` for continuous `f`. -/
theorem integral_rect_eq_iterated {f : ℝ × ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hf : ContinuousOn f (Icc a b ×ˢ Icc c d)) :
    ∫ p in Icc a b ×ˢ Icc c d, f p = ∫ x in a..b, ∫ y in c..d, f (x, y) := by
  have hfR : IntegrableOn f (Icc a b ×ˢ Icc c d) volume :=
    hf.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [Measure.volume_eq_prod, setIntegral_prod f (by rwa [← Measure.volume_eq_prod])]
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc fun x _ => ?_
  rw [intervalIntegral.integral_of_le hcd, ← integral_Icc_eq_integral_Ioc]

theorem gridCell_prod_volume_real {a b c d e g : ℝ} (hab : a < b) (hcd : c < d) (heg : e < g) {m n l : ℕ} (i j k : ℕ) :
    volume.real (gridCell a b m i ×ˢ (gridCell c d n j ×ˢ gridCell e g l k)) =
      ((b - a) / m) * (((d - c) / n) * ((g - e) / l)) := by
  simp only [gridCell, measureReal_def, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico,
    gridPoint_succ_sub, ENNReal.toReal_mul]
  have h1 : 0 ≤ (b - a) / m := by have := sub_pos.2 hab; positivity
  have h2 : 0 ≤ (d - c) / n := by have := sub_pos.2 hcd; positivity
  have h3 : 0 ≤ (g - e) / l := by have := sub_pos.2 heg; positivity
  rw [ENNReal.toReal_ofReal h1, ENNReal.toReal_ofReal h2, ENNReal.toReal_ofReal h3]

/-- OpenStax Calculus 3:§5.4 (CA-577), quantitative form. If `f` varies by at most `ε` between points of the box
`B = [a,b]×[c,d]×[e,g]` within one grid width in each coordinate, every triple Riemann sum on the regular
`m × n × l` grid with arbitrary tags is within `ε (b-a)(d-c)(g-e)` of `∫_B f`. -/
theorem tripleSum_error_le {f : ℝ × ℝ × ℝ → ℝ} {a b c d e g : ℝ} (hab : a < b) (hcd : c < d) (heg : e < g)
    (hf : ContinuousOn f (Icc a b ×ˢ (Icc c d ×ˢ Icc e g))) {m n l : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hl : 0 < l) {ε : ℝ}
    (hε : ∀ p ∈ Icc a b ×ˢ (Icc c d ×ˢ Icc e g), ∀ q ∈ Icc a b ×ˢ (Icc c d ×ˢ Icc e g),
      |p.1 - q.1| ≤ (b - a) / m → |p.2.1 - q.2.1| ≤ (d - c) / n → |p.2.2 - q.2.2| ≤ (g - e) / l →
      |f p - f q| ≤ ε)
    (t : ℕ → ℕ → ℕ → ℝ × ℝ × ℝ)
    (ht : ∀ i < m, ∀ j < n, ∀ k < l, t i j k ∈ Icc (gridPoint a b m i) (gridPoint a b m (i + 1)) ×ˢ
      (Icc (gridPoint c d n j) (gridPoint c d n (j + 1)) ×ˢ Icc (gridPoint e g l k) (gridPoint e g l (k + 1)))) :
    |∑ i ∈ range m, ∑ j ∈ range n, ∑ k ∈ range l,
        f (t i j k) * (((b - a) / m) * (((d - c) / n) * ((g - e) / l))) -
      ∫ p in Icc a b ×ˢ (Icc c d ×ˢ Icc e g), f p| ≤ ε * ((b - a) * ((d - c) * (g - e))) := by
  have hU : (⋃ q ∈ Finset.range m ×ˢ (Finset.range n ×ˢ Finset.range l),
      gridCell a b m q.1 ×ˢ (gridCell c d n q.2.1 ×ˢ gridCell e g l q.2.2)) =
      Ico a b ×ˢ (Ico c d ×ˢ Ico e g) := by
    ext ⟨x, y, z⟩
    simp only [mem_iUnion, Finset.mem_product, Finset.mem_range, mem_prod, exists_prop, Prod.exists]
    constructor
    · rintro ⟨i, j, k, ⟨hi, hj, hk⟩, hx, hy, hz⟩
      exact ⟨(mem_Ico_iff_exists_gridCell hab hm x).2 ⟨i, hi, hx⟩,
        (mem_Ico_iff_exists_gridCell hcd hn y).2 ⟨j, hj, hy⟩,
        (mem_Ico_iff_exists_gridCell heg hl z).2 ⟨k, hk, hz⟩⟩
    · rintro ⟨hx, hy, hz⟩
      obtain ⟨i, hi, hx'⟩ := (mem_Ico_iff_exists_gridCell hab hm x).1 hx
      obtain ⟨j, hj, hy'⟩ := (mem_Ico_iff_exists_gridCell hcd hn y).1 hy
      obtain ⟨k, hk, hz'⟩ := (mem_Ico_iff_exists_gridCell heg hl z).1 hz
      exact ⟨i, j, k, ⟨hi, hj, hk⟩, hx', hy', hz'⟩
  have hfB : IntegrableOn f (Icc a b ×ˢ (Icc c d ×ˢ Icc e g)) volume :=
    hf.integrableOn_compact (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  have hfin : volume (⋃ q ∈ Finset.range m ×ˢ (Finset.range n ×ˢ Finset.range l),
      gridCell a b m q.1 ×ˢ (gridCell c d n q.2.1 ×ˢ gridCell e g l q.2.2)) ≠ ∞ := by
    rw [hU]
    simp only [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  have hfint : IntegrableOn f (⋃ q ∈ Finset.range m ×ˢ (Finset.range n ×ˢ Finset.range l),
      gridCell a b m q.1 ×ˢ (gridCell c d n q.2.1 ×ˢ gridCell e g l q.2.2)) volume := by
    rw [hU]
    exact hfB.mono_set (prod_mono Ico_subset_Icc_self (prod_mono Ico_subset_Icc_self Ico_subset_Icc_self))
  have key := cellSum_error_le (μ := volume) (Finset.range m ×ˢ (Finset.range n ×ˢ Finset.range l))
    (fun q => gridCell a b m q.1 ×ˢ (gridCell c d n q.2.1 ×ˢ gridCell e g l q.2.2))
    (fun q _ => (measurableSet_Ico).prod ((measurableSet_Ico).prod measurableSet_Ico))
    (by
      intro q _ q' _ hne
      simp only [Function.onFun]
      by_cases h1 : q.1 = q'.1
      · rw [h1]
        by_cases h2 : q.2.1 = q'.2.1
        · have h3 : q.2.2 ≠ q'.2.2 := fun h3 => hne (Prod.ext h1 (Prod.ext h2 h3))
          rw [h2]
          exact Disjoint.set_prod_right (Disjoint.set_prod_right (gridCell_disjoint heg.le l h3) _ _) _ _
        · exact Disjoint.set_prod_right (Disjoint.set_prod_left (gridCell_disjoint hcd.le n h2) _ _) _ _
      · exact Disjoint.set_prod_left (gridCell_disjoint hab.le m h1) _ _)
    f (fun q => t q.1 q.2.1 q.2.2) hfin hfint (ε := ε) (by
      intro q hq p hp
      rw [Finset.mem_product, Finset.mem_product, Finset.mem_range, Finset.mem_range, Finset.mem_range] at hq
      have h1 := ht q.1 hq.1 q.2.1 hq.2.1 q.2.2 hq.2.2
      have hp1 : p.1 ∈ Icc (gridPoint a b m q.1) (gridPoint a b m (q.1 + 1)) := Ico_subset_Icc_self hp.1
      have hp2 : p.2.1 ∈ Icc (gridPoint c d n q.2.1) (gridPoint c d n (q.2.1 + 1)) :=
        Ico_subset_Icc_self hp.2.1
      have hp3 : p.2.2 ∈ Icc (gridPoint e g l q.2.2) (gridPoint e g l (q.2.2 + 1)) :=
        Ico_subset_Icc_self hp.2.2
      exact hε p ⟨gridCell_subset_Icc hab.le hm hq.1 hp1, gridCell_subset_Icc hcd.le hn hq.2.1 hp2,
          gridCell_subset_Icc heg.le hl hq.2.2 hp3⟩ _
        ⟨gridCell_subset_Icc hab.le hm hq.1 h1.1, gridCell_subset_Icc hcd.le hn hq.2.1 h1.2.1,
          gridCell_subset_Icc heg.le hl hq.2.2 h1.2.2⟩
        (gridCell_sub_le hp1 h1.1) (gridCell_sub_le hp2 h1.2.1) (gridCell_sub_le hp3 h1.2.2))
  rw [hU] at key
  have e0 : volume.real (Ico a b ×ˢ (Ico c d ×ˢ Ico e g)) = (b - a) * ((d - c) * (g - e)) := by
    simp only [measureReal_def, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.2 hab.le), ENNReal.toReal_ofReal (sub_nonneg.2 hcd.le),
      ENNReal.toReal_ofReal (sub_nonneg.2 heg.le)]
  rw [e0] at key
  have e1 : ∑ q ∈ Finset.range m ×ˢ (Finset.range n ×ˢ Finset.range l), f (t q.1 q.2.1 q.2.2) *
      volume.real (gridCell a b m q.1 ×ˢ (gridCell c d n q.2.1 ×ˢ gridCell e g l q.2.2)) =
      ∑ i ∈ range m, ∑ j ∈ range n, ∑ k ∈ range l,
        f (t i j k) * (((b - a) / m) * (((d - c) / n) * ((g - e) / l))) := by
    rw [Finset.sum_product]
    refine sum_congr rfl fun i _ => ?_
    rw [Finset.sum_product]
    refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
    rw [gridCell_prod_volume_real hab hcd heg]
  have e2 : ∫ p in Ico a b ×ˢ (Ico c d ×ˢ Ico e g), f p = ∫ p in Icc a b ×ˢ (Icc c d ×ˢ Icc e g), f p :=
    setIntegral_congr_set (Measure.set_prod_ae_eq Ico_ae_eq_Icc
      (Measure.set_prod_ae_eq Ico_ae_eq_Icc Ico_ae_eq_Icc))
  rw [e1, e2] at key
  exact key

/-- OpenStax Calculus 3:§5.4 (CA-577). Triple Riemann sums of a function continuous on the box
`[a,b]×[c,d]×[e,g]`, over the regular `m × n × l` grid with arbitrary tags `t m n l i j k` in the `(i,j,k)` subbox,
tend to the triple integral as `m, n, l → ∞`. -/
@[kb "openstaxcalculus2016" "3:Definition (triple integral over a box, eq. 5.10), p. 494"]
theorem tendsto_tripleSum {f : ℝ × ℝ × ℝ → ℝ} {a b c d e g : ℝ} (hab : a < b) (hcd : c < d) (heg : e < g)
    (hf : ContinuousOn f (Icc a b ×ˢ (Icc c d ×ˢ Icc e g)))
    (t : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℝ × ℝ × ℝ)
    (ht : ∀ m n l, ∀ i < m, ∀ j < n, ∀ k < l, t m n l i j k ∈
      Icc (gridPoint a b m i) (gridPoint a b m (i + 1)) ×ˢ
      (Icc (gridPoint c d n j) (gridPoint c d n (j + 1)) ×ˢ Icc (gridPoint e g l k) (gridPoint e g l (k + 1)))) :
    Tendsto (fun q : ℕ × ℕ × ℕ => ∑ i ∈ range q.1, ∑ j ∈ range q.2.1, ∑ k ∈ range q.2.2,
        f (t q.1 q.2.1 q.2.2 i j k) * (((b - a) / q.1) * (((d - c) / q.2.1) * ((g - e) / q.2.2))))
      (atTop ×ˢ (atTop ×ˢ atTop)) (𝓝 (∫ p in Icc a b ×ˢ (Icc c d ×ˢ Icc e g), f p)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have huc := (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).uniformContinuousOn_of_continuous hf
  rw [Metric.uniformContinuousOn_iff_le] at huc
  have hK : 0 < (b - a) * ((d - c) * (g - e)) + 1 := by
    have := mul_pos (sub_pos.2 hab) (mul_pos (sub_pos.2 hcd) (sub_pos.2 heg)); linarith
  have hε' : 0 < ε / (2 * ((b - a) * ((d - c) * (g - e)) + 1)) := by positivity
  obtain ⟨δ, hδ, hδ'⟩ := huc _ hε'
  obtain ⟨N, hN⟩ := exists_nat_gt (max (b - a) (max (d - c) (g - e)) / δ)
  filter_upwards [(eventually_ge_atTop (N + 1)).prod_mk
    ((eventually_ge_atTop (N + 1)).prod_mk (eventually_ge_atTop (N + 1)))] with q hq
  obtain ⟨hm, hn, hl⟩ := hq
  have hm0 : 0 < q.1 := by omega
  have hn0 : 0 < q.2.1 := by omega
  have hl0 : 0 < q.2.2 := by omega
  have h1 : (b - a) / q.1 ≤ δ := by
    refine div_le_of_lt_nat hδ ?_ (by omega : N < q.1)
    exact lt_of_le_of_lt (div_le_div_of_nonneg_right (le_max_left _ _) hδ.le) hN
  have h2 : (d - c) / q.2.1 ≤ δ := by
    refine div_le_of_lt_nat hδ ?_ (by omega : N < q.2.1)
    exact lt_of_le_of_lt (div_le_div_of_nonneg_right
      ((le_max_left _ _).trans (le_max_right _ _)) hδ.le) hN
  have h3 : (g - e) / q.2.2 ≤ δ := by
    refine div_le_of_lt_nat hδ ?_ (by omega : N < q.2.2)
    exact lt_of_le_of_lt (div_le_div_of_nonneg_right
      ((le_max_right _ _).trans (le_max_right _ _)) hδ.le) hN
  have := tripleSum_error_le hab hcd heg hf hm0 hn0 hl0
    (ε := ε / (2 * ((b - a) * ((d - c) * (g - e)) + 1)))
    (fun p hp r hr e1 e2 e3 => by
      have := hδ' p hp r hr (by
        rw [Prod.dist_eq, Prod.dist_eq]
        exact max_le (by rw [Real.dist_eq]; exact e1.trans h1)
          (max_le (by rw [Real.dist_eq]; exact e2.trans h2) (by rw [Real.dist_eq]; exact e3.trans h3)))
      simpa [Real.dist_eq] using this)
    (t q.1 q.2.1 q.2.2) (ht q.1 q.2.1 q.2.2)
  rw [Real.dist_eq]
  refine this.trans_lt ?_
  have hP := mul_pos (sub_pos.2 hab) (mul_pos (sub_pos.2 hcd) (sub_pos.2 heg))
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

/-- OpenStax Calculus 3:§5.4 (CA-577), iterated form: for continuous `f` on a box the triple integral is
`∫_a^b ∫_c^d ∫_e^g f(x,y,z) dz dy dx`. -/
theorem integral_box_eq_iterated {f : ℝ × ℝ × ℝ → ℝ} {a b c d e g : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (heg : e ≤ g)
    (hf : ContinuousOn f (Icc a b ×ˢ (Icc c d ×ˢ Icc e g))) :
    ∫ p in Icc a b ×ˢ (Icc c d ×ˢ Icc e g), f p =
      ∫ x in a..b, ∫ y in c..d, ∫ z in e..g, f (x, y, z) := by
  have hfB : IntegrableOn f (Icc a b ×ˢ (Icc c d ×ˢ Icc e g)) volume :=
    hf.integrableOn_compact (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  have hf2 : ∀ x ∈ Icc a b, ContinuousOn (fun q : ℝ × ℝ => f (x, q)) (Icc c d ×ˢ Icc e g) := fun x hx =>
    hf.comp (Continuous.continuousOn (by fun_prop)) (fun q hq => ⟨hx, hq⟩)
  rw [Measure.volume_eq_prod, setIntegral_prod f (by rwa [← Measure.volume_eq_prod])]
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc fun x hx => ?_
  exact integral_rect_eq_iterated (f := fun q : ℝ × ℝ => f (x, q)) hcd heg (hf2 x hx)

end UndergradKB.Calculus
