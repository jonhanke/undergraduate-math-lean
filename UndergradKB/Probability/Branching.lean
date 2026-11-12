import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-!
# Probability: branching processes (Grinstead–Snell, §10.2)

The offspring law of one parent is a sequence `p k` (probability of `k` children), with generating function
`h(z) = ∑ p k z^k`.  The probability `d n` that the family has died out by generation `n` satisfies
`d 0 = 0`, `d (n+1) = h (d n)`.  We prove that `d n` increases to the smallest root of `h z = z` in `[0,1]`
(the extinction probability), that this root is `1` when the mean offspring number is at most `1`
(and `p 1 < 1`, excluding the degenerate law `h z = z`), and is `< 1` when the mean exceeds `1`
(finite or infinite).
-/

open Finset Filter Set
open scoped Topology

namespace UndergradKB.Probability

/-- An offspring law: nonnegative probabilities `p k` summing to `1`. -/
structure IsOffspring (p : ℕ → ℝ) : Prop where
  nonneg : ∀ k, 0 ≤ p k
  hasSum : HasSum p 1

/-- The generating function `h(z) = ∑ p_k z^k` of the offspring law (Grinstead–Snell §10.2). -/
noncomputable def offspringGF (p : ℕ → ℝ) (z : ℝ) : ℝ := ∑' k, p k * z ^ k

/-- The probability `d_n` of extinction by generation `n`: `d_0 = 0`, `d_n = h(d_{n-1})`. -/
noncomputable def extinctProb (p : ℕ → ℝ) (n : ℕ) : ℝ := (offspringGF p)^[n] 0

/-- The probability of eventual extinction, the limit (supremum) of the `d_n`. -/
noncomputable def extinctionProb (p : ℕ → ℝ) : ℝ := ⨆ n, extinctProb p n

theorem extinctProb_zero (p : ℕ → ℝ) : extinctProb p 0 = 0 := rfl

theorem extinctProb_succ (p : ℕ → ℝ) (n : ℕ) :
    extinctProb p (n + 1) = offspringGF p (extinctProb p n) := by
  simp only [extinctProb, Function.iterate_succ_apply']

namespace Branching

variable {p : ℕ → ℝ}

theorem summable_term (hp : IsOffspring p) {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    Summable fun k => p k * z ^ k :=
  Summable.of_nonneg_of_le (fun k => mul_nonneg (hp.nonneg k) (pow_nonneg hz.1 k))
    (fun k => mul_le_of_le_one_right (hp.nonneg k) (pow_le_one₀ hz.1 hz.2)) hp.hasSum.summable

theorem gf_nonneg (hp : IsOffspring p) {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) : 0 ≤ offspringGF p z :=
  tsum_nonneg fun k => mul_nonneg (hp.nonneg k) (pow_nonneg hz.1 k)

theorem gf_le_one (hp : IsOffspring p) {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) : offspringGF p z ≤ 1 := by
  have := hp.hasSum.tsum_eq
  rw [← this]
  exact (summable_term hp hz).tsum_le_tsum
    (fun k => mul_le_of_le_one_right (hp.nonneg k) (pow_le_one₀ hz.1 hz.2)) hp.hasSum.summable

theorem gf_mono (hp : IsOffspring p) {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1)
    (hxy : x ≤ y) : offspringGF p x ≤ offspringGF p y :=
  (summable_term hp hx).tsum_le_tsum
    (fun k => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.1 hxy k) (hp.nonneg k))
    (summable_term hp hy)

theorem gf_zero (p : ℕ → ℝ) : offspringGF p 0 = p 0 := by
  unfold offspringGF
  rw [tsum_eq_single 0]
  · simp
  · intro k hk; simp [hk]

theorem gf_one (hp : IsOffspring p) : offspringGF p 1 = 1 := by
  simp [offspringGF, hp.hasSum.tsum_eq]

theorem gf_continuousOn (hp : IsOffspring p) : ContinuousOn (offspringGF p) (Icc 0 1) := by
  unfold offspringGF
  refine continuousOn_tsum (u := p) (fun k => by fun_prop) hp.hasSum.summable ?_
  intro k z hz
  rw [norm_mul, Real.norm_of_nonneg (hp.nonneg k), norm_pow, Real.norm_of_nonneg hz.1]
  exact mul_le_of_le_one_right (hp.nonneg k) (pow_le_one₀ hz.1 hz.2)

theorem extinctProb_mem (hp : IsOffspring p) (n : ℕ) : extinctProb p n ∈ Icc (0 : ℝ) 1 := by
  induction n with
  | zero => simp [extinctProb_zero]
  | succ n ih =>
    rw [extinctProb_succ]
    exact ⟨gf_nonneg hp ih, gf_le_one hp ih⟩

theorem extinctProb_mono (hp : IsOffspring p) : Monotone (extinctProb p) := by
  refine monotone_nat_of_le_succ fun n => ?_
  induction n with
  | zero =>
    rw [extinctProb_succ, extinctProb_zero]
    exact gf_nonneg hp ⟨le_rfl, zero_le_one⟩
  | succ n ih =>
    calc extinctProb p (n + 1) = offspringGF p (extinctProb p n) := extinctProb_succ p n
      _ ≤ offspringGF p (extinctProb p (n + 1)) :=
          gf_mono hp (extinctProb_mem hp n) (extinctProb_mem hp (n + 1)) ih
      _ = extinctProb p (n + 1 + 1) := (extinctProb_succ p (n + 1)).symm

theorem extinctProb_le_root (hp : IsOffspring p) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1)
    (hroot : offspringGF p r = r) (n : ℕ) : extinctProb p n ≤ r := by
  induction n with
  | zero => simpa [extinctProb_zero] using hr.1
  | succ n ih =>
    rw [extinctProb_succ]
    calc offspringGF p (extinctProb p n) ≤ offspringGF p r :=
          gf_mono hp (extinctProb_mem hp n) hr ih
      _ = r := hroot

end Branching

open Branching in
/-- Grinstead–Snell Theorem 10.2 (PR-106), first part. The extinction probabilities `d_n = h(d_{n-1})`,
`d_0 = 0`, increase to `d = extinctionProb p`, and `d` is the smallest root of `h z = z` in `[0,1]`. -/
@[kb "grinsteadsnell2006" "Theorem 10.2, p. 388"]
theorem extinction_smallest_root {p : ℕ → ℝ} (hp : IsOffspring p) :
    Monotone (extinctProb p) ∧ Tendsto (extinctProb p) atTop (𝓝 (extinctionProb p)) ∧
      IsLeast {z : ℝ | z ∈ Icc (0 : ℝ) 1 ∧ offspringGF p z = z} (extinctionProb p) := by
  have hmono := extinctProb_mono hp
  have hbdd : BddAbove (range (extinctProb p)) := ⟨1, by rintro _ ⟨n, rfl⟩; exact (extinctProb_mem hp n).2⟩
  have hlim : Tendsto (extinctProb p) atTop (𝓝 (extinctionProb p)) := tendsto_atTop_ciSup hmono hbdd
  have hmem : extinctionProb p ∈ Icc (0 : ℝ) 1 :=
    isClosed_Icc.mem_of_tendsto hlim (Eventually.of_forall (extinctProb_mem hp))
  have hfix : offspringGF p (extinctionProb p) = extinctionProb p := by
    have h1 : Tendsto (fun n => offspringGF p (extinctProb p n)) atTop
        (𝓝 (offspringGF p (extinctionProb p))) :=
      ((gf_continuousOn hp) _ hmem).tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall (extinctProb_mem hp)⟩)
    have h2 : Tendsto (fun n => offspringGF p (extinctProb p n)) atTop (𝓝 (extinctionProb p)) := by
      have := hlim.comp (tendsto_add_atTop_nat 1)
      simpa [Function.comp_def, extinctProb_succ] using this
    exact tendsto_nhds_unique h1 h2
  refine ⟨hmono, hlim, ⟨hmem, hfix⟩, ?_⟩
  rintro r ⟨hr, hroot⟩
  exact le_of_tendsto' hlim fun n => extinctProb_le_root hp hr hroot n

namespace Branching

variable {p : ℕ → ℝ}

theorem one_sub_pow_le (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (k : ℕ) :
    1 - r ^ k ≤ k * (1 - r) := by
  have h := mul_neg_geom_sum r k
  have hs : ∑ i ∈ range k, r ^ i ≤ k := by
    calc ∑ i ∈ range k, r ^ i ≤ ∑ _i ∈ range k, (1 : ℝ) :=
          sum_le_sum fun i _ => pow_le_one₀ hr0 hr1.le
      _ = k := by simp
  rw [← h]; nlinarith

theorem one_sub_pow_lt (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (k : ℕ) (hk : 2 ≤ k) :
    1 - r ^ k < k * (1 - r) := by
  have h := mul_neg_geom_sum r k
  have hs : ∑ i ∈ range k, r ^ i < k := by
    calc ∑ i ∈ range k, r ^ i < ∑ _i ∈ range k, (1 : ℝ) :=
          sum_lt_sum (fun i _ => pow_le_one₀ hr0 hr1.le)
            ⟨1, mem_range.2 (by omega), by simpa using hr1⟩
      _ = k := by simp
  rw [← h]; nlinarith

/-- With mean at most `1` and `p 1 < 1`, there is no root of `h z = z` in `[0,1)`. -/
theorem no_root_lt_one (hp : IsOffspring p) (h1 : p 1 < 1) {m : ℝ}
    (hm : HasSum (fun k : ℕ => (k : ℝ) * p k) m) (hm1 : m ≤ 1) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hroot : offspringGF p r = r) : False := by
  have hrI : r ∈ Icc (0 : ℝ) 1 := ⟨hr0, hr1.le⟩
  have hr : HasSum (fun k => p k * r ^ k) (offspringGF p r) := (summable_term hp hrI).hasSum
  have h2 : HasSum (fun k => p k * (1 - r ^ k)) (1 - offspringGF p r) := by
    have := hp.hasSum.sub hr
    convert this using 1
    funext k; ring
  have h3 : HasSum (fun k : ℕ => ((k : ℝ) * p k) * (1 - r)) (m * (1 - r)) := hm.mul_right _
  have hT := h3.sub h2
  have ht : ∀ k : ℕ, 0 ≤ ((k : ℝ) * p k) * (1 - r) - p k * (1 - r ^ k) := fun k => by
    have := one_sub_pow_le r hr0 hr1 k
    have := hp.nonneg k
    nlinarith
  have hS0 : 0 ≤ m * (1 - r) - (1 - offspringGF p r) := hasSum_le ht hasSum_zero hT
  have hS1 : m * (1 - r) - (1 - offspringGF p r) ≤ 0 := by
    rw [hroot]; nlinarith
  have hz : HasSum (fun k : ℕ => ((k : ℝ) * p k) * (1 - r) - p k * (1 - r ^ k)) 0 := by
    have : m * (1 - r) - (1 - offspringGF p r) = 0 := le_antisymm hS1 hS0
    rwa [this] at hT
  have hall := (hasSum_zero_iff_of_nonneg ht).1 hz
  have hpk : ∀ k, 2 ≤ k → p k = 0 := by
    intro k hk
    have e := congrFun hall k
    simp only [Pi.zero_apply] at e
    have hlt := one_sub_pow_lt r hr0 hr1 k hk
    have : p k * ((k : ℝ) * (1 - r) - (1 - r ^ k)) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · linarith
  have hsup : ∀ k ∉ range 2, p k = 0 := fun k hk => hpk k (by simp at hk; omega)
  have hsum1 : p 0 + p 1 = 1 := by
    have := hp.hasSum.tsum_eq
    rw [tsum_eq_sum hsup] at this
    simpa [sum_range_succ] using this
  have hg : offspringGF p r = p 0 + p 1 * r := by
    unfold offspringGF
    rw [tsum_eq_sum (s := range 2)]
    · simp [sum_range_succ]
    · intro k hk
      simp [hsup k hk]
  rw [hg] at hroot
  nlinarith [hp.nonneg 0, hp.nonneg 1]

end Branching

open Branching in
/-- Grinstead–Snell Theorem 10.2 (PR-106), mean at most one. If the mean number of offspring
`∑ k p_k` is finite and at most `1` (and `p 1 < 1`, excluding the degenerate law `h z = z`), the process
dies out with probability `1`. -/
@[kb "grinsteadsnell2006" "Theorem 10.2, p. 388"]
theorem extinction_prob_eq_one {p : ℕ → ℝ} (hp : IsOffspring p) (h1 : p 1 < 1)
    (hs : Summable fun k : ℕ => (k : ℝ) * p k) (hm : ∑' k : ℕ, (k : ℝ) * p k ≤ 1) :
    extinctionProb p = 1 := by
  obtain ⟨_, _, ⟨hmem, hfix⟩, hleast⟩ := extinction_smallest_root hp
  rcases hmem.2.lt_or_eq with h | h
  · exact (no_root_lt_one hp h1 hs.hasSum hm hmem.1 h hfix).elim
  · exact h

/-- If the mean offspring number exceeds `1` (finite and `> 1`, or infinite), then some partial sum
`∑_{k<K} k p_k` already exceeds `1`. -/
theorem Branching.exists_partial_gt {p : ℕ → ℝ} (hp : IsOffspring p)
    (hm : ¬ (Summable (fun k : ℕ => (k : ℝ) * p k) ∧ ∑' k : ℕ, (k : ℝ) * p k ≤ 1)) :
    ∃ K, 1 < ∑ k ∈ range K, (k : ℝ) * p k := by
  by_contra hcon
  push Not at hcon
  have hnn : ∀ k : ℕ, 0 ≤ (k : ℝ) * p k := fun k => mul_nonneg (Nat.cast_nonneg k) (hp.nonneg k)
  exact hm ⟨summable_of_sum_range_le hnn hcon, Real.tsum_le_of_sum_range_le hnn hcon⟩

open Branching in
/-- Grinstead–Snell Theorem 10.2 (PR-106), mean larger than one. If the mean number of offspring exceeds
`1` (the series `∑ k p_k` has sum `> 1` or diverges), the extinction probability is `< 1`. -/
@[kb "grinsteadsnell2006" "Theorem 10.2, p. 388"]
theorem extinction_prob_lt_one {p : ℕ → ℝ} (hp : IsOffspring p)
    (hm : ¬ (Summable (fun k : ℕ => (k : ℝ) * p k) ∧ ∑' k : ℕ, (k : ℝ) * p k ≤ 1)) :
    extinctionProb p < 1 := by
  obtain ⟨_, _, ⟨hmem, hfix⟩, hleast⟩ := extinction_smallest_root hp
  obtain ⟨K, hK⟩ := exists_partial_gt hp hm
  set q : ℝ → ℝ := fun z => ∑ k ∈ range K, p k * ∑ i ∈ range k, z ^ i with hq
  have hqc : Continuous q := by simp only [hq]; fun_prop
  have hq1 : q 1 = ∑ k ∈ range K, (k : ℝ) * p k := by
    simp only [hq]
    refine sum_congr rfl fun k _ => ?_
    simp [mul_comm]
  have hev : ∀ᶠ z in 𝓝[<] (1 : ℝ), 1 < q z :=
    nhdsWithin_le_nhds ((hqc.continuousAt (x := 1)).eventually_const_lt (by rw [hq1]; exact hK))
  obtain ⟨z, hzq, hz0, hz1⟩ :=
    (hev.and (Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num))).exists
  have hzI : z ∈ Icc (0 : ℝ) 1 := ⟨hz0.le, hz1.le⟩
  -- 1 - h z ≥ ∑_{k<K} p_k (1 - z^k) = (1 - z) q z > 1 - z, hence h z < z
  have hlow : (1 - z) * q z ≤ 1 - offspringGF p z := by
    have h2 : HasSum (fun k => p k * (1 - z ^ k)) (1 - offspringGF p z) := by
      have := hp.hasSum.sub (summable_term hp hzI).hasSum
      convert this using 1
      · funext k; ring
      · rfl
    have hle := sum_le_hasSum (range K) (fun k _ => mul_nonneg (hp.nonneg k)
      (sub_nonneg.2 (pow_le_one₀ hz0.le hz1.le))) h2
    calc (1 - z) * q z = ∑ k ∈ range K, p k * (1 - z ^ k) := by
          simp only [hq]
          rw [mul_sum]
          refine sum_congr rfl fun k _ => ?_
          rw [← mul_neg_geom_sum z k]
          ring
      _ ≤ _ := hle
  have hlt : offspringGF p z < z := by nlinarith
  -- intermediate value theorem for g = h - id on [0, z]
  have hg : ContinuousOn (fun x => offspringGF p x - x) (Icc 0 z) :=
    ((gf_continuousOn hp).mono (Icc_subset_Icc le_rfl hz1.le)).sub continuousOn_id
  have h0 : (0 : ℝ) ∈ Icc (offspringGF p z - z) (offspringGF p 0 - 0) := by
    refine ⟨by linarith, ?_⟩
    rw [gf_zero]; simpa using hp.nonneg 0
  obtain ⟨r, hrI, hr⟩ := intermediate_value_Icc' hz0.le hg h0
  have hrI' : r ∈ Icc (0 : ℝ) 1 := ⟨hrI.1, hrI.2.trans hz1.le⟩
  have := hleast ⟨hrI', by simp only at hr; linarith⟩
  linarith [hrI.2]

end UndergradKB.Probability
