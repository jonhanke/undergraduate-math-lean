import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Nat.Factorization.Basic
import UndergradKB.Topology.PeriodThree
import UndergradKB.Common.Attr

/-!
# The Sharkovskii order and the easy cases of Sharkovskii's theorem

Morris, *Topology Without Tears* (2024), Appendix 3, Theorem A3.6.4 (`morris2024`): if a continuous
`f : ℝ → ℝ` has a point of prime period `n`, it has a point of prime period `k` for every `k` after `n` in
the Sharkovskii order `3 ▹ 5 ▹ 7 ▹ ... ▹ 2·3 ▹ 2·5 ▹ ... ▹ 2²·3 ▹ ... ▹ 2³ ▹ 2² ▹ 2 ▹ 1`.

Here: the order as a bridging definition (strict total order on positive integers), and the cases
`n = 1`, `n = 2` and `n = 3` of the theorem, plus "a point of period `≥ 2` forces a fixed point".
The general case is not proved (see the report).
-/

open Function Set

namespace UndergradKB.Topology

/-- The Sharkovskii order on `n = 2^a · m` and `k = 2^b · l` (`m`, `l` odd), as arithmetic on the data
`(a, m)`, `(b, l)`: `n ▹ k` ("`k` comes after `n`"). -/
def sharkovskiiAux (a m b l : ℕ) : Prop :=
  (1 < m ∧ 1 < l ∧ (a < b ∨ (a = b ∧ m < l))) ∨ (1 < m ∧ l = 1) ∨ (m = 1 ∧ l = 1 ∧ b < a)

/-- `SharkovskiiLT n k`: `k` comes after `n` in the Sharkovskii order
`3 ▹ 5 ▹ 7 ▹ ... ▹ 2·3 ▹ ... ▹ 2³ ▹ 2² ▹ 2 ▹ 1` (meant for positive `n`, `k`). -/
def SharkovskiiLT (n k : ℕ) : Prop :=
  sharkovskiiAux (n.factorization 2) (n / 2 ^ n.factorization 2) (k.factorization 2)
    (k / 2 ^ k.factorization 2)

private lemma sharkovskiiAux_trans {a m b l c r : ℕ} (h1 : sharkovskiiAux a m b l)
    (h2 : sharkovskiiAux b l c r) : sharkovskiiAux a m c r := by
  unfold sharkovskiiAux at *
  omega

private lemma sharkovskiiAux_irrefl (a m : ℕ) : ¬ sharkovskiiAux a m a m := by
  unfold sharkovskiiAux
  omega

/-- Morris, Topology Without Tears, Remark A3.6.3 (TP-448). The Sharkovskii order is irreflexive. -/
@[kb "morris2024" "Remark A3.6.3, p. 458"]
theorem SharkovskiiLT.irrefl (n : ℕ) : ¬ SharkovskiiLT n n := sharkovskiiAux_irrefl _ _

/-- Morris, Topology Without Tears, Remark A3.6.3 (TP-448). The Sharkovskii order is transitive. -/
@[kb "morris2024" "Remark A3.6.3, p. 458"]
theorem SharkovskiiLT.trans {n k j : ℕ} (h1 : SharkovskiiLT n k) (h2 : SharkovskiiLT k j) :
    SharkovskiiLT n j := sharkovskiiAux_trans h1 h2

/-- Morris, Topology Without Tears, Remark A3.6.3 (TP-448). Any two distinct positive integers are
comparable in the Sharkovskii order. -/
@[kb "morris2024" "Remark A3.6.3, p. 458"]
theorem SharkovskiiLT.total {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (hne : n ≠ k) :
    SharkovskiiLT n k ∨ SharkovskiiLT k n := by
  have e1 : 2 ^ n.factorization 2 * (n / 2 ^ n.factorization 2) = n :=
    Nat.ordProj_mul_ordCompl_eq_self n 2
  have e2 : 2 ^ k.factorization 2 * (k / 2 ^ k.factorization 2) = k :=
    Nat.ordProj_mul_ordCompl_eq_self k 2
  unfold SharkovskiiLT sharkovskiiAux
  generalize n.factorization 2 = a at *
  generalize k.factorization 2 = b at *
  generalize n / 2 ^ a = m at *
  generalize k / 2 ^ b = l at *
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp at e1; omega
    · exact h
  have hl : 0 < l := by
    rcases Nat.eq_zero_or_pos l with rfl | h
    · simp at e2; omega
    · exact h
  have hne' : a ≠ b ∨ m ≠ l := by
    by_contra h
    push Not at h
    obtain ⟨rfl, rfl⟩ := h
    exact hne (e1.symm.trans e2)
  omega

/-- The least element `3` precedes every other positive integer `k` that is not a... trivial instance used
below: nothing comes after `1`. -/
theorem not_sharkovskiiLT_one (k : ℕ) : ¬ SharkovskiiLT 1 k := by
  unfold SharkovskiiLT sharkovskiiAux
  simp only [Nat.factorization_one, Finsupp.coe_zero, Pi.zero_apply, pow_zero, Nat.div_one]
  omega

/-- The only positive integer after `2` is `1`. -/
theorem eq_one_of_sharkovskiiLT_two {k : ℕ} (hk : 0 < k) (h : SharkovskiiLT 2 k) : k = 1 := by
  have e2 : 2 ^ k.factorization 2 * (k / 2 ^ k.factorization 2) = k :=
    Nat.ordProj_mul_ordCompl_eq_self k 2
  have h2 : (2 : ℕ).factorization 2 = 1 := Nat.Prime.factorization_self Nat.prime_two
  unfold SharkovskiiLT sharkovskiiAux at h
  rw [h2] at h
  simp only [pow_one, Nat.div_self (by norm_num : 0 < 2)] at h
  generalize k.factorization 2 = b at *
  generalize k / 2 ^ b = l at *
  have : b = 0 ∧ l = 1 := by omega
  obtain ⟨rfl, rfl⟩ := this
  simpa using e2.symm

/-! ### A fixed point from any cycle -/

/-- A continuous map of the real line with a point of prime period `n ≥ 2` has a fixed point (Sharkovskii:
`2 ▹ 1` and every `n ≥ 2` precedes `1`). -/
@[kb "morris2024" "Theorem A3.6.4, p. 458"]
theorem exists_isFixedPt_of_two_le_minimalPeriod {f : ℝ → ℝ} (hf : Continuous f) {x : ℝ} {n : ℕ}
    (hx : minimalPeriod f x = n) (hn : 2 ≤ n) : ∃ p, IsFixedPt f p := by
  set S : Set ℝ := (fun k : ℕ => f^[k] x) '' Iio n with hS
  have hfin : S.Finite := (Set.finite_Iio n).image _
  have hne : S.Nonempty := ⟨x, 0, by simp; omega, rfl⟩
  have hper : IsPeriodicPt f n x := by rw [← hx]; exact isPeriodicPt_minimalPeriod f x
  have hpos : 0 < n := by omega
  have hclosed : ∀ y ∈ S, f y ∈ S := by
    rintro _ ⟨k, -, rfl⟩
    refine ⟨(k + 1) % n, Nat.mod_lt _ hpos, ?_⟩
    show f^[(k + 1) % n] x = f (f^[k] x)
    rw [← hx, iterate_mod_minimalPeriod_eq, iterate_succ_apply']
  have hxp : x ∈ periodicPts f := mk_mem_periodicPts hpos hper
  have hnofix : ∀ y ∈ S, f y ≠ y := by
    rintro _ ⟨k, -, rfl⟩ h
    have h1 := minimalPeriod_eq_one_iff_isFixedPt.mpr h
    rw [minimalPeriod_apply_iterate hxp k, hx] at h1
    omega
  have hu : sInf S ∈ S := hne.csInf_mem hfin
  have hM : sSup S ∈ S := hne.csSup_mem hfin
  have h1 : sInf S < f (sInf S) :=
    lt_of_le_of_ne (csInf_le hfin.bddBelow (hclosed _ hu)) (hnofix _ hu).symm
  have h2 : f (sSup S) < sSup S :=
    lt_of_le_of_ne (le_csSup hfin.bddAbove (hclosed _ hM)) (hnofix _ hM)
  have h3 : sInf S ≤ sSup S := csInf_le hfin.bddBelow hM
  have hc : ContinuousOn (fun t => f t - t) (Icc (sInf S) (sSup S)) :=
    (hf.sub continuous_id).continuousOn
  have h0 : (0 : ℝ) ∈ Icc (f (sSup S) - sSup S) (f (sInf S) - sInf S) :=
    ⟨by linarith, by linarith⟩
  obtain ⟨p, -, hp⟩ := intermediate_value_Icc' h3 hc h0
  exact ⟨p, by simp only at hp; show f p = p; linarith⟩

/-- The `n = 3` case of Sharkovskii's theorem is the Period Three Theorem: `3` precedes every other `k`. -/
theorem sharkovskii_of_period_three {f : ℝ → ℝ} (hf : Continuous f) (h3 : ∃ a, minimalPeriod f a = 3)
    {k : ℕ} (hk : 0 < k) : ∃ x, minimalPeriod f x = k :=
  exists_minimalPeriod_eq_of_minimalPeriod_three hf h3 k hk

/-- Morris, Topology Without Tears, Theorem A3.6.4 (TP-448), the cases `n = 1` and `n = 2`: a continuous
`f : ℝ → ℝ` with a point of prime period `n ∈ {1, 2}` has points of prime period `k` for all `k` after `n`. -/
@[kb "morris2024" "Theorem A3.6.4, p. 458"]
theorem sharkovskii_of_period_one_or_two {f : ℝ → ℝ} (hf : Continuous f) {n : ℕ} (hn : n = 1 ∨ n = 2)
    (hper : ∃ a, minimalPeriod f a = n) {k : ℕ} (hk : 0 < k) (hlt : SharkovskiiLT n k) :
    ∃ x, minimalPeriod f x = k := by
  obtain ⟨a, ha⟩ := hper
  rcases hn with rfl | rfl
  · exact absurd hlt (not_sharkovskiiLT_one k)
  · obtain rfl := eq_one_of_sharkovskiiLT_two hk hlt
    obtain ⟨p, hp⟩ := exists_isFixedPt_of_two_le_minimalPeriod hf ha le_rfl
    exact ⟨p, minimalPeriod_eq_one_iff_isFixedPt.mpr hp⟩

/-! ### A point of period `n ≥ 2` forces a point of period `2` -/

/-- The finite orbit set of a point of prime period `n ≥ 2`: nonempty, finite, mapped into itself by `f`,
without fixed points. -/
private lemma exists_orbit_set {f : ℝ → ℝ} {x : ℝ} {n : ℕ} (hx : minimalPeriod f x = n) (hn : 2 ≤ n) :
    ∃ S : Set ℝ, S.Finite ∧ S.Nonempty ∧ (∀ y ∈ S, f y ∈ S) ∧ (∀ y ∈ S, f y ≠ y) := by
  have hpos : 0 < n := by omega
  have hper : IsPeriodicPt f n x := by rw [← hx]; exact isPeriodicPt_minimalPeriod f x
  have hxp : x ∈ periodicPts f := mk_mem_periodicPts hpos hper
  refine ⟨(fun k : ℕ => f^[k] x) '' Iio n, (Set.finite_Iio n).image _, ⟨x, 0, by simp; omega, rfl⟩,
    ?_, ?_⟩
  · rintro _ ⟨k, -, rfl⟩
    refine ⟨(k + 1) % n, Nat.mod_lt _ hpos, ?_⟩
    show f^[(k + 1) % n] x = f (f^[k] x)
    rw [← hx, iterate_mod_minimalPeriod_eq, iterate_succ_apply']
  · rintro _ ⟨k, -, rfl⟩ h
    have h1 := minimalPeriod_eq_one_iff_isFixedPt.mpr h
    rw [minimalPeriod_apply_iterate hxp k, hx] at h1
    omega

/-- Descent case: if `a < f a`, `f (f a) < a` and `m ≤ f (f m)` with `m ≤ a`, then some `x` has
`f (f x) = x` and `f x ≠ x`. -/
private lemma exists_two_cycle_of_descent {f : ℝ → ℝ} (hf : Continuous f) {a m : ℝ} (hma : m ≤ a)
    (ha : a < f a) (hFa : f (f a) < a) (hm : m ≤ f (f m)) : ∃ x, f (f x) = x ∧ f x ≠ x := by
  have hg : Continuous fun x => f (f x) - x := (hf.comp hf).sub continuous_id
  by_cases hZ : ∃ y ∈ Icc m a, f y = y
  · -- the last fixed point `u` of `f` in `[m, a]`
    obtain ⟨y0, hy0, hfy0⟩ := hZ
    have hcomp : IsCompact (Icc m a ∩ {y | f y = y}) :=
      isCompact_Icc.inter_right (isClosed_eq hf continuous_id)
    obtain ⟨u, ⟨huI, hfu⟩, humax⟩ := hcomp.exists_isGreatest ⟨y0, hy0, hfy0⟩
    have hfu' : f u = u := hfu
    have humax : ∀ y ∈ Icc m a, f y = y → y ≤ u := fun y hy hfy => humax ⟨hy, hfy⟩
    have hua : u < a := by
      refine lt_of_le_of_ne huI.2 ?_
      rintro rfl
      linarith
    -- `f > id` on `(u, a]`
    have hpos : ∀ y ∈ Ioc u a, y < f y := by
      intro y hy
      by_contra hle
      push Not at hle
      have hne : f y ≠ y := fun h => absurd (humax y ⟨huI.1.trans hy.1.le, hy.2⟩ h) (not_le.mpr hy.1)
      have hlt : f y < y := lt_of_le_of_ne hle hne
      have hc : ContinuousOn (fun t => f t - t) (Icc y a) := (hf.sub continuous_id).continuousOn
      have h0 : (0 : ℝ) ∈ Icc (f y - y) (f a - a) := ⟨by linarith, by linarith⟩
      obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc hy.2 hc h0
      have : f z = z := by simp only at hz0; linarith
      have := humax z ⟨huI.1.trans (hy.1.le.trans hz.1), hz.2⟩ this
      linarith [hz.1, hy.1]
    -- a point `s` just above `u` with `f s < a`
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuous_iff.mp hf u (a - u) (by linarith)
    set s : ℝ := u + min (δ / 2) ((a - u) / 2) with hs
    have hmin_pos : 0 < min (δ / 2) ((a - u) / 2) := lt_min (by linarith) (by linarith)
    have hsu : u < s := by rw [hs]; linarith
    have hsa : s < a := by
      have := min_le_right (δ / 2) ((a - u) / 2)
      rw [hs]; linarith
    have hdist : dist s u < δ := by
      rw [Real.dist_eq, hs, add_sub_cancel_left, abs_of_pos hmin_pos]
      have := min_le_left (δ / 2) ((a - u) / 2)
      linarith
    have hfs : f s < a := by
      have := hδ' s hdist
      rw [Real.dist_eq, hfu', abs_lt] at this
      linarith [this.2]
    have hsI : s ∈ Ioc u a := ⟨hsu, hsa.le⟩
    have hfsI : f s ∈ Ioc u a := ⟨lt_trans hsu (hpos s hsI), hfs.le⟩
    have hgs : 0 < f (f s) - s := by
      have := hpos s hsI
      have := hpos (f s) hfsI
      linarith
    have h0 : (0 : ℝ) ∈ Icc (f (f a) - a) (f (f s) - s) := ⟨by linarith, hgs.le⟩
    obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc' hsa.le hg.continuousOn h0
    have hx2 : f (f x) = x := by simp only at hx0; linarith
    refine ⟨x, hx2, fun hfx => ?_⟩
    have := hpos x ⟨lt_of_lt_of_le hsu hx.1, hx.2⟩
    linarith
  · push Not at hZ
    have h0 : (0 : ℝ) ∈ Icc (f (f a) - a) (f (f m) - m) := ⟨by linarith, by linarith⟩
    obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc' hma hg.continuousOn h0
    exact ⟨x, by simp only at hx0; linarith, hZ x hx⟩

/-- Loop case: `[a, b] → [b, c] → [a, b]` under `f` with `b` not fixed gives a point of period `2`. -/
private lemma exists_two_cycle_of_loop {f : ℝ → ℝ} (hf : Continuous f) {a b c : ℝ} (hab : a < b)
    (hbc : b < c) (h1 : f b ≤ a) (h2 : f a = c) (h3 : b ≤ f c) (hbfix : f b ≠ b) :
    ∃ x, f (f x) = x ∧ f x ≠ x := by
  have hI : Icc b c ⊆ f '' Icc a b := by
    have := intermediate_value_Icc' hab.le hf.continuousOn
    rw [h2] at this
    exact (Icc_subset_Icc (h1.trans hab.le) le_rfl).trans this
  have hK : Icc a b ⊆ f '' Icc b c :=
    (Icc_subset_Icc h1 h3).trans (intermediate_value_Icc hbc.le hf.continuousOn)
  obtain ⟨s, t, hs, hst, ht, himg⟩ := exists_subinterval_image_eq hf hbc.le hI
  have hsub : Icc s t ⊆ (fun x => f (f x)) '' Icc s t := by
    have e : (fun x => f (f x)) '' Icc s t = f '' Icc b c := by
      rw [← Set.image_image f f, himg]
    rw [e]
    exact (Icc_subset_Icc hs ht).trans hK
  obtain ⟨x, hx, hfx⟩ := exists_fixedPt_of_subset_image (hf.comp hf) hst hsub
  refine ⟨x, hfx, fun hfix => hbfix ?_⟩
  have hxfx : f x ∈ Icc b c := by rw [← himg]; exact ⟨x, hx, rfl⟩
  have hxI : x ∈ Icc a b := ⟨hs.trans hx.1, hx.2.trans ht⟩
  have hxb : x = b := le_antisymm hxI.2 (by have := hxfx.1; rwa [hfix] at this)
  rw [hxb] at hfix
  exact hfix

/-- Morris, Topology Without Tears, Theorem A3.6.4 (TP-448), the case `k = 2`: a continuous
`f : ℝ → ℝ` with a point of prime period `n ≥ 2` has a point of prime period `2`. -/
@[kb "morris2024" "Theorem A3.6.4, p. 458"]
theorem exists_minimalPeriod_two_of_two_le_minimalPeriod {f : ℝ → ℝ} (hf : Continuous f) {x : ℝ}
    {n : ℕ} (hx : minimalPeriod f x = n) (hn : 2 ≤ n) : ∃ y, minimalPeriod f y = 2 := by
  obtain ⟨S, hfin, hne, hcl, hnf⟩ := exists_orbit_set hx hn
  suffices h : ∃ y, f (f y) = y ∧ f y ≠ y by
    obtain ⟨y, h1, h2⟩ := h
    exact ⟨y, minimalPeriod_eq_prime (p := 2) h1 h2⟩
  -- `a` = the largest point of the orbit that is moved up; `b` = the next orbit point
  set L : Set ℝ := {y ∈ S | y < f y} with hLdef
  have hL : L.Finite := hfin.subset fun y hy => hy.1
  have hmS : sInf S ∈ S := hne.csInf_mem hfin
  have hLne : L.Nonempty :=
    ⟨sInf S, hmS, lt_of_le_of_ne (csInf_le hfin.bddBelow (hcl _ hmS)) (hnf _ hmS).symm⟩
  have haL : sSup L ∈ L := hLne.csSup_mem hL
  set a := sSup L with hadef
  have haS : a ∈ S := haL.1
  have hfa : a < f a := haL.2
  have hMS : sSup S ∈ S := hne.csSup_mem hfin
  have hfM : f (sSup S) < sSup S :=
    lt_of_le_of_ne (le_csSup hfin.bddAbove (hcl _ hMS)) (hnf _ hMS)
  have haM : a < sSup S := by
    refine lt_of_le_of_ne (le_csSup hfin.bddAbove haS) fun h => ?_
    have := le_csSup hfin.bddAbove (hcl _ haS)
    linarith
  set U : Set ℝ := {y ∈ S | a < y} with hUdef
  have hU : U.Finite := hfin.subset fun y hy => hy.1
  have hUne : U.Nonempty := ⟨sSup S, hMS, haM⟩
  have hbU : sInf U ∈ U := hUne.csInf_mem hU
  set b := sInf U with hbdef
  have hbS : b ∈ S := hbU.1
  have hab : a < b := hbU.2
  have hbmin : ∀ y ∈ S, a < y → b ≤ y := fun y hy h => csInf_le hU.bddBelow ⟨hy, h⟩
  have hfb : f b < b := by
    refine lt_of_le_of_ne ?_ (hnf _ hbS)
    by_contra hlt
    push Not at hlt
    have : b ≤ a := le_csSup hL.bddAbove ⟨hbS, hlt⟩
    linarith
  have hfba : f b ≤ a := by
    by_contra hlt
    push Not at hlt
    have := hbmin _ (hcl _ hbS) hlt
    linarith
  have hca : b ≤ f a := hbmin _ (hcl _ haS) hfa
  by_cases he : f (f a) ≤ a
  · rcases he.eq_or_lt with heq | hlt
    · exact ⟨a, heq, (hnf _ haS)⟩
    · exact exists_two_cycle_of_descent hf (csInf_le hfin.bddBelow haS) hfa hlt
        (csInf_le hfin.bddBelow (hcl _ (hcl _ hmS)))
  · push Not at he
    have hbe : b ≤ f (f a) := hbmin _ (hcl _ (hcl _ haS)) he
    have hcb : b < f a := by
      refine lt_of_le_of_ne hca fun h => ?_
      rw [← h] at he
      linarith
    exact exists_two_cycle_of_loop hf hab hcb hfba rfl hbe (hnf _ hbS)

/-! ### The reduction `f ↦ f²` and the powers of two -/

/-- A point of prime period `2^j` (`j ≥ 1`) for `f²` has prime period `2^(j+1)` for `f`. -/
theorem minimalPeriod_eq_two_pow_succ_of_iterate_two {f : ℝ → ℝ} {y : ℝ} {j : ℕ} (hj : 1 ≤ j)
    (h : minimalPeriod (f^[2]) y = 2 ^ j) : minimalPeriod f y = 2 ^ (j + 1) := by
  rw [minimalPeriod_iterate_eq_div_gcd two_ne_zero] at h
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  set p := minimalPeriod f y with hp
  rcases Nat.even_or_odd p with he | ho
  · have h2 : (2 : ℕ) ∣ p := even_iff_two_dvd.mp he
    rw [Nat.gcd_eq_right h2] at h
    rw [pow_succ] at h ⊢
    omega
  · have hodd : p % 2 = 1 := Nat.odd_iff.mp ho
    have hg : Nat.gcd p 2 = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp (Nat.gcd_dvd_right p 2) with h1 | h1
      · exact h1
      · exfalso
        have := Nat.gcd_dvd_left p 2
        rw [h1] at this
        omega
    rw [hg, Nat.div_one, pow_succ] at h
    omega

/-- Morris, Topology Without Tears, Theorem A3.6.4 (TP-448), powers of two: a continuous `f : ℝ → ℝ` with a
point of prime period `2^a` has points of prime period `2^b` for every `b ≤ a`. -/
@[kb "morris2024" "Theorem A3.6.4, p. 458"]
theorem exists_minimalPeriod_two_pow_of_le {a : ℕ} {f : ℝ → ℝ} (hf : Continuous f) {x : ℝ}
    (hx : minimalPeriod f x = 2 ^ a) : ∀ b ≤ a, ∃ y, minimalPeriod f y = 2 ^ b := by
  induction a generalizing f x with
  | zero =>
    intro b hb
    obtain rfl : b = 0 := by omega
    exact ⟨x, hx⟩
  | succ a ih =>
    intro b hb
    have h2 : 2 ≤ 2 ^ (a + 1) := by
      have := Nat.one_le_two_pow (n := a)
      rw [pow_succ]; omega
    rcases Nat.lt_or_ge b (a + 1) with hlt | hge
    · rcases Nat.eq_zero_or_pos b with rfl | hb0
      · obtain ⟨p, hp⟩ := exists_isFixedPt_of_two_le_minimalPeriod hf hx h2
        exact ⟨p, by simpa using minimalPeriod_eq_one_iff_isFixedPt.mpr hp⟩
      · by_cases hb1 : b = 1
        · subst hb1
          obtain ⟨y, hy⟩ := exists_minimalPeriod_two_of_two_le_minimalPeriod hf hx h2
          exact ⟨y, by simpa using hy⟩
        · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
          have hg : Continuous (f^[2]) := hf.iterate 2
          have hxg : minimalPeriod (f^[2]) x = 2 ^ (a' + 1) := by
            rw [minimalPeriod_iterate_eq_div_gcd two_ne_zero, hx]
            have : Nat.gcd (2 ^ (a' + 1 + 1)) 2 = 2 := Nat.gcd_eq_right (dvd_pow_self 2 (by omega))
            rw [this, pow_succ 2 (a' + 1)]
            omega
          obtain ⟨y, hy⟩ := ih hg hxg (b - 1) (by omega)
          refine ⟨y, ?_⟩
          have := minimalPeriod_eq_two_pow_succ_of_iterate_two (f := f) (by omega) hy
          rwa [show b - 1 + 1 = b by omega] at this
    · obtain rfl : b = a + 1 := by omega
      exact ⟨x, hx⟩

/-- A point of prime period `3 · 2^a` forces points of prime period `2^b` for every `b` (the cases
`a = 0` is the Period Three Theorem; the general case reduces to it through `f ↦ f²`). -/
theorem exists_minimalPeriod_two_pow_of_three_mul_two_pow {a : ℕ} {f : ℝ → ℝ} (hf : Continuous f)
    {x : ℝ} (hx : minimalPeriod f x = 3 * 2 ^ a) : ∀ b : ℕ, ∃ y, minimalPeriod f y = 2 ^ b := by
  induction a generalizing f x with
  | zero =>
    intro b
    exact exists_minimalPeriod_eq_of_minimalPeriod_three hf ⟨x, by simpa using hx⟩ _
      (Nat.two_pow_pos b)
  | succ a ih =>
    intro b
    have h2 : 2 ≤ 3 * 2 ^ (a + 1) := by
      have := Nat.one_le_two_pow (n := a)
      rw [pow_succ]; omega
    rcases Nat.eq_zero_or_pos b with rfl | hb0
    · obtain ⟨p, hp⟩ := exists_isFixedPt_of_two_le_minimalPeriod hf hx h2
      exact ⟨p, by simpa using minimalPeriod_eq_one_iff_isFixedPt.mpr hp⟩
    · by_cases hb1 : b = 1
      · subst hb1
        obtain ⟨y, hy⟩ := exists_minimalPeriod_two_of_two_le_minimalPeriod hf hx h2
        exact ⟨y, by simpa using hy⟩
      · have hg : Continuous (f^[2]) := hf.iterate 2
        have hxg : minimalPeriod (f^[2]) x = 3 * 2 ^ a := by
          rw [minimalPeriod_iterate_eq_div_gcd two_ne_zero, hx]
          have : Nat.gcd (3 * 2 ^ (a + 1)) 2 = 2 := by
            apply Nat.gcd_eq_right
            exact Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) 3
          rw [this, pow_succ 2 a]
          omega
        obtain ⟨y, hy⟩ := ih hg hxg (b - 1)
        refine ⟨y, ?_⟩
        have := minimalPeriod_eq_two_pow_succ_of_iterate_two (f := f) (by omega) hy
        rwa [show b - 1 + 1 = b by omega] at this

/-- Morris, Topology Without Tears, Theorem A3.6.4 (TP-448), the case `n = 2^a`: a point of prime period
`2^a` gives points of prime period `k` for every `k` after `2^a` in the Sharkovskii order. -/
@[kb "morris2024" "Theorem A3.6.4, p. 458"]
theorem sharkovskii_of_period_two_pow {a : ℕ} {f : ℝ → ℝ} (hf : Continuous f)
    (hper : ∃ x, minimalPeriod f x = 2 ^ a) {k : ℕ} (hk : 0 < k) (hlt : SharkovskiiLT (2 ^ a) k) :
    ∃ y, minimalPeriod f y = k := by
  obtain ⟨x, hx⟩ := hper
  have e2 : 2 ^ k.factorization 2 * (k / 2 ^ k.factorization 2) = k :=
    Nat.ordProj_mul_ordCompl_eq_self k 2
  have h2 : (2 ^ a).factorization 2 = a := by
    rw [Nat.Prime.factorization_pow Nat.prime_two]; simp
  unfold SharkovskiiLT sharkovskiiAux at hlt
  rw [h2, Nat.div_self (Nat.two_pow_pos a)] at hlt
  generalize k.factorization 2 = b at *
  generalize k / 2 ^ b = l at *
  have hb : l = 1 ∧ b < a := by omega
  obtain ⟨rfl, hba⟩ := hb
  rw [mul_one] at e2
  subst e2
  exact exists_minimalPeriod_two_pow_of_le hf hx b hba.le

end UndergradKB.Topology
