import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Nth
import UndergradKB.Common.Attr

namespace UndergradKB.Calculus

open Filter Finset Topology

/-! ## Greedy rearrangement (abstract form)

Given an enumeration `P` of the indices of the nonnegative terms and `N` of the negative terms, the greedy
procedure adds the next unused nonnegative term while the running sum is `≤ L` and the next unused negative
term otherwise. -/

section Greedy

variable (a : ℕ → ℝ) (P N : ℕ → ℕ) (L : ℝ)

/-- Running sum after using the first `i` nonnegative and first `j` negative terms. -/
noncomputable def greedySum (i j : ℕ) : ℝ := ∑ k ∈ range i, a (P k) + ∑ k ∈ range j, a (N k)

/-- One step of the greedy procedure on the state `(i, j)`. -/
noncomputable def greedyStep (s : ℕ × ℕ) : ℕ × ℕ :=
  if greedySum a P N s.1 s.2 ≤ L then (s.1 + 1, s.2) else (s.1, s.2 + 1)

/-- The state `(i, j)` after `n` steps. -/
noncomputable def greedyState (n : ℕ) : ℕ × ℕ := (greedyStep a P N L)^[n] (0, 0)

/-- The condition "add a nonnegative term at step `n`". -/
def GreedyCond (n : ℕ) : Prop :=
  greedySum a P N (greedyState a P N L n).1 (greedyState a P N L n).2 ≤ L

/-- The index chosen at step `n`. -/
noncomputable def greedyFun (n : ℕ) : ℕ := by
  classical
  exact if GreedyCond a P N L n then P (greedyState a P N L n).1 else N (greedyState a P N L n).2

theorem greedyState_succ (n : ℕ) :
    greedyState a P N L (n + 1) = greedyStep a P N L (greedyState a P N L n) :=
  Function.iterate_succ_apply' _ _ _

theorem greedyState_succ_of_cond {n : ℕ} (h : GreedyCond a P N L n) :
    greedyState a P N L (n + 1) =
      ((greedyState a P N L n).1 + 1, (greedyState a P N L n).2) := by
  rw [greedyState_succ, greedyStep]
  simp only [GreedyCond] at h
  simp [h]

theorem greedyState_succ_of_not {n : ℕ} (h : ¬ GreedyCond a P N L n) :
    greedyState a P N L (n + 1) =
      ((greedyState a P N L n).1, (greedyState a P N L n).2 + 1) := by
  rw [greedyState_succ, greedyStep]
  simp only [GreedyCond] at h
  simp [h]

theorem greedyState_zero : greedyState a P N L 0 = (0, 0) := rfl

theorem greedyFun_of_cond {n : ℕ} (h : GreedyCond a P N L n) :
    greedyFun a P N L n = P (greedyState a P N L n).1 := by
  classical
  unfold greedyFun
  simp [h]

theorem greedyFun_of_not {n : ℕ} (h : ¬ GreedyCond a P N L n) :
    greedyFun a P N L n = N (greedyState a P N L n).2 := by
  classical
  unfold greedyFun
  simp [h]

theorem greedyState_sum (n : ℕ) :
    (greedyState a P N L n).1 + (greedyState a P N L n).2 = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases h : GreedyCond a P N L n
    · rw [greedyState_succ_of_cond a P N L h]; simp only; omega
    · rw [greedyState_succ_of_not a P N L h]; simp only; omega

theorem sum_greedyFun (n : ℕ) :
    ∑ i ∈ range n, a (greedyFun a P N L i) =
      greedySum a P N (greedyState a P N L n).1 (greedyState a P N L n).2 := by
  induction n with
  | zero => simp [greedyState_zero, greedySum]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : GreedyCond a P N L n
    · rw [greedyFun_of_cond a P N L h, greedyState_succ_of_cond a P N L h]
      simp [greedySum, Finset.sum_range_succ]
      ring
    · rw [greedyFun_of_not a P N L h, greedyState_succ_of_not a P N L h]
      simp [greedySum, Finset.sum_range_succ]
      ring

theorem greedyState_fst_mono : Monotone fun n => (greedyState a P N L n).1 := by
  refine monotone_nat_of_le_succ fun n => ?_
  by_cases h : GreedyCond a P N L n
  · rw [greedyState_succ_of_cond a P N L h]; simp
  · rw [greedyState_succ_of_not a P N L h]

theorem greedyState_snd_mono : Monotone fun n => (greedyState a P N L n).2 := by
  refine monotone_nat_of_le_succ fun n => ?_
  by_cases h : GreedyCond a P N L n
  · rw [greedyState_succ_of_cond a P N L h]
  · rw [greedyState_succ_of_not a P N L h]; simp

theorem greedyCond_infinitely_often
    (hNbot : Tendsto (fun j => ∑ k ∈ range j, a (N k)) atTop atBot) (n0 : ℕ) :
    ∃ n, n0 ≤ n ∧ GreedyCond a P N L n := by
  by_contra hcon
  push Not at hcon
  set i0 := (greedyState a P N L n0).1
  set j0 := (greedyState a P N L n0).2
  have hst : ∀ k, greedyState a P N L (n0 + k) = (i0, j0 + k) := by
    intro k
    induction k with
    | zero => simp [i0, j0]
    | succ k ih =>
      rw [← add_assoc, greedyState_succ_of_not a P N L (hcon _ (by omega)), ih]
      rfl
  obtain ⟨J, hJ⟩ := ((hNbot.eventually (eventually_le_atBot (L - ∑ k ∈ range i0, a (P k)))).exists_forall_of_atTop)
  have hc := hcon (n0 + J) (by omega)
  apply hc
  unfold GreedyCond
  rw [hst J]
  have := hJ (j0 + J) (by omega)
  simp only [greedySum]
  linarith

theorem greedyCond_not_infinitely_often
    (hPtop : Tendsto (fun i => ∑ k ∈ range i, a (P k)) atTop atTop) (n0 : ℕ) :
    ∃ n, n0 ≤ n ∧ ¬ GreedyCond a P N L n := by
  by_contra hcon
  push Not at hcon
  set i0 := (greedyState a P N L n0).1
  set j0 := (greedyState a P N L n0).2
  have hst : ∀ k, greedyState a P N L (n0 + k) = (i0 + k, j0) := by
    intro k
    induction k with
    | zero => simp [i0, j0]
    | succ k ih =>
      rw [← add_assoc, greedyState_succ_of_cond a P N L (hcon _ (by omega)), ih]
      rfl
  obtain ⟨J, hJ⟩ := ((hPtop.eventually (eventually_gt_atTop (L - ∑ k ∈ range j0, a (N k)))).exists_forall_of_atTop)
  have hc := hcon (n0 + J) (by omega)
  have hc' : GreedyCond a P N L (n0 + J) := hc
  unfold GreedyCond at hc'
  rw [hst J] at hc'
  have := hJ (i0 + J) (by omega)
  simp only [greedySum] at hc'
  linarith

theorem greedyState_fst_unbounded
    (hNbot : Tendsto (fun j => ∑ k ∈ range j, a (N k)) atTop atBot) (K : ℕ) :
    ∃ n, K ≤ (greedyState a P N L n).1 := by
  induction K with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ K ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨m, hm, hcm⟩ := greedyCond_infinitely_often a P N L hNbot n
    refine ⟨m + 1, ?_⟩
    rw [greedyState_succ_of_cond a P N L hcm]
    have := greedyState_fst_mono a P N L hm
    simp only at this ⊢
    omega

theorem greedyState_snd_unbounded
    (hPtop : Tendsto (fun i => ∑ k ∈ range i, a (P k)) atTop atTop) (K : ℕ) :
    ∃ n, K ≤ (greedyState a P N L n).2 := by
  induction K with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ K ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨m, hm, hcm⟩ := greedyCond_not_infinitely_often a P N L hPtop n
    refine ⟨m + 1, ?_⟩
    rw [greedyState_succ_of_not a P N L hcm]
    have := greedyState_snd_mono a P N L hm
    simp only at this ⊢
    omega

theorem exists_greedyFun_eq_P
    (hNbot : Tendsto (fun j => ∑ k ∈ range j, a (N k)) atTop atBot) (k : ℕ) :
    ∃ n, greedyFun a P N L n = P k := by
  classical
  have hex : ∃ n, k < (greedyState a P N L n).1 := by
    obtain ⟨n, hn⟩ := greedyState_fst_unbounded a P N L hNbot (k + 1)
    exact ⟨n, hn⟩
  set n := Nat.find hex with hn
  have hn1 : k < (greedyState a P N L n).1 := Nat.find_spec hex
  have hn0 : n ≠ 0 := by
    intro h0
    rw [h0, greedyState_zero] at hn1
    simp at hn1
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hm1 : ¬ k < (greedyState a P N L m).1 := Nat.find_min hex (by omega)
  have hcm : GreedyCond a P N L m := by
    by_contra hc
    rw [hm, greedyState_succ_of_not a P N L hc] at hn1
    exact hm1 hn1
  refine ⟨m, ?_⟩
  rw [greedyFun_of_cond a P N L hcm]
  rw [hm, greedyState_succ_of_cond a P N L hcm] at hn1
  simp only at hn1
  congr 1
  omega

theorem exists_greedyFun_eq_N
    (hPtop : Tendsto (fun i => ∑ k ∈ range i, a (P k)) atTop atTop) (k : ℕ) :
    ∃ n, greedyFun a P N L n = N k := by
  classical
  have hex : ∃ n, k < (greedyState a P N L n).2 := by
    obtain ⟨n, hn⟩ := greedyState_snd_unbounded a P N L hPtop (k + 1)
    exact ⟨n, hn⟩
  set n := Nat.find hex with hn
  have hn1 : k < (greedyState a P N L n).2 := Nat.find_spec hex
  have hn0 : n ≠ 0 := by
    intro h0
    rw [h0, greedyState_zero] at hn1
    simp at hn1
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hm1 : ¬ k < (greedyState a P N L m).2 := Nat.find_min hex (by omega)
  have hcm : ¬ GreedyCond a P N L m := by
    intro hc
    rw [hm, greedyState_succ_of_cond a P N L hc] at hn1
    exact hm1 hn1
  refine ⟨m, ?_⟩
  rw [greedyFun_of_not a P N L hcm]
  rw [hm, greedyState_succ_of_not a P N L hcm] at hn1
  simp only at hn1
  congr 1
  omega

theorem greedyFun_injective (hP : Function.Injective P) (hN : Function.Injective N)
    (hdisj : ∀ k l, P k ≠ N l) : Function.Injective (greedyFun a P N L) := by
  have aux : ∀ n m, n < m → greedyFun a P N L n ≠ greedyFun a P N L m := by
    intro n m hnm heq
    by_cases hn : GreedyCond a P N L n <;> by_cases hm : GreedyCond a P N L m
    · rw [greedyFun_of_cond a P N L hn, greedyFun_of_cond a P N L hm] at heq
      have := hP heq
      have h1 : (greedyState a P N L (n + 1)).1 ≤ (greedyState a P N L m).1 :=
        greedyState_fst_mono a P N L (show n + 1 ≤ m by omega)
      rw [greedyState_succ_of_cond a P N L hn] at h1
      simp only at h1
      omega
    · rw [greedyFun_of_cond a P N L hn, greedyFun_of_not a P N L hm] at heq
      exact hdisj _ _ heq
    · rw [greedyFun_of_not a P N L hn, greedyFun_of_cond a P N L hm] at heq
      exact hdisj _ _ heq.symm
    · rw [greedyFun_of_not a P N L hn, greedyFun_of_not a P N L hm] at heq
      have := hN heq
      have h1 : (greedyState a P N L (n + 1)).2 ≤ (greedyState a P N L m).2 :=
        greedyState_snd_mono a P N L (show n + 1 ≤ m by omega)
      rw [greedyState_succ_of_not a P N L hn] at h1
      simp only at h1
      omega
  intro n m h
  by_contra hne
  rcases lt_or_gt_of_ne hne with h1 | h1
  · exact aux n m h1 h
  · exact aux m n h1 h.symm

/-- The greedy procedure converges to `L`. -/
theorem greedySum_tendsto (hP : Function.Injective P) (hN : Function.Injective N)
    (h0 : Tendsto a atTop (𝓝 0)) (hPnn : ∀ k, 0 ≤ a (P k)) (hNneg : ∀ k, a (N k) < 0)
    (hPtop : Tendsto (fun i => ∑ k ∈ range i, a (P k)) atTop atTop)
    (hNbot : Tendsto (fun j => ∑ k ∈ range j, a (N k)) atTop atBot) :
    Tendsto (fun n => greedySum a P N (greedyState a P N L n).1 (greedyState a P N L n).2)
      atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hPa : Tendsto (fun k => a (P k)) atTop (𝓝 0) := h0.comp hP.nat_tendsto_atTop
  have hNa : Tendsto (fun k => a (N k)) atTop (𝓝 0) := h0.comp hN.nat_tendsto_atTop
  obtain ⟨K1, hK1⟩ := Metric.tendsto_atTop.mp hPa (ε / 2) (by positivity)
  obtain ⟨K2, hK2⟩ := Metric.tendsto_atTop.mp hNa (ε / 2) (by positivity)
  obtain ⟨nA, hnA⟩ := greedyState_fst_unbounded a P N L hNbot (max K1 K2)
  obtain ⟨nB, hnB⟩ := greedyState_snd_unbounded a P N L hPtop (max K1 K2)
  set n0 := max nA nB with hn0
  have hi : ∀ n, n0 ≤ n → K1 ≤ (greedyState a P N L n).1 := fun n hn =>
    le_trans (le_trans (le_max_left _ _) hnA)
      (greedyState_fst_mono a P N L (le_trans (le_max_left _ _) hn))
  have hj : ∀ n, n0 ≤ n → K2 ≤ (greedyState a P N L n).2 := fun n hn =>
    le_trans (le_trans (le_max_right _ _) hnB)
      (greedyState_snd_mono a P N L (le_trans (le_max_right _ _) hn))
  set d : ℕ → ℝ := fun n =>
    greedySum a P N (greedyState a P N L n).1 (greedyState a P N L n).2 - L with hd
  have hstepP : ∀ n, n0 ≤ n → GreedyCond a P N L n → d n ≤ 0 ∧ d (n + 1) = d n + a (P (greedyState a P N L n).1) ∧
      a (P (greedyState a P N L n).1) < ε / 2 := by
    intro n hn hc
    refine ⟨?_, ?_, ?_⟩
    · have : greedySum a P N (greedyState a P N L n).1 (greedyState a P N L n).2 ≤ L := hc
      simp only [hd]; linarith
    · simp only [hd]
      rw [greedyState_succ_of_cond a P N L hc]
      simp [greedySum, Finset.sum_range_succ]
      ring
    · have := hK1 _ (hi n hn)
      rw [Real.dist_eq, sub_zero] at this
      exact (abs_lt.mp this).2
  have hstepN : ∀ n, n0 ≤ n → ¬ GreedyCond a P N L n → 0 < d n ∧ d (n + 1) = d n + a (N (greedyState a P N L n).2) ∧
      -(ε / 2) < a (N (greedyState a P N L n).2) := by
    intro n hn hc
    refine ⟨?_, ?_, ?_⟩
    · have : ¬ greedySum a P N (greedyState a P N L n).1 (greedyState a P N L n).2 ≤ L := hc
      simp only [hd]; linarith [not_le.mp this]
    · simp only [hd]
      rw [greedyState_succ_of_not a P N L hc]
      simp [greedySum, Finset.sum_range_succ]
      ring
    · have := hK2 _ (hj n hn)
      rw [Real.dist_eq, sub_zero] at this
      exact (abs_lt.mp this).1
  -- find a time after which `d` is in `(-ε/2, ε/2]`
  obtain ⟨n1, hn1, hc1⟩ := greedyCond_not_infinitely_often a P N L hPtop n0
  have hex : ∃ n, n1 ≤ n ∧ GreedyCond a P N L n := greedyCond_infinitely_often a P N L hNbot n1
  classical
  set m := Nat.find hex with hm
  have hm1 : n1 ≤ m ∧ GreedyCond a P N L m := Nat.find_spec hex
  have hmn : m ≠ n1 := fun h => hc1 (h ▸ hm1.2)
  obtain ⟨p, hp⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by
    intro h; apply hmn; omega)
  have hp1 : n1 ≤ p := by omega
  have hpn : ¬ GreedyCond a P N L p := fun hc => Nat.find_min hex (show p < m by omega) ⟨hp1, hc⟩
  have hinv0 : -(ε / 2) < d m ∧ d m ≤ 0 := by
    have h1 := hstepN p (by omega) hpn
    have h2 := hstepP m (by omega) hm1.2
    have e : d m = d p + a (N (greedyState a P N L p).2) := by rw [hp]; exact h1.2.1
    refine ⟨?_, h2.1⟩
    linarith [h1.1, h1.2.2]
  have hinv : ∀ k, -(ε / 2) < d (m + k) ∧ d (m + k) ≤ ε / 2 := by
    intro k
    induction k with
    | zero => simp only [add_zero]; exact ⟨hinv0.1, by linarith [hinv0.2]⟩
    | succ k ih =>
      by_cases hc : GreedyCond a P N L (m + k)
      · obtain ⟨h1, h2, h3⟩ := hstepP (m + k) (by omega) hc
        rw [← add_assoc, h2]
        constructor <;> linarith [hPnn (greedyState a P N L (m + k)).1, ih.1]
      · obtain ⟨h1, h2, h3⟩ := hstepN (m + k) (by omega) hc
        rw [← add_assoc, h2]
        constructor <;> linarith [hNneg (greedyState a P N L (m + k)).2, ih.2]
  refine ⟨m, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Real.dist_eq]
  have := hinv k
  have e : greedySum a P N (greedyState a P N L (m + k)).1 (greedyState a P N L (m + k)).2 - L = d (m + k) := rfl
  rw [e, abs_lt]
  constructor <;> linarith [this.1, this.2]

end Greedy

/-! ## Positive and negative parts -/

/-- Positive part of a term, `max (a n) 0`. -/
noncomputable def posPart (a : ℕ → ℝ) (n : ℕ) : ℝ := max (a n) 0

/-- Negative part of a term, `max (-a n) 0`. -/
noncomputable def negPart (a : ℕ → ℝ) (n : ℕ) : ℝ := max (-a n) 0

theorem posPart_sub_negPart (a : ℕ → ℝ) (n : ℕ) : posPart a n - negPart a n = a n := by
  unfold posPart negPart
  rcases le_total (a n) 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring

theorem posPart_nonneg (a : ℕ → ℝ) (n : ℕ) : 0 ≤ posPart a n := le_max_right _ _

theorem negPart_nonneg (a : ℕ → ℝ) (n : ℕ) : 0 ≤ negPart a n := le_max_right _ _

/-- OpenStax Calculus 2:§5.5 (CA-357), key lemma of the Riemann rearrangement theorem. If the partial sums of
`∑ a n` converge but `∑ |a n|` diverges (conditional convergence), then both the positive part series
`∑ max (a n) 0` and the negative part series `∑ max (-a n) 0` diverge to `+∞`. -/
@[kb "openstaxcalculus2016" "2:§5.5 text after Example 5.21, p. 450"]
theorem conditionally_convergent_parts_diverge {a : ℕ → ℝ} {S : ℝ}
    (hS : Tendsto (fun n => ∑ i ∈ range n, a i) atTop (𝓝 S)) (habs : ¬ Summable a) :
    Tendsto (fun n => ∑ i ∈ range n, posPart a i) atTop atTop ∧
    Tendsto (fun n => ∑ i ∈ range n, negPart a i) atTop atTop := by
  have key : ∀ (a p q : ℕ → ℝ) (S : ℝ), (∀ n, 0 ≤ p n) → (∀ n, 0 ≤ q n) → (∀ n, p n - q n = a n) →
      Tendsto (fun n => ∑ i ∈ range n, a i) atTop (𝓝 S) → ¬ Summable a →
      Tendsto (fun n => ∑ i ∈ range n, p i) atTop atTop := by
    intro a p q S hp hq hpq hS habs
    rw [← not_summable_iff_tendsto_nat_atTop_of_nonneg hp]
    intro hs
    have h1 : Tendsto (fun n => ∑ i ∈ range n, q i) atTop (𝓝 ((∑' i, p i) - S)) := by
      refine (hs.tendsto_sum_tsum_nat.sub hS).congr fun n => ?_
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by have := hpq i; linarith
    have hqs : Summable q := ((hasSum_iff_tendsto_nat_of_nonneg hq _).mpr h1).summable
    apply habs
    have : a = fun n => p n - q n := funext fun n => (hpq n).symm
    rw [this]
    exact hs.sub hqs
  refine ⟨key a (posPart a) (negPart a) S (posPart_nonneg a) (negPart_nonneg a)
      (posPart_sub_negPart a) hS habs, ?_⟩
  refine key (fun n => - a n) (negPart a) (posPart a) (-S) (negPart_nonneg a) (posPart_nonneg a)
      (fun n => by rw [← posPart_sub_negPart a n]; ring) ?_ ?_
  · simpa [Finset.sum_neg_distrib] using hS.neg
  · rwa [summable_neg_iff]

/-! ## From a conditionally convergent series to the greedy data -/

section Enum

open Classical in
theorem sum_range_eq_sum_nth (p : ℕ → Prop) (f : ℕ → ℝ)
    (hf : ∀ n, ¬ p n → f n = 0) (n : ℕ) :
    ∑ i ∈ range n, f i = ∑ k ∈ range (Nat.count p n), f (Nat.nth p k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Nat.count_succ]
    by_cases h : p n
    · simp only [h, ↓reduceIte]
      rw [Finset.sum_range_succ, Nat.nth_count h]
    · simp only [h, ↓reduceIte]
      rw [hf n h]; simp

/-- A nonnegative-term sequence whose partial sums tend to `∞` enumerated along a predicate. -/
theorem tendsto_sum_nth_atTop (p : ℕ → Prop) (f : ℕ → ℝ)
    (hf0 : ∀ n, 0 ≤ f n) (hf : ∀ n, ¬ p n → f n = 0)
    (htop : Tendsto (fun n => ∑ i ∈ range n, f i) atTop atTop) :
    Tendsto (fun j => ∑ k ∈ range j, f (Nat.nth p k)) atTop atTop := by
  classical
  have hmono : Monotone (fun j => ∑ k ∈ range j, f (Nat.nth p k)) :=
    monotone_nat_of_le_succ fun j => by
      rw [Finset.sum_range_succ]; linarith [hf0 (Nat.nth p j)]
  refine tendsto_atTop_atTop_of_monotone hmono fun M => ?_
  obtain ⟨n, hn⟩ := (htop.eventually (eventually_ge_atTop M)).exists
  exact ⟨Nat.count p n, by rw [← sum_range_eq_sum_nth p f hf n]; exact hn⟩

/-- If `f ≥ 0` vanishes off `p` and has partial sums tending to `∞`, then `p` holds infinitely often. -/
theorem infinite_of_tendsto_sum (p : ℕ → Prop) (f : ℕ → ℝ) (hf : ∀ n, ¬ p n → f n = 0)
    (htop : Tendsto (fun n => ∑ i ∈ range n, f i) atTop atTop) : (Set.ofPred p).Infinite := by
  intro hfin
  obtain ⟨M, hM⟩ := hfin.bddAbove
  have h1 : ∀ k, ∑ i ∈ range (M + 1 + k), f i = ∑ i ∈ range (M + 1), f i := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [← add_assoc, Finset.sum_range_succ, ih, hf, add_zero]
      intro hp
      have := hM hp
      omega
  obtain ⟨N0, hN0⟩ := (htop.eventually (eventually_gt_atTop (∑ i ∈ range (M + 1), f i))).exists_forall_of_atTop
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (show M + 1 ≤ max N0 (M + 1) from le_max_right _ _)
  have := hN0 (max N0 (M + 1)) (le_max_left _ _)
  rw [hk, h1] at this
  exact lt_irrefl _ this

/-- OpenStax Calculus 2:§5.5 (CA-357), Riemann rearrangement theorem. If `∑ a n` converges (its partial sums
tend to some `S`) but not absolutely (`∑ |a n|` diverges), then for every real `L` there is a bijection `σ` of
the natural numbers such that the partial sums of the rearranged series `∑ a (σ n)` tend to `L`. -/
@[kb "openstaxcalculus2016" "2:§5.5 text after Example 5.21, p. 450"]
theorem riemann_rearrangement {a : ℕ → ℝ} {S : ℝ}
    (hS : Tendsto (fun n => ∑ i ∈ range n, a i) atTop (𝓝 S))
    (habs : ¬ Summable (fun n => |a n|)) (L : ℝ) :
    ∃ σ : ℕ ≃ ℕ, Tendsto (fun n => ∑ i ∈ range n, a (σ i)) atTop (𝓝 L) := by
  classical
  have habs' : ¬ Summable a := fun h => habs h.abs
  obtain ⟨hpos, hneg⟩ := conditionally_convergent_parts_diverge hS habs'
  set p : ℕ → Prop := fun n => 0 ≤ a n with hp
  set q : ℕ → Prop := fun n => a n < 0 with hq
  have hpinf : (Set.ofPred p).Infinite := infinite_of_tendsto_sum p (posPart a)
    (fun n hn => by
      have : a n < 0 := not_le.mp hn
      simp [posPart, this.le]) hpos
  have hqinf : (Set.ofPred q).Infinite := infinite_of_tendsto_sum q (negPart a)
    (fun n hn => by
      have : 0 ≤ a n := not_lt.mp hn
      simp [negPart, this]) hneg
  have hPmem : ∀ k, 0 ≤ a (Nat.nth p k) := fun k => Nat.nth_mem_of_infinite hpinf k
  have hNmem : ∀ k, a (Nat.nth q k) < 0 := fun k => Nat.nth_mem_of_infinite hqinf k
  have hPtop : Tendsto (fun i => ∑ k ∈ range i, a (Nat.nth p k)) atTop atTop := by
    refine (tendsto_sum_nth_atTop p (posPart a) (posPart_nonneg a)
      (fun n hn => by
        have : a n < 0 := not_le.mp hn
        simp [posPart, this.le]) hpos).congr fun i => ?_
    exact Finset.sum_congr rfl fun k _ => by simp [posPart, hPmem k]
  have hNbot : Tendsto (fun j => ∑ k ∈ range j, a (Nat.nth q k)) atTop atBot := by
    have := tendsto_neg_atTop_atBot.comp (tendsto_sum_nth_atTop q (negPart a) (negPart_nonneg a)
      (fun n hn => by
        have : 0 ≤ a n := not_lt.mp hn
        simp [negPart, this]) hneg)
    refine this.congr fun j => ?_
    simp only [Function.comp, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => by simp [negPart, (hNmem k).le]
  have h0 : Tendsto a atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => ∑ i ∈ range (n + 1), a i) atTop (𝓝 S) :=
      hS.comp (tendsto_add_atTop_nat 1)
    have h2 := h1.sub hS
    rw [sub_self] at h2
    refine h2.congr (fun n => ?_)
    rw [Finset.sum_range_succ]
    ring
  have hPinj : Function.Injective (Nat.nth p) := Nat.nth_injective hpinf
  have hNinj : Function.Injective (Nat.nth q) := Nat.nth_injective hqinf
  have hdisj : ∀ k l, Nat.nth p k ≠ Nat.nth q l := fun k l h => by
    have h1 := hPmem k
    have h2 := hNmem l
    rw [h] at h1
    linarith
  have hinj := greedyFun_injective a (Nat.nth p) (Nat.nth q) L hPinj hNinj hdisj
  have hsurj : Function.Surjective (greedyFun a (Nat.nth p) (Nat.nth q) L) := by
    intro m
    by_cases hm : p m
    · obtain ⟨n, hn⟩ := exists_greedyFun_eq_P a (Nat.nth p) (Nat.nth q) L hNbot (Nat.count p m)
      exact ⟨n, by rw [hn, Nat.nth_count hm]⟩
    · have hm' : q m := by
        have : a m < 0 := not_le.mp hm
        exact this
      obtain ⟨n, hn⟩ := exists_greedyFun_eq_N a (Nat.nth p) (Nat.nth q) L hPtop (Nat.count q m)
      exact ⟨n, by rw [hn, Nat.nth_count hm']⟩
  refine ⟨Equiv.ofBijective _ ⟨hinj, hsurj⟩, ?_⟩
  refine (greedySum_tendsto a (Nat.nth p) (Nat.nth q) L hPinj hNinj h0 hPmem hNmem hPtop hNbot).congr
    fun n => ?_
  rw [← sum_greedyFun]
  rfl

/-- OpenStax Calculus 2:Example 5.22 (CA-357). The alternating harmonic series `∑ (-1)^n/(n+1)` can be
rearranged to have any prescribed sum `L`: there is a bijection `σ` of `ℕ` with partial sums of
`∑ (-1)^(σ n)/(σ n + 1)` tending to `L`. -/
@[kb "openstaxcalculus2016" "2:Example 5.22, p. 451"]
theorem alternating_harmonic_rearrangement (L : ℝ) :
    ∃ σ : ℕ ≃ ℕ, Tendsto (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ (σ i) / ((σ i : ℝ) + 1)) atTop (𝓝 L) := by
  obtain ⟨S, hS⟩ := Antitone.tendsto_alternating_series_of_tendsto_zero
    (f := fun i : ℕ => 1 / ((i : ℝ) + 1))
    (antitone_nat_of_succ_le fun n => by
      simp only [Nat.cast_add, Nat.cast_one]
      gcongr; linarith)
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hS' : Tendsto (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i / ((i : ℝ) + 1)) atTop (𝓝 S) :=
    Tendsto.congr (fun n => Finset.sum_congr rfl fun i _ => by ring) hS
  have habs : ¬ Summable (fun n : ℕ => |(-1 : ℝ) ^ n / ((n : ℝ) + 1)|) := by
    intro h
    have h1 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
      refine h.congr fun n => ?_
      rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_nonneg (by positivity)]
    exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp (by simpa using h1))
  exact riemann_rearrangement hS' habs L

end Enum

end UndergradKB.Calculus
