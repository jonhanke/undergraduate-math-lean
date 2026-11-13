import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Periodic
import UndergradKB.Topology.PeriodThree
import UndergradKB.Topology.SharkovskiiOdd
import UndergradKB.Common.Attr

/-!
# Sharkovskii's theorem for odd periods: the sorted cycle and its covering graph

For a point of prime period `m` of a continuous `f : ℝ → ℝ`, the points of its cycle are listed increasingly
as `q 0 < ... < q (m - 1)`, `π` is the induced permutation of positions, and the gap `g` is the interval
`[q g, q (g + 1)]`.  The covering relation `Cov a b` ("`f` maps the gap `a` over the gap `b`") is the edge
relation of the Markov graph.  We show: a loop gap exists, some other gap covers it, all gaps are reachable
from it, and a primitive closed walk of gaps of length `l ≠ m` gives a point of prime period `l`
(or the cycle itself).
-/

open Function Set

namespace UndergradKB.Topology

/-- The cycle of a point of prime period `m`, sorted increasingly: `q i` is the `i`-th point (`i < m`) and
`π i` the position of its image. -/
structure SortedOrbit (f : ℝ → ℝ) (m : ℕ) where
  q : ℕ → ℝ
  π : ℕ → ℕ
  q_lt : ∀ i j, i < j → j < m → q i < q j
  π_lt : ∀ i, i < m → π i < m
  f_q : ∀ i, i < m → f (q i) = q (π i)
  per : ∀ i, i < m → minimalPeriod f (q i) = m
  cyc : ∀ i j, i < m → j < m → ∃ k, π^[k] i = j

theorem exists_sortedOrbit {f : ℝ → ℝ} {x : ℝ} {m : ℕ} (hx : minimalPeriod f x = m) (hm : 0 < m) :
    Nonempty (SortedOrbit f m) := by
  classical
  have hxp : x ∈ periodicPts f := by rw [← minimalPeriod_pos_iff_mem_periodicPts]; omega
  have hinj : ∀ i j, i < m → j < m → f^[i] x = f^[j] x → i = j := by
    intro i j hi hj h
    have := iterate_injOn_Iio_minimalPeriod (f := f) (x := x)
    rw [hx] at this
    exact this (show i ∈ Iio m from hi) (show j ∈ Iio m from hj) h
  set P : Finset ℝ := (Finset.range m).image (fun i => f^[i] x) with hP
  have hcard : P.card = m := by
    rw [hP, Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj h
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    exact hinj i j hi hj h
  have hmod : ∀ n, f^[n % m] x = f^[n] x := by
    intro n
    have := iterate_mod_minimalPeriod_eq (f := f) (x := x) (n := n)
    rwa [hx] at this
  have hPmem : ∀ n, f^[n] x ∈ P := by
    intro n
    rw [← hmod n, hP]
    exact Finset.mem_image.mpr ⟨n % m, Finset.mem_range.mpr (Nat.mod_lt _ hm), rfl⟩
  have hPex : ∀ y ∈ P, ∃ a, a < m ∧ f^[a] x = y := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨a, Finset.mem_range.mp ha, rfl⟩
  let e := P.orderEmbOfFin hcard
  let q : ℕ → ℝ := fun i => if h : i < m then e ⟨i, h⟩ else 0
  have hq : ∀ i (h : i < m), q i = e ⟨i, h⟩ := fun i h => by simp [q, h]
  have hqP : ∀ i, i < m → q i ∈ P := by
    intro i h
    rw [hq i h]
    exact Finset.orderEmbOfFin_mem P hcard ⟨i, h⟩
  have hPq : ∀ p ∈ P, ∃ i, i < m ∧ q i = p := by
    intro p hp
    have : p ∈ Set.range e := by
      rw [Finset.range_orderEmbOfFin]
      exact hp
    obtain ⟨i, hi⟩ := this
    exact ⟨i.1, i.2, by rw [hq i.1 i.2]; exact hi⟩
  have hqlt : ∀ i j, i < j → j < m → q i < q j := by
    intro i j hij hj
    rw [hq i (by omega), hq j hj]
    exact e.strictMono (Fin.mk_lt_mk.mpr hij)
  have hqinj : ∀ i j, i < m → j < m → q i = q j → i = j := by
    intro i j hi hj h
    rcases lt_trichotomy i j with h' | h' | h'
    · exact absurd h (hqlt i j h' hj).ne
    · exact h'
    · exact absurd h.symm (hqlt j i h' hi).ne
  have hclosed : ∀ i, i < m → ∃ j, j < m ∧ q j = f (q i) := by
    intro i hi
    obtain ⟨a, -, ha⟩ := hPex _ (hqP i hi)
    obtain ⟨j, hj, hjq⟩ := hPq _ (hPmem (a + 1))
    refine ⟨j, hj, ?_⟩
    rw [hjq, ← ha, iterate_succ_apply']
  let π : ℕ → ℕ := fun i => if h : ∃ j, j < m ∧ q j = f (q i) then Classical.choose h else 0
  have hπ : ∀ i, i < m → π i < m ∧ q (π i) = f (q i) := by
    intro i hi
    have h := hclosed i hi
    have e : π i = Classical.choose h := by simp [π, h]
    rw [e]
    exact Classical.choose_spec h
  have hiter : ∀ k i, i < m → π^[k] i < m ∧ f^[k] (q i) = q (π^[k] i) := by
    intro k
    induction k with
    | zero => intro i hi; exact ⟨hi, rfl⟩
    | succ k ih =>
      intro i hi
      obtain ⟨h1, h2⟩ := ih i hi
      obtain ⟨h3, h4⟩ := hπ _ h1
      refine ⟨by rw [iterate_succ_apply']; exact h3, ?_⟩
      rw [iterate_succ_apply', iterate_succ_apply', h2, h4]
  refine ⟨⟨q, π, hqlt, fun i hi => (hπ i hi).1, fun i hi => ((hπ i hi).2).symm, ?_, ?_⟩⟩
  · intro i hi
    obtain ⟨a, -, ha⟩ := hPex _ (hqP i hi)
    rw [← ha, minimalPeriod_apply_iterate hxp a, hx]
  · intro i j hi hj
    obtain ⟨a, ha, hai⟩ := hPex _ (hqP i hi)
    obtain ⟨b, hb, hbj⟩ := hPex _ (hqP j hj)
    refine ⟨b + m - a, ?_⟩
    obtain ⟨h1, h2⟩ := hiter (b + m - a) i hi
    have hfm : f^[m] x = x := by
      have := isPeriodicPt_minimalPeriod f x
      rw [hx] at this
      exact this
    have : f^[b + m - a] (q i) = q j := by
      rw [← hai, ← hbj, ← iterate_add_apply, show b + m - a + a = b + m by omega,
        iterate_add_apply, hfm]
    rw [this] at h2
    exact hqinj _ _ h1 hj h2.symm

/-- Chain lemma: if `J (i+1) ⊆ f (J i)` for compact intervals `J i = [l i, r i]`, there is a subinterval `K` of
`J 0` with `f^i (K) ⊆ J i` for `i ≤ n` and `f^n (K) = J n`. -/
private lemma chain_aux {f : ℝ → ℝ} (hf : Continuous f) (n : ℕ) :
    ∀ (l r : ℕ → ℝ), (∀ i, l i ≤ r i) →
      (∀ i, Icc (l (i + 1)) (r (i + 1)) ⊆ f '' Icc (l i) (r i)) →
      ∃ s t, l 0 ≤ s ∧ s ≤ t ∧ t ≤ r 0 ∧ (∀ i ≤ n, f^[i] '' Icc s t ⊆ Icc (l i) (r i)) ∧
        f^[n] '' Icc s t = Icc (l n) (r n) := by
  induction n with
  | zero =>
    intro l r hlr _
    refine ⟨l 0, r 0, le_rfl, hlr 0, le_rfl, ?_, by simp⟩
    intro i hi
    obtain rfl : i = 0 := by omega
    simp
  | succ n ih =>
    intro l r hlr hcov
    obtain ⟨s', t', h1, h2, h3, h4, h5⟩ := ih (fun i => l (i + 1)) (fun i => r (i + 1))
      (fun i => hlr _) (fun i => hcov (i + 1))
    obtain ⟨s, t, g1, g2, g3, g4⟩ := exists_subinterval_image_eq hf h2
      ((Icc_subset_Icc h1 h3).trans (hcov 0))
    refine ⟨s, t, g1, g2, g3, ?_, ?_⟩
    · intro i hi
      cases i with
      | zero =>
        rw [iterate_zero, Set.image_id]
        exact Icc_subset_Icc g1 g3
      | succ j =>
        rw [iterate_succ, Set.image_comp, g4]
        exact h4 j (by omega)
    · rw [iterate_succ, Set.image_comp, g4]
      exact h5

/-- A periodic point following an itinerary of intervals. -/
private lemma itinerary_aux {f : ℝ → ℝ} (hf : Continuous f) {n : ℕ} (l r : ℕ → ℝ)
    (hlr : ∀ i, l i ≤ r i) (hcov : ∀ i, Icc (l (i + 1)) (r (i + 1)) ⊆ f '' Icc (l i) (r i))
    (hn : Icc (l 0) (r 0) ⊆ Icc (l n) (r n)) :
    ∃ x, f^[n] x = x ∧ ∀ i ≤ n, f^[i] x ∈ Icc (l i) (r i) := by
  obtain ⟨s, t, h1, h2, h3, h4, h5⟩ := chain_aux hf n l r hlr hcov
  have hsub : Icc s t ⊆ f^[n] '' Icc s t := by
    rw [h5]; exact (Icc_subset_Icc h1 h3).trans hn
  obtain ⟨x, hx, hfx⟩ := exists_fixedPt_of_subset_image (hf.iterate n) h2 hsub
  exact ⟨x, hfx, fun i hi => h4 i hi ⟨x, hx, rfl⟩⟩

namespace SortedOrbit

variable {f : ℝ → ℝ} {m : ℕ} (S : SortedOrbit f m)

theorem q_le {i j : ℕ} (h : i ≤ j) (hj : j < m) : S.q i ≤ S.q j := by
  rcases h.eq_or_lt with rfl | h
  · exact le_rfl
  · exact (S.q_lt i j h hj).le

theorem q_inj {i j : ℕ} (hi : i < m) (hj : j < m) (h : S.q i = S.q j) : i = j := by
  rcases lt_trichotomy i j with h' | h' | h'
  · exact absurd h (S.q_lt i j h' hj).ne
  · exact h'
  · exact absurd h.symm (S.q_lt j i h' hi).ne

theorem q_lt_iff {i j : ℕ} (hi : i < m) (hj : j < m) : S.q i < S.q j ↔ i < j := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    exact absurd h (not_lt.mpr (S.q_le hc hi))
  · intro h
    exact S.q_lt i j h hj

theorem iter {k i : ℕ} (hi : i < m) : S.π^[k] i < m ∧ f^[k] (S.q i) = S.q (S.π^[k] i) := by
  induction k with
  | zero => exact ⟨hi, rfl⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨by rw [iterate_succ_apply']; exact S.π_lt _ h1, ?_⟩
    rw [iterate_succ_apply', iterate_succ_apply', h2, S.f_q _ h1]

theorem pi_iter_m {i : ℕ} (hi : i < m) : S.π^[m] i = i := by
  obtain ⟨h1, h2⟩ := S.iter (k := m) hi
  have hper : f^[m] (S.q i) = S.q i := by
    have := isPeriodicPt_minimalPeriod f (S.q i)
    rw [S.per i hi] at this
    exact this
  rw [hper] at h2
  exact (S.q_inj hi h1 h2).symm

theorem pi_ne (hm : 2 ≤ m) {i : ℕ} (hi : i < m) : S.π i ≠ i := by
  intro h
  have h1 : f (S.q i) = S.q i := by rw [S.f_q i hi, h]
  have := minimalPeriod_eq_one_iff_isFixedPt.mpr h1
  rw [S.per i hi] at this
  omega

theorem pi_pi_ne (hm : 3 ≤ m) {i : ℕ} (hi : i < m) : S.π (S.π i) ≠ i := by
  intro h
  have h1 : f^[2] (S.q i) = S.q i := by
    show f (f (S.q i)) = S.q i
    rw [S.f_q i hi, S.f_q _ (S.π_lt i hi), h]
  have := (show IsPeriodicPt f 2 (S.q i) from h1).minimalPeriod_dvd
  rw [S.per i hi] at this
  have := Nat.le_of_dvd (by norm_num) this
  omega

/-- The covering relation of gaps: `f` maps the gap `a` over the gap `b`. -/
def Cov (a b : ℕ) : Prop := Icc (S.q b) (S.q (b + 1)) ⊆ f '' Icc (S.q a) (S.q (a + 1))

/-- If the images of the endpoints of the gap `a` enclose the gap `g`, then `a` covers `g`. -/
theorem cov_of_between (hf : Continuous f) {a g : ℕ} (ha : a + 1 < m) (hg : g + 1 < m)
    (h1 : min (S.π a) (S.π (a + 1)) ≤ g) (h2 : g < max (S.π a) (S.π (a + 1))) : S.Cov a g := by
  have hle : S.q a ≤ S.q (a + 1) := S.q_le (by omega) ha
  have hIVT := intermediate_value_uIcc (a := S.q a) (b := S.q (a + 1)) hf.continuousOn
  rw [uIcc_of_le hle, S.f_q a (by omega), S.f_q (a + 1) ha] at hIVT
  refine Subset.trans ?_ hIVT
  have hpa := S.π_lt a (by omega)
  have hpb := S.π_lt (a + 1) ha
  rcases le_total (S.π a) (S.π (a + 1)) with h | h
  · rw [min_eq_left h] at h1
    rw [max_eq_right h] at h2
    rw [uIcc_of_le (S.q_le h hpb)]
    exact Icc_subset_Icc (S.q_le h1 (by omega)) (S.q_le (by omega) hpb)
  · rw [min_eq_right h] at h1
    rw [max_eq_left h] at h2
    rw [uIcc_of_ge (S.q_le h hpa)]
    exact Icc_subset_Icc (S.q_le h1 (by omega)) (S.q_le (by omega) hpa)

/-- The edge relation of the Markov graph on gaps (vertices `0, ..., m - 2`). -/
def Edge (a b : ℕ) : Prop := a + 1 < m ∧ b + 1 < m ∧ S.Cov a b

/-- There is a gap that covers itself: the gap just above the last point moved up. -/
theorem exists_loop_gap (hf : Continuous f) (hm : 3 ≤ m) :
    ∃ t, t + 1 < m ∧ t + 1 ≤ S.π t ∧ S.π (t + 1) ≤ t ∧ S.Cov t t := by
  classical
  set t := Nat.findGreatest (fun i => i < S.π i) (m - 1) with ht
  have h0 : (fun i => i < S.π i) 0 := by
    show 0 < S.π 0
    have := S.pi_ne (by omega) (show 0 < m by omega)
    omega
  have hspec : t < S.π t := Nat.findGreatest_spec (P := fun i => i < S.π i) (Nat.zero_le (m - 1)) h0
  have hle : t ≤ m - 1 := Nat.findGreatest_le _
  have hpt := S.π_lt t (by omega)
  have hnext : S.π (t + 1) ≤ t := by
    by_contra hc
    push Not at hc
    have hne := S.pi_ne (by omega) (show t + 1 < m by omega)
    have : t + 1 < S.π (t + 1) := by omega
    exact Nat.findGreatest_is_greatest (P := fun i => i < S.π i) (Nat.lt_succ_self t) (by omega) this
  refine ⟨t, by omega, by omega, hnext, ?_⟩
  exact S.cov_of_between hf (by omega) (by omega) (le_trans (min_le_right _ _) hnext)
    (lt_of_lt_of_le (by omega) (le_max_left _ _))

/-- For an odd cycle, some gap other than the loop gap `t` also covers `t`: otherwise the cycle would
alternate between the two sides of `t`. -/
theorem exists_other_cover (hf : Continuous f) (hm : 3 ≤ m) (hodd : m % 2 = 1) {t : ℕ}
    (ht1 : t + 1 < m) (ht2 : t + 1 ≤ S.π t) (ht3 : S.π (t + 1) ≤ t) :
    ∃ J, J + 1 < m ∧ J ≠ t ∧ S.Cov J t := by
  by_contra hcon
  push Not at hcon
  have hiff : ∀ J, J + 1 < m → J ≠ t → (S.π J ≤ t ↔ S.π (J + 1) ≤ t) := by
    intro J hJ hJt
    by_contra hc
    have hcov : S.Cov J t := by
      apply S.cov_of_between hf hJ ht1
      · by_cases h : S.π J ≤ t
        · exact le_trans (min_le_left _ _) h
        · have : S.π (J + 1) ≤ t := by tauto
          exact le_trans (min_le_right _ _) this
      · by_cases h : S.π J ≤ t
        · have : ¬ S.π (J + 1) ≤ t := by tauto
          exact lt_of_lt_of_le (by omega) (le_max_right _ _)
        · exact lt_of_lt_of_le (by omega) (le_max_left _ _)
    exact hcon J hJ hJt hcov
  have hlow : ∀ d, d ≤ t → ¬ S.π (t - d) ≤ t := by
    intro d
    induction d with
    | zero => intro _; rw [Nat.sub_zero]; omega
    | succ d ih =>
      intro hd
      have h1 := ih (by omega)
      have h2 := hiff (t - (d + 1)) (by omega) (by omega)
      rw [show t - (d + 1) + 1 = t - d by omega] at h2
      tauto
  have hhigh : ∀ d, t + 1 + d < m → S.π (t + 1 + d) ≤ t := by
    intro d
    induction d with
    | zero => intro _; exact ht3
    | succ d ih =>
      intro hd
      have h1 := ih (by omega)
      have h2 := hiff (t + 1 + d) (by omega) (by omega)
      rw [show t + 1 + (d + 1) = t + 1 + d + 1 by omega]
      tauto
  have hflip : ∀ j, j < m → (S.π j ≤ t ↔ ¬ j ≤ t) := by
    intro j hj
    by_cases h : j ≤ t
    · have := hlow (t - j) (by omega)
      rw [show t - (t - j) = j by omega] at this
      tauto
    · have := hhigh (j - (t + 1)) (by omega)
      rw [show t + 1 + (j - (t + 1)) = j by omega] at this
      tauto
  have hpar : ∀ k j, j < m → (S.π^[k] j ≤ t ↔ ((j ≤ t) ↔ k % 2 = 0)) := by
    intro k
    induction k with
    | zero => intro j hj; simp
    | succ k ih =>
      intro j hj
      rw [iterate_succ_apply']
      have hlt := (S.iter (k := k) hj).1
      have h3 : ((k + 1) % 2 = 0) ↔ ¬ (k % 2 = 0) := by omega
      rw [hflip _ hlt, ih j hj, h3]
      tauto
  have := hpar m 0 (by omega)
  rw [S.pi_iter_m (by omega)] at this
  simp [hodd] at this

/-- All gaps are reachable from a loop gap in the Markov graph (the cycle is a single orbit). -/
theorem reach_all (hf : Continuous f) {t : ℕ} (ht1 : t + 1 < m) (ht2 : t + 1 ≤ S.π t)
    (ht3 : S.π (t + 1) ≤ t) : ∀ g, g + 1 < m → Relation.ReflTransGen S.Edge t g := by
  classical
  have hpt := S.π_lt t (by omega)
  have hpt1 := S.π_lt (t + 1) ht1
  set Rn : ℕ → Prop := fun g => Relation.ReflTransGen S.Edge t g with hRn
  have hhull : ∀ a g, Rn a → a + 1 < m → g + 1 < m → min (S.π a) (S.π (a + 1)) ≤ g →
      g < max (S.π a) (S.π (a + 1)) → Rn g := by
    intro a g hRa ha hg h1 h2
    exact Relation.ReflTransGen.tail hRa ⟨ha, hg, S.cov_of_between hf ha hg h1 h2⟩
  have hRt : Rn t := Relation.ReflTransGen.refl
  have hexlo : ∃ p, p ≤ t ∧ ∀ g, p ≤ g → g < t → Rn g := ⟨t, le_rfl, fun g h1 h2 => by omega⟩
  set lo := Nat.find hexlo with hlo
  obtain ⟨hlo1, hlo2⟩ := Nat.find_spec hexlo
  have hlomin : ∀ p, p ≤ t → (∀ g, p ≤ g → g < t → Rn g) → lo ≤ p :=
    fun p h1 h2 => Nat.find_min' hexlo ⟨h1, h2⟩
  have hlomax : 0 < lo → ¬ Rn (lo - 1) := by
    intro h0 hR
    have := hlomin (lo - 1) (by omega) (fun g h1 h2 => by
      by_cases hg : g = lo - 1
      · rw [hg]; exact hR
      · exact hlo2 g (by omega) h2)
    omega
  set Q : ℕ → Prop := fun p => ∀ g, t ≤ g → g < p → Rn g with hQ
  set hi := Nat.findGreatest Q (m - 1) with hhi
  have hQt : Q (t + 1) := fun g h1 h2 => by
    have : g = t := by omega
    exact this ▸ hRt
  have hhi1 : t + 1 ≤ hi := Nat.le_findGreatest (by omega) hQt
  have hhiQ : Q hi := Nat.findGreatest_spec (P := Q) (m := t + 1) (by omega) hQt
  have hhile : hi ≤ m - 1 := Nat.findGreatest_le _
  have hhimax : hi + 1 < m → ¬ Rn hi := by
    intro hlt hR
    have : Q (hi + 1) := fun g h1 h2 => by
      by_cases hg : g = hi
      · rw [hg]; exact hR
      · exact hhiQ g h1 (by omega)
    exact Nat.findGreatest_is_greatest (P := Q) (Nat.lt_succ_self hi) (by omega) this
  have hhimin : ∀ p, p ≤ m - 1 → Q p → p ≤ hi := fun p h1 h2 => Nat.le_findGreatest h1 h2
  have hrun : ∀ g, lo ≤ g → g < hi → Rn g := by
    intro g h1 h2
    by_cases hg : g < t
    · exact hlo2 g h1 hg
    · exact hhiQ g (by omega) h2
  have hB : ∀ a, lo ≤ a → a < hi →
      ((lo ≤ S.π a ∧ S.π a ≤ hi) ↔ (lo ≤ S.π (a + 1) ∧ S.π (a + 1) ≤ hi)) := by
    intro a ha1 ha2
    have hRa := hrun a ha1 ha2
    have hpa := S.π_lt a (by omega)
    have hpb := S.π_lt (a + 1) (by omega)
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · by_contra hc
        push Not at hc
        exact hlomax (by omega) (hhull a (lo - 1) hRa (by omega) (by omega) (by omega) (by omega))
      · by_contra hc
        push Not at hc
        exact hhimax (by omega) (hhull a hi hRa (by omega) (by omega) (by omega) (by omega))
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · by_contra hc
        push Not at hc
        exact hlomax (by omega) (hhull a (lo - 1) hRa (by omega) (by omega) (by omega) (by omega))
      · by_contra hc
        push Not at hc
        exact hhimax (by omega) (hhull a hi hRa (by omega) (by omega) (by omega) (by omega))
  have hbase1 : lo ≤ S.π (t + 1) := by
    apply hlomin _ ht3
    intro g h1 h2
    exact hhull t g hRt ht1 (by omega) (by omega) (by omega)
  have hbase2 : S.π t ≤ hi := by
    apply hhimin _ (by omega)
    intro g h1 h2
    exact hhull t g hRt ht1 (by omega) (by omega) (by omega)
  have hup : ∀ d, t + d ≤ hi → lo ≤ S.π (t + d) ∧ S.π (t + d) ≤ hi := by
    intro d
    induction d with
    | zero => intro _; simp only [Nat.add_zero]; exact ⟨by omega, hbase2⟩
    | succ d ih =>
      intro hd
      have := (hB (t + d) (by omega) (by omega)).mp (ih (by omega))
      rw [show t + (d + 1) = t + d + 1 by omega]
      exact this
  have hdown : ∀ d, d ≤ t - lo → lo ≤ S.π (t - d) ∧ S.π (t - d) ≤ hi := by
    intro d
    induction d with
    | zero => intro _; simp only [Nat.sub_zero]; exact ⟨by omega, hbase2⟩
    | succ d ih =>
      intro hd
      have := (hB (t - (d + 1)) (by omega) (by omega)).mpr
        (by rw [show t - (d + 1) + 1 = t - d by omega]; exact ih (by omega))
      exact this
  have hY : ∀ p, lo ≤ p → p ≤ hi → lo ≤ S.π p ∧ S.π p ≤ hi := by
    intro p h1 h2
    by_cases hp : t ≤ p
    · have := hup (p - t) (by omega)
      rwa [show t + (p - t) = p by omega] at this
    · have := hdown (t - p) (by omega)
      rwa [show t - (t - p) = p by omega] at this
  have hall : ∀ k, lo ≤ S.π^[k] t ∧ S.π^[k] t ≤ hi := by
    intro k
    induction k with
    | zero => simp only [iterate_zero, id_eq]; exact ⟨by omega, by omega⟩
    | succ k ih =>
      rw [iterate_succ_apply']
      exact hY _ ih.1 ih.2
  have hlo0 : lo = 0 := by
    obtain ⟨k, hk⟩ := S.cyc t 0 (by omega) (by omega)
    have := hall k
    rw [hk] at this
    omega
  have hhim : hi = m - 1 := by
    obtain ⟨k, hk⟩ := S.cyc t (m - 1) (by omega) (by omega)
    have := hall k
    rw [hk] at this
    omega
  intro g hg
  by_cases hgt : g < t
  · exact hlo2 g (by omega) hgt
  · exact hhiQ g (by omega) (by omega)

/-- A closed walk of gaps in the Markov graph gives a point of period dividing its length that follows it. -/
theorem exists_periodic_gap_loop (hf : Continuous f) {l : ℕ} {w : ℕ → ℕ} (hl : 0 < l)
    (hper : ∀ i, w (i + l) = w i) (hE : ∀ i, S.Edge (w i) (w (i + 1))) :
    ∃ y, f^[l] y = y ∧ ∀ i, f^[i] y ∈ Icc (S.q (w i)) (S.q (w i + 1)) := by
  have hlr : ∀ i, S.q (w i) ≤ S.q (w i + 1) := fun i => S.q_le (by omega) (hE i).1
  have hn : Icc (S.q (w 0)) (S.q (w 0 + 1)) ⊆ Icc (S.q (w l)) (S.q (w l + 1)) := by
    have := hper 0
    rw [Nat.zero_add] at this
    rw [this]
  obtain ⟨y, hy, hit⟩ := itinerary_aux hf (n := l) (fun i => S.q (w i)) (fun i => S.q (w i + 1)) hlr
    (fun i => (hE i).2.2) hn
  refine ⟨y, hy, fun i => ?_⟩
  have hyp : IsPeriodicPt f l y := hy
  have h1 : f^[i % l] y = f^[i] y := hyp.iterate_mod_apply i
  have hp : Function.Periodic w l := hper
  have h2 : w (i % l) = w i := hp.map_mod_nat i
  have := hit (i % l) (Nat.mod_lt _ hl).le
  rwa [h1, h2] at this

theorem gap_inter {g g' : ℕ} (hg : g + 1 < m) (hg' : g' + 1 < m) (hne : g ≠ g') {z : ℝ}
    (h1 : z ∈ Icc (S.q g) (S.q (g + 1))) (h2 : z ∈ Icc (S.q g') (S.q (g' + 1))) :
    ∃ r, r < m ∧ S.q r = z := by
  rcases lt_or_gt_of_ne hne with h | h
  · refine ⟨g + 1, hg, (le_antisymm h1.2 ?_).symm⟩
    exact le_trans (S.q_le (by omega) (by omega)) h2.1
  · refine ⟨g' + 1, hg', (le_antisymm h2.2 ?_).symm⟩
    exact le_trans (S.q_le (by omega) (by omega)) h1.1

/-- A closed walk of gaps of length `l` which is not a repetition gives a point of prime period exactly `l`,
unless the point is one of the cycle points. -/
theorem mem_cycle_of_not_exact {l : ℕ} {w : ℕ → ℕ} {y : ℝ} (hl : 0 < l)
    (hprim : ∀ p, 0 < p → p < l → ∃ i, w (i + p) ≠ w i) (hwlt : ∀ i, w i + 1 < m)
    (hy : f^[l] y = y) (hit : ∀ i, f^[i] y ∈ Icc (S.q (w i)) (S.q (w i + 1)))
    (hne : minimalPeriod f y ≠ l) : ∃ r, r < m ∧ S.q r = y := by
  have hyp : IsPeriodicPt f l y := hy
  have hpos : 0 < minimalPeriod f y := hyp.minimalPeriod_pos hl
  have hdvd := hyp.minimalPeriod_dvd
  have hlt : minimalPeriod f y < l := lt_of_le_of_ne (Nat.le_of_dvd hl hdvd) hne
  obtain ⟨i, hi⟩ := hprim _ hpos hlt
  have hz1 := hit i
  have hz2 := hit (i + minimalPeriod f y)
  have heq : f^[i + minimalPeriod f y] y = f^[i] y := by
    rw [iterate_add_apply, iterate_minimalPeriod]
  rw [heq] at hz2
  obtain ⟨r, hr, hrz⟩ := S.gap_inter (hwlt i) (hwlt _) hi.symm hz1 hz2
  obtain ⟨hr1, hr2⟩ := S.iter (k := l * (i + 1) - i) hr
  refine ⟨_, hr1, ?_⟩
  rw [← hr2, hrz]
  have : l * (i + 1) - i + i = l * (i + 1) := by
    have : i ≤ l * (i + 1) := by nlinarith
    omega
  rw [← iterate_add_apply, this]
  exact (hyp.mul_const (i + 1)).eq

/-- No primitive closed walk of odd length `l` with `3 ≤ l < m` exists if `f` has no point of odd prime
period `l`. -/
theorem no_prim_loop (hf : Continuous f)
    (hmin : ∀ l, 3 ≤ l → l < m → Odd l → ¬ ∃ y, minimalPeriod f y = l) {l : ℕ} {w : ℕ → ℕ}
    (h3 : 3 ≤ l) (hlm : l < m) (hodd : Odd l) : ¬ IsPrimLoop S.Edge l w := by
  rintro ⟨hl, hper, hE, hprim⟩
  obtain ⟨y, hy, hit⟩ := S.exists_periodic_gap_loop hf hl hper hE
  by_cases hex : minimalPeriod f y = l
  · exact hmin l h3 hlm hodd ⟨y, hex⟩
  · obtain ⟨r, hr, hrq⟩ := S.mem_cycle_of_not_exact hl hprim (fun i => (hE i).1) hy hit hex
    have := (show IsPeriodicPt f l y from hy).minimalPeriod_dvd
    rw [← hrq, S.per r hr] at this
    have := Nat.le_of_dvd hl this
    omega

/-- The Hamiltonian chain of gaps for a minimal odd cycle. -/
theorem exists_chain (hf : Continuous f) (hm : 3 ≤ m) (hodd : m % 2 = 1)
    (hmin : ∀ l, 3 ≤ l → l < m → Odd l → ¬ ∃ y, minimalPeriod f y = l) {t : ℕ}
    (ht1 : t + 1 < m) (ht2 : t + 1 ≤ S.π t) (ht3 : S.π (t + 1) ≤ t) (htl : S.Cov t t) :
    ∃ v : ℕ → ℕ, v 0 = t ∧ (∀ i j, i < m - 1 → j < m - 1 → v i = v j → i = j) ∧
      (∀ i, i < m - 1 → v i < m - 1) ∧ (∀ g, g < m - 1 → ∃ i, i < m - 1 ∧ v i = g) ∧
      (∀ i, i + 1 < m - 1 → S.Cov (v i) (v (i + 1))) ∧ S.Cov (v (m - 2)) (v 0) ∧
      (∀ i j, i < m - 1 → j < m - 1 → S.Cov (v i) (v j) → j ≤ i + 1) ∧
      (∀ i, i < m - 1 → S.Cov (v i) (v 0) → i = 0 ∨ i = m - 2) := by
  obtain ⟨J, hJ1, hJ2, hJ3⟩ := S.exists_other_cover hf hm hodd ht1 ht2 ht3
  have hbd : ∀ a b, S.Edge a b → a < m - 1 ∧ b < m - 1 := fun a b h => by
    have := h.1; have := h.2.1; omega
  obtain ⟨v, hv0, hvinj, hvlt, hvsurj, hvstep, hvcl, hvshort, hvC5⟩ :=
    exists_hamiltonian_chain (R := S.Edge) (N := m - 1) (t := t) ⟨(m - 1) / 2, by omega⟩ hbd
      ⟨ht1, ht1, htl⟩ (fun g hg => S.reach_all hf ht1 ht2 ht3 g (by omega))
      ⟨J, hJ2, hJ1, by omega, hJ3⟩
      (fun l w h3 hl hodd' => S.no_prim_loop hf hmin h3 (by omega) hodd')
  have hE : ∀ i j, i < m - 1 → j < m - 1 → S.Cov (v i) (v j) → S.Edge (v i) (v j) := by
    intro i j hi hj hc
    exact ⟨by have := hvlt i hi; omega, by have := hvlt j hj; omega, hc⟩
  refine ⟨v, hv0, hvinj, hvlt, hvsurj, fun i hi => (hvstep i hi).2.2,
    by rw [show m - 2 = m - 1 - 1 by omega]; exact hvcl.2.2,
    fun i j hi hj hc => hvshort i j hi hj (hE i j hi hj hc), fun i hi hc => ?_⟩
  have := hvC5 i hi (hE i 0 hi (by omega) hc)
  omega

end SortedOrbit

end UndergradKB.Topology
