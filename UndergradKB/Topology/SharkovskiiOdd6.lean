import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import UndergradKB.Topology.SharkovskiiOdd5
import UndergradKB.Common.Attr

/-!
# The converse of Sharkovskii's theorem: the Štefan map

Morris, *Topology Without Tears* (2024), Appendix 3, Theorem A3.6.6 (`morris2024`).  For `m = 2 n + 1` the
Štefan map `stefanMap n` is the continuous piecewise linear self-map of `ℝ` with values in `[0, 2 n]` which is
affine on each gap `[g, g+1]` and sends the node `k` to `stefanPerm n k`; the nodes `0, ..., 2 n` form one cycle
of prime period `m`.  Here: the definition, the cycle, and the fact that there is no periodic point of odd prime
period `l` with `3 ≤ l < m` (a periodic orbit avoiding the nodes follows a closed walk of the Markov graph of
`SharkovskiiOdd5`).
-/

open Function Set

namespace UndergradKB.Topology

/-- The core of the Štefan map on `[0, 2 n]`: four affine pieces on `[0, 1]`, `[1, n]`, `[n, n+1]`, `[n+1, 2n]`. -/
noncomputable def stefanCore (n : ℕ) (y : ℝ) : ℝ :=
  if y ≤ 1 then n + n * y else if y ≤ n then 2 * n + 1 - y else if y ≤ n + 1 then 3 * n + 1 - 2 * y
  else 2 * n - y

/-- The Štefan map of the odd period `2 n + 1`. -/
noncomputable def stefanMap (n : ℕ) (x : ℝ) : ℝ := stefanCore n (max 0 (min x (2 * n)))

theorem continuous_stefanCore {n : ℕ} (hn : 1 ≤ n) : Continuous (stefanCore n) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (n : ℝ) ≤ n + 1 := by linarith
  unfold stefanCore
  refine Continuous.if_le (f := fun y : ℝ => y) (g := fun _ => (1 : ℝ)) (by fun_prop) ?_
    continuous_id continuous_const ?_
  · refine Continuous.if_le (f := fun y : ℝ => y) (g := fun _ => (n : ℝ)) (by fun_prop) ?_
      continuous_id continuous_const ?_
    · refine Continuous.if_le (f := fun y : ℝ => y) (g := fun _ => (n : ℝ) + 1) (by fun_prop)
        (by fun_prop) continuous_id continuous_const ?_
      intro y hy
      subst hy
      ring
    · intro y hy
      subst hy
      simp only [hn1, ↓reduceIte]
      ring
  · intro y hy
    subst hy
    simp only [hn', ↓reduceIte]
    ring

theorem continuous_stefanMap {n : ℕ} (hn : 1 ≤ n) : Continuous (stefanMap n) := by
  unfold stefanMap
  exact (continuous_stefanCore hn).comp (by fun_prop)

section Pieces

variable {n : ℕ} {y : ℝ}

theorem stefanCore_eq1 (h : y ≤ 1) : stefanCore n y = n + n * y := by
  unfold stefanCore
  simp only [h, ↓reduceIte]

theorem stefanCore_eq2 (h1 : 1 ≤ y) (h2 : y ≤ n) : stefanCore n y = 2 * n + 1 - y := by
  unfold stefanCore
  by_cases a : y ≤ 1
  · have : y = 1 := le_antisymm a h1
    subst this
    simp only [le_refl, ↓reduceIte]
    ring
  · simp only [a, h2, ↓reduceIte]

theorem stefanCore_eq3 (hn : 1 ≤ n) (h1 : (n : ℝ) ≤ y) (h2 : y ≤ n + 1) :
    stefanCore n y = 3 * n + 1 - 2 * y := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold stefanCore
  by_cases a : y ≤ 1
  · have h3 : y = 1 := le_antisymm a (by linarith)
    have h4 : (n : ℝ) = 1 := le_antisymm (by linarith) hn'
    subst h3
    simp only [le_refl, ↓reduceIte, h4]
    ring
  · by_cases b : y ≤ n
    · have : y = n := le_antisymm b h1
      simp only [a, b, ↓reduceIte]
      rw [this]
      ring
    · simp only [a, b, h2, ↓reduceIte]

theorem stefanCore_eq4 (hn : 1 ≤ n) (h1 : (n : ℝ) + 1 ≤ y) : stefanCore n y = 2 * n - y := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold stefanCore
  have a : ¬ y ≤ 1 := by intro h; linarith
  have b : ¬ y ≤ n := by intro h; linarith
  by_cases c : y ≤ n + 1
  · have : y = n + 1 := le_antisymm c h1
    simp only [a, b, c, ↓reduceIte]
    rw [this]
    ring
  · simp only [a, b, c, ↓reduceIte]

theorem stefanMap_eq_core (h0 : 0 ≤ y) (h1 : y ≤ 2 * n) : stefanMap n y = stefanCore n y := by
  unfold stefanMap
  rw [min_eq_left h1, max_eq_right h0]

theorem stefanMap_mem (hn : 1 ≤ n) (x : ℝ) : stefanMap n x ∈ Icc (0 : ℝ) (2 * n) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set y := max 0 (min x (2 * n)) with hy
  have hy0 : 0 ≤ y := le_max_left _ _
  have hy1 : y ≤ 2 * n := max_le (by linarith) (min_le_right _ _)
  show stefanCore n y ∈ _
  rcases le_total y 1 with h | h
  · rw [stefanCore_eq1 h]
    constructor <;> nlinarith
  · rcases le_total y n with h' | h'
    · rw [stefanCore_eq2 h h']
      constructor <;> linarith
    · rcases le_total y (n + 1) with h'' | h''
      · rw [stefanCore_eq3 hn h' h'']
        constructor <;> linarith
      · rw [stefanCore_eq4 hn h'']
        constructor <;> linarith

end Pieces

section Nodes

variable {n : ℕ}

theorem stefanPerm_zero (n : ℕ) : stefanPerm n 0 = n := by simp [stefanPerm]

theorem stefanPerm_mid {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ n) : stefanPerm n k = 2 * n + 1 - k := by
  simp [stefanPerm, show k ≠ 0 by omega, h2]

theorem stefanPerm_hi {k : ℕ} (h1 : n < k) : stefanPerm n k = 2 * n - k := by
  simp [stefanPerm, show k ≠ 0 by omega, show ¬ k ≤ n by omega]

theorem stefanPerm_cast_zero : (stefanPerm n 0 : ℝ) = n := by rw [stefanPerm_zero]

theorem stefanPerm_cast_mid {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ n) : (stefanPerm n k : ℝ) = 2 * n + 1 - k := by
  rw [stefanPerm_mid h1 h2, Nat.cast_sub (by omega)]
  push_cast
  ring

theorem stefanPerm_cast_hi {k : ℕ} (h1 : n < k) (h2 : k ≤ 2 * n) : (stefanPerm n k : ℝ) = 2 * n - k := by
  rw [stefanPerm_hi h1, Nat.cast_sub h2]
  push_cast
  ring

theorem stefanMap_node (hn : 1 ≤ n) {k : ℕ} (hk : k ≤ 2 * n) :
    stefanMap n (k : ℝ) = (stefanPerm n k : ℝ) := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hk1 : (k : ℝ) ≤ 2 * n := by exact_mod_cast hk
  rw [stefanMap_eq_core hk0 hk1]
  by_cases h0 : k = 0
  · subst h0
    rw [stefanCore_eq1 (by norm_num), stefanPerm_cast_zero]
    simp
  · by_cases h1 : k ≤ n
    · rw [stefanCore_eq2 (by exact_mod_cast (show 1 ≤ k by omega)) (by exact_mod_cast h1),
        stefanPerm_cast_mid (by omega) h1]
    · rw [stefanCore_eq4 hn (by exact_mod_cast (show n + 1 ≤ k by omega)), stefanPerm_cast_hi (by omega) hk]

theorem stefanPerm_ne (hn : 1 ≤ n) {g : ℕ} (hg : g + 1 ≤ 2 * n) :
    stefanPerm n g ≠ stefanPerm n (g + 1) := by
  by_cases h0 : g = 0
  · rw [h0, stefanPerm_zero, stefanPerm_mid (n := n) (k := 0 + 1) (by omega) (by omega)]
    omega
  by_cases h1 : g + 1 ≤ n
  · rw [stefanPerm_mid (n := n) (k := g) (by omega) (by omega),
      stefanPerm_mid (n := n) (k := g + 1) (by omega) h1]
    omega
  by_cases h2 : g = n
  · rw [stefanPerm_mid (n := n) (k := g) (by omega) (by omega),
      stefanPerm_hi (n := n) (k := g + 1) (by omega)]
    omega
  · rw [stefanPerm_hi (n := n) (k := g) (by omega), stefanPerm_hi (n := n) (k := g + 1) (by omega)]
    omega

/-- The Štefan map is affine on each gap `[g, g + 1]`, with the node values `stefanPerm`. -/
theorem stefanMap_gap (hn : 1 ≤ n) {g : ℕ} (hg : g + 1 ≤ 2 * n) {t : ℝ} (h1 : (g : ℝ) ≤ t)
    (h2 : t ≤ g + 1) :
    stefanMap n t = (stefanPerm n g : ℝ) + ((stefanPerm n (g + 1) : ℝ) - stefanPerm n g) * (t - g) := by
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  have hg1 : (g : ℝ) + 1 ≤ 2 * n := by exact_mod_cast hg
  rw [stefanMap_eq_core (by linarith) (by linarith)]
  by_cases hA : g = 0
  · have e0 : (stefanPerm n g : ℝ) = n := by rw [hA]; exact stefanPerm_cast_zero
    have e1 : (stefanPerm n (g + 1) : ℝ) = 2 * n + 1 - (g + 1 : ℕ) :=
      stefanPerm_cast_mid (by omega) (by omega)
    have hc : (g : ℝ) = 0 := by rw [hA]; simp
    rw [stefanCore_eq1 (by linarith), e0, e1]
    push_cast
    rw [hc]
    ring
  · by_cases hB : g + 1 ≤ n
    · have e0 : (stefanPerm n g : ℝ) = 2 * n + 1 - g := stefanPerm_cast_mid (by omega) (by omega)
      have e1 : (stefanPerm n (g + 1) : ℝ) = 2 * n + 1 - (g + 1 : ℕ) :=
        stefanPerm_cast_mid (by omega) hB
      have hc : (1 : ℝ) ≤ g := by exact_mod_cast (show 1 ≤ g by omega)
      have hc2 : (g : ℝ) + 1 ≤ n := by exact_mod_cast hB
      rw [stefanCore_eq2 (by linarith) (by linarith), e0, e1]
      push_cast
      ring
    · by_cases hC : g = n
      · have e0 : (stefanPerm n g : ℝ) = 2 * n + 1 - g := stefanPerm_cast_mid (by omega) (by omega)
        have e1 : (stefanPerm n (g + 1) : ℝ) = 2 * n - (g + 1 : ℕ) := stefanPerm_cast_hi (by omega) hg
        have hc : (g : ℝ) = n := by rw [hC]
        rw [stefanCore_eq3 hn (by linarith) (by linarith), e0, e1]
        push_cast
        rw [hc]
        ring
      · have e0 : (stefanPerm n g : ℝ) = 2 * n - g := stefanPerm_cast_hi (by omega) (by omega)
        have e1 : (stefanPerm n (g + 1) : ℝ) = 2 * n - (g + 1 : ℕ) := stefanPerm_cast_hi (by omega) hg
        have hc : (n : ℝ) + 1 ≤ g := by exact_mod_cast (show n + 1 ≤ g by omega)
        rw [stefanCore_eq4 hn (by linarith), e0, e1]
        push_cast
        ring

/-- The orbit of the centre `n` under the Štefan permutation: `n, n+1, n-1, n+2, ..., 0`. -/
def stefanOrbit (n i : ℕ) : ℕ := if i % 2 = 0 then n - i / 2 else n + i / 2 + 1

theorem stefanOrbit_even (n s : ℕ) : stefanOrbit n (2 * s) = n - s := by
  unfold stefanOrbit
  have : (2 * s) % 2 = 0 := by omega
  simp only [this, ↓reduceIte]
  omega

theorem stefanOrbit_odd (n s : ℕ) : stefanOrbit n (2 * s + 1) = n + s + 1 := by
  unfold stefanOrbit
  have : (2 * s + 1) % 2 ≠ 0 := by omega
  simp only [this, ↓reduceIte]
  omega

theorem stefanOrbit_le (n : ℕ) {i : ℕ} (hi : i ≤ 2 * n) : stefanOrbit n i ≤ 2 * n := by
  rcases Nat.even_or_odd' i with ⟨s, hs | hs⟩
  · subst hs; rw [stefanOrbit_even]; omega
  · subst hs; rw [stefanOrbit_odd]; omega

theorem stefanPerm_orbit (hn : 1 ≤ n) {i : ℕ} (hi : i ≤ 2 * n) :
    stefanPerm n (stefanOrbit n i) = stefanOrbit n ((i + 1) % (2 * n + 1)) := by
  rcases Nat.even_or_odd' i with ⟨s, hs | hs⟩
  · subst hs
    rcases Nat.lt_or_ge (2 * s) (2 * n) with h | h
    · rw [Nat.mod_eq_of_lt (by omega), stefanOrbit_even, stefanOrbit_odd]
      by_cases hs0 : s = 0
      · subst hs0
        rw [stefanPerm_mid (n := n) (k := n - 0) (by omega) (by omega)]
        omega
      · rw [stefanPerm_mid (n := n) (k := n - s) (by omega) (by omega)]
        omega
    · have : s = n := by omega
      subst this
      rw [show (2 * s + 1) % (2 * s + 1) = 0 by simp, show (0 : ℕ) = 2 * 0 from rfl, stefanOrbit_even,
        stefanOrbit_even, Nat.sub_self, stefanPerm_zero]
      omega
  · subst hs
    rw [show 2 * s + 1 + 1 = 2 * (s + 1) by ring, Nat.mod_eq_of_lt (by omega), stefanOrbit_even, stefanOrbit_odd,
      stefanPerm_hi (n := n) (k := n + s + 1) (by omega)]
    omega

theorem iterate_stefan_center (hn : 1 ≤ n) : ∀ i, i ≤ 2 * n →
    (stefanMap n)^[i] (n : ℝ) = (stefanOrbit n i : ℝ) := by
  intro i
  induction i with
  | zero =>
    intro _
    simp [stefanOrbit]
  | succ i ih =>
    intro hi
    rw [iterate_succ_apply', ih (by omega), stefanMap_node hn (stefanOrbit_le n (by omega)),
      stefanPerm_orbit hn (by omega), Nat.mod_eq_of_lt (by omega)]

theorem iterate_stefan_period (hn : 1 ≤ n) : (stefanMap n)^[2 * n + 1] (n : ℝ) = n := by
  rw [iterate_succ_apply', iterate_stefan_center hn (2 * n) le_rfl,
    stefanMap_node hn (stefanOrbit_le n le_rfl), stefanPerm_orbit hn le_rfl]
  rw [show (2 * n + 1) % (2 * n + 1) = 0 by simp, show (0 : ℕ) = 2 * 0 from rfl, stefanOrbit_even]
  simp

theorem minimalPeriod_stefan_center (hn : 1 ≤ n) : minimalPeriod (stefanMap n) (n : ℝ) = 2 * n + 1 := by
  have hper : IsPeriodicPt (stefanMap n) (2 * n + 1) (n : ℝ) := iterate_stefan_period hn
  have hpos := hper.minimalPeriod_pos (by omega)
  have hle := Nat.le_of_dvd (by omega) hper.minimalPeriod_dvd
  by_contra hne
  have hlt : minimalPeriod (stefanMap n) (n : ℝ) < 2 * n + 1 := lt_of_le_of_ne hle hne
  have hfix := isPeriodicPt_minimalPeriod (stefanMap n) (n : ℝ)
  have h1 := iterate_stefan_center hn (minimalPeriod (stefanMap n) (n : ℝ)) (by omega)
  have h2 : ((stefanOrbit n (minimalPeriod (stefanMap n) (n : ℝ)) : ℕ) : ℝ) = (n : ℝ) := by
    rw [← h1]
    exact hfix.eq
  have h3 : stefanOrbit n (minimalPeriod (stefanMap n) (n : ℝ)) = n := by exact_mod_cast h2
  rcases Nat.even_or_odd' (minimalPeriod (stefanMap n) (n : ℝ)) with ⟨s, hs | hs⟩
  · rw [hs, stefanOrbit_even] at h3
    omega
  · rw [hs, stefanOrbit_odd] at h3
    omega

theorem minimalPeriod_stefan_node (hn : 1 ≤ n) {k : ℕ} (hk : k ≤ 2 * n) :
    minimalPeriod (stefanMap n) (k : ℝ) = 2 * n + 1 := by
  obtain ⟨i, hi, hik⟩ : ∃ i, i ≤ 2 * n ∧ stefanOrbit n i = k := by
    by_cases h : k ≤ n
    · exact ⟨2 * (n - k), by omega, by rw [stefanOrbit_even]; omega⟩
    · exact ⟨2 * (k - n - 1) + 1, by omega, by rw [stefanOrbit_odd]; omega⟩
  have hxp : (n : ℝ) ∈ periodicPts (stefanMap n) := by
    rw [← minimalPeriod_pos_iff_mem_periodicPts, minimalPeriod_stefan_center hn]
    omega
  rw [← hik, ← iterate_stefan_center hn i hi, minimalPeriod_apply_iterate hxp i,
    minimalPeriod_stefan_center hn]

theorem stefanMap_center (hn : 1 ≤ n) {t : ℝ} (h1 : (n : ℝ) ≤ t) (h2 : t ≤ n + 1) :
    stefanMap n t = 3 * n + 1 - 2 * t := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [stefanMap_eq_core (by linarith) (by linarith), stefanCore_eq3 hn h1 h2]

/-- Morris, Topology Without Tears, Theorem A3.6.6 (TP-449), the key lemma for odd `m = 2 n + 1`: the Štefan
map has no periodic point of odd prime period `l` with `3 ≤ l < m`. -/
@[kb "morris2024" "Theorem A3.6.6, p. 458"]
theorem not_odd_period_stefan (hn : 1 ≤ n) {l : ℕ} (hl : l % 2 = 1) (h3 : 3 ≤ l)
    (hlm : l < 2 * n + 1) : ¬ ∃ y, minimalPeriod (stefanMap n) y = l := by
  rintro ⟨y, hy⟩
  set f := stefanMap n with hf
  have hlpos : 0 < l := by omega
  have hper : IsPeriodicPt f l y := by rw [← hy]; exact isPeriodicPt_minimalPeriod f y
  have hyp : y ∈ periodicPts f := mk_mem_periodicPts hlpos hper
  by_cases hnode : ∃ i k : ℕ, k ≤ 2 * n ∧ f^[i] y = (k : ℝ)
  · obtain ⟨i, k, hk, hik⟩ := hnode
    have h1 : minimalPeriod f (f^[i] y) = l := by rw [minimalPeriod_apply_iterate hyp i, hy]
    rw [hik, minimalPeriod_stefan_node hn hk] at h1
    omega
  push Not at hnode
  have hshift : ∀ i, f^[i + l] y = f^[i] y := by
    intro i
    rw [iterate_add_apply, hper.eq]
  have hrange : ∀ i, f^[i] y ∈ Icc (0 : ℝ) (2 * n) := by
    intro i
    have e2 : f^[i + l] y = f (f^[i + l - 1] y) := by
      rw [← iterate_succ_apply' f (i + l - 1) y, show (i + l - 1).succ = i + l by omega]
    rw [← hshift i, e2]
    exact stefanMap_mem hn _
  set w : ℕ → ℕ := fun i => ⌊f^[i] y⌋₊ with hw
  have hwlo : ∀ i, (w i : ℝ) < f^[i] y := by
    intro i
    have h0 : ((w i : ℕ) : ℝ) ≤ f^[i] y := Nat.floor_le (hrange i).1
    refine lt_of_le_of_ne h0 fun h => ?_
    have : w i ≤ 2 * n := by
      have := (hrange i).2
      exact_mod_cast h0.trans this
    exact hnode i (w i) this h.symm
  have hwhi : ∀ i, f^[i] y < w i + 1 := fun i => Nat.lt_floor_add_one _
  have hwlt : ∀ i, w i < 2 * n := by
    intro i
    have := (hwlo i).trans_le (hrange i).2
    exact_mod_cast this
  have hE : ∀ i, StefanEdge n (w i) (w (i + 1)) := by
    intro i
    have hg : w i + 1 ≤ 2 * n := hwlt i
    have hgap := stefanMap_gap hn hg (hwlo i).le (hwhi i).le
    have hne := stefanPerm_ne hn hg
    have hnei : ((stefanPerm n (w i) : ℕ) : ℝ) ≠ ((stefanPerm n (w i + 1) : ℕ) : ℝ) := by
      exact_mod_cast hne
    have e1 : f (f^[i] y) = f^[i + 1] y := (iterate_succ_apply' f i y).symm
    have hlt1 : 0 < f^[i] y - w i := sub_pos.mpr (hwlo i)
    have hlt2 : f^[i] y - w i < 1 := by linarith [hwhi i]
    have hv : f^[i + 1] y = (stefanPerm n (w i) : ℝ) +
        ((stefanPerm n (w i + 1) : ℝ) - stefanPerm n (w i)) * (f^[i] y - w i) := by
      rw [← e1]; exact hgap
    have hv0 : 0 ≤ f^[i + 1] y := (hrange (i + 1)).1
    unfold StefanEdge
    rcases lt_or_gt_of_ne hnei with hlt | hgt
    · left
      have hd : 0 < (stefanPerm n (w i + 1) : ℝ) - stefanPerm n (w i) := by linarith
      have h1 : (stefanPerm n (w i) : ℝ) < f^[i + 1] y := by rw [hv]; nlinarith
      have h2 : f^[i + 1] y < (stefanPerm n (w i + 1) : ℝ) := by rw [hv]; nlinarith
      exact ⟨Nat.le_floor h1.le, (Nat.floor_lt hv0).mpr h2⟩
    · right
      have hd : (stefanPerm n (w i + 1) : ℝ) - stefanPerm n (w i) < 0 := by linarith
      have h1 : (stefanPerm n (w i + 1) : ℝ) < f^[i + 1] y := by rw [hv]; nlinarith
      have h2 : f^[i + 1] y < (stefanPerm n (w i) : ℝ) := by rw [hv]; nlinarith
      exact ⟨Nat.le_floor h1.le, (Nat.floor_lt hv0).mpr h2⟩
  have hwper : ∀ i, w (i + l) = w i := by
    intro i
    simp only [hw, hshift]
  have hconst := stefan_walk_const hn hl h3 (by omega) w hwlt hE hwper
  have hin : ∀ i, (n : ℝ) < f^[i] y ∧ f^[i] y < n + 1 := by
    intro i
    have h1 := hwlo i
    have h2 := hwhi i
    rw [hconst i] at h1 h2
    exact ⟨h1, h2⟩
  set c : ℝ := n + 1 / 3 with hc
  have hiter : ∀ i, f^[i] y - c = (-2) ^ i * (y - c) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have e : f (f^[i] y) = 3 * n + 1 - 2 * f^[i] y :=
        stefanMap_center hn (hin i).1.le (hin i).2.le
      rw [iterate_succ_apply', e, pow_succ]
      have : f^[i] y = c + (-2) ^ i * (y - c) := by linarith
      rw [this, hc]
      ring
  have hl2 := hiter l
  rw [hper.eq] at hl2
  have hodd : Odd l := Nat.odd_iff.mpr hl
  rw [hodd.neg_pow] at hl2
  have hpos : (0 : ℝ) < 2 ^ l := by positivity
  have hyc : y = c := by nlinarith
  have hfix : f y = y := by
    have := hiter 1
    rw [pow_one, iterate_one, ← hyc] at this
    linarith
  have := minimalPeriod_eq_one_iff_isFixedPt.mpr hfix
  omega

end Nodes

end UndergradKB.Topology
