import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Linarith
import UndergradKB.Common.Attr

/-!
# The converse of Sharkovskii's theorem: the Štefan map, combinatorics of its Markov graph

Morris, *Topology Without Tears* (2024), Appendix 3, Theorem A3.6.6 (`morris2024`).  For `m = 2 n + 1` the
Štefan cycle is `n → n+1 → n-1 → n+2 → ... → 0 → n` on the positions `0, ..., 2 n`.  This file contains the
purely combinatorial part: the permutation `stefanPerm`, the covering graph of the gaps `[g, g+1]` and the fact
that a closed walk of odd length `l` with `3 ≤ l ≤ m - 2` in it stays at the loop gap `n`.
-/

namespace UndergradKB.Topology

/-- The Štefan permutation of the positions `0, ..., 2 n`. -/
def stefanPerm (n k : ℕ) : ℕ := if k = 0 then n else if k ≤ n then 2 * n + 1 - k else 2 * n - k

/-- The edges of the Markov graph of the Štefan map: the image of the gap `g` covers the gap `g'`. -/
def StefanEdge (n g g' : ℕ) : Prop :=
  (stefanPerm n g ≤ g' ∧ g' < stefanPerm n (g + 1)) ∨ (stefanPerm n (g + 1) ≤ g' ∧ g' < stefanPerm n g)

lemma stefanEdge_cases {n g g' : ℕ} (hn : 1 ≤ n) (hg : g < 2 * n) (h : StefanEdge n g g') :
    (g = 0 ∧ n ≤ g' ∧ g' < 2 * n) ∨ (1 ≤ g ∧ g < n ∧ g' = 2 * n - g) ∨
      (g = n ∧ (g' = n - 1 ∨ g' = n)) ∨ (n + 1 ≤ g ∧ g' = 2 * n - g - 1) := by
  have p0 : stefanPerm n 0 = n := by simp [stefanPerm]
  have p1 : ∀ k, 1 ≤ k → k ≤ n → stefanPerm n k = 2 * n + 1 - k := fun k h1 h2 => by
    simp [stefanPerm, show k ≠ 0 by omega, h2]
  have p2 : ∀ k, n < k → stefanPerm n k = 2 * n - k := fun k h1 => by
    simp [stefanPerm, show k ≠ 0 by omega, show ¬ k ≤ n by omega]
  unfold StefanEdge at h
  rcases (show g = 0 ∨ (1 ≤ g ∧ g < n) ∨ g = n ∨ n < g by omega) with h0 | h0 | h0 | h0
  · subst h0
    rw [p0, p1 1 le_rfl hn] at h
    omega
  · rw [p1 g h0.1 h0.2.le, p1 (g + 1) (by omega) (by omega)] at h
    omega
  · subst h0
    rw [p1 g hn le_rfl, p2 (g + 1) (by omega)] at h
    omega
  · rw [p2 g h0, p2 (g + 1) (by omega)] at h
    omega

lemma stefanEdge_side {n g g' : ℕ} (hn : 1 ≤ n) (hg : g < 2 * n) (h : StefanEdge n g g') :
    (g = n ∧ g' = n) ∨ (g < n ↔ ¬ g' < n) := by
  rcases stefanEdge_cases hn hg h with h | h | h | h <;> omega

lemma stefanEdge_lt {n g g' : ℕ} (hn : 1 ≤ n) (hg : g < 2 * n) (h : StefanEdge n g g') : g' < 2 * n := by
  rcases stefanEdge_cases hn hg h with h | h | h | h <;> omega

/-- A closed walk of odd length `l` with `3 ≤ l ≤ 2 n - 1` in the Markov graph of the Štefan map stays at the
loop gap `n`. -/
theorem stefan_walk_const {n l : ℕ} (hn : 1 ≤ n) (hl : l % 2 = 1) (h3 : 3 ≤ l) (hlm : l ≤ 2 * n - 1)
    (w : ℕ → ℕ) (hw : ∀ i, w i < 2 * n) (hE : ∀ i, StefanEdge n (w i) (w (i + 1)))
    (hper : ∀ i, w (i + l) = w i) : ∀ i, w i = n := by
  -- there is a loop step
  have hloop : ∃ i, w i = n ∧ w (i + 1) = n := by
    by_contra hno
    push Not at hno
    have hflip : ∀ i, (w (i + 1) < n ↔ ¬ w i < n) := by
      intro i
      rcases stefanEdge_side hn (hw i) (hE i) with ⟨h1, h2⟩ | h
      · exact absurd h2 (hno i h1)
      · omega
    have hk : ∀ k, (w k < n ↔ ((w 0 < n) ↔ k % 2 = 0)) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have h3 : ((k + 1) % 2 = 0) ↔ ¬ (k % 2 = 0) := by omega
        rw [hflip k, ih, h3]
        tauto
    have := hk l
    rw [show w l = w 0 by simpa using hper 0] at this
    have h4 : ¬ (l % 2 = 0) := by omega
    tauto
  obtain ⟨i, hi, hi1⟩ := hloop
  by_contra hne
  push Not at hne
  obtain ⟨j, hj⟩ := hne
  have hpow : ∀ t, w (j + l * t) = w j := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [(show j + l * (t + 1) = (j + l * t) + l by ring), hper, ih]
  classical
  have hex : ∃ j', i < j' ∧ w j' ≠ n := ⟨j + l * (i + 1), by nlinarith, by rw [hpow]; exact hj⟩
  obtain ⟨j0, ⟨hj01, hj02⟩, hj0min⟩ : ∃ j0, (i < j0 ∧ w j0 ≠ n) ∧
      ∀ k, k < j0 → ¬ (i < k ∧ w k ≠ n) := ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
  have hp : w (j0 - 1) = n := by
    by_cases h : j0 - 1 = i
    · rw [h]; exact hi
    · by_contra hc
      exact hj0min (j0 - 1) (by omega) ⟨by omega, hc⟩
  obtain ⟨p, hpdef⟩ : ∃ p, p = j0 - 1 := ⟨_, rfl⟩
  rw [← hpdef] at hp
  have hj0p : j0 = p + 1 := by omega
  rw [hj0p] at hj02
  have hstep := hE p
  rw [hp] at hstep
  have hp1 : w (p + 1) = n - 1 := by
    rcases stefanEdge_cases hn (by omega) hstep with h | h | h | h <;> omega
  -- the forced chain
  have hchain : ∀ s, s ≤ n - 1 → w (p + 1 + 2 * s) = n - 1 - s ∧
      (s + 2 ≤ n → w (p + 1 + 2 * s + 1) = n + 1 + s) := by
    intro s
    induction s with
    | zero =>
      intro _
      have e0 : w (p + 1 + 2 * 0) = n - 1 := hp1
      refine ⟨by omega, fun hs => ?_⟩
      have e1 := hE (p + 1 + 2 * 0)
      rw [e0] at e1
      rcases stefanEdge_cases hn (by omega) e1 with h | h | h | h <;> omega
    | succ s ih =>
      intro hs
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      have e1 := ih2 (by omega)
      have e2 := hE (p + 1 + 2 * s + 1)
      rw [show p + 1 + 2 * s + 1 + 1 = p + 1 + 2 * (s + 1) by omega, e1] at e2
      have e3 : w (p + 1 + 2 * (s + 1)) = n - 1 - (s + 1) := by
        rcases stefanEdge_cases hn (by omega) e2 with h | h | h | h <;> omega
      refine ⟨e3, fun hs2 => ?_⟩
      have e4 := hE (p + 1 + 2 * (s + 1))
      rw [e3] at e4
      rcases stefanEdge_cases hn (by omega) e4 with h | h | h | h <;> omega
  have hfin := (hchain ((l - 1) / 2) (by omega)).1
  have hq := hper p
  rw [hp] at hq
  rw [show p + l = p + 1 + 2 * ((l - 1) / 2) by omega] at hq
  omega

end UndergradKB.Topology
