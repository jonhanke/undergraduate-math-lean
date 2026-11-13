import Mathlib.Logic.Relation
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Find
import UndergradKB.Common.Attr

/-!
# Sharkovskii's theorem for odd periods: a graph lemma

Morris, *Topology Without Tears* (2024), Appendix 3, Theorem A3.6.4 (`morris2024`).  This file contains the
purely combinatorial heart of the Štefan-cycle argument, on vertices `ℕ` (the gaps between consecutive points of
a cycle): a loop vertex of a relation without primitive odd closed walks of length `3, ..., N - 1` lies on a
Hamiltonian chain with no forward shortcuts.
-/

namespace UndergradKB.Topology

/-- A primitive closed walk of length `l` in the relation `R` on `ℕ` (a periodic sequence of vertices
of exact period `l`). -/
def IsPrimLoop (R : ℕ → ℕ → Prop) (l : ℕ) (w : ℕ → ℕ) : Prop :=
  0 < l ∧ (∀ i, w (i + l) = w i) ∧ (∀ i, R (w i) (w (i + 1))) ∧
    ∀ p, 0 < p → p < l → ∃ i, w (i + p) ≠ w i

lemma nat_mod_succ_cases (i e : ℕ) (he : 0 < e) :
    (i % e + 1 < e ∧ (i + 1) % e = i % e + 1) ∨ (i % e + 1 = e ∧ (i + 1) % e = 0) := by
  have h1 : i % e < e := Nat.mod_lt _ he
  have h2 : e * (i / e) + i % e = i := Nat.div_add_mod i e
  rcases Nat.lt_or_ge (i % e + 1) e with h | h
  · left
    refine ⟨h, ?_⟩
    have : i + 1 = (i % e + 1) + e * (i / e) := by omega
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]
  · right
    have h3 : i % e + 1 = e := by omega
    refine ⟨h3, ?_⟩
    have : i + 1 = 0 + e * (i / e + 1) := by rw [Nat.mul_add]; omega
    rw [this, Nat.add_mul_mod_self_left]
    simp

/-- A simple cycle through a vertex carrying a loop has length `N`, if there is no primitive odd closed
walk of length between `3` and `N - 1`. -/
lemma simple_cycle_len_eq {R : ℕ → ℕ → Prop} {N : ℕ} (hN : Even N)
    (hbd : ∀ a b, R a b → a < N ∧ b < N)
    (hH : ∀ l w, 3 ≤ l → l < N → Odd l → ¬ IsPrimLoop R l w)
    {u : ℕ → ℕ} {e : ℕ} (he : 2 ≤ e)
    (hinj : ∀ i j, i < e → j < e → u i = u j → i = j)
    (hstep : ∀ i, i + 1 < e → R (u i) (u (i + 1)))
    (hclose : R (u (e - 1)) (u 0)) (hloop : R (u 0) (u 0)) : e = N := by
  have hlt : ∀ i, i < e → u i < N := by
    intro i hi
    by_cases h : i + 1 < e
    · exact (hbd _ _ (hstep i h)).1
    · have : i = e - 1 := by omega
      subst this
      exact (hbd _ _ hclose).1
  have heN : e ≤ N := by
    have := Finset.card_le_card_of_injOn (s := Finset.range e) (t := Finset.range N) u
      (by intro i hi; simp only [Finset.mem_coe, Finset.mem_range] at hi ⊢; exact hlt i hi)
      (by
        intro i hi j hj hij
        simp only [Finset.mem_coe, Finset.mem_range] at hi hj
        exact hinj i j hi hj hij)
    simpa using this
  have hNev : N % 2 = 0 := Nat.even_iff.mp hN
  by_cases hodd : Odd e
  · exfalso
    have heo : e % 2 = 1 := Nat.odd_iff.mp hodd
    have hltN : e < N := by omega
    apply hH e (fun i => u (i % e)) (by omega) hltN hodd
    refine ⟨by omega, ?_, ?_, ?_⟩
    · intro i
      simp only [Nat.add_mod_right]
    · intro i
      have hr : i % e < e := Nat.mod_lt _ (by omega)
      rcases nat_mod_succ_cases i e (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp only [h2]
        exact hstep _ h1
      · simp only [h2]
        have : i % e = e - 1 := by omega
        rw [this]
        exact hclose
    · intro p hp hpe
      refine ⟨0, ?_⟩
      simp only [Nat.zero_add, Nat.zero_mod]
      rw [Nat.mod_eq_of_lt hpe]
      intro h
      have := hinj p 0 hpe (by omega) h
      omega
  · have hee : e % 2 = 0 := by
      have := Nat.not_odd_iff_even.mp hodd
      exact Nat.even_iff.mp this
    by_contra hne
    have hltN : e + 1 < N := by omega
    set c : ℕ → ℕ := fun i => if i % (e + 1) = 0 then u 0 else u (i % (e + 1) - 1) with hc
    apply hH (e + 1) c (by omega) hltN ⟨e / 2, by omega⟩
    refine ⟨by omega, ?_, ?_, ?_⟩
    · intro i
      simp only [hc, Nat.add_mod_right]
    · intro i
      have hr : i % (e + 1) < e + 1 := Nat.mod_lt _ (by omega)
      rcases nat_mod_succ_cases i (e + 1) (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp only [hc, h2]
        by_cases h0 : i % (e + 1) = 0
        · simp [h0, hloop]
        · have h3 : i % (e + 1) + 1 ≠ 0 := by omega
          simp only [h0, h3, ite_false]
          have := hstep (i % (e + 1) - 1) (by omega)
          rw [show i % (e + 1) - 1 + 1 = i % (e + 1) + 1 - 1 by omega] at this
          exact this
      · simp only [hc, h2]
        have h0 : i % (e + 1) ≠ 0 := by omega
        simp only [h0, ite_false, ite_true]
        rw [show i % (e + 1) - 1 = e - 1 by omega]
        exact hclose
    · intro p hp hpe
      refine ⟨2, ?_⟩
      have h2 : 2 % (e + 1) = 2 := Nat.mod_eq_of_lt (by omega)
      have hc2 : c 2 = u 1 := by simp [hc, h2]
      rw [hc2]
      have hr : (2 + p) % (e + 1) ≠ 2 := by
        by_cases hq : 2 + p < e + 1
        · rw [Nat.mod_eq_of_lt hq]; omega
        · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
      have hr' : (2 + p) % (e + 1) < e + 1 := Nat.mod_lt _ (by omega)
      by_cases h0 : (2 + p) % (e + 1) = 0
      · simp only [hc, h0, ite_true]
        intro h
        have := hinj 0 1 (by omega) (by omega) h
        omega
      · simp only [hc, h0, ite_false]
        intro h
        have := hinj _ _ (by omega) (by omega) h
        omega

/-- Walks of length `n` from `t` to `g`. -/
def WalkTo (R : ℕ → ℕ → Prop) (t : ℕ) (n g : ℕ) : Prop :=
  ∃ w : ℕ → ℕ, w 0 = t ∧ w n = g ∧ ∀ i, i < n → R (w i) (w (i + 1))

lemma exists_walk_of_rtg {R : ℕ → ℕ → Prop} {t g : ℕ} (h : Relation.ReflTransGen R t g) :
    ∃ n, WalkTo R t n g := by
  induction h with
  | refl => exact ⟨0, fun _ => t, rfl, rfl, by simp⟩
  | @tail b c _ hbc ih =>
    obtain ⟨n, w, h0, hn, hs⟩ := ih
    refine ⟨n + 1, fun i => if i ≤ n then w i else c, ?_, ?_, ?_⟩
    · simp [h0]
    · simp
    · intro i hi
      by_cases h1 : i + 1 ≤ n
      · simp only [h1, show i ≤ n by omega, ite_true]
        exact hs i (by omega)
      · have : i = n := by omega
        subst this
        simp only [le_refl, ite_true, show ¬ (i + 1 ≤ i) by omega, ite_false]
        rw [hn]
        exact hbc

theorem exists_hamiltonian_chain {R : ℕ → ℕ → Prop} {N t : ℕ} (hN : Even N)
    (hbd : ∀ a b, R a b → a < N ∧ b < N) (hloop : R t t)
    (hreach : ∀ g, g < N → Relation.ReflTransGen R t g)
    (hback : ∃ J, J ≠ t ∧ R J t)
    (hH : ∀ l w, 3 ≤ l → l < N → Odd l → ¬ IsPrimLoop R l w) :
    ∃ v : ℕ → ℕ, v 0 = t ∧ (∀ i j, i < N → j < N → v i = v j → i = j) ∧
      (∀ i, i < N → v i < N) ∧ (∀ g, g < N → ∃ i, i < N ∧ v i = g) ∧
      (∀ i, i + 1 < N → R (v i) (v (i + 1))) ∧ R (v (N - 1)) (v 0) ∧
      (∀ i j, i < N → j < N → R (v i) (v j) → j ≤ i + 1) ∧
      (∀ i, i < N → R (v i) (v 0) → i = 0 ∨ i = N - 1) := by
  obtain ⟨J, hJt, hJR⟩ := hback
  have hJN : J < N := (hbd _ _ hJR).1
  have hex : ∃ n, WalkTo R t n J := exists_walk_of_rtg (hreach J hJN)
  classical
  set n := Nat.find hex with hn
  have hwalk : WalkTo R t n J := Nat.find_spec hex
  have hmin : ∀ n', n' < n → ¬ WalkTo R t n' J := fun n' h => Nat.find_min hex h
  obtain ⟨w, hw0, hwn, hs⟩ := hwalk
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h] at hwn
      exact absurd (hwn.symm.trans hw0) hJt
    · exact h
  -- injectivity of the walk
  have key : ∀ i j, i < j → j ≤ n → w i = w j → False := by
    intro i j hij hjn heq
    apply hmin (n - (j - i)) (by omega)
    refine ⟨fun k => if k < i then w k else w (k + (j - i)), ?_, ?_, ?_⟩
    · by_cases hi0 : 0 < i
      · simp [hi0, hw0]
      · have : i = 0 := by omega
        subst this
        simp [← heq, hw0]
    · simp only [show ¬ (n - (j - i) < i) by omega, ite_false]
      rw [show n - (j - i) + (j - i) = n by omega]
      exact hwn
    · intro k hk
      by_cases h1 : k + 1 < i
      · simp only [h1, show k < i by omega, ite_true]
        exact hs k (by omega)
      · by_cases h2 : k < i
        · have hki : k + 1 = i := by omega
          simp only [h1, h2, ite_true, ite_false]
          rw [show k + 1 + (j - i) = j by omega, ← heq, ← hki]
          exact hs k (by omega)
        · simp only [h1, h2, ite_false]
          have := hs (k + (j - i)) (by omega)
          rwa [show k + (j - i) + 1 = k + 1 + (j - i) by omega] at this
  have hinj : ∀ i j, i ≤ n → j ≤ n → w i = w j → i = j := by
    intro i j hi hj hij
    rcases lt_trichotomy i j with h | h | h
    · exact (key i j h hj hij).elim
    · exact h
    · exact (key j i h hi hij.symm).elim
  -- no shortcuts
  have hshort : ∀ i j, i ≤ n → j ≤ n → R (w i) (w j) → j ≤ i + 1 := by
    intro i j hi hj hR
    by_contra hlt
    push Not at hlt
    apply hmin (n - (j - i - 1)) (by omega)
    refine ⟨fun k => if k ≤ i then w k else w (k + (j - i - 1)), ?_, ?_, ?_⟩
    · simp [hw0]
    · simp only [show ¬ (n - (j - i - 1) ≤ i) by omega, ite_false]
      rw [show n - (j - i - 1) + (j - i - 1) = n by omega]
      exact hwn
    · intro k hk
      by_cases h1 : k + 1 ≤ i
      · simp only [h1, show k ≤ i by omega, ite_true]
        exact hs k (by omega)
      · by_cases h2 : k ≤ i
        · have hki : k = i := by omega
          simp only [h1, h2, ite_true, ite_false]
          subst hki
          rw [show k + 1 + (j - k - 1) = j by omega]
          exact hR
        · simp only [h1, h2, ite_false]
          have := hs (k + (j - i - 1)) (by omega)
          rwa [show k + (j - i - 1) + 1 = k + 1 + (j - i - 1) by omega] at this
  have hcl : R (w n) (w 0) := by rw [hwn, hw0]; exact hJR
  have hlp : R (w 0) (w 0) := by rw [hw0]; exact hloop
  have hcyc := simple_cycle_len_eq (u := w) (e := n + 1) hN hbd hH (by omega)
    (fun i j hi hj h => hinj i j (by omega) (by omega) h) (fun i hi => hs i (by omega))
    (by simpa using hcl) hlp
  have hNn : N = n + 1 := hcyc.symm
  have hwlt : ∀ i, i < N → w i < N := by
    intro i hi
    by_cases h : i < n
    · exact (hbd _ _ (hs i h)).1
    · have : i = n := by omega
      subst this
      rw [hwn]; exact hJN
  refine ⟨w, hw0, fun i j hi hj h => hinj i j (by omega) (by omega) h, hwlt, ?_, fun i hi => hs i (by omega),
    by rw [show N - 1 = n by omega]; exact hcl, fun i j hi hj hR => hshort i j (by omega) (by omega) hR, ?_⟩
  · intro g hg
    have himg : (Finset.range N).image w = Finset.range N := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
        obtain ⟨i, hi, rfl⟩ := hx
        exact hwlt i hi
      · rw [Finset.card_image_of_injOn]
        intro i hi j hj hij
        simp only [Finset.mem_coe, Finset.mem_range] at hi hj
        exact hinj i j (by omega) (by omega) hij
    have : g ∈ (Finset.range N).image w := by rw [himg]; simpa using hg
    simp only [Finset.mem_image, Finset.mem_range] at this
    obtain ⟨i, hi, hig⟩ := this
    exact ⟨i, hi, hig⟩
  · intro i hi hR
    by_contra hne
    push Not at hne
    have := simple_cycle_len_eq (u := w) (e := i + 1) hN hbd hH (by omega)
      (fun a b ha hb h => hinj a b (by omega) (by omega) h) (fun a ha => hs a (by omega))
      (by simpa using hR) hlp
    omega

end UndergradKB.Topology
