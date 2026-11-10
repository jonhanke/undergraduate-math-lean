import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.Order.Dominance

/-!
# Covers in the dominance order on partitions (Keller–Trotter, Proposition 16.11)

We first work with partitions as eventually-zero nonincreasing sequences `ℕ → ℕ` and their partial
sums `ps`; the proposition is proved there (`cover_seq`) and then transported to the strings
`Fin m → ℕ` of `Order/Dominance.lean`.
-/

namespace UndergradKB.Combinatorics

open Finset

namespace Covers

/-- Partial sums `a 0 + ⋯ + a (k-1)`. -/
def ps (a : ℕ → ℕ) (k : ℕ) : ℕ := ∑ x ∈ range k, a x

lemma ps_zero (a : ℕ → ℕ) : ps a 0 = 0 := by simp [ps]

lemma ps_succ (a : ℕ → ℕ) (k : ℕ) : ps a (k + 1) = ps a k + a k := by
  simp [ps, Finset.sum_range_succ]

lemma ps_conc {a : ℕ → ℕ} (ha : Antitone a) (k : ℕ) :
    ps a (k + 2) + ps a k ≤ 2 * ps a (k + 1) := by
  have h1 : ps a (k + 2) = ps a (k + 1) + a (k + 1) := ps_succ a (k + 1)
  have h2 := ps_succ a k
  have : a (k + 1) ≤ a k := ha (Nat.le_succ k)
  omega

lemma eq_of_ps {a b : ℕ → ℕ} (h : ∀ k, ps a k = ps b k) : a = b := by
  funext k
  have := ps_succ a k
  have := ps_succ b k
  have := h k
  have := h (k + 1)
  omega

/-- A nonincreasing, eventually zero sequence with total `t`. -/
def IsSeqPart (a : ℕ → ℕ) (t : ℕ) : Prop :=
  Antitone a ∧ ∃ N, (∀ k, N ≤ k → a k = 0) ∧ ps a N = t

lemma IsSeqPart.ps_eq {a : ℕ → ℕ} {t : ℕ} (h : IsSeqPart a t) :
    ∃ N, ∀ k, N ≤ k → ps a k = t := by
  obtain ⟨_, N, hN, hs⟩ := h
  refine ⟨N, fun k hk => ?_⟩
  induction k, hk using Nat.le_induction with
  | base => exact hs
  | succ k hk ih => rw [ps_succ, ih, hN k hk, add_zero]

/-- A concave, nondecreasing, eventually constant function `C` with `C 0 = 0` is the sequence of
partial sums of a partition. -/
lemma exists_seq_of_ps (C : ℕ → ℕ) (t N : ℕ) (h0 : C 0 = 0)
    (hconc : ∀ k, C (k + 2) + C k ≤ 2 * C (k + 1)) (hmono : ∀ k, C k ≤ C (k + 1))
    (hev : ∀ k, N ≤ k → C k = t) :
    ∃ c, IsSeqPart c t ∧ ∀ k, ps c k = C k := by
  have hps : ∀ k, ps (fun k => C (k + 1) - C k) k = C k := by
    intro k
    induction k with
    | zero => rw [ps_zero, h0]
    | succ k ih =>
      rw [ps_succ, ih]
      have := hmono k
      omega
  refine ⟨fun k => C (k + 1) - C k, ⟨?_, N, ?_, ?_⟩, hps⟩
  · refine antitone_nat_of_succ_le fun k => ?_
    have := hconc k
    show C (k + 2) - C (k + 1) ≤ C (k + 1) - C k
    omega
  · intro k hk
    show C (k + 1) - C k = 0
    rw [hev k hk, hev (k + 1) (by omega)]
    simp
  · rw [hps, hev N le_rfl]

variable {a b : ℕ → ℕ} {t : ℕ}

/-- Step 1: partial sums of a cover differ by at most one. -/
lemma step_le_one (ha : IsSeqPart a t) (hb : IsSeqPart b t) (hle : ∀ k, ps b k ≤ ps a k)
    (hne : a ≠ b)
    (hcov : ∀ c, IsSeqPart c t → (∀ k, ps b k ≤ ps c k) → (∀ k, ps c k ≤ ps a k) →
      c = a ∨ c = b) : ∀ k, ps a k ≤ ps b k + 1 := by
  obtain ⟨Na, hNa⟩ := ha.ps_eq
  obtain ⟨Nb, hNb⟩ := hb.ps_eq
  have hCmono : ∀ k, min (ps a k) (ps b k + 1) ≤ min (ps a (k + 1)) (ps b (k + 1) + 1) := by
    intro k
    have h1 := ps_succ a k
    have h2 := ps_succ b k
    omega
  obtain ⟨c, hc, hcs⟩ := exists_seq_of_ps (fun k => min (ps a k) (ps b k + 1)) t (max Na Nb)
    (by simp [ps_zero]) (fun k => by
      have h1 := ps_conc ha.1 k
      have h2 := ps_conc hb.1 k
      omega) hCmono (fun k hk => by
      rw [hNa k (le_trans (le_max_left _ _) hk), hNb k (le_trans (le_max_right _ _) hk)]
      omega)
  rcases hcov c hc (fun k => by rw [hcs k]; have := hle k; omega)
    (fun k => by rw [hcs k]; omega) with h | h
  · intro k
    have := hcs k
    rw [h] at this
    omega
  · exfalso
    apply hne
    refine eq_of_ps fun k => ?_
    have := hcs k
    rw [h] at this
    have := hle k
    omega

lemma ps_mono' (a : ℕ → ℕ) {k l : ℕ} (h : k ≤ l) : ps a k ≤ ps a l :=
  Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 h)

lemma ps_two (a : ℕ → ℕ) (k : ℕ) : ps a (k + 2) = ps a k + a k + a (k + 1) := by
  have h1 : ps a (k + 2) = ps a (k + 1) + a (k + 1) := ps_succ a (k + 1)
  rw [h1, ps_succ]

/-- Step 2: the partial sums of a cover differ by `1` exactly on one interval `[r, e)`. -/
lemma step_run (ha : IsSeqPart a t) (hb : IsSeqPart b t) (hle : ∀ k, ps b k ≤ ps a k)
    (hne : a ≠ b)
    (hcov : ∀ c, IsSeqPart c t → (∀ k, ps b k ≤ ps c k) → (∀ k, ps c k ≤ ps a k) →
      c = a ∨ c = b) :
    ∃ r e, 1 ≤ r ∧ r < e ∧
      ∀ k, ps a k = ps b k + (if r ≤ k ∧ k < e then 1 else 0) := by
  have h1 := step_le_one ha hb hle hne hcov
  obtain ⟨Na, hNa⟩ := ha.ps_eq
  obtain ⟨Nb, hNb⟩ := hb.ps_eq
  have hex : ∃ k, ps b k < ps a k := by
    by_contra h
    push Not at h
    exact hne (eq_of_ps fun k => le_antisymm (h k) (hle k))
  obtain ⟨r, hr, hrmin⟩ : ∃ r, ps b r < ps a r ∧ ∀ k, k < r → ps a k = ps b k := by
    refine ⟨Nat.find hex, Nat.find_spec hex, fun k hk => ?_⟩
    have := Nat.find_min hex hk
    have := hle k
    omega
  obtain ⟨e, he, hemin⟩ : ∃ e, (r < e ∧ ps a e = ps b e) ∧ ∀ k, k < e → ¬ (r < k ∧ ps a k = ps b k) := by
    have hex2 : ∃ k, r < k ∧ ps a k = ps b k :=
      ⟨max (max Na Nb) (r + 1), by omega, by
        rw [hNa _ (le_trans (le_max_left _ _) (le_max_left _ _)),
          hNb _ (le_trans (le_max_right _ _) (le_max_left _ _))]⟩
    exact ⟨Nat.find hex2, Nat.find_spec hex2, fun k hk => Nat.find_min hex2 hk⟩
  have hD : ∀ k, r ≤ k → k < e → ps a k = ps b k + 1 := by
    intro k hrk hke
    rcases Nat.eq_or_lt_of_le hrk with h | h
    · subst h
      have := h1 r
      omega
    · have := hemin k hke
      have := h1 k
      have := hle k
      omega
  have hCmono : ∀ k, (if k ≤ e then ps b k else ps a k) ≤
      (if k + 1 ≤ e then ps b (k + 1) else ps a (k + 1)) := by
    intro k
    have h2 := ps_succ a k
    have h3 := ps_succ b k
    have h4 : k = e → ps a k = ps b k := by intro h; subst h; exact he.2
    split_ifs <;> omega
  obtain ⟨c, hc, hcs⟩ := exists_seq_of_ps (fun k => if k ≤ e then ps b k else ps a k) t
    (max Na Nb)
    (by simp [ps_zero]) (fun k => by
      have h2 := ps_conc ha.1 k
      have h3 := ps_conc hb.1 k
      have h4 := hle k
      have h5 : k + 1 = e → ps a (k + 1) = ps b (k + 1) := by intro h; rw [h]; exact he.2
      show (if k + 2 ≤ e then ps b (k + 2) else ps a (k + 2)) +
        (if k ≤ e then ps b k else ps a k) ≤ 2 * (if k + 1 ≤ e then ps b (k + 1) else ps a (k + 1))
      split_ifs <;> omega) hCmono (fun k hk => by
      show (if k ≤ e then ps b k else ps a k) = t
      split_ifs
      · exact hNb k (le_trans (le_max_right _ _) hk)
      · exact hNa k (le_trans (le_max_left _ _) hk))
  have hcs' : ∀ k, ps c k = if k ≤ e then ps b k else ps a k := hcs
  have hmain : ∀ k, ps a k = ps b k + (if r ≤ k ∧ k < e then 1 else 0) := by
    rcases hcov c hc (fun k => by rw [hcs' k]; have := hle k; split_ifs <;> omega)
      (fun k => by rw [hcs' k]; have := hle k; split_ifs <;> omega) with h | h
    · exfalso
      have := hcs' r
      rw [h, if_pos he.1.le] at this
      omega
    · intro k
      by_cases hk : k < r
      · rw [if_neg (by omega), hrmin k hk]; rfl
      · by_cases hk2 : k < e
        · rw [if_pos ⟨by omega, hk2⟩]; exact hD k (by omega) hk2
        · rw [if_neg (by omega)]
          rcases Nat.eq_or_lt_of_le (not_lt.1 hk2) with h' | h'
          · subst h'; exact he.2
          · have := hcs' k
            rw [h, if_neg (by omega)] at this
            omega
  refine ⟨r, e, ?_, he.1, hmain⟩
  by_contra h0
  have h0' : r = 0 := by omega
  subst h0'
  have := hmain 0
  rw [ps_zero, ps_zero, if_pos ⟨le_rfl, by omega⟩] at this
  omega

/-- Partial sums `ps a k` minus the unit correction on `(i, γ]`. -/
def corr (a : ℕ → ℕ) (i γ k : ℕ) : ℕ := ps a k - if i < k ∧ k ≤ γ then 1 else 0

/-- Step 3 (local): the intermediate partition obtained by moving the unit from `i` to `γ`
cannot exist strictly between, which forces the entries between `i` and `j` to equal `a i - 1`. -/
lemma step_inner (ha : IsSeqPart a t) (hb : IsSeqPart b t) (hle : ∀ k, ps b k ≤ ps a k)
    (hcov : ∀ c, IsSeqPart c t → (∀ k, ps b k ≤ ps c k) → (∀ k, ps c k ≤ ps a k) →
      c = a ∨ c = b) {i j : ℕ} (hij : i < j)
    (hform : ∀ k, ps a k = ps b k + (if i + 1 ≤ k ∧ k < j + 1 then 1 else 0)) {γ : ℕ}
    (hiγ : i < γ) (hγj : γ < j)
    (hai : ∀ k, i < k → k < j → a k + 1 ≤ a i) (hpos : 1 ≤ a i)
    (H : (γ = i + 1 ∧ a γ + 2 ≤ a i) ∨ (i + 1 < γ ∧ a γ + 1 ≤ a (γ - 1))) : False := by
  obtain ⟨Na, hNa⟩ := ha.ps_eq
  have hanti : ∀ k, a (k + 1) ≤ a k := fun k => ha.1 (Nat.le_succ k)
  have hps1 : ∀ k, i < k → 1 ≤ ps a k := by
    intro k hk
    have h1 := ps_mono' a (show i + 1 ≤ k from hk)
    have h2 := ps_succ a i
    omega
  have hpsγ : ∀ k, i < k → k ≤ γ → ps b k + 1 = ps a k := by
    intro k hk1 hk2
    have := hform k
    rw [if_pos ⟨by omega, by omega⟩] at this
    omega
  obtain ⟨c, hc, hcs⟩ := exists_seq_of_ps (corr a i γ) t (max Na (γ + 1))
    (by simp [corr, ps_zero]) (fun k => by
      have h2 := ps_conc ha.1 k
      have h3 : ps a (k + 2) = ps a k + a k + a (k + 1) := ps_two a k
      have h4 := ps_succ a k
      have h5 := hanti k
      have h6 := hps1 (k + 1)
      have h7 := hps1 (k + 2)
      have h8 := hps1 k
      show (ps a (k + 2) - (if i < k + 2 ∧ k + 2 ≤ γ then 1 else 0)) + (ps a k - (if i < k ∧ k ≤ γ then 1 else 0)) ≤
        2 * (ps a (k + 1) - (if i < k + 1 ∧ k + 1 ≤ γ then 1 else 0))
      rcases Nat.lt_trichotomy k i with hk | hk | hk
      · split_ifs <;> omega
      · subst hk
        have h9 := hai (k + 1) (by omega) (by omega)
        rcases H with ⟨hγ, hn⟩ | ⟨hγ, hn⟩
        · subst hγ
          split_ifs <;> omega
        · split_ifs <;> omega
      · rcases Nat.lt_trichotomy (k + 1) γ with hk' | hk' | hk'
        · split_ifs <;> omega
        · subst hk'
          have : (k + 1) - 1 = k := by omega
          rw [this] at H
          split_ifs <;> omega
        · split_ifs <;> omega) (fun k => by
      have h4 := ps_succ a k
      have h6 := hps1 (k + 1)
      show (ps a k - (if i < k ∧ k ≤ γ then 1 else 0)) ≤
        (ps a (k + 1) - (if i < k + 1 ∧ k + 1 ≤ γ then 1 else 0))
      rcases Nat.lt_trichotomy k i with hk | hk | hk
      · split_ifs <;> omega
      · subst hk
        split_ifs <;> omega
      · split_ifs <;> omega) (fun k hk => by
      show ps a k - (if i < k ∧ k ≤ γ then 1 else 0) = t
      rw [if_neg (by omega)]
      have := hNa k (le_trans (le_max_left _ _) hk)
      omega)
  have hcs' : ∀ k, ps c k = ps a k - if i < k ∧ k ≤ γ then 1 else 0 := hcs
  rcases hcov c hc (fun k => by
      rw [hcs' k]
      have := hle k
      by_cases hk : i < k ∧ k ≤ γ
      · rw [if_pos hk]; have := hpsγ k hk.1 hk.2; omega
      · rw [if_neg hk]; omega)
    (fun k => by rw [hcs' k]; omega) with h | h
  · have := hcs' γ
    rw [h, if_pos ⟨hiγ, le_rfl⟩] at this
    have := hps1 γ hiγ
    omega
  · have := hcs' (γ + 1)
    rw [h, if_neg (by omega)] at this
    have h1 := hform (γ + 1)
    rw [if_pos ⟨by omega, by omega⟩] at h1
    omega

/-- Proposition 16.11 for sequences (0-indexed): a cover moves one unit from position `i` to a
later position `j`, and all the entries strictly between them equal `a i - 1`. -/
theorem cover_seq (ha : IsSeqPart a t) (hb : IsSeqPart b t) (hle : ∀ k, ps b k ≤ ps a k)
    (hne : a ≠ b)
    (hcov : ∀ c, IsSeqPart c t → (∀ k, ps b k ≤ ps c k) → (∀ k, ps c k ≤ ps a k) →
      c = a ∨ c = b) :
    ∃ i j, i < j ∧ a i = b i + 1 ∧ a j + 1 = b j ∧ (∀ k, k ≠ i → k ≠ j → a k = b k) ∧
      (∀ γ, i < γ → γ < j → a γ + 1 = a i) := by
  obtain ⟨r, e, hr1, hre, hform⟩ := step_run ha hb hle hne hcov
  obtain ⟨i, rfl⟩ : ∃ i, r = i + 1 := ⟨r - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, e = j + 1 := ⟨e - 1, by omega⟩
  have hij : i < j := by omega
  have hak : ∀ k, a k + (if i + 1 ≤ k ∧ k < j + 1 then 1 else 0) =
      b k + (if i + 1 ≤ k + 1 ∧ k + 1 < j + 1 then 1 else 0) := by
    intro k
    have h1 := hform k
    have h2 := hform (k + 1)
    have h3 := ps_succ a k
    have h4 := ps_succ b k
    omega
  have hother : ∀ k, k ≠ i → k ≠ j → a k = b k := by
    intro k hki hkj
    have := hak k
    split_ifs at this <;> omega
  have hai_eq : a i = b i + 1 := by
    have := hak i
    split_ifs at this <;> omega
  have haj_eq : a j + 1 = b j := by
    have := hak j
    split_ifs at this <;> omega
  have hai : ∀ k, i < k → k < j → a k + 1 ≤ a i := by
    intro k hik hkj
    have := hb.1 (show i ≤ k from hik.le)
    have := hother k (by omega) (by omega)
    omega
  have hpos : 1 ≤ a i := by omega
  refine ⟨i, j, hij, hai_eq, haj_eq, hother, ?_⟩
  intro γ hiγ hγj
  induction γ, hiγ using Nat.le_induction with
  | base =>
    by_contra hne'
    change ¬ a (i + 1) + 1 = a i at hne'
    have := hai (i + 1) (by omega) hγj
    exact step_inner (γ := i + 1) ha hb hle hcov hij hform (by omega) hγj hai hpos
      (Or.inl ⟨rfl, by omega⟩)
  | succ γ hγ ih =>
    by_contra hne'
    have h1 := hai (γ + 1) (by omega) hγj
    have h2 := ih (by omega)
    have h3 := ha.1 (Nat.le_succ γ)
    exact step_inner (γ := γ + 1) ha hb hle hcov hij hform (by omega) hγj hai hpos
      (Or.inr ⟨by omega, by simp only [Nat.add_sub_cancel]; omega⟩)

end Covers

/-! ### Transport to strings -/

open Covers in
lemma extZero_antitone {m : ℕ} {V : Fin m → ℕ} (hV : Antitone V) : Antitone (extZero V) := by
  intro k l hkl
  unfold extZero
  by_cases hl : l < m
  · rw [dif_pos hl, dif_pos (lt_of_le_of_lt hkl hl)]
    exact hV (Fin.mk_le_mk.2 hkl)
  · rw [dif_neg hl]
    exact Nat.zero_le _

lemma extZero_pos {m : ℕ} {V : Fin m → ℕ} {t : ℕ} (hV : IsPartitionString V t) {k : ℕ}
    (hk : k < m) : 0 < extZero V k := by
  unfold extZero
  rw [dif_pos hk]
  exact hV.pos _

lemma isSeqPart_extZero {m : ℕ} {V : Fin m → ℕ} {t : ℕ} (hV : IsPartitionString V t) :
    Covers.IsSeqPart (extZero V) t :=
  ⟨extZero_antitone hV.antitone, m, fun k hk => extZero_ge V hk, by
    rw [← hV.sum_eq]; exact psum_of_ge V le_rfl⟩

lemma exists_string {c : ℕ → ℕ} {t : ℕ} (hc : Covers.IsSeqPart c t) :
    ∃ (k : ℕ) (U : Fin k → ℕ), IsPartitionString U t ∧ extZero U = c := by
  obtain ⟨hanti, N, hN, hsum⟩ := hc
  have hex : ∃ k, c k = 0 := ⟨N, hN N le_rfl⟩
  set k0 := Nat.find hex with hk0
  have hk0s : c k0 = 0 := Nat.find_spec hex
  have hafter : ∀ l, k0 ≤ l → c l = 0 := fun l hl => Nat.eq_zero_of_le_zero (hk0s ▸ hanti hl)
  have hbefore : ∀ l, l < k0 → 0 < c l := fun l hl =>
    Nat.pos_of_ne_zero (Nat.find_min hex hl)
  have hps : Covers.ps c k0 = t := by
    have : ∀ l, k0 ≤ l → Covers.ps c l = Covers.ps c k0 := by
      intro l hl
      induction l, hl using Nat.le_induction with
      | base => rfl
      | succ l hl ih => rw [Covers.ps_succ, ih, hafter l hl, add_zero]
    rw [← this (max k0 N)  (le_max_left _ _)]
    have h2 : ∀ l, N ≤ l → Covers.ps c l = t := by
      intro l hl
      induction l, hl using Nat.le_induction with
      | base => exact hsum
      | succ l hl ih => rw [Covers.ps_succ, ih, hN l hl, add_zero]
    exact h2 _ (le_max_right _ _)
  have hext : extZero (fun i : Fin k0 => c i) = c := by
    funext l
    unfold extZero
    by_cases h : l < k0
    · rw [dif_pos h]
    · rw [dif_neg h, hafter l (not_lt.1 h)]
  refine ⟨k0, fun i => c i, ⟨?_, fun i => hbefore i i.2, ?_⟩, hext⟩
  · intro i j hij
    exact hanti (Fin.mk_le_mk.1 hij)
  · rw [← hps, Covers.ps, ← Fin.sum_univ_eq_sum_range (fun i => c i)]

/-- For partitions of the same `t`, dominance is the comparison of partial sums. -/
lemma dominates_iff {m k : ℕ} {V : Fin m → ℕ} {U : Fin k → ℕ} {t : ℕ}
    (hV : IsPartitionString V t) (hU : IsPartitionString U t) :
    Dominates V U ↔ ∀ j, Covers.ps (extZero U) j ≤ Covers.ps (extZero V) j := by
  have hVt : ∀ j, m ≤ j → Covers.ps (extZero V) j = t := fun j hj => by
    rw [← hV.sum_eq]; exact psum_of_ge V hj
  have hUt : ∀ j, k ≤ j → Covers.ps (extZero U) j = t := fun j hj => by
    rw [← hU.sum_eq]; exact psum_of_ge U hj
  have hUle : ∀ j, Covers.ps (extZero U) j ≤ t := fun j => by
    rcases le_total k j with h | h
    · rw [hUt j h]
    · rw [← hUt k le_rfl]; exact Covers.ps_mono' _ h
  constructor
  · rintro ⟨hmk, h⟩ j
    by_cases hj : j ≤ m
    · exact h j hj
    · rw [hVt j (by omega)]; exact hUle j
  · intro h
    refine ⟨?_, fun j _ => h j⟩
    by_contra hkm
    push Not at hkm
    have h1 := h k
    have h2 := hUt k le_rfl
    have h3 := Covers.ps_succ (extZero V) k
    have h4 := extZero_pos hV hkm
    have h5 : Covers.ps (extZero V) (k + 1) ≤ t := by
      rw [← hVt m le_rfl]; exact Covers.ps_mono' _ hkm
    omega

/-- CO-180 (definition). `V` covers `W` in the poset `P(t)` of partitions of `t` with the
dominance order: both are partitions of `t`, `V` dominates `W`, they differ (partitions of
different lengths are compared through their zero-extensions), and every partition of `t`
between them is `V` or `W`. -/
def IsCover {m n : ℕ} (V : Fin m → ℕ) (W : Fin n → ℕ) (t : ℕ) : Prop :=
  IsPartitionString V t ∧ IsPartitionString W t ∧ Dominates V W ∧ extZero V ≠ extZero W ∧
    ∀ (k : ℕ) (U : Fin k → ℕ), IsPartitionString U t → Dominates V U → Dominates U W →
      extZero U = extZero V ∨ extZero U = extZero W

/-- CO-180. Keller–Trotter Proposition 16.11 (covers in the dominance order). Let `V = (v₁,…,v_m)`
and `W = (w₁,…,w_n)` be partitions of `t` (entries `v α = extZero V (α-1)`, `0` beyond the end)
such that `V` covers `W`. Then `n ≤ m + 1` and there are `1 ≤ i < j ≤ n` with
1. `v α = w α` for `α < i`;
2. `v β = w β` for `j < β ≤ m`;
3. `v i = 1 + w i`;
4. either (a) `j ≤ m` and `w j = 1 + v j`, or (b) `j = n = m + 1` and `w j = 1`;
5. if `j > i + 1` then `w γ = v γ = v i - 1` for `i < γ < j`. -/
@[kb "kellertrotter2017" "Proposition 16.11, p. 348"]
theorem cover_description {m n t : ℕ} {V : Fin m → ℕ} {W : Fin n → ℕ} (h : IsCover V W t) :
    n ≤ m + 1 ∧ ∃ i j : ℕ, 1 ≤ i ∧ i < j ∧ j ≤ n ∧
      (∀ α, 1 ≤ α → α < i → extZero V (α - 1) = extZero W (α - 1)) ∧
      (∀ β, j < β → β ≤ m → extZero V (β - 1) = extZero W (β - 1)) ∧
      extZero V (i - 1) = 1 + extZero W (i - 1) ∧
      ((j ≤ m ∧ extZero W (j - 1) = 1 + extZero V (j - 1)) ∨
        (j = n ∧ n = m + 1 ∧ extZero W (j - 1) = 1)) ∧
      (i + 1 < j → ∀ γ, i < γ → γ < j →
        extZero W (γ - 1) = extZero V (γ - 1) ∧ extZero V (γ - 1) = extZero V (i - 1) - 1) := by
  obtain ⟨hV, hW, hdom, hne, hcov⟩ := h
  have ha := isSeqPart_extZero hV
  have hb := isSeqPart_extZero hW
  have hle := (dominates_iff hV hW).1 hdom
  obtain ⟨i0, j0, hij, hai, haj, hoth, hinner⟩ := Covers.cover_seq ha hb hle hne (by
    intro c hc hbc hca
    obtain ⟨k, U, hU, rfl⟩ := exists_string hc
    exact hcov k U hU ((dominates_iff hV hU).2 hca) ((dominates_iff hU hW).2 hbc))
  have hmi : i0 < m := by
    by_contra hh
    have := extZero_ge V (not_lt.1 hh)
    omega
  have hjn : j0 < n := by
    by_contra hh
    have := extZero_ge W (not_lt.1 hh)
    omega
  have hbanti := hb.1
  have hjm : j0 ≤ m := by
    by_contra hh
    push Not at hh
    have h1 := hoth m (by omega) (by omega)
    have h2 := hbanti (show m ≤ j0 from hh.le)
    have h3 := extZero_ge V (le_refl m)
    have h4 := extZero_ge V (show m ≤ j0 from hh.le)
    omega
  have hn : n ≤ m + 1 := by
    by_contra hh
    push Not at hh
    have h1 := hoth (m + 1) (by omega) (by omega)
    have h2 := extZero_ge V (show m ≤ m + 1 by omega)
    have h3 := extZero_pos hW (show m + 1 < n by omega)
    omega
  refine ⟨hn, i0 + 1, j0 + 1, by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · intro α h1 h2
    try simp only [Nat.add_sub_cancel]
    exact hoth (α - 1) (by omega) (by omega)
  · intro β h1 h2
    exact hoth (β - 1) (by omega) (by omega)
  · simp only [Nat.add_sub_cancel]
    omega
  · simp only [Nat.add_sub_cancel]
    rcases Nat.lt_or_ge j0 m with hlt | hge
    · left
      exact ⟨by omega, by omega⟩
    · right
      have hjm' : j0 = m := by omega
      have h1 := extZero_ge V (show m ≤ j0 by omega)
      have h2 := hoth (j0 + 1) (by omega) (by omega)
      have h3 := extZero_ge V (show m ≤ j0 + 1 by omega)
      have h4 : n ≤ j0 + 1 := by
        by_contra hh
        push Not at hh
        have := extZero_pos hW (show j0 + 1 < n by omega)
        omega
      refine ⟨by omega, by omega, by omega⟩
  · intro _ γ h1 h2
    have e1 := hinner (γ - 1) (by omega) (by omega)
    have e2 := hoth (γ - 1) (by omega) (by omega)
    try simp only [Nat.add_sub_cancel]
    omega

end UndergradKB.Combinatorics
