import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-!
# Probability: riffle shuffles and Eulerian numbers (Grinstead–Snell, §3.3)

An *ordering* of a deck of `n` cards is a permutation `σ` of `Fin n`: `σ i` is the card in position `i`
(the identity ordering is the sorted deck).  An `a`-shuffle is recorded by a function `g : Fin n → Fin a`
giving the packet from which position `i` of the new deck is filled; this is the same data as a
cut-interleaving pair (cut sizes are the fibre sizes of `g`, the interleaving is `g` itself), and there are
`a ^ n` of them.  The cards of one packet keep their relative order, so the resulting ordering is the
inverse of the stable sort `Tuple.sort g`.

* `shuffleOrdering g`: the ordering produced from the identity by the shuffle `g`.
* `risingSequences σ`: the number of rising sequences of `σ` (maximal runs of consecutive cards
  appearing in increasing positions), counted by their first cards.
* `eulerianNumber n r`: the number of orderings of `n` cards with `r` rising sequences.
-/

open Finset

namespace UndergradKB.Probability

/-- The ordering of the deck obtained by applying to the identity ordering the shuffle in which position `i`
of the new deck is filled from packet `g i`; the cards of each packet keep their relative order
(Grinstead–Snell §3.3, cut-interleaving pairs of an `a`-shuffle when `α = Fin a`). -/
def shuffleOrdering {n : ℕ} {α : Type*} [LinearOrder α] (g : Fin n → α) : Equiv.Perm (Fin n) :=
  (Tuple.sort g).symm

/-- Card `c` begins a rising sequence of the ordering `σ`: it is card `0`, or card `c - 1` lies to its
right (so the run of consecutive cards `0, 1, ..., c` is broken before `c`). -/
def IsRisingStart {n : ℕ} (σ : Equiv.Perm (Fin n)) (c : Fin n) : Prop :=
  c.val = 0 ∨ ∃ c' : Fin n, c'.val + 1 = c.val ∧ σ.symm c < σ.symm c'

instance {n : ℕ} (σ : Equiv.Perm (Fin n)) : DecidablePred (IsRisingStart σ) := fun c => by
  unfold IsRisingStart; infer_instance

/-- The number of rising sequences of an ordering `σ` of `n` cards (Grinstead–Snell §3.3): a rising
sequence is a maximal subsequence of consecutive cards in increasing positions; they are counted by their
smallest cards. -/
def risingSequences {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ := #{c : Fin n | IsRisingStart σ c}

/-- The Eulerian number `A(n, r)`: the number of orderings of `n` cards with exactly `r` rising sequences
(Grinstead–Snell §3.3). -/
def eulerianNumber (n r : ℕ) : ℕ := #{σ : Equiv.Perm (Fin n) | risingSequences σ = r}

namespace Shuffles

variable {n : ℕ} {α : Type*} [LinearOrder α]

/-- Adjacent form of "monotone and stable". -/
theorem mono_stable_iff_adj (g : Fin n → α) (w : Equiv.Perm (Fin n)) :
    (Monotone (g ∘ w) ∧ IsStable g w) ↔ ∀ c c' : Fin n, c'.val + 1 = c.val →
      g (w c') < g (w c) ∨ (g (w c') = g (w c) ∧ w c' < w c) := by
  constructor
  · rintro ⟨hm, hs⟩ c c' hcc
    have hle : c' ≤ c := by rw [Fin.le_def]; omega
    have h1 : g (w c') ≤ g (w c) := hm hle
    rcases h1.lt_or_eq with h | h
    · exact Or.inl h
    · refine Or.inr ⟨h, lt_of_le_of_ne (hs hle h) (w.injective.ne ?_)⟩
      intro e; rw [Fin.ext_iff] at e; omega
  · intro h
    have key : ∀ d : ℕ, ∀ i j : Fin n, i.val + d + 1 = j.val →
        toLex (g (w i), w i) < toLex (g (w j), w j) := by
      intro d
      induction d with
      | zero =>
        intro i j hij
        rw [Prod.Lex.toLex_lt_toLex]
        exact h j i (by omega)
      | succ d ih =>
        intro i j hij
        have hm : i.val + 1 < n := by omega
        refine lt_trans (b := toLex (g (w ⟨i.val + 1, hm⟩), w ⟨i.val + 1, hm⟩)) ?_ ?_
        · rw [Prod.Lex.toLex_lt_toLex]
          exact h ⟨i.val + 1, hm⟩ i rfl
        · exact ih ⟨i.val + 1, hm⟩ j (by simp only; omega)
    have hlt : ∀ i j : Fin n, i < j →
        g (w i) < g (w j) ∨ (g (w i) = g (w j) ∧ w i < w j) := by
      intro i j hij
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt (Fin.lt_def.1 hij)
      exact Prod.Lex.toLex_lt_toLex.1 (key d i j (by omega))
    refine ⟨fun i j hij => ?_, fun i j hij hg => ?_⟩
    · rcases hij.lt_or_eq with hl | rfl
      · rcases hlt i j hl with h | h
        · exact h.le
        · exact h.1.le
      · exact le_rfl
    · rcases hij.lt_or_eq with hl | rfl
      · rcases hlt i j hl with h | h
        · exact absurd hg h.ne
        · exact h.2.le
      · exact le_rfl

/-- The ordering of the shuffle `g` is `σ` iff `g ∘ σ⁻¹` is, for adjacent cards, lexicographically
increasing together with the position. -/
theorem shuffleOrdering_eq_iff (g : Fin n → α) (σ : Equiv.Perm (Fin n)) :
    shuffleOrdering g = σ ↔ ∀ c c' : Fin n, c'.val + 1 = c.val →
      g (σ.symm c') < g (σ.symm c) ∨ (g (σ.symm c') = g (σ.symm c) ∧ σ.symm c' < σ.symm c) := by
  rw [← mono_stable_iff_adj, ← Tuple.eq_sort_iff]
  unfold shuffleOrdering
  constructor
  · intro h; rw [← h]; simp
  · intro h; rw [← h]; simp

/-- A function on `Fin n` that increases at each step is strictly monotone. -/
theorem strictMono_of_adj {β : Type*} [Preorder β] (f : Fin n → β)
    (h : ∀ c c' : Fin n, c'.val + 1 = c.val → f c' < f c) : StrictMono f := by
  have key : ∀ d : ℕ, ∀ i j : Fin n, i.val + d + 1 = j.val → f i < f j := by
    intro d
    induction d with
    | zero => intro i j hij; exact h j i (by omega)
    | succ d ih =>
      intro i j hij
      have hm : i.val + 1 < n := by omega
      exact lt_trans (h ⟨i.val + 1, hm⟩ i rfl) (ih ⟨i.val + 1, hm⟩ j (by simp only; omega))
  intro i j hij
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt (Fin.lt_def.1 hij)
  exact key d i j (by omega)

/-- A strictly increasing `ℕ`-valued function on `Fin n` grows by at least the index gap. -/
theorem add_le_of_strictMono {u : Fin n → ℕ} (hu : StrictMono u) :
    ∀ k : ℕ, ∀ c d : Fin n, c.val + k = d.val → u c + k ≤ u d := by
  intro k
  induction k with
  | zero => intro c d h; have : c = d := Fin.ext (by omega); subst this; simp
  | succ k ih =>
    intro c d h
    have hm : c.val + 1 < n := by omega
    have h1 : u c < u ⟨c.val + 1, hm⟩ := hu (by simp [Fin.lt_def])
    have h2 := ih ⟨c.val + 1, hm⟩ d (by simp only; omega)
    omega

/-- The number of strictly increasing sequences of length `n` in `{0, ..., M - 1}` is `C(M, n)`. -/
theorem card_strictMono (n M : ℕ) :
    #{u ∈ Fintype.piFinset (fun _ : Fin n => range M) | StrictMono u} = M.choose n := by
  have hc : (powersetCard n (range M)).card = M.choose n := by simp
  rw [← hc]
  refine Finset.card_bij (fun u _ => univ.image u) ?_ ?_ ?_
  · intro u hu
    rw [mem_filter, Fintype.mem_piFinset] at hu
    rw [mem_powersetCard]
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨c, _, rfl⟩ := mem_image.1 hx
      exact hu.1 c
    · rw [card_image_of_injective _ hu.2.injective]; simp
  · intro u1 hu1 u2 hu2 heq
    rw [mem_filter] at hu1 hu2
    have hcard : (univ.image u1).card = n := by
      rw [card_image_of_injective _ hu1.2.injective]; simp
    have e1 := orderEmbOfFin_unique hcard (fun x => mem_image_of_mem u1 (mem_univ x)) hu1.2
    have e2 := orderEmbOfFin_unique hcard
      (fun x => heq ▸ mem_image_of_mem u2 (mem_univ x)) hu2.2
    exact e1.trans e2.symm
  · intro s hs
    rw [mem_powersetCard] at hs
    refine ⟨fun c => s.orderEmbOfFin hs.2 c, ?_, ?_⟩
    · rw [mem_filter, Fintype.mem_piFinset]
      refine ⟨fun c => ?_, (s.orderEmbOfFin hs.2).strictMono⟩
      exact mem_range.2 (mem_range.1 (hs.1 (s.orderEmbOfFin_mem hs.2 c)))
    · ext x
      rw [mem_image]
      constructor
      · rintro ⟨c, _, rfl⟩; exact s.orderEmbOfFin_mem hs.2 c
      · intro hx
        have : x ∈ Set.range (s.orderEmbOfFin hs.2) := by rw [range_orderEmbOfFin]; exact hx
        obtain ⟨c, rfl⟩ := this
        exact ⟨c, mem_univ _, rfl⟩

/-- Admissibility: `h` increases by at least `e (c)` from card `c - 1` to card `c`. -/
def Adm (e : ℕ → ℕ) (h : Fin n → ℕ) : Prop :=
  ∀ c c' : Fin n, c'.val + 1 = c.val → h c' + e c.val ≤ h c

open Classical in
noncomputable instance (e : ℕ → ℕ) : DecidablePred (Adm e : (Fin n → ℕ) → Prop) :=
  fun _ => Classical.propDecidable _

/-- Prefix sums `e 0 + ... + e k`. -/
def pre (e : ℕ → ℕ) (k : ℕ) : ℕ := ∑ i ∈ range (k + 1), e i

theorem pre_succ (e : ℕ → ℕ) (k : ℕ) : pre e (k + 1) = pre e k + e (k + 1) :=
  sum_range_succ _ _

theorem pre_mono (e : ℕ → ℕ) {k m : ℕ} (h : k ≤ m) : pre e k ≤ pre e m :=
  sum_le_sum_of_subset (range_mono (by omega))

theorem pre_le_of_adm {e : ℕ → ℕ} (he0 : e 0 = 0) {h : Fin n → ℕ} (hadm : Adm e h) :
    ∀ k : ℕ, ∀ hk : k < n, pre e k ≤ h ⟨k, hk⟩ := by
  intro k
  induction k with
  | zero => intro hk; simp [pre, he0]
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have h2 := hadm ⟨k + 1, hk⟩ ⟨k, by omega⟩ rfl
    rw [pre_succ]
    simp only at h2
    omega

theorem card_adm (e : ℕ → ℕ) (he0 : e 0 = 0) (n a : ℕ) :
    #{h ∈ Fintype.piFinset (fun _ : Fin n => range a) | Adm e h} =
      (n + a - 1 - ∑ i ∈ range n, e i).choose n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Adm]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hE : ∑ i ∈ range (m + 1), e i = pre e m := rfl
  rw [hE, ← card_strictMono (m + 1) (m + 1 + a - 1 - pre e m)]
  have hlast : m < m + 1 := Nat.lt_succ_self m
  refine Finset.card_nbij' (fun h c => h c + c - pre e c) (fun u c => u c + pre e c - c) ?_ ?_ ?_ ?_
  · intro h hh
    rw [Finset.mem_coe, mem_filter, Fintype.mem_piFinset] at hh
    rw [Finset.mem_coe, mem_filter, Fintype.mem_piFinset]
    obtain ⟨hb, hadm⟩ := hh
    have hge := pre_le_of_adm he0 hadm
    have hmono : StrictMono (fun c : Fin (m + 1) => h c + c - pre e c) := by
      refine strictMono_of_adj _ fun c c' hcc => ?_
      have h1 : pre e c'.val ≤ h c' := hge c' c'.2
      have h2 : pre e c.val ≤ h c := hge c c.2
      have h3 := hadm c c' hcc
      have h4 : pre e c.val = pre e c'.val + e c.val := by
        rw [← hcc, pre_succ]
      omega
    refine ⟨fun c => ?_, hmono⟩
    have hc : c ≤ (⟨m, hlast⟩ : Fin (m + 1)) := by rw [Fin.le_def]; simp only; omega
    have h1 := hmono.monotone hc
    have h2 : pre e m ≤ h ⟨m, hlast⟩ := hge m hlast
    have h3 := mem_range.1 (hb ⟨m, hlast⟩)
    have hpm : pre e c.val ≤ pre e m := pre_mono e (by omega)
    beta_reduce at h1
    rw [mem_range]
    beta_reduce
    simp only at h1 h2 h3
    omega
  · intro u hu
    rw [Finset.mem_coe, mem_filter, Fintype.mem_piFinset] at hu
    rw [Finset.mem_coe, mem_filter, Fintype.mem_piFinset]
    obtain ⟨hb, hmono⟩ := hu
    have h0 : ∀ c : Fin (m + 1), c.val ≤ u c := fun c => by
      have := add_le_of_strictMono hmono c.val ⟨0, hn⟩ c (by simp)
      omega
    have hl : ∀ c : Fin (m + 1), u c + (m - c.val) ≤ u ⟨m, hlast⟩ := fun c =>
      add_le_of_strictMono hmono (m - c.val) c ⟨m, hlast⟩ (by simp only; omega)
    have hM := mem_range.1 (hb ⟨m, hlast⟩)
    have hpm := fun c : Fin (m + 1) => pre_mono e (show c.val ≤ m by omega)
    refine ⟨fun c => ?_, ?_⟩
    · rw [mem_range]
      have := hl c; have := h0 c; have := hpm c
      beta_reduce
      omega
    · intro c c' hcc
      have h4 : pre e c.val = pre e c'.val + e c.val := by
        rw [← hcc, pre_succ]
      have h5 := hmono (show c' < c by rw [Fin.lt_def]; omega)
      have := h0 c; have := h0 c'
      beta_reduce
      omega
  · intro h hh
    rw [Finset.mem_coe, mem_filter] at hh
    have hge := pre_le_of_adm he0 hh.2
    funext c
    have : pre e c.val ≤ h c := hge c c.2
    beta_reduce
    omega
  · intro u hu
    rw [Finset.mem_coe, mem_filter] at hu
    have h0 : ∀ c : Fin (m + 1), c.val ≤ u c := fun c => by
      have := add_le_of_strictMono hu.2 c.val ⟨0, hn⟩ c (by simp)
      omega
    funext c
    have := h0 c
    beta_reduce
    omega

/-- `1` if card `k` lies to the left of card `k - 1` in `σ` (a rising sequence breaks before `k`), else `0`;
`0` out of range. -/
def breakFn (σ : Equiv.Perm (Fin n)) (k : ℕ) : ℕ :=
  if hk : 0 < k ∧ k < n then (if σ.symm ⟨k, hk.2⟩ < σ.symm ⟨k - 1, by omega⟩ then 1 else 0) else 0

theorem breakFn_zero (σ : Equiv.Perm (Fin n)) : breakFn σ 0 = 0 := by simp [breakFn]

theorem breakFn_le (σ : Equiv.Perm (Fin n)) (k : ℕ) : breakFn σ k ≤ 1 := by
  unfold breakFn; split_ifs <;> omega

theorem breakFn_eq (σ : Equiv.Perm (Fin n)) {c c' : Fin n} (hcc : c'.val + 1 = c.val) :
    breakFn σ c.val = if σ.symm c < σ.symm c' then 1 else 0 := by
  have hk : 0 < c.val ∧ c.val < n := ⟨by omega, c.2⟩
  have : c' = ⟨c.val - 1, by omega⟩ := Fin.ext (by simp only; omega)
  rw [this]
  simp only [breakFn, hk, and_self, dite_true, Fin.eta]

theorem isRisingStart_iff (σ : Equiv.Perm (Fin n)) (c : Fin n) :
    IsRisingStart σ c ↔ c.val = 0 ∨ breakFn σ c.val = 1 := by
  unfold IsRisingStart
  refine or_congr_right ⟨?_, ?_⟩
  · rintro ⟨c', hcc, h⟩
    rw [breakFn_eq σ hcc, ite_eq_left_iff.2 (fun h2 => absurd h h2)]
  · intro h
    by_cases h0 : c.val = 0
    · simp [breakFn, h0] at h
    · have hcc : (⟨c.val - 1, by omega⟩ : Fin n).val + 1 = c.val := by simp only; omega
      refine ⟨⟨c.val - 1, by omega⟩, hcc, ?_⟩
      rw [breakFn_eq σ hcc] at h
      by_contra hn
      rw [if_neg hn] at h
      exact absurd h (by omega)

theorem risingSequences_eq (σ : Equiv.Perm (Fin n)) (hn : 0 < n) :
    risingSequences σ = 1 + ∑ i ∈ range n, breakFn σ i := by
  unfold risingSequences
  simp only [isRisingStart_iff]
  rw [filter_or, card_union_of_disjoint]
  · have h1 : #{c : Fin n | c.val = 0} = 1 := by
      rw [card_eq_one]
      exact ⟨⟨0, hn⟩, by ext c; simp [Fin.ext_iff]⟩
    rw [h1, ← Fin.sum_univ_eq_sum_range (fun i => breakFn σ i) n]
    congr 1
    rw [card_filter]
    refine sum_congr rfl fun c _ => ?_
    have := breakFn_le σ c.val
    split_ifs <;> omega
  · rw [disjoint_filter]
    intro c _ h0 h1
    rw [h0, breakFn_zero] at h1
    exact absurd h1 (by omega)

theorem one_le_risingSequences (σ : Equiv.Perm (Fin n)) (hn : 0 < n) : 1 ≤ risingSequences σ := by
  rw [risingSequences_eq σ hn]; omega

theorem risingSequences_le (σ : Equiv.Perm (Fin n)) : risingSequences σ ≤ n := by
  unfold risingSequences
  calc _ ≤ #(univ : Finset (Fin n)) := card_le_univ _
    _ = n := by simp

theorem cond_iff (σ : Equiv.Perm (Fin n)) {a : ℕ} (g : Fin n → Fin a) {c c' : Fin n}
    (hcc : c'.val + 1 = c.val) :
    (g (σ.symm c') < g (σ.symm c) ∨ (g (σ.symm c') = g (σ.symm c) ∧ σ.symm c' < σ.symm c)) ↔
      (g (σ.symm c') : ℕ) + breakFn σ c.val ≤ g (σ.symm c) := by
  rw [breakFn_eq σ hcc]
  have hne : σ.symm c' ≠ σ.symm c :=
    σ.symm.injective.ne (by intro e; rw [Fin.ext_iff] at e; omega)
  by_cases hlt : σ.symm c < σ.symm c'
  · have h2 : ¬ σ.symm c' < σ.symm c := not_lt_of_gt hlt
    simp only [hlt, if_true, h2, and_false, or_false]
    rw [Fin.lt_def]; omega
  · have h2 : σ.symm c' < σ.symm c := lt_of_le_of_ne (not_lt.1 hlt) hne
    simp only [hlt, if_false, h2, and_true]
    rw [Fin.lt_def, Fin.ext_iff]; omega

theorem shuffleOrdering_iff_adm (σ : Equiv.Perm (Fin n)) {a : ℕ} (g : Fin n → Fin a) :
    shuffleOrdering g = σ ↔ Adm (breakFn σ) (fun c => ((g (σ.symm c) : Fin a) : ℕ)) := by
  rw [shuffleOrdering_eq_iff]
  refine ⟨fun h c c' hcc => ?_, fun h c c' hcc => ?_⟩
  · exact (cond_iff σ g hcc).1 (h c c' hcc)
  · exact (cond_iff σ g hcc).2 (h c c' hcc)

/-- Number of `a`-shuffles giving the ordering `σ` (core count). -/
theorem card_shuffles (σ : Equiv.Perm (Fin n)) (a : ℕ) :
    #{g : Fin n → Fin a | shuffleOrdering g = σ} = (n + a - risingSequences σ).choose n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : risingSequences σ = 0 := by simp [risingSequences]
    rw [this]
    simp only [Nat.choose_zero_right]
    rw [card_eq_one]
    refine ⟨fun i => i.elim0, ?_⟩
    ext g
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    exact ⟨fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩
  have key := card_adm (breakFn σ) (breakFn_zero σ) n a
  have hr := risingSequences_eq σ hn
  have : n + a - risingSequences σ = n + a - 1 - ∑ i ∈ range n, breakFn σ i := by omega
  rw [this, ← key]
  refine Finset.card_bij (fun g _ => fun c => ((g (σ.symm c) : Fin a) : ℕ)) ?_ ?_ ?_
  · intro g hg
    rw [mem_filter] at hg
    rw [mem_filter, Fintype.mem_piFinset]
    exact ⟨fun c => mem_range.2 (g (σ.symm c)).2, (shuffleOrdering_iff_adm σ g).1 hg.2⟩
  · intro g1 _ g2 _ h
    funext i
    have := congrFun h (σ i)
    simp only [Equiv.symm_apply_apply] at this
    exact Fin.ext this
  · intro h hh
    rw [mem_filter, Fintype.mem_piFinset] at hh
    refine ⟨fun i => ⟨h (σ i), mem_range.1 (hh.1 (σ i))⟩, ?_, ?_⟩
    · rw [mem_filter, shuffleOrdering_iff_adm]
      refine ⟨mem_univ _, ?_⟩
      simpa using hh.2
    · funext c
      simp

/-- Lexicographic order on pairs is the order of `finProdFinEquiv` (first coordinate more significant). -/
theorem finProd_lt_iff {a b : ℕ} (x y : Fin a × Fin b) :
    finProdFinEquiv x < finProdFinEquiv y ↔ x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2) := by
  rw [Fin.lt_def, Fin.lt_def, Fin.ext_iff]
  simp only [finProdFinEquiv, Equiv.coe_fn_mk]
  have hx := x.2.2
  have hy := y.2.2
  constructor
  · intro h
    by_cases h1 : x.1.val < y.1.val
    · exact Or.inl h1
    · by_cases h2 : x.1.val = y.1.val
      · right; refine ⟨h2, ?_⟩; rw [h2] at h; omega
      · exfalso
        have h3 : y.1.val + 1 ≤ x.1.val := by omega
        have := Nat.mul_le_mul_left b h3
        rw [Nat.mul_add] at this
        omega
  · rintro (h | ⟨h, h'⟩)
    · have h3 : x.1.val + 1 ≤ y.1.val := h
      have := Nat.mul_le_mul_left b h3
      rw [Nat.mul_add] at this
      omega
    · rw [h]; omega

/-- The label of the `ab`-shuffle built from an `a`-shuffle `g1` followed by a `b`-shuffle `g2`: position `i`
of the final deck lies in the `g2 i`-th packet of the second shuffle and comes from the `g1`-packet of the
intermediate position `σ₂ i`. -/
def combine {a b : ℕ} (g1 : Fin n → Fin a) (g2 : Fin n → Fin b) : Fin n → Fin (a * b) :=
  fun i => finProdFinEquiv (g1 (shuffleOrdering g2 i), g2 i)

/-- An `a`-shuffle followed by a `b`-shuffle is the `ab`-shuffle with the combined labels. -/
theorem shuffleOrdering_combine {a b : ℕ} (g1 : Fin n → Fin a) (g2 : Fin n → Fin b) :
    shuffleOrdering (combine g1 g2) = shuffleOrdering g1 * shuffleOrdering g2 := by
  rw [shuffleOrdering_eq_iff]
  intro c c' hcc
  have h1 := (shuffleOrdering_eq_iff g1 (shuffleOrdering g1)).1 rfl c c' hcc
  set j' := (shuffleOrdering g1).symm c' with hj'
  set j := (shuffleOrdering g1).symm c with hj
  have hw : ∀ x, (shuffleOrdering g1 * shuffleOrdering g2).symm x =
      (Tuple.sort g2) ((shuffleOrdering g1).symm x) := fun x => rfl
  have hs2 : ∀ x, shuffleOrdering g2 (Tuple.sort g2 x) = x := fun x => by
    simp [shuffleOrdering]
  rw [hw, hw]
  simp only [combine, hs2]
  rw [← hj', ← hj]
  rcases h1 with h | ⟨h, hl⟩
  · left; rw [finProd_lt_iff]; exact Or.inl h
  · have hm : g2 (Tuple.sort g2 j') ≤ g2 (Tuple.sort g2 j) := Tuple.monotone_sort g2 hl.le
    rcases hm.lt_or_eq with hm | hm
    · left; rw [finProd_lt_iff]; exact Or.inr ⟨h, hm⟩
    · right
      refine ⟨by rw [h, hm], ?_⟩
      exact lt_of_le_of_ne (Tuple.isStable_sort g2 hl.le hm)
        ((Tuple.sort g2).injective.ne hl.ne)

theorem combine_bijective (n a b : ℕ) :
    Function.Bijective (fun p : (Fin n → Fin a) × (Fin n → Fin b) => combine p.1 p.2) := by
  constructor
  · rintro ⟨g1, g2⟩ ⟨g1', g2'⟩ h
    have h2 : g2 = g2' := by
      funext i
      have := congrFun h i
      simp only [combine] at this
      exact (Prod.ext_iff.1 (finProdFinEquiv.injective this)).2
    subst h2
    have h1 : g1 = g1' := by
      funext j
      obtain ⟨i, rfl⟩ := (shuffleOrdering g2).surjective j
      have := congrFun h i
      simp only [combine] at this
      exact (Prod.ext_iff.1 (finProdFinEquiv.injective this)).1
    rw [h1]
  · intro g
    refine ⟨(fun j => (finProdFinEquiv.symm (g ((shuffleOrdering fun i => (finProdFinEquiv.symm (g i)).2).symm j))).1,
      fun i => (finProdFinEquiv.symm (g i)).2), ?_⟩
    funext i
    simp only [combine, Equiv.symm_apply_apply, Prod.mk.eta, Equiv.apply_symm_apply]

end Shuffles

open Shuffles in
/-- Grinstead–Snell Theorem 3.9 (PR-033). Pairs consisting of an `a`-shuffle and a `b`-shuffle are in
bijection with the `ab`-shuffles, in such a way that applying the `a`-shuffle and then the `b`-shuffle to the
identity ordering gives the same ordering as the corresponding `ab`-shuffle (the composite of orderings is
the product in the permutation group: position `i` of the final deck holds the card that the intermediate
deck has in position `σ₂ i`). -/
@[kb "grinsteadsnell2006" "Theorem 3.9, p. 130"]
theorem exists_shuffle_pair_equiv (n a b : ℕ) :
    ∃ e : ((Fin n → Fin a) × (Fin n → Fin b)) ≃ (Fin n → Fin (a * b)),
      ∀ p, shuffleOrdering (e p) = shuffleOrdering p.1 * shuffleOrdering p.2 :=
  ⟨Equiv.ofBijective _ (combine_bijective n a b), fun p => shuffleOrdering_combine p.1 p.2⟩

open Shuffles in
/-- Grinstead–Snell Theorem 3.10 (PR-033). An `a`-shuffle followed by a `b`-shuffle produces each
ordering `σ` equally often as an `ab`-shuffle does; hence, all shuffles being equally likely, the two
procedures induce the same distribution on orderings. -/
@[kb "grinsteadsnell2006" "Theorem 3.10, p. 133"]
theorem card_shuffle_pairs_eq (n a b : ℕ) (σ : Equiv.Perm (Fin n)) :
    #{p : (Fin n → Fin a) × (Fin n → Fin b) | shuffleOrdering p.1 * shuffleOrdering p.2 = σ} =
      #{g : Fin n → Fin (a * b) | shuffleOrdering g = σ} := by
  obtain ⟨e, he⟩ := exists_shuffle_pair_equiv n a b
  refine Finset.card_equiv e fun p => ?_
  simp only [mem_filter, mem_univ, true_and, he]

open Shuffles in
/-- Grinstead–Snell Theorem 3.11 (PR-034). If an ordering `σ` of `n` cards has `r` rising sequences,
then exactly `C(n + a - r, n)` of the `a ^ n` cut-interleaving pairs of an `a`-shuffle of the identity
ordering (recorded as the packet function `g : Fin n → Fin a`) produce `σ`. -/
@[kb "grinsteadsnell2006" "Theorem 3.11, p. 134"]
theorem card_shuffles_eq_choose (n a : ℕ) (σ : Equiv.Perm (Fin n)) :
    #{g : Fin n → Fin a | shuffleOrdering g = σ} = (n + a - risingSequences σ).choose n :=
  card_shuffles σ a

open Shuffles in
/-- Grinstead–Snell Theorem 3.12 (PR-035), Worpitzky's identity: for `n ≥ 1`,
`a ^ n = ∑_{r=1}^{a} C(n + a - r, n) A(n, r)`, where `A(n, r)` is the Eulerian number. -/
@[kb "grinsteadsnell2006" "Theorem 3.12, p. 135"]
theorem pow_eq_sum_choose_mul_eulerian (n a : ℕ) (hn : 0 < n) :
    a ^ n = ∑ r ∈ Icc 1 a, (n + a - r).choose n * eulerianNumber n r := by
  have h1 : a ^ n = ∑ σ : Equiv.Perm (Fin n), (n + a - risingSequences σ).choose n := by
    have : (Finset.univ : Finset (Fin n → Fin a)).card = a ^ n := by simp
    rw [← this, card_eq_sum_card_fiberwise (f := shuffleOrdering) (t := univ) (fun _ _ => mem_univ _)]
    exact sum_congr rfl fun σ _ => by
      rw [← card_shuffles σ a]
  rw [h1]
  have h2 : ∑ σ : Equiv.Perm (Fin n), (n + a - risingSequences σ).choose n =
      ∑ r ∈ range (n + a + 1), (n + a - r).choose n * eulerianNumber n r := by
    rw [← sum_fiberwise_of_maps_to (s := univ) (t := range (n + a + 1)) (g := risingSequences)
      (fun σ _ => mem_range.2 (by have := risingSequences_le σ; omega))]
    refine sum_congr rfl fun r _ => ?_
    have hc : ∀ σ ∈ ({σ : Equiv.Perm (Fin n) | risingSequences σ = r} : Finset _),
        (n + a - risingSequences σ).choose n = (n + a - r).choose n :=
      fun σ hσ => by rw [(mem_filter.1 hσ).2]
    rw [sum_congr rfl hc, sum_const, smul_eq_mul, eulerianNumber, mul_comm]
  rw [h2]
  symm
  refine sum_subset (fun r hr => ?_) (fun r hr hr' => ?_)
  · rw [mem_Icc] at hr; rw [mem_range]; omega
  · rw [mem_range] at hr
    rw [mem_Icc] at hr'
    by_cases h0 : r = 0
    · have : eulerianNumber n r = 0 := by
        rw [eulerianNumber, card_eq_zero, filter_eq_empty_iff]
        intro σ _
        have := one_le_risingSequences σ hn
        omega
      rw [this, mul_zero]
    · have : (n + a - r).choose n = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [this, zero_mul]

end UndergradKB.Probability
