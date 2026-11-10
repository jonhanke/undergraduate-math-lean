import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Rat.Floor
import UndergradKB.Common.Attr

/-!
# Hamiltonian graphs (Keller–Trotter, Chapter 5.3)

Dirac's theorem (Theorem 5.18): a graph on `n ≥ 3` vertices in which every vertex has at least
`⌈n/2⌉` neighbours is hamiltonian.  (For `n = 2` the complete graph `K₂` satisfies the degree
condition but, with Mathlib's convention that a hamiltonian cycle is a genuine cycle, is not
hamiltonian; so `3 ≤ n` is needed.)

The proof follows the book: take a longest path, rotate it into a cycle on the same vertices by a
pigeonhole argument, and extend using connectivity.  Paths are represented by injective
functions `f : ℕ → V` on `{0, …, t-1}` with consecutive vertices adjacent.
-/

namespace UndergradKB.Combinatorics.Hamilton

open SimpleGraph

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- `f` lists a path on the `t` vertices `f 0, …, f (t-1)`. -/
def IsPathFn (G : SimpleGraph V) (t : ℕ) (f : ℕ → V) : Prop :=
  Set.InjOn f (Set.Iio t) ∧ ∀ i, i + 1 < t → G.Adj (f i) (f (i + 1))

lemma IsPathFn.card_le {t : ℕ} {f : ℕ → V} (h : IsPathFn G t f) : t ≤ Fintype.card V := by
  have := Finset.card_image_of_injOn (s := Finset.range t) (f := f) (by simpa using h.1)
  rw [← Finset.card_range t, ← this]
  exact Finset.card_le_univ _

lemma IsPathFn.extend_front {t : ℕ} {f : ℕ → V} (h : IsPathFn G t f) (y : V)
    (hy : y ∉ f '' Set.Iio t) (hadj : G.Adj y (f 0)) :
    IsPathFn G (t + 1) (fun j => if j = 0 then y else f (j - 1)) := by
  refine ⟨?_, ?_⟩
  · intro a ha b hb hab
    simp only [Set.mem_Iio] at ha hb
    simp only at hab
    split_ifs at hab with h1 h2 h2
    · omega
    · exact absurd ⟨b - 1, by simp; omega, hab.symm⟩ hy
    · exact absurd ⟨a - 1, by simp; omega, hab⟩ hy
    · have := h.1 (by simp; omega) (by simp; omega) hab
      omega
  · intro i hi
    simp only
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simpa using hadj
    · have := h.2 (i - 1) (by omega)
      rw [if_neg (by omega), if_neg (by omega)]
      have e : i + 1 - 1 = i - 1 + 1 := by omega
      rw [e]
      exact this

lemma IsPathFn.extend_back {t : ℕ} {f : ℕ → V} (h : IsPathFn G t f) (y : V)
    (hy : y ∉ f '' Set.Iio t) (ht : 0 < t) (hadj : G.Adj (f (t - 1)) y) :
    IsPathFn G (t + 1) (fun j => if j < t then f j else y) := by
  refine ⟨?_, ?_⟩
  · intro a ha b hb hab
    simp only [Set.mem_Iio] at ha hb
    simp only at hab
    split_ifs at hab with h1 h2 h2
    · exact h.1 h1 h2 hab
    · exact absurd ⟨a, h1, hab⟩ hy
    · exact absurd ⟨b, h2, hab.symm⟩ hy
    · omega
  · intro i hi
    simp only
    by_cases h1 : i + 1 < t
    · rw [if_pos (by omega), if_pos h1]
      exact h.2 i h1
    · have : i = t - 1 := by omega
      subst this
      rw [if_pos (by omega), if_neg (by omega)]
      exact hadj

/-- Rotation (the pigeonhole step of the book): in a longest path all neighbours of both
endpoints lie on the path, and then the path closes up into a cycle on the same vertices. -/
lemma exists_cycle_of_longest {n t : ℕ} (hn : n = Fintype.card V)
    (hdeg : ∀ v, n ≤ 2 * G.degree v) {f : ℕ → V} (hf : IsPathFn G t f) (ht : 0 < t)
    (hmax : ∀ s (g : ℕ → V), IsPathFn G s g → s ≤ t) :
    ∃ g : ℕ → V, IsPathFn G t g ∧ g '' Set.Iio t = f '' Set.Iio t ∧ G.Adj (g (t - 1)) (g 0) := by
  have hinj : Set.InjOn f ↑(Finset.range t) := by simpa using hf.1
  set A := (Finset.range t).filter (fun i => G.Adj (f 0) (f i)) with hA
  set B := (Finset.range t).filter (fun i => G.Adj (f i) (f (t - 1))) with hB
  have hAcard : A.card = G.degree (f 0) := by
    rw [← card_neighborFinset_eq_degree, ← Finset.card_image_of_injOn (f := f)
      (hinj.mono (by intro x hx; simp only [hA, Finset.coe_filter] at hx; exact hx.1))]
    congr 1
    ext y
    symm
    simp only [hA, mem_neighborFinset, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hy
      by_cases hmem : y ∈ f '' Set.Iio t
      · obtain ⟨i, hi, rfl⟩ := hmem
        exact ⟨i, ⟨hi, hy⟩, rfl⟩
      · exfalso
        have := hmax _ _ (hf.extend_front y hmem hy.symm)
        omega
    · rintro ⟨i, ⟨_, hi⟩, rfl⟩
      exact hi
  have hBcard : B.card = G.degree (f (t - 1)) := by
    rw [← card_neighborFinset_eq_degree, ← Finset.card_image_of_injOn (f := f)
      (hinj.mono (by intro x hx; simp only [hB, Finset.coe_filter] at hx; exact hx.1))]
    congr 1
    ext y
    symm
    simp only [hB, mem_neighborFinset, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hy
      by_cases hmem : y ∈ f '' Set.Iio t
      · obtain ⟨i, hi, rfl⟩ := hmem
        exact ⟨i, ⟨hi, hy.symm⟩, rfl⟩
      · exfalso
        have := hmax _ _ (hf.extend_back y hmem ht hy)
        omega
    · rintro ⟨i, ⟨_, hi⟩, rfl⟩
      exact hi.symm
  have hle := hf.card_le
  -- the pigeonhole
  obtain ⟨i, hiB, hiA⟩ : ∃ i, i ∈ B ∧ i + 1 ∈ A := by
    by_contra hcon
    push Not at hcon
    have hA0 : ∀ a ∈ A, 1 ≤ a := by
      intro a ha
      by_contra h0
      have : a = 0 := by omega
      subst this
      simp only [hA, Finset.mem_filter] at ha
      exact G.loopless.irrefl _ ha.2
    have hAimg : (A.image (fun a => a - 1)).card = A.card :=
      Finset.card_image_of_injOn (by intro a ha b hb hab; have := hA0 a ha; have := hA0 b hb
                                     simp only at hab; omega)
    have hsub1 : A.image (fun a => a - 1) ⊆ Finset.range (t - 1) := by
      intro x hx
      simp only [Finset.mem_image, hA, Finset.mem_filter, Finset.mem_range] at hx ⊢
      obtain ⟨a, ⟨ha, _⟩, rfl⟩ := hx
      have : a ≠ 0 := by
        rintro rfl
        simp only [hA, Finset.mem_filter] at *
        exact G.loopless.irrefl _ ‹G.Adj (f 0) (f 0)›
      omega
    have hsub2 : B ⊆ Finset.range (t - 1) := by
      intro x hx
      simp only [hB, Finset.mem_filter, Finset.mem_range] at hx ⊢
      have : x ≠ t - 1 := by
        rintro rfl
        exact G.loopless.irrefl _ hx.2
      omega
    have hdisj : Disjoint (A.image (fun a => a - 1)) B := by
      rw [Finset.disjoint_left]
      intro x hx hxB
      obtain ⟨a, haA, rfl⟩ := Finset.mem_image.mp hx
      have := hA0 a haA
      have := hcon (a - 1) hxB
      rw [Nat.sub_add_cancel ‹1 ≤ a›] at this
      exact this haA
    have := Finset.card_union_of_disjoint hdisj
    have h3 := Finset.card_le_card (Finset.union_subset hsub1 hsub2)
    rw [Finset.card_range] at h3
    have := hdeg (f 0)
    have := hdeg (f (t - 1))
    omega
  simp only [hA, hB, Finset.mem_filter, Finset.mem_range] at hiA hiB
  obtain ⟨hiB1, hiB2⟩ := hiB
  obtain ⟨hiA1, hiA2⟩ := hiA
  have hit : i + 1 ≤ t - 1 := by omega
  let σ : ℕ → ℕ := fun j => if j ≤ i then j else t + i - j
  have hσlt : ∀ j, j < t → σ j < t := by
    intro j hj; simp only [σ]; split_ifs <;> omega
  have hσinj : ∀ j k, j < t → k < t → σ j = σ k → j = k := by
    intro j k hj hk h; simp only [σ] at h; split_ifs at h <;> omega
  have hσsurj : ∀ m, m < t → ∃ j, j < t ∧ σ j = m := by
    intro m hm
    by_cases hmi : m ≤ i
    · exact ⟨m, hm, by simp [σ, hmi]⟩
    · exact ⟨t + i - m, by omega, by simp only [σ]; split_ifs <;> omega⟩
  refine ⟨fun j => f (σ j), ⟨?_, ?_⟩, ?_, ?_⟩
  · intro a ha b hb hab
    exact hσinj a b ha hb (hf.1 (hσlt a ha) (hσlt b hb) hab)
  · intro j hj
    simp only [σ]
    by_cases h1 : j + 1 ≤ i
    · rw [if_pos (by omega), if_pos h1]
      exact hf.2 j (by omega)
    · by_cases h2 : j = i
      · subst h2
        rw [if_pos le_rfl, if_neg (by omega)]
        have e : t + j - (j + 1) = t - 1 := by omega
        rw [e]
        exact hiB2
      · rw [if_neg (by omega), if_neg (by omega)]
        have e : t + i - j = (t + i - (j + 1)) + 1 := by omega
        rw [e]
        exact (hf.2 _ (by omega)).symm
  · ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨σ j, hσlt j hj, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      obtain ⟨j, hj, hjm⟩ := hσsurj m hm
      exact ⟨j, hj, by simp only [hjm]⟩
  · simp only [σ]
    rw [if_neg (by omega), if_pos (by omega)]
    have e : t + i - (t - 1) = i + 1 := by omega
    rw [e]
    exact hiA2.symm

lemma succ_mod_cases (t m : ℕ) (ht : 0 < t) :
    ((m + 1) % t = m % t + 1 ∧ m % t + 1 < t) ∨ (m % t + 1 = t ∧ (m + 1) % t = 0) := by
  have hlt := Nat.mod_lt m ht
  have hdm := Nat.div_add_mod m t
  by_cases h : m % t + 1 = t
  · right
    refine ⟨h, ?_⟩
    apply Nat.mod_eq_zero_of_dvd
    exact ⟨m / t + 1, by rw [mul_add, mul_one]; omega⟩
  · left
    have h2 : m % t + 1 < t := by omega
    refine ⟨?_, h2⟩
    have : m + 1 = (m % t + 1) + t * (m / t) := by omega
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2]

/-- A graph all of whose vertices have degree at least `n / 2` (with `n` the number of vertices)
is connected. -/
lemma connected_of_half_degree {n : ℕ} (hn : n = Fintype.card V) (hne : Nonempty V)
    (hdeg : ∀ v, n ≤ 2 * G.degree v) : G.Connected := by
  have hpre : G.Preconnected := by
    intro a b
    by_cases hab : a = b
    · subst hab; exact Reachable.refl _
    by_cases hadj : G.Adj a b
    · exact hadj.reachable
    have hsub : G.neighborFinset a ∪ G.neighborFinset b ⊆ (Finset.univ.erase a).erase b := by
      intro x hx
      simp only [Finset.mem_union, mem_neighborFinset] at hx
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      rcases hx with hx | hx
      · exact ⟨fun h => hadj (h ▸ hx), hx.ne.symm⟩
      · exact ⟨hx.ne.symm, fun h => hadj (h ▸ hx.symm)⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (by simp [Ne.symm hab]), Finset.card_erase_of_mem (by simp),
      Finset.card_univ, ← hn] at hc
    have h1 := Finset.card_union_add_card_inter (G.neighborFinset a) (G.neighborFinset b)
    have h2 := hdeg a
    have h3 := hdeg b
    rw [← card_neighborFinset_eq_degree] at h2 h3
    have h4 : 1 < Fintype.card V := Fintype.one_lt_card_iff.mpr ⟨a, b, hab⟩
    have hpos : 0 < (G.neighborFinset a ∩ G.neighborFinset b).card := by omega
    obtain ⟨c, hc'⟩ := Finset.card_pos.mp hpos
    simp only [Finset.mem_inter, mem_neighborFinset] at hc'
    exact (hc'.1.reachable).trans hc'.2.reachable.symm
  exact { preconnected := hpre, nonempty := hne }

/-- If `S` is closed under adjacency in a connected graph and nonempty, it is everything. -/
lemma mem_of_closed {S : Set V} (hS : ∀ d ∈ S, ∀ c, G.Adj d c → c ∈ S) {a b : V}
    (q : G.Walk a b) (ha : a ∈ S) : b ∈ S := by
  induction q with
  | nil => exact ha
  | cons h _ ih => exact ih (hS _ ha _ h)

/-- The cyclic structure obtained from a Hamiltonian-sized cycle in function form. -/
lemma cycleGraph_adj_cases {n : ℕ} (hn : 3 ≤ n) {u v : Fin n} (h : (u - v).val = 1) :
    u.val = v.val + 1 ∨ (u.val = 0 ∧ v.val + 1 = n) := by
  rw [Fin.val_sub] at h
  have hu := u.isLt
  have hv := v.isLt
  by_cases hlt : n - v.val + u.val < n
  · rw [Nat.mod_eq_of_lt hlt] at h
    omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h
    omega

/-- Dirac's theorem in the form `n ≤ 2 · degree`. -/
theorem dirac_aux (hn3 : 3 ≤ Fintype.card V) (hdeg : ∀ v, Fintype.card V ≤ 2 * G.degree v) :
    G.IsHamiltonian := by
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hconn := connected_of_half_degree rfl hne hdeg
  -- a longest path
  let S : Set ℕ := {t | ∃ f, IsPathFn G t f ∧ 1 ≤ t}
  obtain ⟨x⟩ := hne
  have hSne : S.Nonempty := ⟨1, fun _ => x, ⟨by intro a ha b hb _; simp at ha hb; omega,
    by intro i hi; omega⟩, le_rfl⟩
  have hSb : BddAbove S := ⟨Fintype.card V, by rintro t ⟨f, hf, -⟩; exact hf.card_le⟩
  obtain ⟨f, hf, ht⟩ := Nat.sSup_mem hSne hSb
  set t := sSup S with htdef
  have hmax : ∀ s (g : ℕ → V), IsPathFn G s g → s ≤ t := by
    intro s g hg
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · exact Nat.zero_le _
    · exact le_csSup hSb ⟨g, hg, hs⟩
  obtain ⟨g, hg, himg, hwrap⟩ := exists_cycle_of_longest rfl hdeg hf (by omega) hmax
  have htn : t = Fintype.card V := by
    by_contra htn
    have hlt : t < Fintype.card V := lt_of_le_of_ne hf.card_le htn
    -- some vertex is off the path
    have hoff : ∃ y, y ∉ g '' Set.Iio t := by
      by_contra hcon
      push Not at hcon
      have : Finset.card ((Finset.range t).image g) = t := by
        rw [Finset.card_image_of_injOn (by simpa using hg.1), Finset.card_range]
      have h2 : (Finset.range t).image g = Finset.univ := by
        ext y
        simp only [Finset.mem_image, Finset.mem_range, Finset.mem_univ, iff_true]
        obtain ⟨i, hi, hiy⟩ := hcon y
        exact ⟨i, hi, hiy⟩
      rw [h2, Finset.card_univ] at this
      omega
    -- ... and, by connectivity, one adjacent to the path
    have hadj : ∃ y, y ∉ g '' Set.Iio t ∧ ∃ j, j < t ∧ G.Adj (g j) y := by
      by_contra hcon
      push Not at hcon
      obtain ⟨y, hy⟩ := hoff
      obtain ⟨q⟩ := hconn.preconnected (g 0) y
      refine hy (mem_of_closed (S := g '' Set.Iio t) ?_ q ⟨0, by simp; omega, rfl⟩)
      rintro d ⟨j, hj, rfl⟩ c hc
      by_contra hcn
      exact hcon c hcn j hj hc
    obtain ⟨y, hy, j, hj, hjy⟩ := hadj
    have ht0 : 0 < t := by omega
    -- the rotated path starting at `y`
    let h : ℕ → V := fun k => if k = 0 then y else g ((j + (k - 1)) % t)
    have hpath : IsPathFn G (t + 1) h := by
      refine ⟨?_, ?_⟩
      · intro a ha b hb hab
        simp only [Set.mem_Iio] at ha hb
        simp only [h] at hab
        split_ifs at hab with h1 h2 h2
        · omega
        · exact absurd ⟨_, Nat.mod_lt _ ht0, hab.symm⟩ hy
        · exact absurd ⟨_, Nat.mod_lt _ ht0, hab⟩ hy
        · have := hg.1 (Nat.mod_lt _ ht0) (Nat.mod_lt _ ht0) hab
          have h4 : (j + (a - 1)) ≡ (j + (b - 1)) [MOD t] := this
          have h5 := Nat.ModEq.add_left_cancel' j h4
          rw [Nat.ModEq, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h5
          omega
      · intro i hi
        simp only [h]
        rcases Nat.eq_zero_or_pos i with rfl | hi0
        · simp only [if_true, Nat.zero_add, ne_eq, one_ne_zero, if_false, Nat.sub_self, add_zero]
          rw [Nat.mod_eq_of_lt hj]
          exact hjy.symm
        · rw [if_neg (by omega), if_neg (by omega)]
          have e : i + 1 - 1 = (i - 1) + 1 := by omega
          rw [e, ← add_assoc]
          rcases succ_mod_cases t (j + (i - 1)) ht0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [h1]; exact hg.2 _ h2
          · rw [h2]
            have : (j + (i - 1)) % t = t - 1 := by omega
            rw [this]
            exact hwrap
    have := hmax _ _ hpath
    omega
  -- conclude
  rw [isHamiltonian_iff_cycleGraph_isContained hn3, ← htn]
  obtain ⟨m, hm⟩ : ∃ m, t = m + 3 := ⟨t - 3, by omega⟩
  refine ⟨⟨⟨fun i => g i.val, ?_⟩, ?_⟩⟩
  · intro u v huv
    rw [cycleGraph_adj'] at huv
    rcases huv with h1 | h1
    · rcases cycleGraph_adj_cases (by omega) h1 with h2 | ⟨h2, h3⟩
      · have := hg.2 v.val (by have := u.isLt; omega)
        rw [h2]; exact this.symm
      · have e : v.val = t - 1 := by omega
        simp only [h2, e]
        exact hwrap.symm
    · rcases cycleGraph_adj_cases (by omega) h1 with h2 | ⟨h2, h3⟩
      · have := hg.2 u.val (by have := v.isLt; omega)
        rw [h2]; exact this
      · have e : u.val = t - 1 := by omega
        simp only [h2, e]
        exact hwrap
  · intro u v huv
    apply Fin.ext
    exact hg.1 (by have := u.isLt; simpa [← htn] using this)
      (by have := v.isLt; simpa [← htn] using this) huv

/-- CO-102. Dirac's theorem (Theorem 5.18): a graph on `n` vertices in which every vertex has at
least `⌈n/2⌉` neighbours is hamiltonian.  The book's statement tacitly assumes `n ≥ 3` (for `n = 2`
the graph `K₂` meets the degree condition but has no cycle). -/
@[kb "kellertrotter2017" "Theorem 5.18, p. 104"]
theorem dirac (hn3 : 3 ≤ Fintype.card V)
    (hdeg : ∀ v, ⌈(Fintype.card V : ℚ) / 2⌉₊ ≤ G.degree v) : G.IsHamiltonian := by
  refine dirac_aux hn3 fun v => ?_
  have := Nat.ceil_le.mp (hdeg v)
  have h2 : (Fintype.card V : ℚ) ≤ 2 * G.degree v := by linarith
  exact_mod_cast h2

/-! ### The Petersen graph -/

/-- The vertices of the Petersen graph: the 2-element subsets of a 5-element set. -/
abbrev PetersenVertex := {s : Finset (Fin 5) // s.card = 2}

/-- CO-101. The Petersen graph: vertices are the 2-subsets of `{0,…,4}`, adjacent when disjoint
(Figure 5.17 of the book). -/
@[kb "kellertrotter2017" "text (Figure 5.17), p. 103"]
def petersen : SimpleGraph PetersenVertex where
  Adj s t := Disjoint s.1 t.1
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun s h => by
    have h1 := (Finset.disjoint_self_iff_empty _).mp h
    have h2 := s.2
    rw [h1] at h2
    simp at h2⟩

instance : DecidableRel petersen.Adj := fun s t => inferInstanceAs (Decidable (Disjoint s.1 t.1))

lemma card_petersenVertex : Fintype.card PetersenVertex = 10 := by decide

set_option synthInstance.maxSize 5000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Exhaustive check (by `decide`): the Petersen graph has no closed walk on ten distinct
vertices. -/
lemma petersen_no_ten_cycle :
    ¬ (∃ a0, ∃ a1, petersen.Adj a0 a1 ∧ ∃ a2, (petersen.Adj a1 a2 ∧ a2 ≠ a0) ∧ ∃ a3, (petersen.Adj a2 a3 ∧ a3 ≠ a0 ∧ a3 ≠ a1) ∧ ∃ a4, (petersen.Adj a3 a4 ∧ a4 ≠ a0 ∧ a4 ≠ a1 ∧ a4 ≠ a2) ∧ ∃ a5, (petersen.Adj a4 a5 ∧ a5 ≠ a0 ∧ a5 ≠ a1 ∧ a5 ≠ a2 ∧ a5 ≠ a3) ∧ ∃ a6, (petersen.Adj a5 a6 ∧ a6 ≠ a0 ∧ a6 ≠ a1 ∧ a6 ≠ a2 ∧ a6 ≠ a3 ∧ a6 ≠ a4) ∧ ∃ a7, (petersen.Adj a6 a7 ∧ a7 ≠ a0 ∧ a7 ≠ a1 ∧ a7 ≠ a2 ∧ a7 ≠ a3 ∧ a7 ≠ a4 ∧ a7 ≠ a5) ∧ ∃ a8, (petersen.Adj a7 a8 ∧ a8 ≠ a0 ∧ a8 ≠ a1 ∧ a8 ≠ a2 ∧ a8 ≠ a3 ∧ a8 ≠ a4 ∧ a8 ≠ a5 ∧ a8 ≠ a6) ∧ ∃ a9, (petersen.Adj a8 a9 ∧ a9 ≠ a0 ∧ a9 ≠ a1 ∧ a9 ≠ a2 ∧ a9 ≠ a3 ∧ a9 ≠ a4 ∧ a9 ≠ a5 ∧ a9 ≠ a6 ∧ a9 ≠ a7) ∧ petersen.Adj a9 a0) := by
  decide

/-- CO-101. The Petersen graph is not hamiltonian (stated without proof in the book). -/
@[kb "kellertrotter2017" "text (Figure 5.17), p. 103"]
theorem petersen_not_isHamiltonian : ¬ petersen.IsHamiltonian := by
  intro h
  have h' := (isHamiltonian_iff_cycleGraph_isContained
    (by rw [card_petersenVertex]; norm_num)).mp h
  rw [card_petersenVertex] at h'
  obtain ⟨⟨⟨f, hf⟩, hinj⟩⟩ := h'
  apply petersen_no_ten_cycle
  refine ⟨f 0, f 1, ?_, f 2, ⟨?_, ?_⟩, f 3, ⟨?_, ?_, ?_⟩, f 4, ⟨?_, ?_, ?_, ?_⟩, f 5, ⟨?_, ?_, ?_, ?_, ?_⟩, f 6, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, f 7, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, f 8, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, f 9, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals first
    | exact hf (by decide)
    | exact fun h => absurd (hinj h) (by decide)

end UndergradKB.Combinatorics.Hamilton
