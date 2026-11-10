import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Finset.Powerset
import UndergradKB.Common.Attr

/-!
# Domino tilings of a `2 × n` board (Keller–Trotter, Example 3.5)

A genuine model: cells are pairs `(row, column)` of natural numbers with `row < 2`, `column < n`;
a domino is a set `{a, b}` of two edge-adjacent cells; a tiling of the `2 × n` board is a finite
set of dominoes inside the board that are pairwise disjoint and cover every cell.
We prove `t(n+2) = t(n+1) + t(n)`, `t(0) = t(1) = 1`, hence `t(n) = fib (n+1)`.
-/

namespace UndergradKB.Combinatorics.Recurrence.Domino

open Finset

/-- A cell `(row, column)`. -/
abbrev Cell := ℕ × ℕ

/-- The cells of the `2 × n` board: rows `0, 1` and columns `0, …, n-1`. -/
def board (n : ℕ) : Finset Cell := range 2 ×ˢ range n

/-- Two cells share an edge. -/
def Adj (a b : Cell) : Prop :=
  (a.1 = b.1 ∧ (a.2 + 1 = b.2 ∨ b.2 + 1 = a.2)) ∨ (a.2 = b.2 ∧ (a.1 + 1 = b.1 ∨ b.1 + 1 = a.1))

/-- A domino: the set of two edge-adjacent cells (a `2 × 1` or `1 × 2` rectangle). -/
def IsDomino (d : Finset Cell) : Prop := ∃ a b, Adj a b ∧ d = {a, b}

/-- A tiling of the `2 × n` board by dominoes: a set `T` of dominoes inside the board, pairwise
disjoint, covering every cell. -/
structure IsTiling (n : ℕ) (T : Finset (Finset Cell)) : Prop where
  domino : ∀ d ∈ T, IsDomino d
  subset : ∀ d ∈ T, d ⊆ board n
  disjoint : ∀ d ∈ T, ∀ e ∈ T, d ≠ e → Disjoint d e
  cover : ∀ x ∈ board n, ∃ d ∈ T, x ∈ d

/-- The set of all tilings of the `2 × n` board. -/
def boardTilings (n : ℕ) : Set (Finset (Finset Cell)) := {T | IsTiling n T}

/-- The number `t(n)` of tilings of the `2 × n` board. -/
noncomputable def boardTilingCount (n : ℕ) : ℕ := (boardTilings n).ncard

lemma mem_board {x : Cell} {n : ℕ} : x ∈ board n ↔ x.1 < 2 ∧ x.2 < n := by
  simp [board]

lemma board_mono {m k : ℕ} (h : m ≤ k) : board m ⊆ board k := by
  intro x hx
  rw [mem_board] at hx ⊢
  omega

lemma IsDomino.nonempty {d : Finset Cell} (h : IsDomino d) : d.Nonempty := by
  obtain ⟨a, b, -, rfl⟩ := h
  exact ⟨a, by simp⟩

/-- The vertical domino in column `m`. -/
def Vc (m : ℕ) : Finset Cell := {(0, m), (1, m)}
/-- The horizontal domino in row 0, columns `n, n+1`. -/
def H0 (n : ℕ) : Finset Cell := {(0, n), (0, n + 1)}
/-- The horizontal domino in row 1, columns `n, n+1`. -/
def H1 (n : ℕ) : Finset Cell := {(1, n), (1, n + 1)}

lemma isDomino_Vc (m : ℕ) : IsDomino (Vc m) := ⟨(0, m), (1, m), by simp [Adj], rfl⟩
lemma isDomino_H0 (n : ℕ) : IsDomino (H0 n) := ⟨(0, n), (0, n + 1), by simp [Adj], rfl⟩
lemma isDomino_H1 (n : ℕ) : IsDomino (H1 n) := ⟨(1, n), (1, n + 1), by simp [Adj], rfl⟩

/-- Corner analysis in row 0: a domino in the first `m+1` columns covering `(0, m)`. -/
lemma corner0 {m : ℕ} {d : Finset Cell} (hd : IsDomino d) (hs : d ⊆ board (m + 1))
    (hx : ((0 : ℕ), m) ∈ d) : d = Vc m ∨ ∃ n, m = n + 1 ∧ d = H0 n := by
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, hab, rfl⟩ := hd
  have ha : (a1, a2) ∈ board (m + 1) := hs (by simp)
  have hb : (b1, b2) ∈ board (m + 1) := hs (by simp)
  simp only [mem_insert, mem_singleton, Prod.mk.injEq] at hx
  simp only [mem_board, Adj] at ha hb hab
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h1 h2
    have : (b1 = 1 ∧ b2 = m) ∨ (m = b2 + 1 ∧ b1 = 0) := by omega
    rcases this with ⟨rfl, rfl⟩ | ⟨h, rfl⟩
    · left; rfl
    · right; exact ⟨b2, h, by subst h; rw [H0, Finset.pair_comm]⟩
  · subst h1 h2
    have : (a1 = 1 ∧ a2 = m) ∨ (m = a2 + 1 ∧ a1 = 0) := by omega
    rcases this with ⟨rfl, rfl⟩ | ⟨h, rfl⟩
    · left; rw [Vc, Finset.pair_comm]
    · right; exact ⟨a2, h, by subst h; rfl⟩

/-- Corner analysis in row 1: a domino in the first `m+1` columns covering `(1, m)`. -/
lemma corner1 {m : ℕ} {d : Finset Cell} (hd : IsDomino d) (hs : d ⊆ board (m + 1))
    (hx : ((1 : ℕ), m) ∈ d) : d = Vc m ∨ ∃ n, m = n + 1 ∧ d = H1 n := by
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, hab, rfl⟩ := hd
  have ha : (a1, a2) ∈ board (m + 1) := hs (by simp)
  have hb : (b1, b2) ∈ board (m + 1) := hs (by simp)
  simp only [mem_insert, mem_singleton, Prod.mk.injEq] at hx
  simp only [mem_board, Adj] at ha hb hab
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h1 h2
    have : (b1 = 0 ∧ b2 = m) ∨ (m = b2 + 1 ∧ b1 = 1) := by omega
    rcases this with ⟨rfl, rfl⟩ | ⟨h, rfl⟩
    · left; rw [Vc, Finset.pair_comm]
    · right; exact ⟨b2, h, by subst h; rw [H1, Finset.pair_comm]⟩
  · subst h1 h2
    have : (a1 = 0 ∧ a2 = m) ∨ (m = a2 + 1 ∧ a1 = 1) := by omega
    rcases this with ⟨rfl, rfl⟩ | ⟨h, rfl⟩
    · left; rfl
    · right; exact ⟨a2, h, by subst h; rfl⟩

/-- Extending a tiling of the first `m` columns by dominoes `S` filling columns `m, …, k-1`. -/
lemma IsTiling.extend {m k : ℕ} {T : Finset (Finset Cell)} (hT : IsTiling m T) (hmk : m ≤ k)
    (S : Finset (Finset Cell)) (hSd : ∀ d ∈ S, IsDomino d) (hSs : ∀ d ∈ S, d ⊆ board k)
    (hSm : ∀ d ∈ S, ∀ x ∈ d, m ≤ x.2) (hSdisj : ∀ d ∈ S, ∀ e ∈ S, d ≠ e → Disjoint d e)
    (hSc : ∀ x ∈ board k, m ≤ x.2 → ∃ d ∈ S, x ∈ d) : IsTiling k (S ∪ T) where
  domino d hd := by
    rcases mem_union.1 hd with h | h
    · exact hSd d h
    · exact hT.domino d h
  subset d hd := by
    rcases mem_union.1 hd with h | h
    · exact hSs d h
    · exact (hT.subset d h).trans (board_mono hmk)
  disjoint d hd e he hne := by
    have key : ∀ d ∈ S, ∀ e ∈ T, Disjoint d e := by
      intro d hd e he
      rw [Finset.disjoint_left]
      intro x hxd hxe
      have h1 := hSm d hd x hxd
      have h2 := (mem_board.1 (hT.subset e he hxe)).2
      omega
    rcases mem_union.1 hd with h | h <;> rcases mem_union.1 he with h' | h'
    · exact hSdisj d h e h' hne
    · exact key d h e h'
    · exact (key e h' d h).symm
    · exact hT.disjoint d h e h' hne
  cover x hx := by
    by_cases h : x.2 < m
    · obtain ⟨d, hd, hxd⟩ := hT.cover x (mem_board.2 ⟨(mem_board.1 hx).1, h⟩)
      exact ⟨d, mem_union_right _ hd, hxd⟩
    · obtain ⟨d, hd, hxd⟩ := hSc x hx (by omega)
      exact ⟨d, mem_union_left _ hd, hxd⟩

/-- Removing the dominoes `S` filling columns `m, …, k-1` from a tiling of the first `k` columns. -/
lemma IsTiling.restrict {m k : ℕ} {T : Finset (Finset Cell)} (hT : IsTiling k T)
    (S : Finset (Finset Cell)) (hST : S ⊆ T)
    (hSm : ∀ d ∈ S, ∀ x ∈ d, m ≤ x.2) (hmk : m ≤ k)
    (hSc : ∀ x ∈ board k, m ≤ x.2 → ∃ d ∈ S, x ∈ d) : IsTiling m (T \ S) where
  domino d hd := hT.domino d (mem_sdiff.1 hd).1
  subset d hd := by
    obtain ⟨hdT, hdS⟩ := mem_sdiff.1 hd
    intro x hx
    have hxk := mem_board.1 (hT.subset d hdT hx)
    rw [mem_board]
    refine ⟨hxk.1, ?_⟩
    by_contra hlt
    obtain ⟨e, he, hxe⟩ := hSc x (mem_board.2 hxk) (by omega)
    have hne : d ≠ e := fun h => hdS (h ▸ he)
    exact Finset.disjoint_left.1 (hT.disjoint d hdT e (hST he) hne) hx hxe
  disjoint d hd e he hne := hT.disjoint d (mem_sdiff.1 hd).1 e (mem_sdiff.1 he).1 hne
  cover x hx := by
    obtain ⟨d, hd, hxd⟩ := hT.cover x (board_mono hmk hx)
    refine ⟨d, mem_sdiff.2 ⟨hd, fun hdS => ?_⟩, hxd⟩
    have := hSm d hdS x hxd
    have := (mem_board.1 hx).2
    omega

/-! ### The three kinds of extension -/

lemma Vc_ext {m : ℕ} {T : Finset (Finset Cell)} (hT : IsTiling m T) :
    IsTiling (m + 1) ({Vc m} ∪ T) := by
  refine hT.extend (Nat.le_succ m) {Vc m} ?_ ?_ ?_ ?_ ?_
  · simpa using isDomino_Vc m
  · intro d hd
    rw [mem_singleton] at hd
    subst hd
    intro x hx
    simp only [Vc, mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [mem_board]
  · intro d hd x hx
    rw [mem_singleton] at hd
    subst hd
    simp only [Vc, mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp
  · intro d hd e he hne
    rw [mem_singleton] at hd he
    exact absurd (hd.trans he.symm) hne
  · intro x hx hmx
    refine ⟨Vc m, mem_singleton_self _, ?_⟩
    obtain ⟨x1, x2⟩ := x
    simp only [mem_board] at hx
    simp only [Vc, mem_insert, mem_singleton, Prod.mk.injEq]
    simp only at hmx hx
    omega

lemma H_ext {n : ℕ} {T : Finset (Finset Cell)} (hT : IsTiling n T) :
    IsTiling (n + 2) ({H0 n, H1 n} ∪ T) := by
  have hne : H0 n ≠ H1 n := by
    intro h
    have := congrArg (fun s => ((0 : ℕ), n) ∈ s) h
    simp [H0, H1] at this
  refine hT.extend (by omega) {H0 n, H1 n} ?_ ?_ ?_ ?_ ?_
  · intro d hd
    rcases mem_insert.1 hd with rfl | hd
    · exact isDomino_H0 n
    · rw [mem_singleton] at hd; subst hd; exact isDomino_H1 n
  · intro d hd
    rcases mem_insert.1 hd with rfl | hd
    · intro x hx
      simp only [H0, mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [mem_board]
    · rw [mem_singleton] at hd; subst hd
      intro x hx
      simp only [H1, mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [mem_board]
  · intro d hd x hx
    rcases mem_insert.1 hd with rfl | hd
    · simp only [H0, mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp
    · rw [mem_singleton] at hd; subst hd
      simp only [H1, mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp
  · intro d hd e he hde
    rcases mem_insert.1 hd with rfl | hd <;> rcases mem_insert.1 he with rfl | he
    · exact absurd rfl hde
    · rw [mem_singleton] at he; subst he
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨x1, x2⟩ := x
      simp only [H0, H1, mem_insert, mem_singleton, Prod.mk.injEq] at hx hx'
      omega
    · rw [mem_singleton] at hd; subst hd
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨x1, x2⟩ := x
      simp only [H0, H1, mem_insert, mem_singleton, Prod.mk.injEq] at hx hx'
      omega
    · rw [mem_singleton] at hd he; exact absurd (hd.trans he.symm) hde
  · intro x hx hmx
    obtain ⟨x1, x2⟩ := x
    have hx' : x1 < 2 ∧ x2 < n + 2 := mem_board.1 hx
    have hmx' : n ≤ x2 := hmx
    have : x1 = 0 ∨ x1 = 1 := by omega
    rcases this with rfl | rfl
    · refine ⟨H0 n, by simp, ?_⟩
      simp only [H0, mem_insert, mem_singleton, Prod.mk.injEq, true_and]
      omega
    · refine ⟨H1 n, by simp, ?_⟩
      simp only [H1, mem_insert, mem_singleton, Prod.mk.injEq, true_and]
      omega

/-- Helper: members of a tiling of `m` columns lie strictly left of column `m`. -/
lemma not_mem_of_tiling {m : ℕ} {T : Finset (Finset Cell)} (hT : IsTiling m T) {d : Finset Cell}
    (hd : d ∈ T) {x : Cell} (hx : x ∈ d) : x.2 < m :=
  (mem_board.1 (hT.subset d hd hx)).2

lemma notMem_of_right {m : ℕ} {T S : Finset (Finset Cell)} (hT : IsTiling m T)
    (hSm : ∀ d ∈ S, ∀ x ∈ d, m ≤ x.2) (hS : ∀ d ∈ S, IsDomino d) : Disjoint S T := by
  rw [Finset.disjoint_left]
  intro d hdS hdT
  obtain ⟨x, hx⟩ := (hS d hdS).nonempty
  have := hSm d hdS x hx
  have := not_mem_of_tiling hT hdT hx
  omega

/-! ### The recurrence -/

lemma boardTilings_finite (n : ℕ) : (boardTilings n).Finite := by
  refine Set.Finite.subset ((board n).powerset.powerset.finite_toSet) ?_
  intro T hT
  rw [Finset.mem_coe, mem_powerset]
  intro d hd
  exact mem_powerset.2 (hT.subset d hd)

lemma boardTilings_zero : boardTilings 0 = {∅} := by
  ext T
  simp only [boardTilings, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro hT
    rw [Finset.eq_empty_iff_forall_notMem]
    intro d hd
    obtain ⟨x, hx⟩ := (hT.domino d hd).nonempty
    have := mem_board.1 (hT.subset d hd hx)
    omega
  · rintro rfl
    exact ⟨by simp, by simp, by simp, fun x hx => by simp [mem_board] at hx⟩

lemma boardTilingCount_zero : boardTilingCount 0 = 1 := by
  simp [boardTilingCount, boardTilings_zero]

lemma singleton_inj_on (m : ℕ) (S : Finset (Finset Cell)) (hS : ∀ d ∈ S, IsDomino d)
    (hSm : ∀ d ∈ S, ∀ x ∈ d, m ≤ x.2) :
    Set.InjOn (fun T => S ∪ T) (boardTilings m) := by
  intro T hT T' hT' h
  have e1 : (S ∪ T) \ S = T := Finset.union_sdiff_cancel_left (notMem_of_right hT hSm hS)
  have e2 : (S ∪ T') \ S = T' := Finset.union_sdiff_cancel_left (notMem_of_right hT' hSm hS)
  simp only at h
  rw [← e1, ← e2, h]

lemma boardTilings_one : boardTilings 1 = (fun T => {Vc 0} ∪ T) '' boardTilings 0 := by
  have hS : ∀ d ∈ ({Vc 0} : Finset (Finset Cell)), IsDomino d := by simpa using isDomino_Vc 0
  ext T
  constructor
  · intro hT
    obtain ⟨d, hd, hxd⟩ := hT.cover (0, 0) (by simp [mem_board])
    rcases corner0 (hT.domino d hd) (hT.subset d hd) hxd with rfl | ⟨n, hn, -⟩
    · refine ⟨T \ {Vc 0}, ?_, ?_⟩
      · refine hT.restrict {Vc 0} (by simpa using hd) ?_ (by omega) ?_
        · intro d hd x hx
          rw [mem_singleton] at hd; subst hd
          simp only [Vc, mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl <;> simp
        · intro x hx _
          refine ⟨Vc 0, mem_singleton_self _, ?_⟩
          obtain ⟨x1, x2⟩ := x
          simp only [mem_board] at hx
          simp only [Vc, mem_insert, mem_singleton, Prod.mk.injEq]
          omega
      · exact Finset.union_sdiff_of_subset (by simpa using hd)
    · omega
  · rintro ⟨T', hT', rfl⟩
    exact Vc_ext hT'

lemma boardTilingCount_one : boardTilingCount 1 = 1 := by
  rw [boardTilingCount, boardTilings_one, Set.InjOn.ncard_image
    (singleton_inj_on 0 {Vc 0} (by simpa using isDomino_Vc 0) (by
      intro d hd x hx
      rw [mem_singleton] at hd; subst hd
      simp only [Vc, mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp))]
  exact boardTilingCount_zero

lemma boardTilings_add_two (n : ℕ) :
    boardTilings (n + 2) = (fun T => {Vc (n + 1)} ∪ T) '' boardTilings (n + 1) ∪
      (fun T => {H0 n, H1 n} ∪ T) '' boardTilings n := by
  ext T
  constructor
  · intro hT
    obtain ⟨d, hd, hxd⟩ := hT.cover (0, n + 1) (by simp [mem_board])
    rcases corner0 (hT.domino d hd) (hT.subset d hd) hxd with rfl | ⟨k, hk, rfl⟩
    · left
      refine ⟨T \ {Vc (n + 1)}, ?_, ?_⟩
      · refine hT.restrict {Vc (n + 1)} (by simpa using hd) ?_ (by omega) ?_
        · intro d hd x hx
          rw [mem_singleton] at hd; subst hd
          simp only [Vc, mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl <;> simp
        · intro x hx hmx
          refine ⟨Vc (n + 1), mem_singleton_self _, ?_⟩
          obtain ⟨x1, x2⟩ := x
          simp only [mem_board] at hx
          simp only [Vc, mem_insert, mem_singleton, Prod.mk.injEq]
          simp only at hx hmx
          omega
      · simp only
        exact Finset.union_sdiff_of_subset (by simpa using hd)
    · right
      have hk' : k = n := by omega
      subst hk'
      -- the domino covering (1, k+1)
      obtain ⟨e, he, hxe⟩ := hT.cover (1, k + 1) (by simp [mem_board])
      have hHe : e = H1 k := by
        rcases corner1 (hT.domino e he) (hT.subset e he) hxe with rfl | ⟨j, hj, rfl⟩
        · exfalso
          have hne : Vc (k + 1) ≠ H0 k := by
            intro h
            have := congrArg (fun s => ((1 : ℕ), k + 1) ∈ s) h
            simp [Vc, H0] at this
          exact Finset.disjoint_left.1 (hT.disjoint _ he _ hd hne) (show ((0 : ℕ), k + 1) ∈ Vc (k + 1) by simp [Vc])
            (by simp [H0])
        · have : j = k := by omega
          subst this; rfl
      subst hHe
      refine ⟨T \ {H0 k, H1 k}, ?_, ?_⟩
      · refine hT.restrict {H0 k, H1 k} ?_ ?_ (by omega) ?_
        · intro f hf
          rcases mem_insert.1 hf with rfl | hf
          · exact hd
          · rw [mem_singleton] at hf; subst hf; exact he
        · intro f hf x hx
          rcases mem_insert.1 hf with rfl | hf
          · simp only [H0, mem_insert, mem_singleton] at hx
            rcases hx with rfl | rfl <;> simp
          · rw [mem_singleton] at hf; subst hf
            simp only [H1, mem_insert, mem_singleton] at hx
            rcases hx with rfl | rfl <;> simp
        · intro x hx hmx
          obtain ⟨x1, x2⟩ := x
          have hx' : x1 < 2 ∧ x2 < k + 2 := mem_board.1 hx
          have hmx' : k ≤ x2 := hmx
          have : x1 = 0 ∨ x1 = 1 := by omega
          rcases this with rfl | rfl
          · refine ⟨H0 k, by simp, ?_⟩
            simp only [H0, mem_insert, mem_singleton, Prod.mk.injEq, true_and]
            omega
          · refine ⟨H1 k, by simp, ?_⟩
            simp only [H1, mem_insert, mem_singleton, Prod.mk.injEq, true_and]
            omega
      · simp only
        refine Finset.union_sdiff_of_subset ?_
        intro f hf
        rcases mem_insert.1 hf with rfl | hf
        · exact hd
        · rw [mem_singleton] at hf; subst hf; exact he
  · rintro (⟨T', hT', rfl⟩ | ⟨T', hT', rfl⟩)
    · exact Vc_ext hT'
    · exact H_ext hT'

/-- CO-215. The number `t(n)` of tilings of a `2 × n` board by dominoes satisfies
`t(n+2) = t(n+1) + t(n)`; the last domino covering the top right cell is vertical (leaving a
`2 × (n+1)` board) or horizontal together with the one beneath it (leaving a `2 × n` board). -/
@[kb "kellertrotter2017" "Example 3.5, p. 68"]
theorem boardTilingCount_add_two (n : ℕ) :
    boardTilingCount (n + 2) = boardTilingCount (n + 1) + boardTilingCount n := by
  have hdisj : Disjoint ((fun T => {Vc (n + 1)} ∪ T) '' boardTilings (n + 1))
      ((fun T => {H0 n, H1 n} ∪ T) '' boardTilings n) := by
    rw [Set.disjoint_left]
    rintro T ⟨A, hA, rfl⟩ ⟨B, hB, h⟩
    have hmem : Vc (n + 1) ∈ ({H0 n, H1 n} ∪ B : Finset (Finset Cell)) := by
      have h' : ({H0 n, H1 n} ∪ B : Finset (Finset Cell)) = {Vc (n + 1)} ∪ A := h
      rw [h']; simp
    rcases mem_union.1 hmem with h1 | h1
    · rcases mem_insert.1 h1 with h2 | h2
      · have := congrArg (fun s => ((1 : ℕ), n + 1) ∈ s) h2
        simp [Vc, H0] at this
      · rw [mem_singleton] at h2
        have := congrArg (fun s => ((0 : ℕ), n + 1) ∈ s) h2
        simp [Vc, H1] at this
    · have := not_mem_of_tiling hB h1 (x := (0, n + 1)) (by simp [Vc])
      simp at this
  have hS1 : ∀ d ∈ ({Vc (n + 1)} : Finset (Finset Cell)), IsDomino d := by
    simpa using isDomino_Vc (n + 1)
  have hS2 : ∀ d ∈ ({H0 n, H1 n} : Finset (Finset Cell)), IsDomino d := by
    intro d hd
    rcases mem_insert.1 hd with rfl | hd
    · exact isDomino_H0 n
    · rw [mem_singleton] at hd; subst hd; exact isDomino_H1 n
  rw [boardTilingCount, boardTilings_add_two, Set.ncard_union_eq hdisj
    ((boardTilings_finite _).image _) ((boardTilings_finite _).image _),
    Set.InjOn.ncard_image (singleton_inj_on (n + 1) _ hS1 (by
      intro d hd x hx
      rw [mem_singleton] at hd; subst hd
      simp only [Vc, mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp)),
    Set.InjOn.ncard_image (singleton_inj_on n _ hS2 (by
      intro d hd x hx
      rcases mem_insert.1 hd with rfl | hd
      · simp only [H0, mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl <;> simp
      · rw [mem_singleton] at hd; subst hd
        simp only [H1, mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl <;> simp))]
  rfl

/-- CO-215. `t(n) = fib (n+1)`: the numbers of domino tilings of a `2 × n` board are Fibonacci
numbers (`t(1) = 1`, `t(2) = 2`, `t(3) = 3`, ...). -/
@[kb "kellertrotter2017" "Example 3.5, p. 68; Example 9.2, p. 209"]
theorem boardTilingCount_eq_fib (n : ℕ) : boardTilingCount n = Nat.fib (n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [boardTilingCount_zero]
  | one => simp [boardTilingCount_one]
  | more n ih1 ih2 =>
    rw [boardTilingCount_add_two, ih1, ih2, Nat.fib_add_two (n := n + 1)]
    ring

end UndergradKB.Combinatorics.Recurrence.Domino
