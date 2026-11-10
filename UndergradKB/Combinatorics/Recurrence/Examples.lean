import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import UndergradKB.Common.Attr

/-!
# Counting recurrences (Keller–Trotter, Chapters 3 and 9)

Strings and tilings are modelled concretely; the recurrences, the initial values and the connection
to the Fibonacci numbers are proved.

* Strings of length `n` over a finite alphabet are `Fin n → α`; the first letter is split off with
  `Fin.cons`.
* A tiling of a `2 × n` board is modelled as a composition of `n` into parts `1` and `2`
  (read left to right: `false` is a vertical domino covering one column, `true` is a pair of
  stacked horizontal dominoes covering two columns); this is the standard encoding of such tilings.
  The geometric board itself is not formalized.
-/

namespace UndergradKB.Combinatorics.Recurrence

open Finset

section Strings

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A string `f : Fin n → α` has no forbidden pair `R` in consecutive positions. -/
def NoAdj (R : α → α → Prop) {n : ℕ} (f : Fin n → α) : Prop :=
  ∀ i j : Fin n, j.val = i.val + 1 → ¬ R (f i) (f j)

instance (R : α → α → Prop) [DecidableRel R] {n : ℕ} (f : Fin n → α) :
    Decidable (NoAdj R f) := by unfold NoAdj; infer_instance

/-- The finset of strings of length `n` over `α` in which no consecutive pair satisfies `R`. -/
def goodStr (R : α → α → Prop) [DecidableRel R] (n : ℕ) : Finset (Fin n → α) :=
  univ.filter (fun f => NoAdj R f)

variable (R : α → α → Prop) [DecidableRel R]

omit [Fintype α] [DecidableEq α] [DecidableRel R] in
lemma noAdj_cons {n : ℕ} (a : α) (g : Fin n → α) :
    NoAdj R (Fin.cons a g : Fin (n + 1) → α) ↔ (∀ h : 0 < n, ¬ R a (g ⟨0, h⟩)) ∧ NoAdj R g := by
  constructor
  · intro H
    refine ⟨fun h => ?_, fun i j hij => ?_⟩
    · have := H 0 (Fin.succ ⟨0, h⟩) (by simp)
      rwa [Fin.cons_zero, Fin.cons_succ] at this
    · have := H i.succ j.succ (by simp [hij])
      simpa using this
  · rintro ⟨H1, H2⟩ i j hij
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
      · simp at hij
      · have hj : j = ⟨0, j.pos⟩ := by ext; simp at hij; omega
        have := H1 j.pos
        rw [← hj] at this
        simpa using this
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
      · simp at hij
      · simpa using H2 i j (by simpa using hij)

/-- Good strings of length `n + 1` with first letter `a` correspond to good strings of length `n`
that may follow `a`. -/
lemma fiber_card (n : ℕ) (a : α) :
    ((goodStr R (n + 1)).filter (fun f => f 0 = a)).card =
      ((goodStr R n).filter (fun g => ∀ h : 0 < n, ¬ R a (g ⟨0, h⟩))).card := by
  symm
  apply Finset.card_bij (fun g _ => (Fin.cons a g : Fin (n + 1) → α))
  · intro g hg
    simp only [mem_filter, goodStr, mem_univ, true_and] at hg ⊢
    exact ⟨(noAdj_cons R a g).2 ⟨hg.2, hg.1⟩, by simp⟩
  · intro g₁ _ g₂ _ h
    exact (Fin.cons_injective2 (α := fun _ => α) h).2
  · intro f hf
    simp only [mem_filter, goodStr, mem_univ, true_and] at hf
    obtain ⟨hf, hfa⟩ := hf
    have hf' : f = Fin.cons a (Fin.tail f) := by rw [← hfa]; exact (Fin.cons_self_tail f).symm
    rw [hf'] at hf
    obtain ⟨h1, h2⟩ := (noAdj_cons R a _).1 hf
    refine ⟨Fin.tail f, ?_, hf'.symm⟩
    simp only [mem_filter, goodStr, mem_univ, true_and]
    exact ⟨h2, h1⟩

/-- Splitting the good strings of length `n + 1` according to the first letter. -/
lemma card_good_succ (n : ℕ) :
    (goodStr R (n + 1)).card = ∑ a : α, ((goodStr R n).filter
      (fun g => ∀ h : 0 < n, ¬ R a (g ⟨0, h⟩))).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun f : Fin (n + 1) → α => f 0) (t := univ)
    (fun _ _ => mem_univ _)]
  exact Finset.sum_congr rfl fun a _ => fiber_card R n a

end Strings

/-! ### Binary strings with no two consecutive 1s -/

/-- Forbidden pair for binary strings: two consecutive 1s (`true`). -/
def binBad (x y : Bool) : Prop := x = true ∧ y = true

instance : DecidableRel binBad := fun x y => by unfold binBad; infer_instance

/-- Binary strings of length `n` in which no two consecutive characters are 1. -/
abbrev binGood (n : ℕ) : Finset (Fin n → Bool) := goodStr binBad n

lemma binGood_card_zero : (binGood 0).card = 1 := by decide

/-- CO-218 (initial value). There are 2 good binary strings of length 1. -/
@[kb "kellertrotter2017" "Example 9.3, p. 209"]
lemma binGood_card_one : (binGood 1).card = 2 := by decide

/-- CO-218 (initial value). There are 3 good binary strings of length 2. -/
@[kb "kellertrotter2017" "Example 9.3, p. 209"]
lemma binGood_card_two : (binGood 2).card = 3 := by decide

/-- CO-218. Binary strings with no two consecutive 1s: `a(n+2) = a(n+1) + a(n)` (valid for all
`n ≥ 0`, with `a 0 = 1`; the book's initial values are `a 1 = 2`, `a 2 = 3`). -/
@[kb "kellertrotter2017" "Example 9.3, p. 209"]
theorem binGood_card_succ_succ (n : ℕ) :
    (binGood (n + 2)).card = (binGood (n + 1)).card + (binGood n).card := by
  rw [card_good_succ, Fintype.sum_bool]
  have h1 : ((binGood (n + 1)).filter
      (fun g => ∀ h : 0 < n + 1, ¬ binBad true (g ⟨0, h⟩))).card = (binGood n).card := by
    have := fiber_card binBad n false
    have e : (binGood (n + 1)).filter (fun g => ∀ h : 0 < n + 1, ¬ binBad true (g ⟨0, h⟩))
        = (binGood (n + 1)).filter (fun f => f 0 = false) := by
      apply Finset.filter_congr
      intro g _
      simp [binBad]
    rw [e, this]
    congr 1
    apply Finset.filter_true_of_mem
    intro g _ h
    simp [binBad]
  have h0 : ((binGood (n + 1)).filter
      (fun g => ∀ h : 0 < n + 1, ¬ binBad false (g ⟨0, h⟩))) = binGood (n + 1) := by
    apply Finset.filter_true_of_mem
    intro g _ h
    simp [binBad]
  rw [h0, h1]
  omega

/-- CO-218 (Fibonacci form). The number of binary strings of length `n` with no two consecutive 1s
is `Nat.fib (n + 2)`. (The book writes `a_n = f_{n+1}`, which is off by one in its own indexing
since `a_1 = 2 = f_3`.) -/
@[kb "kellertrotter2017" "Example 9.3, p. 209"]
theorem binGood_card_eq_fib (n : ℕ) : (binGood n).card = Nat.fib (n + 2) := by
  have : ∀ n, (binGood n).card = Nat.fib (n + 2) ∧ (binGood (n + 1)).card = Nat.fib (n + 3) := by
    intro n
    induction n with
    | zero => exact ⟨by rw [binGood_card_zero]; decide, by rw [binGood_card_one]; decide⟩
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [binGood_card_succ_succ, ih.1, ih.2, Nat.fib_add_two (n := n + 2)]
      ring_nf
  exact (this n).1

/-! ### Ternary strings avoiding the substring 20 -/

/-- Forbidden pair for ternary strings over `Fin 3`: a 2 immediately followed by a 0. -/
def ternBad (x y : Fin 3) : Prop := x = 2 ∧ y = 0

instance : DecidableRel ternBad := fun x y => by unfold ternBad; infer_instance

/-- Ternary strings of length `n` that never contain a 2 immediately followed by a 0. -/
abbrev ternGood (n : ℕ) : Finset (Fin n → Fin 3) := goodStr ternBad n

/-- CO-219, CO-216 (initial value). All 3 ternary strings of length 1 are good. -/
@[kb "kellertrotter2017" "Example 9.4, p. 209"]
lemma ternGood_card_one : (ternGood 1).card = 3 := by decide

/-- CO-219, CO-216 (initial value). Exactly 8 of the 9 ternary strings of length 2 are good. -/
@[kb "kellertrotter2017" "Example 9.4, p. 209"]
lemma ternGood_card_two : (ternGood 2).card = 8 := by decide

lemma ternGood_card_zero : (ternGood 0).card = 1 := by decide

/-- CO-219 and CO-216. Ternary strings with no 20: `t(n+2) = 3 t(n+1) - t(n)`, written without
subtraction (valid for all `n ≥ 0`, with `t 0 = 1`). -/
@[kb "kellertrotter2017" "Example 9.4, p. 209; Example 3.6, p. 68"]
theorem ternGood_card_succ_succ (n : ℕ) :
    (ternGood (n + 2)).card + (ternGood n).card = 3 * (ternGood (n + 1)).card := by
  rw [card_good_succ, Fin.sum_univ_three]
  have hall : ∀ a : Fin 3, a ≠ 2 → ((ternGood (n + 1)).filter
      (fun g => ∀ h : 0 < n + 1, ¬ ternBad a (g ⟨0, h⟩))) = ternGood (n + 1) := by
    intro a ha
    apply Finset.filter_true_of_mem
    intro g _ h hb
    exact ha hb.1
  rw [hall 0 (by decide), hall 1 (by decide)]
  have hz := fiber_card ternBad n 0
  have hsplit : ((ternGood (n + 1)).filter (fun f => f 0 = 0)).card +
      ((ternGood (n + 1)).filter (fun f => ¬ f 0 = 0)).card = (ternGood (n + 1)).card :=
    Finset.card_filter_add_card_filter_not _
  have e : (ternGood (n + 1)).filter
      (fun g => ∀ h : 0 < n + 1, ¬ ternBad 2 (g ⟨0, h⟩)) =
      (ternGood (n + 1)).filter (fun f => ¬ f 0 = 0) := by
    apply Finset.filter_congr
    intro g _
    simp [ternBad]
  have e0 : (ternGood n).filter (fun g => ∀ h : 0 < n, ¬ ternBad 0 (g ⟨0, h⟩)) = ternGood n := by
    apply Finset.filter_true_of_mem
    intro g _ h hb
    exact absurd hb.1 (by decide)
  rw [e0] at hz
  rw [hz] at hsplit
  rw [e]
  omega

/-- CO-219 and CO-216, in the book's subtractive form `t(n+2) = 3 t(n+1) - t(n)` in `ℤ`. -/
@[kb "kellertrotter2017" "Example 9.4, p. 209; Example 3.6, p. 68"]
theorem ternGood_card_recurrence (n : ℕ) :
    ((ternGood (n + 2)).card : ℤ) = 3 * (ternGood (n + 1)).card - (ternGood n).card := by
  have := ternGood_card_succ_succ n
  omega

/-- `t(3) = 21`, as stated in the book. -/
lemma ternGood_card_three : (ternGood 3).card = 21 := by
  have h : (ternGood 3).card + (ternGood 1).card = 3 * (ternGood 2).card :=
    ternGood_card_succ_succ 1
  rw [ternGood_card_two, ternGood_card_one] at h
  omega

/-! ### Domino tilings of a `2 × n` board, as compositions into parts 1 and 2 -/

/-- Number of columns of a tile in the encoding: `false` = one vertical domino (1 column),
`true` = a pair of stacked horizontal dominoes (2 columns). -/
def tileWidth (b : Bool) : ℕ := if b then 2 else 1

/-- The tilings of a `2 × n` board, modelled as lists of tiles (read left to right) whose total
width is `n`, i.e. compositions of `n` into parts 1 and 2. -/
def tilings (n : ℕ) : Set (List Bool) := {l | (l.map tileWidth).sum = n}

lemma length_le_width_sum (l : List Bool) : l.length ≤ (l.map tileWidth).sum := by
  induction l with
  | nil => simp
  | cons b l ih => cases b <;> simp [tileWidth] <;> omega

lemma tilings_finite (n : ℕ) : (tilings n).Finite :=
  (List.finite_length_le Bool (n := n)).subset fun l hl => by
    have := length_le_width_sum l
    have hl' : (l.map tileWidth).sum = n := hl
    show l.length ≤ n
    omega

lemma tilings_zero : tilings 0 = {[]} := by
  ext l
  rcases l with _ | ⟨b, l⟩
  · simp [tilings]
  · cases b <;> simp [tilings, tileWidth]

lemma tilings_one : tilings 1 = {[false]} := by
  ext l
  rcases l with _ | ⟨b, l⟩
  · simp [tilings]
  · have h0 : (l.map tileWidth).sum = 0 ↔ l = [] := by
      have : l ∈ tilings 0 ↔ l ∈ ({[]} : Set (List Bool)) := by rw [tilings_zero]
      simpa [tilings] using this
    cases b
    · simp [tilings, tileWidth, h0]
    · simp [tilings, tileWidth]
      omega

lemma tilings_succ_succ (n : ℕ) :
    tilings (n + 2) = (List.cons false) '' tilings (n + 1) ∪ (List.cons true) '' tilings n := by
  ext l
  rcases l with _ | ⟨b, l⟩
  · simp [tilings]
  · cases b <;> simp [tilings, tileWidth] <;> omega

/-- The number `t n` of tilings of the `2 × n` board. -/
noncomputable def tilingCount (n : ℕ) : ℕ := (tilings n).ncard

/-- CO-215 (initial value). `t 1 = 1`. -/
@[kb "kellertrotter2017" "Example 3.5, p. 68; Example 9.2, p. 209"]
lemma tilingCount_one : tilingCount 1 = 1 := by
  simp [tilingCount, tilings_one]

lemma tilingCount_zero : tilingCount 0 = 1 := by
  simp [tilingCount, tilings_zero]

/-- CO-215. The number of tilings of a `2 × n` board by dominoes satisfies
`t(n+2) = t(n+1) + t(n)` (modelled via compositions into parts 1 and 2; see the file docstring). -/
@[kb "kellertrotter2017" "Example 3.5, p. 68; Example 9.2, p. 209"]
theorem tilingCount_succ_succ (n : ℕ) :
    tilingCount (n + 2) = tilingCount (n + 1) + tilingCount n := by
  unfold tilingCount
  have hd : Disjoint ((List.cons false) '' tilings (n + 1)) ((List.cons true) '' tilings n) := by
    rw [Set.disjoint_left]
    rintro l ⟨x, _, rfl⟩ ⟨y, _, h⟩
    simp at h
  rw [tilings_succ_succ, Set.ncard_union_eq hd ((tilings_finite _).image _)
    ((tilings_finite _).image _), Set.ncard_image_of_injective _ (List.cons_injective),
    Set.ncard_image_of_injective _ (List.cons_injective)]

/-- CO-215 (initial value). `t 2 = 2`. -/
@[kb "kellertrotter2017" "Example 3.5, p. 68; Example 9.2, p. 209"]
lemma tilingCount_two : tilingCount 2 = 2 := by
  have := tilingCount_succ_succ 0
  rw [tilingCount_one, tilingCount_zero] at this
  simpa using this

/-- CO-215 (Fibonacci form). `t n = f_{n+1}`. -/
@[kb "kellertrotter2017" "Example 9.2, p. 209"]
theorem tilingCount_eq_fib (n : ℕ) : tilingCount n = Nat.fib (n + 1) := by
  have : ∀ n, tilingCount n = Nat.fib (n + 1) ∧ tilingCount (n + 1) = Nat.fib (n + 2) := by
    intro n
    induction n with
    | zero => exact ⟨by rw [tilingCount_zero]; decide, by rw [tilingCount_one]; decide⟩
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [tilingCount_succ_succ, ih.1, ih.2, Nat.fib_add_two (n := n + 1)]
      ring_nf
  exact (this n).1

/-! ### Lines in general position: solving the recurrence -/

lemma choose_two_succ (n : ℕ) : (n + 2).choose 2 = (n + 1).choose 2 + (n + 1) := by
  have h : (n + 2).choose 2 = (n + 1).choose 1 + (n + 1).choose 2 :=
    Nat.choose_succ_succ' (n + 1) 1
  rw [Nat.choose_one_right] at h
  omega

/-- CO-220. Solution of the recurrence for the number `r n` of regions cut out by `n` lines in
general position: from `r 0 = 1` and `r (n+1) = r n + (n+1)` one gets `r n = 1 + C(n+1, 2)`. The
geometric fact that `n` lines in general position satisfy this recurrence is not formalized. -/
@[kb "kellertrotter2017" "text, p. 210; Example 9.16, p. 220"]
theorem lines_regions_closed_form (r : ℕ → ℕ) (h0 : r 0 = 1)
    (hs : ∀ n, r (n + 1) = r n + (n + 1)) : ∀ n, r n = 1 + (n + 1).choose 2 := by
  intro n
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    rw [hs, ih, choose_two_succ]
    omega

/-- CO-214. Same as `lines_regions_closed_form` in the form of Example 1.12 / 3.3: from `r 1 = 2`
and `r n = n + r (n-1)` for `n ≥ 2` one gets `r n = 1 + C(n+1, 2)` for `n ≥ 1`. The geometry is not
formalized. -/
@[kb "kellertrotter2017" "Example 3.3, p. 67; Example 1.12, p. 36"]
theorem lines_regions_closed_form' (r : ℕ → ℕ) (h1 : r 1 = 2)
    (hs : ∀ n, 2 ≤ n → r n = n + r (n - 1)) : ∀ n, 1 ≤ n → r n = 1 + (n + 1).choose 2 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp [h1]
  | succ n hn ih =>
    rw [hs (n + 1) (by omega), Nat.add_sub_cancel, ih, choose_two_succ]
    omega

end UndergradKB.Combinatorics.Recurrence
