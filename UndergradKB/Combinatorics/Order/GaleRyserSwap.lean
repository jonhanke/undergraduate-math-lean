import Mathlib.Data.Fintype.Fin
import Mathlib.Logic.Relation
import UndergradKB.Combinatorics.Order.GaleRyser
import UndergradKB.Common.Attr

/-!
# The swap construction in the proof of the Gale–Ryser theorem (Keller–Trotter, p. 349)

The book builds a zero-one matrix with row sum string `R` and column sum string `C` by starting from
the matrix with the ones pushed to the left (whose column string is the dual `Rᵈ`) and, for each step
of a chain of covers in the dominance order, exchanging one pair of entries in a row: a one in column
`i` and a zero in column `j` (which exists because column `i` currently holds more ones than column
`j`).  Each exchange lowers the column string at `i` by one and raises it at `j` by one and leaves
all row sums unchanged.  We prove this step and the resulting statement for any chain of such
transfers.  The existence of a chain of covers from `Rᵈ` down to `C` (Proposition 16.11) is not
formalized here (the theorem `gale_ryser` proves existence by max-flow min-cut instead).
-/

namespace UndergradKB.Combinatorics

open Finset

namespace GaleRyserSwap

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Exchange, in row `q`, the entry in column `i` with the entry in column `j`
(the construction assumes the entries are `1` and `0` respectively). -/
def swapOne (M : ι → κ → Bool) (q : ι) (i j : κ) : ι → κ → Bool :=
  fun r k => if r = q then (if k = i then false else if k = j then true else M r k) else M r k

lemma rowSum_eq (M : ι → κ → Bool) (r : ι) :
    rowSum M r = ∑ k, if M r k = true then 1 else 0 := by
  rw [rowSum, Finset.card_filter]

/-- A strictly larger column `i` has a row with a one in `i` and a zero in `j`. -/
lemma exists_swap_row {M : ι → κ → Bool} {i j : κ} (h : colSum M j < colSum M i) :
    ∃ q, M q i = true ∧ M q j = false := by
  by_contra hno
  push Not at hno
  apply absurd h
  rw [not_lt]
  apply Finset.card_le_card
  intro r hr
  rw [Finset.mem_filter] at hr ⊢
  refine ⟨hr.1, ?_⟩
  have := hno r hr.2
  simpa using this

variable {M : ι → κ → Bool} {q : ι} {i j : κ}

lemma rowSum_swapOne (hij : i ≠ j) (hqi : M q i = true) (hqj : M q j = false) (r : ι) :
    rowSum (swapOne M q i j) r = rowSum M r := by
  by_cases hr : r = q
  · subst hr
    rw [rowSum_eq, rowSum_eq]
    have decomp : ∀ g : κ → ℕ, ∑ k, g k = g i + g j + ∑ k ∈ (univ.erase i).erase j, g k := by
      intro g
      rw [← Finset.add_sum_erase _ _ (mem_univ i),
        ← Finset.add_sum_erase _ _ (mem_erase.2 ⟨hij.symm, mem_univ j⟩)]
      ring
    rw [decomp, decomp (fun k => if M r k = true then 1 else 0)]
    have hrest : ∑ k ∈ (univ.erase i).erase j, (if swapOne M r i j r k = true then 1 else 0) =
        ∑ k ∈ (univ.erase i).erase j, (if M r k = true then 1 else 0) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      obtain ⟨hkj, hk'⟩ := mem_erase.1 hk
      have hki := (mem_erase.1 hk').1
      simp [swapOne, hki, hkj]
    have e1 : (if swapOne M r i j r i = true then 1 else 0) = 0 := by simp [swapOne]
    have e2 : (if swapOne M r i j r j = true then 1 else 0) = 1 := by simp [swapOne, hij.symm]
    have e3 : (if M r i = true then 1 else 0) = 1 := by simp [hqi]
    have e4 : (if M r j = true then 1 else 0) = 0 := by simp [hqj]
    beta_reduce
    rw [hrest, e1, e2, e3, e4]
  · unfold rowSum
    congr 1
    refine Finset.filter_congr fun k _ => ?_
    simp [swapOne, hr]

lemma colSum_swapOne_i (hij : i ≠ j) (hqi : M q i = true) :
    colSum (swapOne M q i j) i + 1 = colSum M i := by
  have hset : (univ.filter fun r => swapOne M q i j r i = true) =
      (univ.filter fun r => M r i = true).erase q := by
    ext r
    by_cases hr : r = q
    · subst hr; simp [swapOne]
    · simp [swapOne, hr]
  have hmem : q ∈ univ.filter fun r => M r i = true := by simp [hqi]
  unfold colSum
  rw [hset, Finset.card_erase_of_mem hmem]
  have := Finset.card_pos.2 ⟨q, hmem⟩
  omega

lemma colSum_swapOne_j (hij : i ≠ j) (hqj : M q j = false) :
    colSum (swapOne M q i j) j = colSum M j + 1 := by
  have hset : (univ.filter fun r => swapOne M q i j r j = true) =
      insert q (univ.filter fun r => M r j = true) := by
    ext r
    by_cases hr : r = q
    · subst hr; simp [swapOne, hij.symm]
    · simp [swapOne, hr]
  have hnmem : q ∉ univ.filter fun r => M r j = true := by simp [hqj]
  unfold colSum
  rw [hset, Finset.card_insert_of_notMem hnmem]

lemma colSum_swapOne_other {k : κ} (hki : k ≠ i) (hkj : k ≠ j) :
    colSum (swapOne M q i j) k = colSum M k := by
  unfold colSum
  congr 1
  refine Finset.filter_congr fun r _ => ?_
  by_cases hr : r = q <;> simp [swapOne, hr, hki, hkj]

/-- One transfer of the column sum string: a unit moves from a column `i` to a strictly smaller
column `j`. -/
def Transfer (c c' : κ → ℕ) : Prop :=
  ∃ i j, c j < c i ∧ c' = Function.update (Function.update c i (c i - 1)) j (c j + 1)

/-- CO-335 (the exchange step). If column `i` holds more ones than column `j`, some row has a one in
`i` and a zero in `j`; exchanging these two entries preserves all row sums and changes the column
string by one transfer from `i` to `j`. -/
@[kb "kellertrotter2017" "text (construction in the proof of Theorem 16.12), p. 349"]
theorem exists_swap_step (M : ι → κ → Bool) {i j : κ} (h : colSum M j < colSum M i) :
    ∃ M' : ι → κ → Bool, rowSum M' = rowSum M ∧
      colSum M' = Function.update (Function.update (colSum M) i (colSum M i - 1)) j
        (colSum M j + 1) := by
  have hij : i ≠ j := fun e => by subst e; exact lt_irrefl _ h
  obtain ⟨q, hqi, hqj⟩ := exists_swap_row h
  refine ⟨swapOne M q i j, funext (rowSum_swapOne hij hqi hqj), ?_⟩
  funext k
  have hi := colSum_swapOne_i hij hqi
  have hj := colSum_swapOne_j hij hqj
  by_cases hkj : k = j
  · subst hkj; simp [hj]
  · by_cases hki : k = i
    · subst hki; simp [Function.update_of_ne hij]; omega
    · simp [Function.update_of_ne hkj, Function.update_of_ne hki, colSum_swapOne_other hki hkj]

/-- CO-335. Along any chain of transfers the construction goes through: if some zero-one matrix has
row sum string `R` and column sum string `c`, and `C` is reached from `c` by a chain of transfers (as
in the chain of covers of the book), then a matrix with row sums `R` and column sums `C` exists. -/
@[kb "kellertrotter2017" "text (construction in the proof of Theorem 16.12), p. 349"]
theorem exists_matrix_of_transfers {R : ι → ℕ} {c C : κ → ℕ}
    (h : ∃ M : ι → κ → Bool, rowSum M = R ∧ colSum M = c)
    (hch : Relation.ReflTransGen Transfer c C) :
    ∃ M : ι → κ → Bool, rowSum M = R ∧ colSum M = C := by
  induction hch with
  | refl => exact h
  | tail _ hbc ih =>
    obtain ⟨M, hR, hc⟩ := ih
    obtain ⟨i, j, hlt, rfl⟩ := hbc
    obtain ⟨M', hR', hc'⟩ := exists_swap_step M (i := i) (j := j) (by rw [hc]; exact hlt)
    refine ⟨M', hR'.trans hR, ?_⟩
    rw [hc', hc]

/-- The matrix with the ones of row `r` pushed to the left: row `r` has ones in the first `R r`
columns. Its column sum string is the dual partition of `R`. -/
def leftJustified (n : ℕ) (R : ι → ℕ) : ι → Fin n → Bool := fun r k => decide (k.val < R r)

lemma rowSum_leftJustified {n : ℕ} {R : ι → ℕ} (hR : ∀ r, R r ≤ n) (r : ι) :
    rowSum (leftJustified n R) r = R r := by
  unfold rowSum leftJustified
  simp [Fin.card_filter_val_lt, hR r]

/-- CO-335. The construction of the book: start from the left-justified matrix (column string `Rᵈ`)
and follow a chain of transfers down to `C`; the result is a zero-one matrix with row sum string `R`
and column sum string `C`. -/
@[kb "kellertrotter2017" "text (construction in the proof of Theorem 16.12), p. 349"]
theorem exists_matrix_of_chain {n : ℕ} {R : ι → ℕ} (hR : ∀ r, R r ≤ n) {C : Fin n → ℕ}
    (hch : Relation.ReflTransGen Transfer (colSum (leftJustified n R)) C) :
    ∃ M : ι → Fin n → Bool, rowSum M = R ∧ colSum M = C :=
  exists_matrix_of_transfers
    ⟨leftJustified n R, funext (rowSum_leftJustified hR), rfl⟩ hch

end GaleRyserSwap

end UndergradKB.Combinatorics
