import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fintype.Fin
import UndergradKB.Common.Attr

/-!
# The dominance order on partitions and conjugate partitions (Keller–Trotter, Section 16.5)

A *string* of length `m` is a function `Fin m → ℕ`; a partition of `t` is a nonincreasing string of positive entries
with sum `t`.  Following the book, a string `V` of length `m` dominates a string `W` of length `n` when `m ≤ n` and for
each `j ≤ m` the sum of the first `j` entries of `V` is at least the sum of the first `j` entries of `W`.

* `Dominates`: the dominance relation (CO-179); it is reflexive and transitive, and antisymmetric on strings of the same
  length, so it is a partial order on `P(t)`;
* `conj`: the dual (conjugate) partition: `conj R k` is the number of entries of `R` that exceed `k` (the entries of the
  string are indexed from `0`, so this is the book's "number of entries at least `k + 1`");
* `psum_conj`: the sum of the first `j` entries of `conj R` is `∑ i, min (R i) j`.

Note: in the book's example the dual of `(8,6,6,6,5,5,3,1,1,1)` is printed with first entry `8`; the correct first
entry is `10`, the number of entries (the sum must be `42`).
-/

namespace UndergradKB.Combinatorics

open Finset

/-- The string `V : Fin m → ℕ` extended by zero to all of `ℕ`. -/
def extZero {m : ℕ} (V : Fin m → ℕ) (k : ℕ) : ℕ := if h : k < m then V ⟨k, h⟩ else 0

/-- The sum of the first `j` entries of a string (all of them if `j` exceeds the length). -/
def psum {m : ℕ} (V : Fin m → ℕ) (j : ℕ) : ℕ := ∑ k ∈ range j, extZero V k

/-- CO-179. The dominance relation: a string `V` of length `m` dominates a string `W` of length `n` when `m ≤ n` and
the partial sums of `V` are at least those of `W` up to the length of `V`. On the partitions of a fixed `t` this is the
partial order `V ≥ W` of the book. -/
@[kb "kellertrotter2017" "Definition (unnumbered) dominance order on P(t), p. 347"]
def Dominates {m n : ℕ} (V : Fin m → ℕ) (W : Fin n → ℕ) : Prop :=
  m ≤ n ∧ ∀ j, j ≤ m → psum W j ≤ psum V j

/-- A partition of `t` as a string: nonincreasing, positive entries, with sum `t`. -/
structure IsPartitionString {m : ℕ} (V : Fin m → ℕ) (t : ℕ) : Prop where
  antitone : Antitone V
  pos : ∀ i, 0 < V i
  sum_eq : ∑ i, V i = t

lemma extZero_lt {m : ℕ} (V : Fin m → ℕ) (i : Fin m) : extZero V i = V i := by
  simp [extZero, i.2]

lemma extZero_ge {m : ℕ} (V : Fin m → ℕ) {k : ℕ} (h : m ≤ k) : extZero V k = 0 := by
  simp [extZero, not_lt.2 h]

lemma psum_of_ge {m : ℕ} (V : Fin m → ℕ) {j : ℕ} (h : m ≤ j) : psum V j = ∑ i, V i := by
  unfold psum
  rw [← Finset.sum_range_add_sum_Ico _ h, Finset.sum_eq_zero (s := Finset.Ico m j)
    (fun k hk => extZero_ge V (Finset.mem_Ico.1 hk).1), add_zero, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun i _ => extZero_lt V i

/-- Dominance is reflexive. -/
theorem Dominates.refl {m : ℕ} (V : Fin m → ℕ) : Dominates V V := ⟨le_rfl, fun _ _ => le_rfl⟩

/-- Dominance is transitive. -/
theorem Dominates.trans {m n p : ℕ} {U : Fin m → ℕ} {V : Fin n → ℕ} {W : Fin p → ℕ}
    (h1 : Dominates U V) (h2 : Dominates V W) : Dominates U W :=
  ⟨h1.1.trans h2.1, fun j hj => (h2.2 j (hj.trans h1.1)).trans (h1.2 j hj)⟩

/-- Dominance is antisymmetric (on strings of the same length). -/
theorem Dominates.antisymm {m : ℕ} {V W : Fin m → ℕ} (h1 : Dominates V W) (h2 : Dominates W V) : V = W := by
  funext i
  have e : ∀ j, j ≤ m → psum V j = psum W j := fun j hj => le_antisymm (h2.2 j hj) (h1.2 j hj)
  have hi := e i (i.2.le)
  have hi' := e (i + 1) i.2
  unfold psum at hi hi'
  rw [Finset.sum_range_succ, Finset.sum_range_succ, hi] at hi'
  have := Nat.add_left_cancel hi'
  rwa [extZero_lt, extZero_lt] at this

/-! ### Conjugate partitions -/

/-- The number of entries of a string that exceed `k`. -/
def conjNat {ι : Type*} [Fintype ι] (R : ι → ℕ) (k : ℕ) : ℕ := (Finset.univ.filter fun i => k < R i).card

/-- CO-179 (dual partition). The dual (conjugate) of the string `R`: a string of length `max R` whose `k`-th entry
(from `0`) is the number of entries of `R` larger than `k`. For a partition this is the book's dual `Rᵈ`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) dual partition, p. 348"]
def conj {m : ℕ} (R : Fin m → ℕ) : Fin (Finset.univ.sup R) → ℕ := fun k => conjNat R k

lemma conjNat_eq_zero {m : ℕ} (R : Fin m → ℕ) {k : ℕ} (h : Finset.univ.sup R ≤ k) : conjNat R k = 0 := by
  unfold conjNat
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _ hik
  exact absurd (lt_of_lt_of_le hik ((Finset.le_sup (f := R) (Finset.mem_univ i)).trans h)) (lt_irrefl _)

lemma extZero_conj {m : ℕ} (R : Fin m → ℕ) (k : ℕ) : extZero (conj R) k = conjNat R k := by
  by_cases h : k < Finset.univ.sup R
  · simp [extZero, h, conj]
  · rw [extZero_ge _ (not_lt.1 h), conjNat_eq_zero R (not_lt.1 h)]

/-- The sum of the first `s` entries of the conjugate: `∑_{k<s} #{i : k < R i} = ∑_i min (R i, s)`. -/
theorem psum_conj {m : ℕ} (R : Fin m → ℕ) (s : ℕ) : psum (conj R) s = ∑ i, min (R i) s := by
  unfold psum
  simp_rw [extZero_conj, conjNat, Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.card_filter, show (range s).filter (fun k => k < R i) = range (min (R i) s) by
    ext k; simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]; tauto, Finset.card_range]

end UndergradKB.Combinatorics
