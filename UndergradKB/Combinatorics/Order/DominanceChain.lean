import Mathlib.Data.Fintype.Fin
import Mathlib.Logic.Relation
import UndergradKB.Combinatorics.Order.GaleRyserSwap
import UndergradKB.Combinatorics.Order.Dominance
import UndergradKB.Common.Attr

/-!
# From the dual partition down to `C` by unit transfers (Keller–Trotter, p. 347–349)

In the proof of the Gale–Ryser theorem the book walks from `Rᵈ` down to `C` along a chain of covers
in the dominance order, each cover moving one unit from an earlier position `i` to a later position
`j` (Proposition 16.11).  We prove the existence of such a walk directly: if the string `D` dominates
the nonincreasing string `C` and has the same total, then `C` is reached from `D` by finitely many
unit transfers `Transfer` (each from a position to a later, strictly smaller position).  The step
takes the first position `p` where `D p > C p` and the first later position `q` with `D q < C q`;
all partial sums between `p` and `q` stay at least those of `C`.  The steps are not literally covers
of the poset (the in-between entries need not equal `D p - 1`), but they are the unit transfers the
exchange step of the construction needs.  Combined with `exists_matrix_of_chain` this finishes the
construction.
-/

namespace UndergradKB.Combinatorics

open Finset

namespace GaleRyserSwap

variable {n : ℕ}

lemma psum_succ {m : ℕ} (V : Fin m → ℕ) (j : ℕ) : psum V (j + 1) = psum V j + extZero V j := by
  unfold psum; rw [Finset.sum_range_succ]

lemma extZero_update {D : Fin n → ℕ} (a : Fin n) (v k : ℕ) :
    extZero (Function.update D a v) k = if k = a.val then v else extZero D k := by
  unfold extZero
  by_cases h : k < n
  · by_cases hk : k = a.val
    · have : (⟨k, h⟩ : Fin n) = a := Fin.ext hk
      simp [h, hk, this]
    · have : (⟨k, h⟩ : Fin n) ≠ a := fun e => hk (by rw [← e])
      simp [h, hk, this]
  · have : k ≠ a.val := fun e => h (e ▸ a.2)
    simp [h, this]

/-- The effect of one transfer on the partial sums. -/
lemma psum_transfer (D : Fin n → ℕ) (p q : Fin n) (hpq : p.val < q.val) (hp : 0 < D p) (j : ℕ) :
    psum (Function.update (Function.update D p (D p - 1)) q (D q + 1)) j +
      (if p.val < j ∧ j ≤ q.val then 1 else 0) = psum D j := by
  have hext : ∀ k, extZero (Function.update (Function.update D p (D p - 1)) q (D q + 1)) k +
      (if k = p.val then 1 else 0) = extZero D k + (if k = q.val then 1 else 0) := by
    intro k
    rw [extZero_update, extZero_update]
    have e1 : k = p.val → extZero D k = D p := fun h => h ▸ extZero_lt D p
    have e2 : k = q.val → extZero D k = D q := fun h => h ▸ extZero_lt D q
    split_ifs <;> omega
  induction j with
  | zero => simp [psum]
  | succ j ih =>
    rw [psum_succ, psum_succ]
    have := hext j
    split_ifs at * <;> omega

/-- Lemma used twice: partial sums stay strictly above those of `C` after the first difference. -/
lemma psum_gt {D C : Fin n → ℕ} {p : ℕ} (h0 : psum D p = psum C p)
    (h1 : extZero C p < extZero D p) {N : ℕ}
    (hN : ∀ k, p < k → k < N → extZero C k ≤ extZero D k) :
    ∀ j, p + 1 ≤ j → j ≤ N → psum C j + 1 ≤ psum D j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => intro _; rw [psum_succ, psum_succ]; omega
  | succ j hj ih =>
    intro hjN
    rw [psum_succ, psum_succ]
    have := ih (by omega)
    have := hN j (by omega) (by omega)
    omega

lemma step {D C : Fin n → ℕ} (hC : Antitone C) (hdom : ∀ j, j ≤ n → psum C j ≤ psum D j)
    (hsum : psum D n = psum C n) (hne : D ≠ C) :
    ∃ D', Transfer D D' ∧ (∀ j, j ≤ n → psum C j ≤ psum D' j) ∧ psum D' n = psum C n ∧
      ∑ j ∈ range n, psum D' j < ∑ j ∈ range n, psum D j := by
  classical
  -- the first position where the strings differ
  have hex : ∃ k, k < n ∧ extZero D k ≠ extZero C k := by
    by_contra hno
    push Not at hno
    apply hne
    funext i
    have := hno i i.2
    rwa [extZero_lt, extZero_lt] at this
  obtain ⟨p, hpn, hpne, hpmin⟩ : ∃ p, p < n ∧ extZero D p ≠ extZero C p ∧
      ∀ k, k < p → extZero D k = extZero C k := by
    refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun k hk => ?_⟩
    have := Nat.find_min hex hk
    push Not at this
    exact this (by have := (Nat.find_spec hex).1; omega)
  have h0 : psum D p = psum C p := Finset.sum_congr rfl fun k hk =>
    hpmin k (Finset.mem_range.1 hk)
  have h1 : extZero C p < extZero D p := by
    have := hdom (p + 1) (by omega)
    rw [psum_succ, psum_succ] at this
    omega
  -- the first later position where `D` is smaller
  have hexq : ∃ k, p < k ∧ k < n ∧ extZero D k < extZero C k := by
    by_contra hno
    push Not at hno
    have := psum_gt h0 h1 (N := n) (fun k hk1 hk2 => hno k hk1 hk2) n (by omega) le_rfl
    omega
  obtain ⟨q, ⟨hpq, hqn, hqlt⟩, hqmin⟩ : ∃ q, (p < q ∧ q < n ∧ extZero D q < extZero C q) ∧
      ∀ k, p < k → k < q → extZero C k ≤ extZero D k := by
    refine ⟨Nat.find hexq, Nat.find_spec hexq, fun k hk1 hk2 => ?_⟩
    have := Nat.find_min hexq hk2
    push Not at this
    exact this hk1 (by have := (Nat.find_spec hexq).2.1; omega)
  have hmid := psum_gt h0 h1 (N := q) hqmin
  obtain ⟨pF, hpF⟩ : ∃ pF : Fin n, pF.val = p := ⟨⟨p, hpn⟩, rfl⟩
  obtain ⟨qF, hqF⟩ : ∃ qF : Fin n, qF.val = q := ⟨⟨q, hqn⟩, rfl⟩
  have e1 : extZero D q = D qF := hqF ▸ extZero_lt D qF
  have e2 : extZero D p = D pF := hpF ▸ extZero_lt D pF
  have e3 : extZero C q = C qF := hqF ▸ extZero_lt C qF
  have e4 : extZero C p = C pF := hpF ▸ extZero_lt C pF
  have hDq : D qF < D pF := by
    have : C qF ≤ C pF := hC (show pF ≤ qF from Fin.le_def.2 (by omega))
    omega
  have hDp : 0 < D pF := by omega
  have key := psum_transfer D pF qF (by omega) hDp
  refine ⟨_, ⟨pF, qF, hDq, rfl⟩, ?_, ?_, ?_⟩
  · intro j hj
    have hk := key j
    by_cases hc : pF.val < j ∧ j ≤ qF.val
    · rw [if_pos hc] at hk
      have := hmid j (by omega) (by omega)
      omega
    · rw [if_neg hc] at hk
      have := hdom j hj
      omega
  · have hk := key n
    rw [if_neg (by omega)] at hk
    omega
  · apply Finset.sum_lt_sum
    · intro j _
      have hk := key j
      split_ifs at hk <;> omega
    · refine ⟨p + 1, Finset.mem_range.2 (by omega), ?_⟩
      have hk := key (p + 1)
      rw [if_pos (by omega)] at hk
      omega

/-- CO-335 (chain from `Rᵈ` down to `C`; the content of Proposition 16.11 needed by the
construction). If the string `D` dominates the nonincreasing string `C` (of the same length) and has
the same total, then `C` is reached from `D` by a chain of unit transfers, each moving one unit from
an earlier to a later, strictly smaller entry. -/
@[kb "kellertrotter2017" "Proposition 16.11, p. 347"]
theorem reflTransGen_transfer_of_dominates {D C : Fin n → ℕ} (hC : Antitone C)
    (hdom : Dominates D C) (hsum : ∑ i, D i = ∑ i, C i) :
    Relation.ReflTransGen Transfer D C := by
  have hdom' : ∀ j, j ≤ n → psum C j ≤ psum D j := hdom.2
  have hs : psum D n = psum C n := by
    rw [psum_of_ge D le_rfl, psum_of_ge C le_rfl, hsum]
  have key : ∀ μ (D : Fin n → ℕ), ∑ j ∈ range n, psum D j = μ →
      (∀ j, j ≤ n → psum C j ≤ psum D j) → psum D n = psum C n →
      Relation.ReflTransGen Transfer D C := by
    intro μ
    induction μ using Nat.strong_induction_on with
    | _ μ ih =>
      intro D hμ hd hs
      by_cases hDC : D = C
      · subst hDC; exact Relation.ReflTransGen.refl
      · obtain ⟨D', hT, hd', hs', hlt⟩ := step hC hd hs hDC
        exact Relation.ReflTransGen.head hT (ih _ (hμ ▸ hlt) D' rfl hd' hs')
  exact key _ D rfl hdom' hs

/-- CO-335. Finish of the construction on p. 349: if `Rᵈ` (the column string of the left-justified
matrix) dominates the nonincreasing string `C` and the totals agree, a zero-one matrix with row sum
string `R` and column sum string `C` exists, built by swapping one entry per transfer. -/
@[kb "kellertrotter2017" "text (construction in the proof of Theorem 16.12), p. 349"]
theorem exists_matrix_of_dominates {m : ℕ} {R : Fin m → ℕ} (hR : ∀ r, R r ≤ n) {C : Fin n → ℕ}
    (hC : Antitone C) (hsum : ∑ i, R i = ∑ j, C j)
    (hdom : Dominates (colSum (leftJustified n R)) C) :
    ∃ M : Fin m → Fin n → Bool, rowSum M = R ∧ colSum M = C := by
  refine exists_matrix_of_chain hR (reflTransGen_transfer_of_dominates hC hdom ?_)
  rw [← sum_rowSum_eq_sum_colSum, ← hsum]
  exact Finset.sum_congr rfl fun r _ => rowSum_leftJustified hR r

end GaleRyserSwap

end UndergradKB.Combinatorics
