import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Linarith
import UndergradKB.Common

/-!
# Course layer: Levin, Discrete Mathematics, Chapter 1, worked examples (wave 4)

Logic examples (converse, contrapositive, truth table) and the mini sudoku results.
A mini sudoku grid is a map `Fin 4 × Fin 4 → Fin 4`; the digit `k` of the book is `k - 1 : Fin 4`.
-/

namespace UndergradKB.Foundations.Course

/-- Levin Example 1.2.8: the contrapositive of an implication is equivalent to it, and the inverse is
equivalent to the converse (it is the contrapositive of the converse). -/
@[kb "levin2025" "Example 1.2.8, p. 55"]
theorem levin_ex_1_2_8_converse_contrapositive_inverse :
    (∀ P Q : Prop, (P → Q) ↔ (¬ Q → ¬ P)) ∧ (∀ P Q : Prop, (Q → P) ↔ (¬ P → ¬ Q)) ∧
    ¬ (∀ P Q : Prop, (P → Q) ↔ (Q → P)) := by
  refine ⟨fun _ _ => by tauto, fun _ _ => by tauto, fun h => ?_⟩
  exact (h False True).1 (fun f => f.elim) trivial

/-- Levin Example 1.2.11: from `P → Q` one gets `Q` from `P` and `¬P` from `¬Q`, but nothing follows from
`Q` alone (it does not give `P`) nor from `¬P` alone (it does not give `¬Q`). -/
@[kb "levin2025" "Example 1.2.11, p. 57"]
theorem levin_ex_1_2_11_conclusions :
    (∀ P Q : Prop, (P → Q) → P → Q) ∧ (∀ P Q : Prop, (P → Q) → ¬ Q → ¬ P) ∧
    ¬ (∀ P Q : Prop, (P → Q) → Q → P) ∧ ¬ (∀ P Q : Prop, (P → Q) → ¬ P → ¬ Q) := by
  refine ⟨fun _ _ h => h, fun _ _ h hq hp => hq (h hp), fun h => ?_, fun h => ?_⟩
  · exact h False True (fun a => a.elim) trivial
  · exact h False True (fun a => a.elim) not_false trivial

/-- Levin Example 1.2.12: "P if Q" is `Q → P`, "P only if Q" is `P → Q`, and a biconditional is
exactly the conjunction of these two parts. -/
@[kb "levin2025" "Example 1.2.12, p. 58"]
theorem levin_ex_1_2_12_if_only_if (P Q : Prop) :
    (P ↔ Q) ↔ ((Q → P) ∧ (P → Q)) :=
  ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- Levin Example 1.2.13: rephrasings of `P → Q`: the contrapositive and `¬P ∨ Q` are equivalent to it,
while its converse is not. -/
@[kb "levin2025" "Example 1.2.13, p. 58"]
theorem levin_ex_1_2_13_rephrasings (P Q : Prop) :
    ((P → Q) ↔ (¬ Q → ¬ P)) ∧ ((P → Q) ↔ (¬ P ∨ Q)) ∧ ((Q → P) ↔ (¬ P → ¬ Q)) :=
  ⟨by tauto, by tauto, by tauto⟩

/-- Levin Example 1.2.15: modelling the four suits as `Fin 4` with suits `2, 3` black and `3` the spade:
being a spade implies being black, but being black does not imply being a spade. -/
@[kb "levin2025" "Example 1.2.15, p. 59"]
theorem levin_ex_1_2_15_spade_black :
    (∀ s : Fin 4, s = 3 → 2 ≤ s) ∧ ¬ (∀ s : Fin 4, 2 ≤ s → s = 3) := by
  refine ⟨by decide, by decide⟩

/-- Levin Example 1.3.3: truth table of `¬P ∨ Q` (rows TT, TF, FT, FF) and its equivalence with `P → Q`. -/
@[kb "levin2025" "Example 1.3.3, p. 66"]
theorem levin_ex_1_3_3_truth_table_not_or :
    ([(true, true), (true, false), (false, true), (false, false)].map
        (fun p : Bool × Bool => (!p.1 || p.2)) = [true, false, true, true]) ∧
    ∀ P Q : Prop, (¬ P ∨ Q) ↔ (P → Q) :=
  ⟨by decide, fun _ _ => imp_iff_not_or.symm⟩

/-! ### Mini sudoku -/

/-- Two distinct cells share a row, a column, or a `2 × 2` box. -/
def MiniSudokuSameUnit (a b : Fin 4 × Fin 4) : Prop :=
  a ≠ b ∧ (a.1 = b.1 ∨ a.2 = b.2 ∨ (a.1.val / 2 = b.1.val / 2 ∧ a.2.val / 2 = b.2.val / 2))

/-- A (partial) mini sudoku puzzle is valid: no digit repeats within a row, column or box. -/
def MiniSudokuValid (p : Fin 4 × Fin 4 → Option (Fin 4)) : Prop :=
  ∀ a b, MiniSudokuSameUnit a b → ∀ d, p a = some d → p b ≠ some d

/-- `s` is a solution of `p`: a fully filled valid grid agreeing with every given entry. -/
def MiniSudokuSolution (p : Fin 4 × Fin 4 → Option (Fin 4)) (s : Fin 4 × Fin 4 → Fin 4) : Prop :=
  MiniSudokuValid (fun a => some (s a)) ∧ ∀ a d, p a = some d → s a = d

/-- A puzzle is solvable when it has exactly one solution. -/
def MiniSudokuSolvable (p : Fin 4 × Fin 4 → Option (Fin 4)) : Prop :=
  ∃! s, MiniSudokuSolution p s

private lemma mini_ne_of_unit {p : Fin 4 × Fin 4 → Option (Fin 4)} {s : Fin 4 × Fin 4 → Fin 4}
    (h : MiniSudokuSolution p s) {a b : Fin 4 × Fin 4} (hab : MiniSudokuSameUnit a b) :
    s a ≠ s b := fun e => h.1 a b hab (s a) rfl (by rw [e])

private lemma mini_exists_of_injOn (B : Finset (Fin 4 × Fin 4)) (hB : B.card = 4)
    (s : Fin 4 × Fin 4 → Fin 4) (hi : Set.InjOn s B) (d : Fin 4) : ∃ a ∈ B, s a = d := by
  have h1 : (B.image s).card = 4 := by rw [Finset.card_image_of_injOn hi, hB]
  have h2 := Finset.eq_univ_of_card (B.image s) (by simpa using h1)
  have hd : d ∈ B.image s := by rw [h2]; exact Finset.mem_univ d
  simpa using hd

/-- Levin Proposition 1.4.4: in a solution of a mini sudoku, every digit occurs exactly once in each row,
each column and each box, and so exactly four times in total. -/
@[kb "levin2025" "Proposition 1.4.4, p. 85"]
theorem levin_prop_1_4_4_sudoku_solution_digits
    {p : Fin 4 × Fin 4 → Option (Fin 4)} {s : Fin 4 × Fin 4 → Fin 4}
    (h : MiniSudokuSolution p s) :
    (∀ r d, ∃! c, s (r, c) = d) ∧ (∀ c d, ∃! r, s (r, c) = d) ∧
    (∀ (i j : Fin 2) d, ∃! a : Fin 4 × Fin 4,
      a.1.val / 2 = i.val ∧ a.2.val / 2 = j.val ∧ s a = d) ∧
    (∀ d, (Finset.univ.filter (fun a => s a = d)).card = 4) := by
  have hrc : ∀ r : Fin 4, (Finset.univ.filter (fun a : Fin 4 × Fin 4 => a.1 = r)).card = 4 := by decide
  have hcc : ∀ c : Fin 4, (Finset.univ.filter (fun a : Fin 4 × Fin 4 => a.2 = c)).card = 4 := by decide
  have hbc : ∀ i j : Fin 2, (Finset.univ.filter
      (fun a : Fin 4 × Fin 4 => a.1.val / 2 = i.val ∧ a.2.val / 2 = j.val)).card = 4 := by decide
  have row : ∀ r d, ∃! c, s (r, c) = d := by
    intro r d
    have hi : Set.InjOn s ↑(Finset.univ.filter (fun a : Fin 4 × Fin 4 => a.1 = r)) := by
      intro a ha b hb e
      by_contra hne
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
      exact mini_ne_of_unit h ⟨hne, Or.inl (ha.trans hb.symm)⟩ e
    obtain ⟨⟨r', c⟩, ha, hs⟩ := mini_exists_of_injOn
      (Finset.univ.filter (fun a : Fin 4 × Fin 4 => a.1 = r)) (hrc r) s hi d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    subst ha
    refine ⟨c, hs, fun c' hc' => ?_⟩
    by_contra hne
    exact mini_ne_of_unit h (a := (r', c')) (b := (r', c)) ⟨fun e => hne (by simpa using e),
      Or.inl rfl⟩ (hc'.trans hs.symm)
  have col : ∀ c d, ∃! r, s (r, c) = d := by
    intro c d
    have hi : Set.InjOn s ↑(Finset.univ.filter (fun a : Fin 4 × Fin 4 => a.2 = c)) := by
      intro a ha b hb e
      by_contra hne
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
      exact mini_ne_of_unit h ⟨hne, Or.inr (Or.inl (ha.trans hb.symm))⟩ e
    obtain ⟨⟨r, c'⟩, ha, hs⟩ := mini_exists_of_injOn
      (Finset.univ.filter (fun a : Fin 4 × Fin 4 => a.2 = c)) (hcc c) s hi d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    subst ha
    refine ⟨r, hs, fun r' hr' => ?_⟩
    by_contra hne
    exact mini_ne_of_unit h (a := (r', c')) (b := (r, c')) ⟨fun e => hne (by simpa using e),
      Or.inr (Or.inl rfl)⟩ (hr'.trans hs.symm)
  have box : ∀ (i j : Fin 2) d, ∃! a : Fin 4 × Fin 4,
      a.1.val / 2 = i.val ∧ a.2.val / 2 = j.val ∧ s a = d := by
    intro i j d
    have hi : Set.InjOn s ↑(Finset.univ.filter
        (fun a : Fin 4 × Fin 4 => a.1.val / 2 = i.val ∧ a.2.val / 2 = j.val)) := by
      intro a ha b hb e
      by_contra hne
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
      exact mini_ne_of_unit h ⟨hne, Or.inr (Or.inr ⟨ha.1.trans hb.1.symm, ha.2.trans hb.2.symm⟩)⟩ e
    obtain ⟨a, ha, hs⟩ := mini_exists_of_injOn (Finset.univ.filter
      (fun a : Fin 4 × Fin 4 => a.1.val / 2 = i.val ∧ a.2.val / 2 = j.val))
      (hbc i j) s hi d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    refine ⟨a, ⟨ha.1, ha.2, hs⟩, fun b hb => ?_⟩
    by_contra hne
    exact mini_ne_of_unit h (a := b) (b := a) ⟨hne, Or.inr (Or.inr ⟨hb.1.trans ha.1.symm,
      hb.2.1.trans ha.2.symm⟩)⟩ (hb.2.2.trans hs.symm)
  refine ⟨row, col, box, fun d => ?_⟩
  have hf : ∀ r : Fin 4, ((Finset.univ.filter (fun a : Fin 4 × Fin 4 => s a = d)).filter
      (fun a => a.1 = r)).card = 1 := by
    intro r
    obtain ⟨c, hc, hu⟩ := row r d
    rw [Finset.card_eq_one]
    refine ⟨(r, c), ?_⟩
    ext ⟨r', c'⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨h1, rfl⟩; exact ⟨rfl, hu _ h1⟩
    · rintro ⟨rfl, rfl⟩; exact ⟨hc, rfl⟩
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  simp [hf]

/-- Levin Example 1.4.6: in a solution of the (valid) mini sudoku with clues `1, 3` in the second and third
squares of the top row and `1, 3` in rows 2 and 3 of the last column, a `2` in the top-left square forces a
`2` in the bottom-right square. Digit `k` is encoded as `k - 1`. -/
@[kb "levin2025" "Example 1.4.6, p. 86"]
theorem levin_ex_1_4_6_sudoku_two_corners
    {s : Fin 4 × Fin 4 → Fin 4}
    (h : MiniSudokuSolution
      (fun a => if a = (0, 1) then some 0 else if a = (0, 2) then some 2
        else if a = (1, 3) then some 0 else if a = (2, 3) then some 2 else none) s)
    (h2 : s (0, 0) = 1) : s (3, 3) = 1 := by
  have c01 : s (0, 1) = 0 := h.2 _ _ (by simp)
  have c02 : s (0, 2) = 2 := h.2 _ _ (by simp)
  have c13 : s (1, 3) = 0 := h.2 _ _ (by simp)
  have c23 : s (2, 3) = 2 := h.2 _ _ (by simp)
  have n := fun a b (hab : MiniSudokuSameUnit a b) => mini_ne_of_unit h hab
  have t3 : s (0, 3) = 3 := by
    have e1 := n (0, 3) (0, 0) (by simp [MiniSudokuSameUnit])
    have e2 := n (0, 3) (0, 1) (by simp [MiniSudokuSameUnit])
    have e3 := n (0, 3) (0, 2) (by simp [MiniSudokuSameUnit])
    rw [h2] at e1; rw [c01] at e2; rw [c02] at e3
    omega
  have e1 := n (3, 3) (0, 3) (by simp [MiniSudokuSameUnit])
  have e2 := n (3, 3) (1, 3) (by simp [MiniSudokuSameUnit])
  have e3 := n (3, 3) (2, 3) (by simp [MiniSudokuSameUnit])
  rw [t3] at e1; rw [c13] at e2; rw [c23] at e3
  omega

/-- Levin Example 1.4.10: a solvable mini sudoku puzzle is valid. -/
@[kb "levin2025" "Example 1.4.10, p. 89"]
theorem levin_ex_1_4_10_sudoku_solvable_valid {p : Fin 4 × Fin 4 → Option (Fin 4)}
    (hp : MiniSudokuSolvable p) : MiniSudokuValid p := by
  obtain ⟨s, hs, -⟩ := hp
  intro a b hab d ha hb
  have h1 := hs.2 a d ha
  have h2 := hs.2 b d hb
  exact mini_ne_of_unit hs hab (h1.trans h2.symm)

end UndergradKB.Foundations.Course
