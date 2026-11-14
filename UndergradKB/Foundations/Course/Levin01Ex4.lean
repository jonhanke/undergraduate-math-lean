import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.Nodup
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import UndergradKB.Common
import UndergradKB.Foundations.Course.Levin01Ex3

/-!
# Course layer: Levin, Discrete Mathematics, Chapter 1, worked examples (wave 4, figures)

Mini sudoku examples whose grids were read from the page images. Digit `k` is `k - 1 : Fin 4`, cells are
`(row, column)` with 0-based indices.
-/

namespace UndergradKB.Foundations.Course

private lemma mini4_ne {p : Fin 4 × Fin 4 → Option (Fin 4)} {s : Fin 4 × Fin 4 → Fin 4}
    (h : MiniSudokuSolution p s) {a b : Fin 4 × Fin 4} (hab : MiniSudokuSameUnit a b) :
    s a ≠ s b := fun e => h.1 a b hab (s a) rfl (by rw [e])

/-- Levin Example 1.4.14: every solution of the mini sudoku with clues 2 at r1c2, 3 at r2c2, 3 at r3c1
and 1 at r4c4 has a 3 in the top-right corner r1c4. -/
@[kb "levin2025" "Example 1.4.14, p. 92"]
theorem levin_ex_1_4_14_sudoku_top_right_three {s : Fin 4 × Fin 4 → Fin 4}
    (h : MiniSudokuSolution
      (fun a => if a = (0, 1) then some 1 else if a = (1, 1) then some 2
        else if a = (2, 0) then some 2 else if a = (3, 3) then some 0 else none) s) :
    s (0, 3) = 2 := by
  have c01 : s (0, 1) = 1 := h.2 _ _ (by simp)
  have c11 : s (1, 1) = 2 := h.2 _ _ (by simp)
  have c20 : s (2, 0) = 2 := h.2 _ _ (by simp)
  have c33 : s (3, 3) = 0 := h.2 _ _ (by simp)
  have hrow := (levin_prop_1_4_4_sudoku_solution_digits h).1
  obtain ⟨c, hc, -⟩ := hrow 0 2
  fin_cases c
  · exfalso
    exact mini4_ne h (a := (0, 0)) (b := (2, 0)) (by simp [MiniSudokuSameUnit]) (by simp_all)
  · exfalso
    simp_all
  · exfalso
    obtain ⟨c', hc', -⟩ := hrow 3 2
    fin_cases c'
    · exact mini4_ne h (a := (3, 0)) (b := (2, 0)) (by simp [MiniSudokuSameUnit]) (by simp_all)
    · exact mini4_ne h (a := (3, 1)) (b := (1, 1)) (by simp [MiniSudokuSameUnit]) (by simp_all)
    · exact mini4_ne h (a := (3, 2)) (b := (0, 2)) (by simp [MiniSudokuSameUnit]) (by simp_all)
    · simp_all
  · simpa using hc

/-- Two solutions of one puzzle that differ at `a` also differ at another cell of `a`'s row. -/
private lemma mini4_row {p : Fin 4 × Fin 4 → Option (Fin 4)} {s s' : Fin 4 × Fin 4 → Fin 4}
    (hs : MiniSudokuSolution p s) (hs' : MiniSudokuSolution p s') (a : Fin 4 × Fin 4)
    (ha : s' a ≠ s a) : ∃ b, b ≠ a ∧ b.1 = a.1 ∧ s' b ≠ s b := by
  by_contra hno
  push Not at hno
  obtain ⟨c, hc, -⟩ := (levin_prop_1_4_4_sudoku_solution_digits hs).1 a.1 (s' a)
  by_cases hb : (a.1, c) = a
  · rw [hb] at hc; exact ha hc.symm
  · have e1 := hno (a.1, c) hb rfl
    have : s' (a.1, c) = s' a := e1.trans hc
    exact mini4_ne hs' (a := (a.1, c)) (b := a) ⟨hb, Or.inl rfl⟩ this

private lemma mini4_col {p : Fin 4 × Fin 4 → Option (Fin 4)} {s s' : Fin 4 × Fin 4 → Fin 4}
    (hs : MiniSudokuSolution p s) (hs' : MiniSudokuSolution p s') (a : Fin 4 × Fin 4)
    (ha : s' a ≠ s a) : ∃ b, b ≠ a ∧ b.2 = a.2 ∧ s' b ≠ s b := by
  by_contra hno
  push Not at hno
  obtain ⟨r, hr, -⟩ := (levin_prop_1_4_4_sudoku_solution_digits hs).2.1 a.2 (s' a)
  by_cases hb : (r, a.2) = a
  · rw [hb] at hr; exact ha hr.symm
  · have e1 := hno (r, a.2) hb rfl
    have : s' (r, a.2) = s' a := e1.trans hr
    exact mini4_ne hs' (a := (r, a.2)) (b := a) ⟨hb, Or.inr (Or.inl rfl)⟩ this

/-- Levin Example 1.4.7: a mini sudoku puzzle with exactly three empty squares that has a solution is solvable,
that is, the solution is unique. (Two different solutions would differ in at least four cells, since the cells
where they differ cannot be alone in a row or column, but they can only differ on empty squares.) -/
@[kb "levin2025" "Example 1.4.7, p. 87"]
theorem levin_ex_1_4_7_three_empty_solvable {p : Fin 4 × Fin 4 → Option (Fin 4)}
    (hE : (Finset.univ.filter (fun a => p a = none)).card = 3)
    (hex : ∃ s, MiniSudokuSolution p s) : MiniSudokuSolvable p := by
  obtain ⟨s, hs⟩ := hex
  refine ⟨s, hs, fun s' hs' => ?_⟩
  by_contra hne
  have hne' : ∃ a, s' a ≠ s a := by
    by_contra hall
    push Not at hall
    exact hne (funext hall)
  obtain ⟨a, ha⟩ := hne'
  have hsub : ∀ x, s' x ≠ s x → p x = none := by
    intro x hx
    cases hpx : p x with
    | none => rfl
    | some d => exact absurd ((hs'.2 x d hpx).trans (hs.2 x d hpx).symm) hx
  obtain ⟨d2, hd2a, hd2r, hd2⟩ := mini4_row hs hs' a ha
  obtain ⟨d3, hd3d2, hd3c, hd3⟩ := mini4_col hs hs' d2 hd2
  obtain ⟨d4, hd4a, hd4c, hd4⟩ := mini4_col hs hs' a ha
  have hd2d4 : d2 ≠ d4 := fun e => hd2a (Prod.ext hd2r (by rw [e, hd4c]))
  have hd3a : d3 ≠ a := fun e => hd2a (Prod.ext hd2r (by rw [← hd3c, e]))
  have hd3d4 : d3 ≠ d4 := fun e => hd2a (Prod.ext hd2r (by rw [← hd3c, e, hd4c]))
  have hnd : [a, d2, d3, d4].Nodup := by
    simp [List.nodup_cons, hd2a, hd2a.symm, hd3a, hd3a.symm, hd4a, hd4a.symm, hd3d2, hd3d2.symm,
      hd2d4, hd2d4.symm, hd3d4, hd3d4.symm]
  have hsubset : [a, d2, d3, d4].toFinset ⊆ Finset.univ.filter (fun a => p a = none) := by
    intro x hx
    simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl | rfl
    · exact hsub _ ha
    · exact hsub _ hd2
    · exact hsub _ hd3
    · exact hsub _ hd4
  have := Finset.card_le_card hsubset
  rw [List.toFinset_card_of_nodup hnd, hE] at this
  simp at this

end UndergradKB.Foundations.Course
