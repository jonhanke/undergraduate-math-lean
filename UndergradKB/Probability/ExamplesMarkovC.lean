import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Choose.Sum
import UndergradKB.Common.Attr
import UndergradKB.Probability.MarkovBasic
import UndergradKB.Probability.MarkovRegular
import UndergradKB.Probability.MarkovPassage
import UndergradKB.Probability.ExamplesMarkov
import UndergradKB.Probability.ExamplesMarkovB

/-! # Worked examples on Markov chains, continued (Land of Oz powers, the maze, Ehrenfest recurrence times)

Grinstead–Snell chapter 11: distributions `u P^n` for the Land of Oz (Examples 11.2, 11.3, 11.18), the rat in a
3x3 maze (Examples 11.22, 11.24, 11.25) and the mean recurrence times of the Ehrenfest urn (Example 11.28). -/

namespace UndergradKB.Probability

open Matrix Finset Filter Topology

/-! ## Land of Oz: powers and distributions -/

/-- Grinstead–Snell Example 11.2 (PR-160): the two-step matrix of the Land of Oz chain is
`P^2 = (1/16) [[7, 3, 6], [6, 4, 6], [6, 3, 7]]` (the book prints it to three decimals). -/
@[kb "grinsteadsnell2006" "Example 11.2, p. 415"]
theorem ozMatrix_sq :
    ozMatrix ^ 2 = !![7/16, 3/16, 6/16; 6/16, 4/16, 6/16; 6/16, 3/16, 7/16] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, ozMatrix, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num

/-- Grinstead–Snell Example 11.2 (PR-160): the three-step matrix of the Land of Oz chain is
`P^3 = (1/64) [[26, 13, 25], [26, 12, 26], [25, 13, 26]]` (the book prints it to three decimals). -/
@[kb "grinsteadsnell2006" "Example 11.2, p. 415"]
theorem ozMatrix_cube :
    ozMatrix ^ 3 = !![26/64, 13/64, 25/64; 26/64, 12/64, 26/64; 25/64, 13/64, 26/64] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, ozMatrix, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num

/-- Grinstead–Snell Example 11.3 (PR-160): from the initial vector `u = (1/3, 1/3, 1/3)` the distribution after
three days is `u P^3 = (77/192, 19/96, 77/192)`, that is `(.401, .198, .401)` to three decimals. -/
@[kb "grinsteadsnell2006" "Example 11.3, p. 417"]
theorem ozMatrix_u3 :
    (![1/3, 1/3, 1/3] : Fin 3 → ℝ) ᵥ* ozMatrix ^ 3 = ![77/192, 19/96, 77/192] := by
  rw [ozMatrix_cube]
  funext j
  fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_succ] <;> norm_num

/-- Grinstead–Snell Example 11.18 (PR-160): from every initial probability vector `u` the distribution
`u P^n` after `n` days of the Land of Oz chain tends to `(2/5, 1/5, 2/5)`. -/
@[kb "grinsteadsnell2006" "Example 11.18, p. 443"]
theorem ozMatrix_distribution_tendsto (u : Fin 3 → ℝ) (hu : ∑ i, u i = 1) (j : Fin 3) :
    Tendsto (fun n => (u ᵥ* ozMatrix ^ n) j) atTop (𝓝 (ozFixed j)) := by
  obtain ⟨w, -, hs, hfix, h⟩ := regular_distribution_tendsto ozMatrix_regular
  have hw := ozMatrix_fixed.2.2 w hs hfix
  rw [← hw]
  exact h u hu j

/-! ## The rat in the maze -/

/-- Grinstead–Snell Example 11.22 (PR-161): the transition matrix of the rat in the 3x3 maze; the rooms
`1, …, 9` of the book are the states `0, …, 8`, arranged on a ring `1-2-3-4-9-8-7-6` with the centre `5`
adjacent to `2, 4, 6, 8`; the rat moves to a uniformly chosen adjacent room. -/
@[kb "grinsteadsnell2006" "Example 11.22, p. 448"]
noncomputable def mazeP : Matrix (Fin 9) (Fin 9) ℝ :=
  !![0, 1/2, 0, 0, 0, 1/2, 0, 0, 0;
     1/3, 0, 1/3, 0, 1/3, 0, 0, 0, 0;
     0, 1/2, 0, 1/2, 0, 0, 0, 0, 0;
     0, 0, 1/3, 0, 1/3, 0, 0, 0, 1/3;
     0, 1/4, 0, 1/4, 0, 1/4, 0, 1/4, 0;
     1/3, 0, 0, 0, 1/3, 0, 1/3, 0, 0;
     0, 0, 0, 0, 0, 1/2, 0, 1/2, 0;
     0, 0, 0, 0, 1/3, 0, 1/3, 0, 1/3;
     0, 0, 0, 1/2, 0, 0, 0, 1/2, 0]

/-- The fixed probability vector `(1/12, 1/8, 1/12, 1/8, 1/6, 1/8, 1/12, 1/8, 1/12)` of the maze chain. -/
noncomputable def mazeFixed : Fin 9 → ℝ := ![1/12, 1/8, 1/12, 1/8, 1/6, 1/8, 1/12, 1/8, 1/12]

/-- Grinstead–Snell Example 11.22 (PR-161): the maze matrix is a transition matrix (row stochastic). -/
@[kb "grinsteadsnell2006" "Example 11.22, p. 448"]
theorem mazeP_mem : mazeP ∈ rowStochastic ℝ (Fin 9) := by
  rw [mem_rowStochastic_iff_sum]
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [mazeP]
  · fin_cases i <;> simp [mazeP, Fin.sum_univ_succ] <;> norm_num

theorem maze_pos2 {a b c : Fin 9} (h1 : 0 < mazeP a b) (h2 : 0 < mazeP b c) : 0 < (mazeP ^ 2) a c := by
  have := pow_add_pos (P := mazeP) mazeP_mem (k := 1) (l := 1) (a := a) (b := b) (c := c) (by rwa [pow_one]) (by rwa [pow_one])
  simpa using this

theorem maze_toCenter (i : Fin 9) : ∃ k > 0, 0 < (mazeP ^ k) i 4 := by
  fin_cases i
  · exact ⟨2, by norm_num, maze_pos2 (b := 1) (by simp [mazeP]) (by simp [mazeP])⟩
  · exact ⟨1, by norm_num, by simp [mazeP]⟩
  · exact ⟨2, by norm_num, maze_pos2 (b := 1) (by simp [mazeP]) (by simp [mazeP])⟩
  · exact ⟨1, by norm_num, by simp [mazeP]⟩
  · exact ⟨2, by norm_num, maze_pos2 (b := 1) (by simp [mazeP]) (by simp [mazeP])⟩
  · exact ⟨1, by norm_num, by simp [mazeP]⟩
  · exact ⟨2, by norm_num, maze_pos2 (b := 5) (by simp [mazeP]) (by simp [mazeP])⟩
  · exact ⟨1, by norm_num, by simp [mazeP]⟩
  · exact ⟨2, by norm_num, maze_pos2 (b := 3) (by simp [mazeP]) (by simp [mazeP])⟩

theorem maze_fromCenter (j : Fin 9) : ∃ k > 0, 0 < (mazeP ^ k) 4 j := by
  fin_cases j
  · exact ⟨2, by norm_num, maze_pos2 (b := 1) (by simp [mazeP]) (by simp [mazeP])⟩
  · exact ⟨1, by norm_num, by simp [mazeP]⟩
  · exact ⟨2, by norm_num, maze_pos2 (b := 1) (by simp [mazeP]) (by simp [mazeP])⟩
  · exact ⟨1, by norm_num, by simp [mazeP]⟩
  · exact ⟨2, by norm_num, maze_pos2 (b := 1) (by simp [mazeP]) (by simp [mazeP])⟩
  · exact ⟨1, by norm_num, by simp [mazeP]⟩
  · exact ⟨2, by norm_num, maze_pos2 (b := 5) (by simp [mazeP]) (by simp [mazeP])⟩
  · exact ⟨1, by norm_num, by simp [mazeP]⟩
  · exact ⟨2, by norm_num, maze_pos2 (b := 3) (by simp [mazeP]) (by simp [mazeP])⟩

/-- Grinstead–Snell Example 11.22 (PR-161): the maze chain is ergodic (every room can be reached from every
room). -/
@[kb "grinsteadsnell2006" "Example 11.22, p. 448"]
theorem mazeP_ergodic : IsErgodicChain mazeP := by
  rw [isErgodicChain_iff]
  refine ⟨mazeP_mem, fun i j => ?_⟩
  obtain ⟨k1, h1, p1⟩ := maze_toCenter i
  obtain ⟨k2, h2, p2⟩ := maze_fromCenter j
  exact ⟨k1 + k2, by omega, pow_add_pos mazeP_mem p1 p2⟩

/-- Grinstead–Snell Example 11.22 (PR-161): the fixed probability vector of the maze chain is
`(1/12, 1/8, 1/12, 1/8, 1/6, 1/8, 1/12, 1/8, 1/12)`, and it is the only one. -/
@[kb "grinsteadsnell2006" "Example 11.22, p. 448"]
theorem mazeP_fixed :
    IsFixedRow mazeP mazeFixed ∧ ∑ j, mazeFixed j = 1 ∧
      ∀ v : Fin 9 → ℝ, ∑ i, v i = 1 → IsFixedRow mazeP v → v = mazeFixed := by
  have h1 : IsFixedRow mazeP mazeFixed := by
    unfold IsFixedRow
    funext j
    fin_cases j <;> simp [mazeFixed, mazeP, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]; all_goals norm_num
  have h2 : ∑ j, mazeFixed j = 1 := by
    simp [mazeFixed, Fin.sum_univ_succ]; norm_num
  obtain ⟨w, -, -, -, huniq⟩ := ergodic_fixed_vector mazeP_ergodic
  refine ⟨h1, h2, fun v hv hvf => ?_⟩
  rw [huniq v hv hvf, huniq mazeFixed h2 h1]

/-- Grinstead–Snell Example 11.25 (PR-161): the mean recurrence times of the maze chain are
`(12, 8, 12, 8, 6, 8, 12, 8, 12)`, the reciprocals of the fixed vector. -/
@[kb "grinsteadsnell2006" "Example 11.25, p. 464"]
theorem mazeP_meanRecurrence (i : Fin 9) :
    meanRecurrence mazeP i = (![12, 8, 12, 8, 6, 8, 12, 8, 12] : Fin 9 → ℝ) i := by
  obtain ⟨w, -, hs, hfix, hr⟩ := meanRecurrence_eq_inv mazeP_ergodic
  have hw := mazeP_fixed.2.2 w hs hfix
  subst hw
  rw [hr]
  fin_cases i <;> simp [mazeFixed]

/-- Grinstead–Snell Example 11.24 (PR-161): in the maze chain the expected number of steps to first reach the
centre room `5` (state `4`) from the rooms `1, 2, 3, 4, 6, 7, 8, 9` is `6, 5, 6, 5, 5, 6, 5, 6`. -/
@[kb "grinsteadsnell2006" "Example 11.24, p. 461"]
theorem mazeP_meanFirstPassage_center (i : Fin 9) :
    meanFirstPassage mazeP i 4 = (![6, 5, 6, 5, 0, 5, 6, 5, 6] : Fin 9 → ℝ) i := by
  have key : ∀ m : Fin 9 → ℝ, (∀ k, k ≠ 4 → m k = 1 + ∑ l, mazeP k l * m l) → m 4 = 0 →
      m = ![6, 5, 6, 5, 0, 5, 6, 5, 6] := by
    intro m h z
    have e0 := h 0 (by decide)
    have e1 := h 1 (by decide)
    have e2 := h 2 (by decide)
    have e3 := h 3 (by decide)
    have e5 := h 5 (by decide)
    have e6 := h 6 (by decide)
    have e7 := h 7 (by decide)
    have e8 := h 8 (by decide)
    simp [mazeP, Fin.sum_univ_succ] at e0 e1 e2 e3 e5 e6 e7 e8
    funext i
    fin_cases i <;> simp <;> linarith
  exact congrFun (key (fun k => meanFirstPassage mazeP k 4)
    (fun k hk => meanFirstPassage_eq mazeP_ergodic hk) (meanFirstPassage_self 4)) i

/-! ## Ehrenfest urn: mean recurrence times -/

/-- Grinstead–Snell Example 11.28 (PR-162): in the Ehrenfest urn with `m ≥ 1` balls the mean recurrence time of
state `i` is `2^m / C(m, i)`. -/
@[kb "grinsteadsnell2006" "Example 11.28, p. 469"]
theorem ehrenfest_meanRecurrence {m : ℕ} (hm : 1 ≤ m) (i : Fin (m + 1)) :
    meanRecurrence (ehrenfest m) i = 2 ^ m / (m.choose i : ℝ) := by
  obtain ⟨w, -, hs, hfix, hr⟩ := meanRecurrence_eq_inv (ehrenfest_ergodic_not_regular hm).1
  have hw := (ehrenfest_fixed hm).2.2 w hs hfix
  subst hw
  rw [hr]
  unfold binomialVec
  rw [one_div, inv_div]

/-- Grinstead–Snell Example 11.28 (PR-162): with `2n` balls (`n ≥ 1`) the mean recurrence time of state `i` is
`2^(2n) / C(2n, i)`; in particular the balanced state `n` recurs on average every `2^(2n) / C(2n, n)` steps. -/
@[kb "grinsteadsnell2006" "Example 11.28, p. 469"]
theorem ehrenfest_two_mul_meanRecurrence {n : ℕ} (hn : 1 ≤ n) (i : Fin (2 * n + 1)) :
    meanRecurrence (ehrenfest (2 * n)) i = 2 ^ (2 * n) / ((2 * n).choose i : ℝ) ∧
      meanRecurrence (ehrenfest (2 * n)) ⟨n, by omega⟩ = 2 ^ (2 * n) / ((2 * n).choose n : ℝ) :=
  ⟨ehrenfest_meanRecurrence (by omega) i, ehrenfest_meanRecurrence (by omega) ⟨n, by omega⟩⟩

end UndergradKB.Probability
