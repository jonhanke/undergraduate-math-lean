import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin
import UndergradKB.Common.Attr
import UndergradKB.Probability.MarkovBasic
import UndergradKB.Probability.MarkovRegular
import UndergradKB.Probability.MarkovAbsorbing
import UndergradKB.Probability.MarkovPassage

/-! # Worked examples on Markov chains (Land of Oz)

Grinstead–Snell chapter 11: the Land of Oz weather chain (Examples 11.1, 11.19, 11.20, 11.27). States
`0, 1, 2` are Rain, Nice, Snow. -/

namespace UndergradKB.Probability

open Matrix Finset Filter Topology

/-- Grinstead–Snell Example 11.1 (PR-143): the Land of Oz transition matrix on the states Rain, Nice, Snow. -/
@[kb "grinsteadsnell2006" "Example 11.1, p. 414"]
noncomputable def ozMatrix : Matrix (Fin 3) (Fin 3) ℝ := !![1/2, 1/4, 1/4; 1/2, 0, 1/2; 1/4, 1/4, 1/2]

/-- Grinstead–Snell Example 11.1 (PR-143): the Land of Oz matrix is a transition matrix (row stochastic). -/
@[kb "grinsteadsnell2006" "Example 11.1, p. 414"]
theorem ozMatrix_mem : ozMatrix ∈ rowStochastic ℝ (Fin 3) := by
  rw [mem_rowStochastic_iff_sum]
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [ozMatrix]
  · fin_cases i <;> simp [ozMatrix, Fin.sum_univ_succ] <;> norm_num

/-- The Land of Oz fixed probability vector `(2/5, 1/5, 2/5)`. -/
noncomputable def ozFixed : Fin 3 → ℝ := ![2/5, 1/5, 2/5]

/-- Grinstead–Snell Example 11.19 (PR-143): the Land of Oz chain is regular (`P^2` has all entries positive). -/
@[kb "grinsteadsnell2006" "Example 11.19, p. 444"]
theorem ozMatrix_regular : IsRegularChain ozMatrix := by
  refine ⟨ozMatrix_mem, 2, by norm_num, fun i j => ?_⟩
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, ozMatrix, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num

/-- Grinstead–Snell Example 11.20 (PR-143): the fixed probability vector of the Land of Oz chain is
`(2/5, 1/5, 2/5)`, and it is the only fixed probability vector. -/
@[kb "grinsteadsnell2006" "Example 11.20, p. 444"]
theorem ozMatrix_fixed :
    IsFixedRow ozMatrix ozFixed ∧ ∑ j, ozFixed j = 1 ∧
      ∀ v : Fin 3 → ℝ, ∑ i, v i = 1 → IsFixedRow ozMatrix v → v = ozFixed := by
  have h1 : IsFixedRow ozMatrix ozFixed := by
    unfold IsFixedRow
    funext j
    fin_cases j <;> simp [ozFixed, ozMatrix, Matrix.vecMul, dotProduct, Fin.sum_univ_succ] <;> norm_num
  have h2 : ∑ j, ozFixed j = 1 := by
    simp [ozFixed, Fin.sum_univ_succ]; norm_num
  obtain ⟨w, -, -, -, huniq⟩ := regular_fixed_vector ozMatrix_regular
  refine ⟨h1, h2, fun v hv hvf => ?_⟩
  rw [huniq v hv hvf, huniq ozFixed h2 h1]

/-- Grinstead–Snell Example 11.19 (PR-143): the powers `P^n` of the Land of Oz matrix converge to the matrix
all of whose rows are `(2/5, 1/5, 2/5)`. -/
@[kb "grinsteadsnell2006" "Example 11.19, p. 444"]
theorem ozMatrix_pow_tendsto (i j : Fin 3) :
    Tendsto (fun n => (ozMatrix ^ n) i j) atTop (𝓝 (ozFixed j)) := by
  obtain ⟨w, -, hs, hw⟩ := regular_pow_tendsto ozMatrix_regular
  have hfix : IsFixedRow ozMatrix w := isFixedRow_of_pow_tendsto (i0 := 0) (hw 0)
  have := (ozMatrix_fixed.2.2 w hs hfix)
  rw [← this]
  exact hw i j

/-- Grinstead–Snell Example 11.27 (PR-143): the mean recurrence times of the Land of Oz chain are
`(5/2, 5, 5/2)`, the reciprocals of the fixed vector. -/
@[kb "grinsteadsnell2006" "Example 11.27, p. 468"]
theorem ozMatrix_meanRecurrence :
    meanRecurrence ozMatrix 0 = 5 / 2 ∧ meanRecurrence ozMatrix 1 = 5 ∧ meanRecurrence ozMatrix 2 = 5 / 2 := by
  obtain ⟨w, -, hs, hfix, hr⟩ := meanRecurrence_eq_inv ozMatrix_regular.isErgodicChain
  have hw := ozMatrix_fixed.2.2 w hs hfix
  subst hw
  simp [hr, ozFixed]

/-- The matrix `Z = (I - P + W)⁻¹` of Example 11.27. -/
noncomputable def ozZ : Matrix (Fin 3) (Fin 3) ℝ := !![86/75, 1/25, -14/75; 2/25, 21/25, 2/25; -14/75, 1/25, 86/75]

theorem ozZ_mul : ozZ * (1 - ozMatrix + rowsMatrix ozFixed) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ozZ, ozMatrix, ozFixed, rowsMatrix, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ] <;> norm_num

/-- Grinstead–Snell Example 11.27 (PR-143): the mean first passage matrix of the Land of Oz chain,
`M = [[0, 4, 10/3], [8/3, 0, 8/3], [10/3, 4, 0]]`. -/
@[kb "grinsteadsnell2006" "Example 11.27, p. 468"]
theorem ozMatrix_meanFirstPassage (i j : Fin 3) :
    meanFirstPassage ozMatrix i j = (!![0, 4, 10/3; 8/3, 0, 8/3; 10/3, 4, 0] : Matrix (Fin 3) (Fin 3) ℝ) i j := by
  obtain ⟨w, -, hs, hfix, -, hm⟩ := meanFirstPassage_eq_fundamental ozMatrix_regular.isErgodicChain
  have hw := ozMatrix_fixed.2.2 w hs hfix
  subst hw
  have hinv : (1 - ozMatrix + rowsMatrix ozFixed)⁻¹ = ozZ := Matrix.inv_eq_left_inv ozZ_mul
  rw [hm, hinv]
  fin_cases i <;> fin_cases j <;> simp [ozZ, ozFixed] <;> norm_num

end UndergradKB.Probability
