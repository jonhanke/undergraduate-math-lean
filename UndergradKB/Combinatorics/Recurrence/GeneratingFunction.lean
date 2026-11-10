import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Combinatorics.Enumerative.Catalan.Tree
import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Topology.Instances.Rat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import UndergradKB.Common.Attr

/-!
# Generating functions (Keller–Trotter, Chapters 8 and 9)

Formal power series over `ℚ`: the central binomial series `(1 - 4x)^(-1/2)`, the generating
function of rooted unlabeled binary ordered trees (RUBOTs) counted by leaves, and the partition
generating function `∏ 1/(1 - x^m)`.
-/

namespace UndergradKB.Combinatorics.Recurrence

open PowerSeries Finset
open PowerSeries.WithPiTopology

/-! ### The central binomial series -/

/-- The series `∑ C(2n, n) x^n` over `ℚ`. -/
noncomputable def centralBinomSeries : ℚ⟦X⟧ := PowerSeries.mk fun n => (n.centralBinom : ℚ)

@[simp] lemma coeff_centralBinomSeries (n : ℕ) :
    coeff n centralBinomSeries = (n.centralBinom : ℚ) := by
  simp [centralBinomSeries]

lemma constantCoeff_centralBinomSeries : constantCoeff centralBinomSeries = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_centralBinomSeries]
  simp

/-- The differential equation `(1 - 4x) S' = 2 S` for `S = ∑ C(2n,n) x^n`. -/
lemma centralBinomSeries_deriv :
    (1 - C (4 : ℚ) * X) * d⁄dX centralBinomSeries = C (2 : ℚ) * centralBinomSeries := by
  have key : (1 - C (4 : ℚ) * X) * d⁄dX centralBinomSeries =
      d⁄dX centralBinomSeries - C (4 : ℚ) * (X * d⁄dX centralBinomSeries) := by ring
  rw [key]
  ext n
  rcases n with _ | n
  · rw [map_sub, coeff_C_mul, coeff_C_mul, coeff_zero_X_mul, coeff_derivative]
    have h1 : Nat.centralBinom 1 = 2 := by decide
    simp [h1]
  · rw [map_sub, coeff_C_mul, coeff_C_mul, coeff_succ_X_mul, coeff_derivative, coeff_derivative,
      coeff_centralBinomSeries]
    have h := Nat.succ_mul_centralBinom_succ (n + 1)
    have h' : ((n + 2 : ℕ) : ℚ) * ((n + 2).centralBinom : ℚ) =
        2 * (2 * ((n + 1 : ℕ) : ℚ) + 1) * ((n + 1).centralBinom : ℚ) := by
      exact_mod_cast h
    simp only [coeff_centralBinomSeries]
    push_cast at h' ⊢
    linear_combination h'

/-- CO-202. The series `S = ∑ C(2n,n) x^n` is `(1 - 4x)^(-1/2)`: it has constant coefficient 1 and
satisfies `S^2 (1 - 4x) = 1`, i.e. it is the inverse of the square root of `1 - 4x` with constant
term 1. -/
@[kb "kellertrotter2017" "Theorem 8.13, p. 192"]
theorem centralBinomSeries_sq_mul :
    constantCoeff centralBinomSeries = 1 ∧
      centralBinomSeries ^ 2 * (1 - 4 * X) = 1 := by
  refine ⟨constantCoeff_centralBinomSeries, ?_⟩
  have e4 : (4 : ℚ⟦X⟧) = C 4 := (map_ofNat C 4).symm
  have e4' : (C (4 : ℚ) : ℚ⟦X⟧) = C 2 * C 2 := by rw [← map_mul]; norm_num
  rw [e4]
  apply derivative.ext
  · have hd := centralBinomSeries_deriv
    have h4 : d⁄dX (C (4 : ℚ) * X : ℚ⟦X⟧) = C 4 := by
      simp [Derivation.leibniz]
    rw [derivative_one, Derivation.leibniz, derivative_pow, map_sub, derivative_one, h4]
    simp only [smul_eq_mul, Nat.cast_ofNat, zero_sub]
    have e : (2 : ℚ⟦X⟧) = C 2 := (map_ofNat C 2).symm
    rw [e, e4']
    rw [e4'] at hd
    linear_combination (C (2 : ℚ) * centralBinomSeries) * hd
  · simp [constantCoeff_centralBinomSeries]

/-! ### Rooted unlabeled binary ordered trees and the Catalan series -/

/-- The number `c_n` of rooted unlabeled binary ordered trees (RUBOTs) with `n` leaves. A RUBOT is
modelled as Mathlib's `BinaryTree Unit` (every internal node has an ordered pair of subtrees, empty
subtrees being the leaves), so the leaves are the empty subtrees. -/
noncomputable def rubotCount (n : ℕ) : ℕ := {x : BinaryTree Unit | x.numLeaves = n}.ncard

lemma rubotCount_zero : rubotCount 0 = 0 := by
  have : {x : BinaryTree Unit | x.numLeaves = 0} = ∅ := by
    ext x; simp [(BinaryTree.numLeaves_pos x).ne']
  simp [rubotCount, this]

lemma rubotCount_succ (n : ℕ) : rubotCount (n + 1) = catalan n := by
  rw [rubotCount, ← BinaryTree.treesOfNumNodesEq_card_eq_catalan, ← Set.ncard_coe_finset,
    BinaryTree.coe_treesOfNumNodesEq]
  congr 1
  ext x
  simp [BinaryTree.numLeaves_eq_numNodes_succ]

/-- CO-207 (recurrence). `c_1 = 1` and `c_n = ∑_{k=1}^{n-1} c_k c_{n-k}` for `n ≥ 2`. -/
@[kb "kellertrotter2017" "text, p. 229"]
theorem rubotCount_recurrence (n : ℕ) (hn : 2 ≤ n) :
    rubotCount n = ∑ k ∈ Ico 1 n, rubotCount k * rubotCount (n - k) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [rubotCount_succ, catalan_succ', Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr (by simp) fun i hi => ?_
  have hi' : i < m + 1 := by simpa using hi
  simp only [mem_range] at hi
  rw [show 1 + i = i + 1 by ring, rubotCount_succ, show m + 2 - (i + 1) = (m - i) + 1 by omega,
    rubotCount_succ]

lemma rubotCount_one : rubotCount 1 = 1 := by
  rw [rubotCount_succ]; simp

/-- The generating function `C(x) = ∑_{n ≥ 1} c_n x^n` of RUBOTs by leaf count, over `ℚ`. -/
noncomputable def rubotSeries : ℚ⟦X⟧ := PowerSeries.mk fun n => (rubotCount n : ℚ)

lemma rubotSeries_eq : rubotSeries =
    X * PowerSeries.map (Nat.castRingHom ℚ) PowerSeries.catalanSeries := by
  ext n
  rcases n with _ | n
  · simp [rubotSeries, rubotCount_zero]
  · rw [coeff_succ_X_mul]
    simp [rubotSeries, rubotCount_succ]

/-- CO-207 (functional equation). `C(x) = x + C(x)^2`. -/
@[kb "kellertrotter2017" "text, p. 229"]
theorem rubotSeries_eq_X_add_sq : rubotSeries = X + rubotSeries ^ 2 := by
  have h := congrArg (PowerSeries.map (Nat.castRingHom ℚ)) PowerSeries.catalanSeries_sq_mul_X_add_one
  simp only [map_add, map_mul, map_pow, map_one, PowerSeries.map_X] at h
  rw [rubotSeries_eq]
  linear_combination (-(X : ℚ⟦X⟧)) * h

/-- CO-208. `C(x) = (1 - √(1 - 4x))/2`: the series `1 - 2C(x)` has constant coefficient 1 and
squares to `1 - 4x` (so it is the square root of `1 - 4x` with constant term 1). -/
@[kb "kellertrotter2017" "Theorem 9.28, p. 231"]
theorem rubotSeries_sqrt :
    constantCoeff (1 - 2 * rubotSeries) = 1 ∧
      (1 - 2 * rubotSeries) ^ 2 = 1 - 4 * X := by
  refine ⟨?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply]
    have e2 : (2 : ℚ⟦X⟧) = C 2 := (map_ofNat C 2).symm
    rw [e2]
    simp [rubotSeries, rubotCount_zero]
  · have h := rubotSeries_eq_X_add_sq
    linear_combination (-4 : ℚ⟦X⟧) * h

/-- CO-208 (coefficients). The number of RUBOTs with `n + 1` leaves is
`(1/(n+1)) C(2n, n)` (the Catalan number `C(n)`). -/
@[kb "kellertrotter2017" "Theorem 9.28, p. 231"]
theorem rubotCount_eq_centralBinom_div (n : ℕ) :
    (rubotCount (n + 1) : ℚ) = (n.centralBinom : ℚ) / (n + 1) := by
  rw [rubotCount_succ, eq_div_iff (by positivity)]
  have := succ_mul_catalan_eq_centralBinom n
  exact_mod_cast (by rw [mul_comm]; exact this : catalan n * (n + 1) = n.centralBinom)

/-! ### The partition generating function -/

lemma tsum_pow_eq_inv_one_sub (m : ℕ) (hm : 0 < m) :
    ∑' j : ℕ, (X : ℚ⟦X⟧) ^ (m * j) = (1 - X ^ m)⁻¹ := by
  have h0 : constantCoeff ((X : ℚ⟦X⟧) ^ m) = 0 := by simp [hm.ne']
  have h := tsum_pow_mul_one_sub_of_constantCoeff_eq_zero h0
  simp_rw [pow_mul]
  rw [PowerSeries.eq_inv_iff_mul_eq_one (by simp [hm.ne'])]
  exact h

/-- CO-203. The generating function of the partition numbers `p(n)` is `∏_{m ≥ 1} 1/(1 - x^m)`
(an infinite product of power series, converging coefficientwise). -/
@[kb "kellertrotter2017" "text, p. 192"]
theorem hasProd_partition_card :
    HasProd (fun i : ℕ => (1 - X ^ (i + 1) : ℚ⟦X⟧)⁻¹)
      (PowerSeries.mk fun n => (Fintype.card (Nat.Partition n) : ℚ)) := by
  have h := Nat.Partition.hasProd_powerSeriesMk_card_restricted ℚ (fun _ => True)
  have e1 : (fun n => ((Nat.Partition.restricted n (fun _ => True)).card : ℚ)) =
      fun n => (Fintype.card (Nat.Partition n) : ℚ) := by
    funext n
    simp [Nat.Partition.restricted]
  have e2 : (fun i : ℕ => if (fun _ : ℕ => True) (i + 1) then
      ∑' j : ℕ, (X : ℚ⟦X⟧) ^ ((i + 1) * j) else 1) = fun i : ℕ => (1 - X ^ (i + 1) : ℚ⟦X⟧)⁻¹ := by
    funext i
    simp only [ite_true]
    exact tsum_pow_eq_inv_one_sub (i + 1) (Nat.succ_pos i)
  rw [e1] at h
  rw [e2] at h
  exact h

end UndergradKB.Combinatorics.Recurrence
