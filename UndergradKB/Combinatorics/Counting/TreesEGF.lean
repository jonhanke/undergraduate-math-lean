import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Combinatorics.Enumerative.Catalan.Tree
import Mathlib.Data.Tree.Basic
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Data.Nat.Choose.Central
import UndergradKB.Common.Attr

/-!
# Central binomial asymptotics, binary trees, exponential generating functions

Source: Keller--Trotter, *Applied Combinatorics* (2017), pp. 194, 229, 255.
-/

namespace UndergradKB.Combinatorics

open Filter Asymptotics Topology Real

section Asymptotic

lemma centralBinom_isEquivalent :
    (fun m : ℕ => (m.centralBinom : ℝ)) ~[atTop] fun m : ℕ => 4 ^ m / √(π * m) := by
  have h1 := Stirling.factorial_isEquivalent_stirling
  have h2 := h1.comp_tendsto (tendsto_id.const_mul_atTop' (two_pos : 0 < 2))
  have h3 := h1.pow 2
  have h4 := h2.div h3
  refine (h4.congr_left ?_).congr_right ?_
  · refine Eventually.of_forall fun m => ?_
    have h := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2 * m by omega)
    rw [show 2 * m - m = m by omega] at h
    have hr : ((2 * m).choose m : ℝ) * (m.factorial : ℝ) * (m.factorial : ℝ) =
        ((2 * m).factorial : ℝ) := by exact_mod_cast h
    have hpos : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
    simp only [Pi.div_apply, Function.comp_apply, Pi.pow_apply, id]
    rw [Nat.centralBinom_eq_two_mul_choose]
    rw [← hr]
    field_simp
  · filter_upwards [eventually_ge_atTop 1] with m hm
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    simp only [Pi.div_apply, Function.comp_apply, Pi.pow_apply, id]
    push_cast
    have hs : 0 < √(π * m) := Real.sqrt_pos.2 (by positivity)
    have e1 : √(2 * (2 * (m : ℝ)) * π) = 2 * √(π * m) := by
      rw [show 2 * (2 * (m : ℝ)) * π = 2 ^ 2 * (π * m) by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    have e2 : (√(2 * (m : ℝ) * π) * ((m : ℝ) / rexp 1) ^ m) ^ 2 =
        2 * (π * m) * (((m : ℝ) / rexp 1) ^ m) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      ring
    have e3 : (2 * (m : ℝ) / rexp 1) ^ (2 * m) = 4 ^ m * (((m : ℝ) / rexp 1) ^ m) ^ 2 := by
      rw [show 2 * (m : ℝ) / rexp 1 = 2 * ((m : ℝ) / rexp 1) by ring, mul_pow, pow_mul, pow_mul']
      norm_num
    rw [e1, e2, e3]
    have hq : (((m : ℝ) / rexp 1) ^ m) ≠ 0 := by positivity
    have hs2 : (π * m) = √(π * m) ^ 2 := (Real.sq_sqrt (by positivity)).symm
    generalize √(π * m) = s at hs hs2 e1 ⊢
    rw [hs2]
    field_simp

/-- CO-261 (asymptotics). `C(2n-2, n-1) ~ 4^n / (4 sqrt(pi n))` as `n → ∞`, the estimate for the
Ramsey bound `R(n,n) ≤ C(2n-2, n-1)`, obtained from Stirling's formula. -/
@[kb "kellertrotter2017" "text, p. 255"]
theorem choose_two_mul_sub_two_isEquivalent :
    (fun n : ℕ => (((2 * n - 2).choose (n - 1) : ℕ) : ℝ)) ~[atTop]
      fun n : ℕ => 4 ^ n / (4 * √(π * n)) := by
  have h1 := centralBinom_isEquivalent.comp_tendsto (tendsto_sub_atTop_nat 1)
  have h2 : (fun n : ℕ => (4 : ℝ) ^ (n - 1) / √(π * ((n - 1 : ℕ) : ℝ))) ~[atTop]
      fun n : ℕ => 4 ^ n / (4 * √(π * n)) := by
    apply isEquivalent_of_tendsto_one
    have hlim : Tendsto (fun n : ℕ => √((n : ℝ) / (n + (-1 : ℝ)))) atTop (𝓝 1) := by
      have h := (Real.continuous_sqrt.tendsto 1).comp
        (tendsto_natCast_div_add_atTop (-1 : ℝ))
      rw [Real.sqrt_one] at h
      exact h
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hc : ((n - 1 : ℕ) : ℝ) = n - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    simp only [Pi.div_apply, hc]
    have hp : (0 : ℝ) < π := Real.pi_pos
    have h4 : (4 : ℝ) ^ n = 4 * 4 ^ (n - 1) := by
      rw [← pow_succ']; congr 1; omega
    have h1' : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    have h0' : (0 : ℝ) < (n : ℝ) := by linarith
    have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.2 h0'
    have hsn1 : 0 < √((n : ℝ) - 1) := Real.sqrt_pos.2 h1'
    have hsp : 0 < √π := Real.sqrt_pos.2 hp
    have hpow : (0 : ℝ) < 4 ^ (n - 1) := by positivity
    rw [h4, show (n : ℝ) + -1 = n - 1 by ring, Real.sqrt_div h0'.le,
      Real.sqrt_mul hp.le, Real.sqrt_mul hp.le]
    field_simp
  refine (h1.trans h2).congr_left ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp only [Function.comp_apply, Nat.centralBinom_eq_two_mul_choose]
  rw [show 2 * (n - 1) = 2 * n - 2 by omega]

end Asymptotic

section Trees

/-- CO-129. A rooted unlabelled binary ordered tree (every vertex has 0 or 2 children, children
ordered) is a Mathlib `BinaryTree Unit`: `nil` is a leaf and `node () l r` an internal vertex with
ordered children `l`, `r`.  Its number of leaves is `BinaryTree.numLeaves`, and a tree with `k`
internal vertices has `k + 1` leaves. -/
@[kb "kellertrotter2017" "Definition (unnumbered) rooted unlabeled binary ordered tree, p. 229"]
theorem binaryTree_numLeaves_eq (t : BinaryTree Unit) : t.numLeaves = t.numNodes + 1 :=
  BinaryTree.numLeaves_eq_numNodes_succ t

/-- CO-129. The number of rooted unlabelled binary ordered trees with `n ≥ 1` leaves is the
Catalan number `C_{n-1}`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) rooted unlabeled binary ordered tree, p. 229"]
theorem ncard_binaryTree_numLeaves (n : ℕ) (hn : 1 ≤ n) :
    {t : BinaryTree Unit | t.numLeaves = n}.ncard = catalan (n - 1) := by
  have h : {t : BinaryTree Unit | t.numLeaves = n} =
      ↑(BinaryTree.treesOfNumNodesEq (n - 1)) := by
    ext t
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, BinaryTree.mem_treesOfNumNodesEq,
      BinaryTree.numLeaves_eq_numNodes_succ]
    omega
  rw [h, Set.ncard_coe_finset, BinaryTree.treesOfNumNodesEq_card_eq_catalan]

end Trees

section EGF

open PowerSeries

/-- CO-204. The exponential generating function of a sequence `a`: the formal power series
with coefficients `a n / n!`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) exponential generating function, p. 194"]
noncomputable def egfSeries (a : ℕ → ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => a n / (n.factorial : ℚ)

/-- CO-204. The EGF of the constant sequence `1` is the exponential series. -/
@[kb "kellertrotter2017" "Definition (unnumbered) exponential generating function, p. 194"]
theorem egfSeries_one : egfSeries (fun _ => 1) = PowerSeries.exp ℚ := by
  ext n
  simp [egfSeries, PowerSeries.coeff_exp, one_div]

/-- CO-204. Product rule: the product of the EGFs of `a` and `b` is the EGF of the binomial
convolution `n ↦ ∑_k C(n,k) a_k b_{n-k}`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) exponential generating function, p. 194"]
theorem egfSeries_mul (a b : ℕ → ℚ) :
    egfSeries a * egfSeries b =
      egfSeries fun n => ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * a k * b (n - k) := by
  ext n
  rw [PowerSeries.coeff_mul]
  simp only [egfSeries, PowerSeries.coeff_mk]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := by have := Finset.mem_range.1 hk; omega
  have h := Nat.choose_mul_factorial_mul_factorial hk'
  have hr : (n.choose k : ℚ) * (k.factorial : ℚ) * ((n - k).factorial : ℚ) = n.factorial := by
    exact_mod_cast h
  have h1 : (k.factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((n - k).factorial : ℚ) ≠ 0 := by positivity
  have h3 : (n.choose k : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk').ne'
  rw [← hr]
  field_simp

end EGF

end UndergradKB.Combinatorics
