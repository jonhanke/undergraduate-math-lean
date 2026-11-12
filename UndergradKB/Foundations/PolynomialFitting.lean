import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.FieldSimp
import UndergradKB.Common
import UndergradKB.Foundations.Induction

/-! # Polynomial Fitting

Levin, *Discrete Mathematics*, Section 4.3: a sequence is `Δ^k`-constant when its `k`-th sequence of differences is
constant (FO-202), and Theorem 4.3.6 (Polynomial Fitting, FO-203): the closed formula of a sequence is a polynomial of
degree `k` iff the sequence is `Δ^k`-constant.

Sequences are `a : ℕ → ℝ`; differences are Mathlib's forward difference `Δ_[1] a n = a (n + 1) - a n` (`fwdDiff`).
Mathlib has the direction "polynomial ⇒ constant differences" for polynomial functions on a ring
(`Polynomial.fwdDiff_iter_degree_eq_factorial`); the converse is proved here from the Gregory-Newton formula
`a n = ∑ C(n, j) Δ^j a 0` (`shift_eq_sum_fwdDiff_iter`) and the falling-factorial polynomials `descPochhammer`.
-/

namespace UndergradKB.Foundations

open Polynomial Finset

open scoped fwdDiff

/-- FO-202. `Δ^k`-constant means: the `(k+1)`-st differences vanish. -/
@[kb "levin2025" "Def §4.3.3, p. 363"]
theorem isDeltaConstant_iff_iterate_succ_eq_zero (k : ℕ) (a : ℕ → ℝ) :
    IsDeltaConstant k a ↔ Δ_[1]^[k + 1] a = 0 := by
  rw [Function.iterate_succ_apply']
  constructor
  · rintro ⟨c, hc⟩
    funext n
    simp only [fwdDiff, Pi.zero_apply, hc, sub_self]
  · intro h
    refine ⟨Δ_[1]^[k] a 0, fun n => ?_⟩
    induction n with
    | zero => rfl
    | succ n ih =>
      have := congrFun h n
      simp only [fwdDiff, Pi.zero_apply, sub_eq_zero] at this
      rw [this, ih]

/-- Forward differences commute with restricting a function on `ℝ` to the natural numbers. -/
theorem fwdDiff_iter_comp_natCast (f : ℝ → ℝ) (k : ℕ) :
    Δ_[1]^[k] (fun n : ℕ => f n) = fun n : ℕ => (Δ_[1]^[k] f) n := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← ih]
    congr 1
    funext n
    simp [fwdDiff]

/-- The same for the values of a polynomial at the natural numbers. -/
theorem fwdDiff_iter_eval_natCast (P : ℝ[X]) (k : ℕ) :
    Δ_[1]^[k] (fun n : ℕ => P.eval (n : ℝ)) = fun n : ℕ => (Δ_[1]^[k] P.eval) n :=
  fwdDiff_iter_comp_natCast (fun x => P.eval x) k

/-- The sequence of values of a polynomial of degree at most `k` has vanishing `(k+1)`-st differences. -/
theorem fwdDiff_iter_polynomial_eq_zero (P : ℝ[X]) (k : ℕ) (hP : P.natDegree ≤ k) :
    Δ_[1]^[k + 1] (fun n : ℕ => P.eval (n : ℝ)) = 0 := by
  rw [fwdDiff_iter_eval_natCast, Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (by omega)]
  rfl

/-- Gregory-Newton: if the `(k+1)`-st differences vanish, then `a n = ∑_{j ≤ k} C(n, j) Δ^j a 0`. -/
theorem eq_sum_choose_of_iterate_eq_zero (a : ℕ → ℝ) (k : ℕ) (h : Δ_[1]^[k + 1] a = 0) (n : ℕ) :
    a n = ∑ j ∈ range (k + 1), (n.choose j : ℝ) * Δ_[1]^[j] a 0 := by
  have hz : ∀ j, k + 1 ≤ j → Δ_[1]^[j] a = 0 := by
    intro j hj
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [add_comm, Function.iterate_add_apply, h]
    clear hj
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [Function.iterate_succ_apply', ih]
      funext x; simp [fwdDiff]
  have hN := shift_eq_sum_fwdDiff_iter (1 : ℕ) a n 0
  simp only [zero_add, smul_eq_mul, mul_one, nsmul_eq_mul] at hN
  rw [hN]
  -- both sums equal the sum over `range (max n k + 1)`
  have key : ∀ m, n ≤ m → k ≤ m →
      ∑ j ∈ range (m + 1), (n.choose j : ℝ) * Δ_[1]^[j] a 0 =
        ∑ j ∈ range (n + 1), (n.choose j : ℝ) * Δ_[1]^[j] a 0 ∧
      ∑ j ∈ range (m + 1), (n.choose j : ℝ) * Δ_[1]^[j] a 0 =
        ∑ j ∈ range (k + 1), (n.choose j : ℝ) * Δ_[1]^[j] a 0 := by
    intro m hn hk
    constructor
    · refine (sum_subset (range_subset_range.mpr (by omega)) ?_).symm
      intro j _ hj
      rw [mem_range, not_lt] at hj
      simp [Nat.choose_eq_zero_of_lt (by omega : n < j)]
    · refine (sum_subset (range_subset_range.mpr (by omega)) ?_).symm
      intro j _ hj
      rw [mem_range, not_lt] at hj
      simp [hz j hj]
  obtain ⟨h1, h2⟩ := key (max n k) (le_max_left _ _) (le_max_right _ _)
  rw [← h1, h2]

/-- The polynomial `∑_{j ≤ k} c_j X(X-1)⋯(X-j+1)/j!`, whose value at `n` is `∑ c_j C(n, j)`. -/
noncomputable def newtonPoly (c : ℕ → ℝ) (k : ℕ) : ℝ[X] :=
  ∑ j ∈ range (k + 1), C (c j / (j.factorial : ℝ)) * descPochhammer ℝ j

theorem newtonPoly_eval (c : ℕ → ℝ) (k n : ℕ) :
    (newtonPoly c k).eval (n : ℝ) = ∑ j ∈ range (k + 1), (n.choose j : ℝ) * c j := by
  rw [newtonPoly, eval_finsetSum]
  refine sum_congr rfl fun j _ => ?_
  rw [eval_mul, eval_C, descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
  have : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
  push_cast
  field_simp

theorem newtonPoly_natDegree_le (c : ℕ → ℝ) (k : ℕ) : (newtonPoly c k).natDegree ≤ k := by
  rw [newtonPoly]
  refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [descPochhammer_natDegree]
  exact Nat.lt_succ_iff.mp (mem_range.mp hj)

/-- FO-203 (Levin Theorem 4.3.6, Polynomial Fitting), degree at most `k`: a sequence has a closed formula given by a
polynomial of degree at most `k` iff it is `Δ^k`-constant. -/
@[kb "levin2025" "Theorem 4.3.6, p. 364"]
theorem polynomial_fitting_le (a : ℕ → ℝ) (k : ℕ) :
    (∃ P : ℝ[X], P.natDegree ≤ k ∧ ∀ n : ℕ, a n = P.eval (n : ℝ)) ↔ IsDeltaConstant k a := by
  rw [isDeltaConstant_iff_iterate_succ_eq_zero]
  constructor
  · rintro ⟨P, hP, ha⟩
    have : a = fun n : ℕ => P.eval (n : ℝ) := funext ha
    rw [this]
    exact fwdDiff_iter_polynomial_eq_zero P k hP
  · intro h
    refine ⟨newtonPoly (fun j => Δ_[1]^[j] a 0) k, newtonPoly_natDegree_le _ _, fun n => ?_⟩
    rw [newtonPoly_eval]
    exact eq_sum_choose_of_iterate_eq_zero a k h n

/-- The `k`-th differences of the values of a polynomial of degree exactly `k` are the constant
`(leading coefficient) · k!`. -/
theorem fwdDiff_iter_polynomial_natDegree (P : ℝ[X]) (n : ℕ) :
    Δ_[1]^[P.natDegree] (fun m : ℕ => P.eval (m : ℝ)) n = P.leadingCoeff * P.natDegree.factorial := by
  rw [fwdDiff_iter_eval_natCast, Polynomial.fwdDiff_iter_degree_eq_factorial]
  simp

/-- FO-203 (Levin Theorem 4.3.6, Polynomial Fitting), exact degree: a sequence has a closed formula given by a
polynomial of degree exactly `k` iff its `k`-th differences are a nonzero constant. -/
@[kb "levin2025" "Theorem 4.3.6, p. 364"]
theorem polynomial_fitting (a : ℕ → ℝ) (k : ℕ) :
    (∃ P : ℝ[X], P ≠ 0 ∧ P.natDegree = k ∧ ∀ n : ℕ, a n = P.eval (n : ℝ)) ↔
      ∃ c : ℝ, c ≠ 0 ∧ ∀ n, Δ_[1]^[k] a n = c := by
  constructor
  · rintro ⟨P, hP0, rfl, ha⟩
    have : a = fun n : ℕ => P.eval (n : ℝ) := funext ha
    subst this
    refine ⟨P.leadingCoeff * P.natDegree.factorial, ?_, fwdDiff_iter_polynomial_natDegree P⟩
    exact mul_ne_zero (leadingCoeff_ne_zero.mpr hP0) (by exact_mod_cast (Nat.factorial_pos _).ne')
  · rintro ⟨c, hc0, hc⟩
    obtain ⟨P, hPk, ha⟩ := (polynomial_fitting_le a k).mpr ⟨c, hc⟩
    have haP : a = fun n : ℕ => P.eval (n : ℝ) := funext ha
    rcases lt_or_eq_of_le hPk with hlt | heq
    · exfalso
      obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_lt hlt
      have h0 : Δ_[1]^[k] a = 0 := by
        rw [haP, hj, fwdDiff_iter_eval_natCast,
          Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (by omega)]
        rfl
      exact hc0 ((hc 0).symm.trans (congrFun h0 0))
    · refine ⟨P, ?_, heq, ha⟩
      rintro rfl
      have h0 : Δ_[1]^[k] a = 0 := by
        rw [haP]
        simp only [eval_zero]
        clear hc ha haP heq hPk
        induction k with
        | zero => rfl
        | succ k ih =>
          rw [Function.iterate_succ_apply', ih]
          funext x; simp [fwdDiff]
      exact hc0 ((hc 0).symm.trans (congrFun h0 0))

end UndergradKB.Foundations
