import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.AeqB.Similar
import UndergradKB.Combinatorics.AeqB.Gosper
import UndergradKB.Combinatorics.AeqB.GosperForm

/-!
# Gosper's algorithm as a whole (Petkovsek–Wilf–Zeilberger, "A = B", Chapter 5)

* the outline of the algorithm (Section 5.2) with its correctness and completeness (CO-400);
* the degree candidates of Step 3 and the finite linear system for the undetermined coefficients
  (CO-410);
* the decision theorems of Section 5.6 (CO-417, CO-418, CO-419);
* the WZ-certificate recipe of Section 7.1 (CO-445).
-/

set_option linter.unusedSectionVars false

namespace UndergradKB.Combinatorics.AeqB
open Polynomial Filter

variable {K : Type*} [Field K] [CharZero K]

/-! ### CO-400: the outline of Gosper's algorithm -/

/-- The key equation (5.2.6): `a(n) x(n+1) - b(n-1) x(n) = c(n)`. -/
def GosperEq (a b c x : K[X]) : Prop :=
  a * x.comp (X + 1) - b.comp (X - 1) * x = c

/-- Step 4 of Gosper's algorithm: the candidate antidifference
`z_n = b(n-1) x(n) t_n / c(n)` (equation (5.2.5) times `t_n`). -/
noncomputable def gosperTerm (t : ℕ → K) (b c x : K[X]) : ℕ → K :=
  fun n => (b.comp (X - 1) * x).eval (n : K) * t n / c.eval (n : K)

/-- Step 3 of Gosper's algorithm (abstractly): a nonzero polynomial solution of (5.2.6), if there
is one (`none` if there is none). -/
noncomputable def gosperSolution (a b c : K[X]) : Option K[X] := by
  classical
  exact if h : ∃ x, x ≠ 0 ∧ GosperEq a b c x then some h.choose else none

/-- CO-400. The output of Gosper's algorithm (page 87): given the ratio data `a, b, c` of the
input term `t` (Step 2), return `b(n-1) x(n) t_n / c(n)` for the polynomial solution `x` found in
Step 3, or else the partial sum `∑_{k<n} t_k`. -/
@[kb "petkovsekwilfzeilberger1996" "Gosper's Algorithm (outline), p. 87"]
noncomputable def gosperOutput (t : ℕ → K) (a b c : K[X]) : ℕ → K :=
  match gosperSolution a b c with
  | some x => gosperTerm t b c x
  | none => fun n => ∑ k ∈ Finset.range n, t k

/-- CO-400 (Step 4, correctness). Suppose `q(n) t(n+1) = p(n) t(n)` is written as
`b(n) c(n) t(n+1) = a(n) c(n+1) t(n)` and `x ≠ 0` is a polynomial solution of (5.2.6). Then
`z_n = b(n-1) x(n) t_n / c(n)` is a hypergeometric term with `z(n+1) - z(n) = t(n)`. -/
@[kb "petkovsekwilfzeilberger1996" "Gosper's Algorithm (outline), p. 87"]
theorem gosperTerm_correct {t : ℕ → K} {a b c x : K[X]} (ht : IsHypergeometric t) (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hrel : ∀ᶠ n : ℕ in atTop,
      (b * c).eval (n : K) * t (n + 1) = (a * c.comp (X + 1)).eval (n : K) * t n)
    (hx : x ≠ 0) (h : GosperEq a b c x) :
    IsHypergeometric (gosperTerm t b c x) ∧
      ∀ᶠ n : ℕ in atTop, gosperTerm t b c x (n + 1) - gosperTerm t b c x n = t n := by
  have ht0 := ht.eventually_ne_zero
  have hv0 := eventually_eval_ne_zero hc
  have hz : ∀ᶠ n : ℕ in atTop, c.eval (n : K) * gosperTerm t b c x n
      = (b.comp (X - 1) * x).eval (n : K) * t n := by
    filter_upwards [hv0] with n hn
    simp only [gosperTerm]
    field_simp
  have hu : b.comp (X - 1) * x ≠ 0 := mul_ne_zero (comp_X_sub_one_ne_zero hb) hx
  refine ⟨IsSimilar.isHypergeometric ⟨_, c, hu, hc, hz⟩ ht, ?_⟩
  exact (gosper_reduction_iff ht0 (mul_ne_zero hb hc) hc hrel hz).2
    ((gosper_form_equiv (mul_ne_zero hb hc) hc (by ring)).2 h)

omit [CharZero K] in
theorem exists_ne_zero_gosperEq_iff {a b c : K[X]} (hc : c ≠ 0) :
    (∃ x, x ≠ 0 ∧ GosperEq a b c x) ↔ ∃ x, GosperEq a b c x := by
  refine ⟨fun ⟨x, _, h⟩ => ⟨x, h⟩, fun ⟨x, h⟩ => ⟨x, ?_, h⟩⟩
  rintro rfl
  apply hc
  rw [← h]
  simp

omit [CharZero K] in
theorem gosperSolution_eq_none_iff {a b c : K[X]} (hc : c ≠ 0) :
    gosperSolution a b c = none ↔ ¬ ∃ x, GosperEq a b c x := by
  rw [← exists_ne_zero_gosperEq_iff hc]
  unfold gosperSolution
  classical
  by_cases h : ∃ x, x ≠ 0 ∧ GosperEq a b c x <;> simp [h]

omit [CharZero K] in
theorem gosperSolution_spec {a b c x : K[X]} (hc : c ≠ 0) (hx : gosperSolution a b c = some x) :
    x ≠ 0 ∧ GosperEq a b c x := by
  have hne : ¬ gosperSolution a b c = none := by rw [hx]; simp
  rw [gosperSolution_eq_none_iff hc, not_not] at hne
  obtain ⟨y, hy0, hy⟩ := (exists_ne_zero_gosperEq_iff hc).2 hne
  unfold gosperSolution at hx
  classical
  split_ifs at hx with hh
  rw [Option.some.injEq] at hx
  rw [← hx]
  exact Classical.choose_spec hh

/-- CO-400 (correctness and completeness of the outline, page 87).  Let `t` be hypergeometric
with `b(n) c(n) t(n+1) = a(n) c(n+1) t(n)` and `gcd(a(n), b(n+h)) = 1` for all `h ∈ ℕ` (the data
of Step 2).

* (completeness) if `t` is Gosper-summable then Step 3 finds a nonzero polynomial solution `x`
  and the output is a hypergeometric term `z` with `z(n+1) - z(n) = t(n)`;
* if `t` is not Gosper-summable then Step 3 finds nothing, and the output is the partial sum
  `∑_{k<n} t_k`. -/
@[kb "petkovsekwilfzeilberger1996" "Gosper's Algorithm (outline), p. 87"]
theorem gosperOutput_spec {t : ℕ → K} {a b c : K[X]} (ht : IsHypergeometric t) (hb : b ≠ 0)
    (hc : c ≠ 0) (hab : ∀ h : ℕ, IsCoprime a (b.comp (X + C (h : K))))
    (hrel : ∀ᶠ n : ℕ in atTop,
      (b * c).eval (n : K) * t (n + 1) = (a * c.comp (X + 1)).eval (n : K) * t n) :
    (IsGosperSummable t →
      (∃ x, x ≠ 0 ∧ GosperEq a b c x ∧ gosperSolution a b c = some x) ∧
      IsHypergeometric (gosperOutput t a b c) ∧
      ∀ᶠ n : ℕ in atTop, gosperOutput t a b c (n + 1) - gosperOutput t a b c n = t n) ∧
    (¬ IsGosperSummable t → gosperSolution a b c = none ∧
      gosperOutput t a b c = fun n => ∑ k ∈ Finset.range n, t k) := by
  have hiff := isGosperSummable_iff_polynomial_solution ht hb hc hab hrel
  constructor
  · intro hs
    have hex : ∃ x, GosperEq a b c x := hiff.1 hs
    have hnn : gosperSolution a b c ≠ none := by
      rw [Ne, gosperSolution_eq_none_iff hc, not_not]; exact hex
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 hnn
    obtain ⟨hx0, hxe⟩ := gosperSolution_spec hc hx
    have hout : gosperOutput t a b c = gosperTerm t b c x := by
      unfold gosperOutput; rw [hx]
    refine ⟨⟨x, hx0, hxe, hx⟩, ?_⟩
    rw [hout]
    exact gosperTerm_correct ht hb hc hrel hx0 hxe
  · intro hn
    have hnone : gosperSolution a b c = none := by
      rw [gosperSolution_eq_none_iff hc]
      exact fun hex => hn (hiff.2 hex)
    refine ⟨hnone, ?_⟩
    unfold gosperOutput; rw [hnone]

/-- CO-400. The whole outline, from the hypergeometric term `t` itself: Steps 1 and 2 produce
(by Theorem 5.3.1) `a, b, c` with `b, c` monic, conditions (i)-(iii), and the ratio relation
`b c t(n+1) = a c(n+1) t(n)`; for these, `t` is Gosper-summable iff (5.2.6) has a polynomial
solution, and in that case the output of Step 4 is an antidifference. -/
@[kb "petkovsekwilfzeilberger1996" "Gosper's Algorithm (outline), p. 87"]
theorem gosper_algorithm {t : ℕ → K} (ht : IsHypergeometric t) :
    ∃ a b c : K[X], a ≠ 0 ∧ b.Monic ∧ c.Monic ∧
      (∀ h : ℕ, IsCoprime a (b.comp (X + C (h : K)))) ∧ IsCoprime a c ∧
      IsCoprime b (c.comp (X + 1)) ∧
      (∀ᶠ n : ℕ in atTop,
        (b * c).eval (n : K) * t (n + 1) = (a * c.comp (X + 1)).eval (n : K) * t n) ∧
      (IsGosperSummable t ↔ ∃ x, GosperEq a b c x) ∧
      (IsGosperSummable t →
        IsHypergeometric (gosperOutput t a b c) ∧
        ∀ᶠ n : ℕ in atTop, gosperOutput t a b c (n + 1) - gosperOutput t a b c n = t n) ∧
      (¬ IsGosperSummable t → gosperOutput t a b c = fun n => ∑ k ∈ Finset.range n, t k) := by
  obtain ⟨-, p, q, hp, hq, hpq⟩ := isHypergeometric_iff.1 ht
  have ht0 := ht.eventually_ne_zero
  obtain ⟨a, b, c, ha, hbm, hcm, hform, hab, hac, hbc⟩ := exists_gosper_form p q hp hq
  have hrel : ∀ᶠ n : ℕ in atTop,
      (b * c).eval (n : K) * t (n + 1) = (a * c.comp (X + 1)).eval (n : K) * t n := by
    filter_upwards [hpq, eventually_eval_ne_zero hq] with n e hqn
    apply mul_left_cancel₀ hqn
    have := congrArg (eval (n : K)) hform
    simp only [eval_mul] at this ⊢
    linear_combination (b.eval (n : K) * c.eval (n : K)) * e + t n * this
  have hb := hbm.ne_zero
  have hc := hcm.ne_zero
  have hsp := gosperOutput_spec ht hb hc hab hrel
  refine ⟨a, b, c, ha, hbm, hcm, hab, hac, hbc, hrel,
    isGosperSummable_iff_polynomial_solution ht hb hc hab hrel, ?_, ?_⟩
  · intro hs
    obtain ⟨-, h2, h3⟩ := hsp.1 hs
    exact ⟨h2, h3⟩
  · intro hn
    exact (hsp.2 hn).2

/-! ### CO-410: Step 3, the degree candidates and the finite linear system -/

open Classical in
/-- CO-410 (Step 3.1). The candidate set `D` for the degree of a nonzero polynomial solution of
(5.2.6), as a set of natural numbers.  If `deg a ≠ deg b` or `lc a ≠ lc b` it is the solutions of
`d = deg c - max (deg a, deg b)`; otherwise it contains `d = deg c - deg a + 1` and the `d` with
`d = (B - A) / lc a`, where `A` is the coefficient of `n^{deg a - 1}` in `a(n)` and `B` that in
`b(n-1)`.  (The book's intersection with `ℕ` is built in; `deg c` of `c = 0` is read as `0`.) -/
@[kb "petkovsekwilfzeilberger1996" "Gosper's Algorithm (Step 3.1), p. 96"]
noncomputable def gosperDegreeSet (a b c : K[X]) : Set ℕ :=
  if a.natDegree ≠ b.natDegree ∨ a.leadingCoeff ≠ b.leadingCoeff then
    {d | d + max a.natDegree b.natDegree = c.natDegree}
  else
    {d | d + a.natDegree = c.natDegree + 1} ∪
      {d | (d : K) = ((b.comp (X - 1)).coeff (a.natDegree - 1) - a.coeff (a.natDegree - 1))
        / a.leadingCoeff}

/-- CO-410. The degree bound `d := max D` (and `0` if `D` is empty). -/
noncomputable def gosperDegreeBound (a b c : K[X]) : ℕ := sSup (gosperDegreeSet a b c)

/-- `D` has at most two elements, in particular it is finite. -/
theorem gosperDegreeSet_finite (a b c : K[X]) : (gosperDegreeSet a b c).Finite := by
  unfold gosperDegreeSet
  split_ifs
  · refine (Set.finite_Iic c.natDegree).subset fun d hd => ?_
    simp only [Set.mem_ofPred_eq] at hd
    simp only [Set.mem_Iic]
    omega
  · refine Set.Finite.union ((Set.finite_Iic (c.natDegree + 1)).subset fun d hd => ?_) ?_
    · simp only [Set.mem_ofPred_eq] at hd
      simp only [Set.mem_Iic]
      omega
    · exact Set.Subsingleton.finite fun d1 h1 d2 h2 => Nat.cast_injective (R := K) (h1.trans h2.symm)

theorem natDegree_solution_case2_zero {a b c x : K[X]} (ha : a ≠ 0) (hx : x ≠ 0)
    (hdeg : a.natDegree = 0) (hdegb : b.natDegree = 0) (hlc : a.leadingCoeff = b.leadingCoeff)
    (h : GosperEq a b c x) : x.natDegree = 0 ∨ c.natDegree + 1 = x.natDegree := by
  have hl : a.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 ha
  have haC : a = C a.leadingCoeff := by
    conv_lhs => rw [eq_C_of_natDegree_eq_zero hdeg]
    rw [leadingCoeff, hdeg]
  have hbC : b.comp (X - 1) = C a.leadingCoeff := by
    rw [hlc]
    conv_lhs => rw [eq_C_of_natDegree_eq_zero hdegb]
    rw [leadingCoeff, hdegb, C_comp]
  unfold GosperEq at h
  rw [hbC] at h
  have hc : c = C a.leadingCoeff * (x.comp (X + 1) - x) := by
    have e : a * x.comp (X + 1) = C a.leadingCoeff * x.comp (X + 1) := by rw [← haC]
    rw [← h, e]
    ring
  rcases Nat.eq_zero_or_pos x.natDegree with h0 | hpos
  · exact Or.inl h0
  · right
    obtain ⟨m, hm⟩ : ∃ m, x.natDegree = m + 1 := ⟨x.natDegree - 1, by omega⟩
    have hx1d : (x.comp (X + 1)).natDegree = x.natDegree := by
      rw [comp_X_add_one_eq, natDegree_comp_shift]
    have hx1c : (x.comp (X + 1)).coeff x.natDegree = x.leadingCoeff := by
      rw [comp_X_add_one_eq, coeff_comp_shift_natDegree]
    have hΔ : (x.comp (X + 1) - x).natDegree ≤ x.natDegree - 1 :=
      natDegree_sub_le_pred hx1d.le le_rfl (by rw [hx1c]; rfl)
    have hΔc : (x.comp (X + 1) - x).coeff m = ((x.natDegree : K)) * x.leadingCoeff := by
      have hl' : x.leadingCoeff = x.coeff (m + 1) := by rw [leadingCoeff, hm]
      rw [coeff_sub, coeff_comp_X_add_one_pred x m hm, add_sub_cancel_left, hl', hm]
      push_cast
      ring
    have hne : (x.comp (X + 1) - x).coeff m ≠ 0 := by
      rw [hΔc]
      exact mul_ne_zero (Nat.cast_ne_zero.2 (by omega)) (leadingCoeff_ne_zero.2 hx)
    have h1 : m ≤ (x.comp (X + 1) - x).natDegree := le_natDegree_of_ne_zero hne
    have h2 : c.natDegree = (x.comp (X + 1) - x).natDegree := by
      rw [hc, natDegree_C_mul hl]
    omega

/-- CO-410 (justification of Step 3.1, combining the three cases of Section 5.4).
Every nonzero polynomial solution of (5.2.6) has its degree in `D`. -/
@[kb "petkovsekwilfzeilberger1996" "Gosper's Algorithm (Step 3.1), p. 96"]
theorem natDegree_mem_gosperDegreeSet {a b c x : K[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hx : x ≠ 0)
    (h : GosperEq a b c x) : x.natDegree ∈ gosperDegreeSet a b c := by
  unfold gosperDegreeSet
  split_ifs with hne
  · obtain ⟨-, hc⟩ := natDegree_solution_case1 ha hb hx hne h
    simp only [Set.mem_ofPred_eq]
    omega
  · push Not at hne
    obtain ⟨hdeg, hlc⟩ := hne
    by_cases hk : 1 ≤ a.natDegree
    · rcases natDegree_solution_case2 ha hx hdeg hlc hk h with h1 | h2
      · left
        simp only [Set.mem_ofPred_eq]
        omega
      · right
        exact h2
    · have hk0 : a.natDegree = 0 := by omega
      have hb0 : b.natDegree = 0 := by omega
      rcases natDegree_solution_case2_zero ha hx hk0 hb0 hlc h with h1 | h2
      · right
        simp only [Set.mem_ofPred_eq]
        have ha0 : a.coeff 0 = a.leadingCoeff := by rw [leadingCoeff, hk0]
        have hbC : b.comp (X - 1) = C a.leadingCoeff := by
          rw [hlc]
          conv_lhs => rw [eq_C_of_natDegree_eq_zero hb0]
          rw [leadingCoeff, hb0, C_comp]
        rw [h1, hk0, hbC, Nat.zero_sub, coeff_C_zero, ha0, sub_self, zero_div]
        simp
      · left
        simp only [Set.mem_ofPred_eq]
        omega

/-- CO-410. Every nonzero polynomial solution of (5.2.6) has degree at most `d = max D`. -/
@[kb "petkovsekwilfzeilberger1996" "Gosper's Algorithm (Step 3.1), p. 96"]
theorem natDegree_le_gosperDegreeBound {a b c x : K[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hx : x ≠ 0)
    (h : GosperEq a b c x) : x.natDegree ≤ gosperDegreeBound a b c :=
  le_csSup (gosperDegreeSet_finite a b c).bddAbove (natDegree_mem_gosperDegreeSet ha hb hx h)

/-- CO-410. If `D` is empty there is no nonzero polynomial solution. -/
theorem no_solution_of_gosperDegreeSet_empty {a b c : K[X]} (ha : a ≠ 0) (hb : b ≠ 0)
    (hD : gosperDegreeSet a b c = ∅) : ¬ ∃ x, x ≠ 0 ∧ GosperEq a b c x := by
  rintro ⟨x, hx, h⟩
  have := natDegree_mem_gosperDegreeSet ha hb hx h
  rw [hD] at this
  exact this

/-- The linear operator `x ↦ a(n) x(n+1) - b(n-1) x(n)` on polynomials. -/
noncomputable def gosperOp (a b : K[X]) : K[X] →ₗ[K] K[X] :=
  LinearMap.mulLeft K a ∘ₗ (aeval (X + 1 : K[X])).toLinearMap -
    LinearMap.mulLeft K (b.comp (X - 1))

@[simp]
theorem gosperOp_apply (a b x : K[X]) :
    gosperOp a b x = a * x.comp (X + 1) - b.comp (X - 1) * x := by
  simp [gosperOp, comp_eq_aeval]

theorem natDegree_le_of_mem_degreeLT {x : K[X]} {d : ℕ} (hx : x ∈ degreeLT K (d + 1)) :
    x.natDegree ≤ d := by
  by_cases h0 : x = 0
  · simp [h0]
  · rw [mem_degreeLT] at hx
    have := (natDegree_lt_iff_degree_lt h0).2 hx
    omega

/-- The operator maps polynomials of degree `≤ d` to polynomials of degree `≤ d + max (deg a, deg b)`. -/
theorem gosperOp_mem_degreeLT (a b : K[X]) {d : ℕ} {x : K[X]} (hx : x ∈ degreeLT K (d + 1)) :
    gosperOp a b x ∈ degreeLT K (d + max a.natDegree b.natDegree + 1) := by
  have hxd := natDegree_le_of_mem_degreeLT hx
  rw [mem_degreeLT, gosperOp_apply]
  refine lt_of_le_of_lt
    (degree_le_of_natDegree_le (n := d + max a.natDegree b.natDegree) ?_) (by exact_mod_cast Nat.lt_succ_self _)
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · refine natDegree_mul_le.trans ?_
    rw [comp_X_add_one_eq, natDegree_comp_shift]
    have := le_max_left a.natDegree b.natDegree
    omega
  · refine natDegree_mul_le.trans ?_
    rw [comp_X_sub_one_eq, natDegree_comp_shift]
    have := le_max_right a.natDegree b.natDegree
    omega

/-- CO-410 (Step 3.2). The restriction of the operator to polynomials of degree `≤ d`: a linear
map between finite-dimensional spaces, i.e. the linear system of the undetermined coefficients. -/
noncomputable def gosperOpLT (a b : K[X]) (d : ℕ) :
    degreeLT K (d + 1) →ₗ[K] degreeLT K (d + max a.natDegree b.natDegree + 1) :=
  (gosperOp a b).restrict fun _ hx => gosperOp_mem_degreeLT a b hx

theorem gosperOpLT_coe (a b : K[X]) (d : ℕ) (y : degreeLT K (d + 1)) :
    ((gosperOpLT a b d y : degreeLT K (d + max a.natDegree b.natDegree + 1)) : K[X])
      = a * (y : K[X]).comp (X + 1) - b.comp (X - 1) * y := by
  simp [gosperOpLT, LinearMap.coe_restrict_apply]

/-- The space of polynomials of degree `< n` is finite-dimensional, so the search for
polynomial solutions of degree `≤ d` is a finite linear-algebra problem. -/
instance degreeLT_finite (n : ℕ) : Module.Finite K (degreeLT K n) :=
  Module.Finite.equiv (degreeLTEquiv K n).symm

/-- CO-410 (Step 3, whole). A nonzero polynomial solution of (5.2.6) exists iff the linear system
`gosperOpLT a b d y = c` (with `d = max D`) has a nonzero solution `y` among the polynomials of
degree `≤ d`.  Thus Step 3.2 is a finite linear system (undetermined coefficients) and the
search terminates. -/
@[kb "petkovsekwilfzeilberger1996" "Gosper's Algorithm (Step 3.2), p. 96"]
theorem exists_solution_iff_linear_system {a b c : K[X]} (ha : a ≠ 0) (hb : b ≠ 0) :
    (∃ x, x ≠ 0 ∧ GosperEq a b c x) ↔
      ∃ y : degreeLT K (gosperDegreeBound a b c + 1), (y : K[X]) ≠ 0 ∧
        ((gosperOpLT a b (gosperDegreeBound a b c) y :
          degreeLT K (gosperDegreeBound a b c + max a.natDegree b.natDegree + 1)) : K[X]) = c := by
  constructor
  · rintro ⟨x, hx, h⟩
    refine ⟨⟨x, mem_degreeLT.2 ?_⟩, hx, ?_⟩
    · exact (degree_le_of_natDegree_le (natDegree_le_gosperDegreeBound ha hb hx h)).trans_lt
        (by exact_mod_cast Nat.lt_succ_self _)
    · rw [gosperOpLT_coe]; exact h
  · rintro ⟨y, hy, h⟩
    rw [gosperOpLT_coe] at h
    exact ⟨y, hy, h⟩

/-! ### CO-418: Theorem 5.6.3 -/

omit [CharZero K] in
theorem isSimilar_neg (v : ℕ → K) : IsSimilar (fun n => -v n) v :=
  ⟨-1, 1, by simp, one_ne_zero, Eventually.of_forall fun n => by simp⟩

theorem isSimilar_add_neg {v u : ℕ → K} (hsim : IsSimilar v u)
    (hne : ¬ ∀ᶠ n : ℕ in atTop, v n + -u n = 0) : IsSimilar (fun n => v n + -u n) u := by
  obtain ⟨p, q, hp, hq, h⟩ := hsim
  have hpq : p - q ≠ 0 := by
    intro h0
    apply hne
    filter_upwards [h, eventually_eval_ne_zero hq] with n e hqn
    have h1 : p.eval (n : K) - q.eval (n : K) = 0 := by simpa using congrArg (eval (n : K)) h0
    have : q.eval (n : K) * (v n + -u n) = 0 := by linear_combination e + u n * h1
    exact (mul_eq_zero.1 this).resolve_left hqn
  exact ⟨p - q, q, hpq, hq, h.mono fun n e => by simp only [eval_sub]; linear_combination e⟩

/-- Consequence of Theorem 5.6.1: if pairwise dissimilar hypergeometric terms add up to a
hypergeometric term `v`, one of them is similar to `v`. -/
theorem exists_similar_of_sum_eq {ι : Type*} [DecidableEq ι] (J : Finset ι) (u : ι → ℕ → K)
    (v : ℕ → K) (hu : ∀ i ∈ J, IsHypergeometric (u i)) (hv : IsHypergeometric v)
    (hdis : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → ¬ IsSimilar (u i) (u j))
    (hsum : ∀ᶠ n : ℕ in atTop, ∑ i ∈ J, u i n = v n) :
    ∃ i ∈ J, IsSimilar (u i) v := by
  classical
  let w : Option ι → ℕ → K := fun o => o.elim (fun n => -v n) u
  have hw : ∀ o ∈ Finset.insertNone J, IsHypergeometric (w o) := by
    intro o ho
    rcases o with _ | i
    · exact (isSimilar_neg v).isHypergeometric hv
    · exact hu i (Finset.some_mem_insertNone.1 ho)
  obtain ⟨o1, h1, o2, h2, hne, hsim⟩ := exists_similar_of_sum_eq_zero (Finset.insertNone J)
    ⟨none, by simp⟩ w hw (by
      filter_upwards [hsum] with n h
      rw [Finset.sum_insertNone]
      simp only [w, Option.elim_none, Option.elim_some]
      rw [← h]; ring)
  rcases o1 with _ | i <;> rcases o2 with _ | j
  · exact absurd rfl hne
  · exact ⟨j, Finset.some_mem_insertNone.1 h2, hsim.symm.trans (isSimilar_neg v)⟩
  · exact ⟨i, Finset.some_mem_insertNone.1 h1, hsim.trans (isSimilar_neg v)⟩
  · exact absurd hsim (hdis i (Finset.some_mem_insertNone.1 h1) j (Finset.some_mem_insertNone.1 h2)
      fun h => hne (by rw [h]))

/-- If pairwise dissimilar hypergeometric terms add up to a hypergeometric term `v`, then `v` is
(for large `n`) one of them. -/
theorem exists_eq_of_sum_eq {ι : Type*} [DecidableEq ι] (J : Finset ι) (u : ι → ℕ → K)
    (v : ℕ → K) (hu : ∀ i ∈ J, IsHypergeometric (u i)) (hv : IsHypergeometric v)
    (hdis : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → ¬ IsSimilar (u i) (u j))
    (hsum : ∀ᶠ n : ℕ in atTop, ∑ i ∈ J, u i n = v n) :
    ∃ i ∈ J, ∀ᶠ n : ℕ in atTop, v n = u i n := by
  obtain ⟨i0, hi0, hsim⟩ := exists_similar_of_sum_eq J u v hu hv hdis hsum
  by_cases hR : ∀ᶠ n : ℕ in atTop, v n + -u i0 n = 0
  · exact ⟨i0, hi0, hR.mono fun n h => by linear_combination h⟩
  · exfalso
    have hvu : IsSimilar v (fun n => -u i0 n) := hsim.symm.trans (isSimilar_neg (u i0)).symm
    have hneg : IsHypergeometric (fun n => -u i0 n) :=
      (isSimilar_neg (u i0)).isHypergeometric (hu i0 hi0)
    have hRh : IsHypergeometric (fun n => v n + -u i0 n) :=
      (isHypergeometric_add_iff hv hneg hR).2 hvu
    have hRs : IsSimilar (fun n => v n + -u i0 n) (u i0) :=
      isSimilar_add_neg hsim.symm hR
    have hsum' : ∀ᶠ n : ℕ in atTop, ∑ i ∈ J.erase i0, u i n = v n + -u i0 n := by
      filter_upwards [hsum] with n h
      rw [← h, ← Finset.add_sum_erase J (fun i => u i n) hi0]
      ring
    obtain ⟨i, hi, hsi⟩ := exists_similar_of_sum_eq (J.erase i0) u _
      (fun i hi => hu i (Finset.mem_of_mem_erase hi)) hRh
      (fun i hi j hj => hdis i (Finset.mem_of_mem_erase hi) j (Finset.mem_of_mem_erase hj))
      hsum'
    exact hdis i (Finset.mem_of_mem_erase hi) i0 hi0 (Finset.ne_of_mem_erase hi)
      (hsi.trans hRs)

/-- CO-418. Theorem 5.6.3: if Gosper's algorithm does not succeed on the hypergeometric term `t`
(i.e. `t` is not Gosper-summable), then the partial sums `∑_{k<n} t_k` are not (for large `n`) a
linear combination `∑_{i<m} α_i s_i(n)` of a fixed number `m` of hypergeometric terms `s_i`. -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 5.6.3, p. 104"]
theorem not_closed_form_of_not_isGosperSummable {t : ℕ → K} (ht : IsHypergeometric t)
    (hns : ¬ IsGosperSummable t) {m : ℕ} (s : Fin m → ℕ → K) (α : Fin m → K)
    (hs : ∀ i, IsHypergeometric (s i)) :
    ¬ ∀ᶠ n : ℕ in atTop, ∑ k ∈ Finset.range n, t k = ∑ i, α i * s i n := by
  classical
  intro hS
  set I : Finset (Fin m) := Finset.univ.filter (fun i => α i ≠ 0) with hI
  have hIh : ∀ i ∈ I, IsHypergeometric (fun n => α i * s i n) := by
    intro i hi
    have hai : α i ≠ 0 := (Finset.mem_filter.1 hi).2
    exact IsSimilar.isHypergeometric
      ⟨C (α i), 1, by simpa using hai, one_ne_zero, Eventually.of_forall fun n => by simp⟩ (hs i)
  have hsumI : ∀ n, ∑ i, α i * s i n = ∑ i ∈ I, α i * s i n := fun n =>
    (Finset.sum_filter_of_ne fun x _ hx => left_ne_zero_of_mul hx).symm
  obtain ⟨J, u, hJI, hJh, hJd, hJsum⟩ := exists_dissimilar_sum I (fun i n => α i * s i n) hIh
  have hSJ : ∀ᶠ n : ℕ in atTop, ∑ k ∈ Finset.range n, t k = ∑ j ∈ J, u j n := by
    filter_upwards [hS, hJsum] with n h1 h2
    rw [h1, hsumI, h2]
  have hSJ1 : ∀ᶠ n : ℕ in atTop, ∑ k ∈ Finset.range (n + 1), t k = ∑ j ∈ J, u j (n + 1) :=
    (tendsto_add_atTop_nat 1).eventually hSJ
  set Q : Fin m → Prop := fun j => ∀ᶠ n : ℕ in atTop, u j (n + 1) = u j n with hQ
  set J1 : Finset (Fin m) := J.filter (fun j => ¬ Q j) with hJ1
  have hconst : ∀ᶠ n : ℕ in atTop, ∀ j ∈ J.filter Q, u j (n + 1) = u j n :=
    (Filter.eventually_all_finset _).2 fun j hj => (Finset.mem_filter.1 hj).2
  have hT : ∀ᶠ n : ℕ in atTop, t n = ∑ j ∈ J1, (u j (n + 1) - u j n) := by
    filter_upwards [hSJ, hSJ1, hconst] with n h1 h2 h3
    have e1 : ∑ k ∈ Finset.range (n + 1), t k = ∑ k ∈ Finset.range n, t k + t n :=
      Finset.sum_range_succ _ _
    have e2 : ∑ j ∈ J, (u j (n + 1) - u j n) = ∑ j ∈ J1, (u j (n + 1) - u j n) := by
      rw [← Finset.sum_filter_add_sum_filter_not J Q]
      rw [Finset.sum_eq_zero (s := J.filter Q) (fun j hj => sub_eq_zero.2 (h3 j hj)), zero_add]
    rw [← e2, Finset.sum_sub_distrib, ← h1, ← h2, e1]
    ring
  have hd : ∀ j ∈ J1, IsHypergeometric (fun n => u j (n + 1) - u j n) ∧
      IsSimilar (fun n => u j (n + 1) - u j n) (u j) := fun j hj =>
    isHypergeometric_sub_succ (hJh j (Finset.mem_filter.1 hj).1) (Finset.mem_filter.1 hj).2
  obtain ⟨i0, hi0, hi0t⟩ := exists_eq_of_sum_eq J1 (fun j n => u j (n + 1) - u j n) t
    (fun j hj => (hd j hj).1) ht
    (fun i hi j hj hij hs' => hJd i (Finset.mem_filter.1 hi).1 j (Finset.mem_filter.1 hj).1 hij
      (((hd i hi).2.symm.trans hs').trans (hd j hj).2))
    (hT.mono fun n h => h.symm)
  exact hns ⟨ht, u i0, hJh i0 (Finset.mem_filter.1 hi0).1, hi0t.mono fun n h => h.symm⟩

/-- CO-418, in terms of the algorithm: if Step 3 of Gosper's algorithm finds no polynomial
solution, the output is the partial sum, which is not a closed form of fixed length. -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 5.6.3, p. 104"]
theorem gosper_failure_no_closed_form {t : ℕ → K} {a b c : K[X]} (ht : IsHypergeometric t)
    (hb : b ≠ 0) (hc : c ≠ 0) (hab : ∀ h : ℕ, IsCoprime a (b.comp (X + C (h : K))))
    (hrel : ∀ᶠ n : ℕ in atTop,
      (b * c).eval (n : K) * t (n + 1) = (a * c.comp (X + 1)).eval (n : K) * t n)
    (hfail : gosperSolution a b c = none) {m : ℕ} (s : Fin m → ℕ → K) (α : Fin m → K)
    (hs : ∀ i, IsHypergeometric (s i)) :
    gosperOutput t a b c = (fun n => ∑ k ∈ Finset.range n, t k) ∧
      ¬ ∀ᶠ n : ℕ in atTop, gosperOutput t a b c n = ∑ i, α i * s i n := by
  have hiff := isGosperSummable_iff_polynomial_solution ht hb hc hab hrel
  have hns : ¬ IsGosperSummable t := fun hsum => by
    have := (gosperSolution_eq_none_iff hc).1 hfail
    exact this (hiff.1 hsum)
  have hout : gosperOutput t a b c = fun n => ∑ k ∈ Finset.range n, t k := by
    unfold gosperOutput; rw [hfail]
  refine ⟨hout, ?_⟩
  rw [hout]
  exact not_closed_form_of_not_isGosperSummable ht hns s α hs

/-! ### CO-417: Theorem 5.6.2, deciding rationality -/

theorem eventually_const_of_succ_eq {u : ℕ → K} (h : ∀ᶠ n : ℕ in atTop, u (n + 1) = u n) :
    ∃ α : K, ∀ᶠ n : ℕ in atTop, u n = α := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  refine ⟨u N, eventually_atTop.2 ⟨N, fun n hn => ?_⟩⟩
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih => rw [hN n hn, ih]

/-- A rational hypergeometric term is `p(n)/q(n)` with `q` monic and `p, q` coprime. -/
theorem exists_reduced_rational {t : ℕ → K} (hrat : IsSimilar t (fun _ => (1 : K))) :
    ∃ p q : K[X], q.Monic ∧ IsCoprime p q ∧ p ≠ 0 ∧
      ∀ᶠ n : ℕ in atTop, q.eval (n : K) * t n = p.eval (n : K) := by
  obtain ⟨p, q, hp, hq, h⟩ := hrat
  obtain ⟨d, p1, q1, hd, rfl, rfl, hcop⟩ := exists_coprime_factor p q hq
  have hq1 : q1 ≠ 0 := right_ne_zero_of_mul hq
  have hp1 : p1 ≠ 0 := right_ne_zero_of_mul hp
  have h1 : ∀ᶠ n : ℕ in atTop, q1.eval (n : K) * t n = p1.eval (n : K) := by
    filter_upwards [h, eventually_eval_ne_zero hd] with n e hn
    simp only [eval_mul, mul_one] at e
    apply mul_left_cancel₀ hn
    linear_combination e
  have hlc : q1.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hq1
  have hu : IsUnit (C q1.leadingCoeff⁻¹ : K[X]) :=
    isUnit_C.2 (isUnit_iff_ne_zero.2 (inv_ne_zero hlc))
  refine ⟨p1 * C q1.leadingCoeff⁻¹, q1 * C q1.leadingCoeff⁻¹, monic_mul_leadingCoeff_inv hq1,
    ?_, mul_ne_zero hp1 hu.ne_zero, ?_⟩
  · rw [isCoprime_mul_unit_right_left hu, isCoprime_mul_unit_right_right hu]
    exact hcop
  · filter_upwards [h1] with n e
    simp only [eval_mul, eval_C]
    linear_combination q1.leadingCoeff⁻¹ * e

/-- CO-417. Theorem 5.6.2.  Let `t` be hypergeometric with ratio `r = A(n) Z(n+1) / (B(n) Z(n))`
(here the book's `C` is called `Z`), given in the canonical form of Theorem 5.3.1 (`B, Z` monic,
`gcd(A, B(n+h)) = 1`, `gcd(A, Z) = 1`, `gcd(B, Z(n+1)) = 1`), and let
`B/A = a(n) c(n+1) / (b(n) c(n))` be the canonical form of `B/A` (`b, c` monic, same three
conditions, written `B b c = A a c(n+1)`).  Then `t_n` is a rational function of `n` iff `A` is
monic and `a = b = 1`. -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 5.6.2, p. 103"]
theorem isRational_iff_canonical_forms {t : ℕ → K} {A B Z a b c : K[X]} (ht : IsHypergeometric t)
    (hBm : B.Monic) (hZm : Z.Monic) (hAB : ∀ h : ℕ, IsCoprime A (B.comp (X + C (h : K))))
    (hAZ : IsCoprime A Z) (_hBZ : IsCoprime B (Z.comp (X + 1)))
    (hrel : ∀ᶠ n : ℕ in atTop,
      (B * Z).eval (n : K) * t (n + 1) = (A * Z.comp (X + 1)).eval (n : K) * t n)
    (hbm : b.Monic) (hcm : c.Monic) (hab : ∀ h : ℕ, IsCoprime a (b.comp (X + C (h : K))))
    (hac : IsCoprime a c) (hbc : IsCoprime b (c.comp (X + 1)))
    (hcan : B * (b * c) = A * (a * c.comp (X + 1))) :
    IsSimilar t (fun _ => (1 : K)) ↔ A.Monic ∧ a = 1 ∧ b = 1 := by
  have ht0 := ht.eventually_ne_zero
  have hB0 := hBm.ne_zero
  have hZ0 := hZm.ne_zero
  have hc0 := hcm.ne_zero
  have hA0 : A ≠ 0 := by
    rintro rfl
    have ht1 : ∀ᶠ n : ℕ in atTop, t (n + 1) ≠ 0 := (tendsto_add_atTop_nat 1).eventually ht0
    obtain ⟨n, h1, h2, h3⟩ := (hrel.and (ht1.and
      (eventually_eval_ne_zero (mul_ne_zero hB0 hZ0)))).exists
    simp only [zero_mul, eval_zero] at h1
    exact mul_ne_zero h3 h2 h1
  constructor
  · intro hrat
    obtain ⟨p, q, hqm, hpq, hp0, hpt⟩ := exists_reduced_rational hrat
    have hq0 := hqm.ne_zero
    have hid : B * Z * p.comp (X + 1) * q = A * Z.comp (X + 1) * p * q.comp (X + 1) := by
      have hpt1 : ∀ᶠ n : ℕ in atTop, q.eval ((n + 1 : ℕ) : K) * t (n + 1)
          = p.eval ((n + 1 : ℕ) : K) := (tendsto_add_atTop_nat 1).eventually hpt
      have : B * Z * p.comp (X + 1) * q - A * Z.comp (X + 1) * p * q.comp (X + 1) = 0 := by
        apply eq_zero_of_eventually_eval_eq_zero
        filter_upwards [hrel, hpt, hpt1] with n e1 e2 e3
        simp only [eval_mul, eval_comp_X_add_one] at e1
        simp only [eval_sub, eval_mul, eval_comp_X_add_one]
        linear_combination (-(B.eval (n : K) * Z.eval (n : K) * q.eval (n : K))) * e3
          + (A.eval (n : K) * Z.eval ((n + 1 : ℕ) : K) * q.eval ((n + 1 : ℕ) : K)) * e2
          + (q.eval (n : K) * q.eval ((n + 1 : ℕ) : K)) * e1
      exact sub_eq_zero.1 this
    have hdvd : p ∣ Z := dvd_of_gosper_forms_eq (a := q) (b := q.comp (X + 1)) (c := p)
      (a' := A) (b' := B) (c' := Z) hp0 hZ0 hpq.symm
      (by simpa using isCoprime_comp_shift hpq.symm 1) hAB (by linear_combination -hid)
    obtain ⟨s, hs⟩ := hdvd
    -- A is monic
    have hAm : A.Monic := by
      have hlp : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hp0
      have := congrArg leadingCoeff hid
      simp only [leadingCoeff_mul, comp_X_add_one_eq, leadingCoeff_comp_shift, hBm.leadingCoeff,
        hZm.leadingCoeff, hqm.leadingCoeff] at this
      show A.leadingCoeff = 1
      apply mul_right_cancel₀ hlp
      linear_combination -this
    have hp' : p.comp (X + 1) ≠ 0 := comp_X_add_one_ne_zero hp0
    have hid2 : B * q * s = A * q.comp (X + 1) * s.comp (X + 1) := by
      rw [hs, mul_comp] at hid
      apply mul_left_cancel₀ (mul_ne_zero hp0 hp')
      linear_combination hid
    have hlcs : p.leadingCoeff * s.leadingCoeff = 1 := by
      have := hZm.leadingCoeff
      rwa [hs, leadingCoeff_mul] at this
    have hc0m : (C p.leadingCoeff * q * s).Monic := by
      show (C p.leadingCoeff * q * s).leadingCoeff = 1
      rw [leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_C, hqm.leadingCoeff, mul_one]
      exact hlcs
    have hid3 : B * (C p.leadingCoeff * q * s)
        = A * (C p.leadingCoeff * q * s).comp (X + 1) := by
      simp only [mul_comp, C_comp]
      linear_combination C p.leadingCoeff * hid2
    have hh : a * c.comp (X + 1) * 1 * (C p.leadingCoeff * q * s)
        = 1 * (C p.leadingCoeff * q * s).comp (X + 1) * b * c := by
      apply mul_left_cancel₀ hA0
      linear_combination (-(C p.leadingCoeff * q * s)) * hcan + (b * c) * hid3
    obtain ⟨h1, h2, -⟩ := gosper_form_unique (a := a) (b := b) (c := c) (a' := 1) (b' := 1)
      (c' := C p.leadingCoeff * q * s) hbm hcm monic_one hc0m hab hac hbc
      (fun h => isCoprime_one_left) isCoprime_one_left isCoprime_one_left hh
    exact ⟨hAm, h1, h2⟩
  · rintro ⟨-, rfl, rfl⟩
    have hcan' : B * c = A * c.comp (X + 1) := by simpa using hcan
    set u : ℕ → K := fun n => t n * c.eval (n : K) / Z.eval (n : K) with hu
    have hsucc : ∀ᶠ n : ℕ in atTop, u (n + 1) = u n := by
      have hZ1 : ∀ᶠ n : ℕ in atTop, Z.eval ((n + 1 : ℕ) : K) ≠ 0 :=
        (tendsto_add_atTop_nat 1).eventually (eventually_eval_ne_zero hZ0)
      filter_upwards [hrel, eventually_eval_ne_zero hZ0, hZ1, eventually_eval_ne_zero hB0]
        with n e1 hZn hZ1n hBn
      have e4 := congrArg (eval (n : K)) hcan'
      simp only [eval_mul, eval_comp_X_add_one] at e1 e4
      simp only [hu]
      rw [div_eq_div_iff hZ1n hZn]
      apply mul_left_cancel₀ hBn
      linear_combination c.eval ((n + 1 : ℕ) : K) * e1
        - (Z.eval ((n + 1 : ℕ) : K) * t n) * e4
    obtain ⟨α, hα⟩ := eventually_const_of_succ_eq hsucc
    have hα0 : α ≠ 0 := by
      obtain ⟨n, h1, h2, h3, h4⟩ := (hα.and (ht0.and ((eventually_eval_ne_zero hc0).and
        (eventually_eval_ne_zero hZ0)))).exists
      rw [← h1]
      simp only [hu]
      exact div_ne_zero (mul_ne_zero h2 h3) h4
    refine ⟨C α * Z, c, mul_ne_zero (by simpa using hα0) hZ0, hc0, ?_⟩
    filter_upwards [hα, eventually_eval_ne_zero hZ0] with n h1 h2
    simp only [hu] at h1
    rw [div_eq_iff h2] at h1
    simp only [eval_mul, eval_C]
    linear_combination h1

/-! ### CO-419: the extended Gosper algorithm -/

/-- The result of applying Gosper's algorithm to `u`, abstractly: a hypergeometric antidifference
if `u` is Gosper-summable, and the partial sum `∑_{k<n} u_k` otherwise. -/
noncomputable def gosperAntidiff (u : ℕ → K) : ℕ → K := by
  classical
  exact if h : IsGosperSummable u then Classical.choose h.2 else fun n => ∑ k ∈ Finset.range n, u k

theorem gosperAntidiff_spec (u : ℕ → K) :
    ∀ᶠ n : ℕ in atTop, gosperAntidiff u (n + 1) - gosperAntidiff u n = u n := by
  unfold gosperAntidiff
  split_ifs with h
  · exact (Classical.choose_spec h.2).2
  · exact Eventually.of_forall fun n => by simp [Finset.sum_range_succ]

theorem gosperAntidiff_isHypergeometric {u : ℕ → K} (h : IsGosperSummable u) :
    IsHypergeometric (gosperAntidiff u) := by
  unfold gosperAntidiff
  simp only [h, ↓reduceDIte]
  exact (Classical.choose_spec h.2).1

/-- CO-419. The extended Gosper algorithm (page 105).  Given finitely many hypergeometric terms
`t_i`, Step 1 rewrites `∑ t_i` as a sum of pairwise dissimilar hypergeometric terms `u_j`; Steps 2
and 3 apply Gosper's algorithm to each `u_j` and add the results `s_j`.  Correctness: the sum
`σ = ∑_j s_j` satisfies `σ(n+1) - σ(n) = ∑_i t_i(n)` for large `n`, and each `s_j` is a
hypergeometric term whenever the algorithm succeeds on `u_j`. -/
@[kb "petkovsekwilfzeilberger1996" "Extended Gosper's Algorithm, p. 105"]
theorem extended_gosper {ι : Type*} [DecidableEq ι] (s : Finset ι) (t : ι → ℕ → K)
    (ht : ∀ i ∈ s, IsHypergeometric (t i)) :
    ∃ (J : Finset ι) (u : ι → ℕ → K), J ⊆ s ∧ (∀ j ∈ J, IsHypergeometric (u j)) ∧
      (∀ i ∈ J, ∀ j ∈ J, i ≠ j → ¬ IsSimilar (u i) (u j)) ∧
      (∀ᶠ n : ℕ in atTop, ∑ i ∈ s, t i n = ∑ j ∈ J, u j n) ∧
      (∀ j ∈ J, IsGosperSummable (u j) → IsHypergeometric (gosperAntidiff (u j))) ∧
      ∀ᶠ n : ℕ in atTop, ∑ j ∈ J, gosperAntidiff (u j) (n + 1) - ∑ j ∈ J, gosperAntidiff (u j) n
        = ∑ i ∈ s, t i n := by
  obtain ⟨J, u, hJs, hJh, hJd, hJsum⟩ := exists_dissimilar_sum s t ht
  refine ⟨J, u, hJs, hJh, hJd, hJsum, fun j _ h => gosperAntidiff_isHypergeometric h, ?_⟩
  have hall : ∀ᶠ n : ℕ in atTop, ∀ j ∈ J,
      gosperAntidiff (u j) (n + 1) - gosperAntidiff (u j) n = u j n :=
    (Filter.eventually_all_finset J).2 fun j _ => gosperAntidiff_spec (u j)
  filter_upwards [hall, hJsum] with n h1 h2
  rw [← Finset.sum_sub_distrib, h2]
  exact Finset.sum_congr rfl h1

/-! ### CO-445: finding a WZ certificate with Gosper's algorithm -/

theorem gosperTerm_similar {t : ℕ → K} {b c x : K[X]} (hb : b ≠ 0) (hc : c ≠ 0) (hx : x ≠ 0) :
    IsSimilar (gosperTerm t b c x) t := by
  have hv0 := eventually_eval_ne_zero hc
  have hz : ∀ᶠ n : ℕ in atTop, c.eval (n : K) * gosperTerm t b c x n
      = (b.comp (X - 1) * x).eval (n : K) * t n := by
    filter_upwards [hv0] with n hn
    simp only [gosperTerm]
    field_simp
  exact ⟨_, c, mul_ne_zero (comp_X_sub_one_ne_zero hb) hx, hc, hz⟩

/-- CO-445 (correctness direction).  Fix `n` and put `D(k) = F(n+1,k) - F(n,k)`, a hypergeometric
term in `k` similar to `F(n,k)` (as for a proper hypergeometric `F`).  Feed `D` to Gosper's
algorithm (with the Step 2 data `a, b, c` of `D`). If Gosper succeeds, its output `G(n, ·)` is a
hypergeometric term in `k` with `F(n+1,k) - F(n,k) = G(n,k+1) - G(n,k)` for large `k` (the
WZ equation (7.1.2)), and `R = G/F` is a rational function of `k` (`G(n,·) ~ F(n,·)`), the
certificate.  If Gosper fails, no hypergeometric `G(n, ·)` satisfies the equation, i.e. the
method fails. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 133-134"]
theorem wz_certificate_via_gosper (F : ℕ → ℕ → K) (n : ℕ) {a b c : K[X]}
    (hD : IsHypergeometric (fun k => F (n + 1) k - F n k))
    (hFD : IsSimilar (fun k => F (n + 1) k - F n k) (F n))
    (hb : b ≠ 0) (hc : c ≠ 0) (hab : ∀ h : ℕ, IsCoprime a (b.comp (X + C (h : K))))
    (hrel : ∀ᶠ k : ℕ in atTop, (b * c).eval (k : K) * (F (n + 1) (k + 1) - F n (k + 1))
      = (a * c.comp (X + 1)).eval (k : K) * (F (n + 1) k - F n k)) :
    (IsGosperSummable (fun k => F (n + 1) k - F n k) →
      IsHypergeometric (gosperOutput (fun k => F (n + 1) k - F n k) a b c) ∧
      (∀ᶠ k : ℕ in atTop, F (n + 1) k - F n k =
        gosperOutput (fun k => F (n + 1) k - F n k) a b c (k + 1) -
          gosperOutput (fun k => F (n + 1) k - F n k) a b c k) ∧
      IsSimilar (gosperOutput (fun k => F (n + 1) k - F n k) a b c) (F n)) ∧
    (¬ IsGosperSummable (fun k => F (n + 1) k - F n k) →
      ∀ G : ℕ → K, IsHypergeometric G →
        ¬ ∀ᶠ k : ℕ in atTop, F (n + 1) k - F n k = G (k + 1) - G k) := by
  have hsp := gosperOutput_spec hD hb hc hab hrel
  constructor
  · intro hs
    obtain ⟨⟨x, hx0, hxe, hsol⟩, hh, hdiff⟩ := hsp.1 hs
    refine ⟨hh, hdiff.mono fun k h => h.symm, ?_⟩
    have hout : gosperOutput (fun k => F (n + 1) k - F n k) a b c
        = gosperTerm (fun k => F (n + 1) k - F n k) b c x := by
      unfold gosperOutput; rw [hsol]
    rw [hout]
    exact (gosperTerm_similar hb hc hx0).trans hFD
  · intro hn G hG hGe
    exact hn ⟨hD, G, hG, hGe.mono fun k h => h.symm⟩

end UndergradKB.Combinatorics.AeqB
