import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.AeqB.Similar
import UndergradKB.Combinatorics.AeqB.Gosper
import UndergradKB.Combinatorics.AeqB.SequenceRing
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Polynomial and hypergeometric solutions of recurrences (Petkovsek–Wilf–Zeilberger, "A = B", §8.3, 8.4)

Degree bound for polynomial solutions of `L y = f` (Proposition 8.3.1), and the necessary and
sufficient conditions of Theorem 8.4.1 (algorithm Hyper) for a hypergeometric solution of
`L y = 0` with ratio in canonical form.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace UndergradKB.Combinatorics.AeqB
open Polynomial Filter

variable {K : Type*} [Field K] [CharZero K]

/-! ### The difference operator on `K[n]` -/

/-- The shift `p(n) ↦ p(n+1)` as a `K`-linear map on `K[n]`. -/
def shiftLin : Module.End K K[X] := (aeval (X + 1 : K[X])).toLinearMap

theorem shiftLin_apply (p : K[X]) : shiftLin p = p.comp (X + 1) := rfl

/-- The difference operator `Δ = N - 1`. -/
def deltaLin : Module.End K K[X] := shiftLin - 1

theorem deltaLin_apply (p : K[X]) : deltaLin p = p.comp (X + 1) - p := rfl

theorem shiftLin_pow_apply (i : ℕ) (p : K[X]) : (shiftLin ^ i) p = p.comp (X + C (i : K)) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', Module.End.mul_apply, ih, shiftLin_apply, comp_X_add_one_eq,
      comp_shift_comp_shift]
    push_cast
    rw [add_comm]

/-- `N^i y = ∑_j C(i,j) Δ^j y`. -/
theorem comp_shift_eq_sum (i : ℕ) (y : K[X]) :
    y.comp (X + C (i : K)) = ∑ m ∈ Finset.range (i + 1), i.choose m • ((deltaLin ^ m) y) := by
  rw [← shiftLin_pow_apply]
  have h : (shiftLin : Module.End K K[X]) = deltaLin + 1 := by
    simp [deltaLin]
  rw [h, (Commute.one_right (deltaLin : Module.End K K[X])).add_pow i]
  simp only [LinearMap.sum_apply, one_pow, mul_one]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Module.End.mul_apply, Module.End.natCast_apply, map_nsmul]

/-! ### Degrees of iterated differences -/

theorem coeff_comp_one_of_natDegree_le (w : K[X]) (M : ℕ) (hw : w.natDegree ≤ M) :
    (w.comp (X + 1)).coeff M = w.coeff M := by
  rcases hw.lt_or_eq with h | h
  · rw [coeff_eq_zero_of_natDegree_lt h, coeff_eq_zero_of_natDegree_lt]
    rw [comp_X_add_one_eq, natDegree_comp_shift]; exact h
  · subst h
    rw [comp_X_add_one_eq, coeff_comp_shift_natDegree]; rfl

theorem natDegree_shift_pow_sub_le (e : ℕ) :
    (((X + 1 : K[X]) ^ (e + 1) - X ^ (e + 1)).natDegree ≤ e) ∧
      ((X + 1 : K[X]) ^ (e + 1) - X ^ (e + 1)).coeff e = ((e + 1 : ℕ) : K) := by
  have hX : (X + 1 : K[X]) = X + C 1 := by simp
  rw [hX]
  constructor
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [coeff_sub, coeff_X_add_C_pow, coeff_X_pow]
    rcases (show N = e + 1 ∨ e + 1 < N by omega) with rfl | h
    · simp
    · rw [Nat.choose_eq_zero_of_lt h]; simp [Nat.ne_of_gt h]
  · rw [coeff_sub, coeff_X_add_C_pow, coeff_X_pow, Nat.choose_succ_self_right]
    simp

/-- One step: if `deg z ≤ E` then `deg Δz ≤ E - 1` and the coefficient of `n^{E-1}` in `Δ z` is
`E` times that of `n^E` in `z`. -/
theorem deltaLin_step (z : K[X]) (E : ℕ) (hz : z.natDegree ≤ E) :
    (deltaLin z).natDegree ≤ E - 1 ∧ (E = 0 → deltaLin z = 0) ∧
      (1 ≤ E → (deltaLin z).coeff (E - 1) = E * z.coeff E) := by
  rcases Nat.eq_zero_or_pos E with rfl | hE
  · have hC : z = C (z.coeff 0) := eq_C_of_natDegree_le_zero hz
    have h0 : deltaLin z = 0 := by rw [deltaLin_apply, hC]; simp
    exact ⟨by simp [h0], fun _ => h0, fun h => absurd h (by omega)⟩
  · obtain ⟨e, rfl⟩ : ∃ e, E = e + 1 := ⟨E - 1, by omega⟩
    obtain ⟨a, ha⟩ : ∃ a, a = z.coeff (e + 1) := ⟨_, rfl⟩
    obtain ⟨w, hw⟩ : ∃ w, w = z - C a * X ^ (e + 1) := ⟨_, rfl⟩
    have hwdeg : w.natDegree ≤ e := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [hw, coeff_sub, coeff_C_mul, coeff_X_pow]
      rcases (show N = e + 1 ∨ e + 1 < N by omega) with rfl | h
      · simp [ha]
      · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hz h)]
        simp [Nat.ne_of_gt h]
    have hzw : z = w + C a * X ^ (e + 1) := by rw [hw]; ring
    have hΔ : deltaLin z = C a * ((X + 1 : K[X]) ^ (e + 1) - X ^ (e + 1)) + deltaLin w := by
      have h1 : deltaLin z = deltaLin w + deltaLin (C a * X ^ (e + 1)) := by
        rw [← map_add, ← hzw]
      rw [h1, deltaLin_apply (C a * X ^ (e + 1))]
      simp only [mul_comp, C_comp, X_pow_comp]
      ring
    obtain ⟨hP1, hP2⟩ := natDegree_shift_pow_sub_le (K := K) e
    have hw1 : (deltaLin w).natDegree ≤ e := by
      rw [deltaLin_apply]
      refine (natDegree_sub_le _ _).trans (max_le ?_ hwdeg)
      rw [comp_X_add_one_eq, natDegree_comp_shift]; exact hwdeg
    have hw2 : (deltaLin w).coeff e = 0 := by
      rw [deltaLin_apply, coeff_sub, coeff_comp_one_of_natDegree_le w e hwdeg, sub_self]
    refine ⟨?_, fun h => by omega, fun _ => ?_⟩
    · rw [hΔ, Nat.add_sub_cancel]
      exact (natDegree_add_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans hP1) hw1)
    · rw [hΔ, coeff_add, coeff_C_mul, Nat.add_sub_cancel, hP2, hw2, ha]
      push_cast
      ring

theorem deltaLin_pow (y : K[X]) (D : ℕ) (hy : y.natDegree ≤ D) (j : ℕ) :
    ((deltaLin ^ j) y).natDegree ≤ D - j ∧ (D < j → (deltaLin ^ j) y = 0) ∧
      (j ≤ D → ((deltaLin ^ j) y).coeff (D - j) = (D.descFactorial j : K) * y.coeff D) := by
  induction j with
  | zero => simp [hy]
  | succ j ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have hs := deltaLin_step ((deltaLin ^ j) y) (D - j) h1
    have e : (deltaLin ^ (j + 1)) y = deltaLin ((deltaLin ^ j) y) := by
      rw [pow_succ', Module.End.mul_apply]
    rw [e]
    refine ⟨?_, ?_, ?_⟩
    · have := hs.1; omega
    · intro hlt
      by_cases hj : D < j
      · rw [h2 hj]; simp [deltaLin_apply]
      · exact hs.2.1 (by omega)
    · intro hle
      have e2 : D - (j + 1) = D - j - 1 := by omega
      rw [e2, hs.2.2 (by omega), h3 (by omega), Nat.descFactorial_succ, Nat.cast_mul]
      ring

/-! ### Proposition 8.3.1 -/

/-- The operator `L = ∑_{i ≤ r} p_i(n) N^i` applied to a polynomial `y`:
`(L y)(n) = ∑_i p_i(n) y(n + i)`. -/
def applyOp (p : ℕ → K[X]) (r : ℕ) (y : K[X]) : K[X] :=
  ∑ i ∈ Finset.range (r + 1), p i * y.comp (X + C (i : K))

/-- The coefficient `q_j = ∑_{i=j}^r C(i,j) p_i` of `Δ^j` in the expansion of `L` in terms of
`Δ = N - 1` (equation (8.3.2), p. 159). -/
def qPoly (p : ℕ → K[X]) (r j : ℕ) : K[X] :=
  ∑ i ∈ Finset.Ico j (r + 1), i.choose j • p i

open Classical in
/-- The degree polynomial `α(x) = ∑_{deg q_j - j = b} lc(q_j) x^{\underline j}` of equation
(8.3.4), where `x^{\underline j}` is the falling factorial. -/
def degreePoly (p : ℕ → K[X]) (r : ℕ) (b : ℤ) : K[X] :=
  ∑ j ∈ (Finset.range (r + 1)).filter
      (fun j => qPoly p r j ≠ 0 ∧ ((qPoly p r j).natDegree : ℤ) - j = b),
    C (qPoly p r j).leadingCoeff * descPochhammer K j

theorem qPoly_eq_sum_range (p : ℕ → K[X]) (r j : ℕ) :
    qPoly p r j = ∑ i ∈ Finset.range (r + 1), i.choose j • p i := by
  unfold qPoly
  refine Finset.sum_subset ?_ ?_
  · intro i hi; simp only [Finset.mem_Ico, Finset.mem_range] at hi ⊢; omega
  · intro i hi hni
    simp only [Finset.mem_Ico, Finset.mem_range] at hi hni
    rw [Nat.choose_eq_zero_of_lt (by omega), zero_smul]

/-- `L = ∑ q_j Δ^j`. -/
theorem applyOp_eq (p : ℕ → K[X]) (r : ℕ) (y : K[X]) :
    applyOp p r y = ∑ j ∈ Finset.range (r + 1), qPoly p r j * (deltaLin ^ j) y := by
  have h1 : ∀ i ∈ Finset.range (r + 1), p i * y.comp (X + C (i : K))
      = ∑ m ∈ Finset.range (r + 1), p i * (i.choose m • (deltaLin ^ m) y) := by
    intro i hi
    rw [comp_shift_eq_sum, Finset.mul_sum]
    refine Finset.sum_subset ?_ ?_
    · intro m hm
      simp only [Finset.mem_range] at hm hi ⊢; omega
    · intro m hm hnm
      simp only [Finset.mem_range] at hm hnm
      rw [Nat.choose_eq_zero_of_lt (by omega), zero_smul, mul_zero]
  unfold applyOp
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [qPoly_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, smul_mul_assoc]

open Classical in
/-- Contribution of one term `q_j Δ^j y` to the coefficient of `n^{D+b}`. -/
theorem term_facts (Q y : K[X]) (j D m : ℕ) (b : ℤ) (hy : y.natDegree = D)
    (hb : Q ≠ 0 → (Q.natDegree : ℤ) - j ≤ b) (hm : (m : ℤ) = D + b) :
    (Q * (deltaLin ^ j) y).natDegree ≤ m ∧
      (Q * (deltaLin ^ j) y).coeff m =
        if Q ≠ 0 ∧ (Q.natDegree : ℤ) - j = b then
          Q.leadingCoeff * ((D.descFactorial j : K) * y.coeff D) else 0 := by
  have hD := deltaLin_pow y D hy.le j
  by_cases hQ : Q = 0
  · subst hQ; simp
  have hbQ := hb hQ
  by_cases hj : D < j
  · rw [hD.2.1 hj]
    have : D.descFactorial j = 0 := Nat.descFactorial_eq_zero_iff_lt.2 hj
    simp [this]
  push Not at hj
  have hdeg := hD.1
  have hle : (Q * (deltaLin ^ j) y).natDegree ≤ Q.natDegree + (D - j) :=
    natDegree_mul_le_of_le le_rfl hdeg
  by_cases hc : (Q.natDegree : ℤ) - j = b
  · have hmeq : m = Q.natDegree + (D - j) := by omega
    refine ⟨by omega, ?_⟩
    rw [if_pos (And.intro hQ hc), hmeq, coeff_mul_add_eq_of_natDegree_le le_rfl hdeg, hD.2.2 hj]
    rfl
  · refine ⟨by omega, ?_⟩
    rw [if_neg (fun h => hc h.2)]
    exact coeff_eq_zero_of_natDegree_lt (by omega)

open Classical in
/-- CO-486 (core). Let `y ≠ 0` be a polynomial solution of `L y = f`, and let `b` be (an upper
bound for, in the book exactly) `max (deg q_j - j)`.  Then one of: `deg y + b < 0`;
`f ≠ 0` and `deg y + b = deg f`; or `deg y` is a root of the degree polynomial `α`. -/
theorem degree_cases (p : ℕ → K[X]) (r : ℕ) (y f : K[X]) (b : ℤ)
    (hb : ∀ j ≤ r, qPoly p r j ≠ 0 → ((qPoly p r j).natDegree : ℤ) - j ≤ b)
    (h : applyOp p r y = f) (hy : y ≠ 0) :
    ((y.natDegree : ℤ) + b < 0) ∨ (f ≠ 0 ∧ (y.natDegree : ℤ) + b = f.natDegree) ∨
      (degreePoly p r b).eval (y.natDegree : K) = 0 := by
  by_cases hT : (y.natDegree : ℤ) + b < 0
  · exact Or.inl hT
  push Not at hT
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = y.natDegree + b := ⟨(y.natDegree + b).toNat, by omega⟩
  have hfac : ∀ j ∈ Finset.range (r + 1),
      (qPoly p r j * (deltaLin ^ j) y).natDegree ≤ m ∧
      (qPoly p r j * (deltaLin ^ j) y).coeff m =
        if qPoly p r j ≠ 0 ∧ ((qPoly p r j).natDegree : ℤ) - j = b then
          (qPoly p r j).leadingCoeff * ((y.natDegree.descFactorial j : K) * y.coeff y.natDegree)
        else 0 := fun j hj =>
    term_facts _ y j y.natDegree m b rfl (hb j (by simpa [Nat.lt_succ_iff] using hj)) hm
  have hfeq : f = ∑ j ∈ Finset.range (r + 1), qPoly p r j * (deltaLin ^ j) y := by
    rw [← h, applyOp_eq]
  have hfdeg : f.natDegree ≤ m := by
    rw [hfeq]; exact natDegree_sum_le_of_forall_le _ _ fun j hj => (hfac j hj).1
  have hfc : f.coeff m = y.leadingCoeff * (degreePoly p r b).eval (y.natDegree : K) := by
    rw [hfeq, finsetSum_coeff, Finset.sum_congr rfl fun j hj => (hfac j hj).2, degreePoly,
      eval_finsetSum, Finset.mul_sum, ← Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [eval_mul, eval_C, descPochhammer_eval_eq_descFactorial]
    simp only [leadingCoeff]
    ring
  by_cases hα : (degreePoly p r b).eval (y.natDegree : K) = 0
  · exact Or.inr (Or.inr hα)
  · have hne : f.coeff m ≠ 0 := by
      rw [hfc]; exact mul_ne_zero (leadingCoeff_ne_zero.2 hy) hα
    have hf0 : f ≠ 0 := fun h0 => hne (by rw [h0]; simp)
    have hmf : m ≤ f.natDegree := le_natDegree_of_ne_zero hne
    exact Or.inr (Or.inl ⟨hf0, by omega⟩)

/-- CO-486. Proposition 8.3.1: let `L = ∑_{i ≤ r} p_i N^i`, `q_j = ∑_{i ≥ j} C(i,j) p_i`,
`b = max_j (deg q_j - j)` (the maximum is over the `j` with `q_j ≠ 0`), and `α` the degree
polynomial.  If `d₁` bounds the nonnegative integer roots of `α` and `L y = f` with `f, y`
polynomials, then `deg y ≤ d` for every integer `d` with `deg f - b ≤ d` (when `f ≠ 0`),
`-b - 1 ≤ d` and `d₁ ≤ d` (in particular for the book's `d = max {deg f - b, -b - 1, d₁}`). -/
@[kb "petkovsekwilfzeilberger1996" "Proposition 8.3.1, p. 160"]
theorem natDegree_le_of_applyOp_eq (p : ℕ → K[X]) (r : ℕ) (y f : K[X]) (b : ℤ)
    (hb : ∀ j ≤ r, qPoly p r j ≠ 0 → ((qPoly p r j).natDegree : ℤ) - j ≤ b)
    (_hbmax : ∃ j ≤ r, qPoly p r j ≠ 0 ∧ ((qPoly p r j).natDegree : ℤ) - j = b)
    (d₁ : ℕ) (hd₁ : ∀ x : ℕ, (degreePoly p r b).eval (x : K) = 0 → x ≤ d₁)
    (h : applyOp p r y = f) (d : ℤ) (hd : f ≠ 0 → (f.natDegree : ℤ) - b ≤ d)
    (hd' : -b - 1 ≤ d) (hd₁' : (d₁ : ℤ) ≤ d) :
    y = 0 ∨ (y.natDegree : ℤ) ≤ d := by
  by_cases hy : y = 0
  · exact Or.inl hy
  right
  rcases degree_cases p r y f b hb h hy with h1 | ⟨h2, h3⟩ | h4
  · omega
  · have := hd h2; omega
  · have := hd₁ _ h4; omega

/-- CO-486, book shape: with `d = max {deg f - b, -b - 1, d₁}` (`f ≠ 0`). -/
@[kb "petkovsekwilfzeilberger1996" "Proposition 8.3.1, p. 160"]
theorem natDegree_le_book_bound (p : ℕ → K[X]) (r : ℕ) (y f : K[X]) (b : ℤ)
    (hb : ∀ j ≤ r, qPoly p r j ≠ 0 → ((qPoly p r j).natDegree : ℤ) - j ≤ b)
    (hbmax : ∃ j ≤ r, qPoly p r j ≠ 0 ∧ ((qPoly p r j).natDegree : ℤ) - j = b)
    (d₁ : ℕ) (hd₁ : ∀ x : ℕ, (degreePoly p r b).eval (x : K) = 0 → x ≤ d₁)
    (_hf : f ≠ 0) (h : applyOp p r y = f) :
    y = 0 ∨ (y.natDegree : ℤ) ≤ max (max ((f.natDegree : ℤ) - b) (-b - 1)) d₁ :=
  natDegree_le_of_applyOp_eq p r y f b hb hbmax d₁ hd₁ h _
    (fun _ => (le_max_left _ _).trans (le_max_left _ _))
    ((le_max_right _ _).trans (le_max_left _ _)) (le_max_right _ _)

/-! ### Theorem 8.4.1 (algorithm Hyper) -/

/-- The polynomial `P_i(n) = p_i(n) ∏_{j<i} a(n+j) ∏_{j=i}^{d-1} b(n+j)` of algorithm Hyper. -/
def hyperP (p : ℕ → K[X]) (a b : K[X]) (d i : ℕ) : K[X] :=
  p i * (∏ j ∈ Finset.range i, a.comp (X + C (j : K))) *
    ∏ j ∈ Finset.Ico i d, b.comp (X + C (j : K))

/-- `m = max_i deg P_i`. -/
def hyperDeg (p : ℕ → K[X]) (a b : K[X]) (d : ℕ) : ℕ :=
  (Finset.range (d + 1)).sup fun i => (hyperP p a b d i).natDegree

/-- `α_i`, the coefficient of `n^m` in `P_i(n)`. -/
def hyperAlpha (p : ℕ → K[X]) (a b : K[X]) (d i : ℕ) : K :=
  (hyperP p a b d i).coeff (hyperDeg p a b d)

/-- The auxiliary recurrence (8.4.6) `∑_i z^i P_i(n) c(n+i) = 0`, as an identity of polynomials. -/
def AuxRecurrence (p : ℕ → K[X]) (a b c : K[X]) (z : K) (d : ℕ) : Prop :=
  ∑ i ∈ Finset.range (d + 1), C (z ^ i) * hyperP p a b d i * c.comp (X + C (i : K)) = 0

/-- The ratio `S(n) = z a(n) c(n+1) / (b(n) c(n))` (8.4.7). -/
def hyperRatio (z : K) (a b c : K[X]) (n : ℕ) : K :=
  z * (a.eval (n : K) / b.eval (n : K)) * (c.eval ((n : K) + 1) / c.eval (n : K))

theorem eventually_eval_shift_ne_zero {b : K[X]} (hb : b ≠ 0) (j : ℕ) :
    ∀ᶠ n : ℕ in atTop, b.eval ((n : K) + j) ≠ 0 := by
  filter_upwards [eventually_eval_ne_zero (comp_X_add_C_ne_zero' hb (j : K))] with n hn
  simpa [eval_comp, add_comm] using hn

theorem hyper_step_identity (z : K) (a b c : K[X]) (y : ℕ → K) (n i : ℕ)
    (hb : ∀ j < i, b.eval ((n : K) + j) ≠ 0) (hc : ∀ j ≤ i, c.eval ((n : K) + j) ≠ 0)
    (hS : ∀ j < i, y (n + j + 1) = hyperRatio z a b c (n + j) * y (n + j)) :
    y (n + i) * (c.eval (n : K) * ∏ j ∈ Finset.range i, b.eval ((n : K) + j)) =
      z ^ i * (∏ j ∈ Finset.range i, a.eval ((n : K) + j)) * c.eval ((n : K) + i) * y n := by
  induction i with
  | zero => simp; ring
  | succ i ih =>
    have ih' := ih (fun j hj => hb j (by omega)) (fun j hj => hc j (by omega))
      (fun j hj => hS j (by omega))
    have hbi := hb i (by omega)
    have hci := hc i (by omega)
    have hci1 := hc (i + 1) le_rfl
    have hS' := hS i (by omega)
    simp only [hyperRatio] at hS'
    push_cast at hS' hci1 ⊢
    rw [show n + (i + 1) = n + i + 1 from rfl, hS', Finset.prod_range_succ, Finset.prod_range_succ]
    have e1 : (n : K) + (i + 1) = (n : K) + i + 1 := by ring
    rw [e1] at hci1 ⊢
    calc _ = (z * (a.eval ((n : K) + i)) * c.eval ((n : K) + i + 1) / c.eval ((n : K) + i)) *
          (y (n + i) * (c.eval (n : K) * ∏ j ∈ Finset.range i, b.eval ((n : K) + j))) := by
            field_simp
      _ = _ := by
            rw [ih']
            field_simp
            ring

theorem hyperP_eval (p : ℕ → K[X]) (a b : K[X]) (d i : ℕ) (n : ℕ) :
    (hyperP p a b d i).eval (n : K) = (p i).eval (n : K) *
      (∏ j ∈ Finset.range i, a.eval ((n : K) + j)) *
        ∏ j ∈ Finset.Ico i d, b.eval ((n : K) + j) := by
  simp [hyperP, eval_mul, eval_prod, eval_comp, add_comm]

theorem hyper_sum_identity (p : ℕ → K[X]) (z : K) (a b c : K[X]) (y : ℕ → K) (n d : ℕ)
    (hb : ∀ j < d, b.eval ((n : K) + j) ≠ 0) (hc : ∀ j ≤ d, c.eval ((n : K) + j) ≠ 0)
    (hS : ∀ j < d, y (n + j + 1) = hyperRatio z a b c (n + j) * y (n + j)) :
    (∑ i ∈ Finset.range (d + 1), (p i).eval (n : K) * y (n + i)) *
        (c.eval (n : K) * ∏ j ∈ Finset.range d, b.eval ((n : K) + j)) =
      y n * ∑ i ∈ Finset.range (d + 1),
        z ^ i * (hyperP p a b d i).eval (n : K) * c.eval ((n : K) + i) := by
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hid : i ≤ d := by simpa [Nat.lt_succ_iff] using hi
  have step := hyper_step_identity z a b c y n i (fun j hj => hb j (by omega))
    (fun j hj => hc j (by omega)) (fun j hj => hS j (by omega))
  have hsplit : ∏ j ∈ Finset.range d, b.eval ((n : K) + j) =
      (∏ j ∈ Finset.range i, b.eval ((n : K) + j)) * ∏ j ∈ Finset.Ico i d, b.eval ((n : K) + j) :=
    (Finset.prod_range_mul_prod_Ico (fun j => b.eval ((n : K) + j)) hid).symm
  rw [hyperP_eval, hsplit]
  calc (p i).eval (n : K) * y (n + i) *
        (c.eval (n : K) * ((∏ j ∈ Finset.range i, b.eval ((n : K) + j)) *
          ∏ j ∈ Finset.Ico i d, b.eval ((n : K) + j)))
      = (p i).eval (n : K) * (y (n + i) * (c.eval (n : K) *
          ∏ j ∈ Finset.range i, b.eval ((n : K) + j))) *
          ∏ j ∈ Finset.Ico i d, b.eval ((n : K) + j) := by ring
    _ = _ := by rw [step]; ring

theorem hyper_good_eventually {z : K} {a b c : K[X]} {y : ℕ → K} (hb : b ≠ 0) (hc : c ≠ 0)
    (hS : ∀ᶠ n : ℕ in atTop, y (n + 1) = hyperRatio z a b c n * y n) (d : ℕ) :
    ∀ᶠ n : ℕ in atTop, (∀ j < d, b.eval ((n : K) + j) ≠ 0) ∧ (∀ j ≤ d, c.eval ((n : K) + j) ≠ 0) ∧
      ∀ j < d, y (n + j + 1) = hyperRatio z a b c (n + j) * y (n + j) := by
  have h1 : ∀ᶠ n : ℕ in atTop, ∀ j ∈ Finset.range d, b.eval ((n : K) + j) ≠ 0 :=
    (Filter.eventually_all_finset _).2 fun j _ => eventually_eval_shift_ne_zero hb j
  have h2 : ∀ᶠ n : ℕ in atTop, ∀ j ∈ Finset.range (d + 1), c.eval ((n : K) + j) ≠ 0 :=
    (Filter.eventually_all_finset _).2 fun j _ => eventually_eval_shift_ne_zero hc j
  have h3 : ∀ᶠ n : ℕ in atTop, ∀ j ∈ Finset.range d,
      y (n + j + 1) = hyperRatio z a b c (n + j) * y (n + j) :=
    (Filter.eventually_all_finset _).2 fun j _ => (tendsto_add_atTop_nat j).eventually hS
  filter_upwards [h1, h2, h3] with n a1 a2 a3
  exact ⟨fun j hj => a1 j (Finset.mem_range.2 hj),
    fun j hj => a2 j (Finset.mem_range.2 (by omega)), fun j hj => a3 j (Finset.mem_range.2 hj)⟩

theorem aux_eval (p : ℕ → K[X]) (a b c : K[X]) (z : K) (d n : ℕ) :
    (∑ i ∈ Finset.range (d + 1), C (z ^ i) * hyperP p a b d i * c.comp (X + C (i : K))).eval
        (n : K) =
      ∑ i ∈ Finset.range (d + 1), z ^ i * (hyperP p a b d i).eval (n : K) * c.eval ((n : K) + i) := by
  simp only [eval_finsetSum, eval_mul, eval_C, eval_comp, eval_add, eval_X]

/-- CO-491. Soundness of algorithm Hyper (converse of Theorem 8.4.1): if `c` satisfies the
auxiliary recurrence (8.4.6) for `z, a, b` (with `b, c ≠ 0`) and `y(n+1) = S(n) y(n)` for large
`n`, where `S = z a(n) c(n+1) / (b(n) c(n))`, then `y` satisfies `∑ p_i(n) y(n+i) = 0` for large
`n`. -/
@[kb "petkovsekwilfzeilberger1996" "text (converse of Theorem 8.4.1), p. 163"]
theorem hyper_sound (p : ℕ → K[X]) (d : ℕ) (z : K) (a b c : K[X]) (hb : b ≠ 0) (hc : c ≠ 0)
    (hrec : AuxRecurrence p a b c z d) (y : ℕ → K)
    (hS : ∀ᶠ n : ℕ in atTop, y (n + 1) = hyperRatio z a b c n * y n) :
    ∀ᶠ n : ℕ in atTop, ∑ i ∈ Finset.range (d + 1), (p i).eval (n : K) * y (n + i) = 0 := by
  have hE : ∀ n : ℕ, ∑ i ∈ Finset.range (d + 1),
      z ^ i * (hyperP p a b d i).eval (n : K) * c.eval ((n : K) + i) = 0 := by
    intro n
    have := aux_eval p a b c z d n
    rw [hrec, eval_zero] at this
    exact this.symm
  filter_upwards [hyper_good_eventually (z := z) (a := a) (y := y) hb hc hS d,
    eventually_eval_ne_zero hc,
    (Filter.eventually_all_finset (Finset.range d)).2 fun j _ => eventually_eval_shift_ne_zero hb j]
    with n ⟨h1, h2, h3⟩ h4 h5
  have key := hyper_sum_identity p z a b c y n d h1 h2 h3
  rw [hE n, mul_zero] at key
  have hne : c.eval (n : K) * ∏ j ∈ Finset.range d, b.eval ((n : K) + j) ≠ 0 :=
    mul_ne_zero h4 (Finset.prod_ne_zero_iff.2 fun j hj => h5 j hj)
  exact (mul_eq_zero.1 key).resolve_right hne

/-- The auxiliary recurrence follows from the hypergeometric solution (item 4 of Theorem 8.4.1). -/
theorem aux_of_hyper (p : ℕ → K[X]) (d : ℕ) (y : ℕ → K)
    (hy : ¬ ∀ᶠ n : ℕ in atTop, y n = 0)
    (hL : ∀ᶠ n : ℕ in atTop, ∑ i ∈ Finset.range (d + 1), (p i).eval (n : K) * y (n + i) = 0)
    (z : K) (a b c : K[X]) (hb : b ≠ 0) (hc : c ≠ 0)
    (hS : ∀ᶠ n : ℕ in atTop, y (n + 1) = hyperRatio z a b c n * y n) :
    AuxRecurrence p a b c z d := by
  have hyne : ∀ᶠ n : ℕ in atTop, y n ≠ 0 :=
    (SeqRing.eventually_ne_zero_of_shift_eq hy hS).1
  apply eq_zero_of_eventually_eval_eq_zero
  filter_upwards [hyper_good_eventually (z := z) (a := a) (y := y) hb hc hS d, hL, hyne,
    eventually_eval_ne_zero hc,
    (Filter.eventually_all_finset (Finset.range d)).2 fun j _ => eventually_eval_shift_ne_zero hb j]
    with n ⟨h1, h2, h3⟩ hLn hyn h4 h5
  have key := hyper_sum_identity p z a b c y n d h1 h2 h3
  rw [hLn, zero_mul] at key
  rw [aux_eval]
  exact (mul_eq_zero.1 key.symm).resolve_left hyn

theorem aux_dvd_a (p : ℕ → K[X]) (a b c : K[X]) (z : K) (d : ℕ)
    (hrec : AuxRecurrence p a b c z d)
    (hab : ∀ h : ℕ, IsCoprime a (b.comp (X + C (h : K)))) (hac : IsCoprime a c) : a ∣ p 0 := by
  unfold AuxRecurrence at hrec
  rw [Finset.sum_range_succ'] at hrec
  have h1 : a ∣ ∑ i ∈ Finset.range d,
      C (z ^ (i + 1)) * hyperP p a b d (i + 1) * c.comp (X + C ((i + 1 : ℕ) : K)) := by
    refine Finset.dvd_sum fun i _ => ?_
    have : a ∣ ∏ j ∈ Finset.range (i + 1), a.comp (X + C (j : K)) := by
      have h := Finset.dvd_prod_of_mem (fun j : ℕ => a.comp (X + C (j : K)))
        (Finset.mem_range.2 (Nat.succ_pos i))
      simp only [Nat.cast_zero, C_0, add_zero, comp_X] at h
      exact h
    unfold hyperP
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_right this _) _) _) _
  have h0 := (dvd_add_right h1).1 (by rw [hrec]; exact dvd_zero a)
  have hIco : Finset.Ico 0 d = Finset.range d := Nat.Ico_zero_eq_range d
  have e0 : C (z ^ 0) * hyperP p a b d 0 * c.comp (X + C ((0 : ℕ) : K)) =
      p 0 * ((∏ j ∈ Finset.range d, b.comp (X + C (j : K))) * c) := by
    simp [hyperP, hIco]
    ring
  rw [e0] at h0
  have hcop : IsCoprime a ((∏ j ∈ Finset.range d, b.comp (X + C (j : K))) * c) :=
    IsCoprime.mul_right (IsCoprime.prod_right fun j _ => hab j) hac
  exact hcop.dvd_of_dvd_mul_right (by simpa [mul_comm] using h0)

theorem aux_dvd_b (p : ℕ → K[X]) (a b c : K[X]) (z : K) (hz : z ≠ 0) (d : ℕ) (hd : 0 < d)
    (hrec : AuxRecurrence p a b c z d)
    (hab : ∀ h : ℕ, IsCoprime a (b.comp (X + C (h : K))))
    (hbc : IsCoprime b (c.comp (X + 1))) : b.comp (X + C ((d - 1 : ℕ) : K)) ∣ p d := by
  unfold AuxRecurrence at hrec
  rw [Finset.sum_range_succ] at hrec
  set β := b.comp (X + C ((d - 1 : ℕ) : K)) with hβ
  have h1 : β ∣ ∑ i ∈ Finset.range d,
      C (z ^ i) * hyperP p a b d i * c.comp (X + C (i : K)) := by
    refine Finset.dvd_sum fun i hi => ?_
    have hi' : i < d := Finset.mem_range.1 hi
    have : β ∣ ∏ j ∈ Finset.Ico i d, b.comp (X + C (j : K)) :=
      Finset.dvd_prod_of_mem (fun j : ℕ => b.comp (X + C (j : K)))
        (Finset.mem_Ico.2 ⟨by omega, by omega⟩)
    unfold hyperP
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right this _) _) _
  have h0 := (dvd_add_right h1).1 (by rw [hrec]; exact dvd_zero β)
  have hu : IsUnit (C (z ^ d) : K[X]) := isUnit_C.2 (IsUnit.mk0 _ (pow_ne_zero d hz))
  have e0 : C (z ^ d) * hyperP p a b d d * c.comp (X + C (d : K)) =
      C (z ^ d) * ((p d * ∏ j ∈ Finset.range d, a.comp (X + C (j : K))) *
        c.comp (X + C (d : K))) := by
    simp [hyperP]
    ring
  rw [e0] at h0
  have h2 := (hu.dvd_mul_left).1 h0
  have hca : IsCoprime β (∏ j ∈ Finset.range d, a.comp (X + C (j : K))) := by
    refine IsCoprime.prod_right fun j hj => ?_
    have hj' : j < d := Finset.mem_range.1 hj
    have := isCoprime_comp_shift (hab (d - 1 - j)) (j : K)
    rw [comp_shift_comp_shift,
      show (((d - 1 - j : ℕ) : K) + (j : K)) = ((d - 1 : ℕ) : K) by
        rw [← Nat.cast_add]; congr 1; omega] at this
    exact this.symm
  have hcc : IsCoprime β (c.comp (X + C (d : K))) := by
    have := isCoprime_comp_shift hbc ((d - 1 : ℕ) : K)
    rw [comp_X_add_one_eq, comp_shift_comp_shift,
      show (1 + ((d - 1 : ℕ) : K)) = (d : K) by
        rw [add_comm, ← Nat.cast_succ]; congr 1; omega] at this
    exact this
  have h3 := hcc.dvd_of_dvd_mul_right h2
  exact hca.dvd_of_dvd_mul_right h3

/-- CO-489. Theorem 8.4.1: let `y` be a nonzero solution of `∑_{i ≤ d} p_i(n) y(n+i) = 0`
(`p_0, p_d ≠ 0`, `d ≥ 1`) with `y(n+1) = S(n) y(n)` and `S(n) = z a(n) c(n+1) / (b(n) c(n))` where
`a, b, c` satisfy conditions (i)-(iii) of Theorem 5.3.1 (`b, c` monic).  Then
(1) `∑ α_i z^i = 0`, (2) `a ∣ p_0(n)`, (3) `b ∣ p_d(n - d + 1)`, and (4) `c` satisfies the
auxiliary recurrence (8.4.6). -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 8.4.1, p. 162"]
theorem hyper_necessary (p : ℕ → K[X]) (d : ℕ) (hd : 0 < d) (_hp0 : p 0 ≠ 0) (_hpd : p d ≠ 0)
    (y : ℕ → K) (hy : ¬ ∀ᶠ n : ℕ in atTop, y n = 0)
    (hL : ∀ᶠ n : ℕ in atTop, ∑ i ∈ Finset.range (d + 1), (p i).eval (n : K) * y (n + i) = 0)
    (z : K) (hz : z ≠ 0) (a b c : K[X]) (hbm : b.Monic) (hcm : c.Monic)
    (hab : ∀ h : ℕ, IsCoprime a (b.comp (X + C (h : K)))) (hac : IsCoprime a c)
    (hbc : IsCoprime b (c.comp (X + 1)))
    (hS : ∀ᶠ n : ℕ in atTop, y (n + 1) = hyperRatio z a b c n * y n) :
    (∑ i ∈ Finset.range (d + 1), hyperAlpha p a b d i * z ^ i = 0) ∧ a ∣ p 0 ∧
      b ∣ (p d).comp (X + C (1 - (d : K))) ∧ AuxRecurrence p a b c z d := by
  have hE := aux_of_hyper p d y hy hL z a b c hbm.ne_zero hcm.ne_zero hS
  refine ⟨?_, aux_dvd_a p a b c z d hE hab hac, ?_, hE⟩
  · have hco := congrArg (fun q : K[X] => q.coeff (hyperDeg p a b d + c.natDegree)) hE
    simp only [finsetSum_coeff, coeff_zero] at hco
    rw [← hco]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hP : (hyperP p a b d i).natDegree ≤ hyperDeg p a b d :=
      Finset.le_sup (f := fun i => (hyperP p a b d i).natDegree) hi
    rw [mul_assoc, coeff_C_mul,
      coeff_mul_add_eq_of_natDegree_le hP (natDegree_comp_shift c _).le,
      coeff_comp_shift_natDegree, hcm.leadingCoeff]
    simp only [hyperAlpha]
    ring
  · have h1 := aux_dvd_b p a b c z hz d hd hE hab hbc
    have h2 := dvd_comp_shift h1 (-((d - 1 : ℕ) : K))
    rw [comp_shift_comp_shift, add_neg_cancel, C_0, add_zero, comp_X] at h2
    have e : (1 - (d : K)) = -((d - 1 : ℕ) : K) := by
      rw [Nat.cast_sub hd]; push_cast; ring
    rw [e]
    exact h2

/-! ### First-order recurrences (text, p. 113) -/

/-- CO-422. A first-order recurrence `a₁(n) f(n+1) + a₀(n) f(n) = 0` with nowhere vanishing
coefficients has the solution `f(n) = f(0) ∏_{j<n} (-a₀(j)/a₁(j))`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 113"]
theorem order_one_solution (a₀ a₁ f : ℕ → K) (h₁ : ∀ n, a₁ n ≠ 0)
    (hf : ∀ n, a₁ n * f (n + 1) + a₀ n * f n = 0) (n : ℕ) :
    f n = f 0 * ∏ j ∈ Finset.range n, (-(a₀ j) / a₁ j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ← ih]
    have := hf n
    field_simp [h₁ n]
    linear_combination this

/-- CO-422. For polynomial coefficients `a₀, a₁ ≠ 0`, a solution of the first-order recurrence
(for large `n`) that is not eventually zero is a hypergeometric term, with ratio
`f(n+1)/f(n) = -a₀(n)/a₁(n)` (the sum recurrence of order 1 case). -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 113"]
theorem isHypergeometric_of_order_one (a₀ a₁ : K[X]) (h₀ : a₀ ≠ 0) (h₁ : a₁ ≠ 0) (f : ℕ → K)
    (hf0 : ¬ ∀ᶠ n : ℕ in atTop, f n = 0)
    (hf : ∀ᶠ n : ℕ in atTop, a₁.eval (n : K) * f (n + 1) + a₀.eval (n : K) * f n = 0) :
    IsHypergeometric f ∧
      ∀ᶠ n : ℕ in atTop, f (n + 1) / f n = -(a₀.eval (n : K)) / a₁.eval (n : K) := by
  have hh : IsHypergeometric f := ⟨hf0, a₁, a₀, h₁, h₀, hf⟩
  refine ⟨hh, ?_⟩
  filter_upwards [hf, hh.eventually_ne_zero, eventually_eval_ne_zero h₁] with n e h2 h3
  rw [div_eq_div_iff h2 h3]
  linear_combination e

end UndergradKB.Combinatorics.AeqB

end
