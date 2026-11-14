import Mathlib.Analysis.SpecialFunctions.Exponential
import UndergradKB.Common.Attr
import UndergradKB.DifferentialEquations.FrobeniusSecond

/-! # Example 7.3.2 of Lebl, *Notes on Diffy Qs*: the second solution with a logarithm (DE-205)

`4x²y'' - 4x²y' + (1 - 2x)y = 0`, divided by `4`, is `x² y'' + x p(x) y' + q(x) y = 0` with `p(x) = -x` and
`q(x) = 1/4 - x/2`.  The indicial polynomial is `r(r-1) + P₀ r + Q₀ = r(r-1) + 1/4 = (r - 1/2)²`, so `r = 1/2` is a
double root.  The Frobenius coefficients are `a_k = 1/k!`, so `y₁ = x^{1/2} e^x`, and the general machinery
(`frobenius_second_core_entire`) gives the second solution `y₂ = x^{1/2} ∑ b_k x^k + (ln x) x^{1/2} e^x`, `b₀ = 0`,
with `∑ b_k x^k` convergent for every `x`.
-/

namespace UndergradKB.DifferentialEquations

open Filter Topology Finset

/-- The coefficients of `p(x) = -x`. -/
def exP : ℕ → ℝ := fun k => if k = 1 then -1 else 0

/-- The coefficients of `q(x) = 1/4 - x/2`. -/
noncomputable def exQ : ℕ → ℝ := fun k => if k = 0 then 1 / 4 else if k = 1 then -1 / 2 else 0

lemma exP_summable (x : ℝ) : Summable fun k => exP k * x ^ k := by
  apply summable_of_ne_finset_zero (s := {1})
  intro k hk
  have : k ≠ 1 := by simpa using hk
  simp [exP, this]

lemma exQ_summable (x : ℝ) : Summable fun k => exQ k * x ^ k := by
  apply summable_of_ne_finset_zero (s := {0, 1})
  intro k hk
  have h0 : k ≠ 0 := fun h => hk (by simp [h])
  have h1 : k ≠ 1 := fun h => hk (by simp [h])
  simp [exQ, h0, h1]

lemma psum_exP (x : ℝ) : psum exP x = -x := by
  unfold psum
  rw [tsum_eq_single 1]
  · simp [exP]
  · intro k hk; simp [exP, hk]

lemma psum_exQ (x : ℝ) : psum exQ x = 1 / 4 - x / 2 := by
  unfold psum
  rw [tsum_eq_sum (s := {0, 1})]
  · simp [exQ]; ring
  · intro k hk
    have h0 : k ≠ 0 := fun h => hk (by simp [h])
    have h1 : k ≠ 1 := fun h => hk (by simp [h])
    simp [exQ, h0, h1]

/-- **Indicial equation** of Example 7.3.2: `r(r-1) + P₀ r + Q₀ = (r - 1/2)²`, a double root at `r = 1/2`. -/
lemma example_732_indicial (t : ℝ) : aF exP exQ t = (t - 1 / 2) ^ 2 := by
  unfold aF
  simp [exP, exQ]
  ring

/-- The Frobenius coefficients at the double root `1/2` are `1/k!`. -/
lemma aCoef_ex (k : ℕ) : aCoef exP exQ (1 / 2) k = 1 / (k.factorial : ℝ) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | m
    · simp [aCoef_zero]
    · have hF : aF exP exQ (1 / 2 + ((m + 1 : ℕ) : ℝ)) = ((m : ℝ) + 1) ^ 2 := by
        rw [example_732_indicial]; push_cast; ring
      have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have hF0 : aF exP exQ (1 / 2 + ((m + 1 : ℕ) : ℝ)) ≠ 0 := by rw [hF]; positivity
      have hrec := aCoef_rec exP exQ (1 / 2) (Nat.succ_ne_zero m) hF0
      rw [Finset.sum_range_succ, Finset.sum_eq_zero (s := range m)] at hrec
      · have hP : exP (m + 1 - m) = -1 := by simp [exP]
        have hQ : exQ (m + 1 - m) = -1 / 2 := by simp [exQ]
        rw [hP, hQ, ih m (Nat.lt_succ_self m), hF] at hrec
        rw [Nat.factorial_succ]
        push_cast
        have hf : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
        field_simp
        field_simp at hrec
        nlinarith [hrec]
      · intro j hj
        have hj' := Finset.mem_range.mp hj
        have e1 : m + 1 - j ≠ 1 := by omega
        have e2 : m + 1 - j ≠ 0 := by omega
        simp [exP, exQ, e1, e2]

/-- `∑ a_k x^k = e^x` for `a_k = 1/k!`. -/
lemma fS0_inv_factorial (x : ℝ) : fS0 (fun k => 1 / (k.factorial : ℝ)) x = Real.exp x := by
  unfold fS0
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  congr 1
  funext k
  ring

/-- The second solution of Example 7.3.2 in the book's form. -/
noncomputable def ex732Y2 (b : ℕ → ℝ) (t : ℝ) : ℝ :=
  t ^ (1 / 2 : ℝ) * (∑' k, b k * t ^ k) + Real.log t * (t ^ (1 / 2 : ℝ) * Real.exp t)

/-- **Example 7.3.2 with the logarithmic second solution** (DE-205).  The equation `4x²y'' - 4x²y' + (1-2x)y = 0`
has the indicial polynomial `(r - 1/2)²` (a double root, `example_732_indicial`); the first solution is
`y₁ = x^{1/2} e^x` and there are coefficients `b_k` (`b₀ = 0`) with `∑ b_k x^k` convergent for every `x` such that
`y₂ = x^{1/2} ∑ b_k x^k + (ln x) x^{1/2} e^x` also solves the equation on `x > 0`; `y₁` and `y₂` are linearly
independent on `(0, ∞)`. -/
@[kb "lebldiffyqs2026" "Example 7.3.2, p. 343"]
theorem example_732_series :
    ∃ b : ℕ → ℝ, b 0 = 0 ∧ (∀ x : ℝ, Summable fun k => b k * x ^ k) ∧
      (∀ x : ℝ, 0 < x →
        4 * x ^ 2 * deriv (deriv (fun t : ℝ => t ^ (1 / 2 : ℝ) * Real.exp t)) x -
          4 * x ^ 2 * deriv (fun t : ℝ => t ^ (1 / 2 : ℝ) * Real.exp t) x +
          (1 - 2 * x) * (x ^ (1 / 2 : ℝ) * Real.exp x) = 0) ∧
      (∀ x : ℝ, 0 < x →
        4 * x ^ 2 * deriv (deriv (ex732Y2 b)) x - 4 * x ^ 2 * deriv (ex732Y2 b) x +
          (1 - 2 * x) * ex732Y2 b x = 0) ∧
      (∀ α β : ℝ, (∀ x : ℝ, 0 < x →
        α * (x ^ (1 / 2 : ℝ) * Real.exp x) + β * ex732Y2 b x = 0) → α = 0 ∧ β = 0) := by
  have core := frobenius_second_core_entire exP exQ exP_summable exQ_summable
    (r₁ := 1 / 2) (r₂ := 1 / 2) (N := 0) (by simp [exP]; norm_num) (by simp [exQ]; norm_num) (by simp)
  obtain ⟨hloc, ha0, hb0, -, hy1, hy2, hind⟩ := core
  set a := aCoef exP exQ (1 / 2) with ha
  set b := logB exP exQ (1 / 2) 0 (dCoef exP (1 / 2) a) with hb
  set C := logC exP exQ (1 / 2) 0 (dCoef exP (1 / 2) a) with hC
  obtain ⟨hb00, hC1⟩ := hb0 rfl
  have haeq : a = fun k => 1 / (k.factorial : ℝ) := funext aCoef_ex
  have hy1f : ∀ x, frobY a (1 / 2) x = x ^ (1 / 2 : ℝ) * Real.exp x := fun x => by
    unfold frobY; rw [haeq, fS0_inv_factorial]
  have hYe : frobY a (1 / 2) = fun t : ℝ => t ^ (1 / 2 : ℝ) * Real.exp t := funext hy1f
  have hLe : frobLogY a b (1 / 2) (1 / 2) C = ex732Y2 b := by
    funext t
    unfold frobLogY ex732Y2
    rw [hC1, hy1f]
    unfold frobY fS0
    ring
  have hexp : ∀ x : ℝ, Summable fun k => b k * x ^ k := fun x =>
    (hloc (|x| + 1) (by positivity)).2.summable (by linarith)
  refine ⟨b, hb00, hexp, fun x hx => ?_, fun x hx => ?_, fun α β h => ?_⟩
  · have := hy1 x hx
    rw [hYe, psum_exP, psum_exQ] at this
    simp only at this
    linear_combination 4 * this
  · have := hy2 x hx
    rw [hLe, psum_exP, psum_exQ] at this
    linear_combination 4 * this
  · refine hind α β fun x hx => ?_
    rw [hLe, hy1f]
    exact h x hx

end UndergradKB.DifferentialEquations
