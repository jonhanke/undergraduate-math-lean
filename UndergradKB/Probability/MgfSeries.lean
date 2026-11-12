import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Probability.Moments.ComplexMGF
import UndergradKB.Common.Attr

/-!
# Moment generating functions of bounded random variables

Grinstead–Snell Theorems 10.3 and 10.4: for a bounded random variable the moment series
`∑ μ_k t^k / k!` converges to the moment generating function, and the moment generating function
determines the distribution.
-/

namespace UndergradKB.Probability

open MeasureTheory ProbabilityTheory Filter
open scoped Nat

/-- A bounded random variable has `exp (t X)` integrable for every real `t`. -/
theorem integrable_exp_mul_of_bounded {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : AEMeasurable X P) (M : ℝ)
    (hM : ∀ᵐ ω ∂P, |X ω| ≤ M) (t : ℝ) : Integrable (fun ω => Real.exp (t * X ω)) P := by
  refine Integrable.of_bound (C := Real.exp (|t| * M)) (by fun_prop) ?_
  filter_upwards [hM] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.2
  calc t * X ω ≤ |t * X ω| := le_abs_self _
    _ = |t| * |X ω| := abs_mul _ _
    _ ≤ |t| * M := by gcongr

/-- Grinstead–Snell Theorem 10.3 (PR-107). For a bounded random variable `X` the moments
`μ_k = E(X^k)` exist, and for every real `t` the series `∑ μ_k t^k / k!` converges to the moment
generating function `g(t) = E(e^(tX))`. -/
@[kb "grinsteadsnell2006" "Theorem 10.3, p. 404"]
theorem hasSum_moments_mgf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : AEMeasurable X P) (M : ℝ)
    (hM : ∀ᵐ ω ∂P, |X ω| ≤ M) (t : ℝ) :
    (∀ k : ℕ, Integrable (fun ω => X ω ^ k) P) ∧
      HasSum (fun k : ℕ => t ^ k * (∫ ω, X ω ^ k ∂P) / k !) (mgf X P t) := by
  have hint : ∀ k : ℕ, Integrable (fun ω => X ω ^ k) P := fun k => by
    refine Integrable.of_bound (C := M ^ k) (by fun_prop) ?_
    filter_upwards [hM] with ω hω
    rw [norm_pow, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hω k
  refine ⟨hint, ?_⟩
  have hb : ∀ k : ℕ, ∀ᵐ ω ∂P, ‖(t * X ω) ^ k / (k !)‖ ≤ (|t| * M) ^ k / (k !) := fun k => by
    filter_upwards [hM] with ω hω
    rw [norm_div, norm_pow, Real.norm_eq_abs, abs_mul, Real.norm_natCast]
    gcongr
  have hs : Summable fun k : ℕ => (|t| * M) ^ k / k ! :=
    (NormedSpace.expSeries_div_hasSum_exp (|t| * M)).summable
  have hl : ∀ ω, HasSum (fun k : ℕ => (t * X ω) ^ k / k !) (Real.exp (t * X ω)) := fun ω => by
    simpa [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (t * X ω)
  have h := hasSum_integral_of_dominated_convergence (μ := P)
    (F := fun (k : ℕ) ω => (t * X ω) ^ k / k !) (f := fun ω => Real.exp (t * X ω))
    (fun k _ => (|t| * M) ^ k / k !) (fun k => by fun_prop) hb
    (ae_of_all _ fun _ => hs) (by simp) (ae_of_all _ hl)
  have hm : mgf X P t = ∫ ω, Real.exp (t * X ω) ∂P := rfl
  rw [hm]
  convert h using 2 with k
  simp_rw [integral_div, mul_pow]
  rw [integral_const_mul]

/-- Grinstead–Snell Theorem 10.4 (PR-108). Two bounded random variables with the same moment
generating function on all of `ℝ` have the same distribution. -/
@[kb "grinsteadsnell2006" "Theorem 10.4, p. 405"]
theorem map_eq_of_mgf_eq_of_bounded {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure Ω') [IsProbabilityMeasure Q]
    (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : AEMeasurable X P) (hY : AEMeasurable Y Q) (M : ℝ)
    (hM : ∀ᵐ ω ∂P, |X ω| ≤ M) (h : mgf X P = mgf Y Q) :
    P.map X = Q.map Y := by
  have huniv : integrableExpSet X P = Set.univ :=
    Set.eq_univ_of_forall fun t => integrable_exp_mul_of_bounded P X hX M hM t
  have heq := eqOn_complexMGF_of_mgf h
  refine Measure.ext_of_complexMGF_eq hX hY (funext fun z => heq ?_)
  simp [huniv]

end UndergradKB.Probability
