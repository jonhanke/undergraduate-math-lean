import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import UndergradKB.Common.Attr
import UndergradKB.DifferentialEquations.Frobenius
import UndergradKB.DifferentialEquations.Oscillations
import UndergradKB.DifferentialEquations.SecondOrderLinear

/-! # Logarithmic second solutions in the method of Frobenius (Lebl, *Notes on Diffy Qs*, §7.3)

* Example 7.3.2: `4x²y'' - 4x²y' + (1-2x)y = 0` has the double indicial root `1/2`, the first solution
  `x^{1/2} e^x`, and a second solution `y₂ = x^{1/2} e^x · W(x)` with `W(x) = ∫₁ˣ e^{-s}/s ds`
  (`W(x) = ln x + (power series)`, the book's `∑ b_k x^{k+1/2} + (ln x) y₁`).  Both solutions are
  linearly independent on `(0, ∞)`, so every solution is a combination.
* Double root case: for the Euler equation `x²y'' + a x y' + b y = 0` with a double indicial root
  `r = (1-a)/2` (`(a-1)² = 4b`), `x^r` and `x^r ln x` are independent solutions on `(0, ∞)`.
-/

namespace UndergradKB.DifferentialEquations

open Set Polynomial Filter Topology

/-! ### Generic lemmas -/

/-- `SolvesLin2` only depends on the coefficients on the set `I`. -/
lemma SolvesLin2.congr_coeff {p q p' q' : ℝ → ℝ} {I : Set ℝ} {y : ℝ → ℝ}
    (hp : ∀ t ∈ I, p t = p' t) (hq : ∀ t ∈ I, q t = q' t) (h : SolvesLin2 p q 0 I y) :
    SolvesLin2 p' q' 0 I y := by
  intro t ht
  obtain ⟨a, b, c⟩ := h t ht
  refine ⟨a, b, ?_⟩
  rw [← hp t ht, ← hq t ht]
  exact c

/-- If `u` has no zero on an open set `I` and `v` has a nowhere vanishing derivative on `I`, then `u` and `v u`
are linearly independent on `I`. -/
lemma linIndep_reduction {I : Set ℝ} (hI : IsOpen I) (hne : I.Nonempty) {u v d : ℝ → ℝ}
    (hu : ∀ t ∈ I, u t ≠ 0) (hv : ∀ t ∈ I, HasDerivAt v (d t) t) (hd : ∀ t ∈ I, d t ≠ 0) :
    LinearIndependent ℝ ![fun t : I => u t, fun t : I => v t * u t] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h : ∀ t ∈ I, c 0 + c 1 * v t = 0 := by
    intro t ht
    have := congrFun hc ⟨t, ht⟩
    simp only [Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Pi.zero_apply] at this
    have h2 : (c 0 + c 1 * v t) * u t = 0 := by linear_combination this
    exact (mul_eq_zero.mp h2).resolve_right (hu t ht)
  obtain ⟨t0, ht0⟩ := hne
  have hc1 : c 1 = 0 := by
    have hder : HasDerivAt (fun t => c 0 + c 1 * v t) (c 1 * d t0) t0 :=
      ((hv t0 ht0).const_mul (c 1)).const_add (c 0)
    have hz : HasDerivAt (fun t => c 0 + c 1 * v t) 0 t0 :=
      (hasDerivAt_const t0 (0 : ℝ)).congr_of_eventuallyEq
        (Filter.eventually_of_mem (hI.mem_nhds ht0) fun t ht => h t ht)
    have := hder.unique hz
    exact (mul_eq_zero.mp this).resolve_right (hd t0 ht0)
  have hc0 : c 0 = 0 := by
    have := h t0 ht0
    rw [hc1] at this
    linarith
  intro i
  fin_cases i
  · exact hc0
  · exact hc1

/-- The function `W(x) = ∫₁ˣ e^{-s}/s ds` is differentiable on `x > 0` with derivative `e^{-x}/x`. -/
noncomputable def expIntW (x : ℝ) : ℝ := ∫ s in (1 : ℝ)..x, Real.exp (-s) / s

lemma hasDerivAt_expIntW {x : ℝ} (hx : 0 < x) : HasDerivAt expIntW (Real.exp (-x) / x) x := by
  have hc : ContinuousOn (fun s : ℝ => Real.exp (-s) / s) (Ioi 0) :=
    (Real.continuous_exp.comp_continuousOn continuousOn_neg).div continuousOn_id
      (fun s hs => ne_of_gt hs)
  have hint : IntervalIntegrable (fun s : ℝ => Real.exp (-s) / s) MeasureTheory.volume 1 x := by
    refine (hc.mono ?_).intervalIntegrable
    intro s hs
    rcases le_total 1 x with h | h
    · rw [uIcc_of_le h] at hs; exact lt_of_lt_of_le one_pos hs.1
    · rw [uIcc_of_ge h] at hs; exact lt_of_lt_of_le hx hs.1
  exact intervalIntegral.integral_hasDerivAt_right hint
    (hc.stronglyMeasurableAtFilter isOpen_Ioi x hx) (hc.continuousAt (Ioi_mem_nhds hx))

/-! ### Example 7.3.2: the logarithmic second solution -/

/-- **Example 7.3.2, second solution** (DE-205): for `x > 0` the function
`y₂(x) = x^{1/2} e^x ∫₁ˣ e^{-s}/s ds` solves `4x² y'' - 4x² y' + (1-2x) y = 0`.  (The integral is
`ln x` plus a power series, which is the book's `∑ b_k x^{k+1/2} + (ln x) x^{1/2} e^x`; this closed form of the
power-series part is not derived here.)  Obtained by reduction of order from the first solution. -/
@[kb "lebldiffyqs2026" "Example 7.3.2, p. 343"]
theorem frobenius_example_second_solution :
    SolvesPoly (C 4 * X ^ 2) (-(C 4 * X ^ 2)) (1 - C 2 * X) (Ioi 0)
      (fun x => expIntW x * (Real.sqrt x * Real.exp x)) := by
  have hP : ∀ t ∈ Ioi (0 : ℝ), (C 4 * X ^ 2 : ℝ[X]).eval t ≠ 0 := by
    intro t ht
    have : (0 : ℝ) < t := ht
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    positivity
  rw [solvesPoly_iff hP]
  have h1 := (solvesPoly_iff hP _).mp frobenius_example_solves
  refine reduction_of_order (P := fun t => -t) isOpen_Ioi h1 (fun t ht => ?_) (fun t ht => ?_)
    (fun t ht => ?_)
  · have : (0 : ℝ) < t := ht
    exact (Real.sqrt_pos.2 this).ne' |> fun h => mul_ne_zero h (Real.exp_pos t).ne'
  · have : (0 : ℝ) < t := ht
    have := (hasDerivAt_id t).neg
    refine this.congr_deriv ?_
    simp only [eval_mul, eval_C, eval_pow, eval_X, eval_neg]
    field_simp
  · have ht0 : (0 : ℝ) < t := ht
    refine (hasDerivAt_expIntW ht0).congr_deriv ?_
    have hs : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0.le
    have he : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
    simp only [neg_neg, mul_pow, hs]
    have e2 : Real.exp t ^ 2 = Real.exp t * Real.exp t := sq _
    rw [Real.exp_neg, e2]
    have := (Real.exp_pos t).ne'
    field_simp

/-- **Example 7.3.2, independence** (DE-205): `x^{1/2} e^x` and `x^{1/2} e^x ∫₁ˣ e^{-s}/s ds` are linearly
independent on `(0, ∞)`. -/
@[kb "lebldiffyqs2026" "Example 7.3.2, p. 343"]
theorem frobenius_example_independent :
    LinearIndependent ℝ ![fun t : Ioi (0 : ℝ) => Real.sqrt t * Real.exp t,
      fun t : Ioi (0 : ℝ) => expIntW t * (Real.sqrt t * Real.exp t)] :=
  linIndep_reduction (u := fun t => Real.sqrt t * Real.exp t) (v := expIntW)
    (d := fun t => Real.exp (-t) / t) isOpen_Ioi ⟨1, mem_Ioi.mpr one_pos⟩
    (fun t ht => mul_ne_zero (Real.sqrt_pos.2 ht).ne' (Real.exp_pos t).ne')
    (fun t ht => hasDerivAt_expIntW ht)
    (fun t ht => div_ne_zero (Real.exp_pos _).ne' (ne_of_gt ht))

/-- **Example 7.3.2, general solution** (DE-205): every solution on `(0, ∞)` of
`4x²y'' - 4x²y' + (1-2x)y = 0` (written as `y'' - y' + (1-2x)/(4x²) y = 0`) is `A x^{1/2} e^x + B y₂`. -/
@[kb "lebldiffyqs2026" "Example 7.3.2, p. 343"]
theorem frobenius_example_general_solution {y : ℝ → ℝ}
    (hy : SolvesLin2 (fun _ => -1) (fun t => (1 - 2 * t) / (4 * t ^ 2)) 0 (Ioi 0) y) :
    ∃ A B : ℝ, ∀ t ∈ Ioi (0 : ℝ),
      y t = A * (Real.sqrt t * Real.exp t) + B * (expIntW t * (Real.sqrt t * Real.exp t)) := by
  have hP : ∀ t ∈ Ioi (0 : ℝ), (C 4 * X ^ 2 : ℝ[X]).eval t ≠ 0 := by
    intro t ht
    have : (0 : ℝ) < t := ht
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    positivity
  have hcoef : ∀ t ∈ Ioi (0 : ℝ),
      (-(C 4 * X ^ 2 : ℝ[X])).eval t / (C 4 * X ^ 2 : ℝ[X]).eval t = -1 := by
    intro t ht
    have := hP t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    simp only [eval_mul, eval_C, eval_pow, eval_X, eval_neg] at this ⊢
    field_simp
  have hcoef2 : ∀ t ∈ Ioi (0 : ℝ),
      (1 - C 2 * X : ℝ[X]).eval t / (C 4 * X ^ 2 : ℝ[X]).eval t = (1 - 2 * t) / (4 * t ^ 2) := by
    intro t _
    simp
  have conv : ∀ z, SolvesPoly (C 4 * X ^ 2) (-(C 4 * X ^ 2)) (1 - C 2 * X) (Ioi 0) z →
      SolvesLin2 (fun _ => -1) (fun t => (1 - 2 * t) / (4 * t ^ 2)) 0 (Ioi 0) z := fun z hz =>
    ((solvesPoly_iff hP z).mp hz).congr_coeff hcoef hcoef2
  have hc1 : ContinuousOn (fun _ : ℝ => (-1 : ℝ)) (Ioi 0) := continuousOn_const
  have hc2 : ContinuousOn (fun t : ℝ => (1 - 2 * t) / (4 * t ^ 2)) (Ioi 0) :=
    (by fun_prop : Continuous fun t : ℝ => 1 - 2 * t).continuousOn.div
      (by fun_prop : Continuous fun t : ℝ => 4 * t ^ 2).continuousOn
      (fun t ht => by have : (0 : ℝ) < t := ht; positivity)
  obtain ⟨A, B, h⟩ := lin2_general_solution (ordConnected_Ioi) hc1 hc2
    (conv _ frobenius_example_solves) (conv _ frobenius_example_second_solution)
    frobenius_example_independent ⟨1, by simp⟩ hy
  exact ⟨A, B, h⟩

/-! ### Double root: the Euler equation -/

/-- `t ↦ t^r` solves `x² y'' + a x y' + b y = 0` (as `y'' + (a/x) y' + (b/x²) y = 0`) on `x > 0` when
`r = (1-a)/2` and `(a-1)² = 4b`. -/
lemma euler_rpow_solves (a b : ℝ) (hb : (a - 1) ^ 2 = 4 * b) :
    SolvesLin2 (fun t => a / t) (fun t => b / t ^ 2) 0 (Ioi 0) (fun t => t ^ ((1 - a) / 2)) := by
  refine solvesLin2_of_hasDerivAt isOpen_Ioi
    (y₁ := fun t => ((1 - a) / 2) * t ^ ((1 - a) / 2) / t)
    (y₂ := fun t => ((1 - a) / 2) * (((1 - a) / 2) - 1) * t ^ ((1 - a) / 2) / t ^ 2)
    (fun t ht => hasDerivAt_rpow_div _ t ht) (fun t ht => hasDerivAt_rpow_div2 _ t ht) ?_
  intro t ht
  have ht0 : (0 : ℝ) < t := ht
  have hb' : b = (a - 1) ^ 2 / 4 := by linarith
  subst hb'
  simp only [Pi.zero_apply]
  field_simp
  ring

/-- **Double indicial root, Euler case** (DE-208, case (iv) of the list): if the indicial equation
`r(r-1) + a r + b = 0` of `x² y'' + a x y' + b y = 0` has the double root `r = (1-a)/2` (i.e. `(a-1)² = 4b`),
then `x^r` and `x^r ln x` are solutions on `(0, ∞)` (the second has the form `(ln x) y₁`, with the power
series part `0`), they are linearly independent, and every solution on `(0, ∞)` is `A x^r + B x^r ln x`.
Only the Euler equation (`p`, `q` constant) is covered here; the general Frobenius double-root equation is not. -/
@[kb "lebldiffyqs2026" "§7.3.2 Frobenius cases (i)-(vi), p. 346"]
theorem euler_double_root (a b : ℝ) (hb : (a - 1) ^ 2 = 4 * b) :
    SolvesLin2 (fun t => a / t) (fun t => b / t ^ 2) 0 (Ioi 0) (fun t => t ^ ((1 - a) / 2)) ∧
    SolvesLin2 (fun t => a / t) (fun t => b / t ^ 2) 0 (Ioi 0)
      (fun t => t ^ ((1 - a) / 2) * Real.log t) ∧
    LinearIndependent ℝ ![fun t : Ioi (0 : ℝ) => (t : ℝ) ^ ((1 - a) / 2),
      fun t : Ioi (0 : ℝ) => (t : ℝ) ^ ((1 - a) / 2) * Real.log t] ∧
    ∀ y : ℝ → ℝ, SolvesLin2 (fun t => a / t) (fun t => b / t ^ 2) 0 (Ioi 0) y →
      ∃ A B : ℝ, ∀ t ∈ Ioi (0 : ℝ), y t = A * t ^ ((1 - a) / 2) + B * (t ^ ((1 - a) / 2) * Real.log t) := by
  have hu := euler_rpow_solves a b hb
  have hne : ∀ t ∈ Ioi (0 : ℝ), t ^ ((1 - a) / 2) ≠ 0 := fun t ht => (Real.rpow_pos_of_pos ht _).ne'
  have hPd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t => a * Real.log t) (a / t) t := fun t ht =>
    ((Real.hasDerivAt_log (ne_of_gt ht)).const_mul a).congr_deriv (by ring)
  have hvd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt Real.log (1 / t) t := fun t ht => by
    simpa using Real.hasDerivAt_log (ne_of_gt ht)
  have hexp : ∀ t ∈ Ioi (0 : ℝ),
      Real.exp (-(a * Real.log t)) / (t ^ ((1 - a) / 2)) ^ 2 = 1 / t := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    rw [Real.rpow_def_of_pos ht0, sq, ← Real.exp_add, ← Real.exp_sub]
    have : -(a * Real.log t) - (Real.log t * ((1 - a) / 2) + Real.log t * ((1 - a) / 2)) =
        -Real.log t := by ring
    rw [this, Real.exp_neg, Real.exp_log ht0, one_div]
  have hmul : ∀ t, Real.log t * t ^ ((1 - a) / 2) = t ^ ((1 - a) / 2) * Real.log t := fun t => mul_comm _ _
  have hsol : SolvesLin2 (fun t => a / t) (fun t => b / t ^ 2) 0 (Ioi 0)
      (fun t => t ^ ((1 - a) / 2) * Real.log t) := by
    have := reduction_of_order (P := fun t => a * Real.log t) (v := Real.log) isOpen_Ioi hu hne hPd
      (fun t ht => (hvd t ht).congr_deriv (hexp t ht).symm)
    simpa only [hmul] using this
  have hli : LinearIndependent ℝ ![fun t : Ioi (0 : ℝ) => (t : ℝ) ^ ((1 - a) / 2),
      fun t : Ioi (0 : ℝ) => (t : ℝ) ^ ((1 - a) / 2) * Real.log t] := by
    have := linIndep_reduction isOpen_Ioi (I := Ioi 0) ⟨1, by simp⟩ hne hvd
      (fun t ht => one_div_ne_zero (ne_of_gt ht))
    simpa only [hmul] using this
  refine ⟨hu, hsol, hli, fun y hy => ?_⟩
  have hc1 : ContinuousOn (fun t : ℝ => a / t) (Ioi 0) :=
    continuousOn_const.div continuousOn_id (fun t ht => ne_of_gt ht)
  have hc2 : ContinuousOn (fun t : ℝ => b / t ^ 2) (Ioi 0) :=
    continuousOn_const.div (continuousOn_id.pow 2) (fun t ht => pow_ne_zero 2 (ne_of_gt ht))
  exact lin2_general_solution ordConnected_Ioi hc1 hc2 hu hsol hli ⟨1, by simp⟩ hy

end UndergradKB.DifferentialEquations
