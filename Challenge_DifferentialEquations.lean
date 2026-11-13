/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import UndergradKB.DifferentialEquations.LaplaceUniqueness
import UndergradKB.DifferentialEquations.NthOrderLinear
import UndergradKB.DifferentialEquations.BoundaryValue
import UndergradKB.DifferentialEquations.FrobeniusAnalytic
import UndergradKB.DifferentialEquations.FourierDirichlet
import UndergradKB.DifferentialEquations.Gibbs

/-!
# Headline statements of undergraduate-math-lean 0.2.1: differential equations (Lebl, *Notes on Diffy Qs*)

The main results of this topic that Mathlib and Tau Ceti lack, one theorem each, with every proof a deliberate
`sorry`: the uniqueness of the Laplace transform (Lerch's theorem), the general solution of a homogeneous linear
equation of order `n` (`n` independent solutions span all solutions), and the general solution of the
one-dimensional wave equation as a sum of two travelling waves. Version 0.2.1 adds three more: the method of
Frobenius with analytic coefficients (a series solution at a regular singular point), the pointwise convergence of the
Fourier series of a piecewise smooth function to the average of the one-sided limits, and the Gibbs phenomenon for the
square wave. To check what is claimed, read this file.
`Solution_DifferentialEquations.lean` proves the same statements from the library, and `lake comparator`
(configured by `comparator/DifferentialEquations.json`) checks that each proved statement is exactly the one here
and uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Each statement is the library's statement, copied. The statements were not yet reviewed by a human (see the README).

## Definitions used

Besides Mathlib, the statements use these definitions of the library (namespace `UndergradKB.DifferentialEquations`);
a reader checking a statement should check these too:

* `laplace f s = ∫ t in Ioi 0, exp (-(s * t)) * f t`, the Laplace transform (a Lebesgue integral; for the functions
  of the theorem it converges absolutely for all large `s`).
* `ExpOrder f M c`: `|f t| ≤ M * exp (c * t)` for every `t ≥ 0` (exponential order).
* `IsDerivChain I D` (for `D : Fin (n + 1) → ℝ → ℝ`): for every `k < n` and `t ∈ I`, `D k` has derivative
  `D (k + 1) t` at `t`; so `D 0, …, D n` are a function and its first `n` derivatives on `I`.
* `SolvesLinN a f I D`: `IsDerivChain I D` and `D n t + ∑ k, a k t * D k t = f t` for `t ∈ I`, i.e. `D 0` solves
  `y⁽ⁿ⁾ + aₙ₋₁(t) y⁽ⁿ⁻¹⁾ + ⋯ + a₀(t) y = f(t)` on `I`.
* `WaveEq a y`: `∂²y/∂t² = a² ∂²y/∂x²` at every point `(x, t)` of the plane (iterated one-variable derivatives).
* `fourierA f L n = (1/L) ∫ t in -L..L, f t * cos (n * π / L * t)` and `fourierB f L n` (the same with `sin`): the
  Fourier coefficients of `f`.
* `trigPoly L a b N t = a 0 / 2 + ∑ k ∈ Icc 1 N, (a k * cos (k * π / L * t) + b k * sin (k * π / L * t))`: the
  partial sum of the Fourier series with coefficients `a`, `b`.
* `PiecewiseContinuousOn f a b`: there is a finite set `S` such that `f` is continuous within `[a, b]` at every point
  of `[a, b]` outside `S`, and at each point of `S` the one-sided limits (on the sides lying in `[a, b]`) exist.
* `PiecewiseSmoothOn f a b`: `f` is piecewise continuous on `[a, b]`, is differentiable on `(a, b)` outside a finite
  set, and its derivative `deriv f` is piecewise continuous on `[a, b]`.
* `squareWave t = if t ≤ 0 then -1 else 1`: the square wave (`-1` on `[-π, 0]`, `1` on `(0, π]`); only its values on
  `[-π, π]` enter the Fourier coefficients `fourierA squareWave π`, `fourierB squareWave π`.
* `sinc` is Mathlib's `Real.sinc` (`sin t / t`, with value `1` at `0`).
-/

namespace UndergradKB.Headlines.DifferentialEquations

open Real Set Filter Topology MeasureTheory intervalIntegral UndergradKB.DifferentialEquations

/-- **Uniqueness of the Laplace transform (Lerch's theorem)** (Lebl Theorem 6.1.3): two continuous functions of
exponential order on `[0, ∞)` whose Laplace transforms agree for all large `s` are equal on `[0, ∞)`. Related:
Mathlib has no Laplace transform of functions; Tau Ceti proves that finite positive measures on the half line are
determined by their Laplace transforms, which does not give this statement for functions of either sign. -/
theorem laplace_unique {f g : ℝ → ℝ} {M N c d : ℝ} (hfc : ContinuousOn f (Ici 0))
    (hgc : ContinuousOn g (Ici 0)) (hf : ExpOrder f M c) (hg : ExpOrder g N d)
    (heq : ∀ᶠ s in atTop, laplace f s = laplace g s) : ∀ t, 0 ≤ t → f t = g t := by
  sorry

/-- **The general solution of a homogeneous linear equation of order `n`** (Lebl Theorem 2.3.3; Theorem 2.1.3 for
order 2): on an interval where the coefficients are continuous, if `n` solutions are linearly independent, every
solution is a linear combination of them (and so are its first `n - 1` derivatives, with the same constants).
Related: Mathlib and Tau Ceti have existence and uniqueness for first-order systems; Tau Ceti has the Wronskian of
`y'' = q y`; neither states that the solution space of an equation of order `n` is spanned by `n` independent
solutions. -/
theorem linN_general_solution {n : ℕ} {a : Fin n → ℝ → ℝ} {I : Set ℝ} (hI : I.OrdConnected)
    (hne : I.Nonempty) (ha : ∀ k, ContinuousOn (a k) I) {D : Fin n → Fin (n + 1) → ℝ → ℝ}
    (hD : ∀ i, SolvesLinN a 0 I (D i)) (hli : LinearIndependent ℝ (fun i (t : I) => D i 0 t))
    {E : Fin (n + 1) → ℝ → ℝ} (hE : SolvesLinN a 0 I E) :
    ∃ C : Fin n → ℝ, ∀ k : Fin n, ∀ t ∈ I, E k.castSucc t = ∑ i, C i * D i k.castSucc t := by
  sorry

/-- **The general solution of the wave equation** (Lebl § 4.8, characteristic coordinates): every twice
continuously differentiable solution of `y_tt = a² y_xx` on the plane (`a ≠ 0`) is `F(x + at) + G(x - at)` for two
twice continuously differentiable functions `F` and `G` of one variable. Related: neither Mathlib nor Tau Ceti has
the wave equation. -/
theorem wave_general_solution {a : ℝ} (ha : a ≠ 0) {y : ℝ → ℝ → ℝ}
    (hy : ContDiff ℝ 2 (fun p : ℝ × ℝ => y p.1 p.2)) (hwave : WaveEq a y) :
    ∃ F G : ℝ → ℝ, ContDiff ℝ 2 F ∧ ContDiff ℝ 2 G ∧
      ∀ x t, y x t = F (x + a * t) + G (x - a * t) := by
  sorry

/-- **The method of Frobenius** (Lebl Theorem 7.3.1): for `x² y'' + x p(x) y' + q(x) y = 0` with `p = ∑ Pₖ xᵏ` and
`q = ∑ Qₖ xᵏ` convergent for `|x| < ρ`, and `r` a root of the indicial equation `r (r - 1) + P₀ r + Q₀ = 0` such that
the indicial polynomial does not vanish at `r + k` for any integer `k ≥ 1` (e.g. `r` the larger root), there is a
series `∑ aₖ xᵏ` with `a₀ = 1`, convergent for `|x| < ρ`, with the coefficients given by the usual recurrence, such
that `x ^ r ∑ aₖ xᵏ` is a nonzero solution on `(0, ρ)`. Not claimed: the second solution (with logarithms) when the
roots differ by an integer, and the complex case. Related: neither Mathlib nor Tau Ceti has the indicial equation or
a Frobenius series solution; their nearest ODE material is the Lyapunov-Perron stable manifold theory (Tau Ceti) and
Bessel functions without their differential equation (Mathlib). -/
theorem frobenius_analytic (P Q : ℕ → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hP : ∀ x : ℝ, |x| < ρ → Summable fun k => P k * x ^ k)
    (hQ : ∀ x : ℝ, |x| < ρ → Summable fun k => Q k * x ^ k) {r : ℝ}
    (hr : r * (r - 1) + P 0 * r + Q 0 = 0)
    (hF : ∀ k : ℕ, 1 ≤ k → (r + k) * (r + k - 1) + P 0 * (r + k) + Q 0 ≠ 0) :
    ∃ a : ℕ → ℝ, a 0 = 1 ∧ (∀ x : ℝ, |x| < ρ → Summable fun k => a k * x ^ k) ∧
      (∀ k : ℕ, 1 ≤ k → a k * ((r + k) * (r + k - 1) + P 0 * (r + k) + Q 0) =
        -∑ j ∈ Finset.range k, a j * ((r + (j : ℝ)) * P (k - j) + Q (k - j))) ∧
      (∀ x : ℝ, 0 < x → x < ρ →
        x ^ 2 * deriv (deriv (fun t : ℝ => t ^ r * ∑' k, a k * t ^ k)) x +
          x * (∑' k, P k * x ^ k) * deriv (fun t : ℝ => t ^ r * ∑' k, a k * t ^ k) x +
          (∑' k, Q k * x ^ k) * (x ^ r * ∑' k, a k * x ^ k) = 0) ∧
      ∃ x : ℝ, 0 < x ∧ x < ρ ∧ x ^ r * ∑' k, a k * x ^ k ≠ 0 := by
  sorry

/-- **Pointwise convergence of the Fourier series** (Lebl Theorem 4.3.1): if `f` is `2L`-periodic and piecewise
smooth on `[-L, L]`, then at every point `t` the one-sided limits `f(t+)` and `f(t-)` exist and the partial sums
`a₀/2 + ∑_{k ≤ N} (aₖ cos(kπt/L) + bₖ sin(kπt/L))` of the Fourier series tend to `(f(t+) + f(t-))/2`. Here `f` is
real valued and the series is taken as the limit of the symmetric partial sums. Related: Mathlib has the `L²`
convergence of Fourier series and pointwise convergence only when the Fourier coefficients are summable, and no
Dirichlet kernel or Dini test; Tau Ceti has pointwise convergence for smooth functions on tori, which needs decay of
the coefficients and gives neither piecewise smooth functions nor the midpoint value at a jump. -/
theorem fourier_series_piecewise_smooth {f : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hper : Function.Periodic f (2 * L)) (hpw : PiecewiseSmoothOn f (-L) L) (t : ℝ) :
    ∃ l₁ l₂, Tendsto f (𝓝[>] t) (𝓝 l₁) ∧ Tendsto f (𝓝[<] t) (𝓝 l₂) ∧
      Tendsto (fun N : ℕ => trigPoly L (fourierA f L) (fourierB f L) N t) atTop (𝓝 ((l₁ + l₂) / 2)) := by
  sorry

/-- **The Gibbs phenomenon** (Lebl § 4.2): for the square wave, the partial sums `S_{2M}` of its Fourier series,
evaluated at `π / (2M)`, tend to `(2/π) ∫₀^π sin t / t dt` (about `1.179`), this number exceeds `1.17`, and so for all
large `M` the partial sum at `π / (2M)` exceeds `1.17` although the square wave equals `1` there: the overshoot, about
9% of the jump, does not shrink as more terms are taken. Related: Mathlib has nothing on this, and the Gibbs results in
Tau Ceti concern Gibbs states and measures, not Fourier series. -/
theorem gibbs_phenomenon :
    Tendsto (fun M : ℕ =>
        trigPoly π (fourierA squareWave π) (fourierB squareWave π) (2 * M) (π / (2 * M)))
      atTop (𝓝 ((2 / π) * ∫ t in (0:ℝ)..π, sinc t)) ∧
    1.17 < (2 / π) * ∫ t in (0:ℝ)..π, sinc t ∧
    ∀ᶠ M : ℕ in atTop,
      1.17 < trigPoly π (fourierA squareWave π) (fourierB squareWave π) (2 * M) (π / (2 * M)) ∧
      squareWave (π / (2 * M)) = 1 := by
  sorry

end UndergradKB.Headlines.DifferentialEquations
