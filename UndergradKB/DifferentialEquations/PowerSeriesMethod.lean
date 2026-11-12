import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import UndergradKB.Common.Attr

/-! # Power series and Frobenius methods (Lebl, *Notes on Diffy Qs*, Chapter 7)

The recurrences obtained by comparing coefficients, at the level of formal power series
(`PowerSeries ℝ` with its formal derivative) and of polynomials, for Airy's equation, `y'' + y = 0`, and
Hermite's equation; the Frobenius computation for Bessel's equation on `x^s` (indicial polynomial `r² - p²`);
and the rescaling of Bessel's equation of order 0. Convergence of the series is not treated. -/

namespace UndergradKB.DifferentialEquations

section FormalSeries

open PowerSeries

/-! ## Airy's equation, `y'' = x y` -/

/-- DE-203 (Example 7.2.2, p. 336). A formal power series `y = ∑ a_k x^k` satisfies Airy's equation
`y'' = x y` iff `a₂ = 0` and `a_{k+2} = a_{k-1} / ((k+2)(k+1))` for `k ≥ 1`, written here as
`a_{k+3} = a_k / ((k+3)(k+2))` for `k ≥ 0`; `a₀, a₁` are free. -/
@[kb "lebldiffyqs2026" "Example 7.2.2, p. 336"]
theorem airy_recurrence (y : PowerSeries ℝ) :
    d⁄dX (d⁄dX y) = X * y ↔
      coeff 2 y = 0 ∧ ∀ k : ℕ, coeff (k + 3) y = coeff k y / (((k : ℝ) + 3) * ((k : ℝ) + 2)) := by
  have hc : ∀ n : ℕ, coeff n (d⁄dX (d⁄dX y)) = coeff (n + 2) y * (((n : ℝ) + 2) * ((n : ℝ) + 1)) := by
    intro n
    rw [coeff_derivative, coeff_derivative]
    push_cast
    ring
  constructor
  · intro h
    refine ⟨?_, fun k => ?_⟩
    · have := hc 0
      rw [h, coeff_zero_X_mul] at this
      simpa using this.symm
    · have := hc (k + 1)
      rw [h, coeff_succ_X_mul] at this
      rw [eq_div_iff (by positivity)]
      push_cast at this
      linarith
  · rintro ⟨h2, hk⟩
    ext n
    rw [hc]
    rcases n with _ | k
    · rw [coeff_zero_X_mul]; simp [h2]
    · rw [coeff_succ_X_mul, hk k]
      push_cast
      field_simp
      ring

/-! ## `y'' + y = 0` -/

/-- DE-202 (Example 7.2.1, p. 335; §7.2, p. 336), for the equation `y'' + y = 0`: comparing coefficients, a formal
power series is a solution iff `a_{k+2} (k+2)(k+1) = -a_k` for all `k`, with `a₀, a₁` free. -/
@[kb "lebldiffyqs2026" "Example 7.2.1, p. 335"]
theorem second_order_plus_recurrence (y : PowerSeries ℝ) :
    d⁄dX (d⁄dX y) + y = 0 ↔
      ∀ k : ℕ, coeff (k + 2) y * (((k : ℝ) + 2) * ((k : ℝ) + 1)) = - coeff k y := by
  have hc : ∀ n : ℕ, coeff n (d⁄dX (d⁄dX y) + y) =
      coeff (n + 2) y * (((n : ℝ) + 2) * ((n : ℝ) + 1)) + coeff n y := by
    intro n
    rw [map_add, coeff_derivative, coeff_derivative]
    push_cast
    ring
  constructor
  · intro h k
    have := hc k
    rw [h] at this
    simp only [map_zero] at this
    linarith
  · intro h
    ext n
    rw [hc, h n]
    simp

/-- The coefficients of the cosine series: `(-1)^(k/2) / k!` for even `k`, `0` for odd `k`. -/
noncomputable def cosCoeff (k : ℕ) : ℝ := if Even k then (-1) ^ (k / 2) / (k.factorial : ℝ) else 0

/-- DE-202: the coefficients of the series of `cos` satisfy the recurrence of `y'' + y = 0`, and
`∑ cosCoeff (2m) x^(2m)` is `cos x`; so `cos` is the solution with `a₀ = 1, a₁ = 0`. -/
@[kb "lebldiffyqs2026" "Example 7.2.1, p. 335"]
theorem cosCoeff_solves (x : ℝ) :
    (d⁄dX (d⁄dX (PowerSeries.mk cosCoeff)) + PowerSeries.mk cosCoeff = 0) ∧
    HasSum (fun m : ℕ => cosCoeff (2 * m) * x ^ (2 * m)) (Real.cos x) := by
  refine ⟨(second_order_plus_recurrence _).2 fun k => ?_, ?_⟩
  · simp only [coeff_mk]
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
    · have e1 : Even (2 * m + 2) := ⟨m + 1, by ring⟩
      have e2 : Even (2 * m) := ⟨m, by ring⟩
      have h1 : (2 * m + 2) / 2 = m + 1 := by omega
      have h2 : 2 * m / 2 = m := by omega
      simp only [cosCoeff, e1, e2, ↓reduceIte, h1, h2]
      rw [show 2 * m + 2 = (2 * m + 1) + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      rw [pow_succ]
      have : ((2 * m).factorial : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    · have e1 : ¬ Even (2 * m + 1 + 2) := by
        rw [Nat.not_even_iff_odd]; exact ⟨m + 1, by ring⟩
      have e2 : ¬ Even (2 * m + 1) := by
        rw [Nat.not_even_iff_odd]; exact ⟨m, by ring⟩
      simp [cosCoeff, e1, e2]
  · have := Real.hasSum_cos x
    convert this using 2 with m
    have e : Even (2 * m) := ⟨m, by ring⟩
    have h2 : 2 * m / 2 = m := by omega
    simp only [cosCoeff, e, ↓reduceIte, h2]
    ring

end FormalSeries

section Hermite

open Polynomial

/-! ## Hermite's equation -/

/-- Derivative of the probabilists' Hermite polynomials: `He_{n+1}' = (n+1) He_n`. -/
lemma derivative_hermite_succ (n : ℕ) :
    derivative (hermite (n + 1)) = ((n : ℤ[X]) + 1) * hermite n := by
  induction n with
  | zero => simp [hermite_zero]
  | succ n ih =>
    have e := hermite_succ n
    rw [hermite_succ (n + 1), derivative_sub, derivative_mul, derivative_X, ih, one_mul]
    simp only [derivative_mul, derivative_add, derivative_natCast, derivative_one, zero_add,
      zero_mul]
    push_cast
    linear_combination (-((n : ℤ[X]) + 1)) * e

/-- The probabilists' Hermite polynomials solve `He'' - x He' + n He = 0`. -/
lemma hermite_ode (n : ℕ) :
    derivative (derivative (hermite n)) - X * derivative (hermite n) + (n : ℤ[X]) * hermite n = 0 := by
  cases n with
  | zero => simp [hermite_zero]
  | succ n =>
    have e := hermite_succ n
    rw [derivative_hermite_succ]
    simp only [derivative_mul, derivative_add, derivative_natCast, derivative_one, zero_add, zero_mul]
    push_cast
    linear_combination ((n : ℤ[X]) + 1) * e

/-- The coefficient of `x^k` in `P'' - 2xP' + 2nP` is `(k+2)(k+1) a_{k+2} - 2(k-n) a_k`. -/
lemma coeff_hermiteOp (P : ℝ[X]) (n k : ℕ) :
    coeff (derivative (derivative P) - C 2 * (X * derivative P) + C (2 * (n : ℝ)) * P) k =
      coeff P (k + 2) * (((k : ℝ) + 2) * ((k : ℝ) + 1)) - 2 * ((k : ℝ) - n) * coeff P k := by
  have hX : coeff (X * derivative P) k = (k : ℝ) * coeff P k := by
    rcases k with _ | k
    · simp
    · rw [coeff_X_mul, coeff_derivative]; push_cast; ring
  rw [coeff_add, coeff_sub, coeff_C_mul, coeff_C_mul, hX, coeff_derivative, coeff_derivative]
  push_cast
  ring

/-- DE-204 (Example 7.2.3, p. 339), the recurrence. A polynomial solves Hermite's equation
`y'' - 2x y' + 2n y = 0` iff its coefficients satisfy `a_{k+2} (k+2)(k+1) = 2 (k - n) a_k`. -/
@[kb "lebldiffyqs2026" "Example 7.2.3, p. 339"]
theorem hermite_recurrence (P : ℝ[X]) (n : ℕ) :
    derivative (derivative P) - C 2 * (X * derivative P) + C (2 * (n : ℝ)) * P = 0 ↔
      ∀ k : ℕ, coeff P (k + 2) * (((k : ℝ) + 2) * ((k : ℝ) + 1)) = 2 * ((k : ℝ) - n) * coeff P k := by
  constructor
  · intro h k
    have := coeff_hermiteOp P n k
    rw [h, coeff_zero] at this
    linarith
  · intro h
    ext k
    rw [coeff_hermiteOp, h k, coeff_zero]
    ring

/-- DE-204 (Example 7.2.3, p. 339), polynomial solutions. For every `n : ℕ` the polynomial
`P(x) = He_n(√2 x)` (a scalar multiple of the physicists' Hermite polynomial `H_n`) has degree `n` and
solves `y'' - 2x y' + 2n y = 0`; by `hermite_recurrence` its coefficients obey
`a_{k+2} = 2 (k-n) a_k / ((k+2)(k+1))`, which terminates at `k = n`. -/
@[kb "lebldiffyqs2026" "Example 7.2.3, p. 339"]
theorem hermite_polynomial_solution (n : ℕ) :
    ∃ P : ℝ[X], P.natDegree = n ∧
      derivative (derivative P) - C 2 * (X * derivative P) + C (2 * (n : ℝ)) * P = 0 := by
  set H : ℝ[X] := (hermite n).map (Int.castRingHom ℝ) with hH
  set s : ℝ[X] := C (Real.sqrt 2) with hsdef
  have hs : s * s = C 2 := by
    rw [hsdef, ← C_mul, Real.mul_self_sqrt (by norm_num)]
  have hdq : derivative (s * X) = s := by simp [hsdef]
  have hode : derivative (derivative H) - X * derivative H + (n : ℝ[X]) * H = 0 := by
    have := congrArg (Polynomial.map (Int.castRingHom ℝ)) (hermite_ode n)
    simpa [hH, Polynomial.derivative_map, Polynomial.map_sub, Polynomial.map_mul] using this
  refine ⟨H.comp (s * X), ?_, ?_⟩
  · have h0 : Real.sqrt 2 ≠ 0 := by positivity
    rw [natDegree_comp, hH, natDegree_map_eq_of_injective (RingHom.injective_int _),
      natDegree_hermite, hsdef, natDegree_C_mul_X _ h0]
    simp
  · have h := congrArg (fun r : ℝ[X] => r.comp (s * X)) hode
    simp only [sub_comp, add_comp, mul_comp, X_comp, natCast_comp, zero_comp] at h
    have hds : derivative s = 0 := by simp [hsdef]
    rw [derivative_comp, hdq, derivative_mul, hds, zero_mul, zero_add, derivative_comp, hdq]
    have e1 : C (2 * (n : ℝ)) = C 2 * (n : ℝ[X]) := by simp [C_mul]
    rw [e1]
    linear_combination (C 2 : ℝ[X]) * h +
      (derivative (derivative H)).comp (s * X) * hs

end Hermite

/-! ## Bessel's equation -/

/-- DE-216 (Example 7.3.4, p. 349). If `y` solves Bessel's equation of order 0, `t² y'' + t y' + t² y = 0`
(with `y' = y₁`, `y'' = y₂`), then `x ↦ y(λ x)` solves `x² z'' + x z' + λ² x² z = 0`; its derivatives are
`λ y₁(λ x)` and `λ² y₂(λ x)`. -/
@[kb "lebldiffyqs2026" "Example 7.3.4, p. 349"]
theorem bessel_zero_rescale {y y₁ y₂ : ℝ → ℝ} (hy : ∀ t, HasDerivAt y (y₁ t) t)
    (hy₁ : ∀ t, HasDerivAt y₁ (y₂ t) t) (hb : ∀ t, t ^ 2 * y₂ t + t * y₁ t + t ^ 2 * y t = 0)
    (l x : ℝ) :
    HasDerivAt (fun x => y (l * x)) (l * y₁ (l * x)) x ∧
    HasDerivAt (fun x => l * y₁ (l * x)) (l ^ 2 * y₂ (l * x)) x ∧
    x ^ 2 * (l ^ 2 * y₂ (l * x)) + x * (l * y₁ (l * x)) + l ^ 2 * x ^ 2 * y (l * x) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · have : HasDerivAt (fun x => y (l * x)) (y₁ (l * x) * (l * 1)) x :=
      (hy (l * x)).comp x ((hasDerivAt_id' x).const_mul l)
    convert this using 1
    ring
  · have : HasDerivAt (fun x => l * y₁ (l * x)) (l * (y₂ (l * x) * (l * 1))) x :=
      ((hy₁ (l * x)).comp x ((hasDerivAt_id' x).const_mul l)).const_mul l
    convert this using 1
    ring
  · linear_combination hb (l * x)

/-- Action of the Bessel operator on a monomial: for `x > 0`,
`x² (s(s-1) x^{s-2}) + x (s x^{s-1}) + (x² - p²) x^s = (s² - p²) x^s + x^{s+2}`. This is the computation
behind the indicial equation. -/
lemma bessel_monomial (p s x : ℝ) (hx : 0 < x) :
    x ^ 2 * (s * (s - 1) * x ^ (s - 2)) + x * (s * x ^ (s - 1)) + (x ^ 2 - p ^ 2) * x ^ s =
      (s ^ 2 - p ^ 2) * x ^ s + x ^ (s + 2) := by
  have h1 : x ^ (s - 1) = x ^ s / x := by rw [Real.rpow_sub_one hx.ne']
  have h2 : x ^ (s - 2) = x ^ s / x ^ 2 := by
    rw [Real.rpow_sub hx, Real.rpow_two]
  have h3 : x ^ (s + 2) = x ^ s * x ^ 2 := by
    rw [Real.rpow_add hx, Real.rpow_two]
  rw [h1, h2, h3]
  field_simp
  ring

/-- DE-209 / DE-205 (Section 7.3.3, Bessel's equation, p. 347; Section 7.3, indicial equation, p. 344).
Frobenius ansatz `y = ∑_{k<N} a_k x^{r+k}` on `x > 0`: `y` is twice differentiable (with the termwise
derivatives `y₁`, `y₂`), and the Bessel expression `x² y'' + x y' + (x² - p²) y` equals
`∑ a_k ((r+k)² - p²) x^{r+k} + ∑ a_k x^{r+k+2}`. The lowest power `x^r` therefore has coefficient
`a₀ (r² - p²) = a₀ (r - p)(r + p)` (the indicial equation `(r-p)(r+p) = 0`), and the coefficient of
`x^{r+k+2}` is `a_{k+2}((r+k+2)² - p²) + a_k` (the recurrence). -/
@[kb "lebldiffyqs2026" "Section 7.3.3, p. 347"]
theorem bessel_frobenius_residual (p r : ℝ) (a : ℕ → ℝ) (N : ℕ) :
    (∀ x : ℝ, 0 < x → HasDerivAt (fun x => ∑ k ∈ Finset.range N, a k * x ^ (r + k))
      (∑ k ∈ Finset.range N, a k * ((r + k) * x ^ (r + k - 1))) x) ∧
    (∀ x : ℝ, 0 < x → HasDerivAt (fun x => ∑ k ∈ Finset.range N, a k * ((r + k) * x ^ (r + k - 1)))
      (∑ k ∈ Finset.range N, a k * ((r + k) * (r + k - 1) * x ^ (r + k - 2))) x) ∧
    (∀ x : ℝ, 0 < x →
      x ^ 2 * (∑ k ∈ Finset.range N, a k * ((r + k) * (r + k - 1) * x ^ (r + k - 2))) +
        x * (∑ k ∈ Finset.range N, a k * ((r + k) * x ^ (r + k - 1))) +
        (x ^ 2 - p ^ 2) * (∑ k ∈ Finset.range N, a k * x ^ (r + k)) =
      ∑ k ∈ Finset.range N, a k * (((r + k) ^ 2 - p ^ 2) * x ^ (r + k) + x ^ (r + k + 2))) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · refine HasDerivAt.fun_sum fun k _ => ?_
    exact (Real.hasDerivAt_rpow_const (p := r + k) (Or.inl hx.ne')).const_mul (a k)
  · refine HasDerivAt.fun_sum fun k _ => ?_
    have h := (Real.hasDerivAt_rpow_const (p := r + k - 1) (Or.inl hx.ne')).const_mul ((r + k))
    have := h.const_mul (a k)
    have e : r + k - 1 - 1 = r + k - 2 := by ring
    rw [e] at this
    convert this using 1
    ring
  · rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    linear_combination a k * bessel_monomial p (r + k) x hx

/-- DE-209 (Section 7.3.3, p. 347): the indicial polynomial `r² - p²` of Bessel's equation factors as
`(r - p)(r + p)`, so the exponents are `r = ±p`. -/
@[kb "lebldiffyqs2026" "Section 7.3.3, p. 347"]
theorem bessel_indicial_roots (p r : ℝ) : r ^ 2 - p ^ 2 = 0 ↔ r = p ∨ r = -p := by
  constructor
  · intro h
    have h' : (r - p) * (r + p) = 0 := by linear_combination h
    rcases mul_eq_zero.1 h' with h1 | h1
    · left; linarith
    · right; linarith
  · rintro (h | h) <;> rw [h] <;> ring

end UndergradKB.DifferentialEquations
