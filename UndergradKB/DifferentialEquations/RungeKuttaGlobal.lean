import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import UndergradKB.Common.Attr
import UndergradKB.DifferentialEquations.FirstOrderExtra

/-! # Global error of one-step methods, and of the Runge-Kutta method (Lebl, §1.7)

The book observes that halving the step of the classical Runge-Kutta method divides the error at a fixed point by
about 16 (fourth order), as halving the step of Euler's method halves the error.  The error at a fixed point is a
*global* error: the local errors of the steps accumulate.  We prove the standard convergence theorem for one-step
methods: if the step map `Φ(x, ·, h)` is Lipschitz with constant `e^{hL}` and every step from the exact solution
has local error at most `C h^{p+1}`, then after `n` steps the error is at most `(C h^p / L) (e^{L n h} - 1)`.
The Runge-Kutta step map satisfies the Lipschitz hypothesis whenever `f` is `L`-Lipschitz in `y` (for every `f`).
So a local error `O(h⁵)` gives global error `O(h⁴)`; this is proved unconditionally for the model equation
`y' = λ y`.  (The local error `O(h⁵)` for general `f(x, y)` is not proved: see the checklist row DE-038.) -/

namespace UndergradKB.DifferentialEquations

open Real Finset

/-- The iterates of a one-step method `Φ` (next value `Φ x y h`) from `(x₀, y₀)` with step `h`. -/
noncomputable def oneStepIter (Φ : ℝ → ℝ → ℝ → ℝ) (x₀ y₀ h : ℝ) : ℕ → ℝ
  | 0 => y₀
  | n + 1 => Φ (x₀ + n * h) (oneStepIter Φ x₀ y₀ h n) h

/-- The iterates of the classical fourth-order Runge-Kutta method. -/
noncomputable def rk4Iter (f : ℝ → ℝ → ℝ) (x₀ y₀ h : ℝ) : ℕ → ℝ :=
  oneStepIter (fun x y h => rk4Step f x y h) x₀ y₀ h

/-- **Convergence of one-step methods.**  If the step map is Lipschitz in `y` with constant `e^{hL}` and the local
error of every step from the exact solution is at most `C h^{p+1}` (for the first `N` steps), then the global error
after `n ≤ N` steps is at most `(C h^p / L)(e^{L n h} - 1)`. -/
@[kb "lebldiffyqs2026" "§1.7 Runge-Kutta method, p. 61"]
theorem oneStep_global_error {Φ : ℝ → ℝ → ℝ → ℝ} {y : ℝ → ℝ} {x₀ h L C : ℝ} {p N : ℕ} (hL : 0 < L)
    (hh : 0 < h) (hC : 0 ≤ C)
    (hlip : ∀ n : ℕ, n < N → ∀ u v, |Φ (x₀ + n * h) u h - Φ (x₀ + n * h) v h| ≤ exp (h * L) * |u - v|)
    (hloc : ∀ n : ℕ, n < N → |y (x₀ + (n + 1) * h) - Φ (x₀ + n * h) (y (x₀ + n * h)) h| ≤ C * h ^ (p + 1))
    {n : ℕ} (hn : n ≤ N) :
    |y (x₀ + n * h) - oneStepIter Φ x₀ (y x₀) h n| ≤ C * h ^ p / L * (exp (L * (n * h)) - 1) := by
  set q := exp (h * L) - 1 with hq
  have hhL : 0 < h * L := mul_pos hh hL
  have hq1 : h * L ≤ q := by have := add_one_le_exp (h * L); linarith
  have hq0 : 0 < q := lt_of_lt_of_le hhL hq1
  -- the error times `q` is at most `C h^{p+1} (e^{L n h} - 1)`
  have key : ∀ n : ℕ, n ≤ N →
      |y (x₀ + n * h) - oneStepIter Φ x₀ (y x₀) h n| * q ≤ C * h ^ (p + 1) * (exp (L * (n * h)) - 1) := by
    intro n
    induction n with
    | zero => intro _; simp [oneStepIter]
    | succ n ih =>
      intro hn
      have hnN : n < N := hn
      have ih := ih hnN.le
      set e := |y (x₀ + n * h) - oneStepIter Φ x₀ (y x₀) h n|
      have hstep : |y (x₀ + ((n + 1 : ℕ) : ℝ) * h) - oneStepIter Φ x₀ (y x₀) h (n + 1)| ≤
          C * h ^ (p + 1) + exp (h * L) * e := by
        have hdec : y (x₀ + ((n + 1 : ℕ) : ℝ) * h) - oneStepIter Φ x₀ (y x₀) h (n + 1) =
            (y (x₀ + (n + 1) * h) - Φ (x₀ + n * h) (y (x₀ + n * h)) h) +
              (Φ (x₀ + n * h) (y (x₀ + n * h)) h - Φ (x₀ + n * h) (oneStepIter Φ x₀ (y x₀) h n) h) := by
          simp only [oneStepIter]; push_cast; ring
        rw [hdec]
        exact (abs_add_le _ _).trans (add_le_add (hloc n hnN) (hlip n hnN _ _))
      have hexp : exp (h * L) * exp (L * (n * h)) = exp (L * (((n + 1 : ℕ) : ℝ) * h)) := by
        rw [← exp_add]; congr 1; push_cast; ring
      have hE : 1 ≤ exp (L * (n * h)) := one_le_exp (by positivity)
      calc _ ≤ (C * h ^ (p + 1) + exp (h * L) * e) * q := mul_le_mul_of_nonneg_right hstep hq0.le
        _ = C * h ^ (p + 1) * q + exp (h * L) * (e * q) := by ring
        _ ≤ C * h ^ (p + 1) * q + exp (h * L) * (C * h ^ (p + 1) * (exp (L * (n * h)) - 1)) := by
            gcongr
        _ = C * h ^ (p + 1) * (exp (h * L) * exp (L * (n * h)) - 1) := by rw [hq]; ring
        _ = _ := by rw [hexp]
  have hE : 0 ≤ exp (L * (n * h)) - 1 := by
    have := one_le_exp (show 0 ≤ L * (n * h) by positivity); linarith
  have hk := key n hn
  rw [← le_div_iff₀ hq0] at hk
  refine hk.trans ?_
  rw [div_le_iff₀ hq0]
  have hCp : 0 ≤ C * h ^ p * (exp (L * (n * h)) - 1) := by positivity
  calc C * h ^ (p + 1) * (exp (L * (n * h)) - 1) = (C * h ^ p * (exp (L * (n * h)) - 1)) / L * (h * L) := by
        field_simp; ring
    _ ≤ (C * h ^ p * (exp (L * (n * h)) - 1)) / L * q := by gcongr
    _ = _ := by ring

lemma abs_rk_comb (a b c d : ℝ) : |a + 2 * b + 2 * c + d| ≤ |a| + 2 * |b| + 2 * |c| + |d| := by
  have h1 := abs_add_le (a + 2 * b + 2 * c) d
  have h2 := abs_add_le (a + 2 * b) (2 * c)
  have h3 := abs_add_le a (2 * b)
  rw [abs_mul, abs_two] at h2 h3
  linarith

/-- **The Runge-Kutta step is Lipschitz in `y`** with constant `1 + z + z²/2 + z³/6 + z⁴/24 ≤ e^z`, `z = hL`,
whenever `f(x, ·)` is `L`-Lipschitz and `h ≥ 0`. -/
theorem rk4Step_lipschitz {f : ℝ → ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L) (hlip : ∀ x u v, |f x u - f x v| ≤ L * |u - v|)
    (x u v : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    |rk4Step f x u h - rk4Step f x v h| ≤ exp (h * L) * |u - v| := by
  set d := |u - v| with hd
  have hd0 : 0 ≤ d := abs_nonneg _
  set z := h * L with hz
  have hz0 : 0 ≤ z := mul_nonneg hh hL
  -- the four slopes
  set k1u := f x u
  set k1v := f x v
  have h1 : |k1u - k1v| ≤ L * d := hlip x u v
  set k2u := f (x + h / 2) (u + h / 2 * k1u)
  set k2v := f (x + h / 2) (v + h / 2 * k1v)
  have h2 : |k2u - k2v| ≤ L * (d + h / 2 * (L * d)) := by
    refine (hlip _ _ _).trans (mul_le_mul_of_nonneg_left ?_ hL)
    calc |u + h / 2 * k1u - (v + h / 2 * k1v)| = |(u - v) + h / 2 * (k1u - k1v)| := by ring_nf
      _ ≤ |u - v| + |h / 2 * (k1u - k1v)| := abs_add_le _ _
      _ ≤ d + h / 2 * (L * d) := by
          rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ h / 2)]; gcongr
  set k3u := f (x + h / 2) (u + h / 2 * k2u)
  set k3v := f (x + h / 2) (v + h / 2 * k2v)
  have h3 : |k3u - k3v| ≤ L * (d + h / 2 * (L * (d + h / 2 * (L * d)))) := by
    refine (hlip _ _ _).trans (mul_le_mul_of_nonneg_left ?_ hL)
    calc |u + h / 2 * k2u - (v + h / 2 * k2v)| = |(u - v) + h / 2 * (k2u - k2v)| := by ring_nf
      _ ≤ |u - v| + |h / 2 * (k2u - k2v)| := abs_add_le _ _
      _ ≤ _ := by
          rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ h / 2)]; gcongr
  set k4u := f (x + h) (u + h * k3u)
  set k4v := f (x + h) (v + h * k3v)
  have h4 : |k4u - k4v| ≤ L * (d + h * (L * (d + h / 2 * (L * (d + h / 2 * (L * d)))))) := by
    refine (hlip _ _ _).trans (mul_le_mul_of_nonneg_left ?_ hL)
    calc |u + h * k3u - (v + h * k3v)| = |(u - v) + h * (k3u - k3v)| := by ring_nf
      _ ≤ |u - v| + |h * (k3u - k3v)| := abs_add_le _ _
      _ ≤ _ := by
          rw [abs_mul, abs_of_nonneg hh]; gcongr
  have hsum : rk4Step f x u h - rk4Step f x v h =
      (u - v) + h / 6 * ((k1u - k1v) + 2 * (k2u - k2v) + 2 * (k3u - k3v) + (k4u - k4v)) := by
    simp only [rk4Step, k1u, k1v, k2u, k2v, k3u, k3v, k4u, k4v]; ring
  have hpoly : 1 + z + z ^ 2 / 2 + z ^ 3 / 6 + z ^ 4 / 24 ≤ exp z := by
    have := sum_le_exp_of_nonneg hz0 5
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at this
    norm_num at this
    linarith
  rw [hsum]
  calc _ ≤ |u - v| + |h / 6 * ((k1u - k1v) + 2 * (k2u - k2v) + 2 * (k3u - k3v) + (k4u - k4v))| :=
        abs_add_le _ _
    _ ≤ d + h / 6 * (|k1u - k1v| + 2 * |k2u - k2v| + 2 * |k3u - k3v| + |k4u - k4v|) := by
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ h / 6)]
        gcongr
        exact abs_rk_comb _ _ _ _
    _ ≤ d + h / 6 * (L * d + 2 * (L * (d + h / 2 * (L * d))) +
          2 * (L * (d + h / 2 * (L * (d + h / 2 * (L * d))))) +
          L * (d + h * (L * (d + h / 2 * (L * (d + h / 2 * (L * d))))))) := by gcongr
    _ = (1 + z + z ^ 2 / 2 + z ^ 3 / 6 + z ^ 4 / 24) * d := by rw [hz]; ring
    _ ≤ exp z * d := mul_le_mul_of_nonneg_right hpoly hd0

/-- **Runge-Kutta is fourth order globally, given fourth-order local error** (Lebl §1.7: halving the step divides
the error by about 16).  If `f(x, ·)` is `L`-Lipschitz (`L > 0`) and each Runge-Kutta step from the exact solution
has local error at most `C h⁵` (for the first `N` steps), then after `n ≤ N` steps the error is at most
`(C h⁴ / L)(e^{L n h} - 1)`: a bound proportional to `h⁴`, divided by 16 when `h` is halved (at the same point
`x₀ + n h`). -/
@[kb "lebldiffyqs2026" "§1.7 Runge-Kutta method, p. 61"]
theorem rk4_global_error {f : ℝ → ℝ → ℝ} {y : ℝ → ℝ} {x₀ h L C : ℝ} {N : ℕ} (hL : 0 < L) (hh : 0 < h)
    (hC : 0 ≤ C) (hlip : ∀ x u v, |f x u - f x v| ≤ L * |u - v|)
    (hloc : ∀ n : ℕ, n < N → |y (x₀ + (n + 1) * h) - rk4Step f (x₀ + n * h) (y (x₀ + n * h)) h| ≤ C * h ^ 5)
    {n : ℕ} (hn : n ≤ N) :
    |y (x₀ + n * h) - rk4Iter f x₀ (y x₀) h n| ≤ C * h ^ 4 / L * (exp (L * (n * h)) - 1) :=
  oneStep_global_error (Φ := fun x y h => rk4Step f x y h) (p := 4) hL hh hC
    (fun _ _ u v => rk4Step_lipschitz hL.le hlip _ u v hh.le) hloc hn

/-- **Runge-Kutta on `y' = λ y` is fourth order globally** (unconditional): for `λ ≠ 0`, `0 < h`, `|λ| h ≤ 1`, and
`n h ≤ X`, the error at `x₀ + n h` of the Runge-Kutta iterates against the exact solution `y₀ e^{λ (x - x₀)}` is at
most `K h⁴` with `K = |λ|⁴ |y₀| e^{|λ| X} (e^{|λ| X} - 1) / 100`, independent of `h` and `n`. -/
@[kb "lebldiffyqs2026" "§1.7 Runge-Kutta method, p. 61"]
theorem rk4_linear_global_error {lam : ℝ} (hlam : lam ≠ 0) (x₀ y₀ : ℝ) {h X : ℝ} (hh : 0 < h)
    (hz : |lam| * h ≤ 1) {n : ℕ} (hn : n * h ≤ X) :
    |y₀ * exp (lam * (n * h)) - rk4Iter (fun _ y => lam * y) x₀ y₀ h n| ≤
      |lam| ^ 4 * |y₀| * exp (|lam| * X) * (exp (|lam| * X) - 1) / 100 * h ^ 4 := by
  set y : ℝ → ℝ := fun x => y₀ * exp (lam * (x - x₀)) with hy
  have hL : 0 < |lam| := abs_pos.2 hlam
  have hX : 0 ≤ X := le_trans (by positivity) hn
  have hy0 : y x₀ = y₀ := by simp [hy]
  have hyn : ∀ m : ℕ, y (x₀ + m * h) = y₀ * exp (lam * (m * h)) := fun m => by simp [hy]
  set N : ℕ := n
  set C : ℝ := 1 / 100 * |lam| ^ 5 * (|y₀| * exp (|lam| * X))
  have hlip : ∀ (x u v : ℝ), |(fun _ y => lam * y) x u - (fun _ y => lam * y) x v| ≤ |lam| * |u - v| := by
    intro x u v; simp only; rw [← mul_sub, abs_mul]
  have hloc : ∀ m : ℕ, m < N → |y (x₀ + (m + 1) * h) - rk4Step (fun _ y => lam * y) (x₀ + m * h)
      (y (x₀ + m * h)) h| ≤ C * h ^ 5 := by
    intro m hm
    have hzl : |lam * h| ≤ 1 := by rw [abs_mul, abs_of_pos hh]; exact hz
    have hloc1 := rk4Step_linear_error lam (x₀ + m * h) (y (x₀ + m * h)) h hzl
    have e1 : y (x₀ + (m + 1) * h) = exp (lam * h) * y (x₀ + m * h) := by
      simp only [hy]
      rw [show lam * (x₀ + (m + 1) * h - x₀) = lam * h + lam * (x₀ + m * h - x₀) by ring, exp_add]
      ring
    rw [e1, abs_sub_comm]
    refine hloc1.trans ?_
    have hym : |y (x₀ + m * h)| ≤ |y₀| * exp (|lam| * X) := by
      rw [hyn, abs_mul, abs_exp]
      refine mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) (abs_nonneg _)
      have hmX : (m : ℝ) * h ≤ X := le_trans (by gcongr) hn
      have hmh : (0 : ℝ) ≤ m * h := by positivity
      calc lam * (m * h) ≤ |lam * (m * h)| := le_abs_self _
        _ = |lam| * (m * h) := by rw [abs_mul, abs_of_nonneg hmh]
        _ ≤ |lam| * X := by gcongr
    rw [abs_mul, abs_of_pos hh, mul_pow]
    simp only [C]
    have : 0 ≤ |lam| ^ 5 * h ^ 5 := by positivity
    nlinarith
  have hC : 0 ≤ C := by positivity
  have hg := rk4_global_error hL hh hC hlip hloc (n := n) le_rfl
  rw [hyn, hy0] at hg
  refine hg.trans ?_
  have hE : exp (|lam| * (n * h)) ≤ exp (|lam| * X) := exp_le_exp.2 (by gcongr)
  have hE1 : 0 ≤ exp (|lam| * (n * h)) - 1 := by
    have := one_le_exp (show 0 ≤ |lam| * (n * h) by positivity); linarith
  calc C * h ^ 4 / |lam| * (exp (|lam| * (n * h)) - 1)
      ≤ C * h ^ 4 / |lam| * (exp (|lam| * X) - 1) := by gcongr
    _ = _ := by simp only [C]; field_simp

end UndergradKB.DifferentialEquations
