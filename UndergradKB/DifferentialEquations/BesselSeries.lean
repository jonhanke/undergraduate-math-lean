import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Bessel
import UndergradKB.Common.Attr

/-! # Bessel functions of the first kind (Lebl, *Notes on Diffy Qs*, §7.3.3)

The real series `J_p(x) = ∑ (-1)^k / (k! Γ(k+p+1)) (x/2)^(2k+p)` for `x > 0` (`besselJR`), for every real `p`
that is not a negative integer, is shown to solve Bessel's equation `x² y'' + x y' + (x² - p²) y = 0` on `x > 0`,
by termwise differentiation of the everywhere convergent power series `∑ b_k x^(2k)` (convergence by the ratio
test from the recurrence `4 (k+1) (k+1+p) b_{k+1} = - b_k`).  Also `J_0' = -J_1` and the recurrence
`2 p J_p = x (J_{p-1} + J_{p+1})` for `p > 0`, and wrappers for Mathlib's complex `Complex.besselJ`
(reflection for integer order, the recurrence).
-/

namespace UndergradKB.DifferentialEquations

open Filter Topology

section Series

variable (b : ℕ → ℝ)

/-- The even power series `∑ b_n x^(2n)`. -/
noncomputable def evS (x : ℝ) : ℝ := ∑' n, b n * x ^ (2 * n)

/-- Its termwise derivative. -/
noncomputable def evS1 (x : ℝ) : ℝ := ∑' n, b n * (((2 * n : ℕ) : ℝ) * x ^ (2 * n - 1))

/-- Its termwise second derivative. -/
noncomputable def evS2 (x : ℝ) : ℝ :=
  ∑' n, b n * (((2 * n : ℕ) : ℝ) * (((2 * n - 1 : ℕ) : ℝ) * x ^ (2 * n - 1 - 1)))

variable {b}

lemma summable_n (hsum : ∀ r : ℝ, 0 < r → Summable fun n => |b n| * r ^ n) {r : ℝ} (hr : 0 < r) :
    Summable fun n : ℕ => |b n| * (n : ℝ) * r ^ n := by
  refine (hsum (2 * r) (by positivity)).of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
  have h : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
  calc |b n| * (n : ℝ) * r ^ n = |b n| * ((n : ℝ) * r ^ n) := by ring
    _ ≤ |b n| * (2 ^ n * r ^ n) := by gcongr
    _ = |b n| * (2 * r) ^ n := by rw [mul_pow]

lemma summable_n2 (hsum : ∀ r : ℝ, 0 < r → Summable fun n => |b n| * r ^ n) {r : ℝ} (hr : 0 < r) :
    Summable fun n : ℕ => |b n| * (n : ℝ) ^ 2 * r ^ n := by
  refine (hsum (4 * r) (by positivity)).of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
  have h : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
  have h2 : (n : ℝ) ^ 2 ≤ 4 ^ n := by
    calc (n : ℝ) ^ 2 ≤ (2 ^ n) ^ 2 := by gcongr
      _ = 4 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  calc |b n| * (n : ℝ) ^ 2 * r ^ n = |b n| * ((n : ℝ) ^ 2 * r ^ n) := by ring
    _ ≤ |b n| * (4 ^ n * r ^ n) := by gcongr
    _ = |b n| * (4 * r) ^ n := by rw [mul_pow]

lemma pow_le_R {y R : ℝ} (hy : |y| ≤ R) (hR : 1 ≤ R) {m n : ℕ} (h : m ≤ 2 * n) :
    |y| ^ m ≤ (R ^ 2) ^ n := by
  calc |y| ^ m ≤ R ^ m := pow_le_pow_left₀ (abs_nonneg _) hy m
    _ ≤ R ^ (2 * n) := pow_le_pow_right₀ hR h
    _ = (R ^ 2) ^ n := pow_mul R 2 n

lemma bound0 {y R : ℝ} (hy : |y| ≤ R) (hR : 1 ≤ R) (n : ℕ) :
    ‖b n * y ^ (2 * n)‖ ≤ |b n| * (R ^ 2) ^ n := by
  rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs]
  gcongr
  exact pow_le_R hy hR le_rfl

lemma bound1 {y R : ℝ} (hy : |y| ≤ R) (hR : 1 ≤ R) (n : ℕ) :
    ‖b n * (((2 * n : ℕ) : ℝ) * y ^ (2 * n - 1))‖ ≤ 2 * (|b n| * (n : ℝ) * (R ^ 2) ^ n) := by
  rw [norm_mul, norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
  have h1 : |y| ^ (2 * n - 1) ≤ (R ^ 2) ^ n := pow_le_R hy hR (Nat.sub_le _ _)
  have h2 : |((2 * n : ℕ) : ℝ)| = 2 * n := by
    rw [abs_of_nonneg (by positivity)]; push_cast; ring
  rw [h2]
  calc |b n| * (2 * (n : ℝ) * |y| ^ (2 * n - 1)) ≤ |b n| * (2 * (n : ℝ) * (R ^ 2) ^ n) := by gcongr
    _ = _ := by ring

lemma bound2 {y R : ℝ} (hy : |y| ≤ R) (hR : 1 ≤ R) (n : ℕ) :
    ‖b n * (((2 * n : ℕ) : ℝ) * (((2 * n - 1 : ℕ) : ℝ) * y ^ (2 * n - 1 - 1)))‖
      ≤ 4 * (|b n| * (n : ℝ) ^ 2 * (R ^ 2) ^ n) := by
  rw [norm_mul, norm_mul, norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
    Real.norm_eq_abs]
  have h1 : |y| ^ (2 * n - 1 - 1) ≤ (R ^ 2) ^ n := pow_le_R hy hR (by omega)
  have h2 : |((2 * n : ℕ) : ℝ)| = 2 * n := by
    rw [abs_of_nonneg (by positivity)]; push_cast; ring
  have h3 : |((2 * n - 1 : ℕ) : ℝ)| ≤ 2 * n := by
    rw [abs_of_nonneg (by positivity)]
    have : ((2 * n - 1 : ℕ) : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le _ _
    push_cast at this; linarith
  rw [h2]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc |b n| * (2 * (n : ℝ) * (|((2 * n - 1 : ℕ) : ℝ)| * |y| ^ (2 * n - 1 - 1)))
      ≤ |b n| * (2 * (n : ℝ) * ((2 * n) * (R ^ 2) ^ n)) := by gcongr
    _ = _ := by ring

lemma summable0 (hsum : ∀ r : ℝ, 0 < r → Summable fun n => |b n| * r ^ n) {y R : ℝ} (hy : |y| ≤ R)
    (hR : 1 ≤ R) : Summable fun n => b n * y ^ (2 * n) :=
  Summable.of_norm_bounded (hsum (R ^ 2) (by positivity)) (fun n => bound0 hy hR n)

lemma summable1 (hsum : ∀ r : ℝ, 0 < r → Summable fun n => |b n| * r ^ n) {y R : ℝ} (hy : |y| ≤ R)
    (hR : 1 ≤ R) : Summable fun n => b n * (((2 * n : ℕ) : ℝ) * y ^ (2 * n - 1)) :=
  Summable.of_norm_bounded ((summable_n hsum (by positivity : (0 : ℝ) < R ^ 2)).mul_left 2)
    (fun n => bound1 hy hR n)

lemma summable2 (hsum : ∀ r : ℝ, 0 < r → Summable fun n => |b n| * r ^ n) {y R : ℝ} (hy : |y| ≤ R)
    (hR : 1 ≤ R) :
    Summable fun n => b n * (((2 * n : ℕ) : ℝ) * (((2 * n - 1 : ℕ) : ℝ) * y ^ (2 * n - 1 - 1))) :=
  Summable.of_norm_bounded ((summable_n2 hsum (by positivity : (0 : ℝ) < R ^ 2)).mul_left 4)
    (fun n => bound2 hy hR n)

lemma abs_lt_R (y : ℝ) : |y| ≤ |y| + 1 := by linarith

theorem hasDerivAt_evS (hsum : ∀ r : ℝ, 0 < r → Summable fun n => |b n| * r ^ n) (y : ℝ) :
    HasDerivAt (evS b) (evS1 b y) y := by
  have hR : 1 ≤ |y| + 1 := by linarith [abs_nonneg y]
  have hmem : y ∈ Metric.ball (0 : ℝ) (|y| + 1) := by
    rw [mem_ball_zero_iff, Real.norm_eq_abs]; linarith
  have := hasDerivAt_tsum_of_isPreconnected (g := fun n z => b n * z ^ (2 * n))
    (g' := fun n z => b n * (((2 * n : ℕ) : ℝ) * z ^ (2 * n - 1)))
    ((summable_n hsum (by positivity : (0 : ℝ) < (|y| + 1) ^ 2)).mul_left 2) Metric.isOpen_ball
    (convex_ball (0 : ℝ) _).isPreconnected
    (fun n z _ => (hasDerivAt_pow (2 * n) z).const_mul (b n))
    (fun n z hz => bound1 (by rw [mem_ball_zero_iff, Real.norm_eq_abs] at hz; exact hz.le) hR n)
    hmem (summable0 hsum (abs_lt_R y) hR) hmem
  exact this

theorem hasDerivAt_evS1 (hsum : ∀ r : ℝ, 0 < r → Summable fun n => |b n| * r ^ n) (y : ℝ) :
    HasDerivAt (evS1 b) (evS2 b y) y := by
  have hR : 1 ≤ |y| + 1 := by linarith [abs_nonneg y]
  have hmem : y ∈ Metric.ball (0 : ℝ) (|y| + 1) := by
    rw [mem_ball_zero_iff, Real.norm_eq_abs]; linarith
  have := hasDerivAt_tsum_of_isPreconnected
    (g := fun n z => b n * (((2 * n : ℕ) : ℝ) * z ^ (2 * n - 1)))
    (g' := fun n z => b n * (((2 * n : ℕ) : ℝ) * (((2 * n - 1 : ℕ) : ℝ) * z ^ (2 * n - 1 - 1))))
    ((summable_n2 hsum (by positivity : (0 : ℝ) < (|y| + 1) ^ 2)).mul_left 4) Metric.isOpen_ball
    (convex_ball (0 : ℝ) _).isPreconnected
    (fun n z _ => ((hasDerivAt_pow (2 * n - 1) z).const_mul ((2 * n : ℕ) : ℝ)).const_mul (b n))
    (fun n z hz => bound2 (by rw [mem_ball_zero_iff, Real.norm_eq_abs] at hz; exact hz.le) hR n)
    hmem (summable1 hsum (abs_lt_R y) hR) hmem
  exact this

/-- The series equation: if `4 (n+1) (n+1+p) b_{n+1} = - b_n`, then
`x S'' + (2p+1) S' + x S = 0` for `S = ∑ b_n x^(2n)`. -/
theorem evS_ode (p : ℝ) (hrec : ∀ n : ℕ, b (n + 1) * (4 * ((n : ℝ) + 1) * ((n : ℝ) + 1 + p)) = - b n)
    (hsum : ∀ r : ℝ, 0 < r → Summable fun n => |b n| * r ^ n) (x : ℝ) :
    x * evS2 b x + (2 * p + 1) * evS1 b x + x * evS b x = 0 := by
  have hR : 1 ≤ |x| + 1 := by linarith [abs_nonneg x]
  have s0 := summable0 hsum (abs_lt_R x) hR
  have s1 := summable1 hsum (abs_lt_R x) hR
  have s2 := summable2 hsum (abs_lt_R x) hR
  set A : ℕ → ℝ := fun n =>
    x * (b n * (((2 * n : ℕ) : ℝ) * (((2 * n - 1 : ℕ) : ℝ) * x ^ (2 * n - 1 - 1)))) +
      (2 * p + 1) * (b n * (((2 * n : ℕ) : ℝ) * x ^ (2 * n - 1))) with hA
  have sA : Summable A := (s2.mul_left x).add (s1.mul_left (2 * p + 1))
  have e1 : x * evS2 b x + (2 * p + 1) * evS1 b x = ∑' n, A n := by
    unfold evS2 evS1
    rw [← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_add (s2.mul_left x) (s1.mul_left _)]
  have hA0 : A 0 = 0 := by simp [hA]
  have hAs : ∀ n : ℕ, A (n + 1) = - (b n * x ^ (2 * n + 1)) := by
    intro n
    have e2 : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
    have e3 : 2 * n + 1 - 1 = 2 * n := by omega
    simp only [hA, e2, e3]
    push_cast
    have := hrec n
    rw [pow_succ]
    linear_combination (x ^ (2 * n) * x) * this
  have e4 : ∑' n, A n = ∑' n : ℕ, - (b n * x ^ (2 * n + 1)) := by
    rw [sA.tsum_eq_zero_add, hA0, zero_add]
    exact tsum_congr hAs
  have e5 : x * evS b x = ∑' n : ℕ, b n * x ^ (2 * n + 1) := by
    unfold evS
    rw [← tsum_mul_left]
    exact tsum_congr (fun n => by rw [pow_succ]; ring)
  rw [e1, e4, e5, tsum_neg]
  ring

/-- Ratio test: a nowhere-vanishing sequence with `4 (n+1)(n+1+p) b_{n+1} = - b_n` gives an everywhere
convergent power series. -/
lemma hsum_of_rec (p : ℝ) (hrec : ∀ n : ℕ, b (n + 1) * (4 * ((n : ℝ) + 1) * ((n : ℝ) + 1 + p)) = - b n)
    (hne : ∀ n, b n ≠ 0) : ∀ r : ℝ, 0 < r → Summable fun n => |b n| * r ^ n := by
  intro r hr
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1 + p) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have h2 := tendsto_abs_atTop_atTop.comp h1
  have h3 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have h4 := (h3.atTop_mul_atTop₀ h2).const_mul_atTop (by norm_num : (0 : ℝ) < 4)
  have h5 := (tendsto_const_nhds (x := r)).div_atTop h4
  refine summable_of_ratio_test_tendsto_lt_one (l := 0) zero_lt_one
    (Eventually.of_forall fun n => by have := hne n; positivity) (h5.congr fun n => ?_)
  have hn := hrec n
  have hb := hne n
  have hb1 := hne (n + 1)
  have hpos : (0 : ℝ) < 4 * (((n : ℝ) + 1) * |(n : ℝ) + 1 + p|) := by
    have : (n : ℝ) + 1 + p ≠ 0 := by
      intro h; rw [h] at hn; simp at hn; exact hb hn
    positivity
  have habs : |b (n + 1)| * (4 * (((n : ℝ) + 1) * |(n : ℝ) + 1 + p|)) = |b n| := by
    have := congrArg abs hn
    rw [abs_mul, abs_neg, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4),
      abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)] at this
    rw [← this]; ring
  simp only [Function.comp_apply, Real.norm_eq_abs, abs_mul, abs_abs, abs_pow, abs_of_pos hr]
  have hb' : 0 < |b n| := abs_pos.mpr hb
  rw [← habs]
  field_simp
  ring

/-- The coefficients `(-1)^k / (4^k k! Γ(k+p+1))`. -/
noncomputable def bcoef (p : ℝ) (k : ℕ) : ℝ :=
  (-1) ^ k / ((k.factorial : ℝ) * Real.Gamma ((k : ℝ) + p + 1)) / 4 ^ k

lemma gamma_ne (p : ℝ) (hp : ∀ m : ℕ, p + 1 ≠ -(m : ℝ)) (k : ℕ) : Real.Gamma ((k : ℝ) + p + 1) ≠ 0 := by
  apply Real.Gamma_ne_zero
  intro m h
  apply hp (m + k)
  push_cast
  linarith

lemma bcoef_ne (p : ℝ) (hp : ∀ m : ℕ, p + 1 ≠ -(m : ℝ)) (k : ℕ) : bcoef p k ≠ 0 := by
  have := gamma_ne p hp k
  unfold bcoef
  positivity

lemma bcoef_rec (p : ℝ) (hp : ∀ m : ℕ, p + 1 ≠ -(m : ℝ)) (n : ℕ) :
    bcoef p (n + 1) * (4 * ((n : ℝ) + 1) * ((n : ℝ) + 1 + p)) = - bcoef p n := by
  have hg := gamma_ne p hp n
  have hne : (n : ℝ) + p + 1 ≠ 0 := by
    intro h; apply hp n; linarith
  have e : Real.Gamma (((n + 1 : ℕ) : ℝ) + p + 1) = ((n : ℝ) + p + 1) * Real.Gamma ((n : ℝ) + p + 1) := by
    rw [← Real.Gamma_add_one hne]; push_cast; ring_nf
  have hne2 : (n : ℝ) + 1 + p ≠ 0 := by
    intro h; apply hne; linarith
  unfold bcoef
  rw [e, Nat.factorial_succ]
  push_cast
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma bcoef_hsum (p : ℝ) (hp : ∀ m : ℕ, p + 1 ≠ -(m : ℝ)) :
    ∀ r : ℝ, 0 < r → Summable fun n => |bcoef p n| * r ^ n :=
  hsum_of_rec p (bcoef_rec p hp) (bcoef_ne p hp)

end Series

section Bessel

/-- The real Bessel function of the first kind of order `p`, for `x > 0`, as the series
`∑ (-1)^k / (k! Γ(k+p+1)) (x/2)^(2k+p)` (real powers). -/
noncomputable def besselJR (p x : ℝ) : ℝ :=
  ∑' k : ℕ, (-1) ^ k / ((k.factorial : ℝ) * Real.Gamma ((k : ℝ) + p + 1)) * (x / 2) ^ (2 * (k : ℝ) + p)

lemma term_eq (p x : ℝ) (hx : 0 < x) (k : ℕ) :
    (-1) ^ k / ((k.factorial : ℝ) * Real.Gamma ((k : ℝ) + p + 1)) * (x / 2) ^ (2 * (k : ℝ) + p) =
      (x / 2) ^ p * (bcoef p k * x ^ (2 * k)) := by
  have e1 : (x / 2) ^ (2 * (k : ℝ) + p) = (x / 2) ^ (2 * k) * (x / 2) ^ p := by
    rw [Real.rpow_add (by positivity)]
    congr 1
    rw [show (2 * (k : ℝ)) = ((2 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have e2 : (2 : ℝ) ^ (2 * k) = 4 ^ k := by rw [pow_mul]; norm_num
  unfold bcoef
  rw [e1, div_pow, e2]
  ring

lemma besselJR_eq (p x : ℝ) (hx : 0 < x) :
    besselJR p x = (x / 2) ^ p * evS (bcoef p) x := by
  unfold besselJR evS
  rw [← tsum_mul_left]
  exact tsum_congr (term_eq p x hx)

lemma hasDerivAt_u (p x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (y / 2) ^ p) (p * (x / 2) ^ p / x) x := by
  have h := ((hasDerivAt_id x).div_const 2).rpow_const (p := p) (Or.inl (by simpa using hx.ne'))
  have h' : HasDerivAt (fun y : ℝ => (y / 2) ^ p) (1 / 2 * p * (x / 2) ^ (p - 1)) x := h
  refine h'.congr_deriv ?_
  rw [Real.rpow_sub_one (by positivity)]
  field_simp

lemma hasDerivAt_v (p x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => p * (y / 2) ^ p / y) (p * (p - 1) * (x / 2) ^ p / x ^ 2) x := by
  have h := ((hasDerivAt_u p x hx).const_mul p).div (hasDerivAt_id x) hx.ne'
  have h' : HasDerivAt (fun y : ℝ => p * (y / 2) ^ p / y)
      ((p * (p * (x / 2) ^ p / x) * x - p * (x / 2) ^ p * 1) / x ^ 2) x := h
  refine h'.congr_deriv ?_
  field_simp

/-- First derivative of `besselJR p` on `x > 0` (explicit form). -/
noncomputable def besselJ1 (p x : ℝ) : ℝ :=
  p * (x / 2) ^ p / x * evS (bcoef p) x + (x / 2) ^ p * evS1 (bcoef p) x

/-- Second derivative of `besselJR p` on `x > 0` (explicit form). -/
noncomputable def besselJ2 (p x : ℝ) : ℝ :=
  p * (p - 1) * (x / 2) ^ p / x ^ 2 * evS (bcoef p) x + p * (x / 2) ^ p / x * evS1 (bcoef p) x +
    (p * (x / 2) ^ p / x * evS1 (bcoef p) x + (x / 2) ^ p * evS2 (bcoef p) x)

theorem hasDerivAt_besselJR (p : ℝ) (hp : ∀ m : ℕ, p + 1 ≠ -(m : ℝ)) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (besselJR p) (besselJ1 p x) x := by
  have h := (hasDerivAt_u p x hx).mul (hasDerivAt_evS (bcoef_hsum p hp) x)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hx] with y hy using besselJR_eq p y hy

theorem hasDerivAt_besselJ1 (p : ℝ) (hp : ∀ m : ℕ, p + 1 ≠ -(m : ℝ)) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (besselJ1 p) (besselJ2 p x) x := by
  have h1 := (hasDerivAt_v p x hx).mul (hasDerivAt_evS (bcoef_hsum p hp) x)
  have h2 := (hasDerivAt_u p x hx).mul (hasDerivAt_evS1 (bcoef_hsum p hp) x)
  exact h1.add h2

theorem besselJ2_ode (p : ℝ) (hp : ∀ m : ℕ, p + 1 ≠ -(m : ℝ)) {x : ℝ} (hx : 0 < x) :
    x ^ 2 * besselJ2 p x + x * besselJ1 p x + (x ^ 2 - p ^ 2) * besselJR p x = 0 := by
  have E := evS_ode p (bcoef_rec p hp) (bcoef_hsum p hp) x
  rw [besselJR_eq p x hx]
  unfold besselJ2 besselJ1
  have key : ∀ S S1 S2 u : ℝ, x * S2 + (2 * p + 1) * S1 + x * S = 0 →
      x ^ 2 * (p * (p - 1) * u / x ^ 2 * S + p * u / x * S1 + (p * u / x * S1 + u * S2)) +
        x * (p * u / x * S + u * S1) + (x ^ 2 - p ^ 2) * (u * S) = 0 := by
    intro S S1 S2 u h
    have hx0 : x ≠ 0 := hx.ne'
    have : x ^ 2 * (p * (p - 1) * u / x ^ 2 * S + p * u / x * S1 + (p * u / x * S1 + u * S2)) +
        x * (p * u / x * S + u * S1) + (x ^ 2 - p ^ 2) * (u * S) = u * x * (x * S2 + (2 * p + 1) * S1 + x * S) := by
      field_simp
      ring
    rw [this, h, mul_zero]
  exact key _ _ _ _ E

/-- Bessel's equation. For real `p` that is not a negative integer, the series `J_p` (for `x > 0`) satisfies
`x² y'' + x y' + (x² - p²) y = 0` on `x > 0`, with `y'` and `y''` the actual derivatives (DE-212, DE-213:
for `p` not an integer both `J_p` and `J_{-p}` are covered, `-p` also not being a negative integer when
`p` is a non-integer; for integer order it covers `J_n`, `n ≥ 0`). -/
@[kb "lebldiffyqs2026" "Solutions of Bessel's equation, p. 348"]
theorem besselJR_solves_bessel (p : ℝ) (hp : ∀ m : ℕ, p + 1 ≠ -(m : ℝ)) {x : ℝ} (hx : 0 < x) :
    x ^ 2 * deriv (deriv (besselJR p)) x + x * deriv (besselJR p) x + (x ^ 2 - p ^ 2) * besselJR p x = 0 := by
  have hd : deriv (besselJR p) =ᶠ[𝓝 x] besselJ1 p := by
    filter_upwards [Ioi_mem_nhds hx] with y hy using (hasDerivAt_besselJR p hp hy).deriv
  rw [hd.deriv_eq, (hasDerivAt_besselJ1 p hp hx).deriv, (hasDerivAt_besselJR p hp hx).deriv]
  exact besselJ2_ode p hp hx

lemma hp_of_nonneg {p : ℝ} (hp : 0 ≤ p) : ∀ m : ℕ, p + 1 ≠ -(m : ℝ) := by
  intro m h
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

lemma hp_of_not_int {p : ℝ} (hp : ∀ n : ℤ, p ≠ n) : ∀ m : ℕ, p + 1 ≠ -(m : ℝ) := by
  intro m h
  apply hp (-(m : ℤ) - 1)
  push_cast
  linarith

/-- For `p` not an integer, both `J_p` and `J_{-p}` solve Bessel's equation of order `p` (note
`(-p)² = p²`) on `x > 0` (DE-213, first part; independence of the two is not proved here). -/
@[kb "lebldiffyqs2026" "Solutions of Bessel's equation, p. 348"]
theorem besselJR_pair_solve (p : ℝ) (hp : ∀ n : ℤ, p ≠ n) {x : ℝ} (hx : 0 < x) :
    (x ^ 2 * deriv (deriv (besselJR p)) x + x * deriv (besselJR p) x + (x ^ 2 - p ^ 2) * besselJR p x = 0) ∧
    (x ^ 2 * deriv (deriv (besselJR (-p))) x + x * deriv (besselJR (-p)) x +
      (x ^ 2 - p ^ 2) * besselJR (-p) x = 0) := by
  refine ⟨besselJR_solves_bessel p (hp_of_not_int hp) hx, ?_⟩
  have h := besselJR_solves_bessel (-p) (hp_of_not_int fun n h => hp (-n) (by push_cast; linarith)) hx
  simpa using h

/-- DE-215 (derivative of `J_0`): `J_0' = - J_1` on `x > 0`. -/
@[kb "lebldiffyqs2026" "Properties of Bessel functions, p. 349"]
theorem deriv_besselJR_zero {x : ℝ} (hx : 0 < x) : deriv (besselJR 0) x = - besselJR 1 x := by
  have hp0 := hp_of_nonneg (le_refl (0 : ℝ))
  have hp1 := hp_of_nonneg (zero_le_one' ℝ)
  rw [(hasDerivAt_besselJR 0 hp0 hx).deriv, besselJR_eq 1 x hx]
  unfold besselJ1
  simp only [zero_mul, zero_div, Real.rpow_zero, one_mul, zero_add, Real.rpow_one]
  have hR : 1 ≤ |x| + 1 := by linarith [abs_nonneg x]
  have s1 := summable1 (bcoef_hsum 0 hp0) (abs_lt_R x) hR
  unfold evS1 evS
  rw [s1.tsum_eq_zero_add, ← tsum_mul_left, ← tsum_neg]
  simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add]
  refine tsum_congr fun n => ?_
  have e2 : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
  have g1 : Real.Gamma (((n + 1 : ℕ) : ℝ) + 0 + 1) = ((n + 1).factorial : ℝ) := by
    rw [add_zero]; exact Real.Gamma_nat_eq_factorial (n + 1)
  have g2 : Real.Gamma ((n : ℝ) + 1 + 1) = ((n + 1).factorial : ℝ) := by
    have := Real.Gamma_nat_eq_factorial (n + 1); push_cast at this; exact this
  unfold bcoef
  rw [e2, g1, g2, pow_succ, pow_succ, pow_succ, Nat.factorial_succ]
  push_cast
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma bcoef_pred (p : ℝ) (hp : 0 < p) (n : ℕ) : bcoef (p - 1) n = ((n : ℝ) + p) * bcoef p n := by
  have hq : ∀ m : ℕ, p - 1 + 1 ≠ -(m : ℝ) := by
    intro m h; have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
  have hg := gamma_ne (p - 1) hq n
  have e1 : (n : ℝ) + (p - 1) + 1 = (n : ℝ) + p := by ring
  rw [e1] at hg
  have hne : (n : ℝ) + p ≠ 0 := by positivity
  unfold bcoef
  rw [e1, show (n : ℝ) + p + 1 = ((n : ℝ) + p) + 1 by ring, Real.Gamma_add_one hne]
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp

lemma bcoef_succ_shift (p : ℝ) (hp : ∀ m : ℕ, p + 1 ≠ -(m : ℝ)) (n : ℕ) :
    bcoef (p + 1) n = -4 * ((n : ℝ) + 1) * bcoef p (n + 1) := by
  have hq : ∀ m : ℕ, p + 1 + 1 ≠ -(m : ℝ) := by
    intro m h
    apply hp (m + 1)
    push_cast
    linarith
  have hg := gamma_ne (p + 1) hq n
  unfold bcoef
  rw [show ((n + 1 : ℕ) : ℝ) + p + 1 = (n : ℝ) + (p + 1) + 1 by push_cast; ring, Nat.factorial_succ]
  push_cast
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- Key identity for the recurrence: `2 p S_p = 2 S_{p-1} + (x²/2) S_{p+1}` for the even series. -/
lemma evS_recurrence (p : ℝ) (hp : 0 < p) (x : ℝ) :
    2 * p * evS (bcoef p) x = 2 * evS (bcoef (p - 1)) x + x ^ 2 / 2 * evS (bcoef (p + 1)) x := by
  have hp0 : ∀ m : ℕ, p + 1 ≠ -(m : ℝ) := hp_of_nonneg hp.le
  have hq : ∀ m : ℕ, p - 1 + 1 ≠ -(m : ℝ) := by
    intro m h; have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
  have hr : ∀ m : ℕ, p + 1 + 1 ≠ -(m : ℝ) := by
    intro m h; have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
  have hR : 1 ≤ |x| + 1 := by linarith [abs_nonneg x]
  have sA := summable0 (bcoef_hsum (p - 1) hq) (abs_lt_R x) hR
  have sB := summable0 (bcoef_hsum p hp0) (abs_lt_R x) hR
  have sC := summable0 (bcoef_hsum (p + 1) hr) (abs_lt_R x) hR
  set c : ℕ → ℝ := fun n => 2 * (bcoef (p - 1) n * x ^ (2 * n)) - 2 * p * (bcoef p n * x ^ (2 * n))
    with hc
  have sc : Summable c := (sA.mul_left 2).sub (sB.mul_left (2 * p))
  have e1 : 2 * evS (bcoef (p - 1)) x - 2 * p * evS (bcoef p) x = ∑' n, c n := by
    unfold evS
    rw [← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_sub (sA.mul_left 2) (sB.mul_left _)]
  have hc0 : c 0 = 0 := by
    simp only [hc, bcoef_pred p hp]
    simp
    ring
  have hcs : ∀ n : ℕ, c (n + 1) = - (x ^ 2 / 2 * (bcoef (p + 1) n * x ^ (2 * n))) := by
    intro n
    simp only [hc, bcoef_pred p hp, bcoef_succ_shift p hp0]
    push_cast
    rw [show 2 * (n + 1) = 2 * n + 2 by ring, pow_add]
    ring
  have e2 : ∑' n, c n = - (x ^ 2 / 2 * evS (bcoef (p + 1)) x) := by
    rw [sc.tsum_eq_zero_add, hc0, zero_add]
    unfold evS
    rw [← tsum_mul_left, ← tsum_neg]
    exact tsum_congr hcs
  linarith

/-- DE-215 (recurrence): `2 p J_p(x) = x (J_{p-1}(x) + J_{p+1}(x))` for real `p > 0`, `x > 0`
(the real series; for the complex function see `besselJ_recurrence_complex`). -/
@[kb "lebldiffyqs2026" "Properties of Bessel functions, p. 349"]
theorem besselJR_recurrence (p : ℝ) (hp : 0 < p) {x : ℝ} (hx : 0 < x) :
    2 * p * besselJR p x = x * (besselJR (p - 1) x + besselJR (p + 1) x) := by
  rw [besselJR_eq p x hx, besselJR_eq (p - 1) x hx, besselJR_eq (p + 1) x hx,
    Real.rpow_sub_one (by positivity), Real.rpow_add_one (by positivity)]
  have key := evS_recurrence p hp x
  have hx0 : x ≠ 0 := hx.ne'
  have ht : x * ((x / 2) ^ p / (x / 2)) = 2 * (x / 2) ^ p := by field_simp
  linear_combination (x / 2) ^ p * key - evS (bcoef (p - 1)) x * ht

/-- DE-213 (second part), complex version from Mathlib: `J_{-n} = (-1)^n J_n` for integer `n`. -/
@[kb "lebldiffyqs2026" "Solutions of Bessel's equation, p. 348"]
theorem besselJ_neg_int_complex (n : ℤ) (z : ℂ) :
    Complex.besselJ (-(n : ℂ)) z = (-1) ^ n * Complex.besselJ n z := by
  simpa using Complex.besselJ_neg_int n z

/-- DE-215 (recurrence), complex version from Mathlib: `2 a J_a = z (J_{a-1} + J_{a+1})`. -/
@[kb "lebldiffyqs2026" "Properties of Bessel functions, p. 349"]
theorem besselJ_recurrence_complex (a z : ℂ) :
    2 * a * Complex.besselJ a z = z * (Complex.besselJ (a - 1) z + Complex.besselJ (a + 1) z) := by
  rw [Complex.two_mul_self_mul_besselJ]; ring

/-- DE-213 (second part), real series: for a natural number `n` the series of order `-n` (with the
convention `1/Γ = 0` at the poles, as in the book) satisfies `J_{-n} = (-1)^n J_n` on `x > 0`. -/
@[kb "lebldiffyqs2026" "Solutions of Bessel's equation, p. 348"]
theorem besselJR_neg_nat (n : ℕ) {x : ℝ} (hx : 0 < x) :
    besselJR (-(n : ℝ)) x = (-1) ^ n * besselJR n x := by
  set f : ℕ → ℝ := fun k => (-1) ^ k / ((k.factorial : ℝ) * Real.Gamma ((k : ℝ) + -(n : ℝ) + 1)) *
    (x / 2) ^ (2 * (k : ℝ) + -(n : ℝ)) with hf
  set g : ℕ → ℝ := fun m => (-1) ^ m / ((m.factorial : ℝ) * Real.Gamma ((m : ℝ) + n + 1)) *
    (x / 2) ^ (2 * (m : ℝ) + n) with hg
  have hp0 := hp_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have sg : Summable g := by
    have := summable0 (bcoef_hsum n hp0) (abs_lt_R x) (by linarith [abs_nonneg x])
    have := this.mul_left ((x / 2) ^ (n : ℝ))
    exact this.congr fun m => (term_eq n x hx m).symm
  have hshift : ∀ m : ℕ, f (m + n) = (-1) ^ n * g m := by
    intro m
    have e1 : ((m + n : ℕ) : ℝ) + -(n : ℝ) + 1 = (m : ℝ) + 1 := by push_cast; ring
    have e2 : 2 * ((m + n : ℕ) : ℝ) + -(n : ℝ) = 2 * (m : ℝ) + n := by push_cast; ring
    have e3 : Real.Gamma ((m : ℝ) + n + 1) = ((m + n).factorial : ℝ) := by
      have := Real.Gamma_nat_eq_factorial (m + n); push_cast at this; exact this
    simp only [hf, hg]
    rw [e1, e2, Real.Gamma_nat_eq_factorial m, e3, pow_add]
    have h1 : (m.factorial : ℝ) ≠ 0 := by positivity
    have h2 : ((m + n).factorial : ℝ) ≠ 0 := by positivity
    field_simp
  have hzero : ∀ k ∈ Finset.range n, f k = 0 := by
    intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    have e : (k : ℝ) + -(n : ℝ) + 1 = -((n - k - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    simp only [hf]
    rw [e, Real.Gamma_neg_nat_eq_zero]
    simp
  have sf : Summable f := by
    rw [← summable_nat_add_iff n]
    exact (sg.mul_left ((-1) ^ n)).congr fun m => (hshift m).symm
  unfold besselJR
  rw [← sf.sum_add_tsum_nat_add n, Finset.sum_eq_zero hzero, zero_add, ← tsum_mul_left]
  exact tsum_congr hshift

end Bessel
