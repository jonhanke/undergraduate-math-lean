import UndergradKB.Common.Attr
import UndergradKB.DifferentialEquations.HigherOrderConstant
import UndergradKB.DifferentialEquations.BoundaryValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Complex roots of higher order, BVP eigenvalues, power series at an ordinary point (Lebl §2.3.2, §4.1, §7.2)

* complex characteristic roots `α + iβ` of multiplicity `m` give the real solutions
  `x^k e^{αx} cos βx`, `x^k e^{αx} sin βx`, `k < m` (real and imaginary parts of the complex solution);
* eigenvalues of the homogeneous Dirichlet problem `x'' + λ x = 0`: exactly `(kπ/L)²`;
* convergent power series solutions of `y'' - y = 0` and Airy's equation `y'' = x y`. -/

namespace UndergradKB.DifferentialEquations

open Polynomial Set

/-! ### Complex roots of the characteristic polynomial (DE-064) -/

/-- `q ↦ z q + q'` on complex polynomials. -/
noncomputable def hoc_Tc (z : ℂ) : Module.End ℂ ℂ[X] :=
  z • LinearMap.id + Polynomial.derivative

lemma hoc_Tc_apply (z : ℂ) (q : ℂ[X]) : hoc_Tc z q = z • q + derivative q := by
  simp [hoc_Tc]

/-- The complex derivative chain `x ↦ e^{zx} (T^j q)(x)` for real `x`. -/
noncomputable def hoc_cchain (z : ℂ) (q : ℂ[X]) (j : ℕ) (x : ℝ) : ℂ :=
  Complex.exp (z * x) * ((hoc_Tc z ^ j) q).eval (x : ℂ)

lemma hoc_cchain_hasDerivAt (z : ℂ) (q : ℂ[X]) (j : ℕ) (x : ℝ) :
    HasDerivAt (hoc_cchain z q j) (hoc_cchain z q (j + 1) x) x := by
  have h1 : HasDerivAt (fun w : ℂ => Complex.exp (z * w) * ((hoc_Tc z ^ j) q).eval w)
      (Complex.exp (z * x) * (hoc_Tc z ((hoc_Tc z ^ j) q)).eval (x : ℂ)) (x : ℂ) := by
    have := ((hasDerivAt_id (x : ℂ)).const_mul z).cexp.mul (((hoc_Tc z ^ j) q).hasDerivAt (x : ℂ))
    refine HasDerivAt.congr_deriv this ?_
    rw [hoc_Tc_apply]
    simp only [eval_add, eval_smul, smul_eq_mul, id]
    ring
  have := h1.comp_ofReal
  unfold hoc_cchain
  rw [pow_succ', mul_apply_eq_comp]
  exact this

lemma hoc_cchain_eq {n : ℕ} (a : Fin n → ℝ) (z : ℂ) (q : ℂ[X]) (x : ℝ) :
    hoc_cchain z q n x + ∑ k : Fin n, (a k : ℂ) * hoc_cchain z q k x =
      Complex.exp (z * x) *
        ((aeval (hoc_Tc z) ((hoc_charPoly a).map (algebraMap ℝ ℂ))) q).eval (x : ℂ) := by
  have h : (aeval (hoc_Tc z) ((hoc_charPoly a).map (algebraMap ℝ ℂ))) q =
      (hoc_Tc z ^ n) q + ∑ k : Fin n, (a k : ℂ) • (hoc_Tc z ^ (k : ℕ)) q := by
    simp [hoc_charPoly, Polynomial.map_add, Polynomial.map_sum, map_sum, LinearMap.sum_apply,
      aeval_X_pow]
  rw [h]
  simp only [hoc_cchain, eval_add, eval_finsetSum, eval_smul, smul_eq_mul, mul_add, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

lemma hoc_cchain_solves {n : ℕ} (a : Fin n → ℝ) (z : ℂ) (q : ℂ[X])
    (h0 : ∀ x : ℝ, ((aeval (hoc_Tc z) ((hoc_charPoly a).map (algebraMap ℝ ℂ))) q).eval (x : ℂ) = 0)
    (φ : ℂ →L[ℝ] ℝ) :
    SolvesLinN (fun j _ => a j) 0 univ (fun (j : Fin (n + 1)) x => φ (hoc_cchain z q j x)) := by
  refine ⟨fun k t _ => ?_, fun x _ => ?_⟩
  · have := φ.hasFDerivAt.comp_hasDerivAt t (hoc_cchain_hasDerivAt z q k t)
    simpa [Function.comp_def] using this
  · have e := hoc_cchain_eq a z q x
    rw [h0 x, mul_zero] at e
    have e2 := congrArg φ e
    rw [map_add, map_sum, map_zero] at e2
    simp only [Fin.val_last, Fin.val_castSucc, Pi.zero_apply]
    rw [← e2]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    have : ((a k : ℂ) * hoc_cchain z q k x) = (a k) • hoc_cchain z q k x := by
      rw [Complex.real_smul]
    rw [this, map_smul, smul_eq_mul]

/-- **Complex roots of higher multiplicity** (Lebl, §2.3.2): if the real characteristic polynomial of
`y⁽ⁿ⁾ + ∑ aₖ y⁽ᵏ⁾ = 0` is divisible by `(X - (α + iβ))^m` over `ℂ`, then for every `k < m` both
`x^k e^{αx} cos βx` and `x^k e^{αx} sin βx` (with their derivative chains `D₁`, `D₂`, the real and imaginary
parts of the complex chain) solve the equation. (DE-064) -/
@[kb "lebldiffyqs2026" "§2.3.2 constant-coefficient higher-order, p. 92"]
theorem hoc_complex_root_solves {n : ℕ} (a : Fin n → ℝ) (α β : ℝ) (m : ℕ)
    (hdvd : (X - C ((α : ℂ) + β * Complex.I)) ^ m ∣ (hoc_charPoly a).map (algebraMap ℝ ℂ))
    {k : ℕ} (hk : k < m) :
    ∃ D₁ D₂ : Fin (n + 1) → ℝ → ℝ,
      SolvesLinN (fun j _ => a j) 0 univ D₁ ∧ SolvesLinN (fun j _ => a j) 0 univ D₂ ∧
      D₁ 0 = (fun x => x ^ k * (Real.exp (α * x) * Real.cos (β * x))) ∧
      D₂ 0 = (fun x => x ^ k * (Real.exp (α * x) * Real.sin (β * x))) := by
  set z : ℂ := (α : ℂ) + β * Complex.I with hz
  have h0 : ∀ x : ℝ, ((aeval (hoc_Tc z) ((hoc_charPoly a).map (algebraMap ℝ ℂ))) (X ^ k)).eval
      (x : ℂ) = 0 := by
    obtain ⟨s, hs⟩ := hdvd
    have hD : aeval (hoc_Tc z) (X - C z) = Polynomial.derivative := by
      refine LinearMap.ext fun q => ?_
      simp [hoc_Tc_apply]
    have : (aeval (hoc_Tc z) ((hoc_charPoly a).map (algebraMap ℝ ℂ))) (X ^ k) = 0 := by
      rw [hs, mul_comm, map_mul, map_pow (aeval (hoc_Tc z)), hD, mul_apply_eq_comp,
        pow_apply_eq_iterate,iterate_derivative_eq_zero (by simpa using hk)]
      simp
    intro x
    rw [this]; simp
  have hre : (Complex.reCLM : ℂ →L[ℝ] ℝ) = Complex.reCLM := rfl
  refine ⟨fun j x => Complex.reCLM (hoc_cchain z (X ^ k) j x),
    fun j x => Complex.imCLM (hoc_cchain z (X ^ k) j x),
    hoc_cchain_solves a z _ h0 _, hoc_cchain_solves a z _ h0 _, ?_, ?_⟩
  · funext x
    have e : hoc_cchain z (X ^ k) 0 x = ((x ^ k : ℝ) : ℂ) * Complex.exp (z * x) := by
      simp [hoc_cchain, mul_comm]
    simp only [Fin.val_zero, e, Complex.reCLM_apply, Complex.re_ofReal_mul, Complex.exp_re]
    simp [hz]
  · funext x
    have e : hoc_cchain z (X ^ k) 0 x = ((x ^ k : ℝ) : ℂ) * Complex.exp (z * x) := by
      simp [hoc_cchain, mul_comm]
    simp only [Fin.val_zero, e, Complex.imCLM_apply, Complex.im_ofReal_mul, Complex.exp_im]
    simp [hz]

/-! ### Eigenvalues of homogeneous boundary value problems (DE-114) -/

/-- `lam` is an eigenvalue of the homogeneous Dirichlet problem `x'' + λ x = 0`, `x(a) = x(b) = 0`: there is
a nonzero (on `[a,b]`) solution, the eigenfunction. -/
def IsBVPEigenvalue (lam a b : ℝ) : Prop :=
  ∃ x, BVPHom lam a b x ∧ ∃ t ∈ Icc a b, x t ≠ 0

/-- **Dirichlet eigenvalues on `[0, L]`** (Lebl §4.1): the eigenvalues of `x'' + λ x = 0`, `x(0) = x(L) = 0`
are exactly `(kπ/L)²`, `k ≥ 1`, with eigenfunctions `sin (kπ t / L)`. (DE-114) -/
@[kb "lebldiffyqs2026" "§4.1 eigenvalue problem, p. 190"]
theorem isBVPEigenvalue_iff {L : ℝ} (hL : 0 < L) (lam : ℝ) :
    IsBVPEigenvalue lam 0 L ↔ ∃ n : ℕ, 0 < n ∧ lam = (n * Real.pi / L) ^ 2 := by
  constructor
  · rintro ⟨x, ⟨hx, hode, h0, hxL⟩, hne⟩
    rcases le_or_gt lam 0 with hl | hl
    · exfalso
      obtain ⟨t, ht, hxt⟩ := hne
      exact hxt (dirichlet_eq_zero_of_nonpos hl hx hode h0 hxL t ht)
    · exact dirichlet_eigenvalue_of_pos hL hl hx hode h0 hxL hne
  · rintro ⟨n, hn, rfl⟩
    obtain ⟨h1, h2, h3, h4, t, ht⟩ := sin_dirichlet_eigenfunction hL hn
    refine ⟨fun t => Real.sin (n * Real.pi / L * t), ⟨h1, fun t _ => h2 t, h3, h4⟩, ?_⟩
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have key : (n : ℝ) * Real.pi / L * (L / (2 * n)) = Real.pi / 2 := by
      field_simp
    refine ⟨L / (2 * n), ⟨by positivity, ?_⟩, ?_⟩
    · have h1n : (1 : ℝ) ≤ n := by exact_mod_cast hn
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    · simp only [key, Real.sin_pi_div_two]
      norm_num

/-! ### Power series solutions at an ordinary point (DE-202) -/

/-- The coefficients of the power series solution of `y'' - y = 0`: `a_{2j} = a₀/(2j)!`, `a_{2j+1} = a₁/(2j+1)!`. -/
noncomputable def coshCoeff (a0 a1 : ℝ) (k : ℕ) : ℝ :=
  if Even k then a0 / (k.factorial : ℝ) else a1 / (k.factorial : ℝ)

/-- The coefficients `coshCoeff` satisfy the recurrence `a_{k+2} = a_k / ((k+2)(k+1))`. -/
lemma coshCoeff_rec (a0 a1 : ℝ) (k : ℕ) :
    coshCoeff a0 a1 (k + 2) * (((k : ℝ) + 2) * ((k : ℝ) + 1)) = coshCoeff a0 a1 k := by
  have hf : ((k + 2).factorial : ℝ) = ((k : ℝ) + 2) * ((k : ℝ) + 1) * (k.factorial : ℝ) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
  have hpos : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  unfold coshCoeff
  have hp : Even (k + 2) ↔ Even k := by simp [Nat.even_add]
  by_cases h : Even k
  · rw [if_pos (hp.2 h), if_pos h, hf]; field_simp
  · rw [if_neg (fun h' => h (hp.1 h')), if_neg h, hf]; field_simp

/-- **Power series method for `y'' - y = 0`** (Lebl, Example 7.2.1): the series `∑ a_k x^k` with
`a_{k+2} = a_k/((k+2)(k+1))` (and `a₀`, `a₁` free) converges for every `x`, and its sum is
`a₀ cosh x + a₁ sinh x`. (DE-202) -/
@[kb "lebldiffyqs2026" "Example 7.2.1, p. 335"]
theorem coshCoeff_hasSum (a0 a1 x : ℝ) :
    HasSum (fun k => coshCoeff a0 a1 k * x ^ k) (a0 * Real.cosh x + a1 * Real.sinh x) := by
  refine HasSum.even_add_odd ?_ ?_
  · have := (Real.hasSum_cosh x).mul_left a0
    convert this using 1
    funext k
    simp [coshCoeff]
    ring
  · have := (Real.hasSum_sinh x).mul_left a1
    convert this using 1
    funext k
    simp [coshCoeff]
    ring

/-- The termwise-differentiated coefficient sequence `n ↦ (n+1) c_{n+1}`. -/
def psDer (c : ℕ → ℝ) (n : ℕ) : ℝ := ((n : ℝ) + 1) * c (n + 1)

lemma ps_H_of {c : ℕ → ℝ} (F : ℕ → ℝ) (hF : ∀ k : ℕ, (k : ℝ) + 1 ≤ F k)
    (h : ∀ k, c k = F k * c (k + 3)) (k : ℕ) : ((k : ℝ) + 1) * |c (k + 3)| ≤ |c k| := by
  have h0 : 0 < F k := lt_of_lt_of_le (by positivity) (hF k)
  rw [h k, abs_mul, abs_of_pos h0]
  exact mul_le_mul_of_nonneg_right (hF k) (abs_nonneg _)

/-- A coefficient sequence with `(k+1)|c_{k+3}| ≤ |c_k|` has a series converging absolutely for all `x`. -/
lemma ps_summable {c : ℕ → ℝ} (hc : ∀ k : ℕ, ((k : ℝ) + 1) * |c (k + 3)| ≤ |c k|) (ρ : ℝ)
    (hρ : 0 ≤ ρ) : Summable (fun n => |c n| * ρ ^ n) := by
  set t : ℕ → ℝ := fun n => |c n| * ρ ^ n with ht
  have ht0 : ∀ n, 0 ≤ t n := fun n => by positivity
  have step : ∀ k : ℕ, 2 * ρ ^ 3 ≤ (k : ℝ) + 1 → 2 * t (k + 3) ≤ t k := by
    intro k hk
    have h1 : 2 * ρ ^ 3 * |c (k + 3)| ≤ |c k| :=
      le_trans (mul_le_mul_of_nonneg_right hk (abs_nonneg _)) (hc k)
    have h2 := mul_le_mul_of_nonneg_right h1 (pow_nonneg hρ k)
    simp only [ht]
    calc 2 * (|c (k + 3)| * ρ ^ (k + 3)) = 2 * ρ ^ 3 * |c (k + 3)| * ρ ^ k := by ring
      _ ≤ |c k| * ρ ^ k := h2
  set s : ℕ → ℝ := fun j => t (3 * j) + t (3 * j + 1) + t (3 * j + 2) with hs
  have hs0 : ∀ j, 0 ≤ s j := fun j => by simp only [hs]; have := ht0 (3 * j); have := ht0 (3 * j + 1); have := ht0 (3 * j + 2); linarith
  have hsum : Summable s := by
    refine summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num) ?_
    rw [Filter.eventually_atTop]
    refine ⟨⌈ρ ^ 3⌉₊, fun j hj => ?_⟩
    have hj' : ρ ^ 3 ≤ j := le_trans (Nat.le_ceil _) (by exact_mod_cast hj)
    have e0 := step (3 * j) (by push_cast; linarith [pow_nonneg hρ 3])
    have e1 := step (3 * j + 1) (by push_cast; linarith [pow_nonneg hρ 3])
    have e2 := step (3 * j + 2) (by push_cast; linarith [pow_nonneg hρ 3])
    have a0 : 3 * (j + 1) = 3 * j + 3 := by ring
    have a1 : 3 * (j + 1) + 1 = 3 * j + 1 + 3 := by ring
    have a2 : 3 * (j + 1) + 2 = 3 * j + 2 + 3 := by ring
    rw [Real.norm_of_nonneg (hs0 _), Real.norm_of_nonneg (hs0 _)]
    simp only [hs, a0, a1, a2]
    linarith
  have hpart : ∀ J, ∑ i ∈ Finset.range (3 * J), t i = ∑ j ∈ Finset.range J, s j := by
    intro J
    induction J with
    | zero => simp
    | succ J ih =>
      have : 3 * (J + 1) = 3 * J + 1 + 1 + 1 := by ring
      rw [this, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih,
        Finset.sum_range_succ]
      simp only [hs]; ring
  refine summable_of_sum_range_le (c := ∑' j, s j) ht0 fun N => ?_
  calc ∑ i ∈ Finset.range N, t i ≤ ∑ i ∈ Finset.range (3 * N), t i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) fun i _ _ => ht0 i
    _ = ∑ j ∈ Finset.range N, s j := hpart N
    _ ≤ ∑' j, s j := hsum.sum_le_tsum _ fun j _ => hs0 j

/-- Termwise differentiation of a power series with infinite radius of convergence. -/
lemma ps_hasDerivAt {c : ℕ → ℝ} (h1 : ∀ ρ : ℝ, 0 ≤ ρ → Summable fun n => |c n| * ρ ^ n)
    (h2 : ∀ ρ : ℝ, 0 ≤ ρ → Summable fun n : ℕ => |psDer c n| * ρ ^ n) (x : ℝ) :
    HasDerivAt (fun x => ∑' n, c n * x ^ n) (∑' n, psDer c n * x ^ n) x := by
  set R : ℝ := |x| + 1 with hR
  have hR0 : 0 < R := by positivity
  set u : ℕ → ℝ := fun n => |(n : ℝ) * c n| * R ^ (n - 1) with hu
  have hus : Summable u := by
    rw [← summable_nat_add_iff 1]
    refine (h2 R hR0.le).congr fun n => ?_
    simp only [hu, psDer, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  have hg : ∀ n (y : ℝ), y ∈ Metric.ball (0 : ℝ) R →
      HasDerivAt (fun y => c n * y ^ n) (c n * ((n : ℝ) * y ^ (n - 1))) y :=
    fun n y _ => (hasDerivAt_pow n y).const_mul (c n)
  have hg' : ∀ n (y : ℝ), y ∈ Metric.ball (0 : ℝ) R → ‖c n * ((n : ℝ) * y ^ (n - 1))‖ ≤ u n := by
    intro n y hy
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hy
    have : |y| ^ (n - 1) ≤ R ^ (n - 1) := pow_le_pow_left₀ (abs_nonneg _) hy.le _
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, hu]
    simp only [Nat.abs_cast]
    calc |c n| * ((n : ℝ) * |y| ^ (n - 1)) = ((n : ℝ) * |c n|) * |y| ^ (n - 1) := by ring
      _ ≤ ((n : ℝ) * |c n|) * R ^ (n - 1) := by gcongr
      _ = _ := by rw [abs_mul, Nat.abs_cast]
  have hg0 : Summable fun n => c n * (0 : ℝ) ^ n :=
    Summable.of_norm_bounded (h1 0 le_rfl) fun n => by simp [abs_mul]
  have hx : x ∈ Metric.ball (0 : ℝ) R := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]; linarith
  have key := hasDerivAt_tsum_of_isPreconnected hus Metric.isOpen_ball (convex_ball _ _).isPreconnected
    hg hg' (Metric.mem_ball_self hR0) hg0 hx
  convert key using 1
  have hsm : Summable fun n : ℕ => c n * ((n : ℝ) * x ^ (n - 1)) :=
    Summable.of_norm_bounded hus fun n => hg' n x hx
  rw [hsm.tsum_eq_zero_add]
  simp only [psDer, Nat.cast_zero, zero_mul, mul_zero, zero_add, Nat.add_sub_cancel, Nat.cast_add,
    Nat.cast_one]
  congr 1
  funext n
  ring

/-- **Airy's equation by power series** (Lebl, Example 7.2.2): let `a₀, a₁` be arbitrary, `a₂ = 0`, and
`a_{k+3} = a_k/((k+3)(k+2))`. Then for every `x` the series `y(x) = ∑ a_k x^k` converges, `y` is differentiable
with derivative `y₁(x) = ∑ (k+1) a_{k+1} x^k`, and `y₁` is differentiable with `y₁'(x) = x y(x)`, i.e.
`y'' = x y` on all of `ℝ`. (DE-202) -/
@[kb "lebldiffyqs2026" "Example 7.2.2, p. 336"]
theorem airy_power_series (a : ℕ → ℝ) (h2 : a 2 = 0)
    (hrec : ∀ k : ℕ, a (k + 3) * (((k : ℝ) + 3) * ((k : ℝ) + 2)) = a k) :
    (∀ x, Summable fun n => a n * x ^ n) ∧
    (∀ x, HasDerivAt (fun x => ∑' n, a n * x ^ n) (∑' n, psDer a n * x ^ n) x) ∧
    (∀ x, HasDerivAt (fun x => ∑' n, psDer a n * x ^ n) (x * ∑' n, a n * x ^ n) x) := by
  have Ha : ∀ k : ℕ, ((k : ℝ) + 1) * |a (k + 3)| ≤ |a k| := by
    refine ps_H_of (fun k => ((k : ℝ) + 3) * ((k : ℝ) + 2)) (fun k => ?_) (fun k => ?_)
    · nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    · exact (hrec k).symm.trans (mul_comm _ _)
  have Hb : ∀ k : ℕ, ((k : ℝ) + 1) * |psDer a (k + 3)| ≤ |psDer a k| := by
    refine ps_H_of (fun k => ((k : ℝ) + 3) * ((k : ℝ) + 1)) (fun k => ?_) (fun k => ?_)
    · nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    · have := hrec (k + 1)
      simp only [psDer]
      push_cast at this ⊢
      have e : a (k + 1 + 3) = a (k + 4) := rfl
      rw [e] at this
      rw [← this]; ring
  have Hd : ∀ k : ℕ, ((k : ℝ) + 1) * |psDer (psDer a) (k + 3)| ≤ |psDer (psDer a) k| := by
    refine ps_H_of (fun k => ((k : ℝ) + 1) * ((k : ℝ) + 2)) (fun k => ?_) (fun k => ?_)
    · nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    · have := hrec (k + 2)
      simp only [psDer]
      push_cast at this ⊢
      have e : a (k + 2 + 3) = a (k + 5) := rfl
      rw [e] at this
      have e2 : a (k + 1 + 1) = a (k + 2) := rfl
      rw [e2, ← this]; ring
  have Sa := ps_summable Ha
  have Sb := ps_summable Hb
  have Sd := ps_summable Hd
  refine ⟨fun x => Summable.of_norm_bounded (Sa |x| (abs_nonneg x)) fun n => by simp [abs_mul], fun x => ps_hasDerivAt Sa Sb x, fun x => ?_⟩
  have h := ps_hasDerivAt (c := psDer a) Sb Sd x
  convert h using 1
  have hsd : Summable fun n => psDer (psDer a) n * x ^ n :=
    Summable.of_norm_bounded (Sd |x| (abs_nonneg x)) fun n => by simp [abs_mul]
  rw [hsd.tsum_eq_zero_add, ← tsum_mul_left]
  have d0 : psDer (psDer a) 0 = 0 := by simp [psDer, h2]
  have d1 : ∀ n : ℕ, psDer (psDer a) (n + 1) = a n := by
    intro n
    have := hrec n
    simp only [psDer]
    push_cast
    have e : a (n + 1 + 1) = a (n + 2) := rfl
    have e3 : a (n + 1 + 1 + 1) = a (n + 3) := rfl
    rw [← this, e3]
    ring
  simp only [d0, d1, zero_mul, zero_add, pow_succ]
  congr 1
  funext n
  ring

end UndergradKB.DifferentialEquations
