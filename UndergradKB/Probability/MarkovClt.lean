import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.Distributions.Gaussian.Real
import UndergradKB.Common.Attr
import UndergradKB.Probability.MarkovBasic
import UndergradKB.Probability.MarkovRegular
import UndergradKB.Probability.MarkovPassage
import UndergradKB.Probability.MarkovLLN

/-! # Central limit theorem for ergodic Markov chains (Grinstead–Snell, Theorem 11.17)

For an ergodic chain with fixed probability vector `w` and fundamental matrix `Z = (I - P + W)⁻¹`, the number of
visits `S_j^(n)` to the state `j` (at the times `0, …, n`) satisfies
`P(r < (S_j^(n) - n w_j) / √(n σ_j²) < s) → ∫_r^s φ` with `σ_j² = 2 w_j z_jj - w_j - w_j²` (equation 11.10),
for every initial distribution, provided `σ_j² > 0`.

The proof works on the finite path space of `MarkovBasic` and needs neither eigenvalue perturbation nor a
martingale central limit theorem. With `f = 1_j - w_j`:

* the characteristic function `E exp(iθ ∑_{k ≤ n} f(X_k))` equals `∑_m u_m e^{iθ f_m} (A_θ^n 1)_m`, where
  `(A_θ φ)_m = ∑_l P_ml e^{iθ f_l} φ_l` is the transition operator twisted by `e^{iθ f}` (`path_twist`);
* `A_θ` does not increase the sup norm (`norm_twist_le`);
* two Poisson equations `g = P(f + g)` and `b - σ²/2 = P(b - f g - f²/2)` (solved by the fundamental matrix)
  make `φ_θ = 1 + iθ g + θ² b` an approximate eigenvector: `‖A_θ φ_θ - (1 - θ²σ²/2) φ_θ‖ ≤ K |θ|³`
  (`twist_approx_eigen`);
* hence `A_θ^n 1 = (1 - θ²σ²/2)^n + O(|θ| + n|θ|³)`, and at `θ = s/√n` this tends to `exp(-s²σ²/2)`;
* Lévy's continuity theorem (Mathlib) and the portmanteau theorem give the interval probabilities.
-/

open Finset Filter Topology Matrix Complex MeasureTheory ProbabilityTheory

namespace UndergradKB.Probability

namespace MarkovClt

variable {S : Type*} [Fintype S] [DecidableEq S]

/-! ## The twisted transition operator -/

/-- The transition operator twisted by `e^{iθ f}`: `(A_θ φ)_m = ∑_l P_ml e^{iθ f_l} φ_l`. -/
noncomputable def twist (P : Matrix S S ℝ) (f : S → ℝ) (θ : ℝ) (φ : S → ℂ) : S → ℂ :=
  fun m => ∑ l, (P m l : ℂ) * (cexp (θ * f l * I) * φ l)

theorem norm_cexp_mul_I (x : ℝ) : ‖cexp (x * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I x

theorem norm_exp_twist (θ y : ℝ) : ‖cexp (θ * y * I)‖ = 1 := by
  have : (θ * y * I : ℂ) = ((θ * y : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

theorem norm_twist_apply_le {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) (f : S → ℝ) (θ : ℝ)
    (φ : S → ℂ) (m : S) : ‖twist P f θ φ m‖ ≤ ‖φ‖ := by
  unfold twist
  calc ‖∑ l, (P m l : ℂ) * (cexp (θ * f l * I) * φ l)‖
      ≤ ∑ l, ‖(P m l : ℂ) * (cexp (θ * f l * I) * φ l)‖ := norm_sum_le _ _
    _ ≤ ∑ l, P m l * ‖φ‖ := by
        refine sum_le_sum fun l _ => ?_
        rw [norm_mul, norm_mul, norm_exp_twist, one_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (nonneg_of_mem_rowStochastic hP)]
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm φ l) (nonneg_of_mem_rowStochastic hP)
    _ = ‖φ‖ := by rw [← sum_mul, sum_row_of_mem_rowStochastic hP m, one_mul]

/-- The twisted operator does not increase the sup norm. -/
theorem norm_twist_le {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) (f : S → ℝ) (θ : ℝ)
    (φ : S → ℂ) : ‖twist P f θ φ‖ ≤ ‖φ‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg φ)).2 fun m => norm_twist_apply_le hP f θ φ m

omit [DecidableEq S] in
theorem twist_sub (P : Matrix S S ℝ) (f : S → ℝ) (θ : ℝ) (φ ψ : S → ℂ) :
    twist P f θ (φ - ψ) = twist P f θ φ - twist P f θ ψ := by
  funext m; simp only [twist, Pi.sub_apply, ← sum_sub_distrib]
  exact sum_congr rfl fun l _ => by ring

omit [DecidableEq S] in
theorem twist_smul (P : Matrix S S ℝ) (f : S → ℝ) (θ : ℝ) (c : ℂ) (φ : S → ℂ) :
    twist P f θ (c • φ) = c • twist P f θ φ := by
  funext m; simp only [twist, Pi.smul_apply, smul_eq_mul, mul_sum]
  exact sum_congr rfl fun l _ => by ring

theorem twist_iterate_sub (P : Matrix S S ℝ) (f : S → ℝ) (θ : ℝ) (n : ℕ) (φ ψ : S → ℂ) :
    (twist P f θ)^[n] (φ - ψ) = (twist P f θ)^[n] φ - (twist P f θ)^[n] ψ := by
  induction n generalizing φ ψ with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply, twist_sub, ih]

theorem twist_iterate_smul (P : Matrix S S ℝ) (f : S → ℝ) (θ : ℝ) (n : ℕ) (c : ℂ) (φ : S → ℂ) :
    (twist P f θ)^[n] (c • φ) = c • (twist P f θ)^[n] φ := by
  induction n generalizing φ with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply, twist_smul, ih]

theorem norm_twist_iterate_le {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) (f : S → ℝ) (θ : ℝ)
    (n : ℕ) (φ : S → ℂ) : ‖(twist P f θ)^[n] φ‖ ≤ ‖φ‖ := by
  induction n generalizing φ with
  | zero => exact le_rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact (ih _).trans (norm_twist_le hP f θ φ)

/-- Iterating an approximate eigenvector: if `A φ = λ φ + ε` with `‖λ‖ ≤ 1`, then
`‖A^n φ - λ^n φ‖ ≤ n ‖ε‖`. -/
theorem norm_iterate_sub_pow_le {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) (f : S → ℝ) (θ : ℝ)
    (φ : S → ℂ) (c : ℂ) (hc : ‖c‖ ≤ 1) (n : ℕ) :
    ‖(twist P f θ)^[n] φ - c ^ n • φ‖ ≤ n * ‖twist P f θ φ - c • φ‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (twist P f θ)^[n + 1] φ - c ^ (n + 1) • φ =
        twist P f θ ((twist P f θ)^[n] φ - c ^ n • φ) + c ^ n • (twist P f θ φ - c • φ) := by
      rw [Function.iterate_succ_apply', twist_sub, twist_smul, smul_sub, pow_succ, mul_smul]
      abel
    rw [e]
    calc ‖twist P f θ ((twist P f θ)^[n] φ - c ^ n • φ) + c ^ n • (twist P f θ φ - c • φ)‖
        ≤ ‖(twist P f θ)^[n] φ - c ^ n • φ‖ + ‖c‖ ^ n * ‖twist P f θ φ - c • φ‖ := by
          refine (norm_add_le _ _).trans (add_le_add (norm_twist_le hP f θ _) ?_)
          rw [norm_smul, norm_pow]
      _ ≤ n * ‖twist P f θ φ - c • φ‖ + 1 * ‖twist P f θ φ - c • φ‖ := by
          gcongr
          exact pow_le_one₀ (norm_nonneg _) hc
      _ = ((n + 1 : ℕ) : ℝ) * ‖twist P f θ φ - c • φ‖ := by push_cast; ring

/-! ## Characteristic functions on the path space -/

omit [DecidableEq S] in
theorem sum_paths_succ_complex (n : ℕ) (F : (Fin (n + 2) → S) → ℂ) :
    ∑ x : Fin (n + 2) → S, F x = ∑ y : Fin (n + 1) → S, ∑ s : S, F (Fin.snoc y s) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 2) => S)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Fin.snocEquiv_apply]

/-- The path expectation of `∏_k c(X_k) · φ(X_n)` through the twisted operator. -/
theorem path_twist (u : S → ℝ) (P : Matrix S S ℝ) (f : S → ℝ) (θ : ℝ) (n : ℕ) (φ : S → ℂ) :
    ∑ x : Fin (n + 1) → S, (pathProb u P n x : ℂ) *
        ((∏ k : Fin (n + 1), cexp (θ * f (x k) * I)) * φ (x (Fin.last n))) =
      ∑ m, (u m : ℂ) * (cexp (θ * f m * I) * (twist P f θ)^[n] φ m) := by
  induction n generalizing φ with
  | zero =>
    rw [← (Equiv.funUnique (Fin 1) S).symm.sum_comp]
    refine sum_congr rfl fun m _ => ?_
    simp [pathProb, Fin.last]
  | succ n ih =>
    rw [sum_paths_succ_complex, Function.iterate_succ_apply, ← ih]
    refine sum_congr rfl fun y _ => ?_
    simp only [pathProb_snoc, Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, twist,
      mul_sum]
    refine sum_congr rfl fun s _ => ?_
    push_cast
    ring

/-! ## The approximate eigenvector -/

/-- Third-order Taylor bound for `e^{ix}`. -/
theorem norm_exp_I_sub_taylor_le {x : ℝ} (hx : |x| ≤ 1) :
    ‖cexp (x * I) - (1 + x * I - x ^ 2 / 2)‖ ≤ |x| ^ 3 := by
  have hy : ‖(x * I : ℂ)‖ ≤ 1 := by simpa using hx
  have hb := Complex.exp_bound hy (n := 3) (by norm_num)
  have hs : ∑ m ∈ Finset.range 3, (x * I : ℂ) ^ m / (m.factorial : ℂ) = 1 + x * I - x ^ 2 / 2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    simp [Nat.factorial]
    ring_nf
    simp [Complex.I_sq]
    ring
  rw [hs] at hb
  refine hb.trans ?_
  have hn : ‖(x * I : ℂ)‖ = |x| := by simp [Complex.norm_mul]
  rw [hn]
  have hc : ((3 : ℕ).succ : ℝ) * ((Nat.factorial 3 : ℕ) * (3 : ℕ) : ℝ)⁻¹ = 2 / 9 := by
    norm_num [Nat.factorial]
  rw [hc]
  nlinarith [pow_nonneg (abs_nonneg x) 3]

/-- The approximate eigenvector `φ_θ = 1 + iθ g + θ² b`. -/
noncomputable def phiV (g b : S → ℝ) (θ : ℝ) : S → ℂ :=
  fun m => 1 + (θ * g m : ℝ) * I + ((θ ^ 2 * b m : ℝ) : ℂ)

omit [Fintype S] [DecidableEq S] in
theorem norm_phiV_sub_one_le {g b : S → ℝ} {M θ : ℝ} (hgM : ∀ l, |g l| ≤ M) (hbM : ∀ l, |b l| ≤ M)
    (hθ1 : |θ| ≤ 1) (m : S) : ‖phiV g b θ m - 1‖ ≤ 2 * |θ| * M := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hgM m)
  have e : phiV g b θ m - 1 = (θ * g m : ℝ) * I + ((θ ^ 2 * b m : ℝ) : ℂ) := by
    simp only [phiV]; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_mul, abs_mul, abs_pow]
  have h1 : |θ| * |g m| ≤ |θ| * M := by gcongr; exact hgM m
  have h2 : |θ| ^ 2 * |b m| ≤ |θ| * M := by
    calc |θ| ^ 2 * |b m| ≤ |θ| ^ 2 * M := by gcongr; exact hbM m
      _ = |θ| * (|θ| * M) := by ring
      _ ≤ |θ| * (1 * M) := by gcongr
      _ = |θ| * M := by ring
  linarith

/-- The approximate eigenvector estimate: if `g = P(f + g)` and `b - σ²/2 = P(b - f g - f²/2)`, then
`‖A_θ φ_θ - (1 - θ²σ²/2) φ_θ‖ ≤ 7 M³ |θ|³` for `|θ| M ≤ 1`, `M` a common bound. -/
theorem twist_approx_eigen {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) {f g b : S → ℝ} {σ2 M : ℝ}
    (hg : ∀ m, g m = ∑ l, P m l * (f l + g l))
    (hb : ∀ m, b m - σ2 / 2 = ∑ l, P m l * (b l - f l * g l - f l ^ 2 / 2))
    (hM1 : 1 ≤ M) (hfM : ∀ l, |f l| ≤ M) (hgM : ∀ l, |g l| ≤ M) (hbM : ∀ l, |b l| ≤ M)
    (hσ0 : 0 ≤ σ2) (hσM : σ2 ≤ M) {θ : ℝ} (hθ : |θ| * M ≤ 1) :
    ‖twist P f θ (phiV g b θ) - ((1 - θ ^ 2 * σ2 / 2 : ℝ) : ℂ) • phiV g b θ‖ ≤ 7 * M ^ 3 * |θ| ^ 3 := by
  have hM0 : 0 ≤ M := by linarith
  have ht0 : 0 ≤ |θ| := abs_nonneg θ
  have hθ1 : |θ| ≤ 1 := by nlinarith
  have hM23 : M ^ 2 ≤ M ^ 3 := by nlinarith
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun m => ?_
  -- the second-order Taylor polynomial of `e_l φ_l`
  set Q : S → ℂ := fun l => 1 + (θ * (f l + g l) : ℝ) * I +
    ((θ ^ 2 * (b l - f l * g l - f l ^ 2 / 2) : ℝ) : ℂ) with hQ
  have hsumP : ∑ l, (P m l : ℂ) = 1 := by
    rw [← Complex.ofReal_sum, sum_row_of_mem_rowStochastic hP m]; simp
  have hPQ : ∑ l, (P m l : ℂ) * Q l = 1 + (θ * g m : ℝ) * I + ((θ ^ 2 * (b m - σ2 / 2) : ℝ) : ℂ) := by
    have h1 : ∑ l, (P m l : ℂ) * ((θ * (f l + g l) : ℝ) * I) = (θ * g m : ℝ) * I := by
      rw [hg m, mul_sum, Complex.ofReal_sum, sum_mul]
      exact sum_congr rfl fun l _ => by push_cast; ring
    have h2 : ∑ l, (P m l : ℂ) * ((θ ^ 2 * (b l - f l * g l - f l ^ 2 / 2) : ℝ) : ℂ) =
        ((θ ^ 2 * (b m - σ2 / 2) : ℝ) : ℂ) := by
      rw [hb m, mul_sum, Complex.ofReal_sum]
      exact sum_congr rfl fun l _ => by push_cast; ring
    have hl : ∀ l, (P m l : ℂ) * Q l = (P m l : ℂ) + (P m l : ℂ) * ((θ * (f l + g l) : ℝ) * I) +
        (P m l : ℂ) * ((θ ^ 2 * (b l - f l * g l - f l ^ 2 / 2) : ℝ) : ℂ) := fun l => by
      simp only [hQ]; ring
    rw [sum_congr rfl fun l _ => hl l, sum_add_distrib, sum_add_distrib, hsumP, h1, h2]
  have hsplit : twist P f θ (phiV g b θ) m - (((1 - θ ^ 2 * σ2 / 2 : ℝ) : ℂ) • phiV g b θ) m =
      ∑ l, (P m l : ℂ) * (cexp (θ * f l * I) * phiV g b θ l - Q l) +
        ((θ ^ 2 * σ2 / 2 : ℝ) : ℂ) * ((θ * g m : ℝ) * I + ((θ ^ 2 * b m : ℝ) : ℂ)) := by
    have : twist P f θ (phiV g b θ) m = ∑ l, (P m l : ℂ) * (cexp (θ * f l * I) * phiV g b θ l - Q l) +
        ∑ l, (P m l : ℂ) * Q l := by
      rw [← sum_add_distrib]; exact sum_congr rfl fun l _ => by ring
    rw [this, hPQ]
    simp only [Pi.smul_apply, smul_eq_mul, phiV]
    push_cast
    ring
  rw [Pi.sub_apply, hsplit]
  -- the pointwise Taylor error
  have hpt : ∀ l, ‖cexp (θ * f l * I) * phiV g b θ l - Q l‖ ≤ 6 * M ^ 3 * |θ| ^ 3 := by
    intro l
    have hx : |θ * f l| ≤ 1 := by
      rw [abs_mul]; calc |θ| * |f l| ≤ |θ| * M := by gcongr; exact hfM l
        _ ≤ 1 := hθ
    set R := cexp (θ * f l * I) - (1 + ((θ * f l : ℝ) : ℂ) * I - ((θ * f l : ℝ) : ℂ) ^ 2 / 2) with hR
    have hRb : ‖R‖ ≤ |θ| ^ 3 * M ^ 3 := by
      have h := norm_exp_I_sub_taylor_le hx
      have hR' : R = cexp (((θ * f l : ℝ) : ℂ) * I) - (1 + ((θ * f l : ℝ) : ℂ) * I - ((θ * f l : ℝ) : ℂ) ^ 2 / 2) := by
        simp only [hR]; push_cast; ring_nf
      rw [hR']
      refine h.trans ?_
      rw [abs_mul, mul_pow]; gcongr; exact hfM l
    have hφ : ‖phiV g b θ l‖ ≤ 3 := by
      have := norm_phiV_sub_one_le hgM hbM hθ1 l
      calc ‖phiV g b θ l‖ = ‖(phiV g b θ l - 1) + 1‖ := by ring_nf
        _ ≤ ‖phiV g b θ l - 1‖ + 1 := by simpa using norm_add_le (phiV g b θ l - 1) 1
        _ ≤ 2 * |θ| * M + 1 := by linarith
        _ ≤ 3 := by linarith
    have e : cexp (θ * f l * I) * phiV g b θ l - Q l = R * phiV g b θ l +
        (((θ ^ 3 * f l * b l - θ ^ 3 * f l ^ 2 * g l / 2 : ℝ) : ℂ) * I +
          ((-(θ ^ 4 * f l ^ 2 * b l / 2) : ℝ) : ℂ)) := by
      simp only [hR, hQ, phiV]
      push_cast
      linear_combination (↑θ ^ 2 * ↑(f l) * ↑(g l)) * Complex.I_sq
    rw [e]
    have hE1 : |θ ^ 3 * f l * b l - θ ^ 3 * f l ^ 2 * g l / 2| ≤ 2 * M ^ 3 * |θ| ^ 3 := by
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_mul, abs_div, abs_mul, abs_mul, abs_pow, abs_pow, abs_two]
      have h1 : |θ| ^ 3 * |f l| * |b l| ≤ |θ| ^ 3 * M * M := by
        gcongr; exacts [hfM l, hbM l]
      have h2 : |θ| ^ 3 * |f l| ^ 2 * |g l| ≤ |θ| ^ 3 * M ^ 2 * M := by
        gcongr; exacts [hfM l, hgM l]
      have h3 : |θ| ^ 3 * M * M ≤ M ^ 3 * |θ| ^ 3 := by
        calc |θ| ^ 3 * M * M = |θ| ^ 3 * M ^ 2 := by ring
          _ ≤ |θ| ^ 3 * M ^ 3 := by gcongr
          _ = M ^ 3 * |θ| ^ 3 := by ring
      have h4 : |θ| ^ 3 * M ^ 2 * M = M ^ 3 * |θ| ^ 3 := by ring
      have h5 : 0 ≤ M ^ 3 * |θ| ^ 3 := by positivity
      linarith
    have hE2 : |-(θ ^ 4 * f l ^ 2 * b l / 2)| ≤ M ^ 3 * |θ| ^ 3 := by
      rw [abs_neg, abs_div, abs_mul, abs_mul, abs_pow, abs_pow, abs_two]
      have h1 : |θ| ^ 4 * |f l| ^ 2 * |b l| ≤ |θ| ^ 4 * M ^ 2 * M := by
        gcongr; exacts [hfM l, hbM l]
      have h4 : |θ| ^ 4 ≤ |θ| ^ 3 := pow_le_pow_of_le_one ht0 hθ1 (by norm_num)
      have : |θ| ^ 4 * M ^ 2 * M ≤ |θ| ^ 3 * M ^ 3 := by
        calc |θ| ^ 4 * M ^ 2 * M = |θ| ^ 4 * M ^ 3 := by ring
          _ ≤ |θ| ^ 3 * M ^ 3 := by gcongr
      nlinarith [pow_nonneg ht0 3, pow_nonneg hM0 3]
    calc ‖R * phiV g b θ l + (((θ ^ 3 * f l * b l - θ ^ 3 * f l ^ 2 * g l / 2 : ℝ) : ℂ) * I +
          ((-(θ ^ 4 * f l ^ 2 * b l / 2) : ℝ) : ℂ))‖
        ≤ ‖R‖ * ‖phiV g b θ l‖ + (|θ ^ 3 * f l * b l - θ ^ 3 * f l ^ 2 * g l / 2| +
            |-(θ ^ 4 * f l ^ 2 * b l / 2)|) := by
          refine (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) ((norm_add_le _ _).trans ?_))
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ |θ| ^ 3 * M ^ 3 * 3 + (2 * M ^ 3 * |θ| ^ 3 + M ^ 3 * |θ| ^ 3) := by
          gcongr
      _ = 6 * M ^ 3 * |θ| ^ 3 := by ring
  have hsum : ‖∑ l, (P m l : ℂ) * (cexp (θ * f l * I) * phiV g b θ l - Q l)‖ ≤ 6 * M ^ 3 * |θ| ^ 3 := by
    calc ‖∑ l, (P m l : ℂ) * (cexp (θ * f l * I) * phiV g b θ l - Q l)‖
        ≤ ∑ l, P m l * (6 * M ^ 3 * |θ| ^ 3) := by
          refine (norm_sum_le _ _).trans (sum_le_sum fun l _ => ?_)
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (nonneg_of_mem_rowStochastic hP)]
          exact mul_le_mul_of_nonneg_left (hpt l) (nonneg_of_mem_rowStochastic hP)
      _ = 6 * M ^ 3 * |θ| ^ 3 := by rw [← sum_mul, sum_row_of_mem_rowStochastic hP m, one_mul]
  have hlast : ‖((θ ^ 2 * σ2 / 2 : ℝ) : ℂ) * ((θ * g m : ℝ) * I + ((θ ^ 2 * b m : ℝ) : ℂ))‖ ≤
      M ^ 3 * |θ| ^ 3 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 : ‖((θ * g m : ℝ) : ℂ) * I + ((θ ^ 2 * b m : ℝ) : ℂ)‖ ≤ 2 * |θ| * M := by
      have := norm_phiV_sub_one_le hgM hbM hθ1 m
      have e : phiV g b θ m - 1 = (θ * g m : ℝ) * I + ((θ ^ 2 * b m : ℝ) : ℂ) := by
        simp only [phiV]; ring
      rwa [e] at this
    have h2 : |θ ^ 2 * σ2 / 2| ≤ θ ^ 2 * M / 2 := by
      rw [abs_of_nonneg (by positivity)]; gcongr
    calc |θ ^ 2 * σ2 / 2| * ‖((θ * g m : ℝ) : ℂ) * I + ((θ ^ 2 * b m : ℝ) : ℂ)‖
        ≤ θ ^ 2 * M / 2 * (2 * |θ| * M) := by gcongr
      _ = M ^ 2 * |θ| ^ 3 := by rw [← sq_abs θ]; ring
      _ ≤ M ^ 3 * |θ| ^ 3 := by gcongr
  calc _ ≤ ‖∑ l, (P m l : ℂ) * (cexp (θ * f l * I) * phiV g b θ l - Q l)‖ +
        ‖((θ ^ 2 * σ2 / 2 : ℝ) : ℂ) * ((θ * g m : ℝ) * I + ((θ ^ 2 * b m : ℝ) : ℂ))‖ := norm_add_le _ _
    _ ≤ 6 * M ^ 3 * |θ| ^ 3 + M ^ 3 * |θ| ^ 3 := add_le_add hsum hlast
    _ = 7 * M ^ 3 * |θ| ^ 3 := by ring

theorem norm_exp_twist_sub_one_le (θ y : ℝ) : ‖cexp (θ * y * I) - 1‖ ≤ |θ * y| := by
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := θ * y)
  rw [Real.norm_eq_abs] at h
  convert h using 3
  push_cast; ring

/-- The characteristic function of the additive functional `∑_{k ≤ n} f(X_k)` at `θ` is within
`5 |θ| M + 7 n M³ |θ|³` of `(1 - θ²σ²/2)^n`. -/
theorem cf_sub_pow_le {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) {f g b : S → ℝ} {σ2 M : ℝ}
    (hg : ∀ m, g m = ∑ l, P m l * (f l + g l))
    (hb : ∀ m, b m - σ2 / 2 = ∑ l, P m l * (b l - f l * g l - f l ^ 2 / 2))
    (hM1 : 1 ≤ M) (hfM : ∀ l, |f l| ≤ M) (hgM : ∀ l, |g l| ≤ M) (hbM : ∀ l, |b l| ≤ M)
    (hσ0 : 0 ≤ σ2) (hσM : σ2 ≤ M) {u : S → ℝ} (hu0 : ∀ i, 0 ≤ u i) (hu : ∑ i, u i = 1)
    {θ : ℝ} (hθ : |θ| * M ≤ 1) (n : ℕ) :
    ‖∑ x : Fin (n + 1) → S, (pathProb u P n x : ℂ) * cexp (θ * (∑ k : Fin (n + 1), f (x k)) * I) -
        ((1 - θ ^ 2 * σ2 / 2 : ℝ) : ℂ) ^ n‖ ≤ 5 * |θ| * M + 7 * n * M ^ 3 * |θ| ^ 3 := by
  have hM0 : 0 ≤ M := by linarith
  have ht0 : 0 ≤ |θ| := abs_nonneg θ
  have hθ1 : |θ| ≤ 1 := by nlinarith
  set A := twist P f θ with hA
  set φ := phiV g b θ with hφ
  set c : ℂ := ((1 - θ ^ 2 * σ2 / 2 : ℝ) : ℂ) with hc
  have hc1 : ‖c‖ ≤ 1 := by
    have h2 : θ ^ 2 * σ2 ≤ 1 := by
      calc θ ^ 2 * σ2 ≤ θ ^ 2 * M := by gcongr
        _ = |θ| * (|θ| * M) := by rw [← sq_abs θ]; ring
        _ ≤ 1 * 1 := by gcongr
        _ = 1 := by ring
    rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [sq_nonneg θ]
  -- the characteristic function through the twisted operator
  have hcf : ∑ x : Fin (n + 1) → S, (pathProb u P n x : ℂ) * cexp (θ * (∑ k : Fin (n + 1), f (x k)) * I) =
      ∑ m, (u m : ℂ) * (cexp (θ * f m * I) * A^[n] 1 m) := by
    rw [← path_twist u P f θ n 1]
    refine sum_congr rfl fun x _ => ?_
    rw [Pi.one_apply, mul_one, ← Complex.exp_sum]
    congr 2
    push_cast
    rw [mul_sum, sum_mul]
  have hsumu : ∑ m, (u m : ℂ) = 1 := by rw [← Complex.ofReal_sum, hu]; simp
  have hφ1 : ‖φ - 1‖ ≤ 2 * |θ| * M :=
    (pi_norm_le_iff_of_nonneg (by positivity)).2 fun m => by
      rw [Pi.sub_apply, Pi.one_apply]; exact norm_phiV_sub_one_le hgM hbM hθ1 m
  have hit := norm_iterate_sub_pow_le hP f θ φ c hc1 n
  have heig := twist_approx_eigen hP hg hb hM1 hfM hgM hbM hσ0 hσM hθ
  -- `A^n 1 - c^n 1` is small
  have hmain : ‖A^[n] 1 - c ^ n • (1 : S → ℂ)‖ ≤ 4 * |θ| * M + 7 * n * M ^ 3 * |θ| ^ 3 := by
    have e : A^[n] 1 - c ^ n • (1 : S → ℂ) =
        A^[n] (1 - φ) + (A^[n] φ - c ^ n • φ) + c ^ n • (φ - 1) := by
      rw [twist_iterate_sub, smul_sub]; abel
    rw [e]
    have h1 : ‖A^[n] (1 - φ)‖ ≤ 2 * |θ| * M := by
      refine (norm_twist_iterate_le hP f θ n _).trans ?_
      rw [norm_sub_rev]; exact hφ1
    have h2 : ‖A^[n] φ - c ^ n • φ‖ ≤ 7 * n * M ^ 3 * |θ| ^ 3 := by
      refine hit.trans ?_
      calc (n : ℝ) * ‖twist P f θ φ - c • φ‖ ≤ n * (7 * M ^ 3 * |θ| ^ 3) := by gcongr
        _ = 7 * n * M ^ 3 * |θ| ^ 3 := by ring
    have h3 : ‖c ^ n • (φ - 1)‖ ≤ 2 * |θ| * M := by
      rw [norm_smul, norm_pow]
      calc ‖c‖ ^ n * ‖φ - 1‖ ≤ 1 * (2 * |θ| * M) := by
            gcongr
            exact pow_le_one₀ (norm_nonneg _) hc1
        _ = 2 * |θ| * M := one_mul _
    calc _ ≤ ‖A^[n] (1 - φ)‖ + ‖A^[n] φ - c ^ n • φ‖ + ‖c ^ n • (φ - 1)‖ := norm_add₃_le
      _ ≤ 2 * |θ| * M + 7 * n * M ^ 3 * |θ| ^ 3 + 2 * |θ| * M := by gcongr
      _ = 4 * |θ| * M + 7 * n * M ^ 3 * |θ| ^ 3 := by ring
  rw [hcf]
  have e2 : ∑ m, (u m : ℂ) * (cexp (θ * f m * I) * A^[n] 1 m) - c ^ n =
      ∑ m, (u m : ℂ) * (cexp (θ * f m * I) * (A^[n] 1 m - c ^ n) + (cexp (θ * f m * I) - 1) * c ^ n) := by
    have h1 : c ^ n = ∑ m, (u m : ℂ) * c ^ n := by rw [← sum_mul, hsumu, one_mul]
    calc ∑ m, (u m : ℂ) * (cexp (θ * f m * I) * A^[n] 1 m) - c ^ n
        = ∑ m, (u m : ℂ) * (cexp (θ * f m * I) * A^[n] 1 m) - ∑ m, (u m : ℂ) * c ^ n := by
          rw [← h1]
      _ = _ := by
          rw [← sum_sub_distrib]
          exact sum_congr rfl fun m _ => by ring
  rw [e2]
  have hterm : ∀ m, ‖cexp (θ * f m * I) * (A^[n] 1 m - c ^ n) + (cexp (θ * f m * I) - 1) * c ^ n‖ ≤
      5 * |θ| * M + 7 * n * M ^ 3 * |θ| ^ 3 := by
    intro m
    have hm : ‖A^[n] 1 m - c ^ n‖ ≤ 4 * |θ| * M + 7 * n * M ^ 3 * |θ| ^ 3 := by
      have := norm_le_pi_norm (A^[n] 1 - c ^ n • (1 : S → ℂ)) m
      simp only [Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one] at this
      exact this.trans hmain
    have he : ‖cexp (θ * f m * I) - 1‖ ≤ |θ| * M := by
      refine (norm_exp_twist_sub_one_le θ (f m)).trans ?_
      rw [abs_mul]; gcongr; exact hfM m
    have hcn : ‖c ^ n‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hc1
    calc _ ≤ ‖cexp (θ * f m * I)‖ * ‖A^[n] 1 m - c ^ n‖ + ‖cexp (θ * f m * I) - 1‖ * ‖c ^ n‖ := by
          refine (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ 1 * (4 * |θ| * M + 7 * n * M ^ 3 * |θ| ^ 3) + |θ| * M * 1 := by
          rw [norm_exp_twist]; gcongr
      _ = 5 * |θ| * M + 7 * n * M ^ 3 * |θ| ^ 3 := by ring
  calc _ ≤ ∑ m, ‖(u m : ℂ) * (cexp (θ * f m * I) * (A^[n] 1 m - c ^ n) + (cexp (θ * f m * I) - 1) * c ^ n)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ m, u m * (5 * |θ| * M + 7 * n * M ^ 3 * |θ| ^ 3) := by
        refine sum_le_sum fun m _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hu0 m)]
        exact mul_le_mul_of_nonneg_left (hterm m) (hu0 m)
    _ = 5 * |θ| * M + 7 * n * M ^ 3 * |θ| ^ 3 := by rw [← sum_mul, hu, one_mul]

/-- `|s/√n| → 0`. -/
theorem tendsto_abs_div_sqrt (s : ℝ) : Tendsto (fun n : ℕ => |s / √(n : ℝ)|) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹) atTop (𝓝 0) :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  have := (h.const_mul |s|)
  rw [mul_zero] at this
  refine this.congr fun n => ?_
  rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _), div_eq_mul_inv]

/-- The characteristic function of `∑_{k ≤ n} f(X_k) / √n` tends to `exp(-s²σ²/2)`. -/
theorem cf_tendsto {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) {f g b : S → ℝ} {σ2 : ℝ}
    (hg : ∀ m, g m = ∑ l, P m l * (f l + g l))
    (hb : ∀ m, b m - σ2 / 2 = ∑ l, P m l * (b l - f l * g l - f l ^ 2 / 2))
    (hσ0 : 0 ≤ σ2) {u : S → ℝ} (hu0 : ∀ i, 0 ≤ u i) (hu : ∑ i, u i = 1) (s : ℝ) :
    Tendsto (fun n : ℕ => ∑ x : Fin (n + 1) → S,
        (pathProb u P n x : ℂ) * cexp ((s / √(n : ℝ) : ℝ) * (∑ k : Fin (n + 1), f (x k)) * I))
      atTop (𝓝 (cexp (-((s ^ 2 * σ2 / 2 : ℝ) : ℂ)))) := by
  set M : ℝ := 1 + σ2 + ∑ l, (|f l| + |g l| + |b l|) with hMdef
  have hT : ∀ l, |f l| + |g l| + |b l| ≤ ∑ l, (|f l| + |g l| + |b l|) := fun l =>
    single_le_sum (f := fun l => |f l| + |g l| + |b l|) (fun l _ => by positivity) (mem_univ l)
  have hfM : ∀ l, |f l| ≤ M := fun l => by
    have := hT l; have := abs_nonneg (g l); have := abs_nonneg (b l); linarith
  have hgM : ∀ l, |g l| ≤ M := fun l => by
    have := hT l; have := abs_nonneg (f l); have := abs_nonneg (b l); linarith
  have hbM : ∀ l, |b l| ≤ M := fun l => by
    have := hT l; have := abs_nonneg (f l); have := abs_nonneg (g l); linarith
  have hS0 : 0 ≤ ∑ l, (|f l| + |g l| + |b l|) := sum_nonneg fun l _ => by positivity
  have hM1 : 1 ≤ M := by linarith
  have hσM : σ2 ≤ M := by linarith
  have hM0 : 0 < M := by linarith
  set θ : ℕ → ℝ := fun n => s / √(n : ℝ) with hθdef
  have hθ0 := tendsto_abs_div_sqrt s
  -- the pure power `(1 - θ²σ²/2)^n`
  have hpow : Tendsto (fun n : ℕ => ((1 - θ n ^ 2 * σ2 / 2 : ℝ) : ℂ) ^ n) atTop
      (𝓝 (cexp (-((s ^ 2 * σ2 / 2 : ℝ) : ℂ)))) := by
    refine (Complex.tendsto_one_add_div_pow_exp (-((s ^ 2 * σ2 / 2 : ℝ) : ℂ))).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hsq : θ n ^ 2 = s ^ 2 / n := by
      simp only [hθdef, div_pow, Real.sq_sqrt hn0.le]
    rw [hsq]
    push_cast
    congr 1
    field_simp
    ring
  -- the error bound tends to zero
  have hbound : Tendsto (fun n : ℕ => 5 * |θ n| * M + 7 * n * M ^ 3 * |θ n| ^ 3) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => 5 * |θ n| * M + 7 * M ^ 3 * s ^ 2 * |θ n|) atTop (𝓝 0) := by
      have := ((hθ0.const_mul 5).mul_const M).add (hθ0.const_mul (7 * M ^ 3 * s ^ 2))
      simpa using this
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hsq : |θ n| ^ 2 = s ^ 2 / n := by
      rw [sq_abs]; simp only [hθdef, div_pow, Real.sq_sqrt hn0.le]
    have : (n : ℝ) * |θ n| ^ 3 = s ^ 2 * |θ n| := by
      rw [pow_succ, hsq]; field_simp
    rw [show 7 * (n : ℝ) * M ^ 3 * |θ n| ^ 3 = 7 * M ^ 3 * ((n : ℝ) * |θ n| ^ 3) by ring, this]
    ring
  have hev : ∀ᶠ n : ℕ in atTop, |θ n| * M ≤ 1 := by
    have := hθ0.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / M by positivity))
    filter_upwards [this] with n hn
    rw [lt_div_iff₀ hM0] at hn; exact hn.le
  have hdiff : Tendsto (fun n : ℕ => ∑ x : Fin (n + 1) → S,
        (pathProb u P n x : ℂ) * cexp ((θ n : ℝ) * (∑ k : Fin (n + 1), f (x k)) * I) -
        ((1 - θ n ^ 2 * σ2 / 2 : ℝ) : ℂ) ^ n) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hev] with n hn
    exact cf_sub_pow_le hP hg hb hM1 hfM hgM hbM hσ0 hσM hu0 hu hn n
  have := hdiff.add hpow
  rw [zero_add] at this
  refine this.congr fun n => ?_
  simp only [hθdef, sub_add_cancel]

/-! ## From characteristic functions to interval probabilities -/

/-- Lévy's continuity theorem and the portmanteau theorem for finitely supported laws: if the weights `p n`
on finite sets give characteristic functions of `Y n` converging to `exp(-t²/2)`, then the probability that
`r < Y n < s` tends to the standard normal integral `∫_r^s φ`. -/
theorem tendsto_Ioo_of_charFun {T : ℕ → Type*} [∀ n, Fintype (T n)] (p : ∀ n, T n → ℝ)
    (Y : ∀ n, T n → ℝ) (hp0 : ∀ n x, 0 ≤ p n x) (hp1 : ∀ n, ∑ x, p n x = 1)
    (hcf : ∀ t : ℝ, Tendsto (fun n => ∑ x, (p n x : ℂ) * cexp (t * Y n x * I)) atTop
      (𝓝 (cexp (-((t ^ 2 / 2 : ℝ) : ℂ)))))
    {r s : ℝ} (hrs : r < s) :
    Tendsto (fun n => ∑ x with r < Y n x ∧ Y n x < s, p n x) atTop
      (𝓝 (∫ x in r..s, gaussianPDFReal 0 1 x)) := by
  classical
  set ν : ℕ → Measure ℝ := fun n => Measure.sum (fun x => ENNReal.ofReal (p n x) • Measure.dirac (Y n x))
    with hνdef
  have hνE : ∀ n (E : Set ℝ), MeasurableSet E →
      ν n E = ENNReal.ofReal (∑ x with Y n x ∈ E, p n x) := by
    intro n E hE
    rw [hνdef, Measure.sum_apply _ hE, tsum_fintype, ENNReal.ofReal_sum_of_nonneg
      (fun x _ => hp0 n x), sum_filter]
    refine sum_congr rfl fun x _ => ?_
    rw [Measure.smul_apply, Measure.dirac_apply' _ hE, smul_eq_mul]
    by_cases h : Y n x ∈ E <;> simp [h]
  have hprob : ∀ n, IsProbabilityMeasure (ν n) := fun n => by
    constructor
    rw [hνE n _ MeasurableSet.univ]
    simp [hp1 n]
  have hcfν : ∀ n t, charFun (ν n) t = ∑ x, (p n x : ℂ) * cexp (t * Y n x * I) := by
    intro n t
    rw [charFun_apply_real, hνdef, integral_sum_dirac (fun x => ENNReal.ofReal_ne_top), tsum_fintype]
    refine sum_congr rfl fun x _ => ?_
    rw [ENNReal.toReal_ofReal (hp0 n x), Complex.real_smul]
  set μs : ℕ → ProbabilityMeasure ℝ := fun n => ⟨ν n, hprob n⟩ with hμs
  set μ0 : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩ with hμ0
  have hlim : Tendsto μs atTop (𝓝 μ0) := by
    refine ProbabilityMeasure.tendsto_of_tendsto_charFun fun t => ?_
    have e1 : ∀ n, charFun ((μs n : ProbabilityMeasure ℝ) : Measure ℝ) t =
        ∑ x, (p n x : ℂ) * cexp (t * Y n x * I) := fun n => hcfν n t
    have e2 : charFun ((μ0 : ProbabilityMeasure ℝ) : Measure ℝ) t = cexp (-((t ^ 2 / 2 : ℝ) : ℂ)) := by
      show charFun (gaussianReal 0 1) t = _
      rw [charFun_gaussianReal]
      congr 1
      push_cast
      ring
    simp only [e1, e2]
    exact hcf t
  have hnull : ((μ0 : ProbabilityMeasure ℝ) : Measure ℝ) (frontier (Set.Ioo r s)) = 0 := by
    show gaussianReal 0 1 _ = 0
    rw [frontier_Ioo hrs]
    have : (volume : Measure ℝ) {r, s} = 0 := (Set.toFinite _).measure_zero _
    exact gaussianReal_absolutelyContinuous 0 one_ne_zero this
  have key := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hlim hnull
  have key2 := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp key
  have hg : ((μ0 : ProbabilityMeasure ℝ) : Measure ℝ) (Set.Ioo r s) =
      ENNReal.ofReal (∫ x in r..s, gaussianPDFReal 0 1 x) := by
    show gaussianReal 0 1 _ = _
    rw [gaussianReal_apply_eq_integral 0 one_ne_zero, intervalIntegral.integral_of_le hrs.le,
      integral_Ioc_eq_integral_Ioo]
  rw [hg, ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg hrs.le
    fun x _ => gaussianPDFReal_nonneg 0 1 x)] at key2
  refine key2.congr fun n => ?_
  show (ν n (Set.Ioo r s)).toReal = _
  rw [hνE n _ measurableSet_Ioo, ENNReal.toReal_ofReal (sum_nonneg fun x _ => hp0 n x)]
  simp only [Set.mem_Ioo]

/-! ## Poisson equations through the fundamental matrix -/

theorem sum_w_mulVec {P : Matrix S S ℝ} {w : S → ℝ} (hfix : IsFixedRow P w) (x : S → ℝ) :
    ∑ i, w i * (P *ᵥ x) i = ∑ k, w k * x k := by
  simp only [mulVec, dotProduct, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun k _ => ?_
  have hk := congrFun hfix k
  simp only [vecMul, dotProduct] at hk
  rw [← hk, sum_mul]
  exact sum_congr rfl fun i _ => by ring

theorem fundamental_mulVec {P : Matrix S S ℝ} {w : S → ℝ} (x : S → ℝ) (m : S) :
    ((1 - P + rowsMatrix w) *ᵥ x) m = x m - (P *ᵥ x) m + ∑ k, w k * x k := by
  rw [add_mulVec, sub_mulVec, one_mulVec]
  simp [rowsMatrix, mulVec, dotProduct]

/-- For an ergodic chain the Poisson equation `b - P b = c` with `w · c = 0` is solved by `b = Z c`,
`Z = (I - P + W)⁻¹` the fundamental matrix, and then `w · b = 0`. -/
theorem poisson_solve {P : Matrix S S ℝ} {w : S → ℝ} (hsum : ∑ j, w j = 1) (hfix : IsFixedRow P w)
    (hunit : IsUnit (1 - P + rowsMatrix w)) (c : S → ℝ) (hc : ∑ k, w k * c k = 0) :
    (∀ m, ((1 - P + rowsMatrix w)⁻¹ *ᵥ c) m - (P *ᵥ ((1 - P + rowsMatrix w)⁻¹ *ᵥ c)) m = c m) ∧
      ∑ k, w k * ((1 - P + rowsMatrix w)⁻¹ *ᵥ c) k = 0 := by
  set A := 1 - P + rowsMatrix w with hA
  set b := A⁻¹ *ᵥ c with hb
  have hAb : A *ᵥ b = c := by
    rw [hb, mulVec_mulVec, mul_nonsing_inv A ((isUnit_iff_isUnit_det A).1 hunit), one_mulVec]
  have hpt : ∀ m, b m - (P *ᵥ b) m + ∑ k, w k * b k = c m := fun m => by
    rw [← fundamental_mulVec, hAb]
  have hwb : ∑ k, w k * b k = 0 := by
    have : ∑ m, w m * (b m - (P *ᵥ b) m + ∑ k, w k * b k) = ∑ m, w m * c m := by simp only [hpt]
    simp only [mul_add, mul_sub, sum_add_distrib, sum_sub_distrib, sum_w_mulVec hfix, ← sum_mul,
      hsum, one_mul] at this
    linarith
  refine ⟨fun m => ?_, hwb⟩
  have := hpt m
  rw [hwb, add_zero] at this
  exact this

/-- The rows of the fundamental matrix sum to one. -/
theorem fundamental_row_sum {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) {w : S → ℝ}
    (hsum : ∑ j, w j = 1) (hunit : IsUnit (1 - P + rowsMatrix w)) (i : S) :
    ∑ l, (1 - P + rowsMatrix w)⁻¹ i l = 1 := by
  set A := 1 - P + rowsMatrix w with hA
  have h1 : A *ᵥ (fun _ => (1 : ℝ)) = fun _ => 1 := by
    funext m
    rw [hA, fundamental_mulVec]
    have : (P *ᵥ fun _ => (1 : ℝ)) m = 1 := by
      simpa [mulVec, dotProduct] using sum_row_of_mem_rowStochastic hP m
    rw [this]; simp [hsum]
  have h2 : A⁻¹ *ᵥ (fun _ => (1 : ℝ)) = fun _ => 1 := by
    conv_lhs => rw [← h1]
    rw [mulVec_mulVec, nonsing_inv_mul A ((isUnit_iff_isUnit_det A).1 hunit), one_mulVec]
  have := congrFun h2 i
  simpa [mulVec, dotProduct] using this

end MarkovClt

open MarkovClt

variable {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]

/-- Grinstead–Snell Theorem 11.17 (PR-121), central limit theorem for Markov chains. Let `P` be an ergodic chain
with fixed probability vector `w` and fundamental matrix `Z = (I - P + W)⁻¹`, and let
`σ_j² = 2 w_j z_jj - w_j - w_j²` (equation 11.10). For every initial probability vector `u`, every state `j` with
`σ_j² > 0` and all `r < s`, the probability that the number `S_j^(n)` of visits to `j` at the times `0, …, n`
satisfies `r < (S_j^(n) - n w_j) / √(n σ_j²) < s` tends to `∫_r^s φ` (standard normal density). The book tacitly
assumes `σ_j² > 0`; it fails for instance for the two-state chain that always switches, where `σ_j² = 0`. -/
@[kb "grinsteadsnell2006" "Theorem 11.17, p. 472"]
theorem markov_clt {P : Matrix S S ℝ} (hP : IsErgodicChain P) {u : S → ℝ} (hu0 : ∀ i, 0 ≤ u i)
    (hu : ∑ i, u i = 1) :
    ∃ w : S → ℝ, (∀ j, 0 < w j) ∧ ∑ j, w j = 1 ∧ IsFixedRow P w ∧ IsUnit (1 - P + rowsMatrix w) ∧
      ∀ j : S, 0 < 2 * w j * (1 - P + rowsMatrix w)⁻¹ j j - w j - w j ^ 2 →
        ∀ r s : ℝ, r < s →
          Tendsto (fun n : ℕ => ∑ x : Fin (n + 1) → S with
              r < (((univ.filter fun k : Fin (n + 1) => x k = j).card : ℝ) - n * w j) /
                  √(n * (2 * w j * (1 - P + rowsMatrix w)⁻¹ j j - w j - w j ^ 2)) ∧
                (((univ.filter fun k : Fin (n + 1) => x k = j).card : ℝ) - n * w j) /
                  √(n * (2 * w j * (1 - P + rowsMatrix w)⁻¹ j j - w j - w j ^ 2)) < s,
              pathProb u P n x)
            atTop (𝓝 (∫ x in r..s, gaussianPDFReal 0 1 x)) := by
  obtain ⟨w, hpos, hsum, hfix, hunit, -⟩ := meanFirstPassage_eq_fundamental hP
  refine ⟨w, hpos, hsum, hfix, hunit, fun j hσ r s hrs => ?_⟩
  have hPs := hP.1
  set Z := (1 - P + rowsMatrix w)⁻¹ with hZ
  set σ2 := 2 * w j * Z j j - w j - w j ^ 2 with hσ2
  -- the centred indicator and its Poisson solution
  set f : S → ℝ := fun l => (if l = j then 1 else 0) - w j with hf
  have hf0 : ∑ k, w k * f k = 0 := by
    simp only [hf, mul_sub, mul_ite, mul_one, mul_zero, sum_sub_distrib, sum_ite_eq', mem_univ,
      if_true, ← sum_mul, hsum, one_mul, sub_self]
  obtain ⟨hh, hwh⟩ := poisson_solve hsum hfix hunit f hf0
  set h := Z *ᵥ f with hhdef
  set g : S → ℝ := fun l => h l - f l with hgdef
  have hg : ∀ m, g m = ∑ l, P m l * (f l + g l) := by
    intro m
    have e : ∑ l, P m l * (f l + g l) = (P *ᵥ h) m := by
      simp only [hgdef, add_sub_cancel, mulVec, dotProduct]
    rw [e, hgdef]
    have := hh m
    linarith
  have hhj : h j = Z j j - w j := by
    have : h j = ∑ l, Z j l * f l := rfl
    rw [this]
    simp only [hf, mul_sub, mul_ite, mul_one, mul_zero, sum_sub_distrib, sum_ite_eq', mem_univ, if_true,
      ← sum_mul]
    rw [fundamental_row_sum hPs hsum hunit j, one_mul]
  have hwfh : ∑ l, w l * (f l * h l) = w j * h j := by
    have : ∀ l, w l * (f l * h l) = (if l = j then w l * h l else 0) - w j * (w l * h l) := by
      intro l; simp only [hf]; split_ifs <;> ring
    rw [sum_congr rfl fun l _ => this l, sum_sub_distrib, sum_ite_eq', if_pos (mem_univ j), ← mul_sum,
      hwh, mul_zero, sub_zero]
  have hwff : ∑ l, w l * f l ^ 2 = w j - w j ^ 2 := by
    have : ∀ l, w l * f l ^ 2 = (if l = j then w l * (1 - 2 * w j) else 0) + w j ^ 2 * w l := by
      intro l; simp only [hf]; split_ifs <;> ring
    rw [sum_congr rfl fun l _ => this l, sum_add_distrib, sum_ite_eq', if_pos (mem_univ j), ← mul_sum, hsum]
    ring
  set q : S → ℝ := fun l => f l * g l + f l ^ 2 / 2 with hq
  have hwq : ∑ l, w l * q l = σ2 / 2 := by
    have : ∀ l, w l * q l = w l * (f l * h l) - w l * f l ^ 2 / 2 := by
      intro l; simp only [hq, hgdef]; ring
    rw [sum_congr rfl fun l _ => this l, sum_sub_distrib, hwfh, ← sum_div, hwff, hhj, hσ2]
    ring
  set c : S → ℝ := fun m => σ2 / 2 - (P *ᵥ q) m with hc
  have hc0 : ∑ k, w k * c k = 0 := by
    simp only [hc, mul_sub, sum_sub_distrib, ← sum_mul, hsum, one_mul, sum_w_mulVec hfix, hwq, sub_self]
  obtain ⟨hbP, -⟩ := poisson_solve hsum hfix hunit c hc0
  set b := Z *ᵥ c with hbdef
  have hb : ∀ m, b m - σ2 / 2 = ∑ l, P m l * (b l - f l * g l - f l ^ 2 / 2) := by
    intro m
    have e : ∑ l, P m l * (b l - f l * g l - f l ^ 2 / 2) = (P *ᵥ b) m - (P *ᵥ q) m := by
      simp only [mulVec, dotProduct, hq, ← sum_sub_distrib]
      exact sum_congr rfl fun l _ => by ring
    rw [e]
    have := hbP m
    simp only [hc] at this
    linarith
  have hσ0 : 0 ≤ σ2 := hσ.le
  -- the characteristic functions
  refine tendsto_Ioo_of_charFun (T := fun n => Fin (n + 1) → S) (fun n => pathProb u P n)
    (fun n x => (((univ.filter fun k : Fin (n + 1) => x k = j).card : ℝ) - n * w j) / √(n * σ2))
    (fun n x => pathProb_nonneg hu0 hPs n x) (fun n => sum_pathProb hu hPs n) (fun t => ?_) hrs
  set t' := t / √σ2 with ht'
  have hcf := cf_tendsto hPs hg hb hσ0 hu0 hu t'
  have hlim : cexp (-((t' ^ 2 * σ2 / 2 : ℝ) : ℂ)) = cexp (-((t ^ 2 / 2 : ℝ) : ℂ)) := by
    congr 3
    rw [ht', div_pow, Real.sq_sqrt hσ0]
    field_simp
  rw [hlim] at hcf
  have hθ : Tendsto (fun n : ℕ => t' / √(n : ℝ)) atTop (𝓝 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).2 (tendsto_abs_div_sqrt t')
  have he : Tendsto (fun n : ℕ => cexp (((t' / √(n : ℝ) : ℝ) : ℂ) * w j * I)) atTop (𝓝 1) := by
    have hc : Continuous fun y : ℝ => cexp ((y : ℂ) * w j * I) := by fun_prop
    have := (hc.tendsto 0).comp hθ
    have h0 : cexp (((0 : ℝ) : ℂ) * w j * I) = 1 := by
      rw [Complex.ofReal_zero, zero_mul, zero_mul, Complex.exp_zero]
    rw [h0] at this
    exact this
  have := he.mul hcf
  rw [one_mul] at this
  refine this.congr fun n => ?_
  simp only [Function.comp, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  have hcard : ((univ.filter fun k : Fin (n + 1) => x k = j).card : ℝ) - n * w j =
      ∑ k : Fin (n + 1), f (x k) + w j := by
    simp only [hf, sum_sub_distrib, sum_boole, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  rw [hcard, Real.sqrt_mul (Nat.cast_nonneg n)]
  have hσs : √σ2 ≠ 0 := (Real.sqrt_pos.2 hσ).ne'
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  rw [ht']
  push_cast
  field_simp
  ring

end UndergradKB.Probability
