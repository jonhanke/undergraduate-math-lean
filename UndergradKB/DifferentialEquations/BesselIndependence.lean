import UndergradKB.DifferentialEquations.BesselSeries
import UndergradKB.Common.Attr

/-! # Independence of `J_p`, `J_{-p}` and derivative identities (Lebl, *Notes on Diffy Qs*, §7.3.3)

For `p` not an integer, `J_p` and `J_{-p}` (the real series `besselJR` of `BesselSeries.lean`) are linearly
independent on `x > 0`: near `0` the function `J_{-p}` blows up like `x^(-p)` against `x^p` (for `p > 0`).
Also `J_p' = (p/x) J_p - J_{p+1}` for every admissible `p`, and with the recurrence
`J_p' = (J_{p-1} - J_{p+1})/2` and `x J_p' = x J_{p-1} - p J_p` for `p > 0` (in particular for integer
`n ≥ 1`).  The oscillation of Bessel functions is not formalized.
-/

namespace UndergradKB.DifferentialEquations

open Filter Topology

lemma evS_tendsto (q : ℝ) (hq : ∀ m : ℕ, q + 1 ≠ -(m : ℝ)) :
    Tendsto (evS (bcoef q)) (𝓝 0) (𝓝 (bcoef q 0)) := by
  have hc : ContinuousAt (evS (bcoef q)) 0 := (hasDerivAt_evS (bcoef_hsum q hq) 0).continuousAt
  have h0 : evS (bcoef q) 0 = bcoef q 0 := by
    unfold evS
    rw [tsum_eq_single 0]
    · simp
    · intro n hn
      simp [zero_pow (by omega : 2 * n ≠ 0)]
  rw [← h0]
  exact hc.tendsto

lemma indep_pos (p : ℝ) (hp : 0 < p) (hnp : ∀ n : ℤ, p ≠ n) (a b : ℝ)
    (h : ∀ x : ℝ, 0 < x → a * besselJR p x + b * besselJR (-p) x = 0) : a = 0 ∧ b = 0 := by
  have hP := hp_of_not_int hnp
  have hM := hp_of_not_int (fun n h => hnp (-n) (by push_cast; linarith) : ∀ n : ℤ, -p ≠ n)
  have cP : bcoef p 0 ≠ 0 := bcoef_ne p hP 0
  have cM : bcoef (-p) 0 ≠ 0 := bcoef_ne (-p) hM 0
  have key1 : ∀ᶠ x in 𝓝[>] (0 : ℝ),
      a * (x / 2) ^ (2 * p) * evS (bcoef p) x + b * evS (bcoef (-p)) x = 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : (0 : ℝ) < x := hx
    have := h x hx'
    rw [besselJR_eq p x hx', besselJR_eq (-p) x hx'] at this
    have e : (x / 2) ^ p * (x / 2) ^ (-p) = 1 := by
      rw [← Real.rpow_add (by positivity)]; simp
    have e2 : (x / 2) ^ (2 * p) = (x / 2) ^ p * (x / 2) ^ p := by
      rw [two_mul, Real.rpow_add (by positivity)]
    rw [e2]
    linear_combination ((x / 2) ^ p) * this - (b * evS (bcoef (-p)) x) * e
  have t1 : Tendsto (fun x : ℝ => (x / 2) ^ (2 * p)) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun x : ℝ => (x / 2) ^ (2 * p)) 0 :=
      (continuousAt_id.div_const 2).rpow_const (Or.inr (by linarith))
    have := hc.tendsto
    rwa [show ((0 : ℝ) / 2) ^ (2 * p) = 0 by
      rw [zero_div]; exact Real.zero_rpow (by positivity)] at this
  have t2 := (((t1.const_mul a).mul (evS_tendsto p hP)).add
    ((evS_tendsto (-p) hM).const_mul b)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have t3 : Tendsto (fun x : ℝ => a * (x / 2) ^ (2 * p) * evS (bcoef p) x + b * evS (bcoef (-p)) x)
      (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' (key1.mono fun x hx => hx.symm)
  have hb0 : b = 0 := by
    have := tendsto_nhds_unique t2 t3
    simp only [mul_zero, zero_mul, zero_add] at this
    rcases mul_eq_zero.mp this with h1 | h1
    · exact h1
    · exact absurd h1 cM
  subst hb0
  have key2 : ∀ᶠ x in 𝓝[>] (0 : ℝ), a * evS (bcoef p) x = 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : (0 : ℝ) < x := hx
    have := h x hx'
    rw [besselJR_eq p x hx'] at this
    have hu : (0 : ℝ) < (x / 2) ^ p := by positivity
    have : (x / 2) ^ p * (a * evS (bcoef p) x) = 0 := by linear_combination this
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 hu.ne'
    · exact h1
  have t4 := (((evS_tendsto p hP).const_mul a)).mono_left
    (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have t5 : Tendsto (fun x : ℝ => a * evS (bcoef p) x) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' (key2.mono fun x hx => hx.symm)
  have := tendsto_nhds_unique t4 t5
  rcases mul_eq_zero.mp this with h1 | h1
  · exact ⟨h1, rfl⟩
  · exact absurd h1 cP

/-- DE-209 / DE-213: for `p` not an integer, `J_p` and `J_{-p}` are linearly independent on `(0, ∞)`:
if `a J_p + b J_{-p} = 0` for all `x > 0` then `a = b = 0`. -/
@[kb "lebldiffyqs2026" "§7.3.3 Solutions of Bessel's equation, p. 348"]
theorem besselJR_linearIndependent (p : ℝ) (hp : ∀ n : ℤ, p ≠ n) (a b : ℝ)
    (h : ∀ x : ℝ, 0 < x → a * besselJR p x + b * besselJR (-p) x = 0) : a = 0 ∧ b = 0 := by
  have hp0 : p ≠ 0 := by simpa using hp 0
  rcases lt_or_gt_of_ne hp0 with hn | hpos
  · have := indep_pos (-p) (by linarith)
      (fun n h => hp (-n) (by push_cast; linarith)) b a
      (fun x hx => by have := h x hx; simp only [neg_neg]; linarith)
    exact ⟨this.2, this.1⟩
  · exact indep_pos p hpos hp a b h

/-- DE-209 (Frobenius solutions with exponents `p` and `-p`, `p` not an integer): both `J_p` and `J_{-p}`
solve Bessel's equation (`besselJR_pair_solve`), and distinct pairs `(A, B)` give distinct functions
`A J_p + B J_{-p}` on `x > 0`. -/
@[kb "lebldiffyqs2026" "§7.3.3 Bessel's equation, p. 347"]
theorem besselJR_combination_injective (p : ℝ) (hp : ∀ n : ℤ, p ≠ n) (A B A' B' : ℝ)
    (h : ∀ x : ℝ, 0 < x → A * besselJR p x + B * besselJR (-p) x =
      A' * besselJR p x + B' * besselJR (-p) x) : A = A' ∧ B = B' := by
  have := besselJR_linearIndependent p hp (A - A') (B - B') (fun x hx => by
    have := h x hx; linarith)
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

lemma evS1_eq (p : ℝ) (hp : ∀ m : ℕ, p + 1 ≠ -(m : ℝ)) (x : ℝ) :
    evS1 (bcoef p) x = -(x / 2) * evS (bcoef (p + 1)) x := by
  have hR : 1 ≤ |x| + 1 := by linarith [abs_nonneg x]
  have s1 := summable1 (bcoef_hsum p hp) (abs_lt_R x) hR
  unfold evS1 evS
  rw [s1.tsum_eq_zero_add, ← tsum_mul_left]
  simp only [Nat.cast_zero, mul_zero, zero_mul, zero_add]
  refine tsum_congr fun n => ?_
  have e2 : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
  rw [e2, bcoef_succ_shift p hp n, pow_succ]
  push_cast
  ring

/-- DE-215: `J_p'(x) = (p/x) J_p(x) - J_{p+1}(x)` for `x > 0`, any real `p` that is not a negative integer
(for `p = 0` this is `J_0' = -J_1`). -/
@[kb "lebldiffyqs2026" "§7.3.3 Properties of Bessel functions, p. 349"]
theorem deriv_besselJR_eq (p : ℝ) (hp : ∀ m : ℕ, p + 1 ≠ -(m : ℝ)) {x : ℝ} (hx : 0 < x) :
    deriv (besselJR p) x = p / x * besselJR p x - besselJR (p + 1) x := by
  rw [(hasDerivAt_besselJR p hp hx).deriv]
  unfold besselJ1
  rw [evS1_eq p hp x, besselJR_eq p x hx, besselJR_eq (p + 1) x hx,
    Real.rpow_add_one (by positivity)]
  field_simp
  ring

/-- DE-215: for `p > 0` (in particular every integer `n ≥ 1`) and `x > 0`,
`J_p'(x) = (J_{p-1}(x) - J_{p+1}(x)) / 2`: the derivative is a combination of `J_{p-1}` and `J_{p+1}`. -/
@[kb "lebldiffyqs2026" "§7.3.3 Properties of Bessel functions, p. 349"]
theorem deriv_besselJR_half (p : ℝ) (hp : 0 < p) {x : ℝ} (hx : 0 < x) :
    deriv (besselJR p) x = (besselJR (p - 1) x - besselJR (p + 1) x) / 2 := by
  rw [deriv_besselJR_eq p (hp_of_nonneg hp.le) hx]
  have := besselJR_recurrence p hp hx
  have hx0 : x ≠ 0 := hx.ne'
  field_simp
  linarith

/-- DE-215: for `p > 0` and `x > 0`, `x J_p'(x) = x J_{p-1}(x) - p J_p(x)`. -/
@[kb "lebldiffyqs2026" "§7.3.3 Properties of Bessel functions, p. 349"]
theorem x_mul_deriv_besselJR (p : ℝ) (hp : 0 < p) {x : ℝ} (hx : 0 < x) :
    x * deriv (besselJR p) x = x * besselJR (p - 1) x - p * besselJR p x := by
  rw [deriv_besselJR_half p hp hx]
  have := besselJR_recurrence p hp hx
  linarith

end UndergradKB.DifferentialEquations
