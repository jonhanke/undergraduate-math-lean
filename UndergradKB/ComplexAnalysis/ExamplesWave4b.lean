import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Complex.RemovableSingularity
import UndergradKB.ComplexAnalysis.CauchyFormula
import UndergradKB.ComplexAnalysis.Residue

/-!
# Beck et al., Chapters 8 and 9: further corollaries and examples

* Corollary 8.1.12 (Cauchy's formula for all derivatives, along a simple closed path),
* Corollary 8.1.13 (Cauchy's estimate),
* Corollary 8.2.6 (minimum-modulus theorem),
* Definition 8.3.1 and Examples 8.3.2, 8.3.3, 8.3.4 (Laurent series),
* Example 9.2.9 (a residue at a simple zero of the denominator).
-/

open Set Metric Complex Filter Topology
open scoped Real

namespace UndergradKB.ComplexAnalysis

/-! ### Section 8.1 -/

/-- Beck Corollary 8.1.12: if `f` is holomorphic on the open set `G`, `γ` is a positively oriented
simple closed piecewise smooth path that is `G`-contractible and `w` lies inside `γ`, then the
`k`-th derivative of `f` at `w` is `k! / (2πi)` times the integral over `γ` of
`f z / (z - w)^(k+1)`. -/
@[kb "beck2025" "Corollary 8.1.12, p. 134"]
theorem cauchy_integral_formula_iteratedDeriv {γ : ℝ → ℂ} {f : ℂ → ℂ} {G : Set ℂ}
    (hγ : IsPositivelyOrientedSimpleClosed γ) (hG : IsOpen G)
    (hf : DifferentiableOn ℂ f G) {c : ℂ} (hc : IsGHomotopic G γ (fun _ => c)) {w : ℂ}
    (hw : w ∈ insideOf γ) (k : ℕ) :
    iteratedDeriv k f w =
      k.factorial / (2 * π * I) * pathIntegral (fun z => f z / (z - w) ^ (k + 1)) γ 0 1 :=
  hγ.cauchy_integral_formula_deriv hG hf hc hw k

/-- Beck Corollary 8.1.13 (Cauchy's estimate): if `f` is holomorphic on the open disc `D[w, R]`
and bounded there in modulus by `M`, then `|f^(k)(w)| ≤ k! M / R^k`. As in the book, the estimate
on every smaller circle `C[w, r]` (`r < R`) is passed to the limit `r → R`. -/
@[kb "beck2025" "Corollary 8.1.13, p. 134"]
theorem cauchy_estimate {f : ℂ → ℂ} {w : ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball w R)) (hM : ∀ z ∈ ball w R, ‖f z‖ ≤ M)
    (k : ℕ) : ‖iteratedDeriv k f w‖ ≤ k.factorial * M / R ^ k := by
  have key : ∀ r : ℝ, 0 < r → r < R → ‖iteratedDeriv k f w‖ ≤ k.factorial * M / r ^ k :=
    fun r hr hrR => Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hr
      ((hf.mono (closure_ball_subset_closedBall.trans (closedBall_subset_ball hrR))).diffContOnCl)
      fun z hz => hM z (closedBall_subset_ball hrR (sphere_subset_closedBall hz))
  have hlim : Tendsto (fun r : ℝ => k.factorial * M / r ^ k) (𝓝[<] R)
      (𝓝 (k.factorial * M / R ^ k)) :=
    ((continuousAt_const.div (continuousAt_id.pow k) (pow_ne_zero _ hR.ne')).tendsto).mono_left
      nhdsWithin_le_nhds
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT (half_lt_self hR)] with r hr
  exact key r (lt_trans (half_pos hR) hr.1) hr.2

/-! ### Section 8.2 -/

/-- Beck Corollary 8.2.6 (minimum-modulus theorem): if `f` is holomorphic and nonconstant on a
region (open connected set) `G`, and `|f|` has a weak relative minimum at `a ∈ G` (that is,
`|f a| ≤ |f z|` for all `z` in some disc about `a`), then `f a = 0`. -/
@[kb "beck2025" "Corollary 8.2.6, p. 137"]
theorem minimum_modulus {f : ℂ → ℂ} {G : Set ℂ} (hG : IsOpen G) (hconn : IsConnected G)
    (hf : DifferentiableOn ℂ f G) (hnc : ∃ x ∈ G, ∃ y ∈ G, f x ≠ f y)
    {a : ℂ} (ha : a ∈ G) {ε : ℝ} (hε : 0 < ε) (hmin : ∀ z ∈ ball a ε, ‖f a‖ ≤ ‖f z‖) :
    f a = 0 := by
  have hdiff : ∀ᶠ z in 𝓝 a, DifferentiableAt ℂ f z :=
    Filter.eventually_of_mem (hG.mem_nhds ha) fun z hz => hf.differentiableAt (hG.mem_nhds hz)
  have hloc : IsLocalMin (norm ∘ f) a :=
    Filter.eventually_of_mem (ball_mem_nhds a hε) fun z hz => hmin z hz
  rcases Complex.eventually_eq_or_eq_zero_of_isLocalMin_norm hdiff hloc with h | h
  · exfalso
    have han : AnalyticOnNhd ℂ f G := hf.analyticOnNhd hG
    have heq : EqOn f (fun _ => f a) G :=
      han.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hconn.isPreconnected ha h
    obtain ⟨x, hx, y, hy, hxy⟩ := hnc
    exact hxy ((heq hx).trans (heq hy).symm)
  · exact h

/-! ### Section 8.3 -/

/-- Beck Definition 8.3.1: the value at `z` of the Laurent series `∑_{k ∈ ℤ} c_k (z - z₀)^k`
centred at `z₀` (as an unconditional sum over `ℤ`; it is meaningful when the sum is summable). -/
@[kb "beck2025" "Definition 8.3.1, p. 138"]
noncomputable def laurentSeries (c : ℤ → ℂ) (z₀ z : ℂ) : ℂ := ∑' k : ℤ, c k * (z - z₀) ^ k

/-- Beck Definition 8.3.1 (convergence): the double series converges exactly when the
nonnegative-index part and the negative-index part do, and then the sum is the sum of the two. -/
@[kb "beck2025" "Definition 8.3.1, p. 138"]
theorem laurentSeries_eq_add {c : ℤ → ℂ} {z₀ z a b : ℂ}
    (h₁ : HasSum (fun n : ℕ => c n * (z - z₀) ^ (n : ℤ)) a)
    (h₂ : HasSum (fun n : ℕ => c (-(n + 1 : ℕ)) * (z - z₀) ^ (-((n + 1 : ℕ) : ℤ))) b) :
    HasSum (fun k : ℤ => c k * (z - z₀) ^ k) (a + b) ∧ laurentSeries c z₀ z = a + b := by
  have h : HasSum (fun k : ℤ => c k * (z - z₀) ^ k) (a + b) := by
    refine HasSum.of_nat_of_neg_add_one h₁ ?_
    simpa [Nat.cast_add, Nat.cast_one] using h₂
  exact ⟨h, h.tsum_eq⟩

/-- Coefficients of the Laurent series of `exp (1/z)` about `0`: `c_{-k} = 1/k!` for `k ≥ 0`
and `c_k = 0` for `k > 0`. -/
noncomputable def expInvCoeff (k : ℤ) : ℂ := if k ≤ 0 then ((((-k).toNat).factorial : ℕ) : ℂ)⁻¹ else 0

/-- Beck Example 8.3.2: for `z ≠ 0`, `exp (1/z) = ∑_{k ≥ 0} z^(-k) / k!`, i.e. it is the Laurent
series about `0` with coefficients `c_{-k} = 1/k!` and `c_k = 0` for `k > 0`. -/
@[kb "beck2025" "Example 8.3.2, p. 138"]
theorem hasSum_laurent_exp_inv {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℤ => expInvCoeff k * (z - 0) ^ k) (exp (1 / z)) ∧
      laurentSeries expInvCoeff 0 z = exp (1 / z) := by
  have hnat : HasSum (fun n : ℕ => expInvCoeff n * (z - 0) ^ (n : ℤ)) 1 := by
    have : HasSum (fun n : ℕ => expInvCoeff n * (z - 0) ^ (n : ℤ)) (expInvCoeff (0 : ℕ) *
        (z - 0) ^ ((0 : ℕ) : ℤ)) := by
      refine hasSum_single 0 fun n hn => ?_
      have : ¬ ((n : ℤ) ≤ 0) := by
        have : 0 < n := Nat.pos_of_ne_zero hn
        omega
      rw [expInvCoeff, if_neg this, zero_mul]
    simpa [expInvCoeff] using this
  have hneg : HasSum (fun n : ℕ => expInvCoeff (-(n + 1 : ℕ)) * (z - 0) ^ (-((n + 1 : ℕ) : ℤ)))
      (exp (1 / z) - 1) := by
    have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℂ) (1 / z)
    rw [← Complex.exp_eq_exp_ℂ] at h
    have h' := (hasSum_nat_add_iff' 1).2 h
    simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero, Nat.cast_one,
      div_one] at h'
    convert h' using 1
    funext n
    have : (-((n + 1 : ℕ) : ℤ)) ≤ 0 := by omega
    simp [expInvCoeff, this, div_eq_mul_inv, mul_comm]
    refine Or.inl ?_
    rw [show (-1 + -(n : ℤ)) = -((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  have := laurentSeries_eq_add hnat hneg
  simpa using this

/-- Beck Example 8.3.3: a convergent power series `∑ a_k (z - z₀)^k` is a Laurent series whose
coefficients vanish for negative indices. -/
@[kb "beck2025" "Example 8.3.3, p. 138"]
theorem hasSum_laurent_of_powerSeries {a : ℕ → ℂ} {z₀ z s : ℂ}
    (h : HasSum (fun n : ℕ => a n * (z - z₀) ^ n) s) :
    ∃ c : ℤ → ℂ, (∀ k : ℤ, k < 0 → c k = 0) ∧ (∀ n : ℕ, c n = a n) ∧
      HasSum (fun k : ℤ => c k * (z - z₀) ^ k) s ∧ laurentSeries c z₀ z = s := by
  classical
  let c : ℤ → ℂ := fun k => if 0 ≤ k then a k.toNat else 0
  have hc : ∀ n : ℕ, c n = a n := fun n => by simp [c]
  have h₁ : HasSum (fun n : ℕ => c n * (z - z₀) ^ (n : ℤ)) s := by
    simpa [hc] using h
  have h₂ : HasSum (fun n : ℕ => c (-(n + 1 : ℕ)) * (z - z₀) ^ (-((n + 1 : ℕ) : ℤ))) 0 := by
    have : ∀ n : ℕ, c (-(n + 1 : ℕ)) = 0 := fun n => by
      have : ¬ (0 ≤ -((n + 1 : ℕ) : ℤ)) := by omega
      simp only [c]
      exact if_neg this
    have hfun : (fun n : ℕ => c (-(n + 1 : ℕ)) * (z - z₀) ^ (-((n + 1 : ℕ) : ℤ))) =
        fun _ => 0 := by
      funext n; rw [this n, zero_mul]
    rw [hfun]
    exact hasSum_zero
  have := laurentSeries_eq_add h₁ h₂
  rw [add_zero] at this
  exact ⟨c, fun k hk => by simp [c, not_le.2 hk], hc, this.1, this.2⟩

/-- Beck Example 8.3.4 (first step): the function `1/sin z - 1/z` tends to `0` as `z → 0`, so
it extends continuously to `0` with value `0` (the function `g` of the book). -/
@[kb "beck2025" "Example 8.3.4, p. 139"]
theorem tendsto_inv_sin_sub_inv :
    Tendsto (fun z : ℂ => 1 / Complex.sin z - 1 / z) (𝓝[≠] 0) (𝓝 0) := by
  set s : ℂ → ℂ := dslope Complex.sin 0 with hs
  have hsd : Differentiable ℂ s := fun z =>
    ((Complex.differentiableOn_dslope (Filter.univ_mem)).2
      Complex.differentiable_sin.differentiableOn).differentiableAt Filter.univ_mem
  have hs0 : s 0 = 1 := by simp [hs, dslope_same]
  have heven : ∀ z, s (-z) = s z := by
    intro z
    by_cases hz : z = 0
    · simp [hz]
    · have hz' : -z ≠ 0 := neg_ne_zero.2 hz
      simp only [hs, dslope_of_ne _ hz, dslope_of_ne _ hz', slope_def_field, Complex.sin_neg,
        sub_zero, zero_sub]
      rw [Complex.sin_zero]
      field_simp
      ring
  have hd0 : deriv s 0 = 0 := by
    have h1 : deriv (fun x => s (-x)) 0 = -deriv s (-0) := deriv_comp_neg s 0
    have h2 : (fun x => s (-x)) = s := funext heven
    rw [h2, neg_zero] at h1
    linear_combination (1 / 2 : ℂ) * h1
  have hdsl : ContinuousAt (dslope s 0) 0 :=
    ((Complex.differentiableOn_dslope (Filter.univ_mem)).2
      hsd.differentiableOn).differentiableAt Filter.univ_mem |>.continuousAt
  have hdsl0 : dslope s 0 0 = 0 := by rw [dslope_same, hd0]
  have hlim : Tendsto (fun z => -(dslope s 0 z) / s z) (𝓝 0) (𝓝 0) := by
    have h1 : Tendsto (fun z => -(dslope s 0 z)) (𝓝 0) (𝓝 (-0)) := by
      have := hdsl.tendsto.neg
      rw [hdsl0] at this
      exact this
    have h2 : Tendsto s (𝓝 0) (𝓝 1) := by
      have := hsd.continuous.tendsto 0
      rw [hs0] at this
      exact this
    have := h1.div h2 one_ne_zero
    rw [neg_zero, zero_div] at this
    exact this
  have hs1 : ∀ᶠ z in 𝓝 (0 : ℂ), s z ≠ 0 :=
    (hsd.continuous.continuousAt.eventually_ne (by rw [hs0]; exact one_ne_zero))
  refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hs1] with z hz hsz
  have hz0 : z ≠ 0 := hz
  have hsin : Complex.sin z = z * s z := by
    have := sub_smul_dslope Complex.sin 0 z
    rw [Complex.sin_zero, sub_zero, sub_zero, smul_eq_mul] at this
    exact this.symm
  have hdz : dslope s 0 z = (s z - 1) / z := by
    rw [dslope_of_ne _ hz0, slope_def_field, hs0, sub_zero]
  rw [hdz, hsin]
  field_simp
  ring

/-! ### Section 9.2 -/

/-- Beck Example 9.2.9: the residue of `(z² + 2) / ((exp z - 1) cos z)` at `2πi` is
`(2 - 4π²) / cosh (2π)`. -/
@[kb "beck2025" "Example 9.2.9, p. 156"]
theorem residue_example_9_2_9 :
    residue (fun z : ℂ => (z ^ 2 + 2) / ((Complex.exp z - 1) * Complex.cos z)) (2 * π * I) =
      (2 - 4 * (π : ℂ) ^ 2) / Complex.cosh (2 * π) := by
  have hcos : ∀ z ∈ ball (2 * π * I : ℂ) 1, Complex.cos z ≠ 0 := by
    intro z hz h
    obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.1 h
    have him : |z.im - 2 * π| < 1 := by
      have := Complex.abs_im_le_norm (z - 2 * π * I)
      have h2 : ‖z - 2 * π * I‖ < 1 := by simpa [mem_ball, dist_eq_norm] using hz
      have h3 : (z - 2 * π * I).im = z.im - 2 * π := by simp
      rw [h3] at this
      exact lt_of_le_of_lt (by simpa using this) h2
    have hzim : z.im = 0 := by rw [hk]; simp
    rw [hzim] at him
    have := Real.pi_gt_three
    rw [abs_lt] at him
    linarith [him.1]
  have hf : DifferentiableOn ℂ (fun z : ℂ => (z ^ 2 + 2) / Complex.cos z) (ball (2 * π * I : ℂ) 1) :=
    fun z hz => ((by fun_prop : DifferentiableAt ℂ (fun z : ℂ => z ^ 2 + 2) z).div
      Complex.differentiable_cos.differentiableAt (hcos z hz)).differentiableWithinAt
  have hg : DifferentiableOn ℂ (fun z : ℂ => Complex.exp z - 1) (ball (2 * π * I : ℂ) 1) :=
    (by fun_prop : Differentiable ℂ (fun z : ℂ => Complex.exp z - 1)).differentiableOn
  have hgc : Complex.exp (2 * π * I) - 1 = 0 := by
    rw [Complex.exp_two_pi_mul_I]; ring
  have hg' : deriv (fun z : ℂ => Complex.exp z - 1) (2 * π * I) = 1 := by
    have : deriv (fun z : ℂ => Complex.exp z - 1) (2 * π * I) = Complex.exp (2 * π * I) := by
      simp
    rw [this, Complex.exp_two_pi_mul_I]
  have key := residue_div_of_simple_zero one_pos hf hg hgc (by rw [hg']; exact one_ne_zero)
  rw [hg'] at key
  have e : (fun z : ℂ => (z ^ 2 + 2) / ((Complex.exp z - 1) * Complex.cos z)) =
      fun z => (z ^ 2 + 2) / Complex.cos z / (Complex.exp z - 1) := by
    funext z; rw [div_div, mul_comm (Complex.cos z)]
  rw [e, key, div_one]
  have hc : Complex.cos (2 * π * I) = Complex.cosh (2 * π) := by
    rw [Complex.cos_mul_I]
  rw [hc]
  congr 1
  rw [mul_pow, mul_pow, Complex.I_sq]
  ring

end UndergradKB.ComplexAnalysis
