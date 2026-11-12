import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import UndergradKB.Common.Attr

/-! # First-order equations (Lebl, *Notes on Diffy Qs*, Chapter 1)

Counterexamples to existence and uniqueness, the equation `y' = y²`, the autonomous equation `y' = f(y)`,
substitutions (Bernoulli, homogeneous), the phase line, the logistic equation with harvesting, integrating
factors of exact equations, and first-order linear PDEs (transport equation, characteristics). -/

namespace UndergradKB.DifferentialEquations

open Set Filter Topology

/-! ## Failure of uniqueness and existence -/

/-- `x ↦ x |x|` has derivative `2 |x|` everywhere. -/
lemma hasDerivAt_mul_abs (x : ℝ) : HasDerivAt (fun x : ℝ => x * |x|) (2 * |x|) x := by
  rcases lt_trichotomy x 0 with h | h | h
  · have h1 := (hasDerivAt_pow 2 x).fun_neg
    have := h1.congr_of_eventuallyEq (f₁ := fun x : ℝ => x * |x|) (by
      filter_upwards [Iio_mem_nhds h] with y hy
      rw [abs_of_neg (show y < 0 from hy)]; ring)
    rw [abs_of_neg h]; convert this using 1; simp
  · subst h
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    simp only [zero_add, zero_mul, abs_zero, sub_zero]
    have h1 : (fun h : ℝ => |h|) =o[𝓝 0] (fun _ => (1 : ℝ)) := by
      rw [Asymptotics.isLittleO_one_iff]
      simpa using (continuous_abs.tendsto (0 : ℝ))
    simpa [mul_comm] using h1.mul_isBigO (Asymptotics.isBigO_refl (fun h : ℝ => h) (𝓝 0))
  · have h1 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    have := h1.congr_of_eventuallyEq (f₁ := fun x : ℝ => x * |x|) (by
      filter_upwards [Ioi_mem_nhds h] with y hy
      rw [abs_of_pos (show 0 < y from hy)]; ring)
    rw [abs_of_pos h]; exact this

/-- DE-020 (Example 1.2.2). The initial value problem `y' = 2 √|y|`, `y(0) = 0` has two different solutions on
all of `ℝ`, namely `y = 0` and `y = x |x|`; so uniqueness fails when the right-hand side is not Lipschitz. -/
@[kb "lebldiffyqs2026" "Example 1.2.2, p. 29"]
theorem sqrt_abs_ode_not_unique :
    (∀ x : ℝ, HasDerivAt (fun _ : ℝ => (0 : ℝ)) (2 * Real.sqrt |(0 : ℝ)|) x) ∧
    (∀ x : ℝ, HasDerivAt (fun x : ℝ => x * |x|) (2 * Real.sqrt (abs (x * |x|))) x) ∧
    (0 : ℝ) * |(0 : ℝ)| = 0 ∧ (fun x : ℝ => x * |x|) ≠ (fun _ : ℝ => (0 : ℝ)) := by
  refine ⟨fun x => by simpa using hasDerivAt_const x (0 : ℝ), fun x => ?_, by simp, ?_⟩
  · have : Real.sqrt (abs (x * |x|)) = |x| := by
      rw [abs_mul, abs_abs, abs_mul_abs_self, Real.sqrt_mul_self_eq_abs]
    rw [this]; exact hasDerivAt_mul_abs x
  · intro h
    have := congrFun h 1
    simp at this

/-- DE-019 (Example 1.2.1). The problem `y' = 1/x`, `y(0) = 0` has no solution: there is no function `y`,
differentiable on some interval `(-ε, ε)`, with `y'(x) = 1/x` for all `x ≠ 0` in it. -/
@[kb "lebldiffyqs2026" "Example 1.2.1, p. 29"]
theorem no_solution_inv_ode {ε : ℝ} (hε : 0 < ε) (y : ℝ → ℝ)
    (hy : ∀ x ∈ Ioo (-ε) ε, DifferentiableAt ℝ y x) :
    ¬ ∀ x ∈ Ioo (-ε) ε, x ≠ 0 → deriv y x = 1 / x := by
  intro hder
  have hs : IsOpen (Ioo 0 ε) := isOpen_Ioo
  obtain ⟨c, hc⟩ := hs.exists_is_const_of_deriv_eq_zero (f := fun x => y x - Real.log x)
    (isPreconnected_Ioo)
    (fun x hx => (hy x ⟨by linarith [hx.1], hx.2⟩).differentiableWithinAt.sub
      (Real.differentiableAt_log hx.1.ne').differentiableWithinAt)
    (fun x hx => by
      have h1 := hder x ⟨by linarith [hx.1], hx.2⟩ hx.1.ne'
      have h2 : HasDerivAt (fun x => y x - Real.log x) (deriv y x - x⁻¹) x :=
        (hy x ⟨by linarith [hx.1], hx.2⟩).hasDerivAt.sub (Real.hasDerivAt_log hx.1.ne')
      simp only [Pi.zero_apply]
      rw [h2.deriv, h1]; simp)
  have hT : Tendsto (fun x => y x) (𝓝[>] 0) (𝓝 (y 0)) := by
    have : ContinuousAt y 0 := (hy 0 ⟨by linarith, hε⟩).continuousAt
    exact this.tendsto.mono_left nhdsWithin_le_nhds
  have hL : Tendsto (fun x => y x) (𝓝[>] 0) atBot := by
    have h1 : Tendsto (fun x => Real.log x + c) (𝓝[>] 0) atBot :=
      tendsto_atBot_add_const_right _ _ Real.tendsto_log_nhdsGT_zero
    refine h1.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hε] with x hx
    have := hc x hx
    linarith
  exact not_tendsto_nhds_of_tendsto_atBot hL _ hT

/-! ## `y' = y²` and autonomous equations -/

/-- DE-015 (Example 1.1.4, p. 23; Example 1.2.3, p. 30). For `A ≠ 0`, the function `y = 1/(1/A - x)` solves
`y' = y²`, `y(0) = A` at every `x ≠ 1/A` (in particular on the interval around `0` on one side of the
singularity), and it blows up: `|y| → ∞` as `x → 1/A`. -/
@[kb "lebldiffyqs2026" "Example 1.1.4, p. 23"]
theorem inv_sq_ode (A : ℝ) (hA : A ≠ 0) :
    (∀ x : ℝ, x ≠ 1 / A → HasDerivAt (fun x => 1 / (1 / A - x)) ((1 / (1 / A - x)) ^ 2) x) ∧
    1 / (1 / A - 0) = A ∧
    Tendsto (fun x : ℝ => |1 / (1 / A - x)|) (𝓝[≠] (1 / A)) atTop := by
  refine ⟨fun x hx => ?_, by simp, ?_⟩
  · have hne : 1 / A - x ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
    have h := ((hasDerivAt_id x).const_sub (1 / A)).inv hne
    simp only [one_div, id] at h ⊢
    convert h using 1
    field_simp
  · have h1 : Tendsto (fun x : ℝ => |1 / A - x|) (𝓝[≠] (1 / A)) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have hc : Continuous (fun x : ℝ => |1 / A - x|) := by fun_prop
        have := hc.tendsto (1 / A)
        simp only [sub_self, abs_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx
        exact abs_pos.2 (sub_ne_zero.2 (Ne.symm hx))
    refine (tendsto_inv_nhdsGT_zero.comp h1).congr ?_
    intro x
    simp [abs_inv]

/-- Two functions with the same derivative everywhere differ by a constant. -/
lemma eq_add_const_of_hasDerivAt {f g h : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (h t) t)
    (hg : ∀ t, HasDerivAt g (h t) t) (t : ℝ) : f t = g t + (f 0 - g 0) := by
  have hd : ∀ t, HasDerivAt (fun t => f t - g t) 0 t := fun t => by
    have := (hf t).fun_sub (hg t)
    rwa [sub_self] at this
  have h : f t - g t = f 0 - g 0 :=
    is_const_of_deriv_eq_zero (f := fun t => f t - g t) (fun t => (hd t).differentiableAt)
      (fun t => (hd t).deriv) t 0
  linarith

/-- DE-014 (Example 1.1.3, p. 23). For `y' = f(y)` with `f` nowhere zero, let `G` be an antiderivative of
`1/f`. Then a differentiable `y` solves the equation on an open interval `I` exactly when `G(y(x)) - x`
is constant on `I` (that is, `x = G(y) + C`, the book's `x = ∫ dy / f(y) + C`). -/
@[kb "lebldiffyqs2026" "Example 1.1.3, p. 23"]
theorem autonomous_ode_iff {f G y : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I) (hIc : IsPreconnected I)
    (hf : ∀ u, f u ≠ 0) (hG : ∀ u, HasDerivAt G (1 / f u) u)
    (hy : ∀ x ∈ I, DifferentiableAt ℝ y x) :
    (∀ x ∈ I, HasDerivAt y (f (y x)) x) ↔ ∃ c, ∀ x ∈ I, G (y x) - x = c := by
  constructor
  · intro h
    have hd : ∀ x ∈ I, HasDerivAt (fun x => G (y x) - x) 0 x := by
      intro x hx
      have h2 := ((hG (y x)).comp x (h x hx)).fun_sub (hasDerivAt_id' x)
      have e : 1 / f (y x) * f (y x) - 1 = 0 := by
        rw [one_div, inv_mul_cancel₀ (hf _), sub_self]
      rw [e] at h2
      exact h2
    obtain ⟨c, hc⟩ := hI.exists_is_const_of_deriv_eq_zero (f := fun x => G (y x) - x) hIc
      (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => (hd x hx).deriv)
    exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩ x hx
    have h1 : HasDerivAt (fun x => G (y x) - x) 0 x := by
      refine (hasDerivAt_const x c).congr_of_eventuallyEq ?_
      filter_upwards [hI.mem_nhds hx] with z hz using hc z hz
    have h2 := ((hG (y x)).comp x (hy x hx).hasDerivAt).fun_sub (hasDerivAt_id' x)
    have h5 : 1 / f (y x) * deriv y x = 1 := by
      have := h2.unique h1
      linarith
    have hfx := hf (y x)
    have : deriv y x = f (y x) :=
      calc deriv y x = f (y x) * (1 / f (y x) * deriv y x) := by field_simp
        _ = f (y x) := by rw [h5, mul_one]
    rw [← this]; exact (hy x hx).hasDerivAt

/-- DE-016 (Example 1.1.5, p. 24). The second-order problem `x'' = t²` (with `v = x'`): every solution is
`x(t) = t⁴/12 + x'(0) t + x(0)`, and for any initial data this function is a solution. -/
@[kb "lebldiffyqs2026" "Example 1.1.5, p. 24"]
theorem second_order_t_sq :
    (∀ {x v : ℝ → ℝ}, (∀ t, HasDerivAt x (v t) t) → (∀ t, HasDerivAt v (t ^ 2) t) →
      ∀ t, x t = t ^ 4 / 12 + v 0 * t + x 0) ∧
    (∀ a b : ℝ, (∀ t, HasDerivAt (fun t : ℝ => t ^ 4 / 12 + b * t + a) (t ^ 3 / 3 + b) t) ∧
      (∀ t, HasDerivAt (fun t : ℝ => t ^ 3 / 3 + b) (t ^ 2) t)) := by
  have hv3 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t ^ 3 / 3) (t ^ 2) t := fun t => by
    have := (hasDerivAt_pow 3 t).div_const 3
    convert this using 1
    simp
  have hq : ∀ a b t : ℝ, HasDerivAt (fun t : ℝ => t ^ 4 / 12 + b * t + a) (t ^ 3 / 3 + b) t := by
    intro a b t
    have := (((hasDerivAt_pow 4 t).div_const 12).add ((hasDerivAt_id' t).const_mul b)).add_const a
    convert this using 1
    simp; ring
  refine ⟨fun {x v} hx hv t => ?_, fun a b => ⟨hq a b, fun t => (hv3 t).add_const b⟩⟩
  have hveq : ∀ t, v t = t ^ 3 / 3 + v 0 := by
    intro t
    have := eq_add_const_of_hasDerivAt hv hv3 t
    simpa using this
  have hx' : ∀ t, HasDerivAt x (t ^ 3 / 3 + v 0) t := fun t => by
    have := hx t
    rwa [hveq t] at this
  have := eq_add_const_of_hasDerivAt hx' (hq 0 (v 0)) t
  simp at this
  linarith

/-! ## Substitutions -/

/-- Pointwise form of the Bernoulli substitution: for `y(x) > 0` and `y` differentiable at `x`,
`y' + p y = q yⁿ` holds iff `v = y^(1-n)` satisfies `v' + (1-n) p v = (1-n) q` at `x`. -/
lemma bernoulli_pointwise {p q y : ℝ → ℝ} {n : ℝ} (hn : n ≠ 1) {x : ℝ}
    (hy : DifferentiableAt ℝ y x) (hpos : 0 < y x) :
    deriv y x + p x * y x = q x * y x ^ n ↔
      deriv (fun t => y t ^ (1 - n)) x + (1 - n) * p x * y x ^ (1 - n) = (1 - n) * q x := by
  have hd : HasDerivAt (fun t => y t ^ (1 - n)) (deriv y x * (1 - n) * y x ^ (1 - n - 1)) x :=
    hy.hasDerivAt.rpow_const (Or.inl hpos.ne')
  rw [hd.deriv]
  have h1 : y x ^ (1 - n - 1) = y x ^ (-n) := by congr 1; ring
  have h2 : y x ^ (1 - n) = y x * y x ^ (-n) := by
    rw [Real.rpow_sub hpos, Real.rpow_one, Real.rpow_neg hpos.le]; field_simp
  have hr : y x ^ (-n) * y x ^ n = 1 := by
    rw [Real.rpow_neg hpos.le]; exact inv_mul_cancel₀ (Real.rpow_pos_of_pos hpos n).ne'
  have hrpos : 0 < y x ^ (-n) := Real.rpow_pos_of_pos hpos _
  have hn' : (1 - n) ≠ 0 := sub_ne_zero.2 (Ne.symm hn)
  rw [h1, h2]
  have key : deriv y x * (1 - n) * y x ^ (-n) + (1 - n) * p x * (y x * y x ^ (-n)) - (1 - n) * q x
      = (1 - n) * y x ^ (-n) * (deriv y x + p x * y x - q x * y x ^ n) := by
    linear_combination ((1 - n) * q x) * hr
  constructor
  · intro H
    have : (1 - n) * y x ^ (-n) * (deriv y x + p x * y x - q x * y x ^ n) = 0 := by
      rw [H]; ring
    linarith
  · intro H
    have h0 : (1 - n) * y x ^ (-n) * (deriv y x + p x * y x - q x * y x ^ n) = 0 := by
      rw [← key]; linarith
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h (mul_ne_zero hn' hrpos.ne')
    · linarith

/-- DE-029 (Section 1.5.2, Bernoulli equation, p. 47). On a set `I` where the differentiable function `y`
is positive, `y` solves `y' + p y = q yⁿ` (`n ≠ 1` real) iff `v = y^(1-n)` solves the linear equation
`v' + (1-n) p v = (1-n) q`. -/
@[kb "lebldiffyqs2026" "Section 1.5.2, p. 47"]
theorem bernoulli_iff {p q y : ℝ → ℝ} {n : ℝ} (hn : n ≠ 1) {I : Set ℝ}
    (hy : ∀ x ∈ I, DifferentiableAt ℝ y x) (hpos : ∀ x ∈ I, 0 < y x) :
    (∀ x ∈ I, deriv y x + p x * y x = q x * y x ^ n) ↔
      ∀ x ∈ I, deriv (fun t => y t ^ (1 - n)) x + (1 - n) * p x * y x ^ (1 - n) = (1 - n) * q x :=
  forall₂_congr fun x hx => bernoulli_pointwise hn (hy x hx) (hpos x hx)

/-- DE-030 (Section 1.5.3, p. 48). For `y' = F(y/x)` at a point `x ≠ 0`: the substitution `v = y/x` turns it
into `x v' = F(v) - v`. -/
@[kb "lebldiffyqs2026" "Section 1.5.3, p. 48"]
theorem homogeneous_iff {F y : ℝ → ℝ} {I : Set ℝ} (hx0 : ∀ x ∈ I, x ≠ 0)
    (hy : ∀ x ∈ I, DifferentiableAt ℝ y x) :
    (∀ x ∈ I, deriv y x = F (y x / x)) ↔
      ∀ x ∈ I, x * deriv (fun t => y t / t) x = F (y x / x) - y x / x := by
  refine forall₂_congr fun x hx => ?_
  have hne := hx0 x hx
  have hd : HasDerivAt (fun t => y t / t) ((deriv y x * x - y x * 1) / x ^ 2) x :=
    (hy x hx).hasDerivAt.div (hasDerivAt_id' x) hne
  rw [hd.deriv]
  have e : x * ((deriv y x * x - y x * 1) / x ^ 2) = deriv y x - y x / x := by
    field_simp
  rw [e]
  constructor <;> intro H <;> linarith

/-! ## The logistic equation with harvesting -/

/-- DE-035 (Section 1.6, logistic equation with harvesting, pp. 53-54). The critical points of
`x' = k x (M - x) - h` (`k > 0`) are the real roots of `k x (M - x) - h`. With
`D = (kM)² - 4hk`: two distinct roots if `D > 0`, exactly one (`M/2`) if `D = 0`, none if `D < 0`. -/
@[kb "lebldiffyqs2026" "Section 1.6, p. 53"]
theorem harvesting_critical_points {k M h : ℝ} (hk : 0 < k) :
    ((k * M) ^ 2 - 4 * h * k > 0 →
      ∃ a b : ℝ, a ≠ b ∧ {x : ℝ | k * x * (M - x) - h = 0} = {a, b}) ∧
    ((k * M) ^ 2 - 4 * h * k = 0 → {x : ℝ | k * x * (M - x) - h = 0} = {M / 2}) ∧
    ((k * M) ^ 2 - 4 * h * k < 0 → {x : ℝ | k * x * (M - x) - h = 0} = ∅) := by
  set s : ℝ := (k * M ^ 2 / 4 - h) / k with hs
  have hks : k * s = k * M ^ 2 / 4 - h := by rw [hs]; field_simp
  have hD : (k * M) ^ 2 - 4 * h * k = 4 * k ^ 2 * s := by linear_combination (-4 * k) * hks
  have hE : ∀ x, k * x * (M - x) - h = -(k * ((x - M / 2) ^ 2 - s)) := by
    intro x; linear_combination (-1) * hks
  have hiff : ∀ x, k * x * (M - x) - h = 0 ↔ (x - M / 2) ^ 2 = s := by
    intro x
    rw [hE, neg_eq_zero, mul_eq_zero, sub_eq_zero]
    exact ⟨fun h => h.resolve_left hk.ne', Or.inr⟩
  have hk2 : 0 < 4 * k ^ 2 := by positivity
  refine ⟨fun hpos => ?_, fun hz => ?_, fun hneg => ?_⟩
  · have hs0 : 0 < s := by
      rw [hD] at hpos
      exact (mul_pos_iff_of_pos_left hk2).1 hpos
    refine ⟨M / 2 + Real.sqrt s, M / 2 - Real.sqrt s, ?_, ?_⟩
    · have := Real.sqrt_pos.2 hs0
      intro h; linarith
    · ext x
      simp only [Set.mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
      rw [hiff]
      have hsq := Real.sq_sqrt hs0.le
      constructor
      · intro h
        have h' : (x - M / 2) ^ 2 = (Real.sqrt s) ^ 2 := by rw [hsq]; exact h
        rcases (sq_eq_sq_iff_eq_or_eq_neg).1 h' with h | h
        · left; linarith
        · right; linarith
      · rintro (h | h)
        · have : x - M / 2 = Real.sqrt s := by linarith
          rw [this, hsq]
        · have : x - M / 2 = -Real.sqrt s := by linarith
          rw [this, neg_sq, hsq]
  · have hs0 : s = 0 := by
      rw [hD] at hz
      rcases mul_eq_zero.1 hz with h | h
      · exact absurd h hk2.ne'
      · exact h
    ext x
    simp only [Set.mem_ofPred_eq, mem_singleton_iff]
    rw [hiff, hs0]
    constructor
    · intro h
      have := pow_eq_zero_iff (two_ne_zero) |>.1 h
      linarith
    · intro h; rw [h]; ring
  · have hs0 : s < 0 := by
      by_contra hcon
      have := mul_nonneg hk2.le (not_lt.1 hcon)
      rw [← hD] at this
      linarith
    ext x
    simp only [Set.mem_ofPred_eq, mem_empty_iff_false, iff_false]
    rw [hiff]
    intro h
    nlinarith [sq_nonneg (x - M / 2)]

/-! ## Phase line -/

/-- DE-033 (Section 1.6, phase diagram, p. 52), the monotonicity part. A solution of the autonomous equation
`x' = f(x)` on an interval `I` along which `f(x(t)) > 0` is strictly increasing there. -/
@[kb "lebldiffyqs2026" "Section 1.6, p. 52"]
theorem strictMonoOn_of_autonomous_pos {f x : ℝ → ℝ} {I : Set ℝ} (hI : Convex ℝ I)
    (hx : ∀ t ∈ I, HasDerivAt x (f (x t)) t) (hpos : ∀ t ∈ I, 0 < f (x t)) :
    StrictMonoOn x I := by
  refine strictMonoOn_of_deriv_pos hI (fun t ht => (hx t ht).continuousAt.continuousWithinAt) ?_
  intro t ht
  rw [(hx t (interior_subset ht)).deriv]
  exact hpos t (interior_subset ht)

/-- DE-033/DE-023, the companion fact: the constant function `c` is a solution of `x' = f(x)` exactly when
`f(c) = 0` (critical points are the constant solutions). -/
@[kb "lebldiffyqs2026" "Section 1.6, p. 52"]
theorem const_solution_iff {f : ℝ → ℝ} (c : ℝ) :
    (∀ t : ℝ, HasDerivAt (fun _ : ℝ => c) (f c) t) ↔ f c = 0 := by
  constructor
  · intro h
    exact (h 0).unique (hasDerivAt_const 0 c)
  · intro h t
    rw [h]; exact hasDerivAt_const t c

/-! ## Integrating factors -/

/-- The factor `e^{∫ P}` (with base point `x₀`) used to make an equation exact. -/
noncomputable def intFactor (P : ℝ → ℝ) (x₀ : ℝ) (t : ℝ) : ℝ := Real.exp (∫ s in x₀..t, P s)

lemma hasDerivAt_intFactor {P : ℝ → ℝ} (hP : Continuous P) (x₀ t : ℝ) :
    HasDerivAt (intFactor P x₀) (P t * intFactor P x₀ t) t := by
  have h := ((hP.integral_hasStrictDerivAt x₀ t).hasDerivAt).exp
  unfold intFactor
  convert h using 1
  ring

/-- DE-046 (Section 1.8.2, p. 68). For the equation `M dx + N dy = 0` with partial derivatives
`M_y`, `N_x`. If `(M_y - N_x)/N = P(x)` depends on `x` alone (`N ≠ 0`), then with `u = e^{∫P}` the
equation `uM dx + uN dy = 0` is exact: `(uM)_y = (uN)_x` (both sides are given by the same number `d`). -/
@[kb "lebldiffyqs2026" "Section 1.8.2, p. 68"]
theorem integrating_factor_of_x {M N : ℝ → ℝ → ℝ} {P : ℝ → ℝ} (hP : Continuous P) (x₀ : ℝ)
    {x y My Nx : ℝ} (hMy : HasDerivAt (fun t => M x t) My y) (hNx : HasDerivAt (fun t => N t y) Nx x)
    (hN : N x y ≠ 0) (hP' : (My - Nx) / N x y = P x) :
    ∃ d : ℝ, HasDerivAt (fun t => intFactor P x₀ x * M x t) d y ∧
      HasDerivAt (fun t => intFactor P x₀ t * N t y) d x := by
  refine ⟨intFactor P x₀ x * My, hMy.const_mul _, ?_⟩
  have h := (hasDerivAt_intFactor hP x₀ x).mul hNx
  have e : My = P x * N x y + Nx := by
    field_simp at hP'; linarith
  convert h using 1
  rw [e]; ring

/-- DE-046 (Section 1.8.2, p. 69), the `y`-only version. If `(M_y - N_x)/M = Q(y)` depends on `y` alone
(`M ≠ 0`), then `u = e^{-∫Q}` (here `intFactor (-Q) y₀`, a function of `y`) makes `uM dx + uN dy = 0` exact. -/
@[kb "lebldiffyqs2026" "Section 1.8.2, p. 69"]
theorem integrating_factor_of_y {M N : ℝ → ℝ → ℝ} {Q : ℝ → ℝ} (hQ : Continuous Q) (y₀ : ℝ)
    {x y My Nx : ℝ} (hMy : HasDerivAt (fun t => M x t) My y) (hNx : HasDerivAt (fun t => N t y) Nx x)
    (hM : M x y ≠ 0) (hQ' : (My - Nx) / M x y = Q y) :
    ∃ d : ℝ, HasDerivAt (fun t => intFactor (fun s => -Q s) y₀ y * N t y) d x ∧
      HasDerivAt (fun t => intFactor (fun s => -Q s) y₀ t * M x t) d y := by
  refine ⟨intFactor (fun s => -Q s) y₀ y * Nx, hNx.const_mul _, ?_⟩
  have h := (hasDerivAt_intFactor (P := fun s => -Q s) hQ.neg y₀ y).mul hMy
  have e : My = Q y * M x y + Nx := by
    field_simp at hQ'; linarith
  convert h using 1
  rw [e]; ring

/-! ## First-order linear PDEs -/

/-- DE-047 (Example 1.9.1, p. 72), existence. For differentiable `f`, `u(x,t) = f(x - α t)` is a
differentiable function of `(x,t)` satisfying `α u_x + u_t = 0` and `u(x,0) = f(x)`. Here `u_x` and `u_t`
are the derivatives of `u` along the directions `(1,0)` and `(0,1)`. -/
@[kb "lebldiffyqs2026" "Example 1.9.1, p. 72"]
theorem transport_solution (α : ℝ) {f : ℝ → ℝ} (hf : Differentiable ℝ f) :
    Differentiable ℝ (fun p : ℝ × ℝ => f (p.1 - α * p.2)) ∧
    (∀ p : ℝ × ℝ, α * fderiv ℝ (fun p : ℝ × ℝ => f (p.1 - α * p.2)) p (1, 0) +
      fderiv ℝ (fun p : ℝ × ℝ => f (p.1 - α * p.2)) p (0, 1) = 0) ∧
    ∀ x, (fun p : ℝ × ℝ => f (p.1 - α * p.2)) (x, 0) = f x := by
  have key : ∀ p : ℝ × ℝ, HasFDerivAt (fun p : ℝ × ℝ => f (p.1 - α * p.2))
      (deriv f (p.1 - α * p.2) • ((ContinuousLinearMap.fst ℝ ℝ ℝ) - α • (ContinuousLinearMap.snd ℝ ℝ ℝ))) p := by
    intro p
    have hg : HasFDerivAt (fun p : ℝ × ℝ => p.1 - α * p.2)
        ((ContinuousLinearMap.fst ℝ ℝ ℝ) - α • (ContinuousLinearMap.snd ℝ ℝ ℝ)) p :=
      (hasFDerivAt_fst).sub ((hasFDerivAt_snd).const_smul α)
    exact (hf (p.1 - α * p.2)).hasDerivAt.comp_hasFDerivAt p hg
  refine ⟨fun p => (key p).differentiableAt, fun p => ?_, fun x => by simp⟩
  rw [(key p).fderiv]
  simp
  ring

/-- DE-047 (Example 1.9.1, p. 72), uniqueness. Every differentiable `u` on `ℝ²` with `α u_x + u_t = 0` and
`u(x,0) = f(x)` equals `f(x - α t)`: along the characteristic line `s ↦ (x + α s, s)` it is constant. -/
@[kb "lebldiffyqs2026" "Example 1.9.1, p. 72"]
theorem transport_unique (α : ℝ) {f : ℝ → ℝ} {u : ℝ × ℝ → ℝ} (hu : Differentiable ℝ u)
    (heq : ∀ p : ℝ × ℝ, α * fderiv ℝ u p (1, 0) + fderiv ℝ u p (0, 1) = 0)
    (h0 : ∀ x, u (x, 0) = f x) (x t : ℝ) : u (x, t) = f (x - α * t) := by
  set a := x - α * t with ha
  have hline : ∀ s : ℝ, HasDerivAt (fun s : ℝ => (a + α * s, s)) (α * 1, 1) s := fun s =>
    (((hasDerivAt_id' s).const_mul α).const_add a).prodMk (hasDerivAt_id' s)
  have hw : ∀ s : ℝ, HasDerivAt (fun s : ℝ => u (a + α * s, s)) 0 s := by
    intro s
    have h1 : HasFDerivAt u (fderiv ℝ u (a + α * s, s)) ((fun s : ℝ => (a + α * s, s)) s) :=
      (hu (a + α * s, s)).hasFDerivAt
    have := HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => (a + α * s, s)) s h1 (hline s)
    have e : fderiv ℝ u (a + α * s, s) (α * 1, 1) = 0 := by
      have : ((α * 1, 1) : ℝ × ℝ) = α • ((1, 0) : ℝ × ℝ) + ((0, 1) : ℝ × ℝ) := by simp
      rw [this, map_add, map_smul, smul_eq_mul]
      exact heq _
    rw [e] at this
    exact this
  have hc := is_const_of_deriv_eq_zero (f := fun s : ℝ => u (a + α * s, s))
    (fun s => (hw s).differentiableAt) (fun s => (hw s).deriv) t 0
  simp only [mul_zero, add_zero] at hc
  have : a + α * t = x := by rw [ha]; ring
  rw [this] at hc
  rw [hc, h0]

/-- DE-048 (Section 1.9, Example 1.9.2, p. 74). Let `u` be differentiable with `a u_x + b u_t + c u = g`
(constants `a, b, c`). Along the characteristic line `s ↦ (x₀ + a s, t₀ + b s)` the function
`w(s) = u(x₀ + a s, t₀ + b s)` satisfies the linear ODE `w' + c w = g(x₀ + a s, t₀ + b s)`. -/
@[kb "lebldiffyqs2026" "Example 1.9.2, p. 74"]
theorem characteristic_ode {u g : ℝ × ℝ → ℝ} (hu : Differentiable ℝ u) {a b c : ℝ}
    (heq : ∀ p : ℝ × ℝ, a * fderiv ℝ u p (1, 0) + b * fderiv ℝ u p (0, 1) + c * u p = g p)
    (x₀ t₀ s : ℝ) :
    ∃ w' : ℝ, HasDerivAt (fun s : ℝ => u (x₀ + a * s, t₀ + b * s)) w' s ∧
      w' + c * u (x₀ + a * s, t₀ + b * s) = g (x₀ + a * s, t₀ + b * s) := by
  have hline : HasDerivAt (fun s : ℝ => (x₀ + a * s, t₀ + b * s)) (a * 1, b * 1) s :=
    (((hasDerivAt_id' s).const_mul a).const_add x₀).prodMk
      (((hasDerivAt_id' s).const_mul b).const_add t₀)
  have h1 : HasFDerivAt u (fderiv ℝ u (x₀ + a * s, t₀ + b * s))
      ((fun s : ℝ => (x₀ + a * s, t₀ + b * s)) s) := (hu (x₀ + a * s, t₀ + b * s)).hasFDerivAt
  refine ⟨_, HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => (x₀ + a * s, t₀ + b * s)) s h1 hline, ?_⟩
  have : ((a * 1, b * 1) : ℝ × ℝ) = a • ((1, 0) : ℝ × ℝ) + b • ((0, 1) : ℝ × ℝ) := by simp
  rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  exact heq _

end UndergradKB.DifferentialEquations
