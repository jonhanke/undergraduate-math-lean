import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import UndergradKB.Common.Attr

/-! # Calculus: first-order differential equations and exponential models

OpenStax Calculus 1 §6.8 and Calculus 2 §§2.8, 4.2-4.5: linear equations with an integrating factor, exponential growth
and decay, Newton's law of cooling, doubling time and half-life, continuous compounding, separable equations,
equilibria, the logistic equation. -/

open Real Set Filter Topology

namespace UndergradKB.Calculus

/-- A function with derivative zero everywhere is constant. -/
lemma const_of_hasDerivAt_zero {g : ℝ → ℝ} (h : ∀ x, HasDerivAt g 0 x) (x y : ℝ) : g x = g y :=
  is_const_of_deriv_eq_zero (fun x => (h x).differentiableAt) (fun x => (h x).deriv) x y

/-- OpenStax Calculus 2:§4.5 Integrating factor (CA-326). For `y' + p y = q` with `P` an antiderivative of `p`
(so `μ = exp P` is an integrating factor) and `q` continuous, `y` solves the equation exactly when
`y x = (1/μ x) (∫_{x0}^x μ q + C)` for some constant `C`. -/
@[kb "openstaxcalculus2016" "2:§4.5 Integrating factor, p. 367"]
theorem linear_first_order_iff {p q P y : ℝ → ℝ} (hq : Continuous q) (hP : ∀ x, HasDerivAt P (p x) x)
    (x0 : ℝ) :
    (∀ x, HasDerivAt y (q x - p x * y x) x) ↔
      ∃ C : ℝ, ∀ x, y x = Real.exp (-P x) * ((∫ t in x0..x, Real.exp (P t) * q t) + C) := by
  have hPc : Continuous P := continuous_iff_continuousAt.2 fun x => (hP x).continuousAt
  have hcont : Continuous fun t => Real.exp (P t) * q t := (Real.continuous_exp.comp hPc).mul hq
  have hI : ∀ x, HasDerivAt (fun u => ∫ t in x0..u, Real.exp (P t) * q t) (Real.exp (P x) * q x) x :=
    fun x => (hcont.integral_hasStrictDerivAt x0 x).hasDerivAt
  constructor
  · intro h
    have hF : ∀ x, HasDerivAt (fun u => Real.exp (P u) * y u - ∫ t in x0..u, Real.exp (P t) * q t) 0 x := by
      intro x
      have h1 := ((hP x).exp).mul (h x)
      have := h1.sub (hI x)
      convert this using 1
      ring
    refine ⟨Real.exp (P x0) * y x0, fun x => ?_⟩
    have := const_of_hasDerivAt_zero hF x x0
    simp only [intervalIntegral.integral_same, sub_zero] at this
    have h2 : Real.exp (P x) * y x = (∫ t in x0..x, Real.exp (P t) * q t) + Real.exp (P x0) * y x0 := by
      linarith
    have : y x = Real.exp (-P x) * (Real.exp (P x) * y x) := by
      rw [Real.exp_neg]; field_simp
    rw [this, h2]
  · rintro ⟨C, hC⟩ x
    have hy : y = fun x => Real.exp (-P x) * ((∫ t in x0..x, Real.exp (P t) * q t) + C) := funext hC
    have h1 := ((hP x).neg.exp).mul ((hI x).add_const C)
    rw [hy]
    convert h1 using 1
    simp only [Pi.neg_apply]
    have : Real.exp (-P x) * Real.exp (P x) = 1 := by rw [← Real.exp_add]; simp
    linear_combination (-(q x)) * this

/-! ### Exponential growth and decay, Newton's law of cooling -/

/-- OpenStax Calculus 1:§6.8 Rule: Exponential Growth Model (CA-294); 2:§2.8 (CA-305); 2:§4.3 (CA-318).
General form: `y' = k y` on `ℝ` holds iff `y t = y 0 * exp (k t)`. -/
@[kb "openstaxcalculus2016" "2:§4.3 Equation (exponential growth/decay), p. 352"]
theorem exp_model_iff {y : ℝ → ℝ} {k : ℝ} :
    (∀ t, HasDerivAt y (k * y t) t) ↔ ∀ t, y t = y 0 * Real.exp (k * t) := by
  constructor
  · intro h
    have hg : ∀ t, HasDerivAt (fun u => y u * Real.exp (-(k * u))) 0 t := by
      intro t
      have h1 : HasDerivAt (fun u => Real.exp (-(k * u))) (Real.exp (-(k * t)) * (-k)) t :=
        (((hasDerivAt_id t).const_mul k).neg.exp).congr_deriv (by simp)
      have := (h t).mul h1
      convert this using 1
      ring
    intro t
    have := const_of_hasDerivAt_zero hg t 0
    simp only [mul_zero, neg_zero, Real.exp_zero, mul_one] at this
    have e : Real.exp (-(k * t)) * Real.exp (k * t) = 1 := by rw [← Real.exp_add]; simp
    calc y t = y t * (Real.exp (-(k * t)) * Real.exp (k * t)) := by rw [e, mul_one]
      _ = y 0 * Real.exp (k * t) := by rw [← mul_assoc, this]
  · intro h t
    have hy : y = fun t => y 0 * Real.exp (k * t) := funext h
    have h1 : HasDerivAt (fun t => y 0 * Real.exp (k * t)) (y 0 * (Real.exp (k * t) * k)) t :=
      ((((hasDerivAt_id t).const_mul k).exp).const_mul (y 0)).congr_deriv (by simp)
    rw [hy]
    convert h1 using 1
    ring

/-- OpenStax Calculus 1:§6.8 exponential growth model (CA-294), 2:§2.8 (CA-305): for `k > 0`,
`y' = k y` iff `y t = y0 e^{kt}` with `y0 = y 0`. -/
@[kb "openstaxcalculus2016" "1:§6.8 Rule: Exponential Growth Model (6.27), p. 645"]
theorem exp_growth_iff {y : ℝ → ℝ} {k : ℝ} (_hk : 0 < k) :
    (∀ t, HasDerivAt y (k * y t) t) ↔ ∀ t, y t = y 0 * Real.exp (k * t) := exp_model_iff

/-- OpenStax Calculus 2:§2.8 Rule: Exponential Growth Model (CA-305), initial value `y0` given explicitly. -/
@[kb "openstaxcalculus2016" "2:§2.8 Rule: Exponential Growth Model, p. 212"]
theorem exp_growth_ivp {y : ℝ → ℝ} {k y0 : ℝ} (hk : 0 < k) (h0 : y 0 = y0) :
    (∀ t, HasDerivAt y (k * y t) t) ↔ ∀ t, y t = y0 * Real.exp (k * t) := by
  rw [exp_growth_iff hk, h0]

/-- OpenStax Calculus 1:§6.8 Rule: Exponential Decay Model (CA-297); 2:§2.8 (CA-307): for `k > 0`,
`y' = -k y` iff `y t = y0 e^{-kt}`. -/
@[kb "openstaxcalculus2016" "1:§6.8 Rule: Exponential Decay Model, p. 648"]
theorem exp_decay_iff {y : ℝ → ℝ} {k : ℝ} (_hk : 0 < k) :
    (∀ t, HasDerivAt y (-k * y t) t) ↔ ∀ t, y t = y 0 * Real.exp (-k * t) := exp_model_iff

/-- OpenStax Calculus 2:§2.8 Rule: Exponential Decay Model (CA-307), initial value given explicitly. -/
@[kb "openstaxcalculus2016" "2:§2.8 Rule: Exponential Decay Model, p. 215"]
theorem exp_decay_ivp {y : ℝ → ℝ} {k y0 : ℝ} (hk : 0 < k) (h0 : y 0 = y0) :
    (∀ t, HasDerivAt y (-k * y t) t) ↔ ∀ t, y t = y0 * Real.exp (-k * t) := by
  rw [exp_decay_iff hk, h0]

/-- OpenStax Calculus 2:§4.3 Equation (CA-318): `y' = k y` has the solutions `y0 e^{kt}` for every real `k`
(growth for `k > 0`, decay for `k < 0`), and these are all. -/
@[kb "openstaxcalculus2016" "2:§4.3 Equation (exponential growth/decay), p. 352"]
theorem exp_model_ivp {y : ℝ → ℝ} {k y0 : ℝ} (h0 : y 0 = y0) :
    (∀ t, HasDerivAt y (k * y t) t) ↔ ∀ t, y t = y0 * Real.exp (k * t) := by
  rw [exp_model_iff, h0]

/-- General Newton's law of cooling: `T' = c (T - Ta)` iff `T t = Ta + (T 0 - Ta) e^{ct}`. -/
theorem cooling_general_iff {T : ℝ → ℝ} {c Ta : ℝ} :
    (∀ t, HasDerivAt T (c * (T t - Ta)) t) ↔ ∀ t, T t = Ta + (T 0 - Ta) * Real.exp (c * t) := by
  have key := @exp_model_iff (fun t => T t - Ta) c
  constructor
  · intro h t
    have h' := key.1 (fun t => (h t).sub_const Ta) t
    linarith
  · intro h t
    have h' : ∀ t, (fun t => T t - Ta) t = (fun t => T t - Ta) 0 * Real.exp (c * t) := by
      intro t; simp only; rw [h t]; ring
    have := (key.2 h' t).add_const Ta
    simpa using this

/-- OpenStax Calculus 1:§6.8 (CA-298), 2:§2.8 (CA-308): Newton's law of cooling `T' = -k (T - Ta)` iff
`T t = Ta + (T 0 - Ta) e^{-kt}`. -/
@[kb "openstaxcalculus2016" "1:§6.8 Newton's law of cooling solution, p. 649"]
theorem newton_cooling_iff {T : ℝ → ℝ} {k Ta : ℝ} :
    (∀ t, HasDerivAt T (-k * (T t - Ta)) t) ↔ ∀ t, T t = Ta + (T 0 - Ta) * Real.exp (-k * t) :=
  cooling_general_iff

/-- OpenStax Calculus 2:§4.3 Key Equation (CA-319): `T' = k (T - Ta)` iff `T t = Ta + (T 0 - Ta) e^{kt}`. -/
@[kb "openstaxcalculus2016" "2:§4.3 Key Equation (Newton's law of cooling), p. 377"]
theorem newton_cooling_pos_iff {T : ℝ → ℝ} {k Ta : ℝ} :
    (∀ t, HasDerivAt T (k * (T t - Ta)) t) ↔ ∀ t, T t = Ta + (T 0 - Ta) * Real.exp (k * t) :=
  cooling_general_iff

/-! ### Doubling time and half-life -/

lemma exp_mul_eq_two_iff {k s : ℝ} (hk : k ≠ 0) : Real.exp (k * s) = 2 ↔ s = Real.log 2 / k := by
  rw [eq_div_iff hk]
  constructor
  · intro h
    rw [mul_comm, ← h, Real.log_exp]
  · intro h
    rw [mul_comm, h, Real.exp_log (by norm_num)]

/-- OpenStax Calculus 1:§6.8 doubling time (CA-296); 2:§2.8 (CA-306). For `y t = y0 e^{kt}` with `y0 ≠ 0`,
`k ≠ 0`: `y (t + s) = 2 y t` holds (for one, equivalently every, `t`) exactly when `s = ln 2 / k`. -/
@[kb "openstaxcalculus2016" "1:§6.8 Definition (doubling time), p. 648"]
theorem doubling_time_iff {y : ℝ → ℝ} {y0 k : ℝ} (hy0 : y0 ≠ 0) (hk : k ≠ 0)
    (hy : ∀ t, y t = y0 * Real.exp (k * t)) (t s : ℝ) :
    y (t + s) = 2 * y t ↔ s = Real.log 2 / k := by
  rw [← exp_mul_eq_two_iff hk, hy, hy, mul_add, Real.exp_add]
  have hne : y0 * Real.exp (k * t) ≠ 0 := mul_ne_zero hy0 (Real.exp_pos _).ne'
  constructor
  · intro h
    have : (y0 * Real.exp (k * t)) * Real.exp (k * s) = (y0 * Real.exp (k * t)) * 2 := by
      linarith
    exact mul_left_cancel₀ hne this
  · intro h
    rw [h]; ring

/-- OpenStax Calculus 2:§2.8 doubling time (CA-306): for `k > 0` a quantity `y0 e^{kt}` doubles after the
time `ln 2 / k` (which is positive). -/
@[kb "openstaxcalculus2016" "2:§2.8 Definition (doubling time), p. 215"]
theorem doubling_time {y0 k : ℝ} (hk : 0 < k) (t : ℝ) :
    0 < Real.log 2 / k ∧
      y0 * Real.exp (k * (t + Real.log 2 / k)) = 2 * (y0 * Real.exp (k * t)) := by
  refine ⟨div_pos (Real.log_pos (by norm_num)) hk, ?_⟩
  rw [mul_add, Real.exp_add, mul_div_cancel₀ _ hk.ne', Real.exp_log (by norm_num)]
  ring

/-- OpenStax Calculus 1:§6.8 half-life (CA-299); 2:§2.8 (CA-309). For `y t = y0 e^{-kt}` with `y0 ≠ 0`,
`k ≠ 0`: `y (t + s) = y t / 2` exactly when `s = ln 2 / k`. -/
@[kb "openstaxcalculus2016" "1:§6.8 Definition (half-life), p. 650"]
theorem half_life_iff {y : ℝ → ℝ} {y0 k : ℝ} (hy0 : y0 ≠ 0) (hk : k ≠ 0)
    (hy : ∀ t, y t = y0 * Real.exp (-k * t)) (t s : ℝ) :
    y (t + s) = y t / 2 ↔ s = Real.log 2 / k := by
  rw [← exp_mul_eq_two_iff hk, hy, hy, mul_add, Real.exp_add]
  have hne : y0 * Real.exp (-k * t) ≠ 0 := mul_ne_zero hy0 (Real.exp_pos _).ne'
  have hs : Real.exp (-k * s) = (Real.exp (k * s))⁻¹ := by
    rw [← Real.exp_neg]; ring_nf
  rw [hs]
  constructor
  · intro h
    have h2 : (y0 * Real.exp (-k * t)) * (Real.exp (k * s))⁻¹ = (y0 * Real.exp (-k * t)) * 2⁻¹ := by
      linear_combination h
    have h3 := mul_left_cancel₀ hne h2
    exact inv_injective (by rw [h3])
  · intro h
    rw [h]; ring

/-- OpenStax Calculus 2:§2.8 half-life (CA-309): for `k > 0` a quantity `y0 e^{-kt}` halves after the time
`ln 2 / k` (which is positive). -/
@[kb "openstaxcalculus2016" "2:§2.8 Definition (half-life), p. 217"]
theorem half_life {y0 k : ℝ} (hk : 0 < k) (t : ℝ) :
    0 < Real.log 2 / k ∧
      y0 * Real.exp (-k * (t + Real.log 2 / k)) = y0 * Real.exp (-k * t) / 2 := by
  refine ⟨div_pos (Real.log_pos (by norm_num)) hk, ?_⟩
  have : -k * (Real.log 2 / k) = -Real.log 2 := by field_simp
  rw [mul_add, Real.exp_add, this, Real.exp_neg, Real.exp_log (by norm_num)]
  ring

/-! ### Continuous compounding -/

/-- OpenStax Calculus 1:§6.8 continuous compounding (CA-295): `P0 (1 + r/n)^(n t) → P0 e^{r t}` as `n → ∞`. -/
@[kb "openstaxcalculus2016" "1:§6.8 continuous compound interest, p. 647"]
theorem compound_interest_tendsto (P0 r t : ℝ) :
    Tendsto (fun n : ℕ => P0 * (1 + r / n) ^ ((n : ℝ) * t)) atTop (𝓝 (P0 * Real.exp (r * t))) := by
  have h1 : Tendsto (fun n : ℕ => (1 + r / (n : ℝ)) ^ (n : ℝ)) atTop (𝓝 (Real.exp r)) :=
    (Real.tendsto_one_add_div_rpow_exp r).comp tendsto_natCast_atTop_atTop
  have h2 := h1.rpow_const (p := t) (Or.inl (Real.exp_pos r).ne')
  have h3 : Tendsto (fun n : ℕ => 1 + r / (n : ℝ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat r)
  have h4 : ∀ᶠ n : ℕ in atTop, 0 < 1 + r / (n : ℝ) := h3.eventually_const_lt (by norm_num)
  have h5 : Tendsto (fun n : ℕ => (1 + r / n) ^ ((n : ℝ) * t)) atTop (𝓝 (Real.exp (r * t))) := by
    rw [Real.exp_mul]
    refine h2.congr' ?_
    filter_upwards [h4] with n hn
    rw [Real.rpow_mul hn.le]
  exact h5.const_mul P0

/-! ### Equilibria and separable equations -/

/-- OpenStax Calculus 2:§4.2 Definition (CA-313): for `y' = f y`, the constant function `c` is a solution
iff `f c = 0`. -/
@[kb "openstaxcalculus2016" "2:§4.2 Definition (equilibrium solution), p. 329"]
theorem equilibrium_iff {f : ℝ → ℝ} (c : ℝ) :
    (∀ x, HasDerivAt (fun _ : ℝ => c) (f c) x) ↔ f c = 0 := by
  constructor
  · intro h
    exact (h 0).unique (hasDerivAt_const 0 c)
  · intro h x
    rw [h]; exact hasDerivAt_const x c

/-- OpenStax Calculus 2:§4.3 separation of variables (CA-317), constant solutions: if `h c = 0`, the constant
function `c` solves `y' = g(x) h(y)`. -/
@[kb "openstaxcalculus2016" "2:§4.3 Problem-Solving Strategy (separation of variables), p. 342"]
theorem separable_const_solution {g h : ℝ → ℝ} {c : ℝ} (hc : h c = 0) :
    ∀ x, HasDerivAt (fun _ : ℝ => c) (g x * h c) x := by
  intro x
  rw [hc, mul_zero]; exact hasDerivAt_const x c

/-- OpenStax Calculus 2:§4.3 separation of variables (CA-317), non-constant solutions. On an open interval
`(a, b)`, let `y` be differentiable with `h (y x) ≠ 0`, `H' = 1/h` (at the values of `y`) and `G' = g`.
Then `y' = g(x) h(y)` holds on the interval iff `H (y x) = G x + C` there for some constant `C`. -/
@[kb "openstaxcalculus2016" "2:§4.3 Problem-Solving Strategy (separation of variables), p. 342"]
theorem separable_iff {a b : ℝ} {g h G H y : ℝ → ℝ}
    (hy : ∀ x ∈ Ioo a b, DifferentiableAt ℝ y x) (hh : ∀ x ∈ Ioo a b, h (y x) ≠ 0)
    (hH : ∀ x ∈ Ioo a b, HasDerivAt H (1 / h (y x)) (y x))
    (hG : ∀ x ∈ Ioo a b, HasDerivAt G (g x) x) :
    (∀ x ∈ Ioo a b, HasDerivAt y (g x * h (y x)) x) ↔ ∃ C : ℝ, ∀ x ∈ Ioo a b, H (y x) = G x + C := by
  have hcomp : ∀ x ∈ Ioo a b, HasDerivAt (fun x => H (y x)) (1 / h (y x) * deriv y x) x :=
    fun x hx => ((hH x hx).scomp x (hy x hx).hasDerivAt).congr_deriv (by simp [mul_comm])
  constructor
  · intro hsol
    have hF : ∀ x ∈ Ioo a b, HasDerivAt (fun x => H (y x) - G x) 0 x := by
      intro x hx
      have := (hcomp x hx).sub (hG x hx)
      convert this using 1
      rw [(hsol x hx).deriv]
      field_simp [hh x hx]
      ring
    by_cases hne : (Ioo a b).Nonempty
    · obtain ⟨x1, hx1⟩ := hne
      refine ⟨H (y x1) - G x1, fun x hx => ?_⟩
      have := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
        (f := fun x => H (y x) - G x)
        (fun x hx => (hF x hx).differentiableAt.differentiableWithinAt)
        (fun x hx => (hF x hx).deriv) hx hx1
      linarith
    · exact ⟨0, fun x hx => absurd ⟨x, hx⟩ hne⟩
  · rintro ⟨C, hC⟩ x hx
    have hev : (fun x => H (y x)) =ᶠ[𝓝 x] fun x => G x + C := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with z hz using hC z hz
    have h1 : HasDerivAt (fun x => H (y x)) (g x) x :=
      ((hG x hx).add_const C).congr_of_eventuallyEq hev
    have h2 := (hcomp x hx).unique h1
    have h3 : deriv y x = g x * h (y x) := by
      have := hh x hx
      field_simp at h2
      linarith
    rw [← h3]
    exact (hy x hx).hasDerivAt

/-! ### The logistic equation -/

/-- The logistic solution `P(t) = P0 K e^{rt} / (K + P0 (e^{rt} - 1))` of `P' = r P (1 - P/K)`, `P(0) = P0`
(OpenStax Calculus 2, §4.4). -/
noncomputable def logisticSol (K r P0 t : ℝ) : ℝ :=
  P0 * K * Real.exp (r * t) / (K + P0 * (Real.exp (r * t) - 1))

/-- The logistic formula takes the value `P0` at `t = 0` (for `K ≠ 0`). -/
theorem logisticSol_zero {K r P0 : ℝ} (hK : K ≠ 0) : logisticSol K r P0 0 = P0 := by
  simp only [logisticSol, mul_zero, Real.exp_zero, sub_self, mul_zero, add_zero, mul_one]
  field_simp

/-- OpenStax Calculus 2:Theorem 4.2 (CA-322): the formula solves the logistic equation `P' = r P (1 - P/K)`
wherever its denominator is nonzero (it is positive for all `t` when `0 < P0 ≤ K`, and always for `t ≥ 0`
when `r, P0, K > 0`). -/
@[kb "openstaxcalculus2016" "2:Theorem 4.2, p. 359"]
theorem logisticSol_hasDerivAt {K r P0 : ℝ} (hK : K ≠ 0) (t : ℝ)
    (hD : K + P0 * (Real.exp (r * t) - 1) ≠ 0) :
    HasDerivAt (logisticSol K r P0)
      (r * logisticSol K r P0 t * (1 - logisticSol K r P0 t / K)) t := by
  have e : HasDerivAt (fun t => Real.exp (r * t)) (Real.exp (r * t) * r) t :=
    (((hasDerivAt_id t).const_mul r).exp).congr_deriv (by simp)
  have := (e.const_mul (P0 * K)).div (((e.sub_const 1).const_mul P0).const_add K) hD
  unfold logisticSol
  convert this using 1
  field_simp

/-- OpenStax Calculus 2:Theorem 4.2, Example 4.14 (CA-322), uniqueness: every solution `Q` of
`Q' = r Q (1 - Q/K)` on `ℝ` with `Q 0 = P0` and `Q > 0` (`K ≠ 0`, `P0 > 0`) equals the logistic formula. -/
@[kb "openstaxcalculus2016" "2:Theorem 4.2, p. 359"]
theorem logistic_unique {K r P0 : ℝ} {Q : ℝ → ℝ} (hK : K ≠ 0) (hP0 : 0 < P0)
    (hQ : ∀ t, HasDerivAt Q (r * Q t * (1 - Q t / K)) t) (hQ0 : Q 0 = P0) (hpos : ∀ t, 0 < Q t) :
    ∀ t, Q t = logisticSol K r P0 t := by
  have hu : ∀ t, HasDerivAt (fun t => (Q t)⁻¹) ((-r) * ((Q t)⁻¹ - 1 / K)) t := by
    intro t
    have hne := (hpos t).ne'
    refine ((hQ t).inv hne).congr_deriv ?_
    field_simp
  have key := cooling_general_iff.1 hu
  intro t
  have h1 := key t
  have hE : Real.exp (-r * t) = (Real.exp (r * t))⁻¹ := by rw [neg_mul, Real.exp_neg]
  have hEpos := Real.exp_pos (r * t)
  have h2 : (Q t)⁻¹ = (K + P0 * (Real.exp (r * t) - 1)) / (P0 * K * Real.exp (r * t)) := by
    rw [h1, hE, hQ0]
    field_simp
    ring
  have h3 : Q t = ((Q t)⁻¹)⁻¹ := (inv_inv _).symm
  rw [h3, h2, inv_div]
  rfl

/-- OpenStax Calculus 2:§4.4 inflection point (CA-323). For `r > 0`, `0 < P0 < K` and `P` the logistic solution,
put `ts = ln((K - P0)/P0) / r`. Then `P'' = r² P (1 - P/K)(1 - 2P/K)`; `P'' = 0` iff `P t = K/2` iff `t = ts`;
`P'' > 0` before `ts` and `P'' < 0` after `ts` (growth accelerates, then slows); also `ts > 0` iff `P0 < K/2`. -/
@[kb "openstaxcalculus2016" "2:§4.4 text on point of inflection, p. 359"]
theorem logistic_inflection {K r P0 : ℝ} (hr : 0 < r) (hP0 : 0 < P0) (hPK : P0 < K) :
    let P := logisticSol K r P0
    let ts := Real.log ((K - P0) / P0) / r
    (∀ t, deriv (deriv P) t = r ^ 2 * P t * (1 - P t / K) * (1 - 2 * P t / K)) ∧
    (∀ t, deriv (deriv P) t = 0 ↔ P t = K / 2) ∧
    (∀ t, P t = K / 2 ↔ t = ts) ∧
    (∀ t, t < ts → 0 < deriv (deriv P) t) ∧
    (∀ t, ts < t → deriv (deriv P) t < 0) ∧
    (0 < ts ↔ P0 < K / 2) := by
  intro P ts
  have hK : 0 < K := hP0.trans hPK
  have hc : 0 < (K - P0) / P0 := div_pos (by linarith) hP0
  have hD : ∀ t, 0 < K + P0 * (Real.exp (r * t) - 1) := by
    intro t
    have := Real.exp_pos (r * t)
    nlinarith
  have hder : ∀ t, HasDerivAt P (r * P t * (1 - P t / K)) t :=
    fun t => logisticSol_hasDerivAt hK.ne' t (hD t).ne'
  have hPpos : ∀ t, 0 < P t := fun t =>
    div_pos (by have := Real.exp_pos (r * t); positivity) (hD t)
  have hPK' : ∀ t, P t < K := by
    intro t
    have := Real.exp_pos (r * t)
    have : P t = P0 * K * Real.exp (r * t) / (K + P0 * (Real.exp (r * t) - 1)) := rfl
    rw [this, div_lt_iff₀ (hD t)]
    nlinarith
  have hd1 : deriv P = fun t => r * P t * (1 - P t / K) := funext fun t => (hder t).deriv
  have hd2 : ∀ t, deriv (deriv P) t = r ^ 2 * P t * (1 - P t / K) * (1 - 2 * P t / K) := by
    intro t
    rw [hd1]
    have h : HasDerivAt (fun t => r * P t * (1 - P t / K))
        (r * (r * P t * (1 - P t / K)) * (1 - P t / K) +
          r * P t * -(r * P t * (1 - P t / K) / K)) t :=
      ((hder t).const_mul r).mul (((hder t).div_const K).const_sub 1)
    rw [h.deriv]
    field_simp
    ring
  -- sign of `P t - K/2`
  have hsign : ∀ t, P t - K / 2 =
      K * (P0 * Real.exp (r * t) - (K - P0)) / (2 * (K + P0 * (Real.exp (r * t) - 1))) := by
    intro t
    have := (hD t).ne'
    have : P t = P0 * K * Real.exp (r * t) / (K + P0 * (Real.exp (r * t) - 1)) := rfl
    rw [this]
    field_simp
    ring
  have hlt : ∀ t, P t < K / 2 ↔ t < ts := by
    intro t
    have h1 : P t < K / 2 ↔ P t - K / 2 < 0 := by constructor <;> intro h <;> linarith
    rw [h1, hsign, div_neg_iff]
    have hDpos := hD t
    have : ¬ (0 < K * (P0 * Real.exp (r * t) - (K - P0)) ∧ 2 * (K + P0 * (Real.exp (r * t) - 1)) < 0) := by
      rintro ⟨-, h⟩; linarith
    simp only [this, false_or]
    constructor
    · rintro ⟨h1, -⟩
      have h2 : Real.exp (r * t) < (K - P0) / P0 := by
        rw [lt_div_iff₀ hP0]
        by_contra hh
        have hh := not_lt.1 hh
        nlinarith
      have h3 : r * t < Real.log ((K - P0) / P0) := (Real.lt_log_iff_exp_lt hc).2 h2
      simp only [ts]
      rw [lt_div_iff₀ hr]
      linarith
    · intro h
      have h3 : r * t < Real.log ((K - P0) / P0) := by
        simp only [ts] at h
        rw [lt_div_iff₀ hr] at h
        linarith
      have h2 := (Real.lt_log_iff_exp_lt hc).1 h3
      rw [lt_div_iff₀ hP0] at h2
      refine ⟨?_, by linarith⟩
      nlinarith
  have heq : ∀ t, P t = K / 2 ↔ t = ts := by
    intro t
    have h1 : P t = K / 2 ↔ Real.exp (r * t) = (K - P0) / P0 := by
      rw [← sub_eq_zero, hsign, div_eq_zero_iff, eq_div_iff hP0.ne']
      have : (2 * (K + P0 * (Real.exp (r * t) - 1))) ≠ 0 := by
        have := hD t; positivity
      simp only [this, or_false, mul_eq_zero, hK.ne', false_or]
      constructor <;> intro h <;> linarith
    rw [h1]
    constructor
    · intro h
      have : r * t = Real.log ((K - P0) / P0) := by rw [← h, Real.log_exp]
      simp only [ts]
      rw [eq_div_iff hr.ne']
      linarith
    · intro h
      have : r * t = Real.log ((K - P0) / P0) := by
        simp only [ts] at h
        rw [h]; field_simp
      rw [this, Real.exp_log hc]
  have hfac : ∀ t, 0 < r ^ 2 * P t * (1 - P t / K) := by
    intro t
    have h1 : 0 < 1 - P t / K := by
      have := hPK' t
      rw [sub_pos, div_lt_one hK]; exact this
    have := hPpos t
    positivity
  refine ⟨hd2, ?_, heq, ?_, ?_, ?_⟩
  · intro t
    rw [hd2]
    constructor
    · intro h
      have h1 := hfac t
      have h2 : 1 - 2 * P t / K = 0 := by
        rcases mul_eq_zero.1 h with h | h
        · exact absurd h h1.ne'
        · exact h
      field_simp at h2
      linarith
    · intro h
      rw [h]; field_simp; ring
  · intro t ht
    rw [hd2]
    have h1 := (hlt t).2 ht
    have : 0 < 1 - 2 * P t / K := by
      have : 2 * P t / K < 1 := by rw [div_lt_one hK]; linarith
      linarith
    exact mul_pos (hfac t) this
  · intro t ht
    rw [hd2]
    have h1 : ¬ P t < K / 2 := fun h => absurd ((hlt t).1 h) (not_lt.2 ht.le)
    have h2 : P t ≠ K / 2 := fun h => ht.ne ((heq t).1 h).symm
    have : 1 - 2 * P t / K < 0 := by
      have : 1 < 2 * P t / K := by
        rw [one_lt_div hK]
        rcases lt_or_gt_of_ne h2 with h | h
        · exact absurd h h1
        · linarith
      linarith
    exact mul_neg_of_pos_of_neg (hfac t) this
  · simp only [ts]
    rw [div_pos_iff_of_pos_right hr, Real.log_pos_iff hc.le, one_lt_div hP0]
    constructor <;> intro h <;> linarith

/-! ### Euler's method -/

/-- OpenStax Calculus 2:Theorem 4.1 (CA-315). The Euler iterates for `y' = f x y`, `y x0 = y0` with step `h`:
`y_0 = y0`, `y_{n+1} = y_n + h f(x_n, y_n)` with `x_n = x0 + n h`. -/
noncomputable def eulerIter (f : ℝ → ℝ → ℝ) (x0 y0 h : ℝ) : ℕ → ℝ
  | 0 => y0
  | n + 1 => eulerIter f x0 y0 h n + h * f (x0 + n * h) (eulerIter f x0 y0 h n)

/-- One Euler step is accurate to second order: if `y' = z` and `|z'| ≤ M` then
`|y(x+h) - y(x) - h z(x)| ≤ M h² / 2` for `h ≥ 0`. -/
theorem euler_local_error {y z w : ℝ → ℝ} {M : ℝ} (hy : ∀ x, HasDerivAt y (z x) x)
    (hz : ∀ x, HasDerivAt z (w x) x) (hw : ∀ x, |w x| ≤ M) (x : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    |y (x + h) - y x - h * z x| ≤ M * h ^ 2 / 2 := by
  have step1 : ∀ s, 0 ≤ s → |z (x + s) - z x| ≤ M * s := by
    intro s hs
    have := norm_image_sub_le_of_norm_deriv_le_segment' (f := z) (f' := w) (a := x) (b := x + s)
      (C := M) (fun u _ => (hz u).hasDerivWithinAt) (fun u _ => hw u) (x + s)
      ⟨by linarith, le_rfl⟩
    simpa using this
  have hψ : ∀ s, HasDerivAt (fun s => y (x + s) - y x - s * z x) (z (x + s) - z x) s := by
    intro s
    have h1 : HasDerivAt (fun s => y (x + s)) (z (x + s)) s := by
      exact (hy (x + s)).comp_const_add x s
    exact ((h1.sub_const (y x)).sub ((hasDerivAt_id s).mul_const (z x))).congr_deriv (by simp)
  have hB : ∀ s : ℝ, HasDerivAt (fun s => M * s ^ 2 / 2) (M * s) s := by
    intro s
    have := ((hasDerivAt_pow 2 s).const_mul M).div_const 2
    convert this using 1
    simp; ring
  have := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := fun s => y (x + s) - y x - s * z x) (f' := fun s => z (x + s) - z x) (a := 0) (b := h)
    (B := fun s => M * s ^ 2 / 2) (B' := fun s => M * s)
    (fun s _ => (hψ s).continuousAt.continuousWithinAt)
    (fun s _ => (hψ s).hasDerivWithinAt) (by simp) hB
    (fun s hs => by rw [Real.norm_eq_abs]; exact step1 s hs.1) (x := h) ⟨hh, le_rfl⟩
  simpa using this

/-- OpenStax Calculus 2:Theorem 4.1 / Example 4.9 (CA-315), error bound for Euler's method. Let `y` solve
`y' = f x y` on `ℝ` with `y x0 = y0`, where `f` is Lipschitz in `y` with constant `L > 0` and
`(f x (y x))' = w x` is bounded by `M` (a bound on `y''`). Then for step `h > 0` the Euler iterate after `n` steps
satisfies `|y(x0 + n h) - y_n| ≤ (M h / (2 L)) (e^{L n h} - 1)`: the error is first order in `h`. -/
@[kb "openstaxcalculus2016" "2:Theorem 4.1, p. 333"]
theorem euler_error_bound {f : ℝ → ℝ → ℝ} {y w : ℝ → ℝ} {L M x0 y0 h : ℝ} (hL : 0 < L) (hh : 0 < h)
    (hlip : ∀ x u v, |f x u - f x v| ≤ L * |u - v|)
    (hy : ∀ x, HasDerivAt y (f x (y x)) x)
    (hz : ∀ x, HasDerivAt (fun x => f x (y x)) (w x) x) (hw : ∀ x, |w x| ≤ M)
    (hy0 : y x0 = y0) (n : ℕ) :
    |y (x0 + n * h) - eulerIter f x0 y0 h n| ≤ M * h / (2 * L) * (Real.exp (L * (n * h)) - 1) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hw 0)
  set a := 1 + h * L with ha
  have hapos : 0 ≤ a := by positivity
  have hhL : 0 < h * L := by positivity
  have step : ∀ n : ℕ, |y (x0 + ((n + 1 : ℕ) : ℝ) * h) - eulerIter f x0 y0 h (n + 1)| ≤
      M * h ^ 2 / 2 + a * |y (x0 + n * h) - eulerIter f x0 y0 h n| := by
    intro n
    set xn := x0 + (n : ℝ) * h with hxn
    set Yn := eulerIter f x0 y0 h n
    have hx : x0 + ((n + 1 : ℕ) : ℝ) * h = xn + h := by push_cast; ring
    have hloc := euler_local_error hy hz hw xn hh.le
    have hdecomp : y (x0 + ((n + 1 : ℕ) : ℝ) * h) - eulerIter f x0 y0 h (n + 1) =
        (y (xn + h) - y xn - h * f xn (y xn)) + (y xn - Yn) + h * (f xn (y xn) - f xn Yn) := by
      rw [hx]
      show _ = _
      simp only [eulerIter]
      ring
    rw [hdecomp]
    have hl : |h * (f xn (y xn) - f xn Yn)| ≤ h * L * |y xn - Yn| := by
      rw [abs_mul, abs_of_pos hh]
      calc h * |f xn (y xn) - f xn Yn| ≤ h * (L * |y xn - Yn|) :=
            mul_le_mul_of_nonneg_left (hlip _ _ _) hh.le
        _ = h * L * |y xn - Yn| := by ring
    calc _ ≤ |y (xn + h) - y xn - h * f xn (y xn)| + |y xn - Yn| + |h * (f xn (y xn) - f xn Yn)| :=
          (abs_add_three _ _ _)
      _ ≤ M * h ^ 2 / 2 + a * |y xn - Yn| := by rw [ha]; nlinarith
  have main : ∀ n : ℕ, |y (x0 + n * h) - eulerIter f x0 y0 h n| * (h * L) ≤
      M * h ^ 2 / 2 * (a ^ n - 1) := by
    intro n
    induction n with
    | zero => simp [eulerIter, hy0]
    | succ n ih =>
      have s := step n
      have h1 := mul_le_mul_of_nonneg_right s hhL.le
      have h2 := mul_le_mul_of_nonneg_left ih hapos
      rw [pow_succ a n]
      have : h * L = a - 1 := by rw [ha]; ring
      rw [this] at h1 h2 ⊢
      nlinarith
  have hexp : a ^ n ≤ Real.exp (L * (n * h)) := by
    calc a ^ n ≤ (Real.exp (h * L)) ^ n :=
          pow_le_pow_left₀ hapos (by rw [ha]; linarith [Real.add_one_le_exp (h * L)]) n
      _ = Real.exp (L * (n * h)) := by rw [← Real.exp_nat_mul]; ring_nf
  have := main n
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : 0 < 2 * L)]
  have key : |y (x0 + n * h) - eulerIter f x0 y0 h n| * (2 * L) * h ≤
      M * h ^ 2 / 2 * (a ^ n - 1) * 2 := by nlinarith
  have hm : M * h ^ 2 / 2 * (a ^ n - 1) * 2 ≤ M * h ^ 2 * (Real.exp (L * (n * h)) - 1) := by
    nlinarith [mul_nonneg hM (sq_nonneg h)]
  have : |y (x0 + n * h) - eulerIter f x0 y0 h n| * (2 * L) * h ≤
      M * h * (Real.exp (L * (n * h)) - 1) * h := by nlinarith
  exact le_of_mul_le_mul_right this hh

/-! ### Stability of equilibria -/

/-- `y` solves the autonomous equation `y' = f y` for `t ≥ 0`. -/
def IsSolFrom (f : ℝ → ℝ) (y : ℝ → ℝ) : Prop := ∀ t, 0 ≤ t → HasDerivAt y (f (y t)) t

/-- OpenStax Calculus 2:§4.2 Definition (CA-314), one-sided attraction: every solution starting on the set `S`
close enough to `c` tends to `c`. -/
def AttractsFrom (S : Set ℝ) (f : ℝ → ℝ) (c : ℝ) : Prop :=
  ∃ δ > 0, ∀ y, IsSolFrom f y → y 0 ∈ S → |y 0 - c| < δ → Tendsto y atTop (𝓝 c)

/-- OpenStax Calculus 2:§4.2 Definition (CA-314), one-sided repulsion: there is `ε > 0` such that solutions
starting on `S` arbitrarily close to `c` leave the `ε`-neighbourhood at some time. -/
def RepelsFrom (S : Set ℝ) (f : ℝ → ℝ) (c : ℝ) : Prop :=
  ∃ ε > 0, ∀ δ > 0, ∃ y, IsSolFrom f y ∧ y 0 ∈ S ∧ |y 0 - c| < δ ∧ ∃ t, 0 ≤ t ∧ ε ≤ |y t - c|

/-- OpenStax Calculus 2:§4.2 (CA-314): `c` is an asymptotically stable solution of `y' = f y`: nearby solutions
tend to `c`. -/
def AsympStable (f : ℝ → ℝ) (c : ℝ) : Prop := AttractsFrom univ f c

/-- OpenStax Calculus 2:§4.2 (CA-314): `c` is an unstable solution: nearby solutions move away. -/
def Unstable (f : ℝ → ℝ) (c : ℝ) : Prop := RepelsFrom univ f c

/-- OpenStax Calculus 2:§4.2 (CA-314): `c` is semi-stable: solutions approach it from one side and move away on
the other. -/
def SemiStable (f : ℝ → ℝ) (c : ℝ) : Prop :=
  (AttractsFrom (Iio c) f c ∧ RepelsFrom (Ioi c) f c) ∨ (AttractsFrom (Ioi c) f c ∧ RepelsFrom (Iio c) f c)

/-- OpenStax Calculus 2:§4.2 (CA-314), linearized stability test: if `f c = 0` and `f'(c) < 0`, the equilibrium
`c` of `y' = f y` is asymptotically stable. -/
@[kb "openstaxcalculus2016" "2:§4.2 Definition (asymptotically stable / unstable / semi-stable solution), p. 329"]
theorem asympStable_of_deriv_neg {f : ℝ → ℝ} {c d : ℝ} (hfc : f c = 0) (hd : HasDerivAt f d c)
    (hneg : d < 0) : AsympStable f c := by
  set κ := -d with hκ
  have hκpos : 0 < κ := by rw [hκ]; linarith
  -- sign estimate near `c`
  have hev := (hasDerivAt_iff_isLittleO.1 hd).def (half_pos hκpos)
  obtain ⟨η, hη0, hη⟩ := Metric.eventually_nhds_iff.1 hev
  have hest : ∀ u, |u - c| < η → f u * (u - c) ≤ -(κ / 2) * (u - c) ^ 2 := by
    intro u hu
    have := hη (y := u) (by rwa [Real.dist_eq])
    rw [Real.norm_eq_abs, Real.norm_eq_abs, hfc, smul_eq_mul] at this
    have h1 : |f u - 0 - (u - c) * d| * |u - c| ≤ κ / 2 * |u - c| * |u - c| :=
      mul_le_mul_of_nonneg_right this (abs_nonneg _)
    have h2 : |(f u - 0 - (u - c) * d) * (u - c)| ≤ κ / 2 * (u - c) ^ 2 := by
      rw [abs_mul]
      calc _ ≤ κ / 2 * |u - c| * |u - c| := h1
        _ = κ / 2 * (u - c) ^ 2 := by rw [mul_assoc, ← sq, sq_abs]
    have h3 := (abs_le.1 h2).2
    have : f u * (u - c) = (f u - 0 - (u - c) * d) * (u - c) + d * (u - c) ^ 2 := by ring
    rw [this, hκ]
    nlinarith
  refine ⟨η, hη0, ?_⟩
  intro y hy _ hy0
  have hycont : ContinuousOn y (Ici 0) := fun t ht => (hy t ht).continuousAt.continuousWithinAt
  set r := |y 0 - c| with hr
  set r' := (r + η) / 2 with hr'
  have hr'lt : r' < η := by rw [hr']; linarith
  have hr'gt : r < r' := by rw [hr']; linarith
  have hr0 : 0 ≤ r := abs_nonneg _
  -- Step A: the solution stays within `r'` of `c`
  have hA : ∀ t, 0 ≤ t → (y t - c) ^ 2 ≤ r' ^ 2 := by
    intro t ht
    rcases ht.eq_or_lt with rfl | htpos
    · rw [← sq_abs, ← hr]; nlinarith
    have hfence := image_le_of_deriv_right_lt_deriv_boundary'
      (f := fun t => (y t - c) ^ 2) (f' := fun t => 2 * (y t - c) * f (y t))
      (B := fun _ => r' ^ 2) (B' := fun _ => 0) (a := 0) (b := t)
      (fun s hs => ((hycont.mono (Icc_subset_Ici_self)) s hs).sub_const c |>.pow 2 |> fun h => h)
      (fun s hs => by
        have := ((hy s hs.1).sub_const c).pow 2
        refine (this.congr_deriv ?_).hasDerivWithinAt
        simp)
      (by show (y 0 - c) ^ 2 ≤ r' ^ 2
          rw [← sq_abs, ← hr]; nlinarith) continuousOn_const
      (fun s _ => (hasDerivAt_const s _).hasDerivWithinAt)
      (fun s hs heq => by
        have h1 : |y s - c| = r' := by
          have : |y s - c| ^ 2 = r' ^ 2 := by rw [sq_abs]; exact heq
          exact (sq_eq_sq₀ (abs_nonneg _) (by linarith)).1 this
        have h2 := hest (y s) (by rw [h1]; exact hr'lt)
        have h3 : 0 < (y s - c) ^ 2 := by
          rw [← sq_abs, h1]; have : 0 < r' := by linarith
          positivity
        have : 2 * (y s - c) * f (y s) = 2 * (f (y s) * (y s - c)) := by ring
        show 2 * (y s - c) * f (y s) < 0
        rw [this]
        nlinarith)
    exact hfence (x := t) ⟨le_of_lt htpos, le_rfl⟩
  -- Step B: `V t = (y t - c)^2` decays like `exp (-κ t)`
  have hV : ∀ t, 0 ≤ t → HasDerivAt (fun t => (y t - c) ^ 2 * Real.exp (κ * t))
      ((2 * (y t - c) * f (y t) + κ * (y t - c) ^ 2) * Real.exp (κ * t)) t := by
    intro t ht
    have h1 := ((hy t ht).sub_const c).pow 2
    have h2 : HasDerivAt (fun t => Real.exp (κ * t)) (Real.exp (κ * t) * κ) t :=
      (((hasDerivAt_id t).const_mul κ).exp).congr_deriv (by simp)
    refine (h1.mul h2).congr_deriv ?_
    simp; ring
  have hanti : AntitoneOn (fun t => (y t - c) ^ 2 * Real.exp (κ * t)) (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) ?_ ?_ ?_
    · intro t ht
      exact (hV t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      exact (hV t (le_of_lt ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht0 : 0 ≤ t := le_of_lt ht
      rw [(hV t ht0).deriv]
      have h1 : |y t - c| < η := by
        have := hA t ht0
        have h2 : |y t - c| ≤ r' := by
          rw [← sq_le_sq₀ (abs_nonneg _) (by linarith), sq_abs]; exact this
        linarith
      have h2 := hest (y t) h1
      have : 2 * (y t - c) * f (y t) + κ * (y t - c) ^ 2 ≤ 0 := by nlinarith
      exact mul_nonpos_of_nonpos_of_nonneg this (Real.exp_pos _).le
  have hVle : ∀ t, 0 ≤ t → (y t - c) ^ 2 ≤ (y 0 - c) ^ 2 * Real.exp (-κ * t) := by
    intro t ht
    have := hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht
    simp only [mul_zero, Real.exp_zero, mul_one] at this
    have e : Real.exp (-κ * t) * Real.exp (κ * t) = 1 := by rw [← Real.exp_add]; simp
    calc (y t - c) ^ 2 = (y t - c) ^ 2 * Real.exp (κ * t) * Real.exp (-κ * t) := by
          rw [mul_assoc, mul_comm (Real.exp (κ * t)), e, mul_one]
      _ ≤ (y 0 - c) ^ 2 * Real.exp (-κ * t) :=
          mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
  -- Step C: convergence
  have hlim : Tendsto (fun t : ℝ => Real.sqrt ((y 0 - c) ^ 2 * Real.exp (-κ * t))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => Real.exp (-κ * t)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith : -κ < 0))
    have h2 := (h1.const_mul ((y 0 - c) ^ 2))
    rw [mul_zero] at h2
    have h3 := (Real.continuous_sqrt.tendsto 0).comp h2
    rw [Real.sqrt_zero] at h3
    exact h3
  have : Tendsto (fun t => y t - c) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (hVle t ht)
  simpa using this.add_const c

end UndergradKB.Calculus
