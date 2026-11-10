import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import UndergradKB.Common.Attr

/-! Second-order linear ODEs with constant coefficients: undetermined coefficients, boundary value
problems, the RLC circuit and the power series method (OpenStax Calculus Volume 3, Chapter 7). -/

namespace UndergradKB.Calculus.ODEExtras

open Real Filter Topology

/-! ### Undetermined coefficients -/

/-- Derivative of `A e^{r x}`. -/
lemma ode_deriv_exp (A r : ℝ) :
    deriv (fun x : ℝ => A * exp (r * x)) = fun x => A * r * exp (r * x) := by
  funext x
  have h : HasDerivAt (fun x : ℝ => A * exp (r * x)) (A * (exp (r * x) * r)) x :=
    ((hasDerivAt_id x).const_mul r |>.exp).const_mul A |>.congr_deriv (by simp)
  rw [h.deriv]; ring

/-- OpenStax Calculus 3:Table 7.2 (CA-679). If `P(r) = a r² + b r + c ≠ 0` then
`(k / P(r)) e^{r x}` is a particular solution of `a y'' + b y' + c y = k e^{r x}`. -/
@[kb "openstaxcalculus2016" "3:Table 7.2, p. 767"]
theorem undetermined_exp (a b c k r : ℝ) (hP : a * r ^ 2 + b * r + c ≠ 0) (x : ℝ) :
    a * deriv (deriv (fun x : ℝ => k / (a * r ^ 2 + b * r + c) * exp (r * x))) x
      + b * deriv (fun x : ℝ => k / (a * r ^ 2 + b * r + c) * exp (r * x)) x
      + c * (k / (a * r ^ 2 + b * r + c) * exp (r * x)) = k * exp (r * x) := by
  rw [ode_deriv_exp, ode_deriv_exp]
  have key : (a * r ^ 2 + b * r + c) * (k / (a * r ^ 2 + b * r + c)) = k := mul_div_cancel₀ _ hP
  linear_combination (exp (r * x)) * key

/-- Derivative of `A x e^{r x}`. -/
lemma ode_deriv_xexp (A r : ℝ) :
    deriv (fun x : ℝ => A * (x * exp (r * x))) = fun x => A * exp (r * x) + A * r * (x * exp (r * x)) := by
  funext x
  have h : HasDerivAt (fun x : ℝ => A * (x * exp (r * x)))
      (A * (1 * exp (r * x) + x * (exp (r * x) * r))) x :=
    ((hasDerivAt_id x).mul (((hasDerivAt_id x).const_mul r).exp)).const_mul A
      |>.congr_deriv (by simp)
  rw [h.deriv]; ring

/-- OpenStax Calculus 3:Table 7.2 (CA-679), resonant case. If `r` is a simple root of the
characteristic polynomial (`a r² + b r + c = 0`, `2 a r + b ≠ 0`) then `(k / (2 a r + b)) x e^{r x}`
is a particular solution of `a y'' + b y' + c y = k e^{r x}`. -/
@[kb "openstaxcalculus2016" "3:§7.2 Strategy: Undetermined Coefficients, p. 768"]
theorem undetermined_exp_resonant (a b c k r : ℝ) (hP : a * r ^ 2 + b * r + c = 0)
    (hP' : 2 * a * r + b ≠ 0) (x : ℝ) :
    a * deriv (deriv (fun x : ℝ => k / (2 * a * r + b) * (x * exp (r * x)))) x
      + b * deriv (fun x : ℝ => k / (2 * a * r + b) * (x * exp (r * x))) x
      + c * (k / (2 * a * r + b) * (x * exp (r * x))) = k * exp (r * x) := by
  rw [ode_deriv_xexp (k / (2 * a * r + b)) r]
  beta_reduce
  have h1 : deriv (fun x : ℝ => k / (2 * a * r + b) * exp (r * x) +
      k / (2 * a * r + b) * r * (x * exp (r * x))) x =
      k / (2 * a * r + b) * r * exp (r * x) +
      (k / (2 * a * r + b) * r * exp (r * x) + k / (2 * a * r + b) * r * r * (x * exp (r * x))) := by
    have e1 := congrFun (ode_deriv_exp (k / (2 * a * r + b)) r) x
    have e2 := congrFun (ode_deriv_xexp (k / (2 * a * r + b) * r) r) x
    have hd1 : DifferentiableAt ℝ (fun x : ℝ => k / (2 * a * r + b) * exp (r * x)) x := by fun_prop
    have hd2 : DifferentiableAt ℝ (fun x : ℝ => k / (2 * a * r + b) * r * (x * exp (r * x))) x := by
      fun_prop
    have := hd1.hasDerivAt.fun_add hd2.hasDerivAt
    rw [this.deriv, e1, e2]
  rw [h1]
  have hK : (2 * a * r + b) * (k / (2 * a * r + b)) = k := mul_div_cancel₀ _ hP'
  generalize k / (2 * a * r + b) = K at hK ⊢
  linear_combination (exp (r * x)) * hK + (K * x * exp (r * x)) * hP

/-- OpenStax Calculus 3:Table 7.2 (CA-679), trigonometric right side. With `D = c - a ω²` and
`E = b ω`, if `D² + E² ≠ 0` (frequency `ω` is not resonant) then
`y = A cos ωx + B sin ωx`, `A = (D k - E l)/(D²+E²)`, `B = (D l + E k)/(D²+E²)` solves
`a y'' + b y' + c y = k cos ωx + l sin ωx`. -/
@[kb "openstaxcalculus2016" "3:Table 7.2, p. 767"]
theorem undetermined_trig (a b c k l ω : ℝ) (hΔ : (c - a * ω ^ 2) ^ 2 + (b * ω) ^ 2 ≠ 0) (x : ℝ) :
    a * deriv (deriv (fun x : ℝ =>
        ((c - a * ω ^ 2) * k - b * ω * l) / ((c - a * ω ^ 2) ^ 2 + (b * ω) ^ 2) * cos (ω * x)
        + ((c - a * ω ^ 2) * l + b * ω * k) / ((c - a * ω ^ 2) ^ 2 + (b * ω) ^ 2) * sin (ω * x))) x
      + b * deriv (fun x : ℝ =>
        ((c - a * ω ^ 2) * k - b * ω * l) / ((c - a * ω ^ 2) ^ 2 + (b * ω) ^ 2) * cos (ω * x)
        + ((c - a * ω ^ 2) * l + b * ω * k) / ((c - a * ω ^ 2) ^ 2 + (b * ω) ^ 2) * sin (ω * x)) x
      + c * (((c - a * ω ^ 2) * k - b * ω * l) / ((c - a * ω ^ 2) ^ 2 + (b * ω) ^ 2) * cos (ω * x)
        + ((c - a * ω ^ 2) * l + b * ω * k) / ((c - a * ω ^ 2) ^ 2 + (b * ω) ^ 2) * sin (ω * x))
      = k * cos (ω * x) + l * sin (ω * x) := by
  generalize hA : ((c - a * ω ^ 2) * k - b * ω * l) / ((c - a * ω ^ 2) ^ 2 + (b * ω) ^ 2) = A
  generalize hB : ((c - a * ω ^ 2) * l + b * ω * k) / ((c - a * ω ^ 2) ^ 2 + (b * ω) ^ 2) = B
  have d1 : deriv (fun x : ℝ => A * cos (ω * x) + B * sin (ω * x)) =
      fun x => -(A * ω) * sin (ω * x) + B * ω * cos (ω * x) := by
    funext x
    have h : HasDerivAt (fun x : ℝ => A * cos (ω * x) + B * sin (ω * x))
        (A * (-sin (ω * x) * ω) + B * (cos (ω * x) * ω)) x :=
      (((hasDerivAt_id x).const_mul ω).cos.const_mul A).add
        (((hasDerivAt_id x).const_mul ω).sin.const_mul B) |>.congr_deriv (by simp)
    rw [h.deriv]; ring
  have d2 : deriv (fun x : ℝ => -(A * ω) * sin (ω * x) + B * ω * cos (ω * x)) =
      fun x => -(A * ω ^ 2) * cos (ω * x) - B * ω ^ 2 * sin (ω * x) := by
    funext x
    have h : HasDerivAt (fun x : ℝ => -(A * ω) * sin (ω * x) + B * ω * cos (ω * x))
        (-(A * ω) * (cos (ω * x) * ω) + B * ω * (-sin (ω * x) * ω)) x :=
      (((hasDerivAt_id x).const_mul ω).sin.const_mul (-(A * ω))).add
        (((hasDerivAt_id x).const_mul ω).cos.const_mul (B * ω)) |>.congr_deriv (by simp)
    rw [h.deriv]; ring
  rw [d1, d2]
  have hAΔ : A * ((c - a * ω ^ 2) ^ 2 + (b * ω) ^ 2) = (c - a * ω ^ 2) * k - b * ω * l := by
    rw [← hA]; exact div_mul_cancel₀ _ hΔ
  have hBΔ : B * ((c - a * ω ^ 2) ^ 2 + (b * ω) ^ 2) = (c - a * ω ^ 2) * l + b * ω * k := by
    rw [← hB]; exact div_mul_cancel₀ _ hΔ
  have hD : (c - a * ω ^ 2) * A + b * ω * B = k := by
    apply mul_right_cancel₀ hΔ
    linear_combination (c - a * ω ^ 2) * hAΔ + b * ω * hBΔ
  have hE : (c - a * ω ^ 2) * B - b * ω * A = l := by
    apply mul_right_cancel₀ hΔ
    linear_combination (c - a * ω ^ 2) * hBΔ - b * ω * hAΔ
  linear_combination (cos (ω * x)) * hD + (sin (ω * x)) * hE

/-- The operator `q ↦ a q'' + b q' + c q` on real polynomials. -/
noncomputable def odeOp (a b c : ℝ) (q : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.C a * Polynomial.derivative (Polynomial.derivative q)
    + Polynomial.C b * Polynomial.derivative q + Polynomial.C c * q

lemma odeOp_coeff (a b c : ℝ) (q : Polynomial ℝ) (n : ℕ) :
    (odeOp a b c q).coeff n = a * (q.coeff (n + 2) * (n + 2) * (n + 1))
      + b * (q.coeff (n + 1) * (n + 1)) + c * q.coeff n := by
  simp only [odeOp, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_derivative]
  push_cast
  ring

lemma odeOp_exists (a b c : ℝ) (hc : c ≠ 0) :
    ∀ (n : ℕ) (p : Polynomial ℝ), p.natDegree ≤ n →
      ∃ q : Polynomial ℝ, q.natDegree ≤ n ∧ odeOp a b c q = p := by
  intro n
  induction n with
  | zero =>
    intro p hp
    refine ⟨Polynomial.C (p.coeff 0 / c), by simp, ?_⟩
    rw [Polynomial.eq_C_of_natDegree_le_zero hp]
    simp [odeOp]
    rw [← Polynomial.C_mul]
    congr 1
    field_simp
  | succ n ih =>
    intro p hp
    set q0 : Polynomial ℝ := Polynomial.C (p.coeff (n + 1) / c) * Polynomial.X ^ (n + 1) with hq0
    have hr : (p - odeOp a b c q0).natDegree ≤ n := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [Polynomial.coeff_sub, odeOp_coeff]
      simp only [hq0, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      rcases Nat.lt_or_ge (n + 1) N with h | h
      · have h1 : p.coeff N = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        have : N ≠ n + 1 := by omega
        have : N + 1 ≠ n + 1 := by omega
        have : N + 2 ≠ n + 1 := by omega
        have : N ≠ n := by omega
        have : N + 1 ≠ n := by omega
        simp [*]
      · have : N = n + 1 := by omega
        subst this
        have : n + 1 + 1 ≠ n + 1 := by omega
        have : n + 1 + 2 ≠ n + 1 := by omega
        simp [*]
        field_simp
        ring
    obtain ⟨q1, hq1, hq1e⟩ := ih _ hr
    refine ⟨q1 + q0, ?_, ?_⟩
    · refine (Polynomial.natDegree_add_le _ _).trans (max_le (by omega) ?_)
      exact (Polynomial.natDegree_C_mul_X_pow_le _ _)
    · have : odeOp a b c (q1 + q0) = odeOp a b c q1 + odeOp a b c q0 := by
        simp [odeOp]; ring
      rw [this, hq1e]; ring

/-- OpenStax Calculus 3:Table 7.2 (CA-679), polynomial right side. If `c ≠ 0` and `p` is a
polynomial of degree at most `n` then there is a polynomial `q` of degree at most `n` with
`a q'' + b q' + c q = p` (as functions of `x`). -/
@[kb "openstaxcalculus2016" "3:Table 7.2, p. 767"]
theorem undetermined_polynomial (a b c : ℝ) (hc : c ≠ 0) (p : Polynomial ℝ) :
    ∃ q : Polynomial ℝ, q.natDegree ≤ p.natDegree ∧
      ∀ x : ℝ, a * deriv (deriv (fun x : ℝ => q.eval x)) x + b * deriv (fun x : ℝ => q.eval x) x
        + c * q.eval x = p.eval x := by
  obtain ⟨q, hq, he⟩ := odeOp_exists a b c hc p.natDegree p le_rfl
  refine ⟨q, hq, fun x => ?_⟩
  have h1 : deriv (fun x : ℝ => q.eval x) = fun x => (Polynomial.derivative q).eval x := by
    funext x; exact Polynomial.deriv q
  have h2 : deriv (fun x : ℝ => (Polynomial.derivative q).eval x) =
      fun x => (Polynomial.derivative (Polynomial.derivative q)).eval x := by
    funext x; exact Polynomial.deriv _
  rw [h1, h2, ← he]
  simp [odeOp]

/-! ### Boundary value problems -/

/-- OpenStax Calculus 3:§7.1 (CA-675). `y` solves the two-point boundary value problem
`y'' = F(x, y, y')`, `y(x₀) = α`, `y(x₁) = β`: a twice differentiable solution of the second-order
equation whose values are prescribed at two different points. -/
def IsBVPSolution (F : ℝ → ℝ → ℝ → ℝ) (x₀ x₁ α β : ℝ) (y : ℝ → ℝ) : Prop :=
  Differentiable ℝ y ∧ Differentiable ℝ (deriv y) ∧
    (∀ x, deriv (deriv y) x = F x (y x) (deriv y x)) ∧ y x₀ = α ∧ y x₁ = β

/-- A solution of `y'' = -y` is determined by `y(0)` and `y'(0)`. -/
lemma sho_eq (y : ℝ → ℝ) (h1 : Differentiable ℝ y) (h2 : Differentiable ℝ (deriv y))
    (h : ∀ x, deriv (deriv y) x = -y x) :
    ∀ x, y x = y 0 * cos x + deriv y 0 * sin x := by
  intro x
  set Y : ℝ → ℝ := fun x => y 0 * cos x + deriv y 0 * sin x with hY
  set Y' : ℝ → ℝ := fun x => -(y 0) * sin x + deriv y 0 * cos x with hY'
  have hYd : ∀ x, HasDerivAt Y (Y' x) x := by
    intro x
    have := ((hasDerivAt_cos x).const_mul (y 0)).add ((hasDerivAt_sin x).const_mul (deriv y 0))
    convert this using 1
    simp [hY']
  have hY'd : ∀ x, HasDerivAt Y' (-Y x) x := by
    intro x
    have := ((hasDerivAt_sin x).const_mul (-(y 0))).add ((hasDerivAt_cos x).const_mul (deriv y 0))
    convert this using 1
    simp [hY]
    ring
  set E : ℝ → ℝ := fun x => (y x - Y x) ^ 2 + (deriv y x - Y' x) ^ 2 with hE
  have hEd : ∀ x, HasDerivAt E 0 x := by
    intro x
    have a1 := ((h1 x).hasDerivAt.sub (hYd x)).pow 2
    have a2 := (((h2 x).hasDerivAt).sub (hY'd x)).pow 2
    have := a1.add a2
    convert this using 1
    rw [h x]
    simp; ring
  have hconst : E x = E 0 := is_const_of_deriv_eq_zero
    (fun x => (hEd x).differentiableAt) (fun x => (hEd x).deriv) x 0
  have h0 : E 0 = 0 := by simp [hE, hY, hY']
  have hx : (y x - Y x) ^ 2 + (deriv y x - Y' x) ^ 2 = 0 := by
    have := hconst; rw [h0] at this; exact this
  have : y x - Y x = 0 := by nlinarith [sq_nonneg (y x - Y x), sq_nonneg (deriv y x - Y' x)]
  simpa [hY] using (sub_eq_zero.mp this)

/-- Differentiability facts for `c sin x`. -/
lemma sin_mul_bvp (c : ℝ) :
    IsBVPSolution (fun _ y _ => -y) 0 π 0 0 (fun x => c * sin x) := by
  have d1 : deriv (fun x : ℝ => c * sin x) = fun x => c * cos x := by
    funext x; exact ((hasDerivAt_sin x).const_mul c).deriv
  have d2 : deriv (fun x : ℝ => c * cos x) = fun x => -(c * sin x) := by
    funext x
    have := ((hasDerivAt_cos x).const_mul c).deriv
    rw [this]; ring
  refine ⟨by fun_prop, ?_, ?_, by simp, by simp⟩
  · rw [d1]; fun_prop
  · intro x; rw [d1, d2]

/-- OpenStax Calculus 3:§7.1 (CA-675). The boundary value problem `y'' + y = 0`, `y(0) = 0`,
`y(π) = 0` has infinitely many solutions (all multiples `c sin x`). -/
@[kb "openstaxcalculus2016" "3:§7.1 boundary conditions / boundary-value problem (unnumbered), p. 760"]
theorem bvp_sin_infinitely_many :
    {y : ℝ → ℝ | IsBVPSolution (fun _ y _ => -y) 0 π 0 0 y}.Infinite := by
  have hinj : Function.Injective (fun c : ℝ => (fun x : ℝ => c * sin x)) := by
    intro c d h
    have := congrFun h (π / 2)
    simpa using this
  refine Set.Infinite.mono (s := Set.range (fun c : ℝ => (fun x : ℝ => c * sin x))) ?_
    (Set.infinite_range_of_injective hinj)
  rintro _ ⟨c, rfl⟩
  exact sin_mul_bvp c

/-- OpenStax Calculus 3:§7.1 (CA-675). With the boundary conditions `y(0) = 0`, `y(π/2) = 1`
the equation `y'' + y = 0` has exactly one solution, namely `sin`. -/
@[kb "openstaxcalculus2016" "3:§7.1 boundary conditions / boundary-value problem (unnumbered), p. 760"]
theorem bvp_sin_unique :
    {y : ℝ → ℝ | IsBVPSolution (fun _ y _ => -y) 0 (π / 2) 0 1 y} = {sin} := by
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    have e := sho_eq y h1 h2 h3
    have e2 := e (π / 2)
    rw [h4] at e
    simp only [zero_mul, zero_add] at e e2
    rw [h5] at e2
    simp at e2
    funext x
    rw [e x, ← e2]; simp
  · rintro rfl
    have := sin_mul_bvp 1
    refine ⟨by fun_prop, ?_, ?_, by simp, by simp⟩
    · rw [Real.deriv_sin]; fun_prop
    · intro x; rw [Real.deriv_sin, Real.deriv_cos']

/-! ### RLC circuit -/

/-- Forced spring-mass equation `m q'' + b q' + k q = E(t)`. -/
def ForcedSpring (m b k : ℝ) (E q : ℝ → ℝ) : Prop :=
  ∀ t, m * deriv (deriv q) t + b * deriv q t + k * q t = E t

/-- Energy-type estimate: a solution of the damped equation tends to `0`. -/
theorem damped_solution_tendsto_zero (m b k : ℝ) (hm : 0 < m) (hb : 0 < b) (hk : 0 < k)
    (d : ℝ → ℝ) (hd : Differentiable ℝ d) (hd' : Differentiable ℝ (deriv d))
    (h : ∀ t, m * deriv (deriv d) t + b * deriv d t + k * d t = 0) :
    Tendsto d atTop (𝓝 0) := by
  set ε : ℝ := min 1 (min (b / (2 * m)) (k / (4 * m))) with hε
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεb : ε * m ≤ b / 2 := by
    have : ε ≤ b / (2 * m) := (min_le_right _ _).trans (min_le_left _ _)
    calc ε * m ≤ b / (2 * m) * m := by gcongr
      _ = b / 2 := by field_simp
  have hεk : ε * m ≤ k / 4 := by
    have : ε ≤ k / (4 * m) := (min_le_right _ _).trans (min_le_right _ _)
    calc ε * m ≤ k / (4 * m) * m := by gcongr
      _ = k / 4 := by field_simp
  set p : ℝ → ℝ := deriv d with hp
  set F : ℝ → ℝ := fun t => 1 / 2 * m * p t ^ 2 + 1 / 2 * k * d t ^ 2 + ε * m * (d t * p t)
    + 1 / 2 * ε * b * d t ^ 2 with hF
  set F' : ℝ → ℝ := fun t => -(b - ε * m) * p t ^ 2 - ε * k * d t ^ 2 with hF'
  have hFd : ∀ t, HasDerivAt F (F' t) t := by
    intro t
    have h1 := hd t |>.hasDerivAt
    have h2 := hd' t |>.hasDerivAt
    have e := ((((h2.pow 2).const_mul (1 / 2 * m)).add ((h1.pow 2).const_mul (1 / 2 * k))).add
      ((h1.mul h2).const_mul (ε * m))).add ((h1.pow 2).const_mul (1 / 2 * ε * b))
    refine HasDerivAt.congr_deriv e ?_
    have ht := h t
    simp only [hF']
    norm_num
    linear_combination (p t + ε * d t) * ht
  set ν : ℝ := min (b / 2) (ε * k) with hν
  have hν0 : 0 < ν := by positivity
  have hνb : ν ≤ b / 2 := min_le_left _ _
  have hνk : ν ≤ ε * k := min_le_right _ _
  set M : ℝ := m + k + b with hM
  have hM0 : 0 < M := by positivity
  set lam : ℝ := ν / M with hlam
  have hlam0 : 0 < lam := by positivity
  have hlamM : lam * M = ν := by rw [hlam]; field_simp
  have hlow : ∀ t, 1 / 4 * m * p t ^ 2 + 1 / 4 * k * d t ^ 2 ≤ F t := by
    intro t
    have a1 : 0 ≤ m * (p t / 2 + ε * d t) ^ 2 := by positivity
    have a2 : ε * ε * m ≤ k / 4 := by nlinarith
    have a3 : ε * ε * m * d t ^ 2 ≤ k / 4 * d t ^ 2 := mul_le_mul_of_nonneg_right a2 (sq_nonneg _)
    have a4 : 0 ≤ 1 / 2 * ε * b * d t ^ 2 := by positivity
    simp only [hF]
    nlinarith
  have hup : ∀ t, F t ≤ M * (p t ^ 2 + d t ^ 2) := by
    intro t
    have a1 : ε * m * (d t * p t) ≤ ε * m * ((p t ^ 2 + d t ^ 2) / 2) :=
      mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (d t - p t)]) (by positivity)
    have a2 : ε * m ≤ m := by nlinarith
    have a3 : ε * m * ((p t ^ 2 + d t ^ 2) / 2) ≤ m * ((p t ^ 2 + d t ^ 2) / 2) :=
      mul_le_mul_of_nonneg_right a2 (by positivity)
    have a4 : ε * b * d t ^ 2 ≤ b * d t ^ 2 :=
      mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
    have a5 : 0 ≤ m * p t ^ 2 := by positivity
    have a6 : 0 ≤ k * p t ^ 2 := by positivity
    have a7 : 0 ≤ b * p t ^ 2 := by positivity
    have a8 : 0 ≤ m * d t ^ 2 := by positivity
    have a9 : 0 ≤ k * d t ^ 2 := by positivity
    have a10 : 0 ≤ b * d t ^ 2 := by positivity
    simp only [hF, hM]
    nlinarith
  have hF'le : ∀ t, F' t ≤ -ν * (p t ^ 2 + d t ^ 2) := by
    intro t
    have a1 : ν * p t ^ 2 ≤ (b / 2) * p t ^ 2 := mul_le_mul_of_nonneg_right hνb (sq_nonneg _)
    have a2 : ν * d t ^ 2 ≤ (ε * k) * d t ^ 2 := mul_le_mul_of_nonneg_right hνk (sq_nonneg _)
    have a3 : (ε * m) * p t ^ 2 ≤ (b / 2) * p t ^ 2 := mul_le_mul_of_nonneg_right hεb (sq_nonneg _)
    simp only [hF']
    nlinarith
  set G : ℝ → ℝ := fun t => F t * exp (lam * t) with hG
  have hGd : ∀ t, HasDerivAt G (F' t * exp (lam * t) + F t * (exp (lam * t) * lam)) t := by
    intro t
    have := (hFd t).mul (((hasDerivAt_id t).const_mul lam).exp)
    exact this.congr_deriv (by simp)
  have hGanti : Antitone G := by
    apply antitone_of_deriv_nonpos (fun t => (hGd t).differentiableAt)
    intro t
    rw [(hGd t).deriv]
    have e1 : lam * F t ≤ ν * (p t ^ 2 + d t ^ 2) := by
      calc lam * F t ≤ lam * (M * (p t ^ 2 + d t ^ 2)) := mul_le_mul_of_nonneg_left (hup t) hlam0.le
        _ = ν * (p t ^ 2 + d t ^ 2) := by rw [← hlamM]; ring
    have e2 : F' t * exp (lam * t) + F t * (exp (lam * t) * lam)
        = (F' t + lam * F t) * exp (lam * t) := by ring
    rw [e2]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hF'le t]) (exp_pos _).le
  have hbound : ∀ t, 0 ≤ t → d t ^ 2 ≤ 4 * F 0 / k * exp (-(lam * t)) := by
    intro t ht
    have h1 : G t ≤ G 0 := hGanti ht
    have h0 : G 0 = F 0 := by simp [hG]
    rw [h0] at h1
    have hFt : F t ≤ F 0 * exp (-(lam * t)) := by
      have : F t = G t * exp (-(lam * t)) := by
        simp only [hG]; rw [mul_assoc, ← exp_add]; simp
      rw [this]
      exact mul_le_mul_of_nonneg_right h1 (exp_pos _).le
    have := hlow t
    have : k * d t ^ 2 ≤ 4 * (F 0 * exp (-(lam * t))) := by nlinarith [sq_nonneg (p t), hm]
    rw [div_mul_eq_mul_div, le_div_iff₀ hk]
    nlinarith
  have hexp : Tendsto (fun t : ℝ => exp (-(lam * t))) atTop (𝓝 0) :=
    tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hlam0)
  have hsq : Tendsto (fun t => d t ^ 2) atTop (𝓝 0) := by
    have := hexp.const_mul (4 * F 0 / k)
    rw [mul_zero] at this
    refine squeeze_zero' (Eventually.of_forall fun t => sq_nonneg _)
      ((eventually_ge_atTop 0).mono fun t ht => hbound t ht) this
  have habs : Tendsto (fun t => |d t|) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa [Function.comp_def, Real.sqrt_sq_eq_abs] using this
  exact tendsto_zero_iff_abs_tendsto_zero _ |>.mpr habs

/-- OpenStax Calculus 3:§7.3 Equation 7.9 (CA-688). The charge `q` on the capacitor of a series
RLC circuit satisfies `L q'' + R q' + q / C = E(t)`, which is the forced spring-mass equation
with mass `L`, damping `R` and spring constant `1/C`. -/
@[kb "openstaxcalculus2016" "3:§7.3 Equation 7.9 (RLC series circuit), p. 789"]
theorem rlc_iff_forcedSpring (L R C : ℝ) (E q : ℝ → ℝ) :
    (∀ t, L * deriv (deriv q) t + R * deriv q t + q t / C = E t) ↔ ForcedSpring L R (1 / C) E q := by
  unfold ForcedSpring
  simp [div_eq_inv_mul]

/-- OpenStax Calculus 3:§7.3 Equation 7.9 (CA-688). For `L, R, C > 0`, any two (twice
differentiable) solutions of the RLC equation `L q'' + R q' + q/C = E(t)` differ by a term
tending to `0` as `t → ∞`: the transient dies out. -/
@[kb "openstaxcalculus2016" "3:§7.3 Equation 7.9 (RLC series circuit), p. 789"]
theorem rlc_solutions_differ_by_transient (L R C : ℝ) (hL : 0 < L) (hR : 0 < R) (hC : 0 < C)
    (E q₁ q₂ : ℝ → ℝ) (h₁ : Differentiable ℝ q₁) (h₁' : Differentiable ℝ (deriv q₁))
    (h₂ : Differentiable ℝ q₂) (h₂' : Differentiable ℝ (deriv q₂))
    (e₁ : ∀ t, L * deriv (deriv q₁) t + R * deriv q₁ t + q₁ t / C = E t)
    (e₂ : ∀ t, L * deriv (deriv q₂) t + R * deriv q₂ t + q₂ t / C = E t) :
    Tendsto (fun t => q₁ t - q₂ t) atTop (𝓝 0) := by
  have d1 : deriv (fun t => q₁ t - q₂ t) = fun t => deriv q₁ t - deriv q₂ t := by
    funext t; exact deriv_sub (h₁ t) (h₂ t)
  have d2 : deriv (fun t => deriv q₁ t - deriv q₂ t) =
      fun t => deriv (deriv q₁) t - deriv (deriv q₂) t := by
    funext t; exact deriv_sub (h₁' t) (h₂' t)
  refine damped_solution_tendsto_zero L R (1 / C) hL hR (by positivity) _ (h₁.sub h₂)
    (by rw [d1]; exact h₁'.sub h₂') ?_
  intro t
  rw [d1, d2]
  have := e₁ t
  have := e₂ t
  simp only [one_div]
  rw [div_eq_inv_mul] at *
  linear_combination e₁ t - e₂ t

/-! ### Power series method -/

/-- Coefficients of the term-by-term derivative of `∑ c_n xⁿ`. -/
def dcoef (c : ℕ → ℝ) (n : ℕ) : ℝ := ((n : ℝ) + 1) * c (n + 1)

/-- The sum of the power series `∑ c_n xⁿ`. -/
noncomputable def psum (c : ℕ → ℝ) (x : ℝ) : ℝ := ∑' n, c n * x ^ n

/-- The power series with coefficients `c` has infinite radius of convergence (it converges
absolutely at every point). -/
def EntireCoeff (c : ℕ → ℝ) : Prop := ∀ R : ℝ, 0 ≤ R → Summable fun n => |c n| * R ^ n

lemma nat_mul_pow_le (R : ℝ) (hR : 0 ≤ R) (n : ℕ) : (n : ℝ) * R ^ (n - 1) ≤ (R + 1) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : R ^ n ≤ (R + 1) ^ n := pow_le_pow_left₀ hR (by linarith) n
    rcases n with _ | n
    · simpa using hR
    · simp only [Nat.add_sub_cancel] at ih ⊢
      push_cast at ih ⊢
      calc ((n : ℝ) + 1 + 1) * R ^ (n + 1) = ((n : ℝ) + 1) * R ^ n * R + R ^ (n + 1) := by ring
        _ ≤ (R + 1) ^ (n + 1) * R + (R + 1) ^ (n + 1) := by
          have := mul_le_mul_of_nonneg_right ih hR
          have h2 : R ^ (n + 1) ≤ (R + 1) ^ (n + 1) := pow_le_pow_left₀ hR (by linarith) _
          linarith
        _ = (R + 1) ^ (n + 1 + 1) := by ring

lemma entireCoeff_dcoef {c : ℕ → ℝ} (hc : EntireCoeff c) : EntireCoeff (dcoef c) := by
  intro R hR
  have hs : Summable fun n => |c (n + 1)| * (R + 1) ^ (n + 1) :=
    (summable_nat_add_iff 1).mpr (hc (R + 1) (by linarith))
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
  have := nat_mul_pow_le R hR (n + 1)
  simp only [Nat.add_sub_cancel] at this
  push_cast at this
  simp only [dcoef]
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
  calc ((n : ℝ) + 1) * |c (n + 1)| * R ^ n = |c (n + 1)| * (((n : ℝ) + 1) * R ^ n) := by ring
    _ ≤ |c (n + 1)| * (R + 1) ^ (n + 1) := mul_le_mul_of_nonneg_left this (abs_nonneg _)

lemma summable_psum_terms {c : ℕ → ℝ} (hc : EntireCoeff c) (x : ℝ) :
    Summable fun n => c n * x ^ n := by
  refine Summable.of_norm ?_
  simpa [abs_mul, abs_pow] using hc |x| (abs_nonneg x)

/-- OpenStax Calculus 3:§7.4 (CA-689). Term-by-term differentiation: a power series with infinite
radius of convergence is differentiable everywhere, with derivative the series of the
differentiated terms, `(∑ c_n xⁿ)' = ∑ (n+1) c_{n+1} xⁿ`. -/
@[kb "openstaxcalculus2016" "3:§7.4 Strategy: Finding Power Series Solutions, p. 793"]
theorem hasDerivAt_psum {c : ℕ → ℝ} (hc : EntireCoeff c) (x : ℝ) :
    HasDerivAt (psum c) (psum (dcoef c) x) x := by
  set R : ℝ := |x| + 1 with hR
  have hRpos : 0 < R := by positivity
  have hR0 : 0 ≤ R := hRpos.le
  have hu : Summable fun n => |c n| * (R + 1) ^ n := hc _ (by linarith)
  have hb : ∀ (n : ℕ) (y : ℝ), y ∈ Set.Ioo (-R) R →
      ‖c n * ((n : ℝ) * y ^ (n - 1))‖ ≤ |c n| * (R + 1) ^ n := by
    intro n y hy
    have hy' : |y| ≤ R := abs_le.mpr ⟨hy.1.le, hy.2.le⟩
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, Nat.abs_cast]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    calc (n : ℝ) * |y| ^ (n - 1) ≤ n * R ^ (n - 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hy' _) (by positivity)
      _ ≤ (R + 1) ^ n := nat_mul_pow_le R hR0 n
  have hmem : x ∈ Set.Ioo (-R) R := by
    constructor <;> [linarith [neg_abs_le x]; linarith [le_abs_self x]]
  have key := hasDerivAt_tsum_of_isPreconnected (g := fun (n : ℕ) (y : ℝ) => c n * y ^ n)
    (g' := fun n y => c n * ((n : ℝ) * y ^ (n - 1))) (y₀ := 0) hu isOpen_Ioo isPreconnected_Ioo
    (fun n y _ => (hasDerivAt_pow n y).const_mul (c n)) hb
    (by constructor <;> linarith [hRpos]) (summable_psum_terms hc 0) hmem
  have hsf : Summable fun n : ℕ => c n * ((n : ℝ) * x ^ (n - 1)) :=
    Summable.of_norm_bounded hu (fun n => hb n x hmem)
  have : ∑' n : ℕ, c n * ((n : ℝ) * x ^ (n - 1)) = psum (dcoef c) x := by
    rw [hsf.tsum_eq_zero_add]
    simp only [psum, dcoef]
    simp only [CharP.cast_eq_zero, zero_mul, mul_zero, zero_add]
    refine tsum_congr fun n => ?_
    push_cast
    ring
  rw [this] at key
  exact key

/-- OpenStax Calculus 3:§7.4 (CA-689). The power series method, justified. If `∑ c_n xⁿ` has
infinite radius of convergence and the coefficients satisfy the recursion obtained by equating
coefficients of `xⁿ` in `y'' + β y' + γ y = 0`, namely
`(n+2)(n+1) c_{n+2} + β (n+1) c_{n+1} + γ c_n = 0` for all `n`, then `y = ∑ c_n xⁿ` solves
`y'' + β y' + γ y = 0` on all of `ℝ`. -/
@[kb "openstaxcalculus2016" "3:§7.4 Strategy: Finding Power Series Solutions, p. 793"]
theorem power_series_method {c : ℕ → ℝ} (hc : EntireCoeff c) (β γ : ℝ)
    (hrec : ∀ n : ℕ, ((n : ℝ) + 2) * ((n : ℝ) + 1) * c (n + 2) + β * (((n : ℝ) + 1) * c (n + 1))
      + γ * c n = 0) (x : ℝ) :
    deriv (deriv (psum c)) x + β * deriv (psum c) x + γ * psum c x = 0 := by
  have h1 : deriv (psum c) = psum (dcoef c) := funext fun x => (hasDerivAt_psum hc x).deriv
  have hc1 := entireCoeff_dcoef hc
  have h2 : deriv (psum (dcoef c)) = psum (dcoef (dcoef c)) :=
    funext fun x => (hasDerivAt_psum hc1 x).deriv
  have hc2 := entireCoeff_dcoef hc1
  rw [h1, h2]
  have s0 := summable_psum_terms hc x
  have s1 := summable_psum_terms hc1 x
  have s2 := summable_psum_terms hc2 x
  have : psum (dcoef (dcoef c)) x + β * psum (dcoef c) x + γ * psum c x
      = ∑' n, (dcoef (dcoef c) n + β * dcoef c n + γ * c n) * x ^ n := by
    simp only [psum, add_mul, mul_assoc]
    rw [Summable.tsum_add (s2.add (s1.mul_left β)) (s0.mul_left γ),
      Summable.tsum_add s2 (s1.mul_left β), tsum_mul_left, tsum_mul_left]
  rw [this]
  have hz : ∀ n, (dcoef (dcoef c) n + β * dcoef c n + γ * c n) * x ^ n = 0 := by
    intro n
    have := hrec n
    simp only [dcoef]
    push_cast
    linear_combination x ^ n * this
  simp [hz]

/-- OpenStax Calculus 3:§7.4 Example 7.25 (CA-689). Special case `y'' + y = 0`: the recursion
`(n+2)(n+1) c_{n+2} = - c_n` makes `∑ c_n xⁿ` a solution. -/
@[kb "openstaxcalculus2016" "3:Example 7.25, p. 793"]
theorem power_series_oscillator {c : ℕ → ℝ} (hc : EntireCoeff c)
    (hrec : ∀ n : ℕ, ((n : ℝ) + 2) * ((n : ℝ) + 1) * c (n + 2) = -c n) (x : ℝ) :
    deriv (deriv (psum c)) x + psum c x = 0 := by
  have := power_series_method hc 0 1 (fun n => by linear_combination hrec n) x
  simpa using this

end UndergradKB.Calculus.ODEExtras
