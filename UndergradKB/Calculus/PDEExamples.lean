import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import UndergradKB.Common.Attr

/-! Verified solutions of the two-dimensional heat equation, the two-dimensional wave equation
and Laplace's equation (OpenStax Calculus Volume 3, §4.6, equations 4.17 to 4.19).
Partial derivatives are derivatives of sections (all other variables frozen). -/

namespace UndergradKB.Calculus.PDEExamples

open Real

/-- Partial derivative in `t` of `u(t, x, y)`. -/
noncomputable def pT (u : ℝ → ℝ → ℝ → ℝ) (t x y : ℝ) : ℝ := deriv (fun s => u s x y) t
/-- Partial derivative in `x` of `u(t, x, y)`. -/
noncomputable def pX (u : ℝ → ℝ → ℝ → ℝ) (t x y : ℝ) : ℝ := deriv (fun s => u t s y) x
/-- Partial derivative in `y` of `u(t, x, y)`. -/
noncomputable def pY (u : ℝ → ℝ → ℝ → ℝ) (t x y : ℝ) : ℝ := deriv (fun s => u t x s) y

/-- OpenStax Calculus 3:Equation 4.17 (CA-526). `u(t,x,y)` solves the two-dimensional heat equation
`u_t = α² (u_xx + u_yy)`. -/
def HeatEq2D (α : ℝ) (u : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ t x y, pT u t x y = α ^ 2 * (pX (pX u) t x y + pY (pY u) t x y)

/-- OpenStax Calculus 3:Equation 4.18 (CA-526). `u(t,x,y)` solves the two-dimensional wave equation
`u_tt = c² (u_xx + u_yy)`. -/
def WaveEq2D (c : ℝ) (u : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ t x y, pT (pT u) t x y = c ^ 2 * (pX (pX u) t x y + pY (pY u) t x y)

/-- OpenStax Calculus 3:Equation 4.19 (CA-526). `v(x,y)` solves Laplace's equation
`v_xx + v_yy = 0`. -/
def LaplaceEq2D (v : ℝ → ℝ → ℝ) : Prop :=
  ∀ x y, deriv (fun s => deriv (fun r => v r y) s) x + deriv (fun s => deriv (fun r => v x r) s) y = 0

/-- Separated functions `f(t) g(x) h(y)`. -/
def sep (f g h : ℝ → ℝ) (t x y : ℝ) : ℝ := f t * g x * h y

lemma sep_pT (f g h : ℝ → ℝ) (hf : Differentiable ℝ f) :
    pT (sep f g h) = sep (deriv f) g h := by
  funext t x y
  exact (((hf t).hasDerivAt.mul_const (g x)).mul_const (h y)).deriv

lemma sep_pX (f g h : ℝ → ℝ) (hg : Differentiable ℝ g) :
    pX (sep f g h) = sep f (deriv g) h := by
  funext t x y
  exact ((((hg x).hasDerivAt.const_mul (f t))).mul_const (h y)).deriv.trans (by simp [sep, mul_assoc])

lemma sep_pY (f g h : ℝ → ℝ) (hh : Differentiable ℝ h) :
    pY (sep f g h) = sep f g (deriv h) := by
  funext t x y
  exact (((hh y).hasDerivAt.const_mul (f t * g x))).deriv

/-- `e^{-l t}`. -/
noncomputable def expL (l : ℝ) (t : ℝ) : ℝ := exp (-l * t)
/-- `sin (a x)`. -/
noncomputable def sinL (a : ℝ) (x : ℝ) : ℝ := sin (a * x)
/-- `cos (a x)`. -/
noncomputable def cosL (a : ℝ) (x : ℝ) : ℝ := cos (a * x)

lemma diff_expL (l : ℝ) : Differentiable ℝ (expL l) := by unfold expL; fun_prop
lemma diff_sinL (a : ℝ) : Differentiable ℝ (sinL a) := by unfold sinL; fun_prop
lemma diff_cosL (a : ℝ) : Differentiable ℝ (cosL a) := by unfold cosL; fun_prop

lemma deriv_expL (l : ℝ) : deriv (expL l) = fun t => -l * expL l t := by
  funext t
  have : HasDerivAt (expL l) (exp (-l * t) * (-l * 1)) t :=
    ((hasDerivAt_id t).const_mul (-l)).exp.congr_deriv (by simp)
  rw [this.deriv]; simp only [expL]; ring

lemma deriv_sinL (a : ℝ) : deriv (sinL a) = fun x => a * cosL a x := by
  funext x
  have : HasDerivAt (sinL a) (cos (a * x) * (a * 1)) x :=
    ((hasDerivAt_id x).const_mul a).sin.congr_deriv (by simp)
  rw [this.deriv]; simp only [cosL]; ring

lemma deriv_cosL (a : ℝ) : deriv (cosL a) = fun x => -(a * sinL a x) := by
  funext x
  have : HasDerivAt (cosL a) (-sin (a * x) * (a * 1)) x :=
    ((hasDerivAt_id x).const_mul a).cos.congr_deriv (by simp)
  rw [this.deriv]; simp only [sinL]; ring

lemma deriv_deriv_sinL (a : ℝ) : deriv (deriv (sinL a)) = fun x => -(a ^ 2 * sinL a x) := by
  rw [deriv_sinL]
  funext x
  have := (diff_cosL a x).hasDerivAt.const_mul a
  rw [this.deriv, show deriv (cosL a) x = -(a * sinL a x) by rw [deriv_cosL]]
  ring

lemma deriv_deriv_cosL (a : ℝ) : deriv (deriv (cosL a)) = fun x => -(a ^ 2 * cosL a x) := by
  rw [deriv_cosL]
  funext x
  have := ((diff_sinL a x).hasDerivAt.const_mul a).fun_neg
  rw [this.deriv, show deriv (sinL a) x = a * cosL a x by rw [deriv_sinL]]
  ring

lemma diff_deriv_sinL (a : ℝ) : Differentiable ℝ (deriv (sinL a)) := by
  rw [deriv_sinL]; exact (diff_cosL a).const_mul a

lemma diff_deriv_cosL (a : ℝ) : Differentiable ℝ (deriv (cosL a)) := by
  rw [deriv_cosL]; exact ((diff_sinL a).const_mul a).neg

/-- OpenStax Calculus 3:Equation 4.17 (CA-526). The function
`u(t,x,y) = e^{-α²(a²+b²) t} sin(a x) sin(b y)` solves the heat equation `u_t = α²(u_xx + u_yy)`.
(For `α = 1`, `a = b = 1` this is `e^{-2t} sin x sin y`.) -/
@[kb "openstaxcalculus2016" "3:Equation 4.17, p. 347"]
theorem heat_eq_example (α a b : ℝ) :
    HeatEq2D α (sep (expL (α ^ 2 * (a ^ 2 + b ^ 2))) (sinL a) (sinL b)) := by
  intro t x y
  rw [sep_pT _ _ _ (diff_expL _), sep_pX _ _ _ (diff_sinL a), sep_pX _ _ _ (diff_deriv_sinL a),
    sep_pY _ _ _ (diff_sinL b), sep_pY _ _ _ (diff_deriv_sinL b), deriv_expL, deriv_deriv_sinL,
    deriv_deriv_sinL]
  simp only [sep]
  ring

/-- OpenStax Calculus 3:Equation 4.18 (CA-526). If `ω² = c² (a² + b²)` then
`u(t,x,y) = cos(ω t) sin(a x) sin(b y)` solves the wave equation `u_tt = c² (u_xx + u_yy)`. -/
@[kb "openstaxcalculus2016" "3:Equation 4.18, p. 347"]
theorem wave_eq_example (c a b ω : ℝ) (h : ω ^ 2 = c ^ 2 * (a ^ 2 + b ^ 2)) :
    WaveEq2D c (sep (cosL ω) (sinL a) (sinL b)) := by
  intro t x y
  rw [sep_pT _ _ _ (diff_cosL _), sep_pT _ _ _ (diff_deriv_cosL ω),
    sep_pX _ _ _ (diff_sinL a), sep_pX _ _ _ (diff_deriv_sinL a),
    sep_pY _ _ _ (diff_sinL b), sep_pY _ _ _ (diff_deriv_sinL b), deriv_deriv_cosL,
    deriv_deriv_sinL, deriv_deriv_sinL]
  simp only [sep]
  linear_combination (-(cosL ω t * sinL a x * sinL b y)) * h

/-- OpenStax Calculus 3:Equation 4.19 (CA-526). `v(x,y) = e^x sin y` solves Laplace's equation. -/
@[kb "openstaxcalculus2016" "3:Equation 4.19, p. 347"]
theorem laplace_eq_exp_sin : LaplaceEq2D (fun x y => exp x * sin y) := by
  intro x y
  have h1 : deriv (fun r => exp r * sin y) = fun r => exp r * sin y := by
    funext r; exact ((hasDerivAt_exp r).mul_const _).deriv
  have h2 : deriv (fun r => exp x * sin r) = fun r => exp x * cos r := by
    funext r; exact ((hasDerivAt_sin r).const_mul _).deriv
  have h3 : deriv (fun r => exp x * cos r) = fun r => -(exp x * sin r) := by
    funext r
    have := ((hasDerivAt_cos r).const_mul (exp x)).deriv
    rw [this]; ring
  simp only [h1, h2, h3]
  ring

/-- OpenStax Calculus 3:Equation 4.19 (CA-526). `v(x,y) = x² - y²` solves Laplace's equation. -/
@[kb "openstaxcalculus2016" "3:Equation 4.19, p. 347"]
theorem laplace_eq_quadratic : LaplaceEq2D (fun x y => x ^ 2 - y ^ 2) := by
  intro x y
  have h1 : deriv (fun r : ℝ => r ^ 2 - y ^ 2) = fun r => 2 * r := by
    funext r
    have := ((hasDerivAt_pow 2 r).sub_const (y ^ 2)).deriv
    rw [this]; simp
  have h2 : deriv (fun r : ℝ => x ^ 2 - r ^ 2) = fun r => -(2 * r) := by
    funext r
    have := ((hasDerivAt_pow 2 r).const_sub (x ^ 2)).deriv
    rw [this]; simp
  have h3 : deriv (fun r : ℝ => 2 * r) = fun _ => 2 := by
    funext r; simp
  have h4 : deriv (fun r : ℝ => -(2 * r)) = fun _ => -2 := by
    funext r; simp
  simp only [h1, h2, h3, h4]
  norm_num

end UndergradKB.Calculus.PDEExamples
