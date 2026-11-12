import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import UndergradKB.Common.Attr

/-! # The wave equation: general solution and d'Alembert's formula

Lebl, *Notes on Diffy Qs*, §4.8.  Partial derivatives of `y : ℝ → ℝ → ℝ` (position `x`, time `t`) are
derivatives of the slices `s ↦ y x s` and `ξ ↦ y ξ t`. -/

namespace UndergradKB.DifferentialEquations

open Real intervalIntegral

/-- The one-dimensional wave equation `y_tt = a² y_xx`, stated for all `x, t`. -/
def WaveEq (a : ℝ) (y : ℝ → ℝ → ℝ) : Prop :=
  ∀ x t, deriv (fun s => deriv (fun s => y x s) s) t
    = a ^ 2 * deriv (fun ξ => deriv (fun ξ => y ξ t) ξ) x

lemma contDiff_two_aux {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) :
    Differentiable ℝ F ∧ Differentiable ℝ (deriv F) := by
  have h := contDiff_succ_iff_deriv (n := 1) (f := F) |>.mp (by rw [show ((1 : WithTop ℕ∞) + 1) = 2 by norm_num]; exact hF)
  exact ⟨h.1, (h.2.2 |>.differentiable (by norm_num))⟩

lemma hasDerivAt_comp_lin {F : ℝ → ℝ} (hF : Differentiable ℝ F) (c b s : ℝ) :
    HasDerivAt (fun s => F (c + b * s)) (b * deriv F (c + b * s)) s := by
  have h : HasDerivAt (fun s => F (c + b * s)) (deriv F (c + b * s) * (b * 1)) s :=
    (hF (c + b * s)).hasDerivAt.comp s (((hasDerivAt_id s).const_mul b).const_add c)
  convert h using 1; ring

/-- **General solution of the wave equation (DE-146).** For `C²` functions `F, G`, the function
`F (x + a t) + G (x - a t)` solves `y_tt = a² y_xx`. -/
@[kb "lebldiffyqs2026" "§4.8 characteristic coordinates, p. 252"]
theorem waveEq_add_of_contDiff {F G : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G) (a : ℝ) :
    WaveEq a (fun x t => F (x + a * t) + G (x - a * t)) := by
  intro x t
  obtain ⟨hF1, hF2⟩ := contDiff_two_aux hF
  obtain ⟨hG1, hG2⟩ := contDiff_two_aux hG
  have hs : ∀ s, x - a * s = x + (-a) * s := fun s => by ring
  have hs' : ∀ ξ, ξ - a * t = ξ + (-a) * t := fun s => by ring
  simp only [hs, hs']
  have et : (fun s => deriv (fun s => F (x + a * s) + G (x + (-a) * s)) s)
      = fun s => a * deriv F (x + a * s) + (-a) * deriv G (x + (-a) * s) := by
    funext s
    exact ((hasDerivAt_comp_lin hF1 x a s).add (hasDerivAt_comp_lin hG1 x (-a) s)).deriv
  have ex : (fun ξ => deriv (fun ξ => F (ξ + a * t) + G (ξ + (-a) * t)) ξ)
      = fun ξ => deriv F (ξ + a * t) + deriv G (ξ + (-a) * t) := by
    funext ξ
    exact (((hF1 (ξ + a * t)).hasDerivAt.comp_add_const ξ (a * t)).add
      ((hG1 (ξ + (-a) * t)).hasDerivAt.comp_add_const ξ ((-a) * t))).deriv
  rw [et, ex]
  have h1 : HasDerivAt (fun s => a * deriv F (x + a * s) + (-a) * deriv G (x + (-a) * s))
      (a * (a * deriv (deriv F) (x + a * t)) + (-a) * ((-a) * deriv (deriv G) (x + (-a) * t))) t :=
    ((hasDerivAt_comp_lin hF2 x a t).const_mul a).add
      ((hasDerivAt_comp_lin hG2 x (-a) t).const_mul (-a))
  have h2 : HasDerivAt (fun ξ => deriv F (ξ + a * t) + deriv G (ξ + (-a) * t))
      (deriv (deriv F) (x + a * t) + deriv (deriv G) (x + (-a) * t)) x :=
    ((hF2 (x + a * t)).hasDerivAt.comp_add_const x (a * t)).add
      ((hG2 (x + (-a) * t)).hasDerivAt.comp_add_const x ((-a) * t))
  rw [h1.deriv, h2.deriv]; ring

/-- The d'Alembert solution with initial position `F` and initial velocity `g`. -/
noncomputable def dAlembert (a : ℝ) (F g : ℝ → ℝ) (x t : ℝ) : ℝ :=
  (F (x + a * t) + F (x - a * t)) / 2 + (1 / (2 * a)) * ∫ s in (x - a * t)..(x + a * t), g s

lemma contDiff_two_primitive {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) :
    ContDiff ℝ 2 (fun u => ∫ s in (0 : ℝ)..u, g s) ∧
      ∀ u, deriv (fun u => ∫ s in (0 : ℝ)..u, g s) u = g u := by
  have hd : ∀ u, deriv (fun u => ∫ s in (0 : ℝ)..u, g s) u = g u :=
    fun u => hg.continuous.deriv_integral g 0 u
  refine ⟨?_, hd⟩
  have hdiff : Differentiable ℝ (fun u => ∫ s in (0 : ℝ)..u, g s) := fun u =>
    (intervalIntegral.integral_hasDerivAt_right (hg.continuous.intervalIntegrable _ _)
      (hg.continuous.stronglyMeasurableAtFilter _ _) hg.continuous.continuousAt).differentiableAt
  have := (contDiff_succ_iff_deriv (n := 1) (f := fun u => ∫ s in (0 : ℝ)..u, g s)).mpr
    ⟨hdiff, by simp, by
      have : deriv (fun u => ∫ s in (0 : ℝ)..u, g s) = g := funext hd
      rw [this]; exact hg⟩
  simpa [show ((1 : WithTop ℕ∞) + 1) = 2 by norm_num] using this

/-- **D'Alembert's formula (DE-147).** For `F` of class `C²`, `g` of class `C¹` and `a > 0`, the function
`(F(x+at)+F(x-at))/2 + (1/(2a)) ∫_{x-at}^{x+at} g` solves the wave equation with
`y(x,0) = F(x)` and `y_t(x,0) = g(x)`.  (With `g = 0` this is the zero-velocity case.) -/
@[kb "lebldiffyqs2026" "§4.8 d'Alembert formula, p. 253"]
theorem dAlembert_solves {a : ℝ} {F g : ℝ → ℝ} (ha : 0 < a) (hF : ContDiff ℝ 2 F) (hg : ContDiff ℝ 1 g) :
    WaveEq a (dAlembert a F g) ∧ (∀ x, dAlembert a F g x 0 = F x) ∧
      ∀ x, deriv (fun t => dAlembert a F g x t) 0 = g x := by
  obtain ⟨hΦ, hΦ'⟩ := contDiff_two_primitive hg
  set Φ : ℝ → ℝ := fun u => ∫ s in (0 : ℝ)..u, g s with hΦdef
  have hform : ∀ x t, dAlembert a F g x t
      = (fun z => F z / 2 + Φ z / (2 * a)) (x + a * t)
        + (fun z => F z / 2 - Φ z / (2 * a)) (x - a * t) := by
    intro x t
    have hint : ∫ s in (x - a * t)..(x + a * t), g s = Φ (x + a * t) - Φ (x - a * t) := by
      simp only [hΦdef]
      rw [integral_interval_sub_left (hg.continuous.intervalIntegrable _ _)
        (hg.continuous.intervalIntegrable _ _)]
    simp only [dAlembert, hint]
    field_simp
    ring
  have hfun : dAlembert a F g
      = fun x t => (fun z => F z / 2 + Φ z / (2 * a)) (x + a * t)
        + (fun z => F z / 2 - Φ z / (2 * a)) (x - a * t) := by
    funext x t; exact hform x t
  have hG1 : ContDiff ℝ 2 (fun z => F z / 2 + Φ z / (2 * a)) :=
    (hF.div_const 2).add (hΦ.div_const _)
  have hG2 : ContDiff ℝ 2 (fun z => F z / 2 - Φ z / (2 * a)) :=
    (hF.div_const 2).sub (hΦ.div_const _)
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun]; exact waveEq_add_of_contDiff hG1 hG2 a
  · intro x
    simp [dAlembert]
  · intro x
    obtain ⟨h1, -⟩ := contDiff_two_aux hF
    have hΦd : Differentiable ℝ Φ := (contDiff_two_aux hΦ).1
    have h : HasDerivAt (fun s => (F (x + a * s) / 2 + Φ (x + a * s) / (2 * a))
          + (F (x + (-a) * s) / 2 - Φ (x + (-a) * s) / (2 * a)))
        (a * deriv (fun z => F z / 2 + Φ z / (2 * a)) (x + a * 0)
          + (-a) * deriv (fun z => F z / 2 - Φ z / (2 * a)) (x + (-a) * 0)) 0 :=
      ((hasDerivAt_comp_lin (F := fun z => F z / 2 + Φ z / (2 * a))
      ((h1.div_const 2).add (hΦd.div_const _)) x a 0).add
      (hasDerivAt_comp_lin (F := fun z => F z / 2 - Φ z / (2 * a))
      ((h1.div_const 2).sub (hΦd.div_const _)) x (-a) 0))
    have e : (fun t => dAlembert a F g x t)
        = fun s => (F (x + a * s) / 2 + Φ (x + a * s) / (2 * a))
          + (F (x + (-a) * s) / 2 - Φ (x + (-a) * s) / (2 * a)) := by
      funext t; rw [hform]; simp only [neg_mul, ← sub_eq_add_neg]
    rw [e, h.deriv]
    have d1 : deriv (fun z => F z / 2 + Φ z / (2 * a)) (x + a * 0)
        = deriv F x / 2 + g x / (2 * a) := by
      simp only [mul_zero, add_zero]
      have hh : HasDerivAt (fun z => F z / 2 + Φ z / (2 * a))
          (deriv F x / 2 + deriv Φ x / (2 * a)) x :=
        ((h1 x).hasDerivAt.div_const 2).add ((hΦd x).hasDerivAt.div_const (2 * a))
      rw [hh.deriv, hΦ']
    have d2 : deriv (fun z => F z / 2 - Φ z / (2 * a)) (x + (-a) * 0)
        = deriv F x / 2 - g x / (2 * a) := by
      simp only [mul_zero, add_zero]
      have hh : HasDerivAt (fun z => F z / 2 - Φ z / (2 * a))
          (deriv F x / 2 - deriv Φ x / (2 * a)) x :=
        ((h1 x).hasDerivAt.div_const 2).sub ((hΦd x).hasDerivAt.div_const (2 * a))
      rw [hh.deriv, hΦ']
    rw [d1, d2]; field_simp; ring

/-- Odd `2L`-periodic initial position keeps the ends fixed (DE-147): for `F` odd and `2L`-periodic,
the zero-velocity d'Alembert solution vanishes at `x = 0` and `x = L` for all times. -/
@[kb "lebldiffyqs2026" "§4.8 d'Alembert formula, p. 253"]
theorem dAlembert_ends_zero {F : ℝ → ℝ} {L : ℝ} (a : ℝ) (hodd : ∀ x, F (-x) = -F x)
    (hper : ∀ x, F (x + 2 * L) = F x) (t : ℝ) :
    (F (0 + a * t) + F (0 - a * t)) / 2 = 0 ∧ (F (L + a * t) + F (L - a * t)) / 2 = 0 := by
  constructor
  · have := hodd (a * t)
    simp only [zero_add, zero_sub]; rw [this]; ring
  · have h2 := hper (-L - a * t)
    have h3 := hodd (L + a * t)
    have e1 : -L - a * t + 2 * L = L - a * t := by ring
    have e2 : -(L + a * t) = -L - a * t := by ring
    rw [e1] at h2; rw [e2] at h3
    rw [h2, h3]; ring

/-! ## The heat equation (Lebl §4.6) -/

/-- The heat equation `u_t = k u_xx`, stated for all `x, t`. -/
def HeatEq (k : ℝ) (u : ℝ → ℝ → ℝ) : Prop :=
  ∀ x t, deriv (fun s => u x s) t = k * deriv (fun ξ => deriv (fun ξ => u ξ t) ξ) x

/-- The differentiability needed to differentiate sums termwise: `u` is differentiable in `t`, and
twice differentiable in `x`. -/
structure HeatReg (u : ℝ → ℝ → ℝ) : Prop where
  dt : ∀ x, Differentiable ℝ (fun s => u x s)
  dx : ∀ t, Differentiable ℝ (fun ξ => u ξ t)
  dxx : ∀ t, Differentiable ℝ (fun ξ => deriv (fun ξ => u ξ t) ξ)

/-- **Superposition (DE-140).** A finite linear combination of solutions of the heat equation is a solution,
and it satisfies any homogeneous Dirichlet condition `u(p,t)=0` that all the terms satisfy (in particular
`u(0,t)=u(L,t)=0`). -/
@[kb "lebldiffyqs2026" "§4.6 principle of superposition, p. 233"]
theorem heat_superposition {ι : Type*} (S : Finset ι) (c : ι → ℝ) (u : ι → ℝ → ℝ → ℝ) (k : ℝ)
    (hreg : ∀ i, HeatReg (u i)) (hsol : ∀ i, HeatEq k (u i)) :
    HeatReg (fun x t => ∑ i ∈ S, c i * u i x t) ∧ HeatEq k (fun x t => ∑ i ∈ S, c i * u i x t) ∧
      ∀ p, (∀ i t, u i p t = 0) → ∀ t, ∑ i ∈ S, c i * u i p t = 0 := by
  have hx : ∀ t ξ, HasDerivAt (fun ξ => ∑ i ∈ S, c i * u i ξ t)
      (∑ i ∈ S, c i * deriv (fun ξ => u i ξ t) ξ) ξ := fun t ξ =>
    HasDerivAt.fun_sum fun i _ => (((hreg i).dx t) ξ).hasDerivAt.const_mul (c i)
  have hxx : ∀ t ξ, HasDerivAt (fun ξ => ∑ i ∈ S, c i * deriv (fun ξ => u i ξ t) ξ)
      (∑ i ∈ S, c i * deriv (fun ξ => deriv (fun ξ => u i ξ t) ξ) ξ) ξ := fun t ξ =>
    HasDerivAt.fun_sum fun i _ => (((hreg i).dxx t) ξ).hasDerivAt.const_mul (c i)
  have ht : ∀ x t, HasDerivAt (fun s => ∑ i ∈ S, c i * u i x s)
      (∑ i ∈ S, c i * deriv (fun s => u i x s) t) t := fun x t =>
    HasDerivAt.fun_sum fun i _ => (((hreg i).dt x) t).hasDerivAt.const_mul (c i)
  have e1 : ∀ t, (fun ξ => deriv (fun ξ => ∑ i ∈ S, c i * u i ξ t) ξ)
      = fun ξ => ∑ i ∈ S, c i * deriv (fun ξ => u i ξ t) ξ := fun t => funext fun ξ => (hx t ξ).deriv
  refine ⟨⟨fun x t => (ht x t).differentiableAt, fun t ξ => (hx t ξ).differentiableAt, ?_⟩, ?_, ?_⟩
  · intro t ξ; rw [e1]; exact (hxx t ξ).differentiableAt
  · intro x t
    rw [(ht x t).deriv, e1, (hxx t x).deriv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsol i x t]; ring
  · intro p hp t
    exact Finset.sum_eq_zero fun i _ => by rw [hp i t, mul_zero]

lemma deriv_sin_mul (ω : ℝ) : deriv (fun ξ => sin (ω * ξ)) = fun ξ => ω * cos (ω * ξ) := by
  funext ξ
  have := ((hasDerivAt_id ξ).const_mul ω).sin
  simpa [mul_comm] using this.deriv

lemma deriv_cos_mul (ω : ℝ) : deriv (fun ξ => cos (ω * ξ)) = fun ξ => -(ω * sin (ω * ξ)) := by
  funext ξ
  have := ((hasDerivAt_id ξ).const_mul ω).cos
  simp only [id, mul_one] at this
  rw [this.deriv]; ring

/-- Separated heat solution with an abstract spatial factor `X`, `X'' = -μ X`. -/
theorem heat_term {X : ℝ → ℝ} (hX : ContDiff ℝ 2 X) {μ : ℝ}
    (hμ : ∀ ξ, deriv (deriv X) ξ = -μ * X ξ) (k : ℝ) :
    HeatReg (fun x t => exp (-(k * μ) * t) * X x) ∧
      HeatEq k (fun x t => exp (-(k * μ) * t) * X x) := by
  obtain ⟨h1, h2⟩ := contDiff_two_aux hX
  have hT : ∀ t, HasDerivAt (fun s => exp (-(k * μ) * s)) (-(k * μ) * exp (-(k * μ) * t)) t := by
    intro t
    have := ((hasDerivAt_id t).const_mul (-(k * μ))).exp
    simp only [id, mul_one] at this
    convert this using 1; ring
  have ex : ∀ t, (fun ξ => deriv (fun ξ => exp (-(k * μ) * t) * X ξ) ξ)
      = fun ξ => exp (-(k * μ) * t) * deriv X ξ := fun t =>
    funext fun ξ => ((h1 ξ).hasDerivAt.const_mul _).deriv
  have exx : ∀ t ξ, deriv (fun ξ => exp (-(k * μ) * t) * deriv X ξ) ξ
      = exp (-(k * μ) * t) * deriv (deriv X) ξ := fun t ξ =>
    (((h2 ξ).hasDerivAt).const_mul _).deriv
  refine ⟨⟨fun x t => ((hT t).mul_const (X x)).differentiableAt, fun t ξ =>
    ((h1 ξ).hasDerivAt.const_mul _).differentiableAt, fun t => ?_⟩, fun x t => ?_⟩
  · rw [show (fun ξ => deriv (fun ξ => exp (-(k * μ) * t) * X ξ) ξ) = _ from ex t]
    exact fun ξ => (((h2 ξ).hasDerivAt).const_mul _).differentiableAt
  · rw [((hT t).mul_const (X x)).deriv, ex t, exx, hμ]; ring

/-- **Separated heat solutions (DE-141).** `exp(-k (nπ/L)² t) sin(nπx/L)`-type terms: for any frequency
`ω`, `exp(-k ω² t) sin(ω x)` solves the heat equation. -/
theorem heat_sin_term (k ω : ℝ) :
    HeatReg (fun x t => exp (-(k * ω ^ 2) * t) * sin (ω * x)) ∧
      HeatEq k (fun x t => exp (-(k * ω ^ 2) * t) * sin (ω * x)) := by
  refine heat_term (X := fun ξ => sin (ω * ξ)) (by fun_prop) ?_ k
  intro ξ
  rw [deriv_sin_mul, show (fun ξ => ω * cos (ω * ξ)) = fun ξ => ω * cos (ω * ξ) from rfl]
  have := ((hasDerivAt_id ξ).const_mul ω).cos.const_mul ω
  simp only [id, mul_one] at this
  rw [this.deriv]; ring

theorem heat_cos_term (k ω : ℝ) :
    HeatReg (fun x t => exp (-(k * ω ^ 2) * t) * cos (ω * x)) ∧
      HeatEq k (fun x t => exp (-(k * ω ^ 2) * t) * cos (ω * x)) := by
  refine heat_term (X := fun ξ => cos (ω * ξ)) (by fun_prop) ?_ k
  intro ξ
  rw [deriv_cos_mul]
  have := (((hasDerivAt_id ξ).const_mul ω).sin.const_mul ω).neg
  simp only [id, mul_one] at this
  rw [show (fun ξ => -(ω * sin (ω * ξ))) = -(fun y => ω * sin (ω * y)) from rfl, this.deriv]
  ring

lemma hasDerivAt_cos_mul (ω ξ : ℝ) : HasDerivAt (fun ξ => cos (ω * ξ)) (-(ω * sin (ω * ξ))) ξ := by
  have := ((hasDerivAt_id ξ).const_mul ω).cos
  simp only [id, mul_one] at this
  convert this using 1; ring

lemma hasDerivAt_sin_mul (ω ξ : ℝ) : HasDerivAt (fun ξ => sin (ω * ξ)) (ω * cos (ω * ξ)) ξ := by
  have := ((hasDerivAt_id ξ).const_mul ω).sin
  simp only [id, mul_one] at this
  convert this using 1; ring

/-- Finite sine series for the heat equation with Dirichlet ends. -/
noncomputable def heatSineSum (k L : ℝ) (b : ℕ → ℝ) (N : Finset ℕ) (x t : ℝ) : ℝ :=
  ∑ n ∈ N, b n * (exp (-(k * (n * π / L) ^ 2) * t) * sin (n * π / L * x))

/-- **Heat equation, fixed-temperature ends (DE-141).** Every finite sum
`∑ bₙ e^{-k(nπ/L)² t} sin(nπx/L)` solves `u_t = k u_xx` with `u(0,t) = u(L,t) = 0` and
`u(x,0) = ∑ bₙ sin(nπx/L)`. -/
@[kb "lebldiffyqs2026" "§4.6 separation of variables, p. 234"]
theorem heat_dirichlet_series (k : ℝ) {L : ℝ} (hL : L ≠ 0) (b : ℕ → ℝ) (N : Finset ℕ) :
    HeatEq k (heatSineSum k L b N) ∧ (∀ t, heatSineSum k L b N 0 t = 0) ∧
      (∀ t, heatSineSum k L b N L t = 0) ∧
      ∀ x, heatSineSum k L b N x 0 = ∑ n ∈ N, b n * sin (n * π / L * x) := by
  have h := heat_superposition N b
    (fun n x t => exp (-(k * (n * π / L) ^ 2) * t) * sin (n * π / L * x)) k
    (fun n => (heat_sin_term k _).1) (fun n => (heat_sin_term k _).2)
  refine ⟨h.2.1, ?_, ?_, ?_⟩
  · exact h.2.2 0 (fun n t => by simp)
  · refine h.2.2 L (fun n t => ?_)
    have : (n : ℝ) * π / L * L = n * π := by field_simp
    simp [this, sin_nat_mul_pi]
  · intro x; simp [heatSineSum]

/-- Finite cosine series for the heat equation with insulated ends. -/
noncomputable def heatCosSum (k L : ℝ) (a : ℕ → ℝ) (N : Finset ℕ) (x t : ℝ) : ℝ :=
  ∑ n ∈ N, a n * (exp (-(k * (n * π / L) ^ 2) * t) * cos (n * π / L * x))

/-- **Heat equation, insulated ends (DE-142).** Every finite sum `∑ aₙ e^{-k(nπ/L)² t} cos(nπx/L)` solves
`u_t = k u_xx` with `u_x(0,t) = u_x(L,t) = 0` and `u(x,0) = ∑ aₙ cos(nπx/L)`. -/
@[kb "lebldiffyqs2026" "§4.6 insulated ends, p. 238"]
theorem heat_neumann_series (k : ℝ) {L : ℝ} (hL : L ≠ 0) (a : ℕ → ℝ) (N : Finset ℕ) :
    HeatEq k (heatCosSum k L a N) ∧
      (∀ t, deriv (fun ξ => heatCosSum k L a N ξ t) 0 = 0) ∧
      (∀ t, deriv (fun ξ => heatCosSum k L a N ξ t) L = 0) ∧
      ∀ x, heatCosSum k L a N x 0 = ∑ n ∈ N, a n * cos (n * π / L * x) := by
  have h := heat_superposition N a
    (fun n x t => exp (-(k * (n * π / L) ^ 2) * t) * cos (n * π / L * x)) k
    (fun n => (heat_cos_term k _).1) (fun n => (heat_cos_term k _).2)
  have hd : ∀ t ξ, HasDerivAt (fun ξ => heatCosSum k L a N ξ t)
      (∑ n ∈ N, a n * (exp (-(k * (n * π / L) ^ 2) * t) *
        (-((n * π / L) * sin (n * π / L * ξ))))) ξ := fun t ξ =>
    HasDerivAt.fun_sum fun n _ =>
      ((hasDerivAt_cos_mul (n * π / L) ξ).const_mul _).const_mul _
  refine ⟨h.2.1, fun t => ?_, fun t => ?_, fun x => ?_⟩
  · rw [(hd t 0).deriv]; simp
  · rw [(hd t L).deriv]
    have : (n : ℕ) → (n : ℝ) * π / L * L = n * π := fun n => by field_simp
    simp [this, sin_nat_mul_pi]
  · simp [heatCosSum]

/-! ## Separated solutions of the wave equation (Lebl §4.7) -/

/-- Finite series `∑ bₙ sin(nπx/L) cos(nπat/L)` (string released from rest). -/
noncomputable def waveSineCos (a L : ℝ) (b : ℕ → ℝ) (N : Finset ℕ) (x t : ℝ) : ℝ :=
  ∑ n ∈ N, b n * (sin (n * π / L * x) * cos (n * π * a / L * t))

/-- Finite series `∑ cₙ sin(nπx/L) sin(nπat/L)` (string starting flat with initial velocity). -/
noncomputable def waveSineSin (a L : ℝ) (c : ℕ → ℝ) (N : Finset ℕ) (x t : ℝ) : ℝ :=
  ∑ n ∈ N, c n * (sin (n * π / L * x) * sin (n * π * a / L * t))

/-- **Fixed-end string at rest (DE-144).** Every finite sum `∑ bₙ sin(nπx/L) cos(nπat/L)` solves
`y_tt = a² y_xx`, vanishes at `x = 0` and `x = L`, and has `y(x,0) = ∑ bₙ sin(nπx/L)`, `y_t(x,0) = 0`. -/
@[kb "lebldiffyqs2026" "§4.7 separation of variables for wave equation, p. 244"]
theorem wave_sine_cos_series (a : ℝ) {L : ℝ} (hL : L ≠ 0) (b : ℕ → ℝ) (N : Finset ℕ) :
    WaveEq a (waveSineCos a L b N) ∧ (∀ t, waveSineCos a L b N 0 t = 0) ∧
      (∀ t, waveSineCos a L b N L t = 0) ∧
      (∀ x, waveSineCos a L b N x 0 = ∑ n ∈ N, b n * sin (n * π / L * x)) ∧
      ∀ x, deriv (fun t => waveSineCos a L b N x t) 0 = 0 := by
  have hu : waveSineCos a L b N = fun x t =>
      (fun z => ∑ n ∈ N, b n / 2 * sin (n * π / L * z)) (x + a * t)
        + (fun z => ∑ n ∈ N, b n / 2 * sin (n * π / L * z)) (x - a * t) := by
    funext x t
    simp only [waveSineCos, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    have e1 : (n : ℝ) * π / L * (x + a * t) = n * π / L * x + n * π * a / L * t := by ring
    have e2 : (n : ℝ) * π / L * (x - a * t) = n * π / L * x - n * π * a / L * t := by ring
    rw [e1, e2, sin_add, sin_sub]; ring
  have hc : ContDiff ℝ 2 (fun z => ∑ n ∈ N, b n / 2 * sin (n * π / L * z)) :=
    ContDiff.sum fun n _ => by fun_prop
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hu]; exact waveEq_add_of_contDiff hc hc a
  · intro t; simp [waveSineCos]
  · intro t
    have : ∀ n : ℕ, (n : ℝ) * π / L * L = n * π := fun n => by field_simp
    simp [waveSineCos, this, sin_nat_mul_pi]
  · intro x; simp [waveSineCos]
  · intro x
    have hd : HasDerivAt (fun t => waveSineCos a L b N x t)
        (∑ n ∈ N, b n * (sin (n * π / L * x) * (-((n * π * a / L) * sin (n * π * a / L * 0))))) 0 :=
      HasDerivAt.fun_sum fun n _ =>
        ((hasDerivAt_cos_mul (n * π * a / L) 0).const_mul _).const_mul _
    rw [hd.deriv]; simp

/-- **Fixed-end string with initial velocity (DE-144, DE-145).** Every finite sum
`∑ cₙ sin(nπx/L) sin(nπat/L)` solves the wave equation, vanishes at both ends, starts flat, and has
`y_t(x,0) = ∑ cₙ (nπa/L) sin(nπx/L)`.  Adding it to `wave_sine_cos_series` gives the solution with both
initial position and velocity (superposition, DE-145). -/
@[kb "lebldiffyqs2026" "Theorem 4.7.1, p. 246"]
theorem wave_sine_sin_series (a : ℝ) {L : ℝ} (hL : L ≠ 0) (c : ℕ → ℝ) (N : Finset ℕ) :
    WaveEq a (waveSineSin a L c N) ∧ (∀ t, waveSineSin a L c N 0 t = 0) ∧
      (∀ t, waveSineSin a L c N L t = 0) ∧ (∀ x, waveSineSin a L c N x 0 = 0) ∧
      ∀ x, deriv (fun t => waveSineSin a L c N x t) 0
        = ∑ n ∈ N, c n * (n * π * a / L) * sin (n * π / L * x) := by
  have hu : waveSineSin a L c N = fun x t =>
      (fun z => -∑ n ∈ N, c n / 2 * cos (n * π / L * z)) (x + a * t)
        + (fun z => ∑ n ∈ N, c n / 2 * cos (n * π / L * z)) (x - a * t) := by
    funext x t
    simp only [waveSineSin, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    have e1 : (n : ℝ) * π / L * (x + a * t) = n * π / L * x + n * π * a / L * t := by ring
    have e2 : (n : ℝ) * π / L * (x - a * t) = n * π / L * x - n * π * a / L * t := by ring
    rw [e1, e2, cos_add, cos_sub]; ring
  have hc : ContDiff ℝ 2 (fun z => ∑ n ∈ N, c n / 2 * cos (n * π / L * z)) :=
    ContDiff.sum fun n _ => by fun_prop
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hu]; exact waveEq_add_of_contDiff hc.neg hc a
  · intro t; simp [waveSineSin]
  · intro t
    have : ∀ n : ℕ, (n : ℝ) * π / L * L = n * π := fun n => by field_simp
    simp [waveSineSin, this, sin_nat_mul_pi]
  · intro x; simp [waveSineSin]
  · intro x
    have hd : HasDerivAt (fun t => waveSineSin a L c N x t)
        (∑ n ∈ N, c n * (sin (n * π / L * x) * ((n * π * a / L) * cos (n * π * a / L * 0)))) 0 :=
      HasDerivAt.fun_sum fun n _ =>
        ((hasDerivAt_sin_mul (n * π * a / L) 0).const_mul _).const_mul _
    rw [hd.deriv]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp; ring

/-! ## The Laplace equation (Lebl §4.9, §4.10) -/

/-- Laplace's equation `u_xx + u_yy = 0`, for all `(x, y)`. -/
def LaplaceEq (u : ℝ → ℝ → ℝ) : Prop :=
  ∀ x y, deriv (fun ξ => deriv (fun ξ => u ξ y) ξ) x + deriv (fun η => deriv (fun η => u x η) η) y = 0

open Complex in
/-- The real part of an analytic function of `x + iy` is harmonic. -/
theorem laplace_re_of_hasDerivAt (f f' f'' : ℂ → ℂ) (h1 : ∀ z, HasDerivAt f (f' z) z)
    (h2 : ∀ z, HasDerivAt f' (f'' z) z) : LaplaceEq (fun x y => (f ((x : ℂ) + y * I)).re) := by
  intro x y
  have hx1 : ∀ ξ : ℝ, HasDerivAt (fun ξ : ℝ => (f ((ξ : ℂ) + y * I)).re) (f' (ξ + y * I)).re ξ :=
    fun ξ => ((h1 _).comp_add_const (ξ : ℂ) (y * I)).real_of_complex
  have hx2 : ∀ ξ : ℝ, HasDerivAt (fun ξ : ℝ => (f' ((ξ : ℂ) + y * I)).re)
      (f'' (ξ + y * I)).re ξ :=
    fun ξ => ((h2 _).comp_add_const (ξ : ℂ) (y * I)).real_of_complex
  have hy1 : ∀ η : ℝ, HasDerivAt (fun η : ℝ => (f ((x : ℂ) + η * I)).re)
      (f' (x + η * I) * I).re η := by
    intro η
    have : HasDerivAt (fun w : ℂ => f ((x : ℂ) + w * I)) (f' (x + η * I) * I) (η : ℂ) :=
      ((h1 _).comp (η : ℂ) (((hasDerivAt_id (η : ℂ)).mul_const I).const_add (x : ℂ))).congr_deriv
        (by simp)
    exact this.real_of_complex
  have hy2 : ∀ η : ℝ, HasDerivAt (fun η : ℝ => (f' ((x : ℂ) + η * I) * I).re)
      (f'' (x + η * I) * I * I).re η := by
    intro η
    have : HasDerivAt (fun w : ℂ => f' ((x : ℂ) + w * I) * I) (f'' (x + η * I) * I * I) (η : ℂ) :=
      (((h2 _).comp (η : ℂ) (((hasDerivAt_id (η : ℂ)).mul_const I).const_add (x : ℂ))).mul_const
        I).congr_deriv (by simp)
    exact this.real_of_complex
  have ex : (fun ξ : ℝ => deriv (fun ξ : ℝ => (f ((ξ : ℂ) + y * I)).re) ξ)
      = fun ξ : ℝ => (f' ((ξ : ℂ) + y * I)).re := funext fun ξ => (hx1 ξ).deriv
  have ey : (fun η : ℝ => deriv (fun η : ℝ => (f ((x : ℂ) + η * I)).re) η)
      = fun η : ℝ => (f' ((x : ℂ) + η * I) * I).re := funext fun η => (hy1 η).deriv
  rw [ex, ey, (hx2 x).deriv, (hy2 y).deriv]
  simp [mul_assoc]

open Complex in
/-- **Harmonic polynomials (DE-151).** `Re (x + iy)ⁿ`, i.e. `rⁿ cos nθ`, is harmonic. -/
@[kb "lebldiffyqs2026" "§4.10 series solution, p. 265"]
theorem laplace_re_pow (n : ℕ) : LaplaceEq (fun x y => (((x : ℂ) + y * I) ^ n).re) :=
  laplace_re_of_hasDerivAt (fun z => z ^ n) (fun z => n * z ^ (n - 1))
    (fun z => n * ((((n - 1 : ℕ)) : ℂ) * z ^ (n - 1 - 1)))
    (fun z => hasDerivAt_pow n z)
    (fun z => (hasDerivAt_pow (n - 1) z).const_mul _)

open Complex in
/-- `Im (x + iy)ⁿ`, i.e. `rⁿ sin nθ`, is harmonic. -/
@[kb "lebldiffyqs2026" "§4.10 series solution, p. 265"]
theorem laplace_im_pow (n : ℕ) : LaplaceEq (fun x y => (((x : ℂ) + y * I) ^ n).im) := by
  have h := laplace_re_of_hasDerivAt (fun z => -I * z ^ n) (fun z => -I * (n * z ^ (n - 1)))
    (fun z => -I * (n * ((((n - 1 : ℕ)) : ℂ) * z ^ (n - 1 - 1))))
    (fun z => (hasDerivAt_pow n z).const_mul _)
    (fun z => ((hasDerivAt_pow (n - 1) z).const_mul _).const_mul _)
  convert h using 3
  simp

open Complex in
/-- In polar coordinates `x = r cos θ`, `y = r sin θ`: `Re (x+iy)ⁿ = rⁿ cos nθ` and
`Im (x+iy)ⁿ = rⁿ sin nθ`. -/
theorem pow_polar (r θ : ℝ) (n : ℕ) :
    ((((r * Real.cos θ : ℝ) : ℂ) + ((r * Real.sin θ : ℝ) : ℂ) * I) ^ n).re = r ^ n * Real.cos (n * θ) ∧
    ((((r * Real.cos θ : ℝ) : ℂ) + ((r * Real.sin θ : ℝ) : ℂ) * I) ^ n).im = r ^ n * Real.sin (n * θ) := by
  have e : (((r * Real.cos θ : ℝ) : ℂ) + ((r * Real.sin θ : ℝ) : ℂ) * I)
      = (r : ℂ) * (Complex.cos θ + Complex.sin θ * I) := by
    push_cast; ring
  have e2 : ((r : ℂ) * (Complex.cos θ + Complex.sin θ * I)) ^ n
      = ((r ^ n * Real.cos (n * θ) : ℝ) : ℂ) + ((r ^ n * Real.sin (n * θ) : ℝ) : ℂ) * I := by
    rw [mul_pow, Complex.cos_add_sin_mul_I_pow]
    push_cast; ring
  rw [e, e2]
  constructor <;> simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring

lemma hasDerivAt_sinh_mul (ω y : ℝ) :
    HasDerivAt (fun η => Real.sinh (ω * η)) (ω * Real.cosh (ω * y)) y := by
  exact ((Real.hasDerivAt_sinh (ω * y)).comp y ((hasDerivAt_id y).const_mul ω)).congr_deriv
    (by simp; ring)

lemma hasDerivAt_cosh_mul (ω y : ℝ) :
    HasDerivAt (fun η => Real.cosh (ω * η)) (ω * Real.sinh (ω * y)) y := by
  exact ((Real.hasDerivAt_cosh (ω * y)).comp y ((hasDerivAt_id y).const_mul ω)).congr_deriv
    (by simp; ring)

/-- **Dirichlet problem on a rectangle, one separated term (DE-149).** For any `ω`,
`sinh(ω y) sin(ω x)` is harmonic; for `ω = nπ/L` it vanishes on the sides `x = 0`, `x = L` and on
the bottom `y = 0`. -/
@[kb "lebldiffyqs2026" "§4.9 Dirichlet problem, p. 259"]
theorem laplace_sinh_sin (ω : ℝ) : LaplaceEq (fun x y => Real.sinh (ω * y) * sin (ω * x)) := by
  intro x y
  have ex : ∀ y, (fun ξ => deriv (fun ξ => Real.sinh (ω * y) * sin (ω * ξ)) ξ)
      = fun ξ => Real.sinh (ω * y) * (ω * cos (ω * ξ)) := fun y =>
    funext fun ξ => ((hasDerivAt_sin_mul ω ξ).const_mul _).deriv
  have ey : (fun η => deriv (fun η => Real.sinh (ω * η) * sin (ω * x)) η)
      = fun η => (ω * Real.cosh (ω * η)) * sin (ω * x) :=
    funext fun η => ((hasDerivAt_sinh_mul ω η).mul_const _).deriv
  rw [ex, ey]
  have h1 := ((hasDerivAt_cos_mul ω x).const_mul (Real.sinh (ω * y))).const_mul ω
  have h2 := ((hasDerivAt_cosh_mul ω y).const_mul ω).mul_const (sin (ω * x))
  have h1' : HasDerivAt (fun ξ => Real.sinh (ω * y) * (ω * cos (ω * ξ)))
      (Real.sinh (ω * y) * (ω * (-(ω * sin (ω * x))))) x := by
    have := (hasDerivAt_cos_mul ω x).const_mul ω
    exact this.const_mul (Real.sinh (ω * y))
  rw [h1'.deriv, h2.deriv]; ring

theorem laplace_sinh_sin_boundary {L : ℝ} (hL : L ≠ 0) (n : ℕ) (y : ℝ) :
    Real.sinh (n * π / L * y) * sin (n * π / L * 0) = 0 ∧
    Real.sinh (n * π / L * y) * sin (n * π / L * L) = 0 ∧
    Real.sinh (n * π / L * 0) * sin (n * π / L * y) = 0 := by
  have : (n : ℝ) * π / L * L = n * π := by field_simp
  simp [this, sin_nat_mul_pi]

/-! ## Boundary value problems `x'' + λ x = 0` (Lebl §4.1)

Solutions are `C²` functions on `ℝ` (only their restriction to the interval matters); the differential
equation is imposed on the closed interval `[0, L]`. -/

open Set

lemma contDiff_deriv_aux {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) : ContDiff ℝ 1 (deriv F) := by
  have h := contDiff_succ_iff_deriv (n := 1) (f := F) |>.mp
    (by rw [show ((1 : WithTop ℕ∞) + 1) = 2 by norm_num]; exact hF)
  exact h.2.2

/-- **No nonpositive eigenvalues (DE-115).** If `λ ≤ 0`, a solution of `x'' + λ x = 0` on `[0, L]` with
`x(0) = x(L) = 0` vanishes identically on `[0, L]`.  (The function `x²` is convex there.) -/
@[kb "lebldiffyqs2026" "Example 4.1.3, p. 190"]
theorem dirichlet_eq_zero_of_nonpos {L lam : ℝ} (hlam : lam ≤ 0) {x : ℝ → ℝ} (hx : ContDiff ℝ 2 x)
    (hode : ∀ t ∈ Icc 0 L, deriv (deriv x) t + lam * x t = 0) (h0 : x 0 = 0) (hL : x L = 0) :
    ∀ t ∈ Icc 0 L, x t = 0 := by
  obtain ⟨hd, hd'⟩ := contDiff_two_aux hx
  have hz1 : ∀ t, HasDerivAt (fun t => x t ^ 2) (2 * x t * deriv x t) t := fun t => by
    have := (hd t).hasDerivAt.pow 2
    convert this using 1; simp
  have hzd : deriv (fun t => x t ^ 2) = fun t => 2 * x t * deriv x t :=
    funext fun t => (hz1 t).deriv
  have hz2 : ∀ t, HasDerivAt (fun t => 2 * x t * deriv x t)
      (2 * deriv x t * deriv x t + 2 * x t * deriv (deriv x) t) t := fun t => by
    have := (((hd t).hasDerivAt.const_mul 2).mul (hd' t).hasDerivAt)
    convert this using 1
  have hconv : ConvexOn ℝ (Icc 0 L) (fun t => x t ^ 2) := by
    refine convexOn_of_deriv2_nonneg (convex_Icc 0 L)
      (fun t _ => (hz1 t).continuousAt.continuousWithinAt)
      (fun t _ => (hz1 t).differentiableAt.differentiableWithinAt) ?_ ?_
    · rw [hzd]; exact fun t _ => (hz2 t).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' := hode t (interior_subset ht)
      have : deriv^[2] (fun t => x t ^ 2) t
          = 2 * deriv x t * deriv x t + 2 * x t * deriv (deriv x) t := by
        show deriv (deriv (fun t => x t ^ 2)) t = _
        rw [hzd]; exact (hz2 t).deriv
      rw [this, show deriv (deriv x) t = -lam * x t by linarith]
      nlinarith [sq_nonneg (deriv x t), sq_nonneg (x t)]
  intro t ht
  have hseg : t ∈ segment ℝ 0 L := by
    rw [segment_eq_Icc (le_trans ht.1 ht.2)]; exact ht
  have := hconv.le_on_segment (left_mem_Icc.2 (le_trans ht.1 ht.2))
    (right_mem_Icc.2 (le_trans ht.1 ht.2)) hseg
  simp only [h0, hL, max_self] at this
  have h2 : x t ^ 2 = 0 := le_antisymm (by simpa using this) (sq_nonneg _)
  exact pow_eq_zero_iff two_ne_zero |>.1 h2

/-- Uniqueness of solutions of `x'' = -ω² x` from the initial data: on `[0, L]`, a `C²` solution is
`x(0) cos ωt + (x'(0)/ω) sin ωt`.  (Energy argument: `x'² + ω² x²` is constant for the difference.) -/
theorem ode_solution_eq {ω L : ℝ} (hω : ω ≠ 0) {x : ℝ → ℝ} (hx : ContDiff ℝ 2 x)
    (hode : ∀ t ∈ Icc 0 L, deriv (deriv x) t = -(ω ^ 2) * x t) :
    ∀ t ∈ Icc 0 L, x t = x 0 * cos (ω * t) + deriv x 0 / ω * sin (ω * t) := by
  obtain ⟨hd, hd'⟩ := contDiff_two_aux hx
  set A := x 0 with hA
  set B := deriv x 0 / ω with hB
  let q : ℝ → ℝ := fun t => x t - A * cos (ω * t) - B * sin (ω * t)
  let p : ℝ → ℝ := fun t => deriv x t - A * (-(ω * sin (ω * t))) - B * (ω * cos (ω * t))
  have hq : ∀ t, HasDerivAt q (p t) t := fun t =>
    (((hd t).hasDerivAt.sub ((hasDerivAt_cos_mul ω t).const_mul A)).sub
      ((hasDerivAt_sin_mul ω t).const_mul B))
  have hp : ∀ t, HasDerivAt p (deriv (deriv x) t - A * (-(ω * (ω * cos (ω * t))))
      - B * (ω * (-(ω * sin (ω * t))))) t := fun t =>
    (((hd' t).hasDerivAt.sub (((hasDerivAt_sin_mul ω t).const_mul ω).neg.const_mul A)).sub
      (((hasDerivAt_cos_mul ω t).const_mul ω).const_mul B))
  have hE : ∀ t ∈ Icc 0 L, HasDerivAt (fun t => p t ^ 2 + ω ^ 2 * q t ^ 2) 0 t := by
    intro t ht
    have := ((hp t).pow 2).add (((hq t).pow 2).const_mul (ω ^ 2))
    convert this using 1
    simp only [Nat.cast_ofNat]
    rw [hode t ht]
    have e : q t = x t - A * cos (ω * t) - B * sin (ω * t) := rfl
    have e' : p t = deriv x t - A * (-(ω * sin (ω * t))) - B * (ω * cos (ω * t)) := rfl
    rw [e']
    simp only [e]
    ring
  have hcont : ContinuousOn (fun t => p t ^ 2 + ω ^ 2 * q t ^ 2) (Icc 0 L) := fun t ht =>
    (hE t ht).continuousAt.continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont
    (fun t ht => (hE t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
  have p0 : p 0 = 0 := by simp only [p, hB]; field_simp; simp
  have q0 : q 0 = 0 := by simp [q, hA]
  intro t ht
  have h := hconst t ht
  simp only [p0, q0] at h
  have hq0 : q t = 0 := by
    have hω2 : 0 < ω ^ 2 := by positivity
    have h2 : ω ^ 2 * q t ^ 2 = 0 := by
      nlinarith [sq_nonneg (p t), mul_nonneg hω2.le (sq_nonneg (q t))]
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd h3 hω2.ne'
    · exact pow_eq_zero_iff (two_ne_zero) |>.1 h3
  have : q t = 0 := hq0
  simp only [q] at this
  linarith

/-- **Eigenfunctions (DE-115).** For `L > 0` and `n ≥ 1`, `sin(nπt/L)` is a nonzero solution of
`x'' + λ x = 0`, `x(0) = x(L) = 0`, with `λ = (nπ/L)²`. -/
@[kb "lebldiffyqs2026" "Example 4.1.3, p. 190"]
theorem sin_dirichlet_eigenfunction {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 0 < n) :
    ContDiff ℝ 2 (fun t => sin (n * π / L * t)) ∧
      (∀ t, deriv (deriv (fun t => sin (n * π / L * t))) t
        + (n * π / L) ^ 2 * sin (n * π / L * t) = 0) ∧
      sin (n * π / L * 0) = 0 ∧ sin (n * π / L * L) = 0 ∧
      ∃ t, sin (n * π / L * t) ≠ 0 := by
  refine ⟨by fun_prop, fun t => ?_, by simp, ?_, ?_⟩
  · rw [deriv_sin_mul]
    rw [(hasDerivAt_cos_mul (n * π / L) t).const_mul (n * π / L) |>.deriv]
    ring
  · have : (n : ℝ) * π / L * L = n * π := by field_simp
    rw [this, sin_nat_mul_pi]
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    refine ⟨L / (2 * n), ?_⟩
    have : (n : ℝ) * π / L * (L / (2 * n)) = π / 2 := by field_simp
    rw [this, sin_pi_div_two]; exact one_ne_zero

/-- **Dirichlet eigenvalues are `(nπ/L)²` (DE-115).** If `λ > 0` and `x'' + λ x = 0` on `[0, L]`,
`x(0) = x(L) = 0`, has a nonzero solution, then `λ = (nπ/L)²` for some `n ≥ 1`. -/
@[kb "lebldiffyqs2026" "Example 4.1.3, p. 190"]
theorem dirichlet_eigenvalue_of_pos {L lam : ℝ} (hL : 0 < L) (hlam : 0 < lam) {x : ℝ → ℝ}
    (hx : ContDiff ℝ 2 x) (hode : ∀ t ∈ Icc 0 L, deriv (deriv x) t + lam * x t = 0)
    (h0 : x 0 = 0) (hxL : x L = 0) (hne : ∃ t ∈ Icc 0 L, x t ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ lam = (n * π / L) ^ 2 := by
  set ω := Real.sqrt lam with hωdef
  have hω : 0 < ω := Real.sqrt_pos.2 hlam
  have hω2 : ω ^ 2 = lam := Real.sq_sqrt hlam.le
  have hsol := ode_solution_eq hω.ne' hx (L := L) (fun t ht => by rw [hω2]; linarith [hode t ht])
  have hB : deriv x 0 / ω * sin (ω * L) = 0 := by
    have := hsol L ⟨hL.le, le_rfl⟩
    rw [h0, hxL] at this; simpa using this.symm
  obtain ⟨t0, ht0, hxt0⟩ := hne
  have hB0 : deriv x 0 / ω ≠ 0 := by
    intro hz
    have := hsol t0 ht0
    rw [h0, hz] at this; simp at this; exact hxt0 this
  have hs : sin (ω * L) = 0 := (mul_eq_zero.1 hB).resolve_left hB0
  obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.1 hs
  have hmpos : 0 < m := by
    have : (0 : ℝ) < m * π := by rw [hm]; positivity
    have h' : (0 : ℝ) < m := by
      by_contra hc; have hc' := not_lt.1 hc; nlinarith [Real.pi_pos]
    exact_mod_cast h'
  refine ⟨m.toNat, by omega, ?_⟩
  have hcast : ((m.toNat : ℕ) : ℝ) = m := by exact_mod_cast Int.toNat_of_nonneg hmpos.le
  rw [hcast, ← hω2]
  congr 1
  field_simp
  linarith

/-- **Example 4.1.1 (DE-113).** For `λ = 1` on `[0, π]` the problem `x'' + x = 0`, `x(0) = x(π) = 0` has
infinitely many solutions: every `C sin t` solves it, and these are all the solutions. -/
@[kb "lebldiffyqs2026" "Example 4.1.1, p. 189"]
theorem dirichlet_pi_lambda_one :
    (∀ C : ℝ, ContDiff ℝ 2 (fun t => C * sin t) ∧
      (∀ t, deriv (deriv (fun t => C * sin t)) t + 1 * (C * sin t) = 0) ∧
      C * sin 0 = 0 ∧ C * sin π = 0) ∧
    ∀ x : ℝ → ℝ, ContDiff ℝ 2 x → (∀ t ∈ Icc 0 π, deriv (deriv x) t + 1 * x t = 0) →
      x 0 = 0 → x π = 0 → ∃ C : ℝ, ∀ t ∈ Icc 0 π, x t = C * sin t := by
  refine ⟨fun C => ⟨by fun_prop, fun t => ?_, by simp, by simp⟩, ?_⟩
  · have h1 : deriv (fun t => C * sin t) = fun t => C * cos t := by
      funext s; exact (Real.hasDerivAt_sin s |>.const_mul C).deriv
    rw [h1, (Real.hasDerivAt_cos t |>.const_mul C).deriv]; ring
  · intro x hx hode h0 _
    refine ⟨deriv x 0, fun t ht => ?_⟩
    have := ode_solution_eq (ω := 1) one_ne_zero hx (L := π)
      (fun t ht => by simp; linarith [hode t ht]) t ht
    simpa [h0] using this

/-- **Example 4.1.2 (DE-113).** For `λ = 2` on `[0, π]` the problem `x'' + 2x = 0`,
`x(0) = x(π) = 0` has only the zero solution. -/
@[kb "lebldiffyqs2026" "Example 4.1.2, p. 189"]
theorem dirichlet_pi_lambda_two {x : ℝ → ℝ} (hx : ContDiff ℝ 2 x)
    (hode : ∀ t ∈ Icc 0 π, deriv (deriv x) t + 2 * x t = 0) (h0 : x 0 = 0) (hπ : x π = 0) :
    ∀ t ∈ Icc 0 π, x t = 0 := by
  by_contra hc
  push Not at hc
  obtain ⟨n, hn, h⟩ := dirichlet_eigenvalue_of_pos Real.pi_pos (by norm_num : (0 : ℝ) < 2) hx
    hode h0 hπ hc
  have h' : (n : ℝ) ^ 2 = 2 := by
    have : (n : ℝ) * π / π = n := by field_simp
    rw [this] at h; linarith
  have h'' : n ^ 2 = 2 := by exact_mod_cast h'
  have : n ≤ 1 ∨ 2 ≤ n := by omega
  rcases this with h1 | h1 <;> nlinarith

/-! ## Orthogonality of eigenfunctions (Lebl §4.1, §5.1) -/

/-- **Orthogonality for the regular Sturm-Liouville equation (DE-156).**  Let `p` be `C¹` and `y₁, y₂`
be `C²` solutions of `(p y')' + q y + λᵢ r y = 0` on `[a, b]` with `λ₁ ≠ λ₂`.  If the boundary term
`p (y₁' y₂ - y₁ y₂')` takes the same value at `b` as at `a` (as it does for Dirichlet, Neumann or periodic
conditions), then `∫ y₁ y₂ r = 0`. -/
theorem sl_orthogonality_of_boundary {a b : ℝ} (hab : a ≤ b) {p q r : ℝ → ℝ} (hp : ContDiff ℝ 1 p)
    {y₁ y₂ : ℝ → ℝ} (hy₁ : ContDiff ℝ 2 y₁) (hy₂ : ContDiff ℝ 2 y₂) {l₁ l₂ : ℝ}
    (h₁ : ∀ t ∈ Icc a b, deriv (fun t => p t * deriv y₁ t) t + q t * y₁ t + l₁ * r t * y₁ t = 0)
    (h₂ : ∀ t ∈ Icc a b, deriv (fun t => p t * deriv y₂ t) t + q t * y₂ t + l₂ * r t * y₂ t = 0)
    (hbd : p b * (deriv y₁ b * y₂ b - y₁ b * deriv y₂ b)
      = p a * (deriv y₁ a * y₂ a - y₁ a * deriv y₂ a)) (hne : l₁ ≠ l₂) :
    ∫ t in a..b, y₁ t * y₂ t * r t = 0 := by
  have d1 := contDiff_deriv_aux hy₁
  have d2 := contDiff_deriv_aux hy₂
  have P1 : ContDiff ℝ 1 (fun t => p t * deriv y₁ t) := hp.mul d1
  have P2 : ContDiff ℝ 1 (fun t => p t * deriv y₂ t) := hp.mul d2
  have hy1d : ∀ t, HasDerivAt y₁ (deriv y₁ t) t := fun t =>
    ((hy₁.differentiable (by norm_num)) t).hasDerivAt
  have hy2d : ∀ t, HasDerivAt y₂ (deriv y₂ t) t := fun t =>
    ((hy₂.differentiable (by norm_num)) t).hasDerivAt
  have hP1 : ∀ t, HasDerivAt (fun t => p t * deriv y₁ t) (deriv (fun t => p t * deriv y₁ t) t) t :=
    fun t => ((P1.differentiable one_ne_zero) t).hasDerivAt
  have hP2 : ∀ t, HasDerivAt (fun t => p t * deriv y₂ t) (deriv (fun t => p t * deriv y₂ t) t) t :=
    fun t => ((P2.differentiable one_ne_zero) t).hasDerivAt
  set f' : ℝ → ℝ := fun t =>
    deriv (fun t => p t * deriv y₁ t) t * y₂ t + (p t * deriv y₁ t) * deriv y₂ t
      - (deriv (fun t => p t * deriv y₂ t) t * y₁ t + (p t * deriv y₂ t) * deriv y₁ t) with hf'
  have hW : ∀ t, HasDerivAt (fun t => (p t * deriv y₁ t) * y₂ t - (p t * deriv y₂ t) * y₁ t)
      (f' t) t := fun t => ((hP1 t).mul (hy2d t)).sub ((hP2 t).mul (hy1d t))
  have c1 := P1.continuous_deriv le_rfl
  have c2 := P2.continuous_deriv le_rfl
  have cy1 := hy₁.continuous
  have cy2 := hy₂.continuous
  have cd1 := d1.continuous
  have cd2 := d2.continuous
  have cp := hp.continuous
  have hc : Continuous f' := by simp only [hf']; fun_prop
  have hint := integral_eq_sub_of_hasDerivAt (fun t _ => hW t) (hc.intervalIntegrable a b)
  have hcongr : ∫ t in a..b, f' t = (l₂ - l₁) * ∫ t in a..b, y₁ t * y₂ t * r t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hab] at ht
    have e1 := h₁ t ht
    have e2 := h₂ t ht
    simp only [hf']
    linear_combination (y₂ t) * e1 - (y₁ t) * e2
  have : (l₂ - l₁) * ∫ t in a..b, y₁ t * y₂ t * r t = 0 := by
    rw [← hcongr, hint]
    linear_combination hbd
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (sub_eq_zero.1 h).symm hne
  · exact h

/-- **Regular Sturm-Liouville problem with Dirichlet conditions (DE-156).** Eigenfunctions for distinct
eigenvalues of `(p y')' + q y + λ r y = 0`, `y(a) = y(b) = 0`, are orthogonal with weight `r`. -/
@[kb "lebldiffyqs2026" "Theorem 5.1.2, p. 277"]
theorem sl_orthogonality_dirichlet {a b : ℝ} (hab : a ≤ b) {p q r : ℝ → ℝ} (hp : ContDiff ℝ 1 p)
    {y₁ y₂ : ℝ → ℝ} (hy₁ : ContDiff ℝ 2 y₁) (hy₂ : ContDiff ℝ 2 y₂) {l₁ l₂ : ℝ}
    (h₁ : ∀ t ∈ Icc a b, deriv (fun t => p t * deriv y₁ t) t + q t * y₁ t + l₁ * r t * y₁ t = 0)
    (h₂ : ∀ t ∈ Icc a b, deriv (fun t => p t * deriv y₂ t) t + q t * y₂ t + l₂ * r t * y₂ t = 0)
    (ha₁ : y₁ a = 0) (hb₁ : y₁ b = 0) (ha₂ : y₂ a = 0) (hb₂ : y₂ b = 0) (hne : l₁ ≠ l₂) :
    ∫ t in a..b, y₁ t * y₂ t * r t = 0 :=
  sl_orthogonality_of_boundary hab hp hy₁ hy₂ h₁ h₂ (by simp [ha₁, hb₁, ha₂, hb₂]) hne

/-- Orthogonality for `x'' + λ x = 0` under any boundary condition making the Wronskian-type term
`x₁' x₂ - x₁ x₂'` agree at the two endpoints. -/
theorem eigen_orthogonality_of_boundary {a b : ℝ} (hab : a ≤ b) {y₁ y₂ : ℝ → ℝ}
    (hy₁ : ContDiff ℝ 2 y₁) (hy₂ : ContDiff ℝ 2 y₂) {l₁ l₂ : ℝ}
    (h₁ : ∀ t ∈ Icc a b, deriv (deriv y₁) t + l₁ * y₁ t = 0)
    (h₂ : ∀ t ∈ Icc a b, deriv (deriv y₂) t + l₂ * y₂ t = 0)
    (hbd : deriv y₁ b * y₂ b - y₁ b * deriv y₂ b = deriv y₁ a * y₂ a - y₁ a * deriv y₂ a)
    (hne : l₁ ≠ l₂) : ∫ t in a..b, y₁ t * y₂ t = 0 := by
  have := sl_orthogonality_of_boundary hab (p := fun _ => 1) (q := fun _ => 0) (r := fun _ => 1)
    contDiff_const hy₁ hy₂ (fun t ht => by simpa using h₁ t ht) (fun t ht => by simpa using h₂ t ht)
    (by simpa using hbd) hne
  simpa using this

/-- **Dirichlet eigenfunctions are orthogonal (DE-117).** -/
@[kb "lebldiffyqs2026" "Theorem 4.1.1, p. 193"]
theorem eigen_orthogonality_dirichlet {a b : ℝ} (hab : a ≤ b) {y₁ y₂ : ℝ → ℝ}
    (hy₁ : ContDiff ℝ 2 y₁) (hy₂ : ContDiff ℝ 2 y₂) {l₁ l₂ : ℝ}
    (h₁ : ∀ t ∈ Icc a b, deriv (deriv y₁) t + l₁ * y₁ t = 0)
    (h₂ : ∀ t ∈ Icc a b, deriv (deriv y₂) t + l₂ * y₂ t = 0)
    (ha₁ : y₁ a = 0) (hb₁ : y₁ b = 0) (ha₂ : y₂ a = 0) (hb₂ : y₂ b = 0) (hne : l₁ ≠ l₂) :
    ∫ t in a..b, y₁ t * y₂ t = 0 :=
  eigen_orthogonality_of_boundary hab hy₁ hy₂ h₁ h₂ (by simp [ha₁, hb₁, ha₂, hb₂]) hne

/-- **Neumann eigenfunctions are orthogonal (DE-117).** -/
@[kb "lebldiffyqs2026" "Theorem 4.1.1, p. 193"]
theorem eigen_orthogonality_neumann {a b : ℝ} (hab : a ≤ b) {y₁ y₂ : ℝ → ℝ}
    (hy₁ : ContDiff ℝ 2 y₁) (hy₂ : ContDiff ℝ 2 y₂) {l₁ l₂ : ℝ}
    (h₁ : ∀ t ∈ Icc a b, deriv (deriv y₁) t + l₁ * y₁ t = 0)
    (h₂ : ∀ t ∈ Icc a b, deriv (deriv y₂) t + l₂ * y₂ t = 0)
    (ha₁ : deriv y₁ a = 0) (hb₁ : deriv y₁ b = 0) (ha₂ : deriv y₂ a = 0) (hb₂ : deriv y₂ b = 0)
    (hne : l₁ ≠ l₂) : ∫ t in a..b, y₁ t * y₂ t = 0 :=
  eigen_orthogonality_of_boundary hab hy₁ hy₂ h₁ h₂ (by simp [ha₁, hb₁, ha₂, hb₂]) hne

/-- **Periodic eigenfunctions are orthogonal (DE-117).** -/
@[kb "lebldiffyqs2026" "Theorem 4.1.1, p. 193"]
theorem eigen_orthogonality_periodic {a b : ℝ} (hab : a ≤ b) {y₁ y₂ : ℝ → ℝ}
    (hy₁ : ContDiff ℝ 2 y₁) (hy₂ : ContDiff ℝ 2 y₂) {l₁ l₂ : ℝ}
    (h₁ : ∀ t ∈ Icc a b, deriv (deriv y₁) t + l₁ * y₁ t = 0)
    (h₂ : ∀ t ∈ Icc a b, deriv (deriv y₂) t + l₂ * y₂ t = 0)
    (hv₁ : y₁ a = y₁ b) (hd₁ : deriv y₁ a = deriv y₁ b)
    (hv₂ : y₂ a = y₂ b) (hd₂ : deriv y₂ a = deriv y₂ b) (hne : l₁ ≠ l₂) :
    ∫ t in a..b, y₁ t * y₂ t = 0 :=
  eigen_orthogonality_of_boundary hab hy₁ hy₂ h₁ h₂ (by rw [← hv₁, ← hd₁, ← hv₂, ← hd₂]) hne

/-! ## Orthogonality of the trigonometric system (Lebl §4.2) -/

lemma integral_cos_int {L : ℝ} (hL : 0 < L) (k : ℤ) :
    ∫ t in (-L)..L, cos (k * π / L * t) = if k = 0 then 2 * L else 0 := by
  by_cases hk : k = 0
  · subst hk; simp; ring
  · simp only [hk, ↓reduceIte]
    have hc : (k : ℝ) * π / L ≠ 0 := by
      have : (k : ℝ) ≠ 0 := by exact_mod_cast hk
      positivity
    rw [intervalIntegral.integral_comp_mul_left (fun t => cos t) hc, integral_cos]
    have e1 : (k : ℝ) * π / L * L = k * π := by field_simp
    have e2 : (k : ℝ) * π / L * (-L) = -(k * π) := by field_simp
    rw [e1, e2, sin_neg, Real.sin_int_mul_pi]; simp

/-- **Orthogonality of sines (DE-122).** For `n, m ≥ 1`, `∫_{-L}^{L} sin(nπt/L) sin(mπt/L) dt` is `L` if
`n = m` and `0` otherwise. -/
@[kb "lebldiffyqs2026" "§4.2 orthogonality of sine and cosine, p. 201"]
theorem integral_sin_mul_sin {L : ℝ} (hL : 0 < L) {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    ∫ t in (-L)..L, sin (n * π / L * t) * sin (m * π / L * t) = if n = m then L else 0 := by
  have e : ∀ t : ℝ, sin (n * π / L * t) * sin (m * π / L * t)
      = (cos (((n : ℤ) - m : ℤ) * π / L * t) - cos (((n : ℤ) + m : ℤ) * π / L * t)) / 2 := by
    intro t
    have : (n : ℝ) * π / L * t = (n : ℝ) * π / L * t := rfl
    push_cast
    rw [show ((n : ℝ) - m) * π / L * t = (n : ℝ) * π / L * t - (m : ℝ) * π / L * t by ring,
      show ((n : ℝ) + m) * π / L * t = (n : ℝ) * π / L * t + (m : ℝ) * π / L * t by ring,
      cos_sub, cos_add]
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
    ((by fun_prop : Continuous _).intervalIntegrable _ _)
    ((by fun_prop : Continuous _).intervalIntegrable _ _),
    integral_cos_int hL, integral_cos_int hL]
  by_cases h : n = m
  · subst h
    have : (n : ℤ) + n ≠ 0 := by omega
    simp [this]
  · have h1 : (n : ℤ) - m ≠ 0 := by omega
    have h2 : (n : ℤ) + m ≠ 0 := by omega
    simp [h, h1, h2]

/-- **Orthogonality of cosines (DE-122).** For `n, m ≥ 0`, `∫_{-L}^{L} cos(nπt/L) cos(mπt/L) dt` is
`0` for `n ≠ m`, `L` for `n = m ≥ 1`, and `2L` for `n = m = 0`. -/
@[kb "lebldiffyqs2026" "§4.2 orthogonality of sine and cosine, p. 201"]
theorem integral_cos_mul_cos {L : ℝ} (hL : 0 < L) (n m : ℕ) :
    ∫ t in (-L)..L, cos (n * π / L * t) * cos (m * π / L * t)
      = if n = m then (if n = 0 then 2 * L else L) else 0 := by
  have e : ∀ t : ℝ, cos (n * π / L * t) * cos (m * π / L * t)
      = (cos (((n : ℤ) - m : ℤ) * π / L * t) + cos (((n : ℤ) + m : ℤ) * π / L * t)) / 2 := by
    intro t
    push_cast
    rw [show ((n : ℝ) - m) * π / L * t = (n : ℝ) * π / L * t - (m : ℝ) * π / L * t by ring,
      show ((n : ℝ) + m) * π / L * t = (n : ℝ) * π / L * t + (m : ℝ) * π / L * t by ring,
      cos_sub, cos_add]
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    ((by fun_prop : Continuous _).intervalIntegrable _ _)
    ((by fun_prop : Continuous _).intervalIntegrable _ _),
    integral_cos_int hL, integral_cos_int hL]
  by_cases h : n = m
  · subst h
    by_cases h0 : n = 0
    · subst h0; simp
    · have : (n : ℤ) + n ≠ 0 := by omega
      simp [this, h0]
  · have h1 : (n : ℤ) - m ≠ 0 := by omega
    by_cases h2 : (n : ℤ) + m = 0
    · omega
    · simp [h, h1, h2]

/-- **Sine and cosine are orthogonal (DE-122).** `∫_{-L}^{L} sin(nπt/L) cos(mπt/L) dt = 0` for all `n, m`. -/
@[kb "lebldiffyqs2026" "§4.2 orthogonality of sine and cosine, p. 201"]
theorem integral_sin_mul_cos (L : ℝ) (n m : ℕ) :
    ∫ t in (-L)..L, sin (n * π / L * t) * cos (m * π / L * t) = 0 := by
  have h := intervalIntegral.integral_comp_neg (a := -L) (b := L)
    (fun t => sin (n * π / L * t) * cos (m * π / L * t))
  simp only [mul_neg, sin_neg, cos_neg, neg_neg, neg_mul, intervalIntegral.integral_neg] at h
  linarith

end UndergradKB.DifferentialEquations
