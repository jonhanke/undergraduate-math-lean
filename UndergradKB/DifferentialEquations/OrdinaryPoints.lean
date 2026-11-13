import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.ODE.ExistUnique
import UndergradKB.DifferentialEquations.Picard
import UndergradKB.DifferentialEquations.Nonlinear
import UndergradKB.DifferentialEquations.SecondOrderSystems
import UndergradKB.Common.Attr

/-! # Ordinary and singular points, and planar critical points (Lebl, Chapters 7 and 8)

Ordinary / singular / regular singular points of `P y'' + Q y' + R y = 0` with real polynomial coefficients,
power series of rational functions, the Frobenius example `x^{1/2} e^x`, almost linear critical points,
periodicity of closed trajectories, the divergence of a planar field and second-order autonomous
equations as planar systems. -/

namespace UndergradKB.DifferentialEquations

open Polynomial Set Filter Topology

/-! ## Power series of rational functions (DE-200) -/

/-- **Rational functions are analytic** (DE-200): if `Q(x₀) ≠ 0` then `P/Q` is analytic at `x₀`
(so it has a power series about `x₀`). -/
@[kb "lebldiffyqs2026" "§7.1.5 Power series for rational functions, p. 332"]
theorem analyticAt_rational (P Q : ℝ[X]) {x₀ : ℝ} (h : Q.eval x₀ ≠ 0) :
    AnalyticAt ℝ (fun x => P.eval x / Q.eval x) x₀ := by
  have hp : ∀ R : ℝ[X], AnalyticAt ℝ (fun x => R.eval x) x₀ := fun R => by
    simpa using (analyticAt_id (𝕜 := ℝ) (z := x₀)).aeval_polynomial R
  exact (hp P).div (hp Q) h

/-- **Example 7.1.6** (DE-200): `1/(1+x)² = ∑ (-1)^k (k+1) x^k` for `|x| < 1`. -/
@[kb "lebldiffyqs2026" "Example 7.1.6, p. 333"]
theorem hasSum_inv_one_add_sq {x : ℝ} (hx : |x| < 1) :
    HasSum (fun k : ℕ => (-1 : ℝ) ^ k * ((k : ℝ) + 1) * x ^ k) (1 / (1 + x) ^ 2) := by
  have hn : ‖-x‖ < 1 := by simpa using hx
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one hn
  have h2 := hasSum_geometric_of_norm_lt_one hn
  have h3 := h1.add h2
  have hpos : 1 + x ≠ 0 := by
    have := abs_lt.1 hx; linarith
  convert h3 using 1
  · funext k
    have : (-x) ^ k = (-1) ^ k * x ^ k := by rw [neg_eq_neg_one_mul, mul_pow]
    rw [this]; ring
  · have e : (1 : ℝ) - -x = 1 + x := by ring
    rw [e]
    field_simp
    ring

/-! ## Ordinary and singular points (DE-201) -/

/-- `x₀` is an ordinary point of `P y'' + Q y' + R y = 0` (polynomial coefficients) if `P(x₀) ≠ 0`. -/
def IsOrdinaryPt (P : ℝ[X]) (x₀ : ℝ) : Prop := P.eval x₀ ≠ 0

/-- `x₀` is a singular point if `P(x₀) = 0`. -/
def IsSingularPt (P : ℝ[X]) (x₀ : ℝ) : Prop := P.eval x₀ = 0

/-- `y` solves `P y'' + Q y' + R y = 0` on `I` (twice differentiable there). -/
def SolvesPoly (P Q R : ℝ[X]) (I : Set ℝ) (y : ℝ → ℝ) : Prop :=
  ∀ t ∈ I, DifferentiableAt ℝ y t ∧ DifferentiableAt ℝ (deriv y) t ∧
    P.eval t * deriv (deriv y) t + Q.eval t * deriv y t + R.eval t * y t = 0

lemma solvesPoly_iff {P Q R : ℝ[X]} {I : Set ℝ} (hP : ∀ t ∈ I, P.eval t ≠ 0) (y : ℝ → ℝ) :
    SolvesPoly P Q R I y ↔
      SolvesLin2 (fun t => Q.eval t / P.eval t) (fun t => R.eval t / P.eval t) 0 I y := by
  refine forall₂_congr fun t ht => and_congr_right fun _ => and_congr_right fun _ => ?_
  have := hP t ht
  simp only [Pi.zero_apply]
  constructor
  · intro h
    field_simp
    linear_combination h
  · intro h
    field_simp at h
    linear_combination h

/-- **Initial value problems at an ordinary point** (DE-201): if `P(x₀) ≠ 0`, there is an open interval around
`x₀` on which, for all `y₀, y₁`, the problem `P y'' + Q y' + R y = 0`, `y(x₀) = y₀`, `y'(x₀) = y₁` has exactly
one solution. -/
@[kb "lebldiffyqs2026" "§7.2 Ordinary and singular points, p. 335"]
theorem ordinaryPt_ivp (P Q R : ℝ[X]) {x₀ : ℝ} (h : IsOrdinaryPt P x₀) :
    ∃ a b : ℝ, a < x₀ ∧ x₀ < b ∧ ∀ y₀ y₁ : ℝ, ∃ y : ℝ → ℝ,
      (SolvesPoly P Q R (Ioo a b) y ∧ y x₀ = y₀ ∧ deriv y x₀ = y₁) ∧
      ∀ z : ℝ → ℝ, SolvesPoly P Q R (Ioo a b) z → z x₀ = y₀ → deriv z x₀ = y₁ →
        ∀ t ∈ Ioo a b, z t = y t := by
  have hev : ∀ᶠ t in 𝓝 x₀, P.eval t ≠ 0 := P.continuous.continuousAt.eventually_ne h
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hI : ∀ t ∈ Ioo (x₀ - ε) (x₀ + ε), P.eval t ≠ 0 := fun t ht =>
    hball t (by rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]; constructor <;> linarith [ht.1, ht.2])
  refine ⟨x₀ - ε, x₀ + ε, by linarith, by linarith, fun y₀ y₁ => ?_⟩
  have hx₀ : x₀ ∈ Ioo (x₀ - ε) (x₀ + ε) := ⟨by linarith, by linarith⟩
  have hp : ContinuousOn (fun t => Q.eval t / P.eval t) (Ioo (x₀ - ε) (x₀ + ε)) :=
    Q.continuous.continuousOn.div P.continuous.continuousOn hI
  have hq : ContinuousOn (fun t => R.eval t / P.eval t) (Ioo (x₀ - ε) (x₀ + ε)) :=
    R.continuous.continuousOn.div P.continuous.continuousOn hI
  obtain ⟨y, hy, h0, h1⟩ := lin2_exists isOpen_Ioo ordConnected_Ioo hp hq continuousOn_const hx₀ y₀ y₁
  refine ⟨y, ⟨(solvesPoly_iff hI y).2 hy, h0, h1⟩, fun z hz hz0 hz1 => ?_⟩
  exact lin2_unique ordConnected_Ioo hp hq ((solvesPoly_iff hI z).1 hz) hy hx₀ (by rw [hz0, h0])
    (by rw [hz1, h1])

/-! ## Regular singular points (DE-206) -/

/-- `x₀` is a regular singular point: `P(x₀) = 0` and the limits of `(x-x₀) Q/P` and `(x-x₀)² R/P` at `x₀`
exist and are finite. -/
def IsRegularSingPt (P Q R : ℝ[X]) (x₀ : ℝ) : Prop :=
  IsSingularPt P x₀ ∧
    (∃ L : ℝ, Tendsto (fun x => (x - x₀) * Q.eval x / P.eval x) (𝓝[≠] x₀) (𝓝 L)) ∧
    (∃ L : ℝ, Tendsto (fun x => (x - x₀) ^ 2 * R.eval x / P.eval x) (𝓝[≠] x₀) (𝓝 L))

/-- **Bessel's equation** `x² y'' + x y' + (x² - p²) y = 0` has a regular singular point at `0` (DE-206). -/
@[kb "lebldiffyqs2026" "§7.3.2 Regular singular point, p. 345"]
theorem bessel_regularSingPt (p : ℝ) :
    IsRegularSingPt (X ^ 2) X (X ^ 2 - C (p ^ 2)) 0 := by
  refine ⟨by simp [IsSingularPt], ⟨1, ?_⟩, ⟨-p ^ 2, ?_⟩⟩
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have : x ≠ 0 := hx
    simp; field_simp
  · have : Tendsto (fun x : ℝ => x ^ 2 - p ^ 2) (𝓝[≠] 0) (𝓝 (-p ^ 2)) := by
      have : Tendsto (fun x : ℝ => x ^ 2 - p ^ 2) (𝓝 0) (𝓝 (0 ^ 2 - p ^ 2)) :=
        (by fun_prop : Continuous fun x : ℝ => x ^ 2 - p ^ 2).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have : x ≠ 0 := hx
    simp; field_simp

/-- **Euler's equation** `x² y'' + a x y' + b y = 0` has a regular singular point at `0` (DE-206). -/
@[kb "lebldiffyqs2026" "§7.3.2 Regular singular point, p. 345"]
theorem euler_regularSingPt (a b : ℝ) :
    IsRegularSingPt (X ^ 2) (C a * X) (C b) 0 := by
  refine ⟨by simp [IsSingularPt], ⟨a, ?_⟩, ⟨b, ?_⟩⟩
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have : x ≠ 0 := hx
    simp; field_simp
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have : x ≠ 0 := hx
    simp; field_simp

/-- **Example 7.3.3** (DE-206): `x² y'' + (1+x) y' + (π + x²) y = 0` has `0` as a singular point that is
not regular: the limit of `x Q/P = (1+x)/x` does not exist (it is not finite). -/
@[kb "lebldiffyqs2026" "Example 7.3.3, p. 345"]
theorem irregular_singPt_example :
    IsSingularPt (X ^ 2) 0 ∧
      ¬ IsRegularSingPt (X ^ 2) (1 + X) (C Real.pi + X ^ 2) 0 := by
  refine ⟨by simp [IsSingularPt], ?_⟩
  rintro ⟨-, ⟨L, hL⟩, -⟩
  have h1 : Tendsto (fun x : ℝ => x * ((x - 0) * (1 + X : ℝ[X]).eval x / (X ^ 2 : ℝ[X]).eval x))
      (𝓝[≠] 0) (𝓝 (0 * L)) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).mul hL
  have h2 : Tendsto (fun x : ℝ => 1 + x) (𝓝[≠] 0) (𝓝 1) := by
    have : Tendsto (fun x : ℝ => 1 + x) (𝓝 0) (𝓝 (1 + 0)) :=
      (by fun_prop : Continuous fun x : ℝ => 1 + x).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have h3 := h2.congr' (f₂ := fun x : ℝ => x * ((x - 0) * (1 + X : ℝ[X]).eval x / (X ^ 2 : ℝ[X]).eval x)) <| by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have : x ≠ 0 := hx
    simp; field_simp
  have := tendsto_nhds_unique h1 h3
  simp at this

/-! ## Frobenius example (DE-205) -/

/-- **Example 7.3.2** (DE-205): for `x > 0`, `y = x^{1/2} e^x` solves `4x² y'' - 4x² y' + (1-2x) y = 0`. -/
@[kb "lebldiffyqs2026" "Example 7.3.2, p. 343"]
theorem frobenius_example_solves :
    SolvesPoly (C 4 * X ^ 2) (-(C 4 * X ^ 2)) (1 - C 2 * X) (Ioi 0)
      (fun x => Real.sqrt x * Real.exp x) := by
  intro t ht
  have ht0 : 0 < t := ht
  have hspos : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0.le
  have hs : ∀ u : ℝ, 0 < u → HasDerivAt Real.sqrt (1 / (2 * Real.sqrt u)) u := fun u hu =>
    Real.hasDerivAt_sqrt hu.ne'
  let y1 : ℝ → ℝ := fun u => Real.exp u * (Real.sqrt u + 1 / (2 * Real.sqrt u))
  have hy : ∀ u : ℝ, 0 < u → HasDerivAt (fun x => Real.sqrt x * Real.exp x) (y1 u) u := fun u hu =>
    ((hs u hu).mul (Real.hasDerivAt_exp u)).congr_deriv (by simp only [y1]; ring)
  have hd : ∀ u : ℝ, 0 < u → deriv (fun x => Real.sqrt x * Real.exp x) u = y1 u := fun u hu =>
    (hy u hu).deriv
  have heq : deriv (fun x => Real.sqrt x * Real.exp x) =ᶠ[𝓝 t] y1 := by
    filter_upwards [Ioi_mem_nhds ht0] with u hu using hd u hu
  have h2 : HasDerivAt (fun u => 1 / (2 * Real.sqrt u))
      ((0 * (2 * Real.sqrt t) - 1 * (2 * (1 / (2 * Real.sqrt t)))) / (2 * Real.sqrt t) ^ 2) t :=
    (hasDerivAt_const t (1 : ℝ)).div ((hs t ht0).const_mul 2) (by positivity)
  have hy1 : HasDerivAt y1 (Real.exp t * (Real.sqrt t + 1 / (2 * Real.sqrt t)) +
      Real.exp t * (1 / (2 * Real.sqrt t) +
        (0 * (2 * Real.sqrt t) - 1 * (2 * (1 / (2 * Real.sqrt t)))) / (2 * Real.sqrt t) ^ 2)) t :=
    ((Real.hasDerivAt_exp t).mul ((hs t ht0).add h2)).congr_deriv
      (by simp only [Pi.add_apply])
  refine ⟨(hy t ht0).differentiableAt, hy1.differentiableAt.congr_of_eventuallyEq heq, ?_⟩
  rw [(hy1.congr_of_eventuallyEq heq).deriv, hd t ht0]
  simp only [y1, eval_mul, eval_neg, eval_pow, eval_X, eval_C, eval_sub, eval_one]
  generalize Real.sqrt t = s at *
  subst hsq
  field_simp
  ring

/-- **Indicial equation** (DE-205): `4r(r-1) + 1 = 0` has the double root `r = 1/2`. -/
@[kb "lebldiffyqs2026" "§7.3 Indicial equation, p. 344"]
theorem indicial_double_root (r : ℝ) :
    4 * r * (r - 1) + 1 = 4 * (r - 1 / 2) ^ 2 ∧ (4 * r * (r - 1) + 1 = 0 ↔ r = 1 / 2) := by
  refine ⟨by ring, ?_⟩
  constructor
  · intro h
    have : (r - 1 / 2) ^ 2 = 0 := by linarith
    have := pow_eq_zero_iff (two_ne_zero) |>.1 this
    linarith
  · rintro rfl; norm_num

/-! ## Almost linear critical points (DE-220) -/

/-- `p` is an isolated critical point of the planar field `F`: `F p = 0` and `p` is the only zero nearby. -/
def IsIsolatedCrit (F : ℝ × ℝ → ℝ × ℝ) (p : ℝ × ℝ) : Prop :=
  F p = 0 ∧ ∃ U ∈ 𝓝 p, ∀ q ∈ U, F q = 0 → q = p

/-- `p` is an almost linear critical point: `F` is `C¹`, `F p = 0` and the Jacobian `F'(p)` is invertible. -/
def IsAlmostLinearCrit (F : ℝ × ℝ → ℝ × ℝ) (p : ℝ × ℝ) : Prop :=
  ContDiff ℝ 1 F ∧ F p = 0 ∧ Function.Bijective (fderiv ℝ F p)

/-- **Almost linear critical points are isolated** (DE-220), by the inverse function theorem. -/
@[kb "lebldiffyqs2026" "§8.2.1 Isolated critical points and almost linear systems, p. 357"]
theorem IsAlmostLinearCrit.isIsolated {F : ℝ × ℝ → ℝ × ℝ} {p : ℝ × ℝ}
    (h : IsAlmostLinearCrit F p) : IsIsolatedCrit F p := by
  obtain ⟨hF, hp, hb⟩ := h
  let e : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
    ContinuousLinearEquiv.ofBijective (fderiv ℝ F p) (LinearMap.ker_eq_bot.2 hb.1)
      (LinearMap.range_eq_top.2 hb.2)
  have hs : HasStrictFDerivAt F (e : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p :=
    hF.contDiffAt.hasStrictFDerivAt_fderiv one_ne_zero
  let φ := hs.toOpenPartialHomeomorph F
  have hmem : p ∈ φ.source := hs.mem_toOpenPartialHomeomorph_source
  refine ⟨hp, φ.source, φ.open_source.mem_nhds hmem, fun q hq h0 => ?_⟩
  have hinj : Set.InjOn φ φ.source := φ.injOn
  apply hinj hq hmem
  change F q = F p
  rw [h0, hp]

/-- Example: `x' = -y - x²`, `y' = -x + y²` has an almost linear critical point at the origin. -/
theorem almostLinear_example :
    IsAlmostLinearCrit (fun w : ℝ × ℝ => (-w.2 - w.1 ^ 2, -w.1 + w.2 ^ 2)) (0, 0) := by
  have h1 := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt (x := ((0 : ℝ), (0 : ℝ)))
  have h2 := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt (x := ((0 : ℝ), (0 : ℝ)))
  have hd : HasFDerivAt (fun w : ℝ × ℝ => (-w.2 - w.1 ^ 2, -w.1 + w.2 ^ 2))
      ((-(ContinuousLinearMap.snd ℝ ℝ ℝ)).prod (-(ContinuousLinearMap.fst ℝ ℝ ℝ))) (0, 0) := by
    refine HasFDerivAt.prodMk ?_ ?_
    · have := h2.neg.sub (h1.mul h1)
      convert this using 1
      · funext w; simp [sq]
      · ext <;> simp
    · have := h1.neg.add (h2.mul h2)
      convert this using 1
      · funext w; simp [sq]
      · ext <;> simp
  refine ⟨by fun_prop, by simp, ?_⟩
  rw [hd.fderiv]
  constructor
  · intro a b hab
    simp only [ContinuousLinearMap.prod_apply, neg_apply,
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst', Prod.mk.injEq, neg_inj] at hab
    exact Prod.ext hab.2 hab.1
  · intro c
    exact ⟨(-c.2, -c.1), by simp⟩

/-! ## Closed trajectories (DE-231) -/

/-- **Closed trajectories are periodic** (DE-231): for an autonomous system `x' = F(x)` with `F` Lipschitz, a
global solution with `x(t₀ + T) = x(t₀)` is `T`-periodic. -/
@[kb "lebldiffyqs2026" "§8.4 Closed trajectories and limit cycles, p. 373"]
theorem autonomous_periodic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E → E} {K : NNReal}
    (hF : LipschitzWith K F) {x : ℝ → E} (hx : ∀ t, HasDerivAt x (F (x t)) t) {t₀ T : ℝ}
    (hT : x (t₀ + T) = x t₀) : Function.Periodic x T := by
  have hg : ∀ t, HasDerivAt (fun s => x (s + T)) (F (x (t + T))) t := fun t => by
    simpa using (hx (t + T)).comp_add_const t T
  have := ODE_solution_unique_univ (v := fun _ => F) (s := fun _ => univ) (K := K)
    (fun _ => hF.lipschitzOnWith) (fun t => ⟨hx t, trivial⟩) (fun t => ⟨hg t, trivial⟩)
    (f := x) (g := fun s => x (s + T)) (t₀ := t₀) (by simp [hT])
  intro t
  exact (congrFun this t).symm

/-! ## Divergence (DE-235) -/

/-- The divergence `∂f/∂x + ∂g/∂y` of the planar field `(f, g)` at `(x, y)`. -/
noncomputable def divergence (f g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun u => f u y) x + deriv (fun v => g x v) y

/-- **Divergence as a trace** (DE-235): if the field `F : ℝ² → ℝ²` has Fréchet derivative `L` at `(x,y)`, its
divergence is the trace `L(1,0).1 + L(0,1).2` of the Jacobian. -/
@[kb "lebldiffyqs2026" "§8.4 Divergence of the vector field, p. 376"]
theorem divergence_eq_trace {F : ℝ × ℝ → ℝ × ℝ} {L : ℝ × ℝ →L[ℝ] ℝ × ℝ} {x y : ℝ}
    (h : HasFDerivAt F L (x, y)) :
    divergence (fun a b => (F (a, b)).1) (fun a b => (F (a, b)).2) x y = (L (1, 0)).1 + (L (0, 1)).2 := by
  have h1 : HasDerivAt (fun u : ℝ => (u, y)) ((1 : ℝ), (0 : ℝ)) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
  have h2 : HasDerivAt (fun v : ℝ => (x, v)) ((0 : ℝ), (1 : ℝ)) y :=
    (hasDerivAt_const y x).prodMk (hasDerivAt_id y)
  have a1 := h.comp_hasDerivAt x h1
  have a2 := h.comp_hasDerivAt y h2
  have b1 := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt x a1
  have b2 := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt y a2
  have e1 : deriv (fun u => (F (u, y)).1) x = (L (1, 0)).1 := b1.deriv
  have e2 : deriv (fun v => (F (x, v)).2) y = (L (0, 1)).2 := b2.deriv
  unfold divergence
  simp only [e1, e2]

/-- **Example 8.4.3** (DE-235): the field `(y + y² eˣ, x)` has divergence `y² eˣ`. -/
@[kb "lebldiffyqs2026" "Example 8.4.3, p. 376"]
theorem divergence_example_843 (x y : ℝ) :
    divergence (fun x y => y + y ^ 2 * Real.exp x) (fun x _ => x) x y = y ^ 2 * Real.exp x := by
  unfold divergence
  have h1 : HasDerivAt (fun u : ℝ => y + y ^ 2 * Real.exp u) (y ^ 2 * Real.exp x) x :=
    ((Real.hasDerivAt_exp x).const_mul (y ^ 2)).const_add y
  rw [h1.deriv, deriv_const]
  simp

/-- **Example 8.4.4** (DE-235): the field `(-y - x², -x + y²)` has divergence `2(y - x)`. -/
@[kb "lebldiffyqs2026" "Example 8.4.4, p. 376"]
theorem divergence_example_844 (x y : ℝ) :
    divergence (fun x y => -y - x ^ 2) (fun x y => -x + y ^ 2) x y = 2 * (y - x) := by
  unfold divergence
  have h1 : HasDerivAt (fun u : ℝ => -y - u ^ 2) (-(2 * x)) x := by
    exact ((hasDerivAt_pow 2 x).const_sub (-y)).congr_deriv (by simp)
  have h2 : HasDerivAt (fun v : ℝ => -x + v ^ 2) (2 * y) y := by
    simpa using (hasDerivAt_pow 2 y).const_add (-x)
  rw [h1.deriv, h2.deriv]
  ring

/-! ## Second-order autonomous equations (DE-217) -/

/-- **Second-order autonomous equation as a planar system** (DE-217): `x'' = h(x, x')` corresponds to the planar
system `x' = y`, `y' = h(x, y)`; here `(x, y)` is a planar solution exactly when `(x, y)` solves the
first-order system with the vector field `(y, h(x,y))`. -/
@[kb "lebldiffyqs2026" "§8.1.1 Autonomous systems and phase plane, p. 352"]
theorem planar_sol_iff_second_order (h : ℝ → ℝ → ℝ) (x y : ℝ → ℝ) :
    IsPlanarSol (fun _ v => v) h x y ↔
      ∀ t, 0 ≤ t → HasDerivAt (fun s => (x s, y s)) (y t, h (x t) (y t)) t := by
  unfold IsPlanarSol
  refine forall_congr' fun t => imp_congr_right fun _ => ?_
  exact second_order_ode_iff_system (fun _ a b => h a b) x y t

/-- **Example 8.1.1** (DE-217): `x'' = -x + x²` is the planar system `x' = y`, `y' = -x + x²`. -/
@[kb "lebldiffyqs2026" "Example 8.1.1, p. 352"]
theorem planar_sol_example_811 (x y : ℝ → ℝ) :
    IsPlanarSol (fun _ v => v) (fun u _ => -u + u ^ 2) x y ↔
      ∀ t, 0 ≤ t → HasDerivAt x (y t) t ∧ HasDerivAt y (-x t + x t ^ 2) t :=
  Iff.rfl

end UndergradKB.DifferentialEquations
