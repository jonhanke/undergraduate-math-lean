import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.LagrangeMultipliers
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Topology.Order.Compact
import UndergradKB.Common.Attr

/-! # Calculus: differentiation of functions of two variables

Partial derivatives of `f : ℝ × ℝ → ℝ` (as `fderiv` applied to `(1,0)`, `(0,1)`), critical and saddle points,
tangent plane and linear approximation, total differential, directional derivative and gradient, the two-path
test, Lagrange multipliers, the second derivative test with `D = f_xx f_yy - f_xy²`, and extreme values on
compact sets. -/

namespace UndergradKB.Calculus

open Filter Topology Set Asymptotics

/-! ## Partial derivatives -/

/-- The first partial derivative `f_x` of `f : ℝ × ℝ → ℝ` at `p`: `fderiv` applied to `(1, 0)`. -/
noncomputable def partialX (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := fderiv ℝ f p (1, 0)

/-- The first partial derivative `f_y` of `f : ℝ × ℝ → ℝ` at `p`: `fderiv` applied to `(0, 1)`. -/
noncomputable def partialY (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := fderiv ℝ f p (0, 1)

/-- A linear map on `ℝ × ℝ` is determined by its values on `(1,0)` and `(0,1)`. -/
lemma clm_apply_prod (L : ℝ × ℝ →L[ℝ] ℝ) (v : ℝ × ℝ) :
    L v = v.1 * L (1, 0) + v.2 * L (0, 1) := by
  obtain ⟨x, y⟩ := v
  have : ((x, y) : ℝ × ℝ) = x • ((1, 0) : ℝ × ℝ) + y • ((0, 1) : ℝ × ℝ) := by ext <;> simp
  rw [this, map_add, map_smul, map_smul]
  simp

/-- The derivative of `f` at `p` applied to `v` is `f_x v₁ + f_y v₂`. -/
lemma fderiv_apply_eq (f : ℝ × ℝ → ℝ) (p v : ℝ × ℝ) :
    fderiv ℝ f p v = partialX f p * v.1 + partialY f p * v.2 := by
  rw [clm_apply_prod]; unfold partialX partialY; ring

/-- The partial derivative `f_x` is the ordinary derivative of the section `x ↦ f (x, b)`. -/
lemma hasDerivAt_section_x {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hf : DifferentiableAt ℝ f p) :
    HasDerivAt (fun x => f (x, p.2)) (partialX f p) p.1 := by
  have h1 : HasDerivAt (fun x : ℝ => (x, p.2)) ((1 : ℝ), (0 : ℝ)) p.1 :=
    (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  have h2 : HasFDerivAt f (fderiv ℝ f p) p := hf.hasFDerivAt
  have := h2.comp_hasDerivAt_of_eq p.1 h1 (by simp)
  exact this

/-- The partial derivative `f_y` is the ordinary derivative of the section `y ↦ f (a, y)`. -/
lemma hasDerivAt_section_y {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hf : DifferentiableAt ℝ f p) :
    HasDerivAt (fun y => f (p.1, y)) (partialY f p) p.2 := by
  have h1 : HasDerivAt (fun y : ℝ => (p.1, y)) ((0 : ℝ), (1 : ℝ)) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  have h2 : HasFDerivAt f (fderiv ℝ f p) p := hf.hasFDerivAt
  have := h2.comp_hasDerivAt_of_eq p.2 h1 (by simp)
  exact this

/-! ## Critical points and saddle points -/

/-- Book notion: `p` is a critical point of `f` if both first partial derivatives exist and vanish there, or
at least one of them does not exist. The partials are the derivatives of the two sections through `p`. -/
def IsCriticalPoint (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : Prop :=
  (HasDerivAt (fun x => f (x, p.2)) 0 p.1 ∧ HasDerivAt (fun y => f (p.1, y)) 0 p.2) ∨
  ¬ DifferentiableAt ℝ (fun x => f (x, p.2)) p.1 ∨ ¬ DifferentiableAt ℝ (fun y => f (p.1, y)) p.2

/-- Book notion: a saddle point is a critical point with both first partials equal to zero that is not a
local extremum. -/
def IsSaddlePoint (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : Prop :=
  (HasDerivAt (fun x => f (x, p.2)) 0 p.1 ∧ HasDerivAt (fun y => f (p.1, y)) 0 p.2) ∧ ¬ IsLocalExtr f p

/-- OpenStax Calculus 3:§4.7 (CA-543). For a differentiable function, `p` is a critical point (book
definition) exactly when both first partial derivatives vanish, i.e. `fderiv ℝ f p = 0`. -/
@[kb "openstaxcalculus2016" "3:§4.7 Definition (critical point), p. 395"]
theorem isCriticalPoint_iff {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hf : DifferentiableAt ℝ f p) :
    IsCriticalPoint f p ↔ partialX f p = 0 ∧ partialY f p = 0 := by
  have hx := hasDerivAt_section_x hf
  have hy := hasDerivAt_section_y hf
  constructor
  · rintro (⟨h1, h2⟩ | h | h)
    · exact ⟨hx.unique h1, hy.unique h2⟩
    · exact absurd hx.differentiableAt h
    · exact absurd hy.differentiableAt h
  · rintro ⟨h1, h2⟩
    left
    rw [h1] at hx; rw [h2] at hy
    exact ⟨hx, hy⟩

/-- OpenStax Calculus 3:§4.7 (CA-543). For a differentiable function, `p` is critical iff `fderiv ℝ f p = 0`. -/
@[kb "openstaxcalculus2016" "3:§4.7 Definition (critical point), p. 395"]
theorem isCriticalPoint_iff_fderiv_eq_zero {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hf : DifferentiableAt ℝ f p) :
    IsCriticalPoint f p ↔ fderiv ℝ f p = 0 := by
  rw [isCriticalPoint_iff hf]
  constructor
  · rintro ⟨h1, h2⟩
    refine ContinuousLinearMap.ext fun v => ?_
    rw [fderiv_apply_eq, h1, h2]; simp
  · intro h
    simp [partialX, partialY, h]

/-- OpenStax Calculus 3:§4.7 (CA-543, Fermat's theorem for two variables). A local extremum of a function
differentiable at `p` is a critical point. -/
@[kb "openstaxcalculus2016" "3:§4.7 Definition (critical point), p. 395"]
theorem isCriticalPoint_of_isLocalExtr {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (h : IsLocalExtr f p)
    (hf : DifferentiableAt ℝ f p) : IsCriticalPoint f p :=
  (isCriticalPoint_iff_fderiv_eq_zero hf).2 h.fderiv_eq_zero

/-- OpenStax Calculus 3:§4.7 (CA-546). For a differentiable function, `p` is a saddle point iff both
partials vanish there and `p` is not a local extremum. -/
@[kb "openstaxcalculus2016" "3:§4.7 Definition (saddle point), p. 398"]
theorem isSaddlePoint_iff {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hf : DifferentiableAt ℝ f p) :
    IsSaddlePoint f p ↔ partialX f p = 0 ∧ partialY f p = 0 ∧ ¬ IsLocalExtr f p := by
  have hx := hasDerivAt_section_x hf
  have hy := hasDerivAt_section_y hf
  unfold IsSaddlePoint
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨hx.unique h1, hy.unique h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    rw [h1] at hx; rw [h2] at hy
    exact ⟨⟨hx, hy⟩, h3⟩

/-! ## Tangent plane, linear approximation, total differential -/

/-- Book notion: the function `(x, y) ↦ f(a,b) + f_x(a,b)(x-a) + f_y(a,b)(y-b)` whose graph is the tangent
plane to `z = f(x,y)` at `(a,b)`. -/
noncomputable def tangentPlane (f : ℝ × ℝ → ℝ) (a b : ℝ) (x y : ℝ) : ℝ :=
  f (a, b) + partialX f (a, b) * (x - a) + partialY f (a, b) * (y - b)

/-- Book notion: the total differential `dz = f_x(p) dx + f_y(p) dy`. -/
noncomputable def totalDifferential (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) (dx dy : ℝ) : ℝ :=
  partialX f p * dx + partialY f p * dy

/-- OpenStax Calculus 3:§4.4 (CA-529). Linear approximation: for `f` differentiable at `p`, the error
`f q - (f(a,b) + f_x(a,b)(x-a) + f_y(a,b)(y-b))` is `o(‖q - p‖)`. -/
@[kb "openstaxcalculus2016" "3:§4.4 Definition (linear approximation), p. 359"]
theorem linear_approximation {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hf : DifferentiableAt ℝ f p) :
    (fun q : ℝ × ℝ => f q - tangentPlane f p.1 p.2 q.1 q.2) =o[𝓝 p] fun q => q - p := by
  have h := (hasFDerivAt_iff_isLittleO.1 hf.hasFDerivAt)
  refine h.congr_left fun q => ?_
  rw [fderiv_apply_eq]
  simp only [tangentPlane, Prod.fst_sub, Prod.snd_sub]
  ring_nf

/-- OpenStax Calculus 3:§4.4 (CA-533). The total differential approximates the increment: with
`d = (dx, dy)`, `f(p + d) - f(p) - dz = o(‖d‖)` as `d → 0`. -/
@[kb "openstaxcalculus2016" "3:§4.4 Definition (differentials, total differential), p. 364"]
theorem total_differential_approx {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hf : DifferentiableAt ℝ f p) :
    (fun d : ℝ × ℝ => f (p + d) - f p - totalDifferential f p d.1 d.2) =o[𝓝 0] fun d => d := by
  have h := (hasFDerivAt_iff_isLittleO_nhds_zero.1 hf.hasFDerivAt)
  refine h.congr_left fun d => ?_
  rw [fderiv_apply_eq]
  simp only [totalDifferential]

/-- OpenStax Calculus 3:§4.4 (CA-528). The tangent plane `z = f(a,b) + f_x(a,b)(x-a) + f_y(a,b)(y-b)` is the
only plane `z = z₀ + α(x-a) + β(y-b)` approximating `f` to first order at `(a,b)`: if the error is
`o(‖q - p‖)` then the coefficients are `f(a,b)`, `f_x(a,b)`, `f_y(a,b)`. -/
@[kb "openstaxcalculus2016" "3:§4.4 Definition (equation of the tangent plane), p. 356"]
theorem tangent_plane_unique {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hf : DifferentiableAt ℝ f p)
    {z₀ α β : ℝ}
    (h : (fun q : ℝ × ℝ => f q - (z₀ + α * (q.1 - p.1) + β * (q.2 - p.2))) =o[𝓝 p] fun q => q - p) :
    z₀ = f p ∧ α = partialX f p ∧ β = partialY f p := by
  have hz : z₀ = f p := by
    have h1 : Tendsto (fun q : ℝ × ℝ => f q - (z₀ + α * (q.1 - p.1) + β * (q.2 - p.2))) (𝓝 p) (𝓝 0) := by
      refine h.isBigO.trans_tendsto ?_
      have : Tendsto (fun q : ℝ × ℝ => q - p) (𝓝 p) (𝓝 (p - p)) :=
        (continuous_id.sub continuous_const).tendsto p
      simpa using this
    have h2 : Tendsto (fun q : ℝ × ℝ => f q - (z₀ + α * (q.1 - p.1) + β * (q.2 - p.2))) (𝓝 p)
        (𝓝 (f p - (z₀ + α * (p.1 - p.1) + β * (p.2 - p.2)))) := by
      have hc : ContinuousAt f p := hf.continuousAt
      have : Continuous fun q : ℝ × ℝ => (z₀ + α * (q.1 - p.1) + β * (q.2 - p.2)) := by fun_prop
      exact hc.tendsto.sub this.continuousAt.tendsto
    have := tendsto_nhds_unique h2 h1
    simp at this
    linarith
  subst hz
  set L : ℝ × ℝ →L[ℝ] ℝ := α • ContinuousLinearMap.fst ℝ ℝ ℝ + β • ContinuousLinearMap.snd ℝ ℝ ℝ with hL
  have hd : HasFDerivAt f L p := by
    rw [hasFDerivAt_iff_isLittleO]
    refine h.congr_left fun q => ?_
    simp [hL]
    ring
  have hu := hd.unique hf.hasFDerivAt
  refine ⟨rfl, ?_, ?_⟩
  · have := congrArg (fun M : ℝ × ℝ →L[ℝ] ℝ => M (1, 0)) hu
    simpa [hL, partialX] using this
  · have := congrArg (fun M : ℝ × ℝ →L[ℝ] ℝ => M (0, 1)) hu
    simpa [hL, partialY] using this

/-- OpenStax Calculus 3:§4.4 (CA-527). Tangent lines of curves on the surface lie in the tangent plane: for a
curve `t ↦ (x t, y t, f (x t, y t))` through the point over `(a,b) = (x t₀, y t₀)`, the velocity at `t₀` is
`(x', y', f_x x' + f_y y')`, and every point of the tangent line lies on the plane `z = tangentPlane`. -/
@[kb "openstaxcalculus2016" "3:§4.4 Definition (tangent plane), p. 355"]
theorem curve_tangent_in_tangent_plane {f : ℝ × ℝ → ℝ} {x y : ℝ → ℝ} {x' y' t₀ : ℝ}
    (hx : HasDerivAt x x' t₀) (hy : HasDerivAt y y' t₀)
    (hf : DifferentiableAt ℝ f (x t₀, y t₀)) :
    HasDerivAt (fun t => f (x t, y t))
        (partialX f (x t₀, y t₀) * x' + partialY f (x t₀, y t₀) * y') t₀ ∧
    ∀ s : ℝ, f (x t₀, y t₀) + s * (partialX f (x t₀, y t₀) * x' + partialY f (x t₀, y t₀) * y') =
      tangentPlane f (x t₀) (y t₀) (x t₀ + s * x') (y t₀ + s * y') := by
  refine ⟨?_, fun s => ?_⟩
  · have h1 : HasDerivAt (fun t => (x t, y t)) (x', y') t₀ := hx.prodMk hy
    have h2 : HasFDerivAt f (fderiv ℝ f (x t₀, y t₀)) (x t₀, y t₀) := hf.hasFDerivAt
    have := h2.comp_hasDerivAt t₀ h1
    have e : fderiv ℝ f (x t₀, y t₀) (x', y') =
        partialX f (x t₀, y t₀) * x' + partialY f (x t₀, y t₀) * y' := fderiv_apply_eq _ _ _
    rw [e] at this
    exact this
  · simp only [tangentPlane]
    ring

/-! ## Directional derivatives and the gradient -/

/-- Book notion: the directional derivative `D_u f(p) = f_x(p) u₁ + f_y(p) u₂` in the direction `u`. -/
noncomputable def directionalDeriv (f : ℝ × ℝ → ℝ) (p u : ℝ × ℝ) : ℝ :=
  partialX f p * u.1 + partialY f p * u.2

/-- The length of the gradient `‖∇f(p)‖ = √(f_x² + f_y²)`. -/
noncomputable def gradNorm (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.sqrt (partialX f p ^ 2 + partialY f p ^ 2)

/-- The directional derivative is the derivative at `0` of `t ↦ f(p + t u)`. -/
theorem hasDerivAt_directionalDeriv {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hf : DifferentiableAt ℝ f p)
    (u : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => f (p.1 + t * u.1, p.2 + t * u.2)) (directionalDeriv f p u) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => (p.1 + t * u.1, p.2 + t * u.2)) (u.1, u.2) 0 := by
    have a : HasDerivAt (fun t : ℝ => p.1 + t * u.1) u.1 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).mul_const u.1).const_add p.1
    have b : HasDerivAt (fun t : ℝ => p.2 + t * u.2) u.2 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).mul_const u.2).const_add p.2
    exact a.prodMk b
  have h2 : HasFDerivAt f (fderiv ℝ f p) p := hf.hasFDerivAt
  have := h2.comp_hasDerivAt_of_eq (0:ℝ) h1 (by simp)
  have e : fderiv ℝ f p (u.1, u.2) = directionalDeriv f p u := fderiv_apply_eq _ _ _
  rw [e] at this
  exact this

/-- OpenStax Calculus 3:Theorem 4.13 (CA-541), bounds. For a unit vector `u`, the directional derivative lies
between `-‖∇f‖` and `‖∇f‖`; in particular it is zero in every direction if the gradient is zero. -/
@[kb "openstaxcalculus2016" "3:Theorem 4.13, p. 386"]
theorem directionalDeriv_abs_le (f : ℝ × ℝ → ℝ) (p u : ℝ × ℝ) (hu : u.1 ^ 2 + u.2 ^ 2 = 1) :
    |directionalDeriv f p u| ≤ gradNorm f p := by
  unfold directionalDeriv gradNorm
  apply Real.abs_le_sqrt
  nlinarith [sq_nonneg (partialX f p * u.2 - partialY f p * u.1)]

/-- OpenStax Calculus 3:Theorem 4.13 (CA-541), zero gradient. -/
@[kb "openstaxcalculus2016" "3:Theorem 4.13, p. 386"]
theorem directionalDeriv_eq_zero_of_grad_zero (f : ℝ × ℝ → ℝ) (p u : ℝ × ℝ)
    (hx : partialX f p = 0) (hy : partialY f p = 0) : directionalDeriv f p u = 0 := by
  simp [directionalDeriv, hx, hy]

/-- OpenStax Calculus 3:Theorem 4.13 (CA-541), maximum. If the gradient is nonzero, in the unit direction
`∇f/‖∇f‖` the directional derivative equals `‖∇f‖` (the largest possible value, by `directionalDeriv_abs_le`),
and this direction is the only unit direction attaining it. -/
@[kb "openstaxcalculus2016" "3:Theorem 4.13, p. 386"]
theorem directionalDeriv_max_iff (f : ℝ × ℝ → ℝ) (p u : ℝ × ℝ) (hu : u.1 ^ 2 + u.2 ^ 2 = 1)
    (hN : gradNorm f p ≠ 0) :
    directionalDeriv f p u = gradNorm f p ↔
      u = (partialX f p / gradNorm f p, partialY f p / gradNorm f p) := by
  have hNpos : 0 < gradNorm f p := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hN)
  have hsq : gradNorm f p ^ 2 = partialX f p ^ 2 + partialY f p ^ 2 := by
    unfold gradNorm
    rw [Real.sq_sqrt]; positivity
  set N := gradNorm f p
  set a := partialX f p
  set b := partialY f p
  constructor
  · intro h
    unfold directionalDeriv at h
    have h0 : (u.1 - a / N) ^ 2 + (u.2 - b / N) ^ 2 = 0 := by
      have : (u.1 - a / N) ^ 2 + (u.2 - b / N) ^ 2 =
          (u.1 ^ 2 + u.2 ^ 2) - 2 * (a * u.1 + b * u.2) / N + (a ^ 2 + b ^ 2) / N ^ 2 := by
        field_simp
        ring
      rw [this, hu, h, ← hsq]
      field_simp
      ring
    have h1 : u.1 - a / N = 0 := by nlinarith [sq_nonneg (u.1 - a / N), sq_nonneg (u.2 - b / N)]
    have h2 : u.2 - b / N = 0 := by nlinarith [sq_nonneg (u.1 - a / N), sq_nonneg (u.2 - b / N)]
    ext <;> simp <;> linarith
  · intro h
    subst h
    show a * (a / N) + b * (b / N) = N
    have : a * (a / N) + b * (b / N) = (a ^ 2 + b ^ 2) / N := by ring
    rw [this, ← hsq]
    field_simp

/-- OpenStax Calculus 3:Theorem 4.13 (CA-541), minimum. In the direction `-∇f/‖∇f‖` the directional
derivative equals `-‖∇f‖`, and in the perpendicular direction `(-f_y, f_x)/‖∇f‖` it is zero. -/
@[kb "openstaxcalculus2016" "3:Theorem 4.13, p. 386"]
theorem directionalDeriv_min_and_perp (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) (hN : gradNorm f p ≠ 0) :
    directionalDeriv f p (-(partialX f p / gradNorm f p), -(partialY f p / gradNorm f p)) =
        -gradNorm f p ∧
    directionalDeriv f p (-(partialY f p / gradNorm f p), partialX f p / gradNorm f p) = 0 := by
  have hsq : gradNorm f p ^ 2 = partialX f p ^ 2 + partialY f p ^ 2 := by
    unfold gradNorm
    rw [Real.sq_sqrt]; positivity
  unfold directionalDeriv
  simp only
  constructor
  · field_simp
    linarith [hsq]
  · field_simp
    ring

/-- OpenStax Calculus 3:Theorem 4.14 (CA-542). If `f` is differentiable at the point `(x t₀, y t₀)` of a
curve `t ↦ (x t, y t)` that lies in a level set `f = c` near `t₀`, then `∇f · (x', y') = 0`: the gradient is
perpendicular to the tangent of the level curve. -/
@[kb "openstaxcalculus2016" "3:Theorem 4.14, p. 389"]
theorem gradient_orthogonal_level_curve {f : ℝ × ℝ → ℝ} {x y : ℝ → ℝ} {x' y' t₀ c : ℝ}
    (hx : HasDerivAt x x' t₀) (hy : HasDerivAt y y' t₀)
    (hf : DifferentiableAt ℝ f (x t₀, y t₀)) (hlevel : ∀ᶠ t in 𝓝 t₀, f (x t, y t) = c) :
    partialX f (x t₀, y t₀) * x' + partialY f (x t₀, y t₀) * y' = 0 := by
  have h1 := (curve_tangent_in_tangent_plane hx hy hf).1
  have h2 : HasDerivAt (fun t => f (x t, y t)) 0 t₀ :=
    (hasDerivAt_const t₀ c).congr_of_eventuallyEq (hlevel.mono fun t ht => ht)
  exact h1.unique h2

/-! ## Two-path test -/

/-- OpenStax Calculus 3:§4.2 (CA-513). If two paths approach `p` (without reaching it) and `f` tends to
different values along them, then `f` has no limit at `p`. -/
@[kb "openstaxcalculus2016" "3:§4.2 Principle (limit fails if path-dependent), p. 328"]
theorem not_limit_of_two_paths {ι κ : Type*} {l₁ : Filter ι} {l₂ : Filter κ} [NeBot l₁] [NeBot l₂]
    {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} {γ₁ : ι → ℝ × ℝ} {γ₂ : κ → ℝ × ℝ} {L₁ L₂ : ℝ}
    (hγ₁ : Tendsto γ₁ l₁ (𝓝[≠] p)) (hγ₂ : Tendsto γ₂ l₂ (𝓝[≠] p))
    (h₁ : Tendsto (f ∘ γ₁) l₁ (𝓝 L₁)) (h₂ : Tendsto (f ∘ γ₂) l₂ (𝓝 L₂)) (hne : L₁ ≠ L₂) :
    ¬ ∃ L, Tendsto f (𝓝[≠] p) (𝓝 L) := by
  rintro ⟨L, hL⟩
  exact hne ((tendsto_nhds_unique (hL.comp hγ₁) h₁).symm.trans (tendsto_nhds_unique (hL.comp hγ₂) h₂))

/-- OpenStax Calculus 3:Example 4.9 (CA-513). `f(x,y) = x y / (x² + y²)` has no limit at the origin:
the limit along the `x`-axis is `0` and along the line `y = x` it is `1/2`. -/
@[kb "openstaxcalculus2016" "3:Example 4.9, p. 328"]
theorem no_limit_xy_over_sq_sum :
    ¬ ∃ L, Tendsto (fun q : ℝ × ℝ => q.1 * q.2 / (q.1 ^ 2 + q.2 ^ 2)) (𝓝[≠] (0, 0)) (𝓝 L) := by
  have path : ∀ v : ℝ × ℝ, v ≠ 0 → Tendsto (fun t : ℝ => (t * v.1, t * v.2)) (𝓝[≠] 0)
      (𝓝[≠] ((0 : ℝ), (0 : ℝ))) := by
    intro v hv
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : ContinuousAt (fun t : ℝ => (t * v.1, t * v.2)) 0 := by fun_prop
      simpa using this.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      intro h
      apply hv
      have h1 : t * v.1 = 0 := congrArg Prod.fst h
      have h2 : t * v.2 = 0 := congrArg Prod.snd h
      have ht' : t ≠ 0 := ht
      ext
      · simpa [ht'] using h1
      · simpa [ht'] using h2
  refine not_limit_of_two_paths (l₁ := 𝓝[≠] (0:ℝ)) (l₂ := 𝓝[≠] (0:ℝ)) (L₁ := 0) (L₂ := 1 / 2)
    (path (1, 0) (by simp [Prod.ext_iff])) (path (1, 1) (by simp [Prod.ext_iff])) ?_ ?_ (by norm_num)
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards with t
    simp
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t ≠ 0 := ht
    simp only [Function.comp, mul_one]
    field_simp
    ring

/-! ## Lagrange multipliers -/

/-- OpenStax Calculus 3:Theorem 4.20 (CA-551), any number of variables. If `f` has a local extremum on the
level set `{g = c}` at `p`, `f` and `g` are `C¹` at `p` and the gradient (derivative) of `g` at `p` is nonzero,
then `∇f(p) = λ ∇g(p)` for some `λ`. -/
@[kb "openstaxcalculus2016" "3:Theorem 4.20, p. 412"]
theorem lagrange_multiplier {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f g : E → ℝ} {p : E} {c : ℝ} (hf : ContDiffAt ℝ 1 f p) (hg : ContDiffAt ℝ 1 g p)
    (hc : g p = c) (hext : IsLocalExtrOn f {q | g q = c} p) (hgrad : fderiv ℝ g p ≠ 0) :
    ∃ l : ℝ, fderiv ℝ f p = l • fderiv ℝ g p := by
  subst hc
  obtain ⟨a, b, hab, h⟩ := hext.exists_multipliers_of_hasStrictFDerivAt_1d
    (hg.hasStrictFDerivAt_fderiv one_ne_zero) (hf.hasStrictFDerivAt_fderiv one_ne_zero)
  have hb : b ≠ 0 := by
    rintro rfl
    have ha : a ≠ 0 := by
      rintro rfl
      exact hab rfl
    simp at h
    rcases h with h | h
    · exact ha h
    · exact hgrad h
  refine ⟨-a / b, ?_⟩
  have : b • fderiv ℝ f p = -(a • fderiv ℝ g p) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact h
  have h2 : fderiv ℝ f p = b⁻¹ • (-(a • fderiv ℝ g p)) := by
    rw [← this, smul_smul, inv_mul_cancel₀ hb, one_smul]
  rw [h2, smul_neg, smul_smul, ← neg_smul]
  congr 1
  field_simp

/-- OpenStax Calculus 3:Theorem 4.20 (CA-551), book form in two variables: at a constrained local extremum
of `f` on `g(x,y) = c` where `∇g ≠ 0`, there is `λ` with `f_x = λ g_x` and `f_y = λ g_y`. -/
@[kb "openstaxcalculus2016" "3:Theorem 4.20, p. 412"]
theorem lagrange_multiplier_two_vars {f g : ℝ × ℝ → ℝ} {p : ℝ × ℝ} {c : ℝ}
    (hf : ContDiffAt ℝ 1 f p) (hg : ContDiffAt ℝ 1 g p) (hc : g p = c)
    (hext : IsLocalExtrOn f {q | g q = c} p) (hgrad : partialX g p ≠ 0 ∨ partialY g p ≠ 0) :
    ∃ l : ℝ, partialX f p = l * partialX g p ∧ partialY f p = l * partialY g p := by
  have hne : fderiv ℝ g p ≠ 0 := by
    intro h
    rcases hgrad with h1 | h1
    · exact h1 (by simp [partialX, h])
    · exact h1 (by simp [partialY, h])
  obtain ⟨l, hl⟩ := lagrange_multiplier hf hg hc hext hne
  refine ⟨l, ?_, ?_⟩
  · simp [partialX, hl]
  · simp [partialY, hl]

/-- Lagrange multipliers with two constraints in any number of variables: if `f` has a local extremum on
`{g = c ∧ h = d}` at `p` and the derivatives of `g`, `h` at `p` are linearly independent then
`∇f = λ ∇g + μ ∇h`. -/
theorem lagrange_multiplier_two_constraints {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f g h : E → ℝ} {p : E} (hf : ContDiffAt ℝ 1 f p) (hg : ContDiffAt ℝ 1 g p)
    (hh : ContDiffAt ℝ 1 h p) (hext : IsLocalExtrOn f {q | g q = g p ∧ h q = h p} p)
    (hind : LinearIndependent ℝ ![fderiv ℝ g p, fderiv ℝ h p]) :
    ∃ l m : ℝ, fderiv ℝ f p = l • fderiv ℝ g p + m • fderiv ℝ h p := by
  have hext' : IsLocalExtrOn f {q | ∀ i, ![g, h] i q = ![g, h] i p} p := by
    convert hext using 2
    ext q
    simp [Fin.forall_fin_two]
  obtain ⟨Λ, Λ₀, hne, hsum⟩ := hext'.exists_multipliers_of_hasStrictFDerivAt
    (f' := ![fderiv ℝ g p, fderiv ℝ h p])
    (fun i => by fin_cases i
                 · exact hg.hasStrictFDerivAt_fderiv one_ne_zero
                 · exact hh.hasStrictFDerivAt_fderiv one_ne_zero)
    (hf.hasStrictFDerivAt_fderiv one_ne_zero)
  have hΛ₀ : Λ₀ ≠ 0 := by
    intro h0
    rw [h0] at hsum
    simp only [zero_smul, add_zero, Fin.sum_univ_two] at hsum
    have := Fintype.linearIndependent_iff.1 hind Λ (by simpa using hsum)
    exact hne (Prod.ext (funext this) (by simpa using h0))
  refine ⟨-Λ 0 / Λ₀, -Λ 1 / Λ₀, ?_⟩
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hsum
  have : Λ₀ • fderiv ℝ f p = -(Λ 0 • fderiv ℝ g p + Λ 1 • fderiv ℝ h p) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact hsum
  have h2 : fderiv ℝ f p = Λ₀⁻¹ • (-(Λ 0 • fderiv ℝ g p + Λ 1 • fderiv ℝ h p)) := by
    rw [← this, smul_smul, inv_mul_cancel₀ hΛ₀, one_smul]
  rw [h2, smul_neg, smul_add, smul_smul, smul_smul, neg_add, ← neg_smul, ← neg_smul]
  congr 2 <;> field_simp

/-- OpenStax Calculus 3:§4.8 (CA-552), book form. A constrained local extremum of `f` on `g = c`, `h = d`
(with `∇g`, `∇h` not parallel, i.e. `g_x h_y - g_y h_x ≠ 0`) satisfies `∇f = λ ∇g + μ ∇h`. -/
@[kb "openstaxcalculus2016" "3:§4.8 Method (Lagrange multipliers, two constraints), p. 416"]
theorem lagrange_multiplier_two_constraints_two_vars {f g h : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : ContDiffAt ℝ 1 f p) (hg : ContDiffAt ℝ 1 g p) (hh : ContDiffAt ℝ 1 h p)
    (hext : IsLocalExtrOn f {q | g q = g p ∧ h q = h p} p)
    (hdet : partialX g p * partialY h p - partialY g p * partialX h p ≠ 0) :
    ∃ l m : ℝ, partialX f p = l * partialX g p + m * partialX h p ∧
      partialY f p = l * partialY g p + m * partialY h p := by
  have hind : LinearIndependent ℝ ![fderiv ℝ g p, fderiv ℝ h p] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hc
    have e1 := congrArg (fun M : ℝ × ℝ →L[ℝ] ℝ => M (1, 0)) hc
    have e2 := congrArg (fun M : ℝ × ℝ →L[ℝ] ℝ => M (0, 1)) hc
    simp only [add_apply, smul_apply, smul_eq_mul, zero_apply] at e1 e2
    change c 0 * partialX g p + c 1 * partialX h p = 0 at e1
    change c 0 * partialY g p + c 1 * partialY h p = 0 at e2
    have h0 : c 0 * (partialX g p * partialY h p - partialY g p * partialX h p) = 0 := by
      linear_combination partialY h p * e1 - partialX h p * e2
    have h1 : c 1 * (partialX g p * partialY h p - partialY g p * partialX h p) = 0 := by
      linear_combination partialX g p * e2 - partialY g p * e1
    intro i
    fin_cases i
    · exact (mul_eq_zero.1 h0).resolve_right hdet
    · exact (mul_eq_zero.1 h1).resolve_right hdet
  obtain ⟨l, m, hlm⟩ := lagrange_multiplier_two_constraints hf hg hh hext hind
  refine ⟨l, m, ?_, ?_⟩
  · simp [partialX, hlm]
  · simp [partialY, hlm]

/-! ## Second derivatives along lines (any normed space) -/

section Lines

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma contDiffAt_two_aux {f : E → ℝ} {p : E} (hf : ContDiffAt ℝ 2 f p) :
    (∀ᶠ q in 𝓝 p, DifferentiableAt ℝ f q) ∧ DifferentiableAt ℝ (fderiv ℝ f) p := by
  refine ⟨?_, ?_⟩
  · filter_upwards [hf.eventually (by simp)] with q hq
    exact hq.differentiableAt (by norm_num)
  · have := hf.fderiv_right (m := 1) (by norm_num)
    exact this.differentiableAt (by norm_num)

/-- Second derivative of a section along a line. -/
lemma deriv_deriv_line {f : E → ℝ} {p : E} (u : E) (hf : ContDiffAt ℝ 2 f p) :
    deriv (deriv (fun t : ℝ => f (p + t • u))) 0 = fderiv ℝ (fderiv ℝ f) p u u := by
  obtain ⟨h1, h2⟩ := contDiffAt_two_aux hf
  have hline : HasDerivAt (fun t : ℝ => p + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const u).const_add p
  have hline' : Tendsto (fun t : ℝ => p + t • u) (𝓝 0) (𝓝 p) := by
    have : ContinuousAt (fun t : ℝ => p + t • u) 0 := hline.continuousAt
    simpa using this.tendsto
  have hev : deriv (fun t : ℝ => f (p + t • u)) =ᶠ[𝓝 0] fun t => fderiv ℝ f (p + t • u) u := by
    have : ∀ᶠ t in 𝓝 (0:ℝ), DifferentiableAt ℝ f (p + t • u) := hline'.eventually h1
    have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => p + t • u) u t := fun t => by
      simpa using ((hasDerivAt_id t).smul_const u).const_add p
    filter_upwards [this] with t ht
    exact (ht.hasFDerivAt.comp_hasDerivAt t (hd t)).deriv
  rw [hev.deriv_eq]
  have h3 : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) p) p := h2.hasFDerivAt
  have h4 : HasDerivAt (fun t : ℝ => fderiv ℝ f (p + t • u)) (fderiv ℝ (fderiv ℝ f) p u) 0 := by
    have := h3.comp_hasDerivAt_of_eq (0:ℝ) hline (by simp)
    exact this
  have h5 := h4.clm_apply (hasDerivAt_const (0:ℝ) u)
  simpa using h5.deriv

lemma deriv_line_zero {f : E → ℝ} {p : E} (u : E) (hf : ContDiffAt ℝ 2 f p) :
    deriv (fun t : ℝ => f (p + t • u)) 0 = fderiv ℝ f p u := by
  have hd : HasDerivAt (fun t : ℝ => p + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const u).const_add p
  have h1 := (contDiffAt_two_aux hf).1.self_of_nhds
  have := (h1.hasFDerivAt.comp_hasDerivAt_of_eq (0:ℝ) hd (by simp))
  have h3 := this.deriv
  simp only [Function.comp_def] at h3 ⊢
  simpa using h3

lemma line_cont {f : E → ℝ} {p : E} (u : E) (hf : ContDiffAt ℝ 2 f p) :
    ContinuousAt (fun t : ℝ => f (p + t • u)) 0 := by
  have h1 : ContinuousAt f (p + (0:ℝ) • u) := by
    simpa using hf.continuousAt
  exact h1.comp (f := fun t : ℝ => p + t • u) (by fun_prop)

lemma line_tendsto (p u : E) : Tendsto (fun t : ℝ => p + t • u) (𝓝 0) (𝓝 p) := by
  have : ContinuousAt (fun t : ℝ => p + t • u) 0 := by fun_prop
  simpa using this.tendsto

/-- A positive second derivative in some direction rules out a local maximum at a critical point. -/
lemma not_isLocalMax_of_hessian_pos {f : E → ℝ} {p : E} (hf : ContDiffAt ℝ 2 f p)
    (hp : fderiv ℝ f p = 0) {u : E} (hu : 0 < fderiv ℝ (fderiv ℝ f) p u u) :
    ¬ IsLocalMax f p := by
  intro hmax
  have h0 : deriv (fun t : ℝ => f (p + t • u)) 0 = 0 := by
    rw [deriv_line_zero u hf, hp]; rfl
  have hmin : IsLocalMin (fun t : ℝ => f (p + t • u)) 0 :=
    isLocalMin_of_deriv_deriv_pos (by rw [deriv_deriv_line u hf]; exact hu) h0 (line_cont u hf)
  have hmax' : IsLocalMax (fun t : ℝ => f (p + t • u)) 0 := by
    have := (line_tendsto p u).eventually hmax
    filter_upwards [this] with t ht
    simpa using ht
  have heq : (fun t : ℝ => f (p + t • u)) =ᶠ[𝓝 0] fun _ => f p := by
    filter_upwards [hmin, hmax'] with t h1 h2
    have := le_antisymm h2 h1
    simpa using this
  have h2 : deriv (fun t : ℝ => f (p + t • u)) =ᶠ[𝓝 0] fun _ => (0:ℝ) := by
    filter_upwards [heq.eventuallyEq_nhds] with t ht
    rw [ht.deriv_eq]; simp
  have := h2.deriv_eq
  rw [deriv_deriv_line u hf] at *
  simp at this
  linarith

/-- A negative second derivative in some direction rules out a local minimum at a critical point. -/
lemma not_isLocalMin_of_hessian_neg {f : E → ℝ} {p : E} (hf : ContDiffAt ℝ 2 f p)
    (hp : fderiv ℝ f p = 0) {u : E} (hu : fderiv ℝ (fderiv ℝ f) p u u < 0) :
    ¬ IsLocalMin f p := by
  intro hmin
  have h0 : deriv (fun t : ℝ => f (p + t • u)) 0 = 0 := by
    rw [deriv_line_zero u hf, hp]; rfl
  have hmax : IsLocalMax (fun t : ℝ => f (p + t • u)) 0 :=
    isLocalMax_of_deriv_deriv_neg (by rw [deriv_deriv_line u hf]; exact hu) h0 (line_cont u hf)
  have hmin' : IsLocalMin (fun t : ℝ => f (p + t • u)) 0 := by
    have := (line_tendsto p u).eventually hmin
    filter_upwards [this] with t ht
    simpa using ht
  have heq : (fun t : ℝ => f (p + t • u)) =ᶠ[𝓝 0] fun _ => f p := by
    filter_upwards [hmin', hmax] with t h1 h2
    have := le_antisymm h2 h1
    simpa using this
  have h2 : deriv (fun t : ℝ => f (p + t • u)) =ᶠ[𝓝 0] fun _ => (0:ℝ) := by
    filter_upwards [heq.eventuallyEq_nhds] with t ht
    rw [ht.deriv_eq]; simp
  have := h2.deriv_eq
  rw [deriv_deriv_line u hf] at *
  simp at this
  linarith

lemma hasDerivAt_line {f : E → ℝ} {p q : E} (h : E) {t : ℝ} (hq : q = p + t • h)
    (hf : DifferentiableAt ℝ f q) :
    HasDerivAt (fun s : ℝ => f (p + s • h)) (fderiv ℝ f q h) t := by
  have hd : HasDerivAt (fun s : ℝ => p + s • h) h t := by
    simpa using ((hasDerivAt_id t).smul_const h).const_add p
  subst hq
  exact hf.hasFDerivAt.comp_hasDerivAt t hd

lemma hasDerivAt_line_fderiv {f : E → ℝ} {p q : E} (h : E) {t : ℝ} (hq : q = p + t • h)
    (hf : DifferentiableAt ℝ (fderiv ℝ f) q) :
    HasDerivAt (fun s : ℝ => fderiv ℝ f (p + s • h) h) (fderiv ℝ (fderiv ℝ f) q h h) t := by
  have hd : HasDerivAt (fun s : ℝ => p + s • h) h t := by
    simpa using ((hasDerivAt_id t).smul_const h).const_add p
  subst hq
  have h4 : HasDerivAt (fun s : ℝ => fderiv ℝ f (p + s • h))
      (fderiv ℝ (fderiv ℝ f) (p + t • h) h) t :=
    hf.hasFDerivAt.comp_hasDerivAt t hd
  have h5 := h4.clm_apply (hasDerivAt_const t h)
  simpa using h5

/-- A nonnegative Hessian on a neighbourhood of a critical point gives a local minimum. -/
lemma isLocalMin_of_hessian_nonneg {f : E → ℝ} {p : E} (hf : ContDiffAt ℝ 2 f p)
    (hp : fderiv ℝ f p = 0)
    (hH : ∀ᶠ q in 𝓝 p, ∀ h, 0 ≤ fderiv ℝ (fderiv ℝ f) q h h) : IsLocalMin f p := by
  have hS : ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ f q ∧ DifferentiableAt ℝ (fderiv ℝ f) q ∧
      ∀ h, 0 ≤ fderiv ℝ (fderiv ℝ f) q h h := by
    filter_upwards [hf.eventually (by simp), hH] with q hq hq2
    exact ⟨hq.differentiableAt (by norm_num), (contDiffAt_two_aux hq).2, hq2⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hS
  have hmem : ∀ (h : E) (t : ℝ), t ∈ Icc (0:ℝ) 1 → p + h ∈ Metric.ball p ε →
      p + t • h ∈ Metric.ball p ε := by
    intro h t ht hh
    rw [Metric.mem_ball, dist_eq_norm] at hh ⊢
    simp only [add_sub_cancel_left] at hh ⊢
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    calc t * ‖h‖ ≤ 1 * ‖h‖ := by gcongr; exact ht.2
      _ < ε := by simpa using hh
  show ∀ᶠ x in 𝓝 p, f p ≤ f x
  filter_upwards [Metric.ball_mem_nhds p hε] with x hx
  set h := x - p with hh
  have hxh : p + h = x := by simp [hh]
  have hx' : p + h ∈ Metric.ball p ε := by rw [hxh]; exact hx
  set φ : ℝ → ℝ := fun s => fderiv ℝ f (p + s • h) h with hφ
  set g : ℝ → ℝ := fun s => f (p + s • h) with hg
  have hφ' : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt φ (fderiv ℝ (fderiv ℝ f) (p + t • h) h h) t := by
    intro t ht
    exact hasDerivAt_line_fderiv h rfl (hball _ (hmem h t ht hx')).2.1
  have hg' : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt g (φ t) t := by
    intro t ht
    exact hasDerivAt_line h rfl (hball _ (hmem h t ht hx')).1
  have hφ0 : φ 0 = 0 := by simp [hφ, hp]
  have hφmono : MonotoneOn φ (Icc (0:ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · exact fun t ht => (hφ' t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hφ' t (Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hφ' t (Ioo_subset_Icc_self ht)).deriv]
      exact (hball _ (hmem h t (Ioo_subset_Icc_self ht) hx')).2.2 h
  have hφnn : ∀ t ∈ Icc (0:ℝ) 1, 0 ≤ φ t := by
    intro t ht
    have := hφmono (left_mem_Icc.2 zero_le_one) ht ht.1
    linarith
  have hgmono : MonotoneOn g (Icc (0:ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · exact fun t ht => (hg' t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hg' t (Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hg' t (Ioo_subset_Icc_self ht)).deriv]
      exact hφnn t (Ioo_subset_Icc_self ht)
  have := hgmono (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one) zero_le_one
  simpa [hg, hxh] using this

/-- A nonpositive Hessian near a critical point gives a local maximum. -/
lemma isLocalMax_of_hessian_nonpos {f : E → ℝ} {p : E} (hf : ContDiffAt ℝ 2 f p)
    (hp : fderiv ℝ f p = 0)
    (hH : ∀ᶠ q in 𝓝 p, ∀ h, fderiv ℝ (fderiv ℝ f) q h h ≤ 0) : IsLocalMax f p := by
  have e1 : fderiv ℝ (fun x => -f x) = fun x => -fderiv ℝ f x := by
    funext x; exact fderiv_fun_neg
  have e2 : fderiv ℝ (fderiv ℝ (fun x => -f x)) = fun x => -fderiv ℝ (fderiv ℝ f) x := by
    rw [e1]; funext x; exact fderiv_fun_neg
  have := isLocalMin_of_hessian_nonneg (f := fun x => -f x) hf.neg (by rw [e1]; simp [hp])
    (by
      rw [e2]
      filter_upwards [hH] with q hq h
      simpa using hq h)
  simpa using this.neg

end Lines

/-! ## Second derivative test -/

/-- Book notion: the second partial derivative `f_xx = (f_x)_x`. -/
noncomputable def partialXX (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := partialX (partialX f) p

/-- Book notion: the second partial derivative `f_yy = (f_y)_y`. -/
noncomputable def partialYY (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := partialY (partialY f) p

/-- Book notion: the mixed second partial derivative `f_xy = (f_x)_y`. -/
noncomputable def partialXY (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := partialY (partialX f) p

/-- Book notion: the discriminant `D = f_xx f_yy - (f_xy)²` of the second derivative test. -/
noncomputable def hessianDet (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  partialXX f p * partialYY f p - partialXY f p ^ 2

lemma fderiv_eq_zero_of_partials {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hx : partialX f p = 0)
    (hy : partialY f p = 0) : fderiv ℝ f p = 0 := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [fderiv_apply_eq, hx, hy]; simp

/-- Expansion of a bilinear form `L v v` on `ℝ × ℝ` in the standard basis. -/
lemma bilin_expand (L : ℝ × ℝ →L[ℝ] ℝ × ℝ →L[ℝ] ℝ) (v : ℝ × ℝ) :
    L v v = v.1 * v.1 * L (1, 0) (1, 0) + v.1 * v.2 * L (1, 0) (0, 1)
      + v.2 * v.1 * L (0, 1) (1, 0) + v.2 * v.2 * L (0, 1) (0, 1) := by
  have hv : L v = v.1 • L (1, 0) + v.2 • L (0, 1) := by
    obtain ⟨x, y⟩ := v
    have : ((x, y) : ℝ × ℝ) = x • ((1, 0) : ℝ × ℝ) + y • ((0, 1) : ℝ × ℝ) := by ext <;> simp
    conv_lhs => rw [this, map_add, map_smul, map_smul]
  rw [hv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [clm_apply_prod (L (1, 0)) v, clm_apply_prod (L (0, 1)) v]
  ring

lemma partial_partial {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hd : DifferentiableAt ℝ (fderiv ℝ f) p)
    (v w : ℝ × ℝ) :
    fderiv ℝ (fun q => fderiv ℝ f q v) p w = fderiv ℝ (fderiv ℝ f) p w v := by
  have h1 : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) p) p := hd.hasFDerivAt
  have := (h1.clm_apply (hasFDerivAt_const v p)).fderiv
  rw [this]
  simp

/-- The Hessian entries `f_xx, f_xy, f_yy` of a `C²` function in terms of `fderiv (fderiv f)`. -/
lemma hessian_entries {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hf : ContDiffAt ℝ 2 f p) :
    partialXX f p = fderiv ℝ (fderiv ℝ f) p (1, 0) (1, 0) ∧
    partialYY f p = fderiv ℝ (fderiv ℝ f) p (0, 1) (0, 1) ∧
    partialXY f p = fderiv ℝ (fderiv ℝ f) p (0, 1) (1, 0) := by
  have hd := (contDiffAt_two_aux hf).2
  exact ⟨partial_partial hd (1, 0) (1, 0), partial_partial hd (0, 1) (0, 1),
    partial_partial hd (1, 0) (0, 1)⟩

/-- Near a point where `f` is `C²`, the second derivative is a symmetric quadratic form with coefficients
`A, B, C` (continuous in the base point). -/
lemma hessian_form_eventually {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hf : ContDiffAt ℝ 2 f p) :
    ∀ᶠ q in 𝓝 p, ∀ h : ℝ × ℝ, fderiv ℝ (fderiv ℝ f) q h h =
      fderiv ℝ (fderiv ℝ f) q (1, 0) (1, 0) * h.1 ^ 2
      + 2 * fderiv ℝ (fderiv ℝ f) q (0, 1) (1, 0) * h.1 * h.2
      + fderiv ℝ (fderiv ℝ f) q (0, 1) (0, 1) * h.2 ^ 2 := by
  filter_upwards [hf.eventually (by simp)] with q hq h
  have hs : IsSymmSndFDerivAt ℝ f q := hq.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField])
  rw [bilin_expand, hs (1, 0) (0, 1)]
  ring

lemma hessian_continuousAt {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hf : ContDiffAt ℝ 2 f p) (v w : ℝ × ℝ) :
    ContinuousAt (fun q => fderiv ℝ (fderiv ℝ f) q v w) p := by
  have hc : ContinuousAt (fderiv ℝ (fderiv ℝ f)) p :=
    ((hf.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuousAt
  exact (hc.clm_apply continuousAt_const).clm_apply continuousAt_const

lemma quad_nonneg {a b c x y : ℝ} (ha : 0 < a) (hD : 0 < a * c - b ^ 2) :
    0 ≤ a * x ^ 2 + 2 * b * x * y + c * y ^ 2 := by
  by_contra hneg
  have hneg := not_le.1 hneg
  have := mul_neg_of_pos_of_neg ha hneg
  nlinarith [sq_nonneg (a * x + b * y), mul_nonneg hD.le (sq_nonneg y)]

lemma quad_nonpos {a b c x y : ℝ} (ha : a < 0) (hD : 0 < a * c - b ^ 2) :
    a * x ^ 2 + 2 * b * x * y + c * y ^ 2 ≤ 0 := by
  by_contra hneg
  have hneg := not_le.1 hneg
  have := mul_neg_of_neg_of_pos ha hneg
  nlinarith [sq_nonneg (a * x + b * y), mul_nonneg hD.le (sq_nonneg y)]

lemma exists_indefinite {a b c : ℝ} (hD : a * c - b ^ 2 < 0) :
    ∃ u v : ℝ × ℝ, 0 < a * u.1 ^ 2 + 2 * b * u.1 * u.2 + c * u.2 ^ 2 ∧
      a * v.1 ^ 2 + 2 * b * v.1 * v.2 + c * v.2 ^ 2 < 0 := by
  rcases eq_or_ne a 0 with ha | ha
  · rcases eq_or_ne c 0 with hc | hc
    · subst ha; subst hc
      have hb : b ≠ 0 := by rintro rfl; simp at hD
      rcases lt_or_gt_of_ne hb with h | h
      · refine ⟨(1, -1), (1, 1), ?_, ?_⟩ <;> simp <;> linarith
      · refine ⟨(1, 1), (1, -1), ?_, ?_⟩ <;> simp <;> linarith
    · subst ha
      rcases lt_or_gt_of_ne hc with h | h
      · refine ⟨(c, -b), (0, 1), ?_, ?_⟩
        · simp only
          nlinarith [mul_pos_of_neg_of_neg h hD]
        · simpa using h
      · refine ⟨(0, 1), (c, -b), ?_, ?_⟩
        · simpa using h
        · simp only
          nlinarith [mul_neg_of_pos_of_neg h hD]
  · rcases lt_or_gt_of_ne ha with h | h
    · refine ⟨(-b, a), (1, 0), ?_, ?_⟩
      · simp only
        nlinarith [mul_pos_of_neg_of_neg h hD]
      · simpa using h
    · refine ⟨(1, 0), (-b, a), ?_, ?_⟩
      · simpa using h
      · simp only
        nlinarith [mul_neg_of_pos_of_neg h hD]

/-- OpenStax Calculus 3:Theorem 4.17 (CA-547), local minimum. If `f` is `C²` near a critical point `p` and
`D = f_xx f_yy - f_xy² > 0` with `f_xx > 0`, then `f` has a local minimum at `p`. -/
@[kb "openstaxcalculus2016" "3:Theorem 4.17, p. 398"]
theorem second_derivative_test_min {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hf : ContDiffAt ℝ 2 f p)
    (hx : partialX f p = 0) (hy : partialY f p = 0)
    (hD : 0 < hessianDet f p) (hxx : 0 < partialXX f p) : IsLocalMin f p := by
  obtain ⟨e1, e2, e3⟩ := hessian_entries hf
  unfold hessianDet at hD
  rw [e1, e2, e3] at hD
  rw [e1] at hxx
  refine isLocalMin_of_hessian_nonneg hf (fderiv_eq_zero_of_partials hx hy) ?_
  have hA := hessian_continuousAt hf (1, 0) (1, 0)
  have hB := hessian_continuousAt hf (0, 1) (1, 0)
  have hC := hessian_continuousAt hf (0, 1) (0, 1)
  have h1 : ∀ᶠ q in 𝓝 p, 0 < fderiv ℝ (fderiv ℝ f) q (1, 0) (1, 0) :=
    hA.eventually (lt_mem_nhds hxx)
  have h2 : ∀ᶠ q in 𝓝 p, 0 < fderiv ℝ (fderiv ℝ f) q (1, 0) (1, 0) * fderiv ℝ (fderiv ℝ f) q (0, 1) (0, 1)
      - fderiv ℝ (fderiv ℝ f) q (0, 1) (1, 0) ^ 2 :=
    ((hA.mul hC).sub (hB.pow 2)).eventually (lt_mem_nhds hD)
  filter_upwards [hessian_form_eventually hf, h1, h2] with q hq ha hDq h
  rw [hq h]
  exact quad_nonneg ha hDq

/-- OpenStax Calculus 3:Theorem 4.17 (CA-547), local maximum. If `f` is `C²` near a critical point `p` and
`D > 0` with `f_xx < 0`, then `f` has a local maximum at `p`. -/
@[kb "openstaxcalculus2016" "3:Theorem 4.17, p. 398"]
theorem second_derivative_test_max {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hf : ContDiffAt ℝ 2 f p)
    (hx : partialX f p = 0) (hy : partialY f p = 0)
    (hD : 0 < hessianDet f p) (hxx : partialXX f p < 0) : IsLocalMax f p := by
  obtain ⟨e1, e2, e3⟩ := hessian_entries hf
  unfold hessianDet at hD
  rw [e1, e2, e3] at hD
  rw [e1] at hxx
  refine isLocalMax_of_hessian_nonpos hf (fderiv_eq_zero_of_partials hx hy) ?_
  have hA := hessian_continuousAt hf (1, 0) (1, 0)
  have hB := hessian_continuousAt hf (0, 1) (1, 0)
  have hC := hessian_continuousAt hf (0, 1) (0, 1)
  have h1 : ∀ᶠ q in 𝓝 p, fderiv ℝ (fderiv ℝ f) q (1, 0) (1, 0) < 0 :=
    hA.eventually (gt_mem_nhds hxx)
  have h2 : ∀ᶠ q in 𝓝 p, 0 < fderiv ℝ (fderiv ℝ f) q (1, 0) (1, 0) * fderiv ℝ (fderiv ℝ f) q (0, 1) (0, 1)
      - fderiv ℝ (fderiv ℝ f) q (0, 1) (1, 0) ^ 2 :=
    ((hA.mul hC).sub (hB.pow 2)).eventually (lt_mem_nhds hD)
  filter_upwards [hessian_form_eventually hf, h1, h2] with q hq ha hDq h
  rw [hq h]
  exact quad_nonpos ha hDq

/-- OpenStax Calculus 3:Theorem 4.17 (CA-547, CA-546), saddle point. If `f` is `C²` near a critical point `p`
and `D = f_xx f_yy - f_xy² < 0`, then `p` is a saddle point: neither a local minimum nor a local maximum. -/
@[kb "openstaxcalculus2016" "3:Theorem 4.17, p. 398"]
theorem second_derivative_test_saddle {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hf : ContDiffAt ℝ 2 f p)
    (hx : partialX f p = 0) (hy : partialY f p = 0) (hD : hessianDet f p < 0) :
    ¬ IsLocalMin f p ∧ ¬ IsLocalMax f p ∧ IsSaddlePoint f p := by
  obtain ⟨e1, e2, e3⟩ := hessian_entries hf
  unfold hessianDet at hD
  rw [e1, e2, e3] at hD
  have hp := fderiv_eq_zero_of_partials hx hy
  obtain ⟨u, v, hu, hv⟩ := exists_indefinite hD
  have hq := (hessian_form_eventually hf).self_of_nhds
  rw [← hq u] at hu
  rw [← hq v] at hv
  have hmin := not_isLocalMin_of_hessian_neg hf hp hv
  have hmax := not_isLocalMax_of_hessian_pos hf hp hu
  have hd := (contDiffAt_two_aux hf).1.self_of_nhds
  refine ⟨hmin, hmax, ?_, ?_⟩
  · have h1 := hasDerivAt_section_x hd
    rw [hx] at h1
    have h2 := hasDerivAt_section_y hd
    rw [hy] at h2
    exact ⟨h1, h2⟩
  · rintro (h | h)
    · exact hmin h
    · exact hmax h

/-! ### The inconclusive case `D = 0` -/

lemma partialX_eq {g : ℝ × ℝ → ℝ} {q : ℝ × ℝ} {d : ℝ} (hd : DifferentiableAt ℝ g q)
    (h : HasDerivAt (fun x => g (x, q.2)) d q.1) : partialX g q = d :=
  (hasDerivAt_section_x hd).unique h

lemma partialY_eq {g : ℝ × ℝ → ℝ} {q : ℝ × ℝ} {d : ℝ} (hd : DifferentiableAt ℝ g q)
    (h : HasDerivAt (fun y => g (q.1, y)) d q.2) : partialY g q = d :=
  (hasDerivAt_section_y hd).unique h

/-- The test functions `x⁴ + s y⁴` have `D = 0` at the origin. -/
lemma hessianDet_quartic (s : ℝ) :
    hessianDet (fun q : ℝ × ℝ => q.1 ^ 4 + s * q.2 ^ 4) (0, 0) = 0 := by
  have eX : partialX (fun q : ℝ × ℝ => q.1 ^ 4 + s * q.2 ^ 4) = fun q => 4 * q.1 ^ 3 := by
    funext q
    refine partialX_eq (by fun_prop) ?_
    simpa using ((hasDerivAt_pow 4 q.1).add_const (s * q.2 ^ 4))
  have eY : partialY (fun q : ℝ × ℝ => q.1 ^ 4 + s * q.2 ^ 4) = fun q => s * (4 * q.2 ^ 3) := by
    funext q
    refine partialY_eq (by fun_prop) ?_
    have := ((hasDerivAt_pow 4 q.2).const_mul s).const_add (q.1 ^ 4)
    simpa using this
  have hXX : partialXX (fun q : ℝ × ℝ => q.1 ^ 4 + s * q.2 ^ 4) (0, 0) = 0 := by
    unfold partialXX
    rw [eX]
    have h := partialX_eq (g := fun q : ℝ × ℝ => 4 * q.1 ^ 3) (q := (0, 0)) (by fun_prop)
      ((hasDerivAt_pow 3 (0 : ℝ)).const_mul 4)
    rw [h]; simp
  have hYY : partialYY (fun q : ℝ × ℝ => q.1 ^ 4 + s * q.2 ^ 4) (0, 0) = 0 := by
    unfold partialYY
    rw [eY]
    have h := partialY_eq (g := fun q : ℝ × ℝ => s * (4 * q.2 ^ 3)) (q := (0, 0)) (by fun_prop)
      (((hasDerivAt_pow 3 (0 : ℝ)).const_mul 4).const_mul s)
    rw [h]; simp
  have hXY : partialXY (fun q : ℝ × ℝ => q.1 ^ 4 + s * q.2 ^ 4) (0, 0) = 0 := by
    unfold partialXY
    rw [eX]
    exact partialY_eq (g := fun q : ℝ × ℝ => 4 * q.1 ^ 3) (q := (0, 0)) (by fun_prop)
      (hasDerivAt_const _ _)
  unfold hessianDet
  rw [hXX, hYY, hXY]
  simp

/-- OpenStax Calculus 3:Theorem 4.17 (CA-547), the case `D = 0` is inconclusive: `x⁴ + y⁴` and `x⁴ - y⁴`
both have `D = 0` at the origin (a critical point), but the first has a local minimum there and the second a
saddle point (no local extremum). -/
@[kb "openstaxcalculus2016" "3:Theorem 4.17, p. 398"]
theorem second_derivative_test_inconclusive :
    (hessianDet (fun q : ℝ × ℝ => q.1 ^ 4 + q.2 ^ 4) (0, 0) = 0 ∧
      IsLocalMin (fun q : ℝ × ℝ => q.1 ^ 4 + q.2 ^ 4) (0, 0)) ∧
    (hessianDet (fun q : ℝ × ℝ => q.1 ^ 4 + (-1) * q.2 ^ 4) (0, 0) = 0 ∧
      ¬ IsLocalExtr (fun q : ℝ × ℝ => q.1 ^ 4 + (-1) * q.2 ^ 4) (0, 0)) := by
  refine ⟨⟨?_, ?_⟩, ⟨hessianDet_quartic (-1), ?_⟩⟩
  · simpa using hessianDet_quartic 1
  · exact Filter.Eventually.of_forall fun q => by simp; positivity
  · have hpath : Tendsto (fun t : ℝ => ((t, 0) : ℝ × ℝ)) (𝓝[≠] 0) (𝓝 ((0 : ℝ), (0 : ℝ))) := by
      have : Continuous fun t : ℝ => ((t, 0) : ℝ × ℝ) := by fun_prop
      exact (this.tendsto' 0 _ rfl).mono_left nhdsWithin_le_nhds
    have hpath' : Tendsto (fun t : ℝ => ((0, t) : ℝ × ℝ)) (𝓝[≠] 0) (𝓝 ((0 : ℝ), (0 : ℝ))) := by
      have : Continuous fun t : ℝ => ((0, t) : ℝ × ℝ) := by fun_prop
      exact (this.tendsto' 0 _ rfl).mono_left nhdsWithin_le_nhds
    rintro (h | h)
    · -- local min fails along the `y`-axis
      have := (hpath'.eventually h).and self_mem_nhdsWithin
      obtain ⟨t, ht, ht0⟩ := this.exists
      have ht0' : t ≠ 0 := ht0
      simp at ht
      have : 0 < t ^ 4 := by positivity
      linarith
    · have := (hpath.eventually h).and self_mem_nhdsWithin
      obtain ⟨t, ht, ht0⟩ := this.exists
      have ht0' : t ≠ 0 := ht0
      simp at ht
      have : 0 < t ^ 4 := by positivity
      linarith

/-! ## Extreme values on a closed bounded set -/

/-- OpenStax Calculus 3:Theorem 4.19 (CA-550). Let `K ⊆ ℝ²` be closed and bounded (compact) and nonempty,
`f` continuous on `K` and differentiable at the interior points. Then `f` attains an absolute maximum on `K`
and an absolute minimum on `K`, and each is attained either on the boundary of `K` or at a critical point
of `f` in the interior. -/
@[kb "openstaxcalculus2016" "3:Theorem 4.19, p. 402"]
theorem absolute_extrema_on_compact {f : ℝ × ℝ → ℝ} {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hne : K.Nonempty) (hcont : ContinuousOn f K) (hdiff : ∀ p ∈ interior K, DifferentiableAt ℝ f p) :
    (∃ p ∈ K, IsMaxOn f K p ∧ (p ∈ frontier K ∨ (p ∈ interior K ∧ IsCriticalPoint f p))) ∧
    (∃ p ∈ K, IsMinOn f K p ∧ (p ∈ frontier K ∨ (p ∈ interior K ∧ IsCriticalPoint f p))) := by
  constructor
  · obtain ⟨p, hp, hmax⟩ := hK.exists_isMaxOn hne hcont
    refine ⟨p, hp, hmax, ?_⟩
    by_cases hi : p ∈ interior K
    · right
      refine ⟨hi, ?_⟩
      have hl : IsLocalMax f p := hmax.isLocalMax (mem_interior_iff_mem_nhds.1 hi)
      exact isCriticalPoint_of_isLocalExtr (Or.inr hl) (hdiff p hi)
    · left
      exact ⟨subset_closure hp, hi⟩
  · obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hne hcont
    refine ⟨p, hp, hmin, ?_⟩
    by_cases hi : p ∈ interior K
    · right
      refine ⟨hi, ?_⟩
      have hl : IsLocalMin f p := hmin.isLocalMin (mem_interior_iff_mem_nhds.1 hi)
      exact isCriticalPoint_of_isLocalExtr (Or.inl hl) (hdiff p hi)
    · left
      exact ⟨subset_closure hp, hi⟩

end UndergradKB.Calculus
