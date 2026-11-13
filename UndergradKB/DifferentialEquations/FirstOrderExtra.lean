import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Matrix.Normed
import UndergradKB.Common.Attr
import UndergradKB.DifferentialEquations.FirstOrder
import UndergradKB.DifferentialEquations.HigherOrderConstant

/-! # Extra first-order material (Lebl, Chapter 1, plus a few related items)

* DE-023: implicit solutions `G(x, y(x)) = C` satisfy `G_x + G_y y' = 0`; singular (constant) solutions.
* DE-033: phase diagram for `x' = f(x)`: equilibria are not crossed (uniqueness), monotone between equilibria.
* DE-044: the form `(-y dx + x dy)/(x² + y²)` is closed but has no potential on the punctured plane.
* DE-039, DE-038: Heun and Runge-Kutta steps; exact one-step multipliers and order bounds for `y' = λ y`.
* DE-107: truncated Taylor series of `e^{tA}` converge.
* DE-068: the `x^k` rule of undetermined coefficients for `y'' + b y' + c y = e^{rx}`. -/

namespace UndergradKB.DifferentialEquations

open Set Filter Topology NNReal

/-! ### DE-023 implicit solutions -/

/-- **Implicit solutions** (Lebl, §1.3.2) (DE-023): if `G` is differentiable at `(x, y(x))` with derivative `L`,
`y` is differentiable at `x`, and `G(t, y(t)) = C` for all `t` in an open set `I` containing `x`, then
`G_x + G_y y' = 0`, where `G_x = L (1, 0)` and `G_y = L (0, 1)`. -/
@[kb "lebldiffyqs2026" "§1.3.2 implicit solution, p. 34"]
theorem implicit_solution_ode {G : ℝ × ℝ → ℝ} {y : ℝ → ℝ} {C : ℝ} {I : Set ℝ} (hI : IsOpen I)
    {x y' : ℝ} (hx : x ∈ I) (hy : HasDerivAt y y' x) {L : ℝ × ℝ →L[ℝ] ℝ}
    (hG : HasFDerivAt G L (x, y x)) (hsol : ∀ t ∈ I, G (t, y t) = C) :
    L (1, 0) + L (0, 1) * y' = 0 := by
  have hc : HasDerivAt (fun t : ℝ => (t, y t)) ((1 : ℝ), y') x := (hasDerivAt_id' x).prodMk hy
  have h1 : HasDerivAt (fun t : ℝ => G (t, y t)) (L (1, y')) x := hG.comp_hasDerivAt x hc
  have h2 : HasDerivAt (fun t : ℝ => G (t, y t)) 0 x :=
    (hasDerivAt_const x C).congr_of_eventuallyEq
      (by filter_upwards [hI.mem_nhds hx] with t ht; exact hsol t ht)
  have h3 := h1.unique h2
  have e : ((1 : ℝ), y') = ((1 : ℝ), (0 : ℝ)) + y' • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
  rw [e, map_add, map_smul] at h3
  simpa [mul_comm] using h3

/-- Solving the implicit relation for the slope (DE-023): where `G_y ≠ 0`, `y' = -G_x / G_y`. -/
@[kb "lebldiffyqs2026" "§1.3.2 implicit solution, p. 34"]
theorem implicit_solution_slope {G : ℝ × ℝ → ℝ} {y : ℝ → ℝ} {C : ℝ} {I : Set ℝ} (hI : IsOpen I)
    {x y' : ℝ} (hx : x ∈ I) (hy : HasDerivAt y y' x) {L : ℝ × ℝ →L[ℝ] ℝ}
    (hG : HasFDerivAt G L (x, y x)) (hsol : ∀ t ∈ I, G (t, y t) = C) (hGy : L (0, 1) ≠ 0) :
    y' = -L (1, 0) / L (0, 1) := by
  have := implicit_solution_ode hI hx hy hG hsol
  field_simp
  linarith

/-- **Singular solutions** (Lebl, §1.3.2) (DE-023): if `g c = 0`, the constant function `y ≡ c` solves
`y' = f(x) g(y)`, even though it is lost when one divides by `g(y)`. -/
@[kb "lebldiffyqs2026" "§1.3.2 singular solutions, p. 35"]
theorem singular_solution_const (f g : ℝ → ℝ) {c : ℝ} (hc : g c = 0) :
    ∀ x : ℝ, HasDerivAt (fun _ : ℝ => c) (f x * g c) x := fun x => by
  simpa [hc] using hasDerivAt_const x c

/-! ### DE-033 phase diagram -/

section Phase

variable {f x : ℝ → ℝ} {I : Set ℝ}

/-- A solution of `x' = f(x)` that touches an equilibrium `c` at an interior time equals `c` near that time. -/
lemma eventually_eq_equilibrium (hf : LocallyLipschitz f) {c : ℝ} (hc : f c = 0)
    (hx : ∀ t ∈ I, HasDerivAt x (f (x t)) t) (hI : IsOpen I) {t₁ : ℝ} (ht₁ : t₁ ∈ I)
    (h1 : x t₁ = c) : x =ᶠ[𝓝 t₁] fun _ => c := by
  obtain ⟨K, s, hs, hL⟩ := hf c
  have hxc : ContinuousAt x t₁ := (hx t₁ ht₁).continuousAt
  have hxs : ∀ᶠ t in 𝓝 t₁, x t ∈ s := hxc.eventually_mem (by rw [h1]; exact hs)
  have hIn : ∀ᶠ t in 𝓝 t₁, t ∈ I := hI.mem_nhds ht₁
  refine ODE_solution_unique_of_eventually (v := fun _ => f) (s := fun _ => s) (K := K)
    (t₀ := t₁) (f := x) (g := fun _ => c) ?_ ?_ ?_ h1
  · exact Eventually.of_forall fun _ => hL
  · filter_upwards [hIn, hxs] with t ht hts
    exact ⟨hx t ht, hts⟩
  · exact Eventually.of_forall fun t => ⟨by simpa [hc] using hasDerivAt_const t c, mem_of_mem_nhds hs⟩

/-- **Equilibria are not crossed** (uniqueness part of the phase diagram, Lebl §1.6) (DE-033): let `f` be
locally Lipschitz with `f c = 0` and `x` a solution of `x' = f(x)` on an open interval `I`. If
`x` differs from `c` at one time, it differs from `c` at all times of `I`. -/
theorem equilibrium_not_crossed (hf : LocallyLipschitz f) {c : ℝ} (hc : f c = 0)
    (hI : IsOpen I) (hIc : IsPreconnected I) (hx : ∀ t ∈ I, HasDerivAt x (f (x t)) t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ I) (h0 : x t₀ ≠ c) : ∀ t ∈ I, x t ≠ c := by
  intro t ht hxt
  have hsub : I ⊆ interior {t | x t = c} := by
    refine hIc.subset_of_closure_inter_subset (u := interior {t | x t = c}) isOpen_interior
      ⟨t, ht, ?_⟩ ?_
    · rw [mem_interior_iff_mem_nhds]
      exact eventually_eq_equilibrium hf hc hx hI ht hxt
    · rintro s ⟨hs, hsI⟩
      have hfr : ∃ᶠ r in 𝓝 s, x r = c :=
        (mem_closure_iff_frequently.mp hs).mono fun r hr => interior_subset hr
      have hxs : x s = c :=
        tendsto_nhds_unique_of_frequently_eq (hx s hsI).continuousAt tendsto_const_nhds hfr
      rw [mem_interior_iff_mem_nhds]
      exact eventually_eq_equilibrium hf hc hx hI hsI hxs
  exact h0 (interior_subset (hsub ht₀))

/-- **A solution starting below an equilibrium stays below it** (Lebl §1.6 phase diagram, DE-033): `f` locally
Lipschitz, `f c = 0`, `x` a solution of `x' = f(x)` on an open interval `I` with `x t₀ < c`; then `x t < c`
for all `t ∈ I` (earlier and later times). -/
@[kb "lebldiffyqs2026" "§1.6 phase diagram, p. 52"]
theorem solution_below_equilibrium (hf : LocallyLipschitz f) {c : ℝ} (hc : f c = 0)
    (hI : IsOpen I) (hIc : IsPreconnected I) (hx : ∀ t ∈ I, HasDerivAt x (f (x t)) t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ I) (h0 : x t₀ < c) : ∀ t ∈ I, x t < c := by
  intro t ht
  by_contra hge
  push Not at hge
  have hcont : ContinuousOn x I := fun s hs => (hx s hs).continuousAt.continuousWithinAt
  obtain ⟨s, hs, hsc⟩ := hIc.intermediate_value ht₀ ht hcont ⟨h0.le, hge⟩
  exact equilibrium_not_crossed hf hc hI hIc hx ht₀ h0.ne s hs hsc

/-- The mirror statement (DE-033): a solution starting above an equilibrium stays above it. -/
@[kb "lebldiffyqs2026" "§1.6 phase diagram, p. 52"]
theorem solution_above_equilibrium (hf : LocallyLipschitz f) {c : ℝ} (hc : f c = 0)
    (hI : IsOpen I) (hIc : IsPreconnected I) (hx : ∀ t ∈ I, HasDerivAt x (f (x t)) t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ I) (h0 : c < x t₀) : ∀ t ∈ I, c < x t := by
  intro t ht
  by_contra hge
  push Not at hge
  have hcont : ContinuousOn x I := fun s hs => (hx s hs).continuousAt.continuousWithinAt
  obtain ⟨s, hs, hsc⟩ := hIc.intermediate_value ht ht₀ hcont ⟨hge, h0.le⟩
  exact equilibrium_not_crossed hf hc hI hIc hx ht₀ h0.ne' s hs hsc

/-- **Between two equilibria** (Lebl §1.6 phase diagram, DE-033): if `f a = f c = 0`, `f > 0` on `(a, c)`, `f`
is locally Lipschitz and `x` solves `x' = f(x)` on an open interval `I` with `x t₀ ∈ (a, c)`, then `x` stays in
`(a, c)` and is strictly increasing on `I`. -/
@[kb "lebldiffyqs2026" "§1.6 phase diagram, p. 52"]
theorem solution_between_equilibria_strictMono (hf : LocallyLipschitz f) {a c : ℝ}
    (ha : f a = 0) (hc : f c = 0) (hpos : ∀ y ∈ Ioo a c, 0 < f y)
    (hI : IsOpen I) (hO : I.OrdConnected) (hx : ∀ t ∈ I, HasDerivAt x (f (x t)) t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ I) (h0 : x t₀ ∈ Ioo a c) :
    (∀ t ∈ I, x t ∈ Ioo a c) ∧ StrictMonoOn x I := by
  have hIc : IsPreconnected I := hO.isPreconnected
  have hmem : ∀ t ∈ I, x t ∈ Ioo a c := fun t ht =>
    ⟨solution_above_equilibrium hf ha hI hIc hx ht₀ h0.1 t ht,
      solution_below_equilibrium hf hc hI hIc hx ht₀ h0.2 t ht⟩
  exact ⟨hmem, strictMonoOn_of_autonomous_pos hO.convex hx fun t ht => hpos _ (hmem t ht)⟩

end Phase

/-! ### DE-044 closed but not exact -/

/-- The coefficient `M = -y/(x²+y²)` of `dx` (DE-044). -/
noncomputable def angleFormM (p : ℝ × ℝ) : ℝ := -p.2 / (p.1 ^ 2 + p.2 ^ 2)

/-- The coefficient `N = x/(x²+y²)` of `dy` (DE-044). -/
noncomputable def angleFormN (p : ℝ × ℝ) : ℝ := p.1 / (p.1 ^ 2 + p.2 ^ 2)

lemma sq_add_sq_ne_zero_of_ne {p : ℝ × ℝ} (hp : p ≠ 0) : p.1 ^ 2 + p.2 ^ 2 ≠ 0 := by
  intro h
  apply hp
  have h1 : p.1 = 0 := by nlinarith [sq_nonneg p.1, sq_nonneg p.2]
  have h2 : p.2 = 0 := by nlinarith [sq_nonneg p.1, sq_nonneg p.2]
  exact Prod.ext h1 h2

/-- **The form is closed** (Lebl, Example 1.8.4) (DE-044): on the punctured plane `M_y = N_x`, both equal
`(y² - x²)/(x² + y²)²`. -/
@[kb "lebldiffyqs2026" "Example 1.8.4, p. 66"]
theorem angleForm_closed {p : ℝ × ℝ} (hp : p ≠ 0) :
    HasDerivAt (fun s => angleFormM (p.1, s)) ((p.2 ^ 2 - p.1 ^ 2) / (p.1 ^ 2 + p.2 ^ 2) ^ 2) p.2 ∧
    HasDerivAt (fun s => angleFormN (s, p.2)) ((p.2 ^ 2 - p.1 ^ 2) / (p.1 ^ 2 + p.2 ^ 2) ^ 2) p.1 := by
  have hne := sq_add_sq_ne_zero_of_ne hp
  obtain ⟨a, b⟩ := p
  simp only at hne ⊢
  constructor
  · have hn : HasDerivAt (fun s : ℝ => -s) (-1) b := (hasDerivAt_id' b).neg
    have hd : HasDerivAt (fun s : ℝ => a ^ 2 + s ^ 2) (2 * b) b := by
      simpa using ((hasDerivAt_id' b).pow 2).const_add (a ^ 2)
    have := hn.div hd hne
    unfold angleFormM
    convert this using 1
    field_simp
    ring
  · have hn : HasDerivAt (fun s : ℝ => s) 1 a := hasDerivAt_id' a
    have hd : HasDerivAt (fun s : ℝ => s ^ 2 + b ^ 2) (2 * a) a := by
      simpa using ((hasDerivAt_id' a).pow 2).add_const (b ^ 2)
    have := hn.div hd hne
    unfold angleFormN
    convert this using 1
    field_simp
    ring

/-- **No potential on the punctured plane** (Lebl, Example 1.8.4) (DE-044): there is no `F`, differentiable at
every point of `ℝ² ∖ {0}`, with `F_x = M` and `F_y = N`. (Along the unit circle `t ↦ F(cos t, sin t)` would
have derivative `1`, but it takes equal values at `0` and `2π`.) -/
@[kb "lebldiffyqs2026" "Example 1.8.4, p. 66"]
theorem angleForm_no_potential (F : ℝ × ℝ → ℝ)
    (hF : ∀ p : ℝ × ℝ, p ≠ 0 → DifferentiableAt ℝ F p ∧ fderiv ℝ F p (1, 0) = angleFormM p ∧
      fderiv ℝ F p (0, 1) = angleFormN p) : False := by
  set g : ℝ → ℝ := fun t => F (Real.cos t, Real.sin t) with hg
  have hder : ∀ t, HasDerivAt g 1 t := by
    intro t
    have hp : ((Real.cos t, Real.sin t) : ℝ × ℝ) ≠ 0 := by
      intro h
      have h1 : Real.cos t = 0 := congrArg Prod.fst h
      have h2 : Real.sin t = 0 := congrArg Prod.snd h
      have := Real.sin_sq_add_cos_sq t
      rw [h1, h2] at this
      norm_num at this
    obtain ⟨hd, hM, hN⟩ := hF _ hp
    have hc : HasDerivAt (fun t : ℝ => (Real.cos t, Real.sin t)) (-Real.sin t, Real.cos t) t :=
      (Real.hasDerivAt_cos t).prodMk (Real.hasDerivAt_sin t)
    have h1 := hd.hasFDerivAt.comp_hasDerivAt t hc
    have e : ((-Real.sin t, Real.cos t) : ℝ × ℝ) =
        (-Real.sin t) • ((1 : ℝ), (0 : ℝ)) + Real.cos t • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
    rw [e, map_add, map_smul, map_smul, hM, hN] at h1
    have hsum : Real.cos t ^ 2 + Real.sin t ^ 2 = 1 := Real.cos_sq_add_sin_sq t
    simp only [angleFormM, angleFormN, hsum, div_one, smul_eq_mul] at h1
    have h3 : -Real.sin t * -Real.sin t + Real.cos t * Real.cos t = 1 := by nlinarith [hsum]
    rw [h3] at h1
    exact h1
  have hder2 : ∀ t, HasDerivAt (fun t => g t - t) 0 t := fun t => by
    have h := (hder t).sub (hasDerivAt_id' t)
    rw [sub_self] at h
    exact h
  have hdiff : Differentiable ℝ (fun t => g t - t) := fun t => (hder2 t).differentiableAt
  have hd0 : ∀ t, deriv (fun t => g t - t) t = 0 := fun t => (hder2 t).deriv
  have := is_const_of_deriv_eq_zero hdiff hd0 (2 * Real.pi) 0
  simp only [hg, Real.cos_two_pi, Real.sin_two_pi, Real.cos_zero, Real.sin_zero] at this
  linarith [Real.pi_pos]

/-- **Potential on the right half plane** (Lebl, Example 1.8.4) (DE-044): `F(x, y) = arctan(y/x)` is
differentiable on `x > 0` with `F_x = M` and `F_y = N`. -/
@[kb "lebldiffyqs2026" "Example 1.8.4, p. 66"]
theorem angleForm_potential_halfPlane {p : ℝ × ℝ} (hp : 0 < p.1) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ => Real.arctan (q.2 / q.1)) p ∧
    fderiv ℝ (fun q : ℝ × ℝ => Real.arctan (q.2 / q.1)) p (1, 0) = angleFormM p ∧
    fderiv ℝ (fun q : ℝ × ℝ => Real.arctan (q.2 / q.1)) p (0, 1) = angleFormN p := by
  obtain ⟨a, b⟩ := p
  simp only at hp
  have hne : a ^ 2 + b ^ 2 ≠ 0 := by positivity
  have hdiff : DifferentiableAt ℝ (fun q : ℝ × ℝ => Real.arctan (q.2 / q.1)) (a, b) :=
    have hq : DifferentiableAt ℝ (fun q : ℝ × ℝ => q.2 / q.1) (a, b) := by
      fun_prop (disch := exact hp.ne')
    hq.arctan
  refine ⟨hdiff, ?_, ?_⟩
  · have hc : HasDerivAt (fun s : ℝ => (s, b)) ((1 : ℝ), (0 : ℝ)) a :=
      (hasDerivAt_id' a).prodMk (hasDerivAt_const a b)
    have h1 := hdiff.hasFDerivAt.comp_hasDerivAt a hc
    have h2 : HasDerivAt (fun s : ℝ => Real.arctan (b / s)) (-b / (a ^ 2 + b ^ 2)) a := by
      have hq : HasDerivAt (fun s : ℝ => b / s) (-b / a ^ 2) a := by
        refine ((hasDerivAt_const a b).div (hasDerivAt_id' a) hp.ne').congr_deriv ?_
        ring
      have := hq.arctan
      convert this using 1
      field_simp
    exact (h1.unique h2).trans (by simp [angleFormM])
  · have hc : HasDerivAt (fun s : ℝ => (a, s)) ((0 : ℝ), (1 : ℝ)) b :=
      (hasDerivAt_const b a).prodMk (hasDerivAt_id' b)
    have h1 := hdiff.hasFDerivAt.comp_hasDerivAt b hc
    have h2 : HasDerivAt (fun s : ℝ => Real.arctan (s / a)) (a / (a ^ 2 + b ^ 2)) b := by
      have hq : HasDerivAt (fun s : ℝ => s / a) (1 / a) b :=
        (hasDerivAt_id' b).div_const a
      have := hq.arctan
      convert this using 1
      field_simp
    exact (h1.unique h2).trans (by simp [angleFormN])

/-! ### DE-039 / DE-038 one-step methods -/

/-- One step of the improved Euler (Heun) method for `y' = f(x, y)` with step `h`:
`y + h (k₁ + k₂)/2`, `k₁ = f(x, y)`, `k₂ = f(x + h, y + h k₁)`. -/
noncomputable def heunStep (f : ℝ → ℝ → ℝ) (x y h : ℝ) : ℝ :=
  y + h / 2 * (f x y + f (x + h) (y + h * f x y))

/-- One step of the classical fourth-order Runge-Kutta method with step `h`:
`y + h (k₁ + 2k₂ + 2k₃ + k₄)/6`. -/
noncomputable def rk4Step (f : ℝ → ℝ → ℝ) (x y h : ℝ) : ℝ :=
  y + h / 6 * (f x y + 2 * f (x + h / 2) (y + h / 2 * f x y) +
    2 * f (x + h / 2) (y + h / 2 * f (x + h / 2) (y + h / 2 * f x y)) +
    f (x + h) (y + h * f (x + h / 2) (y + h / 2 * f (x + h / 2) (y + h / 2 * f x y))))

/-- On the model equation `y' = λ y`, a Heun step multiplies by `1 + z + z²/2`, `z = λ h` (DE-039). -/
@[kb "lebldiffyqs2026" "§1.7 improved Euler method, p. 62"]
theorem heunStep_linear (lam x y h : ℝ) :
    heunStep (fun _ y => lam * y) x y h = (1 + lam * h + (lam * h) ^ 2 / 2) * y := by
  unfold heunStep; ring

/-- **Heun is second order on `y' = λ y`** (DE-039, partial: only the model equation, not general `f`): the
one-step multiplier differs from `e^z` by at most `(2/9)|z|³` for `|z| ≤ 1`, so the local error against the exact
solution `y e^{λh}` is `O(h³)`. -/
@[kb "lebldiffyqs2026" "§1.7 improved Euler method, p. 62"]
theorem heunStep_linear_error (lam x y h : ℝ) (hz : |lam * h| ≤ 1) :
    |heunStep (fun _ y => lam * y) x y h - Real.exp (lam * h) * y| ≤ 2 / 9 * |lam * h| ^ 3 * |y| := by
  rw [heunStep_linear]
  have hb := Real.exp_bound hz (n := 3) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb
  norm_num at hb
  have e : (1 + lam * h + (lam * h) ^ 2 / 2) * y - Real.exp (lam * h) * y =
      -(Real.exp (lam * h) - (1 + lam * h + (lam * h) ^ 2 / 2)) * y := by ring
  rw [e, abs_mul, abs_neg]
  have h0 : 0 ≤ |y| := abs_nonneg y
  calc _ ≤ (|lam * h| ^ 3 * (2 / 9)) * |y| := by
        apply mul_le_mul_of_nonneg_right _ h0
        simpa only [abs_mul] using hb
    _ = _ := by ring

/-- On the model equation `y' = λ y`, an RK4 step multiplies by `1 + z + z²/2 + z³/6 + z⁴/24`, `z = λ h`
(DE-038). -/
@[kb "lebldiffyqs2026" "§1.7 Runge-Kutta method, p. 61"]
theorem rk4Step_linear (lam x y h : ℝ) :
    rk4Step (fun _ y => lam * y) x y h =
      (1 + lam * h + (lam * h) ^ 2 / 2 + (lam * h) ^ 3 / 6 + (lam * h) ^ 4 / 24) * y := by
  unfold rk4Step; ring

/-- **RK4 is fourth order on `y' = λ y`** (DE-038, partial: only the model equation, not general `f`): the
one-step multiplier differs from `e^z` by at most `|z|⁵/100` for `|z| ≤ 1`, so the local error is `O(h⁵)`. -/
@[kb "lebldiffyqs2026" "§1.7 Runge-Kutta method, p. 61"]
theorem rk4Step_linear_error (lam x y h : ℝ) (hz : |lam * h| ≤ 1) :
    |rk4Step (fun _ y => lam * y) x y h - Real.exp (lam * h) * y| ≤ 1 / 100 * |lam * h| ^ 5 * |y| := by
  rw [rk4Step_linear]
  have hb := Real.exp_bound hz (n := 5) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb
  norm_num at hb
  have e : (1 + lam * h + (lam * h) ^ 2 / 2 + (lam * h) ^ 3 / 6 + (lam * h) ^ 4 / 24) * y -
      Real.exp (lam * h) * y = -(Real.exp (lam * h) -
        (1 + lam * h + (lam * h) ^ 2 / 2 + (lam * h) ^ 3 / 6 + (lam * h) ^ 4 / 24)) * y := by ring
  rw [e, abs_mul, abs_neg]
  have h0 : 0 ≤ |y| := abs_nonneg y
  calc _ ≤ (|lam * h| ^ 5 * (1 / 100)) * |y| := by
        apply mul_le_mul_of_nonneg_right _ h0
        simpa only [abs_mul] using hb
    _ = _ := by ring

/-! ### DE-107 truncated Taylor series of the matrix exponential -/

section TaylorExp

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- **Truncated Taylor series of `e^{tA}`** (Lebl, §3.8.5) (DE-107): for a real square matrix `A`, the partial
sums `∑_{k<N} (t^k/k!) A^k` converge to `e^{tA}` as `N → ∞`. (No error bound is claimed.) -/
@[kb "lebldiffyqs2026" "§3.8.5 approximations, p. 174"]
theorem exp_taylor_tendsto {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, (t ^ k / (k.factorial : ℝ)) • A ^ k) atTop
      (𝓝 (NormedSpace.exp (t • A))) := by
  have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • A)).tendsto_sum_nat
  refine h.congr fun N => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_pow, smul_smul, div_eq_inv_mul, mul_comm]

end TaylorExp

/-! ### DE-068 the `x^k` rule -/

/-- **Simple resonance** (Lebl, §2.5.2) (DE-068): if `r` is a simple root of `r² + b r + c` (that is,
`r² + b r + c = 0` and `2r + b ≠ 0`), then `y = x e^{rx}/(2r + b)` solves `y'' + b y' + c y = e^{rx}`. -/
@[kb "lebldiffyqs2026" "§2.5.2 undetermined coefficients, p. 105"]
theorem hoc_undetermined_exp_simple_root (b c r : ℝ) (hr : r ^ 2 + b * r + c = 0) (hs : 2 * r + b ≠ 0) :
    hoc_Solves2 1 b c (fun x => Real.exp (r * x)) (fun x => x * Real.exp (r * x) / (2 * r + b)) := by
  set K := 2 * r + b with hK
  have h1 : ∀ x, HasDerivAt (fun x => x * Real.exp (r * x) / K)
      ((Real.exp (r * x) + r * x * Real.exp (r * x)) / K) x := fun x =>
    (((hasDerivAt_id' x).mul (hasDerivAt_exp_mul' r x)).div_const K).congr_deriv (by ring)
  have h2 : ∀ x, HasDerivAt (fun x => (Real.exp (r * x) + r * x * Real.exp (r * x)) / K)
      ((2 * r * Real.exp (r * x) + r ^ 2 * x * Real.exp (r * x)) / K) x := fun x =>
    (((hasDerivAt_exp_mul' r x).add
      (((hasDerivAt_id' x).const_mul r).mul (hasDerivAt_exp_mul' r x))).div_const K).congr_deriv
      (by ring)
  have e1 : deriv (fun x => x * Real.exp (r * x) / K) =
      fun x => (Real.exp (r * x) + r * x * Real.exp (r * x)) / K := funext fun x => (h1 x).deriv
  intro x
  refine ⟨(h1 x).differentiableAt, ?_, ?_⟩
  · rw [e1]; exact (h2 x).differentiableAt
  · rw [e1, (h2 x).deriv]
    show 1 * ((2 * r * Real.exp (r * x) + r ^ 2 * x * Real.exp (r * x)) / K) +
      b * ((Real.exp (r * x) + r * x * Real.exp (r * x)) / K) +
      c * (x * Real.exp (r * x) / K) = Real.exp (r * x)
    field_simp
    have hc : c = -(r ^ 2 + b * r) := by linarith
    rw [hK, hc]; ring

/-- **Double resonance** (Lebl, §2.5.2) (DE-068): if `b² = 4c` and `r = -b/2` is the double root, then
`y = x² e^{rx}/2` solves `y'' + b y' + c y = e^{rx}`. -/
@[kb "lebldiffyqs2026" "§2.5.2 undetermined coefficients, p. 105"]
theorem hoc_undetermined_exp_double_root (b c r : ℝ) (hbc : b ^ 2 = 4 * c) (hr : r = -b / 2) :
    hoc_Solves2 1 b c (fun x => Real.exp (r * x)) (fun x => x ^ 2 * Real.exp (r * x) / 2) := by
  have hb : b = -2 * r := by linarith
  have hc : c = r ^ 2 := by subst hb; nlinarith
  have h1 : ∀ x, HasDerivAt (fun x => x ^ 2 * Real.exp (r * x) / 2)
      ((x * Real.exp (r * x) + r * x ^ 2 * Real.exp (r * x) / 2)) x := fun x =>
    ((((hasDerivAt_id' x).pow 2).mul (hasDerivAt_exp_mul' r x)).div_const 2).congr_deriv
      (by simp; ring)
  have h2 : ∀ x, HasDerivAt (fun x => x * Real.exp (r * x) + r * x ^ 2 * Real.exp (r * x) / 2)
      (Real.exp (r * x) + 2 * r * x * Real.exp (r * x) + r ^ 2 * x ^ 2 * Real.exp (r * x) / 2) x :=
    fun x =>
    (((hasDerivAt_id' x).mul (hasDerivAt_exp_mul' r x)).add
      ((((hasDerivAt_id' x).pow 2).const_mul r |>.mul (hasDerivAt_exp_mul' r x)).div_const 2)).congr_deriv
      (by simp; ring)
  have e1 : deriv (fun x => x ^ 2 * Real.exp (r * x) / 2) =
      fun x => x * Real.exp (r * x) + r * x ^ 2 * Real.exp (r * x) / 2 :=
    funext fun x => (h1 x).deriv
  intro x
  refine ⟨(h1 x).differentiableAt, ?_, ?_⟩
  · rw [e1]; exact (h2 x).differentiableAt
  · rw [e1, (h2 x).deriv]
    show 1 * (Real.exp (r * x) + 2 * r * x * Real.exp (r * x) + r ^ 2 * x ^ 2 * Real.exp (r * x) / 2) +
      b * (x * Real.exp (r * x) + r * x ^ 2 * Real.exp (r * x) / 2) +
      c * (x ^ 2 * Real.exp (r * x) / 2) = Real.exp (r * x)
    rw [hb, hc]; ring

end UndergradKB.DifferentialEquations
