import UndergradKB.Common.Attr
import UndergradKB.DifferentialEquations.SecondOrderLinear
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Constant-coefficient second-order equations `a y'' + b y' + c y = 0` (Lebl §2.2, §0.2, §2.4)

`SolvesCC a b c y` says that `y` is twice differentiable on all of `ℝ` and satisfies `a y'' + b y' + c y = 0`.
For `a ≠ 0` it is the case `p = b/a`, `q = c/a` of `SolvesLin2`, so existence of the explicit solutions plus
`lin2_unique` yields "these are all the solutions". The root hypotheses are stated as polynomial identities
`∀ r, a r² + b r + c = a (r - r₁)(r - r₂)` (resp. `a ((r-α)² + β²)`). -/

namespace UndergradKB.DifferentialEquations

open Set Filter Topology

/-- `y` solves `a y'' + b y' + c y = 0` on all of `ℝ`. -/
def SolvesCC (a b c : ℝ) (y : ℝ → ℝ) : Prop :=
  ∀ x, DifferentiableAt ℝ y x ∧ DifferentiableAt ℝ (deriv y) x ∧
    a * deriv (deriv y) x + b * deriv y x + c * y x = 0

lemma solvesCC_iff {a b c : ℝ} (ha : a ≠ 0) {y : ℝ → ℝ} :
    SolvesCC a b c y ↔ SolvesLin2 (fun _ => b / a) (fun _ => c / a) 0 univ y := by
  have key : ∀ u v w : ℝ, a * u + b * v + c * w = 0 ↔ u + b / a * v + c / a * w = 0 := by
    intro u v w
    have : u + b / a * v + c / a * w = (a * u + b * v + c * w) / a := by field_simp
    rw [this, div_eq_zero_iff]
    simp [ha]
  constructor
  · intro h t _
    obtain ⟨h1, h2, h3⟩ := h t
    exact ⟨h1, h2, (key _ _ _).1 h3⟩
  · intro h t
    obtain ⟨h1, h2, h3⟩ := h t (mem_univ t)
    exact ⟨h1, h2, (key _ _ _).2 h3⟩

/-- If `y' = y₁` and `y₁' = y₂` everywhere, then `y` solves the equation iff the algebraic relation holds. -/
lemma solvesCC_iff_of_hasDerivAt {a b c : ℝ} {y y₁ y₂ : ℝ → ℝ}
    (h1 : ∀ x, HasDerivAt y (y₁ x) x) (h2 : ∀ x, HasDerivAt y₁ (y₂ x) x) :
    SolvesCC a b c y ↔ ∀ x, a * y₂ x + b * y₁ x + c * y x = 0 := by
  have e1 : deriv y = y₁ := funext fun x => (h1 x).deriv
  have e2 : deriv y₁ = y₂ := funext fun x => (h2 x).deriv
  unfold SolvesCC
  simp only [e1, e2]
  constructor
  · intro h x
    exact (h x).2.2
  · intro h x
    exact ⟨(h1 x).differentiableAt, (h2 x).differentiableAt, h x⟩

lemma solvesCC_linComb {a b c : ℝ} (ha : a ≠ 0) {y₁ y₂ : ℝ → ℝ} (h₁ : SolvesCC a b c y₁)
    (h₂ : SolvesCC a b c y₂) (C₁ C₂ : ℝ) : SolvesCC a b c (fun x => C₁ * y₁ x + C₂ * y₂ x) :=
  (solvesCC_iff ha).2 (lin2_superposition isOpen_univ ((solvesCC_iff ha).1 h₁)
    ((solvesCC_iff ha).1 h₂) C₁ C₂)

/-- Uniqueness for the constant-coefficient equation. -/
theorem cc_unique {a b c : ℝ} (ha : a ≠ 0) {y z : ℝ → ℝ} (hy : SolvesCC a b c y)
    (hz : SolvesCC a b c z) (h0 : y 0 = z 0) (h1 : deriv y 0 = deriv z 0) : y = z :=
  funext fun t => lin2_unique ordConnected_univ continuousOn_const continuousOn_const
    ((solvesCC_iff ha).1 hy) ((solvesCC_iff ha).1 hz) (mem_univ 0) h0 h1 t (mem_univ t)

/-- Completeness criterion: if two solutions `e₁, e₂` can match any initial data at `0`, every solution is
a combination of them. -/
theorem cc_general {a b c : ℝ} (ha : a ≠ 0) {e₁ e₂ e₁' e₂' : ℝ → ℝ} (he₁ : SolvesCC a b c e₁)
    (he₂ : SolvesCC a b c e₂) (d₁ : ∀ x, HasDerivAt e₁ (e₁' x) x) (d₂ : ∀ x, HasDerivAt e₂ (e₂' x) x)
    (hsolve : ∀ y0 y1 : ℝ, ∃ C₁ C₂ : ℝ, C₁ * e₁ 0 + C₂ * e₂ 0 = y0 ∧ C₁ * e₁' 0 + C₂ * e₂' 0 = y1)
    {y : ℝ → ℝ} (hy : SolvesCC a b c y) : ∃ C₁ C₂ : ℝ, ∀ x, y x = C₁ * e₁ x + C₂ * e₂ x := by
  obtain ⟨C₁, C₂, h0, h1⟩ := hsolve (y 0) (deriv y 0)
  have hz := solvesCC_linComb ha he₁ he₂ C₁ C₂
  have hzd : deriv (fun x => C₁ * e₁ x + C₂ * e₂ x) 0 = C₁ * e₁' 0 + C₂ * e₂' 0 :=
    (((d₁ 0).const_mul C₁).add ((d₂ 0).const_mul C₂)).deriv
  have := cc_unique ha hy hz h0.symm (by rw [hzd, h1])
  exact ⟨C₁, C₂, fun x => congrFun this x⟩

lemma hasDerivAt_exp_mul' (r x : ℝ) :
    HasDerivAt (fun x => Real.exp (r * x)) (r * Real.exp (r * x)) x := by
  have := ((hasDerivAt_id x).const_mul r).exp
  exact this.congr_deriv (by simp only [id_eq, mul_one]; ring)

lemma hasDerivAt_cos_mul' (β x : ℝ) :
    HasDerivAt (fun x => Real.cos (β * x)) (-(β * Real.sin (β * x))) x := by
  have := ((hasDerivAt_id x).const_mul β).cos
  exact this.congr_deriv (by simp only [id_eq, mul_one]; ring)

lemma hasDerivAt_sin_mul' (β x : ℝ) :
    HasDerivAt (fun x => Real.sin (β * x)) (β * Real.cos (β * x)) x := by
  have := ((hasDerivAt_id x).const_mul β).sin
  exact this.congr_deriv (by simp only [id_eq, mul_one]; ring)

/-- **Characteristic equation** (Lebl §2.2): `e^{rx}` solves `a y'' + b y' + c y = 0` exactly when
`a r² + b r + c = 0`. -/
@[kb "lebldiffyqs2026" "Section 2.2, p. 85"]
theorem cc_exp_iff (a b c r : ℝ) :
    SolvesCC a b c (fun x => Real.exp (r * x)) ↔ a * r ^ 2 + b * r + c = 0 := by
  rw [solvesCC_iff_of_hasDerivAt (y₁ := fun x => r * Real.exp (r * x))
    (y₂ := fun x => r * (r * Real.exp (r * x))) (hasDerivAt_exp_mul' r)
    (fun x => (hasDerivAt_exp_mul' r x).const_mul r)]
  constructor
  · intro h
    have h0 := h 0
    simp only [mul_zero, Real.exp_zero] at h0
    linear_combination h0
  · intro h x
    linear_combination (Real.exp (r * x)) * h

/-- **Theorem 2.2.1, distinct real roots** (Lebl): if `a ≠ 0` and `a r² + b r + c = a (r - r₁)(r - r₂)` with
`r₁ ≠ r₂`, the solutions on `ℝ` of `a y'' + b y' + c y = 0` are exactly `C₁ e^{r₁x} + C₂ e^{r₂x}`. -/
@[kb "lebldiffyqs2026" "Theorem 2.2.1, p. 85"]
theorem cc_real_distinct {a b c r₁ r₂ : ℝ} (ha : a ≠ 0) (hr : r₁ ≠ r₂)
    (hroots : ∀ r, a * r ^ 2 + b * r + c = a * (r - r₁) * (r - r₂)) {y : ℝ → ℝ} :
    SolvesCC a b c y ↔ ∃ C₁ C₂ : ℝ, ∀ x, y x = C₁ * Real.exp (r₁ * x) + C₂ * Real.exp (r₂ * x) := by
  have s1 : SolvesCC a b c (fun x => Real.exp (r₁ * x)) :=
    (cc_exp_iff a b c r₁).2 (by rw [hroots r₁]; ring)
  have s2 : SolvesCC a b c (fun x => Real.exp (r₂ * x)) :=
    (cc_exp_iff a b c r₂).2 (by rw [hroots r₂]; ring)
  have hne : r₁ - r₂ ≠ 0 := sub_ne_zero.2 hr
  constructor
  · intro hy
    refine cc_general ha s1 s2 (hasDerivAt_exp_mul' r₁) (hasDerivAt_exp_mul' r₂) ?_ hy
    intro y0 y1
    refine ⟨(y1 - r₂ * y0) / (r₁ - r₂), (r₁ * y0 - y1) / (r₁ - r₂), ?_, ?_⟩ <;>
      simp only [mul_zero, Real.exp_zero, mul_one] <;> field_simp <;> ring
  · rintro ⟨C₁, C₂, h⟩
    have : y = fun x => C₁ * Real.exp (r₁ * x) + C₂ * Real.exp (r₂ * x) := funext h
    rw [this]
    exact solvesCC_linComb ha s1 s2 C₁ C₂

/-- **Theorem 2.2.1, double root** (Lebl): if `a ≠ 0` and `a r² + b r + c = a (r - r₀)²`, the solutions on `ℝ` are
exactly `(C₁ + C₂ x) e^{r₀ x}`. -/
@[kb "lebldiffyqs2026" "Theorem 2.2.1, p. 85"]
theorem cc_real_double {a b c r₀ : ℝ} (ha : a ≠ 0)
    (hroots : ∀ r, a * r ^ 2 + b * r + c = a * (r - r₀) ^ 2) {y : ℝ → ℝ} :
    SolvesCC a b c y ↔ ∃ C₁ C₂ : ℝ, ∀ x, y x = (C₁ + C₂ * x) * Real.exp (r₀ * x) := by
  have hb : b = -2 * a * r₀ := by
    have h0 := hroots 0
    have h1 := hroots 1
    linear_combination h1 - h0
  have hc : c = a * r₀ ^ 2 := by
    have h0 := hroots 0
    linear_combination h0
  subst hb hc
  have d1 := hasDerivAt_exp_mul' r₀
  have d2 : ∀ x, HasDerivAt (fun x => x * Real.exp (r₀ * x)) ((1 + r₀ * x) * Real.exp (r₀ * x)) x :=
    fun x => ((hasDerivAt_id' x).mul (hasDerivAt_exp_mul' r₀ x)).congr_deriv (by ring)
  have d2' : ∀ x, HasDerivAt (fun x => (1 + r₀ * x) * Real.exp (r₀ * x))
      ((2 * r₀ + r₀ ^ 2 * x) * Real.exp (r₀ * x)) x := fun x =>
    ((((hasDerivAt_id' x).const_mul r₀).const_add 1).mul (hasDerivAt_exp_mul' r₀ x)).congr_deriv
      (by ring)
  have s1 : SolvesCC a (-2 * a * r₀) (a * r₀ ^ 2) (fun x => Real.exp (r₀ * x)) :=
    (cc_exp_iff _ _ _ r₀).2 (by ring)
  have s2 : SolvesCC a (-2 * a * r₀) (a * r₀ ^ 2) (fun x => x * Real.exp (r₀ * x)) :=
    (solvesCC_iff_of_hasDerivAt d2 d2').2 (fun x => by ring)
  constructor
  · intro hy
    obtain ⟨C₁, C₂, h⟩ := cc_general ha s1 s2 d1 d2 (e₁' := fun x => r₀ * Real.exp (r₀ * x))
      (e₂' := fun x => (1 + r₀ * x) * Real.exp (r₀ * x)) (by
        intro y0 y1
        refine ⟨y0, y1 - r₀ * y0, ?_, ?_⟩ <;> simp only [mul_zero, Real.exp_zero, mul_one]
          <;> ring) hy
    exact ⟨C₁, C₂, fun x => by rw [h x]; ring⟩
  · rintro ⟨C₁, C₂, h⟩
    have : y = fun x => C₁ * Real.exp (r₀ * x) + C₂ * (x * Real.exp (r₀ * x)) :=
      funext fun x => by rw [h x]; ring
    rw [this]
    exact solvesCC_linComb ha s1 s2 C₁ C₂

/-- **Theorem 2.2.3, complex roots** (Lebl): if `a ≠ 0`, `β ≠ 0` and `a r² + b r + c = a ((r - α)² + β²)` (roots
`α ± iβ`), the real solutions on `ℝ` are exactly `e^{αx}(C₁ cos βx + C₂ sin βx)`. -/
@[kb "lebldiffyqs2026" "Theorem 2.2.3, p. 88"]
theorem cc_complex {a b c α β : ℝ} (ha : a ≠ 0) (hβ : β ≠ 0)
    (hroots : ∀ r, a * r ^ 2 + b * r + c = a * ((r - α) ^ 2 + β ^ 2)) {y : ℝ → ℝ} :
    SolvesCC a b c y ↔ ∃ C₁ C₂ : ℝ, ∀ x,
      y x = Real.exp (α * x) * (C₁ * Real.cos (β * x) + C₂ * Real.sin (β * x)) := by
  have hb : b = -2 * a * α := by
    have h0 := hroots 0
    have h1 := hroots 1
    linear_combination h1 - h0
  have hc : c = a * (α ^ 2 + β ^ 2) := by
    have h0 := hroots 0
    linear_combination h0
  subst hb hc
  have d1 : ∀ x, HasDerivAt (fun x => Real.exp (α * x) * Real.cos (β * x))
      (Real.exp (α * x) * (α * Real.cos (β * x) - β * Real.sin (β * x))) x := fun x =>
    ((hasDerivAt_exp_mul' α x).mul (hasDerivAt_cos_mul' β x)).congr_deriv (by ring)
  have d1' : ∀ x, HasDerivAt
      (fun x => Real.exp (α * x) * (α * Real.cos (β * x) - β * Real.sin (β * x)))
      (Real.exp (α * x) * ((α ^ 2 - β ^ 2) * Real.cos (β * x) - 2 * α * β * Real.sin (β * x))) x :=
    fun x => ((hasDerivAt_exp_mul' α x).mul (((hasDerivAt_cos_mul' β x).const_mul α).sub
      ((hasDerivAt_sin_mul' β x).const_mul β))).congr_deriv (by simp only [Pi.sub_apply]; ring)
  have d2 : ∀ x, HasDerivAt (fun x => Real.exp (α * x) * Real.sin (β * x))
      (Real.exp (α * x) * (α * Real.sin (β * x) + β * Real.cos (β * x))) x := fun x =>
    ((hasDerivAt_exp_mul' α x).mul (hasDerivAt_sin_mul' β x)).congr_deriv (by ring)
  have d2' : ∀ x, HasDerivAt
      (fun x => Real.exp (α * x) * (α * Real.sin (β * x) + β * Real.cos (β * x)))
      (Real.exp (α * x) * ((α ^ 2 - β ^ 2) * Real.sin (β * x) + 2 * α * β * Real.cos (β * x))) x :=
    fun x => ((hasDerivAt_exp_mul' α x).mul (((hasDerivAt_sin_mul' β x).const_mul α).add
      ((hasDerivAt_cos_mul' β x).const_mul β))).congr_deriv (by simp only [Pi.add_apply]; ring)
  have s1 : SolvesCC a (-2 * a * α) (a * (α ^ 2 + β ^ 2))
      (fun x => Real.exp (α * x) * Real.cos (β * x)) :=
    (solvesCC_iff_of_hasDerivAt d1 d1').2 (fun x => by ring)
  have s2 : SolvesCC a (-2 * a * α) (a * (α ^ 2 + β ^ 2))
      (fun x => Real.exp (α * x) * Real.sin (β * x)) :=
    (solvesCC_iff_of_hasDerivAt d2 d2').2 (fun x => by ring)
  constructor
  · intro hy
    obtain ⟨C₁, C₂, h⟩ := cc_general ha s1 s2 d1 d2 (by
      intro y0 y1
      refine ⟨y0, (y1 - α * y0) / β, ?_, ?_⟩ <;>
        simp only [mul_zero, Real.exp_zero, Real.cos_zero, Real.sin_zero, mul_one, zero_add,
          add_zero, sub_zero]
      field_simp
      ring) hy
    exact ⟨C₁, C₂, fun x => by rw [h x]; ring⟩
  · rintro ⟨C₁, C₂, h⟩
    have : y = fun x => C₁ * (Real.exp (α * x) * Real.cos (β * x)) +
        C₂ * (Real.exp (α * x) * Real.sin (β * x)) := funext fun x => by rw [h x]; ring
    rw [this]
    exact solvesCC_linComb ha s1 s2 C₁ C₂

/-! ### Chapter 0: the fundamental equations -/

/-- **Third fundamental equation** (Lebl §0.2.4): for `k > 0` the solutions of `y'' = -k² y` (that is
`y'' + k² y = 0`) are exactly `C₁ cos kx + C₂ sin kx`. -/
@[kb "lebldiffyqs2026" "Section 0.2.4, p. 14"]
theorem fundamental_cos_sin {k : ℝ} (hk : 0 < k) {y : ℝ → ℝ} :
    SolvesCC 1 0 (k ^ 2) y ↔ ∃ C₁ C₂ : ℝ, ∀ x, y x = C₁ * Real.cos (k * x) + C₂ * Real.sin (k * x) := by
  rw [cc_complex (α := 0) (β := k) one_ne_zero hk.ne' (fun r => by ring)]
  constructor
  · rintro ⟨C₁, C₂, h⟩
    exact ⟨C₁, C₂, fun x => by simpa using h x⟩
  · rintro ⟨C₁, C₂, h⟩
    exact ⟨C₁, C₂, fun x => by simpa using h x⟩

/-- **Fourth fundamental equation** (Lebl §0.2.4): for `k > 0` the solutions of `y'' = k² y` are exactly
`C₁ e^{kx} + C₂ e^{-kx}`. -/
@[kb "lebldiffyqs2026" "Section 0.2.4, p. 14"]
theorem fundamental_exp {k : ℝ} (hk : 0 < k) {y : ℝ → ℝ} :
    SolvesCC 1 0 (-(k ^ 2)) y ↔
      ∃ C₁ C₂ : ℝ, ∀ x, y x = C₁ * Real.exp (k * x) + C₂ * Real.exp (-k * x) :=
  cc_real_distinct (r₁ := k) (r₂ := -k) one_ne_zero (by linarith) (fun r => by ring)

/-- The same solutions written with hyperbolic functions (Lebl §0.2.4):
`D₁ cosh kx + D₂ sinh kx`. -/
@[kb "lebldiffyqs2026" "Section 0.2.4, p. 14"]
theorem fundamental_cosh_sinh {k : ℝ} (hk : 0 < k) {y : ℝ → ℝ} :
    SolvesCC 1 0 (-(k ^ 2)) y ↔
      ∃ D₁ D₂ : ℝ, ∀ x, y x = D₁ * Real.cosh (k * x) + D₂ * Real.sinh (k * x) := by
  rw [fundamental_exp hk]
  constructor
  · rintro ⟨C₁, C₂, h⟩
    refine ⟨C₁ + C₂, C₁ - C₂, fun x => ?_⟩
    rw [h x, Real.cosh_eq, Real.sinh_eq, neg_mul]
    ring
  · rintro ⟨D₁, D₂, h⟩
    refine ⟨(D₁ + D₂) / 2, (D₁ - D₂) / 2, fun x => ?_⟩
    rw [h x, Real.cosh_eq, Real.sinh_eq, neg_mul]
    ring

/-- **Example 0.2.2** (Lebl): the solutions of `y'' = 0` are exactly `C₁ x + C₂`. -/
@[kb "lebldiffyqs2026" "Example 0.2.2, p. 14"]
theorem second_derivative_zero_general {y : ℝ → ℝ} :
    SolvesCC 1 0 0 y ↔ ∃ C₁ C₂ : ℝ, ∀ x, y x = C₁ * x + C₂ := by
  rw [cc_real_double (r₀ := 0) one_ne_zero (fun r => by ring)]
  constructor
  · rintro ⟨C₁, C₂, h⟩
    exact ⟨C₂, C₁, fun x => by rw [h x]; simp; ring⟩
  · rintro ⟨C₁, C₂, h⟩
    exact ⟨C₂, C₁, fun x => by rw [h x]; simp; ring⟩

/-- **Example 0.2.2, initial conditions** (Lebl): `y'' = 0` with `y(0) = 2`, `y'(0) = 3` has exactly the
solution `3x + 2`. -/
@[kb "lebldiffyqs2026" "Example 0.2.2, p. 14"]
theorem second_derivative_zero_ivp {y : ℝ → ℝ} :
    (SolvesCC 1 0 0 y ∧ y 0 = 2 ∧ deriv y 0 = 3) ↔ ∀ x, y x = 3 * x + 2 := by
  have hz : ∀ x : ℝ, HasDerivAt (fun x : ℝ => 3 * x + 2) 3 x := fun x =>
    (((hasDerivAt_id' x).const_mul 3).add_const 2).congr_deriv (by ring)
  have sz : SolvesCC 1 0 0 (fun x : ℝ => 3 * x + 2) :=
    (solvesCC_iff_of_hasDerivAt (y₁ := fun _ => (3 : ℝ)) (y₂ := fun _ => (0 : ℝ)) hz
      (fun x => hasDerivAt_const x 3)).2 (fun x => by ring)
  constructor
  · rintro ⟨hy, h0, h1⟩
    have := cc_unique one_ne_zero hy sz (by simp [h0]) (by rw [h1, (hz 0).deriv])
    exact fun x => congrFun this x
  · intro h
    have : y = fun x : ℝ => 3 * x + 2 := funext h
    subst this
    exact ⟨sz, by norm_num, (hz 0).deriv⟩

/-! ### Mechanical vibrations (§2.4) -/

/-- **Free undamped motion** (Lebl §2.4, Example 2.4.1): for `m, k > 0` the solutions of `m x'' + k x = 0` are
exactly `A cos ω₀t + B sin ω₀t` with `ω₀ = √(k/m)`. -/
@[kb "lebldiffyqs2026" "Example 2.4.1, p. 98"]
theorem free_undamped {m k : ℝ} (hm : 0 < m) (hk : 0 < k) {x : ℝ → ℝ} :
    SolvesCC m 0 k x ↔ ∃ A B : ℝ, ∀ t,
      x t = A * Real.cos (Real.sqrt (k / m) * t) + B * Real.sin (Real.sqrt (k / m) * t) := by
  have hsq : Real.sqrt (k / m) ^ 2 = k / m := Real.sq_sqrt (div_pos hk hm).le
  rw [cc_complex (α := 0) (β := Real.sqrt (k / m)) hm.ne' (Real.sqrt_pos.2 (div_pos hk hm)).ne'
    (fun r => by rw [hsq]; field_simp; ring)]
  constructor
  · rintro ⟨C₁, C₂, h⟩
    exact ⟨C₁, C₂, fun x => by simpa using h x⟩
  · rintro ⟨C₁, C₂, h⟩
    exact ⟨C₁, C₂, fun x => by simpa using h x⟩

/-- Free damped motion, **overdamped** case (Lebl §2.4.3): for `m, k, c > 0` and `c² > 4km`, the characteristic
equation has two distinct negative roots `r₁, r₂` and the solutions of `m x'' + c x' + k x = 0` are exactly
`C₁ e^{r₁ t} + C₂ e^{r₂ t}`. -/
@[kb "lebldiffyqs2026" "Section 2.4.3, p. 100"]
theorem free_damped_over {m c k : ℝ} (hm : 0 < m) (hk : 0 < k) (hc : 0 < c) (hdisc : 4 * k * m < c ^ 2) :
    ∃ r₁ r₂ : ℝ, r₁ < 0 ∧ r₂ < 0 ∧ r₁ ≠ r₂ ∧
      (∀ r, m * r ^ 2 + c * r + k = m * (r - r₁) * (r - r₂)) ∧
      ∀ x : ℝ → ℝ, SolvesCC m c k x ↔
        ∃ C₁ C₂ : ℝ, ∀ t, x t = C₁ * Real.exp (r₁ * t) + C₂ * Real.exp (r₂ * t) := by
  set D := Real.sqrt (c ^ 2 - 4 * k * m) with hDdef
  have hD : D ^ 2 = c ^ 2 - 4 * k * m := Real.sq_sqrt (by linarith)
  have hDpos : 0 < D := Real.sqrt_pos.2 (by linarith)
  have hDc : D < c := by
    by_contra h
    have h := not_lt.1 h
    nlinarith [mul_pos hk hm]
  have hroots : ∀ r, m * r ^ 2 + c * r + k =
      m * (r - (-c + D) / (2 * m)) * (r - (-c - D) / (2 * m)) := by
    intro r
    field_simp
    linear_combination hD
  have hne : (-c + D) / (2 * m) ≠ (-c - D) / (2 * m) := by
    intro h
    rw [div_left_inj' (by positivity)] at h
    linarith
  refine ⟨(-c + D) / (2 * m), (-c - D) / (2 * m), div_neg_of_neg_of_pos (by linarith) (by positivity),
    div_neg_of_neg_of_pos (by linarith) (by positivity), hne, hroots, fun x => ?_⟩
  exact cc_real_distinct hm.ne' hne hroots

/-- Free damped motion, **critically damped** case (Lebl §2.4.3): for `m, k, c > 0` and `c² = 4km`, with
`p = c/(2m)`, the solutions of `m x'' + c x' + k x = 0` are exactly `(C₁ + C₂ t) e^{-p t}`. -/
@[kb "lebldiffyqs2026" "Section 2.4.3, p. 100"]
theorem free_damped_critical {m c k : ℝ} (hm : 0 < m) (_hk : 0 < k) (_hc : 0 < c)
    (hdisc : c ^ 2 = 4 * k * m) {x : ℝ → ℝ} :
    SolvesCC m c k x ↔ ∃ C₁ C₂ : ℝ, ∀ t, x t = (C₁ + C₂ * t) * Real.exp (-(c / (2 * m)) * t) := by
  apply cc_real_double hm.ne'
  intro r
  field_simp
  linear_combination (-1 : ℝ) * hdisc

/-- Free damped motion, **underdamped** case (Lebl §2.4.3): for `m, k, c > 0` and `c² < 4km`, with
`p = c/(2m)` and `ω₁ = √(k/m - p²)`, the solutions of `m x'' + c x' + k x = 0` are exactly
`e^{-p t}(A cos ω₁t + B sin ω₁t)`. -/
@[kb "lebldiffyqs2026" "Section 2.4.3, p. 100"]
theorem free_damped_under {m c k : ℝ} (hm : 0 < m) (_hk : 0 < k) (_hc : 0 < c)
    (hdisc : c ^ 2 < 4 * k * m) {x : ℝ → ℝ} :
    SolvesCC m c k x ↔ ∃ A B : ℝ, ∀ t,
      x t = Real.exp (-(c / (2 * m)) * t) *
        (A * Real.cos (Real.sqrt (k / m - (c / (2 * m)) ^ 2) * t) +
          B * Real.sin (Real.sqrt (k / m - (c / (2 * m)) ^ 2) * t)) := by
  have hpos : 0 < k / m - (c / (2 * m)) ^ 2 := by
    have : k / m - (c / (2 * m)) ^ 2 = (4 * k * m - c ^ 2) / (4 * m ^ 2) := by
      field_simp
      ring
    rw [this]
    exact div_pos (by linarith) (by positivity)
  have hsq := Real.sq_sqrt hpos.le
  apply cc_complex hm.ne' (Real.sqrt_pos.2 hpos).ne'
  intro r
  rw [hsq]
  field_simp
  ring

/-- In the overdamped case every solution tends to `0` as `t → ∞` (Lebl §2.4.3). -/
@[kb "lebldiffyqs2026" "Section 2.4.3, p. 100"]
theorem free_damped_over_tendsto {m c k : ℝ} (hm : 0 < m) (hk : 0 < k) (hc : 0 < c)
    (hdisc : 4 * k * m < c ^ 2) {x : ℝ → ℝ} (hx : SolvesCC m c k x) :
    Tendsto x atTop (𝓝 0) := by
  obtain ⟨r₁, r₂, h1, h2, -, -, hiff⟩ := free_damped_over hm hk hc hdisc
  obtain ⟨C₁, C₂, h⟩ := (hiff x).1 hx
  have e1 : Tendsto (fun t => Real.exp (r₁ * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg h1)
  have e2 : Tendsto (fun t => Real.exp (r₂ * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg h2)
  have := (e1.const_mul C₁).add (e2.const_mul C₂)
  simp only [mul_zero, add_zero] at this
  exact this.congr (fun t => (h t).symm)

/-- In the critically damped case every solution tends to `0` as `t → ∞` (Lebl §2.4.3). -/
@[kb "lebldiffyqs2026" "Section 2.4.3, p. 100"]
theorem free_damped_critical_tendsto {m c k : ℝ} (hm : 0 < m) (hk : 0 < k) (hc : 0 < c)
    (hdisc : c ^ 2 = 4 * k * m) {x : ℝ → ℝ} (hx : SolvesCC m c k x) :
    Tendsto x atTop (𝓝 0) := by
  obtain ⟨C₁, C₂, h⟩ := (free_damped_critical hm hk hc hdisc).1 hx
  set p := c / (2 * m) with hp
  have hp0 : 0 < p := by positivity
  have hlin : Tendsto (fun t : ℝ => p * t) atTop atTop := tendsto_id.const_mul_atTop hp0
  have e1 : Tendsto (fun t : ℝ => Real.exp (-(p * t))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hlin)
  have e2 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hlin
  have := (e1.const_mul C₁).add (e2.const_mul (C₂ / p))
  simp only [mul_zero, add_zero] at this
  refine this.congr (fun t => ?_)
  rw [h t]
  simp only [Function.comp, pow_one, neg_mul]
  field_simp

end UndergradKB.DifferentialEquations
