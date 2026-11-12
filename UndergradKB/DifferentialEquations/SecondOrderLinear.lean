import UndergradKB.DifferentialEquations.LinearSystems
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Second-order linear equations `y'' + p(x) y' + q(x) y = f(x)` (Lebl §2.1, §2.5)

Lebl writes the equation as `y'' + p(x) y' + q(x) y = f(x)` on an interval `I` with continuous `p, q, f`. We write
`SolvesLin2 p q f I y` for "`y` is twice differentiable on `I` and satisfies the equation there" (a bridging
definition: Mathlib has no notion of a solution of a scalar second-order equation). The theory is reduced to the
first-order system `(y, y')' = A(x) (y, y') + (0, f)` of `LinearSystems.lean`. -/

namespace UndergradKB.DifferentialEquations

open Set

/-- `y` solves `y'' + p(x) y' + q(x) y = f(x)` at every point of `I` (twice differentiable there). -/
def SolvesLin2 (p q f : ℝ → ℝ) (I : Set ℝ) (y : ℝ → ℝ) : Prop :=
  ∀ t ∈ I, DifferentiableAt ℝ y t ∧ DifferentiableAt ℝ (deriv y) t ∧
    deriv (deriv y) t + p t * deriv y t + q t * y t = f t

/-- The companion linear map `(u, v) ↦ (v, -q u - p v)` of `y'' + p y' + q y = 0`. -/
noncomputable def companion2 (p q : ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  ((ContinuousLinearMap.snd ℝ ℝ ℝ).prod 0) +
    q • ((0 : ℝ × ℝ →L[ℝ] ℝ).prod (-ContinuousLinearMap.fst ℝ ℝ ℝ)) +
    p • ((0 : ℝ × ℝ →L[ℝ] ℝ).prod (-ContinuousLinearMap.snd ℝ ℝ ℝ))

@[simp] lemma companion2_apply (p q : ℝ) (w : ℝ × ℝ) :
    companion2 p q w = (w.2, -q * w.1 - p * w.2) := by
  simp [companion2]; ring

lemma continuousOn_companion2 {p q : ℝ → ℝ} {I : Set ℝ} (hp : ContinuousOn p I)
    (hq : ContinuousOn q I) : ContinuousOn (fun t => companion2 (p t) (q t)) I := by
  unfold companion2
  fun_prop

/-- A solution of the scalar equation gives a solution `(y, y')` of the first-order system. -/
lemma SolvesLin2.hasDerivAt_vec {p q f : ℝ → ℝ} {I : Set ℝ} {y : ℝ → ℝ}
    (hy : SolvesLin2 p q f I y) :
    ∀ t ∈ I, HasDerivAt (fun u => (y u, deriv y u))
      (companion2 (p t) (q t) (y t, deriv y t) + (0, f t)) t := by
  intro t ht
  obtain ⟨h1, h2, h3⟩ := hy t ht
  convert h1.hasDerivAt.prodMk h2.hasDerivAt using 1
  ext
  · simp
  · simp only [companion2_apply, Prod.snd_add]
    linarith

/-- **Uniqueness for the second-order linear equation** (Lebl, Theorem 2.1.2, uniqueness half): if `p, q` are
continuous on an interval `I`, two solutions of `y'' + p y' + q y = f` on `I` with the same `y(a)` and `y'(a)` at a
point `a ∈ I` agree on `I`. -/
@[kb "lebldiffyqs2026" "Theorem 2.1.2, p. 80"]
theorem lin2_unique {p q f : ℝ → ℝ} {I : Set ℝ} (hI : I.OrdConnected) (hp : ContinuousOn p I)
    (hq : ContinuousOn q I) {y z : ℝ → ℝ} (hy : SolvesLin2 p q f I y) (hz : SolvesLin2 p q f I z)
    {a : ℝ} (ha : a ∈ I) (h0 : y a = z a) (h1 : deriv y a = deriv z a) : ∀ t ∈ I, y t = z t := by
  have := linear_unique hI (continuousOn_companion2 hp hq) (f := fun t => (0, f t))
    hy.hasDerivAt_vec hz.hasDerivAt_vec ha (by simp [h0, h1])
  intro t ht
  exact congrArg Prod.fst (this t ht)

lemma SolvesLin2.eventually_hasDerivAt {p q f : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I) {y : ℝ → ℝ}
    (hy : SolvesLin2 p q f I y) {t : ℝ} (ht : t ∈ I) :
    ∀ᶠ u in nhds t, HasDerivAt y (deriv y u) u :=
  Filter.eventually_of_mem (hI.mem_nhds ht) fun u hu => (hy u hu).1.hasDerivAt

/-- Linear combinations: if `y₁` solves the equation with right side `f₁` and `y₂` with `f₂` on an open set,
`c₁ y₁ + c₂ y₂` solves it with right side `c₁ f₁ + c₂ f₂`. -/
theorem SolvesLin2.linComb {p q f₁ f₂ : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I) {y₁ y₂ : ℝ → ℝ}
    (h₁ : SolvesLin2 p q f₁ I y₁) (h₂ : SolvesLin2 p q f₂ I y₂) (c₁ c₂ : ℝ) :
    SolvesLin2 p q (fun t => c₁ * f₁ t + c₂ * f₂ t) I (fun t => c₁ * y₁ t + c₂ * y₂ t) := by
  intro t ht
  have hd : ∀ᶠ u in nhds t, deriv (fun t => c₁ * y₁ t + c₂ * y₂ t) u =
      c₁ * deriv y₁ u + c₂ * deriv y₂ u := by
    filter_upwards [h₁.eventually_hasDerivAt hI ht, h₂.eventually_hasDerivAt hI ht] with u hu1 hu2
    exact ((hu1.const_mul c₁).add (hu2.const_mul c₂)).deriv
  obtain ⟨a1, b1, e1⟩ := h₁ t ht
  obtain ⟨a2, b2, e2⟩ := h₂ t ht
  have hdd : HasDerivAt (deriv fun t => c₁ * y₁ t + c₂ * y₂ t)
      (c₁ * deriv (deriv y₁) t + c₂ * deriv (deriv y₂) t) t :=
    ((b1.hasDerivAt.const_mul c₁).add (b2.hasDerivAt.const_mul c₂)).congr_of_eventuallyEq hd
  refine ⟨(a1.const_mul c₁).add (a2.const_mul c₂), hdd.differentiableAt, ?_⟩
  rw [hdd.deriv, hd.self_of_nhds]
  linear_combination c₁ * e1 + c₂ * e2

/-- **Superposition** (Lebl, Theorem 2.1.1): on an open set, any linear combination `C₁ y₁ + C₂ y₂` of solutions of
the homogeneous equation `y'' + p y' + q y = 0` is a solution. -/
@[kb "lebldiffyqs2026" "Theorem 2.1.1, p. 79"]
theorem lin2_superposition {p q : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I) {y₁ y₂ : ℝ → ℝ}
    (h₁ : SolvesLin2 p q 0 I y₁) (h₂ : SolvesLin2 p q 0 I y₂) (C₁ C₂ : ℝ) :
    SolvesLin2 p q 0 I (fun t => C₁ * y₁ t + C₂ * y₂ t) := by
  have := h₁.linComb hI h₂ C₁ C₂
  convert this using 1
  funext t; simp

/-- **Nonhomogeneous equations** (Lebl, Theorem 2.5.1): if `yₚ` is a particular solution of
`y'' + p y' + q y = f` on an open set, then `y` solves this equation exactly when `y - yₚ` solves the homogeneous
equation. -/
@[kb "lebldiffyqs2026" "Theorem 2.5.1, p. 104"]
theorem lin2_nonhomogeneous_iff {p q f : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I) {yp : ℝ → ℝ}
    (hp : SolvesLin2 p q f I yp) (y : ℝ → ℝ) :
    SolvesLin2 p q f I y ↔ SolvesLin2 p q 0 I (fun t => y t - yp t) := by
  constructor
  · intro hy
    have := hy.linComb hI hp 1 (-1)
    convert this using 1
    · funext t; simp
    · funext t; ring
  · intro hy
    have := hy.linComb hI hp 1 1
    simpa using this

/-- **General solution** (Lebl, Theorem 2.1.3): if `p, q` are continuous on an open interval `I` and `y₁, y₂` are
linearly independent solutions on `I` of the homogeneous equation `y'' + p y' + q y = 0`, then every solution on `I`
is `C₁ y₁ + C₂ y₂` for some constants. -/
@[kb "lebldiffyqs2026" "Theorem 2.1.3, p. 81"]
theorem lin2_general_solution {p q : ℝ → ℝ} {I : Set ℝ} (hI : I.OrdConnected)
    (hp : ContinuousOn p I) (hq : ContinuousOn q I) {y₁ y₂ : ℝ → ℝ}
    (h₁ : SolvesLin2 p q 0 I y₁) (h₂ : SolvesLin2 p q 0 I y₂)
    (hli : LinearIndependent ℝ ![fun t : I => y₁ t, fun t : I => y₂ t]) (hne : I.Nonempty)
    {y : ℝ → ℝ} (hy : SolvesLin2 p q 0 I y) :
    ∃ C₁ C₂ : ℝ, ∀ t ∈ I, y t = C₁ * y₁ t + C₂ * y₂ t := by
  let x : Fin 2 → ℝ → ℝ × ℝ := ![fun u => (y₁ u, deriv y₁ u), fun u => (y₂ u, deriv y₂ u)]
  have hx : ∀ i, ∀ t ∈ I, HasDerivAt (x i) (companion2 (p t) (q t) (x i t)) t := by
    intro i t ht
    fin_cases i
    · simpa [x] using h₁.hasDerivAt_vec t ht
    · simpa [x] using h₂.hasDerivAt_vec t ht
  have hlix : LinearIndependent ℝ (fun i (t : I) => x i t) := by
    rw [Fintype.linearIndependent_iff] at hli ⊢
    intro c hc
    apply hli c
    funext t
    have := congrArg Prod.fst (congrFun hc t)
    simpa [Fin.sum_univ_two, x] using this
  have hcard : Fintype.card (Fin 2) = Module.finrank ℝ (ℝ × ℝ) := by simp
  obtain ⟨c, hc, -⟩ := linear_general_solution hI (continuousOn_companion2 hp hq) hx hlix hcard
    (y := fun u => (y u, deriv y u)) (by simpa using hy.hasDerivAt_vec) hne
  refine ⟨c 0, c 1, fun t ht => ?_⟩
  have := congrArg Prod.fst (hc t ht)
  simpa [Fin.sum_univ_two, x] using this

/-- The general solution of the nonhomogeneous equation (Lebl, Theorem 2.5.1 with Theorem 2.1.3): every solution of
`y'' + p y' + q y = f` on an open interval is `C₁ y₁ + C₂ y₂ + yₚ`. -/
@[kb "lebldiffyqs2026" "Theorem 2.5.1, p. 104"]
theorem lin2_general_solution_nonhomogeneous {p q f : ℝ → ℝ} {I : Set ℝ} (hI : I.OrdConnected)
    (hIo : IsOpen I) (hp : ContinuousOn p I) (hq : ContinuousOn q I) {y₁ y₂ yp : ℝ → ℝ}
    (h₁ : SolvesLin2 p q 0 I y₁) (h₂ : SolvesLin2 p q 0 I y₂)
    (hli : LinearIndependent ℝ ![fun t : I => y₁ t, fun t : I => y₂ t]) (hne : I.Nonempty)
    (hyp : SolvesLin2 p q f I yp) {y : ℝ → ℝ} (hy : SolvesLin2 p q f I y) :
    ∃ C₁ C₂ : ℝ, ∀ t ∈ I, y t = C₁ * y₁ t + C₂ * y₂ t + yp t := by
  obtain ⟨C₁, C₂, h⟩ := lin2_general_solution hI hp hq h₁ h₂ hli hne
    ((lin2_nonhomogeneous_iff hIo hyp y).1 hy)
  exact ⟨C₁, C₂, fun t ht => by linarith [h t ht]⟩

end UndergradKB.DifferentialEquations
