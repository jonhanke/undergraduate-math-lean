import UndergradKB.Common.Attr
import UndergradKB.DifferentialEquations.NthOrderLinear
import UndergradKB.DifferentialEquations.MatrixSystems
import UndergradKB.DifferentialEquations.ConstantCoefficients
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-! # Higher-order constant coefficients, undetermined coefficients, eigenvector decoupling (Lebl §2.3.2, §2.5.2, §3.9)

* `y⁽ⁿ⁾ + ∑ aₖ y⁽ᵏ⁾ = 0` with the characteristic polynomial `p(r) = rⁿ + ∑ aₖ rᵏ`. The derivatives of
  `e^{rx} q(x)` (`q` a polynomial) are `e^{rx} (T^j q)(x)` with `T = r + d/dx` acting on polynomials, so the equation
  becomes `p(T) q = 0`; a root of multiplicity `m` gives `p = (X - r₀)^m s` and `T - r₀ = d/dx` kills `x^k`, `k < m`.
* two cases of undetermined coefficients for `a y'' + b y' + c y = f`;
* decoupling `x' = A x + f` through `A = E D E⁻¹`, and exponential / cosine forcing of systems. -/

namespace UndergradKB.DifferentialEquations

open Polynomial Matrix Set

/-! ### Characteristic polynomial and the operator `T = r + d/dx` -/

/-- The characteristic polynomial `rⁿ + ∑ aₖ rᵏ` of `y⁽ⁿ⁾ + ∑ aₖ y⁽ᵏ⁾ = 0`. -/
noncomputable def hoc_charPoly {n : ℕ} (a : Fin n → ℝ) : ℝ[X] :=
  X ^ n + ∑ k : Fin n, C (a k) * X ^ (k : ℕ)

lemma hoc_charPoly_eval {n : ℕ} (a : Fin n → ℝ) (r : ℝ) :
    (hoc_charPoly a).eval r = r ^ n + ∑ k : Fin n, a k * r ^ (k : ℕ) := by
  simp [hoc_charPoly, eval_finsetSum]

/-- `q ↦ r q + q'` on polynomials: differentiation of `e^{rx} q(x)` divided by `e^{rx}`. -/
noncomputable def hoc_T (r : ℝ) : Module.End ℝ ℝ[X] :=
  r • LinearMap.id + Polynomial.derivative

lemma hoc_T_apply (r : ℝ) (q : ℝ[X]) : hoc_T r q = r • q + derivative q := by
  simp [hoc_T]

/-- The candidate derivative chain `x ↦ e^{rx} (T^j q)(x)`, `j = 0, …, n`. -/
noncomputable def hoc_chain (n : ℕ) (r : ℝ) (q : ℝ[X]) : Fin (n + 1) → ℝ → ℝ :=
  fun j x => Real.exp (r * x) * ((hoc_T r ^ (j : ℕ)) q).eval x

lemma hoc_hasDerivAt (r : ℝ) (s : ℝ[X]) (x : ℝ) :
    HasDerivAt (fun x => Real.exp (r * x) * s.eval x) (Real.exp (r * x) * (hoc_T r s).eval x) x := by
  have := (hasDerivAt_exp_mul' r x).mul (s.hasDerivAt x)
  convert this using 1
  rw [hoc_T_apply]
  simp only [eval_add, eval_smul, smul_eq_mul]
  ring

lemma hoc_chain_isDerivChain (n : ℕ) (r : ℝ) (q : ℝ[X]) : IsDerivChain univ (hoc_chain n r q) := by
  intro k t _
  have := hoc_hasDerivAt r ((hoc_T r ^ (k : ℕ)) q) t
  simp only [hoc_chain, Fin.val_succ, pow_succ', mul_apply_eq_comp]
  exact this

lemma hoc_chain_equation {n : ℕ} (a : Fin n → ℝ) (r : ℝ) (q : ℝ[X]) (x : ℝ) :
    hoc_chain n r q (Fin.last n) x + ∑ k : Fin n, a k * hoc_chain n r q k.castSucc x =
      Real.exp (r * x) * ((aeval (hoc_T r) (hoc_charPoly a)) q).eval x := by
  have h : (aeval (hoc_T r) (hoc_charPoly a)) q =
      (hoc_T r ^ n) q + ∑ k : Fin n, a k • (hoc_T r ^ (k : ℕ)) q := by
    simp [hoc_charPoly, map_sum, LinearMap.sum_apply, aeval_X_pow]
  rw [h]
  simp only [hoc_chain, Fin.val_last, Fin.val_castSucc, eval_add, eval_finsetSum, eval_smul, smul_eq_mul,
    mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => by ring

lemma hoc_solves_iff {n : ℕ} (a : Fin n → ℝ) (r : ℝ) (q : ℝ[X]) :
    SolvesLinN (fun j _ => a j) 0 univ (hoc_chain n r q) ↔
      ∀ x, ((aeval (hoc_T r) (hoc_charPoly a)) q).eval x = 0 := by
  constructor
  · intro h x
    have := h.2 x (mem_univ x)
    simp only [Pi.zero_apply] at this
    rw [hoc_chain_equation] at this
    exact (mul_eq_zero.1 this).resolve_left (Real.exp_pos _).ne'
  · intro h
    refine ⟨hoc_chain_isDerivChain n r q, fun x _ => ?_⟩
    simp only [Pi.zero_apply]
    rw [hoc_chain_equation, h x, mul_zero]

lemma hoc_T_pow_one (r : ℝ) (j : ℕ) : (hoc_T r ^ j) 1 = C (r ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', mul_apply_eq_comp, ih, hoc_T_apply, derivative_C, pow_succ', C_mul,
      smul_eq_C_mul, add_zero]

lemma hoc_aeval_one {n : ℕ} (a : Fin n → ℝ) (r : ℝ) :
    (aeval (hoc_T r) (hoc_charPoly a)) 1 = C ((hoc_charPoly a).eval r) := by
  have h : (aeval (hoc_T r) (hoc_charPoly a)) 1 =
      (hoc_T r ^ n) 1 + ∑ k : Fin n, a k • (hoc_T r ^ (k : ℕ)) 1 := by
    simp [hoc_charPoly, map_sum, LinearMap.sum_apply, aeval_X_pow]
  rw [h, hoc_charPoly_eval]
  simp [hoc_T_pow_one, map_sum, smul_eq_C_mul]

/-- The chain of `x^k e^{r₀x}`. -/
lemma hoc_chain_zero (n : ℕ) (r : ℝ) (k : ℕ) :
    hoc_chain n r (X ^ k) 0 = fun x => x ^ k * Real.exp (r * x) := by
  funext x
  simp [hoc_chain, mul_comm]

/-- **`e^{rx}` solves the constant-coefficient equation iff `r` is a root of the characteristic polynomial**
(Lebl, §2.3.2): a derivative chain `D` on `ℝ` with `D 0 = e^{rx}` solves `y⁽ⁿ⁾ + ∑ aₖ y⁽ᵏ⁾ = 0` iff
`rⁿ + ∑ aₖ rᵏ = 0`. (DE-064) -/
@[kb "lebldiffyqs2026" "§2.3.2 constant coefficients, p. 92"]
theorem hoc_exp_solves_iff {n : ℕ} (a : Fin n → ℝ) (r : ℝ) {D : Fin (n + 1) → ℝ → ℝ}
    (h0 : D 0 = fun x => Real.exp (r * x)) (hD : IsDerivChain univ D) :
    SolvesLinN (fun j _ => a j) 0 univ D ↔ r ^ n + ∑ k : Fin n, a k * r ^ (k : ℕ) = 0 := by
  have hc : hoc_chain n r 1 0 = fun x => Real.exp (r * x) := by
    funext x; simp [hoc_chain]
  have hDc : D = hoc_chain n r 1 := by
    funext j t
    have e1 := hD.iteratedDeriv_eq isOpen_univ j t (mem_univ t)
    have e2 := (hoc_chain_isDerivChain n r 1).iteratedDeriv_eq isOpen_univ j t (mem_univ t)
    rw [← e1, h0, ← hc]
    exact e2
  rw [hDc, hoc_solves_iff, ← hoc_charPoly_eval]
  constructor
  · intro h
    have := h 0
    rw [hoc_aeval_one] at this
    simpa using this
  · intro h x
    rw [hoc_aeval_one]
    simp [h]

/-- **Multiple roots** (Lebl, §2.3.2, Examples 2.3.4-2.3.5): if `r₀` is a root of multiplicity at least `m` of
`p(r) = rⁿ + ∑ aₖ rᵏ` (i.e. `(X - r₀)^m ∣ p`), then for every `k < m` the function `x^k e^{r₀x}`, together with its
derivatives (the chain `hoc_chain n r₀ (X^k)`, which are the iterated derivatives on `ℝ`), solves
`y⁽ⁿ⁾ + ∑ aₖ y⁽ᵏ⁾ = 0`. (DE-064) -/
@[kb "lebldiffyqs2026" "§2.3.2 constant coefficients, p. 93"]
theorem hoc_multiple_root_solves {n : ℕ} (a : Fin n → ℝ) (r₀ : ℝ) (m : ℕ)
    (hdvd : (X - C r₀) ^ m ∣ hoc_charPoly a) {k : ℕ} (hk : k < m) :
    SolvesLinN (fun j _ => a j) 0 univ (hoc_chain n r₀ (X ^ k)) ∧
      hoc_chain n r₀ (X ^ k) 0 = (fun x => x ^ k * Real.exp (r₀ * x)) ∧
      ∀ (j : Fin (n + 1)) (x : ℝ), iteratedDeriv j (fun x => x ^ k * Real.exp (r₀ * x)) x =
        hoc_chain n r₀ (X ^ k) j x := by
  have hc0 := hoc_chain_zero n r₀ k
  refine ⟨?_, hc0, ?_⟩
  · rw [hoc_solves_iff]
    obtain ⟨s, hs⟩ := hdvd
    have hD : aeval (hoc_T r₀) (X - C r₀) = Polynomial.derivative := by
      refine LinearMap.ext fun q => ?_
      simp [hoc_T_apply]
    have : (aeval (hoc_T r₀) (hoc_charPoly a)) (X ^ k) = 0 := by
      rw [hs, mul_comm, map_mul, map_pow (aeval (hoc_T r₀)), hD, mul_apply_eq_comp, pow_apply_eq_iterate,
        iterate_derivative_eq_zero (by simpa using hk)]
      simp
    intro x
    rw [this]; simp
  · intro j x
    have := (hoc_chain_isDerivChain n r₀ (X ^ k)).iteratedDeriv_eq isOpen_univ j x (mem_univ x)
    rw [hc0] at this
    exact this

/-- **A double root gives `x e^{r₀x}`** (Lebl, Example 2.3.4): if `(X - r₀)² ∣ p` then `x e^{r₀x}` and its
derivatives solve the equation. (DE-064) -/
@[kb "lebldiffyqs2026" "Example 2.3.4, p. 93"]
theorem hoc_double_root_solves {n : ℕ} (a : Fin n → ℝ) (r₀ : ℝ)
    (hdvd : (X - C r₀) ^ 2 ∣ hoc_charPoly a) :
    SolvesLinN (fun j _ => a j) 0 univ (hoc_chain n r₀ (X ^ 1)) ∧
      hoc_chain n r₀ (X ^ 1) 0 = (fun x => x * Real.exp (r₀ * x)) := by
  have := hoc_multiple_root_solves a r₀ 2 hdvd (k := 1) (by norm_num)
  refine ⟨this.1, ?_⟩
  simpa using this.2.1

/-! ### Independence of exponentials and the distinct-roots general solution -/

lemma hoc_exp_linIndep {n : ℕ} (r : Fin n → ℝ) (hr : Function.Injective r) :
    LinearIndependent ℝ (fun i (t : (univ : Set ℝ)) => Real.exp (r i * t)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h0 : ∀ t, ∑ i, c i * Real.exp (r i * t) = 0 := fun t => by
    have := congrFun hc ⟨t, trivial⟩
    simpa [Finset.sum_apply] using this
  have hj : ∀ j : ℕ, ∀ t, ∑ i, c i * r i ^ j * Real.exp (r i * t) = 0 := by
    intro j
    induction j with
    | zero => simpa using h0
    | succ j ih =>
      intro t
      have hd : HasDerivAt (fun t => ∑ i, c i * r i ^ j * Real.exp (r i * t))
          (∑ i, c i * r i ^ (j + 1) * Real.exp (r i * t)) t := by
        apply HasDerivAt.fun_sum
        intro i _
        have := (hasDerivAt_exp_mul' (r i) t).const_mul (c i * r i ^ j)
        convert this using 1
        ring
      have hz : (fun t => ∑ i, c i * r i ^ j * Real.exp (r i * t)) = fun _ => 0 := funext ih
      rw [hz] at hd
      exact hd.unique (hasDerivAt_const t 0)
  have hv : c ᵥ* Matrix.vandermonde r = 0 := by
    funext j
    have := hj j 0
    simpa [Matrix.vecMul, dotProduct, Matrix.vandermonde] using this
  have := Matrix.eq_zero_of_vecMul_eq_zero (Matrix.det_vandermonde_ne_zero_iff.2 hr) hv
  intro i
  exact congrFun this i

/-- **Distinct real roots** (Lebl, Theorem 2.3.3 with §2.3.2): if the characteristic polynomial
`p(r) = rⁿ + ∑ aₖ rᵏ` has `n` distinct real roots `r₁, …, rₙ`, then every solution `E` of
`y⁽ⁿ⁾ + ∑ aₖ y⁽ᵏ⁾ = 0` on `ℝ` (with its derivative chain) is `y = ∑ Cᵢ e^{rᵢ x}`, and its derivatives are
`y⁽ᵏ⁾ = ∑ Cᵢ rᵢᵏ e^{rᵢ x}`. (DE-064) -/
@[kb "lebldiffyqs2026" "Theorem 2.3.3, p. 92"]
theorem hoc_distinct_roots_general_solution {n : ℕ} (a : Fin n → ℝ) (r : Fin n → ℝ)
    (hr : Function.Injective r) (hroot : ∀ i, r i ^ n + ∑ k : Fin n, a k * r i ^ (k : ℕ) = 0)
    {E : Fin (n + 1) → ℝ → ℝ} (hE : SolvesLinN (fun j _ => a j) 0 univ E) :
    ∃ C : Fin n → ℝ, ∀ (k : Fin n) (t : ℝ),
      E k.castSucc t = ∑ i, C i * (r i ^ (k : ℕ) * Real.exp (r i * t)) := by
  have hD : ∀ i, SolvesLinN (fun j _ => a j) 0 univ (hoc_chain n (r i) 1) := by
    intro i
    rw [hoc_solves_iff]
    intro x
    rw [hoc_aeval_one, hoc_charPoly_eval, hroot i]
    simp
  have hli : LinearIndependent ℝ (fun i (t : (univ : Set ℝ)) => hoc_chain n (r i) 1 0 t) := by
    have : (fun i (t : (univ : Set ℝ)) => hoc_chain n (r i) 1 0 t) =
        fun i (t : (univ : Set ℝ)) => Real.exp (r i * t) := by
      funext i t; simp [hoc_chain]
    rw [this]
    exact hoc_exp_linIndep r hr
  obtain ⟨C, hC⟩ := linN_general_solution ordConnected_univ univ_nonempty (fun _ => continuousOn_const)
    hD hli hE
  refine ⟨C, fun k t => ?_⟩
  rw [hC k t (mem_univ t)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [hoc_chain, hoc_T_pow_one, mul_comm]

/-- **General solution for distinct real roots, in terms of `y`** (Lebl, §2.3.2): for `n ≥ 1`, every solution
satisfies `y(x) = C₁ e^{r₁ x} + ⋯ + Cₙ e^{rₙ x}`. (DE-064) -/
@[kb "lebldiffyqs2026" "§2.3.2 constant coefficients, p. 92"]
theorem hoc_distinct_roots_solution {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (r : Fin n → ℝ)
    (hr : Function.Injective r) (hroot : ∀ i, r i ^ n + ∑ k : Fin n, a k * r i ^ (k : ℕ) = 0)
    {E : Fin (n + 1) → ℝ → ℝ} (hE : SolvesLinN (fun j _ => a j) 0 univ E) :
    ∃ C : Fin n → ℝ, ∀ t : ℝ, E 0 t = ∑ i, C i * Real.exp (r i * t) := by
  obtain ⟨C, hC⟩ := hoc_distinct_roots_general_solution a r hr hroot hE
  refine ⟨C, fun t => ?_⟩
  have := hC ⟨0, hn⟩ t
  have e : (⟨0, hn⟩ : Fin n).castSucc = 0 := Fin.ext rfl
  rw [e] at this
  simpa using this

/-! ### Undetermined coefficients (Lebl §2.5.2) -/

/-- `y` is twice differentiable on `ℝ` and `a y'' + b y' + c y = f`. -/
def hoc_Solves2 (a b c : ℝ) (f y : ℝ → ℝ) : Prop :=
  ∀ x, DifferentiableAt ℝ y x ∧ DifferentiableAt ℝ (deriv y) x ∧
    a * deriv (deriv y) x + b * deriv y x + c * y x = f x

/-- **Exponential right-hand side** (Lebl, §2.5.2): if `aα² + bα + c ≠ 0` then
`y_p = e^{αx} / (aα² + bα + c)` solves `a y'' + b y' + c y = e^{αx}`. (DE-068) -/
@[kb "lebldiffyqs2026" "§2.5.2 undetermined coefficients, p. 105"]
theorem hoc_undetermined_exp (a b c α : ℝ) (h : a * α ^ 2 + b * α + c ≠ 0) :
    hoc_Solves2 a b c (fun x => Real.exp (α * x))
      (fun x => Real.exp (α * x) / (a * α ^ 2 + b * α + c)) := by
  set K := a * α ^ 2 + b * α + c with hK
  have h1 : ∀ x, HasDerivAt (fun x => Real.exp (α * x) / K) (α * Real.exp (α * x) / K) x :=
    fun x => (hasDerivAt_exp_mul' α x).div_const K
  have h2 : ∀ x, HasDerivAt (fun x => α * Real.exp (α * x) / K) (α * (α * Real.exp (α * x)) / K) x :=
    fun x => ((hasDerivAt_exp_mul' α x).const_mul α).div_const K
  have e1 : deriv (fun x => Real.exp (α * x) / K) = fun x => α * Real.exp (α * x) / K :=
    funext fun x => (h1 x).deriv
  intro x
  refine ⟨(h1 x).differentiableAt, ?_, ?_⟩
  · rw [e1]; exact (h2 x).differentiableAt
  · rw [e1, (h2 x).deriv]
    show a * (α * (α * Real.exp (α * x)) / K) + b * (α * Real.exp (α * x) / K) +
      c * (Real.exp (α * x) / K) = Real.exp (α * x)
    field_simp
    rw [hK]; ring

/-- The operator `Q ↦ a Q'' + b Q' + c Q` on polynomials. -/
noncomputable def hoc_L (a b c : ℝ) (Q : ℝ[X]) : ℝ[X] :=
  C a * derivative (derivative Q) + C b * derivative Q + C c * Q

lemma hoc_L_add (a b c : ℝ) (P Q : ℝ[X]) : hoc_L a b c (P + Q) = hoc_L a b c P + hoc_L a b c Q := by
  simp only [hoc_L, derivative_add]; ring

lemma hoc_L_coeff (a b c : ℝ) (Q : ℝ[X]) (i : ℕ) :
    (hoc_L a b c Q).coeff i = a * (Q.coeff (i + 1 + 1) * ((i + 1 : ℕ) + 1) * (i + 1)) +
      b * (Q.coeff (i + 1) * (i + 1)) + c * Q.coeff i := by
  simp [hoc_L, coeff_derivative, coeff_C_mul]

lemma hoc_poly_exists_aux (a b c : ℝ) (hc : c ≠ 0) (N : ℕ) :
    ∀ P : ℝ[X], (∀ i, N ≤ i → P.coeff i = 0) →
      ∃ Q : ℝ[X], hoc_L a b c Q = P ∧ ∀ i, N ≤ i → Q.coeff i = 0 := by
  induction N with
  | zero =>
    intro P hP
    have : P = 0 := by ext i; simpa using hP i (Nat.zero_le _)
    refine ⟨0, ?_, fun i _ => by simp⟩
    simp [this, hoc_L]
  | succ N ih =>
    intro P hP
    set l := P.coeff N / c with hl
    set Q0 : ℝ[X] := C l * X ^ N with hQ0
    have hQ0c : ∀ i, Q0.coeff i = if i = N then l else 0 := fun i => by
      rw [hQ0, coeff_C_mul_X_pow]
    have hP' : ∀ i, N ≤ i → (P - hoc_L a b c Q0).coeff i = 0 := by
      intro i hi
      rw [coeff_sub, hoc_L_coeff, hQ0c, hQ0c, hQ0c]
      rcases eq_or_lt_of_le hi with h | h
      · subst h
        have h2 : N + 1 + 1 ≠ N := by omega
        have h3 : N + 1 ≠ N := by omega
        have h4 : c * (P.coeff N / c) = P.coeff N := by field_simp
        simp [hl, h2, h4]
      · have h1 : i ≠ N := by omega
        have h2 : i + 1 ≠ N := by omega
        have h3 : i + 1 + 1 ≠ N := by omega
        rw [hP i (by omega)]
        simp [h1, h2, h3]
    obtain ⟨Q1, hQ1, hQ1c⟩ := ih _ hP'
    refine ⟨Q0 + Q1, ?_, ?_⟩
    · rw [hoc_L_add, hQ1]; ring
    · intro i hi
      rw [coeff_add, hQ0c, hQ1c i (by omega)]
      have : i ≠ N := by omega
      simp [this]

/-- **Polynomial right-hand side** (Lebl, §2.5.2): if `c ≠ 0`, for every polynomial `P` of degree `d` there is a
polynomial `Q` of the same degree `d` with `a Q'' + b Q' + c Q = P`; as functions on `ℝ`, `y = Q(x)` is then a
particular solution of `a y'' + b y' + c y = P(x)`. (DE-068) -/
@[kb "lebldiffyqs2026" "§2.5.2 undetermined coefficients, p. 105"]
theorem hoc_undetermined_poly (a b c : ℝ) (hc : c ≠ 0) (P : ℝ[X]) :
    ∃ Q : ℝ[X], Q.natDegree = P.natDegree ∧
      hoc_Solves2 a b c (fun x => P.eval x) (fun x => Q.eval x) := by
  obtain ⟨Q, hQ, hQc⟩ := hoc_poly_exists_aux a b c hc (P.natDegree + 1) P
    (fun i hi => coeff_eq_zero_of_natDegree_lt (by omega))
  have hle : Q.natDegree ≤ P.natDegree :=
    natDegree_le_iff_coeff_eq_zero.2 fun N hN => hQc N (by omega)
  have hge : P.natDegree ≤ Q.natDegree := by
    rw [← hQ]
    refine natDegree_le_iff_coeff_eq_zero.2 fun N hN => ?_
    rw [hoc_L_coeff, coeff_eq_zero_of_natDegree_lt hN, coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]
    simp
  refine ⟨Q, le_antisymm hle hge, fun x => ?_⟩
  have e1 : deriv (fun x => Q.eval x) = fun x => (derivative Q).eval x :=
    funext fun x => (Q.hasDerivAt x).deriv
  have e2 : deriv (fun x => (derivative Q).eval x) = fun x => (derivative (derivative Q)).eval x :=
    funext fun x => ((derivative Q).hasDerivAt x).deriv
  refine ⟨(Q.hasDerivAt x).differentiableAt, ?_, ?_⟩
  · rw [e1]; exact ((derivative Q).hasDerivAt x).differentiableAt
  · rw [e1, e2, ← hQ]
    simp [hoc_L]

/-! ### Eigenvector decoupling (Lebl §3.9) -/

lemma hoc_hasDerivAt_const_mulVec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) {g : ℝ → Fin n → ℝ}
    {g' : Fin n → ℝ} {t : ℝ} (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => M *ᵥ g s) (M *ᵥ g') t := by
  have := (matCLM n M).hasFDerivAt.comp_hasDerivAt t hg
  simpa [Function.comp_def] using this

/-- **Eigenvector decoupling** (Lebl, §3.9.1): if `A = E D E⁻¹` with `E` invertible and `D = diag(λ₁, …, λₙ)`, then
`x` solves `x' = A x + f` on `I` iff `ξ = E⁻¹ x` solves the decoupled scalar equations
`ξₖ' = λₖ ξₖ + (E⁻¹ f)ₖ`. (DE-109) -/
@[kb "lebldiffyqs2026" "Definition candidates D069-D070, p. 180"]
theorem hoc_eigen_decoupling {n : ℕ} {E A : Matrix (Fin n) (Fin n) ℝ} (hE : IsUnit E.det)
    {lam : Fin n → ℝ} (hA : A = E * diagonal lam * E⁻¹) {I : Set ℝ} (f x : ℝ → Fin n → ℝ) :
    (∀ t ∈ I, HasDerivAt x (A *ᵥ x t + f t) t) ↔
      ∀ k : Fin n, ∀ t ∈ I, HasDerivAt (fun s => (E⁻¹ *ᵥ x s) k)
        (lam k * (E⁻¹ *ᵥ x t) k + (E⁻¹ *ᵥ f t) k) t := by
  have hinv : ∀ v : Fin n → ℝ, E⁻¹ *ᵥ (A *ᵥ v) = diagonal lam *ᵥ (E⁻¹ *ᵥ v) := by
    intro v
    rw [hA, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 1
    calc E⁻¹ * (E * diagonal lam * E⁻¹) = (E⁻¹ * E) * diagonal lam * E⁻¹ := by simp only [mul_assoc]
      _ = diagonal lam * E⁻¹ := by rw [Matrix.nonsing_inv_mul _ hE, one_mul]
  have hAv : ∀ v : Fin n → ℝ, A *ᵥ v = E *ᵥ (diagonal lam *ᵥ (E⁻¹ *ᵥ v)) := by
    intro v
    rw [hA]
    simp [Matrix.mulVec_mulVec, mul_assoc]
  have hEE : ∀ v : Fin n → ℝ, E *ᵥ (E⁻¹ *ᵥ v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hE, Matrix.one_mulVec]
  constructor
  · intro h k t ht
    have h1 := hoc_hasDerivAt_const_mulVec E⁻¹ (h t ht)
    have h2 := (hasDerivAt_pi.1 h1) k
    convert h2 using 1
    rw [Matrix.mulVec_add, hinv, Pi.add_apply, Matrix.mulVec_diagonal]
  · intro h t ht
    have hξ : HasDerivAt (fun s => E⁻¹ *ᵥ x s)
        (diagonal lam *ᵥ (E⁻¹ *ᵥ x t) + E⁻¹ *ᵥ f t) t := by
      rw [hasDerivAt_pi]
      intro k
      rw [Pi.add_apply, Matrix.mulVec_diagonal]
      exact h k t ht
    have h3 := hoc_hasDerivAt_const_mulVec E hξ
    have hx : (fun s => E *ᵥ (E⁻¹ *ᵥ x s)) = x := funext fun s => hEE (x s)
    rw [hx] at h3
    convert h3 using 1
    rw [Matrix.mulVec_add, hEE, hAv]

/-! ### Systems with exponential or cosine forcing (Lebl §3.9) -/

lemma hoc_det_neg_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) :
    (A - α • (1 : Matrix (Fin n) (Fin n) ℝ)).det ≠ 0 ↔ (α • (1 : Matrix (Fin n) (Fin n) ℝ) - A).det ≠ 0 := by
  rw [← neg_sub, Matrix.det_neg]
  simp

/-- **Exponential forcing of a system** (Lebl, Example 3.9.2): if `(αI - A) c = b` then
`x_p(t) = e^{αt} c` satisfies `x_p' = A x_p + e^{αt} b`. (DE-110) -/
theorem hoc_exp_forcing_hasDerivAt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (b c : Fin n → ℝ)
    (hc : (α • (1 : Matrix (Fin n) (Fin n) ℝ) - A) *ᵥ c = b) (t : ℝ) :
    HasDerivAt (fun s => Real.exp (α * s) • c)
      (A *ᵥ (Real.exp (α * t) • c) + Real.exp (α * t) • b) t := by
  have hb : b = α • c - A *ᵥ c := by
    rw [← hc]; simp [Matrix.sub_mulVec, Matrix.smul_mulVec]
  have h := ((hasDerivAt_id' t).const_mul α).exp.smul_const c
  convert h using 1
  rw [hb, Matrix.mulVec_smul]
  ext i
  simp
  ring

/-- **Particular solution for exponential forcing** (Lebl, Example 3.9.2): for `x' = A x + e^{αt} b` with
`det (A - αI) ≠ 0` (`α` not an eigenvalue), there is a constant vector `c` with `(αI - A) c = b` and
`x_p = e^{αt} c` is a particular solution; consequently the solutions are exactly `x_c + x_p`. (DE-110) -/
@[kb "lebldiffyqs2026" "Example 3.9.2, p. 181"]
theorem hoc_exp_forcing_particular {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (b : Fin n → ℝ)
    (hdet : (A - α • (1 : Matrix (Fin n) (Fin n) ℝ)).det ≠ 0) :
    ∃ c : Fin n → ℝ, (α • (1 : Matrix (Fin n) (Fin n) ℝ) - A) *ᵥ c = b ∧
      (∀ t, HasDerivAt (fun s => Real.exp (α * s) • c)
        (A *ᵥ (Real.exp (α * t) • c) + Real.exp (α * t) • b) t) ∧
      ∀ x : ℝ → Fin n → ℝ, (∀ t, HasDerivAt x (A *ᵥ x t + Real.exp (α * t) • b) t) ↔
        ∀ t, HasDerivAt (x - fun s => Real.exp (α * s) • c) (A *ᵥ (x - fun s => Real.exp (α * s) • c) t) t := by
  have hd := (hoc_det_neg_iff A α).1 hdet
  have hu : IsUnit (α • (1 : Matrix (Fin n) (Fin n) ℝ) - A).det := isUnit_iff_ne_zero.2 hd
  have hc : (α • (1 : Matrix (Fin n) (Fin n) ℝ) - A) *ᵥ ((α • (1 : Matrix (Fin n) (Fin n) ℝ) - A)⁻¹ *ᵥ b) = b := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  refine ⟨_, hc, hoc_exp_forcing_hasDerivAt A α b _ hc, fun x => ?_⟩
  have := matrix_nonhomogeneous_iff (I := (univ : Set ℝ)) (P := fun _ => A)
    (f := fun t => Real.exp (α * t) • b)
    (xp := fun s => Real.exp (α * s) • ((α • (1 : Matrix (Fin n) (Fin n) ℝ) - A)⁻¹ *ᵥ b))
    (fun t _ => hoc_exp_forcing_hasDerivAt A α b _ hc t) x
  simpa using this

/-- **Cosine forcing of a second-order system** (Lebl, Example 3.9.3 and §3.9.3): if `(A + ω² I) c = -b` then
`x_p(t) = c cos ωt` satisfies `x_p' = v`, `v = -ω sin(ωt) c` and `v' = A x_p + b cos ωt`, i.e. `x_p'' = A x_p + b cos ωt`.
(DE-112) -/
theorem hoc_cos_forcing_hasDerivAt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) (b c : Fin n → ℝ)
    (hc : (A + ω ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ c = -b) (t : ℝ) :
    HasDerivAt (fun s => Real.cos (ω * s) • c) ((-ω * Real.sin (ω * t)) • c) t ∧
      HasDerivAt (fun s => (-ω * Real.sin (ω * s)) • c)
        (A *ᵥ (Real.cos (ω * t) • c) + Real.cos (ω * t) • b) t := by
  have hb : b = -(A *ᵥ c) - ω ^ 2 • c := by
    have h1 : A *ᵥ c + ω ^ 2 • c = -b := by
      rw [← hc]; simp [Matrix.add_mulVec, Matrix.smul_mulVec]
    have h2 : b = -(A *ᵥ c + ω ^ 2 • c) := by rw [h1, neg_neg]
    rw [h2]; abel
  constructor
  · have h := ((hasDerivAt_id' t).const_mul ω).cos.smul_const c
    convert h using 1
    ext i; simp only [Pi.smul_apply, smul_eq_mul]; ring
  · have h := (((hasDerivAt_id' t).const_mul ω).sin.const_mul (-ω)).smul_const c
    convert h using 1
    rw [hb, Matrix.mulVec_smul]
    ext i; simp; ring

/-- **Particular solution for cosine forcing** (Lebl, Example 3.9.3, §3.9.3): for `x'' = A x + b cos ωt` with
`det (A + ω² I) ≠ 0`, there is `c` with `(A + ω² I) c = -b`, and `x_p = c cos ωt` is a particular solution
(`x_p' = v`, `v' = A x_p + b cos ωt`). (DE-112) -/
@[kb "lebldiffyqs2026" "§3.9.3 second-order constant coefficients, p. 185"]
theorem hoc_cos_forcing_particular {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) (b : Fin n → ℝ)
    (hdet : (A + ω ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)).det ≠ 0) :
    ∃ c : Fin n → ℝ, (A + ω ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ c = -b ∧
      ∀ t, HasDerivAt (fun s => Real.cos (ω * s) • c) ((-ω * Real.sin (ω * t)) • c) t ∧
        HasDerivAt (fun s => (-ω * Real.sin (ω * s)) • c)
          (A *ᵥ (Real.cos (ω * t) • c) + Real.cos (ω * t) • b) t := by
  have hu : IsUnit (A + ω ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)).det := isUnit_iff_ne_zero.2 hdet
  have hc : (A + ω ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ
      ((A + ω ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹ *ᵥ (-b)) = -b := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  exact ⟨_, hc, hoc_cos_forcing_hasDerivAt A ω b _ hc⟩

end UndergradKB.DifferentialEquations
