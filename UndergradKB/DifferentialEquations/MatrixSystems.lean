import UndergradKB.DifferentialEquations.LinearSystems
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Systems `x' = P(t) x + f(t)` in matrix form (Lebl, Chapter 3)

Vectors are `Fin n → ℝ`, matrices `Matrix (Fin n) (Fin n) ℝ`, and `P *ᵥ x` is the matrix-vector product. The
theorems are the matrix instances of `LinearSystems.lean` (uniqueness on an interval, superposition, fundamental
matrices), plus the constant-coefficient theory: the eigenvector method and the matrix exponential `e^{tA}`
(Mathlib's `NormedSpace.exp`). Statements avoid choosing a matrix norm: derivatives are taken only of
vector-valued functions; a norm on matrices is used only inside proofs. -/

namespace UndergradKB.DifferentialEquations

open Set Matrix NormedSpace

variable {n : ℕ}

/-- The matrix `M` as a continuous linear map `x ↦ M *ᵥ x`. -/
noncomputable def matCLM (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :=
  (LinearMap.toContinuousLinearMap : ((Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ≃ₗ[ℝ] _).toLinearMap ∘ₗ
    Matrix.toLin'.toLinearMap

@[simp] lemma matCLM_apply (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    matCLM n M x = M *ᵥ x := by
  simp [matCLM, Matrix.toLin'_apply]

lemma continuous_matCLM : Continuous (matCLM n) :=
  (matCLM n).continuous_of_finiteDimensional

lemma continuousOn_matCLM {P : ℝ → Matrix (Fin n) (Fin n) ℝ} {I : Set ℝ} (hP : ContinuousOn P I) :
    ContinuousOn (fun t => matCLM n (P t)) I :=
  continuous_matCLM.comp_continuousOn hP

/-- **Uniqueness for linear systems** (Lebl, Theorem 3.1.1 for linear systems; Theorem 3.3.2 setting): if `P` and
`f` are continuous on an interval `I` (only `P` is needed), two solutions of `x' = P(t) x + f(t)` on `I` that agree
at one point agree on `I`. -/
@[kb "lebldiffyqs2026" "Theorem 3.1.1, p. 125"]
theorem matrix_linear_unique {I : Set ℝ} (hI : I.OrdConnected) {P : ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hP : ContinuousOn P I) {f x y : ℝ → Fin n → ℝ}
    (hx : ∀ t ∈ I, HasDerivAt x (P t *ᵥ x t + f t) t) (hy : ∀ t ∈ I, HasDerivAt y (P t *ᵥ y t + f t) t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ I) (h0 : x t₀ = y t₀) : ∀ t ∈ I, x t = y t :=
  linear_unique hI (continuousOn_matCLM hP) (by simpa using hx) (by simpa using hy) ht₀ h0

/-- **Superposition** (Lebl, Theorem 3.3.1): linear combinations of solutions of `x' = P(t) x` are solutions. -/
@[kb "lebldiffyqs2026" "Theorem 3.3.1, p. 137"]
theorem matrix_superposition {I : Set ℝ} {P : ℝ → Matrix (Fin n) (Fin n) ℝ} {ι : Type*}
    (s : Finset ι) {x : ι → ℝ → Fin n → ℝ} (hx : ∀ i ∈ s, ∀ t ∈ I, HasDerivAt (x i) (P t *ᵥ x i t) t)
    (c : ι → ℝ) :
    ∀ t ∈ I, HasDerivAt (fun u => ∑ i ∈ s, c i • x i u) (P t *ᵥ ∑ i ∈ s, c i • x i t) t := by
  have := linear_superposition (A := fun t => matCLM n (P t)) s (by simpa using hx) c
  simpa [Matrix.mulVec_sum, Matrix.mulVec_smul] using this

/-- **Nonhomogeneous systems** (Lebl, Theorem 3.3.2): if `xₚ` solves `x' = P(t) x + f(t)`, the solutions are exactly
`x_c + xₚ` with `x_c` solving the homogeneous system. -/
@[kb "lebldiffyqs2026" "Theorem 3.3.2, p. 138"]
theorem matrix_nonhomogeneous_iff {I : Set ℝ} {P : ℝ → Matrix (Fin n) (Fin n) ℝ} {f xp : ℝ → Fin n → ℝ}
    (hp : ∀ t ∈ I, HasDerivAt xp (P t *ᵥ xp t + f t) t) (x : ℝ → Fin n → ℝ) :
    (∀ t ∈ I, HasDerivAt x (P t *ᵥ x t + f t) t) ↔
      ∀ t ∈ I, HasDerivAt (x - xp) (P t *ᵥ (x - xp) t) t := by
  have := linear_nonhomogeneous_iff (A := fun t => matCLM n (P t)) (I := I) (f := f)
    (by simpa using hp) x
  simpa using this

/-- **General solution from `n` independent solutions** (Lebl, §3.3, fundamental matrix): if `x₁, …, xₙ` are
linearly independent (as functions on `I`) solutions of `x' = P(t) x` with `P` continuous on the interval `I`, then
every solution is uniquely `c₁ x₁ + ⋯ + cₙ xₙ`. -/
@[kb "lebldiffyqs2026" "§3.3 fundamental matrix, p. 137"]
theorem matrix_general_solution {I : Set ℝ} (hI : I.OrdConnected) (hne : I.Nonempty)
    {P : ℝ → Matrix (Fin n) (Fin n) ℝ} (hP : ContinuousOn P I) {x : Fin n → ℝ → Fin n → ℝ}
    (hx : ∀ i, ∀ t ∈ I, HasDerivAt (x i) (P t *ᵥ x i t) t)
    (hli : LinearIndependent ℝ (fun i (t : I) => x i t)) {y : ℝ → Fin n → ℝ}
    (hy : ∀ t ∈ I, HasDerivAt y (P t *ᵥ y t) t) :
    ∃! c : Fin n → ℝ, ∀ t ∈ I, y t = ∑ i, c i • x i t :=
  linear_general_solution hI (continuousOn_matCLM hP) (by simpa using hx) hli (by simp)
    (by simpa using hy) hne

/-- The columns of a matrix-valued function: `colFun X j t = (X t)ⱼ`. -/
def colFun (X : ℝ → Matrix (Fin n) (Fin n) ℝ) (j : Fin n) (t : ℝ) : Fin n → ℝ := fun i => X t i j

lemma mulVec_eq_sum_col (M : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) :
    M *ᵥ c = ∑ j, c j • (fun i => M i j) := by
  ext i; simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

/-- **Fundamental matrix solution** (Lebl, §3.3): let `X(t)` be a fundamental matrix of `x' = P(t) x` on an
interval `I` (its columns are solutions, linearly independent as functions on `I`), `P` continuous on `I`. Then
`X(t)` is invertible for every `t ∈ I`, and every solution is `x(t) = X(t) c` for a unique constant vector `c`. -/
@[kb "lebldiffyqs2026" "§3.3 fundamental matrix, p. 137"]
theorem fundamental_matrix {I : Set ℝ} (hI : I.OrdConnected) (hne : I.Nonempty)
    {P : ℝ → Matrix (Fin n) (Fin n) ℝ} (hP : ContinuousOn P I) {X : ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hX : ∀ j, ∀ t ∈ I, HasDerivAt (colFun X j) (P t *ᵥ colFun X j t) t)
    (hli : LinearIndependent ℝ (fun j (t : I) => colFun X j t)) :
    (∀ t ∈ I, (X t).det ≠ 0) ∧
      ∀ y : ℝ → Fin n → ℝ, (∀ t ∈ I, HasDerivAt y (P t *ᵥ y t) t) →
        ∃! c : Fin n → ℝ, ∀ t ∈ I, y t = X t *ᵥ c := by
  constructor
  · intro t ht
    have h := linear_values_linearIndependent hI (continuousOn_matCLM hP) (by simpa using hX) hli ht
    have : LinearIndependent ℝ (X t).col := by
      convert h using 1
      ext j i; rfl
    exact ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.linearIndependent_col_iff_isUnit.mp this)).ne_zero
  · intro y hy
    have := matrix_general_solution hI hne hP hX hli hy
    simp only [mulVec_eq_sum_col]
    exact this

/-! ## Constant coefficients: eigenvectors and the matrix exponential -/

/-- **Eigenvector solutions** (Lebl, §3.4): if `A v = λ v` then `x(t) = v e^{λ t}` solves `x' = A x`. -/
@[kb "lebldiffyqs2026" "Theorem 3.4.1, p. 142"]
theorem eigen_solution {A : Matrix (Fin n) (Fin n) ℝ} {v : Fin n → ℝ} {μ : ℝ} (hv : A *ᵥ v = μ • v)
    (t : ℝ) : HasDerivAt (fun u => Real.exp (μ * u) • v) (A *ᵥ (Real.exp (μ * t) • v)) t := by
  have h := ((hasDerivAt_id' t).const_mul μ).exp.smul_const v
  convert h using 1
  rw [Matrix.mulVec_smul, hv, smul_smul]
  congr 1; ring

/-- **Eigenvalue method** (Lebl, Theorems 3.4.1 and 3.7.1): if the `n × n` matrix `A` has `n` linearly independent
eigenvectors `v₁, …, vₙ` with eigenvalues `λ₁, …, λₙ` (for instance `n` distinct real eigenvalues), then every
solution of `x' = A x` is `x(t) = c₁ v₁ e^{λ₁ t} + ⋯ + cₙ vₙ e^{λₙ t}` for unique constants. -/
@[kb "lebldiffyqs2026" "Theorem 3.7.1, p. 162"]
theorem eigen_general_solution {A : Matrix (Fin n) (Fin n) ℝ} {v : Fin n → Fin n → ℝ} {μ : Fin n → ℝ}
    (hv : ∀ i, A *ᵥ v i = μ i • v i) (hli : LinearIndependent ℝ v) {y : ℝ → Fin n → ℝ}
    (hy : ∀ t, HasDerivAt y (A *ᵥ y t) t) :
    ∃! c : Fin n → ℝ, ∀ t, y t = ∑ i, c i • (Real.exp (μ i * t) • v i) := by
  have hli' : LinearIndependent ℝ (fun i (t : (univ : Set ℝ)) => Real.exp (μ i * t) • v i) := by
    rw [Fintype.linearIndependent_iff] at hli ⊢
    intro c hc
    apply hli c
    have := congrFun hc ⟨0, trivial⟩
    simpa using this
  have := matrix_general_solution ordConnected_univ univ_nonempty (P := fun _ => A)
    continuousOn_const (x := fun i u => Real.exp (μ i * u) • v i)
    (fun i t _ => eigen_solution (hv i) t) hli' (fun t _ => hy t)
  simpa using this

/-- **Complex eigenvalues** (Lebl, Theorem 3.4.2): let `A` be real and `a + i b` an eigenvalue with eigenvector
`w + i u` (`w, u` real vectors), i.e. `A w = a w - b u` and `A u = b w + a u`. Then the real and imaginary parts of
`(w + i u) e^{(a + i b) t}`, namely `e^{at}(w cos bt - u sin bt)` and `e^{at}(w sin bt + u cos bt)`, solve
`x' = A x`. -/
@[kb "lebldiffyqs2026" "Theorem 3.4.2, p. 145"]
theorem complex_eigen_solutions {A : Matrix (Fin n) (Fin n) ℝ} {w u : Fin n → ℝ} {a b : ℝ}
    (hw : A *ᵥ w = a • w - b • u) (hu : A *ᵥ u = b • w + a • u) (t : ℝ) :
    HasDerivAt (fun s => Real.exp (a * s) • (Real.cos (b * s) • w - Real.sin (b * s) • u))
      (A *ᵥ (Real.exp (a * t) • (Real.cos (b * t) • w - Real.sin (b * t) • u))) t ∧
    HasDerivAt (fun s => Real.exp (a * s) • (Real.sin (b * s) • w + Real.cos (b * s) • u))
      (A *ᵥ (Real.exp (a * t) • (Real.sin (b * t) • w + Real.cos (b * t) • u))) t := by
  have he := ((hasDerivAt_id' t).const_mul a).exp
  have hc := ((hasDerivAt_id' t).const_mul b).cos
  have hs := ((hasDerivAt_id' t).const_mul b).sin
  constructor
  · have h := he.smul ((hc.smul_const w).sub (hs.smul_const u))
    convert h using 1
    rw [Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hw, hu]
    ext i; simp; ring
  · have h := he.smul ((hs.smul_const w).add (hc.smul_const u))
    convert h using 1
    rw [Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hw, hu]
    ext i; simp; ring

section Exp

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- `matCLM` as a continuous linear map for the operator norm on matrices (used in proofs only). -/
noncomputable def matCLM' (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :=
  LinearMap.toContinuousLinearMap (matCLM n)

lemma hasDerivAt_mulVec {M : ℝ → Matrix (Fin n) (Fin n) ℝ} {M' : Matrix (Fin n) (Fin n) ℝ}
    {g : ℝ → Fin n → ℝ} {g' : Fin n → ℝ} {t : ℝ} (hM : HasDerivAt M M' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => M s *ᵥ g s) (M' *ᵥ g t + M t *ᵥ g') t := by
  have h1 : HasDerivAt (fun s => matCLM' n (M s)) (matCLM' n M') t :=
    (matCLM' n).hasFDerivAt.comp_hasDerivAt t hM
  have := h1.clm_apply hg
  simpa [matCLM'] using this

lemma hasDerivAt_exp_smul (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => exp (s • A)) (A * exp (t • A)) t :=
  hasDerivAt_exp_smul_const' A t

/-- **The matrix exponential solves the system** (Lebl, Theorem 3.8.1): `x(t) = e^{tA} c` solves `x' = A x` with
`x(0) = c`. -/
@[kb "lebldiffyqs2026" "Theorem 3.8.1, p. 169"]
theorem exp_solution (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => exp (s • A) *ᵥ c) (A *ᵥ (exp (t • A) *ᵥ c)) t := by
  have := hasDerivAt_mulVec (hasDerivAt_exp_smul A t) (hasDerivAt_const t c)
  simpa [Matrix.mulVec_mulVec] using this

lemma continuous_exp_smul (A : Matrix (Fin n) (Fin n) ℝ) : Continuous fun s : ℝ => exp (s • A) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp_smul A t).continuousAt

end Exp

lemma exp_smul_mul_exp_neg_smul (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    exp (t • A) * exp ((-t) • A) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl A).smul_left t).smul_right (-t))]
  simp

/-- **Integrating factor for constant-coefficient systems** (Lebl, §3.9.1): for `f` continuous,
`x(t) = e^{tA} (c + ∫₀ᵗ e^{-sA} f(s) ds)` solves `x' = A x + f(t)` with `x(0) = c`, and every solution of
`x' = A x + f(t)` is of this form with `c = x(0)`. -/
@[kb "lebldiffyqs2026" "§3.9.1 integrating factor, p. 177"]
theorem integrating_factor_system (A : Matrix (Fin n) (Fin n) ℝ) {f : ℝ → Fin n → ℝ}
    (hf : Continuous f) (c : Fin n → ℝ) :
    (∀ t, HasDerivAt (fun s => exp (s • A) *ᵥ (c + ∫ u in (0 : ℝ)..s, exp ((-u) • A) *ᵥ f u))
      (A *ᵥ (exp (t • A) *ᵥ (c + ∫ u in (0 : ℝ)..t, exp ((-u) • A) *ᵥ f u)) + f t) t) ∧
    ∀ x : ℝ → Fin n → ℝ, (∀ t, HasDerivAt x (A *ᵥ x t + f t) t) →
      ∀ t, x t = exp (t • A) *ᵥ (x 0 + ∫ u in (0 : ℝ)..t, exp ((-u) • A) *ᵥ f u) := by
  have hg : Continuous fun u : ℝ => exp ((-u) • A) *ᵥ f u :=
    ((continuous_exp_smul A).comp continuous_neg).matrix_mulVec hf
  have key : ∀ c : Fin n → ℝ, ∀ t,
      HasDerivAt (fun s => exp (s • A) *ᵥ (c + ∫ u in (0 : ℝ)..s, exp ((-u) • A) *ᵥ f u))
        (A *ᵥ (exp (t • A) *ᵥ (c + ∫ u in (0 : ℝ)..t, exp ((-u) • A) *ᵥ f u)) + f t) t := by
    intro c t
    let _ := Matrix.linftyOpNormedAddCommGroup (m := Fin n) (n := Fin n) (α := ℝ)
    let _ := Matrix.linftyOpNormedRing (n := Fin n) (α := ℝ)
    let _ := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin n) (α := ℝ)
    have h1 := hasDerivAt_mulVec (hasDerivAt_exp_smul A t)
      ((hg.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add c)
    convert h1 using 1
    simp only [Matrix.mulVec_mulVec, exp_smul_mul_exp_neg_smul, Matrix.one_mulVec]
  refine ⟨key c, fun x hx t => ?_⟩
  have := matrix_linear_unique ordConnected_univ (P := fun _ => A) continuousOn_const (f := f)
    (x := x) (fun t _ => hx t) (fun t _ => key (x 0) t) (mem_univ 0) (by simp) t trivial
  exact this

/-- **Generalized eigenvectors** (Lebl, §3.7, defect one): if `(A - λ I) v₁ = 0` and `(A - λ I) v₂ = v₁`, then
`x(t) = (v₂ + v₁ t) e^{λ t}` solves `x' = A x` (together with the eigenvector solution `v₁ e^{λ t}`). -/
@[kb "lebldiffyqs2026" "§3.7 generalized eigenvector, p. 166"]
theorem generalized_eigen_solution {A : Matrix (Fin n) (Fin n) ℝ} {v₁ v₂ : Fin n → ℝ} {μ : ℝ}
    (h₁ : A *ᵥ v₁ = μ • v₁) (h₂ : A *ᵥ v₂ = μ • v₂ + v₁) (t : ℝ) :
    HasDerivAt (fun s => Real.exp (μ * s) • (v₂ + s • v₁))
      (A *ᵥ (Real.exp (μ * t) • (v₂ + t • v₁))) t := by
  have he := ((hasDerivAt_id' t).const_mul μ).exp
  have hl : HasDerivAt (fun s : ℝ => v₂ + s • v₁) v₁ t := by
    simpa using ((hasDerivAt_id' t).smul_const v₁).const_add v₂
  convert he.smul hl using 1
  rw [Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, h₁, h₂]
  ext i; simp; ring

/-- **General solution of `x' = A x`** (Lebl, Theorem 3.8.1): every solution of the constant-coefficient system
`x' = A x` is `x(t) = e^{tA} x(0)`; conversely these are solutions. -/
@[kb "lebldiffyqs2026" "Theorem 3.8.1, p. 169"]
theorem exp_general_solution (A : Matrix (Fin n) (Fin n) ℝ) {x : ℝ → Fin n → ℝ}
    (hx : ∀ t, HasDerivAt x (A *ᵥ x t) t) : ∀ t, x t = exp (t • A) *ᵥ x 0 := by
  intro t
  have := matrix_linear_unique ordConnected_univ (P := fun _ => A) continuousOn_const (f := 0)
    (x := x) (y := fun s => exp (s • A) *ᵥ x 0) (fun t _ => by simpa using hx t)
    (fun t _ => by simpa using exp_solution A (x 0) t) (mem_univ 0) (by simp) t trivial
  exact this

/-- **`e^{tA}` from any fundamental matrix** (Lebl, §3.8.4): if `X(t)` is a fundamental matrix solution of
`x' = A x` (its columns solve the system and `X(0)` is invertible), then `e^{tA} = X(t) X(0)⁻¹`. -/
@[kb "lebldiffyqs2026" "§3.8.4 fundamental matrix solutions, p. 173"]
theorem exp_eq_fundamental (A : Matrix (Fin n) (Fin n) ℝ) {X : ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hX : ∀ j t, HasDerivAt (colFun X j) (A *ᵥ colFun X j t) t) (h0 : (X 0).det ≠ 0) (t : ℝ) :
    exp (t • A) = X t * (X 0)⁻¹ := by
  have hcol : ∀ j, colFun X j t = exp (t • A) *ᵥ colFun X j 0 := fun j => exp_general_solution A (hX j) t
  have hXt : X t = exp (t • A) * X 0 := by
    ext i j
    have := congrFun (hcol j) i
    simpa [colFun, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have hu : IsUnit (X 0).det := isUnit_iff_ne_zero.mpr h0
  rw [hXt, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

end UndergradKB.DifferentialEquations
