import UndergradKB.DifferentialEquations.MatrixSystems
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Dimension.Finite

/-! # Second-order systems, and matrix exponential identities (Lebl, Chapter 3)

Second-order systems `x'' = A x` (and forced versions) are handled in the form "`x` has derivative `x'` and `x'`
has derivative `A x`", and reduced to the first-order system on `ℝⁿ × ℝⁿ` for uniqueness. Also the scalar
reduction of `y'' = f(t, y, y')` to a first-order system, and algebraic facts on `e^{tA}`. -/

namespace UndergradKB.DifferentialEquations

open Set Matrix NormedSpace

variable {n : ℕ}

/-- `(x, x')` is a solution of the second-order system `x'' = A x`. -/
def SecondOrderSol (A : Matrix (Fin n) (Fin n) ℝ) (x x' : ℝ → Fin n → ℝ) : Prop :=
  ∀ t, HasDerivAt x (x' t) t ∧ HasDerivAt x' (A *ᵥ x t) t

lemma sos_term {A : Matrix (Fin n) (Fin n) ℝ} {v : Fin n → ℝ} {ω : ℝ}
    (hv : A *ᵥ v = (-(ω ^ 2)) • v) (a b t : ℝ) :
    HasDerivAt (fun s => (a * Real.cos (ω * s) + b * Real.sin (ω * s)) • v)
      ((ω * (-a * Real.sin (ω * t) + b * Real.cos (ω * t))) • v) t ∧
    HasDerivAt (fun s => (ω * (-a * Real.sin (ω * s) + b * Real.cos (ω * s))) • v)
      (A *ᵥ ((a * Real.cos (ω * t) + b * Real.sin (ω * t)) • v)) t := by
  have hc := ((hasDerivAt_id' t).const_mul ω).cos
  have hs := ((hasDerivAt_id' t).const_mul ω).sin
  constructor
  · have h := (((hc.const_mul a).add (hs.const_mul b))).smul_const v
    convert h using 2
    simp; ring
  · have h := (((hs.const_mul (-a)).add (hc.const_mul b)).const_mul ω).smul_const v
    convert h using 1
    rw [Matrix.mulVec_smul, hv, smul_smul]
    congr 1; simp; ring

/-- **Undamped second-order systems, solutions** (DE-095, Lebl Theorem 3.6.1 (i)): if `A v = -ω² v`, then
`x(t) = (a cos ωt + b sin ωt) v` solves `x'' = A x`. -/
@[kb "lebldiffyqs2026" "Theorem 3.6.1, p. 154"]
theorem second_order_eigen_solution {A : Matrix (Fin n) (Fin n) ℝ} {v : Fin n → ℝ} {ω : ℝ}
    (hv : A *ᵥ v = (-(ω ^ 2)) • v) (a b : ℝ) :
    SecondOrderSol A (fun s => (a * Real.cos (ω * s) + b * Real.sin (ω * s)) • v)
      (fun s => (ω * (-a * Real.sin (ω * s) + b * Real.cos (ω * s))) • v) :=
  fun t => sos_term hv a b t

/-- **Zero eigenvalue** (DE-095, Lebl Theorem 3.6.1 (i)): if `A v = 0`, then `x(t) = (a + b t) v` solves
`x'' = A x`. -/
@[kb "lebldiffyqs2026" "Theorem 3.6.1, p. 154"]
theorem second_order_zero_eigen_solution {A : Matrix (Fin n) (Fin n) ℝ} {v : Fin n → ℝ}
    (hv : A *ᵥ v = 0) (a b : ℝ) :
    SecondOrderSol A (fun s => (a + b * s) • v) (fun _ => b • v) := by
  intro t
  constructor
  · have h := ((hasDerivAt_id' t).const_mul b |>.const_add a).smul_const v
    simpa using h
  · have : A *ᵥ ((a + b * t) • v) = 0 := by rw [Matrix.mulVec_smul, hv, smul_zero]
    rw [this]; exact hasDerivAt_const t _

/-- The first-order system on `ℝⁿ × ℝⁿ` attached to `x'' = A x`: `(u, w) ↦ (w, A u)`. -/
noncomputable def sosCLM (A : Matrix (Fin n) (Fin n) ℝ) :
    ((Fin n → ℝ) × (Fin n → ℝ)) →L[ℝ] ((Fin n → ℝ) × (Fin n → ℝ)) :=
  (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ)).prod
    ((matCLM n A).comp (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ)))

lemma sos_hasDerivAt {A : Matrix (Fin n) (Fin n) ℝ} {x x' : ℝ → Fin n → ℝ} (h : SecondOrderSol A x x')
    (t : ℝ) : HasDerivAt (fun s => (x s, x' s)) (sosCLM A (x t, x' t) + 0) t := by
  have := (h t).1.prodMk (h t).2
  simpa [sosCLM] using this

/-- **Uniqueness for second-order systems** (DE-095, Lebl Theorem 3.6.1 (ii)): two solutions of `x'' = A x` with
the same position and velocity at `t = 0` agree for all `t`. -/
@[kb "lebldiffyqs2026" "Theorem 3.6.1, p. 154"]
theorem second_order_unique {A : Matrix (Fin n) (Fin n) ℝ} {x x' y y' : ℝ → Fin n → ℝ}
    (hx : SecondOrderSol A x x') (hy : SecondOrderSol A y y') (h0 : x 0 = y 0) (h0' : x' 0 = y' 0) :
    ∀ t, x t = y t ∧ x' t = y' t := by
  intro t
  have := linear_unique (A := fun _ => sosCLM A) (I := univ) ordConnected_univ continuousOn_const
    (f := 0) (x := fun s => (x s, x' s)) (y := fun s => (y s, y' s))
    (fun t _ => by simpa using sos_hasDerivAt hx t) (fun t _ => by simpa using sos_hasDerivAt hy t)
    (mem_univ 0) (by simp [h0, h0']) t trivial
  exact Prod.mk.inj this

/-- **General solution of an undamped second-order system** (DE-095, Lebl Theorem 3.6.1 (iii)): if `A` has `n`
linearly independent eigenvectors `v_k` with eigenvalues `-ω_k²`, `ω_k > 0`, then every solution of `x'' = A x`
is `x(t) = ∑ₖ (a_k cos ω_k t + b_k sin ω_k t) v_k`. -/
@[kb "lebldiffyqs2026" "Theorem 3.6.1, p. 154"]
theorem second_order_general_solution {A : Matrix (Fin n) (Fin n) ℝ} {v : Fin n → Fin n → ℝ}
    {ω : Fin n → ℝ} (hω : ∀ k, 0 < ω k) (hv : ∀ k, A *ᵥ v k = (-(ω k ^ 2)) • v k)
    (hli : LinearIndependent ℝ v) {x x' : ℝ → Fin n → ℝ} (hx : SecondOrderSol A x x') :
    ∃ a b : Fin n → ℝ, ∀ t, x t = ∑ k, (a k * Real.cos (ω k * t) + b k * Real.sin (ω k * t)) • v k := by
  classical
  let B := basisOfLinearIndependentOfCardEqFinrank' v hli (by simp)
  have hB : ∀ k, B k = v k := fun k => by simp [B]
  refine ⟨fun k => B.repr (x 0) k, fun k => B.repr (x' 0) k / ω k, ?_⟩
  set a : Fin n → ℝ := fun k => B.repr (x 0) k
  set b : Fin n → ℝ := fun k => B.repr (x' 0) k / ω k
  let y : ℝ → Fin n → ℝ := fun s => ∑ k, (a k * Real.cos (ω k * s) + b k * Real.sin (ω k * s)) • v k
  let y' : ℝ → Fin n → ℝ := fun s =>
    ∑ k, (ω k * (-a k * Real.sin (ω k * s) + b k * Real.cos (ω k * s))) • v k
  have hy : SecondOrderSol A y y' := by
    intro t
    constructor
    · exact HasDerivAt.fun_sum (fun k _ => (sos_term (hv k) (a k) (b k) t).1)
    · have := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => (sos_term (hv k) (a k) (b k) t).2)
      convert this using 1
      simp [y, Matrix.mulVec_sum]
  have hy0 : y 0 = x 0 := by
    simp only [y, mul_zero, Real.cos_zero, Real.sin_zero, mul_one, add_zero]
    conv_rhs => rw [← B.sum_repr (x 0)]
    simp [hB, a]
  have hy0' : y' 0 = x' 0 := by
    simp only [y', mul_zero, Real.cos_zero, Real.sin_zero, neg_mul, mul_one]
    conv_rhs => rw [← B.sum_repr (x' 0)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hB]
    congr 1
    have := (hω k).ne'
    simp only [b]
    field_simp
    simp
  intro t
  exact ((second_order_unique hy hx hy0 hy0') t).1.symm

/-- The forced second-order system `x'' = A x + F cos ωt`, with velocity `x'`. -/
def ForcedSecondOrderSol (A : Matrix (Fin n) (Fin n) ℝ) (F : Fin n → ℝ) (ω : ℝ) (x x' : ℝ → Fin n → ℝ) :
    Prop :=
  ∀ t, HasDerivAt x (x' t) t ∧ HasDerivAt x' (A *ᵥ x t + Real.cos (ω * t) • F) t

/-- **Forced undamped systems** (DE-096, Lebl Example 3.6.3): if `(A + ω² I) c = -F` (which can be solved when
`ω` is not a natural frequency, i.e. `-ω²` is not an eigenvalue of `A`), then `x_p = c cos ωt` is a particular
solution of `x'' = A x + F cos ωt`, and the solutions are exactly `x_p` plus solutions of the homogeneous system
`x'' = A x` (for the pair of position and velocity). -/
@[kb "lebldiffyqs2026" "Example 3.6.3, p. 159"]
theorem forced_second_order {A : Matrix (Fin n) (Fin n) ℝ} {F c : Fin n → ℝ} {ω : ℝ}
    (hc : A *ᵥ c + ω ^ 2 • c = -F) :
    ForcedSecondOrderSol A F ω (fun s => Real.cos (ω * s) • c) (fun s => (-ω * Real.sin (ω * s)) • c) ∧
    ∀ x x' : ℝ → Fin n → ℝ, ForcedSecondOrderSol A F ω x x' ↔
      SecondOrderSol A (x - fun s => Real.cos (ω * s) • c)
        (x' - fun s => (-ω * Real.sin (ω * s)) • c) := by
  have hp : ForcedSecondOrderSol A F ω (fun s => Real.cos (ω * s) • c)
      (fun s => (-ω * Real.sin (ω * s)) • c) := by
    intro t
    have hcos := ((hasDerivAt_id' t).const_mul ω).cos
    have hsin := ((hasDerivAt_id' t).const_mul ω).sin
    constructor
    · have h := hcos.smul_const c
      convert h using 1
      simp [neg_mul, mul_comm]
    · have h := (hsin.const_mul (-ω)).smul_const c
      convert h using 1
      have hAc : A *ᵥ c = -F - ω ^ 2 • c := by rw [eq_sub_iff_add_eq]; exact hc
      rw [Matrix.mulVec_smul, hAc]
      simp only [smul_sub, smul_neg, smul_smul]
      ext i; simp; ring
  refine ⟨hp, fun x x' => ?_⟩
  constructor
  · intro h t
    refine ⟨(h t).1.sub (hp t).1, ?_⟩
    convert (h t).2.sub (hp t).2 using 1
    simp [Matrix.mulVec_sub]
  · intro h t
    refine ⟨?_, ?_⟩
    · simpa using (h t).1.add (hp t).1
    · convert (h t).2.add (hp t).2 using 1
      · ext s; simp
      · simp [Matrix.mulVec_sub]; abel

/-! ## Matrix exponential identities -/

/-- **Commuting matrices** (DE-102, Lebl Theorem 3.8.2): if `AB = BA` then `e^{A+B} = e^A e^B`. -/
@[kb "lebldiffyqs2026" "Theorem 3.8.2, p. 170"]
theorem exp_add_of_commute_book (A B : Matrix (Fin n) (Fin n) ℝ) (h : A * B = B * A) :
    exp (A + B) = exp A * exp B :=
  Matrix.exp_add_of_commute A B h

/-- **Conjugation** (DE-103, Lebl §3.8.3): for invertible `B`, `e^{B A B⁻¹} = B e^A B⁻¹`. -/
@[kb "lebldiffyqs2026" "§3.8.3 conjugation of the exponential, p. 171"]
theorem exp_conj_book (A B : Matrix (Fin n) (Fin n) ℝ) (hB : IsUnit B.det) :
    exp (B * A * B⁻¹) = B * exp A * B⁻¹ :=
  Matrix.exp_conj B A ((Matrix.isUnit_iff_isUnit_det B).mpr hB)

/-- **Diagonalization** (DE-105, Lebl Example 3.8.1 and §3.8.3): if `A = E D E⁻¹` with `E` invertible and
`D = diag(λ₁, …, λₙ)`, then `e^{tA} = E diag(e^{tλ₁}, …, e^{tλₙ}) E⁻¹`. -/
@[kb "lebldiffyqs2026" "Example 3.8.1, p. 172"]
theorem exp_diagonalizable (E : Matrix (Fin n) (Fin n) ℝ) (hE : IsUnit E.det) (μ : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A = E * diagonal μ * E⁻¹) (t : ℝ) :
    exp (t • A) = E * diagonal (fun i => Real.exp (t * μ i)) * E⁻¹ := by
  have h1 : t • A = E * diagonal (fun i => t * μ i) * E⁻¹ := by
    have hd : (diagonal fun i => t * μ i : Matrix (Fin n) (Fin n) ℝ) = t • diagonal μ := by
      rw [← Matrix.diagonal_smul]; rfl
    rw [hd, hA]
    simp
  rw [h1, exp_conj_book _ _ hE, Matrix.exp_diagonal]
  congr 3
  ext i
  simp [Real.exp_eq_exp_ℝ]

/-- **Nilpotent matrices** (DE-104, Lebl §3.8.1): if `B^k = 0` then `e^B = ∑_{j<k} B^j / j!`. -/
@[kb "lebldiffyqs2026" "§3.8.1 nilpotent matrices, p. 171"]
theorem exp_nilpotent (B : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (hB : B ^ k = 0) :
    exp B = ∑ j ∈ Finset.range k, ((j.factorial : ℝ)⁻¹) • B ^ j := by
  rw [exp_eq_tsum (𝕂 := ℝ)]
  refine tsum_eq_sum (fun j hj => ?_)
  have : B ^ j = 0 := by
    have hkj : k ≤ j := by simpa using hj
    rw [← Nat.sub_add_cancel hkj, pow_add, hB, mul_zero]
  rw [this, smul_zero]

/-- **Reduction to a first-order system** (DE-075, Lebl §3.1.3): `y'' = f(t, y, y')` holds for `y` with
derivative `v` exactly when `(y, v)` solves the first-order system `(y, v)' = (v, f(t, y, v))`. -/
@[kb "lebldiffyqs2026" "§3.1.3 changing to first-order systems, p. 122"]
theorem second_order_ode_iff_system (f : ℝ → ℝ → ℝ → ℝ) (y v : ℝ → ℝ) (t : ℝ) :
    (HasDerivAt y (v t) t ∧ HasDerivAt v (f t (y t) (v t)) t) ↔
      HasDerivAt (fun s => (y s, v s)) (v t, f t (y t) (v t)) t :=
  ⟨fun h => h.1.prodMk h.2, fun h => ⟨by exact (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t h,
    by exact (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t h⟩⟩

end UndergradKB.DifferentialEquations
