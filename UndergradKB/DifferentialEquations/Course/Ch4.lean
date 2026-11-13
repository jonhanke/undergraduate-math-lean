import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import UndergradKB.Common.Attr

/-!
# Lebl, Notes on Diffy Qs, Chapter 4 (Fourier series and PDEs): course layer

Thin wrappers around Mathlib stating the preliminary facts of the chapter in the book's terms.
-/

namespace UndergradKB.DifferentialEquations.Course.Ch4

open scoped RealInnerProductSpace

/-- Lebl §4.1 symmetric matrix (DE-116). A matrix equal to its transpose has
`A i j = A j i` for all entries. -/
@[kb "lebldiffyqs2026" "§4.1 symmetric matrix, p. 193"]
theorem lebl_symmetric_matrix_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    A.IsSymm ↔ ∀ i j, A i j = A j i := by
  constructor
  · intro h i j
    exact (congrFun (congrFun h.eq i) j).symm
  · intro h
    ext i j
    exact (h j i)

/-- Lebl §4.2 periodic function (DE-119). `f` is `P`-periodic iff `f (t + P) = f t` for all `t`. -/
@[kb "lebldiffyqs2026" "§4.2 periodic function, p. 198"]
theorem lebl_periodic_iff (f : ℝ → ℝ) (P : ℝ) :
    Function.Periodic f P ↔ ∀ t, f (t + P) = f t :=
  Iff.rfl

/-- Lebl §4.2 decomposition in orthogonal vectors (DE-121). A vector decomposes along an
orthonormal basis `w` with coefficients `⟨w i, v⟩` (the orthonormal case, where
`⟨w i, w i⟩ = 1`). -/
@[kb "lebldiffyqs2026" "§4.2 decomposition in orthogonal vectors, p. 199"]
theorem lebl_orthonormal_decomposition {n : ℕ} (w : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (v : EuclideanSpace ℝ (Fin n)) :
    ∑ i, ⟪w i, v⟫ • w i = v :=
  w.sum_repr' v

/-- Lebl Theorem 4.3.1 (DE-129), Mathlib's mean-square form: for a square-integrable function on the circle
`ℝ/Tℤ` the Fourier series converges to `f` in `L²`. (Pointwise convergence for `C¹` functions:
`UndergradKB.DifferentialEquations.fourier_series_C1`.) -/
@[kb "lebldiffyqs2026" "Theorem 4.3.1, p. 211"]
theorem lebl_fourier_series_L2 {T : ℝ} [Fact (0 < T)] (f : MeasureTheory.Lp ℂ 2 (@AddCircle.haarAddCircle T _)) :
    HasSum (fun i => fourierCoeff f i • fourierLp 2 i) f :=
  hasSum_fourier_series_L2 f

/-- Lebl Theorem 4.3.1 (DE-129), Mathlib's pointwise form: if the Fourier coefficients of a continuous function
on the circle are summable, its Fourier series converges to it at every point. -/
@[kb "lebldiffyqs2026" "Theorem 4.3.1, p. 211"]
theorem lebl_fourier_series_of_summable {T : ℝ} [Fact (0 < T)] {f : C(AddCircle T, ℂ)}
    (h : Summable (fourierCoeff f)) (x : AddCircle T) :
    HasSum (fun i => fourierCoeff f i • fourier i x) (f x) :=
  has_pointwise_sum_fourier_series_of_summable h x

/-- Lebl Theorem 5.1.4 (DE-158), the Fourier case of eigenfunction expansions: Parseval's identity
`∑ |cₙ|² = ∫ |f|²` for the orthonormal basis `e^{2π i n x / T}`. -/
@[kb "lebldiffyqs2026" "Theorem 5.1.4, p. 279"]
theorem lebl_parseval {T : ℝ} [Fact (0 < T)] (f : MeasureTheory.Lp ℂ 2 (@AddCircle.haarAddCircle T _)) :
    ∑' i : ℤ, ‖fourierCoeff f i‖ ^ 2 = ∫ t : AddCircle T, ‖f t‖ ^ 2 ∂AddCircle.haarAddCircle :=
  tsum_sq_fourierCoeff f

/-- Lebl §4.9 harmonic functions (DE-148): the real part of a complex-analytic function is harmonic
(`u_xx + u_yy = 0`). -/
@[kb "lebldiffyqs2026" "§4.9 Laplacian, Laplace equation, harmonic function, p. 258"]
theorem lebl_harmonic_re {f : ℂ → ℂ} {z : ℂ} (h : AnalyticAt ℂ f z) :
    InnerProductSpace.HarmonicAt (fun w => (f w).re) z :=
  h.harmonicAt_re

end UndergradKB.DifferentialEquations.Course.Ch4
