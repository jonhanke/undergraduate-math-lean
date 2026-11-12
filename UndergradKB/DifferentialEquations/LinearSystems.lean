import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import UndergradKB.Common.Attr

/-! # Linear systems `x' = A(t) x + f(t)`: uniqueness, superposition, general solution

The solution theory of linear equations (Lebl, *Notes on Diffy Qs*, §2.1, §2.3, §3.3) in a finite-dimensional
real normed space `E` (the book's `ℝⁿ`), with a coefficient `A(t)` that is a continuous family of linear maps on an
interval `I`. Everything is reduced to one statement, `linear_eq_zero_of_eq_zero`: a solution of the homogeneous
system that vanishes at one point of the interval vanishes on the whole interval (Mathlib's Gronwall uniqueness
`ODE_solution_unique_of_mem_Icc_right`, applied on compact subintervals where `‖A(t)‖` is bounded).
Scalar equations of order two and `n` (`SecondOrderLinear.lean`) and matrix systems (`MatrixSystems.lean`) are
special cases. -/

namespace UndergradKB.DifferentialEquations

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Uniqueness core.** On an interval `I`, a solution of `x' = A(t) x` with `A` continuous on `I` that vanishes
at one point `t₀ ∈ I` vanishes on all of `I`. -/
theorem linear_eq_zero_of_eq_zero {I : Set ℝ} (hI : I.OrdConnected) {A : ℝ → E →L[ℝ] E}
    (hA : ContinuousOn A I) {x : ℝ → E} (hx : ∀ t ∈ I, HasDerivAt x (A t (x t)) t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ I) (h0 : x t₀ = 0) : ∀ t ∈ I, x t = 0 := by
  intro t ht
  have hJ : uIcc t₀ t ⊆ I := hI.uIcc_subset ht₀ ht
  obtain ⟨K, hK⟩ := isCompact_uIcc.exists_bound_of_continuousOn (hA.mono hJ)
  have hlip : ∀ s ∈ uIcc t₀ t, LipschitzOnWith (Real.toNNReal K) (fun y => A s y) univ := by
    intro s hs
    refine ((A s).lipschitzWith.weaken ?_).lipschitzOnWith
    rw [← Real.toNNReal_coe (r := ‖A s‖₊), coe_nnnorm]
    exact Real.toNNReal_le_toNNReal (hK s hs)
  have hcont : ContinuousOn x (uIcc t₀ t) := fun s hs => (hx s (hJ hs)).continuousAt.continuousWithinAt
  have hz : ∀ s, HasDerivAt (fun _ : ℝ => (0 : E)) (A s ((fun _ : ℝ => (0 : E)) s)) s := by
    intro s; simpa using hasDerivAt_const s (0 : E)
  rcases le_total t₀ t with h | h
  · have hsub : Icc t₀ t ⊆ uIcc t₀ t := Icc_subset_uIcc
    have := ODE_solution_unique_of_mem_Icc_right (v := fun s y => A s y) (s := fun _ => univ)
      (g := fun _ => (0 : E)) (fun s hs => hlip s (hsub (Ico_subset_Icc_self hs)))
      (hcont.mono hsub) (fun s hs => (hx s (hJ (hsub (Ico_subset_Icc_self hs)))).hasDerivWithinAt)
      (fun _ _ => trivial) continuousOn_const (fun s _ => (hz s).hasDerivWithinAt)
      (fun _ _ => trivial) h0
    exact this ⟨h, le_rfl⟩
  · have hsub : Icc t t₀ ⊆ uIcc t₀ t := Icc_subset_uIcc'
    have := ODE_solution_unique_of_mem_Icc_left (v := fun s y => A s y) (s := fun _ => univ)
      (g := fun _ => (0 : E)) (fun s hs => hlip s (hsub (Ioc_subset_Icc_self hs)))
      (hcont.mono hsub) (fun s hs => (hx s (hJ (hsub (Ioc_subset_Icc_self hs)))).hasDerivWithinAt)
      (fun _ _ => trivial) continuousOn_const (fun s _ => (hz s).hasDerivWithinAt)
      (fun _ _ => trivial) h0
    exact this ⟨le_rfl, h⟩

/-- **Uniqueness for the linear initial value problem** (the uniqueness half of Lebl, Theorems 2.1.2, 2.3.2 and of
Picard's theorem 3.1.1 for linear systems): two solutions of `x' = A(t) x + f(t)` on an interval `I`, with `A`
continuous on `I`, that agree at one point of `I` agree on all of `I`. -/
@[kb "lebldiffyqs2026" "§3.3, p. 137"]
theorem linear_unique {I : Set ℝ} (hI : I.OrdConnected) {A : ℝ → E →L[ℝ] E}
    (hA : ContinuousOn A I) {f x y : ℝ → E} (hx : ∀ t ∈ I, HasDerivAt x (A t (x t) + f t) t)
    (hy : ∀ t ∈ I, HasDerivAt y (A t (y t) + f t) t) {t₀ : ℝ} (ht₀ : t₀ ∈ I)
    (h0 : x t₀ = y t₀) : ∀ t ∈ I, x t = y t := by
  have := linear_eq_zero_of_eq_zero hI hA (x := x - y)
    (fun t ht => by convert (hx t ht).sub (hy t ht) using 1; simp) ht₀ (by simp [h0])
  intro t ht
  exact sub_eq_zero.mp (this t ht)

/-- **Superposition** for linear homogeneous systems (Lebl, Theorem 3.3.1): a linear combination of solutions of
`x' = A(t) x` is a solution. -/
@[kb "lebldiffyqs2026" "Theorem 3.3.1, p. 137"]
theorem linear_superposition {I : Set ℝ} {A : ℝ → E →L[ℝ] E} {ι : Type*} (s : Finset ι)
    {x : ι → ℝ → E} (hx : ∀ i ∈ s, ∀ t ∈ I, HasDerivAt (x i) (A t (x i t)) t) (c : ι → ℝ) :
    ∀ t ∈ I, HasDerivAt (fun u => ∑ i ∈ s, c i • x i u) (A t (∑ i ∈ s, c i • x i t)) t := by
  intro t ht
  have := HasDerivAt.fun_sum (u := s) (fun i hi => (hx i hi t ht).const_smul (c i))
  simpa [map_sum, map_smul] using this

/-- **Nonhomogeneous systems** (Lebl, Theorem 3.3.2): if `xₚ` solves `x' = A(t) x + f(t)` on `I`, then the solutions
of the nonhomogeneous system are exactly `x_c + xₚ` with `x_c` a solution of the homogeneous system. -/
@[kb "lebldiffyqs2026" "Theorem 3.3.2, p. 138"]
theorem linear_nonhomogeneous_iff {I : Set ℝ} {A : ℝ → E →L[ℝ] E} {f xp : ℝ → E}
    (hp : ∀ t ∈ I, HasDerivAt xp (A t (xp t) + f t) t) (x : ℝ → E) :
    (∀ t ∈ I, HasDerivAt x (A t (x t) + f t) t) ↔
      ∀ t ∈ I, HasDerivAt (x - xp) (A t ((x - xp) t)) t := by
  constructor
  · intro hx t ht
    convert (hx t ht).sub (hp t ht) using 1; simp
  · intro hx t ht
    convert (hx t ht).add (hp t ht) using 1
    · ext u; simp
    · simp; abel

/-- Values at one time of linearly independent solutions are linearly independent (the step behind the
nonvanishing of the Wronskian, Lebl §2.1 and §3.3). -/
theorem linear_values_linearIndependent {I : Set ℝ} (hI : I.OrdConnected) {A : ℝ → E →L[ℝ] E}
    (hA : ContinuousOn A I) {ι : Type*} [Fintype ι] {x : ι → ℝ → E}
    (hx : ∀ i, ∀ t ∈ I, HasDerivAt (x i) (A t (x i t)) t)
    (hli : LinearIndependent ℝ (fun i (t : I) => x i t)) {t₀ : ℝ} (ht₀ : t₀ ∈ I) :
    LinearIndependent ℝ (fun i => x i t₀) := by
  classical
  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro c hc
  apply hli c
  have := linear_eq_zero_of_eq_zero hI hA
    (linear_superposition (A := A) Finset.univ (fun i _ => hx i) c) ht₀ (by simpa using hc)
  funext t
  simpa using this t t.2

/-- **General solution of a linear homogeneous system** (Lebl, §3.3 and Definition of a fundamental matrix, p. 137;
also Theorems 2.1.3 and 2.3.3 for scalar equations): if `x₁, …, xₙ` are `n = dim E` linearly independent solutions
of `x' = A(t) x` on an interval `I` (with `A` continuous on `I`), then every solution on `I` is
`c₁ x₁ + ⋯ + cₙ xₙ` for unique constants `cᵢ`. -/
@[kb "lebldiffyqs2026" "§3.3 fundamental matrix, p. 137"]
theorem linear_general_solution [FiniteDimensional ℝ E] {I : Set ℝ} (hI : I.OrdConnected)
    {A : ℝ → E →L[ℝ] E} (hA : ContinuousOn A I) {ι : Type*} [Fintype ι] {x : ι → ℝ → E}
    (hx : ∀ i, ∀ t ∈ I, HasDerivAt (x i) (A t (x i t)) t)
    (hli : LinearIndependent ℝ (fun i (t : I) => x i t)) (hcard : Fintype.card ι = Module.finrank ℝ E)
    {y : ℝ → E} (hy : ∀ t ∈ I, HasDerivAt y (A t (y t)) t) (hne : I.Nonempty) :
    ∃! c : ι → ℝ, ∀ t ∈ I, y t = ∑ i, c i • x i t := by
  classical
  obtain ⟨t₀, ht₀⟩ := hne
  have hli0 := linear_values_linearIndependent hI hA hx hli ht₀
  let b := basisOfLinearIndependentOfCardEqFinrank' _ hli0 hcard
  have hb : ∀ i, b i = x i t₀ := fun i => by simp [b, basisOfLinearIndependentOfCardEqFinrank']
  refine ⟨fun i => b.repr (y t₀) i, ?_, ?_⟩
  · have hsum : y t₀ = ∑ i, b.repr (y t₀) i • x i t₀ := by
      conv_lhs => rw [← b.sum_repr (y t₀)]
      simp [hb]
    intro t ht
    have hs := linear_superposition (A := A) Finset.univ (fun i _ => hx i) (fun i => b.repr (y t₀) i)
    exact linear_unique hI hA (f := 0) (y := fun u => ∑ i, b.repr (y t₀) i • x i u)
      (by simpa using hy) (fun t ht => by simpa using hs t ht) ht₀ hsum t ht
  · intro c hc
    have h1 := hc t₀ ht₀
    funext i
    show c i = b.repr (y t₀) i
    have : y t₀ = ∑ i, c i • b i := by simpa [hb] using h1
    rw [this, b.repr_sum_self]

end UndergradKB.DifferentialEquations
