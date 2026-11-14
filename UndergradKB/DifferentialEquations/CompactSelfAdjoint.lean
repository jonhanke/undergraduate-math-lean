import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Topology.Sequences

/-! # Eigenvalues of compact symmetric operators

Two complements to Mathlib's spectral theorem for compact self-adjoint operators on a real Hilbert
space `E`:

* `finite_eigenvalues_abs_ge`: for every `ε > 0` there are only finitely many eigenvalues `μ` with
  `ε ≤ |μ|` (eigenvalues cannot accumulate away from `0`);
* `finiteDimensional_range_of_finite`: if there are only finitely many nonzero eigenvalues, then the
  range of the operator is finite-dimensional.

The first uses an orthonormal sequence of eigenvectors: the images `T eₙ = μₙ eₙ` lie in a compact
set, so a subsequence is Cauchy, contradicting `‖μₙ eₙ - μₘ eₘ‖² = μₙ² + μₘ² ≥ 2 ε²`.  The second
uses the spectral theorem `ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`. -/

namespace UndergradKB.DifferentialEquations
namespace CompactSA

open Module.End
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {T : E →L[ℝ] E}

omit [CompleteSpace E] in
/-- Symmetry of `T` in the form `⟪T x, y⟫ = ⟪x, T y⟫`. -/
lemma sym_apply (hT' : (T : E →ₗ[ℝ] E).IsSymmetric) (x y : E) :
    ⟪T x, y⟫ = ⟪x, T y⟫ := hT' x y

omit [CompleteSpace E] in
/-- Eigenvectors of a symmetric operator for distinct eigenvalues are orthogonal. -/
lemma inner_eq_zero_of_eigen (hT' : (T : E →ₗ[ℝ] E).IsSymmetric) {x y : E} {a b : ℝ}
    (hx : T x = a • x) (hy : T y = b • y) (hab : a ≠ b) : ⟪x, y⟫ = 0 := by
  have h := sym_apply hT' x y
  rw [hx, hy, real_inner_smul_left, real_inner_smul_right] at h
  have h2 : (a - b) * ⟪x, y⟫ = 0 := by linarith
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3) hab
  · exact h3

/-- A norm-one sequence of eigenvectors with distinct eigenvalues of absolute value at least
`ε > 0` is impossible for a compact symmetric operator. -/
lemma false_of_orthonormal_eigen (hT : IsCompactOperator T)
    (hT' : (T : E →ₗ[ℝ] E).IsSymmetric) {ε : ℝ} (hε : 0 < ε)
    (μ : ℕ → ℝ) (hμ : Function.Injective μ) (hμε : ∀ n, ε ≤ |μ n|)
    (e : ℕ → E) (he : ∀ n, ‖e n‖ = 1) (hTe : ∀ n, T (e n) = μ n • e n) : False := by
  have hK : IsCompact (closure ((T : E →ₗ[ℝ] E) '' Metric.closedBall (0 : E) 1)) :=
    IsCompactOperator.isCompact_closure_image_closedBall (f := (T : E →ₗ[ℝ] E)) hT 1
  have hmem : ∀ n, T (e n) ∈ closure ((T : E →ₗ[ℝ] E) '' Metric.closedBall (0 : E) 1) := fun n =>
    subset_closure ⟨e n, by simp [he n], rfl⟩
  obtain ⟨a, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  have hc := hlim.cauchySeq
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hc ε hε
  have hd := hN N le_rfl (N + 1) (Nat.le_succ N)
  simp only [Function.comp_apply, dist_eq_norm] at hd
  have hne : φ N ≠ φ (N + 1) := fun h => by
    have := hφ.injective h
    omega
  set m := φ N
  set n := φ (N + 1)
  have horth : ⟪e m, e n⟫ = 0 :=
    inner_eq_zero_of_eigen hT' (hTe m) (hTe n) (fun h => hne (hμ h))
  have hsq : ‖μ m • e m - μ n • e n‖ ^ 2 = μ m ^ 2 + μ n ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_left, real_inner_smul_right, horth, norm_smul,
      norm_smul, he, he]
    simp [sq_abs]
  have h1 : ε ^ 2 ≤ μ m ^ 2 := by
    rw [← sq_abs (μ m)]; exact pow_le_pow_left₀ hε.le (hμε m) 2
  have h2 : ε ^ 2 ≤ μ n ^ 2 := by
    rw [← sq_abs (μ n)]; exact pow_le_pow_left₀ hε.le (hμε n) 2
  rw [hTe m, hTe n] at hd
  have h0 := norm_nonneg (μ m • e m - μ n • e n)
  nlinarith

/-- Eigenvalues of a compact symmetric operator do not accumulate away from 0. -/
theorem finite_eigenvalues_abs_ge (hT : IsCompactOperator T)
    (hT' : (T : E →ₗ[ℝ] E).IsSymmetric) {ε : ℝ} (hε : 0 < ε) :
    {μ : ℝ | HasEigenvalue (T : Module.End ℝ E) μ ∧ ε ≤ |μ|}.Finite := by
  by_contra hinf
  have hinf' : {μ : ℝ | HasEigenvalue (T : Module.End ℝ E) μ ∧ ε ≤ |μ|}.Infinite := hinf
  let emb := hinf'.natEmbedding
  let μ : ℕ → ℝ := fun n => (emb n).1
  have hμ : Function.Injective μ := fun a b h => emb.injective (Subtype.ext h)
  have hμev : ∀ n, HasEigenvalue (T : Module.End ℝ E) (μ n) := fun n => (emb n).2.1
  have hμε : ∀ n, ε ≤ |μ n| := fun n => (emb n).2.2
  have hex : ∀ n, ∃ v : E, T v = μ n • v ∧ v ≠ 0 := fun n => by
    obtain ⟨v, hv1, hv2⟩ := (hμev n).exists_hasEigenvector
    exact ⟨v, mem_eigenspace_iff.mp hv1, hv2⟩
  choose v hv hv0 using hex
  refine false_of_orthonormal_eigen hT hT' hε μ hμ hμε (fun n => ‖v n‖⁻¹ • v n) ?_ ?_
  · intro n
    rw [norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hv0 n))
  · intro n
    rw [map_smul, hv n, smul_comm]

omit [CompleteSpace E] in
/-- The span of eigenspaces for nonzero eigenvalues is orthogonal to the kernel. -/
lemma inner_eq_zero_of_mem_ker (hT' : (T : E →ₗ[ℝ] E).IsSymmetric) {v u : E} (hv : T v = 0)
    {ν : ℝ} (hν : ν ≠ 0) (hu : u ∈ eigenspace (T : Module.End ℝ E) ν) : ⟪v, u⟫ = 0 := by
  have hu' : T u = ν • u := mem_eigenspace_iff.mp hu
  have h := sym_apply hT' v u
  rw [hv, hu', inner_zero_left, real_inner_smul_right] at h
  rcases mul_eq_zero.mp h.symm with h1 | h1
  · exact absurd h1 hν
  · exact h1

/-- If a compact symmetric operator has only finitely many nonzero eigenvalues, its range is
finite-dimensional. -/
theorem finiteDimensional_range_of_finite (hT : IsCompactOperator T)
    (hT' : (T : E →ₗ[ℝ] E).IsSymmetric)
    (hfin : {μ : ℝ | μ ≠ 0 ∧ HasEigenvalue (T : Module.End ℝ E) μ}.Finite) :
    FiniteDimensional ℝ (LinearMap.range (T : E →ₗ[ℝ] E)) := by
  -- the sum of the eigenspaces for nonzero eigenvalues
  let S : {μ : ℝ | μ ≠ 0 ∧ HasEigenvalue (T : Module.End ℝ E) μ} → Submodule ℝ E :=
    fun μ => eigenspace (T : Module.End ℝ E) μ.1
  have : Finite {μ : ℝ | μ ≠ 0 ∧ HasEigenvalue (T : Module.End ℝ E) μ} := hfin.to_subtype
  have : ∀ μ, FiniteDimensional ℝ (S μ) := fun μ =>
    ContinuousLinearMap.finite_dimensional_eigenspace hT μ.1 μ.2.1
  let V : Submodule ℝ E := ⨆ μ, S μ
  have : FiniteDimensional ℝ V := inferInstance
  have : CompleteSpace V := FiniteDimensional.complete ℝ V
  -- V is orthogonal to the kernel
  have hVker : ∀ v, T v = 0 → ∀ u ∈ V, ⟪v, u⟫ = 0 := by
    intro v hv
    have hle : V ≤ (Submodule.span ℝ {v})ᗮ := by
      refine iSup_le fun μ u hu => ?_
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      exact inner_eq_zero_of_mem_ker hT' hv μ.2.1 hu
    intro u hu
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hle hu)
  -- range ≤ V
  have hrange : LinearMap.range (T : E →ₗ[ℝ] E) ≤ V := by
    rintro g ⟨f, rfl⟩
    set w : E := (T : E →ₗ[ℝ] E) f - V.starProjection ((T : E →ₗ[ℝ] E) f) with hw
    have hwV : w ∈ Vᗮ := Submodule.sub_starProjection_mem_orthogonal _
    have hperp : ∀ μ, ∀ v ∈ eigenspace (T : Module.End ℝ E) μ, ⟪v, w⟫ = 0 := by
      intro μ v hv
      by_cases hμ0 : μ = 0
      · subst hμ0
        have hTv : T v = 0 := by simpa using mem_eigenspace_iff.mp hv
        have hPg : V.starProjection ((T : E →ₗ[ℝ] E) f) ∈ V := Submodule.starProjection_apply_mem _ _
        rw [hw, inner_sub_right, hVker v hTv _ hPg]
        have : ⟪v, T f⟫ = 0 := by
          rw [← sym_apply hT' v f, hTv, inner_zero_left]
        simpa using this
      · by_cases hev : HasEigenvalue (T : Module.End ℝ E) μ
        · have hvV : v ∈ V := by
            have : S ⟨μ, hμ0, hev⟩ ≤ V := le_iSup S ⟨μ, hμ0, hev⟩
            exact this hv
          exact (Submodule.mem_orthogonal V w).mp hwV v hvV
        · by_contra hne
          have hv0 : v ≠ 0 := by
            rintro rfl
            exact hne (inner_zero_left _)
          exact hev (hasEigenvalue_of_hasEigenvector ⟨hv, hv0⟩)
    have hw0 : w ∈ (⨆ μ, eigenspace (T : Module.End ℝ E) μ)ᗮ := by
      have hle : (⨆ μ, eigenspace (T : Module.End ℝ E) μ) ≤ (Submodule.span ℝ {w})ᗮ := by
        refine iSup_le fun μ v hv => ?_
        rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm]
        exact hperp μ v hv
      rw [Submodule.mem_orthogonal]
      intro u hu
      have := Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hle hu)
      rw [real_inner_comm]
      exact this
    rw [ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hT hT',
      Submodule.mem_bot] at hw0
    have : (T : E →ₗ[ℝ] E) f = V.starProjection ((T : E →ₗ[ℝ] E) f) := sub_eq_zero.mp hw0
    rw [this]
    exact Submodule.starProjection_apply_mem _ _
  exact Submodule.finiteDimensional_of_le hrange

end CompactSA
end UndergradKB.DifferentialEquations
