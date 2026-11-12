import UndergradKB.DifferentialEquations.MatrixSystems
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Variation of parameters for systems (Lebl §3.9.2)

For a fundamental matrix `X(t)` of `x' = P(t) x` on an open interval `I`, the function
`xₚ(t) = X(t) ∫_{t₀}^t X(s)⁻¹ f(s) ds` is a particular solution of `x' = P(t) x + f(t)`. -/

namespace UndergradKB.DifferentialEquations

open Set Matrix MeasureTheory

variable {n : ℕ}

lemma continuousAt_of_cols {X : ℝ → Matrix (Fin n) (Fin n) ℝ} {t : ℝ}
    (h : ∀ j, ContinuousAt (colFun X j) t) : ContinuousAt X t :=
  continuousAt_pi.2 fun i => continuousAt_pi.2 fun j => continuousAt_pi.1 (h j) i

lemma continuousAt_inv_of_det {X : ℝ → Matrix (Fin n) (Fin n) ℝ} {t : ℝ} (hX : ContinuousAt X t)
    (hdet : (X t).det ≠ 0) : ContinuousAt (fun s => (X s)⁻¹) t := by
  have h : ContinuousAt Ring.inverse (X t).det := by
    rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hdet
  exact (continuousAt_matrix_inv (X t) h).comp hX

/-- **Variation of parameters** (Lebl, §3.9.2): let `P` and `f` be continuous on an open interval `I` and `X(t)`
a fundamental matrix of `x' = P(t) x` on `I` (its columns are solutions and `X(t)` is invertible on `I`, which holds
for linearly independent columns by `fundamental_matrix`). Then for `t₀ ∈ I`,
`xₚ(t) = X(t) ∫_{t₀}^t X(s)⁻¹ f(s) ds` solves `x' = P(t) x + f(t)` on `I`. -/
@[kb "lebldiffyqs2026" "§3.9.2 variable-coefficient variation of parameters, p. 184"]
theorem system_variation_of_parameters {I : Set ℝ} (hIo : IsOpen I) (hI : I.OrdConnected)
    {P : ℝ → Matrix (Fin n) (Fin n) ℝ} {f : ℝ → Fin n → ℝ} (hf : ContinuousOn f I)
    {X : ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hX : ∀ j, ∀ t ∈ I, HasDerivAt (colFun X j) (P t *ᵥ colFun X j t) t)
    (hdet : ∀ t ∈ I, (X t).det ≠ 0) {t₀ : ℝ} (ht₀ : t₀ ∈ I) :
    ∀ t ∈ I, HasDerivAt (fun s => X s *ᵥ ∫ u in t₀..s, (X u)⁻¹ *ᵥ f u)
      (P t *ᵥ (X t *ᵥ ∫ u in t₀..t, (X u)⁻¹ *ᵥ f u) + f t) t := by
  intro t ht
  set h : ℝ → Fin n → ℝ := fun u => (X u)⁻¹ *ᵥ f u with hh
  have hXc : ∀ s ∈ I, ContinuousAt X s := fun s hs =>
    continuousAt_of_cols fun j => (hX j s hs).continuousAt
  have hcont : ContinuousOn h I := by
    intro s hs
    have h1 := continuousAt_inv_of_det (hXc s hs) (hdet s hs)
    have h2 := (hf s hs).continuousAt (hIo.mem_nhds hs)
    have hm : Continuous fun p : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ) => p.1 *ᵥ p.2 :=
      continuous_fst.matrix_mulVec continuous_snd
    exact (hm.continuousAt.comp (h1.prodMk h2)).continuousWithinAt
  have hg : HasDerivAt (fun s => ∫ u in t₀..s, h u) (h t) t :=
    intervalIntegral.integral_hasDerivAt_right
      ((hcont.mono (hI.uIcc_subset ht₀ ht)).intervalIntegrable)
      (hcont.stronglyMeasurableAtFilter hIo t ht) (hcont.continuousAt (hIo.mem_nhds ht))
  have hsum : (fun s => X s *ᵥ ∫ u in t₀..s, h u) =
      fun s => ∑ j, (∫ u in t₀..s, h u) j • colFun X j s := by
    funext s; rw [mulVec_eq_sum_col]; rfl
  rw [hsum]
  have hd := HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
    (hasDerivAt_pi.1 hg j).smul (hX j t ht)
  convert hd using 1
  have hinv : X t *ᵥ h t = f t := by
    simp only [hh, Matrix.mulVec_mulVec]
    rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hdet t ht)), Matrix.one_mulVec]
  rw [Finset.sum_add_distrib, ← hinv, mulVec_eq_sum_col (X t) (h t), mulVec_eq_sum_col (X t),
    Matrix.mulVec_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mulVec_smul]
  rfl

end UndergradKB.DifferentialEquations
