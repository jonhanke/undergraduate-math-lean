import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Asymptotics.Lemmas
import UndergradKB.Common.Attr

/-! # Standard non-holomorphic functions (rows CX-027)

Complex conjugation is nowhere complex differentiable, and `z ↦ (conj z)^2` is complex
differentiable at the origin only.  The argument restricts a complex derivative to the real axis
and to the imaginary axis; the two one-sided derivatives must agree, and they do not. -/

namespace UndergradKB.ComplexAnalysis

open Complex Asymptotics Filter ComplexConjugate

lemma hasDerivAt_ofReal' (x : ℝ) : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := by
  simpa using HasDerivAt.ofReal_comp (hasDerivAt_id x)

/-- A complex derivative restricts to the real direction. -/
lemma hasDerivAt_real_direction {f : ℂ → ℂ} {c z : ℂ} (hf : HasDerivAt f c z) :
    HasDerivAt (fun t : ℝ => f (z + t)) c 0 := by
  have h1 : HasDerivAt (fun t : ℝ => z + (t : ℂ)) 1 0 := (hasDerivAt_ofReal' 0).const_add z
  have := HasDerivAt.scomp_of_eq (x := (0 : ℝ)) (h := fun t : ℝ => z + (t : ℂ)) hf h1 (by simp)
  simpa [Function.comp_def] using this

/-- A complex derivative restricts to the imaginary direction, with a factor `I`. -/
lemma hasDerivAt_imag_direction {f : ℂ → ℂ} {c z : ℂ} (hf : HasDerivAt f c z) :
    HasDerivAt (fun t : ℝ => f (z + t * I)) (I * c) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => z + (t : ℂ) * I) I 0 := by
    simpa using ((hasDerivAt_ofReal' 0).mul_const I).const_add z
  have := HasDerivAt.scomp_of_eq (x := (0 : ℝ)) (h := fun t : ℝ => z + (t : ℂ) * I) hf h1 (by simp)
  simpa [Function.comp_def] using this

/-- Beck Example 2.2.4 (CX-027): complex conjugation has no complex derivative at any point. -/
@[kb "beck2025" "Example 2.2.4, p. 37"]
theorem conj_not_differentiableAt (z : ℂ) : ¬ DifferentiableAt ℂ (fun w : ℂ => conj w) z := by
  intro hd
  have hc := hd.hasDerivAt
  have h1 := hasDerivAt_real_direction hc
  have h2 := hasDerivAt_imag_direction hc
  have e1 : HasDerivAt (fun t : ℝ => conj (z + (t : ℂ))) 1 0 := by
    simpa using (hasDerivAt_ofReal' 0).const_add (conj z)
  have e2 : HasDerivAt (fun t : ℝ => conj (z + (t : ℂ) * I)) (-I) 0 := by
    have : (fun t : ℝ => conj (z + (t : ℂ) * I)) = fun t : ℝ => conj z + (t : ℂ) * (-I) := by
      ext t; simp
    rw [this]
    simpa using ((hasDerivAt_ofReal' 0).mul_const (-I)).const_add (conj z)
  have a := h1.unique e1
  have b := h2.unique e2
  rw [a] at b
  have h := congrArg Complex.im b
  simp at h
  norm_num at h

/-- The map `w ↦ (conj w)^2` has complex derivative `0` at the origin. -/
lemma conj_sq_hasDerivAt_zero : HasDerivAt (fun w : ℂ => (conj w) ^ 2) 0 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have h : (fun h : ℂ => h ^ 2) =o[nhds 0] fun h : ℂ => h := isLittleO_pow_id (by norm_num)
  have h2 := h.norm_left
  rw [← isLittleO_norm_left]
  refine h2.congr_left (fun x => ?_)
  simp [norm_pow]

/-- Beck Example 2.2.3 (CX-027), first half: `(conj z)^2` is differentiable at `0`. -/
@[kb "beck2025" "Example 2.2.3, p. 36"]
theorem conj_sq_differentiableAt_zero : DifferentiableAt ℂ (fun w : ℂ => (conj w) ^ 2) 0 :=
  conj_sq_hasDerivAt_zero.differentiableAt

/-- Beck Example 2.2.3 (CX-027), second half: `(conj z)^2` is not differentiable at `z ≠ 0`. -/
@[kb "beck2025" "Example 2.2.3, p. 36"]
theorem conj_sq_not_differentiableAt {z : ℂ} (hz : z ≠ 0) :
    ¬ DifferentiableAt ℂ (fun w : ℂ => (conj w) ^ 2) z := by
  intro hd
  have hc := hd.hasDerivAt
  have h1 := hasDerivAt_real_direction hc
  have h2 := hasDerivAt_imag_direction hc
  have e1 : HasDerivAt (fun t : ℝ => (conj (z + (t : ℂ))) ^ 2) (2 * conj z) 0 := by
    have := ((hasDerivAt_ofReal' 0).const_add (conj z)).fun_pow 2
    simp only [map_add, conj_ofReal]
    simpa using this
  have e2 : HasDerivAt (fun t : ℝ => (conj (z + (t : ℂ) * I)) ^ 2) (-(2 * I * conj z)) 0 := by
    have : (fun t : ℝ => (conj (z + (t : ℂ) * I)) ^ 2)
        = fun t : ℝ => (conj z + (t : ℂ) * (-I)) ^ 2 := by
      ext t; simp
    rw [this]
    have := (((hasDerivAt_ofReal' 0).mul_const (-I)).const_add (conj z)).fun_pow 2
    convert this using 1
    simp; ring
  have a := h1.unique e1
  have b := h2.unique e2
  rw [a] at b
  have hc2 : (4 * I * conj z) = 0 := by linear_combination b
  have : conj z = 0 := by
    simpa [Complex.I_ne_zero] using hc2
  exact hz (by simpa using this)

end UndergradKB.ComplexAnalysis
