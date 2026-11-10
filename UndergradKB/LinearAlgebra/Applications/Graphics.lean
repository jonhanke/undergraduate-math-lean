import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import UndergradKB.Common.Attr

/-! # Computer graphics by homogeneous coordinates (Hefferon, Topic: Computer Graphics)

A point `(x, y)` of the plane is the vector `(x, y, 1)`; a `3 × 3` matrix acts on such vectors. -/

namespace UndergradKB.LinearAlgebra

open Matrix

/-- Normalization of a homogeneous vector `(a, b, c)` to the plane point `(a/c, b/c)`. -/
noncomputable def dehomogenize (v : Fin 3 → ℝ) : Fin 2 → ℝ := ![v 0 / v 2, v 1 / v 2]

/-- A `3 × 3` matrix acts on homogeneous coordinates independently of the representative:
scaling a representative scales the image (so the projective point is the same), a nonzero
scalar multiple has the same normalization, the normalization of `(x, y, 1)` is `(x, y)`, and an
invertible matrix induces the map `mk v ↦ mk (M v)` on projective points. -/
@[kb "hefferon2020" "Topic-Graphics.2, p. 403"]
theorem hefferon_Topic_Graphics_2 (M : Matrix (Fin 3) (Fin 3) ℝ) :
    (∀ (c : ℝ) (v : Fin 3 → ℝ), M *ᵥ (c • v) = c • (M *ᵥ v)) ∧
    (∀ (c : ℝ) (v : Fin 3 → ℝ), c ≠ 0 → dehomogenize (c • v) = dehomogenize v) ∧
    (∀ x y : ℝ, dehomogenize ![x, y, 1] = ![x, y]) ∧
    (∀ (hM : IsUnit M) (v : Fin 3 → ℝ) (hv : v ≠ 0),
      ∃ h : M *ᵥ v ≠ 0,
        Projectivization.map (Matrix.toLin' M) (Matrix.mulVec_injective_iff_isUnit.2 hM)
          (Projectivization.mk ℝ v hv) = Projectivization.mk ℝ (M *ᵥ v) h) := by
  refine ⟨fun c v => by rw [Matrix.mulVec_smul], fun c v hc => ?_, fun x y => ?_, fun hM v hv => ?_⟩
  · ext i
    fin_cases i <;> simp [dehomogenize, mul_div_mul_left _ _ hc]
  · simp [dehomogenize]
  · have hinj := Matrix.mulVec_injective_iff_isUnit.2 hM
    have h : M *ᵥ v ≠ 0 := by
      intro h0
      exact hv (hinj (by rw [h0, Matrix.mulVec_zero]))
    exact ⟨h, Projectivization.map_mk _ _ v hv⟩

/-- The `3 × 3` homogeneous matrix of the affine map `x ↦ A x + t` of the plane. -/
def homogeneousMatrix (A : Matrix (Fin 2) (Fin 2) ℝ) (t : Fin 2 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![A 0 0, A 0 1, t 0; A 1 0, A 1 1, t 1; 0, 0, 1]

/-- The homogeneous matrix of the translation by `(tx, ty)`. -/
def translationMatrix (tx ty : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, tx; 0, 1, ty; 0, 0, 1]

/-- Translation, which is not linear on `ℝ²`, is realized on homogeneous coordinates by the
matrix `[[1,0,tx],[0,1,ty],[0,0,1]]`: it sends `(x, y, 1)` to `(x + tx, y + ty, 1)`; composition
of translations is multiplication of the matrices; a nonzero translation is not linear; and more
generally the homogeneous matrices of affine maps `x ↦ A x + t` multiply to the matrix of the
composite map. -/
@[kb "hefferon2020" "Topic-Graphics.3, p. 404"]
theorem hefferon_Topic_Graphics_3 :
    (∀ tx ty x y : ℝ, translationMatrix tx ty *ᵥ ![x, y, 1] = ![x + tx, y + ty, 1]) ∧
    (∀ s t s' t' : ℝ, translationMatrix s t * translationMatrix s' t' =
      translationMatrix (s + s') (t + t')) ∧
    (∀ (tx ty : ℝ), (tx ≠ 0 ∨ ty ≠ 0) →
      ¬ ∃ f : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ), ∀ v, f v = v + ![tx, ty]) ∧
    (∀ (A B : Matrix (Fin 2) (Fin 2) ℝ) (s t : Fin 2 → ℝ),
      homogeneousMatrix A s * homogeneousMatrix B t = homogeneousMatrix (A * B) (A *ᵥ t + s)) := by
  refine ⟨fun tx ty x y => ?_, fun s t s' t' => ?_, ?_, fun A B s t => ?_⟩
  · ext i
    fin_cases i <;> simp [translationMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [translationMatrix, Matrix.mul_apply, Fin.sum_univ_three] <;> ring
  · rintro tx ty h ⟨f, hf⟩
    have h0 := hf 0
    rw [map_zero, zero_add] at h0
    rcases h with h | h
    · have := congrFun h0 0
      simp at this
      exact h this.symm
    · have := congrFun h0 1
      simp at this
      exact h this.symm
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [homogeneousMatrix, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        Fin.sum_univ_two] <;> ring

/-- Rotation by `θ` about the origin as a homogeneous matrix. -/
noncomputable def rotationMatrix (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos θ, -Real.sin θ, 0; Real.sin θ, Real.cos θ, 0; 0, 0, 1]

/-- Scaling of the axes by `sx` and `sy` as a homogeneous matrix. -/
def scalingMatrix (sx sy : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![sx, 0, 0; 0, sy, 0; 0, 0, 1]

/-- Reflection in the line `y = x` as a homogeneous matrix. -/
def reflectDiagMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 1, 0; 1, 0, 0; 0, 0, 1]

/-- Reflection in the line `y = -x` as a homogeneous matrix. -/
def reflectAntiDiagMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -1, 0; -1, 0, 0; 0, 0, 1]

/-- Horizontal shear `(x, y) ↦ (x + k y, y)` as a homogeneous matrix. -/
def shearMatrix (k : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, k, 0; 0, 1, 0; 0, 0, 1]

/-- Rotation, scaling of the axes, reflections in `y = x` and `y = -x`, and shear are given on
homogeneous coordinates by `3 × 3` matrices (for example the rotation matrix
`[[cos θ, -sin θ, 0], [sin θ, cos θ, 0], [0, 0, 1]]`). -/
@[kb "hefferon2020" "Topic-Graphics.4, p. 404"]
theorem hefferon_Topic_Graphics_4 (θ sx sy k x y : ℝ) :
    rotationMatrix θ *ᵥ ![x, y, 1] = ![x * Real.cos θ - y * Real.sin θ,
      x * Real.sin θ + y * Real.cos θ, 1] ∧
    scalingMatrix sx sy *ᵥ ![x, y, 1] = ![sx * x, sy * y, 1] ∧
    reflectDiagMatrix *ᵥ ![x, y, 1] = ![y, x, 1] ∧
    reflectAntiDiagMatrix *ᵥ ![x, y, 1] = ![-y, -x, 1] ∧
    shearMatrix k *ᵥ ![x, y, 1] = ![x + k * y, y, 1] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> ext i <;> fin_cases i <;>
    simp [rotationMatrix, scalingMatrix, reflectDiagMatrix, reflectAntiDiagMatrix, shearMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

end UndergradKB.LinearAlgebra
