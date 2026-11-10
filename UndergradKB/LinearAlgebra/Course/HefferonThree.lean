import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Data.Matrix.Basis
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import UndergradKB.Common.Attr

/-! # Hefferon chapter Three (Hefferon-only rows) -/

namespace UndergradKB.LinearAlgebra.Course

open Matrix

section Maps

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- A linear map sends a linearly dependent family to a linearly dependent family. -/
@[kb "hefferon2020" "Three.II.2.18, p. 216"]
theorem hefferon_Three_II_2_18 {ι : Type*} (f : V →ₗ[K] W) (v : ι → V)
    (hv : ¬ LinearIndependent K v) : ¬ LinearIndependent K (f ∘ v) :=
  fun h => hv (LinearIndependent.of_comp f h)

/-- A one-to-one linear map is an isomorphism from its domain onto its range. -/
@[kb "hefferon2020" "Three.II.2.u1, p. 217"]
theorem hefferon_Three_II_2_u1 (f : V →ₗ[K] W) (hf : Function.Injective f) :
    ∃ e : V ≃ₗ[K] LinearMap.range f, ∀ v, (e v : W) = f v :=
  ⟨LinearEquiv.ofInjective f hf, fun _ => rfl⟩

end Maps

section Matrices

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- The zero map is represented by the zero matrix with respect to any bases, and conversely. -/
@[kb "hefferon2020" "Three.IV.1.6, p. 244",
  kb "hefferon2020" "Three.IV.1.7, p. 244"]
theorem hefferon_Three_IV_1_6 (B : Module.Basis n K V) (D : Module.Basis m K W) :
    LinearMap.toMatrix B D (0 : V →ₗ[K] W) = 0 ∧ Matrix.toLin B D (0 : Matrix m n K) = 0 :=
  ⟨map_zero _, map_zero _⟩

end Matrices

section MatrixAlgebra

variable {R : Type*} {l m n p : Type*}

/-- Matrix multiplication is associative. -/
@[kb "hefferon2020" "Three.IV.2.12, p. 250"]
theorem hefferon_Three_IV_2_12 [Semiring R] [Fintype m] [Fintype n]
    (A : Matrix l m R) (B : Matrix m n R) (C : Matrix n p R) :
    A * B * C = A * (B * C) :=
  Matrix.mul_assoc A B C

/-- Matrix multiplication distributes over addition on both sides. -/
@[kb "hefferon2020" "Three.IV.2.13, p. 250"]
theorem hefferon_Three_IV_2_13 [Semiring R] [Fintype m]
    (A : Matrix l m R) (B C : Matrix m n R) (D E : Matrix l m R) :
    A * (B + C) = A * B + A * C ∧ (D + E) * B = D * B + E * B :=
  ⟨Matrix.mul_add A B C, Matrix.add_mul D E B⟩

/-- Multiplying by a zero matrix on either side gives a zero matrix. -/
@[kb "hefferon2020" "Three.IV.3.1, p. 255"]
theorem hefferon_Three_IV_3_1 [NonUnitalNonAssocSemiring R] [Fintype m]
    (A : Matrix l m R) (B : Matrix m n R) :
    A * (0 : Matrix m n R) = 0 ∧ (0 : Matrix l m R) * B = 0 :=
  ⟨Matrix.mul_zero A, Matrix.zero_mul B⟩

/-- The unit matrix with `(i, j)` entry one has that entry one and all others zero. -/
@[kb "hefferon2020" "Three.IV.3.2, p. 255"]
theorem hefferon_Three_IV_3_2 [Zero R] [One R] [DecidableEq m] [DecidableEq n]
    (i : m) (j : n) (a : m) (b : n) :
    Matrix.single i j (1 : R) a b = if i = a ∧ j = b then 1 else 0 := rfl

/-- Left multiplication by the unit matrix `(i,j)` copies row `j` into row `i` (others zero);
right multiplication copies column `i` into column `j`. -/
@[kb "hefferon2020" "Three.IV.3.u1, p. 255"]
theorem hefferon_Three_IV_3_u1 [NonAssocSemiring R] [Fintype m] [DecidableEq m] [DecidableEq l]
    [DecidableEq n] (i : l) (j : m) (M : Matrix m n R) (a : l) (b : n) :
    (Matrix.single i j (1 : R) * M) a b = if a = i then M j b else 0 := by
  by_cases h : a = i
  · subst h; simp
  · simp [h]

/-- Right multiplication by the unit matrix `(i,j)` copies column `i` into column `j`. -/
@[kb "hefferon2020" "Three.IV.3.u1, p. 255"]
theorem hefferon_Three_IV_3_u1' [NonAssocSemiring R] [Fintype m] [DecidableEq m] [DecidableEq n]
    (i : m) (j : n) (M : Matrix l m R) (a : l) (b : n) :
    (M * Matrix.single i j (1 : R)) a b = if b = j then M a i else 0 := by
  by_cases h : b = j
  · subst h; simp
  · simp [h]

/-- Entry `i` of a matrix-vector product is the dot product of row `i` with the vector. -/
@[kb "hefferon2020" "Three.III.1.6, p. 225"]
theorem hefferon_Three_III_1_6 [NonUnitalNonAssocSemiring R] [Fintype n]
    (A : Matrix m n R) (x : n → R) (i : m) : (A *ᵥ x) i = A i ⬝ᵥ x := rfl

end MatrixAlgebra

section Projections

/-- Projection into `M` along `N` of `m + n` (with `V = M ⊕ N`) is `m`. -/
@[kb "hefferon2020" "Three.VI.3.1, p. 296"]
theorem hefferon_Three_VI_3_1 {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (M N : Submodule K V) (h : IsCompl M N) {x y : V} (hx : x ∈ M) (hy : y ∈ N) :
    M.projection N h (x + y) = x := by
  rw [map_add, Submodule.projection_apply_of_mem_left h hx,
    Submodule.projection_apply_of_mem_right h hy, add_zero]

/-- A linear idempotent map is the projection onto its range along its null space. -/
@[kb "hefferon2020" "Three.VI.3.28, p. 304"]
theorem hefferon_Three_VI_3_28 {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (t : V →ₗ[K] V) (ht : t ∘ₗ t = t) :
    ∃ h : IsCompl (LinearMap.range t) (LinearMap.ker t),
      t = (LinearMap.range t).projection (LinearMap.ker t) h := by
  have hi : IsIdempotentElem t := by
    exact ht
  exact ⟨LinearMap.IsIdempotentElem.isCompl hi, LinearMap.IsIdempotentElem.eq_projection hi⟩

/-- A vector is orthogonal to every member of a set iff it is orthogonal to every member of its
span. -/
@[kb "hefferon2020" "Three.VI.3.22, p. 303"]
theorem hefferon_Three_VI_3_22 {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (S : Set E) (v : E) :
    (∀ s ∈ S, inner 𝕜 v s = 0) ↔ ∀ w ∈ Submodule.span 𝕜 S, inner 𝕜 v w = 0 := by
  refine ⟨fun h w hw => ?_, fun h s hs => h s (Submodule.subset_span hs)⟩
  induction hw using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add x y _ _ hx hy => simp [inner_add_right, hx, hy]
  | smul a x _ hx => simp [inner_smul_right, hx]

end Projections

end UndergradKB.LinearAlgebra.Course
