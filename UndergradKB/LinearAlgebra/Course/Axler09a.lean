import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.Fin
import UndergradKB.Common.Attr

/-! # Axler, Chapter 9 (part a): bilinear forms, quadratic forms, alternating multilinear forms

Course-layer wrappers for the `in Mathlib` rows of Axler 9A and 9B.  Several 9B rows are shared with
Hefferon Chapter Four and carry both tags. -/

open Module Matrix

namespace UndergradKB.LinearAlgebra.Course

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-! ## 9A Bilinear forms -/

/-- Axler 9.1: a bilinear form is a map `V × V → K` that is linear in each argument separately; such
maps are exactly the elements of `LinearMap.BilinForm K V`. -/
@[kb "axler2024" "9.1, p. 351"]
theorem axler_9_1 (β : V → V → K)
    (h1 : ∀ u₁ u₂ w, β (u₁ + u₂) w = β u₁ w + β u₂ w) (h2 : ∀ (c : K) u w, β (c • u) w = c * β u w)
    (h3 : ∀ u w₁ w₂, β u (w₁ + w₂) = β u w₁ + β u w₂) (h4 : ∀ (c : K) u w, β u (c • w) = c * β u w) :
    ∃ B : LinearMap.BilinForm K V, ∀ u w, B u w = β u w :=
  ⟨LinearMap.mk₂ K β h1 h2 h3 h4, fun _ _ => rfl⟩

/-- Axler 9.3: bilinear forms form a vector space under pointwise addition and scalar multiplication. -/
@[kb "axler2024" "9.3, p. 352"]
theorem axler_9_3 (B₁ B₂ : LinearMap.BilinForm K V) (c : K) (u w : V) :
    (B₁ + B₂) u w = B₁ u w + B₂ u w ∧ (c • B₁) u w = c * B₁ u w := by
  simp

/-- Axler 9.4: the matrix of a bilinear form in a basis has entries `β (e_j, e_k)`, and
`β ↦ M(β)` is a linear bijection onto matrices. -/
@[kb "axler2024" "9.4, p. 352"]
theorem axler_9_4 {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Basis ι K V) :
    (∀ (B : LinearMap.BilinForm K V) j k, LinearMap.BilinForm.toMatrix e B j k = B (e j) (e k)) ∧
      Function.Bijective (LinearMap.BilinForm.toMatrix e) :=
  ⟨fun B j k => LinearMap.BilinForm.toMatrix_apply e B j k, (LinearMap.BilinForm.toMatrix e).bijective⟩

/-- Axler 9.6: the forms `(u, w) ↦ β (u, T w)` and `(u, w) ↦ β (T u, w)` have matrices `M(β) M(T)` and
`M(T)ᵗ M(β)`. -/
@[kb "axler2024" "9.6, p. 353"]
theorem axler_9_6 {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Basis ι K V)
    (B : LinearMap.BilinForm K V) (T : V →ₗ[K] V) :
    LinearMap.BilinForm.toMatrix e (B.compRight T) =
        LinearMap.BilinForm.toMatrix e B * LinearMap.toMatrix e e T ∧
      LinearMap.BilinForm.toMatrix e (B.compLeft T) =
        (LinearMap.toMatrix e e T)ᵀ * LinearMap.BilinForm.toMatrix e B :=
  ⟨LinearMap.BilinForm.toMatrix_compRight e B T, LinearMap.BilinForm.toMatrix_compLeft e B T⟩

/-- Axler 9.7: change of basis; if `C` is the change-of-basis matrix from `e` to `f`, then
`M(β, f) = Cᵗ M(β, e) C`. -/
@[kb "axler2024" "9.7, p. 354"]
theorem axler_9_7 {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : Basis ι K V) (f : Basis κ K V) (B : LinearMap.BilinForm K V) :
    LinearMap.BilinForm.toMatrix f B =
      (e.toMatrix f)ᵀ * LinearMap.BilinForm.toMatrix e B * e.toMatrix f :=
  (LinearMap.BilinForm.toMatrix_mul_basis_toMatrix e f B).symm

/-- Axler 9.9: a bilinear form is symmetric if `β (u, w) = β (w, u)`. -/
@[kb "axler2024" "9.9, p. 355"]
theorem axler_9_9 (B : LinearMap.BilinForm K V) : B.IsSymm ↔ ∀ u w, B u w = B w u :=
  LinearMap.BilinForm.isSymm_def

omit [Field K] in
/-- Axler 9.11: a square matrix is symmetric if it equals its transpose. -/
@[kb "axler2024" "9.11, p. 355"]
theorem axler_9_11 {n : Type*} (A : Matrix n n K) : A.IsSymm ↔ A = Aᵀ :=
  eq_comm

/-- Axler 9.14: a bilinear form is alternating if `β (v, v) = 0` for all `v`. -/
@[kb "axler2024" "9.14, p. 357"]
theorem axler_9_14 (B : LinearMap.BilinForm K V) : B.IsAlt ↔ ∀ v, B v v = 0 :=
  Iff.rfl

/-- Axler 9.16: over a field of characteristic zero (the book's `ℝ` or `ℂ`), a bilinear form is
alternating iff `β (u, w) = - β (w, u)` for all `u, w`. -/
@[kb "axler2024" "9.16, p. 358"]
theorem axler_9_16 [CharZero K] (B : LinearMap.BilinForm K V) :
    B.IsAlt ↔ ∀ u w, B u w = - B w u := by
  change LinearMap.IsAlt B ↔ _
  rw [LinearMap.isAlt_iff_eq_neg_flip]
  constructor
  · intro h u w
    have := LinearMap.congr_fun₂ h u w
    simpa using this
  · intro h
    ext u w
    simp [h u w]

/-- Axler 9.18: the quadratic form `q_β (v) = β (v, v)` of a bilinear form is a quadratic form, and
(when `2` is invertible, e.g. over `ℝ` or `ℂ`) every quadratic form arises this way. -/
@[kb "axler2024" "9.18, p. 359"]
theorem axler_9_18 [Invertible (2 : K)] :
    (∀ B : LinearMap.BilinForm K V, ∃ Q : QuadraticForm K V, ∀ v, Q v = B v v) ∧
    (∀ Q : QuadraticForm K V, ∃ B : LinearMap.BilinForm K V, ∀ v, Q v = B v v) :=
  ⟨fun B => ⟨B.toQuadraticMap, fun v => LinearMap.BilinMap.toQuadraticMap_apply B v⟩,
   fun Q => ⟨QuadraticMap.associated Q, fun v => (QuadraticMap.associated_eq_self_apply K Q v).symm⟩⟩

/-! ## 9B Alternating multilinear forms -/

/-- Axler 9.24, 9.25 (and Hefferon Four.I.3.2): an `m`-linear form is linear in each slot when the other
slots are held fixed. -/
@[kb "axler2024" "9.24, p. 364", kb "axler2024" "9.25, p. 364",
  kb "hefferon2020" "Four.I.3.2, p. 348"]
theorem axler_9_24 {m : ℕ} (f : MultilinearMap K (fun _ : Fin m => V) K) (v : Fin m → V) (i : Fin m)
    (x y : V) (c : K) :
    f (Function.update v i (x + y)) = f (Function.update v i x) + f (Function.update v i y) ∧
      f (Function.update v i (c • x)) = c * f (Function.update v i x) :=
  ⟨f.map_update_add v i x y, f.map_update_smul v i c x⟩

/-- Axler 9.27: an alternating `m`-linear form vanishes whenever two inputs are equal. -/
@[kb "axler2024" "9.27, p. 365"]
theorem axler_9_27 {m : ℕ} (α : V [⋀^Fin m]→ₗ[K] K) (v : Fin m → V) (i j : Fin m) (hij : i ≠ j)
    (h : v i = v j) : α v = 0 :=
  α.map_eq_zero_of_eq v h hij

/-- Axler 9.28: an alternating form vanishes on any linearly dependent list. -/
@[kb "axler2024" "9.28, p. 365"]
theorem axler_9_28 {m : ℕ} (α : V [⋀^Fin m]→ₗ[K] K) (v : Fin m → V) (h : ¬ LinearIndependent K v) :
    α v = 0 :=
  α.map_linearDependent v h

/-- Axler 9.30 (and Hefferon Four.I.2.2): swapping two inputs of an alternating form negates the value;
more generally permuting the inputs multiplies by the sign of the permutation. -/
@[kb "axler2024" "9.30, p. 366", kb "hefferon2020" "Four.I.2.2, p. 342"]
theorem axler_9_30 {m : ℕ} (α : V [⋀^Fin m]→ₗ[K] K) (v : Fin m → V) (i j : Fin m) (hij : i ≠ j)
    (σ : Equiv.Perm (Fin m)) :
    α (v ∘ Equiv.swap i j) = - α v ∧ α (v ∘ σ) = ((Equiv.Perm.sign σ : ℤ) : K) * α v :=
  ⟨α.map_swap v hij, by rw [AlternatingMap.map_perm, Units.smul_def]; simp⟩

/-- Axler 9.34 (and Hefferon Four.I.4.4): interchanging two entries of a permutation changes its sign. -/
@[kb "axler2024" "9.34, p. 367", kb "hefferon2020" "Four.I.4.4, p. 358"]
theorem axler_9_34 {m : ℕ} (σ : Equiv.Perm (Fin m)) (i j : Fin m) (hij : i ≠ j) :
    Equiv.Perm.sign (σ * Equiv.swap i j) = - Equiv.Perm.sign σ := by
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij, mul_neg_one]

/-- Axler 9.32 (and Hefferon Four.I.4.1, Four.I.4.7): the sign of a permutation of `{1, ..., m}` is
`(-1) ^ N` where `N` is the number of inversions. -/
@[kb "axler2024" "9.32, p. 367", kb "hefferon2020" "Four.I.4.1, p. 357",
  kb "hefferon2020" "Four.I.4.7, p. 359"]
theorem axler_9_32 {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    Equiv.Perm.sign σ =
      (-1 : ℤˣ) ^ ((Finset.univ.filter fun p : Fin m × Fin m => p.1 < p.2 ∧ σ p.2 < σ p.1).card) := by
  have aux : ∀ (i : Fin m), ∏ j ∈ Finset.Ioi i, (if σ i < σ j then (1 : ℤˣ) else -1) =
      (-1 : ℤˣ) ^ ((Finset.univ.filter fun j : Fin m => i < j ∧ σ j < σ i).card) := by
    intro i
    rw [Finset.prod_ite]
    simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
    congr 2
    ext j
    simp [not_lt, le_iff_lt_or_eq, σ.injective.eq_iff]
    intro h h'
    subst h'
    exact absurd h (lt_irrefl _)
  rw [Equiv.Perm.sign_eq_prod_prod_Ioi]
  simp_rw [aux]
  rw [Finset.prod_pow_eq_pow_sum, Finset.card_filter, Fintype.sum_prod_type]
  simp_rw [Finset.card_filter]

/-- Axler 9.35: for an alternating form, `α (v_{j₁}, ..., v_{j_m}) = sign (j₁, ..., j_m) α (v₁, ..., v_m)`. -/
@[kb "axler2024" "9.35, p. 368"]
theorem axler_9_35 {m : ℕ} (α : V [⋀^Fin m]→ₗ[K] K) (v : Fin m → V) (σ : Equiv.Perm (Fin m)) :
    α (fun k => v (σ k)) = ((Equiv.Perm.sign σ : ℤ) : K) * α v := by
  have := AlternatingMap.map_perm α v σ
  rw [Units.smul_def] at this
  simpa [Function.comp_def] using this

/-- Axler 9.36: for a basis `e` and `v_k = ∑_j b_{jk} e_j`, an alternating form satisfies
`α v = α e * ∑_σ sign σ * ∏_k b_{σ k, k}`. -/
@[kb "axler2024" "9.36, p. 368"]
theorem axler_9_36 {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Basis ι K V)
    (α : V [⋀^ι]→ₗ[K] K) (b : ι → ι → K) (v : ι → V) (hv : ∀ k, v k = ∑ j, b j k • e j) :
    α v = α e * ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : K) * ∏ k, b (σ k) k := by
  have h := AlternatingMap.eq_smul_basis_det e α
  have hM : e.toMatrix v = Matrix.of b := by
    ext j k
    simp [Basis.toMatrix_apply, hv k, map_sum, Finsupp.single_apply]
  have : α v = α e * (e.det v) := by
    conv_lhs => rw [h]
    simp
  rw [this, Basis.det_apply, hM, Matrix.det_apply]
  simp [Units.smul_def, zsmul_eq_mul]

/-- Axler 9.39: for a nonzero alternating `n`-linear form `α` on an `n`-dimensional space,
`α (v₁, ..., v_n) ≠ 0` iff `v` is a basis. -/
@[kb "axler2024" "9.39, p. 370"]
theorem axler_9_39 {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Basis ι K V)
    (α : V [⋀^ι]→ₗ[K] K) (hα : α ≠ 0) (v : ι → V) :
    α v ≠ 0 ↔ LinearIndependent K v ∧ Submodule.span K (Set.range v) = ⊤ := by
  have h := AlternatingMap.eq_smul_basis_det e α
  have he : α e ≠ 0 := fun h0 => hα ((AlternatingMap.map_basis_eq_zero_iff e α).1 h0)
  have : α v = α e * (e.det v) := by
    conv_lhs => rw [h]
    simp
  rw [Basis.is_basis_iff_det e, isUnit_iff_ne_zero, this]
  simp [he]

end UndergradKB.LinearAlgebra.Course
